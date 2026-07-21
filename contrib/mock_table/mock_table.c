#include "postgres.h"
#include "fmgr.h"
#include "optimizer/plancat.h"
#include "optimizer/planner.h"
#include "optimizer/pathnode.h"
#include "optimizer/cost.h"
#include "optimizer/optimizer.h"
#include "optimizer/restrictinfo.h"
#include "catalog/namespace.h"
#include "utils/lsyscache.h"
#include "utils/builtins.h"
#include "nodes/extensible.h"
#include "nodes/makefuncs.h"
#include "optimizer/paths.h"
#include "optimizer/tlist.h"
#include "parser/parsetree.h"
#include "parser/parse_relation.h"
#include "commands/explain.h"
#include "executor/executor.h"
#include "miscadmin.h"
#include "utils/ruleutils.h"

#include <string.h>
#include <float.h>

#include "fqp_path_utils.h"
#include "fqp_trace.h"
#include "mock_table.h"

PG_MODULE_MAGIC;

static get_relation_info_hook_type prev_get_rel_info_hook = NULL;
static set_rel_pathlist_hook_type prev_set_rel_pathlist_hook = NULL;
static set_join_pathlist_hook_type prev_set_join_pathlist_hook = NULL;
static planner_hook_type prev_planner_hook = NULL;

static CustomPathMethods exchange_path_methods;

/*
 * Experimental pruning mode: local/sink is absorbing.
 *
 * Each database optimizes the query as a candidate final sink. With this
 * enabled, once either child side of a join is already available locally at
 * this sink, the joinrel is left local and we do not issue remote EXPLAINs for
 * alternate destinations. Set to 0 to return to exhaustive destination-aware
 * FQP join enumeration.
 */
#define FQP_LOCAL_ABSORBING_JOIN_PRUNING 0

static PlannedStmt *fqp_planner_hook(Query *parse,
                                     const char *query_string,
                                     int cursorOptions,
                                     ParamListInfo boundParams);

static PlannedStmt *
fqp_planner_hook(Query *parse,
                 const char *query_string,
                 int cursorOptions,
                 ParamListInfo boundParams)
{
    PlannedStmt *result = NULL;
    bool started_trace = false;

    if (!fqp_trace_is_active())
    {
        fqp_trace_begin(query_string);
        started_trace = true;
    }

    PG_TRY();
    {
        if (prev_planner_hook)
            result = prev_planner_hook(parse, query_string, cursorOptions, boundParams);
        else
            result = standard_planner(parse, query_string, cursorOptions, boundParams);
    }
    PG_CATCH();
    {
        if (started_trace)
            fqp_trace_finish(false);
        PG_RE_THROW();
    }
    PG_END_TRY();

    if (started_trace)
        fqp_trace_finish(true);

    return result;
}

static void begin_exchange_scan(CustomScanState *node, EState *estate, int eflags) {
    CustomScan  *cscan;
    ListCell    *lc;

    /*
     * EXPLAIN prints CustomScan children from CustomScanState.custom_ps.
     * Populate it from planner-time custom_plans.
     */
    if (node->custom_ps == NIL)
    {
        cscan = (CustomScan *) node->ss.ps.plan;
        foreach(lc, cscan->custom_plans)
        {
            Plan       *subplan = (Plan *) lfirst(lc);
            PlanState  *substate;

            substate = ExecInitNode(subplan, estate, eflags);
            node->custom_ps = lappend(node->custom_ps, substate);
        }
    }

    if (eflags & EXEC_FLAG_EXPLAIN_ONLY)
        return;

    elog(ERROR, "Execution reached local mock node. FQP Orchestrator failed to intercept the plan.");
}

static TupleTableSlot *exec_exchange_scan(CustomScanState *node) { return NULL; }

static void end_exchange_scan(CustomScanState *node) {
    ListCell *lc;

    foreach(lc, node->custom_ps)
        ExecEndNode((PlanState *) lfirst(lc));
}

static void rescan_exchange_scan(CustomScanState *node) {
    ListCell *lc;

    foreach(lc, node->custom_ps)
        ExecReScan((PlanState *) lfirst(lc));
}


static void
explain_exchange_scan(CustomScanState *node, List *ancestors, ExplainState *es)
{
    CustomScan  *cscan;
    const char  *scan_kind;
    int          dest_rti;
    int          remote_expr_count;
    int          remote_projection_count;
    bool         has_local_qual;
    bool         has_dest_source;
    char         dest_source[64];
    RangeTblEntry *dest_rte;
    const char  *dest_text;
    List        *dpcontext;
    bool         useprefix;
    List        *remote_filters;
    List        *remote_projections;
    ListCell    *lc;

    cscan = (CustomScan *) node->ss.ps.plan;
    scan_kind = (cscan->scan.scanrelid != 0) ? "baserel" : "joinrel";
    dest_rti = fqp_dest_rti_from_custom_private(cscan->custom_private);
    remote_expr_count = 0;
    remote_projection_count = 0;
    has_local_qual = (cscan->scan.plan.qual != NIL);
    has_dest_source = false;
    dest_source[0] = '\0';
    remote_filters = NIL;
    remote_projections = NIL;
    dpcontext = set_deparse_context_plan(es->deparse_cxt, node->ss.ps.plan, ancestors);
    useprefix = true; //(es->rtable_size > 1 || es->verbose);

    foreach(lc, cscan->custom_exprs)
    {
        Node *expr = (Node *) lfirst(lc);

        if (expr != NULL)
            remote_filters = lappend(remote_filters,
                                     deparse_expression(expr, dpcontext, useprefix, false));
    }

    if (list_length(cscan->custom_private) > 1)
    {
        List *restrictlist = (List *) lsecond(cscan->custom_private);

        List *actual_clauses = get_actual_clauses(restrictlist);

        foreach(lc, actual_clauses)
        {
            Node *expr = (Node *) lfirst(lc);

            if (expr != NULL)
                remote_filters = lappend(remote_filters,
                                         deparse_expression(expr, dpcontext, useprefix, false));
        }
    }

    List *tlist_to_deparse = (cscan->custom_scan_tlist != NIL) ? cscan->custom_scan_tlist : cscan->scan.plan.targetlist;
    foreach(lc, tlist_to_deparse)
    {
        TargetEntry *tle = (TargetEntry *) lfirst(lc);

        if (tle != NULL && !tle->resjunk)
            remote_projections = lappend(remote_projections,
                                         deparse_expression((Node *) tle->expr,
                                                            dpcontext,
                                                            useprefix,
                                                            false));
    }

    remote_expr_count = list_length(remote_filters);
    remote_projection_count = list_length(remote_projections);

    dest_rte = NULL;
    if (dest_rti > 0 &&
        node->ss.ps.state != NULL &&
        node->ss.ps.state->es_range_table != NIL &&
        dest_rti <= list_length(node->ss.ps.state->es_range_table))
    {
        dest_rte = rt_fetch((Index) dest_rti, node->ss.ps.state->es_range_table);
        has_dest_source = fqp_get_source_for_rte(dest_rte, dest_source, sizeof(dest_source));
    }

    if (dest_rti == 0)
        dest_text = "local";
    else if (has_dest_source)
        dest_text = psprintf("remote (source=%s)", dest_source);
    else
        dest_text = "remote (source=unknown)";

    double data_movement_cost = 0.0;
    if (dest_rti > 0)
    {
        double movement_factor = mock_table_data_movement_factor();
        data_movement_cost = movement_factor * (double) cscan->scan.plan.plan_rows * (double) cscan->scan.plan.plan_width;
    }
    double op_cost = (double) cscan->scan.plan.total_cost - data_movement_cost;
    ExplainPropertyText("FQP Annotation", dest_text, es);
    ExplainPropertyText("FQP Scan Kind", scan_kind, es);
    ExplainPropertyFloat("FQP Data Movement Cost", NULL, data_movement_cost, 2, es);
    ExplainPropertyFloat("FQP Op Cost", NULL, op_cost, 2, es);
    // ExplainPropertyText("FQP Annotation Source", has_dest_source ? dest_source : (dest_rti == 0 ? "local" : "unknown"), es);
    // ExplainPropertyInteger("FQP Annotation RTI", NULL, dest_rti, es);
    ExplainPropertyInteger("FQP Remote Expr Count", NULL, remote_expr_count, es);
    // ExplainPropertyInteger("FQP Remote Projection Count", NULL, remote_projection_count, es);
    if (remote_filters != NIL)
        ExplainPropertyList("FQP Remote Filters", remote_filters, es);
    if (remote_projections != NIL)
        ExplainPropertyList("FQP Remote Projections", remote_projections, es);
    ExplainPropertyBool("FQP Local Qual Present", has_local_qual, es);
}

static CustomExecMethods exchange_exec_methods = {
    .CustomName = "FQP_Data_Exchange_Exec",
    .BeginCustomScan = begin_exchange_scan,
    .ExecCustomScan = exec_exchange_scan,
    .EndCustomScan = end_exchange_scan,
    .ReScanCustomScan = rescan_exchange_scan,
    .ExplainCustomScan = explain_exchange_scan
};

static Node *create_exchange_scan_state(CustomScan *cscan) {
    CustomScanState *cscanstate = makeNode(CustomScanState);
    cscanstate->ss.ps.plan = (Plan *) cscan;
    cscanstate->methods = &exchange_exec_methods;
    return (Node *) cscanstate;
}

static CustomScanMethods exchange_scan_methods = {
    "FQP_Data_Exchange_Scan",
    create_exchange_scan_state
};

static Plan *create_exchange_plan(PlannerInfo *root, RelOptInfo *rel, struct CustomPath *best_path, List *tlist, List *clauses, List *custom_plans) 
{
    CustomScan *cscan = makeNode(CustomScan);
    Index scanrelid;

    scanrelid = IS_SIMPLE_REL(rel) ? rel->relid : 0; // for basrerels only, null for joinrels
    
    cscan->scan.plan.targetlist = tlist;

    cscan->scan.plan.qual = NIL;
    cscan->scan.scanrelid = scanrelid;

    if (scanrelid == 0) // not a baserel
        cscan->custom_scan_tlist = tlist;
    else
    {
        cscan->custom_scan_tlist = NIL; // no targetlist for baserel
        cscan->custom_exprs = extract_actual_clauses(clauses, false); // type mismatch if clauses directly stored
    }

    // propagate estimates so explain shows rows/width
    cscan->scan.plan.plan_rows = best_path->path.rows;
    cscan->scan.plan.plan_width = best_path->path.pathtarget->width;
    cscan->flags = best_path->flags;
    cscan->methods = &exchange_scan_methods;

    // will need annotation to scan from remote
    cscan->custom_private = best_path->custom_private;
    cscan->custom_plans = custom_plans;

    return &cscan->scan.plan;
}

static CustomPathMethods exchange_path_methods = {
    "FQP_Data_Exchange_Path",
    create_exchange_plan,
    NULL
};

static List *
fqp_make_custom_private_join(int dest_rti, List *restrictlist)
{
    return list_make2(makeInteger(dest_rti), restrictlist ? (Node *) restrictlist : (Node *) NIL);
}

static void
fqp_log_remote_base_explain(RangeTblEntry *rte, Index rti)
{
    const char *nspname;
    const char *relname;

    if (rte == NULL || rte->rtekind != RTE_RELATION)
        return;

    nspname = get_namespace_name(get_rel_namespace(rte->relid));
    relname = get_rel_name(rte->relid);
    if (nspname == NULL || relname == NULL)
        return;

    elog(LOG,
         "mock_table remote explain (baserel rti=%d): EXPLAIN SELECT * FROM %s.%s",
         (int) rti,
         quote_identifier(nspname),
         quote_identifier(relname));
}

static void 
fqp_set_rel_pathlist_hook(PlannerInfo *root, RelOptInfo *rel, Index rti, RangeTblEntry *rte) {
    CustomPath *cpath;
    char source[64];

    if (prev_set_rel_pathlist_hook) {
        prev_set_rel_pathlist_hook(root, rel, rti, rte);
    }

    if (rte == NULL || rte->rtekind != RTE_RELATION)
        return;

    if (is_remote_table(rte->relid)) {
        bool supported;
        bool got_remote_cost;
        char *sql;
        Cost startup_cost;
        Cost total_cost;
        Cost data_movement_cost;
        double movement_factor;
        Cardinality plan_rows;
        int plan_width;

        rel->pathlist = NIL;
        rel->partial_pathlist = NIL;

        cpath = makeNode(CustomPath);
        cpath->path.pathtype = T_CustomScan;
        cpath->path.parent = rel;
        cpath->path.pathtarget = rel->reltarget;

        source[0] = '\0';
        (void) fqp_get_source_for_rte(rte, source, sizeof(source));

        sql = mock_deparse_base_sql_for_source(root,
                       rel,
                       cpath->path.pathtarget,
                       (source[0] != '\0') ? source : NULL,
                       &supported);
        startup_cost = 150.0;
        total_cost = 150.0 + (rel->tuples * 0.05);
        plan_rows = rel->rows;
        plan_width = rel->reltarget->width;
        got_remote_cost = false;

        if (supported)
        {
            if (source[0] != '\0')
                got_remote_cost = mock_remote_explain_sql_for_source(source,
                                                                     sql,
                                                                     &startup_cost,
                                                                     &total_cost,
                                                                     &plan_rows,
                                                                     &plan_width);
            else
                got_remote_cost = mock_remote_explain_sql(sql,
                                                          &startup_cost,
                                                          &total_cost,
                                                          &plan_rows,
                                                          &plan_width);

            if (got_remote_cost)
            {
                elog(LOG,
                     "mock_table remote parsed base cost used (rti=%d source=%s): startup=%.3f total=%.3f rows=%.0f width=%d",
                     (int) rti,
                     (source[0] != '\0') ? source : "default",
                     startup_cost,
                     total_cost,
                     (double) plan_rows,
                     plan_width);
            }
            else
                fqp_log_remote_base_explain(rte, rti);
        }
        else
            fqp_log_remote_base_explain(rte, rti);

        movement_factor = mock_table_data_movement_factor();
        data_movement_cost = (Cost) (movement_factor * (double) plan_rows * (double) plan_width);
        total_cost += data_movement_cost;

        cpath->path.rows = plan_rows;
        cpath->path.startup_cost = startup_cost;
        cpath->path.total_cost = total_cost;
        if (plan_width > 0)
            cpath->path.pathtarget->width = plan_width;
        
        cpath->flags = 0;
        cpath->custom_paths = NIL;

        cpath->custom_private = list_make1(makeInteger((int) rti));
        cpath->methods = &exchange_path_methods;

        add_path(rel, (Path *) cpath);

        elog(LOG, "mock_table: added remote baserel custom path for rti=%d", (int) rti);
    }
}

static void 
fqp_get_relation_info_hook(PlannerInfo *root, Oid relOid, bool inhparent, RelOptInfo *rel) {
    bool supported;
    bool got_remote_cost;
    char *sql;
    Cost startup_cost;
    Cost total_cost;
    Cardinality plan_rows;
    int plan_width;
    double page_estimate;

    if (prev_get_rel_info_hook) {
        prev_get_rel_info_hook(root, relOid, inhparent, rel);
    }

    if (is_remote_table(relOid)) {
        RangeTblEntry *rte;
        char source[64];

        sql = NULL;
        startup_cost = 0.0;
        total_cost = 0.0;
        plan_rows = rel->tuples;
        plan_width = 0;
        got_remote_cost = false;
        source[0] = '\0';

        rte = (rel != NULL && IS_SIMPLE_REL(rel)) ? fqp_rt_fetch(root, rel->relid) : NULL;
        if (rte != NULL)
            (void) fqp_get_source_for_rte(rte, source, sizeof(source));

        sql = mock_deparse_base_sql_for_source(root,
                               rel,
                               rel->reltarget,
                               (source[0] != '\0') ? source : NULL,
                               &supported);

        if (supported)
        {
            if (source[0] != '\0')
                got_remote_cost = mock_remote_explain_sql_for_source(source,
                                                                     sql,
                                                                     &startup_cost,
                                                                     &total_cost,
                                                                     &plan_rows,
                                                                     &plan_width);
            else
                got_remote_cost = mock_remote_explain_sql(sql,
                                                          &startup_cost,
                                                          &total_cost,
                                                          &plan_rows,
                                                          &plan_width);
        }

        if (got_remote_cost)
        {
            rel->tuples = plan_rows;

            if (plan_width <= 0)
                plan_width = 32;

            page_estimate = ((double) plan_rows * (double) plan_width) / (double) BLCKSZ;
            if (page_estimate < 1.0)
                page_estimate = 1.0;

            rel->pages = (BlockNumber) page_estimate;

            elog(LOG,
                "mock_table remote relation info used (relid=%u source=%s): startup=%.3f total=%.3f rows=%.0f width=%d pages=%u",
                 relOid,
                (source[0] != '\0') ? source : "default",
                  startup_cost,
                  total_cost,
                 (double) plan_rows,
                 plan_width,
                 rel->pages);
        }
        else
        {
            rel->tuples = 600;
            rel->pages = 50;
            elog(LOG,
                 "mock_table: relation info remote EXPLAIN unavailable for relid=%u, using fallback tuples/pages",
                 relOid);
        }
    }
}

static void
fqp_set_join_pathlist_hook(PlannerInfo *root, RelOptInfo *joinrel, RelOptInfo *outerrel, RelOptInfo *innerrel, JoinType jointype, JoinPathExtraData *extra)
{
    int outerRel;
    int innerRel;
    CustomPath *cpath;
    bool supported;
    bool got_remote_cost;
    char *sql;
    Cost startup_cost;
    Cost total_cost;
    Cost data_movement_cost;
    double movement_factor;
    Cardinality plan_rows;
    int plan_width;
    int dest_rti;
    int source_count;
    bool is_mixed_local_remote;
    bool has_local_candidate = false;
    List *sources;
    List *join_path_candidates;
    ListCell *lc;

    if (prev_set_join_pathlist_hook)
        prev_set_join_pathlist_hook(root, joinrel, outerrel, innerrel, jointype, extra);

    if (fqp_is_final_joinrel(root, joinrel)) { // final sink, no changes
        elog(LOG, "mock_table: final joinrel detected, keeping core planner join paths");
        return;
    }

#if FQP_LOCAL_ABSORBING_JOIN_PRUNING
    /*
     * FQP LOCAL-ABSORBING PRUNING:
     *
     * This partitions distributed optimization by final sink. If either child
     * side is already available locally at this sink, keep this join local and
     * skip remote EXPLAINs for alternate destinations. Disable by setting
     * FQP_LOCAL_ABSORBING_JOIN_PRUNING to 0 above.
     */
    if (fqp_rel_has_sink_local_path(root, outerrel) ||
        fqp_rel_has_sink_local_path(root, innerrel))
    {
        elog(LOG,
             "mock_table: local-absorbing pruning kept joinrel local; skipping remote join EXPLAIN candidates");
        return;
    }
#endif

    outerRel = reloptinfo_dest_rti(root, outerrel);
    innerRel = reloptinfo_dest_rti(root, innerrel);
    is_mixed_local_remote = ((outerRel != 0 && innerRel == 0) ||
                             (outerRel == 0 && innerRel != 0));

    cpath = makeNode(CustomPath);
    cpath->path.pathtype = T_CustomScan;
    cpath->path.parent = joinrel;
    cpath->path.pathtarget = joinrel->reltarget;
    
    sql = NULL;
    supported = true;

    startup_cost = DBL_MAX;
    total_cost = DBL_MAX;
    plan_rows = joinrel->rows;
    plan_width = joinrel->reltarget->width;
    dest_rti = (outerRel != 0) ? outerRel : innerRel;
    got_remote_cost = false;
    sources = NIL;
    join_path_candidates = NIL;
    source_count = 0;

    fqp_collect_source_candidates_from_rel(root,
                                           outerrel,
                                           &sources,
                                           &has_local_candidate);
    fqp_collect_source_candidates_from_rel(root,
                                           innerrel,
                                           &sources,
                                           &has_local_candidate);

    source_count = list_length(sources);

    if (source_count == 0)
    {
        elog(LOG, "mock_table: joinrel has no remote FQP destination candidates, keeping core planner join paths");
        return;
    }

    // elog(LOG,
    //      "mock_table: joinrel candidate source scope restricted to annotated outer/inner rels (count=%d)",
    //      source_count);

    if (supported)
    {
        if (sources != NIL)
        {
            foreach(lc, sources)
            {
                FqpSourceCandidate *cand = (FqpSourceCandidate *) lfirst(lc);
                CustomPath *cand_path;
                Cost cand_startup;
                Cost cand_total;
                Cardinality cand_rows;
                int cand_width;
                Cost cand_movement;
                bool cand_supported;
                bool cand_got_remote_cost;
                Path *outer_path;
                Path *inner_path;

                cand_startup = DBL_MAX;
                cand_total = DBL_MAX;
                cand_rows = joinrel->rows;
                cand_width = joinrel->reltarget->width;
                cand_supported = true;
                cand_got_remote_cost = false;

                sql = mock_deparse_join_sql_for_source(root,
                                                       joinrel,
                                                       outerrel,
                                                       innerrel,
                                                       jointype,
                                                       (extra != NULL) ? extra->restrictlist : NIL,
                                                       cand->source,
                                                       &cand_supported);
                if (!cand_supported)
                    continue;

                elog(LOG, "mock_table remote explain (join source=%s): EXPLAIN %s", cand->source, sql);

                cand_got_remote_cost = mock_remote_explain_sql_for_source(cand->source,
                                                                          sql,
                                                                          &cand_startup,
                                                                          &cand_total,
                                                                          &cand_rows,
                                                                          &cand_width);
                if (!cand_got_remote_cost)
                    continue;

                movement_factor = mock_table_data_movement_factor();
                cand_movement = (Cost) (movement_factor * (double) cand_rows * (double) cand_width);
                cand_total += cand_movement;

                elog(LOG,
                     "mock_table remote parsed join candidate used (source=%s): startup=%.3f total=%.3f rows=%.0f width=%d movement=%.3f",
                     cand->source,
                     cand_startup,
                     cand_total,
                     (double) cand_rows,
                     cand_width,
                     cand_movement);

                cand_path = makeNode(CustomPath);
                cand_path->path.pathtype = T_CustomScan;
                cand_path->path.parent = joinrel;
                cand_path->path.pathtarget = copy_pathtarget(joinrel->reltarget);
                cand_path->path.startup_cost = cand_startup;
                cand_path->path.total_cost = cand_total;
                cand_path->path.rows = cand_rows;
                if (cand_width > 0)
                    cand_path->path.pathtarget->width = cand_width;
                cand_path->flags = 0;
                cand_path->custom_private = fqp_make_custom_private_join(cand->rti, (extra != NULL) ? extra->restrictlist : NIL);
                outer_path = fqp_best_path_for_source(root, outerrel, cand->source);
                inner_path = fqp_best_path_for_source(root, innerrel, cand->source);
                if (outer_path == NULL)
                    outer_path = outerrel->cheapest_total_path;
                if (inner_path == NULL)
                    inner_path = innerrel->cheapest_total_path;
                cand_path->custom_paths = list_make2(outer_path, inner_path);
                cand_path->methods = &exchange_path_methods;

                fqp_add_ranked_join_path_candidate(&join_path_candidates,
                                                   cand_path,
                                                   cand->source);
                got_remote_cost = true;
            }

            if (got_remote_cost)
            {
                fqp_preserve_top_join_path_candidates(joinrel,
                                                      join_path_candidates);
                elog(LOG, "mock_table: added remote-remote custom join paths for joinrel");
            }

            return;
        }
        else
        {
            if (is_mixed_local_remote)
            {
                elog(LOG,
                     "mock_table: mixed local-remote join has no remote source candidate; skipping generic remote EXPLAIN fallback (outer_dest_rti=%d inner_dest_rti=%d)",
                     outerRel,
                     innerRel);
                return;
            }
            else
            {
                sql = mock_deparse_join_sql(root,
                                            joinrel,
                                            outerrel,
                                            innerrel,
                                            jointype,
                                            (extra != NULL) ? extra->restrictlist : NIL,
                                            &supported);

                if (supported)
                    elog(LOG, "mock_table remote explain (join): EXPLAIN %s", sql);
                else
                    elog(LOG, "mock_table remote explain (join): deparse unsupported");

                got_remote_cost = mock_remote_explain_sql(sql,
                                                          &startup_cost,
                                                          &total_cost,
                                                          &plan_rows,
                                                          &plan_width);
            }
        }
    }

    if (got_remote_cost)
        elog(LOG,
             "mock_table remote parsed join cost used: startup=%.3f total=%.3f rows=%.0f width=%d",
             startup_cost,
             total_cost,
             (double) plan_rows,
             plan_width);

    if (supported && got_remote_cost)
    {
        movement_factor = mock_table_data_movement_factor();
        data_movement_cost = (Cost) (movement_factor * (double) plan_rows * (double) plan_width);
        total_cost += data_movement_cost;
    }

    cpath->path.startup_cost = startup_cost;
    cpath->path.total_cost = total_cost;
    cpath->path.rows = plan_rows;
    if (plan_width > 0)
        cpath->path.pathtarget->width = plan_width;
    cpath->flags = 0;
    cpath->custom_private = fqp_make_custom_private_join(dest_rti, (extra != NULL) ? extra->restrictlist : NIL);

    cpath->custom_paths = list_make2(outerrel->cheapest_total_path, innerrel->cheapest_total_path);
    cpath->methods = &exchange_path_methods;

    fqp_add_path_keep_interesting_dest(joinrel, (Path *) cpath);

    elog(LOG, "mock_table: added remote-remote custom join path for joinrel");
    if (supported && !got_remote_cost)
        elog(LOG, "mock_table: remote EXPLAIN failed for join, using fallback cost");
}

void _PG_init(void) {
    mock_table_define_comms_gucs();

    prev_get_rel_info_hook = get_relation_info_hook;
    prev_set_rel_pathlist_hook = set_rel_pathlist_hook;
    prev_set_join_pathlist_hook = set_join_pathlist_hook;
    prev_planner_hook = planner_hook;

    get_relation_info_hook = fqp_get_relation_info_hook; // hook to mimic remote table stats
    set_rel_pathlist_hook = fqp_set_rel_pathlist_hook; // hook for custom baserel scans
    set_join_pathlist_hook = fqp_set_join_pathlist_hook; // hook for custom join paths
    planner_hook = fqp_planner_hook; // per-root-query local remote EXPLAIN trace
}

void _PG_fini(void) {
    get_relation_info_hook = prev_get_rel_info_hook;
    set_rel_pathlist_hook = prev_set_rel_pathlist_hook;
    set_join_pathlist_hook = prev_set_join_pathlist_hook;
    planner_hook = prev_planner_hook;
}
