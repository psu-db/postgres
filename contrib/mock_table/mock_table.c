#include "postgres.h"
#include "fmgr.h"
#include "optimizer/plancat.h"
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
#include "parser/parsetree.h"
#include "parser/parse_relation.h"
#include "commands/explain.h"
#include "executor/executor.h"

#include <string.h>

#include "mock_table.h"

PG_MODULE_MAGIC;

static get_relation_info_hook_type prev_get_rel_info_hook = NULL;
static set_rel_pathlist_hook_type prev_set_rel_pathlist_hook = NULL;
static set_join_pathlist_hook_type prev_set_join_pathlist_hook = NULL;

static CustomPathMethods exchange_path_methods;

static bool is_remote_table(Oid relid);

static RangeTblEntry *
fqp_rt_fetch(PlannerInfo *root, Index rti)
{
    RangeTblEntry *rte;

    rte = NULL;
    if (root->simple_rte_array != NULL && rti < root->simple_rel_array_size)
        rte = root->simple_rte_array[rti];
    if (rte == NULL)
        rte = rt_fetch(rti, root->parse->rtable);

    return rte;
}

typedef struct FqpSourceCandidate
{
    char   *source;
    int		rti;
} FqpSourceCandidate;

static bool
fqp_parse_source_from_relname(const char *relname, char *source, int source_sz)
{
    const char *sep;
    int		 len;

    if (relname == NULL || source == NULL || source_sz <= 1)
        return false;

    sep = strchr(relname, '_');
    if (sep == NULL || sep == relname)
        return false;

    len = (int) (sep - relname);
    if (len >= source_sz)
        return false;

    memcpy(source, relname, len);
    source[len] = '\0';
    return true;
}

static bool
fqp_get_source_for_rte(RangeTblEntry *rte, char *source, int source_sz)
{
    char   *relname;

    if (rte == NULL || rte->rtekind != RTE_RELATION)
        return false;

    if (!is_remote_table(rte->relid))
        return false;

    relname = get_rel_name(rte->relid);
    if (relname == NULL)
        return false;

    return fqp_parse_source_from_relname(relname, source, source_sz);
}

static bool
fqp_source_exists(List *sources, const char *source)
{
    ListCell   *lc;

    foreach(lc, sources)
    {
        FqpSourceCandidate *cand = (FqpSourceCandidate *) lfirst(lc);

        if (strcmp(cand->source, source) == 0)
            return true;
    }

    return false;
}

static List *
fqp_collect_remote_sources(PlannerInfo *root, Relids relids)
{
    List   *sources = NIL;
    int		 member = -1;

    while ((member = bms_next_member(relids, member)) >= 0)
    {
        Index			 rti;
        RangeTblEntry *rte;
        char		 source[64];
        FqpSourceCandidate *cand;

        rti = (Index) member;
        rte = fqp_rt_fetch(root, rti);
        if (!fqp_get_source_for_rte(rte, source, sizeof(source)))
            continue;

        if (fqp_source_exists(sources, source))
            continue;

        cand = (FqpSourceCandidate *) palloc(sizeof(FqpSourceCandidate));
        cand->source = pstrdup(source);
        cand->rti = (int) rti;
        sources = lappend(sources, cand);
    }

    return sources;
}

static bool is_remote_table(Oid relid) {
    Oid namespaceId = get_rel_namespace(relid);
    char *schemaName = get_namespace_name(namespaceId);
    
    if (schemaName && strcmp(schemaName, "remote") == 0) {
        return true;
    }
    return false;
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

    // TODO: bring data from remote
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


static int
fqp_dest_rti_from_custom_private(List *custom_private)
{
    if (custom_private == NIL)
        return 0;

    Node *n = (Node *) linitial(custom_private);
    if (n == NULL || !IsA(n, Integer))
        return 0;

    // destination rti (0 -> local, other -> remote rti)
    return intVal(n);
}

static void
explain_exchange_scan(CustomScanState *node, List *ancestors, ExplainState *es)
{
    CustomScan  *cscan;
    int          dest_rti;
    int          remote_expr_count;
    bool         has_local_qual;
    const char  *dest_text;

    cscan = (CustomScan *) node->ss.ps.plan;
    dest_rti = fqp_dest_rti_from_custom_private(cscan->custom_private);
    remote_expr_count = list_length(cscan->custom_exprs);
    has_local_qual = (cscan->scan.plan.qual != NIL);

    if (dest_rti == 0)
        dest_text = "local";
    else
        dest_text = psprintf("remote (table_rti=%d)", dest_rti);

    ExplainPropertyText("FQP Annotation", dest_text, es);
    ExplainPropertyInteger("FQP Annotation RTI", NULL, dest_rti, es);
    ExplainPropertyInteger("FQP Remote Expr Count", NULL, remote_expr_count, es);
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

    /* All quals are expected to be evaluated remotely. */
    cscan->scan.plan.qual = NIL;
    cscan->scan.scanrelid = scanrelid;

    if (scanrelid == 0)
        cscan->custom_scan_tlist = tlist;
    else
        cscan->custom_exprs = extract_actual_clauses(clauses, false); // type mismatch if clauses directly stored

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
fqp_make_custom_private_dest_rti(int dest_rti)
{
    return list_make1(makeInteger(dest_rti));
}

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

static void fqp_set_rel_pathlist_hook(PlannerInfo *root, RelOptInfo *rel, Index rti, RangeTblEntry *rte) {
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
                elog(LOG, "mock_table remote explain (baserel rti=%d): %s", (int) rti, sql);
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
        data_movement_cost = (plan_rows > 0) ? (Cost) (movement_factor * (double) plan_rows * (double) plan_width) : 0.0;
        total_cost += data_movement_cost;

        cpath->path.rows = plan_rows;
        cpath->path.startup_cost = startup_cost;
        cpath->path.total_cost = total_cost;
        if (plan_width > 0)
            cpath->path.pathtarget->width = plan_width;
        
        cpath->flags = 0;
        cpath->custom_paths = NIL;

        // annotation - remote baserel - should I change this to string?
        cpath->custom_private = fqp_make_custom_private_dest_rti((int) rti);
        cpath->methods = &exchange_path_methods;

        add_path(rel, (Path *) cpath);

        elog(LOG, "mock_table: added remote baserel custom path for rti=%d", (int) rti);
    }
}

static void fqp_get_relation_info_hook(PlannerInfo *root, Oid relOid, bool inhparent, RelOptInfo *rel) {
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

static int
reloptinfo_dest_rti(PlannerInfo *root, RelOptInfo *rel)
{
    if (rel == NULL)
        return 0;

    if (IS_SIMPLE_REL(rel))
    {
        // rel must be a baserel
        Index rti = rel->relid;
        RangeTblEntry* rte = root->simple_rte_array[rti];
        if (rte->rtekind == RTE_RELATION && is_remote_table(rte->relid))
            return (int) rti;
        else
            return 0;
    }

    // For joinrel, use the cheapest path's annotation if it's one of our custom paths. otherwise assume local.
    if (rel->reloptkind == RELOPT_JOINREL) 
    {
        if (rel->cheapest_total_path && rel->cheapest_total_path->pathtype == T_CustomScan)
        {
            CustomPath *cp = (CustomPath *) rel->cheapest_total_path;
            return fqp_dest_rti_from_custom_private(cp->custom_private);
        }
    }
    
    return 0;
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
    Cost best_startup_cost;
    Cost best_total_cost;
    Cost data_movement_cost;
    double movement_factor;
    Cardinality plan_rows;
    Cardinality best_rows;
    int plan_width;
    int best_width;
    int dest_rti;
    int source_count;
    List *sources;
    ListCell *lc;

    if (prev_set_join_pathlist_hook)
        prev_set_join_pathlist_hook(root, joinrel, outerrel, innerrel, jointype, extra);

    outerRel = reloptinfo_dest_rti(root, outerrel);
    innerRel = reloptinfo_dest_rti(root, innerrel);

    if (outerRel == 0 && innerRel == 0) {
        elog(LOG, "mock_table: joinrel local-local, keeping core planner join paths");
        return; // both local, do nothing
    }

    if ((outerRel != 0 && innerRel == 0) || (outerRel == 0 && innerRel != 0)) {
        elog(LOG,
             "mock_table: joinrel mixed local-remote (outer_dest_rti=%d inner_dest_rti=%d), keeping core planner join paths; no cascade remote EXPLAIN in this branch",
             outerRel,
             innerRel);
        return;
    }
    
    // Both are remote
    
    // joinrel->pathlist = NIL;
    // joinrel->partial_pathlist = NIL;

    cpath = makeNode(CustomPath);
    cpath->path.pathtype = T_CustomScan;
    cpath->path.parent = joinrel;
    cpath->path.pathtarget = joinrel->reltarget;
    
    sql = NULL;
    supported = true;

    startup_cost = 2.0;
    total_cost = 50.0;
    plan_rows = joinrel->rows;
    plan_width = joinrel->reltarget->width;
    best_startup_cost = startup_cost;
    best_total_cost = total_cost;
    best_rows = plan_rows;
    best_width = plan_width;
    dest_rti = outerRel;
    got_remote_cost = false;
    sources = fqp_collect_remote_sources(root, joinrel->relids);
    source_count = list_length(sources);

    if (supported)
    {
        if (source_count > 1)
        {
            bool have_candidate = false;

            foreach(lc, sources)
            {
                FqpSourceCandidate *cand = (FqpSourceCandidate *) lfirst(lc);
                Cost cand_startup;
                Cost cand_total;
                Cardinality cand_rows;
                int cand_width;
                Cost cand_movement;

                cand_startup = startup_cost;
                cand_total = total_cost;
                cand_rows = plan_rows;
                cand_width = plan_width;

                sql = mock_deparse_join_sql_for_source(root,
                                                       joinrel,
                                                       outerrel,
                                                       innerrel,
                                                       jointype,
                                                       (extra != NULL) ? extra->restrictlist : NIL,
                                                       cand->source,
                                                       &supported);
                if (!supported)
                    continue;

                elog(LOG, "mock_table remote explain (join source=%s): EXPLAIN %s", cand->source, sql);

                if (!mock_remote_explain_sql_for_source(cand->source,
                                                        sql,
                                                        &cand_startup,
                                                        &cand_total,
                                                        &cand_rows,
                                                        &cand_width))
                    continue;

                cand_movement = (cand_rows > 0) ?
                    (Cost) (mock_table_data_movement_factor() * (double) cand_rows) : 0.0;
                cand_total += cand_movement;

                elog(LOG,
                     "mock_table remote parsed join candidate used (source=%s): startup=%.3f total=%.3f rows=%.0f width=%d movement=%.3f",
                     cand->source,
                     cand_startup,
                     cand_total,
                     (double) cand_rows,
                     cand_width,
                     cand_movement);

                if (!have_candidate || cand_total < best_total_cost)
                {
                    best_startup_cost = cand_startup;
                    best_total_cost = cand_total;
                    best_rows = cand_rows;
                    best_width = cand_width;
                    dest_rti = cand->rti;
                    have_candidate = true;
                }
            }

            got_remote_cost = have_candidate;
            startup_cost = best_startup_cost;
            total_cost = best_total_cost;
            plan_rows = best_rows;
            plan_width = best_width;
        }
        else if (source_count == 1)
        {
            FqpSourceCandidate *cand = (FqpSourceCandidate *) linitial(sources);

            sql = mock_deparse_join_sql_for_source(root,
                                                   joinrel,
                                                   outerrel,
                                                   innerrel,
                                                   jointype,
                                                   (extra != NULL) ? extra->restrictlist : NIL,
                                                   cand->source,
                                                   &supported);

            if (supported)
            {
                elog(LOG, "mock_table remote explain (join source=%s): EXPLAIN %s", cand->source, sql);
                got_remote_cost = mock_remote_explain_sql_for_source(cand->source,
                                                                      sql,
                                                                      &startup_cost,
                                                                      &total_cost,
                                                                      &plan_rows,
                                                                      &plan_width);
            }
            dest_rti = cand->rti;
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

    if (got_remote_cost)
        elog(LOG,
             "mock_table remote parsed join cost used: startup=%.3f total=%.3f rows=%.0f width=%d",
             startup_cost,
             total_cost,
             (double) plan_rows,
             plan_width);

    if (!(supported && source_count > 1 && got_remote_cost))
    {
        movement_factor = mock_table_data_movement_factor();
        data_movement_cost = (plan_rows > 0) ? (Cost) (movement_factor * (double) plan_rows) : 0.0;
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

    add_path(joinrel, (Path *) cpath);

    // set to cheapest path
    // joinrel->cheapest_total_path = (Path *) cpath;
    // joinrel->cheapest_startup_path = (Path *) cpath;

    elog(LOG, "mock_table: added remote-remote custom join path for joinrel");
    if (supported && !got_remote_cost)
        elog(LOG, "mock_table: remote EXPLAIN failed for join, using fallback cost");
}

void _PG_init(void) {
    mock_table_define_comms_gucs();

    prev_get_rel_info_hook = get_relation_info_hook;
    prev_set_rel_pathlist_hook = set_rel_pathlist_hook;
    prev_set_join_pathlist_hook = set_join_pathlist_hook;

    get_relation_info_hook = fqp_get_relation_info_hook; // hook to mimic remote table stats
    set_rel_pathlist_hook = fqp_set_rel_pathlist_hook; // hook for custom baserel scans
    set_join_pathlist_hook = fqp_set_join_pathlist_hook; // hook for custom join paths
}

void _PG_fini(void) {
    get_relation_info_hook = prev_get_rel_info_hook;
    set_rel_pathlist_hook = prev_set_rel_pathlist_hook;
    set_join_pathlist_hook = prev_set_join_pathlist_hook;
}
