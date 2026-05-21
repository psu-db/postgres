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
#include "utils/ruleutils.h"

#include <string.h>

#include "mock_table.h"

PG_MODULE_MAGIC;

// #define FQP_MAX_LOCAL_ROWS_FOR_REMOTE_PROBE 10000.0

static get_relation_info_hook_type prev_get_rel_info_hook = NULL;
static set_rel_pathlist_hook_type prev_set_rel_pathlist_hook = NULL;
static set_join_pathlist_hook_type prev_set_join_pathlist_hook = NULL;

static CustomPathMethods exchange_path_methods;

static bool is_remote_table(Oid relid);
static int fqp_dest_rti_from_custom_private(List *custom_private);

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

typedef struct FqpRelSiteInfo
{
    int     dest_rti;
    char    source[64];
    bool    has_remote_site;
} FqpRelSiteInfo;

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

static bool
fqp_get_source_for_rti(PlannerInfo *root, Index rti, char *source, int source_sz)
{
    if (root == NULL || source == NULL || source_sz <= 1 || rti <= 0)
        return false;

    return fqp_get_source_for_rte(fqp_rt_fetch(root, rti), source, source_sz);
}

static bool
fqp_get_source_for_rel(PlannerInfo *root, RelOptInfo *rel, FqpRelSiteInfo *site)
{
    if (site == NULL)
        return false;

    site->dest_rti = 0;
    site->source[0] = '\0';
    site->has_remote_site = false;

    if (root == NULL || rel == NULL)
        return false;

    if (IS_SIMPLE_REL(rel))
    {
        if (fqp_get_source_for_rti(root, rel->relid, site->source, sizeof(site->source)))
        {
            site->dest_rti = (int) rel->relid;
            site->has_remote_site = true;
            return true;
        }

        return false;
    }

    if (rel->reloptkind == RELOPT_JOINREL &&
        rel->cheapest_total_path != NULL &&
        rel->cheapest_total_path->pathtype == T_CustomScan)
    {
        CustomPath *cp = (CustomPath *) rel->cheapest_total_path;

        site->dest_rti = fqp_dest_rti_from_custom_private(cp->custom_private);
        if (site->dest_rti <= 0)
            return false;

        if (fqp_get_source_for_rti(root, (Index) site->dest_rti, site->source, sizeof(site->source)))
        {
            site->has_remote_site = true;
            return true;
        }

        site->dest_rti = 0;
    }

    return false;
}

static bool
fqp_candidate_source_exists(PlannerInfo *root, int *candidate_dests, int candidate_count, const char *source)
{
    int i;

    if (root == NULL || candidate_dests == NULL || source == NULL || source[0] == '\0')
        return false;

    for (i = 0; i < candidate_count; i++)
    {
        int existing_dest_rti;
        char existing_source[64];

        existing_dest_rti = candidate_dests[i];
        if (existing_dest_rti <= 0)
            continue;

        existing_source[0] = '\0';
        if (!fqp_get_source_for_rti(root, (Index) existing_dest_rti, existing_source, sizeof(existing_source)))
            continue;

        if (strcmp(existing_source, source) == 0)
            return true;
    }

    return false;
}

static bool
fqp_requires_data_movement(bool rel_remote,
                           const FqpRelSiteInfo *rel_site,
                           int candidate_dest_rti,
                           const char *candidate_source)
{
    if (!rel_remote)
        return (candidate_dest_rti != 0);

    if (candidate_dest_rti == 0)
        return true;

    if (rel_site == NULL || rel_site->source[0] == '\0')
        return true;

    if (candidate_source == NULL || candidate_source[0] == '\0')
        return true;

    return strcmp(rel_site->source, candidate_source) != 0;
}

static Cost
fqp_data_movement_cost(Cardinality rows, int width)
{
    double factor;

    if (rows <= 0 || width <= 0)
        return 0.0;

    factor = mock_table_data_movement_factor();
    return (Cost) (factor * (double) rows * (double) width);
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
    useprefix = true;//(es->rtable_size > 1 || es->verbose);

    foreach(lc, cscan->custom_exprs)
    {
        Node *expr = (Node *) lfirst(lc);

        if (expr != NULL)
            remote_filters = lappend(remote_filters,
                                     deparse_expression(expr, dpcontext, useprefix, false));
    }

    if (cscan->custom_private != NIL && list_length(cscan->custom_private) > 1)
    {
        List *restrictlist = (List *) lsecond(cscan->custom_private);

        if (restrictlist != NIL)
        {
            List *actual_clauses = get_actual_clauses(restrictlist);

            foreach(lc, actual_clauses)
            {
                Node *expr = (Node *) lfirst(lc);

                if (expr != NULL)
                    remote_filters = lappend(remote_filters,
                                             deparse_expression(expr, dpcontext, useprefix, false));
            }
        }
    }

    foreach(lc, cscan->custom_scan_tlist)
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

    ExplainPropertyText("FQP Annotation", dest_text, es);
    ExplainPropertyText("FQP Scan Kind", scan_kind, es);
    // ExplainPropertyText("FQP Annotation Source", has_dest_source ? dest_source : (dest_rti == 0 ? "local" : "unknown"), es);
    // ExplainPropertyInteger("FQP Annotation RTI", NULL, dest_rti, es);
    ExplainPropertyInteger("FQP Remote Expr Count", NULL, remote_expr_count, es);
    ExplainPropertyInteger("FQP Remote Projection Count", NULL, remote_projection_count, es);
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
                // elog(LOG, "mock_table remote explain (baserel rti=%d): %s", (int) rti, sql);
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

static bool
fqp_is_final_joinrel(PlannerInfo *root, RelOptInfo *joinrel)
{
    int member = -1;

    if (root == NULL || joinrel == NULL)
        return false;

    if (joinrel->relids == NULL || root->all_baserels == NULL)
        return false;

    /* * Fast path: If the bitmaps match directly, it's definitively the final joinrel.
     * This handles queries that don't involve mixed-schema table mappings.
     */
    if (bms_is_subset(root->all_baserels, joinrel->relids))
    {
        elog(LOG, "fqp_is_final_joinrel: Fast path hit. root->all_baserels is subset of joinrel->relids.");
        return true;
    }

    elog(LOG, "fqp_is_final_joinrel: Fast path failed. Falling back to schema-agnostic name matching.");

    /* * Federated Schema-Agnostic Path: 
     * Check if every base relation in the query root has a corresponding relation 
     * with the same base table name in the joinrel, ignoring the schema.
     */
    while ((member = bms_next_member(root->all_baserels, member)) >= 0)
    {
        RangeTblEntry *rte_root = fqp_rt_fetch(root, (Index) member);
        char *root_relname;
        bool found_match = false;
        int join_member = -1;

        /* Only process actual relations */
        if (rte_root == NULL || rte_root->rtekind != RTE_RELATION)
            continue;

        root_relname = get_rel_name(rte_root->relid);
        if (root_relname == NULL)
            continue;

        elog(LOG, "fqp_is_final_joinrel: Checking root RTI %d (table: %s)", member, root_relname);

        /* Search the joinrel for a table with the identical unqualified name */
        while ((join_member = bms_next_member(joinrel->relids, join_member)) >= 0)
        {
            RangeTblEntry *rte_join = fqp_rt_fetch(root, (Index) join_member);
            char *join_relname;

            if (rte_join == NULL || rte_join->rtekind != RTE_RELATION)
                continue;

            join_relname = get_rel_name(rte_join->relid);
            if (join_relname == NULL)
                continue;

            elog(LOG, "fqp_is_final_joinrel:   Comparing against joinrel RTI %d (table: %s)", join_member, join_relname);

            if (strcmp(root_relname, join_relname) == 0)
            {
                elog(LOG, "fqp_is_final_joinrel:   -> Match found! (root RTI %d == joinrel RTI %d by name %s)", member, join_member, root_relname);
                found_match = true;
                break; /* Move on to the next root relation */
            }
        }

        /* * If we found a table in the query root that is NOT represented 
         * by name in this joinrel, it is not the final join.
         */
        if (!found_match)
        {
            elog(LOG, "fqp_is_final_joinrel: Root table %s (RTI %d) NOT found in joinrel. Returning false.", root_relname, member);
            return false;
        }
    }

    elog(LOG, "fqp_is_final_joinrel: All root relations found in joinrel by name. Returning true.");
    return true;
}

static bool
fqp_is_local_candidate_source(const char *candidate_source)
{
    const char *local_source;

    if (candidate_source == NULL || candidate_source[0] == '\0')
        return false;

    local_source = mock_table_local_source_id();
    elog(LOG, "Local and candidate sources: %s vs %s", local_source, candidate_source);
    if (local_source == NULL || local_source[0] == '\0')
        return false;

    return strcmp(local_source, candidate_source) == 0;
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
    bool is_mixed_local_remote;
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

    if (fqp_is_final_joinrel(root, joinrel)) {
        elog(LOG, "mock_table: final joinrel detected, keeping core planner join paths");
        return;
    }

    is_mixed_local_remote = ((outerRel != 0 && innerRel == 0) ||
                             (outerRel == 0 && innerRel != 0));

    // if (is_mixed_local_remote) {
    //     double local_rows;

    //     elog(LOG,
    //          "mock_table: joinrel mixed local-remote (outer_dest_rti=%d inner_dest_rti=%d), evaluating remote probe candidate",
    //          outerRel,
    //          innerRel);

    //     local_rows = (outerRel == 0) ? outerrel->rows : innerrel->rows;
    //     if (local_rows > FQP_MAX_LOCAL_ROWS_FOR_REMOTE_PROBE)
    //     {
    //         elog(LOG,
    //              "mock_table: local relation too large (%.0f rows) to push to remote, skipping remote EXPLAIN",
    //              local_rows);
    //         return;
    //     }
    // }
    

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
    dest_rti = (outerRel != 0) ? outerRel : innerRel;
    got_remote_cost = false;
    sources = NIL;
    source_count = 0;

    if (outerRel > 0)
    {
        char outer_source[64];

        if (fqp_get_source_for_rti(root, (Index) outerRel, outer_source, sizeof(outer_source)))
        {
            FqpSourceCandidate *cand = (FqpSourceCandidate *) palloc(sizeof(FqpSourceCandidate));

            cand->source = pstrdup(outer_source);
            cand->rti = outerRel;
            sources = lappend(sources, cand);
        }
    }

    if (innerRel > 0)
    {
        char inner_source[64];

        if (fqp_get_source_for_rti(root, (Index) innerRel, inner_source, sizeof(inner_source)) &&
            !fqp_source_exists(sources, inner_source))
        {
            FqpSourceCandidate *cand = (FqpSourceCandidate *) palloc(sizeof(FqpSourceCandidate));

            cand->source = pstrdup(inner_source);
            cand->rti = innerRel;
            sources = lappend(sources, cand);
        }
    }

    source_count = list_length(sources);

    // elog(LOG,
    //      "mock_table: joinrel candidate source scope restricted to annotated outer/inner rels (count=%d)",
    //      source_count);

    if (supported)
    {
        // children have different annotations
        if (source_count > 1)
        {
            bool have_candidate = false;
            bool saw_nonlocal_candidate = false;

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

                if (fqp_is_local_candidate_source(cand->source))
                {
                    elog(LOG,
                         "mock_table: skipping self-source join probe candidate (source=%s)",
                         cand->source);
                    continue;
                }

                saw_nonlocal_candidate = true;

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

            if (!saw_nonlocal_candidate)
            {
                elog(LOG,
                     "mock_table: all join probe candidates are local/self; keeping core planner join paths");
                return;
            }

            got_remote_cost = have_candidate;
            startup_cost = best_startup_cost;
            total_cost = best_total_cost;
            plan_rows = best_rows;
            plan_width = best_width;
        }
        // children have same annotation
        else if (source_count == 1)
        {
            FqpSourceCandidate *cand = (FqpSourceCandidate *) linitial(sources);

            if (fqp_is_local_candidate_source(cand->source))
            {
                elog(LOG,
                     "mock_table: only join probe candidate is local/self (source=%s); keeping core planner join paths",
                     cand->source);
                return;
            }

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
            if (is_mixed_local_remote)
            {
                elog(LOG,
                     "mock_table: mixed local-remote join has no remote source candidate; skipping generic remote EXPLAIN fallback (outer_dest_rti=%d inner_dest_rti=%d)",
                     outerRel,
                     innerRel);
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

    if (supported && source_count >= 1 && got_remote_cost)
    {
        movement_factor = mock_table_data_movement_factor();
        data_movement_cost = (plan_rows > 0) ? (Cost) (movement_factor * (double) plan_rows) : 0.0;
        total_cost += data_movement_cost;
    }

    // {
    //     Cost child_startup = 0.0;
    //     Cost child_total = 0.0;

    //     if (outerrel != NULL && outerrel->cheapest_total_path != NULL)
    //     {
    //         child_startup += outerrel->cheapest_total_path->startup_cost;
    //         child_total += outerrel->cheapest_total_path->total_cost;
    //     }

    //     if (innerrel != NULL && innerrel->cheapest_total_path != NULL)
    //     {
    //         child_startup += innerrel->cheapest_total_path->startup_cost;
    //         child_total += innerrel->cheapest_total_path->total_cost;
    //     }

    //     cpath->path.startup_cost = startup_cost + child_startup;
    //     cpath->path.total_cost = total_cost + child_total;
    // }
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
