#include "postgres.h"
#include "fmgr.h"
#include "optimizer/plancat.h"
#include "optimizer/pathnode.h"
#include "optimizer/cost.h"
#include "optimizer/optimizer.h"
#include "catalog/namespace.h"
#include "utils/lsyscache.h"
#include "nodes/extensible.h"
#include "nodes/makefuncs.h"
#include "optimizer/paths.h"
#include "parser/parsetree.h"
#include "commands/explain.h"
#include "executor/executor.h"

#include "mock_table.h"

PG_MODULE_MAGIC;

static get_relation_info_hook_type prev_get_rel_info_hook = NULL;
static set_rel_pathlist_hook_type prev_set_rel_pathlist_hook = NULL;
static set_join_pathlist_hook_type prev_set_join_pathlist_hook = NULL;

static CustomPathMethods exchange_path_methods;

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

    if (eflags & EXEC_FLAG_EXPLAIN_ONLY)
        return;

    // TODO: bring data from remote
    elog(ERROR, "Execution reached local mock node. FQP Orchestrator failed to intercept the plan.");
}
static TupleTableSlot *exec_exchange_scan(CustomScanState *node) {}
static void end_exchange_scan(CustomScanState *node) {}
static void rescan_exchange_scan(CustomScanState *node) {}


static int
fqp_dest_rti_from_custom_private(List *custom_private)
{
    if (!custom_private == NIL ||  list_length(custom_private) != 1)
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
    const char  *dest_text;

    cscan = (CustomScan *) node->ss.ps.plan;
    dest_rti = fqp_dest_rti_from_custom_private(cscan->custom_private);

    if (dest_rti == 0)
        dest_text = "local";
    else
        dest_text = psprintf("remote (table_rti=%d)", dest_rti);

    ExplainPropertyText("FQP Annotation", dest_text, es);
    ExplainPropertyInteger("FQP Annotation RTI", NULL, dest_rti, es);
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
    cscan->scan.plan.qual = clauses;
    cscan->scan.scanrelid = scanrelid;

    if (scanrelid == 0)
        cscan->custom_scan_tlist = tlist;

    // propagate estimates so explain shows rows/width
    cscan->scan.plan.plan_rows = best_path->path.rows;
    cscan->scan.plan.plan_width = best_path->path.pathtarget->width;
    cscan->flags = best_path->flags;
    cscan->methods = &exchange_scan_methods;

    /* Carry any planner-time private data through to execution. */
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

static void fqp_set_rel_pathlist_hook(PlannerInfo *root, RelOptInfo *rel, Index rti, RangeTblEntry *rte) {
    if (prev_set_rel_pathlist_hook) {
        prev_set_rel_pathlist_hook(root, rel, rti, rte);
    }

    if (is_remote_table(rte->relid)) {
        rel->pathlist = NIL;
        rel->partial_pathlist = NIL;

        CustomPath *cpath = makeNode(CustomPath);
        cpath->path.pathtype = T_CustomScan;
        cpath->path.parent = rel;
        cpath->path.pathtarget = rel->reltarget;

        // TODO: invoke explain to remote
        cpath->path.rows = rel->rows;
        cpath->path.startup_cost = 150.0; 
        cpath->path.total_cost = 150.0 + (rel->tuples * 0.05); 
        
        cpath->flags = 0;
        cpath->custom_paths = NIL;

        // annotation - remote baserel - should I change this to string?
        cpath->custom_private = fqp_make_custom_private_dest_rti((int) rti);
        cpath->methods = &exchange_path_methods;

        add_path(rel, (Path *) cpath);
    }
}

static void fqp_get_relation_info_hook(PlannerInfo *root, Oid relOid, bool inhparent, RelOptInfo *rel) {

    if (prev_get_rel_info_hook) {
        prev_get_rel_info_hook(root, relOid, inhparent, rel);
    }

    if (is_remote_table(relOid)) {
        // TODO: get this from explain on remote baserels
        rel->tuples = 6000000.0; 
        rel->pages = 50000;
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
        RangeTblEntry* rte = root->simple_rte_array[rti]
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
    if (prev_set_join_pathlist_hook)
        prev_set_join_pathlist_hook(root, joinrel, outerrel, innerrel, jointype, extra);

    outerRel = reloptinfo_dest_rti(root, outerrel);
    innerRel = reloptinfo_dest_rti(root, innerrel);

    if (outerRel == 0 && innerRel) == 0) {
        // annotate as local
        // how to add the annotation?
        return; // both local, do nothing
    }

    if (outerRel != 0 && innerRel == 0 || outerRel == 0 && innerRel != 0) {
        // one of them is remote, the other is local, we can still use regular join path but with annotation
        return;
    }
    
    // Both are remote

    joinrel->pathlist = NIL;
    joinrel->partial_pathlist = NIL;

    CustomPath *cpath = makeNode(CustomPath);
    cpath->path.pathtype = T_CustomScan;
    cpath->path.parent = joinrel;
    cpath->path.pathtarget = joinrel->reltarget;
    
    // TODO: issue explain
    cpath->path.startup_cost = 200.0;
    cpath->path.total_cost = 2000.0;
    cpath->path.rows = 1000000;
    cpath->custom_private = fqp_make_custom_private_dest_rti(outerRel); // or innerRel, based on cheaper dest
    // cpath->flags = 0;
    cpath->custom_paths = list_make2(outerrel->cheapest_total_path, innerrel->cheapest_total_path);
    cpath->methods = &exchange_path_methods;

    add_path(joinrel, (Path *) cpath);

    // set to cheapest path
    joinrel->cheapest_total_path = (Path *) cpath;
    joinrel->cheapest_startup_path = (Path *) cpath;
}

void _PG_init(void) {
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
