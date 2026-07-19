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
#include "portability/instr_time.h"
#include "utils/ruleutils.h"
#include "utils/json.h"
#include "utils/memutils.h"

#include <stdio.h>
#include <string.h>
#include <float.h>

#include "mock_table.h"

PG_MODULE_MAGIC;

static get_relation_info_hook_type prev_get_rel_info_hook = NULL;
static set_rel_pathlist_hook_type prev_set_rel_pathlist_hook = NULL;
static set_join_pathlist_hook_type prev_set_join_pathlist_hook = NULL;
static planner_hook_type prev_planner_hook = NULL;

static CustomPathMethods exchange_path_methods;


#define FQP_LOCAL_EXPLAIN_TRACE_PATH "/Users/vishi/Desktop/DBGrp/repos/a_main/fqp_db_interface/tmp/fqp_pg_explain_profile.json"

static MemoryContext fqp_trace_context = NULL;
static StringInfo fqp_trace_items = NULL;
static bool fqp_trace_active = false;
static uint64 fqp_trace_root_seq = 0;
static uint64 fqp_trace_explain_count = 0;
static char fqp_trace_root_hash[17];
static char *fqp_trace_root_query = NULL;
static instr_time fqp_trace_start;

static bool is_remote_table(Oid relid);
static int fqp_dest_rti_from_custom_private(List *custom_private);
static bool fqp_is_local_candidate_source(const char *candidate_source);
static PlannedStmt *fqp_planner_hook(Query *parse,
                                     const char *query_string,
                                     int cursorOptions,
                                     ParamListInfo boundParams);

static void
fqp_trace_reset_state(void)
{
    fqp_trace_context = NULL;
    fqp_trace_items = NULL;
    fqp_trace_active = false;
    fqp_trace_explain_count = 0;
    fqp_trace_root_hash[0] = '\0';
    fqp_trace_root_query = NULL;
}

static uint64
fqp_fnv1a64(const char *str)
{
    uint64 hash = UINT64CONST(14695981039346656037);
    const unsigned char *p = (const unsigned char *) str;

    if (p == NULL)
        return hash;

    while (*p != '\0')
    {
        hash ^= (uint64) *p++;
        hash *= UINT64CONST(1099511628211);
    }

    return hash;
}

static void
fqp_hash_to_hex(uint64 hash, char *buf, Size bufsz)
{
    snprintf(buf, bufsz, "%016llx", (unsigned long long) hash);
}

static bool
fqp_append_json_array_record(const char *path, const char *record)
{
    FILE *fp;
    long end_pos;
    long close_bracket_pos;
    long pos;
    int ch;
    bool has_existing_records = false;

    fp = fopen(path, "r+");
    if (fp == NULL)
    {
        fp = fopen(path, "w");
        if (fp == NULL)
            return false;

        fprintf(fp, "[\n%s\n]\n", record);
        fclose(fp);
        return true;
    }

    if (fseek(fp, 0, SEEK_END) != 0)
    {
        fclose(fp);
        return false;
    }

    end_pos = ftell(fp);
    if (end_pos <= 0)
    {
        fclose(fp);
        fp = fopen(path, "w");
        if (fp == NULL)
            return false;
        fprintf(fp, "[\n%s\n]\n", record);
        fclose(fp);
        return true;
    }

    pos = end_pos - 1;
    while (pos >= 0)
    {
        if (fseek(fp, pos, SEEK_SET) != 0)
        {
            fclose(fp);
            return false;
        }

        ch = fgetc(fp);
        if (ch != ' ' && ch != '\n' && ch != '\r' && ch != '\t')
            break;
        pos--;
    }

    if (pos < 0 || ch != ']')
    {
        fclose(fp);
        fp = fopen(path, "w");
        if (fp == NULL)
            return false;
        fprintf(fp, "[\n%s\n]\n", record);
        fclose(fp);
        return true;
    }

    close_bracket_pos = pos;
    pos--;
    while (pos >= 0)
    {
        if (fseek(fp, pos, SEEK_SET) != 0)
        {
            fclose(fp);
            return false;
        }

        ch = fgetc(fp);
        if (ch != ' ' && ch != '\n' && ch != '\r' && ch != '\t')
            break;
        pos--;
    }
    has_existing_records = (pos >= 0 && ch != '[');

    if (fseek(fp, close_bracket_pos, SEEK_SET) != 0)
    {
        fclose(fp);
        return false;
    }

    fprintf(fp, "%s\n%s\n]\n", has_existing_records ? "," : "", record);
    fclose(fp);
    return true;
}

static void
fqp_trace_begin(const char *query_string)
{
    MemoryContext oldcontext;

    if (fqp_trace_active)
        return;

    oldcontext = MemoryContextSwitchTo(TopMemoryContext);
    fqp_trace_context = AllocSetContextCreate(TopMemoryContext,
                                              "mock_table local explain trace",
                                              ALLOCSET_DEFAULT_SIZES);
    MemoryContextSwitchTo(fqp_trace_context);

    fqp_trace_items = makeStringInfo();
    fqp_trace_root_query = pstrdup(query_string != NULL ? query_string : "");
    fqp_trace_root_seq++;
    fqp_trace_explain_count = 0;
    fqp_hash_to_hex(fqp_fnv1a64(fqp_trace_root_query),
                    fqp_trace_root_hash,
                    sizeof(fqp_trace_root_hash));
    INSTR_TIME_SET_CURRENT(fqp_trace_start);
    fqp_trace_active = true;

    MemoryContextSwitchTo(oldcontext);
}

void
mock_table_record_remote_explain(const char *target_source,
                                 const char *sql,
                                 bool ok,
                                 double elapsed_ms,
                                 Cost startup_cost,
                                 Cost total_cost,
                                 Cardinality rows,
                                 int width)
{
    MemoryContext oldcontext;
    char sql_hash[17];

    if (!fqp_trace_active || fqp_trace_context == NULL || fqp_trace_items == NULL)
        return;

    oldcontext = MemoryContextSwitchTo(fqp_trace_context);

    fqp_trace_explain_count++;
    fqp_hash_to_hex(fqp_fnv1a64(sql), sql_hash, sizeof(sql_hash));

    if (fqp_trace_items->len > 0)
        appendStringInfoChar(fqp_trace_items, ',');

    appendStringInfo(fqp_trace_items,
                     "{\"seq\":%llu,\"target_source_id\":",
                     (unsigned long long) fqp_trace_explain_count);
    escape_json(fqp_trace_items, target_source != NULL ? target_source : "");
    appendStringInfo(fqp_trace_items,
                     ",\"ok\":%s,\"elapsed_ms\":%.3f,"
                     "\"startup_cost\":%.6f,\"total_cost\":%.6f,"
                     "\"rows\":%.0f,\"width\":%d,\"sql_hash\":\"%s\",\"sql\":",
                     ok ? "true" : "false",
                     elapsed_ms,
                     (double) startup_cost,
                     (double) total_cost,
                     (double) rows,
                     width,
                     sql_hash);
    escape_json(fqp_trace_items, sql != NULL ? sql : "");
    appendStringInfoChar(fqp_trace_items, '}');

    MemoryContextSwitchTo(oldcontext);
}

static void
fqp_trace_finish(bool ok)
{
    MemoryContext oldcontext;
    StringInfoData line;
    instr_time duration;
    double elapsed_ms;

    if (!fqp_trace_active)
        return;

    if (fqp_trace_explain_count == 0)
    {
        MemoryContextDelete(fqp_trace_context);
        fqp_trace_reset_state();
        return;
    }

    INSTR_TIME_SET_CURRENT(duration);
    INSTR_TIME_SUBTRACT(duration, fqp_trace_start);
    elapsed_ms = INSTR_TIME_GET_MILLISEC(duration);

    oldcontext = MemoryContextSwitchTo(fqp_trace_context);
    initStringInfo(&line);
    appendStringInfo(&line,
                     "{\"event\":\"local_explain_trace\","
                     "\"source_id\":");
    escape_json(&line, mock_table_local_source_id());
    appendStringInfo(&line,
                     ",\"pid\":%d,\"root_query_seq\":%llu,"
                     "\"root_sql_hash\":\"%s\",\"ok\":%s,"
                     "\"elapsed_ms\":%.3f,\"remote_explain_count\":%llu,"
                     "\"root_query\":",
                     MyProcPid,
                     (unsigned long long) fqp_trace_root_seq,
                     fqp_trace_root_hash,
                     ok ? "true" : "false",
                     elapsed_ms,
                     (unsigned long long) fqp_trace_explain_count);
    escape_json(&line, fqp_trace_root_query != NULL ? fqp_trace_root_query : "");
    appendStringInfo(&line,
                     ",\"remote_explains\":[%s]}",
                     fqp_trace_items->data);

    if (!fqp_append_json_array_record(FQP_LOCAL_EXPLAIN_TRACE_PATH, line.data))
        elog(LOG,
             "mock_table local explain trace: could not append to %s",
             FQP_LOCAL_EXPLAIN_TRACE_PATH);

    MemoryContextSwitchTo(oldcontext);
    MemoryContextDelete(fqp_trace_context);
    fqp_trace_reset_state();
}

static PlannedStmt *
fqp_planner_hook(Query *parse,
                 const char *query_string,
                 int cursorOptions,
                 ParamListInfo boundParams)
{
    PlannedStmt *result = NULL;
    bool started_trace = false;

    if (!fqp_trace_active)
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

static bool
fqp_source_rti_exists(List *sources, int rti)
{
    ListCell   *lc;

    foreach(lc, sources)
    {
        FqpSourceCandidate *cand = (FqpSourceCandidate *) lfirst(lc);

        if (cand->rti == rti)
            return true;
    }

    return false;
}

static bool
fqp_get_source_for_rti(PlannerInfo *root, Index rti, char *source, int source_sz)
{
    if (root == NULL || rti <= 0)
        return false;

    return fqp_get_source_for_rte(fqp_rt_fetch(root, rti), source, source_sz);
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
    if (!IsA(n, Integer))
        return 0;

    // destination rti (0 -> local, other -> remote rti)
    return intVal(n);
}

static bool
fqp_path_dest_rti(Path *path, int *dest_rti)
{
    CustomPath *cp;
    int         rti;

    if (path == NULL || path->pathtype != T_CustomScan)
        return false;

    cp = (CustomPath *) path;
    rti = fqp_dest_rti_from_custom_private(cp->custom_private);
    if (rti <= 0)
        return false;

    if (dest_rti != NULL)
        *dest_rti = rti;

    return true;
}

static Path *
fqp_best_path_for_source(PlannerInfo *root, RelOptInfo *rel, const char *source)
{
    ListCell   *lc;
    Path       *best_path;
    int         path_dest_rti;
    char        path_source[64];

    if (root == NULL || rel == NULL || source == NULL || source[0] == '\0')
        return NULL;

    best_path = NULL;
    foreach(lc, rel->pathlist)
    {
        Path *path = (Path *) lfirst(lc);

        if (!fqp_path_dest_rti(path, &path_dest_rti))
            continue;

        path_source[0] = '\0';
        if (!fqp_get_source_for_rti(root, (Index) path_dest_rti, path_source, sizeof(path_source)))
            continue;

        if (strcmp(path_source, source) != 0)
            continue;

        if (best_path == NULL || compare_path_costs(path, best_path, TOTAL_COST) < 0)
            best_path = path;
    }

    return best_path;
}

static void
fqp_add_path_keep_interesting_dest(RelOptInfo *rel, Path *path)
{
    /*
     * PostgreSQL does not know that FQP destination/source is a physical
     * property. A path that is dominated on local cost can still be the only
     * path at a useful remote destination for an upper join.
     *
     * Do not call add_path() here: when it rejects a path it also frees it.
     * Keep these paths explicitly and let set_cheapest() choose the cheapest
     * path later while upper FQP joins can still inspect all destinations.
     */
    rel->pathlist = lappend(rel->pathlist, path);
    elog(LOG,
         "mock_table: preserved FQP destination path for upper joins");
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

    // Fallback only. Join enumeration below scans all FQP paths for destinations.
    if (rel->reloptkind == RELOPT_JOINREL) 
    {
        int dest_rti;

        if (fqp_path_dest_rti(rel->cheapest_total_path, &dest_rti))
            return dest_rti;
    }
    
    return 0;
}

static void
fqp_add_source_candidate_for_rti(PlannerInfo *root,
                                 List **sources,
                                 bool *has_local_candidate,
                                 int rti)
{
    char source[64];
    FqpSourceCandidate *cand;

    if (rti <= 0 || fqp_source_rti_exists(*sources, rti))
        return;

    source[0] = '\0';
    if (!fqp_get_source_for_rti(root, (Index) rti, source, sizeof(source)))
        return;

    if (fqp_is_local_candidate_source(source))
    {
        *has_local_candidate = true;
        return;
    }

    if (fqp_source_exists(*sources, source))
        return;

    cand = (FqpSourceCandidate *) palloc(sizeof(FqpSourceCandidate));
    cand->source = pstrdup(source);
    cand->rti = rti;
    *sources = lappend(*sources, cand);
}

static void
fqp_collect_source_candidates_from_rel(PlannerInfo *root,
                                       RelOptInfo *rel,
                                       List **sources,
                                       bool *has_local_candidate)
{
    ListCell   *lc;

    if (rel == NULL)
        return;

    if (IS_SIMPLE_REL(rel))
    {
        fqp_add_source_candidate_for_rti(root,
                                         sources,
                                         has_local_candidate,
                                         reloptinfo_dest_rti(root, rel));
        return;
    }

    foreach(lc, rel->pathlist)
    {
        Path *path = (Path *) lfirst(lc);
        int   dest_rti;

        if (!fqp_path_dest_rti(path, &dest_rti))
            continue;

        fqp_add_source_candidate_for_rti(root,
                                         sources,
                                         has_local_candidate,
                                         dest_rti);
    }
}

static bool
fqp_is_final_joinrel(PlannerInfo *root, RelOptInfo *joinrel)
{
    if (root == NULL || joinrel == NULL)
        return false;

    if (joinrel->relids == NULL || root->all_baserels == NULL)
        return false;

    // If the bitmaps match directly, it's the final joinrel.
    if (bms_is_subset(root->all_baserels, joinrel->relids))
    {
        elog(LOG, "fqp_is_final_joinrel: Fast path hit. root->all_baserels is subset of joinrel->relids.");
        return true;
    }

    return false;
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
    Cost data_movement_cost;
    double movement_factor;
    Cardinality plan_rows;
    int plan_width;
    int dest_rti;
    int source_count;
    bool is_mixed_local_remote;
    bool has_local_candidate = false;
    List *sources;
    ListCell *lc;

    if (prev_set_join_pathlist_hook)
        prev_set_join_pathlist_hook(root, joinrel, outerrel, innerrel, jointype, extra);

    if (fqp_is_final_joinrel(root, joinrel)) { // final sink, no changes
        elog(LOG, "mock_table: final joinrel detected, keeping core planner join paths");
        return;
    }

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

                fqp_add_path_keep_interesting_dest(joinrel, (Path *) cand_path);
                got_remote_cost = true;
            }

            if (got_remote_cost)
                elog(LOG, "mock_table: added remote-remote custom join paths for joinrel");

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
