#include "postgres.h"

#include "catalog/namespace.h"
#include "nodes/makefuncs.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "parser/parsetree.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"

#include <string.h>

#include "mock_table.h"
#include "fqp_path_utils.h"

/*
 * Experimental top-k annotation propagation.
 *
 * Keep only the cheapest k FQP destination annotations at each joinrel. With
 * three sites this keeps at most one useful annotation per sink/source in the
 * common case, while bounding the amount of state that can flow upward through
 * the DP. Set to 0 to preserve every FQP destination candidate.
 */
#define FQP_JOIN_ANNOTATION_TOP_K 3

typedef struct FqpJoinPathCandidate
{
    CustomPath *path;
    char       *source;
} FqpJoinPathCandidate;

static bool fqp_is_local_candidate_source(const char *candidate_source);

RangeTblEntry *
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

static bool
fqp_parse_source_from_relname(const char *relname, char *source, int source_sz)
{
    const char *sep;
    int         len;

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

bool
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

bool
is_remote_table(Oid relid)
{
    Oid namespaceId = get_rel_namespace(relid);
    char *schemaName = get_namespace_name(namespaceId);

    if (schemaName && strcmp(schemaName, "remote") == 0)
        return true;
    return false;
}

int
fqp_dest_rti_from_custom_private(List *custom_private)
{
    Node *n;

    if (custom_private == NIL)
        return 0;

    n = (Node *) linitial(custom_private);
    if (!IsA(n, Integer))
        return 0;

    return intVal(n);
}

bool
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

Path *
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

void
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

void
fqp_add_ranked_join_path_candidate(List **candidates,
                                   CustomPath *path,
                                   const char *source)
{
    FqpJoinPathCandidate *candidate;
    List       *ranked;
    ListCell   *lc;
    bool        inserted;

    if (candidates == NULL || path == NULL)
        return;

    candidate = (FqpJoinPathCandidate *) palloc(sizeof(FqpJoinPathCandidate));
    candidate->path = path;
    candidate->source = pstrdup((source != NULL) ? source : "unknown");

#if FQP_JOIN_ANNOTATION_TOP_K <= 0
    *candidates = lappend(*candidates, candidate);
    return;
#endif

    ranked = NIL;
    inserted = false;

    foreach(lc, *candidates)
    {
        FqpJoinPathCandidate *existing = (FqpJoinPathCandidate *) lfirst(lc);

        if (!inserted &&
            compare_path_costs((Path *) path,
                               (Path *) existing->path,
                               TOTAL_COST) < 0)
        {
            ranked = lappend(ranked, candidate);
            inserted = true;
        }

        ranked = lappend(ranked, existing);
    }

    if (!inserted)
        ranked = lappend(ranked, candidate);

    *candidates = ranked;
}

void
fqp_preserve_top_join_path_candidates(RelOptInfo *joinrel, List *candidates)
{
    ListCell   *lc;
    int         kept;
    int         total;

    kept = 0;
    total = list_length(candidates);

    foreach(lc, candidates)
    {
        FqpJoinPathCandidate *candidate = (FqpJoinPathCandidate *) lfirst(lc);

#if FQP_JOIN_ANNOTATION_TOP_K > 0
        if (kept >= FQP_JOIN_ANNOTATION_TOP_K)
        {
            elog(LOG,
                 "mock_table: top-k join annotation pruning dropped destination source=%s total=%.3f",
                 candidate->source,
                 candidate->path->path.total_cost);
            continue;
        }
#endif

        fqp_add_path_keep_interesting_dest(joinrel, (Path *) candidate->path);
        kept++;
    }

#if FQP_JOIN_ANNOTATION_TOP_K > 0
    if (total > FQP_JOIN_ANNOTATION_TOP_K)
        elog(LOG,
             "mock_table: top-k join annotation propagation kept %d of %d candidate paths (k=%d)",
             kept,
             total,
             FQP_JOIN_ANNOTATION_TOP_K);
#endif
}

int
reloptinfo_dest_rti(PlannerInfo *root, RelOptInfo *rel)
{
    if (rel == NULL)
        return 0;

    if (IS_SIMPLE_REL(rel))
    {
        Index rti = rel->relid;
        RangeTblEntry* rte = root->simple_rte_array[rti];

        if (rte->rtekind == RTE_RELATION && is_remote_table(rte->relid))
            return (int) rti;
        else
            return 0;
    }

    if (rel->reloptkind == RELOPT_JOINREL)
    {
        int dest_rti;

        if (fqp_path_dest_rti(rel->cheapest_total_path, &dest_rti))
            return dest_rti;
    }

    return 0;
}

bool
fqp_rel_has_sink_local_path(PlannerInfo *root, RelOptInfo *rel)
{
    ListCell   *lc;

    if (root == NULL || rel == NULL)
        return false;

    if (IS_SIMPLE_REL(rel))
    {
        RangeTblEntry *rte;
        char source[64];

        rte = fqp_rt_fetch(root, rel->relid);
        if (rte == NULL || rte->rtekind != RTE_RELATION)
            return false;

        if (!is_remote_table(rte->relid))
            return true;

        source[0] = '\0';
        if (fqp_get_source_for_rte(rte, source, sizeof(source)) &&
            fqp_is_local_candidate_source(source))
            return true;

        return false;
    }

    foreach(lc, rel->pathlist)
    {
        Path *path = (Path *) lfirst(lc);
        int   dest_rti;
        char  source[64];

        /*
         * Non-FQP paths are ordinary PostgreSQL paths and therefore execute
         * locally in this optimizer instance.
         */
        if (!fqp_path_dest_rti(path, &dest_rti))
            return true;

        source[0] = '\0';
        if (fqp_get_source_for_rti(root, (Index) dest_rti, source, sizeof(source)) &&
            fqp_is_local_candidate_source(source))
            return true;
    }

    return false;
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

void
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

bool
fqp_is_final_joinrel(PlannerInfo *root, RelOptInfo *joinrel)
{
    if (root == NULL || joinrel == NULL)
        return false;

    if (joinrel->relids == NULL || root->all_baserels == NULL)
        return false;

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
