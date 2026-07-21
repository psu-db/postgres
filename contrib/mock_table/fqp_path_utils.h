#ifndef FQP_PATH_UTILS_H
#define FQP_PATH_UTILS_H

#include "postgres.h"

#include "nodes/extensible.h"
#include "nodes/pathnodes.h"

typedef struct FqpSourceCandidate
{
    char   *source;
    int     rti;
} FqpSourceCandidate;

extern RangeTblEntry *fqp_rt_fetch(PlannerInfo *root, Index rti);
extern bool is_remote_table(Oid relid);
extern bool fqp_get_source_for_rte(RangeTblEntry *rte, char *source, int source_sz);
extern int fqp_dest_rti_from_custom_private(List *custom_private);
extern void fqp_add_ranked_join_path_candidate(List **candidates,
                                               CustomPath *path,
                                               const char *source);
extern void fqp_preserve_top_join_path_candidates(RelOptInfo *joinrel, List *candidates);
extern void fqp_collect_source_candidates_from_rel(PlannerInfo *root,
                                                   RelOptInfo *rel,
                                                   List **sources,
                                                   bool *has_local_candidate);
extern bool fqp_is_final_joinrel(PlannerInfo *root, RelOptInfo *joinrel);

#endif
