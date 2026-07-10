#include "postgres.h"
#include "catalog/namespace.h"
#include "parser/parsetree.h"
#include "parser/parse_relation.h"
#include "optimizer/cost.h"
#include "optimizer/optimizer.h"
#include "optimizer/paths.h"
#include "nodes/bitmapset.h"
#include "nodes/pg_list.h"
#include "nodes/plannodes.h"
#include "utils/hsearch.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"

#include "mock_table.h"

static HTAB *remote_join_cost_hashtab = NULL;
static MemoryContext remote_join_cost_mcxt = NULL;

void
init_remote_join_cost_memo(MemoryContext mcxt)
{
    HASHCTL		hash_ctl;

    if (remote_join_cost_hashtab != NULL && remote_join_cost_mcxt == mcxt)
        return;

    remote_join_cost_mcxt = mcxt;

    MemSet(&hash_ctl, 0, sizeof(hash_ctl));
    hash_ctl.keysize = sizeof(Relids);
    hash_ctl.entrysize = sizeof(RemoteJoinCostEntry);
    hash_ctl.hash = bitmap_hash;
    hash_ctl.match = bitmap_match;
    hash_ctl.hcxt = mcxt;
    remote_join_cost_hashtab = hash_create("RemoteJoinCostMemo",
                                     256L,
                                     &hash_ctl,
                                     HASH_ELEM | HASH_FUNCTION | HASH_COMPARE | HASH_CONTEXT);
}

RemoteJoinCostEntry *
lookup_or_create_remote_join_cost(Relids relids, bool *found)
{
    RemoteJoinCostEntry *entry;

    Assert(remote_join_cost_hashtab != NULL);

    entry = (RemoteJoinCostEntry *) hash_search(remote_join_cost_hashtab,
											   &relids,
                                               HASH_ENTER,
                                               found);
    if (!*found)
    {
        entry->startup_cost = 0;
        entry->total_cost = 0;
        entry->rows = 0;
        entry->join_dest_rti = 0;
        entry->valid = false;
    }

    return entry;
}

