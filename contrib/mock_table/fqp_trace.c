#include "postgres.h"

#include "miscadmin.h"
#include "portability/instr_time.h"
#include "utils/json.h"
#include "utils/memutils.h"

#include <stdio.h>
#include <string.h>

#include "mock_table.h"
#include "fqp_trace.h"

#define FQP_LOCAL_EXPLAIN_TRACE_PATH "/Users/vishi/Desktop/DBGrp/repos/a_main/fqp_db_interface/tmp/fqp_pg_explain_profile.json"

static MemoryContext fqp_trace_context = NULL;
static StringInfo fqp_trace_items = NULL;
static bool fqp_trace_active = false;
static uint64 fqp_trace_root_seq = 0;
static uint64 fqp_trace_explain_count = 0;
static char fqp_trace_root_hash[17];
static char *fqp_trace_root_query = NULL;
static instr_time fqp_trace_start;

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

bool
fqp_trace_is_active(void)
{
    return fqp_trace_active;
}

void
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

void
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
