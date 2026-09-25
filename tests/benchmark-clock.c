#include "sail.h"
#include <inttypes.h>
#include <time.h>

static uint64_t start_wall, start_cpu;

static uint64_t now_ns(clockid_t clock_id)
{
    struct timespec t;
    if (clock_gettime(clock_id, &t) != 0) abort();
    return (uint64_t)t.tv_sec * UINT64_C(1000000000) + (uint64_t)t.tv_nsec;
}

unit benchmark_start(const unit unused)
{
    start_wall = now_ns(CLOCK_MONOTONIC);
    start_cpu = now_ns(CLOCK_PROCESS_CPUTIME_ID);
    return UNIT;
}

unit benchmark_stop(const sail_string label)
{
    uint64_t cpu = now_ns(CLOCK_PROCESS_CPUTIME_ID) - start_cpu;
    uint64_t wall = now_ns(CLOCK_MONOTONIC) - start_wall;
    printf("{\"case\":\"%s\",\"wall_ns\":%" PRIu64 ",\"cpu_ns\":%" PRIu64 "}\n",
           label, wall, cpu);
    return UNIT;
}
