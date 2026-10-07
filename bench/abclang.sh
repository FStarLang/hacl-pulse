#!/bin/bash
# ab.sh <A.c-or-.o> <tagA> <B.o> <tagB> [rounds] [extra cflags...]
# Interleaves the two variants so both see the same machine state, and runs
# each one at several code offsets.  A benchmark box that is shared with other
# tenants delivers 60-80% transient slowdowns on an individual core; the only
# defence is that both sides of the comparison sit inside the same window.
set -e
A=$1; TA=$2; B=$3; TB=$4; ROUNDS=${5:-3}; shift 5 || true
R=${HACL_PULSE:-$(cd "$(dirname "$0")/.." && pwd)}
CPU=${BENCH_CPU:-2}
for o in $A $B; do :; done
for n in 0 23; do
  clang -std=c11 -O3 "$@" -DSHIM='"shim_pulse.h"' -I . -I $R/dist -I $R/c bench.c pad_$n.o $A Hacl_Random.o -o /tmp/bench/ab_${TA}_$n
  clang -std=c11 -O3 "$@" -DSHIM='"shim_pulse.h"' -I . -I $R/dist -I $R/c bench.c pad_$n.o $B Hacl_Random.o -o /tmp/bench/ab_${TB}_$n
done
for r in $(seq 1 $ROUNDS); do
  for n in 0 23; do
    taskset -c $CPU /tmp/bench/ab_${TA}_$n > /tmp/bench/AB${TA}_${n}_$r.csv
    taskset -c $CPU /tmp/bench/ab_${TB}_$n > /tmp/bench/AB${TB}_${n}_$r.csv
    taskset -c $CPU /tmp/bench/ab_${TB}_$n > /tmp/bench/AB${TB}_${n}_${r}b.csv
    taskset -c $CPU /tmp/bench/ab_${TA}_$n > /tmp/bench/AB${TA}_${n}_${r}b.csv
  done
done
