#!/bin/bash
# ab2.sh <A.o> <tagA> <A-include-dir> <A-extra> <B.o> <tagB> <B-include-dir> <B-extra> [rounds] [cc]
set -e
A=$1; TA=$2; IA=$3; XA=$4; B=$5; TB=$6; IB=$7; XB=$8; ROUNDS=${9:-2}; CC=${10:-gcc}
R=${HACL_PULSE:-$(cd "$(dirname "$0")/.." && pwd)}
CPU=${BENCH_CPU:-2}
for n in 0 23; do
  $CC -std=c11 -O3 $XA -DSHIM='"shim_pulse.h"' -I . -I $IA -I $R/c bench.c pad_$n.o $A Hacl_Random.o -o /tmp/bench/ab_${TA}_$n
  $CC -std=c11 -O3 $XB -DSHIM='"shim_pulse.h"' -I . -I $IB -I $R/c bench.c pad_$n.o $B Hacl_Random.o -o /tmp/bench/ab_${TB}_$n
done
for r in $(seq 1 $ROUNDS); do
  for n in 0 23; do
    taskset -c $CPU /tmp/bench/ab_${TA}_$n > /tmp/bench/AB${TA}_${n}_$r.csv
    taskset -c $CPU /tmp/bench/ab_${TB}_$n > /tmp/bench/AB${TB}_${n}_$r.csv
    taskset -c $CPU /tmp/bench/ab_${TB}_$n > /tmp/bench/AB${TB}_${n}_${r}b.csv
    taskset -c $CPU /tmp/bench/ab_${TA}_$n > /tmp/bench/AB${TA}_${n}_${r}b.csv
  done
done
