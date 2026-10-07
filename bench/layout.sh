#!/bin/bash
# layout.sh <hacl.o> <tag>  -- run the suite at four code offsets
R=${HACL_PULSE:-$(cd "$(dirname "$0")/.." && pwd)}
for n in 0 23 57 101; do
  gcc -std=c11 -O3 -DSHIM='"shim_pulse.h"' -I . -I $R/dist -I $R/c bench.c pad_$n.o "$1" Hacl_Random.o -o /tmp/bench/bl_$2_$n
  taskset -c ${BENCH_CPU:-2} /tmp/bench/bl_$2_$n > /tmp/bench/L$2_$n.csv
done
