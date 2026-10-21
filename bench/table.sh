#!/bin/bash
# table.sh [rounds] -- rebuild the published performance table.
#
# Runs the three contenders -- hacl-pulse, HACL* as built for portable C, and
# HACL* in its best available configuration -- interleaved on one core, at two
# link-time code offsets, in palindromic order so that no contender is
# systematically favoured by a drifting machine.
#
# Environment:
#   BENCH_CPU   core to pin to            (default 2)
#   BENCH_CC    gcc | clang               (default gcc)
#   BENCH_OUT   output directory          (default /tmp/bench)
#   HACL_STAR   HACL* checkout to compare (default /tmp/hacl-star)
#
# HACL* is rebuilt with BENCH_CC into $HACL_STAR/dist/build-$BENCH_CC (once, then
# cached), so that a clang run compares clang against clang.  Linking the
# checkout's own libevercrypt.a, which its Makefile builds with cc, made every
# clang row compare clang-compiled hacl-pulse against gcc-compiled HACL*.
set -e
cd "$(dirname "$0")"
ROUNDS=${1:-3}
R=${HACL_PULSE:-$(cd .. && pwd)}
S=${HACL_STAR:-/tmp/hacl-star}
H=$S/dist/gcc-compatible
K=$S/dist/karamel
CPU=${BENCH_CPU:-2}
CC=${BENCH_CC:-gcc}
OUT=${BENCH_OUT:-/tmp/bench}
IREF="-I . -I $H -I $H/internal -I $K/include -I $K/krmllib/dist/minimal"

[ -d "$H" ] || { echo "no HACL* at $S -- set HACL_STAR" >&2; exit 1; }
[ -f "$R/dist/Hacl.c" ] || { echo "no $R/dist/Hacl.c -- run make extract" >&2; exit 1; }
mkdir -p "$OUT"

HB=$S/dist/build-$CC
if [ ! -f "$HB/libevercrypt.a" ]; then
  rm -rf "$HB"; mkdir -p "$HB"
  cp -r "$H"/. "$HB"/
  make -C "$HB" clean >/dev/null 2>&1 || true
  make -C "$HB" CC="$CC" -j"$(nproc)" libevercrypt.a >"$HB/build.log" 2>&1 \
    || { echo "HACL* build with $CC failed, see $HB/build.log" >&2; exit 1; }
fi
LIB=$HB/libevercrypt.a

# The two link-time code offsets.  Built here so that a fresh checkout works.
for n in 0 23; do [ -e pad_$n.o ] || ./mkpad.sh $n; done

$CC -std=c11 -O3 -I $R/dist -I $R/c -c $R/dist/Hacl.c -o $OUT/t_hacl.o
for n in 0 23; do
  $CC -std=c11 -O3 -DBS_PRECOMP7 -DSHIM='"shim_pulse.h"' -I . -I $R/dist -I $R/c \
      bench.c pad_$n.o $OUT/t_hacl.o -o $OUT/t_pulse_$n
  $CC -std=c11 -O3 -DSHIM='"shim_ref.h"' $IREF \
      bench.c pad_$n.o $LIB -o $OUT/t_ref_$n
  $CC -std=c11 -O3 -DBS_REF_BEST -DSHIM='"shim_ref.h"' $IREF \
      bench.c pad_$n.o $LIB -o $OUT/t_best_$n
done

for r in $(seq 1 $ROUNDS); do
  for n in 0 23; do
    for v in pulse ref best best ref pulse; do
      i=1; while [ -e $OUT/T${v}_${n}_${r}_$i.csv ]; do i=$((i+1)); done
      taskset -c $CPU $OUT/t_${v}_$n > $OUT/T${v}_${n}_${r}_$i.csv
    done
  done
done
