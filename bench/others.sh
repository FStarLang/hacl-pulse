#!/bin/bash
# others.sh [rounds] -- hacl-pulse against other libraries.
#
# Builds one driver (others/others.c) per contender and runs them all
# interleaved on one core, in palindromic order, for [rounds] rounds (default
# 3).  mkothers.py turns the CSVs into the README's comparison table.
#
# Contenders, each at a pinned version, fetched and built once into $OTHERS:
#   hacl-pulse  dist/Hacl.c, built twice: with gcc and with clang
#   openssl     the system libcrypto (whatever `openssl version` says)
#   awslc       aws/aws-lc, Release, gcc
#   libsodium   jedisct1/libsodium (stable branch), its default -O3, gcc
#   libjade     formosa-crypto/libjade release 2023.05-2, pre-generated asm
#   firedancer  firedancer-io/firedancer ballet, MACHINE=native, clang
#               (its makefile refuses this machine's gcc 15.2)
#   dalek       ed25519-dalek 2 / x25519-dalek 2 via others/dalek, LTO,
#               -C target-cpu=native
#
# Every driver checks its library against hacl-pulse before timing anything
# and exits non-zero on a mismatch (see others/others.c).
#
# Environment:
#   BENCH_CPU   core to pin to      (default 2)
#   BENCH_OUT   output directory    (default /tmp/bench-others)
#   OTHERS      dependency cache    (default /tmp/others)
#   CARGO       cargo binary        (default: cargo on PATH, else ~/.cargo/bin/cargo)
set -e
cd "$(dirname "$0")"
ROUNDS=${1:-3}
R=$(cd .. && pwd)
CPU=${BENCH_CPU:-2}
OUT=${BENCH_OUT:-/tmp/bench-others}
D=${OTHERS:-/tmp/others}
CARGO=${CARGO:-$(command -v cargo || echo ~/.cargo/bin/cargo)}
J=$(nproc)

AWSLC_REV=ffca1276f5565a71cf4717c29828b29b600e4251
SODIUM_REV=1da41306a7abd814dcea30389ac63ef3b6907302
FD_REV=849c582ad1175fd22f6aef28e3afff543e06096b
JADE_URL=https://github.com/formosa-crypto/libjade/releases/download/release%2F2023.05-2/libjade-dist-src-amd64.tar.gz
JADE_SHA=ffbf658c247407f9f030d6309b80428692676f81e22ca0f8e5b6465e00e32c51

[ -f "$R/dist/Hacl.c" ] || { echo "no $R/dist/Hacl.c -- run make extract" >&2; exit 1; }
mkdir -p "$D" "$OUT"

checkout() { # dir url rev
  [ -d "$D/$1" ] || git clone -q "$2" "$D/$1"
  if [ "$(git -C "$D/$1" rev-parse HEAD)" != "$3" ]; then
    git -C "$D/$1" fetch -q origin "$3" 2>/dev/null || git -C "$D/$1" fetch -q origin
    git -C "$D/$1" checkout -q "$3"
  fi
}
built() { [ -f "$D/$1.done" ] && [ "$(cat "$D/$1.done")" = "$2" ]; }

if ! built awslc $AWSLC_REV; then
  echo "building aws-lc..." >&2
  checkout aws-lc https://github.com/aws/aws-lc.git $AWSLC_REV
  rm -rf "$D/awslc-build" "$D/awslc"
  cmake -S "$D/aws-lc" -B "$D/awslc-build" -G Ninja -DCMAKE_BUILD_TYPE=Release \
        -DCMAKE_C_COMPILER=gcc -DCMAKE_CXX_COMPILER=g++ -DBUILD_TESTING=OFF \
        -DCMAKE_INSTALL_PREFIX="$D/awslc" >"$D/awslc.log" 2>&1
  ninja -C "$D/awslc-build" install >>"$D/awslc.log" 2>&1 \
    || { echo "aws-lc build failed, see $D/awslc.log" >&2; exit 1; }
  echo $AWSLC_REV > "$D/awslc.done"
fi

if ! built sodium $SODIUM_REV; then
  echo "building libsodium..." >&2
  checkout libsodium https://github.com/jedisct1/libsodium.git $SODIUM_REV
  rm -rf "$D/sodium-build" "$D/sodium"; mkdir -p "$D/sodium-build"
  (cd "$D/sodium-build" && CC=gcc "$D/libsodium/configure" -q --disable-shared --prefix="$D/sodium" \
     && make -j$J install) >"$D/sodium.log" 2>&1 \
    || { echo "libsodium build failed, see $D/sodium.log" >&2; exit 1; }
  echo $SODIUM_REV > "$D/sodium.done"
fi

if ! built jade $JADE_SHA; then
  echo "fetching libjade..." >&2
  curl -sSL -o "$D/jade.tgz" "$JADE_URL"
  echo "$JADE_SHA  $D/jade.tgz" | sha256sum -c --quiet
  rm -rf "$D/jade-dist"; mkdir -p "$D/jade-dist"
  tar -xzf "$D/jade.tgz" -C "$D/jade-dist"
  echo $JADE_SHA > "$D/jade.done"
fi
JD=$(echo "$D"/jade-dist/*/libjade)

if ! built fd $FD_REV; then
  echo "building firedancer ballet..." >&2
  checkout firedancer https://github.com/firedancer-io/firedancer.git $FD_REV
  make -C "$D/firedancer" -j$J MACHINE=native CC=clang lib >"$D/fd.log" 2>&1 \
    || { echo "firedancer build failed, see $D/fd.log" >&2; exit 1; }
  echo $FD_REV > "$D/fd.done"
fi
FDL=$(echo "$D"/firedancer/build/native/clang/*/lib)

echo "building dalek..." >&2
(cd others/dalek && RUSTFLAGS="-C target-cpu=native" CARGO_TARGET_DIR="$D/dalek-target" \
   "$CARGO" build --release --locked -q)

# ---- drivers ---------------------------------------------------------------
W="-std=c17 -O3 -Wall -Wno-unused-variable -Wno-unused-function"
INC="-I $R/dist -I $R/c"
gcc   -std=c11 -O3 $INC -c "$R/dist/Hacl.c" -o "$OUT/hacl_gcc.o"
clang -std=c11 -O3 $INC -c "$R/dist/Hacl.c" -o "$OUT/hacl_clang.o"
drv() { # name cc ops extra-args...
  local n=$1 cc=$2 ops=$3; shift 3
  $cc $W -DOPS="\"$ops\"" $INC others/others.c "$@" -o "$OUT/o_$n"
}
drv pulse-gcc   gcc   ops_pulse.h "$OUT/hacl_gcc.o"
drv pulse-clang clang ops_pulse.h "$OUT/hacl_clang.o"
drv openssl     gcc   ops_openssl.h "$OUT/hacl_gcc.o" -Wno-deprecated-declarations -lcrypto
drv awslc       gcc   ops_awslc.h -I "$D/awslc/include" "$OUT/hacl_gcc.o" "$D/awslc/lib/libcrypto.a" -lpthread
drv libsodium   gcc   ops_sodium.h -I "$D/sodium/include" "$OUT/hacl_gcc.o" "$D/sodium/lib/libsodium.a" -lpthread
drv libjade     gcc   ops_jade.h "$OUT/hacl_gcc.o" \
  "$JD"/crypto_hash/{sha256_ref,sha512_ref,sha3_256_avx2}/*.s "$JD"/crypto_xof/shake128_avx2/*.s \
  "$JD"/crypto_stream/{chacha_chacha20_ietf_avx2,salsa20_salsa20_avx2}/*.s \
  "$JD"/crypto_onetimeauth/poly1305_avx2/*.s "$JD"/crypto_secretbox/xsalsa20poly1305_avx2/*.s \
  "$JD"/crypto_scalarmult/curve25519_mulx/*.s
# Firedancer's headers are configured by FD_HAS_* macros; these are the ones
# its MACHINE=native build derived for this CPU (config/machine/native.mk),
# minus any this CPU lacks (SHA-NI, GFNI, AVX-512 IFMA).
FDF="-march=native -DFD_HAS_DOUBLE=1 -DFD_HAS_INT128=1 -DFD_HAS_ALLOCA=1 -DFD_HAS_THREADS=1
     -DFD_HAS_X86=1 -DFD_IS_X86_64=1 -DFD_HAS_SSE=1 -DFD_HAS_AVX=1 -DFD_USING_CLANG=1
     -D_XOPEN_SOURCE=700 -D_DEFAULT_SOURCE"
echo | clang -march=native -dM -E - | grep -q '__AES__ '    && FDF="$FDF -DFD_HAS_AESNI=1"
echo | clang -march=native -dM -E - | grep -q '__SHA__ '    && FDF="$FDF -DFD_HAS_SHANI=1"
echo | clang -march=native -dM -E - | grep -q '__GFNI__ '   && FDF="$FDF -DFD_HAS_GFNI=1"
echo | clang -march=native -dM -E - | grep -q '__AVX512IFMA__ ' && FDF="$FDF -DFD_HAS_AVX512=1"
drv firedancer  clang ops_firedancer.h $FDF -I "$D/firedancer/src" "$OUT/hacl_gcc.o" \
  "$FDL/libfd_ballet.a" "$FDL/libfd_util.a" -lpthread -lm
drv dalek       gcc   ops_dalek.h "$OUT/hacl_gcc.o" "$D/dalek-target/release/libdalekffi.a" -lpthread -ldl -lm

# ---- runs ------------------------------------------------------------------
V="pulse-gcc pulse-clang openssl awslc libsodium libjade firedancer dalek"
VR=$(echo $V | tr ' ' '\n' | tac | tr '\n' ' ')
rm -f "$OUT"/O*.csv
for r in $(seq 1 $ROUNDS); do
  for v in $V $VR; do
    i=1; while [ -e "$OUT/O${v}_${r}_$i.csv" ]; do i=$((i+1)); done
    taskset -c $CPU "$OUT/o_$v" > "$OUT/O${v}_${r}_$i.csv" \
      || { echo "$v failed (agreement check?), see $OUT/O${v}_${r}_$i.csv" >&2; exit 1; }
  done
done
echo "done: python3 mkothers.py $OUT" >&2
