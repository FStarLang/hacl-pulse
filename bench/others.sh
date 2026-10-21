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
#   ML-DSA only:
#   pqcrystals-ref, pqcrystals-avx2
#               pq-crystals/dilithium ref/ and avx2/, with their own
#               makefiles' flags, gcc
#   mldsa-native
#               pq-code-package/mldsa-native, monolithic multilevel build
#               with the x86-64 native (AVX2) backends, gcc
#   libcrux     libcrux-ml-dsa via others/libcrux (Rust, its AVX2 code
#               selected at run time), LTO, -C target-cpu=native; the crate
#               pins its toolchain (rust-toolchain.toml), so CARGO must be
#               rustup's
#
# Every driver checks its library against hacl-pulse before timing anything
# and exits non-zero on a mismatch (see others/others.c).
#
# Environment:
#   BENCH_CPU   core to pin to      (default 2)
#   BENCH_OUT   output directory    (default /tmp/bench-others)
#   OTHERS      dependency cache    (default /tmp/others)
#   CARGO       cargo binary        (default: ~/.cargo/bin/cargo, else cargo on PATH)
set -e
cd "$(dirname "$0")"
ROUNDS=${1:-3}
R=$(cd .. && pwd)
CPU=${BENCH_CPU:-2}
OUT=${BENCH_OUT:-/tmp/bench-others}
D=${OTHERS:-/tmp/others}
CARGO=${CARGO:-$([ -x ~/.cargo/bin/cargo ] && echo ~/.cargo/bin/cargo || command -v cargo)}
J=$(nproc)

AWSLC_REV=ffca1276f5565a71cf4717c29828b29b600e4251
SODIUM_REV=1da41306a7abd814dcea30389ac63ef3b6907302
FD_REV=849c582ad1175fd22f6aef28e3afff543e06096b
PQC_REV=d35ba3fe5449bee3e6d43e1f296c3ca818bd36be
MLDSA_NATIVE_REV=6daba6073b1b51097e36c20c5ba61f644d0273cc
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

echo "building libcrux..." >&2
(cd others/libcrux && RUSTFLAGS="-C target-cpu=native" CARGO_TARGET_DIR="$D/libcrux-target" \
   "$CARGO" build --release --locked -q)

# pq-crystals: every parameter set is a separate build of the same sources
# (namespaced symbols), Keccak once; one archive per variant.
pqc() { # variant cflags
  local v=$1 f m o; local S="$D/dilithium/$v" B="$D/pqc-$v"; shift
  local MODE="sign.c packing.c polyvec.c poly.c rounding.c symmetric-shake.c" SHARED="fips202.c"
  [ $v = ref ] && MODE="$MODE ntt.c reduce.c"
  [ $v = avx2 ] && MODE="$MODE ntt.S invntt.S pointwise.S shuffle.S consts.c rejsample.c" \
                && SHARED="$SHARED fips202x4.c f1600x4.S"
  rm -rf "$B"; mkdir -p "$B"
  for m in 2 3 5; do for f in $MODE; do
    gcc "$@" -Wa,-I"$S" -DDILITHIUM_MODE=$m -c "$S/$f" -o "$B/${m}_${f%.*}.o"
  done; done
  for f in $SHARED; do gcc "$@" -Wa,-I"$S" -c "$S/$f" -o "$B/${f%.*}.o"; done
  rm -f "$D/libpqc-$v.a"; ar rcs "$D/libpqc-$v.a" "$B"/*.o
}
if ! built pqc $PQC_REV; then
  echo "building pq-crystals dilithium..." >&2
  checkout dilithium https://github.com/pq-crystals/dilithium.git $PQC_REV
  pqc ref -O3 -fomit-frame-pointer
  pqc avx2 -mavx2 -mpopcnt -march=native -mtune=native -O3
  echo $PQC_REV > "$D/pqc.done"
fi
checkout mldsa-native https://github.com/pq-code-package/mldsa-native.git $MLDSA_NATIVE_REV

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
drv libcrux     gcc   ops_libcrux.h "$OUT/hacl_gcc.o" "$D/libcrux-target/release/liblibcruxffi.a" -lpthread -ldl -lm
drv pqcrystals-ref  gcc ops_pqcrystals.h "$OUT/hacl_gcc.o" "$D/libpqc-ref.a"
drv pqcrystals-avx2 gcc ops_pqcrystals.h -DPQ_AVX2 "$OUT/hacl_gcc.o" "$D/libpqc-avx2.a"
# mldsa-native's own flags for this CPU (examples/*/auto.mk): AVX2, BMI2, POPCNT.
MN="$D/mldsa-native/mldsa"
MNF="-O3 -mavx2 -mbmi2 -mpopcnt -DMLD_CONFIG_MULTILEVEL_BUILD -DMLD_CONFIG_USE_NATIVE_BACKEND_ARITH
     -DMLD_CONFIG_USE_NATIVE_BACKEND_FIPS202 -I $MN"
gcc $MNF -DMLD_CONFIG_MULTILEVEL_WITH_SHARED -c "$MN/mldsa_native_asm.S" -o "$OUT/mldsa_native_asm.o"
drv mldsa-native gcc  ops_mldsanative.h $MNF "$OUT/hacl_gcc.o" "$OUT/mldsa_native_asm.o"

# ---- runs ------------------------------------------------------------------
V="pulse-gcc pulse-clang openssl awslc libsodium libjade firedancer dalek
   libcrux pqcrystals-ref pqcrystals-avx2 mldsa-native"
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
