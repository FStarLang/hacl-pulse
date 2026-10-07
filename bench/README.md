# The benchmark harness

Every performance number in the top-level `README.md` was produced by the
scripts in this directory, and `REPORT.md` here is the running record of how
each of them moved and why.

The harness exists because the first thing we measured was wrong. A naive
timing loop on a shared cloud box reported hacl-pulse's ChaCha20 as both twice
as fast and half as fast as HACL\*'s within the same hour, and a single
`-falign-functions` change moved a hash benchmark by 18% with no change to the
code being timed. Almost everything below is a defence against one of those
two failure modes: a machine that drifts, and a compiler that lays code out
differently for reasons that have nothing to do with the algorithm.

## The three contenders

One benchmark body, `bench.c`, is compiled three times against two shims:

| Tag | Shim | What it is |
| --- | --- | --- |
| `pulse` | `shim_pulse.h` | this repository's `dist/Hacl.c`, extracted by Custard from the Pulse sources |
| `ref` | `shim_ref.h` | HACL\*'s portable C distribution — the algorithms compiled as plain scalar C, no intrinsics |
| `best` | `shim_ref.h` with `-DBS_REF_BEST` | HACL\* at its best: EverCrypt's runtime dispatch onto Vale assembly, AVX2 and the SHA/AES instruction extensions |

`best` is the column that matters. It is what a user actually gets from HACL\*
today, so it is what the top-level README leads with. `ref` is kept as a
secondary column because it isolates *compiled-code* quality from *instruction
selection*: when hacl-pulse loses to `best` but beats `ref`, the gap is a
backend we have not written yet rather than code we generated badly.

The shims exist so that the three builds differ in nothing but which library
they call. The same loop counts, the same buffers, the same warmup, the same
`clock_gettime` call sites.

## What the harness does about a dishonest machine

`table.sh` is the driver, and nearly all of it is anti-self-deception:

- **Two link-time code offsets.** `mkpad.sh N` generates a file of `N` one-byte
  functions, compiled with `-falign-functions=1`, which is linked ahead of the
  benchmark and shifts everything after it in the text segment. The suite is
  run at offsets 0 and 23. If a "speedup" only exists at one offset it is
  alignment luck, not a speedup. This has caught several would-be improvements.
- **Palindromic interleaving.** Each round runs the contenders in the order
  `pulse ref best best ref pulse`. A machine that is getting steadily slower
  (or faster) across the window biases the first and last slots in opposite
  directions, and a palindrome puts every contender equally at both ends.
- **Core pinning.** `taskset -c $BENCH_CPU` keeps a run on one core so that it
  is not migrated onto a busy sibling mid-measurement.
- **Minimum, not mean, across runs.** All the analysis scripts reduce by `min`.
  Interference can only ever make a measurement slower, so the minimum over
  repetitions is the best estimate of the true cost and the only statistic that
  is robust to a noisy neighbour.
- **A canary row.** `bench.c` times a fixed dependent-add loop, whose cost is a
  property of the core clock and nothing else, once before the suite and once
  after. It reports the faster of the two and their ratio as a `canary` row. If
  that spread is not close to 1.0 the core was not healthy for the duration and
  the run is discarded rather than interpreted. On this box, transient 60–80%
  slowdowns on an individual core are routine.

## Running it

The harness needs a HACL\* checkout to compare against, with its C distribution
and `libevercrypt.a` already built:

```sh
git clone https://github.com/hacl-star/hacl-star /tmp/hacl-star
make -C /tmp/hacl-star/dist/gcc-compatible -j
```

and this repository extracted (`make verify && make extract`, so that
`dist/Hacl.c` exists). Then:

```sh
cd bench
BENCH_CPU=2 BENCH_CC=gcc   BENCH_OUT=/tmp/r60g ./table.sh 3
BENCH_CPU=2 BENCH_CC=clang BENCH_OUT=/tmp/r60c ./table.sh 3
```

Three rounds take roughly half an hour per compiler. Both compilers are always
run: gcc and clang disagree about this code often enough, and by large enough
margins, that a single-compiler result has twice been actively misleading — see
`REPORT.md` Part 52, where one misplaced compiler attribute cost gcc 20% and
clang 74%.

Environment variables: `BENCH_CPU` (core to pin to, default 2), `BENCH_CC`
(`gcc` or `clang`, default gcc), `BENCH_OUT` (output directory, default
`/tmp/bench`), `HACL_STAR` (the checkout to compare against, default
`/tmp/hacl-star`), `HACL_PULSE` (this repository, default: the parent of this
directory).

Output is one CSV per contender per offset per round, named
`T<contender>_<offset>_<round>_<n>.csv`, with the columns
`impl,benchmark,size,ns,iterations`.

## Reading the results

| Script | Use |
| --- | --- |
| `d46b.py NEW OLD CFG` | regression diff: every row where `NEW` differs from `OLD` by more than 1.5%, which is this harness's noise floor. The first thing to run after any change. |
| `d46.py` | the same, without the threshold — every row, for when you want the whole picture |
| `gap.py DIR` | rank every benchmark by hacl-pulse / HACL\*-portable |
| `gapbest.py DIR` | rank every benchmark by hacl-pulse / HACL\*-best. **This is the ranking that chooses what to work on next.** |
| `mktable.py DIR` | regenerate the markdown performance table in the top-level `README.md`, so those numbers are never typed by hand |

`CFG` is a configuration string recorded alongside the numbers; `cfg.c` prints
EverCrypt's view of the CPU (`shaext`, `avx2`, `aesni`, `adx`, …) so that a
result can be attributed to the right dispatch decision later.

## The probe tools

These are not part of the published table. They are the tools used to answer
"why is this row slow", kept because the same questions keep coming back.

| File | Use |
| --- | --- |
| `ab.sh A tagA B tagB [rounds]` | A/B two object files through the full suite, interleaved and at both offsets. The standard way to test one change. |
| `ab2.sh` | the same, when the two sides need different include paths and flags (comparing two whole distributions) |
| `abclang.sh` | `ab.sh` under clang |
| `layout.sh obj tag` | run one build at four code offsets (0, 23, 57, 101) to measure how much of a result is alignment |
| `probe2.c` | a standalone timing harness with the canary loop, for timing a handful of functions without the full suite |
| `probe_pre.c` | bignum/Montgomery-precomputation probe |
| `bench_vec.c` | times HACL\*'s 128- and 256-bit vector implementations directly, to establish what a vector backend for hacl-pulse would be worth before writing one |
| `cfg.c` | print EverCrypt's CPU feature detection |

## What is not here

The result data. Sixty-odd run directories of CSVs, several hundred megabytes,
are not worth versioning: they are reproducible from the harness, they are
specific to one machine, and the conclusions drawn from them are in
`REPORT.md`, which is. `.gitignore` keeps the generated `pad_*.c`/`pad_*.o` and
any `*.csv` or `rNN*/` directories out of the repository for the same reason.

## REPORT.md

`REPORT.md` is the long-form record: one Part per optimization, in order, each
giving the measurement that motivated it, the hypothesis, the experiment that
confirmed or killed the hypothesis, the change, and the measured result. It
includes the ones that did not work, which are the more useful half. If you
want to know why some piece of this library is shaped oddly, it is probably
explained there.
