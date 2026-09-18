# Reproducing the search and the experiments

This guide covers the numerical side of the paper: verifying the certificate
in integer arithmetic, running the cutting-plane and column-generation search
of Section 4, and repeating the computational experiments of Section 5 and
Appendix C. The Lean proof is covered in [lean-proof.md](lean-proof.md).

Nothing here is a premise of the theorem. The formal proof re-verifies the
certificate from its integer rows; the tools below check the same certificate
independently and document how it was found.

## Environment

The experiments reported in the paper ran on Windows 11 with an Intel Core
i7-14700K, 63.72 GiB of RAM and a 40 GiB process-memory cap, using Python
3.12.4, NumPy 2.0.2, SciPy 1.13.1, HiGHS (highspy) 1.15.1, SCS 3.2.8, CVXPY
1.6.5 and OpenBLAS 0.3.27; the C++ routines were compiled with MinGW GCC
13.2.0. The search code and the verifiers also run on Linux and on ARM or x86
macOS with Clang; they use portable bit extraction and standard C++ threads and
need neither OpenMP nor BMI2.

You need Python 3.9 to 3.12 (3.12 recommended), a C++17 compiler available as
`c++` with `std::thread` and `__int128`, and the pinned packages:

```sh
python -m venv .research-repro/venv
. .research-repro/venv/bin/activate        # Windows: .research-repro\venv\Scripts\activate
python -m pip install -r requirements.txt
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
```

Run every command from the repository root. Every command below writes only
under the ignored `.research-repro/` directory. On Windows, run the campaign
scripts through `python -X utf8 experiments/runtime.py SCRIPT ...`, which fixes
the dependent-DLL search path for the compiled oracles and pins the BLAS
thread count.

## Verify the certificate in integer arithmetic

```sh
python search/exactify_five_root.py \
  --certificate certificate/K4_turan_order7_certificate.json \
  --cross-check-pricing --threads 2 \
  --cache .research-repro/integer-check --output .research-repro/integer-check.json
```

The verifier reads the integer factor vectors, checks their dimensions and
conservative overflow bounds, rebuilds every Gram matrix, and evaluates the
integer coefficient `C₇(G)` of Appendix A.2 for all 13,051,375 tetrahedron-free
one-vertex extensions of the 964 six-vertex representatives with two
implementations: a C++ verifier that reconstructs the five-root flags and type
automorphisms independently and uses the grouped sum over five-vertex root
sets, and, with `--cross-check-pricing`, the search's own coefficient
evaluator in exact mode. Python separately enumerates every ordered root
labeling and flag pair at the maximizing and at selected six-vertex
representatives. The output records the exact maximum
`11245394264033484 / 20160000000000000`, the reduced bound, the maximizing
extension, the raw count and the hashes of the inputs.

The same script converts a saved floating-point dual of the search into an
exact certificate (`python search/exactify_five_root.py DUAL.npz --types ...
--factorization svd --scale 2000000 ...`), following Appendix B.3: SVD
compression of the factor vectors at relative tolerance `1e-7`, rounding to
multiples of `1/2000000`, and a complete exact re-evaluation.

## The search

`search/` contains the implementation described in Section 4 and Appendix B:

| File | Role |
| --- | --- |
| `analyze_certificate.py` | builds the six-vertex coefficient cache (`components.npz`) from the flag bases; run once per cache directory |
| `reconstruct_optimization.py` | the twelve-block seven-vertex model (blocks with at most four roots): the restricted dual LP in HiGHS, eigenvector cuts, complete column pricing, checkpoints |
| `five_root_oracle.py`, `five_root_oracle.cpp`, `five_root_exact_oracle.hpp` | the five-root blocks: six-vertex flags of each type, the full automorphism action on Gram matrices, the fast coefficient evaluator and its exact counterpart |
| `expand_seven_optimization.py` | the search over all 35 blocks (`--types` selects the five-root types); the driver used for `M7-all5` |
| `optimization_oracle.cpp`, `optimization_oracle_tail.inc`, `optimization_order8.inc` | the compiled pricing kernel over all raw seven-vertex extensions (the last file is an unused eight-vertex extension that the kernel is compiled with) |
| `exactify_five_root.py` | exact conversion and independent verification, above |

Build the cache, then run a fresh search over all 23 five-root types with the
settings of Appendix B.1:

```sh
python search/analyze_certificate.py --cache .research-repro/cache \
  --output .research-repro/certificate_diagnostics.json
python search/expand_seven_optimization.py \
  --types 0,1,3,7,11,12,13,15,30,31,63,76,77,86,87,94,116,117,119,222,236,237,254 \
  --cache .research-repro/cache --deps .research-repro/empty-deps \
  --mode with --seed-turan --price-first --price-top 8 --threads 2 \
  --max-cuts 80 --keep-cuts 1800 --psd-tolerance 1e-7 --price-tolerance 1e-7 \
  --seconds 3600 --max-iter 100000 --checkpoint \
  --output-dir .research-repro/search/M7-all5
```

`--mode with` imposes the stationarity equality; `--seed-turan` initializes
the constraint set `W` with the seven-vertex subgraphs of the balanced cyclic
three-part construction; the empty `--deps` directory makes the optimizer use
the `highspy` of the active environment. The run directory receives the
iteration history, the best globally evaluated dual (`*_best_dual.npz`), the
last primal and a resumable checkpoint. Convert the best dual with
`exactify_five_root.py` as above.

Fresh searches are not bit-for-bit reproducible across machines: BLAS
implementations, eigenvectors in repeated eigenspaces, LP degeneracy and
time limits change the trajectory. Verify any new candidate with the exact
conversion; the exact fractions of the archived candidates are recorded in
`experiments/results_complete_20260913/`.

## The experiments

`experiments/` contains the instrumented runners of the thirteen SDP–method
configurations of Section 5, the campaign supervisors that ran them under time
and memory limits, and the records of the completed campaign. See
[`experiments/README.md`](../experiments/README.md) for the file inventory and
for how the paper's tables map to `results.csv`.

A single one-hour trial of one configuration, after building the cache above
and validating the models:

```sh
python experiments/validate_selected.py --cache .research-repro/cache \
  --output .research-repro/validation
python experiments/run_seven_method.py --model M7-all5 --method LP-CUT-CG \
  --cache .research-repro/cache --output .research-repro/runs/M7-all5-LP-CUT-CG-1 \
  --seconds 3600 --rep 1
```

`run_seven_method.py` implements `SDP-FULL`, `LP-CG` (named `LP-CUT` in the
code and records), `SDP-CUT` (named `SDP-CG`) and `LP-CUT-CG` on `M7-no5` and
`M7-all5`; `run_remaining_method.py` implements the same methods on `M6` and
`LP-CUT-CG` on `M7-lift6`; `run_long_reference.py` is the six-hour `M6`
`SDP-FULL` reference with the larger SCS iteration cap; `--phase long
--seconds 21600` gives the six-hour LP searches. Each run directory contains
`run.json` (settings, timings, residuals), `history.jsonl` (every candidate
with its global coefficient maximum and eligibility), `best_dual.npz`, and the
exact conversions under `exact/`. The full campaign, with pilots, validation
gates, repetitions, memory caps and repair handling, is the durable queue
`run_complete_campaign.py --campaign DIR`; `summarize_complete.py` audits a
finished campaign directory and `report_complete.py` renders the report and
the figures.

## Figures

```sh
python figures/generate_plots.py
```

renders the four figures of the paper from `figures/plot-data.json`, a
portable extraction of the per-run trajectories and exact checkpoint bounds
of the 43 recorded runs. It needs Matplotlib and pdfLaTeX with the Latin
Modern fonts; see [`figures/README.md`](../figures/README.md).
