# Computational experiments

This directory contains the instrumented runners of the computational
experiments of the paper (Section 5 and Appendix C), the supervisors that
ran them, and the records of the completed campaign. The search code they
drive is in `search/`; see [`docs/reproduction.md`](../docs/reproduction.md)
for the environment and the commands.

## Records: `results_complete_20260913/`

The campaign ran thirteen SDP–method configurations three times each with a
one-hour search budget, three separate six-hour searches, and an independent
one-hour `M6` reference with the larger SCS iteration cap.

| File | Contents |
| --- | --- |
| `REPORT.md` | the report written at the end of the campaign, with settings, repaired attempts, limitations and the exact fractions |
| `results.csv`, `results.json` | the 39 one-hour trials: search and initialization times, the numerical coefficient maximum, the exact SVD and uncompressed bounds, factor counts, solver, eigenvalue and pricing times, retained columns and cuts, residuals, peak memory, and the source hashes of the executed code |
| `long-runs.csv` | the three six-hour trials and the `M6` reference |
| `checkpoints.csv` | the exact bounds of the candidates available at the 60, 300, 900, 1800 and 3600 second budgets, with verification cost; missing slots are missing |
| `attempts.csv`, `attempt-provenance.json` | all 75 task attempts of the campaign, including pilots, failures, repairs and interruptions |
| `seven-methods.pdf`, `seven-methods.svg`, `long-runs.pdf`, `long-runs.svg` | the figures rendered from the campaign records (the paper's figures are regenerated from `figures/plot-data.json`) |
| `validation.json`, `publication-manifest.json` | the audit outcome and the SHA-256 hashes of the campaign inputs and of the files here |

The paper's method names differ from the code's: `LP-CG` in the paper is
`LP-CUT` in the code and records, and `SDP-CUT` in the paper is `SDP-CG`.
The paper's method-comparison tables on `M6` and on the seven-vertex SDPs, its
SDP-comparison table and its computational-cost table are medians of
`results.csv` by configuration; its six-hour table is `long-runs.csv`. The
six-hour `M7-all5` trial produced the certificate of the main theorem,
distributed as `certificate/K4_turan_order7_certificate.json`.

The records were written on the machine that ran the campaign. Before
publication, the personal directory prefix of every recorded path was replaced
by `<repo>`, the certificate was moved to `certificate/`, and the hashes of the
files in this directory were recomputed; `publication-manifest.json` documents
this. The campaign's scratch directory (per-iteration archives, coefficient
caches, solver binaries and the two earlier partial reports that the merged
report was assembled from) is not distributed, so `summarize_complete.py` and
`report_complete.py` cannot be re-run on it; the merged records here are the
authoritative outputs.

## Runners

| Script | Role |
| --- | --- |
| `run_seven_method.py` | one trial of `SDP-FULL`, `LP-CUT`, `SDP-CG` or `LP-CUT-CG` on `M7-no5` or `M7-all5`; `--phase long` for six-hour searches |
| `run_remaining_method.py` | one trial of the same methods on `M6`, and `LP-CUT-CG` on `M7-lift6` |
| `run_long_reference.py` | the six-hour `M6` `SDP-FULL` reference |
| `run_complete_campaign.py` | the durable sequential queue of the completion campaign: validation gates, pilots, feature caches, productions, long runs, with memory and time limits |
| `run_overnight.py`, `run_selected.py`, `run_replacement.py`, `run_remaining_campaign.py`, `pilot_remaining.py` | the supervisors of the earlier stages of the campaign, whose 21 trials are included in the records |
| `runtime.py` | shared support: source hashing, atomic JSON writes, model construction, the Windows DLL search path; also a wrapper that runs any script with pinned threading |
| `seven_full.py`, `seven_full_native.py`, `seven_full_streamed.py`, `seven_native.py`, `owned_scs.py` | the full-coefficient LP and the direct SCS interfaces of the `LP-CUT` and `SDP-FULL` arms, and the generated-cut SDP of `SDP-CG` |
| `lp_memory.py`, `no5_lp_memory.py`, `recycle_highs.py` | the memory policies and HiGHS instance recycling of the full LP arms (Appendix C.1) |
| `remaining_models.py`, `exactify_order6.py` | the `M6` and `M7-lift6` models and the exact conversion of six-vertex certificates |
| `seven_catalog.cpp` | the canonical enumeration of the 1,295,600 seven-vertex classes for the full arms |
| `validate_*.py`, `test_runtime.py` | the validation gates run before production trials |
| `summarize_complete.py`, `report_complete.py`, `summarize_selected.py`, `summarize_remaining.py`, `report_remaining.py` | the audit and report generators of the campaign stages |

Each trial writes `run.json`, `history.jsonl`, `best_dual.npz` and its exact
conversions under `exact/`; the supervisors add `supervisor.json` and sampled
process-tree memory. Runs are not bit-for-bit reproducible across machines;
their exact certificates are verified from scratch after each search.

The campaign code also knows a fourth seven-vertex model, `M7-three5`, with
three of the five-root types. It was excluded from the campaign and is not
reported in the paper; the campaign manifest records the exclusion.
