# Computational experiments

This directory contains the instrumented runners of the computational
experiments of the paper (Section 5 and Appendix C), the supervisors that
ran them, the records of the completed campaign, and the tooling and records
of the continued search that produced the certificate of the main theorem
(Appendix C.3). The search code they drive is in `search/`; see
[`docs/reproduction.md`](../docs/reproduction.md) for the environment and the
commands.

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
certificate of the six-hour `M7-all5` trial is distributed as
`certificate/legacy/K4_turan_order7_six_hour_certificate.json`. It was the
certificate of the main theorem in the first arXiv version of the paper; the
continuation below supersedes it.

The records were written on the machine that ran the campaign. Before
publication, the personal directory prefix of every recorded path was replaced
by `<repo>`, the certificate was moved to `certificate/` (now
`certificate/legacy/`), and the hashes of the files in this directory were
recomputed; `publication-manifest.json` documents this. The [evidence bundle](evidence/README.md) supplies the exact certificates,
checkpoint certificates, per-run settings, histories, verification records and
executed versions of the released source modules. Original and distributed
hashes are separate. Large numerical arrays, coefficient caches, solver binaries
and superseded private reports are omitted. The historical report generators
expect that original private layout; use the portable bundle checker to audit
the published records and `figures/generate_plots.py` to regenerate the figures.

## Continuation to convergence

The six-hour `M7-all5` search was stopped by its time limit. The certificate
of the main theorem comes from continuing it without a time limit until the
convergence tests were met (Appendix C.3). Two settings differ from the
six-hour run: the three blocks with `2ℓ − s = 5`, zero in the six-hour
certificate, are excluded, and the HiGHS option `small_matrix_value` is `1e-12`
instead of the default `1e-9`. The continuation therefore has its own model
code, the native 32-block model `M7-all5-32`:

| Script | Role |
| --- | --- |
| `model32.py` | the 32 active blocks (six evaluated through six-vertex tables, 26 through seven-vertex products) and the restricted LP over them; every start and resume asserts that no block with `2ℓ − s = 5` is loaded |
| `run_unlimited32.py` | the worker: `LP-CUT-CG` without a time or iteration limit. It starts from a six-hour checkpoint and best dual (`--init legacy-checkpoint`, migrated to the 32-block model), from the six-hour certificate (`--init baseline-certificate`), or from its own newest checkpoint (`--init resume`), and ends as converged only after a final audit that rebuilds the LP and repeats every test |
| `supervise_unlimited32.py` | `prepare`, `launch`, `supervise`, `stop`: a durable supervisor with a memory ceiling, stage-hang and disk guards, automatic resume, periodic and terminal exact verification, `status.json` and `PROGRESS.md` (Windows) |
| `export_legacy35.py` | writes a 32-block dual in the 35-slot layout read by `search/exactify_five_root.py`; the three excluded slots are empty |
| `verify_candidate32.py` | snapshot, export, exact conversion with both complete integer scans, and exact comparison with the six-hour bound and with the best earlier candidate of the run |
| `validate_model32.py` | preflight: comparison of the 32-block model with the 35-slot implementation, round trip of the six-hour certificate, rejection of corrupted inputs |
| `report_unlimited32.py` | writes `REPORT.md` in a run directory |

Every native file stores the model identity (the 32 dimensions, the block
indices, the five-root type masks and the hashes of the ordered flag bases)
and is rejected on a mismatch. Checkpoints keep the retained graphs, the
directions, the counters and the LP basis; three generations are kept, each
with a SHA-256 sidecar.

The records of the run of September 18, 2026 are in
[`results_unlimited32_20260918/`](results_unlimited32_20260918/README.md): the
report, the final audit, the per-iteration history, every exact verification,
the final floating-point dual, and its certificate at the experiments' scale
`M = 2000000`. The certificate at `M = 8000000` is the main certificate,
`certificate/K4_turan_order7_certificate.json`. See the
[reproduction guide](../docs/reproduction.md#continuation-to-convergence) for
the commands.

## Starting a new campaign

Use `python experiments/reproduce.py` to inspect all 43 tasks, then add `--run`
to execute them on Windows under the recorded 40 GiB cap. `--select TASK_ID`
selects one task. This entry point builds missing caches and validates models;
it needs no historical `status.json`. See the [reproduction guide](../docs/reproduction.md).
The old supervisors below preserve the historical campaign workflow and require
its state; they are not the fresh-checkout entry point.

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

Each worker writes `run.json`, `history.jsonl` and `best_dual.npz`;
`reproduce.py` additionally verifies the final SVD and uncompressed candidates
and all available checkpoints under `exact/`. The supervisors add `supervisor.json` and sampled
process-tree memory. Runs are not bit-for-bit reproducible across machines;
their exact certificates are verified from scratch after each search.
