# Preflight summary (2026-09-18)

All checks ran with the campaign virtual environment (Python 3.12.4, NumPy 2.0.2, SciPy 1.13.1,
highspy 1.15.1, MinGW GCC 13.2.0) against a fresh cache in `cache/` (`components.npz` copied with
identical SHA-256 from the six-hour campaign; both oracle libraries recompiled from current sources).

| Check | Result | Evidence |
| --- | --- | --- |
| Model manifest: 32 blocks, 23 five-root types, ordered bases equal to the six-hour run, no `2*l-s=5` block | passed | `validation/validation.json`, `validation/model_manifest.json` |
| Coefficient matrices of all 32 blocks equal the historical implementation on the empty graph, construction graphs, the baseline maximizer and further K4-free graphs; independent Python enumeration of blocks 0 to 8; ordered five-root sums; `S = -3[[f^2]]` sign and normalization | passed | `validation/validation.json` |
| Whole-candidate evaluation with random signed tau and off-diagonal Grams, embedded into the 35-slot model with zeros only in slots 1, 3, 4 | passed (difference 0 up to 1e-13) | `validation/validation.json` |
| Pinned baseline: SHA-256, empty excluded slots, float reprice, integer roundtrip through the 32-to-35 adapter | passed | `validation/validation.json` |
| Baseline through native format, adapter and exactifier (`cuts`, M = 2000000) | exactly 312372062889819/560000000000000, 794 rows, maximizer 4840262484 | `baseline-check/candidates/baseline-roundtrip-cuts/` |
| Misindexed, wrong-identity, perturbed and stale-claim inputs | rejected or disagree | `validation/validation.json` |
| Legacy checkpoint migration: 6,339 masks, 2,322 directions, none in legacy blocks 1, 3, 4; best dual has empty excluded factors; all 1,016 best-dual directions already present; inherited value recomputed by a complete scan (0.55780700211698) | passed | `resume-A/attempts/attempt-001/run.json` |
| Migrated inherited dual through the verification pipeline (svd 1e-7, M = 2000000) | exactly the baseline fraction | `supervisor-test/candidates/20260918-031046-*/verification.json` |
| Smoke run, save, reload and resume (4 straight iterations against 2 + resume + 2) | restricted objective after resume differs by 2.2e-12; model, settings (`time_limit_seconds = null`) and incumbent survive | `resume-A`, `resume-B` |
| Durable supervisor: WMI-owned hidden process, worker start, status files, concurrent verification, graceful stop marked interrupted (never converged), final verification | passed | `supervisor-test`, `supervisor-test2` |

Settings that differ from the inherited ones (recorded in every `run.json`):

1. The native runner sets the HiGHS option `small_matrix_value` to 1e-12 (the HiGHS minimum) instead of its
   default 1e-9. Feasibility tolerances stay at 1e-9, one LP thread, two scan threads.
2. Hidden processes not descended from a foreground application are power-throttled by Windows 11 (every stage
   twice as slow). Worker and verifier opt out per process (`ProcessPowerThrottling`); no system setting is changed.
3. A cold LP solve without a basis takes more than 50 minutes at this size, so the final audit rebuilds the LP in a
   new solver instance from W and the directions and reuses the previous basis statuses only as a starting point.

Sandbox runs already produced a verified certificate below the baseline (15618582357403/28000000000000);
production keeps its own `exact/` records.
