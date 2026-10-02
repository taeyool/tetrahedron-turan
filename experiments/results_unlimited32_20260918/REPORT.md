# Unlimited 32-block seven-vertex search (M7-all5-32, LP-CUT-CG)

Report written 2026-09-18 11:23:32. Run directory: `<repo>\.research-repro\unlimited32-20260918-022937`.

## Stopping status

- Supervisor status: **converged**; numerical convergence established: **True**.
- Mode `until_converged`: no wall-time deadline and no iteration limit were configured (`time_limit_seconds=None`, `iteration_limit=None`).
- Completed iterations: 493; cumulative search time: 7.68 h over 1 attempt(s); duplicate-candidate PSD fallbacks: 0; failed audits: 0; prune events: 8 (6967 directions).

## Source, environment and model

- Source revision `7e81898096e629ecced80d2c69e04f5ec5ef5f3a`; local changes at launch:

```text
?? paper/research/experiments/section6/UNLIMITED_32_BLOCK_SEARCH.md
?? paper/research/experiments/section6/export_legacy35.py
?? paper/research/experiments/section6/model32.py
?? paper/research/experiments/section6/report_unlimited32.py
?? paper/research/experiments/section6/run_unlimited32.py
?? paper/research/experiments/section6/supervise_unlimited32.py
?? paper/research/experiments/section6/validate_model32.py
?? paper/research/experiments/section6/verify_candidate32.py
```

- Python `<repo>\.research-repro\section6-campaign-20260909-01\venv\Scripts\python.exe`; memory ceiling 40 GiB; worker options {'scan_threads': 2, 'price_top': 8, 'max_cuts': 80, 'keep_cuts': 3000, 'lp_tolerance': 1e-09, 'lp_solver': 'choose', 'checkpoint_every': 5}.
- Model `M7-all5-32`: 32 blocks (6 six-vertex-table blocks, 26 seven-vertex-product blocks); excluded legacy indices [1, 3, 4] (the three `2*l-s=5` blocks) are not loaded, optimized, separated or serialized. Full manifest: `attempts/attempt-001/model_manifest.json`.

## Initialization

```json
{
  "kind": "continuation_with_block_model_migration",
  "legacy_checkpoint": "<repo>\\.research-repro\\section6-complete-20260911-01\\jobs\\long-M7-all5-LP-CUT-CG\\attempt-02\\master_checkpoint.npz",
  "legacy_checkpoint_sha256": "eaf546c6b63abadac41da2195953240a26790c7de59cfeaa8cb29d7482ee5d7a",
  "legacy_best_dual": {
    "tau": 9.65107725037637,
    "claimed_upper": 0.5578070021169798,
    "excluded_nonzero_rows": {
      "1": 0,
      "3": 0,
      "4": 0
    }
  },
  "legacy_best_dual_sha256": "1ba7801fe03d5d4a7597ed621a1d88940aaacf8d82c74278b00a6aef827961ad",
  "legacy_masks": 6339,
  "legacy_directions": 2322,
  "legacy_directions_in_excluded_blocks": 0,
  "legacy_direction_counts": [
    0,
    0,
    0,
    0,
    0,
    0,
    3,
    2,
    0,
    8,
    1134,
    804,
    23,
    27,
    37,
    16,
    23,
    0,
    0,
    25,
    38,
    41,
    4,
    0,
    1,
    0,
    6,
    29,
    14,
    19,
    31,
    10,
    0,
    18,
    9
  ],
  "legacy_basis_restored_after_exact_identity_check": true,
  "best_dual_directions_added": 0,
  "best_dual_directions_already_present": 1016,
  "inherited_repriced_upper": 0.55780700211698,
  "inherited_repriced_minus_claimed": 2.220446049250313e-16,
  "inherited_maximizer": 27003827629
}
```

Initial |W| = 6339, initial directions = 2322, recomputed inherited numerical value = 0.55780700211698.

## Policy and recorded deviations from the inherited six-hour settings

- `mode` = `until_converged`
- `time_limit_seconds` = `None`
- `iteration_limit` = `None`
- `policy` = `LP-CUT-CG with duplicate-candidate PSD fallback`
- `price_top` = `8`
- `max_cuts` = `80`
- `keep_cuts` = `3000`
- `psd_tolerance` = `1e-07`
- `price_tolerance` = `1e-07`
- `convergence_tolerance` = `1e-07`
- `lp_feasibility_tolerance` = `1e-09`
- `lp_small_matrix_value` = `1e-12`
- `lp_solver` = `choose`
- `lp_threads` = `1`
- `blas_threads` = `1`
- `max_price_top` = `64`
- `scan_threads` = `2`
- `checkpoint_every_iterations` = `5`
- `dense_entry_admission_limit` = `500000000`
- `stationarity` = `True`
- `stationarity_face` = `False`

Runtime policy changes:

- none

## Attempts

| attempt | init | start | end | worker status | supervisor reason | iterations | peak RSS (GiB) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | legacy-checkpoint | 2026-09-18 03:28:32 | 2026-09-18 11:09:27 | converged | None | 0 -> 493 | 1.85 |

## Final audit

- B = 0.5577888893156411, L = 0.5577888893156393, U = 0.5577888898789329
- U-L = 5.632936339594607e-10, B-L = 1.7763568394002505e-15, minimum eigenvalue over 32 blocks = -9.688189481824633e-08
- sum(y)-1 = -7.999156892424253e-13, sum(y s) = 1.3704315460216776e-15, min(y) = 0.0, minimum cut multiplier = -0.0
- max retained coefficient minus B = 5.632918576026213e-10, HiGHS max primal/dual infeasibility = 0.0 / 0.0
- |W| = 6434, directions = 2958, tau = 11.095385220779908
- tests: {'lp_succeeded_and_finite': True, 'complete_scan_finished': True, 'gap': True, 'psd': True, 'normalization': True, 'stationarity': True, 'nonnegative_y': True, 'certificate_weights_nonnegative': True, 'B_consistent_with_L': True, 'retained_graphs_within_B': True, 'cut_rows_feasible': True}

An approximately feasible y does not prove a lower bound on the SDP optimum; numerical convergence and the exact upper-bound certificate below are separate deliverables, not a proved SDP optimum.

## Numerical and exact bounds

- Best numerical upper value U: 0.5577888895418102 (`incumbent/best_numerical.npz`)
- Pinned baseline: 312372062889819/560000000000000 = 0.5578072551603911
- Strongest verified certificate of this run: **14993367693127837/26880000000000000** = 0.557788976678863 (final-polish-svd-tol1e-7-M8000000), 780 integer factor rows, scale 8000000, svd.
- Exact comparison: new < baseline is **True**; baseline - new = 19653023339/1075200000000000 = 1.827848e-05.
- Certificate: `<repo>\.research-repro\unlimited32-20260918-022937\exact\certificate-final-polish-svd-tol1e-7-M8000000.json` (sha256 `7c6f5e76c820e61097dfa3488718e0e53d922b79dae6136b29aa5be34c473f2a`).

## Exact verifications

| label | numerical U | verified fraction | decimal | factors | improves baseline |
| --- | --- | --- | --- | --- | --- |
| 20260918-035835-f05f0b27c658-svd-M2000000 | 0.557803702691724 | 78092584885827/140000000000000 | 0.5578041777559072 | 800 | True |
| 20260918-065850-7f69728bb4f0-svd-M2000000 | 0.5577938588209074 | 312364922192703/560000000000000 | 0.5577945039155411 | 788 | True |
| 20260918-095906-985204121912-svd-M2000000 | 0.5577893986851555 | 44623236125741/80000000000000 | 0.5577904515717625 | 779 | True |
| 20260918-110927-c2cbb9d698a7-svd-M2000000 | 0.5577888895418104 | 15618113867497/28000000000000 | 0.5577897809820357 | 780 | True |
| final-converged-99543b7fa36e-svd-M2000000 | 0.5577888898789327 | 139447364189/250000000000 | 0.557789456756 | 780 | True |
| final-polish-cuts-tol1e-7-M2000000 | 0.5577888898789327 | 78090590695263/140000000000000 | 0.5577899335375929 | 1106 | True |
| final-polish-svd-tol1e-7-M4000000 | 0.5577888898789327 | 156180961478403/280000000000000 | 0.5577891481371535 | 780 | True |
| final-polish-svd-tol1e-8-M2000000 | 0.5577888898789327 | 139447364189/250000000000 | 0.557789456756 | 780 | True |
| final-polish-svd-tol1e-6-M2000000 | 0.5577888898789327 | 139447364189/250000000000 | 0.557789456756 | 780 | True |
| final-polish-svd-tol1e-7-M5000000 | 0.5577888898789327 | 976131111964419/1750000000000000 | 0.5577892068368109 | 780 | True |
| final-polish-svd-tol1e-7-M6000000 | 0.5577888898789327 | 1757035698319/3150000000000 | 0.5577891105774603 | 780 | True |
| final-polish-svd-tol1e-7-M8000000 | 0.5577888898789327 | 14993367693127837/26880000000000000 | 0.557788976678863 | 780 | True |

Every accepted certificate passed: rational factor rows, the independent complete scan of 13,051,375 raw extensions, agreement with the optimization oracle full integer scan (`--cross-check-pricing`), the exactifier direct ordered-root checks, and an exact rational comparison. Legacy slots 1, 3 and 4 are empty serialization padding only.

Paper updates and Lean formalization are separate follow-up tasks; a new computational certificate is not a Lean theorem.


## Addendum: elapsed times, trajectory, rounding study and recovery notes

### Elapsed times

- Six-hour legacy run (35-slot model, `attempt-02` of `section6-complete-20260911-01`): 21,610 s of search,
  831 iterations, ended by its time limit without convergence (204 duplicate-candidate fallbacks).
- This run (native 32-block model): initialization and migration 17.3 s, search 27,632 s (7.68 h) in one
  attempt, 493 iterations (415 direction rounds adding 7,603 directions, 76 graph rounds adding 95 graphs,
  8 prune events removing 6,967 dual-inactive directions, none of them active). Stage totals: LP 21,245 s,
  eigenproblems 247 s, complete scans 5,961 s (two threads, 13,051,375 raw extensions per scan).
  Two LP solves after a single added column took 364 s and 518 s (HiGHS dual phase 1); all other solves
  took under 110 s. Peak process-tree RSS 1.85 GiB against the 40 GiB ceiling. No restart, no failed
  audit, no stage hang, no memory or disk guard was triggered, and no runtime policy change was needed.
- Exact verification: about 200 s per candidate with two threads during the search, about 41 s with eight
  threads after the search.

### Trajectory (attempt 1)

| iteration | search time (h) | B | U | minimum eigenvalue | \|W\| | directions |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | 0.00 | 0.5578065490 | 0.5578065496 | -2.75e-07 | 6339 | 2322 |
| 100 | 1.67 | 0.5577985353 | 0.5577985354 | -2.41e-07 | 6365 | 2840 |
| 200 | 3.39 | 0.5577941154 | 0.5577941158 | -1.99e-07 | 6402 | 2932 |
| 300 | 5.04 | 0.5577911713 | 0.5577911715 | -1.59e-07 | 6426 | 2816 |
| 400 | 6.54 | 0.5577893651 | 0.5577893652 | -1.21e-07 | 6433 | 2454 |
| 492 (audit) | 7.68 | 0.5577888893 | 0.5577888899 | -9.69e-08 | 6434 | 2958 |

Iteration 0 reproduces the last legacy iteration exactly after migration (same B, same eigenvalues; the
legacy basis was reused after an exact identity check, zero simplex iterations). Iteration 491 passed all
in-loop tests; iteration 492 was the fresh audit (new solver instance, all coefficients recomputed from W
and the directions, full spectra, complete scan) and passed every test, so the run ended as converged.

The best numerical value recorded during the search (`incumbent/best_numerical.npz`, iteration 491,
U = 0.5577888895418102) and the audited final dual (`incumbent/final_converged.npz`, U = 0.5577888898789329)
differ by 3.4e-10; both were exactified.

### Rounding study on the audited final dual (all verified, all below the baseline)

| factorization | SVD tolerance | scale M | verified fraction | decimal | rounding loss | rows |
| --- | --- | --- | --- | --- | --- | --- |
| svd | 1e-7 | 2,000,000 (paper default) | 139447364189/250000000000 | 0.557789456756 | 5.7e-07 | 780 |
| svd | 1e-6 or 1e-8 | 2,000,000 | same as above | | | 780 |
| cuts | none | 2,000,000 | 78090590695263/140000000000000 | 0.5577899335375929 | 1.0e-06 | 1106 |
| svd | 1e-7 | 4,000,000 | 156180961478403/280000000000000 | 0.5577891481371535 | 2.6e-07 | 780 |
| svd | 1e-7 | 5,000,000 | 976131111964419/1750000000000000 | 0.5577892068368109 | 3.2e-07 | 780 |
| svd | 1e-7 | 6,000,000 | 1757035698319/3150000000000 | 0.5577891105774603 | 2.2e-07 | 780 |
| svd | 1e-7 | 8,000,000 | 14993367693127837/26880000000000000 | 0.557788976678863 | 8.7e-08 | 780 |
| svd | 1e-7 | 10,000,000 | rejected by the exactifier's int64 overflow guard (not bypassed) | | | |

Recommended deliverables:

- Paper-convention certificate (M = 2,000,000, SVD 1e-7, as in the published 794-row certificate):
  `exact/certificate-final-converged-99543b7fa36e-svd-M2000000.json`, bound **139447364189/250000000000**
  = 0.557789456756, 780 integer factor rows; baseline minus new = 9967106459/560000000000000 = 1.78e-05.
- Strongest verified certificate (M = 8,000,000): `exact/certificate-final-polish-svd-tol1e-7-M8000000.json`,
  bound **14993367693127837/26880000000000000** = 0.557788976678863, 780 rows; baseline minus new =
  19653023339/1075200000000000 = 1.83e-05. Larger integers than the paper convention; whether the Lean
  chain should use it is a separate decision.

Both satisfy `new_verified_fraction < 312372062889819/560000000000000`. Compared with the baseline
(794 rows, maximizer 4840262484), the new certificates have 780 rows.

### Meaning of the result

Numerical convergence at tolerance 1e-7 was established by the fresh audit (`final_audit.json`): LP
optimal and finite, complete scan finished, `U - L = 5.6e-10`, every block's minimum eigenvalue at least
-9.7e-08, `sum(y) - 1 = -8.0e-13`, `sum(y s(G)) = 1.4e-15`, `min(y) = 0`, certificate weights nonnegative,
`B - L = 1.8e-15`, retained graphs within `B + 5.6e-10`, cut rows feasible to 1.7e-16. This is a numerical
statement about the LP-CUT-CG iterate; it does not prove a lower bound on the SDP optimum. The exact
upper bounds above are separate, independently verified deliverables.

### Preflight

`preflight/PREFLIGHT.md` summarizes the checks that preceded the launch (model manifest, coefficient
comparisons with the historical implementation, baseline roundtrip through the 32-to-35 adapter and the
exactifier, corrupted-input rejection, save/reload/resume, supervisor sandbox including a graceful stop).
