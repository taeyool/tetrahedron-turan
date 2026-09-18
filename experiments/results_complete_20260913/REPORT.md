# Computational evaluation: completed campaign report

This report was written during the experiments, before the paper's final
section numbering; its "Section 6" is the paper's Section 5 and Appendix C.

The selected matrix contains **13 configurations and 39 fresh production trials**, each configuration repeated three times. The September 11-13 completion campaign added 18 productions, three separate fresh six-hour studies, and an independent one-hour M6 native reference. All new final candidates passed model-specific integer verification. The original 21 trials are included unchanged.

The completion controller finished after 54.34 elapsed hours, including setup, pilots, diagnostics, repaired attempts, searches and verification. Its 48 tasks are orchestration units, not 48 scientific configurations. Paper authoring time is additional. Every new production has status `time_limit`; none is presented as a converged SDP optimum. The original M6 SDP-FULL iteration-limit outcomes remain labeled `numerical_failure`.

## Main findings

On each seven-vertex model, LP-CUT-CG gives the strongest one-hour exact certificate among the four measured pipelines. Full LP-CUT reaches the shared numerical targets more slowly and stores all 1,295,600 configuration columns. Generated SDP reduces memory substantially relative to full SDP, but leaves unresolved restricted-master feasibility and produces weaker certificates. These are observations about the pinned implementations and declared policies, not universal complexity or solver rankings.

## Production endpoints

Bounds and times below are medians [minimum, maximum] of three repetitions. Numerical targets were frozen before this completion campaign: 0.5628 (M7-no5), 0.5646 (M7-all5), and 0.5617 (M6). A missing target time is censored, not an invented timeout value. RSS is sampled process-tree resident memory, distinct from kernel-recorded commit memory.

| Model | Method | Exact SVD bound | Search seconds | Target seconds | Median RSS GiB | Status |
| --- | --- | --- | --- | --- | ---: | --- |
| M6 | LP-CUT | 0.561670318397 [0.561670318397, 0.561670318397] | 5.156 [5.062, 5.234] | 3.500 [3.421, 3.547] | 0.255 | completed |
| M6 | LP-CUT-CG | 0.561669244574 [0.561669244574, 0.561669244574] | 6.906 [6.891, 7.203] | 5.359 [5.297, 5.390] | 0.210 | completed |
| M6 | SDP-CG | 0.572865345909 [0.572865345909, 0.572865345909] | 3595.469 [3595.438, 3595.469] | not reached | 0.209 | time_limit |
| M6 | SDP-FULL | 0.561665585236 [0.561665585236, 0.561665585236] | 2129.906 [2089.438, 2163.516] | 2129.875 [2089.406, 2163.485] | 0.231 | numerical_failure |
| M7-all5 | LP-CUT | 0.560454252478 [0.560454252478, 0.560454252478] | 3603.328 [3603.328, 3606.047] | 679.703 [677.032, 681.109] | 15.663 | time_limit |
| M7-all5 | LP-CUT-CG | 0.558581395366 [0.558581395366, 0.558581395366] | 3610.437 [3603.985, 3611.719] | 290.235 [289.437, 291.563] | 2.118 | time_limit |
| M7-all5 | SDP-CG | 0.596480377283 [0.596480377283, 0.596480377283] | 3259.438 [3253.500, 3261.140] | not reached | 2.896 | time_limit |
| M7-all5 | SDP-FULL | 0.617248271542 [0.617225865865, 0.617248271542] | 3404.594 [3382.625, 3404.610] | not reached | 28.731 | time_limit |
| M7-lift6 | LP-CUT-CG | 0.561671088720 [0.561671088720, 0.561671088720] | 1188.485 [1186.266, 1191.062] | 284.594 [284.313, 285.312] | 0.558 | completed |
| M7-no5 | LP-CUT | 0.561797610593 [0.561797610593, 0.561857102633] | 3593.797 [3464.265, 3598.828] | 1899.625 [1894.016, 1906.828] | 15.053 | time_limit |
| M7-no5 | LP-CUT-CG | 0.559209644128 [0.559209644128, 0.559209644128] | 3602.235 [3600.860, 3603.141] | 298.594 [298.375, 299.813] | 0.988 | time_limit |
| M7-no5 | SDP-CG | 0.568804336858 [0.568730807531, 0.568855004904] | 3600.484 [3580.062, 3618.578] | not reached | 1.160 | time_limit |
| M7-no5 | SDP-FULL | 0.615533579739 [0.615533579739, 0.653791939462] | 3533.125 [3521.407, 3548.250] | not reached | 24.174 | time_limit |

The matched-target median LP-CUT / LP-CUT-CG search-time ratios are 6.36 for M7-no5 and 2.34 for M7-all5. They include the full-LP memory policies described below; no ratio is assigned to SDP arms that did not reach the target. For LP-CUT-CG, enlarging only host order (M6 to M7-lift6) does not improve the rounded finite-budget certificate, while the additional order-seven and five-root square families do. Relaxation nesting does not imply monotone time-limited outcomes.

## Cost, residuals and exact representations

All stage timings include completed work even if the last evaluation was late. Candidate selection excludes late evaluations. Native-call time includes model assembly and backend work, while the separate eigen column is the exported-moment diagnostic and LP separation outside native cones. Row updates, file I/O, recycling, and finalization explain the remainder; component medians need not add to a median total.

| Model | Method | Init s | Solver/call s | Eigen s | Pricing s | Final columns | Final cuts |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| M7-all5 | LP-CUT | 0.781 | 1578.125 | 11.736 | 365.333 | 1295600 | 383 |
| M7-all5 | LP-CUT-CG | 0.563 | 384.923 | 104.350 | 2930.592 | 5078 | 2792 |
| M7-all5 | SDP-CG | 0.594 | 3172.236 | 3.501 | 79.140 | 11758 | 0 |
| M7-all5 | SDP-FULL | 0.797 | 3372.625 | 0.547 | 11.265 | 1295600 | 0 |
| M7-no5 | LP-CUT | 0.766 | 1208.312 | 0.204 | 230.892 | 1295600 | 229 |
| M7-no5 | LP-CUT-CG | 0.562 | 725.103 | 2.611 | 2787.829 | 2859 | 2328 |
| M7-no5 | SDP-CG | 0.547 | 3477.891 | 0.125 | 120.592 | 6688 | 0 |
| M7-no5 | SDP-FULL | 0.750 | 3514.141 | 0.000 | 9.328 | 1295600 | 0 |

Every new production endpoint is listed below; complete fractions, integer-entry counts, scale, factorization, residuals, source hashes, ordered bases, timing and certificate paths are in `results.csv` / `results.json`. All fractions use the common primary SVD policy, with uncompressed rounding reported alongside it. No algorithm ordering is reversed by the rounding choice.

| Model / method / repetition | SVD exact fraction | Factors | Uncompressed exact fraction | Min moment eigenvalue |
| --- | --- | ---: | --- | ---: |
| M7-no5 / SDP-FULL / 1 | 86174701163427/140000000000000 | 339 | 258524099442223/420000000000000 | -0.06843 |
| M7-all5 / SDP-FULL / 1 | 345659032063647/560000000000000 | 8687 | 345659029852419/560000000000000 | -0.052827 |
| M7-all5 / SDP-CG / 1 | 16701450563937/28000000000000 | 14836 | 4175362704641/7000000000000 | -0.0034425 |
| M7-no5 / LP-CUT / 1 | 1123714205267/2000000000000 | 138 | 1123714790993/2000000000000 | -0.00022762 |
| M7-no5 / SDP-CG / 1 | 5732806539912449/10080000000000000 | 492 | 5732806557582707/10080000000000000 | -0.00063678 |
| M7-all5 / LP-CUT / 1 | 280227126239/500000000000 | 219 | 33627246150473/60000000000000 | -5.8956e-05 |
| M7-all5 / SDP-FULL / 2 | 345646484884529/560000000000000 | 8720 | 345646488486549/560000000000000 | -0.057646 |
| M7-all5 / SDP-CG / 2 | 16701450563937/28000000000000 | 14836 | 4175362704641/7000000000000 | -0.0034425 |
| M7-no5 / LP-CUT / 2 | 235954996449037/420000000000000 | 139 | 3932583679497/7000000000000 | -0.00059231 |
| M7-no5 / SDP-CG / 2 | 179189326544831/315000000000000 | 492 | 39819851222731/70000000000000 | -0.001915 |
| M7-all5 / LP-CUT / 2 | 280227126239/500000000000 | 219 | 33627246150473/60000000000000 | -5.8956e-05 |
| M7-no5 / SDP-FULL / 2 | 86174701163427/140000000000000 | 339 | 258524099442223/420000000000000 | -0.06843 |
| M7-all5 / SDP-CG / 3 | 16701450563937/28000000000000 | 14836 | 4175362704641/7000000000000 | -0.0034425 |
| M7-no5 / LP-CUT / 3 | 235954996449037/420000000000000 | 139 | 3932583679497/7000000000000 | -0.00059231 |
| M7-no5 / SDP-CG / 3 | 497703794751/875000000000 | 495 | 716693462962219/1260000000000000 | -0.0039718 |
| M7-all5 / LP-CUT / 3 | 280227126239/500000000000 | 219 | 33627246150473/60000000000000 | -5.8956e-05 |
| M7-no5 / SDP-FULL / 3 | 13075838789243/20000000000000 | 337 | 5230335387673/8000000000000 | -0.063612 |
| M7-all5 / SDP-FULL / 3 | 345659032063647/560000000000000 | 8687 | 345659029852419/560000000000000 | -0.052827 |

Full-native SCS has large residuals: no5 primal 0.107-0.132, dual 0.131-0.156, gap 0.0208-0.0234; all5 primal 0.279-0.358, dual 0.204-0.221, gap 0.0363-0.0468. Its last moment vectors are not feasible certificates of relaxation optima. Full-universe exact evaluation of the exported integer squares yields valid, but weak, upper bounds despite this. The stopping statuses are `optimal_inaccurate` / `time_limit`, not numerical convergence. The native iteration counts (no5 97/97/99, all5 55/54/55) differ because stopping is based on wall time. Generated SDP also has substantial moment violations; those residuals and PSD repair magnitudes are preserved in the individual rows.

## Longer studies

The earlier saved masters did not support exact continuation of their internal solver state. The longer studies therefore started as separate fresh repetition 1, selected before results, with a six-hour budget. They are not fourth main repetitions or continuations of whichever short trial happened to be best. M6 and M7-lift6 LP-CUT-CG had already passed their stopping tests and were not extended.

| Study | One-hour exact SVD bound | Six-hour exact SVD bound | Factors at six hours | Search s |
| --- | --- | --- | ---: | ---: |
| M7-no5 / LP-CUT-CG | 15657870035573/28000000000000 | 93898077539659/168000000000000 | 437 | 21609.313 |
| M7-all5 / LP-CUT-CG | 9773183281611/17500000000000 | 312372062889819/560000000000000 | 794 | 21609.766 |
| M6 / SDP-FULL | not available; separate reference below | 16849596538693/30000000000000 | 80 | 21595.266 |

M7-no5 improves from 0.559209644128 to 0.558917128212. The repaired M7-all5 long study improves from its own one-hour value 0.558467616092 to 0.557807255160. That all5 trajectory adds a validated PSD-cut fallback when pricing repeats existing columns; 204 fallback updates occurred. It is a separately disclosed longer-run policy, so its one-hour checkpoint does not replace the earlier main LP-CUT-CG repetitions. Both six-hour LP searches remain time-limited. Their last evaluations finished after budget (overshoot 9.313/9.766 s) and were excluded; the saved best candidates were available before 21,600 s.

The M6 six-hour native run exposes only its final candidate, not intermediate iterates. An independent fresh one-hour run under the same extended native iteration ceiling gives 404395939151293/720000000000000 = 0.5616610265990181 (84 factors); the six-hour result is 16849596538693/30000000000000 = 0.5616532179564333 (80 factors). They are two independent executions, not points of a single exposed native trajectory. Neither supplies an exact primal/dual enclosure.

The best new research certificate is **312372062889819/560000000000000 = 0.5578072551603911**, with 794 integer-square factors. It is the certificate of the paper's main theorem. It is distributed as [`certificate/K4_turan_order7_certificate.json`](../../certificate/K4_turan_order7_certificate.json), and its Lean formalization is recorded under [`certificate/verification/`](../../certificate/verification/README.md).

## Settings, validation and repaired attempts

The campaign retains every actually executed source snapshot and SHA-256 manifest. Windows 11, i7-14700K (20 physical/28 logical cores), 63.72 GiB physical RAM, balanced power plan; Python 3.12.4, NumPy 2.0.2, SciPy 1.13.1, HiGHS 1.15.1, SCS 3.2.8, CVXPY 1.6.5, OpenBLAS 0.3.27, MinGW GCC 13.2.0. Solver and BLAS use one thread, exhaustive pricing two. The additional campaign uses schedule seed 611, one experiment at a time, and an enforced 40 GiB process-tree commit cap. Initialization allows 3600 s, search 3600 s plus 60 s watchdog grace; exact jobs have separate limits. The initial schedule was changed only to place repair gates and dependent pilots before affected fresh repetitions.

All models keep stationarity and the specified bases. Seven-vertex enumeration has 1,295,600 canonical classes from 13,051,375 raw extensions, with 504,000 relabeling checks. Complete coefficient caches occupy 17,930,331,144 bytes (no5) and 20,417,604,732 bytes (all5); measured construction takes 110.203 and 132.328 s. Native CSC caches take 12,127,128,520 and 13,786,775,880 bytes, constructed in 92.391 and 294.703 s. These shared cold costs are not included in warm initialization or search time.

Full LP uses bounded coefficient reads and chunked insertion, retaining all configurations. The common memory guard caps projected coefficients at 500 million and retains all dual-active cuts; the old generated/m6/lifted groups never approached that threshold. All5 full LP uses this policy. Repeated no5 memory failures required a stricter 300 million ceiling (229 cuts plus two base rows at full columns), preserving all active cuts and admitting the largest fitting prefix of up to 80 eigenvalue-ranked violated cuts. Full-instance recycling exports all coefficients, costs, bounds and basis statuses, destroys the old HiGHS instance, and verifies hashes after restoration; all this time counts in search. Internal factorization/scaling is rebuilt. A full-hour pilot exercised 21 successful recycle/solve cycles before three fresh no5 productions. This is a disclosed policy difference, not an identical-policy algorithm ablation.

Full native SDP uses the same auxiliary-marginal mathematical formulation through a validated SCS executable that owns its input CSC, avoiding Python/CVX canonicalization copies. Its indirect solver also owns a transpose. The source version, compiler/BLAS and tolerances are pinned; ownership and deadline instrumentation were validated against stock SCS and the official wheel. Tiny fixtures had stock/owned array equality and maximum wheel difference 2.98e-8 under a 2e-7 validation tolerance. Full-model forward/adjoint, sign, off-diagonal scaling and global pricing roundtrips passed.

Earlier full-native rho_x=1e-6 and 0.01 attempts failed before the initial work-cache linear solve completed. A pilot-frozen rho_x=100 obtained time-limited candidates and is used consistently in all six fresh full-native productions. This changes SCS splitting/preconditioning, not the mathematical SDP; the feasibility targets remain 1e-8, production ceiling 20 million iterations, and best inner-CG tolerance 1e-12. Generated SDP retains rho_x=1e-6, 300 s restricted-solve limits and model-specific whole-iteration admission reserves. Full-native reserves 30 s (no5) / 150 s (all5) for export/evaluation. Inner-CG residual logs are linear-system diagnostics and must not be called SDP feasibility residuals.

Original allocation failures, unsuccessful conditioning pilots, the two no5 failures after a verified fresh second recycle, and the interrupted redundant no5 trial are all retained as distinct attempts in `attempts.csv`. No failure was deleted or relabeled as convergence. Detailed repair evidence is in the campaign `repairs/` directory, and `attempt-provenance.json` links source/settings to every attempt. Changing settings was followed by validation and fresh repetitions for the affected group; completed unaffected groups were not repeated.

The final audit checks 93 unique new exact artifacts, their source dual hashes, exact fractions, complete-scan records, and candidate eligibility. Across the 39 main trials, 153 of 195 scheduled checkpoint slots have an available verified candidate. The other 42 have no completed native candidate by the scheduled time (12 from earlier M6, 30 from new native arms), and are explicitly missing. Final SVD and uncompressed certificates are retained for every main trial. Exact factor scale is 2,000,000, multiplier denominator M^2 and SVD tolerance 1e-7. Verification runs after timed search. `checkpoints.csv` includes retrospective candidate-availability plus actual verification cost for new candidates; reuse records link to the original cost, not zero-cost fresh certification.

## Artifacts and interpretation

- `results.csv` and `results.json`: 39 main trials, 13 group summaries, new settings/residuals, exact fractions and provenance.
- `long-runs.csv`: three six-hour trials and the independent M6 one-hour reference.
- `checkpoints.csv`: available and missing checkpoints; no late candidate is backdated.
- `attempts.csv`, `attempt-provenance.json`: all 75 task attempts, including pilots, failures and interruptions.
- `seven-methods.pdf` / `.svg`: four pipelines on each seven-vertex model; three observed curves, exact crosses at checkpoint budgets, native first-candidate dots.
- `long-runs.pdf` / `.svg`: fresh six-hour trajectories and separate M6 one-hour reference.
- `validation.json`, `publication-manifest.json`: audit outcomes and SHA-256 links to retained inputs.

Cold setup, file I/O, wall-time admission and differing memory safeguards limit attribution to mathematical algorithms alone. Three deterministic repetitions measure timing and solver variability, not arbitrary initialization robustness. Negative moment eigenvalues prevent a claim of numerical or exact SDP optimality. Integer verification proves the exported upper certificates, not primal feasibility. The excluded historical replay is not counted; its earlier archived comparison remains separate evidence.
