# Continuation to convergence (September 18, 2026)

These are the records of the search that produced the certificate of the
main theorem (paper, Appendix C.3). The six-hour `LP-CUT-CG` search on
`M7-all5` was continued from its final state (6339 retained coefficient
inequalities and 2322 vectors) without a time limit, on the 32-block model
`M7-all5-32` and with the HiGHS option `small_matrix_value` set to `1e-12`.
It met all convergence tests after 493 further iterations and 7.7 hours of
search time. At termination `U − B = 5.6e-10` and every block had smallest
eigenvalue at least `−9.7e-8`.

| File | Contents |
| --- | --- |
| `REPORT.md` | the report written at the end of the run: initialization and model migration, settings, elapsed times, stopping status, final residuals, bounds, and the rounding study over the scale `M` |
| `final_audit.json` | the final convergence audit (iteration 492) with all residuals and tests |
| `history.jsonl` | the per-iteration log |
| `config.json` | the supervisor configuration |
| `model_manifest.json` | the 32 active blocks `(s, l, sigma, dimension, ordered_basis_sha256)` |
| `PREFLIGHT.md`, `preflight-validation.json` | the checks that preceded the launch |
| `verifications.jsonl`, `best_verified.json` | all exact verifications of the run and the strongest verified certificate |
| `final_converged.npz` | the audited final floating-point dual `(τ, Q)` in the 32-block format, from which both certificates below were rounded |
| `final_primal.npz` | the final LP solution: the retained seven-vertex graphs and their weights |
| `unlimited32-certificate-M2000000.json`, `.summary.json` | the certificate at the scale of the experiments, `M = 2000000`: `139447364189/250000000000 = 0.557789456756`, 780 factor vectors |
| `unlimited32-certificate-M8000000.summary.json` | the summary of the certificate at `M = 8000000`: `14993367693127837/26880000000000000 = 0.557788976678863…`, 780 factor vectors |
| `publication-manifest.json` | the SHA-256 hashes of the original and the distributed files |

The certificate at `M = 8000000` is the main certificate of this repository,
[`certificate/K4_turan_order7_certificate.json`](../../certificate/K4_turan_order7_certificate.json),
and the input of the Lean proof. Both certificates passed the complete
independent scan of all 13,051,375 raw extensions, the cross-check against
the search's own coefficient evaluator in exact mode, and the direct
ordered-root checks. Numerical convergence of the search is not a premise of
the bound: the integer verifiers and the Lean proof check the certificate
alone.

To rebuild either certificate from `final_converged.npz`, see the
[reproduction guide](../../docs/reproduction.md#continuation-to-convergence).

The records were written on the machine that ran the search and describe its
layout: the run directory `.research-repro/unlimited32-20260918-022937/`,
whose subfolders (`attempts/`, `candidates/`, `exact/`, `incumbent/`,
`preflight/`) the report and the preflight summary refer to, and the tooling
under `paper/research/experiments/section6/` instead of `experiments/`. The
"baseline" of these records is the six-hour certificate, now
[`certificate/legacy/K4_turan_order7_six_hour_certificate.json`](../../certificate/legacy/K4_turan_order7_six_hour_certificate.json).
Before publication, the personal directory prefix of every recorded path was
replaced by `<repo>`, the names of unrelated untracked files were removed
from the worktree status quoted in `REPORT.md`, and `REPORT.md` and
`PREFLIGHT.md` were abridged; `publication-manifest.json` lists the original
and the distributed hashes. The report calls the paper
update and the Lean formalization follow-up tasks; the bound has since been
formalized (see [`docs/lean-proof.md`](../../docs/lean-proof.md)). The
checkpoint of the six-hour run that the search started from, the
intermediate checkpoints and the coefficient caches are large numerical
arrays and are not distributed.
