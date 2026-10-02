# Release-material validation

This document records the checks performed on the release materials. The
first table covers the update of October 2026, which replaced the
certificate, the Lean chain and their records with those of the search
continued to convergence. The second table records the checks of September
21–22, 2026 on the materials that the update did not change. All checks ran
on Windows.

## Update to the converged certificate (October 2, 2026)

| Check | Result |
| --- | --- |
| Lean input and generation-manifest preflight | Passed: 241 modules in the released headline closure, 125 frozen inputs |
| Generated Lean modules | The 129 generated modules were regenerated in the release layout from the release certificate. All 142 chain modules have the same code tokens as the originally verified chain after removing comments and whitespace, and so do the 103 certificate-independent modules |
| Full release Lean build | Commit `857fe4b`: all 246 project modules, all 49 coefficient sweeps, both final theorems, literal-bound witnesses and the 17-declaration axiom audit passed; see the [new record](../certificate/verification/release-20261002/README.md) |
| Original Lean record | The original September 28 PASS record, sweep logs and axiom audit are included unchanged. All 344 original module hashes match their archived texts; the 241 released modules have identical code tokens after removing comments and whitespace |
| Main certificate integer check | Two exhaustive implementations agree over all 13,051,375 extensions on the bound 14993367693127837/26880000000000000 |
| Main certificate reconstruction | From `final_converged.npz`, `verify_candidate32.py` with `M = 8000000` reproduces every integer of the main certificate, and with `M = 2000000` every integer of the published certificate 139447364189/250000000000; only provenance fields differ |
| Six-hour certificate | At its new location under `certificate/legacy/`, both exhaustive implementations agree on 312372062889819/560000000000000 |
| 32-block model validation | `validate_model32.py` passed in the release layout: coefficient comparisons with the 35-slot implementation, the round trip of the six-hour certificate, and the rejection of corrupted inputs |
| Continuation worker | A two-iteration smoke run of `run_unlimited32.py` from the six-hour certificate completed; import and argument checks passed for all seven continuation scripts |
| Continuation records | All distributed files match `publication-manifest.json`; the personal-path scan of every added file is clean |
| Experiment archive | `experiments/evidence.py --check` passes unchanged: 43 runs, 171 checkpoint certificates, 1,419 files |
| Campaign report | `REPORT.md` and `report_complete.py` changed only to name the six-hour certificate's new location; their two hashes and the certificate path were updated in `publication-manifest.json`, and the other 12 report-file hashes are unchanged |
| Documentation and source | Python and JSON syntax, local Markdown links and whitespace checks passed |

A fresh full Lean compilation of commit `857fe4b` completed in 12 hours
35 minutes, including recovery from a memory failure by reducing build
concurrency. No proof source changes were needed; style and unused-variable
warnings remain. The September 28 original PASS record is preserved
separately. The 7.7-hour continued search itself was not rerun for this
packaging check; its records are those of the original run.

## Checks of September 21–22, 2026 on unchanged materials

| Check | Result |
| --- | --- |
| Experiment archive | All compressed-object and distributed-file hashes pass; original hashes agree with the publication manifest wherever recorded |
| Final result links | All 43 SVD certificates and all 43 uncompressed certificates agree with their reported exact fractions |
| Checkpoint links | All 224 slots are mapped: 171 verified certificates and 53 slots without a completed candidate |
| Historical source versions | All 62 requested versions of the released pipeline modules were recovered; none is missing |
| Repaired M7 exact conversion | Saved M7-no5 and M7-lift6 duals reproduce respectively 15657870035573/28000000000000 and 23590185726251/42000000000000, with both full integer scans agreeing |
| M6 archived certificate | An extracted certificate was independently checked over all 964 classes using both counting paths |
| Fresh M6 workflow | Cache construction, independent model validation, a five-second LP-CUT-CG pilot, memory-policy checks, and exact SVD/uncompressed/checkpoint verification completed |
| Seven-vertex model validation | Both M7-no5 and M7-all5 passed construction, pricing, coefficient and corrupted-export checks |
| Seven-vertex catalogue | Compiled and enumerated 1,295,600 classes covering 13,051,375 raw extensions; 504,000 permuted-label checks passed |
| Native SCS | Built both executables from the bundled 3.2.8 sources. Stock and owned results agreed exactly on both small fixtures; differences from the Python wheel were below 3e-8. The deadline fixture passed |
| Entry points | Import/argument checks passed for 13 entry points; the new plan contains 13 configurations repeated three times, three six-hour trials and one one-hour reference |

The 58-hour experimental campaign and its large full-model coefficient
caches were not regenerated during these packaging checks. Numerical checks
were performed on Windows, not Linux or macOS. The validation record of the
previous release state, including its full Lean build of the 794-factor
chain, is in the history of this repository at the tag
[`arxiv-v1`](https://github.com/taeyool/tetrahedron-turan/blob/arxiv-v1/docs/release-validation.md).

The [reproduction guide](reproduction.md) gives the supported fresh-checkout
workflow. The [experiment evidence guide](../experiments/evidence/README.md)
explains how to extract and independently check a published certificate.
The [Lean record guide](../certificate/verification/README.md) separates the
original proof run, the release source-correspondence check, and the new full
build.
