# Release-material validation

Checked on Windows on September 21–22, 2026. The release materials were completed
against the manuscript and the original experiment archives. This document
records the checks performed while repairing the distribution.

| Check | Result |
| --- | --- |
| Lean input and generation-manifest preflight | Passed: 241 modules in the released headline closure, 125 frozen inputs |
| Full release Lean build | Commit `8bf9d8d`: all 246 project modules, all 49 coefficient sweeps, both final theorems, literal-bound witnesses and the 17-declaration axiom audit passed; see the [new record](../certificate/verification/release-20260921/README.md) |
| Historical Lean record | The original September 14 PASS record, sweep logs and axiom audit were restored unchanged. All 344 historical module hashes match their archived texts; the 241 released modules have identical code tokens after removing comments and whitespace |
| Main certificate integer check | Two exhaustive implementations agree over all 13,051,375 extensions on the bound 312372062889819/560000000000000 |
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
| Existing report | All 14 report-file hashes and both reporting-source hashes remain unchanged |
| Documentation and source | Python/JSON syntax, local Markdown links and whitespace checks passed. The obsolete convergence plot was removed; the three manuscript figures were preserved |

A fresh full Lean compilation of commit `8bf9d8d` completed in 10 hours
37 minutes, including recovery from a memory failure by reducing build
concurrency. No proof source changes were needed; style and unused-variable
warnings remain. The September 14 historical PASS record is preserved
separately. The 58-hour experimental campaign and its large full-model
coefficient caches were not regenerated during this packaging check.
Numerical checks were performed on Windows, not Linux or macOS.

The [reproduction guide](reproduction.md) gives the supported fresh-checkout
workflow. The [experiment evidence guide](../experiments/evidence/README.md)
explains how to extract and independently check a published certificate.
The [Lean record guide](../certificate/verification/README.md) separates the
historical proof run, release source-correspondence check, and new full build.
