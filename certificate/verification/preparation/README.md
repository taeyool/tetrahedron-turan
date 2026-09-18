# Preparatory FullSevenLong builds

These logs record the first builds of the `FullSevenLong` chain on this
machine, in three bounded stages, before `verify_full_seven_long.py` was run.
They are operational timing evidence only; the tracked
[`../formalization.json`](../formalization.json) is the authority for the
complete formalization result.

| Log | Content | Wall clock |
| --- | --- | --- |
| `stage1-data.log` | 21 five-root data modules, 3 old-family factor modules, Ext56/RootingReindex/Sym3RootingReindex/Mask6Inj (LEAN_NUM_THREADS=8) | 3m45.295s |
| `stage2-semantics.log` | five-root semantic modules through FiveRootSem and FiveRootSOS, Blocks, Column, Check (LEAN_NUM_THREADS=8) | 13m19.949s |
| `stage3-headline.log` | all 49 sweeps, BlockCheck/BlockElt/DegreeCheck, the remaining chain, TetrahedronDifferential, TetrahedronBoost, TetrahedronLongHeadline in one Lake invocation (LEAN_NUM_THREADS=12) | 174m45.604s |

[`operational.json`](operational.json) extracts every Lake `Built` line with
its module and elapsed time. The 49 sweep leaves took between
579 and 3217 seconds each (median
2150 s) with twelve Lake jobs running
concurrently; these overlapping timings are not a clean-build benchmark.

`SHA256SUMS` lists the archived files; check it from this directory with
`sha256sum -c SHA256SUMS`.
