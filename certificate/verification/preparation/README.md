# Preparatory FullSevenConverged builds

These logs record the first builds of the `FullSevenConverged` chain on this
machine, in bounded stages, before `verify_full_seven_converged.py` was run.
They are operational timing evidence only; the tracked
[`../formalization.json`](../formalization.json) is the authority for the
complete formalization result.

| Log | `LEAN_NUM_THREADS` | Status | Wall clock |
| --- | ---: | --- | --- |
| `stage1-data.log` | 8 | ok | n/a |
| `stage2-semantics.log` | 8 | ok | n/a |
| `stage3-headline.log` | 12 | ok | n/a |

Stage 1 built the 21 five-root data modules and the 3 old-family factor
modules. Stage 2 was intended for the five-root semantic modules, `Blocks`,
`Column` and `Check`; because `FiveRootExpand` imports `Reduce`, whose closure
contains `Bound` and hence all 49 sweeps, that Lake invocation also built the
sweeps and the rest of the chain below the headlines with eight jobs. Stage 3
then built the remaining modules and the three headline targets.

[`operational.json`](operational.json) extracts every Lake `Built` line of a
`FullSevenConverged` module with its elapsed time. The 49 sweep leaves took
between 3119 and 5257 seconds each (median
3454 s) under the stated parallelism; these
overlapping timings are not a clean-build benchmark.

`SHA256SUMS` lists the archived files; check it from this directory with
`sha256sum -c SHA256SUMS`.
