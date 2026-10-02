# Full release build: PASS

Commit `857fe4bc4e9fd63d268a9e1764d1c5ee79c1ab52` was compiled with Lean
4.27.0 on Windows, starting without a project build cache. The build began
on October 2, 2026 at 09:15:34 KST and completed at 21:50:46 KST: 12 hours
35 minutes, including a memory failure and recovery. Pinned
Mathlib dependency caches were downloaded.

All 246 project modules compiled successfully. The final `lake build`
passed, as did all 49 FullSevenConverged coefficient sweeps, both final
theorems, the literal-fraction witnesses for
`14993367693127837/26880000000000000`, and the axiom audit of 17
declarations. The final theorems have the documented five-axiom footprint,
with no `sorryAx`. All project source hashes remained unchanged.

## Records

- [attempt-02/verification/formalization.json](attempt-02/verification/formalization.json)
  is the PASS record for the public commit.
- [attempt-02/full-library.log](attempt-02/full-library.log) records the
  successful full library build (2891 jobs including dependencies).
- [attempt-02/verification/lean-axioms.log](attempt-02/verification/lean-axioms.log)
  records the axiom audit; [PinnedHeadline.lean](attempt-02/verification/PinnedHeadline.lean)
  contains the two literal-bound witnesses.
- [attempt-02/status.json](attempt-02/status.json) records every command,
  exit code, timing, peak memory and stage-log hash of the recovery, and
  [attempt-02/build-plan.json](attempt-02/build-plan.json) its targets.
- [attempt-02/chain-sweeps.log](attempt-02/chain-sweeps.log) records the fresh
  builds of the 49 coefficient sweeps. The batch logs under
  `attempt-02/verification/sweeps/` are the verifier's confirmations of those
  builds.
- [initial-source-hashes.json](initial-source-hashes.json) freezes all 246
  project modules before the first attempt.
- [status.json](status.json) and [base-library.log](base-library.log)
  preserve the first attempt and its memory error.
- [SHA256SUMS](SHA256SUMS) covers the archived records and logs byte for byte.
  Machine-local path prefixes in the original records were replaced by
  `<repo>` (the release checkout; the build ran in its clone
  `<repo>\.research-repro\lv`) and `<home>` before publication. The hashes in
  the two `status.json` files and in `SHA256SUMS` cover the distributed bytes;
  `original_log_sha256` keeps the hash of each log as the build wrote it.

## Resource settings and warnings

Every stage ran under a 40 GiB process-tree memory cap. The first attempt
built the 103 certificate-independent modules in one Lake invocation with
four Lean threads. After 15 minutes the module `TetrahedronOrder5` and
six-vertex completeness sweeps were compiling concurrently and the cap was
exceeded.

The recovery reused the 59 modules already built in the same unchanged
checkout. It built the remaining 44 certificate-independent modules in
dependency order with at most two targets per invocation and four Lean
threads. The first pair, `TetrahedronOrder5` and a completeness sweep, again
reached the cap; the sweep completed and `TetrahedronOrder5` was then built
alone, with a peak job commit of 36.72 GiB, the largest of any successful
stage. The chain followed in bounded stages:

| Stage | `LEAN_NUM_THREADS` | Wall clock | Peak job commit |
| --- | ---: | --- | ---: |
| 44 certificate-independent modules (23 invocations) | 4 | 7 h 0 min | 36.72 GiB |
| 24 chain data modules | 8 | 2 min 20 s | 5.97 GiB |
| chain modules through `Check` | 8 | 20 min 50 s | 1.39 GiB |
| 49 coefficient sweeps | 12 | 4 h 15 min | 12.76 GiB |
| remaining chain and both headlines | 6 | 33 min 5 s | 35.34 GiB |
| full `lake build` | 4 | 13 s | 0.62 GiB |
| official verifier | 8 | 51 s | 0.61 GiB |

The 49 sweep modules took between 1079 s and 5140 s each (median 3556 s)
with twelve Lake jobs running concurrently. The full library build and the
verifier reused the freshly produced artifacts; their short timings are not
clean-build benchmarks.

The recovery has no compiler errors other than the memory failure of the
first pair. Its [57 distinct warning locations](attempt-02/warnings.txt)
concern unused variables, section variables or simp arguments and style
suggestions. No proof source changes were needed. The original September 28
record in the parent directory remains unchanged.

From the repository root, check this archive's hashes, source correspondence,
build results, sweep coverage, and axiom record without recompiling:

```sh
python scripts/check_release_evidence.py
```
