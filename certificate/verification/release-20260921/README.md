# Full release build: PASS

Commit `8bf9d8d286bb409ae922393a261b08648b2b6d79` was compiled with Lean
4.27.0 on Windows, starting without a project build cache. The build began
on September 21, 2026 at 14:06:32 KST and completed on September 22 at
00:43:48 KST: 10 hours 37 minutes 15 seconds, including a memory failure
and recovery. Pinned Mathlib dependency caches were downloaded.

All 246 project modules compiled successfully. The final `lake build`
passed, as did all 49 FullSevenLong coefficient sweeps, both final
theorems, the literal-fraction witnesses for
`312372062889819/560000000000000`, and the axiom audit of 17 declarations.
The final theorems have the documented five-axiom footprint, with no
`sorryAx`. All project source hashes remained unchanged.

## Records

- [attempt-02/verification/formalization.json](attempt-02/verification/formalization.json)
  is the new PASS record for the public commit.
- [attempt-02/full-library.log](attempt-02/full-library.log) records the
  successful full library build (2891 jobs including dependencies).
- [attempt-02/verification/lean-axioms.log](attempt-02/verification/lean-axioms.log)
  records the axiom audit; [PinnedHeadline.lean](attempt-02/verification/PinnedHeadline.lean)
  contains the two literal-bound witnesses.
- [attempt-02/status.json](attempt-02/status.json) records every command,
  exit code, timing, and stage-log hash of the successful recovery.
- [initial-source-hashes.json](initial-source-hashes.json) freezes all 246
  project modules before the first attempt. The original fresh coefficient
  sweep builds are recorded in [verification/sweeps/](verification/sweeps/).
- [status.json](status.json) and [verification/lean-headline.log](verification/lean-headline.log)
  preserve the first attempt and its memory errors.
- [SHA256SUMS](SHA256SUMS) covers the archived records and logs byte for byte.
  Machine-local path prefixes in the original records were replaced by
  `<repo>` (the parent directory of the build checkout) and `<home>` before
  publication; the hashes in `status.json` and `SHA256SUMS` cover the
  distributed bytes.

## Resource settings and warnings

The first attempt used 12 Lean threads, batches of 12 new coefficient
sweeps, and a 40 GiB process-tree memory cap. All 49 new sweeps passed.
The subsequent headline build started older supporting sweep modules
concurrently and exceeded that cap.

The recovery reused successful artifacts from the same unchanged checkout.
It built every project module in dependency order, with at most two project
targets per invocation and four Lean threads, before the full library
build and the official verifier. Its peak recorded job commit usage was
33.04 GiB. The final verifier reused these freshly produced artifacts;
its short timing is not a clean-build benchmark.

The successful recovery has no compiler errors. Its
[57 distinct warning locations/messages](attempt-02/warnings.txt) concern
unused variables or simp arguments, deprecated names, and style suggestions.
No proof source changes were needed. The historical September 14 record
in the parent directory remains unchanged.

From the repository root, check this archive's hashes, source correspondence,
build results, sweep coverage, and axiom record without recompiling:

```sh
python scripts/check_release_evidence.py
```
