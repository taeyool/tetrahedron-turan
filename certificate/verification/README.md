# Lean verification record

The files directly in this directory preserve the completed verification
run of September 28, 2026 (UTC), made in the original repository. Its
`formalization.json` and logs are unchanged. A separate
[release build record](release-20261002/README.md) records the successful
full compilation of public commit `857fe4b` on October 2, 2026, including
all 246 project modules and the complete verifier.
The release certificate is
[`../K4_turan_order7_certificate.json`](../K4_turan_order7_certificate.json).
The numerical search is not part of the Lean proof; only the integer factor
rows of that file are consumed.

- `formalization.json` is written by the driver, with status `PASS` only after
  every stage succeeds: the certificate hash and the generation manifests; all
  49 seven-vertex coefficient sweeps, built in bounded batches; the two
  headline modules `FullSevenConverged.TetrahedronDifferential` and
  `FullSevenConverged.TetrahedronBoost`; the axiom audit
  `AxiomCheckFullSevenConverged.lean`; and an independent witness file that
  type-checks the literal fraction `14993367693127837 / 26880000000000000`
  against both theorems. It records the import closure of the headline
  theorems with the hash of every module, the frozen inputs (build
  configuration, templates, generators, generator support files), the axiom
  footprint of every audited theorem, the log hashes, the Lean version, the
  Git revision, and the thread and batch settings.
- `lean-headline.log`, `lean-axioms.log` and `lean-pinned-headline.log` are
  the logs of the headline build, the axiom audit and the witness; `sweeps/`
  holds the batch reports of the coefficient sweeps.
- `preparation/` preserves the staged first builds of the chain on an Intel
  Core i7-14700K (28 threads, 64 GB, Windows 11), with per-module `Built`
  timings and a `SHA256SUMS` list; see
  [`preparation/README.md`](preparation/README.md). These are operational
  timings, not a clean-build benchmark.

Every file here is stored with `-text`, so the bytes hashed in
`formalization.json` are the bytes checked out.

`release-source-map.json` explains the move from the original repository:
only the certificate's recorded source path changed; its mathematical data
did not. The raw hash of the original certificate file is intentionally
retained in the original record, which names that file by its original path.
The original build hashed 344 modules, including auxiliary targets; the
release headline closure has 241. One auxiliary target, the module
`TetrahedronConvergedHeadline`, restated the bound for definitions of the
original repository and is not released; the original record therefore
audits 21 declarations and the release build 17. The exact original module
texts are in `historical-sources.json.gz`. The 241 released modules have the
same code tokens after removing comments and whitespace.

Check both records, their logs and axiom lists, source hashes, and the
release mapping without running Lean:

```sh
python scripts/check_release_evidence.py
python scripts/exact_certificate/verify_full_seven_converged.py --check-only
```

These checks establish archive integrity and source correspondence. They do
not replace a fresh Lean compilation.

To produce a fresh record, run from the repository root:

```sh
lake exe cache get
python scripts/exact_certificate/verify_full_seven_converged.py \
  --threads 4 --sweep-batch-size 2 --output-dir .research-repro/lean-verification
```

The driver writes to the given directory and leaves this one untouched. Lake
reuses modules that are already built, so the sweep timings of a run over an
existing build are cache confirmations rather than build costs.

The verification record of the earlier 794-factor chain `FullSevenLong`,
which accompanied the first arXiv version of the paper, is in the history of
this repository at the tag
[`arxiv-v1`](https://github.com/taeyool/tetrahedron-turan/tree/arxiv-v1/certificate/verification).
