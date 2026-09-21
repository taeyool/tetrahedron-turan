# Historical experimental evidence

This bundle accompanies the 39 one-hour trials, three six-hour trials and
independent one-hour M6 reference reported in the paper. It contains:

- final SVD-compressed and uncompressed integer certificates;
- available exact checkpoint certificates and their verification records;
- run settings, iteration histories, update logs, resource measurements and
  supervisor records;
- 62 executed versions of the released search, experiment and verifier
  source modules, including versions before repairs;
- the environment and the original publication-input hashes.

The bundle contains 1,419 named files, stored in 1,214 compressed objects
(approximately 297 MiB). Identical distributed files share one object.
Missing checkpoint candidates remain missing; no interpolation or new
experiment results have been introduced.
All 224 reported checkpoint slots are mapped explicitly: 171 have a verified
certificate and 53 have no completed candidate.

`manifest.json` maps historical paths from `results.json` to compressed
objects. Its `runs` list identifies each final certificate, and
`source_versions` identifies the actual historical code rather than assuming
the current source was used for every run. Only source modules relevant to
the released pipeline are bundled; hashes of unrelated development modules
in the original records remain provenance information.

Personal repository prefixes in text have been replaced by `<repo>`.
`original_sha256` refers to the original archived bytes; `sha256` refers to
the distributed bytes. `reported_sha256`, when present, is the original
publication manifest's hash. These are intentionally separate. Parts of a
compressed object are concatenated in order before gzip decompression.

Large floating-point NPZ arrays, coefficient caches and solver binaries are
not included. They are unnecessary to check the integer certificates.
Original dual hashes remain in the records, but do not assert that those
numerical arrays are distributed. New searches regenerate their own arrays.
Historical source snapshots retain their original layout and are evidence,
not the fresh-checkout entry point; use `experiments/reproduce.py` to run.

## Inspect and extract

Run from the repository root:

```sh
python experiments/evidence.py --check
python experiments/evidence.py --list
python experiments/evidence.py --extract ".research-repro/section6-campaign-20260910-01/runs/M7-no5/rep-01/exact/final-svd/certificate.json" --output .research-repro/extracted-no5.json
python -X utf8 experiments/runtime.py experiments/verify_evidence.py --certificate .research-repro/extracted-no5.json --cache .research-repro/recheck-no5 --output .research-repro/recheck-no5.json
```

`--check` verifies every compressed and uncompressed hash and matches all
reported final fractions and available checkpoint certificates to the
summary. This is an integrity check, separate from coefficient verification.
`verify_evidence.py` checks M6 certificates over all 964 six-vertex classes
by two counting paths; M7 certificates use two full integer scans of all
13,051,375 extensions. Neither command runs Lean. Extraction refuses to
overwrite an existing file.

The figures can be regenerated directly from `figures/plot-data.json`; no
historical directory tree needs to be reconstructed.
