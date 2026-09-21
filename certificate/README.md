# The certificate

`K4_turan_order7_certificate.json` is the exact seven-vertex flag-algebra
certificate of the paper's main theorem,

```text
π(K₄⁽³⁾) ≤ 312372062889819/560000000000000 = 0.5578072551603910714…
```

Everything in it is integer or rational; no floating-point number enters any
verified quantity. It was produced by the six-hour `LP-CUT-CG` search on the
`M7-all5` model described in Section 5 and Appendix C of the paper, converted
to integers as described in Appendix B.3, and it is the sole input of the Lean
formalization.

## Contents

| Field | Meaning |
| --- | --- |
| `bound_fraction`, `bound_numerator_unreduced`, `common_denominator_unreduced` | the bound, and the maximum integer coefficient `11245394264033484` over `5040 · M² = 20160000000000000` |
| `scale` | the common denominator `M = 2000000` of all factor vectors |
| `stationarity` | the multiplier `τ = 38604309001505 / M²` of the identity `S = 3(ρ² − ⟦d·d⟧₁)` and its six-vertex coefficient convention `(3n₁ − n₂)/60` |
| `H_representatives` | the 964 tetrahedron-free six-vertex 3-graphs as 20-bit edge masks |
| `order6_blocks`, `order6_factors_by_block` | the flag bases and integer factor vectors of the blocks whose products use at most six vertices (only the two four-root blocks σ₄¹ and σ₄² are nonempty, two factors each) |
| `order7_s1_factors`, `order7_s3_nonedge_factors`, `order7_s3_edge_factors` | the 7, 236 and 187 factor vectors of the one-root and the two three-root blocks |
| `order7_s5_blocks` | for each of the 23 five-root types: its identifier, its six-vertex flags, the denominator 5040, and its factor vectors (nonempty for 18 types, 360 rows in total) |
| `factor_counts`, `total_integer_square_factors` | 794 factor vectors, 333,260 integer entries |
| `example_maximizing_raw_mask` | a seven-vertex extension attaining the maximum, `4840262484` |
| `exact_verification` | the record of the two independent integer scans and the ordered-root checks run when the certificate was created |
| `reconstruction` | provenance: the floating-point dual it was rounded from, the SVD tolerance, and the factor counts before compression |

The file's bytes are pinned by SHA-256 in
`scripts/exact_certificate/full_seven_long_common.py` and in the generation
manifests and verification record of the Lean chain. It differs from the copy
written by the search campaign only in the `reconstruction.source_dual`
string, whose personal directory prefix was replaced by `<repo>`; the
campaign records in `experiments/results_complete_20260913/` list the hash of
the campaign's copy.

## Verification

Independent integer verification, without Lean (Python 3.12, the pinned
`requirements.txt`, a C++17 compiler):

```sh
python -X utf8 experiments/runtime.py search/exactify_five_root.py \
  --certificate certificate/K4_turan_order7_certificate.json \
  --cross-check-pricing --threads 2 \
  --cache .research-repro/integer-check --output .research-repro/integer-check.json
```

Formal verification, with Lean (see [docs/lean-proof.md](../docs/lean-proof.md)):

```sh
lake exe cache get
python scripts/exact_certificate/verify_full_seven_long.py \
  --threads 4 --sweep-batch-size 2 --output-dir .research-repro/lean-verification
```

The Lean development does not trust either external scan: it re-derives every
Gram matrix from the integer rows, re-checks every coefficient inequality by
compiled evaluation, and identifies the compiled values with the coefficients
of the flag-algebra expressions. `verification/` holds the tracked record of a
complete run of the driver.

## Other files

| File | Role |
| --- | --- |
| `verification/` | the Lean verification record and the build logs ([README](verification/README.md)) |
| `flag_sdp_hyper3.py` | flag enumeration library: canonical forms, rooted flag catalogues, and densities of 3-graphs on bitmasks; used by the search and by every verifier |
| `h6_all_reps.txt` | canonical masks of all 2136 six-vertex 3-graphs up to isomorphism, of which 964 are tetrahedron-free |
| `exact_certificate_raw_oracle.cpp` | the exhaustive C++ evaluator over all one-vertex extensions of the six-vertex representatives, from which the exact kernels are derived |
| `portable_raw_oracle.py` | rewrites the oracle's bit extraction and threading for compilers without OpenMP or BMI2 |
| `verify_K4_turan_order7_certificate.py` | verifier for certificates in the original schema with at most four roots per block; it does not handle the five-root blocks of the main certificate |
| `legacy/` | three earlier certificates of this project that the code reads for their shared flag bases and representatives ([README](legacy/README.md)) |
