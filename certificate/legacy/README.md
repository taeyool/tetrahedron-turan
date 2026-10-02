# Earlier certificates

## The six-hour certificate

`K4_turan_order7_six_hour_certificate.json` is the 794-factor certificate of
the six-hour `LP-CUT-CG` search on `M7-all5` (paper, Appendix C.3), with scale
`M = 2000000` and bound

```text
312372062889819/560000000000000 = 0.5578072551603910714…
```

It was the certificate of the main theorem in the first arXiv version of the
paper and was formalized there as the Lean chain `FullSevenLong`; see the tag
[`arxiv-v1`](https://github.com/taeyool/tetrahedron-turan/tree/arxiv-v1).
The main certificate [`../K4_turan_order7_certificate.json`](../K4_turan_order7_certificate.json)
supersedes it. The continuation tooling in `experiments/` pins this file by
hash as its baseline: a new candidate is accepted only if its bound is
smaller, and `--init baseline-certificate` seeds a search from it. It has the
schema of the main certificate and is checked by the same integer verifier:

```sh
python -X utf8 experiments/runtime.py search/exactify_five_root.py \
  --certificate certificate/legacy/K4_turan_order7_six_hour_certificate.json \
  --cross-check-pricing --threads 2 \
  --cache .research-repro/six-hour-check --output .research-repro/six-hour-check.json
```

## Certificates used as structural inputs

The other three JSON files are earlier exact certificates of this project for
the same problem, with blocks of at most four roots. They are **not** part of
the proof of the main theorem. They are kept because the search and
verification code reads the shared flag bases, the 964 six-vertex
representatives, the block normalizations and the older factor tables from
them:

| File | Read by | Used for |
| --- | --- | --- |
| `K4_turan_order7_exact_certificate.json` | `search/reconstruct_optimization.py`, `search/analyze_certificate.py` | six-vertex representatives and block structure of the optimizer; the coefficient cache |
| `K4_turan_order7_symmetry_compressed_certificate.json` | `scripts/exact_certificate/derive_full_seven_converged_chain.py`, `search/analyze_certificate.py` | structural check that the certificate being formalized uses the same representatives, blocks and normalizations |
| `K4_turan_order7_reconstructed_certificate.json` | `search/exactify_five_root.py` | schema baseline for the five-root verifier |

`../verify_K4_turan_order7_certificate.py` can verify these three files
exhaustively; it does not handle the five-root blocks of the main and
six-hour certificates.
Their `reconstruction` fields name research archives that are not distributed.
