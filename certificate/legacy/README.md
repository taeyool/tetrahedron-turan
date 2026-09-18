# Earlier certificates used as structural inputs

These three JSON files are earlier exact certificates of this project for the
same problem, with blocks of at most four roots. They are **not** part of the
proof of the main theorem. They are kept because the search and verification
code reads the shared flag bases, the 964 six-vertex representatives, the
block normalizations and the older factor tables from them:

| File | Read by | Used for |
| --- | --- | --- |
| `K4_turan_order7_exact_certificate.json` | `search/reconstruct_optimization.py`, `search/analyze_certificate.py` | six-vertex representatives and block structure of the optimizer; the coefficient cache |
| `K4_turan_order7_symmetry_compressed_certificate.json` | `scripts/exact_certificate/derive_full_seven_long_chain.py`, `search/analyze_certificate.py` | structural check that the certificate being formalized uses the same representatives, blocks and normalizations |
| `K4_turan_order7_reconstructed_certificate.json` | `search/exactify_five_root.py` | schema baseline for the five-root verifier |

`../verify_K4_turan_order7_certificate.py` can verify these older files
exhaustively; it does not handle the five-root blocks of the main certificate.
Their `reconstruction` fields name research archives that are not distributed.
