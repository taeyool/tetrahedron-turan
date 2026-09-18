# Generating and verifying the certificate chain

The Lean chain `LeanFlagAlgebras/Core/Examples/FullSevenLong/` is tied to the
certificate `certificate/K4_turan_order7_certificate.json`. The scripts here
generate its certificate-dependent modules from that file, and build and audit
the result. Every pinned value, the certificate path and hash, the bound, the
scale, the factor counts, the namespace and the build targets, lives in one
module, `full_seven_long_common.py`, which the other scripts import.

| Script | Role |
| --- | --- |
| `full_seven_long_common.py` | pinned values, template and output locations, the hash convention |
| `derive_full_seven_long_five_root.py` | the 18 five-root factor modules and the flag, automorphism, lookup and ordered-sample data modules (21 modules) with `five_root_manifest.json` |
| `derive_full_seven_long_chain.py` | the 105 certificate-dependent proof modules instantiated from the templates (through `full_seven_assembly.py`), the three one- and three-root factor modules, `AxiomCheckFullSevenLong.lean`, and `manifest.json` recording every replacement site and every hash |
| `full_seven_assembly.py` | the structural extension of the templates that adds the five-root contribution to the coefficient split, the sum of squares and the scaled coefficient identity |
| `build_full_seven_long_sweeps.py` | builds the 49 coefficient sweeps in bounded batches (a memory-control helper) |
| `verify_full_seven_long.py` | the verification driver: preflight, bounded sweeps, both headlines, the axiom audit, the literal-fraction witness, source-stability checks, and the `PASS` record |

## Templates

The chain's certificate-dependent proofs are written once, as templates, and
instantiated for the certificate. The 105 templates under
`templates/Examples/` were written for an earlier certificate of this project
with the same block structure (the same six-vertex representatives, flag bases
and normalizations); they contain that certificate's tables and constants.
The generator applies the structural assembly, replaces every factor table,
row count, scale, stationarity multiplier, recomputed class number and bound,
redirects the certificate-dependent imports into the `FullSevenLong`
namespace, and checks that no constant of the template certificate survives.
The templates are not Lean modules of this repository; the generated modules
name their template in a header comment, and `manifest.json` records each
template's hash and its replacement sites with occurrence counts.

The thirteen five-root semantic modules (`FiveRootBits`, `FiveRootFlags`,
`FiveRootTableFacts`, `FiveRootColumn`, `FiveRootPullback`, `FiveRootSamples`,
`FiveRootOrderedColumn`, `FiveRootColumnSum`, `FiveRootGramSem`,
`FiveRootOrderedSem`, `FiveRootSem`, `FiveRootSOS`, `FiveRootExpand`) are
handwritten sources of the chain; the generator records their hashes without
touching them.

## Hash convention

The certificate is hashed as raw bytes (`certificate/.gitattributes` keeps them
with `-text`). Lean, Python and JSON sources are hashed as UTF-8 text with CRLF
normalized to LF, so that the manifests agree on every checkout regardless of
`core.autocrlf`; the generators write LF, and the chain and template
directories force LF on checkout.

## Commands

From the repository root, with the pinned `lean-toolchain` and, for the
generators, Python 3.12 with `requirements.txt`:

```sh
python scripts/exact_certificate/derive_full_seven_long_five_root.py
python scripts/exact_certificate/derive_full_seven_long_chain.py
lake exe cache get
python scripts/exact_certificate/verify_full_seven_long.py \
  --threads 4 --sweep-batch-size 2 --output-dir .research-repro/lean-verification
```

Both generators refuse any certificate other than the pinned one and leave
identical files untouched. Do not regenerate while a build is running. The
driver refuses Python's optimized mode, which would disable its assertions;
use `--lake /path/to/lake` if `lake` is not on the path, and `--check-only` to
run the preflight without building. Reduce both `--threads` and
`--sweep-batch-size` to one when memory is constrained; a plain `lake build`
or an unbounded headline build can start many large sweep workers at once.
Lake reuses completed modules after an interruption, so keep `.lake/` when
resuming.

Generation alone establishes nothing: the Lean build and the axiom audit do.
The tracked record of a complete run is described in
[`certificate/verification/README.md`](../../certificate/verification/README.md).
