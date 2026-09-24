# tetrahedron-turan

A machine-checked upper bound for the Turán density of the tetrahedron
`K₄⁽³⁾`, the complete 3-uniform hypergraph on four vertices, in Lean 4:

```lean
theorem FlagAlgebras.Core.Tetrahedron.FullSevenLong.tetraTuranDensity_le_certValue :
    tetraTuranDensity ≤ 312372062889819 / 560000000000000
```

The constant is `0.5578072551603910714…`, below the previously published bound
`0.5615` and above the conjectured value `5/9 = 0.5555…`. The proof uses an
exact seven-vertex flag-algebra certificate, 794 integer factor vectors in 23
blocks, together with the degree-stationarity identity of Razborov's
differential method. An independent finite-cloning route
(`tetraTuranDensity_le_certValue_finite`) proves the same bound from the same
certificate.

This repository accompanies the paper

> Gyeongwon Jeong, Seonghun Park, Seonghyuk Im, Joonkyung Lee and Hongseok Yang,
> *A New Upper Bound for the Turán Density of the Tetrahedron*,
> [arXiv:2609.27495](https://arxiv.org/abs/2609.27495), 2026.

It contains the Lean formalization, the exact certificate and its verification
record, the independent integer verifiers, the search code, and the records of
the paper's computational experiments.

## Verify the bound in Lean

Requirements: [elan](https://github.com/leanprover/elan) (the toolchain is pinned
to Lean 4.27.0 by `lean-toolchain`), Git, and Python 3.9 or later without any
extra package.

```sh
lake exe cache get
python scripts/exact_certificate/verify_full_seven_long.py \
  --threads 4 --sweep-batch-size 2 --output-dir .research-repro/lean-verification
```

The driver checks the certificate hash and the generation manifests, builds the
49 seven-vertex coefficient sweeps in bounded batches, builds both headline
modules, runs the axiom audit `AxiomCheckFullSevenLong.lean`, type-checks the
literal fraction against both theorems, and writes `formalization.json` with
status `PASS` only when every step succeeds. A plain `lake build` builds the
entire project library without writing a verification record. The
[fresh release build](certificate/verification/release-20260921/README.md)
of commit `8bf9d8d` passed all 246 project modules and the complete verifier
on September 21–22, 2026. It took 10 hours 37 minutes, including recovery
from a memory failure by building project modules in dependency order with
at most two targets per invocation. Older supporting sweeps require more
memory than the roughly 2 GB used by each new coefficient sweep;
`--sweep-batch-size` limits only the latter. See
[docs/lean-proof.md](docs/lean-proof.md) for the statement, proof architecture,
trust boundary and measured build costs, and
[certificate/verification/](certificate/verification/README.md) for both
the historical and release verification records.

The [experiment evidence bundle](experiments/evidence/README.md) includes
certificates and execution records for all 43 reported trials. A fresh
experiment plan is available with `python experiments/reproduce.py`.

## Verify the certificate without Lean

The certificate [`certificate/K4_turan_order7_certificate.json`](certificate/K4_turan_order7_certificate.json)
can be checked in exact integer arithmetic, independently of Lean and of the
optimization that produced it. With Python 3.12, the pinned packages of
`requirements.txt` and a C++17 compiler available as `c++`:

```sh
python -m pip install -r requirements.txt
python -X utf8 experiments/runtime.py search/exactify_five_root.py \
  --certificate certificate/K4_turan_order7_certificate.json \
  --cross-check-pricing --threads 2 \
  --cache .research-repro/integer-check --output .research-repro/integer-check.json
```

This rebuilds every Gram matrix from the integer factor vectors, evaluates the
coefficient of all 13,051,375 tetrahedron-free one-vertex extensions of the 964
six-vertex representatives with two independent implementations, and checks
the recorded maximum `11245394264033484 / 20160000000000000`, which reduces to
the bound. See [certificate/README.md](certificate/README.md).

## What is proved

The statement mentions only finite sets, binomial coefficients and a limit.
The definitions are in
[`LeanFlagAlgebras/Core/Examples/FullSevenLong/TetrahedronExtremal.lean`](LeanFlagAlgebras/Core/Examples/FullSevenLong/TetrahedronExtremal.lean):

- `Sym3Graph n`: a set of three-element subsets of `Fin n`;
- `HasTetraSet G`: some four vertices span all four triples;
- `exTetra n`: the maximum number of edges of an `n`-vertex 3-graph without a
  tetrahedron;
- `tetraTuranDensity`: the limit of `exTetra n / C(n,3)`, whose existence is
  the theorem `tendsto_tetraTuranDensity`.

The certificate enters through the coefficient bound
`columnValue_le_columnBound`, checked for every tetrahedron-free seven-vertex
3-graph by 49 compiled sweeps, and through the identification of the compiled
integer evaluator with the downward sums of squares of the flag algebra
(`s5ColumnNum_eq_ordered`, `s5ColumnNum_eq_ordered_sum`, `fiveRootElt_eq_scaled`).
Razborov's differential method (`LeanFlagAlgebras/Core/Differential/`) proves
that an edge-density maximizer is degree-stationary, so the final theorem has
no stationarity hypothesis.

## Axioms

`lake env lean AxiomCheckFullSevenLong.lean` prints the footprint of every
theorem below.

| Theorems | Axioms |
| --- | --- |
| `maxDens_eq_exTetra`, `tendsto_tetraTuranDensity`, `isDegreeStationary_of_maximizer`, `turanDensity_le_of_stationary_bound`, `maximizerIsStationary` | `propext`, `Classical.choice`, `Quot.sound` |
| `tetraTuranDensity_le_certValue`, `tetraTuranDensity_le_certValue_finite`, `columnValue_le_columnBound`, `edge_le_certBound_of_stationary`, `finiteBoost` | the three above plus `Lean.ofReduceBool`, `Lean.trustCompiler` |

The two additional axioms disclose the trust in Lean's compiler required by
`native_decide`, which is used for the finite catalogue facts, the
permutation and lookup tables, and the exhaustive coefficient checks. The
six-vertex completeness sweep uses kernel reduction. There are no `sorry`s and
no user-declared axioms.

## Repository layout

| Path | Contents |
| --- | --- |
| `LeanFlagAlgebras/Core/` | Flag algebras over finite relational signatures: densities, the flag algebra, positive homomorphisms, the downward operator, limits and sampling |
| `LeanFlagAlgebras/Core/Differential/` | Razborov's vertex differential and the stationarity of maximizers, theory-generically ([README](LeanFlagAlgebras/Core/Differential/README.md)) |
| `LeanFlagAlgebras/Core/Compute/` | Computable 3-graphs on bitmasks, enumeration, deletion, cloning and counting |
| `LeanFlagAlgebras/Core/Examples/` | The tetrahedron-free theory, the kernel-checked catalogue of the 964 six-vertex classes, and the certificate chain `FullSevenLong/` |
| `AxiomCheckFullSevenLong.lean` | The axiom audit of the headline theorems |
| `certificate/` | The exact certificate, its Lean verification record, and the integer verifiers ([README](certificate/README.md)) |
| `scripts/exact_certificate/` | Generation of the certificate-dependent Lean modules from the certificate, and the verification driver ([README](scripts/exact_certificate/README.md)) |
| `search/` | The cutting-plane and column-generation search and the exact conversion of its output (paper, Section 4 and Appendix B) |
| `experiments/` | The runners and records of the computational experiments (paper, Section 5 and Appendix C) ([README](experiments/README.md)) |
| `figures/` | The experimental figures of the paper and the data they are drawn from |
| `docs/` | [The Lean proof](docs/lean-proof.md) and [reproduction of the search and experiments](docs/reproduction.md) |

The namespace and directory name `FullSevenLong` records the search that
produced the certificate: the full seven-vertex model, with all 23 five-root
types, run with the longer six-hour budget.

## Citation

```bibtex
@misc{JeongParkImLeeYang2026,
  author = {Jeong, Gyeongwon and Park, Seonghun and Im, Seonghyuk and Lee, Joonkyung and Yang, Hongseok},
  title = {A New Upper Bound for the {Tur{\'a}n} Density of the Tetrahedron},
  year = {2026},
  eprint = {2609.27495},
  archivePrefix = {arXiv},
  primaryClass = {math.CO},
  url = {https://arxiv.org/abs/2609.27495}
}
```

`CITATION.cff` carries the same reference for GitHub's "Cite this repository" button.

## License

Apache License 2.0; see [LICENSE](LICENSE).
