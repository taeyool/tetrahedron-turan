# The Lean proof

The development `FlagAlgebras.Core.Tetrahedron.FullSevenConverged` proves

\[
\pi(K_4^{(3)})\leq \frac{14993367693127837}{26880000000000000}
= 0.5577889766788629836\ldots
\]

for the Turán density of the tetrahedron defined in the repository, from the
780-factor integer certificate
[`certificate/K4_turan_order7_certificate.json`](../certificate/K4_turan_order7_certificate.json).
This is the certificate of the paper's main theorem.

## Statement

```lean
namespace FlagAlgebras.Core.Tetrahedron.FullSevenConverged
def exTetra (n : Nat) : Nat :=
  ((Finset.univ : Finset (Sym3Graph n)).filter
    fun G => not G.HasTetraSet).sup fun G => G.edges.card
noncomputable def tetraTuranDensity : Real :=
  limUnder atTop fun n : Nat => (exTetra n : Real) / (n.choose 3 : Real)

theorem tetraTuranDensity_le_certValue :
    tetraTuranDensity <= 14993367693127837 / 26880000000000000
theorem tetraTuranDensity_le_certValue_finite :
    tetraTuranDensity <= 14993367693127837 / 26880000000000000
end FlagAlgebras.Core.Tetrahedron.FullSevenConverged
```

The first theorem, in
[`TetrahedronDifferential.lean`](../LeanFlagAlgebras/Core/Examples/FullSevenConverged/TetrahedronDifferential.lean),
uses Razborov's differential method: a maximizer of the edge density is
degree-stationary (`isDegreeStationary_of_maximizer`), so the stationarity
multiplier of the certificate contributes nothing at the maximizer. The
second, in
[`TetrahedronBoost.lean`](../LeanFlagAlgebras/Core/Examples/FullSevenConverged/TetrahedronBoost.lean),
uses a finite cloning argument instead. Both consume the same certificate
through `edge_le_certBound_of_stationary`. The convergence of the sequence
`exTetra n / C(n,3)` is the theorem `tendsto_tetraTuranDensity`, and
`maxDens_eq_exTetra` identifies the maximal flag density at every size with
the extremal number.

## Pinned integer input

| Field | Value |
|---|---|
| Certificate | `certificate/K4_turan_order7_certificate.json` |
| SHA-256 of the raw bytes | pinned in `scripts/exact_certificate/full_seven_converged_common.py` and checked by every script |
| Bound | `14993367693127837/26880000000000000` |
| Scale `M` | `8000000` |
| Common denominator `5040 M²` | `322560000000000000` |
| Maximum column numerator | `179920412317534044` |
| Stationarity numerator `τ` (over `M²`) | `710104654129914` |
| Factor rows | 780 (`1 + 2` four-root, `7` one-root, `236 + 185` three-root, `349` five-root) |
| Integer entries | 326557 (235321 in the five-root rows) |
| Active five-root types | 18 of the 23 tetrahedron-free five-vertex types |
| Recorded maximizing raw mask | `1629596093` |

The type identifiers of the active five-root blocks are
`0, 1, 3, 7, 11, 15, 30, 31, 63, 77, 87, 94, 116, 117, 119, 222, 237, 254`,
each the smallest edge-set encoding over all labelings of the type, as in
Appendix A.1 of the paper. The seven four-root and smaller blocks that the
certificate leaves empty are not materialized.

The certificate was rounded from the final floating-point dual of the search
described in Appendix C.3 of the paper (see
[reproduction.md](reproduction.md#continuation-to-convergence)). Neither that
search nor its numerical convergence is a premise of the proof: Lean checks
the fixed integer certificate.

## Proof architecture

```text
JSON integer rows -> Lean factor tables -> Gram/exact coefficient calculations
  -> agreement with ordered-root evaluation (s5ColumnNum_eq_ordered)
  -> agreement with the actual downward sums of squares (s5ColumnNum_eq_ordered_sum,
     fiveRootElt_eq_scaled)
  -> coefficient bound for every tetrahedron-free 7-vertex graph
     (49 native sweeps, columnValue_le_columnBound)
  -> bound for stationary edge-density maximizers (edge_le_certBound_of_stationary)
  -> bound for the Turán density (both routes)
```

The chain directory `LeanFlagAlgebras/Core/Examples/FullSevenConverged/` has
142 modules of three kinds:

| Kind | Modules | Origin |
| --- | --- | --- |
| Five-root data | 21 (`FiveRootFactors00`–`17`, `FiveRootData`, `FiveRootTables`, `FiveRootOrderedData`) | generated from the certificate by `derive_full_seven_converged_five_root.py` |
| Five-root semantics | 13 (`FiveRootBits`, `FiveRootFlags`, `FiveRootTableFacts`, `FiveRootColumn`, `FiveRootPullback`, `FiveRootSamples`, `FiveRootOrderedColumn`, `FiveRootColumnSum`, `FiveRootGramSem`, `FiveRootOrderedSem`, `FiveRootSem`, `FiveRootSOS`, `FiveRootExpand`) | handwritten |
| Certificate-dependent proofs | 108 (the 49 sweeps, the one-, three- and four-root tables `FactorsS1`, `FactorsS30`, `FactorsS31`, `Blocks`, `Column`, `Check`, the block and degree checks, the stationarity and limit modules, both headlines) | instantiated from proof templates by `derive_full_seven_converged_chain.py` |

The semantic modules are generic over the data modules: their proofs mention
only `s5Rows b`, `s5Dim b`, `Fin 18`, the 120 root permutations and the 21
root sets. Only `FiveRootSOS` and `FiveRootExpand` state the scale, as the
literals `M² = 64000000000000` and `5040 M² = 322560000000000000`. The fast
evaluator sums the full type-automorphism action on each Gram matrix, retains
both orders of the two outside vertices, and divides by
`7.descFactorial 5 * 2 = 5040` and by `M²` exactly once each. This is the
grouped sum of Proposition 4.1 of the paper; `s5ColumnNum_eq_ordered` proves it
equal to the sum over all ordered root labelings.

The chain imports three certificate-independent parts of the repository:

- the generic flag-algebra library and Razborov's differential method
  (`LeanFlagAlgebras/Core/`, 42 modules);
- the kernel-checked catalogue of the 964 tetrahedron-free six-vertex
  3-graphs (`LeanFlagAlgebras/Core/Examples/`, 57 modules): the representative
  masks, the completeness sweep over all `2^20` edge sets in 32 pieces, the
  pairwise non-isomorphism orbit checks, and the generic counting identities
  for one-, three- and five-vertex rootings of a seven-vertex host;
- Mathlib at the revision pinned in `lake-manifest.json`.

The released import closure of the headline theorems has 241 modules.
The retained original verification record also hashed auxiliary targets and
therefore lists 344 modules. Their archived sources and the mapping of the
241 released modules are checked by `python scripts/check_release_evidence.py`;
the code tokens agree after removing comments and whitespace. This packaging
check is separate from rerunning Lean.

## Generation and hashing

The certificate-dependent modules are produced from templates by the scripts
in [`scripts/exact_certificate/`](../scripts/exact_certificate/README.md); the
two manifests in the chain directory record the certificate hash, every
template hash, every replacement site and every generated file hash. The
certificate is hashed as raw bytes. Lean, Python and JSON sources are hashed as
UTF-8 text with CRLF normalized to LF, and the generators write LF
(`FullSevenConverged/.gitattributes` forces LF on checkout). Generation is not
verification: only the Lean build and the axiom audit establish the theorem.

## Reproduction

From the repository root, with the pinned `lean-toolchain` (Lean 4.27.0):

```sh
lake exe cache get
python scripts/exact_certificate/verify_full_seven_converged.py \
  --threads 4 --sweep-batch-size 2 --output-dir .research-repro/lean-verification
```

`verify_full_seven_converged.py --check-only` runs the input, manifest and
source preflight without building. To regenerate the generated modules first,
use Python 3.12 with `requirements.txt` and run the two generators before the
verifier; they refuse any certificate other than the pinned one. Do not
regenerate while a build is running.

## Trust boundary

The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`. The
finite catalogue, permutation, lookup-table and exhaustive coefficient checks
use `native_decide`, which adds `Lean.ofReduceBool` and `Lean.trustCompiler`:
the two final theorems have exactly this five-axiom footprint. The limit,
stationarity and consumption theorems (`maxDens_eq_exTetra`,
`tendsto_tetraTuranDensity`, `turanDensity_le_of_stationary_bound`,
`isDegreeStationary_of_maximizer`, `maximizerIsStationary`) and the generic
rooting identities (`FlagAlgebras.Core.isStationary_of_maximizer`,
`FlagAlgebras.Core.Tetrahedron.gamma56_eq_rooting5040`,
`FlagAlgebras.Core.sum_injective_filter_eq_rootSubset_perm`) use only the
standard three. No `sorry`, no new axiom, and no imported external numerical
assertion is used; the C++ integer scans recorded in the JSON's
`exact_verification` field corroborate the arithmetic but are not premises of
the proof. The raw extension count `13051375` recorded there is not an
isomorphism-class count; the Lean sweeps enumerate every labeled extension of
the 964 six-vertex representatives.

## Measured build cost

The [fresh release build of commit `857fe4b`](../certificate/verification/release-20261002/README.md)
started without a project build cache and completed all 246 project modules
and the official verifier in 12 hours 35 minutes on October 2, 2026, on an
Intel Core i7-14700K (28 threads, 64 GB, Windows 11) under a 40 GiB memory
cap. This includes a memory failure during concurrent compilation of
`TetrahedronOrder5` and older supporting sweeps, and recovery in dependency
order with at most two certificate-independent targets per invocation.
`TetrahedronOrder5`, which the headline theorems import, peaked at 36.72 GiB
of job commit memory when built alone. The 49
coefficient sweeps took 4 hours 15 minutes with twelve Lake jobs, between
1079 s and 5140 s each (median 3556 s) and 12.76 GiB together; the remaining
chain and both headlines took 33 minutes and peaked at 35.34 GiB. No proof
sources changed. The final verifier reused the newly built artifacts.

The chain was first built on the same machine (Intel Core i7-14700K, 28
threads, 64 GB, Windows 11) in three bounded Lake invocations, archived with
per-module timings under
[`certificate/verification/preparation/`](../certificate/verification/preparation/README.md):

| Stage | Contents | `LEAN_NUM_THREADS` | Wall clock |
| --- | --- | ---: | --- |
| 1 | 21 five-root data modules, 3 one- and three-root factor modules | 8 | 3 min 49 s |
| 2 | five-root semantic modules, `Blocks`, `Column`, `Check`, and, because `FiveRootExpand` imports `Reduce`, whose closure contains `Bound`, all 49 sweeps and the chain below the headlines | 8 | 7 h 33 min |
| 3 | `BlockElt`, `DegreeCheck`, the remaining chain, both headlines, and the auxiliary module `TetrahedronConvergedHeadline` of the original repository, which is not released | 12 | 30 min 38 s |

Notable single modules: `FiveRootFactors00` 134 s, `FiveRootFlags` 517 s,
`FiveRootTableFacts` 164 s, `FiveRootSOS` 11 s, `Extension` 517 s, `Column`
683 s (including the `native_decide` evaluation of the recorded maximizing
column), `RootFlags` 597 s, `GatherPull` 536 s, `BlockCheck` 180 s,
`DegreeCheck` 1585 s, `TetrahedronDifferential` 35 s, `TetrahedronBoost` 22 s.
The 49 sweep leaves took between 3119 s and 5257 s each (median 3454 s) with
eight Lake jobs running concurrently, about 1.9 GB per sweep process. This is
about 1.7 times the sweep times of the earlier 794-factor chain at
`M = 2000000`; the larger scale makes the intermediate integers of the
compiled evaluator larger. These are overlapping operational timings, not a
clean-build benchmark. The verification record of a complete run of the
driver is described in
[`certificate/verification/README.md`](../certificate/verification/README.md).
