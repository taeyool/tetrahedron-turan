# `Core/Differential`: Razborov's differential method, theory-generically

The vertex differential `∂₁` of Razborov's §4.3 and Theorem 4.3 (the
differential method), for an arbitrary vertex uniform relational theory,
ending in the consequence that flag-algebra certificates consume: a
realized maximizer of a model density is stationary for the model's
rooting (Corollary 4.6(a) in the shape of the paper's "maximizers are
degree-stationary").

Everything is sorry-free and uses only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`); the tetrahedron bounds proved through
it add only the certificate's `native_decide` axioms (see
`AxiomCheckFullSevenLong.lean` at the repository root).

## Files, in dependency order

| file | content | Razborov |
|---|---|---|
| `Eval.lean` | `densityEval`/`hostEval` (evaluation of flag vectors at hosts), size-`L` expansion, zero-space criterion `mem_zeroSpace_of_densityEval_zero`, `zeroSpace_densityEval_eventually_zero` | §4.3 tool |
| `Vertex.lean` | `RelTheory.VertexUniform`, `rootedAt`, `deleteVertex`, `unroot`, `rootExtensions`, `labelPlacements`, `piVec` (π¹), `muVec` (π̃¹), `partialVertexVec` (∂₁), support and uniform bounds | Def. of ∂₁ |
| `Deletion.lean` | `sum_rootExtensions_flagDensity` (`p^{(N,v)}(π¹M) = p(M, N−v)`), `flagDensity_total_probability`, **Lemma 4.2(a)** `vertex_deletion_density` / `vertex_deletion_hostEval`, mean-zero `sum_hostEval_partialVertexVec` | Lemma 4.2(a) |
| `Stability.lean` | single-vertex and restriction stability of host evaluations, `abs_hostEval_restrict_sub_le` | proof of 4.3 |
| `Telescope.lean` | Lemma 4.2(a) in set form, the telescoping deletion of good vertices `hostEval_restrict_sdiff_ge`, the maximality bound on large hosts `eventually_densityEval_le` | proof of 4.3 |
| `Maximizer.lean` | `profileEval`, vertex form of the empirical rooting measure, extension clause `ae_profileEval_piVec` (`φ¹(π¹M) = φ₀(M)` a.s.), the deletion core `exists_deletion_of_pos_measure`, **Theorem 4.3** (linear objective, realized weak-limit form) `ae_profileEval_partialVertexVec_nonpos` and `_eq_zero` | Thm 3.5, Thm 4.3 |
| `Stationary.lean` | vertex type is `1` in `A⁰`, `q(1_{σ₁}) = 1`, Theorem 3.5 for vectors, **`isStationary_of_maximizer`** | Cor 4.6(a) |
| `Descent.lean` | **Lemma 4.2(b)** `partialVertexVec_zeroSpace`, `partialVertex : A⁰ → A¹`, averaging identity `densityEval_downwardVector`, **Lemma 4.2(c)** `downward_partialVertex` | Lemma 4.2(b,c) |
| `Upward.lean` | the upward operator `upward : A⁰ → A¹` (well defined by `p^{(N,v)}(π¹f) = p(f, N−v)`), `partialVertex_basis` (`∂₁M = ℓ(π¹M − π̃¹M)` on the algebra), the double counts `sum_pairCount_rootExtensions` and `sum_sum_pairCount_rootExtensions`, **Theorem 2.8(a)** `downward_upward_mul` (`⟦π¹(x)·y⟧₁ = x·⟦y⟧₁`), and **Theorem 2.8, the homomorphism clause**: `upward_mul` (`π¹(x·y) = π¹(x)·π¹(y)`), `upward_one`, packaged as `upwardAlgHom : A⁰ →ₐ[ℝ] A¹` | Thm 2.8 |
| `Smooth.lean` | **Theorem 4.3 for a `C¹` objective** `φ ↦ F(φ(f₁), …, φ(f_k))`: the linearization `linearize` (`∑ᵢ ∂ᵢF(x₀) • fᵢ`), the first-order condition at a maximizer `exists_radius_fderiv_le` and at large finite hosts `exists_size_fderiv_le`, `ae_fderiv_partialVertexVec_eq_zero` (`∑ᵢ ∂ᵢF(x₀) φ¹(∂₁fᵢ) = 0` a.s.; differentiability of `F` at `x₀` suffices), its `C¹` form `ae_fderiv_partialVertexVec_eq_zero_of_contDiff`, and the realization-free `exists_weakLimit_ae_fderiv_eq_zero` | Thm 4.3 |

Instantiation at the tetrahedron-free theory:
`Core/Examples/FullSevenLong/TetrahedronDifferential.lean` (vertex uniformity, the
hyperedge's single rooting, every homomorphism below the finite Turán
density, `isDegreeStationary_of_maximizer`, `turanDensity_le_of_stationary_bound`,
the headline `tetraTuranDensity_le_certValue`, the paper's (Dgrad) identity
`downward_degreeFlag_mul_partialVertex_edgeElt` : `⟦d·∂₁ρ⟧₁ = 3D`, and the
chain's named statements D2 and M2d as theorems).

## Hypotheses and scope

* The theory must be *vertex uniform* (`RelTheory.VertexUniform 𝕋 σ₁`): the
  one-vertex model `σ₁` is the induced substructure at every vertex of every
  member. Holds for uniform hypergraph theories and their
  forbidden-substructure subtheories.
* Theorem 4.3 is proved in the *realized* form: the maximizer `φ₀` comes
  with a sequence of hosts realizing it, and the almost-sure statements are
  about a weak limit of the empirical rooting measures along that sequence
  (whose restriction to the homomorphism space is the random extension
  `ℙ[φ₀]` of `Core/Ensemble`). It is proved for a *linear* objective
  `φ ↦ φ(f)` (`Maximizer.lean`) and for a *`C¹` objective*
  `φ ↦ F(φ(f₁), …, φ(f_k))` (`Smooth.lean`: differentiability of `F` at
  the maximizer's value vector suffices, and the conclusion is
  `∑ᵢ ∂ᵢF(x₀) φ¹(∂₁ fᵢ) = 0` almost surely).
  Since every homomorphism is realized (`Core/Limit/Sampling.lean`,
  `exists_realizedBy`, the sampling direction of Theorem 3.3), the
  realization hypothesis can be dropped: `isStationary_of_maximizer'`,
  `exists_weakLimit_ae_fderiv_eq_zero`, and at the tetrahedron the chain's
  named statements D2 (`everyHomRealized`) and M2d
  (`maximizerIsStationary`) are theorems.
* The route to the tetrahedron bound does not go through Theorem 2.8(a):
  almost surely `φ¹(d) = φ¹(π̃¹ρ) = φ¹(π¹ρ) = φ₀(ρ)`, and the moments of `d`
  and `d·d` under `ℙ[φ₀]` then give `φ₀(D) = 0`. Theorem 2.8 is formalized
  separately (`Upward.lean`): `π¹` is an `ℝ`-algebra homomorphism
  (`upwardAlgHom`), and the identity (a) `downward_upward_mul` yields the
  paper's identity `⟦d·∂₁ρ⟧₁ = 3D`.
