import LeanFlagAlgebras.Core.Differential.Maximizer
import LeanFlagAlgebras.Core.Differential.Stationary

/-! # Core: the vertex differential on the flag algebra (Razborov Lemma 4.2(b), (c))

The remaining two clauses of Razborov's Lemma 4.2:

* (b) `∂₁` respects the zero spaces (`partialVertexVec_zeroSpace`), so it
  descends to a linear map `partialVertex : A⁰ → A¹`: at a host `(N, v)`
  of size `L + 1`, Lemma 4.2(a) reads `p^{(N,v)}(∂₁ k) = (L+1)(p(k, N − v)
  − p(k, N))`, and both densities vanish for `k` in the zero space once the
  hosts are large;
* (c) `⟦∂₁ f⟧₁ = 0` for every `f ∈ A⁰` (`downward_partialVertex`): the
  density of `⟦g⟧₁` at a host `H` is the average of the rooted evaluations
  of `g` over the vertices of `H` (`densityEval_downwardVector`, the
  averaging identity of `Core/Downward` at the vertex type), and the rooted
  evaluations of `∂₁ f` average to zero (`sum_hostEval_partialVertexVec`).

The averaging identity is obtained from the labeling combinatorics of
`Core/Ensemble/Empirical` (`sum_sigmaLabelings`,
`sum_labelingCount_mul_subflagDensity`); nothing measure-theoretic is
used. -/

namespace FlagAlgebras.Core

open Finset
open Classical

variable {S : Signature} [S.NullaryFree] {𝕋 : RelTheory S}
variable {σ₁ : Model S (Fin 1)} [hvu : 𝕋.VertexUniform σ₁] [𝕋.IsType σ₁]

/-! ## Lemma 4.2(b): `∂₁` respects the zero spaces -/

omit [𝕋.IsType σ₁] in
/-- **Razborov's Lemma 4.2(b).** The vertex differential maps the zero space
of the unlabeled algebra into the zero space of the vertex-typed one. -/
theorem partialVertexVec_zeroSpace {k : FlagVector 𝕋 (emptyType S)}
    (hk : k ∈ ZeroSpace 𝕋 (emptyType S)) :
    partialVertexVec σ₁ k ∈ ZeroSpace 𝕋 σ₁ := by
  obtain ⟨L₀, hL₀⟩ := zeroSpace_densityEval_eventually_zero hk
  set B := k.support.sup (fun M => M.1) with hB
  have hBsupp : ∀ M ∈ k.support, M.1 ≤ B := fun M hM => Finset.le_sup (f := fun M => M.1) hM
  set L := max B L₀ with hL
  refine mem_zeroSpace_of_densityEval_zero (L := L + 1) ?_ ?_
  · intro F hF
    have := partialVertexVec_support_le (σ₁ := σ₁) hBsupp F hF
    omega
  · intro G
    rw [densityEval_out]
    set N := (Quotient.out G).unlabel with hN
    set r := (Quotient.out G).rootEmbed.toEmbedding 0 with hr
    have hG : Quotient.out G = rootedAt σ₁ N r := (rootedAt_unlabel_root _).symm
    rw [hG]
    have hdel := vertex_deletion_hostEval (σ₁ := σ₁) N r k (L := L)
      (by rw [Fintype.card_fin]) (fun M hM => by have := hBsupp M hM; omega)
    have h1 : hostEval N k = 0 := by
      rw [hostEval_toFlag]
      exact hL₀ (L + 1) (by omega) _
    have h2 : hostEval (deleteVertex N r) k = 0 := by
      rw [hostEval_eq_densityEval_reindex]
      refine hL₀ _ ?_ _
      rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ,
        Fintype.card_fin]
      omega
    rw [h1, h2, zero_add] at hdel
    have hL1 : (1 / ((L : ℝ) + 1)) ≠ 0 := by positivity
    exact (mul_eq_zero.mp hdel.symm).resolve_left hL1

omit [𝕋.IsType σ₁] in
/-- **The vertex differential on the flag algebra**, `∂₁ : A⁰ → A¹`. -/
noncomputable def partialVertex :
    FlagAlgebra 𝕋 (emptyType S) → FlagAlgebra 𝕋 σ₁ :=
  Quotient.map (partialVertexVec σ₁) fun f g hfg => by
    show partialVertexVec σ₁ f - partialVertexVec σ₁ g ∈ ZeroSpace 𝕋 σ₁
    rw [← partialVertexVec_sub]
    exact partialVertexVec_zeroSpace hfg

omit [𝕋.IsType σ₁] in
@[simp]
theorem partialVertex_quot (f : FlagVector 𝕋 (emptyType S)) :
    partialVertex (σ₁ := σ₁) (⟦f⟧ : FlagAlgebra 𝕋 (emptyType S))
      = ⟦partialVertexVec σ₁ f⟧ :=
  rfl

omit [𝕋.IsType σ₁] in
theorem partialVertex_add (x y : FlagAlgebra 𝕋 (emptyType S)) :
    partialVertex (σ₁ := σ₁) (x + y) = partialVertex x + partialVertex y := by
  rw [← Quotient.out_eq x, ← Quotient.out_eq y, ← add_quot, partialVertex_quot,
    partialVertex_quot, partialVertex_quot, partialVertexVec_add, add_quot]

omit [𝕋.IsType σ₁] in
theorem partialVertex_smul (r : ℝ) (x : FlagAlgebra 𝕋 (emptyType S)) :
    partialVertex (σ₁ := σ₁) (r • x) = r • partialVertex x := by
  rw [← Quotient.out_eq x, ← smul_quot, partialVertex_quot, partialVertex_quot,
    partialVertexVec_smul, smul_quot]

/-! ## The averaging identity at the vertex type -/

section Averaging

/-- The rooted densities of a vertex-typed flag sum, over the vertices of a
host, to the averaging count of `Core/Downward`. -/
theorem sum_flagDensity_rootedAt {n : ℕ} (H : LabeledFlag 𝕋 (emptyType S) (Fin n))
    (F : FinFlag 𝕋 σ₁) :
    ∑ v : Fin n, ((flagDensity (Quotient.out F.2) (rootedAt σ₁ H v) : ℚ) : ℝ)
      = ((((flagCount (Quotient.out F.2).unlabel H
            * labelingCount (Quotient.out F.2).unlabel (Quotient.out F.2) : ℕ) : ℚ)
          / ((n - 1).choose (F.1 - 1) : ℚ) : ℚ) : ℝ) := by
  have h1 := sum_sigmaLabelings σ₁ H
    (fun θ => ((subflagDensity F.2
      (rootAt σ₁ H θ (isSigmaLabeling_vertexUniform H θ)).toFlag : ℚ) : ℝ))
    (fun F' => ((subflagDensity F.2 F' : ℚ) : ℝ)) (fun _ _ => rfl)
  rw [sum_sigmaLabelings_vertex] at h1
  have h2 : ∀ v : Fin n,
      ((subflagDensity F.2 (rootAt σ₁ H (constEmb v)
        (isSigmaLabeling_vertexUniform H _)).toFlag : ℚ) : ℝ)
        = ((flagDensity (Quotient.out F.2) (rootedAt σ₁ H v) : ℚ) : ℝ) := fun v => by
    rw [subflagDensity_toFlag_right]
    rfl
  simp only [h2] at h1
  rw [h1]
  have h3 := sum_labelingCount_mul_subflagDensity σ₁ H F
  rw [Fintype.card_fin] at h3
  have hsumR : (∑ F' : Flag 𝕋 σ₁ (Fin n),
      (labelingCount H (Quotient.out F') : ℝ) * ((subflagDensity F.2 F' : ℚ) : ℝ))
      = ((∑ F' : Flag 𝕋 σ₁ (Fin n),
          (labelingCount H (Quotient.out F') : ℚ) * subflagDensity F.2 F' : ℚ) : ℝ) := by
    push_cast
    rfl
  rw [hsumR, h3]

/-- The density of the downward image of a single vertex-typed flag at a
host is the vertex average of its rooted densities. -/
theorem densityEval_downwardFinFlag {n : ℕ} (H : LabeledFlag 𝕋 (emptyType S) (Fin n))
    (F : FinFlag 𝕋 σ₁) (hF : F.1 ≤ n) :
    densityEval (downwardFinFlag F) ⟨n, H.toFlag⟩
      = (n : ℝ)⁻¹ * ∑ v : Fin n, ((flagDensity (Quotient.out F.2) (rootedAt σ₁ H v) : ℚ) : ℝ) := by
  rw [sum_flagDensity_rootedAt H F]
  unfold downwardFinFlag
  rw [densityEval_smul, densityEval_basisVector]
  rw [show subflagDensity (Quotient.out F.2).unlabel.toFlag H.toFlag
    = flagDensity (Quotient.out F.2).unlabel H from rfl]
  have hF1 : 1 ≤ F.1 := by
    have := finFlag_size_ge F
    simpa using this
  have hn : 1 ≤ n := hF1.trans hF
  rw [show ((n : ℕ) : ℝ)⁻¹ = (((n : ℕ) : ℚ)⁻¹ : ℚ) by push_cast; rfl, ← Rat.cast_mul,
    ← Rat.cast_mul]
  congr 1
  unfold labelingFactor flagDensity
  rw [Fintype.card_embedding_eq]
  simp only [Fintype.card_fin, Nat.descFactorial_one, Nat.sub_zero]
  have hbin : (n : ℚ) * ((n - 1).choose (F.1 - 1) : ℚ) = (F.1 : ℚ) * (n.choose F.1 : ℚ) := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (F.1 - 1)
    rw [Nat.sub_add_cancel hn, Nat.sub_add_cancel hF1] at h
    rw [mul_comm (F.1 : ℚ)]
    exact_mod_cast h
  have hc1 : (0 : ℚ) < n.choose F.1 := by exact_mod_cast Nat.choose_pos hF
  have hc2 : (0 : ℚ) < (n - 1).choose (F.1 - 1) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hF1' : (0 : ℚ) < F.1 := by exact_mod_cast hF1
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  rw [div_mul_div_comm, inv_mul_eq_div, div_div,
    div_eq_div_iff (mul_ne_zero hF1'.ne' hc1.ne') (mul_ne_zero hc2.ne' hn'.ne')]
  push_cast
  linear_combination ((labelingCount (Quotient.out F.2).unlabel (Quotient.out F.2) : ℚ)
    * (flagCount (Quotient.out F.2).unlabel H : ℚ)) * hbin

/-- **The averaging identity at the vertex type**: the density of the
downward image of a vertex-typed vector at a host is the average over the
vertices of the rooted evaluations. -/
theorem densityEval_downwardVector {n : ℕ} (H : LabeledFlag 𝕋 (emptyType S) (Fin n))
    (g : FlagVector 𝕋 σ₁) (hg : ∀ F ∈ g.support, F.1 ≤ n) :
    densityEval (downwardVector g) ⟨n, H.toFlag⟩
      = (n : ℝ)⁻¹ * ∑ v : Fin n, hostEval (rootedAt σ₁ H v) g := by
  unfold downwardVector linearExtension
  rw [densityEval_sum]
  simp_rw [densityEval_smul]
  rw [Finset.sum_congr rfl fun F hF => by rw [densityEval_downwardFinFlag H F (hg F hF)]]
  simp_rw [hostEval_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [← Finset.mul_sum]
  ring

end Averaging

/-! ## Lemma 4.2(c): `⟦∂₁ f⟧₁ = 0` -/

/-- The downward image of the vertex differential lies in the zero space. -/
theorem downwardVector_partialVertexVec_zeroSpace (f : FlagVector 𝕋 (emptyType S)) :
    downwardVector (partialVertexVec σ₁ f) ∈ ZeroSpace 𝕋 (emptyType S) := by
  set B := f.support.sup (fun M => M.1) with hB
  have hBsupp : ∀ M ∈ f.support, M.1 ≤ B := fun M hM => Finset.le_sup (f := fun M => M.1) hM
  have hsupp := partialVertexVec_support_le (σ₁ := σ₁) hBsupp
  refine mem_zeroSpace_of_densityEval_zero (L := B + 1) ?_ ?_
  · intro F hF
    unfold downwardVector linearExtension at hF
    obtain ⟨F', hF', hFF'⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum hF)
    have h1 := Finsupp.support_smul hFF'
    unfold downwardFinFlag at h1
    have h2 := Finsupp.support_smul h1
    rw [basisVector_support, Finset.mem_singleton] at h2
    subst h2
    exact hsupp F' hF'
  · intro G
    have h := densityEval_downwardVector (Quotient.out G) (partialVertexVec σ₁ f) hsupp
    rw [show (Quotient.out G).toFlag = G from Quotient.out_eq G] at h
    rw [h, sum_hostEval_partialVertexVec (σ₁ := σ₁) (Quotient.out G) f (L := B)
      (by rw [Fintype.card_fin]) hBsupp, mul_zero]

/-- **Razborov's Lemma 4.2(c).** `⟦∂₁ f⟧₁ = 0` for every `f ∈ A⁰`: on
average over the deleted vertex, nothing changes. -/
theorem downward_partialVertex (x : FlagAlgebra 𝕋 (emptyType S)) :
    downward (partialVertex (σ₁ := σ₁) x) = 0 := by
  obtain ⟨f, rfl⟩ := Quotient.exists_rep x
  rw [partialVertex_quot, downward_quot]
  show (⟦downwardVector (partialVertexVec σ₁ f)⟧ : FlagAlgebra 𝕋 (emptyType S))
    = ⟦(0 : FlagVector 𝕋 (emptyType S))⟧
  refine Quotient.sound ?_
  show downwardVector (partialVertexVec σ₁ f) - 0 ∈ ZeroSpace 𝕋 (emptyType S)
  rw [sub_zero]
  exact downwardVector_partialVertexVec_zeroSpace f

end FlagAlgebras.Core
