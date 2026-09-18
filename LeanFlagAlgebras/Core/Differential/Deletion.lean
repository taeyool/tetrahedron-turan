import LeanFlagAlgebras.Core.Differential.Vertex
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-! # Core: vertex deletion and the vertex differential (Razborov Lemma 4.2(a))

The two counting identities behind Razborov's Lemma 4.2(a), for a model `M`
on `ℓ` vertices, a host `N` on `L + 1 ≥ ℓ + 1` vertices and a vertex `v`:

* `sum_rootExtensions_flagDensity` : `p^{(N,v)}(π¹ M) = p(M, N − v)` — the
  root-containing `(ℓ+1)`-subsets inducing a root extension of `M`
  correspond, by removing `v`, to the `ℓ`-subsets of `N − v` inducing `M`;
* `flagDensity_total_probability` : conditioning the uniformly random
  `ℓ`-subset defining `p(M, N)` on whether it contains `v`,
  `p(M, N) = (ℓ/(L+1)) p^{(N,v)}(π̃¹ M) + ((L+1−ℓ)/(L+1)) p(M, N − v)`.

Together: **Lemma 4.2(a)**, `p(M, N − v) = p(M, N) + (1/(L+1)) p^{(N,v)}(∂₁ M)`
(`vertex_deletion_density`), and its linear extension to flag vectors
(`vertex_deletion_hostEval`). A third identity, `sum_flagCount_deleteVertex`,
averages the deletion over the vertex: `∑_v p(M, N − v) = (L+1) p(M, N)`,
so that the differential has mean zero over the root
(`sum_hostEval_partialVertexVec`). -/

namespace FlagAlgebras.Core

open Finset
open Classical

variable {S : Signature} [S.NullaryFree] {𝕋 : RelTheory S}

/-! ## Witness sets of distinct classes are disjoint -/

section Generic

variable {T : Type} [Fintype T] {σ : Model S T} {V W' : Type} [Fintype V] [Fintype W']
  [DecidableEq V]

omit [S.NullaryFree] [DecidableEq V] in
theorem flagWitnesses_out_disjoint (G : LabeledFlag 𝕋 σ V) {F₁ F₂ : Flag 𝕋 σ W'}
    (hne : F₁ ≠ F₂) :
    Disjoint (flagWitnesses (Quotient.out F₁) G) (flagWitnesses (Quotient.out F₂) G) := by
  refine Finset.disjoint_left.mpr fun A hA₁ hA₂ => hne ?_
  obtain ⟨hr₁, -, ⟨i₁⟩⟩ := mem_flagWitnesses.mp hA₁
  obtain ⟨hr₂, -, ⟨i₂⟩⟩ := mem_flagWitnesses.mp hA₂
  calc F₁ = Quotient.mk _ (Quotient.out F₁) := (Quotient.out_eq F₁).symm
    _ = Quotient.mk _ (Quotient.out F₂) := Quotient.sound ⟨i₁.symm.trans i₂⟩
    _ = F₂ := Quotient.out_eq F₂

omit [S.NullaryFree] in
/-- Summing witness counts over a set of classes counts the union of their
witness sets. -/
theorem sum_flagCount_out (G : LabeledFlag 𝕋 σ V) (s : Finset (Flag 𝕋 σ W')) :
    ∑ F ∈ s, flagCount (Quotient.out F) G
      = (s.biUnion fun F => flagWitnesses (Quotient.out F) G).card := by
  rw [Finset.card_biUnion fun F₁ _ F₂ _ hne => flagWitnesses_out_disjoint G hne]
  rfl

end Generic

variable {σ₁ : Model S (Fin 1)} [𝕋.VertexUniform σ₁]
variable {V : Type} [Fintype V] [DecidableEq V] (N : LabeledFlag 𝕋 (emptyType S) V) (v : V)

/-! ## The root extensions: `p^{(N,v)}(π¹ M) = p(M, N − v)` -/

/-- The root-containing witnesses of the root extensions of `M` in `(N, v)`
correspond to the witnesses of `M` in `N − v`, by removing the root. -/
theorem sum_rootExtensions_flagCount {ℓ : ℕ} (M : FlagWithSize 𝕋 (emptyType S) ℓ) :
    ∑ F ∈ rootExtensions σ₁ M, flagCount (Quotient.out F) (rootedAt σ₁ N v)
      = flagCount (Quotient.out M) (deleteVertex N v) := by
  rw [sum_flagCount_out, deleteVertex, flagCount_restrict, Finset.filter_congr_decidable]
  refine Finset.card_bij' (fun W _ => W.erase v) (fun W _ => insert v W) ?_ ?_ ?_ ?_
  · intro W hW
    obtain ⟨F, hF, hWF⟩ := Finset.mem_biUnion.mp hW
    obtain ⟨e'⟩ := mem_rootExtensions.mp hF
    obtain ⟨hroot, hcard, ⟨e⟩⟩ := mem_flagWitnesses.mp hWF
    have hv : v ∈ W := hroot 0
    refine Finset.mem_filter.mpr ⟨mem_flagWitnesses.mpr ⟨emptyType_root_mem _ _, ?_, ?_⟩, ?_⟩
    · rw [Finset.card_erase_of_mem hv, hcard, Fintype.card_fin, Fintype.card_fin,
        Nat.add_sub_cancel]
    · exact ⟨((unroot_restrict_iso N v hroot).symm.trans (unrootIso e)).trans e'⟩
    · exact Finset.erase_subset_erase v (Finset.subset_univ W)
  · intro W' hW'
    obtain ⟨hwit, hsub⟩ := Finset.mem_filter.mp hW'
    obtain ⟨hr', hcard', ⟨e'⟩⟩ := mem_flagWitnesses.mp hwit
    have hv' : v ∉ W' := (Finset.subset_erase.mp hsub).2
    have hroot : ∀ t, (rootedAt σ₁ N v).rootEmbed.toEmbedding t ∈ insert v W' :=
      fun _ => Finset.mem_insert_self v W'
    have hcoe : Fintype.card {x // x ∈ insert v W'} = Fintype.card (Fin (ℓ + 1)) := by
      rw [Fintype.card_coe, Finset.card_insert_of_notMem hv', hcard', Fintype.card_fin,
        Fintype.card_fin]
    set X : LabeledFlag 𝕋 σ₁ (Fin (ℓ + 1)) :=
      ((rootedAt σ₁ N v).restrict (insert v W') hroot).reindex (Fintype.equivOfCardEq hcoe)
      with hX
    obtain ⟨eX⟩ : Nonempty (Quotient.out X.toFlag ≃ᶠ X) :=
      Quotient.exact (Quotient.out_eq X.toFlag)
    refine Finset.mem_biUnion.mpr ⟨X.toFlag, mem_rootExtensions.mpr ⟨?_⟩,
      mem_flagWitnesses.mpr ⟨hroot, ?_, ⟨?_⟩⟩⟩
    · exact ((unrootIso (eX.trans
        (((rootedAt σ₁ N v).restrict _ hroot).reindexIso _).symm)).trans
        (unroot_restrict_iso N v hroot)).trans
        ((N.restrictCongr (Finset.erase_insert hv') _ _).trans e')
    · rw [Finset.card_insert_of_notMem hv', hcard', Fintype.card_fin, Fintype.card_fin]
    · exact (((rootedAt σ₁ N v).restrict _ hroot).reindexIso _).trans eX.symm
  · intro W hW
    obtain ⟨F, -, hWF⟩ := Finset.mem_biUnion.mp hW
    obtain ⟨hroot, -, -⟩ := mem_flagWitnesses.mp hWF
    exact Finset.insert_erase (hroot 0)
  · intro W' hW'
    have hv' : v ∉ W' := (Finset.subset_erase.mp (Finset.mem_filter.mp hW').2).2
    exact Finset.erase_insert hv'

/-! ## The rootings: root-containing witnesses of `M` -/

/-- The witnesses of the rootings of `M` in `(N, v)` are exactly the
witnesses of `M` in `N` that contain `v`. -/
theorem biUnion_labelPlacements_eq {ℓ : ℕ} (M : FlagWithSize 𝕋 (emptyType S) ℓ) :
    (labelPlacements σ₁ M).biUnion
        (fun F => flagWitnesses (Quotient.out F) (rootedAt σ₁ N v))
      = (flagWitnesses (Quotient.out M) N).filter (fun W => v ∈ W) := by
  ext W
  rw [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨F, hF, hWF⟩
    obtain ⟨hroot, hcard, ⟨e⟩⟩ := mem_flagWitnesses.mp hWF
    have hM : Flag.unlabel F = M := mem_labelPlacements.mp hF
    have hout : (Quotient.out F).unlabel.toFlag = Quotient.mk _ (Quotient.out M) := by
      rw [out_unlabel_toFlag_eq, hM, Quotient.out_eq]
    obtain ⟨e'⟩ := Quotient.exact hout
    refine ⟨mem_flagWitnesses.mpr ⟨emptyType_root_mem _ _, hcard, ⟨?_⟩⟩, hroot 0⟩
    exact ((LabeledFlagIso.ofEmptyType (ModelIso.refl _) :
      N.restrict W (emptyType_root_mem N W)
        ≃ᶠ ((rootedAt σ₁ N v).restrict W hroot).unlabel).trans e.unlabel).trans e'
  · rintro ⟨hwit, hv⟩
    obtain ⟨hr, hcard, ⟨e⟩⟩ := mem_flagWitnesses.mp hwit
    have hroot : ∀ t, (rootedAt σ₁ N v).rootEmbed.toEmbedding t ∈ W := fun _ => hv
    have hcoe : Fintype.card {x // x ∈ W} = Fintype.card (Fin ℓ) := by
      rw [Fintype.card_coe, hcard]
    set X : LabeledFlag 𝕋 σ₁ (Fin ℓ) :=
      ((rootedAt σ₁ N v).restrict W hroot).reindex (Fintype.equivOfCardEq hcoe) with hX
    obtain ⟨eX⟩ : Nonempty (Quotient.out X.toFlag ≃ᶠ X) :=
      Quotient.exact (Quotient.out_eq X.toFlag)
    refine ⟨X.toFlag, mem_labelPlacements.mpr ?_, mem_flagWitnesses.mpr
      ⟨hroot, hcard, ⟨(((rootedAt σ₁ N v).restrict W hroot).reindexIso _).trans eX.symm⟩⟩⟩
    rw [Flag.unlabel_mk, ← Quotient.out_eq M]
    exact Quotient.sound ⟨((((rootedAt σ₁ N v).restrict W hroot).reindexIso _).symm.unlabel).trans
      ((LabeledFlagIso.ofEmptyType (ModelIso.refl _) :
        ((rootedAt σ₁ N v).restrict W hroot).unlabel
          ≃ᶠ N.restrict W (emptyType_root_mem N W)).trans e)⟩

theorem sum_labelPlacements_flagCount {ℓ : ℕ} (M : FlagWithSize 𝕋 (emptyType S) ℓ) :
    ∑ F ∈ labelPlacements σ₁ M, flagCount (Quotient.out F) (rootedAt σ₁ N v)
      = ((flagWitnesses (Quotient.out M) N).filter (fun W => v ∈ W)).card := by
  rw [sum_flagCount_out, biUnion_labelPlacements_eq]

omit [S.NullaryFree] [𝕋.VertexUniform σ₁] in
/-- The witnesses of `M` in `N − v` are the witnesses of `M` in `N` avoiding
`v`. -/
theorem flagCount_deleteVertex_eq_filter {ℓ : ℕ} (M : FlagWithSize 𝕋 (emptyType S) ℓ) :
    flagCount (Quotient.out M) (deleteVertex N v)
      = ((flagWitnesses (Quotient.out M) N).filter (fun W => v ∉ W)).card := by
  rw [deleteVertex, flagCount_restrict, Finset.filter_congr_decidable]
  congr 1
  refine Finset.filter_congr fun W _ => ?_
  rw [Finset.subset_erase]
  exact ⟨fun h => h.2, fun h => ⟨Finset.subset_univ W, h⟩⟩

omit [S.NullaryFree] [𝕋.VertexUniform σ₁] in
theorem flagCount_split {ℓ : ℕ} (M : FlagWithSize 𝕋 (emptyType S) ℓ) :
    ((flagWitnesses (Quotient.out M) N).filter (fun W => v ∈ W)).card
        + ((flagWitnesses (Quotient.out M) N).filter (fun W => v ∉ W)).card
      = flagCount (Quotient.out M) N :=
  Finset.card_filter_add_card_filter_not _

omit [S.NullaryFree] [𝕋.VertexUniform σ₁] in
/-- **Averaging the deletion over the vertex**, at the level of counts:
`∑_v |wit(M, N − v)| = (|V| − ℓ) |wit(M, N)|`. -/
theorem sum_flagCount_deleteVertex {ℓ : ℕ} (M : FlagWithSize 𝕋 (emptyType S) ℓ) :
    ∑ v : V, flagCount (Quotient.out M) (deleteVertex N v)
      = (Fintype.card V - ℓ) * flagCount (Quotient.out M) N := by
  rw [Finset.sum_congr rfl fun v _ => flagCount_deleteVertex_eq_filter N v M]
  have h : ∀ v : V, ((flagWitnesses (Quotient.out M) N).filter (fun W => v ∉ W)).card
      = ∑ W ∈ flagWitnesses (Quotient.out M) N, if v ∉ W then 1 else 0 := fun v => by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun v _ => h v, Finset.sum_comm]
  have h2 : ∀ W ∈ flagWitnesses (Quotient.out M) N,
      (∑ v : V, if v ∉ W then 1 else 0) = Fintype.card V - ℓ := by
    intro W hW
    obtain ⟨-, hcard, -⟩ := mem_flagWitnesses.mp hW
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones, Finset.filter_not,
      Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ_diff, hcard,
      Fintype.card_fin]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]
  rfl

/-! ## The density identities -/

/-- `p^{(N,v)}(π¹ M) = p(M, N − v)`. -/
theorem sum_rootExtensions_flagDensity {ℓ L : ℕ} (M : FlagWithSize 𝕋 (emptyType S) ℓ)
    (hV : Fintype.card V = L + 1) :
    ∑ F ∈ rootExtensions σ₁ M, flagDensity (Quotient.out F) (rootedAt σ₁ N v)
      = flagDensity (Quotient.out M) (deleteVertex N v) := by
  have hterm : ∀ F ∈ rootExtensions σ₁ M,
      flagDensity (Quotient.out F) (rootedAt σ₁ N v)
        = (flagCount (Quotient.out F) (rootedAt σ₁ N v) : ℚ) / (L.choose ℓ : ℚ) := by
    intro F _
    rw [flagDensity]
    simp only [Fintype.card_fin, hV, Nat.add_sub_cancel]
  have hdel : flagDensity (Quotient.out M) (deleteVertex N v)
      = (flagCount (Quotient.out M) (deleteVertex N v) : ℚ) / (L.choose ℓ : ℚ) := by
    rw [flagDensity]
    simp only [Fintype.card_fin, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ, hV, Nat.add_sub_cancel, Nat.sub_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, hdel, ← Nat.cast_sum,
    sum_rootExtensions_flagCount]

omit [S.NullaryFree] [𝕋.VertexUniform σ₁] in
theorem flagDensity_deleteVertex_eq {ℓ L : ℕ} (M : FlagWithSize 𝕋 (emptyType S) ℓ)
    (hV : Fintype.card V = L + 1) :
    flagDensity (Quotient.out M) (deleteVertex N v)
      = (((flagWitnesses (Quotient.out M) N).filter (fun W => v ∉ W)).card : ℚ)
        / (L.choose ℓ : ℚ) := by
  rw [flagDensity, flagCount_deleteVertex_eq_filter]
  simp only [Fintype.card_fin, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ v),
    Finset.card_univ, hV, Nat.add_sub_cancel, Nat.sub_zero]

/-- **Total probability** (Razborov, proof of Lemma 4.2(a)): conditioning the
uniformly random `ℓ`-subset defining `p(M, N)` on whether it contains `v`. -/
theorem flagDensity_total_probability {ℓ L : ℕ} (M : FlagWithSize 𝕋 (emptyType S) ℓ)
    (hV : Fintype.card V = L + 1) (hℓ : ℓ ≤ L) :
    flagDensity (Quotient.out M) N
      = ((ℓ : ℚ) / ((L : ℚ) + 1))
          * ∑ F ∈ labelPlacements σ₁ M, flagDensity (Quotient.out F) (rootedAt σ₁ N v)
        + (((L + 1 - ℓ : ℕ) : ℚ) / ((L : ℚ) + 1))
          * flagDensity (Quotient.out M) (deleteVertex N v) := by
  set cIn := ((flagWitnesses (Quotient.out M) N).filter (fun W => v ∈ W)).card with hcIn
  set cOut := ((flagWitnesses (Quotient.out M) N).filter (fun W => v ∉ W)).card with hcOut
  have hsplit : cIn + cOut = flagCount (Quotient.out M) N := flagCount_split N v M
  have hpN : flagDensity (Quotient.out M) N
      = (flagCount (Quotient.out M) N : ℚ) / ((L + 1).choose ℓ : ℚ) := by
    rw [flagDensity]
    simp only [Fintype.card_fin, hV, Nat.sub_zero]
  have hdel : flagDensity (Quotient.out M) (deleteVertex N v)
      = (cOut : ℚ) / (L.choose ℓ : ℚ) := flagDensity_deleteVertex_eq N v M hV
  have hmu : ∑ F ∈ labelPlacements σ₁ M, flagDensity (Quotient.out F) (rootedAt σ₁ N v)
      = (cIn : ℚ) / (L.choose (ℓ - 1) : ℚ) := by
    have hterm : ∀ F ∈ labelPlacements σ₁ M,
        flagDensity (Quotient.out F) (rootedAt σ₁ N v)
          = (flagCount (Quotient.out F) (rootedAt σ₁ N v) : ℚ) / (L.choose (ℓ - 1) : ℚ) := by
      intro F _
      rw [flagDensity]
      simp only [Fintype.card_fin, hV, Nat.add_sub_cancel]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Nat.cast_sum,
      sum_labelPlacements_flagCount]
  rw [hpN, hdel, hmu]
  have hL1 : ((L : ℚ) + 1) ≠ 0 := by positivity
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · have h0 : cIn = 0 := by
      rw [hcIn, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro W hW hv
      obtain ⟨-, hcard, -⟩ := mem_flagWitnesses.mp hW
      rw [Fintype.card_fin] at hcard
      exact Finset.notMem_empty v (Finset.card_eq_zero.mp hcard ▸ hv)
    rw [← hsplit, h0]
    simp only [Nat.cast_zero, zero_div, zero_mul, zero_add, Nat.sub_zero,
      Nat.choose_zero_right, Nat.cast_one, div_one]
    push_cast
    rw [div_self hL1, one_mul]
  · obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
    have hb0 : (0 : ℚ) < L.choose k := by exact_mod_cast Nat.choose_pos (by omega)
    have hc0 : (0 : ℚ) < L.choose (k + 1) := by exact_mod_cast Nat.choose_pos hℓ
    have ha0 : (0 : ℚ) < (L + 1).choose (k + 1) := by
      exact_mod_cast Nat.choose_pos (by omega)
    have hb : ((L : ℚ) + 1) * (L.choose k : ℚ)
        = ((L + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq L k
    have hc : (L.choose (k + 1) : ℚ) * ((L : ℚ) + 1)
        = ((L + 1).choose (k + 1) : ℚ) * ((L + 1 - (k + 1) : ℕ) : ℚ) := by
      exact_mod_cast Nat.choose_mul_succ_eq L (k + 1)
    have h1 : ((k + 1 : ℕ) : ℚ) / ((L : ℚ) + 1) * ((cIn : ℚ) / (L.choose (k + 1 - 1) : ℚ))
        = (cIn : ℚ) / ((L + 1).choose (k + 1) : ℚ) := by
      rw [Nat.add_sub_cancel, div_mul_div_comm, div_eq_div_iff (mul_ne_zero hL1 hb0.ne') ha0.ne']
      push_cast
      linear_combination (-(cIn : ℚ)) * hb
    have h2 : ((L + 1 - (k + 1) : ℕ) : ℚ) / ((L : ℚ) + 1)
          * ((cOut : ℚ) / (L.choose (k + 1) : ℚ))
        = (cOut : ℚ) / ((L + 1).choose (k + 1) : ℚ) := by
      rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hL1 hc0.ne') ha0.ne']
      linear_combination (-(cOut : ℚ)) * hc
    rw [h1, h2, ← add_div, ← hsplit, Nat.cast_add]

/-! ## Lemma 4.2(a) -/

/-- **Razborov's Lemma 4.2(a).** For a model `M` on `ℓ` vertices, a host `N`
on `L + 1 ≥ ℓ + 1` vertices and a vertex `v` of `N`,
`p(M, N − v) = p(M, N) + (1/(L+1)) · p^{(N,v)}(∂₁ M)`. -/
theorem vertex_deletion_density (M : FinFlag 𝕋 (emptyType S)) {L : ℕ}
    (hV : Fintype.card V = L + 1) (hL : M.1 ≤ L) :
    ((flagDensity (Quotient.out M.2) (deleteVertex N v) : ℚ) : ℝ)
      = ((flagDensity (Quotient.out M.2) N : ℚ) : ℝ)
        + (1 / ((L : ℝ) + 1))
          * hostEval (rootedAt σ₁ N v) (partialVertexVec σ₁ (basisVector M)) := by
  rw [hostEval_partialVertexVec_basisVector, sum_rootExtensions_flagDensity N v M.2 hV]
  have hμ := flagDensity_total_probability (σ₁ := σ₁) N v M.2 hV hL
  set P : ℚ := flagDensity (Quotient.out M.2) (deleteVertex N v) with hP
  set p : ℚ := flagDensity (Quotient.out M.2) N with hp
  set Sμ : ℚ := ∑ F ∈ labelPlacements σ₁ M.2, flagDensity (Quotient.out F) (rootedAt σ₁ N v)
    with hSμ
  have hsub : ((L + 1 - M.1 : ℕ) : ℚ) = (L : ℚ) + 1 - M.1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hsub] at hμ
  have key : P = p + (1 / ((L : ℚ) + 1)) * ((M.1 : ℚ) * (P - Sμ)) := by
    have h1 : ((L : ℚ) + 1) ≠ 0 := by positivity
    rw [hμ]
    field_simp
    ring
  calc (P : ℝ) = ((p + (1 / ((L : ℚ) + 1)) * ((M.1 : ℚ) * (P - Sμ)) : ℚ) : ℝ) := by
        rw [← key]
    _ = (p : ℝ) + 1 / ((L : ℝ) + 1) * ((M.1 : ℝ) * ((P : ℝ) - (Sμ : ℝ))) := by
        push_cast
        ring

/-- Lemma 4.2(a) extended linearly to flag vectors supported on sizes `≤ L`. -/
theorem vertex_deletion_hostEval (f : FlagVector 𝕋 (emptyType S)) {L : ℕ}
    (hV : Fintype.card V = L + 1) (hf : ∀ M ∈ f.support, M.1 ≤ L) :
    hostEval (deleteVertex N v) f
      = hostEval N f
        + (1 / ((L : ℝ) + 1)) * hostEval (rootedAt σ₁ N v) (partialVertexVec σ₁ f) := by
  rw [partialVertexVec_eq_sum, hostEval_sum, Finset.mul_sum, hostEval_apply, hostEval_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun M hM => ?_
  rw [hostEval_smul, vertex_deletion_density (σ₁ := σ₁) N v M hV (hf M hM)]
  ring

/-! ## The differential has mean zero over the root -/

omit [S.NullaryFree] in
/-- Averaging the deletion over the vertex, in density form:
`∑_v p(M, N − v) = |V| · p(M, N)`. -/
theorem sum_flagDensity_deleteVertex {ℓ L : ℕ} (M : FlagWithSize 𝕋 (emptyType S) ℓ)
    (hV : Fintype.card V = L + 1) (hℓ : ℓ ≤ L) :
    ∑ v : V, flagDensity (Quotient.out M) (deleteVertex N v)
      = ((L : ℚ) + 1) * flagDensity (Quotient.out M) N := by
  have hterm : ∀ v : V, flagDensity (Quotient.out M) (deleteVertex N v)
      = (flagCount (Quotient.out M) (deleteVertex N v) : ℚ) / (L.choose ℓ : ℚ) := by
    intro v
    rw [flagDensity]
    simp only [Fintype.card_fin, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ, hV, Nat.add_sub_cancel, Nat.sub_zero]
  rw [Finset.sum_congr rfl fun v _ => hterm v, ← Finset.sum_div, ← Nat.cast_sum,
    sum_flagCount_deleteVertex, hV, flagDensity]
  simp only [Fintype.card_fin, hV, Nat.sub_zero]
  have hc0 : (0 : ℚ) < L.choose ℓ := by exact_mod_cast Nat.choose_pos hℓ
  have ha0 : (0 : ℚ) < (L + 1).choose ℓ := by exact_mod_cast Nat.choose_pos (by omega)
  have hbin : (L.choose ℓ : ℚ) * ((L : ℚ) + 1)
      = ((L + 1).choose ℓ : ℚ) * ((L + 1 - ℓ : ℕ) : ℚ) := by
    exact_mod_cast Nat.choose_mul_succ_eq L ℓ
  rw [mul_div_assoc', div_eq_div_iff hc0.ne' ha0.ne']
  push_cast
  linear_combination (-(flagCount (Quotient.out M) N : ℚ)) * hbin

/-- **The differential has mean zero over the root**: summing
`p^{(N,v)}(∂₁ f)` over all vertices `v` gives zero. -/
theorem sum_hostEval_partialVertexVec (f : FlagVector 𝕋 (emptyType S)) {L : ℕ}
    (hV : Fintype.card V = L + 1) (hf : ∀ M ∈ f.support, M.1 ≤ L) :
    ∑ v : V, hostEval (rootedAt σ₁ N v) (partialVertexVec σ₁ f) = 0 := by
  have hL1 : ((L : ℝ) + 1) ≠ 0 := by positivity
  have h : ∀ v : V, hostEval (rootedAt σ₁ N v) (partialVertexVec σ₁ f)
      = ((L : ℝ) + 1) * (hostEval (deleteVertex N v) f - hostEval N f) := by
    intro v
    rw [vertex_deletion_hostEval (σ₁ := σ₁) N v f hV hf]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun v _ => h v, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, hV, nsmul_eq_mul]
  have hsum : ∑ v : V, hostEval (deleteVertex N v) f = ((L : ℝ) + 1) * hostEval N f := by
    simp_rw [hostEval_apply]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun M hM => ?_
    rw [← Finset.mul_sum, ← Rat.cast_sum, sum_flagDensity_deleteVertex N M.2 hV (hf M hM)]
    push_cast
    ring
  rw [hsum]
  push_cast
  ring

end FlagAlgebras.Core
