import LeanFlagAlgebras.Core.Differential.Descent

/-! # Core: the upward operator and Razborov's Theorem 2.8(a)

The upward operator `π¹ : A⁰ → A¹` (Razborov §2.3.2, for the vertex type):
on models, `π¹(M)` is the sum of the `1`-flags obtained by attaching a new
root to `M` in every way (`piVec` of `Core/Differential/Vertex`), extended
linearly (`upwardVec`). It respects the zero spaces because
`p^{(N,v)}(π¹ f) = p(f, N − v)` (`hostEval_upwardVec`, the first counting
identity of `Core/Differential/Deletion`), so it descends to `upward`.

**Theorem 2.8(a)**: `⟦π¹(x) · y⟧₁ = x · ⟦y⟧₁` for `x ∈ A⁰`, `y ∈ A¹`
(`downward_upward_mul`). Both sides are evaluated at every host `H` of size
`n ≥ |F| + |G|` for basis flags `F`, `G`. The left side is the vertex average
of the pair densities `p(F', G; (H,v))` over the root extensions `F'` of
`F`; the right side is `q(G) · p(F, G|₀; H)`. Removing the root from `W₁`
identifies the rooted witness pairs `(v, W₁, W₂)` with the disjoint witness
pairs `(W₁', W₂)` of `(F, G|₀)` in `H` carrying a labeling of `H|_{W₂}`
realizing `G` (`sum_pairCount_rootExtensions`), and the two binomial
normalizers match. The zero-space criterion then gives the identity in
`A⁰`. -/

namespace FlagAlgebras.Core

open Finset
open Classical

variable {S : Signature} [S.NullaryFree] {𝕋 : RelTheory S}
variable {σ₁ : Model S (Fin 1)} [hvu : 𝕋.VertexUniform σ₁] [𝕋.IsType σ₁]

/-! ## Root sets of rooted and unlabeled hosts -/

section Roots

variable {V : Type} [Fintype V]

omit [S.NullaryFree] [𝕋.IsType σ₁] in
theorem mem_rootFinset_rootedAt (N : LabeledFlag 𝕋 (emptyType S) V) (v x : V) :
    x ∈ (rootedAt σ₁ N v).rootFinset ↔ x = v := by
  unfold LabeledFlag.rootFinset
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, rfl⟩
    rfl
  · rintro rfl
    exact ⟨0, rfl⟩

omit [S.NullaryFree] hvu in
theorem notMem_rootFinset_emptyType (N : LabeledFlag 𝕋 (emptyType S) V) (x : V) :
    x ∉ N.rootFinset := by
  intro h
  obtain ⟨t, -, -⟩ := Finset.mem_map.mp h
  exact t.elim0

end Roots

/-! ## The upward operator on flag vectors -/

variable (σ₁) in
/-- The upward operator `π¹` on flag vectors: the linear extension of
`piVec`. -/
noncomputable def upwardVec : FlagVector 𝕋 (emptyType S) → FlagVector 𝕋 σ₁ :=
  linearExtension (piVec σ₁)

omit hvu [𝕋.IsType σ₁] in
@[simp]
theorem upwardVec_basisVector (M : FinFlag 𝕋 (emptyType S)) :
    upwardVec σ₁ (basisVector M) = piVec σ₁ M := by
  unfold upwardVec
  rw [linearExtension_basisVector]

omit hvu [𝕋.IsType σ₁] in
theorem upwardVec_add (f f' : FlagVector 𝕋 (emptyType S)) :
    upwardVec σ₁ (f + f') = upwardVec σ₁ f + upwardVec σ₁ f' := by
  unfold upwardVec
  rw [linearExtension_add]

omit hvu [𝕋.IsType σ₁] in
theorem upwardVec_sub (f f' : FlagVector 𝕋 (emptyType S)) :
    upwardVec σ₁ (f - f') = upwardVec σ₁ f - upwardVec σ₁ f' := by
  unfold upwardVec
  rw [linearExtension_sub]

omit hvu [𝕋.IsType σ₁] in
theorem upwardVec_smul (r : ℝ) (f : FlagVector 𝕋 (emptyType S)) :
    upwardVec σ₁ (r • f) = r • upwardVec σ₁ f := by
  unfold upwardVec
  rw [linearExtension_smul]

omit hvu [𝕋.IsType σ₁] in
theorem upwardVec_eq_sum (f : FlagVector 𝕋 (emptyType S)) :
    upwardVec σ₁ f = ∑ M ∈ f.support, f M • piVec σ₁ M :=
  rfl

omit hvu [𝕋.IsType σ₁] in
theorem mem_support_piVec {M : FinFlag 𝕋 (emptyType S)} {F : FinFlag 𝕋 σ₁}
    (hF : F ∈ (piVec σ₁ M).support) : F.1 = M.1 + 1 := by
  unfold piVec at hF
  obtain ⟨G, -, hG⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum hF)
  rw [basisVector_support, Finset.mem_singleton] at hG
  subst hG
  rfl

omit [𝕋.IsType σ₁] in
/-- `p^{(N,v)}(π¹ f) = p(f, N − v)`: the first counting identity, linearly
extended. -/
theorem hostEval_upwardVec {V : Type} [Fintype V] [DecidableEq V]
    (N : LabeledFlag 𝕋 (emptyType S) V) (v : V) (f : FlagVector 𝕋 (emptyType S)) :
    hostEval (rootedAt σ₁ N v) (upwardVec σ₁ f) = hostEval (deleteVertex N v) f := by
  have hV : Fintype.card V = (Fintype.card V - 1) + 1 := by
    have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    omega
  rw [upwardVec_eq_sum, hostEval_sum, hostEval_apply]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [hostEval_smul, hostEval_piVec, sum_rootExtensions_flagDensity N v M.2 hV]

/-! ## The upward operator on the flag algebra -/

omit [𝕋.IsType σ₁] in
/-- The upward operator respects the zero spaces (Razborov Theorem 2.8, the
well-definedness of `π¹`). -/
theorem upwardVec_zeroSpace {k : FlagVector 𝕋 (emptyType S)}
    (hk : k ∈ ZeroSpace 𝕋 (emptyType S)) :
    upwardVec σ₁ k ∈ ZeroSpace 𝕋 σ₁ := by
  obtain ⟨L₀, hL₀⟩ := zeroSpace_densityEval_eventually_zero hk
  set B := k.support.sup (fun M => M.1) with hB
  have hBsupp : ∀ M ∈ k.support, M.1 ≤ B := fun M hM => Finset.le_sup (f := fun M => M.1) hM
  set L := max B L₀ with hL
  refine mem_zeroSpace_of_densityEval_zero (L := L + 1) ?_ ?_
  · intro F hF
    unfold upwardVec linearExtension at hF
    obtain ⟨M, hM, hFM⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum hF)
    have := mem_support_piVec (Finsupp.support_smul hFM)
    have := hBsupp M hM
    omega
  · intro G
    rw [densityEval_out]
    set N := (Quotient.out G).unlabel with hN
    set r := (Quotient.out G).rootEmbed.toEmbedding 0 with hr
    have hG : Quotient.out G = rootedAt σ₁ N r := (rootedAt_unlabel_root _).symm
    rw [hG, hostEval_upwardVec, hostEval_eq_densityEval_reindex]
    refine hL₀ _ ?_ _
    rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ,
      Fintype.card_fin]
    omega

/-- **The upward operator** `π¹ : A⁰ → A¹` on the flag algebras. -/
noncomputable def upward :
    FlagAlgebra 𝕋 (emptyType S) → FlagAlgebra 𝕋 σ₁ :=
  Quotient.map (upwardVec σ₁) fun f g hfg => by
    show upwardVec σ₁ f - upwardVec σ₁ g ∈ ZeroSpace 𝕋 σ₁
    rw [← upwardVec_sub]
    exact upwardVec_zeroSpace hfg

omit [𝕋.IsType σ₁] in
@[simp]
theorem upward_quot (f : FlagVector 𝕋 (emptyType S)) :
    upward (σ₁ := σ₁) (⟦f⟧ : FlagAlgebra 𝕋 (emptyType S)) = ⟦upwardVec σ₁ f⟧ :=
  rfl

omit [𝕋.IsType σ₁] in
theorem upward_add (x y : FlagAlgebra 𝕋 (emptyType S)) :
    upward (σ₁ := σ₁) (x + y) = upward x + upward y := by
  rw [← Quotient.out_eq x, ← Quotient.out_eq y, ← add_quot, upward_quot, upward_quot,
    upward_quot, upwardVec_add, add_quot]

omit [𝕋.IsType σ₁] in
theorem upward_smul (r : ℝ) (x : FlagAlgebra 𝕋 (emptyType S)) :
    upward (σ₁ := σ₁) (r • x) = r • upward x := by
  rw [← Quotient.out_eq x, ← smul_quot, upward_quot, upward_quot, upwardVec_smul, smul_quot]

omit [S.NullaryFree] hvu in
theorem quot_sub (f g : FlagVector 𝕋 σ₁) :
    (⟦f - g⟧ : FlagAlgebra 𝕋 σ₁) = (⟦f⟧ : FlagAlgebra 𝕋 σ₁) - (⟦g⟧ : FlagAlgebra 𝕋 σ₁) := by
  rw [sub_eq_add_neg, add_quot, neg_quot, ← sub_eq_add_neg]

variable (σ₁) in
/-- Razborov's `π̃¹ M` in the algebra: the sum of the rootings of `M`. -/
noncomputable def muElt (M : FinFlag 𝕋 (emptyType S)) : FlagAlgebra 𝕋 σ₁ :=
  ⟦muVec σ₁ M⟧

/-- The vertex differential is `ℓ (π¹ M − π̃¹ M)` on the algebra as well. -/
theorem partialVertex_basis (M : FinFlag 𝕋 (emptyType S)) :
    partialVertex (σ₁ := σ₁) (⟦basisVector M⟧ : FlagAlgebra 𝕋 (emptyType S))
      = (M.1 : ℝ) • (upward (σ₁ := σ₁) ⟦basisVector M⟧ - muElt σ₁ M) := by
  rw [partialVertex_quot, partialVertexVec_basisVector, upward_quot, upwardVec_basisVector,
    smul_quot, muElt, quot_sub]

/-! ## Witness transport between `(N, v)` and `N` -/

section Witnesses

variable {V : Type} [Fintype V] [DecidableEq V]
variable (N : LabeledFlag 𝕋 (emptyType S) V) (v : V)

omit [𝕋.IsType σ₁] in
/-- A root-containing witness of a root extension of `M` in `(N, v)`, with
the root removed, is a witness of `M` in `N`. -/
theorem erase_mem_flagWitnesses_of_rootExtension {ℓ : ℕ}
    {M : FlagWithSize 𝕋 (emptyType S) ℓ} {F' : FlagWithSize 𝕋 σ₁ (ℓ + 1)}
    (hF' : F' ∈ rootExtensions σ₁ M) {W : Finset V}
    (hW : W ∈ flagWitnesses (Quotient.out F') (rootedAt σ₁ N v)) :
    W.erase v ∈ flagWitnesses (Quotient.out M) N := by
  obtain ⟨e'⟩ := mem_rootExtensions.mp hF'
  obtain ⟨hroot, hcard, ⟨e⟩⟩ := mem_flagWitnesses.mp hW
  have hv : v ∈ W := hroot 0
  refine mem_flagWitnesses.mpr ⟨emptyType_root_mem _ _, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem hv, hcard, Fintype.card_fin, Fintype.card_fin,
      Nat.add_sub_cancel]
  · exact ⟨((unroot_restrict_iso N v hroot).symm.trans (unrootIso e)).trans e'⟩

omit [𝕋.IsType σ₁] in
/-- A witness of `M` in `N` avoiding `v`, with `v` inserted, witnesses some
root extension of `M` in `(N, v)`. -/
theorem exists_rootExtension_insert {ℓ : ℕ} {M : FlagWithSize 𝕋 (emptyType S) ℓ}
    {W' : Finset V} (hW' : W' ∈ flagWitnesses (Quotient.out M) N) (hv' : v ∉ W') :
    ∃ F' ∈ rootExtensions σ₁ M,
      insert v W' ∈ flagWitnesses (Quotient.out F') (rootedAt σ₁ N v) := by
  obtain ⟨hr', hcard', ⟨e'⟩⟩ := mem_flagWitnesses.mp hW'
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
  refine ⟨X.toFlag, mem_rootExtensions.mpr ⟨?_⟩, mem_flagWitnesses.mpr ⟨hroot, ?_, ⟨?_⟩⟩⟩
  · exact ((unrootIso (eX.trans
      (((rootedAt σ₁ N v).restrict _ hroot).reindexIso _).symm)).trans
      (unroot_restrict_iso N v hroot)).trans
      ((N.restrictCongr (Finset.erase_insert hv') _ _).trans e')
  · rw [Finset.card_insert_of_notMem hv', hcard', Fintype.card_fin, Fintype.card_fin]
  · exact (((rootedAt σ₁ N v).restrict _ hroot).reindexIso _).trans eX.symm

omit [𝕋.IsType σ₁] [DecidableEq V] in
/-- A witness of a rooted flag in `(N, v)` witnesses its unlabeling in `N`. -/
theorem mem_flagWitnesses_unlabel_of_rooted {m : ℕ} {G : LabeledFlag 𝕋 σ₁ (Fin m)}
    {W : Finset V} (hW : W ∈ flagWitnesses G (rootedAt σ₁ N v)) :
    W ∈ flagWitnesses G.unlabel N := by
  obtain ⟨hroot, hcard, ⟨e⟩⟩ := mem_flagWitnesses.mp hW
  refine mem_flagWitnesses.mpr ⟨emptyType_root_mem _ _, hcard, ⟨?_⟩⟩
  exact (LabeledFlagIso.ofEmptyType (ModelIso.refl _) :
    N.restrict W (emptyType_root_mem N W) ≃ᶠ ((rootedAt σ₁ N v).restrict W hroot).unlabel).trans
    e.unlabel

omit [𝕋.IsType σ₁] in
/-- **Rooted witnesses are labelings**: the vertices `v` at which a subset
`W` witnesses `G` in `(N, v)` correspond to the labelings of `N|_W`
realizing `G`. -/
theorem card_filter_rooted_witness {m : ℕ} (G : LabeledFlag 𝕋 σ₁ (Fin m)) (W : Finset V) :
    (Finset.univ.filter fun v : V => W ∈ flagWitnesses G (rootedAt σ₁ N v)).card
      = labelingCount (N.restrict W (emptyType_root_mem N W)) G := by
  unfold labelingCount
  have hmem : ∀ v, W ∈ flagWitnesses G (rootedAt σ₁ N v) → v ∈ W :=
    fun v h => (mem_flagWitnesses.mp h).1 0
  refine Finset.card_bij' (fun v hv => constEmb ⟨v, hmem v (Finset.mem_filter.mp hv).2⟩)
    (fun θ _ => (θ 0).val) ?_ ?_ ?_ ?_
  · intro v hv
    obtain ⟨-, hW⟩ := Finset.mem_filter.mp hv
    obtain ⟨hroot, -, ⟨e⟩⟩ := mem_flagWitnesses.mp hW
    refine mem_flagLabelings.mpr ⟨isSigmaLabeling_vertexUniform _ _, ⟨?_⟩⟩
    have e' : rootedAt σ₁ (N.restrict W (emptyType_root_mem N W)) ⟨v, hmem v hW⟩ ≃ᶠ G := by
      rw [rootedAt_restrict]
      exact e
    exact e'
  · intro θ hθ
    obtain ⟨h, ⟨e⟩⟩ := mem_flagLabelings.mp hθ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      mem_flagWitnesses.mpr ⟨fun _ => (θ 0).property, ?_, ⟨?_⟩⟩⟩
    · rw [← Fintype.card_coe W]
      exact Fintype.card_congr e.toIso.toEquiv
    · have hθ' : (⟨(N.restrict W (emptyType_root_mem N W)).toModel,
          (N.restrict W (emptyType_root_mem N W)).mem, ⟨θ, h⟩⟩ :
            LabeledFlag 𝕋 σ₁ {x // x ∈ W})
          = rootedAt σ₁ (N.restrict W (emptyType_root_mem N W)) ⟨(θ 0).val, (θ 0).property⟩ :=
        LabeledFlag.ext_of rfl (Function.Embedding.ext fun i => by
          rw [Subsingleton.elim i 0]
          rfl)
      rw [hθ', rootedAt_restrict] at e
      exact e
  · intro v _
    rfl
  · intro θ _
    exact Function.Embedding.ext fun i => by
      rw [Subsingleton.elim i 0]
      rfl

omit [S.NullaryFree] hvu [𝕋.IsType σ₁] [DecidableEq V] in
/-- Witness pairs whose first components are of distinct classes are
disjoint. -/
theorem pairWitnesses_out_disjoint {m : ℕ} {ℓ' : ℕ} (G : LabeledFlag 𝕋 σ₁ (Fin m))
    (X : LabeledFlag 𝕋 σ₁ V) {F₁ F₂ : FlagWithSize 𝕋 σ₁ ℓ'} (hne : F₁ ≠ F₂) :
    Disjoint (pairWitnesses (Quotient.out F₁) G X) (pairWitnesses (Quotient.out F₂) G X) := by
  refine Finset.disjoint_left.mpr fun P h₁ h₂ => ?_
  have := Finset.disjoint_left.mp (flagWitnesses_out_disjoint X hne)
    (mem_pairWitnesses.mp h₁).1
  exact this (mem_pairWitnesses.mp h₂).1

omit [𝕋.IsType σ₁] in
/-- **The double count.** Rooted witness pairs of the root extensions of `M`
and of `G` in `(N, v)`, summed over `v`, are the disjoint witness pairs of
`M` and `G|₀` in `N`, each counted once per labeling of the second set
realizing `G`. -/
theorem sum_pairCount_rootExtensions {ℓ m : ℕ} (M : FlagWithSize 𝕋 (emptyType S) ℓ)
    (G : LabeledFlag 𝕋 σ₁ (Fin m)) :
    ∑ v : V, ∑ F' ∈ rootExtensions σ₁ M, pairCount (Quotient.out F') G (rootedAt σ₁ N v)
      = pairCount (Quotient.out M) G.unlabel N * labelingCount G.unlabel G := by
  have hL : ∀ v : V,
      ∑ F' ∈ rootExtensions σ₁ M, pairCount (Quotient.out F') G (rootedAt σ₁ N v)
        = ((rootExtensions σ₁ M).biUnion fun F' =>
            pairWitnesses (Quotient.out F') G (rootedAt σ₁ N v)).card := fun v => by
    rw [Finset.card_biUnion fun F₁ _ F₂ _ hne => pairWitnesses_out_disjoint G _ hne]
    rfl
  rw [Finset.sum_congr rfl fun v _ => hL v, ← Finset.card_sigma]
  have hR : pairCount (Quotient.out M) G.unlabel N * labelingCount G.unlabel G
      = ((pairWitnesses (Quotient.out M) G.unlabel N).sigma fun P =>
          Finset.univ.filter fun v : V => P.2 ∈ flagWitnesses G (rootedAt σ₁ N v)).card := by
    rw [Finset.card_sigma, pairCount, Finset.card_eq_sum_ones, Finset.sum_mul]
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [one_mul, card_filter_rooted_witness N G P.2]
    obtain ⟨-, h₂, -⟩ := mem_pairWitnesses.mp hP
    obtain ⟨hr, -, ⟨e⟩⟩ := mem_flagWitnesses.mp h₂
    exact (labelingCount_congr_host e G).symm
  rw [hR]
  refine Finset.card_bij' (fun x _ => ⟨(x.2.1.erase x.1, x.2.2), x.1⟩)
    (fun y _ => ⟨y.2, (insert y.2 y.1.1, y.1.2)⟩) ?_ ?_ ?_ ?_
  · rintro ⟨v, W₁, W₂⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨F', hF', hP⟩ := Finset.mem_biUnion.mp hx.2
    obtain ⟨h₁, h₂, hshare⟩ := mem_pairWitnesses.mp hP
    refine Finset.mem_sigma.mpr ⟨mem_pairWitnesses.mpr
      ⟨erase_mem_flagWitnesses_of_rootExtension N v hF' h₁,
        mem_flagWitnesses_unlabel_of_rooted N v h₂, ?_⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₂⟩⟩
    intro x hx₁ hx₂
    exfalso
    have hxv := (mem_rootFinset_rootedAt N v x).mp (hshare x (Finset.mem_of_mem_erase hx₁) hx₂)
    exact (Finset.mem_erase.mp hx₁).1 hxv
  · rintro ⟨⟨W₁', W₂⟩, v⟩ hy
    rw [Finset.mem_sigma] at hy
    obtain ⟨hP, hv⟩ := hy
    obtain ⟨h₁, h₂, hshare⟩ := mem_pairWitnesses.mp hP
    have hvW₂ : v ∈ W₂ := (mem_flagWitnesses.mp (Finset.mem_filter.mp hv).2).1 0
    have hv' : v ∉ W₁' := fun h => notMem_rootFinset_emptyType N v (hshare v h hvW₂)
    obtain ⟨F', hF', hins⟩ := exists_rootExtension_insert (σ₁ := σ₁) N v h₁ hv'
    refine Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_biUnion.mpr
      ⟨F', hF', mem_pairWitnesses.mpr ⟨hins, (Finset.mem_filter.mp hv).2, ?_⟩⟩⟩
    intro x hx₁ hx₂
    rw [mem_rootFinset_rootedAt]
    rcases Finset.mem_insert.mp hx₁ with rfl | hx₁'
    · rfl
    · exact absurd (hshare x hx₁' hx₂) (notMem_rootFinset_emptyType N x)
  · rintro ⟨v, W₁, W₂⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨F', -, hP⟩ := Finset.mem_biUnion.mp hx.2
    have hv : v ∈ W₁ := (mem_flagWitnesses.mp (mem_pairWitnesses.mp hP).1).1 0
    show (⟨v, (insert v (W₁.erase v), W₂)⟩ : Σ _ : V, Finset V × Finset V) = ⟨v, (W₁, W₂)⟩
    rw [Finset.insert_erase hv]
  · rintro ⟨⟨W₁', W₂⟩, v⟩ hy
    rw [Finset.mem_sigma] at hy
    obtain ⟨hP, hv⟩ := hy
    obtain ⟨-, -, hshare⟩ := mem_pairWitnesses.mp hP
    have hvW₂ : v ∈ W₂ := (mem_flagWitnesses.mp (Finset.mem_filter.mp hv).2).1 0
    have hv' : v ∉ W₁' := fun h => notMem_rootFinset_emptyType N v (hshare v h hvW₂)
    show (⟨((insert v W₁').erase v, W₂), v⟩ : Σ _ : Finset V × Finset V, V) = ⟨(W₁', W₂), v⟩
    rw [Finset.erase_insert hv']

end Witnesses

/-! ## Products and pair densities at a host -/

section Products

omit [S.NullaryFree] hvu in
theorem subflagPairDensity_out_out {T U₁ U₂ W : Type} [Fintype T] {σ : Model S T}
    [Fintype U₁] [Fintype U₂] [Fintype W] (A : Flag 𝕋 σ U₁) (B : Flag 𝕋 σ U₂)
    (X : LabeledFlag 𝕋 σ W) :
    subflagPairDensity A B X.toFlag
      = flagPairDensity (Quotient.out A) (Quotient.out B) X := by
  conv_lhs => rw [← Quotient.out_eq A, ← Quotient.out_eq B]
  rfl

omit hvu in
omit [S.NullaryFree] in
/-- The host evaluation of a flag product is the pair density. -/
theorem hostEval_flagMul {T : Type} [Fintype T] {σ : Model S T} {U : Type} [Fintype U]
    (X : LabeledFlag 𝕋 σ U) (A B : FinFlag 𝕋 σ)
    (h : A.1 + B.1 ≤ Fintype.card U + Fintype.card T) :
    hostEval X (flagMul A B)
      = ((flagPairDensity (Quotient.out A.2) (Quotient.out B.2) X : ℚ) : ℝ) := by
  have hk : Fintype.card T ≤ A.1 := finFlag_size_ge A
  unfold flagMul flagMulWithSize
  rw [hostEval_sum]
  simp_rw [hostEval_smul, hostEval_basisVector]
  rw [← subflagPairDensity_out_out, subflagPairDensity_chain_host
    (W' := Fin (A.1 + B.1 - Fintype.card T)) (by simp only [Fintype.card_fin]; omega)
    (by simp only [Fintype.card_fin]; omega) A.2 B.2 X.toFlag, Rat.cast_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [Rat.cast_mul, subflagDensity_toFlag_right]

omit [S.NullaryFree] hvu in
theorem mem_support_flagMul {T : Type} [Fintype T] {σ : Model S T} {A B : FinFlag 𝕋 σ}
    {K : FinFlag 𝕋 σ} (hK : K ∈ (flagMul A B).support) :
    K.1 = A.1 + B.1 - Fintype.card T := by
  unfold flagMul flagMulWithSize at hK
  obtain ⟨G, -, hG⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum hK)
  have := Finsupp.support_smul hG
  rw [basisVector_support, Finset.mem_singleton] at this
  subst this
  rfl

omit hvu [𝕋.IsType σ₁] in
theorem downwardVector_support_le {g : FlagVector 𝕋 σ₁} {B : ℕ}
    (hg : ∀ F ∈ g.support, F.1 ≤ B) :
    ∀ K ∈ (downwardVector g).support, K.1 ≤ B := by
  intro K hK
  unfold downwardVector linearExtension at hK
  obtain ⟨F', hF', hFF'⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum hK)
  have h1 := Finsupp.support_smul hFF'
  unfold downwardFinFlag at h1
  have h2 := Finsupp.support_smul h1
  rw [basisVector_support, Finset.mem_singleton] at h2
  subst h2
  exact hg F' hF'

end Products

/-! ## The density identity behind Theorem 2.8(a) -/

section Identity

omit hvu [𝕋.IsType σ₁] in
/-- The product of `π¹ F` with a basis flag, evaluated at a rooted host, is
the sum of pair densities over the root extensions. -/
theorem hostEval_piVec_mul_basisVector {V : Type} [Fintype V]
    (X : LabeledFlag 𝕋 σ₁ V) (F : FinFlag 𝕋 (emptyType S)) (G : FinFlag 𝕋 σ₁)
    (h : F.1 + 1 + G.1 ≤ Fintype.card V + 1) :
    hostEval X (piVec σ₁ F * basisVector G)
      = ∑ F' ∈ rootExtensions σ₁ F.2,
          ((flagPairDensity (Quotient.out F') (Quotient.out G.2) X : ℚ) : ℝ) := by
  unfold piVec
  rw [Finset.sum_mul, hostEval_sum]
  refine Finset.sum_congr rfl fun F' _ => ?_
  rw [basisVector_mul_basisVector, hostEval_flagMul X _ G (by simpa using h)]

omit hvu [𝕋.IsType σ₁] in
/-- The support of `π¹ F · G` lies at size `|F| + |G|`. -/
theorem support_piVec_mul_basisVector (F : FinFlag 𝕋 (emptyType S)) (G : FinFlag 𝕋 σ₁) :
    ∀ K ∈ (piVec σ₁ F * basisVector G).support, K.1 ≤ F.1 + G.1 := by
  intro K hK
  unfold piVec at hK
  rw [Finset.sum_mul] at hK
  obtain ⟨F', -, hK'⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum hK)
  rw [basisVector_mul_basisVector] at hK'
  have := mem_support_flagMul hK'
  simp only [Fintype.card_fin] at this
  omega

omit [𝕋.IsType σ₁] in
/-- **The vertex average of the rooted pair densities** is the labeling
factor times the unlabeled pair density. -/
theorem sum_hostEval_piVec_mul (F : FinFlag 𝕋 (emptyType S)) (G : FinFlag 𝕋 σ₁) {n : ℕ}
    (H : LabeledFlag 𝕋 (emptyType S) (Fin n)) (hn : F.1 + G.1 ≤ n) :
    (n : ℝ)⁻¹ * ∑ v : Fin n, hostEval (rootedAt σ₁ H v) (piVec σ₁ F * basisVector G)
      = ((labelingFactor (Quotient.out G.2).unlabel (Quotient.out G.2) : ℚ) : ℝ)
        * ((flagPairDensity (Quotient.out F.2) (Quotient.out G.2).unlabel H : ℚ) : ℝ) := by
  set ℓ := F.1 with hℓ
  set m := G.1 with hm
  have hm1 : 1 ≤ m := by
    have := finFlag_size_ge G
    simpa using this
  have hn1 : 1 ≤ n := by omega
  set lc := labelingCount (Quotient.out G.2).unlabel (Quotient.out G.2) with hlc
  set PC := pairCount (Quotient.out F.2) (Quotient.out G.2).unlabel H with hPC
  -- the rooted pair densities, summed
  have htermQ : ∀ (v : Fin n) (F' : FlagWithSize 𝕋 σ₁ (ℓ + 1)),
      flagPairDensity (Quotient.out F') (Quotient.out G.2) (rootedAt σ₁ H v)
        = (pairCount (Quotient.out F') (Quotient.out G.2) (rootedAt σ₁ H v) : ℚ)
          / (pairChoose (n - 1) ℓ (m - 1) : ℚ) := by
    intro v F'
    rw [flagPairDensity]
    simp only [Fintype.card_fin, Nat.add_sub_cancel]
    rfl
  have hsumQ : ∑ v : Fin n, ∑ F' ∈ rootExtensions σ₁ F.2,
      flagPairDensity (Quotient.out F') (Quotient.out G.2) (rootedAt σ₁ H v)
        = ((PC * lc : ℕ) : ℚ) / (pairChoose (n - 1) ℓ (m - 1) : ℚ) := by
    simp_rw [htermQ, ← Finset.sum_div]
    have hcast : (∑ v : Fin n, ∑ F' ∈ rootExtensions σ₁ F.2,
        (pairCount (Quotient.out F') (Quotient.out G.2) (rootedAt σ₁ H v) : ℚ))
        = ((∑ v : Fin n, ∑ F' ∈ rootExtensions σ₁ F.2,
            pairCount (Quotient.out F') (Quotient.out G.2) (rootedAt σ₁ H v) : ℕ) : ℚ) := by
      push_cast
      rfl
    rw [hcast, sum_pairCount_rootExtensions H F.2 (Quotient.out G.2)]
  have hsum : ∑ v : Fin n, hostEval (rootedAt σ₁ H v) (piVec σ₁ F * basisVector G)
      = ((((PC * lc : ℕ) : ℚ) / (pairChoose (n - 1) ℓ (m - 1) : ℚ) : ℚ) : ℝ) := by
    rw [Finset.sum_congr rfl fun v _ =>
      hostEval_piVec_mul_basisVector (rootedAt σ₁ H v) F G (by rw [Fintype.card_fin]; omega)]
    rw [← hsumQ]
    push_cast
    rfl
  rw [hsum]
  -- the unlabeled pair density and the labeling factor
  rw [flagPairDensity]
  simp only [Fintype.card_fin, Nat.sub_zero]
  rw [labelingFactor, Fintype.card_embedding_eq]
  simp only [Fintype.card_fin, Nat.descFactorial_one]
  rw [show (n : ℝ)⁻¹ = (((n : ℚ)⁻¹ : ℚ) : ℝ) by push_cast; rfl, ← Rat.cast_mul, ← Rat.cast_mul]
  congr 1
  -- the binomial identity `m · pairChoose n ℓ m = n · pairChoose (n-1) ℓ (m-1)`
  have hchoose1 : ((n - 1).choose ℓ : ℚ) * (n : ℚ) = (n.choose ℓ : ℚ) * ((n - ℓ : ℕ) : ℚ) := by
    have h := Nat.choose_mul_succ_eq (n - 1) ℓ
    rw [Nat.sub_add_cancel hn1] at h
    exact_mod_cast h
  have hchoose2 : ((n - ℓ : ℕ) : ℚ) * ((n - ℓ - 1).choose (m - 1) : ℚ)
      = ((n - ℓ).choose m : ℚ) * (m : ℚ) := by
    have h := Nat.add_one_mul_choose_eq (n - ℓ - 1) (m - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n - ℓ), Nat.sub_add_cancel hm1] at h
    exact_mod_cast h
  have hmain : (m : ℚ) * (pairChoose n ℓ m : ℚ) = (n : ℚ) * (pairChoose (n - 1) ℓ (m - 1) : ℚ) := by
    unfold pairChoose
    push_cast
    rw [Nat.sub_right_comm] at hchoose2
    linear_combination (-((n - 1 - ℓ).choose (m - 1) : ℚ)) * hchoose1
      + (-(n.choose ℓ : ℚ)) * hchoose2
  have hpos1 : (0 : ℚ) < pairChoose n ℓ m := by
    exact_mod_cast pairChoose_pos (by omega : ℓ + m ≤ n)
  have hpos2 : (0 : ℚ) < pairChoose (n - 1) ℓ (m - 1) := by
    exact_mod_cast pairChoose_pos (by omega : ℓ + (m - 1) ≤ n - 1)
  have hn0 : (0 : ℚ) < n := by exact_mod_cast hn1
  have hm0 : (0 : ℚ) < m := by exact_mod_cast hm1
  rw [inv_mul_eq_div, div_div, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero hpos2.ne' hn0.ne') (mul_ne_zero hm0.ne' hpos1.ne')]
  push_cast
  linear_combination ((PC : ℚ) * (lc : ℚ)) * hmain

/-- **Theorem 2.8(a) at the level of densities**: at every host of size
`n ≥ |F| + |G|`, `⟦π¹ F · G⟧₁` and `F · ⟦G⟧₁` evaluate alike. -/
theorem densityEval_downwardVector_piVec_mul (F : FinFlag 𝕋 (emptyType S)) (G : FinFlag 𝕋 σ₁)
    {n : ℕ} (H : LabeledFlag 𝕋 (emptyType S) (Fin n)) (hn : F.1 + G.1 ≤ n) :
    densityEval (downwardVector (piVec σ₁ F * basisVector G)) ⟨n, H.toFlag⟩
      = densityEval (basisVector F * downwardVector (basisVector G)) ⟨n, H.toFlag⟩ := by
  rw [densityEval_downwardVector H _ (fun K hK => (support_piVec_mul_basisVector F G K hK).trans hn),
    sum_hostEval_piVec_mul F G H hn]
  rw [downwardVector_basisVector, downwardFinFlag, ← one_smul ℝ (basisVector F),
    flagVector_smul_mul_smul_comm, one_mul, densityEval_smul, basisVector_mul_basisVector,
    ← hostEval_toFlag, hostEval_flagMul H F _ (by simp only [Fintype.card_fin]; omega)]
  congr 1
  obtain ⟨e⟩ : Nonempty (Quotient.out (⟨G.1, (Quotient.out G.2).unlabel.toFlag⟩ :
      FinFlag 𝕋 (emptyType S)).2 ≃ᶠ (Quotient.out G.2).unlabel) :=
    Quotient.exact (Quotient.out_eq (Quotient.out G.2).unlabel.toFlag)
  rw [flagPairDensity_congr (LabeledFlagIso.refl _) e (LabeledFlagIso.refl _)]

/-- The basis case of Theorem 2.8(a), in the zero space. -/
theorem downwardVector_piVec_mul_sub_mem (F : FinFlag 𝕋 (emptyType S)) (G : FinFlag 𝕋 σ₁) :
    downwardVector (piVec σ₁ F * basisVector G)
      - basisVector F * downwardVector (basisVector G) ∈ ZeroSpace 𝕋 (emptyType S) := by
  refine mem_zeroSpace_of_densityEval_zero (L := F.1 + G.1) ?_ ?_
  · intro K hK
    rcases Finset.mem_union.mp (Finsupp.support_sub hK) with h | h
    · exact downwardVector_support_le (support_piVec_mul_basisVector F G) K h
    · rw [downwardVector_basisVector, downwardFinFlag, ← one_smul ℝ (basisVector F),
        flagVector_smul_mul_smul_comm, basisVector_mul_basisVector] at h
      have := mem_support_flagMul (Finsupp.support_smul h)
      simp only [Fintype.card_fin, Nat.sub_zero] at this
      omega
  · intro H
    rw [densityEval_sub, sub_eq_zero]
    have h := densityEval_downwardVector_piVec_mul F G (Quotient.out H) le_rfl
    rw [show (Quotient.out H).toFlag = H from Quotient.out_eq H] at h
    exact h

/-- **Theorem 2.8(a) on flag vectors**: `⟦π¹ f · g⟧₁ − f · ⟦g⟧₁` lies in the
zero space. -/
theorem downwardVector_upwardVec_mul_sub_mem (f : FlagVector 𝕋 (emptyType S))
    (g : FlagVector 𝕋 σ₁) :
    downwardVector (upwardVec σ₁ f * g) - f * downwardVector g ∈ ZeroSpace 𝕋 (emptyType S) := by
  have hexp : upwardVec σ₁ f * g
      = ∑ F ∈ f.support, ∑ G ∈ g.support, (f F * g G) • (piVec σ₁ F * basisVector G) := by
    rw [upwardVec_eq_sum]
    conv_lhs => rw [flagVector_eq_sum_basisVector g]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun G _ => ?_
    rw [flagVector_smul_mul_smul_comm]
  have hexp' : f * downwardVector g
      = ∑ F ∈ f.support, ∑ G ∈ g.support,
          (f F * g G) • (basisVector F * downwardVector (basisVector G)) := by
    conv_lhs => rw [flagVector_eq_sum_basisVector f, flagVector_eq_sum_basisVector g]
    rw [downwardVector_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun G _ => ?_
    rw [downwardVector_smul, flagVector_smul_mul_smul_comm]
  rw [hexp, hexp', downwardVector_sum]
  simp_rw [downwardVector_sum, downwardVector_smul]
  rw [← Finset.sum_sub_distrib]
  refine zeroSpace_closed_under_sum _ _ fun F _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine zeroSpace_closed_under_sum _ _ fun G _ => ?_
  rw [← smul_sub]
  exact zeroSpace_closed_under_smul _ _ (downwardVector_piVec_mul_sub_mem F G)

/-- **Razborov's Theorem 2.8(a)**: `⟦π¹(x) · y⟧₁ = x · ⟦y⟧₁` for `x ∈ A⁰`,
`y ∈ A¹`. -/
theorem downward_upward_mul [𝕋.IsType (emptyType S)] (x : FlagAlgebra 𝕋 (emptyType S))
    (y : FlagAlgebra 𝕋 σ₁) :
    downward (upward (σ₁ := σ₁) x * y) = x * downward y := by
  refine Quotient.inductionOn₂ x y fun f g => ?_
  rw [upward_quot, ← mul_quot, downward_quot, downward_quot, ← mul_quot]
  exact Quotient.sound (downwardVector_upwardVec_mul_sub_mem f g)

end Identity

/-! ## Multiplicativity of the upward operator (Theorem 2.8, the homomorphism clause) -/

omit hvu [𝕋.IsType σ₁] in
theorem upwardVec_sum {ι : Type} (s : Finset ι) (c : ι → FlagVector 𝕋 (emptyType S)) :
    upwardVec σ₁ (∑ i ∈ s, c i) = ∑ i ∈ s, upwardVec σ₁ (c i) := by
  unfold upwardVec
  rw [linearExtension_sum]

section Multiplicative

variable {V : Type} [Fintype V] [DecidableEq V]
variable (N : LabeledFlag 𝕋 (emptyType S) V) (v : V)

omit [S.NullaryFree] hvu [𝕋.IsType σ₁] [DecidableEq V] in
/-- Witness pairs whose first components are of distinct classes are
disjoint. -/
theorem pairWitnesses_out_disjoint_left {m ℓ' : ℕ} (G₁ G₂ : LabeledFlag 𝕋 σ₁ (Fin m))
    (X : LabeledFlag 𝕋 σ₁ V) {F₁ F₂ : FlagWithSize 𝕋 σ₁ ℓ'} (hne : F₁ ≠ F₂) :
    Disjoint (pairWitnesses (Quotient.out F₁) G₁ X) (pairWitnesses (Quotient.out F₂) G₂ X) := by
  refine Finset.disjoint_left.mpr fun P h₁ h₂ => ?_
  have := Finset.disjoint_left.mp (flagWitnesses_out_disjoint X hne)
    (mem_pairWitnesses.mp h₁).1
  exact this (mem_pairWitnesses.mp h₂).1

omit [S.NullaryFree] hvu [𝕋.IsType σ₁] [DecidableEq V] in
/-- Witness pairs whose second components are of distinct classes are
disjoint. -/
theorem pairWitnesses_out_disjoint_right {m ℓ' : ℕ} (F₁ F₂ : LabeledFlag 𝕋 σ₁ (Fin m))
    (X : LabeledFlag 𝕋 σ₁ V) {G₁ G₂ : FlagWithSize 𝕋 σ₁ ℓ'} (hne : G₁ ≠ G₂) :
    Disjoint (pairWitnesses F₁ (Quotient.out G₁) X) (pairWitnesses F₂ (Quotient.out G₂) X) := by
  refine Finset.disjoint_left.mpr fun P h₁ h₂ => ?_
  have := Finset.disjoint_left.mp (flagWitnesses_out_disjoint X hne)
    (mem_pairWitnesses.mp h₁).2.1
  exact this (mem_pairWitnesses.mp h₂).2.1

omit [𝕋.IsType σ₁] in
/-- **The double count for products.** Rooted witness pairs of root extensions
of `M₁`, `M₂` in `(N, v)`, with the root removed from both sets, are the
witness pairs of `M₁`, `M₂` in `N − v`. -/
theorem sum_sum_pairCount_rootExtensions {ℓ₁ ℓ₂ : ℕ} (M₁ : FlagWithSize 𝕋 (emptyType S) ℓ₁)
    (M₂ : FlagWithSize 𝕋 (emptyType S) ℓ₂) :
    ∑ F₁' ∈ rootExtensions σ₁ M₁, ∑ F₂' ∈ rootExtensions σ₁ M₂,
        pairCount (Quotient.out F₁') (Quotient.out F₂') (rootedAt σ₁ N v)
      = pairCount (Quotient.out M₁) (Quotient.out M₂) (deleteVertex N v) := by
  rw [deleteVertex, pairCount_restrict]
  unfold pairRestrictCount
  rw [Finset.filter_congr_decidable, ← Finset.sum_product']
  have hdisj : ∀ P ∈ rootExtensions σ₁ M₁ ×ˢ rootExtensions σ₁ M₂,
      ∀ Q ∈ rootExtensions σ₁ M₁ ×ˢ rootExtensions σ₁ M₂, P ≠ Q →
        Disjoint (pairWitnesses (Quotient.out P.1) (Quotient.out P.2) (rootedAt σ₁ N v))
          (pairWitnesses (Quotient.out Q.1) (Quotient.out Q.2) (rootedAt σ₁ N v)) := by
    intro P _ Q _ hne
    by_cases h1 : P.1 = Q.1
    · exact pairWitnesses_out_disjoint_right _ _ _ fun h2 => hne (Prod.ext h1 h2)
    · exact pairWitnesses_out_disjoint_left _ _ _ h1
  rw [show (∑ P ∈ rootExtensions σ₁ M₁ ×ˢ rootExtensions σ₁ M₂,
      pairCount (Quotient.out P.1) (Quotient.out P.2) (rootedAt σ₁ N v))
      = ((rootExtensions σ₁ M₁ ×ˢ rootExtensions σ₁ M₂).biUnion fun P =>
          pairWitnesses (Quotient.out P.1) (Quotient.out P.2) (rootedAt σ₁ N v)).card from by
    rw [Finset.card_biUnion hdisj]
    rfl]
  refine Finset.card_bij' (fun P _ => (P.1.erase v, P.2.erase v))
    (fun Q _ => (insert v Q.1, insert v Q.2)) ?_ ?_ ?_ ?_
  · rintro ⟨W₁, W₂⟩ hP
    obtain ⟨⟨F₁', F₂'⟩, hF, hW⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨hF₁, hF₂⟩ := Finset.mem_product.mp hF
    obtain ⟨h₁, h₂, hshare⟩ := mem_pairWitnesses.mp hW
    refine Finset.mem_filter.mpr ⟨mem_pairWitnesses.mpr
      ⟨erase_mem_flagWitnesses_of_rootExtension N v hF₁ h₁,
        erase_mem_flagWitnesses_of_rootExtension N v hF₂ h₂, ?_⟩,
      Finset.erase_subset_erase v (Finset.subset_univ _),
      Finset.erase_subset_erase v (Finset.subset_univ _)⟩
    intro x hx₁ hx₂
    exfalso
    have hxv := (mem_rootFinset_rootedAt N v x).mp
      (hshare x (Finset.mem_of_mem_erase hx₁) (Finset.mem_of_mem_erase hx₂))
    exact (Finset.mem_erase.mp hx₁).1 hxv
  · rintro ⟨W₁', W₂'⟩ hQ
    obtain ⟨hQ, hsub₁, hsub₂⟩ := Finset.mem_filter.mp hQ
    obtain ⟨h₁, h₂, hshare⟩ := mem_pairWitnesses.mp hQ
    have hv₁ : v ∉ W₁' := (Finset.subset_erase.mp hsub₁).2
    have hv₂ : v ∉ W₂' := (Finset.subset_erase.mp hsub₂).2
    obtain ⟨F₁', hF₁, hins₁⟩ := exists_rootExtension_insert (σ₁ := σ₁) N v h₁ hv₁
    obtain ⟨F₂', hF₂, hins₂⟩ := exists_rootExtension_insert (σ₁ := σ₁) N v h₂ hv₂
    refine Finset.mem_biUnion.mpr ⟨(F₁', F₂'), Finset.mem_product.mpr ⟨hF₁, hF₂⟩,
      mem_pairWitnesses.mpr ⟨hins₁, hins₂, ?_⟩⟩
    intro x hx₁ hx₂
    rw [mem_rootFinset_rootedAt]
    rcases Finset.mem_insert.mp hx₁ with rfl | hx₁'
    · rfl
    · rcases Finset.mem_insert.mp hx₂ with rfl | hx₂'
      · rfl
      · exact absurd (hshare x hx₁' hx₂') (notMem_rootFinset_emptyType N x)
  · rintro ⟨W₁, W₂⟩ hP
    obtain ⟨⟨F₁', F₂'⟩, -, hW⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨h₁, h₂, -⟩ := mem_pairWitnesses.mp hW
    have hv₁ : v ∈ W₁ := (mem_flagWitnesses.mp h₁).1 0
    have hv₂ : v ∈ W₂ := (mem_flagWitnesses.mp h₂).1 0
    show (insert v (W₁.erase v), insert v (W₂.erase v)) = (W₁, W₂)
    rw [Finset.insert_erase hv₁, Finset.insert_erase hv₂]
  · rintro ⟨W₁', W₂'⟩ hQ
    obtain ⟨-, hsub₁, hsub₂⟩ := Finset.mem_filter.mp hQ
    have hv₁ : v ∉ W₁' := (Finset.subset_erase.mp hsub₁).2
    have hv₂ : v ∉ W₂' := (Finset.subset_erase.mp hsub₂).2
    show ((insert v W₁').erase v, (insert v W₂').erase v) = (W₁', W₂')
    rw [Finset.erase_insert hv₁, Finset.erase_insert hv₂]

omit [𝕋.IsType σ₁] in
/-- `p^{(N,v)}(π¹ M₁ · π¹ M₂) = p(M₁ · M₂, N − v)`: the rooted pair densities
of the root extensions sum to the pair density in `N − v` (the two
normalizers agree). -/
theorem hostEval_piVec_mul_piVec (M₁ M₂ : FinFlag 𝕋 (emptyType S))
    (hn : M₁.1 + M₂.1 + 1 ≤ Fintype.card V) :
    hostEval (rootedAt σ₁ N v) (piVec σ₁ M₁ * piVec σ₁ M₂)
      = hostEval (deleteVertex N v) (flagMul M₁ M₂) := by
  have hcard : ∀ inst : Fintype {x // x ∈ Finset.univ.erase v},
      @Fintype.card _ inst = Fintype.card V - 1 := fun inst => by
    rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
  rw [hostEval_flagMul _ M₁ M₂ (by rw [hcard, Fintype.card_fin]; omega), flagPairDensity]
  unfold piVec
  rw [Finset.sum_mul, hostEval_sum]
  simp_rw [Finset.mul_sum, hostEval_sum, basisVector_mul_basisVector]
  rw [Finset.sum_congr rfl fun F₁' _ => Finset.sum_congr rfl fun F₂' _ =>
    hostEval_flagMul (rootedAt σ₁ N v) _ _ (by simp only [Fintype.card_fin]; omega)]
  simp_rw [flagPairDensity]
  simp only [Fintype.card_fin, Nat.add_sub_cancel, Nat.sub_zero, hcard]
  have hcastR : (∑ F₁' ∈ rootExtensions σ₁ M₁.2, ∑ F₂' ∈ rootExtensions σ₁ M₂.2,
      (((pairCount (Quotient.out F₁') (Quotient.out F₂') (rootedAt σ₁ N v) : ℚ)
        / (pairChoose (Fintype.card V - 1) M₁.1 M₂.1 : ℚ) : ℚ) : ℝ))
      = ((∑ F₁' ∈ rootExtensions σ₁ M₁.2, ∑ F₂' ∈ rootExtensions σ₁ M₂.2,
          ((pairCount (Quotient.out F₁') (Quotient.out F₂') (rootedAt σ₁ N v) : ℚ)
            / (pairChoose (Fintype.card V - 1) M₁.1 M₂.1 : ℚ)) : ℚ) : ℝ) := by
    push_cast
    rfl
  rw [hcastR]
  congr 1
  simp_rw [← Finset.sum_div]
  congr 1
  have hcastQ : (∑ F₁' ∈ rootExtensions σ₁ M₁.2, ∑ F₂' ∈ rootExtensions σ₁ M₂.2,
      (pairCount (Quotient.out F₁') (Quotient.out F₂') (rootedAt σ₁ N v) : ℚ))
      = ((∑ F₁' ∈ rootExtensions σ₁ M₁.2, ∑ F₂' ∈ rootExtensions σ₁ M₂.2,
          pairCount (Quotient.out F₁') (Quotient.out F₂') (rootedAt σ₁ N v) : ℕ) : ℚ) := by
    push_cast
    rfl
  rw [hcastQ, sum_sum_pairCount_rootExtensions N v M₁.2 M₂.2]

omit hvu [𝕋.IsType σ₁] in
theorem support_piVec_mul_piVec (M₁ M₂ : FinFlag 𝕋 (emptyType S)) :
    ∀ K ∈ (piVec σ₁ M₁ * piVec σ₁ M₂).support, K.1 = M₁.1 + M₂.1 + 1 := by
  intro K hK
  unfold piVec at hK
  rw [Finset.sum_mul] at hK
  obtain ⟨F₁', -, hK₁⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum hK)
  rw [Finset.mul_sum] at hK₁
  obtain ⟨F₂', -, hK₂⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum hK₁)
  rw [basisVector_mul_basisVector] at hK₂
  have := mem_support_flagMul hK₂
  simp only [Fintype.card_fin] at this
  omega

end Multiplicative

omit [𝕋.IsType σ₁] in
/-- The basis case of multiplicativity, in the zero space. -/
theorem upwardVec_flagMul_sub_mem (M₁ M₂ : FinFlag 𝕋 (emptyType S)) :
    upwardVec σ₁ (flagMul M₁ M₂) - piVec σ₁ M₁ * piVec σ₁ M₂ ∈ ZeroSpace 𝕋 σ₁ := by
  refine mem_zeroSpace_of_densityEval_zero (L := M₁.1 + M₂.1 + 1) ?_ ?_
  · intro K hK
    rcases Finset.mem_union.mp (Finsupp.support_sub hK) with h | h
    · unfold upwardVec linearExtension at h
      obtain ⟨M, hM, hKM⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum h)
      have h1 := mem_support_piVec (Finsupp.support_smul hKM)
      have h2 := mem_support_flagMul hM
      simp only [Fintype.card_fin, Nat.sub_zero] at h2
      omega
    · exact (support_piVec_mul_piVec M₁ M₂ K h).le
  · intro G
    rw [densityEval_sub, sub_eq_zero, densityEval_out, densityEval_out]
    set N := (Quotient.out G).unlabel with hN
    set r := (Quotient.out G).rootEmbed.toEmbedding 0 with hr
    have hG : Quotient.out G = rootedAt σ₁ N r := (rootedAt_unlabel_root _).symm
    rw [hG, hostEval_upwardVec, hostEval_piVec_mul_piVec N r M₁ M₂ (by rw [Fintype.card_fin])]

omit [𝕋.IsType σ₁] in
/-- Multiplicativity on flag vectors: `π¹(f · g) − π¹(f) · π¹(g)` lies in the
zero space. -/
theorem upwardVec_mul_sub_mem (f g : FlagVector 𝕋 (emptyType S)) :
    upwardVec σ₁ (f * g) - upwardVec σ₁ f * upwardVec σ₁ g ∈ ZeroSpace 𝕋 σ₁ := by
  have h1 : upwardVec σ₁ (f * g)
      = ∑ F ∈ f.support, ∑ G ∈ g.support, (f F * g G) • upwardVec σ₁ (flagMul F G) := by
    rw [flagVector_mul_eq_nested_sum, upwardVec_sum]
    simp_rw [upwardVec_sum, upwardVec_smul]
  have h2 : upwardVec σ₁ f * upwardVec σ₁ g
      = ∑ F ∈ f.support, ∑ G ∈ g.support, (f F * g G) • (piVec σ₁ F * piVec σ₁ G) := by
    rw [upwardVec_eq_sum, upwardVec_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun G _ => ?_
    rw [flagVector_smul_mul_smul_comm]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine zeroSpace_closed_under_sum _ _ fun F _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine zeroSpace_closed_under_sum _ _ fun G _ => ?_
  rw [← smul_sub]
  exact zeroSpace_closed_under_smul _ _ (upwardVec_flagMul_sub_mem F G)

omit [𝕋.IsType σ₁] in
/-- **Razborov's Theorem 2.8, multiplicativity**: `π¹(x · y) = π¹(x) · π¹(y)`. -/
theorem upward_mul (x y : FlagAlgebra 𝕋 (emptyType S)) :
    upward (σ₁ := σ₁) (x * y) = upward x * upward y := by
  refine Quotient.inductionOn₂ x y fun f g => ?_
  rw [← mul_quot, upward_quot, upward_quot, upward_quot, ← mul_quot]
  exact Quotient.sound (upwardVec_mul_sub_mem f g)

omit [𝕋.IsType σ₁] in
theorem upward_zero : upward (σ₁ := σ₁) (0 : FlagAlgebra 𝕋 (emptyType S)) = 0 := by
  show upward (σ₁ := σ₁) (⟦0⟧ : FlagAlgebra 𝕋 (emptyType S)) = ⟦0⟧
  rw [upward_quot]
  exact congrArg _ (linearExtension_zero _)

/-! ## The unit -/

omit hvu [𝕋.IsType σ₁] in
/-- Empty-type flags on empty carriers are isomorphic. -/
noncomputable def LabeledFlagIso.ofIsEmpty {V W : Type} [IsEmpty V] [IsEmpty W]
    (F : LabeledFlag 𝕋 (emptyType S) V) (G : LabeledFlag 𝕋 (emptyType S) W) : F ≃ᶠ G :=
  LabeledFlagIso.ofEmptyType ⟨Equiv.equivOfIsEmpty V W,
    fun r f => (IsEmpty.false (f ⟨0, Signature.NullaryFree.ar_pos r⟩)).elim⟩

omit hvu [𝕋.IsType σ₁] in
/-- Every one-vertex `1`-flag is a root extension of the empty flag. -/
theorem rootExtensions_unit [𝕋.IsType (emptyType S)] :
    rootExtensions σ₁ (1 : FinFlag 𝕋 (emptyType S)).2 = Finset.univ := by
  ext F'
  simp only [Finset.mem_univ, iff_true]
  rw [mem_rootExtensions]
  haveI h1 : IsEmpty {x // x ∈ (Finset.univ :
      Finset (Fin ((1 : FinFlag 𝕋 (emptyType S)).1 + 1))).erase
        ((Quotient.out F').rootEmbed.toEmbedding 0)} := by
    refine Fintype.card_eq_zero_iff.mp ?_
    rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, finFlag_one_fst, Fintype.card_fin]
  haveI h2 : IsEmpty (Fin (1 : FinFlag 𝕋 (emptyType S)).1) := by
    refine Fintype.card_eq_zero_iff.mp ?_
    rw [Fintype.card_fin, finFlag_one_fst, Fintype.card_fin]
  exact ⟨LabeledFlagIso.ofIsEmpty _ _⟩

/-- **`π¹(1) = 1`**: the root extensions of the empty flag are all the
one-vertex `1`-flags, which sum to the unit. -/
theorem upward_one [𝕋.IsType (emptyType S)] :
    upward (σ₁ := σ₁) (1 : FlagAlgebra 𝕋 (emptyType S)) = 1 := by
  show upward (σ₁ := σ₁) (⟦basisVector 1⟧ : FlagAlgebra 𝕋 (emptyType S)) = 1
  rw [upward_quot, upwardVec_basisVector, piVec, rootExtensions_unit, sum_quot]
  exact sum_flagWithSize_eq_one _ (by rw [finFlag_one_fst]; simp)

/-- **Razborov's Theorem 2.8**: the upward operator is an `ℝ`-algebra
homomorphism `A⁰ → A¹`. -/
noncomputable def upwardAlgHom [𝕋.IsType (emptyType S)] :
    FlagAlgebra 𝕋 (emptyType S) →ₐ[ℝ] FlagAlgebra 𝕋 σ₁ where
  toFun := upward
  map_one' := upward_one
  map_mul' := upward_mul
  map_zero' := upward_zero
  map_add' := upward_add
  commutes' := fun r => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, upward_smul, upward_one]

@[simp]
theorem upwardAlgHom_apply [𝕋.IsType (emptyType S)] (x : FlagAlgebra 𝕋 (emptyType S)) :
    upwardAlgHom (σ₁ := σ₁) x = upward x :=
  rfl

end FlagAlgebras.Core
