import LeanFlagAlgebras.Core.Differential.Eval

/-! # Core: the vertex type, rooting, vertex deletion and `∂₁`

Razborov's differential method (§4.3) works over a *vertex uniform* theory:
one whose one-vertex models are all isomorphic, so that there is a single
type `1` of size one and every vertex of every model can serve as its root.
This file sets up, theory-generically:

* `RelTheory.VertexUniform 𝕋 σ₁` — the one-vertex model `σ₁` is the
  induced substructure at every vertex of every member model;
* `rootedAt σ₁ N v` — the `1`-flag `(N, v)`;
* `deleteVertex N v` — the host `N − v`, the induced sub-flag on the other
  vertices; `unroot F` — a `1`-flag with its root removed;
* `rootExtensions σ₁ M` — the `1`-flags of size `ℓ + 1` whose root-deleted
  flag is `M`; `labelPlacements σ₁ M` — the `1`-flags of size `ℓ` whose
  unlabeling is `M` (the rootings of `M`);
* `piVec σ₁ M = ∑ rootExtensions` (the model-level upward operator `π¹`),
  `muVec σ₁ M = ∑ labelPlacements` (Razborov's `π̃¹`), and the vertex
  differential `partialVertexVec σ₁ M = ℓ (π¹ M − π̃¹ M)`, extended linearly.

The counting identities relating these to vertex deletion are in
`Core/Differential/Deletion`. -/

namespace FlagAlgebras.Core

open Finset
open Classical

variable {S : Signature} [S.NullaryFree] {𝕋 : RelTheory S}

/-! ## Vertex uniformity -/

/-- The constant embedding of the one-point type at `v`. -/
def constEmb {V : Type} (v : V) : Fin 1 ↪ V :=
  ⟨fun _ => v, fun a b _ => Subsingleton.elim a b⟩

@[simp]
theorem constEmb_apply {V : Type} (v : V) (i : Fin 1) : constEmb v i = v :=
  rfl

/-- **Vertex uniformity** (Razborov §4.3): the one-vertex model `σ₁` is the
induced substructure at every vertex of every member model, so that every
vertex is a `σ₁`-labeling. For the uniform theories and their
forbidden-substructure subtheories this holds with `σ₁` the discrete
one-point model. -/
class RelTheory.VertexUniform (𝕋 : RelTheory S) (σ₁ : Model S (Fin 1)) : Prop where
  /-- Every vertex is a `σ₁`-labeling. -/
  interp_const : ∀ {V : Type} (N : Model S V), 𝕋.Mem N → ∀ (v : V) (r : S.Rel)
    (f : Fin (S.ar r) → Fin 1), N.interp r (⇑(constEmb v) ∘ f) ↔ σ₁.interp r f

omit [S.NullaryFree] in
/-- Two labeled flags with the same model and the same root embedding are
equal. -/
theorem LabeledFlag.ext_of {T V : Type} {σ : Model S T} {F G : LabeledFlag 𝕋 σ V}
    (hM : F.toModel = G.toModel)
    (hθ : F.rootEmbed.toEmbedding = G.rootEmbed.toEmbedding) : F = G := by
  obtain ⟨M, hM', ⟨θ, hθ'⟩⟩ := F
  obtain ⟨M', hM'', ⟨θ', hθ''⟩⟩ := G
  change M = M' at hM
  change θ = θ' at hθ
  subst hM
  subst hθ
  rfl

/-- Every empty-type flag is its own unlabeling. -/
theorem LabeledFlag.unlabel_emptyType {V : Type} (N : LabeledFlag 𝕋 (emptyType S) V) :
    N.unlabel = N :=
  LabeledFlag.ext_of rfl (Function.Embedding.ext fun x => x.elim0)

variable {σ₁ : Model S (Fin 1)}

/-! ## Rooting -/

section Rooting

variable [𝕋.VertexUniform σ₁]

variable (σ₁) in
/-- The host rooted at a vertex: the `1`-flag `(N, v)`. -/
def rootedAt {V : Type} (N : LabeledFlag 𝕋 (emptyType S) V) (v : V) :
    LabeledFlag 𝕋 σ₁ V :=
  ⟨N.toModel, N.mem,
    ⟨constEmb v, RelTheory.VertexUniform.interp_const N.toModel N.mem v⟩⟩

omit [S.NullaryFree] in
@[simp]
theorem rootedAt_toModel {V : Type} (N : LabeledFlag 𝕋 (emptyType S) V) (v : V) :
    (rootedAt σ₁ N v).toModel = N.toModel :=
  rfl

omit [S.NullaryFree] in
@[simp]
theorem rootedAt_root {V : Type} (N : LabeledFlag 𝕋 (emptyType S) V) (v : V)
    (i : Fin 1) : (rootedAt σ₁ N v).rootEmbed.toEmbedding i = v :=
  rfl

variable (𝕋 σ₁) in
/-- Over a vertex uniform theory the vertex type is a type of the theory. -/
theorem RelTheory.VertexUniform.isType : 𝕋.IsType σ₁ := by
  obtain ⟨M, hM⟩ := 𝕋.mem_inhabited 1
  exact ⟨(rootedAt σ₁ (LabeledFlag.ofEmptyType hM) 0).type_mem⟩

/-- Rooting the unlabeling of a `1`-flag at its root recovers the flag:
every `1`-flag is of the form `(N, v)`. -/
theorem rootedAt_unlabel_root {V : Type} (F : LabeledFlag 𝕋 σ₁ V) :
    rootedAt σ₁ F.unlabel (F.rootEmbed.toEmbedding 0) = F :=
  LabeledFlag.ext_of rfl (Function.Embedding.ext fun i => by
    show F.rootEmbed.toEmbedding 0 = F.rootEmbed.toEmbedding i
    exact congrArg _ (Subsingleton.elim 0 i))

omit [S.NullaryFree] in
/-- Rooting a restriction is restricting the rooted host. -/
theorem rootedAt_restrict {V : Type} (N : LabeledFlag 𝕋 (emptyType S) V)
    {A : Finset V} (hA : ∀ t, N.rootEmbed.toEmbedding t ∈ A) (v : V) (hv : v ∈ A) :
    rootedAt σ₁ (N.restrict A hA) ⟨v, hv⟩
      = (rootedAt σ₁ N v).restrict A (fun _ => hv) :=
  LabeledFlag.ext_of rfl (Function.Embedding.ext fun _ => rfl)

end Rooting

/-! ## Vertex deletion and unrooting -/

/-- The host with the vertex `v` deleted: the induced sub-flag on the
other vertices. -/
noncomputable def deleteVertex {V : Type} [Fintype V] [DecidableEq V]
    (N : LabeledFlag 𝕋 (emptyType S) V) (v : V) : LabeledFlag 𝕋 (emptyType S) {x // x ∈ Finset.univ.erase v} :=
  N.restrict (Finset.univ.erase v) (emptyType_root_mem N _)

/-- A `1`-flag with its root removed. -/
noncomputable def unroot {V : Type} [Fintype V] [DecidableEq V] (F : LabeledFlag 𝕋 σ₁ V) :
    LabeledFlag 𝕋 (emptyType S)
      {x // x ∈ Finset.univ.erase (F.rootEmbed.toEmbedding 0)} :=
  F.unlabel.restrict (Finset.univ.erase (F.rootEmbed.toEmbedding 0))
    (emptyType_root_mem _ _)

/-- Unrooting respects flag isomorphism. -/
noncomputable def unrootIso {V W : Type} [Fintype V] [Fintype W] [DecidableEq V]
    [DecidableEq W] {F : LabeledFlag 𝕋 σ₁ V} {G : LabeledFlag 𝕋 σ₁ W} (e : F ≃ᶠ G) :
    unroot F ≃ᶠ unroot G :=
  (e.unlabel.restrictMap (Finset.univ.erase (F.rootEmbed.toEmbedding 0))
    (emptyType_root_mem _ _)).trans
    (G.unlabel.restrictCongr (by
      rw [Finset.map_erase, Finset.map_univ_equiv]
      congr 1
      exact e.root_preserve 0) _ _)

section RootedDeletion

variable [𝕋.VertexUniform σ₁]

theorem unroot_rootedAt {V : Type} [Fintype V] [DecidableEq V]
    (N : LabeledFlag 𝕋 (emptyType S) V) (v : V) : unroot (rootedAt σ₁ N v) = deleteVertex N v :=
  LabeledFlag.ext_of rfl (Function.Embedding.ext fun x => x.elim0)

/-- Unrooting the restriction of a rooted host to a root-containing subset is
restricting the host to the subset with the root removed. -/
noncomputable def unroot_restrict_iso {V : Type} [Fintype V] [DecidableEq V]
    (N : LabeledFlag 𝕋 (emptyType S) V) (v : V) {W : Finset V}
    (hW : ∀ t, (rootedAt σ₁ N v).rootEmbed.toEmbedding t ∈ W) :
    unroot ((rootedAt σ₁ N v).restrict W hW)
      ≃ᶠ N.restrict (W.erase v) (emptyType_root_mem N _) := by
  let r : {x // x ∈ W} := ((rootedAt σ₁ N v).restrict W hW).rootEmbed.toEmbedding 0
  let e₀ : ((rootedAt σ₁ N v).restrict W hW).unlabel
      ≃ᶠ N.restrict W (emptyType_root_mem N W) :=
    LabeledFlagIso.ofEmptyType (ModelIso.refl _)
  have h1 : (Finset.univ.erase r).map e₀.toIso.toEquiv.toEmbedding = Finset.univ.erase r := by
    show (Finset.univ.erase r).map (Equiv.refl _).toEmbedding = _
    rw [Equiv.refl_toEmbedding, Finset.map_refl]
  have h2 : (Finset.univ.erase r).map (Function.Embedding.subtype (· ∈ W)) = W.erase v := by
    rw [Finset.map_erase, Finset.univ_eq_attach, Finset.attach_map_val]
    rfl
  let i₁ : unroot ((rootedAt σ₁ N v).restrict W hW)
      ≃ᶠ (N.restrict W (emptyType_root_mem N W)).restrict
          ((Finset.univ.erase r).map e₀.toIso.toEquiv.toEmbedding)
          (e₀.root_mem_map (emptyType_root_mem _ _)) :=
    e₀.restrictMap (Finset.univ.erase r) (emptyType_root_mem _ _)
  let i₂ : (N.restrict W (emptyType_root_mem N W)).restrict
          ((Finset.univ.erase r).map e₀.toIso.toEquiv.toEmbedding)
          (e₀.root_mem_map (emptyType_root_mem _ _))
      ≃ᶠ (N.restrict W (emptyType_root_mem N W)).restrict (Finset.univ.erase r)
          (emptyType_root_mem _ _) :=
    (N.restrict W (emptyType_root_mem N W)).restrictCongr h1 _ _
  let i₃ : (N.restrict W (emptyType_root_mem N W)).restrict (Finset.univ.erase r)
          (emptyType_root_mem _ _)
      ≃ᶠ N.restrict ((Finset.univ.erase r).map (Function.Embedding.subtype (· ∈ W)))
          (N.root_mem_map_subtype (emptyType_root_mem N W) (emptyType_root_mem _ _)) :=
    N.restrictRestrict (emptyType_root_mem N W) (emptyType_root_mem _ _)
  let i₄ : N.restrict ((Finset.univ.erase r).map (Function.Embedding.subtype (· ∈ W)))
          (N.root_mem_map_subtype (emptyType_root_mem N W) (emptyType_root_mem _ _))
      ≃ᶠ N.restrict (W.erase v) (emptyType_root_mem N _) :=
    N.restrictCongr h2 _ _
  exact ((i₁.trans i₂).trans i₃).trans i₄

end RootedDeletion

/-! ## Root extensions, rootings, and the vertex differential -/

variable (σ₁) in
/-- The root extensions of an unlabeled class `M` on `ℓ` vertices: the
`1`-flags on `ℓ + 1` vertices whose root-deleted flag is `M`. -/
noncomputable def rootExtensions {ℓ : ℕ} (M : FlagWithSize 𝕋 (emptyType S) ℓ) :
    Finset (FlagWithSize 𝕋 σ₁ (ℓ + 1)) :=
  Finset.univ.filter fun F => Nonempty (unroot (Quotient.out F) ≃ᶠ Quotient.out M)

theorem mem_rootExtensions {ℓ : ℕ} {M : FlagWithSize 𝕋 (emptyType S) ℓ}
    {F : FlagWithSize 𝕋 σ₁ (ℓ + 1)} :
    F ∈ rootExtensions σ₁ M ↔ Nonempty (unroot (Quotient.out F) ≃ᶠ Quotient.out M) := by
  unfold rootExtensions
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

variable (σ₁) in
/-- The rootings of an unlabeled class `M`: the `1`-flags of the same size
whose unlabeling is `M`. -/
noncomputable def labelPlacements {ℓ : ℕ} (M : FlagWithSize 𝕋 (emptyType S) ℓ) :
    Finset (FlagWithSize 𝕋 σ₁ ℓ) :=
  Finset.univ.filter fun F => Flag.unlabel F = M

theorem mem_labelPlacements {ℓ : ℕ} {M : FlagWithSize 𝕋 (emptyType S) ℓ}
    {F : FlagWithSize 𝕋 σ₁ ℓ} :
    F ∈ labelPlacements σ₁ M ↔ Flag.unlabel F = M := by
  unfold labelPlacements
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

variable (σ₁) in
/-- Razborov's model-level upward operator `π¹(M)`: the sum of all
`1`-flags obtained from `M` by attaching a new root in every possible
way. -/
noncomputable def piVec (M : FinFlag 𝕋 (emptyType S)) : FlagVector 𝕋 σ₁ :=
  ∑ F ∈ rootExtensions σ₁ M.2, basisVector ⟨M.1 + 1, F⟩

variable (σ₁) in
/-- Razborov's `π̃¹(M)`: the sum of all rootings of `M`. -/
noncomputable def muVec (M : FinFlag 𝕋 (emptyType S)) : FlagVector 𝕋 σ₁ :=
  ∑ F ∈ labelPlacements σ₁ M.2, basisVector ⟨M.1, F⟩

variable (σ₁) in
/-- **The vertex differential** on formal combinations of models:
`∂₁ M = ℓ (π¹(M) − π̃¹(M))` for `M` on `ℓ` vertices, extended linearly. -/
noncomputable def partialVertexVec : FlagVector 𝕋 (emptyType S) → FlagVector 𝕋 σ₁ :=
  linearExtension fun M : FinFlag 𝕋 (emptyType S) =>
    (M.1 : ℝ) • (piVec σ₁ M - muVec σ₁ M)

@[simp]
theorem partialVertexVec_basisVector (M : FinFlag 𝕋 (emptyType S)) :
    partialVertexVec σ₁ (basisVector M) = (M.1 : ℝ) • (piVec σ₁ M - muVec σ₁ M) := by
  unfold partialVertexVec
  rw [linearExtension_basisVector]

theorem partialVertexVec_add (f f' : FlagVector 𝕋 (emptyType S)) :
    partialVertexVec σ₁ (f + f') = partialVertexVec σ₁ f + partialVertexVec σ₁ f' := by
  unfold partialVertexVec
  rw [linearExtension_add]

theorem partialVertexVec_sub (f f' : FlagVector 𝕋 (emptyType S)) :
    partialVertexVec σ₁ (f - f') = partialVertexVec σ₁ f - partialVertexVec σ₁ f' := by
  unfold partialVertexVec
  rw [linearExtension_sub]

theorem partialVertexVec_smul (r : ℝ) (f : FlagVector 𝕋 (emptyType S)) :
    partialVertexVec σ₁ (r • f) = r • partialVertexVec σ₁ f := by
  unfold partialVertexVec
  rw [linearExtension_smul]

theorem partialVertexVec_sum {ι : Type} (s : Finset ι)
    (c : ι → FlagVector 𝕋 (emptyType S)) :
    partialVertexVec σ₁ (∑ i ∈ s, c i) = ∑ i ∈ s, partialVertexVec σ₁ (c i) := by
  unfold partialVertexVec
  rw [linearExtension_sum]

theorem partialVertexVec_eq_sum (f : FlagVector 𝕋 (emptyType S)) :
    partialVertexVec σ₁ f
      = ∑ M ∈ f.support, f M • partialVertexVec σ₁ (basisVector M) := by
  simp_rw [partialVertexVec_basisVector]
  rfl

/-- The vertex differential raises the support sizes by at most one. -/
theorem partialVertexVec_support_le {f : FlagVector 𝕋 (emptyType S)} {B : ℕ}
    (hf : ∀ M ∈ f.support, M.1 ≤ B) :
    ∀ F ∈ (partialVertexVec σ₁ f).support, F.1 ≤ B + 1 := by
  intro F hF
  unfold partialVertexVec linearExtension at hF
  obtain ⟨M, hM, hFM⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum hF)
  have hFM' := Finsupp.support_smul (Finsupp.support_smul hFM)
  rcases Finset.mem_union.mp (Finsupp.support_sub hFM') with h | h
  · unfold piVec at h
    obtain ⟨G, -, hG⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum h)
    rw [basisVector_support, Finset.mem_singleton] at hG
    subst hG
    exact Nat.succ_le_succ (hf M hM)
  · unfold muVec at h
    obtain ⟨G, -, hG⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum h)
    rw [basisVector_support, Finset.mem_singleton] at hG
    subst hG
    exact Nat.le_succ_of_le (hf M hM)

/-! ## Host evaluations of `π¹`, `π̃¹` and `∂₁` -/

section HostEval

variable {V : Type} [Fintype V]

theorem hostEval_piVec (G : LabeledFlag 𝕋 σ₁ V) (M : FinFlag 𝕋 (emptyType S)) :
    hostEval G (piVec σ₁ M)
      = ((∑ F ∈ rootExtensions σ₁ M.2, flagDensity (Quotient.out F) G : ℚ) : ℝ) := by
  unfold piVec
  rw [hostEval_sum, Rat.cast_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [hostEval_basisVector]

theorem hostEval_muVec (G : LabeledFlag 𝕋 σ₁ V) (M : FinFlag 𝕋 (emptyType S)) :
    hostEval G (muVec σ₁ M)
      = ((∑ F ∈ labelPlacements σ₁ M.2, flagDensity (Quotient.out F) G : ℚ) : ℝ) := by
  unfold muVec
  rw [hostEval_sum, Rat.cast_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [hostEval_basisVector]

theorem hostEval_partialVertexVec_basisVector (G : LabeledFlag 𝕋 σ₁ V)
    (M : FinFlag 𝕋 (emptyType S)) :
    hostEval G (partialVertexVec σ₁ (basisVector M))
      = (M.1 : ℝ) *
        (((∑ F ∈ rootExtensions σ₁ M.2, flagDensity (Quotient.out F) G : ℚ) : ℝ)
          - ((∑ F ∈ labelPlacements σ₁ M.2, flagDensity (Quotient.out F) G : ℚ) : ℝ)) := by
  rw [partialVertexVec_basisVector, hostEval_smul, hostEval_sub, hostEval_piVec,
    hostEval_muVec]

variable (σ₁) in
/-- A crude bound on the evaluation of `∂₁ M`, uniform in the host. -/
noncomputable def partialBound (M : FinFlag 𝕋 (emptyType S)) : ℝ :=
  (M.1 : ℝ) * ((rootExtensions σ₁ M.2).card + (labelPlacements σ₁ M.2).card)

theorem partialBound_nonneg (M : FinFlag 𝕋 (emptyType S)) :
    0 ≤ partialBound σ₁ M :=
  mul_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

omit [S.NullaryFree] in
theorem sum_flagDensity_le_card {T : Type} [Fintype T] {σ : Model S T} {W : Type}
    [Fintype W] (G : LabeledFlag 𝕋 σ V) (s : Finset (Flag 𝕋 σ W)) :
    ((∑ F ∈ s, flagDensity (Quotient.out F) G : ℚ) : ℝ) ≤ s.card := by
  rw [Rat.cast_sum]
  calc (∑ F ∈ s, ((flagDensity (Quotient.out F) G : ℚ) : ℝ))
      ≤ ∑ _F ∈ s, (1 : ℝ) := Finset.sum_le_sum fun F _ => by
          exact_mod_cast flagDensity_le_one (Quotient.out F) G
    _ = s.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

omit [S.NullaryFree] in
theorem sum_flagDensity_nonneg {T : Type} [Fintype T] {σ : Model S T} {W : Type}
    [Fintype W] (G : LabeledFlag 𝕋 σ V) (s : Finset (Flag 𝕋 σ W)) :
    0 ≤ ((∑ F ∈ s, flagDensity (Quotient.out F) G : ℚ) : ℝ) := by
  rw [Rat.cast_sum]
  exact Finset.sum_nonneg fun F _ => Rat.cast_nonneg.mpr (flagDensity_nonneg (Quotient.out F) G)

theorem abs_hostEval_partialVertexVec_basisVector_le (G : LabeledFlag 𝕋 σ₁ V)
    (M : FinFlag 𝕋 (emptyType S)) :
    |hostEval G (partialVertexVec σ₁ (basisVector M))| ≤ partialBound σ₁ M := by
  rw [hostEval_partialVertexVec_basisVector, partialBound, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) M.1)]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg M.1)
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_of_nonneg (sum_flagDensity_nonneg G _)]
    exact sum_flagDensity_le_card G _
  · rw [abs_of_nonneg (sum_flagDensity_nonneg G _)]
    exact sum_flagDensity_le_card G _

/-- The evaluation of `∂₁ f` is bounded uniformly in the host. -/
theorem abs_hostEval_partialVertexVec_le (G : LabeledFlag 𝕋 σ₁ V)
    (f : FlagVector 𝕋 (emptyType S)) :
    |hostEval G (partialVertexVec σ₁ f)|
      ≤ ∑ M ∈ f.support, |f M| * partialBound σ₁ M := by
  rw [partialVertexVec_eq_sum, hostEval_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun M _ => ?_)
  rw [hostEval_smul, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_hostEval_partialVertexVec_basisVector_le G M)
    (abs_nonneg _)

end HostEval

end FlagAlgebras.Core
