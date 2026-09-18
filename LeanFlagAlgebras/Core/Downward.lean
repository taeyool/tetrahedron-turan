import LeanFlagAlgebras.Core.Algebra
import Mathlib.Data.Fintype.CardEmbedding

/-! # Core: the downward (unlabeling) operator — groundwork

Razborov's `⟦·⟧_σ : A^σ → A^∅` sends a σ-flag `F` to its unlabeling
weighted by the normalizing factor `q_σ(F)`: the probability that a
uniformly random injection of the label set into the vertices realizes a
flag isomorphic to `F`. This file builds the combinatorial layer: valid
labelings of an unlabeled host (`IsFlagLabeling`, `flagLabelings`,
`labelingCount`), their invariance under isomorphism in both slots,
positivity (the root embedding labels a flag's own unlabeling), the
factor `labelingFactor ∈ (0, 1]`, and the resulting linear map
`downwardVector` on flag vectors. The averaging identity that descends it
to the quotient algebras follows in a later slice. -/

namespace FlagAlgebras.Core

open Classical

variable {S : Signature} {T U U' V V' : Type}
variable {𝕋 : RelTheory S} {σ : Model S T}

section Labelings

variable [S.NullaryFree]

/-- `θ` realizes the σ-flag `F` on the unlabeled host `N`: it is an
induced embedding of the type whose resulting flag is isomorphic to `F`. -/
def IsFlagLabeling (N : LabeledFlag 𝕋 (emptyType S) V)
    (F : LabeledFlag 𝕋 σ U) (θ : T ↪ V) : Prop :=
  ∃ h : ∀ (r : S.Rel) (f : Fin (S.ar r) → T),
      N.toModel.interp r (⇑θ ∘ f) ↔ σ.interp r f,
    Nonempty ((⟨N.toModel, N.mem, ⟨θ, h⟩⟩ : LabeledFlag 𝕋 σ V) ≃ᶠ F)

/-- The labelings of `N` realizing `F`. -/
noncomputable def flagLabelings [Fintype T] [Fintype V]
    (N : LabeledFlag 𝕋 (emptyType S) V) (F : LabeledFlag 𝕋 σ U) :
    Finset (T ↪ V) :=
  Finset.univ.filter (IsFlagLabeling N F)

omit [S.NullaryFree] in
/-- Membership in the labeling set, stated without exposing the classical
`filter` instances. -/
lemma mem_flagLabelings [Fintype T] [Fintype V]
    {N : LabeledFlag 𝕋 (emptyType S) V} {F : LabeledFlag 𝕋 σ U}
    {θ : T ↪ V} :
    θ ∈ flagLabelings N F ↔ IsFlagLabeling N F θ := by
  unfold flagLabelings
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The number of labelings of `N` realizing `F`. -/
noncomputable def labelingCount [Fintype T] [Fintype V]
    (N : LabeledFlag 𝕋 (emptyType S) V) (F : LabeledFlag 𝕋 σ U) : ℕ :=
  (flagLabelings N F).card

omit [S.NullaryFree] in
/-- The labeling set depends only on the isomorphism class of the target
flag. -/
lemma flagLabelings_congr_flag [Fintype T] [Fintype V]
    (N : LabeledFlag 𝕋 (emptyType S) V) {F : LabeledFlag 𝕋 σ U}
    {F' : LabeledFlag 𝕋 σ U'} (e : F ≃ᶠ F') :
    flagLabelings N F = flagLabelings N F' := by
  ext θ
  rw [mem_flagLabelings, mem_flagLabelings]
  constructor
  · rintro ⟨h, ⟨i⟩⟩
    exact ⟨h, ⟨i.trans e⟩⟩
  · rintro ⟨h, ⟨i⟩⟩
    exact ⟨h, ⟨i.trans e.symm⟩⟩

omit [S.NullaryFree] in
lemma labelingCount_congr_flag [Fintype T] [Fintype V]
    (N : LabeledFlag 𝕋 (emptyType S) V) {F : LabeledFlag 𝕋 σ U}
    {F' : LabeledFlag 𝕋 σ U'} (e : F ≃ᶠ F') :
    labelingCount N F = labelingCount N F' := by
  unfold labelingCount
  rw [flagLabelings_congr_flag N e]

omit [S.NullaryFree] in
/-- The labeling count depends only on the isomorphism class of the host:
an isomorphism transports labelings bijectively. -/
lemma labelingCount_congr_host [Fintype T] [Fintype V] [Fintype V']
    {N : LabeledFlag 𝕋 (emptyType S) V} {N' : LabeledFlag 𝕋 (emptyType S) V'}
    (e : N ≃ᶠ N') (F : LabeledFlag 𝕋 σ U) :
    labelingCount N F = labelingCount N' F := by
  unfold labelingCount
  refine Finset.card_bij'
    (fun θ _ => θ.trans e.toIso.toEquiv.toEmbedding)
    (fun θ _ => θ.trans e.symm.toIso.toEquiv.toEmbedding) ?_ ?_ ?_ ?_
  · intro θ hθ
    obtain ⟨h, ⟨i⟩⟩ := mem_flagLabelings.mp hθ
    have h' : ∀ (r : S.Rel) (f : Fin (S.ar r) → T),
        N'.toModel.interp r (⇑(θ.trans e.toIso.toEquiv.toEmbedding) ∘ f)
          ↔ σ.interp r f := by
      intro r f
      rw [show ⇑(θ.trans e.toIso.toEquiv.toEmbedding) ∘ f
          = ⇑e.toIso.toEquiv ∘ (⇑θ ∘ f) from rfl,
        e.toIso.interp_iff]
      exact h r f
    have j : (⟨N'.toModel, N'.mem,
          ⟨θ.trans e.toIso.toEquiv.toEmbedding, h'⟩⟩ :
          LabeledFlag 𝕋 σ V') ≃ᶠ
        (⟨N.toModel, N.mem, ⟨θ, h⟩⟩ : LabeledFlag 𝕋 σ V) :=
      ⟨e.toIso.symm, fun t => e.toIso.toEquiv.symm_apply_apply _⟩
    exact mem_flagLabelings.mpr ⟨h', ⟨j.trans i⟩⟩
  · intro θ hθ
    obtain ⟨h, ⟨i⟩⟩ := mem_flagLabelings.mp hθ
    have h' : ∀ (r : S.Rel) (f : Fin (S.ar r) → T),
        N.toModel.interp r (⇑(θ.trans e.symm.toIso.toEquiv.toEmbedding) ∘ f)
          ↔ σ.interp r f := by
      intro r f
      rw [show ⇑(θ.trans e.symm.toIso.toEquiv.toEmbedding) ∘ f
          = ⇑e.symm.toIso.toEquiv ∘ (⇑θ ∘ f) from rfl,
        e.symm.toIso.interp_iff]
      exact h r f
    have j : (⟨N.toModel, N.mem,
          ⟨θ.trans e.symm.toIso.toEquiv.toEmbedding, h'⟩⟩ :
          LabeledFlag 𝕋 σ V) ≃ᶠ
        (⟨N'.toModel, N'.mem, ⟨θ, h⟩⟩ : LabeledFlag 𝕋 σ V') :=
      ⟨e.symm.toIso.symm, fun t => e.symm.toIso.toEquiv.symm_apply_apply _⟩
    exact mem_flagLabelings.mpr ⟨h', ⟨j.trans i⟩⟩
  · intro θ _
    dsimp only
    exact Function.Embedding.ext fun t =>
      e.toIso.toEquiv.symm_apply_apply _
  · intro θ _
    dsimp only
    exact Function.Embedding.ext fun t =>
      e.toIso.toEquiv.apply_symm_apply _

/-- The root embedding labels a flag's own unlabeling. -/
lemma isFlagLabeling_rootEmbed (F : LabeledFlag 𝕋 σ V) :
    IsFlagLabeling F.unlabel F F.rootEmbed.toEmbedding :=
  ⟨F.rootEmbed.interp_iff, ⟨LabeledFlagIso.refl F⟩⟩

lemma labelingCount_self_pos [Fintype T] [Fintype V]
    (F : LabeledFlag 𝕋 σ V) : 0 < labelingCount F.unlabel F :=
  Finset.card_pos.mpr ⟨F.rootEmbed.toEmbedding,
    mem_flagLabelings.mpr (isFlagLabeling_rootEmbed F)⟩

omit [S.NullaryFree] in
lemma labelingCount_le_card [Fintype T] [Fintype V]
    (N : LabeledFlag 𝕋 (emptyType S) V) (F : LabeledFlag 𝕋 σ U) :
    labelingCount N F ≤ Fintype.card (T ↪ V) := by
  rw [← Finset.card_univ]
  exact Finset.card_filter_le _ _

/-- Razborov's normalizing factor `q_σ`: the fraction of injections of the
label set into the host realizing `F`. -/
noncomputable def labelingFactor [Fintype T] [Fintype V]
    (N : LabeledFlag 𝕋 (emptyType S) V) (F : LabeledFlag 𝕋 σ U) : ℚ :=
  (labelingCount N F : ℚ) / (Fintype.card (T ↪ V) : ℚ)

omit [S.NullaryFree] in
lemma labelingFactor_nonneg [Fintype T] [Fintype V]
    (N : LabeledFlag 𝕋 (emptyType S) V) (F : LabeledFlag 𝕋 σ U) :
    0 ≤ labelingFactor N F :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

omit [S.NullaryFree] in
lemma labelingFactor_le_one [Fintype T] [Fintype V]
    (N : LabeledFlag 𝕋 (emptyType S) V) (F : LabeledFlag 𝕋 σ U) :
    labelingFactor N F ≤ 1 := by
  rw [labelingFactor]
  rcases Nat.eq_zero_or_pos (Fintype.card (T ↪ V)) with h | h
  · rw [h]
    simp
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast labelingCount_le_card N F

/-- A flag's own factor is positive: the root embedding witnesses it. -/
lemma labelingFactor_self_pos [Fintype T] [Fintype V]
    (F : LabeledFlag 𝕋 σ V) : 0 < labelingFactor F.unlabel F := by
  refine div_pos (by exact_mod_cast labelingCount_self_pos F) ?_
  have hne : Nonempty (T ↪ V) := ⟨F.rootEmbed.toEmbedding⟩
  exact_mod_cast Fintype.card_pos

omit [S.NullaryFree] in
/-- The factor depends only on the isomorphism classes of both slots. -/
lemma labelingFactor_congr [Fintype T] [Fintype V] [Fintype V']
    {N : LabeledFlag 𝕋 (emptyType S) V} {N' : LabeledFlag 𝕋 (emptyType S) V'}
    (eN : N ≃ᶠ N') {F : LabeledFlag 𝕋 σ U} {F' : LabeledFlag 𝕋 σ U'}
    (eF : F ≃ᶠ F') : labelingFactor N F = labelingFactor N' F' := by
  have hcard : Fintype.card V = Fintype.card V' :=
    Fintype.card_congr eN.toIso.toEquiv
  rw [labelingFactor, labelingFactor, labelingCount_congr_flag N eF,
    labelingCount_congr_host eN F',
    show Fintype.card (T ↪ V) = Fintype.card (T ↪ V') by
      rw [Fintype.card_embedding_eq, Fintype.card_embedding_eq, hcard]]

end Labelings

/-! ## The downward map on flag vectors -/

variable [S.NullaryFree] [Fintype T]

/-- The downward image of a size-tagged flag: its unlabeling, weighted by
the normalizing factor of a representative. -/
noncomputable def downwardFinFlag (F : FinFlag 𝕋 σ) :
    FlagVector 𝕋 (emptyType S) :=
  (labelingFactor (Quotient.out F.2).unlabel (Quotient.out F.2) : ℝ) •
    basisVector ⟨F.1, (Quotient.out F.2).unlabel.toFlag⟩

/-- The downward operator on flag vectors: the linear extension of
`downwardFinFlag`. -/
noncomputable def downwardVector :
    FlagVector 𝕋 σ → FlagVector 𝕋 (emptyType S) :=
  linearExtension downwardFinFlag

@[simp]
lemma downwardVector_basisVector (F : FinFlag 𝕋 σ) :
    downwardVector (basisVector F) = downwardFinFlag F :=
  linearExtension_basisVector _ F

lemma downwardVector_add (f g : FlagVector 𝕋 σ) :
    downwardVector (f + g) = downwardVector f + downwardVector g :=
  linearExtension_add _ f g

lemma downwardVector_smul (r : ℝ) (f : FlagVector 𝕋 σ) :
    downwardVector (r • f) = r • downwardVector f :=
  linearExtension_smul _ r f

lemma downwardVector_sub (f g : FlagVector 𝕋 σ) :
    downwardVector (f - g) = downwardVector f - downwardVector g :=
  linearExtension_sub _ f g

lemma downwardVector_sum {ι : Type} (s : Finset ι)
    (f : ι → FlagVector 𝕋 σ) :
    downwardVector (∑ i ∈ s, f i) = ∑ i ∈ s, downwardVector (f i) :=
  linearExtension_sum _ s f

/-! ## The averaging identity

Counting pairs (labeling, witness subset) two ways: grouped by the subset,
each witness of the unlabeling carries the labelings of `F` itself; grouped
by the labeling, the valid labelings partition into isomorphism classes and
each carries the witnesses of `F` in the labeled host. This is the
count-level content of the descent of `⟦·⟧_σ` to the quotient algebras. -/

section AveragingIdentity

omit [S.NullaryFree] [Fintype T] in
/-- Root-membership conditions are vacuous for empty-type flags. -/
lemma emptyType_root_mem (G : LabeledFlag 𝕋 (emptyType S) V)
    (W : Finset V) : ∀ t, G.rootEmbed.toEmbedding t ∈ W :=
  fun t => t.elim0

variable [Fintype U] [Fintype V]

/-- The pairs of a valid labeling and a witness subset counted by both
sides of the averaging identity. -/
private noncomputable def labelingPairs (F : LabeledFlag 𝕋 σ U)
    (G : LabeledFlag 𝕋 (emptyType S) V) : Finset ((T ↪ V) × Finset V) :=
  Finset.univ.filter fun p =>
    ∃ h : ∀ (r : S.Rel) (f : Fin (S.ar r) → T),
        G.toModel.interp r (⇑p.1 ∘ f) ↔ σ.interp r f,
      p.2 ∈ flagWitnesses F ⟨G.toModel, G.mem, ⟨p.1, h⟩⟩

omit [S.NullaryFree] in
private lemma mem_labelingPairs {F : LabeledFlag 𝕋 σ U}
    {G : LabeledFlag 𝕋 (emptyType S) V} {p : (T ↪ V) × Finset V} :
    p ∈ labelingPairs F G ↔
      ∃ h : ∀ (r : S.Rel) (f : Fin (S.ar r) → T),
          G.toModel.interp r (⇑p.1 ∘ f) ↔ σ.interp r f,
        p.2 ∈ flagWitnesses F ⟨G.toModel, G.mem, ⟨p.1, h⟩⟩ := by
  unfold labelingPairs
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

omit [S.NullaryFree] in
/-- Grouping the pairs by the labeling: valid labelings partition into
isomorphism classes, each carrying the witnesses of `F` in the labeled
host. -/
private lemma labelingPairs_card_eq_sum_classes (F : LabeledFlag 𝕋 σ U)
    (G : LabeledFlag 𝕋 (emptyType S) V) :
    (labelingPairs F G).card
      = ∑ F' : Flag 𝕋 σ V,
          labelingCount G (Quotient.out F') * flagCount F (Quotient.out F') := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := (Finset.univ : Finset (T ↪ V)))
    (fun p _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  rw [← Finset.sum_subset
    (Finset.subset_univ (Finset.univ.biUnion
      fun F' : Flag 𝕋 σ V => flagLabelings G (Quotient.out F'))) ?hvanish]
  case hvanish =>
    intro θ _ hθ
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro p hp
    obtain ⟨hmem, hfst⟩ := Finset.mem_filter.mp hp
    obtain ⟨h, hw⟩ := mem_labelingPairs.mp hmem
    refine hθ (Finset.mem_biUnion.mpr
      ⟨(⟨G.toModel, G.mem, ⟨p.1, h⟩⟩ : LabeledFlag 𝕋 σ V).toFlag,
        Finset.mem_univ _, ?_⟩)
    rw [← hfst]
    refine mem_flagLabelings.mpr ⟨h, ?_⟩
    obtain ⟨i⟩ := Quotient.exact (Quotient.out_eq
      (⟨G.toModel, G.mem, ⟨p.1, h⟩⟩ : LabeledFlag 𝕋 σ V).toFlag)
    exact ⟨i.symm⟩
  rw [Finset.sum_biUnion ?hdisj]
  case hdisj =>
    intro G₁ _ G₂ _ hne
    refine Finset.disjoint_left.mpr fun θ hθ₁ hθ₂ => hne ?_
    obtain ⟨h₁, ⟨i₁⟩⟩ := mem_flagLabelings.mp hθ₁
    obtain ⟨h₂, ⟨i₂⟩⟩ := mem_flagLabelings.mp hθ₂
    calc G₁ = Quotient.mk _ (Quotient.out G₁) := (Quotient.out_eq G₁).symm
      _ = Quotient.mk _ (Quotient.out G₂) :=
        Quotient.sound ⟨i₁.symm.trans i₂⟩
      _ = G₂ := Quotient.out_eq G₂
  refine Finset.sum_congr rfl fun F' _ => ?_
  have hconst : ∀ θ ∈ flagLabelings G (Quotient.out F'),
      ((labelingPairs F G).filter fun p => p.1 = θ).card
        = flagCount F (Quotient.out F') := by
    intro θ hθ
    obtain ⟨h, ⟨i⟩⟩ := mem_flagLabelings.mp hθ
    rw [← flagCount_congr_right F i]
    refine Finset.card_bij' (fun p _ => p.2) (fun W _ => (θ, W)) ?_ ?_ ?_ ?_
    · rintro ⟨p₁, p₂⟩ hp
      obtain ⟨hmem, hfst⟩ := Finset.mem_filter.mp hp
      obtain ⟨h', hw⟩ := mem_labelingPairs.mp hmem
      dsimp only at hfst ⊢
      subst hfst
      exact hw
    · intro W hW
      refine Finset.mem_filter.mpr
        ⟨mem_labelingPairs.mpr ⟨h, hW⟩, rfl⟩
    · rintro ⟨p₁, p₂⟩ hp
      obtain ⟨-, hfst⟩ := Finset.mem_filter.mp hp
      dsimp only at hfst ⊢
      rw [hfst]
    · intro W _
      rfl
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
  rfl

/-- Grouping the pairs by the subset: each witness of the unlabeling
carries the labelings of `F` in the restriction, which are the labelings of
`F` itself. -/
private lemma labelingPairs_card_eq_count_mul (F : LabeledFlag 𝕋 σ U)
    (G : LabeledFlag 𝕋 (emptyType S) V) :
    (labelingPairs F G).card
      = flagCount F.unlabel G * labelingCount F.unlabel F := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.snd) (t := flagWitnesses F.unlabel G) ?hmaps]
  case hmaps =>
    intro p hp
    obtain ⟨h, hw⟩ := mem_labelingPairs.mp (Finset.mem_coe.mp hp)
    obtain ⟨hin, hcard, ⟨i⟩⟩ := mem_flagWitnesses.mp hw
    refine Finset.mem_coe.mpr (mem_flagWitnesses.mpr
      ⟨emptyType_root_mem G p.2, hcard, ⟨?_⟩⟩)
    exact ⟨i.toIso, fun t => t.elim0⟩
  have hper : ∀ W ∈ flagWitnesses F.unlabel G,
      ((labelingPairs F G).filter fun p => p.2 = W).card
        = labelingCount F.unlabel F := by
    intro W hWmem
    obtain ⟨hroot₀, hcard₀, ⟨j⟩⟩ := mem_flagWitnesses.mp hWmem
    rw [← labelingCount_congr_host j F, ← labelingCount_congr_flag _
      (LabeledFlagIso.refl F)]
    refine Finset.card_bij'
      (fun p hp => Function.Embedding.codRestrict _ p.1
        (fun t => by
          obtain ⟨hmem, hsnd⟩ := Finset.mem_filter.mp hp
          obtain ⟨h, hw⟩ := mem_labelingPairs.mp hmem
          obtain ⟨hin, -, -⟩ := mem_flagWitnesses.mp hw
          rw [← hsnd]
          exact hin t))
      (fun θ' _ => (θ'.trans (Function.Embedding.subtype _), W)) ?_ ?_ ?_ ?_
    · rintro ⟨p₁, p₂⟩ hp
      obtain ⟨hmem, hsnd⟩ := Finset.mem_filter.mp hp
      obtain ⟨h, hw⟩ := mem_labelingPairs.mp hmem
      dsimp only at hsnd
      subst hsnd
      obtain ⟨hin, hcard, ⟨i⟩⟩ := mem_flagWitnesses.mp hw
      exact mem_flagLabelings.mpr ⟨fun r f => h r f, ⟨i⟩⟩
    · intro θ' hθ'
      obtain ⟨h', ⟨i'⟩⟩ := mem_flagLabelings.mp hθ'
      have h : ∀ (r : S.Rel) (f : Fin (S.ar r) → T),
          G.toModel.interp r
            (⇑(θ'.trans (Function.Embedding.subtype _)) ∘ f)
            ↔ σ.interp r f := fun r f => h' r f
      refine Finset.mem_filter.mpr
        ⟨mem_labelingPairs.mpr ⟨h, mem_flagWitnesses.mpr
          ⟨fun t => (θ' t).property, hcard₀, ⟨i'⟩⟩⟩, rfl⟩
    · rintro ⟨p₁, p₂⟩ hp
      obtain ⟨-, hsnd⟩ := Finset.mem_filter.mp hp
      dsimp only at hsnd ⊢
      rw [Prod.mk.injEq]
      exact ⟨Function.Embedding.ext fun t => rfl, hsnd.symm⟩
    · intro θ' _
      exact Function.Embedding.ext fun t => Subtype.ext rfl
  rw [Finset.sum_congr rfl hper, Finset.sum_const, smul_eq_mul]
  rfl

/-- **The averaging identity** at the level of counts: witnesses of the
unlabeling times self-labelings equal the class-wise labelings times
witnesses in the labeled hosts. -/
theorem flagCount_unlabel_mul_labelingCount (F : LabeledFlag 𝕋 σ U)
    (G : LabeledFlag 𝕋 (emptyType S) V) :
    flagCount F.unlabel G * labelingCount F.unlabel F
      = ∑ F' : Flag 𝕋 σ V,
          labelingCount G (Quotient.out F') * flagCount F (Quotient.out F') :=
  (labelingPairs_card_eq_count_mul F G).symm.trans
    (labelingPairs_card_eq_sum_classes F G)

end AveragingIdentity

/-! ## The rational descent

Dividing the averaging identity by the normalizers turns it into the
statement that the downward image of an averaging relation is a scalar
multiple of an averaging relation of the empty type, so `downwardVector`
maps `ZeroSpace` into `ZeroSpace` and descends to the quotient algebras:
Razborov's `⟦·⟧_σ : A^σ → A^∅`. -/

section Descent

/-- Choosing an `n`-subset and labeling inside it is labeling first and
completing: the normalizer identity behind the rational descent. -/
private lemma choose_mul_descFactorial {k n ℓ : ℕ} (hkn : k ≤ n)
    (hnl : n ≤ ℓ) :
    ℓ.choose n * n.descFactorial k
      = ℓ.descFactorial k * (ℓ - k).choose (n - k) := by
  have hK : 0 < (n - k).factorial * (ℓ - n).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_right hK
  have e1 := Nat.choose_mul_factorial_mul_factorial hnl
  have e2 := Nat.factorial_mul_descFactorial hkn
  have e3 := Nat.factorial_mul_descFactorial (le_trans hkn hnl)
  have e4 := Nat.choose_mul_factorial_mul_factorial
    (Nat.sub_le_sub_right hnl k)
  have hsub : ℓ - k - (n - k) = ℓ - n := by omega
  rw [hsub] at e4
  calc ℓ.choose n * n.descFactorial k *
        ((n - k).factorial * (ℓ - n).factorial)
      = ℓ.choose n * ((n - k).factorial * n.descFactorial k) *
        (ℓ - n).factorial := by ring
    _ = ℓ.choose n * n.factorial * (ℓ - n).factorial := by rw [e2]
    _ = ℓ.factorial := e1
    _ = (ℓ - k).factorial * ℓ.descFactorial k := e3.symm
    _ = ((ℓ - k).choose (n - k) * (n - k).factorial * (ℓ - n).factorial) *
        ℓ.descFactorial k := by rw [e4]
    _ = ℓ.descFactorial k * (ℓ - k).choose (n - k) *
        ((n - k).factorial * (ℓ - n).factorial) := by ring

omit [S.NullaryFree] in
/-- Subflag densities of classes are the labeled densities of their
canonical representatives. -/
lemma subflagDensity_out {U' V' : Type} [Fintype U'] [Fintype V']
    (A : Flag 𝕋 σ U') (B : Flag 𝕋 σ V') :
    subflagDensity A B = flagDensity (Quotient.out A) (Quotient.out B) := by
  conv_lhs => rw [← Quotient.out_eq A, ← Quotient.out_eq B]
  rfl

omit [S.NullaryFree] [Fintype T] in
private lemma subflagDensity_toFlag_out {𝕋' : RelTheory S} {T' U' V' : Type}
    [Fintype T'] {σ' : Model S T'} [Fintype U'] [Fintype V']
    (A : LabeledFlag 𝕋' σ' U') (B : Flag 𝕋' σ' V') :
    subflagDensity A.toFlag B = flagDensity A (Quotient.out B) := by
  conv_lhs => rw [← Quotient.out_eq B]
  rfl

omit [Fintype T] in
private lemma flag_out_unlabel {V' : Type} (F' : Flag 𝕋 σ V') :
    (Quotient.out F').unlabel.toFlag = Flag.unlabel F' := by
  conv_rhs => rw [← Quotient.out_eq F']
  rfl

/-- A nonzero labeling count forces the unlabeling class. -/
private lemma unlabel_eq_of_labelingCount_ne_zero {V' : Type} [Fintype V']
    {H : Flag 𝕋 (emptyType S) V'} {F' : Flag 𝕋 σ V'}
    (h : labelingCount (Quotient.out H) (Quotient.out F') ≠ 0) :
    Flag.unlabel F' = H := by
  obtain ⟨θ, hθ⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  obtain ⟨hval, ⟨i⟩⟩ := mem_flagLabelings.mp hθ
  have j : Quotient.out H ≃ᶠ (Quotient.out F').unlabel :=
    ⟨i.toIso, fun t => t.elim0⟩
  calc Flag.unlabel F'
      = (Quotient.out F').unlabel.toFlag := (flag_out_unlabel F').symm
    _ = (Quotient.out H).toFlag := Quotient.sound ⟨j.symm⟩
    _ = H := Quotient.out_eq H

/-- On the unlabeling fiber, labelings of the class representative are
labelings of the flag's own unlabeling. -/
private lemma labelingCount_out_eq {V' : Type} [Fintype V']
    {H : Flag 𝕋 (emptyType S) V'} {F' : Flag 𝕋 σ V'}
    (h : Flag.unlabel F' = H) :
    labelingCount (Quotient.out H) (Quotient.out F')
      = labelingCount (Quotient.out F').unlabel (Quotient.out F') := by
  have hq : (⟦Quotient.out H⟧ : Flag 𝕋 (emptyType S) V')
      = ⟦(Quotient.out F').unlabel⟧ := by
    rw [Quotient.out_eq, ← h, ← flag_out_unlabel]
    rfl
  obtain ⟨j⟩ := Quotient.exact hq
  exact labelingCount_congr_host j _

/-- The coefficient identity of the descent: on each unlabeling fiber, the
expansion coefficients recombine into the factor times the empty-type
density. -/
private lemma downward_coeff (F : FinFlag 𝕋 σ) {ℓ : ℕ} (hℓ : F.1 ≤ ℓ)
    (H : FlagWithSize 𝕋 (emptyType S) ℓ) :
    ∑ F' ∈ Finset.univ.filter
        (fun F' : FlagWithSize 𝕋 σ ℓ => Flag.unlabel F' = H),
        subflagDensity F.2 F' *
          labelingFactor (Quotient.out F').unlabel (Quotient.out F')
      = labelingFactor (Quotient.out F.2).unlabel (Quotient.out F.2) *
          subflagDensity (Quotient.out F.2).unlabel.toFlag H := by
  classical
  have hk : Fintype.card T ≤ F.1 := finFlag_size_ge F
  have hcount :
      (∑ F' ∈ Finset.univ.filter
          (fun F' : FlagWithSize 𝕋 σ ℓ => Flag.unlabel F' = H),
        flagCount (Quotient.out F.2) (Quotient.out F') *
          labelingCount (Quotient.out F').unlabel (Quotient.out F'))
      = flagCount (Quotient.out F.2).unlabel (Quotient.out H) *
          labelingCount (Quotient.out F.2).unlabel (Quotient.out F.2) := by
    rw [Finset.sum_congr rfl fun F' hF' => by
      rw [← labelingCount_out_eq (Finset.mem_filter.mp hF').2, mul_comm]]
    rw [Finset.sum_subset
      (Finset.filter_subset _ _)
      (fun F' _ hF' => by
        have hz : labelingCount (Quotient.out H) (Quotient.out F') = 0 := by
          by_contra hne
          exact (Finset.mem_filter.mp
            (Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, unlabel_eq_of_labelingCount_ne_zero hne⟩)
            |> fun h => hF' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2⟩))
        rw [hz, zero_mul])]
    exact (flagCount_unlabel_mul_labelingCount (Quotient.out F.2)
      (Quotient.out H)).symm
  have c1 : (((ℓ - Fintype.card T).choose (F.1 - Fintype.card T) : ℕ) : ℚ)
      ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have c2 : ((ℓ.descFactorial (Fintype.card T) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega)).ne'
  have c3 : ((F.1.descFactorial (Fintype.card T) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hk).ne'
  have c4 : ((ℓ.choose F.1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hℓ).ne'
  have keyN := choose_mul_descFactorial hk hℓ
  have keyQ : ((ℓ.choose F.1 : ℕ) : ℚ) *
        ((F.1.descFactorial (Fintype.card T) : ℕ) : ℚ)
      = ((ℓ.descFactorial (Fintype.card T) : ℕ) : ℚ) *
        (((ℓ - Fintype.card T).choose (F.1 - Fintype.card T) : ℕ) : ℚ) := by
    exact_mod_cast keyN
  have hsummand : ∀ F' : FlagWithSize 𝕋 σ ℓ,
      subflagDensity F.2 F' *
          labelingFactor (Quotient.out F').unlabel (Quotient.out F')
        = ((flagCount (Quotient.out F.2) (Quotient.out F') : ℚ) *
            (labelingCount (Quotient.out F').unlabel (Quotient.out F') : ℚ)) /
          ((((ℓ - Fintype.card T).choose (F.1 - Fintype.card T) : ℕ) : ℚ) *
            ((ℓ.descFactorial (Fintype.card T) : ℕ) : ℚ)) := by
    intro F'
    rw [subflagDensity_out, flagDensity, labelingFactor,
      Fintype.card_embedding_eq]
    simp only [Fintype.card_fin]
    rw [div_mul_div_comm]
  have hrhs :
      labelingFactor (Quotient.out F.2).unlabel (Quotient.out F.2) *
          subflagDensity (Quotient.out F.2).unlabel.toFlag H
        = ((labelingCount (Quotient.out F.2).unlabel (Quotient.out F.2) : ℚ) *
            (flagCount (Quotient.out F.2).unlabel (Quotient.out H) : ℚ)) /
          (((F.1.descFactorial (Fintype.card T) : ℕ) : ℚ) *
            ((ℓ.choose F.1 : ℕ) : ℚ)) := by
    rw [subflagDensity_toFlag_out, flagDensity, labelingFactor,
      Fintype.card_embedding_eq]
    simp only [Fintype.card_fin, Nat.sub_zero]
    rw [div_mul_div_comm]
  rw [Finset.sum_congr rfl fun F' _ => hsummand F', ← Finset.sum_div, hrhs]
  rw [div_eq_div_iff (mul_ne_zero c1 c2) (mul_ne_zero c3 c4)]
  have hcountQ :
      (∑ F' ∈ Finset.univ.filter
          (fun F' : FlagWithSize 𝕋 σ ℓ => Flag.unlabel F' = H),
        (flagCount (Quotient.out F.2) (Quotient.out F') : ℚ) *
          (labelingCount (Quotient.out F').unlabel (Quotient.out F') : ℚ))
      = (flagCount (Quotient.out F.2).unlabel (Quotient.out H) : ℚ) *
          (labelingCount (Quotient.out F.2).unlabel (Quotient.out F.2) : ℚ) := by
    exact_mod_cast hcount
  rw [hcountQ]
  linear_combination (flagCount (Quotient.out F.2).unlabel (Quotient.out H) : ℚ) *
    (labelingCount (Quotient.out F.2).unlabel (Quotient.out F.2) : ℚ) * keyQ

/-- The downward image of the density expansion is the factor times the
empty-type expansion of the unlabeling. -/
private lemma sum_downward_expansion (F : FinFlag 𝕋 σ) {ℓ : ℕ}
    (hℓ : F.1 ≤ ℓ) :
    ∑ F' : FlagWithSize 𝕋 σ ℓ,
        (subflagDensity F.2 F' : ℝ) • downwardFinFlag ⟨ℓ, F'⟩
      = (labelingFactor (Quotient.out F.2).unlabel (Quotient.out F.2) : ℝ) •
          flagExpansion
            (⟨F.1, (Quotient.out F.2).unlabel.toFlag⟩ :
              FinFlag 𝕋 (emptyType S)) ℓ := by
  classical
  rw [flagExpansion, Finset.smul_sum,
    Finset.sum_congr rfl fun H _ => smul_smul _ _ _]
  rw [Finset.sum_congr rfl fun F' _ => by
    rw [show downwardFinFlag (⟨ℓ, F'⟩ : FinFlag 𝕋 σ)
        = (labelingFactor (Quotient.out F').unlabel (Quotient.out F') : ℝ) •
          basisVector ⟨ℓ, (Quotient.out F').unlabel.toFlag⟩ from rfl,
      smul_smul]]
  rw [← Finset.sum_fiberwise Finset.univ
    (fun F' : FlagWithSize 𝕋 σ ℓ => Flag.unlabel F')
    (fun F' =>
      (((subflagDensity F.2 F' : ℚ) : ℝ) *
          ((labelingFactor (Quotient.out F').unlabel (Quotient.out F') : ℚ) : ℝ)) •
        basisVector ⟨ℓ, (Quotient.out F').unlabel.toFlag⟩)]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [Finset.sum_congr rfl fun F' hF' => by
    rw [show (⟨ℓ, (Quotient.out F').unlabel.toFlag⟩ :
        FinFlag 𝕋 (emptyType S)) = ⟨ℓ, H⟩ by
      rw [flag_out_unlabel, (Finset.mem_filter.mp hF').2]]]
  rw [← Finset.sum_smul]
  congr 1
  exact_mod_cast downward_coeff F hℓ H

/-- The downward image of an averaging relation is a scalar multiple of an
averaging relation: the heart of the descent. -/
theorem downwardVector_zeroElement_mem (F : FinFlag 𝕋 σ) {ℓ : ℕ}
    (hℓ : F.1 ≤ ℓ) :
    downwardVector (zeroElement F ℓ) ∈ ZeroSpace 𝕋 (emptyType S) := by
  have key : downwardVector (zeroElement F ℓ)
      = (labelingFactor (Quotient.out F.2).unlabel (Quotient.out F.2) : ℝ) •
          zeroElement
            (⟨F.1, (Quotient.out F.2).unlabel.toFlag⟩ :
              FinFlag 𝕋 (emptyType S)) ℓ := by
    rw [zeroElement, downwardVector_sub, downwardVector_basisVector,
      flagExpansion, downwardVector_sum,
      Finset.sum_congr rfl fun F' _ => by
        rw [downwardVector_smul, downwardVector_basisVector],
      sum_downward_expansion F hℓ, zeroElement, smul_sub]
    rfl
  rw [key]
  exact zeroSpace_closed_under_smul _ _ (zeroElement_in_zeroSpace hℓ)

/-- `downwardVector` maps the relation space into the relation space. -/
theorem downwardVector_zeroSpace {f : FlagVector 𝕋 σ}
    (hf : f ∈ ZeroSpace 𝕋 σ) :
    downwardVector f ∈ ZeroSpace 𝕋 (emptyType S) := by
  rcases zeroSpace_eq_sum_spanElement f hf with ⟨I, hI, c, v, hv, hsum⟩
  haveI := hI
  rw [hsum, downwardVector_sum]
  refine zeroSpace_closed_under_sum _ _ fun i _ => ?_
  rw [downwardVector_smul]
  refine zeroSpace_closed_under_smul _ _ ?_
  obtain ⟨G, ℓ, hℓ, hvi⟩ := mem_zeroSet.mp (hv i)
  rw [hvi]
  exact downwardVector_zeroElement_mem G hℓ

/-- **Razborov's unlabeling operator** `⟦·⟧_σ : A^σ → A^∅`, descended to
the quotient algebras. -/
noncomputable def downward :
    FlagAlgebra 𝕋 σ → FlagAlgebra 𝕋 (emptyType S) :=
  Quotient.map downwardVector fun f g hfg => by
    show downwardVector f - downwardVector g ∈ ZeroSpace 𝕋 (emptyType S)
    rw [← downwardVector_sub]
    exact downwardVector_zeroSpace hfg

@[simp]
theorem downward_quot (f : FlagVector 𝕋 σ) :
    downward (⟦f⟧ : FlagAlgebra 𝕋 σ) = ⟦downwardVector f⟧ :=
  rfl

theorem downward_add (x y : FlagAlgebra 𝕋 σ) :
    downward (x + y) = downward x + downward y := by
  rw [← Quotient.out_eq x, ← Quotient.out_eq y, ← add_quot, downward_quot,
    downward_quot, downward_quot, downwardVector_add, add_quot]

theorem downward_smul (r : ℝ) (x : FlagAlgebra 𝕋 σ) :
    downward (r • x) = r • downward x := by
  rw [← Quotient.out_eq x, ← smul_quot, downward_quot, downward_quot,
    downwardVector_smul, smul_quot]

theorem downward_zero :
    downward (0 : FlagAlgebra 𝕋 σ) = 0 := by
  show downward (⟦0⟧ : FlagAlgebra 𝕋 σ) = (⟦0⟧ : FlagAlgebra 𝕋 (emptyType S))
  rw [downward_quot]
  exact congrArg _ (linearExtension_zero _)

theorem downward_neg [𝕋.IsType σ] [𝕋.IsType (emptyType S)]
    (x : FlagAlgebra 𝕋 σ) : downward (-x) = -downward x := by
  rw [← neg_one_smul ℝ x, downward_smul, neg_one_smul]

theorem downward_sub [𝕋.IsType σ] [𝕋.IsType (emptyType S)]
    (x y : FlagAlgebra 𝕋 σ) :
    downward (x - y) = downward x - downward y := by
  rw [sub_eq_add_neg, downward_add, downward_neg, ← sub_eq_add_neg]

theorem downward_sum [𝕋.IsType σ] [𝕋.IsType (emptyType S)] {ι : Type}
    (s : Finset ι) (f : ι → FlagAlgebra 𝕋 σ) :
    downward (∑ i ∈ s, f i) = ∑ i ∈ s, downward (f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, downward_zero]
  | insert i s his ih =>
    rw [Finset.sum_insert his, Finset.sum_insert his, downward_add, ih]

/-- The downward image of a single flag: the normalizing factor times its
unlabeling. -/
theorem downward_basis (F : FinFlag 𝕋 σ) :
    downward (⟦basisVector F⟧ : FlagAlgebra 𝕋 σ)
      = (labelingFactor (Quotient.out F.2).unlabel (Quotient.out F.2) : ℝ) •
        (⟦basisVector ⟨F.1, (Quotient.out F.2).unlabel.toFlag⟩⟧ :
          FlagAlgebra 𝕋 (emptyType S)) := by
  rw [downward_quot, downwardVector_basisVector,
    show downwardFinFlag F
        = (labelingFactor (Quotient.out F.2).unlabel (Quotient.out F.2) : ℝ) •
          basisVector ⟨F.1, (Quotient.out F.2).unlabel.toFlag⟩ from rfl,
    smul_quot]

omit [Fintype T] in
/-- The unlabeling of the chosen representative is the unlabeling of the
class. -/
theorem out_unlabel_toFlag_eq (X : Flag 𝕋 σ V) :
    (Quotient.out X).unlabel.toFlag = Flag.unlabel X := by
  conv_rhs => rw [← Quotient.out_eq X]
  rfl

/-- The downward image of a single flag, with the unlabeling stated at the
class level. -/
theorem downward_basis' (F : FinFlag 𝕋 σ) :
    downward (⟦basisVector F⟧ : FlagAlgebra 𝕋 σ)
      = (labelingFactor (Quotient.out F.2).unlabel (Quotient.out F.2) : ℝ) •
        (⟦basisVector ⟨F.1, Flag.unlabel F.2⟩⟧ :
          FlagAlgebra 𝕋 (emptyType S)) := by
  rw [downward_basis, out_unlabel_toFlag_eq]

/-- Regroup a weighted sum of downward basis images over the unlabeled
classes: the coefficient of an unlabeled class collects the weighted
labeling factors of its typed fiber. -/
theorem sum_smul_downward_basis_regroup [𝕋.IsType σ]
    [𝕋.IsType (emptyType S)] {ℓ : ℕ} (w : FlagWithSize 𝕋 σ ℓ → ℝ) :
    ∑ X : FlagWithSize 𝕋 σ ℓ, w X • downward ⟦basisVector ⟨ℓ, X⟩⟧
      = ∑ H : FlagWithSize 𝕋 (emptyType S) ℓ,
          (∑ X ∈ Finset.univ.filter
              (fun X : FlagWithSize 𝕋 σ ℓ => Flag.unlabel X = H),
            w X * (labelingFactor (Quotient.out X).unlabel
              (Quotient.out X) : ℝ))
            • ⟦basisVector ⟨ℓ, H⟩⟧ := by
  classical
  rw [Finset.sum_congr rfl fun X _ => by
    rw [downward_basis', smul_smul]]
  rw [← Finset.sum_fiberwise Finset.univ
    (fun X : FlagWithSize 𝕋 σ ℓ => Flag.unlabel X)
    (fun X => (w X * (labelingFactor (Quotient.out X).unlabel
      (Quotient.out X) : ℝ)) • ⟦basisVector ⟨ℓ, Flag.unlabel X⟩⟧)]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun X hX => ?_
  rw [(Finset.mem_filter.mp hX).2]

/-- The downward image of a product of flags: the pair-density expansion
at any admissible level, pushed through the averaging operator. This is
the shape of the product tables of semidefinite certificates. -/
theorem downward_basisVector_mul [𝕋.IsType σ] [𝕋.IsType (emptyType S)]
    {m₁ m₂ ℓ : ℕ} (F₁ : FlagWithSize 𝕋 σ m₁) (F₂ : FlagWithSize 𝕋 σ m₂)
    (hℓ : m₁ + m₂ ≤ ℓ + Fintype.card T) :
    downward ((⟦basisVector ⟨m₁, F₁⟩⟧ : FlagAlgebra 𝕋 σ)
        * ⟦basisVector ⟨m₂, F₂⟩⟧)
      = ∑ H : FlagWithSize 𝕋 σ ℓ,
          ((subflagPairDensity F₁ F₂ H : ℚ) : ℝ)
            • downward ⟦basisVector ⟨ℓ, H⟩⟧ := by
  rw [basisVector_quot_mul_eq_flagMulWithSize_quot
      (⟨m₁, F₁⟩ : FinFlag 𝕋 σ) (⟨m₂, F₂⟩ : FinFlag 𝕋 σ) ℓ
      (by simpa using hℓ),
    show flagMulWithSize (⟨m₁, F₁⟩ : FinFlag 𝕋 σ) ⟨m₂, F₂⟩ ℓ
        = ∑ H : FlagWithSize 𝕋 σ ℓ,
          ((subflagPairDensity F₁ F₂ H : ℚ) : ℝ) • basisVector ⟨ℓ, H⟩
      from rfl,
    sum_quot,
    Finset.sum_congr rfl fun H _ => smul_quot _ _,
    downward_sum]
  exact Finset.sum_congr rfl fun H _ => downward_smul _ _

end Descent

end FlagAlgebras.Core
