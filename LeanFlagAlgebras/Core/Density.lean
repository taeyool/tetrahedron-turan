import LeanFlagAlgebras.Core.Flag
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! # Core: subflag densities

Razborov's key quantity `p(F, G)` (Definition 1, `t = 1`), theory-generically:
choose an `|F|`-element vertex subset of `G` containing the roots, uniformly
at random, and ask that the induced sub-flag be isomorphic to `F`.

`flagCount` counts the witnessing subsets, `flagDensity` normalizes by
`(|G| − |σ|).choose (|F| − |σ|)`, matching the `SimpleGraph`-based
`labeledGraphCount`/`labeledGraphDensity`. Basic facts proved here:
the count is bounded by the normalizer (`flagCount_le_choose`), densities lie
in `[0, 1]`, and the count depends only on the isomorphism class of the
pattern flag (`flagCount_congr_left`). Invariance in the host flag and the
descent to `Flag` quotients follow in a later slice, together with the chain
rule (Lemma 2.2). -/

namespace FlagAlgebras.Core

open Classical

variable {S : Signature} {T U U' V V' : Type}
variable {𝕋 : RelTheory S} {σ : Model S T}

/-- The number of vertices of a flag. -/
noncomputable def LabeledFlag.size [Fintype V] (_ : LabeledFlag 𝕋 σ V) : ℕ :=
  Fintype.card V

/-- The roots of a flag, as a `Finset`. -/
noncomputable def LabeledFlag.rootFinset [Fintype T] [Fintype V]
    (G : LabeledFlag 𝕋 σ V) : Finset V :=
  Finset.univ.map G.rootEmbed.toEmbedding

lemma LabeledFlag.card_rootFinset [Fintype T] [Fintype V]
    (G : LabeledFlag 𝕋 σ V) : G.rootFinset.card = Fintype.card T := by
  rw [LabeledFlag.rootFinset, Finset.card_map, Finset.card_univ]

lemma LabeledFlag.rootFinset_subset [Fintype T] [Fintype V]
    {G : LabeledFlag 𝕋 σ V} {W : Finset V}
    (hW : ∀ t, G.rootEmbed.toEmbedding t ∈ W) : G.rootFinset ⊆ W := by
  intro x hx
  obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hx
  exact hW t

/-- The subsets of `G`'s vertices witnessing an induced copy of the pattern
flag `F`: they contain all roots, have the size of `F`, and induce a flag
isomorphic to `F`. -/
noncomputable def flagWitnesses [Fintype T] [Fintype U] [Fintype V]
    (F : LabeledFlag 𝕋 σ U) (G : LabeledFlag 𝕋 σ V) : Finset (Finset V) :=
  Finset.univ.filter fun W =>
    ∃ hW : ∀ t, G.rootEmbed.toEmbedding t ∈ W,
      W.card = Fintype.card U ∧ Nonempty (G.restrict W hW ≃ᶠ F)

/-- Membership in the witness set, stated without exposing the classical
`filter` instances (which differ between elaboration sites). -/
lemma mem_flagWitnesses [Fintype T] [Fintype U] [Fintype V]
    {F : LabeledFlag 𝕋 σ U} {G : LabeledFlag 𝕋 σ V} {W : Finset V} :
    W ∈ flagWitnesses F G ↔
      ∃ hW : ∀ t, G.rootEmbed.toEmbedding t ∈ W,
        W.card = Fintype.card U ∧ Nonempty (G.restrict W hW ≃ᶠ F) := by
  unfold flagWitnesses
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The unnormalized subflag count: the number of vertex subsets of `G`
inducing a copy of `F`. -/
noncomputable def flagCount [Fintype T] [Fintype U] [Fintype V]
    (F : LabeledFlag 𝕋 σ U) (G : LabeledFlag 𝕋 σ V) : ℕ :=
  (flagWitnesses F G).card

/-- The subflag count is bounded by the number of size-`|F|` vertex subsets
containing the roots. -/
lemma flagCount_le_choose [Fintype T] [Fintype U] [Fintype V]
    (F : LabeledFlag 𝕋 σ U) (G : LabeledFlag 𝕋 σ V) :
    flagCount F G ≤
      (Fintype.card V - Fintype.card T).choose
        (Fintype.card U - Fintype.card T) := by
  classical
  set R := G.rootFinset with hR
  have hcard :
      ((Finset.univ \ R).powersetCard
        (Fintype.card U - Fintype.card T)).card =
      (Fintype.card V - Fintype.card T).choose
        (Fintype.card U - Fintype.card T) := by
    rw [Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, G.card_rootFinset]
  rw [flagCount, ← hcard]
  refine Finset.card_le_card_of_injOn (fun W => W \ R) ?_ ?_
  · intro W hW
    obtain ⟨hroot, hcardW, -⟩ :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hW)).2
    have hRW : R ⊆ W := LabeledFlag.rootFinset_subset hroot
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    constructor
    · exact Finset.sdiff_subset_sdiff (Finset.subset_univ W) subset_rfl
    · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hRW, hcardW,
        G.card_rootFinset]
  · intro W₁ h₁ W₂ h₂ heq
    obtain ⟨hroot₁, -, -⟩ :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp h₁)).2
    obtain ⟨hroot₂, -, -⟩ :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp h₂)).2
    have hR₁ : R ⊆ W₁ := LabeledFlag.rootFinset_subset hroot₁
    have hR₂ : R ⊆ W₂ := LabeledFlag.rootFinset_subset hroot₂
    have := congrArg (· ∪ R) heq
    simpa [Finset.sdiff_union_of_subset hR₁,
      Finset.sdiff_union_of_subset hR₂] using this

/-- The subflag density `p(F, G)`: the probability that a uniformly random
size-`|F|` vertex subset of `G` containing the roots induces a copy of
`F`. -/
noncomputable def flagDensity [Fintype T] [Fintype U] [Fintype V]
    (F : LabeledFlag 𝕋 σ U) (G : LabeledFlag 𝕋 σ V) : ℚ :=
  (flagCount F G : ℚ) /
    ((Fintype.card V - Fintype.card T).choose
      (Fintype.card U - Fintype.card T) : ℚ)

lemma flagDensity_nonneg [Fintype T] [Fintype U] [Fintype V]
    (F : LabeledFlag 𝕋 σ U) (G : LabeledFlag 𝕋 σ V) :
    0 ≤ flagDensity F G :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma flagDensity_le_one [Fintype T] [Fintype U] [Fintype V]
    (F : LabeledFlag 𝕋 σ U) (G : LabeledFlag 𝕋 σ V) :
    flagDensity F G ≤ 1 := by
  rw [flagDensity]
  rcases Nat.eq_zero_or_pos
      ((Fintype.card V - Fintype.card T).choose
        (Fintype.card U - Fintype.card T)) with h | h
  · rw [h]
    simp
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast flagCount_le_choose F G

/-- The witness set depends only on the isomorphism class of the pattern
flag (as a set of subsets of the host; the pattern only enters through the
induced-copy condition). -/
lemma flagWitnesses_congr_left [Fintype T] [Fintype U] [Fintype U'] [Fintype V]
    {F : LabeledFlag 𝕋 σ U} {F' : LabeledFlag 𝕋 σ U'} (e : F ≃ᶠ F')
    (G : LabeledFlag 𝕋 σ V) : flagWitnesses F G = flagWitnesses F' G := by
  have hcardU : Fintype.card U = Fintype.card U' :=
    Fintype.card_congr e.toIso.toEquiv
  ext W
  rw [mem_flagWitnesses, mem_flagWitnesses]
  constructor
  · rintro ⟨hW, hcard, ⟨i⟩⟩
    exact ⟨hW, hcardU ▸ hcard, ⟨i.trans e⟩⟩
  · rintro ⟨hW, hcard, ⟨i⟩⟩
    exact ⟨hW, hcardU ▸ hcard, ⟨i.trans e.symm⟩⟩

/-- The subflag count depends only on the isomorphism class of the pattern
flag. -/
lemma flagCount_congr_left [Fintype T] [Fintype U] [Fintype U'] [Fintype V]
    {F : LabeledFlag 𝕋 σ U} {F' : LabeledFlag 𝕋 σ U'} (e : F ≃ᶠ F')
    (G : LabeledFlag 𝕋 σ V) : flagCount F G = flagCount F' G := by
  have hcardU : Fintype.card U = Fintype.card U' :=
    Fintype.card_congr e.toIso.toEquiv
  unfold flagCount flagWitnesses
  congr 1
  apply Finset.filter_congr
  intro W _
  constructor
  · rintro ⟨hW, hcard, ⟨i⟩⟩
    exact ⟨hW, hcardU ▸ hcard, ⟨i.trans e⟩⟩
  · rintro ⟨hW, hcard, ⟨i⟩⟩
    exact ⟨hW, hcardU ▸ hcard, ⟨i.trans e.symm⟩⟩

/-- The subflag density depends only on the isomorphism class of the pattern
flag. -/
lemma flagDensity_congr_left [Fintype T] [Fintype U] [Fintype U'] [Fintype V]
    {F : LabeledFlag 𝕋 σ U} {F' : LabeledFlag 𝕋 σ U'} (e : F ≃ᶠ F')
    (G : LabeledFlag 𝕋 σ V) : flagDensity F G = flagDensity F' G := by
  have hcardU : Fintype.card U = Fintype.card U' :=
    Fintype.card_congr e.toIso.toEquiv
  rw [flagDensity, flagDensity, flagCount_congr_left e G, hcardU]

/-- A flag isomorphism carries the root set onto the root set. -/
lemma LabeledFlagIso.rootFinset_map [Fintype T] [Fintype V] [Fintype V']
    {G : LabeledFlag 𝕋 σ V} {G' : LabeledFlag 𝕋 σ V'} (e : G ≃ᶠ G') :
    G.rootFinset.map e.toIso.toEquiv.toEmbedding = G'.rootFinset := by
  rw [LabeledFlag.rootFinset, LabeledFlag.rootFinset, Finset.map_map]
  congr 1
  exact Function.Embedding.ext fun t => e.root_preserve t

/-- A host isomorphism carries witnessing subsets to witnessing subsets. -/
lemma LabeledFlagIso.mem_flagWitnesses_map [Fintype T] [Fintype U] [Fintype V]
    [Fintype V'] {G : LabeledFlag 𝕋 σ V} {G' : LabeledFlag 𝕋 σ V'}
    (e : G ≃ᶠ G') {F : LabeledFlag 𝕋 σ U} {W : Finset V}
    (hW : W ∈ flagWitnesses F G) :
    W.map e.toIso.toEquiv.toEmbedding ∈ flagWitnesses F G' := by
  obtain ⟨hroot, hcard, ⟨i⟩⟩ := mem_flagWitnesses.mp hW
  exact mem_flagWitnesses.mpr ⟨e.root_mem_map hroot,
    by rw [Finset.card_map]; exact hcard,
    ⟨(e.restrictMap W hroot).symm.trans i⟩⟩

/-- The subflag count depends only on the isomorphism class of the host flag:
an isomorphism transports witnessing subsets bijectively. -/
lemma flagCount_congr_right [Fintype T] [Fintype U] [Fintype V] [Fintype V']
    (F : LabeledFlag 𝕋 σ U) {G : LabeledFlag 𝕋 σ V} {G' : LabeledFlag 𝕋 σ V'}
    (e : G ≃ᶠ G') : flagCount F G = flagCount F G' := by
  unfold flagCount flagWitnesses
  refine Finset.card_bij'
    (fun A _ => A.map e.toIso.toEquiv.toEmbedding)
    (fun B _ => B.map e.symm.toIso.toEquiv.toEmbedding) ?_ ?_ ?_ ?_
  · intro A hA
    obtain ⟨hroot, hcard, ⟨i⟩⟩ := (Finset.mem_filter.mp hA).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.root_mem_map hroot,
      by rw [Finset.card_map]; exact hcard,
      ⟨(e.restrictMap A hroot).symm.trans i⟩⟩
  · intro B hB
    obtain ⟨hroot, hcard, ⟨i⟩⟩ := (Finset.mem_filter.mp hB).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.symm.root_mem_map hroot,
      by rw [Finset.card_map]; exact hcard,
      ⟨(e.symm.restrictMap B hroot).symm.trans i⟩⟩
  · intro A _
    dsimp only
    rw [Finset.map_map,
      show e.toIso.toEquiv.toEmbedding.trans e.symm.toIso.toEquiv.toEmbedding
          = Function.Embedding.refl V from
        Function.Embedding.ext fun a => e.toIso.toEquiv.symm_apply_apply a,
      Finset.map_refl]
  · intro B _
    dsimp only
    rw [Finset.map_map,
      show e.symm.toIso.toEquiv.toEmbedding.trans e.toIso.toEquiv.toEmbedding
          = Function.Embedding.refl V' from
        Function.Embedding.ext fun a => e.toIso.toEquiv.apply_symm_apply a,
      Finset.map_refl]

/-- The subflag density depends only on the isomorphism class of the host
flag. -/
lemma flagDensity_congr_right [Fintype T] [Fintype U] [Fintype V] [Fintype V']
    (F : LabeledFlag 𝕋 σ U) {G : LabeledFlag 𝕋 σ V} {G' : LabeledFlag 𝕋 σ V'}
    (e : G ≃ᶠ G') : flagDensity F G = flagDensity F G' := by
  have hcardV : Fintype.card V = Fintype.card V' :=
    Fintype.card_congr e.toIso.toEquiv
  rw [flagDensity, flagDensity, flagCount_congr_right F e, hcardV]

/-- Subflag density on isomorphism classes: the descent of `flagDensity` to
the `Flag` quotients, Razborov's `p(F, G)` as a function of flags. -/
noncomputable def subflagDensity [Fintype T] [Fintype U] [Fintype V] :
    Flag 𝕋 σ U → Flag 𝕋 σ V → ℚ :=
  Quotient.lift₂ flagDensity fun _ _ _ _ hF hG => by
    obtain ⟨eF⟩ := hF
    obtain ⟨eG⟩ := hG
    rw [flagDensity_congr_left eF, flagDensity_congr_right _ eG]

@[simp]
lemma subflagDensity_mk [Fintype T] [Fintype U] [Fintype V]
    (F : LabeledFlag 𝕋 σ U) (G : LabeledFlag 𝕋 σ V) :
    subflagDensity F.toFlag G.toFlag = flagDensity F G :=
  rfl

lemma subflagDensity_nonneg [Fintype T] [Fintype U] [Fintype V]
    (F : Flag 𝕋 σ U) (G : Flag 𝕋 σ V) : 0 ≤ subflagDensity F G :=
  Quotient.inductionOn₂ F G fun F G => flagDensity_nonneg F G

lemma subflagDensity_le_one [Fintype T] [Fintype U] [Fintype V]
    (F : Flag 𝕋 σ U) (G : Flag 𝕋 σ V) : subflagDensity F G ≤ 1 :=
  Quotient.inductionOn₂ F G fun F G => flagDensity_le_one F G

/-! ## The unit flag and same-size hosts

The unit flag `1_σ` has exactly one witness in any host (the root set), so its
density is `1`; in a host of the pattern's size the only candidate witness is
the full vertex set, so the density is `1` on the pattern's own isomorphism
class and `0` elsewhere. These are the degenerate densities normalizing the
flag algebra. -/

/-- The unit flag is the induced sub-flag on the roots, up to the canonical
isomorphism. -/
noncomputable def LabeledFlag.ofTypeRestrictIso [Fintype T] [Fintype V]
    (G : LabeledFlag 𝕋 σ V) (hσ : 𝕋.Mem σ)
    (h : ∀ t, G.rootEmbed.toEmbedding t ∈ G.rootFinset) :
    (LabeledFlag.ofType 𝕋 σ hσ) ≃ᶠ (G.restrict G.rootFinset h) where
  toIso :=
    ⟨Equiv.ofBijective (fun t => ⟨G.rootEmbed.toEmbedding t, h t⟩)
      ⟨fun _ _ hab => G.rootEmbed.toEmbedding.injective
          (congrArg Subtype.val hab),
        fun x => by
          obtain ⟨t, -, ht⟩ := Finset.mem_map.mp x.property
          exact ⟨t, Subtype.ext ht⟩⟩,
      fun r f => G.rootEmbed.interp_iff r f⟩
  root_preserve := fun _ => rfl

/-- The unit flag's witnesses in any host: exactly the root set. -/
lemma flagWitnesses_ofType [Fintype T] [Fintype V] (hσ : 𝕋.Mem σ)
    (G : LabeledFlag 𝕋 σ V) :
    flagWitnesses (LabeledFlag.ofType 𝕋 σ hσ) G = {G.rootFinset} := by
  ext W
  rw [mem_flagWitnesses, Finset.mem_singleton]
  constructor
  · rintro ⟨hW, hcard, -⟩
    exact (Finset.eq_of_subset_of_card_le (LabeledFlag.rootFinset_subset hW)
      (le_of_eq (by rw [hcard, G.card_rootFinset]))).symm
  · rintro rfl
    have hroot : ∀ t, G.rootEmbed.toEmbedding t ∈ G.rootFinset := fun t =>
      Finset.mem_map.mpr ⟨t, Finset.mem_univ t, rfl⟩
    exact ⟨hroot, G.card_rootFinset, ⟨(G.ofTypeRestrictIso hσ hroot).symm⟩⟩

lemma flagCount_ofType [Fintype T] [Fintype V] (hσ : 𝕋.Mem σ)
    (G : LabeledFlag 𝕋 σ V) :
    flagCount (LabeledFlag.ofType 𝕋 σ hσ) G = 1 := by
  rw [flagCount, flagWitnesses_ofType, Finset.card_singleton]

/-- The unit flag has density `1` in every host. -/
lemma flagDensity_ofType [Fintype T] [Fintype V] (hσ : 𝕋.Mem σ)
    (G : LabeledFlag 𝕋 σ V) :
    flagDensity (LabeledFlag.ofType 𝕋 σ hσ) G = 1 := by
  rw [flagDensity, flagCount_ofType, Nat.sub_self, Nat.choose_zero_right]
  simp

/-- In a host of the pattern's size that is a copy of the pattern, the unique
witness is the full vertex set. -/
lemma flagWitnesses_card_eq [Fintype T] [Fintype U] [Fintype V]
    (F : LabeledFlag 𝕋 σ U) (G : LabeledFlag 𝕋 σ V)
    (hcard : Fintype.card V = Fintype.card U) (h : Nonempty (G ≃ᶠ F)) :
    flagWitnesses F G = {Finset.univ} := by
  obtain ⟨e⟩ := h
  ext W
  rw [mem_flagWitnesses, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hcardW, -⟩
    exact Finset.eq_univ_of_card W (by rw [hcardW, hcard])
  · rintro rfl
    exact ⟨fun t => Finset.mem_univ _,
      by rw [Finset.card_univ, hcard],
      ⟨(G.restrictUniv _).trans e⟩⟩

/-- In a host of the pattern's size that is not a copy of the pattern, there
is no witness. -/
lemma flagWitnesses_card_eq_empty [Fintype T] [Fintype U] [Fintype V]
    (F : LabeledFlag 𝕋 σ U) (G : LabeledFlag 𝕋 σ V)
    (hcard : Fintype.card V = Fintype.card U) (h : ¬Nonempty (G ≃ᶠ F)) :
    flagWitnesses F G = ∅ := by
  ext W
  simp only [Finset.notMem_empty, iff_false]
  intro hW
  obtain ⟨hroot, hcardW, ⟨i⟩⟩ := mem_flagWitnesses.mp hW
  have hWuniv : W = Finset.univ := Finset.eq_univ_of_card W (by
    rw [hcardW, hcard])
  subst hWuniv
  exact h ⟨(G.restrictUniv hroot).symm.trans i⟩

/-- The unit flag has density `1` in every host, on isomorphism classes. -/
lemma subflagDensity_ofType [Fintype T] [Fintype V] (hσ : 𝕋.Mem σ)
    (G : Flag 𝕋 σ V) :
    subflagDensity (LabeledFlag.ofType 𝕋 σ hσ).toFlag G = 1 :=
  Quotient.inductionOn G fun g => flagDensity_ofType hσ g

lemma flagDensity_unitFlag [Fintype T] [Fintype V] (hσ : 𝕋.Mem σ)
    (G : LabeledFlag 𝕋 σ V) : flagDensity (unitFlag 𝕋 σ hσ) G = 1 :=
  (flagDensity_congr_left (unitFlagIso 𝕋 σ hσ) G).symm.trans
    (flagDensity_ofType hσ G)

/-- The canonical unit flag has density `1` in every host. -/
lemma subflagDensity_unitFlag [Fintype T] [Fintype V] (hσ : 𝕋.Mem σ)
    (G : Flag 𝕋 σ V) :
    subflagDensity (unitFlag 𝕋 σ hσ).toFlag G = 1 :=
  Quotient.inductionOn G fun g => flagDensity_unitFlag hσ g

/-- A flag has density `1` in itself. -/
lemma subflagDensity_self [Fintype T] [Fintype U] (F : Flag 𝕋 σ U) :
    subflagDensity F F = 1 := by
  refine Quotient.inductionOn F fun f => ?_
  show flagDensity f f = 1
  rw [flagDensity, flagCount,
    flagWitnesses_card_eq f f rfl ⟨LabeledFlagIso.refl f⟩,
    Finset.card_singleton, Nat.choose_self]
  simp

/-- Distinct flags of the same size have density `0` in one another. -/
lemma subflagDensity_eq_zero_of_ne [Fintype T] [Fintype U]
    {F G : Flag 𝕋 σ U} (h : F ≠ G) : subflagDensity F G = 0 := by
  revert h
  refine Quotient.inductionOn₂ F G fun f g h => ?_
  have hni : ¬Nonempty (g ≃ᶠ f) := fun ⟨e⟩ =>
    h (Quotient.sound ⟨e.symm⟩)
  show flagDensity f g = 0
  rw [flagDensity, flagCount, flagWitnesses_card_eq_empty f g rfl hni,
    Finset.card_empty]
  simp

/-! ## The chain rule (Razborov Lemma 2.2, `t = 1`)

Proved by double counting pairs `roots ⊆ W ⊆ A` of a witness and an
intermediate subset, then grouping the intermediate subsets by the
isomorphism class of the induced sub-flag. -/

/-- The trinomial revision: choosing a `b`-subset then a `c`-subset inside it
is choosing the `c`-subset first and completing. -/
lemma choose_mul_choose {a b c : ℕ} (hcb : c ≤ b) (hba : b ≤ a) :
    a.choose b * b.choose c = a.choose c * (a - c).choose (b - c) := by
  have hK : 0 < c.factorial * ((b - c).factorial * (a - b).factorial) :=
    Nat.mul_pos (Nat.factorial_pos _)
      (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
  apply Nat.eq_of_mul_eq_mul_right hK
  have e1 := Nat.choose_mul_factorial_mul_factorial hcb
  have e2 := Nat.choose_mul_factorial_mul_factorial hba
  have e3 := Nat.choose_mul_factorial_mul_factorial
    (Nat.sub_le_sub_right hba c)
  have e4 := Nat.choose_mul_factorial_mul_factorial (le_trans hcb hba)
  have hsub : a - c - (b - c) = a - b := by omega
  rw [hsub] at e3
  calc a.choose b * b.choose c *
        (c.factorial * ((b - c).factorial * (a - b).factorial))
      = b.choose c * c.factorial * (b - c).factorial *
        (a.choose b * (a - b).factorial) := by ring
    _ = b.factorial * (a.choose b * (a - b).factorial) := by rw [e1]
    _ = a.choose b * b.factorial * (a - b).factorial := by ring
    _ = a.factorial := e2
    _ = a.choose c * c.factorial * (a - c).factorial := e4.symm
    _ = a.choose c * c.factorial *
        ((a - c).choose (b - c) * (b - c).factorial * (a - b).factorial) := by
        rw [e3]
    _ = a.choose c * (a - c).choose (b - c) *
        (c.factorial * ((b - c).factorial * (a - b).factorial)) := by ring

/-- The number of `m`-element supersets of a fixed `R`, for any predicate
characterizing them (the predicate is abstract so that callers' `Decidable`
instances match). -/
lemma card_superset_filter [Fintype V] {R : Finset V} {m : ℕ}
    (hm : R.card ≤ m) (q : Finset V → Prop) [DecidablePred q]
    (hq : ∀ A, q A ↔ R ⊆ A ∧ A.card = m) :
    (Finset.univ.filter q).card
      = (Fintype.card V - R.card).choose (m - R.card) := by
  have hcard : ((Finset.univ \ R).powersetCard (m - R.card)).card
      = (Fintype.card V - R.card).choose (m - R.card) := by
    rw [Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ]
  rw [← hcard]
  refine Finset.card_bij' (fun A _ => A \ R) (fun X _ => X ∪ R) ?_ ?_ ?_ ?_
  · intro A hA
    obtain ⟨hRA, hAcard⟩ := (hq A).mp (Finset.mem_filter.mp hA).2
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ A) subset_rfl,
      by rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hRA, hAcard]⟩
  · intro X hX
    obtain ⟨hXsub, hXcard⟩ := Finset.mem_powersetCard.mp hX
    have hdisj : Disjoint X R := Finset.disjoint_left.mpr
      fun x hxX hxR => (Finset.mem_sdiff.mp (hXsub hxX)).2 hxR
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hq _).mpr
      ⟨Finset.subset_union_right, ?_⟩⟩
    rw [Finset.card_union_of_disjoint hdisj, hXcard]
    omega
  · intro A hA
    obtain ⟨hRA, -⟩ := (hq A).mp (Finset.mem_filter.mp hA).2
    dsimp only
    exact Finset.sdiff_union_of_subset hRA
  · intro X hX
    obtain ⟨hXsub, -⟩ := Finset.mem_powersetCard.mp hX
    dsimp only
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact h1
      · exact absurd h1 h2
    · intro hx
      exact ⟨Or.inl hx, fun hxR => (Finset.mem_sdiff.mp (hXsub hx)).2 hxR⟩

/-- The number of witnesses of `F` contained in a given subset, as a total
function of the subset (fixing the classical `filter` instances once). -/
noncomputable def restrictCount [Fintype T] [Fintype U] [Fintype V]
    (F : LabeledFlag 𝕋 σ U) (G : LabeledFlag 𝕋 σ V) (A : Finset V) : ℕ :=
  ((flagWitnesses F G).filter (· ⊆ A)).card

/-- Mapping a witness of an induced sub-flag into the ambient host. -/
lemma mem_flagWitnesses_map_subtype [Fintype T] [Fintype U] [Fintype V]
    {F : LabeledFlag 𝕋 σ U} {G : LabeledFlag 𝕋 σ V} {A : Finset V}
    (hA : ∀ t, G.rootEmbed.toEmbedding t ∈ A) {B : Finset {x // x ∈ A}}
    (hB : B ∈ flagWitnesses F (G.restrict A hA)) :
    B.map (Function.Embedding.subtype _) ∈ flagWitnesses F G := by
  obtain ⟨hroot, hcard, ⟨i⟩⟩ := mem_flagWitnesses.mp hB
  exact mem_flagWitnesses.mpr ⟨G.root_mem_map_subtype hA hroot,
    by rw [Finset.card_map]; exact hcard,
    ⟨(G.restrictRestrict hA hroot).symm.trans i⟩⟩

/-- Restricting a witness contained in `A` to a witness of the induced
sub-flag on `A`. -/
lemma mem_flagWitnesses_subtype [Fintype T] [Fintype U] [Fintype V]
    {F : LabeledFlag 𝕋 σ U} {G : LabeledFlag 𝕋 σ V} {A : Finset V}
    (hA : ∀ t, G.rootEmbed.toEmbedding t ∈ A) {W : Finset V}
    (hW : W ∈ flagWitnesses F G) (hWA : W ⊆ A) :
    W.subtype (· ∈ A) ∈ flagWitnesses F (G.restrict A hA) := by
  obtain ⟨hroot, hcard, ⟨i⟩⟩ := mem_flagWitnesses.mp hW
  have hsub : ∀ t, (G.restrict A hA).rootEmbed.toEmbedding t
      ∈ W.subtype (· ∈ A) :=
    fun t => Finset.mem_subtype.mpr (hroot t)
  have heq : (W.subtype (· ∈ A)).map (Function.Embedding.subtype _) = W := by
    rw [Finset.subtype_map, Finset.filter_true_of_mem fun x hx => hWA hx]
  exact mem_flagWitnesses.mpr ⟨hsub,
    by rw [Finset.card_subtype,
      Finset.filter_true_of_mem fun x hx => hWA hx]; exact hcard,
    ⟨((G.restrictRestrict hA hsub).trans
      (G.restrictCongr heq _ hroot)).trans i⟩⟩

/-- Counting inside a restriction is counting below the subset: the witnesses
of `F` in the induced sub-flag on `A` correspond to the witnesses of `F` in
`G` that are contained in `A`. The first ingredient of the chain rule. -/
lemma flagCount_restrict [Fintype T] [Fintype U] [Fintype V]
    (F : LabeledFlag 𝕋 σ U) (G : LabeledFlag 𝕋 σ V) {A : Finset V}
    (hA : ∀ t, G.rootEmbed.toEmbedding t ∈ A) :
    flagCount F (G.restrict A hA)
      = ((flagWitnesses F G).filter (· ⊆ A)).card := by
  unfold flagCount
  refine Finset.card_bij'
    (fun B _ => B.map (Function.Embedding.subtype _))
    (fun W _ => W.subtype (· ∈ A)) ?_ ?_ ?_ ?_
  · intro B hB
    obtain ⟨hroot, hcard, ⟨i⟩⟩ := mem_flagWitnesses.mp hB
    refine Finset.mem_filter.mpr ⟨mem_flagWitnesses.mpr
      ⟨G.root_mem_map_subtype hA hroot,
        by rw [Finset.card_map]; exact hcard,
        ⟨(G.restrictRestrict hA hroot).symm.trans i⟩⟩, ?_⟩
    intro x hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp hx
    exact b.property
  · intro W hW
    obtain ⟨hin, hWA⟩ := Finset.mem_filter.mp hW
    obtain ⟨hroot, hcard, ⟨i⟩⟩ := mem_flagWitnesses.mp hin
    have hsub : ∀ t, (G.restrict A hA).rootEmbed.toEmbedding t
        ∈ W.subtype (· ∈ A) :=
      fun t => Finset.mem_subtype.mpr (hroot t)
    have heq : (W.subtype (· ∈ A)).map (Function.Embedding.subtype _) = W := by
      rw [Finset.subtype_map, Finset.filter_true_of_mem fun x hx => hWA hx]
    exact mem_flagWitnesses.mpr ⟨hsub,
      by rw [Finset.card_subtype,
        Finset.filter_true_of_mem fun x hx => hWA hx]; exact hcard,
      ⟨((G.restrictRestrict hA hsub).trans
        (G.restrictCongr heq _ hroot)).trans i⟩⟩
  · intro B _
    dsimp only
    ext x
    rw [Finset.mem_subtype]
    exact Finset.mem_map' _
  · intro W hW
    obtain ⟨-, hWA⟩ := Finset.mem_filter.mp hW
    dsimp only
    rw [Finset.subtype_map, Finset.filter_true_of_mem fun x hx => hWA hx]

/-- `restrictCount` is the subflag count of the induced sub-flag. -/
lemma restrictCount_eq_flagCount [Fintype T] [Fintype U] [Fintype V]
    (F : LabeledFlag 𝕋 σ U) (G : LabeledFlag 𝕋 σ V) {A : Finset V}
    (hA : ∀ t, G.rootEmbed.toEmbedding t ∈ A) :
    restrictCount F G A = flagCount F (G.restrict A hA) :=
  (flagCount_restrict F G hA).symm

/-- Double counting the pairs `roots ⊆ W ⊆ A`: summing the witness counts
below all root-containing `m`-subsets counts every witness once per
completion to an `m`-set. -/
private lemma sum_restrictCount_index [Fintype T] [Fintype U] [Fintype V]
    (F : LabeledFlag 𝕋 σ U) (G : LabeledFlag 𝕋 σ V) {m : ℕ}
    (hm : Fintype.card U ≤ m) (p : Finset V → Prop) [DecidablePred p]
    (hp : ∀ A, p A ↔ (∀ t, G.rootEmbed.toEmbedding t ∈ A) ∧ A.card = m) :
    ∑ A ∈ Finset.univ.filter p, restrictCount F G A
      = flagCount F G *
        (Fintype.card V - Fintype.card U).choose (m - Fintype.card U) := by
  have hsummand : ∀ A, restrictCount F G A
      = ∑ W ∈ flagWitnesses F G, if W ⊆ A then 1 else 0 := by
    intro A
    rw [restrictCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun A _ => hsummand A, Finset.sum_comm]
  have hper : ∀ W ∈ flagWitnesses F G,
      (∑ A ∈ Finset.univ.filter p, if W ⊆ A then 1 else 0)
        = (Fintype.card V - Fintype.card U).choose (m - Fintype.card U) := by
    intro W hWmem
    obtain ⟨hroot, hcard, -⟩ := mem_flagWitnesses.mp hWmem
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones, Finset.filter_filter]
    have hcount := card_superset_filter (R := W) (m := m)
      (by rw [hcard]; exact hm)
      (fun A => p A ∧ W ⊆ A)
      (fun A => by
        show p A ∧ W ⊆ A ↔ W ⊆ A ∧ A.card = m
        rw [hp A]
        constructor
        · rintro ⟨⟨-, hAcard⟩, hWA⟩
          exact ⟨hWA, hAcard⟩
        · rintro ⟨hWA, hAcard⟩
          exact ⟨⟨fun t => hWA (hroot t), hAcard⟩, hWA⟩)
    rw [hcount, hcard]
  rw [Finset.sum_congr rfl hper, Finset.sum_const, smul_eq_mul]
  rfl

/-- The root-containing subsets of intermediate size partition into the
witness sets of the intermediate flags, one per isomorphism class. -/
lemma index_eq_biUnion {W' : Type} [Fintype T] [Fintype V] [Fintype W']
    (G : LabeledFlag 𝕋 σ V) (p : Finset V → Prop) [DecidablePred p]
    (hp : ∀ A, p A ↔ (∀ t, G.rootEmbed.toEmbedding t ∈ A)
      ∧ A.card = Fintype.card W') :
    Finset.univ.filter p
      = Finset.univ.biUnion
          (fun F' : Flag 𝕋 σ W' => flagWitnesses F'.out G) := by
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
  rw [hp A]
  constructor
  · rintro ⟨hroot, hcard⟩
    have hcoe : Fintype.card {x // x ∈ A} = Fintype.card W' := by
      rw [Fintype.card_coe]; exact hcard
    refine ⟨((G.restrict A hroot).reindex (Fintype.equivOfCardEq hcoe)).toFlag,
      mem_flagWitnesses.mpr ⟨hroot, hcard, ?_⟩⟩
    obtain ⟨i⟩ := Quotient.exact (Quotient.out_eq
      ((G.restrict A hroot).reindex (Fintype.equivOfCardEq hcoe)).toFlag)
    exact ⟨((G.restrict A hroot).reindexIso
      (Fintype.equivOfCardEq hcoe)).trans i.symm⟩
  · rintro ⟨F', hA⟩
    obtain ⟨hroot, hcard, -⟩ := mem_flagWitnesses.mp hA
    exact ⟨hroot, hcard⟩

/-- Grouping the intermediate subsets by the isomorphism class of the
induced sub-flag. -/
private lemma sum_over_classes {W' : Type}
    [Fintype T] [Fintype U] [Fintype V] [Fintype W']
    (F : LabeledFlag 𝕋 σ U) (G : LabeledFlag 𝕋 σ V)
    (p : Finset V → Prop) [DecidablePred p]
    (hp : ∀ A, p A ↔ (∀ t, G.rootEmbed.toEmbedding t ∈ A)
      ∧ A.card = Fintype.card W') :
    ∑ A ∈ Finset.univ.filter p, restrictCount F G A
      = ∑ F' : Flag 𝕋 σ W', flagCount F'.out G * flagCount F F'.out := by
  rw [index_eq_biUnion G p hp, Finset.sum_biUnion ?hdisj]
  case hdisj =>
    intro F₁ _ F₂ _ hne
    refine Finset.disjoint_left.mpr fun A hA₁ hA₂ => hne ?_
    obtain ⟨hr₁, -, ⟨i₁⟩⟩ := mem_flagWitnesses.mp hA₁
    obtain ⟨hr₂, -, ⟨i₂⟩⟩ := mem_flagWitnesses.mp hA₂
    calc F₁ = Quotient.mk _ F₁.out := (Quotient.out_eq F₁).symm
      _ = Quotient.mk _ F₂.out := Quotient.sound ⟨i₁.symm.trans i₂⟩
      _ = F₂ := Quotient.out_eq F₂
  refine Finset.sum_congr rfl fun F' _ => ?_
  have hconst : ∀ A ∈ flagWitnesses F'.out G,
      restrictCount F G A = flagCount F F'.out := by
    intro A hA
    obtain ⟨hroot, -, ⟨i⟩⟩ := mem_flagWitnesses.mp hA
    rw [restrictCount_eq_flagCount F G hroot]
    exact flagCount_congr_right F i
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
  rfl

/-- The chain rule at the level of counts. -/
private lemma flagCount_chain {W' : Type}
    [Fintype T] [Fintype U] [Fintype V] [Fintype W']
    (F : LabeledFlag 𝕋 σ U) (G : LabeledFlag 𝕋 σ V)
    (h₁ : Fintype.card U ≤ Fintype.card W') :
    flagCount F G * (Fintype.card V - Fintype.card U).choose
        (Fintype.card W' - Fintype.card U)
      = ∑ F' : Flag 𝕋 σ W', flagCount F'.out G * flagCount F F'.out := by
  classical
  rw [← sum_restrictCount_index F G h₁
      (fun A => (∀ t, G.rootEmbed.toEmbedding t ∈ A)
        ∧ A.card = Fintype.card W')
      (fun _ => Iff.rfl),
    sum_over_classes F G _ (fun _ => Iff.rfl)]

/-- The chain rule for labeled flags (Razborov Lemma 2.2, `t = 1`). -/
lemma flagDensity_chain {W' : Type}
    [Fintype T] [Fintype U] [Fintype V] [Fintype W']
    (F : LabeledFlag 𝕋 σ U) (G : LabeledFlag 𝕋 σ V)
    (h₁ : Fintype.card U ≤ Fintype.card W')
    (h₂ : Fintype.card W' ≤ Fintype.card V) :
    flagDensity F G
      = ∑ F' : Flag 𝕋 σ W', flagDensity F F'.out * flagDensity F'.out G := by
  have hk : Fintype.card T ≤ Fintype.card U :=
    Fintype.card_le_of_injective _ F.rootEmbed.toEmbedding.injective
  have c1 : (((Fintype.card V - Fintype.card T).choose
      (Fintype.card U - Fintype.card T) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have c2 : (((Fintype.card W' - Fintype.card T).choose
      (Fintype.card U - Fintype.card T) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have c3 : (((Fintype.card V - Fintype.card T).choose
      (Fintype.card W' - Fintype.card T) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have keyN : (Fintype.card V - Fintype.card T).choose
        (Fintype.card W' - Fintype.card T)
        * (Fintype.card W' - Fintype.card T).choose
          (Fintype.card U - Fintype.card T)
      = (Fintype.card V - Fintype.card T).choose
          (Fintype.card U - Fintype.card T)
        * (Fintype.card V - Fintype.card U).choose
          (Fintype.card W' - Fintype.card U) := by
    have h := choose_mul_choose
      (a := Fintype.card V - Fintype.card T)
      (b := Fintype.card W' - Fintype.card T)
      (c := Fintype.card U - Fintype.card T)
      (by omega) (by omega)
    rwa [show Fintype.card V - Fintype.card T
          - (Fintype.card U - Fintype.card T)
        = Fintype.card V - Fintype.card U by omega,
      show Fintype.card W' - Fintype.card T
          - (Fintype.card U - Fintype.card T)
        = Fintype.card W' - Fintype.card U by omega] at h
  have keyQ : (((Fintype.card V - Fintype.card T).choose
        (Fintype.card W' - Fintype.card T) : ℕ) : ℚ)
        * ((Fintype.card W' - Fintype.card T).choose
          (Fintype.card U - Fintype.card T) : ℕ)
      = (((Fintype.card V - Fintype.card T).choose
          (Fintype.card U - Fintype.card T) : ℕ) : ℚ)
        * ((Fintype.card V - Fintype.card U).choose
          (Fintype.card W' - Fintype.card U) : ℕ) := by
    exact_mod_cast keyN
  have hchainQ : (flagCount F G : ℚ) *
        ((Fintype.card V - Fintype.card U).choose
          (Fintype.card W' - Fintype.card U) : ℕ)
      = ∑ F' : Flag 𝕋 σ W',
          (flagCount F'.out G : ℚ) * (flagCount F F'.out : ℚ) := by
    have hN := flagCount_chain (W' := W') F G h₁
    calc (flagCount F G : ℚ) *
          ((Fintype.card V - Fintype.card U).choose
            (Fintype.card W' - Fintype.card U) : ℕ)
        = ((flagCount F G * (Fintype.card V - Fintype.card U).choose
            (Fintype.card W' - Fintype.card U) : ℕ) : ℚ) := by push_cast; ring
      _ = ((∑ F' : Flag 𝕋 σ W',
            flagCount F'.out G * flagCount F F'.out : ℕ) : ℚ) := by rw [hN]
      _ = ∑ F' : Flag 𝕋 σ W',
            (flagCount F'.out G : ℚ) * (flagCount F F'.out : ℚ) := by
          push_cast
          rfl
  have hsummand : ∀ F' : Flag 𝕋 σ W',
      flagDensity F F'.out * flagDensity F'.out G
        = ((flagCount F'.out G : ℚ) * (flagCount F F'.out : ℚ)) /
          ((((Fintype.card V - Fintype.card T).choose
              (Fintype.card W' - Fintype.card T) : ℕ) : ℚ) *
            (((Fintype.card W' - Fintype.card T).choose
              (Fintype.card U - Fintype.card T) : ℕ) : ℚ)) := by
    intro F'
    simp only [flagDensity]
    rw [div_mul_div_comm]
    ring
  have lhs_eq : flagDensity F G = (flagCount F G : ℚ) /
      (((Fintype.card V - Fintype.card T).choose
        (Fintype.card U - Fintype.card T) : ℕ) : ℚ) := rfl
  rw [lhs_eq, Finset.sum_congr rfl fun F' _ => hsummand F',
    ← Finset.sum_div, ← hchainQ, div_eq_div_iff c1 (mul_ne_zero c3 c2)]
  linear_combination (flagCount F G : ℚ) * keyQ

/-- **The chain rule** (Razborov Lemma 2.2, `t = 1`): a subflag density is
the sum, over all flags of any intermediate size, of the density of the
pattern in the intermediate flag times the density of the intermediate flag
in the host. -/
theorem subflagDensity_chain {W' : Type}
    [Fintype T] [Fintype U] [Fintype V] [Fintype W']
    (h₁ : Fintype.card U ≤ Fintype.card W')
    (h₂ : Fintype.card W' ≤ Fintype.card V)
    (F : Flag 𝕋 σ U) (G : Flag 𝕋 σ V) :
    subflagDensity F G
      = ∑ F' : Flag 𝕋 σ W', subflagDensity F F' * subflagDensity F' G := by
  refine Quotient.inductionOn₂ F G fun F G => ?_
  show flagDensity F G = _
  rw [flagDensity_chain F G h₁ h₂]
  refine Finset.sum_congr rfl fun F' _ => ?_
  conv_rhs => rw [← Quotient.out_eq F']
  rfl

end FlagAlgebras.Core
