import LeanFlagAlgebras.Core.Theory
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.EquivFin

/-! # Core: types and flags

Razborov §2.1, theory-generically. A *type* `σ` is a model of the theory on a
label type `T` (Razborov takes `T = [k]`); a *σ-flag* over a theory `𝕋` is a
model in `𝕋` together with an induced embedding of `σ` distinguishing the
labeled vertices (`LabeledFlag`). Label-preserving isomorphism
(`LabeledFlagIso`, `≃ᶠ`) and the quotient `Flag 𝕋 σ V` mirror the
`LabeledGraph`/`Flag` layer of the `SimpleGraph`-based development.

The type of an inhabited flag is automatically in the theory
(`LabeledFlag.type_mem`) — this is where heredity of `RelTheory` first pays:
no separate membership hypothesis on `σ` is carried around.

`LabeledFlag.restrict` is the induced sub-flag on a vertex subset containing
the roots, the basic operation underlying subflag densities
(`Core/Density.lean`). -/

namespace FlagAlgebras.Core

open Classical

variable {S : Signature} {T U V W X : Type}

/-- A `σ`-flag over the theory `𝕋`: a model of the theory together with an
induced embedding of the type `σ`, distinguishing the labeled vertices.
Razborov's `F = (M, θ)` with `M ⊨ T`. -/
structure LabeledFlag (𝕋 : RelTheory S) (σ : Model S T) (V : Type) where
  /-- The underlying model. -/
  toModel : Model S V
  /-- The model satisfies the theory. -/
  mem : 𝕋.Mem toModel
  /-- The induced embedding of the type, labeling the root vertices. -/
  rootEmbed : ModelEmbedding σ toModel

variable {𝕋 : RelTheory S} {σ : Model S T}

namespace LabeledFlag

/-- The root vertices of a flag: the image of the type embedding. -/
def rootSet (F : LabeledFlag 𝕋 σ V) : Set V :=
  Set.range F.rootEmbed.toEmbedding

/-- Restricting a flag to its roots recovers the type. -/
lemma comap_rootEmbed (F : LabeledFlag 𝕋 σ V) :
    F.toModel.comap F.rootEmbed.toEmbedding = σ := by
  refine Model.ext ?_
  funext r f
  exact propext (F.rootEmbed.interp_iff r f)

/-- The type of an inhabited flag is itself in the theory (by heredity). -/
lemma type_mem (F : LabeledFlag 𝕋 σ V) : 𝕋.Mem σ :=
  F.comap_rootEmbed ▸ 𝕋.mem_comap F.rootEmbed.toEmbedding F.mem

/-- The unit flag `1_σ`: the type viewed as a flag over itself. -/
def ofType (𝕋 : RelTheory S) (σ : Model S T) (hσ : 𝕋.Mem σ) :
    LabeledFlag 𝕋 σ T where
  toModel := σ
  mem := hσ
  rootEmbed := ⟨Function.Embedding.refl T, fun _ _ => Iff.rfl⟩

/-- Pad the type into any carrier: the σ-flag with no structure outside
the roots. Over pad-closed theories this produces flags of every size. -/
def ofPad [𝕋.PadClosed] (hσ : 𝕋.Mem σ) (f : T ↪ V) :
    LabeledFlag 𝕋 σ V where
  toModel := σ.pad f
  mem := RelTheory.PadClosed.mem_pad f hσ
  rootEmbed := σ.padEmbedding f

/-- Over a pad-closed theory, σ-flags exist on every carrier at least as
large as the type. -/
lemma nonempty_of_card_le [𝕋.PadClosed] [Fintype T] [Fintype V]
    (hσ : 𝕋.Mem σ) (h : Fintype.card T ≤ Fintype.card V) :
    Nonempty (LabeledFlag 𝕋 σ V) := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := T) (β := V) h
  exact ⟨LabeledFlag.ofPad hσ f⟩

/-- Over a signature without nullary relations, every member model is a
flag over the empty type on `Fin 0`: the canonical unlabeled flags. -/
def ofEmptyType [S.NullaryFree] {M : Model S V} (hM : 𝕋.Mem M) :
    LabeledFlag 𝕋 (emptyType S) V where
  toModel := M
  mem := hM
  rootEmbed :=
    ⟨⟨Fin.elim0, fun x => x.elim0⟩,
      fun r f => (f ⟨0, Signature.NullaryFree.ar_pos r⟩).elim0⟩

/-- Forget the labels: a σ-flag as a flag over the empty type. -/
def unlabel [S.NullaryFree] (F : LabeledFlag 𝕋 σ V) :
    LabeledFlag 𝕋 (emptyType S) V :=
  LabeledFlag.ofEmptyType F.mem

/-- The induced sub-flag on a vertex subset containing all roots. -/
def restrict (G : LabeledFlag 𝕋 σ V) (W : Finset V)
    (hW : ∀ t, G.rootEmbed.toEmbedding t ∈ W) :
    LabeledFlag 𝕋 σ {x // x ∈ W} where
  toModel := G.toModel.comap (Function.Embedding.subtype _)
  mem := 𝕋.mem_comap _ G.mem
  rootEmbed :=
    ⟨⟨fun t => ⟨G.rootEmbed.toEmbedding t, hW t⟩,
      fun _ _ hab => G.rootEmbed.toEmbedding.injective (congrArg Subtype.val hab)⟩,
     fun r f => G.rootEmbed.interp_iff r f⟩

end LabeledFlag

/-- An isomorphism of `σ`-flags: a model isomorphism respecting the type
embeddings. Flags are the isomorphism classes under this relation. -/
structure LabeledFlagIso (F : LabeledFlag 𝕋 σ V) (G : LabeledFlag 𝕋 σ W) where
  /-- The underlying model isomorphism. -/
  toIso : ModelIso F.toModel G.toModel
  /-- The isomorphism carries roots to roots, label by label. -/
  root_preserve : ∀ t, toIso.toEquiv (F.rootEmbed.toEmbedding t) =
    G.rootEmbed.toEmbedding t

@[inherit_doc] scoped infixl:50 " ≃ᶠ " => LabeledFlagIso

namespace LabeledFlagIso

variable {F : LabeledFlag 𝕋 σ V} {G : LabeledFlag 𝕋 σ W} {H : LabeledFlag 𝕋 σ X}

/-- Reflexivity of flag isomorphism. -/
@[refl]
def refl (F : LabeledFlag 𝕋 σ V) : F ≃ᶠ F :=
  ⟨ModelIso.refl _, fun _ => rfl⟩

/-- Symmetry of flag isomorphism. -/
@[symm]
def symm (e : F ≃ᶠ G) : G ≃ᶠ F where
  toIso := e.toIso.symm
  root_preserve := fun t => by
    rw [← e.root_preserve t]
    exact e.toIso.toEquiv.symm_apply_apply _

/-- Transitivity of flag isomorphism. -/
def trans (e₁ : F ≃ᶠ G) (e₂ : G ≃ᶠ H) : F ≃ᶠ H where
  toIso := e₁.toIso.trans e₂.toIso
  root_preserve := fun t => by
    show e₂.toIso.toEquiv (e₁.toIso.toEquiv (F.rootEmbed.toEmbedding t)) = _
    rw [e₁.root_preserve, e₂.root_preserve]

/-- A flag isomorphism carries root-containing subsets to root-containing
subsets. -/
lemma root_mem_map {G : LabeledFlag 𝕋 σ V} {G' : LabeledFlag 𝕋 σ W}
    (e : G ≃ᶠ G') {A : Finset V}
    (hA : ∀ t, G.rootEmbed.toEmbedding t ∈ A) :
    ∀ t, G'.rootEmbed.toEmbedding t ∈ A.map e.toIso.toEquiv.toEmbedding :=
  fun t => by
    rw [← e.root_preserve t]
    exact Finset.mem_map_of_mem _ (hA t)

/-- Unlabeling respects flag isomorphism. -/
def unlabel [S.NullaryFree] {F : LabeledFlag 𝕋 σ V} {G : LabeledFlag 𝕋 σ W}
    (e : F ≃ᶠ G) : F.unlabel ≃ᶠ G.unlabel :=
  ⟨e.toIso, fun t => t.elim0⟩

/-- Restrict a flag isomorphism to a root-containing subset and its image:
the induced sub-flags are isomorphic. -/
def restrictMap {G : LabeledFlag 𝕋 σ V} {G' : LabeledFlag 𝕋 σ W}
    (e : G ≃ᶠ G') (A : Finset V)
    (hA : ∀ t, G.rootEmbed.toEmbedding t ∈ A) :
    (G.restrict A hA) ≃ᶠ
      (G'.restrict (A.map e.toIso.toEquiv.toEmbedding) (e.root_mem_map hA)) where
  toIso := e.toIso.comapCongr (Function.Embedding.subtype _)
    (Function.Embedding.subtype _)
    (e.toIso.toEquiv.subtypeEquiv fun _ => (Finset.mem_map' _).symm)
    (fun _ => rfl)
  root_preserve := fun t => Subtype.ext (e.root_preserve t)

end LabeledFlagIso

namespace LabeledFlag

/-- Roots stay in the `Finset.map` image of a subset of a restriction. -/
lemma root_mem_map_subtype (G : LabeledFlag 𝕋 σ V) {A : Finset V}
    (hA : ∀ t, G.rootEmbed.toEmbedding t ∈ A) {B : Finset {x // x ∈ A}}
    (hB : ∀ t, (G.restrict A hA).rootEmbed.toEmbedding t ∈ B) :
    ∀ t, G.rootEmbed.toEmbedding t ∈ B.map (Function.Embedding.subtype _) :=
  fun t => Finset.mem_map_of_mem _ (hB t)

/-- Restrictions along equal subsets are isomorphic (indeed equal). -/
def restrictCongr (G : LabeledFlag 𝕋 σ V) {A₁ A₂ : Finset V} (heq : A₁ = A₂)
    (h₁ : ∀ t, G.rootEmbed.toEmbedding t ∈ A₁)
    (h₂ : ∀ t, G.rootEmbed.toEmbedding t ∈ A₂) :
    (G.restrict A₁ h₁) ≃ᶠ (G.restrict A₂ h₂) := by
  subst heq
  exact LabeledFlagIso.refl _

/-- Restricting a restriction is restricting: the induced sub-flag of an
induced sub-flag is the induced sub-flag on the composed subset. -/
noncomputable def restrictRestrict (G : LabeledFlag 𝕋 σ V) {A : Finset V}
    (hA : ∀ t, G.rootEmbed.toEmbedding t ∈ A) {B : Finset {x // x ∈ A}}
    (hB : ∀ t, (G.restrict A hA).rootEmbed.toEmbedding t ∈ B) :
    ((G.restrict A hA).restrict B hB) ≃ᶠ
      (G.restrict (B.map (Function.Embedding.subtype _))
        (G.root_mem_map_subtype hA hB)) where
  toIso := (ModelIso.refl G.toModel).comapCongr
    ((Function.Embedding.subtype _).trans (Function.Embedding.subtype _))
    (Function.Embedding.subtype _)
    (Equiv.ofBijective
      (fun b => ⟨b.val.val, Finset.mem_map_of_mem _ b.property⟩)
      ⟨fun _ _ h => by
         have hval := congrArg Subtype.val h
         dsimp only at hval
         exact Subtype.ext (Subtype.ext hval),
       fun y => by
         obtain ⟨x, hxB, hxy⟩ := Finset.mem_map.mp y.property
         exact ⟨⟨x, hxB⟩, Subtype.ext hxy⟩⟩)
    (fun _ => rfl)
  root_preserve := fun _ => Subtype.ext rfl

/-- Restricting a flag to the full vertex set changes nothing, up to the
canonical isomorphism along the subtype equivalence. -/
noncomputable def restrictUniv [Fintype V] (G : LabeledFlag 𝕋 σ V)
    (h : ∀ t, G.rootEmbed.toEmbedding t ∈ (Finset.univ : Finset V)) :
    (G.restrict Finset.univ h) ≃ᶠ G where
  toIso := ⟨Equiv.subtypeUnivEquiv fun x => Finset.mem_univ x,
    fun _ _ => Iff.rfl⟩
  root_preserve := fun _ => rfl

/-- Transport a flag along an equivalence of vertex types. -/
def reindex (G : LabeledFlag 𝕋 σ V) (e : V ≃ W) : LabeledFlag 𝕋 σ W where
  toModel := G.toModel.comap e.symm.toEmbedding
  mem := 𝕋.mem_comap _ G.mem
  rootEmbed :=
    ⟨G.rootEmbed.toEmbedding.trans e.toEmbedding, fun r f => by
      have hcomp : (e.symm.toEmbedding : W → V) ∘
          ((G.rootEmbed.toEmbedding.trans e.toEmbedding : T ↪ W) ∘ f)
          = G.rootEmbed.toEmbedding ∘ f := funext fun x => by simp
      show G.toModel.interp r _ ↔ _
      rw [hcomp]
      exact G.rootEmbed.interp_iff r f⟩

/-- The canonical isomorphism onto the transported flag. -/
def reindexIso (G : LabeledFlag 𝕋 σ V) (e : V ≃ W) : G ≃ᶠ G.reindex e where
  toIso :=
    ⟨e, fun r f => by
      show G.toModel.interp r _ ↔ G.toModel.interp r f
      rw [show (e.symm.toEmbedding : W → V) ∘ ((e : V → W) ∘ f) = f from
        funext fun x => by simp]⟩
  root_preserve := fun _ => rfl

end LabeledFlag

/-- The unit flag `1_σ` on the canonical carrier `Fin |T|`: the type,
reindexed. This is the representative the flag algebra's unit uses. -/
noncomputable def unitFlag (𝕋 : RelTheory S) (σ : Model S T) [Fintype T]
    (hσ : 𝕋.Mem σ) : LabeledFlag 𝕋 σ (Fin (Fintype.card T)) :=
  (LabeledFlag.ofType 𝕋 σ hσ).reindex (Fintype.equivFin T)

/-- The unit flag is the type, up to the reindexing isomorphism. -/
noncomputable def unitFlagIso (𝕋 : RelTheory S) (σ : Model S T) [Fintype T]
    (hσ : 𝕋.Mem σ) : (LabeledFlag.ofType 𝕋 σ hσ) ≃ᶠ unitFlag 𝕋 σ hσ :=
  (LabeledFlag.ofType 𝕋 σ hσ).reindexIso (Fintype.equivFin T)

/-- The setoid of `σ`-flags on a fixed vertex type under flag isomorphism. -/
def labeledFlagSetoid (𝕋 : RelTheory S) (σ : Model S T) (V : Type) :
    Setoid (LabeledFlag 𝕋 σ V) where
  r F G := Nonempty (F ≃ᶠ G)
  iseqv :=
    ⟨fun F => ⟨.refl F⟩,
     fun ⟨e⟩ => ⟨e.symm⟩,
     fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

/-- A `σ`-flag up to isomorphism: the generic analogue of `Flag σ V`. -/
def Flag (𝕋 : RelTheory S) (σ : Model S T) (V : Type) :=
  Quotient (labeledFlagSetoid 𝕋 σ V)

/-- The flag of a labeled representative. -/
def LabeledFlag.toFlag (F : LabeledFlag 𝕋 σ V) : Flag 𝕋 σ V :=
  Quotient.mk _ F

/-- Unlabeling on isomorphism classes. -/
def Flag.unlabel [S.NullaryFree] : Flag 𝕋 σ V → Flag 𝕋 (emptyType S) V :=
  Quotient.map LabeledFlag.unlabel fun _ _ ⟨e⟩ => ⟨e.unlabel⟩

@[simp]
lemma Flag.unlabel_mk [S.NullaryFree] (F : LabeledFlag 𝕋 σ V) :
    F.toFlag.unlabel = F.unlabel.toFlag :=
  rfl

/-- There are finitely many labeled flags on a finite vertex type. -/
noncomputable instance LabeledFlag.fintype [Fintype T] [Fintype V] :
    Fintype (LabeledFlag 𝕋 σ V) := by
  haveI : DecidableEq T := Classical.decEq T
  refine Fintype.ofInjective
    (fun F => (F.toModel, (F.rootEmbed.toEmbedding : T → V))) ?_
  rintro ⟨M, hM, ⟨f, hf⟩⟩ ⟨N, hN, ⟨g, hg⟩⟩ h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
  dsimp at h1 h2
  subst h1
  have hfg : f = g := DFunLike.coe_injective h2
  subst hfg
  rfl

/-- There are finitely many flags (isomorphism classes) on a finite vertex
type: the base of the sum in the chain rule. -/
noncomputable instance Flag.fintype [Fintype T] [Fintype V] :
    Fintype (Flag 𝕋 σ V) :=
  @Quotient.fintype _ _ (labeledFlagSetoid 𝕋 σ V)
    fun _ _ => Classical.propDecidable _

/-- Over the empty type the root conditions are vacuous, so any model
isomorphism upgrades to a flag isomorphism. -/
def LabeledFlagIso.ofEmptyType [S.NullaryFree]
    {N : LabeledFlag 𝕋 (emptyType S) V} {N' : LabeledFlag 𝕋 (emptyType S) W}
    (e : N.toModel ≃ᵣ N'.toModel) : N ≃ᶠ N' :=
  ⟨e, fun t => t.elim0⟩

/-- Empty-type flag classes are exactly model-isomorphism classes: the
equality test for unlabeled flags reduces to model isomorphism. -/
lemma LabeledFlag.toFlag_eq_toFlag_iff_modelIso [S.NullaryFree]
    {N N' : LabeledFlag 𝕋 (emptyType S) V} :
    N.toFlag = N'.toFlag ↔ Nonempty (N.toModel ≃ᵣ N'.toModel) := by
  constructor
  · intro h
    obtain ⟨i⟩ := Quotient.exact h
    exact ⟨i.toIso⟩
  · rintro ⟨e⟩
    exact Quotient.sound ⟨LabeledFlagIso.ofEmptyType e⟩

end FlagAlgebras.Core
