import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Set

/-! # Core: relational signatures and models

The theory-generic foundation of the flag-algebra development, following
Razborov §2: a finite relational `Signature` (finitely many predicate symbols,
no functions or constants), `Model`s of a signature over an arbitrary vertex
type, induced substructures (`Model.comap` along an injection), model
embeddings and isomorphisms, and the two closure properties (`Model.SymmRel`,
`Model.SupportInj`) whose conjunction `Model.IsUniform` characterises
uniform-hypergraph-like models.

No first-order syntax appears anywhere: a "universal theory" enters only
through the semantic interface `RelTheory` (see `Core/Theory.lean`) — a
hereditary, isomorphism-closed, every-size-inhabited class of models, which is
all of Razborov's standing assumptions on `T`.

This layer is deliberately independent of the `SimpleGraph`-based development;
instances live in `Core/Instances/`. -/

namespace FlagAlgebras.Core

/-- A finite relational signature: a finite type of relation symbols together
with an arity for each. Razborov's language `L` "containing only predicate
symbols". -/
structure Signature where
  /-- The type of relation symbols. -/
  Rel : Type
  [relFintype : Fintype Rel]
  [relDecEq : DecidableEq Rel]
  /-- The arity of each relation symbol. -/
  ar : Rel → ℕ

attribute [instance] Signature.relFintype Signature.relDecEq

/-- A model of the signature `S` on the vertex type `V`: an interpretation of
every relation symbol as a predicate on argument tuples. No axioms are imposed
here; membership in a theory is a separate predicate (`RelTheory.Mem`). -/
@[ext]
structure Model (S : Signature) (V : Type) where
  /-- The interpretation of the relation symbol `r` on argument tuples. -/
  interp : ∀ r : S.Rel, (Fin (S.ar r) → V) → Prop

variable {S : Signature} {U V W X : Type}

/-! ## Induced substructures -/

/-- Pull a model back along an injection: the induced substructure on `V`.
For `s : Set W` and `f = Function.Embedding.subtype s` this is Razborov's
`M|_s`. -/
def Model.comap (f : V ↪ W) (M : Model S W) : Model S V where
  interp r g := M.interp r (f ∘ g)

@[simp]
lemma Model.comap_interp (f : V ↪ W) (M : Model S W) (r : S.Rel)
    (g : Fin (S.ar r) → V) : (M.comap f).interp r g ↔ M.interp r (f ∘ g) :=
  Iff.rfl

@[simp]
lemma Model.comap_refl (M : Model S V) : M.comap (Function.Embedding.refl V) = M :=
  rfl

lemma Model.comap_comap (f : U ↪ V) (g : V ↪ W) (M : Model S W) :
    (M.comap g).comap f = M.comap (f.trans g) :=
  rfl

/-! ## Model embeddings and isomorphisms

Razborov's *model embedding* is an injective map inducing an isomorphism onto
its image, i.e. it transports the interpretation along the map *in both
directions* (an induced embedding). -/

/-- A model embedding `M ↪ N`: an injection of vertex types under which the
interpretations correspond exactly (induced embedding). -/
structure ModelEmbedding (M : Model S V) (N : Model S W) where
  /-- The underlying injection of vertex types. -/
  toEmbedding : V ↪ W
  /-- The embedding is induced: a relation holds on the image iff it holds on
  the preimage. -/
  interp_iff : ∀ (r : S.Rel) (f : Fin (S.ar r) → V),
    N.interp r (toEmbedding ∘ f) ↔ M.interp r f

/-- A model isomorphism: an equivalence of vertex types under which the
interpretations correspond exactly. -/
structure ModelIso (M : Model S V) (N : Model S W) where
  /-- The underlying equivalence of vertex types. -/
  toEquiv : V ≃ W
  /-- Relations correspond along the equivalence. -/
  interp_iff : ∀ (r : S.Rel) (f : Fin (S.ar r) → V),
    N.interp r (toEquiv ∘ f) ↔ M.interp r f

@[inherit_doc] scoped infixl:25 " ≃ᵣ " => ModelIso

namespace ModelIso

/-- The interpretation correspondence of an isomorphism, read from the
codomain side. -/
lemma interp_iff' {M : Model S V} {N : Model S W} (e : M ≃ᵣ N) (r : S.Rel)
    (g : Fin (S.ar r) → W) : N.interp r g ↔ M.interp r (e.toEquiv.symm ∘ g) := by
  have h := e.interp_iff r (e.toEquiv.symm ∘ g)
  rwa [show e.toEquiv ∘ (e.toEquiv.symm ∘ g) = g from
    funext fun i => e.toEquiv.apply_symm_apply _] at h

/-- The identity isomorphism. -/
def refl (M : Model S V) : M ≃ᵣ M :=
  ⟨Equiv.refl V, fun _ _ => Iff.rfl⟩

/-- The inverse of a model isomorphism. -/
def symm {M : Model S V} {N : Model S W} (e : M ≃ᵣ N) : N ≃ᵣ M :=
  ⟨e.toEquiv.symm, fun r g => (e.interp_iff' r g).symm⟩

/-- Composition of model isomorphisms. -/
def trans {M : Model S V} {N : Model S W} {P : Model S X}
    (e₁ : M ≃ᵣ N) (e₂ : N ≃ᵣ P) : M ≃ᵣ P :=
  ⟨e₁.toEquiv.trans e₂.toEquiv, fun r f =>
    (e₂.interp_iff r (e₁.toEquiv ∘ f)).trans (e₁.interp_iff r f)⟩

/-- Every model isomorphism is in particular a model embedding. -/
def toModelEmbedding {M : Model S V} {N : Model S W} (e : M ≃ᵣ N) :
    ModelEmbedding M N :=
  ⟨e.toEquiv.toEmbedding, e.interp_iff⟩

/-- Transport a pullback along a model isomorphism: if `e : M ≃ᵣ N` carries
the embedded copy of `A` inside `V` onto the embedded copy of `B` inside `W`
(via `j`), then the induced substructures are isomorphic via `j`. -/
def comapCongr {M : Model S V} {N : Model S W} (e : M ≃ᵣ N) {A B : Type}
    (f : A ↪ V) (g : B ↪ W) (j : A ≃ B)
    (hcomm : ∀ a, e.toEquiv (f a) = g (j a)) :
    (M.comap f) ≃ᵣ (N.comap g) where
  toEquiv := j
  interp_iff := fun r x => by
    have h := e.interp_iff r (f ∘ x)
    rwa [show e.toEquiv ∘ (f ∘ x) = g ∘ (j ∘ x) from
      funext fun i => hcomm (x i)] at h

end ModelIso

/-- The induced substructure embeds canonically into the ambient model. -/
def ModelEmbedding.ofComap (f : V ↪ W) (M : Model S W) :
    ModelEmbedding (M.comap f) M :=
  ⟨f, fun _ _ => Iff.rfl⟩

/-- Pulling back along an equivalence is a model isomorphism. -/
def ModelIso.ofComapEquiv (e : V ≃ W) (M : Model S W) :
    (M.comap e.toEmbedding) ≃ᵣ M :=
  ⟨e, fun _ _ => Iff.rfl⟩

/-! ## Uniformity: symmetric relations with injective support

An arity-`k` relation that is invariant under permutations of its arguments
and holds only on injective tuples is the same data as a set of `k`-element
vertex subsets: a `k`-uniform hyperedge relation. `Model.IsUniform` (all
relation symbols symmetric with injective support) characterises simple
graphs for the arity-2 signature and 3-uniform hypergraphs for the arity-3
signature; see `Core/Instances/`. -/

/-- The relation `r` is symmetric: invariant under permuting its arguments. -/
def Model.SymmRel (M : Model S V) (r : S.Rel) : Prop :=
  ∀ (e : Equiv.Perm (Fin (S.ar r))) (f : Fin (S.ar r) → V),
    M.interp r (f ∘ e) ↔ M.interp r f

/-- The relation `r` holds only on injective argument tuples (no "loops"). -/
def Model.SupportInj (M : Model S V) (r : S.Rel) : Prop :=
  ∀ f, M.interp r f → Function.Injective f

/-- A model is uniform if every relation is symmetric with injective support:
the hypergraph-like models. -/
def Model.IsUniform (M : Model S V) : Prop :=
  ∀ r, M.SymmRel r ∧ M.SupportInj r

/-- For a symmetric relation the interpretation depends only on the *set* of
arguments: two injective tuples with the same range are interchangeable. This
is the bridge between tuple-based interpretations and edge-set
representations of uniform hypergraphs. -/
lemma Model.SymmRel.interp_iff_of_range_eq {M : Model S V} {r : S.Rel}
    (hs : M.SymmRel r) {f g : Fin (S.ar r) → V}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hrange : Set.range f = Set.range g) :
    M.interp r f ↔ M.interp r g := by
  have hmem : ∀ x, g x ∈ Set.range f := fun x => hrange.symm ▸ Set.mem_range_self x
  set e0 : Fin (S.ar r) → Fin (S.ar r) :=
    fun x => (Equiv.ofInjective f hf).symm ⟨g x, hmem x⟩ with he0
  have hfe0 : ∀ x, f (e0 x) = g x :=
    fun x => Equiv.apply_ofInjective_symm hf ⟨g x, hmem x⟩
  have he0inj : Function.Injective e0 := by
    intro x y hxy
    apply hg
    rw [← hfe0 x, ← hfe0 y, hxy]
  have he0surj : Function.Surjective e0 := by
    intro y
    have hy : f y ∈ Set.range g := by rw [← hrange]; exact Set.mem_range_self y
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, hf ?_⟩
    rw [hfe0 x, hx]
  have h := hs (Equiv.ofBijective e0 ⟨he0inj, he0surj⟩) f
  rw [show f ∘ (Equiv.ofBijective e0 ⟨he0inj, he0surj⟩) = g from funext fun x => hfe0 x] at h
  exact h.symm

lemma Model.IsUniform.comap {M : Model S W} (h : M.IsUniform) (f : V ↪ W) :
    (M.comap f).IsUniform := by
  intro r
  obtain ⟨hs, hi⟩ := h r
  refine ⟨fun e g => hs e (f ∘ g), fun g hg => ?_⟩
  exact (hi _ hg).of_comp

lemma Model.IsUniform.of_iso {M : Model S V} {N : Model S W} (e : M ≃ᵣ N)
    (h : M.IsUniform) : N.IsUniform := by
  intro r
  obtain ⟨hs, hi⟩ := h r
  constructor
  · intro p g
    rw [e.interp_iff' r (g ∘ p), e.interp_iff' r g]
    exact hs p (e.toEquiv.symm ∘ g)
  · intro g hg
    have hinj := hi _ ((e.interp_iff' r g).mp hg)
    exact fun a b hab => hinj (congrArg e.toEquiv.symm hab)

/-! ## Padding

Extending a model by vertices that carry no relations: `Model.pad M f`
places a copy of `M` along the injection `f` and interprets every relation
as holding only on tuples inside that copy. This is Razborov's "add
isolated vertices" construction — heredity gives substructures, padding
gives extensions, and together they produce flags of every size. -/

/-- Pad a model along an injection: relations hold exactly on tuples from
the embedded copy, where they are inherited from `M`. -/
def Model.pad (M : Model S V) (f : V ↪ W) : Model S W where
  interp r g := ∃ g' : Fin (S.ar r) → V, f ∘ g' = g ∧ M.interp r g'

/-- The embedded copy inside a padding is induced: `M` embeds into
`M.pad f`. -/
def Model.padEmbedding (M : Model S V) (f : V ↪ W) :
    ModelEmbedding M (M.pad f) where
  toEmbedding := f
  interp_iff := fun r g => by
    constructor
    · rintro ⟨g', hg', hM⟩
      rwa [show g' = g from funext fun i =>
        f.injective (congrFun hg' i)] at hM
    · intro hM
      exact ⟨g, rfl, hM⟩

/-- Padding preserves uniformity: the padded relations are symmetric with
injective support whenever the original ones are. -/
lemma Model.IsUniform.pad {M : Model S V} (h : M.IsUniform) (f : V ↪ W) :
    (M.pad f).IsUniform := by
  intro r
  obtain ⟨hs, hi⟩ := h r
  constructor
  · intro e g
    constructor
    · rintro ⟨g', hg', hM⟩
      refine ⟨g' ∘ e.symm, funext fun i => ?_, (hs e.symm g').mpr hM⟩
      show f (g' (e.symm i)) = g i
      rw [show f (g' (e.symm i)) = (g ∘ e) (e.symm i) from congrFun hg' _]
      exact congrArg g (e.apply_symm_apply i)
    · rintro ⟨g', hg', hM⟩
      exact ⟨g' ∘ e, funext fun i => congrFun hg' (e i), (hs e g').mpr hM⟩
  · intro g hg
    obtain ⟨g', hg', hM⟩ := hg
    rw [← hg']
    exact f.injective.comp (hi g' hM)

/-! ## The discrete model -/

open Classical in
/-- There are finitely many models on a finite vertex type (classically:
interpretations are `Prop`-valued functions on finite data). -/
noncomputable instance Model.fintype [Fintype V] : Fintype (Model S V) :=
  Fintype.ofInjective Model.interp fun _ _ h => Model.ext h

/-- The discrete model: no relation holds. A model of every reasonable theory,
witnessing inhabitedness at every size. -/
def Model.discrete (S : Signature) (V : Type) : Model S V :=
  ⟨fun _ _ => False⟩

@[simp]
lemma Model.discrete_interp (r : S.Rel) (f : Fin (S.ar r) → V) :
    ¬(Model.discrete S V).interp r f :=
  id

lemma Model.discrete_isUniform : (Model.discrete S V).IsUniform :=
  fun _ => ⟨fun _ _ => Iff.rfl, fun _ hf => hf.elim⟩

/-! ## Nullary-free signatures and the empty type -/

/-- The signature has no nullary relation symbols: every arity is positive.
The standing assumption behind unlabeled (empty-type) flags — a relation
with no arguments could distinguish models on the empty carrier. -/
class Signature.NullaryFree (S : Signature) : Prop where
  /-- Every relation symbol has positive arity. -/
  ar_pos : ∀ r : S.Rel, 0 < S.ar r

/-- The empty type: the discrete model on the empty carrier. Flags over it
are the unlabeled flags, the home of the downward operator. -/
abbrev emptyType (S : Signature) : Model S (Fin 0) :=
  Model.discrete S (Fin 0)

end FlagAlgebras.Core
