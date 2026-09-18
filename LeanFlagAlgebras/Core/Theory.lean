import LeanFlagAlgebras.Core.Signature

/-! # Core: universal theories, semantically

Razborov's standing assumptions on the theory `T` (§2: a universal first-order
theory with equality in a relational language, having infinite models) are
captured semantically, with no syntax: a `RelTheory` is a class of models that
is isomorphism-closed, hereditary (closed under induced substructures), and
inhabited at every finite size. These three properties are exactly what the
flag-algebra calculus consumes; conversely, the finite models of any such
universal theory form such a class.

`uniformTheory S` — all relations symmetric with injective support — is the
common core of the graph and hypergraph instances (`Core/Instances/`).
Forbidden-substructure subtheories (e.g. K₄⁽³⁾-free 3-graphs) will be built on
top of this interface as further `RelTheory`s. -/

namespace FlagAlgebras.Core

variable {S : Signature} {V W : Type}

/-- A universal relational theory, presented semantically: a class of models
that is isomorphism-closed, hereditary, and inhabited at every finite size.
Membership is a predicate on models over an *arbitrary* vertex type;
finiteness enters only where flags and densities do. -/
structure RelTheory (S : Signature) where
  /-- Membership: `Mem M` says the model `M` satisfies the theory. -/
  Mem : ∀ ⦃V : Type⦄, Model S V → Prop
  /-- Membership is invariant under model isomorphism. -/
  mem_iso : ∀ {V W : Type} {M : Model S V} {N : Model S W},
    (M ≃ᵣ N) → Mem M → Mem N
  /-- The theory is universal/hereditary: membership passes to induced
  substructures. -/
  mem_comap : ∀ {V W : Type} (f : V ↪ W) {M : Model S W},
    Mem M → Mem (M.comap f)
  /-- The theory has at least one model of every finite size. -/
  mem_inhabited : ∀ n : ℕ, ∃ M : Model S (Fin n), Mem M

namespace RelTheory

variable (𝕋 : RelTheory S)

/-- Transport membership along an equivalence of vertex types. -/
lemma mem_congr (e : V ≃ W) {M : Model S W} (h : 𝕋.Mem M) :
    𝕋.Mem (M.comap e.toEmbedding) :=
  𝕋.mem_comap e.toEmbedding h

/-- Membership is reflected by model isomorphisms. -/
lemma mem_iso_iff {M : Model S V} {N : Model S W} (e : M ≃ᵣ N) :
    𝕋.Mem M ↔ 𝕋.Mem N :=
  ⟨𝕋.mem_iso e, 𝕋.mem_iso e.symm⟩

end RelTheory

/-- The model `σ` is a type for the theory `𝕋`: a member on its label
carrier (Razborov Definition 2's "type of size `k`"). Bundled as a class so
that the flag-algebra layer can assume it implicitly. -/
class RelTheory.IsType (𝕋 : RelTheory S) {T : Type} (σ : Model S T) :
    Prop where
  /-- The type is a model of the theory. -/
  mem : 𝕋.Mem σ

/-- The theory is closed under padding with structureless vertices.
Together with heredity this produces σ-flags of every size; it holds for
the uniform theories and their forbidden-substructure subtheories, since a
padded model contains no relation instances beyond the embedded copy. -/
class RelTheory.PadClosed (𝕋 : RelTheory S) : Prop where
  /-- Padding preserves membership. -/
  mem_pad : ∀ {V W : Type} (f : V ↪ W) {M : Model S V},
    𝕋.Mem M → 𝕋.Mem (M.pad f)

/-- The theory of uniform models over `S`: every relation symmetric with
injective support. For the one-relation arity-2 signature this is the theory
of simple graphs; for arity 3, of 3-uniform hypergraphs. -/
def uniformTheory (S : Signature) : RelTheory S where
  Mem _ M := M.IsUniform
  mem_iso := fun {_ _ _ _} e h => Model.IsUniform.of_iso e h
  mem_comap := fun {_ _} f {_} h => Model.IsUniform.comap h f
  mem_inhabited := fun _ => ⟨Model.discrete S _, Model.discrete_isUniform⟩

@[simp]
lemma uniformTheory_mem (M : Model S V) :
    (uniformTheory S).Mem M ↔ M.IsUniform :=
  Iff.rfl

instance : (uniformTheory S).PadClosed where
  mem_pad := fun {_ _} f {_} h => Model.IsUniform.pad h f

end FlagAlgebras.Core
