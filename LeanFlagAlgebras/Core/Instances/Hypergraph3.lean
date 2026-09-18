import LeanFlagAlgebras.Core.Theory

/-! # Core instance: 3-uniform hypergraphs

The arity-3 one-relation signature and its uniform theory `THypergraph3` —
the target instance of the theory-generic layer. A 3-uniform hypergraph is
presented either as a model (a symmetric, injective-support ternary relation)
or as a set of hyperedges; `ofTripleSet` builds a model from an edge-set
family, and `THypergraph3_interp_congr` states the converse direction's key
fact: in a uniform model the interpretation of a triple depends only on its
vertex set. -/

namespace FlagAlgebras.Core

variable {V : Type}

/-- The signature of 3-uniform hypergraphs: a single ternary relation
symbol. Reducible so that `Fin (hypergraph3Sig.ar r)` literals elaborate. -/
abbrev hypergraph3Sig : Signature where
  Rel := Unit
  ar _ := 3

instance : hypergraph3Sig.NullaryFree :=
  ⟨fun r => by cases r; decide⟩

/-- The theory of 3-uniform hypergraphs: the uniform models of
`hypergraph3Sig`. -/
def THypergraph3 : RelTheory hypergraph3Sig := uniformTheory hypergraph3Sig

/-- The model of a 3-uniform hypergraph given by a family `E` of hyperedges
(as vertex sets): a triple is related iff it is injective and its range lies
in `E`. Members of `E` that are not 3-element sets are silently unused. -/
def ofTripleSet (E : Set (Set V)) : Model hypergraph3Sig V where
  interp _ f := Function.Injective f ∧ Set.range f ∈ E

@[simp]
lemma ofTripleSet_interp (E : Set (Set V)) (r : hypergraph3Sig.Rel)
    (f : Fin 3 → V) :
    (ofTripleSet E).interp r f ↔ Function.Injective f ∧ Set.range f ∈ E :=
  Iff.rfl

/-- Edge-set models satisfy the 3-uniform hypergraph theory. -/
lemma ofTripleSet_mem (E : Set (Set V)) : THypergraph3.Mem (ofTripleSet E) := by
  intro r
  constructor
  · intro e f
    have hr : Set.range (f ∘ e) = Set.range f := by
      rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
    have hi : Function.Injective (f ∘ e) ↔ Function.Injective f := by
      constructor
      · intro h
        have h2 := h.comp e.symm.injective
        rwa [show (f ∘ e) ∘ e.symm = f from funext fun x => by simp] at h2
      · intro h
        exact h.comp e.injective
    rw [ofTripleSet_interp, ofTripleSet_interp, hi, hr]
  · intro f hf
    exact hf.1

/-- In a 3-uniform hypergraph model, whether a triple is a hyperedge depends
only on its vertex set. -/
lemma THypergraph3_interp_congr {M : Model hypergraph3Sig V}
    (hM : THypergraph3.Mem M) {f g : Fin 3 → V}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hrange : Set.range f = Set.range g) :
    M.interp () f ↔ M.interp () g :=
  (hM ()).1.interp_iff_of_range_eq hf hg hrange

end FlagAlgebras.Core
