import LeanFlagAlgebras.Core.Theory
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! # Core instance: simple graphs

The arity-2 one-relation signature and its uniform theory `TGraph`, together
with the bridge to Mathlib's `SimpleGraph`: `ofSimpleGraph` and
`Model.toSimpleGraph` are mutually inverse, and membership in `TGraph` is
*exactly* being (the model of) a simple graph
(`TGraph_mem_iff_exists_simpleGraph`).

This instance is the regression anchor for the theory-generic layer: every
interface decision must keep this file (and the 3-uniform sibling
`Instances/Hypergraph3.lean`) small and painless. -/

namespace FlagAlgebras.Core

variable {V : Type}

/-- The signature of graphs: a single binary relation symbol. Reducible so
that `Fin (graphSig.ar r)` literals such as `f 0`, `f 1` elaborate. -/
abbrev graphSig : Signature where
  Rel := Unit
  ar _ := 2

instance : graphSig.NullaryFree :=
  ⟨fun r => by cases r; decide⟩

/-- The theory of simple graphs: the uniform models of `graphSig`
(symmetric, no loops). -/
def TGraph : RelTheory graphSig := uniformTheory graphSig

/-- Every index in `Fin 2` is `0` or `1`. -/
private lemma fin_two : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide

/-- The model of a simple graph. -/
def ofSimpleGraph (G : SimpleGraph V) : Model graphSig V where
  interp _ f := G.Adj (f 0) (f 1)

@[simp]
lemma ofSimpleGraph_interp (G : SimpleGraph V) (r : graphSig.Rel)
    (f : Fin 2 → V) : (ofSimpleGraph G).interp r f ↔ G.Adj (f 0) (f 1) :=
  Iff.rfl

/-- The model of a simple graph satisfies the graph theory. -/
lemma ofSimpleGraph_mem (G : SimpleGraph V) : TGraph.Mem (ofSimpleGraph G) := by
  intro r
  cases r
  constructor
  · intro e f
    show G.Adj (f (e 0)) (f (e 1)) ↔ G.Adj (f 0) (f 1)
    have h01 : e 0 ≠ e 1 := fun h => absurd (e.injective h) (by decide +kernel)
    rcases fin_two (e 0) with h0 | h0 <;> rcases fin_two (e 1) with h1 | h1
    · exact absurd (h0.trans h1.symm) h01
    · rw [h0, h1]
    · rw [h0, h1]; exact G.adj_comm _ _
    · exact absurd (h0.trans h1.symm) h01
  · intro f hf
    have hne : f 0 ≠ f 1 := G.ne_of_adj hf
    intro a b hab
    rcases fin_two a with rfl | rfl <;> rcases fin_two b with rfl | rfl
    · rfl
    · exact absurd hab hne
    · exact absurd hab.symm hne
    · rfl

/-- The simple graph of a model of the graph theory. -/
def Model.toSimpleGraph (M : Model graphSig V) (hM : TGraph.Mem M) :
    SimpleGraph V where
  Adj u v := M.interp () ![u, v]
  symm := by
    intro u v h
    have hs := (hM ()).1 (Equiv.swap 0 1) ![u, v]
    have hswap : (![u, v] ∘ (Equiv.swap (0 : Fin 2) 1)) = ![v, u] := by
      funext i
      rcases fin_two i with rfl | rfl <;> simp
    rw [hswap] at hs
    exact hs.mpr h
  loopless := by
    intro u h
    have hinj := (hM ()).2 ![u, u] h
    have : (0 : Fin 2) = 1 := hinj (by simp)
    exact absurd this (by decide +kernel)

@[simp]
lemma Model.toSimpleGraph_adj (M : Model graphSig V) (hM : TGraph.Mem M)
    (u v : V) : (M.toSimpleGraph hM).Adj u v ↔ M.interp () ![u, v] :=
  Iff.rfl

/-- Round trip on the graph side. -/
@[simp]
lemma toSimpleGraph_ofSimpleGraph (G : SimpleGraph V) :
    (ofSimpleGraph G).toSimpleGraph (ofSimpleGraph_mem G) = G := by
  ext u v
  show G.Adj (![u, v] 0) (![u, v] 1) ↔ G.Adj u v
  simp

/-- Round trip on the model side. -/
@[simp]
lemma ofSimpleGraph_toSimpleGraph (M : Model graphSig V) (hM : TGraph.Mem M) :
    ofSimpleGraph (M.toSimpleGraph hM) = M := by
  refine Model.ext ?_
  funext r f
  cases r
  have hf : ![f 0, f 1] = f := by
    funext i
    rcases fin_two i with rfl | rfl <;> simp
  show (M.interp () ![f 0, f 1]) = (M.interp () f)
  rw [hf]

/-- The graph theory is exactly the class of models of simple graphs. -/
lemma TGraph_mem_iff_exists_simpleGraph (M : Model graphSig V) :
    TGraph.Mem M ↔ ∃ G : SimpleGraph V, M = ofSimpleGraph G :=
  ⟨fun h => ⟨M.toSimpleGraph h, (ofSimpleGraph_toSimpleGraph M h).symm⟩,
   fun ⟨_, hG⟩ => hG ▸ ofSimpleGraph_mem _⟩

end FlagAlgebras.Core
