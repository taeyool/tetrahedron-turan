import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Parity
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7CellSem

/-! # Rooting bookkeeping for the order-7 families

Two small facts the enumeration accounting rests on.

The single-vertex type has no hyperedges, so *every* map `Fin 1 → Fin 7`
is a well-formed rooting: the one-root rooting set is all of `univ`,
with seven elements. That is the `1/7` of `gammaS1_eq_rooting`.

For the three-root families the rooting set is cut by the parity of the
root triple, which `wellFormed_s3Type_iff` already identified with the
certificate's record bit; here it is packaged as an explicit
description of `rootingsOf` for both types, and the two sets are shown
to partition the injective rootings. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

open Classical

/-! ## One root: every map is a rooting -/

lemma vertexGraph_edges_empty : vertexGraph.edges = ∅ := rfl

/-- Any single-vertex rooting is well formed: a one-vertex pullback has
no triples to carry. -/
lemma wf_vertexGraph (G : Sym3Graph 7) (θ : Fin 1 → Fin 7) :
    (Sym3Flag.mk G θ).WellFormed vertexGraph := by
  constructor
  · intro a b _
    exact Subsingleton.elim a b
  · refine Sym3Graph.ext ?_
    rw [vertexGraph_edges_empty]
    ext e
    show e ∈ Finset.univ.filter _ ↔ _
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨-, hc, -⟩
      exfalso
      have hle : e.card ≤ 1 := by
        calc e.card ≤ Fintype.card (Fin 1) := Finset.card_le_univ e
          _ = 1 := by simp
      omega
    · intro he
      exact absurd he (Finset.notMem_empty e)

/-- **The one-root rooting set is everything.** -/
theorem rootingsOf_vertexGraph (G : Sym3Graph 7) :
    rootingsOf vertexGraph G = Finset.univ := by
  ext θ
  simp only [Finset.mem_univ, iff_true]
  exact mem_rootingsOf.mpr (wf_vertexGraph G θ)

/-- There are seven one-root rootings — the normalizer of
`gammaS1_eq_rooting`. -/
lemma rootingsOf_vertexGraph_card (G : Sym3Graph 7) :
    (rootingsOf vertexGraph G).card = 7 := by
  rw [rootingsOf_vertexGraph, Finset.card_univ]
  simp

/-! ## Three roots: the rooting sets are cut by parity -/

/-- The injective three-rootings of a host. -/
def injRootings : Finset (Fin 3 → Fin 7) :=
  Finset.univ.filter fun θ => Function.Injective θ

/-- **The nonedge rooting set**: injective rootings whose root triple is
not a hyperedge. -/
theorem rootingsOf_s3Type_zero (w : ℕ) :
    rootingsOf (s3Type 0) (graphOfMask 7 w)
      = injRootings.filter fun θ => w.testBit (rootRank θ) = false := by
  ext θ
  rw [Finset.mem_filter, injRootings, Finset.mem_filter]
  constructor
  · intro hmem
    have hwf := mem_rootingsOf.mp hmem
    exact ⟨⟨Finset.mem_univ _, hwf.1⟩,
      (wellFormed_s3Type_iff hwf.1).2.mp hwf⟩
  · rintro ⟨⟨-, hinj⟩, hbit⟩
    exact mem_rootingsOf.mpr ((wellFormed_s3Type_iff hinj).2.mpr hbit)

/-- **The edge rooting set**: injective rootings whose root triple is a
hyperedge. -/
theorem rootingsOf_s3Type_one (w : ℕ) :
    rootingsOf (s3Type 1) (graphOfMask 7 w)
      = injRootings.filter fun θ => w.testBit (rootRank θ) = true := by
  ext θ
  rw [Finset.mem_filter, injRootings, Finset.mem_filter]
  constructor
  · intro hmem
    have hwf := mem_rootingsOf.mp hmem
    exact ⟨⟨Finset.mem_univ _, hwf.1⟩,
      (wellFormed_s3Type_iff hwf.1).1.mp hwf⟩
  · rintro ⟨⟨-, hinj⟩, hbit⟩
    exact mem_rootingsOf.mpr ((wellFormed_s3Type_iff hinj).1.mpr hbit)

/-- **The two three-root families partition the injective rootings**:
summing a quantity over both is summing it over all of them. -/
theorem sum_injRootings_split {M : Type} [AddCommMonoid M]
    (w : ℕ) (f : (Fin 3 → Fin 7) → M) :
    (∑ θ ∈ rootingsOf (s3Type 0) (graphOfMask 7 w), f θ)
        + ∑ θ ∈ rootingsOf (s3Type 1) (graphOfMask 7 w), f θ
      = ∑ θ ∈ injRootings, f θ := by
  rw [rootingsOf_s3Type_zero, rootingsOf_s3Type_one]
  rw [show (injRootings.filter fun θ => w.testBit (rootRank θ) = true)
      = injRootings.filter fun θ => ¬(w.testBit (rootRank θ) = false) from by
    refine Finset.filter_congr fun θ _ => ?_
    cases h : w.testBit (rootRank θ) <;> simp]
  exact Finset.sum_filter_add_sum_filter_not injRootings
    (fun θ => w.testBit (rootRank θ) = false) f

set_option maxRecDepth 65536 in
/-- There are 210 injective three-rootings — the normalizer of
`gammaS3_eq_rooting`. -/
lemma injRootings_card : injRootings.card = 210 := by
  rw [injRootings]
  decide

end FlagAlgebras.Core.Tetrahedron
