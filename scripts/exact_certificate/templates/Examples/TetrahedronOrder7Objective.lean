import LeanFlagAlgebras.Core.Examples.TetrahedronOrder5
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Deck

/-! # The objective at a seven-vertex class

The certificate's column carries an edge term, counted in bits. The
flag algebra's objective is the subflag density of the hyperedge. This
file identifies them: the density of the hyperedge in a seven-vertex
class is the set-bit count of any mask realizing it, over `35`.

Both halves already exist — `edgeCount7_eq_card_edges` turns bits into
hyperedges, and the literal density theorem turns hyperedges into a
density over the binomial normalizer. What is new is only that they
compose, which fixes the edge coefficient of the expansion identity. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

/-- **The objective, read off a mask**: the hyperedge density of a
seven-vertex class is the set-bit count over `C(7,3) = 35`. -/
theorem subflagDensity_edge_graphOfMask {w : ℕ}
    (hw : TetraFree.Mem (graphOfMask 7 w).toModel) :
    subflagDensity (edgeGraph.toFlag edgeGraph_mem)
        ((graphOfMask 7 w).toFlag hw)
      = (edgeCount7 w : ℚ) / 35 := by
  rw [Sym3Graph.subflagDensity_toFlag, edge_flagCountC_eq_card,
    edgeCount7_eq_card_edges, show Nat.choose 7 3 = 35 from rfl]
  norm_num

/-- The same statement for the representative the coverage theorem
chose: the edge coefficient of the class is the bit count of its
representative. -/
theorem subflagDensity_edge_of_toFlag {w : ℕ}
    (hw : TetraFree.Mem (graphOfMask 7 w).toModel)
    {H : FlagWithSize TetraFree emptyType 7}
    (hH : (graphOfMask 7 w).toFlag hw = H) :
    subflagDensity (edgeGraph.toFlag edgeGraph_mem) H
      = (edgeCount7 w : ℚ) / 35 := by
  rw [← hH]
  exact subflagDensity_edge_graphOfMask hw

end FlagAlgebras.Core.Tetrahedron
