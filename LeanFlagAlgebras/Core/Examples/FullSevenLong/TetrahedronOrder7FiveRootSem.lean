import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootGramSem
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootColumnSum
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootOrderedSem

/-! The fast five-root evaluator has the full ordered-root square-factor
semantics. Its 21 root sets retain every automorphism, and its factor two
retains both orders of the complementary outside vertices. -/

namespace FlagAlgebras.Core.Tetrahedron.FullSevenLong

open FlagAlgebras.Core
open scoped BigOperators

theorem s5ColumnNum_eq_ordered (w : ℕ) : s5ColumnNum w = s5OrderedColumnNum w :=
  s5ColumnNum_eq_ordered_of_cell w fun s =>
    s5RootCell_eq_sum_perms w (s5Samples.getD s.val default)

/-- The integer numerator equals the sum of the unnormalized pair coefficients
for every active factor row and every typed ordered rooting. Division by 5040
therefore gives precisely the five-root SOS coefficient. -/
theorem s5ColumnNum_eq_ordered_sum (w : ℕ)
    (hmem : TetraFree.Mem (graphOfMask 7 w).toModel) :
    (s5ColumnNum w : ℚ) =
      ∑ b : Fin 18, ∑ r : Fin (s5Rows b),
        ∑ θ ∈ rootingsOf (s5Type b) (graphOfMask 7 w), extPairSum56
          (fun i : Fin (s5Dim b) => (fS5 b r.val i.val : ℚ))
          (fun i => s5Flag b i.val) (graphOfMask 7 w) θ := by
  rw [s5ColumnNum_eq_ordered]
  exact s5OrderedColumnNum_eq_ordered_sum w hmem

end FlagAlgebras.Core.Tetrahedron.FullSevenLong
