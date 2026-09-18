import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootSOS
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootSem
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7Reduce

/-! # The five-root numeric element is the scaled sum of squares

The semantic bridge supplies a factor of `1 / 5040`. The complete column
denominator additionally contains the integer factor scale squared,
`2000000^2 = 4000000000000`. This module identifies the actual numeric
five-root contribution with precisely that scaled downward SOS.
-/

namespace FlagAlgebras.Core.Tetrahedron.FullSevenLong

open FlagAlgebras.Core Classical

set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

/-- The five-root contribution at a class has exactly the factor-square scale. -/
lemma fiveRootCoeff_eq_scaled (H : FlagWithSize TetraFree emptyType 7) :
    (fiveRootCoeff H : ℝ) = (1 / 4000000000000 : ℝ) *
      ∑ b : Fin 18, ∑ r : Fin (s5Rows b), gammaS5 b r H := by
  change (((s5ColumnNum (boundedRep H) : ℚ) / 20160000000000000 : ℚ) : ℝ) = _
  apply fiveRootScaledCoeff_of_ordered_sum H (boundedRep H) (boundedRep_mem H)
    (toFlag_boundedRep H (boundedRep_mem H))
  exact s5ColumnNum_eq_ordered_sum (boundedRep H) (boundedRep_mem H)

/-- The concrete five-root coefficient element is the sum of actual downward
squares divided by the factor scale squared. -/
theorem fiveRootElt_eq_scaled :
    fiveRootElt = (1 / 4000000000000 : ℝ) • fiveRootSOS := by
  have helt : fiveRootElt = ∑ H : FlagWithSize TetraFree emptyType 7,
      (fiveRootCoeff H : ℝ) •
        (⟦basisVector ⟨7, H⟩⟧ : FlagAlgebra TetraFree emptyType) := rfl
  rw [helt, fiveRootSOS_expand, Finset.smul_sum]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [fiveRootCoeff_eq_scaled, smul_smul]

end FlagAlgebras.Core.Tetrahedron.FullSevenLong
