import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronDifferential
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronBoost

example : FlagAlgebras.Core.Tetrahedron.FullSevenLong.tetraTuranDensity ≤ (312372062889819 / 560000000000000 : ℝ) :=
  FlagAlgebras.Core.Tetrahedron.FullSevenLong.tetraTuranDensity_le_certValue

example : FlagAlgebras.Core.Tetrahedron.FullSevenLong.tetraTuranDensity ≤ (312372062889819 / 560000000000000 : ℝ) :=
  FlagAlgebras.Core.Tetrahedron.FullSevenLong.tetraTuranDensity_le_certValue_finite

#check FlagAlgebras.Core.Tetrahedron.FullSevenLong.tetraTuranDensity_le_certValue
#print axioms FlagAlgebras.Core.Tetrahedron.FullSevenLong.tetraTuranDensity_le_certValue
#print axioms FlagAlgebras.Core.Tetrahedron.FullSevenLong.maxDens_eq_exTetra
#print axioms FlagAlgebras.Core.Tetrahedron.FullSevenLong.tendsto_tetraTuranDensity
#print axioms FlagAlgebras.Core.Tetrahedron.FullSevenLong.edge_le_certBound_of_stationary
#print axioms FlagAlgebras.Core.Tetrahedron.FullSevenLong.columnValue_le_columnBound
#print axioms FlagAlgebras.Core.Tetrahedron.FullSevenLong.finiteBoost
#print axioms FlagAlgebras.Core.Tetrahedron.FullSevenLong.tetraTuranDensity_le_certValue_finite
#print axioms FlagAlgebras.Core.Tetrahedron.FullSevenLong.turanDensity_le_of_stationary_bound
#print axioms FlagAlgebras.Core.Tetrahedron.FullSevenLong.isDegreeStationary_of_maximizer
#print axioms FlagAlgebras.Core.Tetrahedron.FullSevenLong.maximizerIsStationary
#print axioms FlagAlgebras.Core.Tetrahedron.FullSevenLong.fiveRootSOS_nonneg
#print axioms FlagAlgebras.Core.Tetrahedron.FullSevenLong.fiveRootElt_eq_scaled
#print axioms FlagAlgebras.Core.Tetrahedron.FullSevenLong.s5ColumnNum_eq_ordered
#print axioms FlagAlgebras.Core.Tetrahedron.FullSevenLong.s5ColumnNum_eq_ordered_sum
#print axioms FlagAlgebras.Core.isStationary_of_maximizer
#print axioms FlagAlgebras.Core.Tetrahedron.gamma56_eq_rooting5040
#print axioms FlagAlgebras.Core.sum_injective_filter_eq_rootSubset_perm
