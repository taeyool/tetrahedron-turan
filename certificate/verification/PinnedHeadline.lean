import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronDifferential
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronBoost
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronLongHeadline

example : FlagAlgebras.Core.Tetrahedron.FullSevenLong.tetraTuranDensity ≤ (312372062889819 / 560000000000000 : ℝ) :=
  FlagAlgebras.Core.Tetrahedron.FullSevenLong.tetraTuranDensity_le_certValue

example : FlagAlgebras.Core.Tetrahedron.FullSevenLong.tetraTuranDensity ≤ (312372062889819 / 560000000000000 : ℝ) :=
  FlagAlgebras.Core.Tetrahedron.FullSevenLong.tetraTuranDensity_le_certValue_finite

example : FlagAlgebras.Core.Tetrahedron.tetraTuranDensity ≤ (312372062889819 / 560000000000000 : ℝ) :=
  FlagAlgebras.Core.Tetrahedron.FullSevenLong.tetraTuranDensity_le_longCertValue

example : FlagAlgebras.Core.Tetrahedron.tetraTuranDensity ≤ (312372062889819 / 560000000000000 : ℝ) :=
  FlagAlgebras.Core.Tetrahedron.FullSevenLong.tetraTuranDensity_le_longCertValue_finite

example : FlagAlgebras.Core.Tetrahedron.FullSevenLong.tetraTuranDensity = FlagAlgebras.Core.Tetrahedron.tetraTuranDensity := rfl
