import LeanFlagAlgebras.Core.Examples.FullSevenConverged.TetrahedronDifferential
import LeanFlagAlgebras.Core.Examples.FullSevenConverged.TetrahedronBoost
import LeanFlagAlgebras.Core.Examples.FullSevenConverged.TetrahedronConvergedHeadline

example : FlagAlgebras.Core.Tetrahedron.FullSevenConverged.tetraTuranDensity ≤ (14993367693127837 / 26880000000000000 : ℝ) :=
  FlagAlgebras.Core.Tetrahedron.FullSevenConverged.tetraTuranDensity_le_certValue

example : FlagAlgebras.Core.Tetrahedron.FullSevenConverged.tetraTuranDensity ≤ (14993367693127837 / 26880000000000000 : ℝ) :=
  FlagAlgebras.Core.Tetrahedron.FullSevenConverged.tetraTuranDensity_le_certValue_finite

example : FlagAlgebras.Core.Tetrahedron.tetraTuranDensity ≤ (14993367693127837 / 26880000000000000 : ℝ) :=
  FlagAlgebras.Core.Tetrahedron.FullSevenConverged.tetraTuranDensity_le_convergedCertValue

example : FlagAlgebras.Core.Tetrahedron.tetraTuranDensity ≤ (14993367693127837 / 26880000000000000 : ℝ) :=
  FlagAlgebras.Core.Tetrahedron.FullSevenConverged.tetraTuranDensity_le_convergedCertValue_finite

example : FlagAlgebras.Core.Tetrahedron.FullSevenConverged.tetraTuranDensity = FlagAlgebras.Core.Tetrahedron.tetraTuranDensity := rfl
