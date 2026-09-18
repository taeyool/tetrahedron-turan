import LeanFlagAlgebras.Core.Examples.TetrahedronRealize
import Mathlib.Topology.Sequences

/-! # Subsequence compactness for density vectors

The compactness half of the realization program: any sequence of finite
flags admits a subsequence along which every flag density converges.
The density vector of a finite flag lives in the countable product of
unit intervals — flags of each size form a `Fintype`, so the index is
countable, the product is compact and first countable, and Bolzano–
Weierstrass in that space is exactly the diagonal argument. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

instance : Countable (FinFlag TetraFree emptyType) := by
  unfold FinFlag
  infer_instance

/-- The density vector of a finite flag: all flag densities at once. -/
noncomputable def densityVec (G : FinFlag TetraFree emptyType) :
    FinFlag TetraFree emptyType → ℝ :=
  fun F => ((subflagDensity F.2 G.2 : ℚ) : ℝ)

/-- **Subsequence compactness**: along a subsequence, all flag
densities converge simultaneously, and the sizes still blow up. -/
theorem exists_convergent_subseq (Gs : ℕ → FinFlag TetraFree emptyType)
    (hsz : Filter.Tendsto (fun k => (Gs k).1) Filter.atTop Filter.atTop) :
    ∃ s : ℕ → ℕ, StrictMono s
      ∧ Filter.Tendsto (fun k => (Gs (s k)).1) Filter.atTop Filter.atTop
      ∧ ∃ L : FinFlag TetraFree emptyType → ℝ,
          ∀ F : FinFlag TetraFree emptyType,
            Filter.Tendsto (fun k => densityVec (Gs (s k)) F)
              Filter.atTop (nhds (L F)) := by
  have hcompact : IsCompact (Set.pi Set.univ
      fun _ : FinFlag TetraFree emptyType => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ k, densityVec (Gs k) ∈ Set.pi Set.univ
      (fun _ : FinFlag TetraFree emptyType => Set.Icc (0 : ℝ) 1) := by
    intro k
    rw [Set.mem_univ_pi]
    intro F
    constructor
    · show (0 : ℝ) ≤ ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ)
      exact_mod_cast subflagDensity_nonneg F.2 (Gs k).2
    · show ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ) ≤ 1
      exact_mod_cast subflagDensity_le_one F.2 (Gs k).2
  obtain ⟨L, -, s, hs, hconv⟩ := hcompact.isSeqCompact hmem
  refine ⟨s, hs, hsz.comp hs.tendsto_atTop, L, fun F => ?_⟩
  exact (tendsto_pi_nhds.mp hconv) F

end FlagAlgebras.Core.Tetrahedron
