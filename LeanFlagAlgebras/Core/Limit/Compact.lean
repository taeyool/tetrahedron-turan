import LeanFlagAlgebras.Core.Limit.Profile
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Core: subsequence compactness for density vectors

The compactness half of realization, theory-generically: any sequence of
finite flags admits a subsequence along which every flag density
converges. The density vector of a finite flag lives in the countable
product of unit intervals (flags of each size form a `Fintype`, so the
index is countable); the product is compact and first countable, and
Bolzano–Weierstrass there is exactly the diagonal argument.

Generalises `Core/Examples/TetrahedronCompact`. -/

namespace FlagAlgebras.Core

open Filter

variable {S : Signature} {T : Type} [Fintype T]
variable {𝕋 : RelTheory S} {σ : Model S T}

instance : Countable (FinFlag 𝕋 σ) := by
  unfold FinFlag
  infer_instance

/-- The density vector of a finite flag: all flag densities at once. -/
noncomputable def densityVec (G : FinFlag 𝕋 σ) : FinFlag 𝕋 σ → ℝ :=
  fun F => ((subflagDensity F.2 G.2 : ℚ) : ℝ)

/-- **Subsequence compactness**: along a subsequence, all flag densities
converge simultaneously, and the sizes still blow up. -/
theorem exists_convergent_subseq (Gs : ℕ → FinFlag 𝕋 σ)
    (hsz : Tendsto (fun k => (Gs k).1) atTop atTop) :
    ∃ s : ℕ → ℕ, StrictMono s
      ∧ Tendsto (fun k => (Gs (s k)).1) atTop atTop
      ∧ ∃ L : FinFlag 𝕋 σ → ℝ,
          ∀ F : FinFlag 𝕋 σ,
            Tendsto (fun k => densityVec (Gs (s k)) F) atTop (nhds (L F)) := by
  have hcompact : IsCompact (Set.pi Set.univ
      fun _ : FinFlag 𝕋 σ => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ k, densityVec (Gs k) ∈ Set.pi Set.univ
      (fun _ : FinFlag 𝕋 σ => Set.Icc (0 : ℝ) 1) := by
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

end FlagAlgebras.Core
