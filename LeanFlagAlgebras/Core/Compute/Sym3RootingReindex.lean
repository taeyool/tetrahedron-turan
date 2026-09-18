import LeanFlagAlgebras.Core.Compute.RootingReindex
import LeanFlagAlgebras.Core.Compute.Sym3Fiber

/-! # Grouping literal graph rootings by sorted root sets

The type restriction remains an indicator after grouping injections into
image sets and permutations. No automorphism averaging is assumed here.
-/

namespace FlagAlgebras.Core

open Classical

/-- Every well-formed rooting appears once in the root-set/permutation sum. -/
theorem sum_rootings_eq_rootSubset_perm {k n : ℕ} {M : Type*} [AddCommMonoid M]
    (σ : Sym3Graph k) (G : Sym3Graph n) (f : (Fin k → Fin n) → M) :
    (∑ θ ∈ rootingsOf σ G, f θ) =
      ∑ s : RootSubset k (Fin n), ∑ p : Equiv.Perm (Fin k),
        if G.pullback (fun i => sortedRootEmbedding s (p i)) = σ
        then f (fun i => sortedRootEmbedding s (p i)) else 0 := by
  change (∑ θ ∈ Finset.univ.filter
    (fun θ => Function.Injective θ ∧ G.pullback θ = σ), f θ) = _
  convert sum_injective_filter_eq_rootSubset_perm (fun θ => G.pullback θ = σ) f using 1
  · refine Finset.sum_congr ?_ fun θ _ => rfl
    ext θ
    simp
  · refine Finset.sum_congr ?_ fun s _ => ?_
    · ext s
      simp
    · refine Finset.sum_congr ?_ fun p _ => ?_
      · ext p
        simp
      · by_cases h : G.pullback (fun i => sortedRootEmbedding s (p i)) = σ
        · simp only [if_pos h]
        · simp only [if_neg h]

end FlagAlgebras.Core
