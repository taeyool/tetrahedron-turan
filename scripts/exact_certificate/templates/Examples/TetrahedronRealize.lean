import LeanFlagAlgebras.Core.Examples.TetrahedronMaximizer
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Realization vocabulary, and the boost reduction of M2d

The maximizer statement needs semantic input: a positive homomorphism
of the generic core is a purely algebraic object, and connecting it to
finite tetrahedron-free models — where the deletion and cloning
estimates live — is a genuine theorem (the realization direction of
Razborov's Theorem 3.3).

This file fixes the vocabulary and performs the one reduction that
needs no analysis at all: if a homomorphism with genuinely negative
degree variance always admits a strictly better one — the total content
of realization, subsequence compactness, the cloning boost, and the
variance-limit exchange — then a maximizer must be degree stationary.
So M2d is reduced to `BoostedLimitExists`, and the remaining program is
to prove that statement from the finite layers. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

/-- A sequence of finite flags realizes a homomorphism: the sizes blow
up and every flag density converges to the homomorphism's value. -/
def RealizedBy (φ : PositiveHom TetraFree emptyType)
    (Gs : ℕ → FinFlag TetraFree emptyType) : Prop :=
  Filter.Tendsto (fun k => (Gs k).1) Filter.atTop Filter.atTop
    ∧ ∀ F : FinFlag TetraFree emptyType,
        Filter.Tendsto
          (fun k => ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ))
          Filter.atTop (nhds (φ ⟦basisVector F⟧))

/-- **D2, named**: every positive homomorphism of the tetrahedron-free
theory is realized by a sequence of finite tetrahedron-free flags.
Razborov, Theorem 3.3, realization direction. -/
def EveryHomRealized : Prop :=
  ∀ φ : PositiveHom TetraFree emptyType,
    ∃ Gs : ℕ → FinFlag TetraFree emptyType, RealizedBy φ Gs

/-- **The boost statement**: a homomorphism with genuinely negative
degree-stationarity value admits a strictly better edge density. This
is the total content of realization, subsequence compactness, the
finite cloning boost, and the variance-limit exchange: realize `φ`,
extract the persistent empirical variance, clone to gain a uniform
density increment, and pass to a limit homomorphism of the boosted
sequence. -/
def BoostedLimitExists : Prop :=
  ∀ φ : PositiveHom TetraFree emptyType,
    φ degreeStationarity < 0 →
    ∃ ψ : PositiveHom TetraFree emptyType, φ edgeElt < ψ edgeElt

/-- **M2d follows from the boost statement.** A maximizer cannot admit
a strictly better homomorphism, so its stationarity value cannot be
negative — and it is never positive. -/
theorem maximizerIsStationary_of_boost (h : BoostedLimitExists) :
    MaximizerIsStationary := by
  intro φ hmax
  by_contra hstat
  have hle := positiveHom_degreeStationarity_nonpos φ
  have hlt : φ degreeStationarity < 0 :=
    lt_of_le_of_ne hle fun h0 => hstat h0
  obtain ⟨ψ, hψ⟩ := h φ hlt
  exact absurd (hmax ψ) (not_le.mpr hψ)

/-- **The bound at a maximizer, on the boost statement alone.** -/
theorem edge_le_certBound_of_boost (h : BoostedLimitExists)
    (φ : PositiveHom TetraFree emptyType) (hφ : IsEdgeMaximizer φ) :
    φ edgeElt ≤ ((certBound : ℚ) : ℝ) :=
  edge_le_certBound_of_maximizer (maximizerIsStationary_of_boost h) φ hφ

end FlagAlgebras.Core.Tetrahedron
