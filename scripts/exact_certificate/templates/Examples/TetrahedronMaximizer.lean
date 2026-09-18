import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7RootScaled

/-! # The maximizer semantics, and what is left of the theorem

With `IsRootScaled` proved, the certified bound holds for every
degree-stationary positive homomorphism. The remaining step to the
Turán statement is semantic: an *edge-density maximizer* is degree
stationary. That is Razborov's Theorem 4.3 (specialized to the linear
functional `f = ρ`) for 3-uniform hypergraphs relative to the
tetrahedron-free theory; the graph version is fully proved on the
differential-methods branch, and its proof runs through machinery the
generic core does not yet carry — rooted homomorphism ensembles, flag
sequences realizing a homomorphism, and the vertex-deletion estimates.

This file fixes the interface: the maximizer predicate, the named
statement `MaximizerIsStationary` (M2d), and the bound drawn from it.
Everything else in the chain is a theorem. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

/-- An edge-density maximizer among the positive homomorphisms of the
tetrahedron-free theory. -/
def IsEdgeMaximizer (φ : PositiveHom TetraFree emptyType) : Prop :=
  ∀ ψ : PositiveHom TetraFree emptyType, ψ edgeElt ≤ φ edgeElt

/-- **M2d, named**: an edge-density maximizer is degree stationary.
Razborov, Theorem 4.3 for 3-graphs relative to the tetrahedron-free
theory, specialized to the edge functional. -/
def MaximizerIsStationary : Prop :=
  ∀ φ : PositiveHom TetraFree emptyType,
    IsEdgeMaximizer φ → IsDegreeStationary φ

/-- **The bound at a maximizer**, on M2d alone: an edge-density
maximizer assigns the hyperedge at most the certificate's value. -/
theorem edge_le_certBound_of_maximizer (h : MaximizerIsStationary)
    (φ : PositiveHom TetraFree emptyType) (hφ : IsEdgeMaximizer φ) :
    φ edgeElt ≤ ((certBound : ℚ) : ℝ) :=
  edge_le_certBound_of_stationary φ (h φ hφ)

/-- **Every homomorphism is below the certificate, on M2d plus a
maximizer's existence**: if some maximizer exists, its bound caps the
whole semantic spectrum. -/
theorem edge_le_certBound_forall (h : MaximizerIsStationary)
    (φmax : PositiveHom TetraFree emptyType) (hmax : IsEdgeMaximizer φmax)
    (ψ : PositiveHom TetraFree emptyType) :
    ψ edgeElt ≤ ((certBound : ℚ) : ℝ) :=
  le_trans (hmax ψ) (edge_le_certBound_of_maximizer h φmax hmax)

end FlagAlgebras.Core.Tetrahedron
