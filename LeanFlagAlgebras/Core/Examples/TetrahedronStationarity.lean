import LeanFlagAlgebras.Core.Stationarity
import LeanFlagAlgebras.Core.Examples.Tetrahedron

/-! # The vertex-degree stationarity element for tetrahedron-free 3-graphs

The order-7 certificate is not a pure sum of squares: it adds a multiple
of the vertex-degree stationarity term, and that term is what pushes the
bound below the previous record. This file instantiates the generic
stationarity layer at the vertex type of the tetrahedron-free theory and
records what it means there.

The rooted quantity is `degreeFlag`, the one-rooted hyperedge — its value
at a vertex is that vertex's normalized degree. Its stationarity element
is minus the variance of the degree, so:

* every homomorphism gives it a nonpositive value (free, from
  Cauchy–Schwarz);
* a homomorphism is stationary exactly when the degree has no variance,
  which is what extremality supplies for an edge-density maximizer.

The second bullet is *not* proved here — it is the semantic input of
Razborov's differential method, and it enters downstream as the explicit
hypothesis `IsStationary`. Everything that consumes the certificate is
then unconditional given that one hypothesis. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

instance : TetraFree.IsType vertexGraph.toModel := ⟨vertexGraph_mem⟩

/-- The one-rooted hyperedge: a labeled vertex together with a hyperedge
through it. Its density at a vertex is the normalized degree. -/
def degreeSym3Flag : Sym3Flag 1 3 := ⟨⟨{{0, 1, 2}}, by decide⟩, ![0]⟩

lemma degreeSym3Flag_wf : degreeSym3Flag.WellFormed vertexGraph := by decide

lemma degreeSym3Flag_mem :
    TetraFree.Mem degreeSym3Flag.graph.toModel := by decide

/-- The degree flag as an element of the vertex-typed flag algebra. -/
noncomputable def degreeFlag : FlagAlgebra TetraFree vertexGraph.toModel :=
  ⟦basisVector (⟨3, degreeSym3Flag.toFlag (𝕋 := TetraFree)
    degreeSym3Flag_wf degreeSym3Flag_mem⟩ :
      FinFlag TetraFree vertexGraph.toModel)⟧

/-- The vertex-degree stationarity element: minus the variance of the
degree across the vertices. -/
noncomputable def degreeStationarity : FlagAlgebra TetraFree emptyType :=
  stationarity degreeFlag

/-- **The degree variance is never negative**, so the stationarity
element is never positive — no extremality needed. -/
theorem positiveHom_degreeStationarity_nonpos
    (φ : PositiveHom TetraFree emptyType) :
    φ degreeStationarity ≤ 0 :=
  positiveHom_stationarity_nonpos φ degreeFlag

/-- Being stationary for the degree flag: the degree variance vanishes.
This is the property an edge-density maximizer has. -/
abbrev IsDegreeStationary (φ : PositiveHom TetraFree emptyType) : Prop :=
  IsStationary φ degreeFlag

/-- A nonnegative degree-stationarity value is already a vanishing one,
since the value is never positive. -/
theorem isDegreeStationary_of_nonneg {φ : PositiveHom TetraFree emptyType}
    (h : 0 ≤ φ degreeStationarity) : IsDegreeStationary φ :=
  isStationary_of_nonneg h

/-- **The certificate shape of the order-7 bound.** A decomposition of
`c • 1` into the edge element, nonnegative multiples of downward squares
(over any type), a multiple of the degree stationarity element, and
further nonnegative terms bounds the edge density at every
degree-stationary homomorphism.

This is the exact form the order-7 certificate produces: the stationarity
multiplier `τ` is what lets the bound fall below the pure sum-of-squares
value, and it is legitimate precisely because the maximizer is
degree-stationary. -/
theorem positiveHom_le_of_degree_stationarity_decomp
    (φ : PositiveHom TetraFree emptyType) (hφ : IsDegreeStationary φ)
    {c τ : ℝ} {ι κ : Type} (s : Finset ι) (t : Finset κ)
    (q : ι → ℝ) (hq : ∀ i ∈ s, 0 ≤ q i)
    (y : ι → FlagAlgebra TetraFree vertexGraph.toModel)
    (d : κ → ℝ) (hd : ∀ j ∈ t, 0 ≤ d j)
    (B : κ → FlagAlgebra TetraFree emptyType)
    (hB : ∀ j ∈ t, (0 : FlagAlgebra TetraFree emptyType) ≤ B j)
    (e : FlagAlgebra TetraFree emptyType)
    (hrep : c • (1 : FlagAlgebra TetraFree emptyType)
      = e + (∑ i ∈ s, q i • downward (y i * y i)) + τ • degreeStationarity
        + ∑ j ∈ t, d j • B j) :
    φ e ≤ c :=
  positiveHom_le_of_stationarity_decomp φ s t q hq y d hd B hB
    degreeFlag hφ e hrep

/-- The same decomposition with the semidefinite part abstract, so a
certificate may draw its squares from several rooting types. -/
theorem positiveHom_le_of_degree_stationarity_nonneg
    (φ : PositiveHom TetraFree emptyType) (hφ : IsDegreeStationary φ)
    {c τ : ℝ} {P R e : FlagAlgebra TetraFree emptyType}
    (hP : (0 : FlagAlgebra TetraFree emptyType) ≤ P)
    (hR : (0 : FlagAlgebra TetraFree emptyType) ≤ R)
    (hrep : c • (1 : FlagAlgebra TetraFree emptyType)
      = e + P + τ • degreeStationarity + R) :
    φ e ≤ c :=
  positiveHom_le_of_stationarity_nonneg φ hP hR hφ hrep

end FlagAlgebras.Core.Tetrahedron
