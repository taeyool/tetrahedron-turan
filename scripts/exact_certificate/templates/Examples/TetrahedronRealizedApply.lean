import LeanFlagAlgebras.Core.Examples.TetrahedronLimitHom

/-! # Values of a realized homomorphism

A homomorphism realized by a sequence has *every* value determined by
the sequence, not just the basis values: a general algebra element is a
finite combination of basis classes, the homomorphism is linear, and
the basis values converge — so the element's value is the limit of the
corresponding finite density combinations.

This is the piece that lets the boost argument read the stationarity
value of a realized homomorphism off its finite models: no sampling
direction of realization is needed anywhere, because the homomorphisms
the final bound consumes arrive *with* their realizing sequences. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core Filter

/-- Finite sums of flag vectors pass through the quotient. -/
lemma quot_sum {ι : Type} (s : Finset ι)
    (g : ι → FlagVector TetraFree emptyType) :
    (⟦∑ i ∈ s, g i⟧ : FlagAlgebra TetraFree emptyType)
      = ∑ i ∈ s, (⟦g i⟧ : FlagAlgebra TetraFree emptyType) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, add_quot]

/-- A general class as a combination of basis classes. -/
lemma quot_eq_sum_basis (f : FlagVector TetraFree emptyType) :
    (⟦f⟧ : FlagAlgebra TetraFree emptyType)
      = ∑ F ∈ f.support, f F • (⟦basisVector F⟧
          : FlagAlgebra TetraFree emptyType) := by
  conv_lhs => rw [flagVector_eq_sum_basisVector f]
  rw [quot_sum]
  exact Finset.sum_congr rfl fun F _ => smul_quot (f F) (basisVector F)

/-- **The value of a realized homomorphism at any class is the limit of
the finite density combinations.** -/
theorem realized_apply {φ : PositiveHom TetraFree emptyType}
    {Gs : ℕ → FinFlag TetraFree emptyType} (h : RealizedBy φ Gs)
    (f : FlagVector TetraFree emptyType) :
    Tendsto
      (fun k => ∑ F ∈ f.support,
        f F * ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ))
      atTop (nhds (φ ⟦f⟧)) := by
  have hval : φ ⟦f⟧ = ∑ F ∈ f.support, f F * φ ⟦basisVector F⟧ := by
    rw [quot_eq_sum_basis f, PositiveHom.map_sum]
    exact Finset.sum_congr rfl fun F _ => PositiveHom.map_smul φ _ _
  rw [hval]
  exact tendsto_finset_sum _ fun F _ => (h.2 F).const_mul (f F)

end FlagAlgebras.Core.Tetrahedron
