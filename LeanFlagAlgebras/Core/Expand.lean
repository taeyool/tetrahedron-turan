import LeanFlagAlgebras.Core.Downward

/-! # Expanding a squared linear combination

A certificate's semidefinite part is built from elements
`x = ∑ i, c i • ⟦Fᵢ⟧` of a rooted algebra, and what the assembly needs
is the expansion of `downward (x * x)` over the unlabeled classes: the
coefficient of a class collects, over its typed fiber, the quadratic
form `∑ i j, cᵢ cⱼ · p(Fᵢ, Fⱼ; X)` weighted by the labeling factor.

The order-5 certificate proved this for its one concrete element; the
order-7 certificate has five block families at four different rooted
types, so this file states it once, generically. The proof is the same
`Finset` shuffle: bilinearity, the product expansion of basis vectors,
and the fiber regrouping of the downward images.

This file deliberately does not touch `Core/Downward.lean` — everything
here is downstream of it, so the sweep pieces do not rebuild. -/

namespace FlagAlgebras.Core

open Classical

variable {S : Signature} {T : Type} [Fintype T] [S.NullaryFree]
variable {𝕋 : RelTheory S} {σ : Model S T}

omit [S.NullaryFree] in
/-- **The square of a linear combination of basis vectors**, expanded at
level `ℓ`: the coefficient of a typed class is the quadratic form of the
pair densities. -/
theorem linear_sq_expand [𝕋.IsType σ] {ι : Type} [Fintype ι] {n ℓ : ℕ}
    (c : ι → ℝ) (F : ι → FlagWithSize 𝕋 σ n)
    (hℓ : n + n ≤ ℓ + Fintype.card T) :
    (∑ i, c i • (⟦basisVector ⟨n, F i⟩⟧ : FlagAlgebra 𝕋 σ))
        * (∑ j, c j • ⟦basisVector ⟨n, F j⟩⟧)
      = ∑ X : FlagWithSize 𝕋 σ ℓ,
          (∑ i, ∑ j, c i * c j
              * ((subflagPairDensity (F i) (F j) X : ℚ) : ℝ))
            • ⟦basisVector ⟨ℓ, X⟩⟧ := by
  rw [Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by
      rw [flagAlgebra_smul_mul_smul_comm,
        basisVector_quot_mul_eq_flagMulWithSize_quot
          (⟨n, F i⟩ : FinFlag 𝕋 σ) (⟨n, F j⟩ : FinFlag 𝕋 σ) ℓ
          (by simpa using hℓ),
        show flagMulWithSize (⟨n, F i⟩ : FinFlag 𝕋 σ) ⟨n, F j⟩ ℓ
            = ∑ X : FlagWithSize 𝕋 σ ℓ,
              ((subflagPairDensity (F i) (F j) X : ℚ) : ℝ) •
                basisVector ⟨ℓ, X⟩ from rfl,
        sum_quot,
        Finset.sum_congr rfl fun X (_ : X ∈ Finset.univ) => smul_quot _ _,
        Finset.smul_sum]]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => Finset.sum_comm,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]

/-- **The downward square of a linear combination**, expanded over the
unlabeled classes: the coefficient of a class is the labeling-weighted
quadratic form over its typed fiber. This is the shape every block of a
semidefinite certificate takes. -/
theorem downward_linear_sq [𝕋.IsType σ] [𝕋.IsType (emptyType S)]
    {ι : Type} [Fintype ι] {n ℓ : ℕ}
    (c : ι → ℝ) (F : ι → FlagWithSize 𝕋 σ n)
    (hℓ : n + n ≤ ℓ + Fintype.card T) :
    downward ((∑ i, c i • (⟦basisVector ⟨n, F i⟩⟧ : FlagAlgebra 𝕋 σ))
        * (∑ j, c j • ⟦basisVector ⟨n, F j⟩⟧))
      = ∑ H : FlagWithSize 𝕋 (emptyType S) ℓ,
          (∑ X ∈ Finset.univ.filter
              (fun X : FlagWithSize 𝕋 σ ℓ => Flag.unlabel X = H),
            (∑ i, ∑ j, c i * c j
                * ((subflagPairDensity (F i) (F j) X : ℚ) : ℝ))
              * (labelingFactor (Quotient.out X).unlabel
                  (Quotient.out X) : ℝ))
            • ⟦basisVector ⟨ℓ, H⟩⟧ := by
  rw [linear_sq_expand c F hℓ, downward_sum,
    Finset.sum_congr rfl fun X (_ : X ∈ Finset.univ) => downward_smul _ _]
  exact sum_smul_downward_basis_regroup _

end FlagAlgebras.Core
