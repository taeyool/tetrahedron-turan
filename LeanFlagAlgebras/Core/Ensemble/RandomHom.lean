import LeanFlagAlgebras.Core.Ensemble.Extension
import LeanFlagAlgebras.Core.Limit.Sampling

/-! # Core: random homomorphism extensions (Razborov's Theorem 3.5)

The packaging of `Core/Ensemble/Extension`: a probability measure on the
profile space concentrated on the homomorphism space restricts to a
probability measure on the homomorphism space itself, and integrals of
functions of the profile are unchanged. Applied to the weak limit of the
empirical labeling measures along a realizing sequence this gives the
*random extension* `ℙ[φ₀]` of a realized base homomorphism `φ₀`:

  `∫ φ, φ(f) dℙ[φ₀] = φ₀(⟦f⟧_σ) / φ₀(⟦1_σ⟧_σ)`  for every `f ∈ A^σ`,

Razborov's Theorem 3.5 (existence) in the realized form. The realizing
sequence is an explicit hypothesis; the sampling direction of Theorem 3.3
removes it and is not needed for the differential method's use. -/

namespace FlagAlgebras.Core

open Filter Topology MeasureTheory
open scoped ENNReal

variable {S : Signature} [S.NullaryFree] {T : Type} [Fintype T]
variable {𝕋 : RelTheory S} (σ : Model S T) [𝕋.IsType σ]

/-! ## Restricting a concentrated measure to the homomorphism space -/

/-- A probability measure on the profile space concentrated on the
homomorphism space assigns it full measure. -/
theorem prob_positiveHomSpace_eq_one (ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ))
    (hℙ : ∀ᵐ (a : FlagDensitySpace 𝕋 σ) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ)),
      a ∈ PositiveHomSpace 𝕋 σ) :
    (ℙ : Measure (FlagDensitySpace 𝕋 σ)) (PositiveHomSpace 𝕋 σ) = 1 := by
  rw [← prob_compl_eq_zero_iff positiveHomSpace_measurableSet]
  rw [ae_iff] at hℙ
  exact hℙ

/-- The restriction of a concentrated probability measure to the
homomorphism space. -/
noncomputable def restrictHomSpace (ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ))
    (hℙ : ∀ᵐ (a : FlagDensitySpace 𝕋 σ) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ)),
      a ∈ PositiveHomSpace 𝕋 σ) :
    ProbabilityMeasure (PositiveHomSpace 𝕋 σ) :=
  ⟨Measure.comap Subtype.val (ℙ : Measure (FlagDensitySpace 𝕋 σ)), ⟨by
    rw [Measure.comap_apply Subtype.val Subtype.val_injective
      (fun s hs => positiveHomSpace_measurableSet.subtype_image hs) _
      MeasurableSet.univ, Set.image_univ, Subtype.range_coe_subtype]
    exact prob_positiveHomSpace_eq_one σ ℙ hℙ⟩⟩

theorem restrictHomSpace_coe (ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ))
    (hℙ : ∀ᵐ (a : FlagDensitySpace 𝕋 σ) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ)),
      a ∈ PositiveHomSpace 𝕋 σ) :
    (restrictHomSpace σ ℙ hℙ : Measure (PositiveHomSpace 𝕋 σ))
      = Measure.comap Subtype.val (ℙ : Measure (FlagDensitySpace 𝕋 σ)) :=
  rfl

/-- Integrals of functions of the profile are unchanged by the
restriction. -/
theorem integral_restrictHomSpace (ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ))
    (hℙ : ∀ᵐ (a : FlagDensitySpace 𝕋 σ) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ)),
      a ∈ PositiveHomSpace 𝕋 σ)
    (g : FlagDensitySpace 𝕋 σ → ℝ) :
    ∫ a : PositiveHomSpace 𝕋 σ, g (a : FlagDensitySpace 𝕋 σ)
        ∂(restrictHomSpace σ ℙ hℙ : Measure (PositiveHomSpace 𝕋 σ))
      = ∫ a, g a ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ)) := by
  rw [restrictHomSpace_coe, integral_subtype_comap positiveHomSpace_measurableSet]
  exact setIntegral_eq_integral_of_ae_compl_eq_zero
    (hℙ.mono fun a ha hna => absurd ha hna)

/-- Evaluation of the homomorphism behind a point, as a bounded continuous
function on the (compact) homomorphism space. -/
noncomputable def evalHomBCF (x : FlagAlgebra 𝕋 σ) :
    BoundedContinuousFunction (PositiveHomSpace 𝕋 σ) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun a => PositiveHomSpace.toPosHom a x,
      PositiveHomSpace.continuous_toPosHom_apply x⟩

@[simp]
theorem evalHomBCF_apply (x : FlagAlgebra 𝕋 σ) (a : PositiveHomSpace 𝕋 σ) :
    evalHomBCF σ x a = PositiveHomSpace.toPosHom a x :=
  rfl

theorem integrable_toPosHom_apply (μ : Measure (PositiveHomSpace 𝕋 σ))
    [IsFiniteMeasure μ] (x : FlagAlgebra 𝕋 σ) :
    Integrable (fun a : PositiveHomSpace 𝕋 σ => PositiveHomSpace.toPosHom a x) μ :=
  (evalHomBCF σ x).integrable μ

/-! ## The random extension of a realized homomorphism -/

variable [𝕋.IsType (emptyType S)]

/-- **Razborov's Theorem 3.5, realized form (existence).** For a base
homomorphism `φ₀` realized by a sequence of finite hosts and giving the
unlabelled type positive density, there is a probability measure on the
homomorphism space of `σ` whose expectation of `φ ↦ φ(f)` is the
normalised downward value `φ₀(⟦f⟧_σ) / φ₀(⟦1_σ⟧_σ)`, for every `f`. -/
theorem exists_randomExtension (φ₀ : PositiveHom 𝕋 (emptyType S))
    (Gs : ℕ → FinFlag 𝕋 (emptyType S)) (h : RealizedBy φ₀ Gs)
    (hσ : 0 < φ₀ ⟦basisVector (typeFlag σ)⟧) :
    ∃ ℙ : ProbabilityMeasure (PositiveHomSpace 𝕋 σ),
      ∀ x : FlagAlgebra 𝕋 σ,
        ∫ a, PositiveHomSpace.toPosHom a x ∂(ℙ : Measure (PositiveHomSpace 𝕋 σ))
          = φ₀ (downward x) / φ₀ (downward (1 : FlagAlgebra 𝕋 σ)) := by
  obtain ⟨s, ℙ, hs, hlim⟩ := exists_weakLimit σ Gs
  have hae := ae_mem_positiveHomSpace σ φ₀ Gs hs hlim h hσ
  refine ⟨restrictHomSpace σ ℙ hae, fun x => ?_⟩
  refine Quotient.inductionOn x fun v => ?_
  have hbasis : ∀ F : FinFlag 𝕋 σ,
      ∫ a, PositiveHomSpace.toPosHom a ⟦basisVector F⟧
          ∂(restrictHomSpace σ ℙ hae : Measure (PositiveHomSpace 𝕋 σ))
        = downwardRatio σ φ₀ F := by
    intro F
    have h1 : (fun a : PositiveHomSpace 𝕋 σ =>
        PositiveHomSpace.toPosHom a ⟦basisVector F⟧)
        = fun a : PositiveHomSpace 𝕋 σ =>
            ((a : FlagDensitySpace 𝕋 σ) : FinFlag 𝕋 σ → ℝ) F := by
      funext a
      exact PositiveHomSpace.toPosHom_basis a F
    rw [h1, integral_restrictHomSpace σ ℙ hae
      (fun a : FlagDensitySpace 𝕋 σ => (a : FinFlag 𝕋 σ → ℝ) F)]
    exact integral_eval_weakLimit σ φ₀ Gs hs hlim h hσ F
  have hL : ∫ a, PositiveHomSpace.toPosHom a ⟦v⟧
      ∂(restrictHomSpace σ ℙ hae : Measure (PositiveHomSpace 𝕋 σ))
      = ∑ F ∈ v.support, v F * downwardRatio σ φ₀ F := by
    have hfun : (fun a : PositiveHomSpace 𝕋 σ => PositiveHomSpace.toPosHom a ⟦v⟧)
        = fun a : PositiveHomSpace 𝕋 σ =>
            ∑ F ∈ v.support, v F * PositiveHomSpace.toPosHom a ⟦basisVector F⟧ := by
      funext a
      rw [PositiveHom.apply_quot]
    rw [hfun, integral_finset_sum _ fun F _ =>
      (integrable_toPosHom_apply σ _ ⟦basisVector F⟧).const_mul (v F)]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [integral_const_mul, hbasis F]
  rw [hL, quot_eq_sum_basis v, downward_sum, PositiveHom.map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [downward_smul, PositiveHom.map_smul, downwardRatio, mul_div_assoc]

/-- **Razborov's Theorem 3.5 (existence), unconditionally**: every base
homomorphism giving the unlabelled type positive density has a random
extension; the realizing sequence is supplied by the sampling direction of
Theorem 3.3 (`exists_realizedBy`). -/
theorem exists_randomExtension_of_pos (φ₀ : PositiveHom 𝕋 (emptyType S))
    (hσ : 0 < φ₀ ⟦basisVector (typeFlag σ)⟧) :
    ∃ ℙ : ProbabilityMeasure (PositiveHomSpace 𝕋 σ),
      ∀ x : FlagAlgebra 𝕋 σ,
        ∫ a, PositiveHomSpace.toPosHom a x ∂(ℙ : Measure (PositiveHomSpace 𝕋 σ))
          = φ₀ (downward x) / φ₀ (downward (1 : FlagAlgebra 𝕋 σ)) := by
  obtain ⟨Gs, h⟩ := exists_realizedBy φ₀
  exact exists_randomExtension σ φ₀ Gs h hσ

/-- The random extension `ℙ[φ₀]` of a realized base homomorphism. -/
noncomputable def randomExtension (φ₀ : PositiveHom 𝕋 (emptyType S))
    (Gs : ℕ → FinFlag 𝕋 (emptyType S)) (h : RealizedBy φ₀ Gs)
    (hσ : 0 < φ₀ ⟦basisVector (typeFlag σ)⟧) :
    ProbabilityMeasure (PositiveHomSpace 𝕋 σ) :=
  Classical.choose (exists_randomExtension σ φ₀ Gs h hσ)

/-- **The defining property of `ℙ[φ₀]`.** -/
theorem integral_randomExtension (φ₀ : PositiveHom 𝕋 (emptyType S))
    (Gs : ℕ → FinFlag 𝕋 (emptyType S)) (h : RealizedBy φ₀ Gs)
    (hσ : 0 < φ₀ ⟦basisVector (typeFlag σ)⟧) (x : FlagAlgebra 𝕋 σ) :
    ∫ a, PositiveHomSpace.toPosHom a x
        ∂(randomExtension σ φ₀ Gs h hσ : Measure (PositiveHomSpace 𝕋 σ))
      = φ₀ (downward x) / φ₀ (downward (1 : FlagAlgebra 𝕋 σ)) :=
  Classical.choose_spec (exists_randomExtension σ φ₀ Gs h hσ) x

/-- The normaliser `φ₀(⟦1_σ⟧_σ)` is positive. -/
theorem positiveHom_downward_one_pos (φ₀ : PositiveHom 𝕋 (emptyType S))
    (hσ : 0 < φ₀ ⟦basisVector (typeFlag σ)⟧) :
    0 < φ₀ (downward (1 : FlagAlgebra 𝕋 σ)) := by
  rw [positiveHom_downward_one]
  exact mul_pos (by exact_mod_cast FinFlag.qFactor_pos σ 1) hσ

/-- The defining property, cleared of the normaliser. -/
theorem positiveHom_downward_eq_integral (φ₀ : PositiveHom 𝕋 (emptyType S))
    (Gs : ℕ → FinFlag 𝕋 (emptyType S)) (h : RealizedBy φ₀ Gs)
    (hσ : 0 < φ₀ ⟦basisVector (typeFlag σ)⟧) (x : FlagAlgebra 𝕋 σ) :
    φ₀ (downward x)
      = φ₀ (downward (1 : FlagAlgebra 𝕋 σ))
        * ∫ a, PositiveHomSpace.toPosHom a x
            ∂(randomExtension σ φ₀ Gs h hσ : Measure (PositiveHomSpace 𝕋 σ)) := by
  rw [integral_randomExtension σ φ₀ Gs h hσ x,
    mul_div_cancel₀ _ (positiveHom_downward_one_pos σ φ₀ hσ).ne']

end FlagAlgebras.Core
