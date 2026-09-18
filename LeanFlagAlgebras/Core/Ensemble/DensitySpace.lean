import LeanFlagAlgebras.Core.Limit.Realize
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Metrizable.Uniformity

/-! # Core: the density-profile space and the homomorphism space

The analytic home of the ensemble semantics. A *density profile* assigns
to every finite `σ`-flag a number in `[0, 1]`; the profiles form a
countable product of unit intervals, hence a compact metrizable space with
its Borel σ-algebra (`FlagDensitySpace`). Finite flags and positive
homomorphisms both embed into it through their profiles.

The *homomorphism space* `PositiveHomSpace` is the set of profiles of
positive homomorphisms. By the profile characterisation of
`Core/Limit/Profile` it is cut out by the chain, product and unit
relations, each a closed condition on continuous coordinate functions, so
it is closed, compact and measurable: the random-extension measures of
`Core/Ensemble/Extension` live on it.

Generalises the density-space part of the `SimpleGraph` development's
`FlagAlgebra/FlagSequence.lean` to an arbitrary theory and type. -/

namespace FlagAlgebras.Core

open Filter Topology MeasureTheory

variable {S : Signature} {T : Type} [Fintype T]
variable {𝕋 : RelTheory S} {σ : Model S T}

/-! ## The density-profile space -/

/-- The space of density profiles: functions from finite `σ`-flags to
`[0, 1]`, as a subset of the product. -/
def FlagDensitySpace (𝕋 : RelTheory S) (σ : Model S T) :
    Set (FinFlag 𝕋 σ → ℝ) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

variable (𝕋 σ) in
theorem flagDensitySpace_isCompact : IsCompact (FlagDensitySpace 𝕋 σ) :=
  isCompact_univ_pi fun _ => isCompact_Icc

instance : CompactSpace (FlagDensitySpace 𝕋 σ) :=
  isCompact_iff_compactSpace.mp (flagDensitySpace_isCompact 𝕋 σ)

noncomputable instance : MetricSpace (FlagDensitySpace 𝕋 σ) :=
  TopologicalSpace.metrizableSpaceMetric (FlagDensitySpace 𝕋 σ)

/-- Coordinates of a profile lie in `[0, 1]`. -/
theorem FlagDensitySpace.mem_Icc (a : FlagDensitySpace 𝕋 σ) (F : FinFlag 𝕋 σ) :
    (a : FinFlag 𝕋 σ → ℝ) F ∈ Set.Icc (0 : ℝ) 1 :=
  (Set.mem_univ_pi.mp a.2) F

theorem FlagDensitySpace.nonneg (a : FlagDensitySpace 𝕋 σ) (F : FinFlag 𝕋 σ) :
    0 ≤ (a : FinFlag 𝕋 σ → ℝ) F :=
  (FlagDensitySpace.mem_Icc a F).1

theorem FlagDensitySpace.le_one (a : FlagDensitySpace 𝕋 σ) (F : FinFlag 𝕋 σ) :
    (a : FinFlag 𝕋 σ → ℝ) F ≤ 1 :=
  (FlagDensitySpace.mem_Icc a F).2

theorem FlagDensitySpace.abs_le_one (a : FlagDensitySpace 𝕋 σ)
    (F : FinFlag 𝕋 σ) : |(a : FinFlag 𝕋 σ → ℝ) F| ≤ 1 := by
  rw [abs_le]
  have h := FlagDensitySpace.mem_Icc a F
  exact ⟨by linarith [h.1], h.2⟩

/-- Evaluation at a flag is continuous on the profile space. -/
theorem FlagDensitySpace.continuous_eval (F : FinFlag 𝕋 σ) :
    Continuous fun a : FlagDensitySpace 𝕋 σ => (a : FinFlag 𝕋 σ → ℝ) F :=
  (continuous_apply F).comp continuous_subtype_val

/-- Evaluation at a flag is measurable on the profile space. -/
theorem FlagDensitySpace.measurable_eval (F : FinFlag 𝕋 σ) :
    Measurable fun a : FlagDensitySpace 𝕋 σ => (a : FinFlag 𝕋 σ → ℝ) F :=
  (measurable_pi_apply F).comp measurable_subtype_coe

/-- Convergence in the profile space is coordinatewise convergence. -/
theorem FlagDensitySpace.tendsto_iff {ι : Type} {l : Filter ι}
    (u : ι → FlagDensitySpace 𝕋 σ) (a : FlagDensitySpace 𝕋 σ) :
    Tendsto u l (𝓝 a)
      ↔ ∀ F : FinFlag 𝕋 σ,
          Tendsto (fun i => (u i : FinFlag 𝕋 σ → ℝ) F) l
            (𝓝 ((a : FinFlag 𝕋 σ → ℝ) F)) := by
  rw [tendsto_subtype_rng, tendsto_pi_nhds]

/-- The profile of a finite flag, as a point of the space. -/
noncomputable def FinFlag.toDensity (G : FinFlag 𝕋 σ) : FlagDensitySpace 𝕋 σ :=
  ⟨densityVec G, by
    rw [FlagDensitySpace, Set.mem_univ_pi]
    intro F
    rw [Set.mem_Icc]
    constructor
    · show (0 : ℝ) ≤ ((subflagDensity F.2 G.2 : ℚ) : ℝ)
      exact_mod_cast subflagDensity_nonneg F.2 G.2
    · show ((subflagDensity F.2 G.2 : ℚ) : ℝ) ≤ 1
      exact_mod_cast subflagDensity_le_one F.2 G.2⟩

@[simp]
theorem FinFlag.toDensity_apply (G F : FinFlag 𝕋 σ) :
    (G.toDensity : FinFlag 𝕋 σ → ℝ) F = ((subflagDensity F.2 G.2 : ℚ) : ℝ) :=
  rfl

/-! ## The homomorphism space -/

section IsType

variable [𝕋.IsType σ]

/-- A homomorphism's values on flags are at most one. -/
theorem profile_le_one (φ : PositiveHom 𝕋 σ) (F : FinFlag 𝕋 σ) :
    φ.profile F ≤ 1 := by
  have hsum := sum_positiveHom_basisVector_eq_one φ F.1 (finFlag_size_ge F)
  have hF : φ.profile F = φ ⟦basisVector ⟨F.1, F.2⟩⟧ := rfl
  rw [hF, ← hsum]
  exact Finset.single_le_sum
    (fun F' _ => positiveHom_basisVector_nonneg φ ⟨F.1, F'⟩) (Finset.mem_univ F.2)

/-- The profile of a positive homomorphism, as a point of the space. -/
noncomputable def PositiveHom.toDensity (φ : PositiveHom 𝕋 σ) :
    FlagDensitySpace 𝕋 σ :=
  ⟨φ.profile, by
    rw [FlagDensitySpace, Set.mem_univ_pi]
    exact fun F => ⟨profile_nonneg φ F, profile_le_one φ F⟩⟩

@[simp]
theorem PositiveHom.toDensity_apply (φ : PositiveHom 𝕋 σ) (F : FinFlag 𝕋 σ) :
    (φ.toDensity : FinFlag 𝕋 σ → ℝ) F = φ ⟦basisVector F⟧ :=
  rfl

theorem PositiveHom.toDensity_injective :
    Function.Injective (PositiveHom.toDensity (𝕋 := 𝕋) (σ := σ)) :=
  fun φ₁ φ₂ h => PositiveHom.profile_injective (congrArg Subtype.val h)

/-- The homomorphism space: the profiles of positive homomorphisms. -/
def PositiveHomSpace (𝕋 : RelTheory S) (σ : Model S T) [Fintype T]
    [𝕋.IsType σ] : Set (FlagDensitySpace 𝕋 σ) :=
  Set.range PositiveHom.toDensity

/-- A realized homomorphism is the limit of the profiles of its
sequence, in the profile space. -/
theorem RealizedBy.tendsto_toDensity {φ : PositiveHom 𝕋 σ}
    {Gs : ℕ → FinFlag 𝕋 σ} (h : RealizedBy φ Gs) :
    Tendsto (fun k => (Gs k).toDensity) atTop (𝓝 φ.toDensity) := by
  rw [FlagDensitySpace.tendsto_iff]
  intro F
  exact h.2 F

/-- The homomorphism space is cut out by the chain, product and unit
relations (nonnegativity being built into the profile space). -/
theorem positiveHomSpace_eq :
    PositiveHomSpace 𝕋 σ
      = {a : FlagDensitySpace 𝕋 σ |
          ChainClosed (a : FinFlag 𝕋 σ → ℝ) ∧ MulClosed (a : FinFlag 𝕋 σ → ℝ)
            ∧ (a : FinFlag 𝕋 σ → ℝ) 1 = 1} := by
  ext a
  rw [PositiveHomSpace, Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨chainClosed_profile φ, mulClosed_profile φ, profile_one φ⟩
  · rintro ⟨hC, hM, h1⟩
    obtain ⟨φ, hφ⟩ := (exists_hom_profile_iff (a : FinFlag 𝕋 σ → ℝ)).mpr
      ⟨hC, hM, h1, FlagDensitySpace.nonneg a⟩
    exact ⟨φ, Subtype.ext hφ⟩

/-- The chain relations cut out a closed set. -/
theorem isClosed_chainClosed :
    IsClosed {a : FlagDensitySpace 𝕋 σ | ChainClosed (a : FinFlag 𝕋 σ → ℝ)} := by
  have h : {a : FlagDensitySpace 𝕋 σ | ChainClosed (a : FinFlag 𝕋 σ → ℝ)}
      = ⋂ (F : FinFlag 𝕋 σ) (ℓ : ℕ) (_ : F.1 ≤ ℓ),
          {a : FlagDensitySpace 𝕋 σ |
            (a : FinFlag 𝕋 σ → ℝ) F
              = ∑ F' : FlagWithSize 𝕋 σ ℓ,
                  ((subflagDensity F.2 F' : ℚ) : ℝ) * (a : FinFlag 𝕋 σ → ℝ) ⟨ℓ, F'⟩} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [h]
  refine isClosed_iInter fun F => isClosed_iInter fun ℓ => isClosed_iInter fun _ => ?_
  refine isClosed_eq (FlagDensitySpace.continuous_eval F) ?_
  exact continuous_finset_sum _ fun F' _ =>
    continuous_const.mul (FlagDensitySpace.continuous_eval ⟨ℓ, F'⟩)

/-- The product relations cut out a closed set. -/
theorem isClosed_mulClosed :
    IsClosed {a : FlagDensitySpace 𝕋 σ | MulClosed (a : FinFlag 𝕋 σ → ℝ)} := by
  have h : {a : FlagDensitySpace 𝕋 σ | MulClosed (a : FinFlag 𝕋 σ → ℝ)}
      = ⋂ (F₁ : FinFlag 𝕋 σ) (F₂ : FinFlag 𝕋 σ),
          {a : FlagDensitySpace 𝕋 σ |
            (∑ G : FlagWithSize 𝕋 σ (F₁.1 + F₂.1 - Fintype.card T),
              ((subflagPairDensity F₁.2 F₂.2 G : ℚ) : ℝ)
                * (a : FinFlag 𝕋 σ → ℝ) ⟨F₁.1 + F₂.1 - Fintype.card T, G⟩)
              = (a : FinFlag 𝕋 σ → ℝ) F₁ * (a : FinFlag 𝕋 σ → ℝ) F₂} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [h]
  refine isClosed_iInter fun F₁ => isClosed_iInter fun F₂ => ?_
  refine isClosed_eq ?_ ((FlagDensitySpace.continuous_eval F₁).mul
    (FlagDensitySpace.continuous_eval F₂))
  exact continuous_finset_sum _ fun G _ =>
    continuous_const.mul (FlagDensitySpace.continuous_eval _)

/-- The unit relation cuts out a closed set. -/
theorem isClosed_unitProfile :
    IsClosed {a : FlagDensitySpace 𝕋 σ | (a : FinFlag 𝕋 σ → ℝ) 1 = 1} :=
  isClosed_eq (FlagDensitySpace.continuous_eval 1) continuous_const

/-- **The homomorphism space is closed.** -/
theorem positiveHomSpace_isClosed : IsClosed (PositiveHomSpace 𝕋 σ) := by
  rw [positiveHomSpace_eq]
  have h : {a : FlagDensitySpace 𝕋 σ |
      ChainClosed (a : FinFlag 𝕋 σ → ℝ) ∧ MulClosed (a : FinFlag 𝕋 σ → ℝ)
        ∧ (a : FinFlag 𝕋 σ → ℝ) 1 = 1}
      = {a : FlagDensitySpace 𝕋 σ | ChainClosed (a : FinFlag 𝕋 σ → ℝ)}
        ∩ ({a : FlagDensitySpace 𝕋 σ | MulClosed (a : FinFlag 𝕋 σ → ℝ)}
          ∩ {a : FlagDensitySpace 𝕋 σ | (a : FinFlag 𝕋 σ → ℝ) 1 = 1}) := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [h]
  exact isClosed_chainClosed.inter (isClosed_mulClosed.inter isClosed_unitProfile)

theorem positiveHomSpace_isCompact : IsCompact (PositiveHomSpace 𝕋 σ) :=
  positiveHomSpace_isClosed.isCompact

instance : CompactSpace (PositiveHomSpace 𝕋 σ) :=
  isCompact_iff_compactSpace.mp positiveHomSpace_isCompact

theorem positiveHomSpace_measurableSet : MeasurableSet (PositiveHomSpace 𝕋 σ) :=
  positiveHomSpace_isClosed.measurableSet

/-- The homomorphism behind a point of the homomorphism space. -/
noncomputable def PositiveHomSpace.toPosHom (a : PositiveHomSpace 𝕋 σ) :
    PositiveHom 𝕋 σ :=
  Classical.choose a.2

theorem PositiveHomSpace.toDensity_toPosHom (a : PositiveHomSpace 𝕋 σ) :
    (PositiveHomSpace.toPosHom a).toDensity = a.1 :=
  Classical.choose_spec a.2

@[simp]
theorem PositiveHomSpace.toPosHom_basis (a : PositiveHomSpace 𝕋 σ)
    (F : FinFlag 𝕋 σ) :
    PositiveHomSpace.toPosHom a ⟦basisVector F⟧
      = (a.1 : FinFlag 𝕋 σ → ℝ) F := by
  rw [← PositiveHomSpace.toDensity_toPosHom a]
  rfl

/-- Evaluating the homomorphism behind a point at any class is the
profile-weighted support sum, hence measurable in the point. -/
theorem PositiveHomSpace.toPosHom_apply (a : PositiveHomSpace 𝕋 σ)
    (f : FlagVector 𝕋 σ) :
    PositiveHomSpace.toPosHom a ⟦f⟧
      = ∑ F ∈ f.support, f F * (a.1 : FinFlag 𝕋 σ → ℝ) F := by
  rw [PositiveHom.apply_quot]
  exact Finset.sum_congr rfl fun F _ => by rw [PositiveHomSpace.toPosHom_basis]

theorem PositiveHomSpace.measurable_toPosHom_apply (x : FlagAlgebra 𝕋 σ) :
    Measurable fun a : PositiveHomSpace 𝕋 σ => PositiveHomSpace.toPosHom a x := by
  refine Quotient.inductionOn x fun f => ?_
  simp_rw [PositiveHomSpace.toPosHom_apply]
  refine Finset.measurable_sum _ fun F _ => Measurable.const_mul ?_ _
  exact (FlagDensitySpace.measurable_eval F).comp measurable_subtype_coe

theorem PositiveHomSpace.continuous_toPosHom_apply (x : FlagAlgebra 𝕋 σ) :
    Continuous fun a : PositiveHomSpace 𝕋 σ => PositiveHomSpace.toPosHom a x := by
  refine Quotient.inductionOn x fun f => ?_
  simp_rw [PositiveHomSpace.toPosHom_apply]
  refine continuous_finset_sum _ fun F _ => continuous_const.mul ?_
  exact (FlagDensitySpace.continuous_eval F).comp continuous_subtype_val

/-- Values of the homomorphism behind a point are bounded by the
support-weighted `ℓ¹` norm of a representative. -/
theorem PositiveHomSpace.abs_toPosHom_apply_le (a : PositiveHomSpace 𝕋 σ)
    (f : FlagVector 𝕋 σ) :
    |PositiveHomSpace.toPosHom a ⟦f⟧| ≤ ∑ F ∈ f.support, |f F| := by
  rw [PositiveHomSpace.toPosHom_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun F _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (FlagDensitySpace.abs_le_one _ F)

end IsType

end FlagAlgebras.Core
