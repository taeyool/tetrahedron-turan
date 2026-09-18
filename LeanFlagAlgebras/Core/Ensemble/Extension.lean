import LeanFlagAlgebras.Core.Ensemble.Empirical
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! # Core: the random extension measure along a realizing sequence

Razborov's Theorem 3.5 in its *realized* form. Let `φ₀` be a positive
homomorphism of the unlabelled algebra realized by a sequence of finite
hosts `Gs`, and let the unlabelled type `σ|₀` have positive density under
`φ₀`. Then the empirical labeling measures of the hosts (`Core/Ensemble/
Empirical`) are eventually defined, form a sequence of probability
measures on the compact profile space, and by Prokhorov's theorem have a
weakly convergent subsequence. The limit `ℙ` has the moments

  `∫ a F dℙ = φ₀(⟦F⟧_σ) / φ₀(⟦1_σ⟧_σ)`  (`integral_eval_weakLimit`),

because the finite moment identity passes to the limit along the
realizing sequence, and it is concentrated on the homomorphism space
(`ae_mem_positiveHomSpace`): the chain and unit relations hold exactly at
every finite level, the product relation up to `O(1/n)`, and each
relation is a closed condition whose defect is a nonnegative bounded
continuous function with vanishing integrals.

`Core/Ensemble/RandomHom` packages the limit as a probability measure on
the homomorphism space with the defining property for every element of
the labelled algebra. -/

namespace FlagAlgebras.Core

open Filter Topology MeasureTheory
open scoped ENNReal

variable {S : Signature} [S.NullaryFree] {T : Type} [Fintype T]
variable {𝕋 : RelTheory S}

/-! ## Unlabelings, labeling factors and the downward ratio -/

section Downward

variable (σ : Model S T) [𝕋.IsType σ]

/-- The unlabeling of a finite `σ`-flag, through the canonical
representative. -/
noncomputable def FinFlag.unlabelFlag (F : FinFlag 𝕋 σ) :
    FinFlag 𝕋 (emptyType S) :=
  ⟨F.1, (Quotient.out F.2).unlabel.toFlag⟩

/-- Razborov's normalizing factor `q_σ(F)` of a finite flag. -/
noncomputable def FinFlag.qFactor (F : FinFlag 𝕋 σ) : ℚ :=
  labelingFactor (Quotient.out F.2).unlabel (Quotient.out F.2)

theorem FinFlag.qFactor_pos (F : FinFlag 𝕋 σ) : 0 < F.qFactor :=
  labelingFactor_self_pos _

/-- The unlabelled type: the unlabeling of the unit flag. -/
noncomputable def typeFlag : FinFlag 𝕋 (emptyType S) :=
  (1 : FinFlag 𝕋 σ).unlabelFlag

theorem downward_basisVector_quot (F : FinFlag 𝕋 σ) :
    downward (⟦basisVector F⟧ : FlagAlgebra 𝕋 σ)
      = (F.qFactor : ℝ) • (⟦basisVector F.unlabelFlag⟧ : FlagAlgebra 𝕋 (emptyType S)) := by
  rw [downward_quot, downwardVector_basisVector, downwardFinFlag, smul_quot]
  rfl

variable [𝕋.IsType (emptyType S)]

theorem positiveHom_downward_basisVector (φ₀ : PositiveHom 𝕋 (emptyType S))
    (F : FinFlag 𝕋 σ) :
    φ₀ (downward ⟦basisVector F⟧) = (F.qFactor : ℝ) * φ₀ ⟦basisVector F.unlabelFlag⟧ := by
  rw [downward_basisVector_quot, PositiveHom.map_smul]

/-- The downward ratio `φ₀(⟦F⟧_σ) / φ₀(⟦1_σ⟧_σ)`. -/
noncomputable def downwardRatio (φ₀ : PositiveHom 𝕋 (emptyType S)) (F : FinFlag 𝕋 σ) : ℝ :=
  φ₀ (downward ⟦basisVector F⟧) / φ₀ (downward (1 : FlagAlgebra 𝕋 σ))

theorem downwardRatio_eq (φ₀ : PositiveHom 𝕋 (emptyType S)) (F : FinFlag 𝕋 σ) :
    downwardRatio σ φ₀ F
      = (F.qFactor : ℝ) * φ₀ ⟦basisVector F.unlabelFlag⟧
        / (((1 : FinFlag 𝕋 σ).qFactor : ℝ) * φ₀ ⟦basisVector (typeFlag σ)⟧) := by
  unfold downwardRatio
  rw [positiveHom_downward_basisVector,
    show downward (1 : FlagAlgebra 𝕋 σ) = downward ⟦basisVector 1⟧ from rfl,
    positiveHom_downward_basisVector]
  rfl

/-- The unlabelled density of the type, evaluated at `φ₀`, is the value of
`⟦1_σ⟧_σ` up to the positive factor `q(1_σ)`. -/
theorem positiveHom_downward_one (φ₀ : PositiveHom 𝕋 (emptyType S)) :
    φ₀ (downward (1 : FlagAlgebra 𝕋 σ))
      = ((1 : FinFlag 𝕋 σ).qFactor : ℝ) * φ₀ ⟦basisVector (typeFlag σ)⟧ := by
  rw [show downward (1 : FlagAlgebra 𝕋 σ) = downward ⟦basisVector 1⟧ from rfl,
    positiveHom_downward_basisVector]
  rfl

end Downward

/-! ## Hosts along a realizing sequence -/

/-- The density of a labeled flag in the canonical representative of a
class is the class density. -/
lemma flagDensity_out_right {m n : ℕ} (X : LabeledFlag 𝕋 (emptyType S) (Fin m))
    (G : Flag 𝕋 (emptyType S) (Fin n)) :
    flagDensity X (Quotient.out G) = subflagDensity X.toFlag G := by
  rw [subflagDensity_out]
  obtain ⟨e⟩ : Nonempty (Quotient.out X.toFlag ≃ᶠ X) :=
    Quotient.exact (Quotient.out_eq X.toFlag)
  exact (flagDensity_congr_left e (Quotient.out G)).symm

section Realized

variable (σ : Model S T) [𝕋.IsType σ] [𝕋.IsType (emptyType S)]
variable (φ₀ : PositiveHom 𝕋 (emptyType S)) (Gs : ℕ → FinFlag 𝕋 (emptyType S))

/-- The canonical host representative of the `k`-th flag of the sequence. -/
noncomputable def hostAt (k : ℕ) : LabeledFlag 𝕋 (emptyType S) (Fin (Gs k).1) :=
  Quotient.out (Gs k).2

/-- The finite moment identity along the sequence, in class densities. -/
theorem integral_eval_hostAt (k : ℕ)
    (hne : (sigmaLabelings σ (hostAt Gs k)).Nonempty) (F : FinFlag 𝕋 σ)
    (hF : F.1 ≤ (Gs k).1) :
    ∫ a, (a : FinFlag 𝕋 σ → ℝ) F ∂(empiricalMeasure σ (hostAt Gs k))
      = (F.qFactor : ℝ) * ((subflagDensity F.unlabelFlag.2 (Gs k).2 : ℚ) : ℝ)
        / (((1 : FinFlag 𝕋 σ).qFactor : ℝ)
          * ((subflagDensity (typeFlag σ).2 (Gs k).2 : ℚ) : ℝ)) := by
  rw [integral_eval_empiricalMeasure σ _ hne F hF]
  unfold hostAt
  rw [flagDensity_out_right, flagDensity_out_right]
  push_cast
  rfl

/-- Along a realizing sequence of `φ₀` with positive type density, the
hosts eventually have `σ`-labelings. -/
theorem eventually_sigmaLabelings_nonempty (h : RealizedBy φ₀ Gs)
    (hσ : 0 < φ₀ ⟦basisVector (typeFlag σ)⟧) :
    ∀ᶠ k in atTop, (sigmaLabelings σ (hostAt Gs k)).Nonempty := by
  have hconv := h.2 (typeFlag σ)
  filter_upwards [hconv.eventually (lt_mem_nhds hσ)] with k hk
  rw [← Finset.card_pos, card_sigmaLabelings_eq σ (hostAt Gs k)]
  refine Nat.mul_pos ?_ (labelingCount_self_pos _)
  rcases Nat.eq_zero_or_pos
    (flagCount (Quotient.out (1 : FinFlag 𝕋 σ).2).unlabel (hostAt Gs k)) with h0 | h0
  · exfalso
    have hd : subflagDensity (typeFlag σ).2 (Gs k).2 = 0 := by
      show subflagDensity ((Quotient.out (1 : FinFlag 𝕋 σ).2).unlabel).toFlag (Gs k).2 = 0
      rw [← flagDensity_out_right, flagDensity]
      unfold hostAt at h0
      rw [h0]
      simp
    rw [hd] at hk
    simp at hk
  · exact h0

open Classical in
/-- The empirical measures of the hosts, as probability measures (a Dirac
mass at the unit profile stands in before the labelings exist). -/
noncomputable def empiricalSeq (k : ℕ) : ProbabilityMeasure (FlagDensitySpace 𝕋 σ) :=
  if hne : (sigmaLabelings σ (hostAt Gs k)).Nonempty then empiricalProb σ (hostAt Gs k) hne
  else ⟨Measure.dirac (FinFlag.toDensity (1 : FinFlag 𝕋 σ)), inferInstance⟩

theorem empiricalSeq_of_nonempty (k : ℕ)
    (hne : (sigmaLabelings σ (hostAt Gs k)).Nonempty) :
    empiricalSeq σ Gs k = empiricalProb σ (hostAt Gs k) hne := by
  unfold empiricalSeq
  rw [dif_pos hne]

/-! ## The weak limit -/

noncomputable instance : MetricSpace (ProbabilityMeasure (FlagDensitySpace 𝕋 σ)) :=
  TopologicalSpace.metrizableSpaceMetric _

/-- **Prokhorov**: the empirical measures have a weakly convergent
subsequence. -/
theorem exists_weakLimit :
    ∃ (s : ℕ → ℕ) (ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ)),
      StrictMono s ∧ Tendsto (fun k => empiricalSeq σ Gs (s k)) atTop (𝓝 ℙ) := by
  have hc : IsCompact (closure (Set.range (empiricalSeq σ Gs))) :=
    isCompact_closure_of_isTightMeasureSet IsTightMeasureSet.of_compactSpace
  obtain ⟨ℙ, -, s, hs, hlim⟩ :=
    hc.isSeqCompact fun k => subset_closure (Set.mem_range_self k)
  exact ⟨s, ℙ, hs, hlim⟩

/-- Coordinate evaluation as a bounded continuous function. -/
noncomputable def evalBCF (F : FinFlag 𝕋 σ) :
    BoundedContinuousFunction (FlagDensitySpace 𝕋 σ) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun a => (a : FinFlag 𝕋 σ → ℝ) F, FlagDensitySpace.continuous_eval F⟩

@[simp]
theorem evalBCF_apply (F : FinFlag 𝕋 σ) (a : FlagDensitySpace 𝕋 σ) :
    evalBCF σ F a = (a : FinFlag 𝕋 σ → ℝ) F :=
  rfl

/-- The empirical moments converge to the downward ratio. -/
theorem tendsto_integral_eval (h : RealizedBy φ₀ Gs)
    (hσ : 0 < φ₀ ⟦basisVector (typeFlag σ)⟧) (F : FinFlag 𝕋 σ) :
    Tendsto (fun k => ∫ a, (a : FinFlag 𝕋 σ → ℝ) F
        ∂(empiricalSeq σ Gs k : Measure (FlagDensitySpace 𝕋 σ)))
      atTop (𝓝 (downwardRatio σ φ₀ F)) := by
  have hev : ∀ᶠ k in atTop,
      ∫ a, (a : FinFlag 𝕋 σ → ℝ) F
          ∂(empiricalSeq σ Gs k : Measure (FlagDensitySpace 𝕋 σ))
        = (F.qFactor : ℝ) * ((subflagDensity F.unlabelFlag.2 (Gs k).2 : ℚ) : ℝ)
          / (((1 : FinFlag 𝕋 σ).qFactor : ℝ)
            * ((subflagDensity (typeFlag σ).2 (Gs k).2 : ℚ) : ℝ)) := by
    filter_upwards [eventually_sigmaLabelings_nonempty σ φ₀ Gs h hσ,
      h.1.eventually_ge_atTop F.1] with k hne hk
    rw [empiricalSeq_of_nonempty σ Gs k hne, empiricalProb_coe,
      integral_eval_hostAt σ Gs k hne F hk]
  rw [tendsto_congr' hev, downwardRatio_eq]
  refine Tendsto.div (tendsto_const_nhds.mul (h.2 F.unlabelFlag))
    (tendsto_const_nhds.mul (h.2 (typeFlag σ))) ?_
  exact mul_ne_zero (by exact_mod_cast (FinFlag.qFactor_pos σ 1).ne') hσ.ne'

/-- **The moments of the weak limit** are the downward ratios. -/
theorem integral_eval_weakLimit {s : ℕ → ℕ} (hs : StrictMono s)
    {ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ)}
    (hlim : Tendsto (fun k => empiricalSeq σ Gs (s k)) atTop (𝓝 ℙ))
    (h : RealizedBy φ₀ Gs) (hσ : 0 < φ₀ ⟦basisVector (typeFlag σ)⟧)
    (F : FinFlag 𝕋 σ) :
    ∫ a, (a : FinFlag 𝕋 σ → ℝ) F ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ))
      = downwardRatio σ φ₀ F := by
  have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) (evalBCF σ F)
  have h2 := (tendsto_integral_eval σ φ₀ Gs h hσ F).comp hs.tendsto_atTop
  exact tendsto_nhds_unique h1 h2

/-! ## The limit is concentrated on the homomorphism space -/

/-- A nonnegative bounded continuous function whose empirical integrals
tend to zero vanishes almost everywhere for the weak limit. -/
theorem ae_eq_zero_of_tendsto_integral {s : ℕ → ℕ}
    {ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ)}
    (hlim : Tendsto (fun k => empiricalSeq σ Gs (s k)) atTop (𝓝 ℙ))
    (g : BoundedContinuousFunction (FlagDensitySpace 𝕋 σ) ℝ) (hg : ∀ a, 0 ≤ g a)
    (hint : Tendsto (fun k => ∫ a, g a
        ∂(empiricalSeq σ Gs (s k) : Measure (FlagDensitySpace 𝕋 σ)))
      atTop (𝓝 0)) :
    ∀ᵐ (a : FlagDensitySpace 𝕋 σ) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ)), g a = 0 := by
  have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) g
  have h0 : ∫ a, g a ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ)) = 0 :=
    tendsto_nhds_unique h1 hint
  rw [integral_eq_zero_iff_of_nonneg hg (g.integrable _)] at h0
  filter_upwards [h0] with a ha
  exact ha

/-- The chain defect at `(F, ℓ)`, as a bounded continuous function. -/
noncomputable def chainBCF (F : FinFlag 𝕋 σ) (ℓ : ℕ) :
    BoundedContinuousFunction (FlagDensitySpace 𝕋 σ) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun a => |(a : FinFlag 𝕋 σ → ℝ) F
        - ∑ F' : FlagWithSize 𝕋 σ ℓ,
            ((subflagDensity F.2 F' : ℚ) : ℝ) * (a : FinFlag 𝕋 σ → ℝ) ⟨ℓ, F'⟩|,
      ((FlagDensitySpace.continuous_eval F).sub (continuous_finset_sum _ fun F' _ =>
        continuous_const.mul (FlagDensitySpace.continuous_eval ⟨ℓ, F'⟩))).abs⟩

@[simp]
theorem chainBCF_apply (F : FinFlag 𝕋 σ) (ℓ : ℕ) (a : FlagDensitySpace 𝕋 σ) :
    chainBCF σ F ℓ a
      = |(a : FinFlag 𝕋 σ → ℝ) F
          - ∑ F' : FlagWithSize 𝕋 σ ℓ,
              ((subflagDensity F.2 F' : ℚ) : ℝ) * (a : FinFlag 𝕋 σ → ℝ) ⟨ℓ, F'⟩| :=
  rfl

/-- The chain defect vanishes at every rooted profile of a large host. -/
theorem chainBCF_labelPoint {n : ℕ} (N : LabeledFlag 𝕋 (emptyType S) (Fin n))
    {θ : T ↪ Fin n} (h : IsSigmaLabeling σ N θ) (F : FinFlag 𝕋 σ) {ℓ : ℕ}
    (hℓ : F.1 ≤ ℓ) (hn : ℓ ≤ n) :
    chainBCF σ F ℓ (labelPoint σ N θ) = 0 := by
  rw [chainBCF_apply, abs_eq_zero, sub_eq_zero, labelPoint_apply σ N h]
  rw [Finset.sum_congr rfl fun F' (_ : F' ∈ Finset.univ) => by
    rw [labelPoint_apply σ N h]]
  have hchain := subflagDensity_chain (W' := Fin ℓ) (by simpa using hℓ)
    (by simpa using hn) F.2 (rootAt σ N θ h).toFlag
  rw [hchain]
  push_cast
  rfl

theorem integral_chainBCF_eq_zero (k : ℕ)
    (hne : (sigmaLabelings σ (hostAt Gs k)).Nonempty) (F : FinFlag 𝕋 σ)
    {ℓ : ℕ} (hℓ : F.1 ≤ ℓ) (hn : ℓ ≤ (Gs k).1) :
    ∫ a, chainBCF σ F ℓ a
        ∂(empiricalSeq σ Gs k : Measure (FlagDensitySpace 𝕋 σ)) = 0 := by
  rw [empiricalSeq_of_nonempty σ Gs k hne, empiricalProb_coe,
    integral_empiricalMeasure σ _ (chainBCF σ F ℓ).continuous]
  rw [Finset.sum_eq_zero fun θ hθ =>
    chainBCF_labelPoint σ _ (mem_sigmaLabelings.mp hθ) F hℓ hn, mul_zero]

/-- **The weak limit is almost surely chain closed.** -/
theorem ae_chainClosed {s : ℕ → ℕ} (hs : StrictMono s)
    {ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ)}
    (hlim : Tendsto (fun k => empiricalSeq σ Gs (s k)) atTop (𝓝 ℙ))
    (h : RealizedBy φ₀ Gs) (hσ : 0 < φ₀ ⟦basisVector (typeFlag σ)⟧) :
    ∀ᵐ (a : FlagDensitySpace 𝕋 σ) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ)),
      ChainClosed (a : FinFlag 𝕋 σ → ℝ) := by
  unfold ChainClosed
  rw [ae_all_iff]
  intro F
  rw [ae_all_iff]
  intro ℓ
  by_cases hℓ : F.1 ≤ ℓ
  · have hz := ae_eq_zero_of_tendsto_integral σ Gs hlim (chainBCF σ F ℓ)
      (fun a => abs_nonneg _) ?_
    · filter_upwards [hz] with a ha
      intro _
      rw [chainBCF_apply, abs_eq_zero, sub_eq_zero] at ha
      exact ha
    · have hev : ∀ᶠ k in atTop, ∫ a, chainBCF σ F ℓ a
          ∂(empiricalSeq σ Gs (s k) : Measure (FlagDensitySpace 𝕋 σ)) = 0 := by
        have hsz : Tendsto (fun k => (Gs (s k)).1) atTop atTop :=
          h.1.comp hs.tendsto_atTop
        filter_upwards [hs.tendsto_atTop.eventually
            (eventually_sigmaLabelings_nonempty σ φ₀ Gs h hσ), hsz.eventually_ge_atTop ℓ] with k hne hk
        exact integral_chainBCF_eq_zero σ Gs (s k) hne F hℓ hk
      exact tendsto_const_nhds.congr' (hev.mono fun k hk => hk.symm)
  · exact ae_of_all _ fun a hle => absurd hle hℓ

/-- The unit defect, as a bounded continuous function. -/
noncomputable def unitBCF : BoundedContinuousFunction (FlagDensitySpace 𝕋 σ) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun a => |(a : FinFlag 𝕋 σ → ℝ) 1 - 1|,
      ((FlagDensitySpace.continuous_eval 1).sub continuous_const).abs⟩

theorem unitBCF_labelPoint {n : ℕ} (N : LabeledFlag 𝕋 (emptyType S) (Fin n))
    {θ : T ↪ Fin n} (h : IsSigmaLabeling σ N θ) :
    unitBCF σ (labelPoint σ N θ) = 0 := by
  show |(labelPoint σ N θ : FinFlag 𝕋 σ → ℝ) 1 - 1| = 0
  rw [abs_eq_zero, sub_eq_zero, labelPoint_apply σ N h, finFlag_one_snd,
    subflagDensity_unitFlag]
  norm_num

/-- **The weak limit is almost surely normalised.** -/
theorem ae_unit {s : ℕ → ℕ} (hs : StrictMono s)
    {ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ)}
    (hlim : Tendsto (fun k => empiricalSeq σ Gs (s k)) atTop (𝓝 ℙ))
    (h : RealizedBy φ₀ Gs) (hσ : 0 < φ₀ ⟦basisVector (typeFlag σ)⟧) :
    ∀ᵐ (a : FlagDensitySpace 𝕋 σ) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ)),
      (a : FinFlag 𝕋 σ → ℝ) 1 = 1 := by
  have hz := ae_eq_zero_of_tendsto_integral σ Gs hlim (unitBCF σ)
    (fun a => abs_nonneg _) ?_
  · filter_upwards [hz] with a ha
    have : |(a : FinFlag 𝕋 σ → ℝ) 1 - 1| = 0 := ha
    rw [abs_eq_zero, sub_eq_zero] at this
    exact this
  · have hev : ∀ᶠ k in atTop, ∫ a, unitBCF σ a
        ∂(empiricalSeq σ Gs (s k) : Measure (FlagDensitySpace 𝕋 σ)) = 0 := by
      filter_upwards [hs.tendsto_atTop.eventually
          (eventually_sigmaLabelings_nonempty σ φ₀ Gs h hσ)] with k hne
      rw [empiricalSeq_of_nonempty σ Gs (s k) hne, empiricalProb_coe,
        integral_empiricalMeasure σ _ (unitBCF σ).continuous]
      rw [Finset.sum_eq_zero fun θ hθ =>
        unitBCF_labelPoint σ _ (mem_sigmaLabelings.mp hθ), mul_zero]
    exact tendsto_const_nhds.congr' (hev.mono fun k hk => hk.symm)

/-- The product defect at `(F₁, F₂)`, as a bounded continuous function. -/
noncomputable def mulBCF (F₁ F₂ : FinFlag 𝕋 σ) :
    BoundedContinuousFunction (FlagDensitySpace 𝕋 σ) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun a => |(∑ G : FlagWithSize 𝕋 σ (F₁.1 + F₂.1 - Fintype.card T),
          ((subflagPairDensity F₁.2 F₂.2 G : ℚ) : ℝ)
            * (a : FinFlag 𝕋 σ → ℝ) ⟨F₁.1 + F₂.1 - Fintype.card T, G⟩)
        - (a : FinFlag 𝕋 σ → ℝ) F₁ * (a : FinFlag 𝕋 σ → ℝ) F₂|,
      ((continuous_finset_sum _ fun G _ =>
        continuous_const.mul (FlagDensitySpace.continuous_eval _)).sub
          ((FlagDensitySpace.continuous_eval F₁).mul
            (FlagDensitySpace.continuous_eval F₂))).abs⟩

@[simp]
theorem mulBCF_apply (F₁ F₂ : FinFlag 𝕋 σ) (a : FlagDensitySpace 𝕋 σ) :
    mulBCF σ F₁ F₂ a
      = |(∑ G : FlagWithSize 𝕋 σ (F₁.1 + F₂.1 - Fintype.card T),
            ((subflagPairDensity F₁.2 F₂.2 G : ℚ) : ℝ)
              * (a : FinFlag 𝕋 σ → ℝ) ⟨F₁.1 + F₂.1 - Fintype.card T, G⟩)
          - (a : FinFlag 𝕋 σ → ℝ) F₁ * (a : FinFlag 𝕋 σ → ℝ) F₂| :=
  rfl

/-- The product defect at a rooted profile of an `n`-vertex host is at
most `(|F₁| - |σ|)(|F₂| - |σ|) / (n - |σ|)`. -/
theorem mulBCF_labelPoint_le {n : ℕ} (N : LabeledFlag 𝕋 (emptyType S) (Fin n))
    {θ : T ↪ Fin n} (h : IsSigmaLabeling σ N θ) (F₁ F₂ : FinFlag 𝕋 σ)
    (hn : F₁.1 + F₂.1 - Fintype.card T ≤ n) (hn' : Fintype.card T < n) :
    mulBCF σ F₁ F₂ (labelPoint σ N θ)
      ≤ (((F₁.1 - Fintype.card T) * (F₂.1 - Fintype.card T) : ℕ) : ℝ)
          / ((n - Fintype.card T : ℕ) : ℝ) := by
  have hk₁ := finFlag_size_ge F₁
  have hk₂ := finFlag_size_ge F₂
  rw [mulBCF_apply, labelPoint_apply σ N h, labelPoint_apply σ N h]
  rw [Finset.sum_congr rfl fun G (_ : G ∈ Finset.univ) => by
    rw [labelPoint_apply σ N h]]
  have hchain := subflagPairDensity_chain_host
    (W' := Fin (F₁.1 + F₂.1 - Fintype.card T))
    (by simp only [Fintype.card_fin]; omega) (by simpa using hn) F₁.2 F₂.2
    (rootAt σ N θ h).toFlag
  have hsum : (∑ G : FlagWithSize 𝕋 σ (F₁.1 + F₂.1 - Fintype.card T),
      ((subflagPairDensity F₁.2 F₂.2 G : ℚ) : ℝ)
        * ((subflagDensity G (rootAt σ N θ h).toFlag : ℚ) : ℝ))
      = ((subflagPairDensity F₁.2 F₂.2 (rootAt σ N θ h).toFlag : ℚ) : ℝ) := by
    rw [hchain]
    push_cast
    rfl
  rw [hsum]
  exact abs_subflagPairDensity_sub_mul_le F₁.2 F₂.2 (rootAt σ N θ h).toFlag
    (by omega) hn'

/-- **The weak limit is almost surely multiplicatively closed.** -/
theorem ae_mulClosed {s : ℕ → ℕ} (hs : StrictMono s)
    {ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ)}
    (hlim : Tendsto (fun k => empiricalSeq σ Gs (s k)) atTop (𝓝 ℙ))
    (h : RealizedBy φ₀ Gs) (hσ : 0 < φ₀ ⟦basisVector (typeFlag σ)⟧) :
    ∀ᵐ (a : FlagDensitySpace 𝕋 σ) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ)),
      MulClosed (a : FinFlag 𝕋 σ → ℝ) := by
  unfold MulClosed
  rw [ae_all_iff]
  intro F₁
  rw [ae_all_iff]
  intro F₂
  have hz := ae_eq_zero_of_tendsto_integral σ Gs hlim (mulBCF σ F₁ F₂)
    (fun a => abs_nonneg _) ?_
  · filter_upwards [hz] with a ha
    rw [mulBCF_apply, abs_eq_zero, sub_eq_zero] at ha
    exact ha
  · have hsz : Tendsto (fun k => (Gs (s k)).1) atTop atTop :=
      h.1.comp hs.tendsto_atTop
    have hszN : Tendsto (fun k => (Gs (s k)).1 - Fintype.card T) atTop atTop :=
      (tendsto_sub_atTop_nat (Fintype.card T)).comp hsz
    have hszR : Tendsto (fun k => (((Gs (s k)).1 - Fintype.card T : ℕ) : ℝ))
        atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hszN
    have hzero : Tendsto
        (fun k => (((F₁.1 - Fintype.card T) * (F₂.1 - Fintype.card T) : ℕ) : ℝ)
          / (((Gs (s k)).1 - Fintype.card T : ℕ) : ℝ)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hszR
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero ?_ ?_
    · exact Eventually.of_forall fun k =>
        integral_nonneg fun a => abs_nonneg _
    · filter_upwards [hs.tendsto_atTop.eventually
          (eventually_sigmaLabelings_nonempty σ φ₀ Gs h hσ),
        hsz.eventually_ge_atTop (F₁.1 + F₂.1 - Fintype.card T),
        hsz.eventually_ge_atTop (Fintype.card T + 1)] with k hne hk hk1
      rw [empiricalSeq_of_nonempty σ Gs (s k) hne, empiricalProb_coe,
        integral_empiricalMeasure σ _ (mulBCF σ F₁ F₂).continuous]
      have hcard : (0 : ℝ) < (sigmaLabelings σ (hostAt Gs (s k))).card := by
        exact_mod_cast Finset.card_pos.mpr hne
      rw [inv_mul_le_iff₀ hcard]
      calc ∑ θ ∈ sigmaLabelings σ (hostAt Gs (s k)), mulBCF σ F₁ F₂ (labelPoint σ _ θ)
          ≤ ∑ _θ ∈ sigmaLabelings σ (hostAt Gs (s k)),
              (((F₁.1 - Fintype.card T) * (F₂.1 - Fintype.card T) : ℕ) : ℝ)
                / (((Gs (s k)).1 - Fintype.card T : ℕ) : ℝ) :=
            Finset.sum_le_sum fun θ hθ =>
              mulBCF_labelPoint_le σ _ (mem_sigmaLabelings.mp hθ) F₁ F₂ hk (by omega)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **The weak limit is concentrated on the homomorphism space.** -/
theorem ae_mem_positiveHomSpace {s : ℕ → ℕ} (hs : StrictMono s)
    {ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ)}
    (hlim : Tendsto (fun k => empiricalSeq σ Gs (s k)) atTop (𝓝 ℙ))
    (h : RealizedBy φ₀ Gs) (hσ : 0 < φ₀ ⟦basisVector (typeFlag σ)⟧) :
    ∀ᵐ (a : FlagDensitySpace 𝕋 σ) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ)),
      a ∈ PositiveHomSpace 𝕋 σ := by
  filter_upwards [ae_chainClosed σ φ₀ Gs hs hlim h hσ, ae_mulClosed σ φ₀ Gs hs hlim h hσ,
    ae_unit σ φ₀ Gs hs hlim h hσ] with a hC hM h1
  rw [positiveHomSpace_eq]
  exact ⟨hC, hM, h1⟩

end Realized

end FlagAlgebras.Core
