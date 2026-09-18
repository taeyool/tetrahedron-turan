import LeanFlagAlgebras.Core.Ensemble.DensitySpace

/-! # Core: the empirical labeling measure of a finite host

The finite level of Razborov's random extension. An unlabelled host `N`
on `n` vertices and a type `σ` determine the set of *`σ`-labelings* of
`N`: the injections of the label set that induce a copy of `σ`. Rooting
`N` at a uniformly random labeling and reading off the density profile of
the rooted flag gives a probability measure on the profile space, the
*empirical labeling measure* `empiricalMeasure σ N`, a uniform average of
Dirac masses.

Its defining moment identity is the finite form of Razborov's Theorem 3.5:
the expected density of a `σ`-flag `F` under the empirical measure is the
downward ratio

  `q(F) · p(F|₀, N) / (q(1_σ) · p(σ|₀, N))`,

the density of the unlabeling of `F` weighted by its labeling factor,
normalised by the same quantity for the unit flag. The proof groups the
labelings by the isomorphism class of the rooted flag (`sum_sigmaLabelings`),
applies the averaging identity `flagCount_unlabel_mul_labelingCount` of
`Core/Downward` to `F` and to the unit flag, and closes with one binomial
identity. Along a realizing sequence of hosts the ratio converges to
`φ₀(⟦F⟧_σ) / φ₀(⟦1_σ⟧_σ)`, which is how the limit measure of
`Core/Ensemble/Extension` acquires its moments. -/

namespace FlagAlgebras.Core

open Finset Filter Topology MeasureTheory
open scoped ENNReal

variable {S : Signature} [S.NullaryFree] {T V : Type} [Fintype T]
variable {𝕋 : RelTheory S}

/-! ## `σ`-labelings and rooting -/

/-- `θ` is a `σ`-labeling of the unlabelled host `N`: an injection of the
label set under which the interpretations agree with `σ`, that is, an
induced copy of the type. -/
def IsSigmaLabeling (σ : Model S T) (N : LabeledFlag 𝕋 (emptyType S) V)
    (θ : T ↪ V) : Prop :=
  ∀ (r : S.Rel) (f : Fin (S.ar r) → T),
    N.toModel.interp r (⇑θ ∘ f) ↔ σ.interp r f

/-- The host rooted at a `σ`-labeling. -/
def rootAt (σ : Model S T) (N : LabeledFlag 𝕋 (emptyType S) V) (θ : T ↪ V)
    (h : IsSigmaLabeling σ N θ) : LabeledFlag 𝕋 σ V :=
  ⟨N.toModel, N.mem, ⟨θ, h⟩⟩

open Classical in
/-- The `σ`-labelings of a host. -/
noncomputable def sigmaLabelings (σ : Model S T) [Fintype V]
    (N : LabeledFlag 𝕋 (emptyType S) V) : Finset (T ↪ V) :=
  Finset.univ.filter (IsSigmaLabeling σ N)

lemma mem_sigmaLabelings [Fintype V] {σ : Model S T}
    {N : LabeledFlag 𝕋 (emptyType S) V} {θ : T ↪ V} :
    θ ∈ sigmaLabelings σ N ↔ IsSigmaLabeling σ N θ := by
  classical
  unfold sigmaLabelings
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- A labeling realizing any `σ`-flag on the host is a `σ`-labeling. -/
lemma IsFlagLabeling.isSigmaLabeling {σ : Model S T} {U : Type}
    {N : LabeledFlag 𝕋 (emptyType S) V} {F : LabeledFlag 𝕋 σ U} {θ : T ↪ V}
    (h : IsFlagLabeling N F θ) : IsSigmaLabeling σ N θ := by
  obtain ⟨h', -⟩ := h
  exact h'

/-- A `σ`-labeling realizes the class `F'` exactly when rooting at it
produces `F'`. -/
lemma mem_flagLabelings_iff_toFlag_eq [Fintype V] {σ : Model S T}
    {N : LabeledFlag 𝕋 (emptyType S) V} {θ : T ↪ V}
    (h : IsSigmaLabeling σ N θ) (F' : Flag 𝕋 σ V) :
    θ ∈ flagLabelings N (Quotient.out F') ↔ (rootAt σ N θ h).toFlag = F' := by
  rw [mem_flagLabelings]
  constructor
  · rintro ⟨h', ⟨e⟩⟩
    show Quotient.mk _ (rootAt σ N θ h) = F'
    rw [← Quotient.out_eq F']
    exact Quotient.sound ⟨e⟩
  · intro heq
    refine ⟨h, ?_⟩
    unfold LabeledFlag.toFlag at heq
    exact Quotient.exact (heq.trans (Quotient.out_eq F').symm)

open Classical in
/-- The `σ`-labelings are partitioned by the class of the rooted flag. -/
lemma sigmaLabelings_eq_biUnion [Fintype V] (σ : Model S T)
    (N : LabeledFlag 𝕋 (emptyType S) V) :
    sigmaLabelings σ N
      = (Finset.univ : Finset (Flag 𝕋 σ V)).biUnion
          fun F' => flagLabelings N (Quotient.out F') := by
  ext θ
  rw [mem_sigmaLabelings, Finset.mem_biUnion]
  constructor
  · intro h
    exact ⟨(rootAt σ N θ h).toFlag, Finset.mem_univ _,
      (mem_flagLabelings_iff_toFlag_eq h _).mpr rfl⟩
  · rintro ⟨F', -, hθ⟩
    exact (mem_flagLabelings.mp hθ).isSigmaLabeling

lemma pairwiseDisjoint_flagLabelings [Fintype V] (σ : Model S T)
    (N : LabeledFlag 𝕋 (emptyType S) V) :
    ((Finset.univ : Finset (Flag 𝕋 σ V)) : Set (Flag 𝕋 σ V)).PairwiseDisjoint
      fun F' => flagLabelings N (Quotient.out F') := by
  intro F₁ _ F₂ _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro θ h₁ h₂
  have hs := (mem_flagLabelings.mp h₁).isSigmaLabeling
  exact hne (((mem_flagLabelings_iff_toFlag_eq hs F₁).mp h₁).symm.trans
    ((mem_flagLabelings_iff_toFlag_eq hs F₂).mp h₂))

open Classical in
/-- **Splitting a sum over `σ`-labelings by the rooted class.** A quantity
depending only on the class of the rooted flag sums to the class-wise
labeling counts against its values. -/
lemma sum_sigmaLabelings [Fintype V] (σ : Model S T)
    (N : LabeledFlag 𝕋 (emptyType S) V) (G : (T ↪ V) → ℝ)
    (g : Flag 𝕋 σ V → ℝ)
    (hG : ∀ θ (h : IsSigmaLabeling σ N θ), G θ = g (rootAt σ N θ h).toFlag) :
    ∑ θ ∈ sigmaLabelings σ N, G θ
      = ∑ F' : Flag 𝕋 σ V, (labelingCount N (Quotient.out F') : ℝ) * g F' := by
  rw [sigmaLabelings_eq_biUnion,
    Finset.sum_biUnion (pairwiseDisjoint_flagLabelings σ N)]
  refine Finset.sum_congr rfl fun F' _ => ?_
  rw [labelingCount, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun θ hθ => ?_
  have hs := (mem_flagLabelings.mp hθ).isSigmaLabeling
  rw [hG θ hs, (mem_flagLabelings_iff_toFlag_eq hs F').mp hθ, Nat.cast_one,
    one_mul]

open Classical in
/-- The number of `σ`-labelings is the sum of the class-wise counts. -/
lemma card_sigmaLabelings [Fintype V] (σ : Model S T)
    (N : LabeledFlag 𝕋 (emptyType S) V) :
    (sigmaLabelings σ N).card
      = ∑ F' : Flag 𝕋 σ V, labelingCount N (Quotient.out F') := by
  rw [sigmaLabelings_eq_biUnion,
    Finset.card_biUnion (pairwiseDisjoint_flagLabelings σ N)]
  rfl

/-! ## The averaging identities in density form -/

section IsType

variable (σ : Model S T) [𝕋.IsType σ]

/-- The unit class's representative has count one in every `σ`-flag. -/
lemma flagCount_unit_out {W : Type} [Fintype W] (F' : LabeledFlag 𝕋 σ W) :
    flagCount (Quotient.out (1 : FinFlag 𝕋 σ).2) F' = 1 := by
  have h1 : Nonempty (Quotient.out (1 : FinFlag 𝕋 σ).2
      ≃ᶠ unitFlag 𝕋 σ RelTheory.IsType.mem) :=
    Quotient.exact (Quotient.out_eq (1 : FinFlag 𝕋 σ).2)
  obtain ⟨e⟩ := h1
  rw [flagCount_congr_left (e.trans (unitFlagIso 𝕋 σ _).symm) F',
    flagCount_ofType]

/-- The number of `σ`-labelings of a host, through the averaging identity
for the unit flag. -/
lemma card_sigmaLabelings_eq {n : ℕ} (N : LabeledFlag 𝕋 (emptyType S) (Fin n)) :
    (sigmaLabelings σ N).card
      = flagCount (Quotient.out (1 : FinFlag 𝕋 σ).2).unlabel N
        * labelingCount (Quotient.out (1 : FinFlag 𝕋 σ).2).unlabel
            (Quotient.out (1 : FinFlag 𝕋 σ).2) := by
  rw [card_sigmaLabelings, flagCount_unlabel_mul_labelingCount]
  refine Finset.sum_congr rfl fun F' _ => ?_
  rw [flagCount_unit_out σ, mul_one]

/-- The averaging identity for `F`, in density form. -/
lemma sum_labelingCount_mul_subflagDensity {n : ℕ}
    (N : LabeledFlag 𝕋 (emptyType S) (Fin n)) (F : FinFlag 𝕋 σ) :
    ∑ F' : Flag 𝕋 σ (Fin n),
        (labelingCount N (Quotient.out F') : ℚ) * subflagDensity F.2 F'
      = ((flagCount (Quotient.out F.2).unlabel N
          * labelingCount (Quotient.out F.2).unlabel (Quotient.out F.2) : ℕ) : ℚ)
        / ((n - Fintype.card T).choose (F.1 - Fintype.card T) : ℚ) := by
  rw [flagCount_unlabel_mul_labelingCount, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun F' _ => ?_
  rw [subflagDensity_out, flagDensity]
  simp only [Fintype.card_fin]
  push_cast
  ring

/-! ## The empirical labeling measure -/

variable {n : ℕ}

open Classical in
/-- The density profile of the host rooted at `θ` (and a dummy point off
the `σ`-labelings). -/
noncomputable def labelPoint (N : LabeledFlag 𝕋 (emptyType S) (Fin n))
    (θ : T ↪ Fin n) : FlagDensitySpace 𝕋 σ :=
  if h : IsSigmaLabeling σ N θ then FinFlag.toDensity ⟨n, (rootAt σ N θ h).toFlag⟩
  else FinFlag.toDensity 1

lemma labelPoint_apply (N : LabeledFlag 𝕋 (emptyType S) (Fin n)) {θ : T ↪ Fin n}
    (h : IsSigmaLabeling σ N θ) (F : FinFlag 𝕋 σ) :
    (labelPoint σ N θ : FinFlag 𝕋 σ → ℝ) F
      = ((subflagDensity F.2 (rootAt σ N θ h).toFlag : ℚ) : ℝ) := by
  unfold labelPoint
  rw [dif_pos h]
  rfl

/-- **The empirical labeling measure**: root the host at a uniformly random
`σ`-labeling and record the profile of the rooted flag. -/
noncomputable def empiricalMeasure (N : LabeledFlag 𝕋 (emptyType S) (Fin n)) :
    Measure (FlagDensitySpace 𝕋 σ) :=
  ((sigmaLabelings σ N).card : ℝ≥0∞)⁻¹
    • ∑ θ ∈ sigmaLabelings σ N, Measure.dirac (labelPoint σ N θ)

theorem empiricalMeasure_univ (N : LabeledFlag 𝕋 (emptyType S) (Fin n))
    (hne : (sigmaLabelings σ N).Nonempty) :
    empiricalMeasure σ N Set.univ = 1 := by
  rw [empiricalMeasure, Measure.smul_apply, Measure.finset_sum_apply]
  simp only [Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (by exact_mod_cast (Finset.card_pos.mpr hne).ne') (ENNReal.natCast_ne_top _)

theorem empiricalMeasure_isProbabilityMeasure
    (N : LabeledFlag 𝕋 (emptyType S) (Fin n))
    (hne : (sigmaLabelings σ N).Nonempty) :
    IsProbabilityMeasure (empiricalMeasure σ N) :=
  ⟨empiricalMeasure_univ σ N hne⟩

/-- The empirical measure as a probability measure. -/
noncomputable def empiricalProb (N : LabeledFlag 𝕋 (emptyType S) (Fin n))
    (hne : (sigmaLabelings σ N).Nonempty) :
    ProbabilityMeasure (FlagDensitySpace 𝕋 σ) :=
  ⟨empiricalMeasure σ N, empiricalMeasure_isProbabilityMeasure σ N hne⟩

@[simp]
theorem empiricalProb_coe (N : LabeledFlag 𝕋 (emptyType S) (Fin n))
    (hne : (sigmaLabelings σ N).Nonempty) :
    (empiricalProb σ N hne : Measure (FlagDensitySpace 𝕋 σ)) = empiricalMeasure σ N :=
  rfl

/-- Integrals against the empirical measure are labeling averages. -/
theorem integral_empiricalMeasure (N : LabeledFlag 𝕋 (emptyType S) (Fin n))
    {g : FlagDensitySpace 𝕋 σ → ℝ} (hg : Continuous g) :
    ∫ a, g a ∂(empiricalMeasure σ N)
      = ((sigmaLabelings σ N).card : ℝ)⁻¹
          * ∑ θ ∈ sigmaLabelings σ N, g (labelPoint σ N θ) := by
  rw [empiricalMeasure, integral_smul_measure,
    integral_finset_sum_measure fun θ _ =>
      integrable_dirac' hg.stronglyMeasurable enorm_lt_top]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun θ _ =>
    integral_dirac' g (labelPoint σ N θ) hg.stronglyMeasurable

/-- The binomial identity behind the moment identity: with `k ≤ m ≤ n`,
`m^{\underline k} · C(n,m) = C(n,k) · k! · C(n-k, m-k)`. -/
lemma descFactorial_mul_choose_eq {n m k : ℕ} (hkm : k ≤ m) :
    m.descFactorial k * n.choose m
      = n.choose k * k.descFactorial k * (n - k).choose (m - k) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose m k,
    Nat.descFactorial_eq_factorial_mul_choose k k, Nat.choose_self, mul_one]
  have h := Nat.choose_mul (n := n) (k := m) (s := k) hkm
  calc k.factorial * m.choose k * n.choose m
      = k.factorial * (n.choose m * m.choose k) := by ring
    _ = k.factorial * (n.choose k * (n - k).choose (m - k)) := by rw [h]
    _ = n.choose k * k.factorial * (n - k).choose (m - k) := by ring

/-- The rational algebra of the moment identity. -/
lemma moment_algebra {A B D E c₁ cm ck dm dk : ℚ} (hE : E ≠ 0) (hD : D ≠ 0)
    (hc₁ : c₁ ≠ 0) (hcm : cm ≠ 0) (hdm : dm ≠ 0) (hdk : dk ≠ 0) (hck : ck ≠ 0)
    (hnat : dm * cm = ck * dk * c₁) :
    (E * D)⁻¹ * (A * B / c₁) = (B / dm * (A / cm)) / (D / dk * (E / ck)) := by
  have hc₁' : c₁ = dm * cm / (ck * dk) := by
    rw [eq_div_iff (mul_ne_zero hck hdk)]
    linear_combination -hnat
  subst hc₁'
  field_simp

/-- **The moment identity of the empirical measure** (the finite form of
Razborov's Theorem 3.5): the expected density of `F` under the empirical
labeling measure of `N` is the downward ratio
`q(F) p(F|₀, N) / (q(1_σ) p(σ|₀, N))`. -/
theorem integral_eval_empiricalMeasure (N : LabeledFlag 𝕋 (emptyType S) (Fin n))
    (hne : (sigmaLabelings σ N).Nonempty) (F : FinFlag 𝕋 σ) (hF : F.1 ≤ n) :
    ∫ a, (a : FinFlag 𝕋 σ → ℝ) F ∂(empiricalMeasure σ N)
      = ((labelingFactor (Quotient.out F.2).unlabel (Quotient.out F.2)
            * flagDensity (Quotient.out F.2).unlabel N : ℚ) : ℝ)
        / ((labelingFactor (Quotient.out (1 : FinFlag 𝕋 σ).2).unlabel
              (Quotient.out (1 : FinFlag 𝕋 σ).2)
            * flagDensity (Quotient.out (1 : FinFlag 𝕋 σ).2).unlabel N : ℚ) : ℝ) := by
  have hkm : Fintype.card T ≤ F.1 := finFlag_size_ge F
  rw [integral_empiricalMeasure σ N (FlagDensitySpace.continuous_eval F),
    sum_sigmaLabelings σ N _ (fun F' => ((subflagDensity F.2 F' : ℚ) : ℝ))
      (fun θ h => labelPoint_apply σ N h F)]
  have hsumR : (∑ F' : Flag 𝕋 σ (Fin n),
      (labelingCount N (Quotient.out F') : ℝ) * ((subflagDensity F.2 F' : ℚ) : ℝ))
      = ((∑ F' : Flag 𝕋 σ (Fin n),
          (labelingCount N (Quotient.out F') : ℚ) * subflagDensity F.2 F' : ℚ) : ℝ) := by
    push_cast
    rfl
  rw [hsumR, sum_labelingCount_mul_subflagDensity σ N F,
    show ((sigmaLabelings σ N).card : ℝ) = (((sigmaLabelings σ N).card : ℚ) : ℝ) by
      norm_cast,
    card_sigmaLabelings_eq σ N, ← Rat.cast_inv, ← Rat.cast_mul, ← Rat.cast_div]
  congr 1
  -- the rational identity
  have hcard : (sigmaLabelings σ N).card ≠ 0 := (Finset.card_pos.mpr hne).ne'
  rw [card_sigmaLabelings_eq σ N] at hcard
  have hE : (flagCount (Quotient.out (1 : FinFlag 𝕋 σ).2).unlabel N : ℚ) ≠ 0 := by
    exact_mod_cast left_ne_zero_of_mul hcard
  have hD : (labelingCount (Quotient.out (1 : FinFlag 𝕋 σ).2).unlabel
      (Quotient.out (1 : FinFlag 𝕋 σ).2) : ℚ) ≠ 0 := by
    exact_mod_cast right_ne_zero_of_mul hcard
  have hc₁ : ((n - Fintype.card T).choose (F.1 - Fintype.card T) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.sub_le_sub_right hF _)).ne'
  have hcm : (n.choose F.1 : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hF).ne'
  have hdm : (F.1.descFactorial (Fintype.card T) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hkm).ne'
  have hdk : ((Fintype.card T).descFactorial (Fintype.card T) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr le_rfl).ne'
  have hck : (n.choose (Fintype.card T) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hkm.trans hF)).ne'
  have hnat : (F.1.descFactorial (Fintype.card T) : ℚ) * (n.choose F.1 : ℚ)
      = (n.choose (Fintype.card T) : ℚ)
        * ((Fintype.card T).descFactorial (Fintype.card T) : ℚ)
        * ((n - Fintype.card T).choose (F.1 - Fintype.card T) : ℚ) := by
    exact_mod_cast descFactorial_mul_choose_eq (n := n) hkm
  unfold labelingFactor flagDensity
  simp only [Fintype.card_fin, Fintype.card_embedding_eq, Nat.sub_zero, Nat.cast_mul]
  exact moment_algebra hE hD hc₁ hcm hdm hdk hck hnat

end IsType

end FlagAlgebras.Core
