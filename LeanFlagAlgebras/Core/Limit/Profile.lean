import LeanFlagAlgebras.Core.PositiveHom
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Core: density profiles and the homomorphisms they determine

A positive homomorphism is determined by its *profile*, the function
`F ↦ φ ⟦F⟧` on finite flags. This file characterises, theory-generically,
which profiles arise: those that are chain closed (they satisfy every
averaging relation exactly), multiplicative through pair densities at the
product size, normalised at the unit flag, and nonnegative. Such a
profile extends linearly to flag vectors, kills the `ZeroSpace`, descends
to the quotient, and the descent is a positive homomorphism
(`homOfProfile`); conversely every homomorphism's profile has the four
properties. This is the algebraic half of Razborov's Theorem 3.3, stated
without any sequence: the limit constructions (`Core/Limit/Realize`) only
have to verify the four properties along a realizing sequence, and the
random-extension measures (`Core/Ensemble`) only have to show that they
hold almost surely.

The definitions generalise `Core/Examples/TetrahedronLimitLin` and
`TetrahedronLimitHom` from the tetrahedron-free theory over the empty
type to an arbitrary theory and type. -/

namespace FlagAlgebras.Core

variable {S : Signature} {T : Type} [Fintype T]
variable {𝕋 : RelTheory S} {σ : Model S T}

/-! ## The four properties of a profile -/

/-- A profile is *chain closed* when it satisfies every averaging
relation: its value at a flag is the density-weighted sum of its values
at any larger size. -/
def ChainClosed (L : FinFlag 𝕋 σ → ℝ) : Prop :=
  ∀ (F : FinFlag 𝕋 σ) (ℓ : ℕ), F.1 ≤ ℓ →
    L F = ∑ F' : FlagWithSize 𝕋 σ ℓ,
      ((subflagDensity F.2 F' : ℚ) : ℝ) * L ⟨ℓ, F'⟩

/-- A profile is *multiplicatively closed* when the pair-density expansion
of a product of two flags, at the product size `|F₁| + |F₂| - |σ|`,
evaluates to the product of the values. -/
def MulClosed (L : FinFlag 𝕋 σ → ℝ) : Prop :=
  ∀ F₁ F₂ : FinFlag 𝕋 σ,
    (∑ G : FlagWithSize 𝕋 σ (F₁.1 + F₂.1 - Fintype.card T),
      ((subflagPairDensity F₁.2 F₂.2 G : ℚ) : ℝ)
        * L ⟨F₁.1 + F₂.1 - Fintype.card T, G⟩)
      = L F₁ * L F₂

/-! ## Linear extension and descent to the quotient -/

/-- The linear extension of a profile to flag vectors. -/
noncomputable def limitLin (L : FinFlag 𝕋 σ → ℝ) :
    FlagVector 𝕋 σ →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ L

@[simp]
lemma limitLin_basis (L : FinFlag 𝕋 σ → ℝ) (F : FinFlag 𝕋 σ) :
    limitLin L (basisVector F) = L F := by
  rw [limitLin, basisVector, Finsupp.linearCombination_single, one_smul]

/-- The linear extension as a support sum. -/
lemma limitLin_apply (L : FinFlag 𝕋 σ → ℝ) (f : FlagVector 𝕋 σ) :
    limitLin L f = ∑ F ∈ f.support, f F * L F := by
  rw [limitLin, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun F _ => smul_eq_mul _ _

/-- A chain-closed profile kills every generator of the zero space. -/
lemma limitLin_zeroElement {L : FinFlag 𝕋 σ → ℝ} (hC : ChainClosed L)
    (F : FinFlag 𝕋 σ) (ℓ : ℕ) (hFℓ : F.1 ≤ ℓ) :
    limitLin L (zeroElement F ℓ) = 0 := by
  rw [zeroElement, map_sub, limitLin_basis, flagExpansion, map_sum]
  rw [Finset.sum_congr rfl fun F' (_ : F' ∈ Finset.univ) => by
    rw [map_smul, limitLin_basis]]
  rw [hC F ℓ hFℓ, sub_eq_zero]
  rfl

/-- A chain-closed profile kills the whole `ZeroSpace`. -/
lemma limitLin_zeroSpace {L : FinFlag 𝕋 σ → ℝ} (hC : ChainClosed L)
    {k : FlagVector 𝕋 σ} (hk : k ∈ ZeroSpace 𝕋 σ) :
    limitLin L k = 0 := by
  have hle : ZeroSpace 𝕋 σ ≤ LinearMap.ker (limitLin L) := by
    rw [ZeroSpace, Submodule.span_le]
    rintro x ⟨F, ℓ, hFℓ, rfl⟩
    exact LinearMap.mem_ker.mpr (limitLin_zeroElement hC F ℓ hFℓ)
  exact LinearMap.mem_ker.mp (hle hk)

/-- The descent of a chain-closed profile to the flag algebra:
flag-equivalent vectors differ by an element of `ZeroSpace`, which the
linear extension kills. -/
noncomputable def limitQuot {L : FinFlag 𝕋 σ → ℝ} (hC : ChainClosed L) :
    FlagAlgebra 𝕋 σ → ℝ :=
  Quotient.lift (fun f => limitLin L f) fun f g hfg => by
    have h0 := limitLin_zeroSpace hC hfg
    rw [map_sub] at h0
    exact sub_eq_zero.mp h0

@[simp]
lemma limitQuot_mk {L : FinFlag 𝕋 σ → ℝ} (hC : ChainClosed L)
    (f : FlagVector 𝕋 σ) :
    limitQuot hC ⟦f⟧ = limitLin L f := rfl

@[simp]
lemma limitQuot_basis {L : FinFlag 𝕋 σ → ℝ} (hC : ChainClosed L)
    (F : FinFlag 𝕋 σ) :
    limitQuot hC ⟦basisVector F⟧ = L F := by
  rw [limitQuot_mk, limitLin_basis]

lemma limitQuot_add {L : FinFlag 𝕋 σ → ℝ} (hC : ChainClosed L)
    (x y : FlagAlgebra 𝕋 σ) :
    limitQuot hC (x + y) = limitQuot hC x + limitQuot hC y := by
  refine Quotient.inductionOn₂ x y fun f g => ?_
  rw [← add_quot, limitQuot_mk, limitQuot_mk, limitQuot_mk, map_add]

lemma limitQuot_smul {L : FinFlag 𝕋 σ → ℝ} (hC : ChainClosed L) (r : ℝ)
    (x : FlagAlgebra 𝕋 σ) :
    limitQuot hC (r • x) = r * limitQuot hC x := by
  refine Quotient.inductionOn x fun f => ?_
  rw [← smul_quot, limitQuot_mk, limitQuot_mk, map_smul, smul_eq_mul]

lemma limitQuot_one [𝕋.IsType σ] {L : FinFlag 𝕋 σ → ℝ}
    (hC : ChainClosed L) :
    limitQuot hC (1 : FlagAlgebra 𝕋 σ) = L 1 := by
  show limitQuot hC ⟦(1 : FlagVector 𝕋 σ)⟧ = L 1
  rw [show (1 : FlagVector 𝕋 σ) = basisVector 1 from rfl, limitQuot_basis]

/-- A multiplicatively closed profile evaluates a flag product to the
product of the values. -/
lemma limitLin_flagMul {L : FinFlag 𝕋 σ → ℝ} (hM : MulClosed L)
    (F₁ F₂ : FinFlag 𝕋 σ) :
    limitLin L (flagMul F₁ F₂) = L F₁ * L F₂ := by
  rw [flagMul, flagMulWithSize, map_sum]
  rw [Finset.sum_congr rfl fun G (_ : G ∈ Finset.univ) => by
    rw [map_smul, limitLin_basis, smul_eq_mul]]
  exact hM F₁ F₂

/-- The descent of a chain-closed, multiplicatively closed profile is
multiplicative, by bilinearity. -/
lemma limitQuot_mul {L : FinFlag 𝕋 σ → ℝ} (hC : ChainClosed L)
    (hM : MulClosed L) (x y : FlagAlgebra 𝕋 σ) :
    limitQuot hC (x * y) = limitQuot hC x * limitQuot hC y := by
  refine Quotient.inductionOn₂ x y fun f g => ?_
  rw [← mul_quot, limitQuot_mk, limitQuot_mk, limitQuot_mk,
    flagVector_mul_eq_nested_sum, map_sum]
  rw [Finset.sum_congr rfl fun F (_ : F ∈ f.support) => by
    rw [map_sum,
      Finset.sum_congr rfl fun G (_ : G ∈ g.support) => by
        rw [map_smul, limitLin_flagMul hM, smul_eq_mul]]]
  rw [limitLin_apply, limitLin_apply, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  refine Finset.sum_congr rfl fun G _ => ?_
  ring

/-! ## Profiles are homomorphisms, and conversely -/

section IsType

variable [𝕋.IsType σ]

/-- **A profile with the four properties is a positive homomorphism.** -/
noncomputable def homOfProfile (L : FinFlag 𝕋 σ → ℝ) (hC : ChainClosed L)
    (hM : MulClosed L) (h1 : L 1 = 1) (hnn : ∀ F, 0 ≤ L F) :
    PositiveHom 𝕋 σ := by
  refine ⟨AlgHom.mk' ⟨⟨⟨limitQuot hC, ?_⟩, ?_⟩, ?_, ?_⟩ ?_, ?_⟩
  · rw [limitQuot_one hC]
    exact h1
  · exact fun x y => limitQuot_mul hC hM x y
  · show limitQuot hC 0 = 0
    show limitQuot hC ⟦0⟧ = 0
    rw [limitQuot_mk, map_zero]
  · exact fun x y => limitQuot_add hC x y
  · intro c x
    show limitQuot hC (c • x) = c • limitQuot hC x
    rw [limitQuot_smul hC c x]
    rfl
  · intro F
    show 0 ≤ limitQuot hC ⟦basisVector F⟧
    rw [limitQuot_basis]
    exact hnn F

@[simp]
lemma homOfProfile_basis (L : FinFlag 𝕋 σ → ℝ) (hC : ChainClosed L)
    (hM : MulClosed L) (h1 : L 1 = 1) (hnn : ∀ F, 0 ≤ L F)
    (F : FinFlag 𝕋 σ) :
    homOfProfile L hC hM h1 hnn ⟦basisVector F⟧ = L F :=
  limitQuot_basis hC F

lemma homOfProfile_mk (L : FinFlag 𝕋 σ → ℝ) (hC : ChainClosed L)
    (hM : MulClosed L) (h1 : L 1 = 1) (hnn : ∀ F, 0 ≤ L F)
    (f : FlagVector 𝕋 σ) :
    homOfProfile L hC hM h1 hnn ⟦f⟧ = limitLin L f := rfl

/-- A general class as a combination of basis classes. -/
lemma quot_eq_sum_basis (f : FlagVector 𝕋 σ) :
    (⟦f⟧ : FlagAlgebra 𝕋 σ)
      = ∑ F ∈ f.support, f F • (⟦basisVector F⟧ : FlagAlgebra 𝕋 σ) := by
  conv_lhs => rw [flagVector_eq_sum_basisVector f]
  rw [sum_quot]
  exact Finset.sum_congr rfl fun F _ => smul_quot (f F) (basisVector F)

/-- The value of a homomorphism at any class is the profile-weighted
support sum. -/
lemma PositiveHom.apply_quot (φ : PositiveHom 𝕋 σ) (f : FlagVector 𝕋 σ) :
    φ ⟦f⟧ = ∑ F ∈ f.support, f F * φ ⟦basisVector F⟧ := by
  rw [quot_eq_sum_basis f, PositiveHom.map_sum]
  exact Finset.sum_congr rfl fun F _ => PositiveHom.map_smul φ _ _

/-- **A homomorphism is determined by its profile.** -/
theorem PositiveHom.ext_of_basis {φ₁ φ₂ : PositiveHom 𝕋 σ}
    (h : ∀ F : FinFlag 𝕋 σ, φ₁ ⟦basisVector F⟧ = φ₂ ⟦basisVector F⟧) :
    φ₁ = φ₂ := by
  refine PositiveHom.ext fun x => ?_
  refine Quotient.inductionOn x fun f => ?_
  rw [PositiveHom.apply_quot, PositiveHom.apply_quot]
  exact Finset.sum_congr rfl fun F _ => by rw [h F]

/-- The profile of a homomorphism. -/
noncomputable def PositiveHom.profile (φ : PositiveHom 𝕋 σ) : FinFlag 𝕋 σ → ℝ :=
  fun F => φ ⟦basisVector F⟧

theorem PositiveHom.profile_injective :
    Function.Injective (PositiveHom.profile (𝕋 := 𝕋) (σ := σ)) :=
  fun _ _ h => PositiveHom.ext_of_basis fun F => congrFun h F

/-- The profile of a homomorphism is chain closed. -/
theorem chainClosed_profile (φ : PositiveHom 𝕋 σ) :
    ChainClosed φ.profile := by
  intro F ℓ hFℓ
  show φ ⟦basisVector F⟧ = _
  rw [basisVector_quot_eq_sum F ℓ hFℓ, PositiveHom.map_sum]
  exact Finset.sum_congr rfl fun F' _ => PositiveHom.map_smul φ _ _

/-- The profile of a homomorphism is multiplicatively closed. -/
theorem mulClosed_profile (φ : PositiveHom 𝕋 σ) :
    MulClosed φ.profile := by
  intro F₁ F₂
  have h := PositiveHom.map_mul φ ⟦basisVector F₁⟧ ⟦basisVector F₂⟧
  rw [basisVector_quot_mul_eq_flagMul_quot, flagMul, flagMulWithSize,
    sum_quot, PositiveHom.map_sum] at h
  show _ = φ ⟦basisVector F₁⟧ * φ ⟦basisVector F₂⟧
  rw [← h]
  exact Finset.sum_congr rfl fun G _ => by
    rw [smul_quot, PositiveHom.map_smul]
    rfl

theorem profile_one (φ : PositiveHom 𝕋 σ) : φ.profile 1 = 1 := by
  show φ ⟦basisVector 1⟧ = 1
  rw [show (⟦basisVector 1⟧ : FlagAlgebra 𝕋 σ) = 1 from rfl]
  exact PositiveHom.map_one φ

theorem profile_nonneg (φ : PositiveHom 𝕋 σ) (F : FinFlag 𝕋 σ) :
    0 ≤ φ.profile F :=
  positiveHom_basisVector_nonneg φ F

/-- **The profile characterisation**: a profile comes from a positive
homomorphism iff it is chain closed, multiplicatively closed, normalised
and nonnegative. -/
theorem exists_hom_profile_iff (L : FinFlag 𝕋 σ → ℝ) :
    (∃ φ : PositiveHom 𝕋 σ, φ.profile = L)
      ↔ ChainClosed L ∧ MulClosed L ∧ L 1 = 1 ∧ ∀ F, 0 ≤ L F := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨chainClosed_profile φ, mulClosed_profile φ, profile_one φ,
      profile_nonneg φ⟩
  · rintro ⟨hC, hM, h1, hnn⟩
    exact ⟨homOfProfile L hC hM h1 hnn, funext fun F => homOfProfile_basis L hC hM h1 hnn F⟩

end IsType

end FlagAlgebras.Core
