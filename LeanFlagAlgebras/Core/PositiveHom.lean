import LeanFlagAlgebras.Core.Algebra
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Rat.Cast.Order

/-! # Core: positive homomorphisms and the semantic order

A `PositiveHom 𝕋 σ` is an `ℝ`-algebra homomorphism `FlagAlgebra 𝕋 σ → ℝ`
that is nonnegative on every flag: the semantic evaluations of the flag
algebra (limits of subflag densities). The set of elements every positive
homomorphism sends to a nonnegative value is the `semanticCone`, inducing
the preorder `≤` in which density bounds are stated. This file collects the
homomorphism calculus and the basic positivity/monotonicity facts of that
order, theory-generically. -/

namespace FlagAlgebras.Core

variable {S : Signature} {T : Type} [Fintype T]
variable {𝕋 : RelTheory S} {σ : Model S T} [𝕋.IsType σ]

/-- An `ℝ`-algebra homomorphism from the flag algebra to the reals. -/
abbrev FlagHom (𝕋 : RelTheory S) (σ : Model S T) [Fintype T]
    [𝕋.IsType σ] : Type :=
  FlagAlgebra 𝕋 σ →ₐ[ℝ] ℝ

/-- A *positive* homomorphism: an algebra map `FlagAlgebra 𝕋 σ → ℝ` that is
nonnegative on every flag. These are exactly the semantic evaluations
(limits of subflag densities) of the flag algebra. -/
def PositiveHom (𝕋 : RelTheory S) (σ : Model S T) [Fintype T]
    [𝕋.IsType σ] : Type :=
  { φ : FlagHom 𝕋 σ // ∀ F : FinFlag 𝕋 σ, 0 ≤ φ ⟦basisVector F⟧ }

instance : FunLike (PositiveHom 𝕋 σ) (FlagAlgebra 𝕋 σ) ℝ where
  coe φ := φ.val
  coe_injective' f g h := by
    rcases f with ⟨f, _⟩
    rcases g with ⟨g, _⟩
    simp only at h
    congr
    exact DFunLike.coe_injective h

namespace PositiveHom

@[ext]
theorem ext {φ₁ φ₂ : PositiveHom 𝕋 σ}
    (h : ∀ f : FlagAlgebra 𝕋 σ, φ₁ f = φ₂ f) : φ₁ = φ₂ := by
  apply Subtype.ext
  exact AlgHom.ext h

@[simp]
theorem map_zero (φ : PositiveHom 𝕋 σ) : φ 0 = 0 :=
  φ.val.map_zero

@[simp]
theorem map_one (φ : PositiveHom 𝕋 σ) : φ 1 = 1 :=
  φ.val.map_one

theorem map_add (φ : PositiveHom 𝕋 σ) (f g : FlagAlgebra 𝕋 σ) :
    φ (f + g) = φ f + φ g :=
  φ.val.map_add f g

theorem map_sub (φ : PositiveHom 𝕋 σ) (f g : FlagAlgebra 𝕋 σ) :
    φ (f - g) = φ f - φ g :=
  _root_.map_sub (φ.val : FlagAlgebra 𝕋 σ →+* ℝ) f g

theorem map_mul (φ : PositiveHom 𝕋 σ) (f g : FlagAlgebra 𝕋 σ) :
    φ (f * g) = φ f * φ g :=
  φ.val.map_mul f g

theorem map_smul (φ : PositiveHom 𝕋 σ) (r : ℝ) (f : FlagAlgebra 𝕋 σ) :
    φ (r • f) = r * φ f := by
  calc φ (r • f) = φ.val (r • f) := rfl
    _ = r • φ.val f := _root_.map_smul φ.val r f
    _ = r * φ f := rfl

theorem map_sum (φ : PositiveHom 𝕋 σ) {ι : Type} (s : Finset ι)
    (f : ι → FlagAlgebra 𝕋 σ) :
    φ (∑ i ∈ s, f i) = ∑ i ∈ s, φ (f i) :=
  _root_.map_sum (φ.val : FlagAlgebra 𝕋 σ →+* ℝ) f s

end PositiveHom

/-- A positive homomorphism is nonnegative on every flag (the defining
property). -/
theorem positiveHom_basisVector_nonneg (φ : PositiveHom 𝕋 σ)
    (F : FinFlag 𝕋 σ) : 0 ≤ φ ⟦basisVector F⟧ :=
  φ.2 F

/-- The φ-values of all flags of a fixed size `ℓ ≥ |T|` sum to `1`
(a probability-distribution normalization). -/
theorem sum_positiveHom_basisVector_eq_one (φ : PositiveHom 𝕋 σ) (ℓ : ℕ)
    (hℓ : Fintype.card T ≤ ℓ) :
    ∑ F : FlagWithSize 𝕋 σ ℓ, φ ⟦basisVector ⟨ℓ, F⟩⟧ = 1 := by
  rw [← PositiveHom.map_sum, sum_flagWithSize_eq_one ℓ hℓ,
    PositiveHom.map_one]

/-- A positive homomorphism maps every flag into `[0, 1]`: the upper bound,
since each flag is one summand of a sum-to-one of nonnegatives. -/
theorem positiveHom_basisVector_le_one (φ : PositiveHom 𝕋 σ)
    (F : FinFlag 𝕋 σ) : φ ⟦basisVector F⟧ ≤ 1 := by
  classical
  have hℓ : Fintype.card T ≤ F.1 := finFlag_size_ge F
  rw [← sum_positiveHom_basisVector_eq_one φ F.1 hℓ]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ F.2)]
  have hF : F = ⟨F.1, F.2⟩ := rfl
  rw [← hF, le_add_iff_nonneg_right]
  exact Finset.sum_nonneg fun G _ =>
    positiveHom_basisVector_nonneg φ ⟨F.1, G⟩

/-! ## The semantic cone and the induced order -/

/-- The semantic cone: flag-algebra elements that *every* positive
homomorphism sends to a nonnegative value. Membership `0 ≤ f` is exactly an
unconditional density inequality. -/
def semanticCone (𝕋 : RelTheory S) (σ : Model S T) [Fintype T]
    [𝕋.IsType σ] : Set (FlagAlgebra 𝕋 σ) :=
  { f : FlagAlgebra 𝕋 σ | ∀ φ : PositiveHom 𝕋 σ, 0 ≤ φ f }

noncomputable instance : LE (FlagAlgebra 𝕋 σ) where
  le f g := g - f ∈ semanticCone 𝕋 σ

/-- Unfolds the semantic order: `f ≤ g` iff every positive homomorphism
agrees. -/
theorem le_def (f g : FlagAlgebra 𝕋 σ) :
    f ≤ g ↔ g - f ∈ semanticCone 𝕋 σ :=
  Iff.rfl

theorem flag_sub_nonneg (f g : FlagAlgebra 𝕋 σ) : f ≤ g ↔ 0 ≤ g - f := by
  rw [le_def, le_def, sub_zero]

noncomputable instance : Preorder (FlagAlgebra 𝕋 σ) where
  le_refl f := by
    intro φ
    rw [sub_self, PositiveHom.map_zero]
  le_trans f g h hfg hgh := by
    intro φ
    have hsum : φ (h - f) = φ (h - g) + φ (g - f) := by
      rw [← PositiveHom.map_add]
      congr 1
      abel
    rw [hsum]
    exact add_nonneg (hgh φ) (hfg φ)

/-- Every flag is nonnegative in the semantic order. -/
theorem flag_nonneg (F : FinFlag 𝕋 σ) :
    (0 : FlagAlgebra 𝕋 σ) ≤ ⟦basisVector F⟧ := by
  intro φ
  rw [sub_zero]
  exact φ.2 F

/-- The semantic order is compatible with addition. -/
theorem flag_add_le_add {f f' g g' : FlagAlgebra 𝕋 σ} (hf : f ≤ f')
    (hg : g ≤ g') : f + g ≤ f' + g' := by
  intro φ
  have hsum : φ (f' + g' - (f + g)) = φ (f' - f) + φ (g' - g) := by
    rw [← PositiveHom.map_add]
    congr 1
    abel
  rw [hsum]
  exact add_nonneg (hf φ) (hg φ)

theorem flag_add_le_add_left {f g : FlagAlgebra 𝕋 σ} (h : f ≤ g)
    (a : FlagAlgebra 𝕋 σ) : a + f ≤ a + g :=
  flag_add_le_add (le_refl a) h

theorem flag_add_le_add_right {f g : FlagAlgebra 𝕋 σ} (h : f ≤ g)
    (a : FlagAlgebra 𝕋 σ) : f + a ≤ g + a := by
  simpa [add_comm] using flag_add_le_add h (le_refl a)

instance : AddLeftMono (FlagAlgebra 𝕋 σ) where
  elim := fun a _ _ h => flag_add_le_add_left h a

instance : AddRightMono (FlagAlgebra 𝕋 σ) where
  elim := fun a _ _ h => flag_add_le_add_right h a

/-- A nonnegative scalar times a nonnegative element is nonnegative. -/
theorem smul_nonneg_of_nonneg {r : ℝ} {f : FlagAlgebra 𝕋 σ} (hr : 0 ≤ r)
    (hf : 0 ≤ f) : (0 : FlagAlgebra 𝕋 σ) ≤ r • f := by
  intro φ
  rw [sub_zero, PositiveHom.map_smul]
  exact mul_nonneg hr (by simpa using hf φ)

/-- Sums of nonnegative elements are nonnegative. -/
theorem sum_nonneg' {ι : Type} {s : Finset ι} {f : ι → FlagAlgebra 𝕋 σ}
    (h : ∀ i ∈ s, (0 : FlagAlgebra 𝕋 σ) ≤ f i) :
    (0 : FlagAlgebra 𝕋 σ) ≤ ∑ i ∈ s, f i := by
  intro φ
  rw [sub_zero, PositiveHom.map_sum]
  exact Finset.sum_nonneg fun i hi => by simpa using h i hi φ

/-- Termwise comparison of sums in the semantic order. -/
theorem flag_sum_le_sum {ι : Type} {s : Finset ι}
    {f g : ι → FlagAlgebra 𝕋 σ} (h : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  intro φ
  rw [← Finset.sum_sub_distrib, PositiveHom.map_sum]
  exact Finset.sum_nonneg fun i hi => h i hi φ

/-- Scaling monotonicity against nonnegative elements. -/
theorem flag_smul_le_smul {c d : ℝ} (hcd : c ≤ d) {x : FlagAlgebra 𝕋 σ}
    (hx : 0 ≤ x) : c • x ≤ d • x := by
  intro φ
  rw [show d • x - c • x = (d - c) • x from (sub_smul d c x).symm,
    PositiveHom.map_smul]
  refine mul_nonneg (sub_nonneg.mpr hcd) ?_
  simpa using hx φ

/-- **The averaging assembly**: a flag is bounded in the semantic order by
any uniform bound on its densities at an expansion level. The engine of
certificate proofs: expand, bound each coefficient, collapse the
normalization. -/
theorem basisVector_quot_le_smul_one (F : FinFlag 𝕋 σ)
    (ℓ : ℕ) (hF : F.1 ≤ ℓ) (hT : Fintype.card T ≤ ℓ) {c : ℚ}
    (hc : ∀ H : FlagWithSize 𝕋 σ ℓ, subflagDensity F.2 H ≤ c) :
    (⟦basisVector F⟧ : FlagAlgebra 𝕋 σ) ≤ (c : ℝ) • 1 := by
  rw [basisVector_quot_eq_sum F ℓ hF, ← sum_flagWithSize_eq_one ℓ hT,
    Finset.smul_sum]
  refine flag_sum_le_sum fun H _ => ?_
  refine flag_smul_le_smul ?_ (flag_nonneg _)
  exact (Rat.cast_le (K := ℝ)).mpr (hc H)

end FlagAlgebras.Core
