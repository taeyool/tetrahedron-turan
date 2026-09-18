import LeanFlagAlgebras.Core.Downward
import Mathlib.Data.Rat.Cast.Order

/-! # Core: density evaluation of flag vectors and the zero-space criterion

Razborov's `p^G(f)`: the linear extension of `F ↦ p(F, G)` to formal flag
vectors, at a host class (`densityEval`) or at a labeled host on any finite
carrier (`hostEval`). The criterion for membership in the zero space: a
vector supported on sizes `≤ L` whose evaluations vanish at every host of
size `L` lies in `ZeroSpace` — the averaging relations put it equal to its
size-`L` expansion, which is zero (`mem_zeroSpace_of_densityEval_zero`).
Conversely every element of the zero space evaluates to zero at all
sufficiently large hosts, by the chain rule
(`zeroSpace_densityEval_eventually_zero`).

This is the tool behind Razborov's Lemma 4.2(b): an operator defined on
models descends to the flag algebra once its evaluations at large hosts
are controlled. Theory-generic port of `Differential/Eval.lean` of the
simple-graph development. -/

namespace FlagAlgebras.Core

open Finset

variable {S : Signature} {T : Type} [Fintype T]
variable {𝕋 : RelTheory S} {σ : Model S T}

/-! ## Evaluation at a host class -/

/-- Razborov's `p^G(f)`: the density evaluation of a flag vector at a host
class, the linear extension of `F ↦ p(F, G)`. -/
noncomputable def densityEval (f : FlagVector 𝕋 σ) (G : FinFlag 𝕋 σ) : ℝ :=
  linearExtension (fun F : FinFlag 𝕋 σ => ((subflagDensity F.2 G.2 : ℚ) : ℝ)) f

@[simp]
theorem densityEval_basisVector (F G : FinFlag 𝕋 σ) :
    densityEval (basisVector F) G = ((subflagDensity F.2 G.2 : ℚ) : ℝ) := by
  unfold densityEval
  rw [linearExtension_basisVector]

@[simp]
theorem densityEval_zero (G : FinFlag 𝕋 σ) :
    densityEval (0 : FlagVector 𝕋 σ) G = 0 := by
  unfold densityEval
  rw [linearExtension_zero]

theorem densityEval_add (f f' : FlagVector 𝕋 σ) (G : FinFlag 𝕋 σ) :
    densityEval (f + f') G = densityEval f G + densityEval f' G := by
  unfold densityEval
  rw [linearExtension_add]

theorem densityEval_neg (f : FlagVector 𝕋 σ) (G : FinFlag 𝕋 σ) :
    densityEval (-f) G = -densityEval f G := by
  unfold densityEval
  rw [linearExtension_neg]

theorem densityEval_sub (f f' : FlagVector 𝕋 σ) (G : FinFlag 𝕋 σ) :
    densityEval (f - f') G = densityEval f G - densityEval f' G := by
  unfold densityEval
  rw [linearExtension_sub]

theorem densityEval_smul (r : ℝ) (f : FlagVector 𝕋 σ) (G : FinFlag 𝕋 σ) :
    densityEval (r • f) G = r * densityEval f G := by
  unfold densityEval
  rw [linearExtension_smul]
  rfl

theorem densityEval_sum {ι : Type} (s : Finset ι) (c : ι → FlagVector 𝕋 σ)
    (G : FinFlag 𝕋 σ) :
    densityEval (∑ i ∈ s, c i) G = ∑ i ∈ s, densityEval (c i) G := by
  unfold densityEval
  rw [linearExtension_sum]

/-- The evaluation as a support sum. -/
theorem densityEval_apply (f : FlagVector 𝕋 σ) (G : FinFlag 𝕋 σ) :
    densityEval f G = ∑ F ∈ f.support, f F * ((subflagDensity F.2 G.2 : ℚ) : ℝ) :=
  rfl

/-- Density evaluations are bounded by the `ℓ¹`-norm of the coefficients. -/
theorem abs_densityEval_le (f : FlagVector 𝕋 σ) (G : FinFlag 𝕋 σ) :
    |densityEval f G| ≤ ∑ F ∈ f.support, |f F| := by
  rw [densityEval_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun F _ => ?_)
  rw [abs_mul]
  have h0 : (0 : ℝ) ≤ ((subflagDensity F.2 G.2 : ℚ) : ℝ) :=
    Rat.cast_nonneg.mpr (subflagDensity_nonneg F.2 G.2)
  have h1 : ((subflagDensity F.2 G.2 : ℚ) : ℝ) ≤ 1 :=
    by exact_mod_cast subflagDensity_le_one F.2 G.2
  calc |f F| * |((subflagDensity F.2 G.2 : ℚ) : ℝ)|
      = |f F| * ((subflagDensity F.2 G.2 : ℚ) : ℝ) := by rw [abs_of_nonneg h0]
    _ ≤ |f F| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |f F| := mul_one _

/-! ## Evaluation at a labeled host on any carrier -/

section Host

variable {V : Type} [Fintype V]

/-- The density evaluation at a labeled host on an arbitrary finite carrier:
the linear extension of `F ↦ p(F, G)` with `F` read off the class
representative. -/
noncomputable def hostEval (G : LabeledFlag 𝕋 σ V) (f : FlagVector 𝕋 σ) : ℝ :=
  linearExtension
    (fun F : FinFlag 𝕋 σ => ((flagDensity (Quotient.out F.2) G : ℚ) : ℝ)) f

@[simp]
theorem hostEval_basisVector (G : LabeledFlag 𝕋 σ V) (F : FinFlag 𝕋 σ) :
    hostEval G (basisVector F) = ((flagDensity (Quotient.out F.2) G : ℚ) : ℝ) := by
  unfold hostEval
  rw [linearExtension_basisVector]

@[simp]
theorem hostEval_zero (G : LabeledFlag 𝕋 σ V) :
    hostEval G (0 : FlagVector 𝕋 σ) = 0 := by
  unfold hostEval
  rw [linearExtension_zero]

theorem hostEval_add (G : LabeledFlag 𝕋 σ V) (f f' : FlagVector 𝕋 σ) :
    hostEval G (f + f') = hostEval G f + hostEval G f' := by
  unfold hostEval
  rw [linearExtension_add]

theorem hostEval_neg (G : LabeledFlag 𝕋 σ V) (f : FlagVector 𝕋 σ) :
    hostEval G (-f) = -hostEval G f := by
  unfold hostEval
  rw [linearExtension_neg]

theorem hostEval_sub (G : LabeledFlag 𝕋 σ V) (f f' : FlagVector 𝕋 σ) :
    hostEval G (f - f') = hostEval G f - hostEval G f' := by
  unfold hostEval
  rw [linearExtension_sub]

theorem hostEval_smul (G : LabeledFlag 𝕋 σ V) (r : ℝ) (f : FlagVector 𝕋 σ) :
    hostEval G (r • f) = r * hostEval G f := by
  unfold hostEval
  rw [linearExtension_smul]
  rfl

theorem hostEval_sum (G : LabeledFlag 𝕋 σ V) {ι : Type} (s : Finset ι)
    (c : ι → FlagVector 𝕋 σ) :
    hostEval G (∑ i ∈ s, c i) = ∑ i ∈ s, hostEval G (c i) := by
  unfold hostEval
  rw [linearExtension_sum]

theorem hostEval_apply (G : LabeledFlag 𝕋 σ V) (f : FlagVector 𝕋 σ) :
    hostEval G f
      = ∑ F ∈ f.support, f F * ((flagDensity (Quotient.out F.2) G : ℚ) : ℝ) :=
  rfl

/-- Host evaluations depend only on the isomorphism class of the host. -/
theorem hostEval_congr {W : Type} [Fintype W] {G : LabeledFlag 𝕋 σ V}
    {G' : LabeledFlag 𝕋 σ W} (e : G ≃ᶠ G') (f : FlagVector 𝕋 σ) :
    hostEval G f = hostEval G' f := by
  rw [hostEval_apply, hostEval_apply]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [flagDensity_congr_right _ e]

/-- Host evaluations are bounded by the `ℓ¹`-norm of the coefficients. -/
theorem abs_hostEval_le (G : LabeledFlag 𝕋 σ V) (f : FlagVector 𝕋 σ) :
    |hostEval G f| ≤ ∑ F ∈ f.support, |f F| := by
  rw [hostEval_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun F _ => ?_)
  rw [abs_mul]
  have h0 : (0 : ℝ) ≤ ((flagDensity (Quotient.out F.2) G : ℚ) : ℝ) :=
    Rat.cast_nonneg.mpr (flagDensity_nonneg (Quotient.out F.2) G)
  have h1 : ((flagDensity (Quotient.out F.2) G : ℚ) : ℝ) ≤ 1 :=
    by exact_mod_cast flagDensity_le_one (Quotient.out F.2) G
  calc |f F| * |((flagDensity (Quotient.out F.2) G : ℚ) : ℝ)|
      = |f F| * ((flagDensity (Quotient.out F.2) G : ℚ) : ℝ) := by rw [abs_of_nonneg h0]
    _ ≤ |f F| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |f F| := mul_one _

/-- A class density against a labeled host is the density of the class
representative. -/
theorem subflagDensity_toFlag_right {U : Type} [Fintype U] (F : Flag 𝕋 σ U)
    (G : LabeledFlag 𝕋 σ V) :
    subflagDensity F G.toFlag = flagDensity (Quotient.out F) G := by
  conv_lhs => rw [← Quotient.out_eq F]
  rfl

/-- On a canonical carrier, the host evaluation is the class evaluation. -/
theorem hostEval_toFlag {n : ℕ} (G : LabeledFlag 𝕋 σ (Fin n)) (f : FlagVector 𝕋 σ) :
    hostEval G f = densityEval f ⟨n, G.toFlag⟩ := by
  rw [hostEval_apply, densityEval_apply]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [subflagDensity_toFlag_right]

/-- The class evaluation is the host evaluation at the representative. -/
theorem densityEval_out {n : ℕ} (f : FlagVector 𝕋 σ) (G : FlagWithSize 𝕋 σ n) :
    densityEval f ⟨n, G⟩ = hostEval (Quotient.out G) f := by
  rw [hostEval_toFlag]
  have h : (Quotient.out G).toFlag = G := Quotient.out_eq G
  rw [h]

end Host

/-! ## The size-`L` expansion and the zero-space criterion -/

/-- The size-`L` expansion of a flag vector: the formal combination of all
size-`L` flags weighted by the vector's density evaluations. -/
noncomputable def expandAt (L : ℕ) (f : FlagVector 𝕋 σ) : FlagVector 𝕋 σ :=
  ∑ G : FlagWithSize 𝕋 σ L, densityEval f ⟨L, G⟩ • basisVector ⟨L, G⟩

theorem expandAt_basisVector (F : FinFlag 𝕋 σ) (L : ℕ) :
    expandAt L (basisVector F) = flagExpansion F L := by
  unfold expandAt flagExpansion
  refine Finset.sum_congr rfl fun G _ => ?_
  rw [densityEval_basisVector]

/-- A flag vector supported on sizes `≤ L` is flag-equal to its size-`L`
expansion: the linear extension of the averaging relations. -/
theorem flagVector_eqv_expandAt {f : FlagVector 𝕋 σ} {L : ℕ}
    (h_supp : ∀ F ∈ f.support, F.1 ≤ L) :
    flagVectorEqv f (expandAt L f) := by
  have h1 : flagVectorEqv f (∑ F ∈ f.support, f F • flagExpansion F L) := by
    nth_rw 1 [flagVector_eq_sum_basisVector f]
    apply flagVectorEqv_sum
    intro F hF
    exact flagVectorEqv_smul _ (basisVector_eqv_flagExpansion F L (h_supp F hF))
  have h2 : (∑ F ∈ f.support, f F • flagExpansion F L) = expandAt L f := by
    unfold flagExpansion expandAt
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun G _ => ?_
    rw [densityEval_apply, Finset.sum_smul]
  exact h1.trans (flagVector_eq_eqv h2)

theorem expandAt_eq_zero_of_eval_zero {f : FlagVector 𝕋 σ} {L : ℕ}
    (h : ∀ G : FlagWithSize 𝕋 σ L, densityEval f ⟨L, G⟩ = 0) :
    expandAt L f = 0 := by
  apply Finset.sum_eq_zero
  intro G _
  rw [h G, zero_smul]

/-- **Zero-space membership criterion.** A vector supported on sizes `≤ L`
whose density evaluations vanish at every size-`L` host lies in the zero
space. -/
theorem mem_zeroSpace_of_densityEval_zero {f : FlagVector 𝕋 σ} {L : ℕ}
    (h_supp : ∀ F ∈ f.support, F.1 ≤ L)
    (h_eval : ∀ G : FlagWithSize 𝕋 σ L, densityEval f ⟨L, G⟩ = 0) :
    f ∈ ZeroSpace 𝕋 σ := by
  have h := flagVector_eqv_expandAt h_supp
  unfold flagVectorEqv at h
  rwa [expandAt_eq_zero_of_eval_zero h_eval, sub_zero] at h

/-- The generating relations evaluate to zero at every host of size at least
their expansion size: the chain rule. -/
theorem densityEval_zeroElement (F : FinFlag 𝕋 σ) {ℓ L : ℕ} (hℓ : F.1 ≤ ℓ)
    (hL : ℓ ≤ L) (G : FlagWithSize 𝕋 σ L) :
    densityEval (zeroElement F ℓ) ⟨L, G⟩ = 0 := by
  unfold zeroElement
  rw [densityEval_sub, sub_eq_zero, densityEval_basisVector]
  unfold flagExpansion
  rw [densityEval_sum]
  simp_rw [densityEval_smul, densityEval_basisVector]
  rw [subflagDensity_chain (W' := Fin ℓ) (by simpa using hℓ) (by simpa using hL) F.2 G]
  push_cast
  rfl

/-- Every element of the zero space has vanishing density evaluations at all
sufficiently large host sizes. -/
theorem zeroSpace_densityEval_eventually_zero {k : FlagVector 𝕋 σ}
    (hk : k ∈ ZeroSpace 𝕋 σ) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ G : FlagWithSize 𝕋 σ L, densityEval k ⟨L, G⟩ = 0 := by
  obtain ⟨I, hI, c, v, hv, hk_sum⟩ := zeroSpace_eq_sum_spanElement k hk
  simp only [mem_zeroSet] at hv
  choose F ℓ hFℓ hveq using hv
  refine ⟨Finset.univ.sup ℓ, fun L hL G => ?_⟩
  rw [hk_sum, densityEval_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [densityEval_smul, hveq i,
    densityEval_zeroElement (F i) (hFℓ i) (le_trans (Finset.le_sup (mem_univ i)) hL) G,
    mul_zero]

/-- Flag-equal vectors have equal evaluations at all sufficiently large
hosts. -/
theorem densityEval_eq_of_eqv {f g : FlagVector 𝕋 σ} (h : flagVectorEqv f g) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ G : FlagWithSize 𝕋 σ L,
      densityEval f ⟨L, G⟩ = densityEval g ⟨L, G⟩ := by
  obtain ⟨L₀, hL₀⟩ := zeroSpace_densityEval_eventually_zero h
  refine ⟨L₀, fun L hL G => ?_⟩
  have := hL₀ L hL G
  rwa [densityEval_sub, sub_eq_zero] at this

end FlagAlgebras.Core
