import LeanFlagAlgebras.Core.Downward
import LeanFlagAlgebras.Core.PositiveHom
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Linarith

/-! # Core: square positivity of the downward operator

Razborov's Theorem 3.14, proved measure-free: the downward image of a
square is nonnegative in the semantic order of the empty-type algebra.

The proof avoids the random-homomorphism measure extension entirely.
Since a positive homomorphism `φ` respects the averaging relations,
`φ (downward (x·x))` can be evaluated on the level-`ℓ` expansion for
*every* admissible `ℓ`: it is a sum over size-`ℓ` flags `H` of the
pair-density quadratic form `Q_H = ∑ᵢⱼ aᵢaⱼ p(Fᵢ,Fⱼ;H)` weighted by the
nonnegative factors `q(H)·φ(H↓)`. The product approximation bounds `Q_H`
below by the true square `(∑ᵢ aᵢ p(Fᵢ;H))² ≥ 0` minus
`M·(n−k)²/(ℓ−k)`, and the weights sum to `φ (downward 1) ≤ 1`. Letting
`ℓ → ∞` gives nonnegativity. -/

namespace FlagAlgebras.Core

open Classical

variable {S : Signature} {T : Type} [Fintype T] [S.NullaryFree]
variable {𝕋 : RelTheory S} {σ : Model S T}

omit [S.NullaryFree] in
private lemma subflagPairDensity_out {U₁' U₂' V' : Type} [Fintype U₁']
    [Fintype U₂'] [Fintype V'] (A : Flag 𝕋 σ U₁') (B : Flag 𝕋 σ U₂')
    (C : Flag 𝕋 σ V') :
    subflagPairDensity A B C
      = flagPairDensity (Quotient.out A) (Quotient.out B)
        (Quotient.out C) := by
  conv_lhs => rw [← Quotient.out_eq A, ← Quotient.out_eq B,
    ← Quotient.out_eq C]
  rfl

omit [S.NullaryFree] in
/-- The product approximation on isomorphism classes, cast to the reals. -/
private lemma abs_subflag_estimate {n ℓ : ℕ} (Fi Fj : FlagWithSize 𝕋 σ n)
    (H : FlagWithSize 𝕋 σ ℓ) (hℓ : n + n ≤ ℓ + Fintype.card T)
    (hk : Fintype.card T < ℓ) :
    |((subflagPairDensity Fi Fj H : ℚ) : ℝ)
        - ((subflagDensity Fi H : ℚ) : ℝ) *
          ((subflagDensity Fj H : ℚ) : ℝ)|
      ≤ (((n - Fintype.card T) * (n - Fintype.card T) : ℕ) : ℝ) /
        ((ℓ - Fintype.card T : ℕ) : ℝ) := by
  have h : |subflagPairDensity Fi Fj H
      - subflagDensity Fi H * subflagDensity Fj H|
      ≤ (((n - Fintype.card T) * (n - Fintype.card T) : ℕ) : ℚ) /
        ((ℓ - Fintype.card T : ℕ) : ℚ) := by
    rw [subflagPairDensity_out, subflagDensity_out, subflagDensity_out]
    have h0 := abs_flagPairDensity_sub_mul_le (Quotient.out Fi)
      (Quotient.out Fj) (Quotient.out H) (by simpa using hℓ)
      (by simpa using hk)
    simpa using h0
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h'
  rw [Nat.cast_mul]
  exact h'

variable [𝕋.IsType σ] [𝕋.IsType (emptyType S)]

/-- A positive homomorphism sends the downward image of `1` into `[−∞, 1]`:
the image is a single flag scaled by a normalizing factor in `[0, 1]`. -/
theorem positiveHom_downward_one_le (φ : PositiveHom 𝕋 (emptyType S)) :
    φ (downward (1 : FlagAlgebra 𝕋 σ)) ≤ 1 := by
  rw [show (1 : FlagAlgebra 𝕋 σ)
      = ⟦basisVector (1 : FinFlag 𝕋 σ)⟧ from rfl,
    downward_basis, PositiveHom.map_smul]
  have hq1 : labelingFactor (Quotient.out (1 : FinFlag 𝕋 σ).2).unlabel
      (Quotient.out (1 : FinFlag 𝕋 σ).2) ≤ 1 :=
    labelingFactor_le_one _ _
  have hφ1 := positiveHom_basisVector_le_one φ
    ⟨(1 : FinFlag 𝕋 σ).1,
      (Quotient.out (1 : FinFlag 𝕋 σ).2).unlabel.toFlag⟩
  have hφ0 := positiveHom_basisVector_nonneg φ
    ⟨(1 : FinFlag 𝕋 σ).1,
      (Quotient.out (1 : FinFlag 𝕋 σ).2).unlabel.toFlag⟩
  have hq1' : ((labelingFactor (Quotient.out (1 : FinFlag 𝕋 σ).2).unlabel
      (Quotient.out (1 : FinFlag 𝕋 σ).2) : ℚ) : ℝ) ≤ 1 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hq1
    rwa [Rat.cast_one] at h
  exact mul_le_one₀ hq1' hφ0 hφ1

/-- The value of the downward image of `1` expands over any level `ℓ` as the
`q`-weighted sum of unlabeled flag values. -/
private lemma positiveHom_downward_one_expand
    (φ : PositiveHom 𝕋 (emptyType S)) (ℓ : ℕ)
    (hℓ : Fintype.card T ≤ ℓ) :
    φ (downward (1 : FlagAlgebra 𝕋 σ))
      = ∑ H : FlagWithSize 𝕋 σ ℓ,
          ((labelingFactor (Quotient.out H).unlabel
              (Quotient.out H) : ℚ) : ℝ) *
            φ ⟦basisVector ⟨ℓ, (Quotient.out H).unlabel.toFlag⟩⟧ := by
  rw [show (1 : FlagAlgebra 𝕋 σ)
    = ∑ H : FlagWithSize 𝕋 σ ℓ, ⟦basisVector ⟨ℓ, H⟩⟧ from
    (sum_flagWithSize_eq_one ℓ hℓ).symm]
  rw [downward_sum, PositiveHom.map_sum]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [downward_basis, PositiveHom.map_smul]

set_option maxHeartbeats 1600000 in
/-- The uniform lower bound at a single expansion level: the value of a
downward square under a positive homomorphism is at least
`−M·(n−k)²/(ℓ−k)`. -/
private lemma downward_square_step {n : ℕ} (c : FlagWithSize 𝕋 σ n → ℝ)
    (x : FlagAlgebra 𝕋 σ)
    (hrep : x = ∑ F' : FlagWithSize 𝕋 σ n, c F' • ⟦basisVector ⟨n, F'⟩⟧)
    (φ : PositiveHom 𝕋 (emptyType S)) {ℓ : ℕ}
    (hℓ' : n + n ≤ ℓ + Fintype.card T) (hk' : Fintype.card T < ℓ) :
    -((∑ Fi : FlagWithSize 𝕋 σ n, |c Fi|) ^ 2 *
        ((((n - Fintype.card T) * (n - Fintype.card T) : ℕ) : ℝ) /
          ((ℓ - Fintype.card T : ℕ) : ℝ)))
      ≤ φ (downward (x * x)) := by
  set M : ℝ := (∑ Fi : FlagWithSize 𝕋 σ n, |c Fi|) ^ 2 with hM
  set B : ℝ := (((n - Fintype.card T) * (n - Fintype.card T) : ℕ) : ℝ) /
    ((ℓ - Fintype.card T : ℕ) : ℝ) with hB
  have hM0 : (0:ℝ) ≤ M := sq_nonneg _
  have hB0 : (0:ℝ) ≤ B := by
    rw [hB]
    positivity
  have hxx : x * x = ∑ H : FlagWithSize 𝕋 σ ℓ,
      (∑ Fi : FlagWithSize 𝕋 σ n, ∑ Fj : FlagWithSize 𝕋 σ n,
        c Fi * c Fj * ((subflagPairDensity Fi Fj H : ℚ) : ℝ)) •
        (⟦basisVector ⟨ℓ, H⟩⟧ : FlagAlgebra 𝕋 σ) := by
    rw [hrep, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl fun Fi _ => Finset.sum_congr rfl fun Fj _ => by
      rw [flagAlgebra_smul_mul_smul_comm,
        basisVector_quot_mul_eq_flagMulWithSize_quot
          (⟨n, Fi⟩ : FinFlag 𝕋 σ) (⟨n, Fj⟩ : FinFlag 𝕋 σ) ℓ
          (by simpa using hℓ'),
        show flagMulWithSize (⟨n, Fi⟩ : FinFlag 𝕋 σ) ⟨n, Fj⟩ ℓ
            = ∑ H : FlagWithSize 𝕋 σ ℓ,
              ((subflagPairDensity Fi Fj H : ℚ) : ℝ) •
                basisVector ⟨ℓ, H⟩ from rfl,
        sum_quot,
        Finset.sum_congr rfl fun H _ => smul_quot _ _,
        Finset.smul_sum]]
    rw [Finset.sum_congr rfl fun Fi _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun Fi _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun Fj _ => ?_
    rw [smul_smul]
  have hφval : φ (downward (x * x))
      = ∑ H : FlagWithSize 𝕋 σ ℓ,
          (∑ Fi : FlagWithSize 𝕋 σ n, ∑ Fj : FlagWithSize 𝕋 σ n,
            c Fi * c Fj * ((subflagPairDensity Fi Fj H : ℚ) : ℝ)) *
          (((labelingFactor (Quotient.out H).unlabel
              (Quotient.out H) : ℚ) : ℝ) *
            φ ⟦basisVector
              ⟨ℓ, (Quotient.out H).unlabel.toFlag⟩⟧) := by
    rw [hxx, downward_sum, PositiveHom.map_sum]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [downward_smul, downward_basis, PositiveHom.map_smul,
      PositiveHom.map_smul]
  have hQH : ∀ H : FlagWithSize 𝕋 σ ℓ,
      -(M * B) ≤ ∑ Fi : FlagWithSize 𝕋 σ n, ∑ Fj : FlagWithSize 𝕋 σ n,
        c Fi * c Fj * ((subflagPairDensity Fi Fj H : ℚ) : ℝ) := by
    intro H
    have habs : ∀ Fi Fj : FlagWithSize 𝕋 σ n,
        |c Fi * c Fj *
          (((subflagPairDensity Fi Fj H : ℚ) : ℝ)
            - ((subflagDensity Fi H : ℚ) : ℝ) *
              ((subflagDensity Fj H : ℚ) : ℝ))|
          ≤ |c Fi| * |c Fj| * B := by
      intro Fi Fj
      rw [abs_mul, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hB]
      exact abs_subflag_estimate Fi Fj H hℓ' hk'
    have hsplit : (∑ Fi : FlagWithSize 𝕋 σ n, ∑ Fj : FlagWithSize 𝕋 σ n,
          c Fi * c Fj * ((subflagPairDensity Fi Fj H : ℚ) : ℝ))
        = (∑ Fi : FlagWithSize 𝕋 σ n,
            c Fi * ((subflagDensity Fi H : ℚ) : ℝ)) ^ 2
          + ∑ Fi : FlagWithSize 𝕋 σ n, ∑ Fj : FlagWithSize 𝕋 σ n,
              c Fi * c Fj *
                (((subflagPairDensity Fi Fj H : ℚ) : ℝ)
                  - ((subflagDensity Fi H : ℚ) : ℝ) *
                    ((subflagDensity Fj H : ℚ) : ℝ)) := by
      rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun Fi _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun Fj _ => ?_
      ring
    have hsum_eq : (∑ Fi : FlagWithSize 𝕋 σ n,
          ∑ Fj : FlagWithSize 𝕋 σ n, |c Fi| * |c Fj| * B)
        = M * B := by
      rw [hM, sq, Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun Fi _ => ?_
      rw [Finset.sum_mul]
    have h2 : -(M * B) ≤ ∑ Fi : FlagWithSize 𝕋 σ n,
        ∑ Fj : FlagWithSize 𝕋 σ n,
          c Fi * c Fj *
            (((subflagPairDensity Fi Fj H : ℚ) : ℝ)
              - ((subflagDensity Fi H : ℚ) : ℝ) *
                ((subflagDensity Fj H : ℚ) : ℝ)) := by
      calc -(M * B)
          = ∑ Fi : FlagWithSize 𝕋 σ n, ∑ Fj : FlagWithSize 𝕋 σ n,
              -(|c Fi| * |c Fj| * B) := by
            rw [← hsum_eq]
            simp
        _ ≤ _ := by
            refine Finset.sum_le_sum fun Fi _ =>
              Finset.sum_le_sum fun Fj _ => ?_
            have h0 := neg_abs_le (c Fi * c Fj *
              (((subflagPairDensity Fi Fj H : ℚ) : ℝ)
                - ((subflagDensity Fi H : ℚ) : ℝ) *
                  ((subflagDensity Fj H : ℚ) : ℝ)))
            have h1 := habs Fi Fj
            linarith
    have h1 : (0:ℝ) ≤ (∑ Fi : FlagWithSize 𝕋 σ n,
        c Fi * ((subflagDensity Fi H : ℚ) : ℝ)) ^ 2 := sq_nonneg _
    rw [hsplit]
    linarith
  have hone := positiveHom_downward_one_expand (σ := σ) φ ℓ (le_of_lt hk')
  have hone_le := positiveHom_downward_one_le (σ := σ) φ
  have hMB : -(M * B) ≤ 0 := neg_nonpos.mpr (mul_nonneg hM0 hB0)
  calc -(M * B) = -(M * B) * 1 := (mul_one _).symm
    _ ≤ -(M * B) * φ (downward (1 : FlagAlgebra 𝕋 σ)) :=
        mul_le_mul_of_nonpos_left hone_le hMB
    _ = -(M * B) * (∑ H : FlagWithSize 𝕋 σ ℓ,
          ((labelingFactor (Quotient.out H).unlabel
              (Quotient.out H) : ℚ) : ℝ) *
            φ ⟦basisVector ⟨ℓ, (Quotient.out H).unlabel.toFlag⟩⟧) := by
        rw [hone]
    _ = ∑ H : FlagWithSize 𝕋 σ ℓ,
          -(M * B) *
            (((labelingFactor (Quotient.out H).unlabel
                (Quotient.out H) : ℚ) : ℝ) *
              φ ⟦basisVector ⟨ℓ, (Quotient.out H).unlabel.toFlag⟩⟧) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ H : FlagWithSize 𝕋 σ ℓ,
          (∑ Fi : FlagWithSize 𝕋 σ n, ∑ Fj : FlagWithSize 𝕋 σ n,
            c Fi * c Fj * ((subflagPairDensity Fi Fj H : ℚ) : ℝ)) *
          (((labelingFactor (Quotient.out H).unlabel
              (Quotient.out H) : ℚ) : ℝ) *
            φ ⟦basisVector ⟨ℓ, (Quotient.out H).unlabel.toFlag⟩⟧) := by
        refine Finset.sum_le_sum fun H _ => ?_
        refine mul_le_mul_of_nonneg_right (hQH H) ?_
        refine mul_nonneg ?_ (positiveHom_basisVector_nonneg φ
          ⟨ℓ, (Quotient.out H).unlabel.toFlag⟩)
        have hq := labelingFactor_nonneg (Quotient.out H).unlabel
          (Quotient.out H)
        have hq' := (Rat.cast_le (K := ℝ)).mpr hq
        rwa [Rat.cast_zero] at hq'
    _ = φ (downward (x * x)) := by rw [hφval]

/-- **Square positivity** (Razborov Theorem 3.14): the downward image of a
square is nonnegative in the semantic order of the empty-type algebra. -/
theorem downward_square_nonneg (x : FlagAlgebra 𝕋 σ) :
    (0 : FlagAlgebra 𝕋 (emptyType S)) ≤ downward (x * x) := by
  intro φ
  rw [sub_zero]
  by_contra hneg
  push_neg at hneg
  obtain ⟨n, c, hrep⟩ := exists_level_expansion x
  set M : ℝ := (∑ Fi : FlagWithSize 𝕋 σ n, |c Fi|) ^ 2 with hM
  set y := φ (downward (x * x)) with hy
  obtain ⟨N, hN⟩ := exists_nat_gt
    (M * (((n - Fintype.card T) * (n - Fintype.card T) : ℕ) : ℝ) / (-y))
  have hy0 : (0:ℝ) < -y := by linarith
  set ℓ := Fintype.card T + N + 2 * n + 1 with hℓdef
  have hb := downward_square_step c x hrep φ
    (ℓ := ℓ) (by omega) (by omega)
  rw [← hM, ← hy] at hb
  have hden : (0:ℝ) < ((ℓ - Fintype.card T : ℕ) : ℝ) := by
    have h0 : 0 < ℓ - Fintype.card T := by omega
    exact_mod_cast h0
  have hNden : (N : ℝ) ≤ ((ℓ - Fintype.card T : ℕ) : ℝ) := by
    have h0 : N ≤ ℓ - Fintype.card T := by omega
    exact_mod_cast h0
  rw [div_lt_iff₀ hy0] at hN
  have hlt2 : M * ((((n - Fintype.card T) *
      (n - Fintype.card T) : ℕ) : ℝ) /
        ((ℓ - Fintype.card T : ℕ) : ℝ)) < -y := by
    rw [← mul_div_assoc, div_lt_iff₀ hden]
    calc M * (((n - Fintype.card T) * (n - Fintype.card T) : ℕ) : ℝ)
        < (N : ℝ) * (-y) := hN
      _ ≤ ((ℓ - Fintype.card T : ℕ) : ℝ) * (-y) :=
          mul_le_mul_of_nonneg_right hNden (le_of_lt hy0)
      _ = -y * ((ℓ - Fintype.card T : ℕ) : ℝ) := mul_comm _ _
  linarith [hb]

/-- The sum-of-squares certificate primitive: any combination of downward
squares with nonnegative coefficients is nonnegative in the semantic
order. This is the exact shape in which semidefinite certificates enter
flag-algebra proofs. -/
theorem downward_sos_nonneg {ι : Type} (s : Finset ι) (q : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (x : ι → FlagAlgebra 𝕋 σ) :
    (0 : FlagAlgebra 𝕋 (emptyType S))
      ≤ ∑ i ∈ s, q i • downward (x i * x i) := by
  calc (0 : FlagAlgebra 𝕋 (emptyType S))
      = ∑ i ∈ s, (0 : FlagAlgebra 𝕋 (emptyType S)) :=
        Finset.sum_const_zero.symm
    _ ≤ ∑ i ∈ s, q i • downward (x i * x i) :=
        flag_sum_le_sum fun i hi => by
          have h := flag_smul_le_smul (hq i hi)
            (downward_square_nonneg (x i))
          rwa [zero_smul] at h

/-- The value of a downward square is nonnegative, pointwise. -/
theorem positiveHom_downward_square_nonneg
    (φ : PositiveHom 𝕋 (emptyType S)) (x : FlagAlgebra 𝕋 σ) :
    0 ≤ φ (downward (x * x)) := by
  have h := downward_square_nonneg x φ
  rwa [sub_zero] at h

/-- The value of the downward unit is nonnegative: it is its own square. -/
theorem positiveHom_downward_one_nonneg
    (φ : PositiveHom 𝕋 (emptyType S)) :
    0 ≤ φ (downward (1 : FlagAlgebra 𝕋 σ)) := by
  have h := positiveHom_downward_square_nonneg φ (1 : FlagAlgebra 𝕋 σ)
  rwa [mul_one] at h

/-- **The flag-algebra Cauchy–Schwarz inequality** (Razborov, the working
corollary of Theorem 3.14): under any positive homomorphism, the squared
value of a downward image is at most the value of the downward square
times the value of the downward unit. Proved by the discriminant of the
square family `⟦(x − c·1)²⟧↓ ≥ 0`. -/
theorem positiveHom_downward_cauchy_schwarz
    (φ : PositiveHom 𝕋 (emptyType S)) (x : FlagAlgebra 𝕋 σ) :
    φ (downward x) ^ 2
      ≤ φ (downward (x * x)) * φ (downward (1 : FlagAlgebra 𝕋 σ)) := by
  have hq : ∀ c : ℝ,
      0 ≤ φ (downward (1 : FlagAlgebra 𝕋 σ)) * (c * c)
        + (-(2 * φ (downward x))) * c + φ (downward (x * x)) := by
    intro c
    have hsq : (x - c • (1 : FlagAlgebra 𝕋 σ)) * (x - c • 1)
        = x * x - (2 * c) • x + (c * c) • 1 := by
      rw [sub_mul, mul_sub, mul_sub, mul_smul_comm, mul_one,
        smul_mul_assoc, one_mul, smul_mul_assoc, one_mul, smul_smul,
        show (2 * c) = c + c from by ring, add_smul]
      abel
    have h := positiveHom_downward_square_nonneg φ
      (x - c • (1 : FlagAlgebra 𝕋 σ))
    rw [hsq, downward_add, downward_sub, downward_smul, downward_smul,
      PositiveHom.map_add, PositiveHom.map_sub, PositiveHom.map_smul,
      PositiveHom.map_smul] at h
    nlinarith [h]
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith [hd]

/-- The downward value of a square dominates the square of the downward
value: Cauchy–Schwarz with the unit bound. -/
theorem positiveHom_downward_sq_le
    (φ : PositiveHom 𝕋 (emptyType S)) (x : FlagAlgebra 𝕋 σ) :
    φ (downward x) ^ 2 ≤ φ (downward (x * x)) := by
  have hcs := positiveHom_downward_cauchy_schwarz φ x
  have h1 := positiveHom_downward_one_le (σ := σ) φ
  have h0 := positiveHom_downward_square_nonneg φ x
  nlinarith

/-- **The SOS certificate assembly**: if `c·1` decomposes as the target
element plus a nonnegative combination of downward squares plus a
nonnegative combination of nonnegative elements, then the target is
bounded by `c·1` in the semantic order. Every semidefinite certificate
enters a bound proof through this theorem: the representation `hrep` is
the coefficient identity checked on literal tables, the squares carry
the semidefinite part, and the remainder carries the slack at each
expansion class. -/
theorem le_smul_one_of_sos_decomp {c : ℝ} {ι κ : Type}
    (s : Finset ι) (t : Finset κ)
    (q : ι → ℝ) (hq : ∀ i ∈ s, 0 ≤ q i) (x : ι → FlagAlgebra 𝕋 σ)
    (d : κ → ℝ) (hd : ∀ j ∈ t, 0 ≤ d j)
    (B : κ → FlagAlgebra 𝕋 (emptyType S))
    (hB : ∀ j ∈ t, (0 : FlagAlgebra 𝕋 (emptyType S)) ≤ B j)
    (e : FlagAlgebra 𝕋 (emptyType S))
    (hrep : c • (1 : FlagAlgebra 𝕋 (emptyType S))
      = e + (∑ i ∈ s, q i • downward (x i * x i)) + ∑ j ∈ t, d j • B j) :
    e ≤ c • 1 := by
  have hS := downward_sos_nonneg s q hq x
  have hT : (0 : FlagAlgebra 𝕋 (emptyType S)) ≤ ∑ j ∈ t, d j • B j := by
    calc (0 : FlagAlgebra 𝕋 (emptyType S))
        = ∑ j ∈ t, (0 : FlagAlgebra 𝕋 (emptyType S)) :=
          Finset.sum_const_zero.symm
      _ ≤ ∑ j ∈ t, d j • B j :=
          flag_sum_le_sum fun j hj => by
            have h := flag_smul_le_smul (hd j hj) (hB j hj)
            rwa [zero_smul] at h
  intro φ
  have hsplit : c • (1 : FlagAlgebra 𝕋 (emptyType S)) - e
      = (∑ i ∈ s, q i • downward (x i * x i)) + ∑ j ∈ t, d j • B j := by
    rw [hrep]
    abel
  rw [hsplit, PositiveHom.map_add]
  have h1 := hS φ
  have h2 := hT φ
  rw [sub_zero] at h1 h2
  linarith

end FlagAlgebras.Core
