import LeanFlagAlgebras.Core.SquarePositivity

/-! # Core: the stationarity element

Certificates that beat pure sums of squares add a *stationarity* term —
an element whose value vanishes exactly for the extremal homomorphisms,
and which therefore costs nothing at the optimum while tightening the
bound everywhere the certificate is checked.

For a rooted quantity `x`, the stationarity element is

  `stationarity x = x↓ · x↓ − (x · x)↓`,

the negated variance of `x` across the rooting. Two facts make it
usable. First, its value is *always* nonpositive — that is exactly the
Cauchy–Schwarz inequality of `SquarePositivity`, so it is free. Second,
for a homomorphism at which the value is nonnegative — the equality case,
which is what extremality supplies — a certificate carrying a
nonnegative multiple of the stationarity term still yields its bound
(`positiveHom_le_of_stationarity_decomp`).

The second hypothesis is where the extremal input enters: nothing here
proves that a particular homomorphism is stationary. That is a semantic
statement about maximizers (Razborov's differential method), and it is
kept as an explicit hypothesis so that everything downstream of it is
unconditional. -/

namespace FlagAlgebras.Core

variable {S : Signature} {T : Type} [Fintype T] [S.NullaryFree]
variable {𝕋 : RelTheory S} {σ : Model S T}

section

variable [𝕋.IsType σ] [𝕋.IsType (emptyType S)]

/-- The stationarity element of a rooted quantity: the negated variance
of `x` across the rooting, `x↓ · x↓ − (x · x)↓`. -/
noncomputable def stationarity (x : FlagAlgebra 𝕋 σ) :
    FlagAlgebra 𝕋 (emptyType S) :=
  downward x * downward x - downward (x * x)

/-- **The stationarity element is never positive.** Its value is minus a
variance, so this is the flag-algebra Cauchy–Schwarz inequality read
backwards — no extremality is involved. -/
theorem positiveHom_stationarity_nonpos
    (φ : PositiveHom 𝕋 (emptyType S)) (x : FlagAlgebra 𝕋 σ) :
    φ (stationarity x) ≤ 0 := by
  have hcs := positiveHom_downward_sq_le φ x
  rw [stationarity, PositiveHom.map_sub, PositiveHom.map_mul]
  nlinarith [hcs]

/-- A homomorphism is *stationary* for `x` when the variance of `x`
vanishes: the equality case of Cauchy–Schwarz. Extremal homomorphisms
are stationary for the quantities the certificate differentiates. -/
def IsStationary (φ : PositiveHom 𝕋 (emptyType S)) (x : FlagAlgebra 𝕋 σ) :
    Prop :=
  φ (stationarity x) = 0

/-- Nonnegativity of the value is already stationarity, since the value
is never positive. -/
theorem isStationary_of_nonneg {φ : PositiveHom 𝕋 (emptyType S)}
    {x : FlagAlgebra 𝕋 σ} (h : 0 ≤ φ (stationarity x)) :
    IsStationary φ x :=
  le_antisymm (positiveHom_stationarity_nonpos φ x) h

/-- **Certificate assembly with a stationarity term.** If the unit
decomposes coefficient-wise into the target `e`, nonnegative multiples of
downward squares, a nonnegative multiple of the stationarity element of
`x`, and further nonnegative terms, then every homomorphism stationary
for `x` obeys the bound.

Without the stationarity hypothesis the conclusion is false in general:
the stationarity term has the wrong sign to be discarded, which is
precisely why it sharpens the certificate. -/
theorem positiveHom_le_of_stationarity_decomp
    (φ : PositiveHom 𝕋 (emptyType S)) {c τ : ℝ} {ι κ : Type}
    (s : Finset ι) (t : Finset κ)
    (q : ι → ℝ) (hq : ∀ i ∈ s, 0 ≤ q i) (y : ι → FlagAlgebra 𝕋 σ)
    (d : κ → ℝ) (hd : ∀ j ∈ t, 0 ≤ d j)
    (B : κ → FlagAlgebra 𝕋 (emptyType S))
    (hB : ∀ j ∈ t, (0 : FlagAlgebra 𝕋 (emptyType S)) ≤ B j)
    (x : FlagAlgebra 𝕋 σ) (hstat : IsStationary φ x)
    (e : FlagAlgebra 𝕋 (emptyType S))
    (hrep : c • (1 : FlagAlgebra 𝕋 (emptyType S))
      = e + (∑ i ∈ s, q i • downward (y i * y i)) + τ • stationarity x
        + ∑ j ∈ t, d j • B j) :
    φ e ≤ c := by
  have hsq : 0 ≤ φ (∑ i ∈ s, q i • downward (y i * y i)) := by
    have h := downward_sos_nonneg s q hq y φ
    rwa [sub_zero] at h
  have hrest : 0 ≤ φ (∑ j ∈ t, d j • B j) := by
    have hT : (0 : FlagAlgebra 𝕋 (emptyType S)) ≤ ∑ j ∈ t, d j • B j := by
      calc (0 : FlagAlgebra 𝕋 (emptyType S))
          = ∑ j ∈ t, (0 : FlagAlgebra 𝕋 (emptyType S)) :=
            Finset.sum_const_zero.symm
        _ ≤ ∑ j ∈ t, d j • B j :=
            flag_sum_le_sum fun j hj => by
              have h := flag_smul_le_smul (hd j hj) (hB j hj)
              rwa [zero_smul] at h
    have h := hT φ
    rwa [sub_zero] at h
  have hval := congrArg (fun z => φ z) hrep
  simp only [PositiveHom.map_add, PositiveHom.map_smul,
    PositiveHom.map_one, mul_one] at hval
  rw [hstat, mul_zero] at hval
  linarith

omit [𝕋.IsType σ] in
/-- **The stationarity decomposition with an abstract semidefinite
part.** A certificate of any size mixes squares from several rooting
types at once, and no single `σ` expresses that; here the semidefinite
part enters as an arbitrary nonnegative element, which
`downward_sos_nonneg` supplies one type at a time and addition then
combines.

The stationarity element still has to live at a single type — but that
is no restriction in practice, since a certificate uses one extremality
constraint, not a family of them. -/
theorem positiveHom_le_of_stationarity_nonneg
    (φ : PositiveHom 𝕋 (emptyType S)) {c τ : ℝ}
    {P R e : FlagAlgebra 𝕋 (emptyType S)}
    (hP : (0 : FlagAlgebra 𝕋 (emptyType S)) ≤ P)
    (hR : (0 : FlagAlgebra 𝕋 (emptyType S)) ≤ R)
    {x : FlagAlgebra 𝕋 σ} (hstat : IsStationary φ x)
    (hrep : c • (1 : FlagAlgebra 𝕋 (emptyType S))
      = e + P + τ • stationarity x + R) :
    φ e ≤ c := by
  have hP' : 0 ≤ φ P := by have h := hP φ; rwa [sub_zero] at h
  have hR' : 0 ≤ φ R := by have h := hR φ; rwa [sub_zero] at h
  have hval := congrArg (fun z => φ z) hrep
  simp only [PositiveHom.map_add, PositiveHom.map_smul,
    PositiveHom.map_one, mul_one] at hval
  rw [hstat, mul_zero] at hval
  linarith

end

end FlagAlgebras.Core
