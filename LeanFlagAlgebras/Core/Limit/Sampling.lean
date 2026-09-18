import LeanFlagAlgebras.Core.Limit.Realize

/-! # Core: sampling — the converse half of Razborov's Theorem 3.3

Every positive homomorphism `φ ∈ Hom⁺(A^σ, ℝ)` is realized by a sequence of
finite flags: there are `Gs : ℕ → FinFlag 𝕋 σ` with sizes tending to
infinity and `p(F, Gs k) → φ(F)` for every flag `F`
(`exists_realizedBy`).

Razborov's proof samples a random size-`n` flag from the probability
distribution `G ↦ φ(G)` on the classes of size `n` and shows that the
densities concentrate: `E p(F, G) = φ(F)` (the chain rule read through
`φ`) and `E p(F, G)² ≤ φ(F)² + O(1/n)` (the product estimate against
`φ(F·F) = φ(F)²`), so `Var p(F, G) = O(1/n)`. The formalization keeps the
argument finite and deterministic: the `φ`-weighted average of the
defect functional
`D_m(G) = ∑_{i ≤ m} 2⁻ⁱ (p(F_i, G) − φ(F_i))²`, over the classes of a
suitable size `N(m)`, is at most `2⁻ᵐ`, hence some class `G_m` of that
size has `D_m(G_m) ≤ 2⁻ᵐ`; along `m ↦ G_m` every flag density converges
(`F_i` running through an enumeration of the countably many flags). No
measure theory is used. -/

namespace FlagAlgebras.Core

open Filter Finset Topology

variable {S : Signature} {T : Type} [Fintype T]
variable {𝕋 : RelTheory S} {σ : Model S T} [𝕋.IsType σ]

/-! ## The distribution of a homomorphism at a size, and its moments -/

/-- The weight a positive homomorphism puts on a size-`n` class. -/
noncomputable def weight (φ : PositiveHom 𝕋 σ) {n : ℕ} (G : FlagWithSize 𝕋 σ n) : ℝ :=
  φ ⟦basisVector ⟨n, G⟩⟧

theorem weight_nonneg (φ : PositiveHom 𝕋 σ) {n : ℕ} (G : FlagWithSize 𝕋 σ n) :
    0 ≤ weight φ G :=
  positiveHom_basisVector_nonneg φ _

theorem sum_weight (φ : PositiveHom 𝕋 σ) {n : ℕ} (hn : Fintype.card T ≤ n) :
    ∑ G : FlagWithSize 𝕋 σ n, weight φ G = 1 :=
  sum_positiveHom_basisVector_eq_one φ n hn

/-- **The first moment**: the `φ`-weighted average of `p(F, ·)` over the
classes of size `n ≥ |F|` is `φ(F)` — the chain rule read through `φ`. -/
theorem sum_weight_mul_density (φ : PositiveHom 𝕋 σ) (F : FinFlag 𝕋 σ) {n : ℕ}
    (hF : F.1 ≤ n) :
    ∑ G : FlagWithSize 𝕋 σ n, weight φ G * ((subflagDensity F.2 G : ℚ) : ℝ)
      = φ ⟦basisVector F⟧ := by
  rw [basisVector_quot_eq_sum F n hF, PositiveHom.map_sum]
  refine Finset.sum_congr rfl fun G _ => ?_
  rw [PositiveHom.map_smul, weight, mul_comm]

/-- **The pair moment**: the `φ`-weighted average of the pair density
`p(F, F; ·)` is `φ(F)²`, since `F·F` expands by pair densities. -/
theorem sum_weight_mul_pairDensity (φ : PositiveHom 𝕋 σ) (F : FinFlag 𝕋 σ) {n : ℕ}
    (hF : F.1 + F.1 ≤ n + Fintype.card T) :
    ∑ G : FlagWithSize 𝕋 σ n, weight φ G * ((subflagPairDensity F.2 F.2 G : ℚ) : ℝ)
      = φ ⟦basisVector F⟧ ^ 2 := by
  rw [sq, ← PositiveHom.map_mul, basisVector_quot_mul_eq_flagMulWithSize_quot F F n hF]
  unfold flagMulWithSize
  rw [sum_quot]
  simp_rw [smul_quot]
  rw [PositiveHom.map_sum]
  refine Finset.sum_congr rfl fun G _ => ?_
  rw [PositiveHom.map_smul, weight, mul_comm]

/-- **The second moment** is at most `φ(F)² + (|F|−k)²/(n−k)`, by the
product estimate. -/
theorem sum_weight_mul_sq_density_le (φ : PositiveHom 𝕋 σ) (F : FinFlag 𝕋 σ) {n : ℕ}
    (hF : F.1 + F.1 ≤ n + Fintype.card T) (hn : Fintype.card T < n) :
    ∑ G : FlagWithSize 𝕋 σ n, weight φ G * ((subflagDensity F.2 G : ℚ) : ℝ) ^ 2
      ≤ φ ⟦basisVector F⟧ ^ 2
        + (((F.1 - Fintype.card T) * (F.1 - Fintype.card T) : ℕ) : ℝ)
          / ((n - Fintype.card T : ℕ) : ℝ) := by
  set C : ℝ := (((F.1 - Fintype.card T) * (F.1 - Fintype.card T) : ℕ) : ℝ)
    / ((n - Fintype.card T : ℕ) : ℝ) with hC
  rw [← sum_weight_mul_pairDensity φ F hF]
  calc ∑ G : FlagWithSize 𝕋 σ n, weight φ G * ((subflagDensity F.2 G : ℚ) : ℝ) ^ 2
      ≤ ∑ G : FlagWithSize 𝕋 σ n,
          weight φ G * (((subflagPairDensity F.2 F.2 G : ℚ) : ℝ) + C) := by
        refine Finset.sum_le_sum fun G _ => mul_le_mul_of_nonneg_left ?_ (weight_nonneg φ G)
        have h := abs_subflagPairDensity_sub_mul_le F.2 F.2 G hF hn
        rw [abs_le] at h
        rw [sq]
        linarith [h.1]
    _ = ∑ G : FlagWithSize 𝕋 σ n, weight φ G * ((subflagPairDensity F.2 F.2 G : ℚ) : ℝ)
          + (∑ G : FlagWithSize 𝕋 σ n, weight φ G) * C := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun G _ => ?_
        ring
    _ = _ := by rw [sum_weight φ (by omega), one_mul]

/-- **The variance bound**: the `φ`-weighted mean square of
`p(F, ·) − φ(F)` is at most `(|F|−k)²/(n−k)`. -/
theorem sum_weight_mul_sq_sub_le (φ : PositiveHom 𝕋 σ) (F : FinFlag 𝕋 σ) {n : ℕ}
    (hF : F.1 + F.1 ≤ n + Fintype.card T) (hn : Fintype.card T < n) :
    ∑ G : FlagWithSize 𝕋 σ n,
        weight φ G * (((subflagDensity F.2 G : ℚ) : ℝ) - φ ⟦basisVector F⟧) ^ 2
      ≤ (((F.1 - Fintype.card T) * (F.1 - Fintype.card T) : ℕ) : ℝ)
          / ((n - Fintype.card T : ℕ) : ℝ) := by
  have hk : Fintype.card T ≤ F.1 := finFlag_size_ge F
  have h1 := sum_weight_mul_density φ F (by omega : F.1 ≤ n)
  have h2 := sum_weight_mul_sq_density_le φ F hF hn
  have h3 := sum_weight φ (by omega : Fintype.card T ≤ n)
  set c := φ ⟦basisVector F⟧ with hc
  have hexp : ∑ G : FlagWithSize 𝕋 σ n,
      weight φ G * (((subflagDensity F.2 G : ℚ) : ℝ) - c) ^ 2
      = ∑ G : FlagWithSize 𝕋 σ n, weight φ G * ((subflagDensity F.2 G : ℚ) : ℝ) ^ 2
        - 2 * c * ∑ G : FlagWithSize 𝕋 σ n, weight φ G * ((subflagDensity F.2 G : ℚ) : ℝ)
        + c ^ 2 * ∑ G : FlagWithSize 𝕋 σ n, weight φ G := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun G _ => ?_
    ring
  rw [hexp, h1, h3]
  linarith [h2]

/-! ## A class with small weighted defect -/

/-- A quantity whose `φ`-weighted average is at most `δ` is at most `δ` at
some class. -/
theorem exists_le_of_sum_weight_mul_le (φ : PositiveHom 𝕋 σ) {n : ℕ}
    (hn : Fintype.card T ≤ n) (D : FlagWithSize 𝕋 σ n → ℝ) {δ : ℝ}
    (h : ∑ G : FlagWithSize 𝕋 σ n, weight φ G * D G ≤ δ) :
    ∃ G : FlagWithSize 𝕋 σ n, D G ≤ δ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨G₀, hG₀⟩ : ∃ G : FlagWithSize 𝕋 σ n, 0 < weight φ G := by
    by_contra hall
    push_neg at hall
    have hzero : ∑ G : FlagWithSize 𝕋 σ n, weight φ G = 0 :=
      Finset.sum_eq_zero fun G _ => le_antisymm (hall G) (weight_nonneg φ G)
    rw [sum_weight φ hn] at hzero
    exact one_ne_zero hzero
  have hlt : ∑ G : FlagWithSize 𝕋 σ n, weight φ G * δ
      < ∑ G : FlagWithSize 𝕋 σ n, weight φ G * D G :=
    Finset.sum_lt_sum (fun G _ => mul_le_mul_of_nonneg_left (hcon G).le (weight_nonneg φ G))
      ⟨G₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hcon G₀) hG₀⟩
  rw [← Finset.sum_mul, sum_weight φ hn, one_mul] at hlt
  linarith

/-! ## The realizing sequence -/

section Sequence

variable (φ : PositiveHom 𝕋 σ) (e : ℕ → FinFlag 𝕋 σ)

/-- The defect functional at level `m`: the `2⁻ⁱ`-weighted squared
deviations of the densities of the first `m + 1` enumerated flags. -/
noncomputable def defect (m : ℕ) {n : ℕ} (G : FlagWithSize 𝕋 σ n) : ℝ :=
  ∑ i ∈ Finset.range (m + 1),
    (1 / 2 : ℝ) ^ i * (((subflagDensity (e i).2 G : ℚ) : ℝ) - φ ⟦basisVector (e i)⟧) ^ 2

theorem defect_nonneg (m : ℕ) {n : ℕ} (G : FlagWithSize 𝕋 σ n) : 0 ≤ defect φ e m G :=
  Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (sq_nonneg _)

theorem term_le_defect {m i : ℕ} (hi : i ≤ m) {n : ℕ} (G : FlagWithSize 𝕋 σ n) :
    (1 / 2 : ℝ) ^ i * (((subflagDensity (e i).2 G : ℚ) : ℝ) - φ ⟦basisVector (e i)⟧) ^ 2
      ≤ defect φ e m G :=
  Finset.single_le_sum (f := fun i =>
      (1 / 2 : ℝ) ^ i * (((subflagDensity (e i).2 G : ℚ) : ℝ) - φ ⟦basisVector (e i)⟧) ^ 2)
    (fun i _ => mul_nonneg (by positivity) (sq_nonneg _))
    (Finset.mem_range.mpr (by omega))

/-- The size bound and the variance sum of the first `m + 1` flags. -/
noncomputable def sizeSup (m : ℕ) : ℕ :=
  (Finset.range (m + 1)).sup fun i => (e i).1

noncomputable def varSum (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (m + 1), ((e i).1 - Fintype.card T) * ((e i).1 - Fintype.card T)

/-- The host size at level `m`. -/
noncomputable def hostSize (m : ℕ) : ℕ :=
  Fintype.card T + 2 ^ m * (varSum e m + 1) + 2 * sizeSup e m

theorem le_hostSize (m : ℕ) : m ≤ hostSize e m := by
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 : 2 ^ m ≤ 2 ^ m * (varSum e m + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold hostSize
  omega

/-- The weighted average of the level-`m` defect over the classes of size
`hostSize m` is at most `2⁻ᵐ`. -/
theorem sum_weight_mul_defect_le (m : ℕ) :
    ∑ G : FlagWithSize 𝕋 σ (hostSize e m), weight φ G * defect φ e m G ≤ (1 / 2 : ℝ) ^ m := by
  set k := Fintype.card T with hk
  set n := hostSize e m with hn
  have hkn : k < n := by
    have : 1 ≤ 2 ^ m * (varSum e m + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    unfold hostSize at hn
    omega
  have hsize : ∀ i ∈ Finset.range (m + 1), (e i).1 + (e i).1 ≤ n + k := by
    intro i hi
    have : (e i).1 ≤ sizeSup e m := Finset.le_sup (f := fun i => (e i).1) hi
    unfold hostSize at hn
    omega
  have hnk : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hkn
  -- exchange the sums and bound each variance
  unfold defect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc]
  calc ∑ i ∈ Finset.range (m + 1), ∑ G : FlagWithSize 𝕋 σ n,
        weight φ G * (1 / 2 : ℝ) ^ i
          * (((subflagDensity (e i).2 G : ℚ) : ℝ) - φ ⟦basisVector (e i)⟧) ^ 2
      = ∑ i ∈ Finset.range (m + 1), (1 / 2 : ℝ) ^ i * ∑ G : FlagWithSize 𝕋 σ n,
          weight φ G * (((subflagDensity (e i).2 G : ℚ) : ℝ) - φ ⟦basisVector (e i)⟧) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun G _ => ?_
        ring
    _ ≤ ∑ i ∈ Finset.range (m + 1), (1 / 2 : ℝ) ^ i
          * ((((e i).1 - k) * ((e i).1 - k) : ℕ) : ℝ) / ((n - k : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (sum_weight_mul_sq_sub_le φ (e i) (hsize i hi) hkn)
          (by positivity)
    _ ≤ ∑ i ∈ Finset.range (m + 1),
          ((((e i).1 - k) * ((e i).1 - k) : ℕ) : ℝ) / ((n - k : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [mul_div_assoc]
        refine mul_le_of_le_one_left (by positivity) ?_
        exact pow_le_one₀ (by norm_num) (by norm_num)
    _ = (varSum e m : ℝ) / ((n - k : ℕ) : ℝ) := by
        rw [← Finset.sum_div, varSum]
        push_cast
        rfl
    _ ≤ (1 / 2 : ℝ) ^ m := by
        rw [div_le_iff₀ hnk]
        have h1 : ((2 ^ m * (varSum e m + 1) : ℕ) : ℝ) ≤ ((n - k : ℕ) : ℝ) := by
          exact_mod_cast (show 2 ^ m * (varSum e m + 1) ≤ n - k by
            unfold hostSize at hn; omega)
        have h2 : (1 / 2 : ℝ) ^ m * ((2 ^ m * (varSum e m + 1) : ℕ) : ℝ) = varSum e m + 1 := by
          push_cast
          rw [one_div, inv_pow, inv_mul_cancel_left₀ (by positivity)]
        calc (varSum e m : ℝ) ≤ varSum e m + 1 := by linarith
          _ = (1 / 2 : ℝ) ^ m * ((2 ^ m * (varSum e m + 1) : ℕ) : ℝ) := h2.symm
          _ ≤ (1 / 2 : ℝ) ^ m * ((n - k : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)

/-- A class of size `hostSize m` with level-`m` defect at most `2⁻ᵐ`. -/
theorem exists_defect_le (m : ℕ) :
    ∃ G : FlagWithSize 𝕋 σ (hostSize e m), defect φ e m G ≤ (1 / 2 : ℝ) ^ m :=
  exists_le_of_sum_weight_mul_le φ (by unfold hostSize; omega) _
    (sum_weight_mul_defect_le φ e m)

/-- The sampled sequence: at level `m`, a class of size `hostSize m` with
defect at most `2⁻ᵐ`. -/
noncomputable def sampled (m : ℕ) : FinFlag 𝕋 σ :=
  ⟨hostSize e m, Classical.choose (exists_defect_le φ e m)⟩

theorem sampled_fst (m : ℕ) : (sampled φ e m).1 = hostSize e m :=
  rfl

theorem defect_sampled_le (m : ℕ) :
    defect φ e m (sampled φ e m).2 ≤ (1 / 2 : ℝ) ^ m :=
  Classical.choose_spec (exists_defect_le φ e m)

/-- Along the sampled sequence, the density of every enumerated flag
converges to its `φ`-value. -/
theorem tendsto_sampled (he : Function.Surjective e) (F : FinFlag 𝕋 σ) :
    Tendsto (fun m => ((subflagDensity F.2 (sampled φ e m).2 : ℚ) : ℝ)) atTop
      (𝓝 (φ ⟦basisVector F⟧)) := by
  obtain ⟨i₀, rfl⟩ := he F
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hgeom : Tendsto (fun m => (2 : ℝ) ^ i₀ * (1 / 2 : ℝ) ^ m) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul ((2 : ℝ) ^ i₀)
    rwa [mul_zero] at this
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp hgeom) (ε ^ 2) (by positivity)
  refine ⟨max M i₀, fun m hm => ?_⟩
  have hM' := hM m (le_of_max_le_left hm)
  have hi₀ : i₀ ≤ m := le_of_max_le_right hm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hM'
  have hterm := (term_le_defect φ e hi₀ (sampled φ e m).2).trans (defect_sampled_le φ e m)
  have hsq : (((subflagDensity (e i₀).2 (sampled φ e m).2 : ℚ) : ℝ)
      - φ ⟦basisVector (e i₀)⟧) ^ 2 ≤ (2 : ℝ) ^ i₀ * (1 / 2 : ℝ) ^ m := by
    have h2 : (2 : ℝ) ^ i₀ * (1 / 2 : ℝ) ^ i₀ = 1 := by
      rw [← mul_pow]
      norm_num
    calc (((subflagDensity (e i₀).2 (sampled φ e m).2 : ℚ) : ℝ)
          - φ ⟦basisVector (e i₀)⟧) ^ 2
        = (2 : ℝ) ^ i₀ * ((1 / 2 : ℝ) ^ i₀ * (((subflagDensity (e i₀).2 (sampled φ e m).2 : ℚ) : ℝ)
            - φ ⟦basisVector (e i₀)⟧) ^ 2) := by
          rw [← mul_assoc, h2, one_mul]
      _ ≤ (2 : ℝ) ^ i₀ * (1 / 2 : ℝ) ^ m :=
          mul_le_mul_of_nonneg_left hterm (by positivity)
  rw [Real.dist_eq]
  exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt hsq hM') hε.le

end Sequence

/-- **Razborov's Theorem 3.3, sampling direction.** Every positive
homomorphism is realized by a sequence of finite flags. -/
theorem exists_realizedBy (φ : PositiveHom 𝕋 σ) :
    ∃ Gs : ℕ → FinFlag 𝕋 σ, RealizedBy φ Gs := by
  haveI : Nonempty (FinFlag 𝕋 σ) := ⟨1⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (FinFlag 𝕋 σ)
  refine ⟨sampled φ e, ?_, fun F => tendsto_sampled φ e he F⟩
  exact tendsto_atTop_mono (fun m => le_hostSize e m) tendsto_id

end FlagAlgebras.Core
