import LeanFlagAlgebras.Core.Differential.Maximizer
import LeanFlagAlgebras.Core.Limit.Sampling
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # Core: Razborov's Theorem 4.3 for a `C¹` objective

Razborov states the differential method for objectives of the form
`φ ↦ F(φ(f₁), …, φ(f_k))` with `F` continuously differentiable, not only for
linear ones. Let `φ₀` maximize such an objective over the positive
homomorphisms, let `x₀ = (φ₀(f₁), …, φ₀(f_k))`, and let `L = dF(x₀)`. Then,
almost surely under a weak limit `ℙ` of the empirical rooting measures along
a sequence realizing `φ₀`, the derivative of the objective along the vertex
differential vanishes at the random rooted homomorphism:

  `∑ᵢ ∂ᵢF(x₀) · φ¹(∂₁ fᵢ) = 0`   (`ae_fderiv_partialVertexVec_eq_zero`).

Only differentiability of `F` at `x₀` is used (`HasFDerivAt`); the `C¹` form
is `ae_fderiv_partialVertexVec_eq_zero_of_contDiff`, and
`exists_weakLimit_ae_fderiv_eq_zero` drops the realizing sequence.

The proof runs the deletion core of the linear case
(`exists_deletion_of_pos_measure`) on the *linearized* objective
`g = ∑ᵢ ∂ᵢF(x₀) • fᵢ`. If `ℙ(∂₁ g > 0) > 0`, deleting `n/K` well-chosen
vertices of a large host raises `p(g, ·)` by `ε/(8K)` while moving every
coordinate `p(fᵢ, ·)` by at most `M/K`, so the deleted host stays within `r`
of `x₀`. There the first-order condition at the maximizer,
`L(y − x₀) ≤ θ ‖y − x₀‖` for homomorphisms `y` near `x₀`
(`exists_radius_fderiv_le`, from differentiability and maximality), holds up
to `η` at all large finite hosts (`exists_size_fderiv_le`, by compactness),
and contradicts the gain once `K` is large and `θ` is small. -/

namespace FlagAlgebras.Core

open Filter Topology MeasureTheory Finset
open Classical

variable {S : Signature} [S.NullaryFree] {𝕋 : RelTheory S}

/-! ## The linearization of an objective -/

section Linearize

/-- The coefficients of a continuous linear functional on `Fin k → ℝ`. -/
noncomputable def coeff {k : ℕ} (L : (Fin k → ℝ) →L[ℝ] ℝ) (i : Fin k) : ℝ :=
  L fun j => if i = j then 1 else 0

theorem apply_eq_sum_coeff {k : ℕ} (L : (Fin k → ℝ) →L[ℝ] ℝ) (y : Fin k → ℝ) :
    L y = ∑ i, coeff L i * y i := by
  have h := LinearMap.pi_apply_eq_sum_univ (L : (Fin k → ℝ) →ₗ[ℝ] ℝ) y
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

variable [𝕋.IsType (emptyType S)]

/-- The linearization `∑ᵢ ∂ᵢF(x₀) • fᵢ` of an objective `F(φ(f₁), …, φ(f_k))`
at a point where the derivative of `F` is `L`. -/
noncomputable def linearize {k : ℕ} (L : (Fin k → ℝ) →L[ℝ] ℝ)
    (f : Fin k → FlagVector 𝕋 (emptyType S)) : FlagVector 𝕋 (emptyType S) :=
  ∑ i, coeff L i • f i

omit [S.NullaryFree] [𝕋.IsType (emptyType S)] in
theorem hostEval_linearize {V : Type} [Fintype V] (G : LabeledFlag 𝕋 (emptyType S) V)
    {k : ℕ} (L : (Fin k → ℝ) →L[ℝ] ℝ) (f : Fin k → FlagVector 𝕋 (emptyType S)) :
    hostEval G (linearize L f) = L fun i => hostEval G (f i) := by
  unfold linearize
  rw [hostEval_sum, apply_eq_sum_coeff]
  exact Finset.sum_congr rfl fun i _ => hostEval_smul G _ _

omit [S.NullaryFree] [𝕋.IsType (emptyType S)] in
theorem densityEval_linearize (G : FinFlag 𝕋 (emptyType S))
    {k : ℕ} (L : (Fin k → ℝ) →L[ℝ] ℝ) (f : Fin k → FlagVector 𝕋 (emptyType S)) :
    densityEval (linearize L f) G = L fun i => densityEval (f i) G := by
  unfold linearize
  rw [densityEval_sum, apply_eq_sum_coeff]
  exact Finset.sum_congr rfl fun i _ => densityEval_smul _ _ _

omit [S.NullaryFree] in
theorem positiveHom_linearize (φ : PositiveHom 𝕋 (emptyType S))
    {k : ℕ} (L : (Fin k → ℝ) →L[ℝ] ℝ) (f : Fin k → FlagVector 𝕋 (emptyType S)) :
    φ ⟦linearize L f⟧ = L fun i => φ ⟦f i⟧ := by
  unfold linearize
  rw [sum_quot, PositiveHom.map_sum, apply_eq_sum_coeff]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_quot, PositiveHom.map_smul]

omit [S.NullaryFree] [𝕋.IsType (emptyType S)] in
/-- The profile evaluation is linear in the flag vector. -/
theorem profileEval_sum_smul {T : Type} [Fintype T] {σ : Model S T}
    (a : FlagDensitySpace 𝕋 σ) {ι : Type} (s : Finset ι) (c : ι → ℝ)
    (g : ι → FlagVector 𝕋 σ) :
    profileEval a (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i * profileEval a (g i) := by
  show linearExtension (fun F => (a : FinFlag 𝕋 σ → ℝ) F) _ = _
  rw [linearExtension_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [linearExtension_smul]; rfl

omit [𝕋.IsType (emptyType S)] in
theorem profileEval_partialVertexVec_linearize {σ₁ : Model S (Fin 1)} [𝕋.VertexUniform σ₁]
    (a : FlagDensitySpace 𝕋 σ₁)
    {k : ℕ} (L : (Fin k → ℝ) →L[ℝ] ℝ) (f : Fin k → FlagVector 𝕋 (emptyType S)) :
    profileEval a (partialVertexVec σ₁ (linearize L f))
      = L fun i => profileEval a (partialVertexVec σ₁ (f i)) := by
  unfold linearize
  rw [partialVertexVec_sum]
  simp_rw [partialVertexVec_smul]
  rw [profileEval_sum_smul, apply_eq_sum_coeff]

end Linearize

/-! ## The first-order condition at a maximizer -/

section FirstOrder

variable [𝕋.IsType (emptyType S)] (φ₀ : PositiveHom 𝕋 (emptyType S))

omit [S.NullaryFree] in
/-- **The first-order condition at a maximizer.** If `F` is differentiable at
`x₀ = (φ₀(fᵢ))ᵢ` with derivative `L` and `φ₀` maximizes `φ ↦ F((φ(fᵢ))ᵢ)`,
then for every `θ > 0` there is a radius `r > 0` within which
`L(y − x₀) ≤ θ ‖y − x₀‖` for every homomorphism value vector `y`. -/
theorem exists_radius_fderiv_le {k : ℕ} (f : Fin k → FlagVector 𝕋 (emptyType S))
    (F : (Fin k → ℝ) → ℝ) {L : (Fin k → ℝ) →L[ℝ] ℝ}
    (hF : HasFDerivAt F L fun i => φ₀ ⟦f i⟧)
    (hmax : ∀ φ : PositiveHom 𝕋 (emptyType S), F (fun i => φ ⟦f i⟧) ≤ F fun i => φ₀ ⟦f i⟧)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ r : ℝ, 0 < r ∧ ∀ φ : PositiveHom 𝕋 (emptyType S),
      ‖(fun i => φ ⟦f i⟧) - fun i => φ₀ ⟦f i⟧‖ ≤ r →
        L ((fun i => φ ⟦f i⟧) - fun i => φ₀ ⟦f i⟧)
          ≤ θ * ‖(fun i => φ ⟦f i⟧) - fun i => φ₀ ⟦f i⟧‖ := by
  set x₀ : Fin k → ℝ := fun i => φ₀ ⟦f i⟧ with hx₀
  have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hF).def hθ
  rw [Metric.eventually_nhds_iff] at hlo
  obtain ⟨r, hr, hlo⟩ := hlo
  refine ⟨r / 2, by positivity, fun φ hφ => ?_⟩
  set y : Fin k → ℝ := fun i => φ ⟦f i⟧ with hy
  have hdist : dist (y - x₀) 0 < r := by
    rw [dist_zero_right]
    linarith
  have h := hlo hdist
  rw [add_sub_cancel, Real.norm_eq_abs, abs_le] at h
  have hm : F y ≤ F x₀ := hmax φ
  linarith [h.1]

omit [S.NullaryFree] in
/-- **The first-order condition at large finite hosts.** If
`L(y − x₀) ≤ θ ‖y − x₀‖` for all homomorphism value vectors `y` within `r` of
`x₀`, then for every `η > 0` the same holds up to `η` at every sufficiently
large host whose value vector is within `r` of `x₀` (otherwise a sequence of
violating hosts would realize a violating homomorphism). -/
theorem exists_size_fderiv_le {k : ℕ} (f : Fin k → FlagVector 𝕋 (emptyType S))
    {L : (Fin k → ℝ) →L[ℝ] ℝ} {θ r : ℝ}
    (hA : ∀ φ : PositiveHom 𝕋 (emptyType S),
      ‖(fun i => φ ⟦f i⟧) - fun i => φ₀ ⟦f i⟧‖ ≤ r →
        L ((fun i => φ ⟦f i⟧) - fun i => φ₀ ⟦f i⟧)
          ≤ θ * ‖(fun i => φ ⟦f i⟧) - fun i => φ₀ ⟦f i⟧‖)
    {η : ℝ} (hη : 0 < η) :
    ∃ m₀ : ℕ, ∀ G : FinFlag 𝕋 (emptyType S), m₀ ≤ G.1 →
      ‖(fun i => densityEval (f i) G) - fun i => φ₀ ⟦f i⟧‖ ≤ r →
        L ((fun i => densityEval (f i) G) - fun i => φ₀ ⟦f i⟧)
          ≤ θ * ‖(fun i => densityEval (f i) G) - fun i => φ₀ ⟦f i⟧‖ + η := by
  set x₀ : Fin k → ℝ := fun i => φ₀ ⟦f i⟧ with hx₀
  by_contra hcon
  push_neg at hcon
  choose G hG using hcon
  have hsz : Tendsto (fun m => (G m).1) atTop atTop :=
    tendsto_atTop_mono (fun m => (hG m).1) tendsto_id
  obtain ⟨s, hs, ψ, hψ⟩ := exists_realized_subseq G hsz
  have hconv : Tendsto (fun j => fun i => densityEval (f i) (G (s j))) atTop
      (𝓝 fun i => ψ ⟦f i⟧) := by
    rw [tendsto_pi_nhds]
    intro i
    have := realized_apply hψ (f i)
    simpa only [densityEval_apply] using this
  have hd : Tendsto (fun j => (fun i => densityEval (f i) (G (s j))) - x₀) atTop
      (𝓝 ((fun i => ψ ⟦f i⟧) - x₀)) := hconv.sub tendsto_const_nhds
  have hL : Tendsto (fun j => L ((fun i => densityEval (f i) (G (s j))) - x₀)) atTop
      (𝓝 (L ((fun i => ψ ⟦f i⟧) - x₀))) := (L.continuous.tendsto _).comp hd
  have hr : ‖(fun i => ψ ⟦f i⟧) - x₀‖ ≤ r := le_of_tendsto' hd.norm fun j => (hG (s j)).2.1
  have hge : θ * ‖(fun i => ψ ⟦f i⟧) - x₀‖ + η ≤ L ((fun i => ψ ⟦f i⟧) - x₀) :=
    le_of_tendsto_of_tendsto' ((hd.norm.const_mul θ).add_const η) hL
      fun j => (hG (s j)).2.2.le
  have := hA ψ hr
  linarith

end FirstOrder

/-! ## Theorem 4.3 for a differentiable objective -/

section Smooth

variable {σ₁ : Model S (Fin 1)} [𝕋.VertexUniform σ₁] [𝕋.IsType σ₁] [𝕋.IsType (emptyType S)]
variable (φ₀ : PositiveHom 𝕋 (emptyType S)) (Gs : ℕ → FinFlag 𝕋 (emptyType S))

/-- **Theorem 4.3 for a differentiable objective, the inequality.** If `φ₀`
maximizes `φ ↦ F((φ(fᵢ))ᵢ)` with `F` differentiable at `(φ₀(fᵢ))ᵢ`, then
almost surely the vertex differential of the linearized objective evaluates
to at most zero. -/
theorem ae_profileEval_partialVertexVec_linearize_nonpos (h : RealizedBy φ₀ Gs) {k : ℕ}
    (f : Fin k → FlagVector 𝕋 (emptyType S)) (F : (Fin k → ℝ) → ℝ)
    {L : (Fin k → ℝ) →L[ℝ] ℝ} (hF : HasFDerivAt F L fun i => φ₀ ⟦f i⟧)
    (hmax : ∀ φ : PositiveHom 𝕋 (emptyType S), F (fun i => φ ⟦f i⟧) ≤ F fun i => φ₀ ⟦f i⟧)
    {s : ℕ → ℕ} (hs : StrictMono s) {ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ₁)}
    (hlim : Tendsto (fun k => empiricalSeq σ₁ Gs (s k)) atTop (𝓝 ℙ)) :
    ∀ᵐ (a : FlagDensitySpace 𝕋 σ₁) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ₁)),
      profileEval a (partialVertexVec σ₁ (linearize L f)) ≤ 0 := by
  set x₀ : Fin k → ℝ := fun i => φ₀ ⟦f i⟧ with hx₀
  set g := linearize L f with hg
  by_contra hcon
  rw [ae_iff] at hcon
  simp only [not_le] at hcon
  obtain ⟨ε, hε, hK⟩ := exists_deletion_of_pos_measure φ₀ Gs h g hs hlim hcon
  -- the movement constant and the first-order slack
  set M : ℝ := 2 * ∑ i, sizeNorm (f i) with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => sizeNorm_nonneg _)
  set θ : ℝ := ε / (32 * (M + 1)) with hθ
  have hθpos : 0 < θ := by positivity
  have hθM : θ * M ≤ ε / 32 := by
    have h1 : θ * (M + 1) = ε / 32 := by
      rw [hθ]
      field_simp
    have h2 : θ * M ≤ θ * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) hθpos.le
    linarith
  obtain ⟨r, hr, hA⟩ := exists_radius_fderiv_le φ₀ f F hF hmax hθpos
  -- the deletion scale
  obtain ⟨K₀, hK₀⟩ := exists_nat_ge (max (2 * M / r) (ε / (32 * r)))
  obtain ⟨K, hKK₀, hK2N, hev⟩ := hK K₀
  have hKR : (K₀ : ℝ) ≤ K := by exact_mod_cast hKK₀
  have hKpos : (0 : ℝ) < K := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK2N
    linarith
  have hMK : M / K ≤ r / 2 := by
    have h1 : 2 * M / r ≤ K := (le_max_left _ _).trans (hK₀.trans hKR)
    rw [div_le_iff₀ hr] at h1
    rw [div_le_iff₀ hKpos]
    linarith
  set u : ℝ := ε / (64 * K) with hu
  have hupos : 0 < u := by positivity
  have hur : u ≤ r / 2 := by
    have h1 : ε / (32 * r) ≤ K := (le_max_right _ _).trans (hK₀.trans hKR)
    rw [div_le_iff₀ (by positivity)] at h1
    rw [hu, div_le_iff₀ (by positivity)]
    linarith
  set η' : ℝ := u / (θ + 1) with hη'
  have hη'pos : 0 < η' := by positivity
  have hη'u : η' ≤ u := div_le_self hupos.le (by linarith)
  have hθη' : θ * η' ≤ u := by
    have h1 : θ * η' = θ * u / (θ + 1) := by
      rw [hη']
      ring
    rw [h1, div_le_iff₀ (by positivity)]
    nlinarith
  have hθMK : θ * (M / K) ≤ 2 * u := by
    calc θ * (M / K) = (θ * M) / K := by ring
      _ ≤ (ε / 32) / K := div_le_div_of_nonneg_right hθM hKpos.le
      _ = 2 * u := by
        rw [hu]
        field_simp
        ring
  obtain ⟨m₀, hm₀⟩ := exists_size_fderiv_le φ₀ f hA hupos
  -- realization: all coordinates and the linearized objective converge
  have hsz : Tendsto (fun j => (Gs (s j)).1) atTop atTop := h.1.comp hs.tendsto_atTop
  have hreal : ∀ i, Tendsto (fun j => densityEval (f i) (Gs (s j))) atTop (𝓝 (x₀ i)) := by
    intro i
    have := (realized_apply h (f i)).comp hs.tendsto_atTop
    simpa only [densityEval_apply] using this
  have hnear : ∀ᶠ j in atTop, ∀ i, |densityEval (f i) (Gs (s j)) - x₀ i| < η' := by
    rw [eventually_all]
    intro i
    filter_upwards [(hreal i).eventually (Metric.ball_mem_nhds _ hη'pos)] with j hj
    rw [Real.dist_eq] at hj
    exact hj
  have hrealg : Tendsto (fun j => densityEval g (Gs (s j))) atTop (𝓝 (φ₀ ⟦g⟧)) := by
    have := (realized_apply h g).comp hs.tendsto_atTop
    simpa only [densityEval_apply] using this
  have hnearg : ∀ᶠ j in atTop, |densityEval g (Gs (s j)) - φ₀ ⟦g⟧| < η' := by
    filter_upwards [hrealg.eventually (Metric.ball_mem_nhds _ hη'pos)] with j hj
    rw [Real.dist_eq] at hj
    exact hj
  -- the contradiction at a large host
  have hfalse : ∀ᶠ j : ℕ in atTop, False := by
    filter_upwards [hev, hsz.eventually_ge_atTop (2 * m₀ + 2), hnear, hnearg]
      with j hj1 hj2 hj3 hj4
    set n := (Gs (s j)).1 with hn
    set H := hostAt Gs (s j) with hH
    obtain ⟨E, hEcard, htele⟩ := hj1
    set t := n / K with ht
    have ht2 : t * 2 ≤ n := (Nat.mul_le_mul_left _ hK2N).trans (Nat.div_mul_le_self n K)
    have htK : t * K ≤ n := Nat.div_mul_le_self n K
    have hn0 : 0 < n := by omega
    have hnt : 0 < n - t := by omega
    set A : Finset (Fin n) := Finset.univ \ E with hA
    have hAcard : A.card = n - t := by
      rw [hA, Finset.card_univ_diff, hEcard, Fintype.card_fin]
    set H' := H.restrict A (emptyType_root_mem H A) with hH'
    have htele' : hostEval H g + ε / (8 * K) ≤ hostEval H' g := htele
    have hHd : ∀ g' : FlagVector 𝕋 (emptyType S), hostEval H g' = densityEval g' (Gs (s j)) :=
      fun g' => (densityEval_out g' (Gs (s j)).2).symm
    have hHx : ∀ i, |hostEval H (f i) - x₀ i| < η' := fun i => by
      rw [hHd]
      exact hj3 i
    -- each coordinate moves by at most `M / K` under the deletion
    have hmove : ∀ i, |hostEval H' (f i) - hostEval H (f i)| ≤ M / K := fun i => by
      have h1 := abs_hostEval_restrict_sub_le H (f i) t (emptyType_root_mem H A)
        (by rw [Fintype.card_fin, hAcard]; omega) (by rw [Fintype.card_fin, hAcard]; omega)
      rw [hAcard, Fintype.card_fin, Nat.sub_zero] at h1
      refine h1.trans ?_
      have hs0 : 0 ≤ sizeNorm (f i) := sizeNorm_nonneg _
      have hsM : 2 * sizeNorm (f i) ≤ M := by
        rw [hM]
        have := Finset.single_le_sum (fun i _ => sizeNorm_nonneg (f i)) (Finset.mem_univ i)
        linarith
      have hntR : (0 : ℝ) < ((n - t : ℕ) : ℝ) := by exact_mod_cast hnt
      rw [div_le_div_iff₀ hntR hKpos]
      have hcast : ((n - t : ℕ) : ℝ) = (n : ℝ) - t := by
        rw [Nat.cast_sub (by omega)]
      rw [hcast]
      have htKR : (t : ℝ) * K ≤ n := by exact_mod_cast htK
      have ht2R : (t : ℝ) * 2 ≤ n := by exact_mod_cast ht2
      have hF1 : (t : ℝ) * K * sizeNorm (f i) ≤ (n : ℝ) * sizeNorm (f i) :=
        mul_le_mul_of_nonneg_right htKR hs0
      have hF2 : (t : ℝ) * 2 * sizeNorm (f i) ≤ (n : ℝ) * sizeNorm (f i) :=
        mul_le_mul_of_nonneg_right ht2R hs0
      have hF3 : 2 * sizeNorm (f i) * ((n : ℝ) - t) ≤ M * ((n : ℝ) - t) :=
        mul_le_mul_of_nonneg_right hsM (by linarith)
      nlinarith [hF1, hF2, hF3]
    -- the deleted host's value vector is within `M / K + η'` of `x₀`
    have hy'M : ‖(fun i => hostEval H' (f i)) - x₀‖ ≤ M / K + η' := by
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      rw [Pi.sub_apply, Real.norm_eq_abs]
      show |hostEval H' (f i) - x₀ i| ≤ M / K + η'
      calc |hostEval H' (f i) - x₀ i|
          = |(hostEval H' (f i) - hostEval H (f i)) + (hostEval H (f i) - x₀ i)| := by ring_nf
        _ ≤ |hostEval H' (f i) - hostEval H (f i)| + |hostEval H (f i) - x₀ i| := abs_add_le _ _
        _ ≤ M / K + η' := add_le_add (hmove i) (hHx i).le
    have hy'r : ‖(fun i => hostEval H' (f i)) - x₀‖ ≤ r := by
      linarith [hy'M, hMK, hη'u, hur]
    -- the first-order bound at the deleted host
    set G' : FinFlag 𝕋 (emptyType S) := ⟨_, (H'.reindex (Fintype.equivFin _)).toFlag⟩ with hG'
    have hG'd : ∀ g' : FlagVector 𝕋 (emptyType S), densityEval g' G' = hostEval H' g' :=
      fun g' => (hostEval_eq_densityEval_reindex H' g').symm
    have hsize : m₀ ≤ G'.1 := by
      show m₀ ≤ Fintype.card {x // x ∈ A}
      rw [Fintype.card_coe, hAcard]
      omega
    have hcoord : (fun i => densityEval (f i) G') = fun i => hostEval H' (f i) :=
      funext fun i => hG'd (f i)
    have hfo := hm₀ G' hsize (by rw [hcoord]; exact hy'r)
    rw [hcoord] at hfo
    -- the linearized objective measures exactly `L(y − x₀)`
    have hLg : L ((fun i => hostEval H' (f i)) - x₀) = hostEval H' g - φ₀ ⟦g⟧ := by
      rw [map_sub, hg, hostEval_linearize, positiveHom_linearize]
    have hnorm : θ * ‖(fun i => hostEval H' (f i)) - x₀‖ ≤ θ * (M / K + η') :=
      mul_le_mul_of_nonneg_left hy'M hθpos.le
    have hlow : φ₀ ⟦g⟧ - η' < hostEval H g := by
      rw [hHd g]
      rw [abs_sub_lt_iff] at hj4
      linarith [hj4.2]
    have h8 : ε / (8 * K) = 8 * u := by
      rw [hu]
      field_simp
      ring
    linarith [hfo, hLg, hnorm, htele', hlow, h8, hθMK, hθη', hη'u, hupos]
  obtain ⟨j, hj⟩ := hfalse.exists
  exact hj

/-- **Theorem 4.3 for a differentiable objective, equality form**, for the
linearized objective. -/
theorem ae_profileEval_partialVertexVec_linearize_eq_zero (h : RealizedBy φ₀ Gs) {k : ℕ}
    (f : Fin k → FlagVector 𝕋 (emptyType S)) (F : (Fin k → ℝ) → ℝ)
    {L : (Fin k → ℝ) →L[ℝ] ℝ} (hF : HasFDerivAt F L fun i => φ₀ ⟦f i⟧)
    (hmax : ∀ φ : PositiveHom 𝕋 (emptyType S), F (fun i => φ ⟦f i⟧) ≤ F fun i => φ₀ ⟦f i⟧)
    {s : ℕ → ℕ} (hs : StrictMono s) {ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ₁)}
    (hlim : Tendsto (fun k => empiricalSeq σ₁ Gs (s k)) atTop (𝓝 ℙ)) :
    ∀ᵐ (a : FlagDensitySpace 𝕋 σ₁) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ₁)),
      profileEval a (partialVertexVec σ₁ (linearize L f)) = 0 :=
  ae_profileEval_eq_zero_of_nonpos _
    (ae_profileEval_partialVertexVec_linearize_nonpos φ₀ Gs h f F hF hmax hs hlim)
    (integral_profileEval_partialVertexVec φ₀ Gs h _ hs hlim)

/-- **Razborov's Theorem 4.3 for a differentiable objective.** If `φ₀`
maximizes `φ ↦ F(φ(f₁), …, φ(f_k))` over the positive homomorphisms and `F`
is differentiable at `x₀ = (φ₀(fᵢ))ᵢ` with derivative `L`, then, almost surely
under a weak limit `ℙ` of the empirical rooting measures along a sequence
realizing `φ₀`, the derivative of the objective along the vertex
differential vanishes: `L(φ¹(∂₁ f₁), …, φ¹(∂₁ f_k)) = ∑ᵢ ∂ᵢF(x₀) φ¹(∂₁ fᵢ) = 0`. -/
theorem ae_fderiv_partialVertexVec_eq_zero (h : RealizedBy φ₀ Gs) {k : ℕ}
    (f : Fin k → FlagVector 𝕋 (emptyType S)) (F : (Fin k → ℝ) → ℝ)
    {L : (Fin k → ℝ) →L[ℝ] ℝ} (hF : HasFDerivAt F L fun i => φ₀ ⟦f i⟧)
    (hmax : ∀ φ : PositiveHom 𝕋 (emptyType S), F (fun i => φ ⟦f i⟧) ≤ F fun i => φ₀ ⟦f i⟧)
    {s : ℕ → ℕ} (hs : StrictMono s) {ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ₁)}
    (hlim : Tendsto (fun k => empiricalSeq σ₁ Gs (s k)) atTop (𝓝 ℙ)) :
    ∀ᵐ (a : FlagDensitySpace 𝕋 σ₁) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ₁)),
      L (fun i => profileEval a (partialVertexVec σ₁ (f i))) = 0 := by
  filter_upwards [ae_profileEval_partialVertexVec_linearize_eq_zero φ₀ Gs h f F hF hmax hs hlim]
    with a ha
  rwa [profileEval_partialVertexVec_linearize] at ha

/-- **Theorem 4.3 for a `C¹` objective**: the derivative is `fderiv ℝ F x₀`. -/
theorem ae_fderiv_partialVertexVec_eq_zero_of_contDiff (h : RealizedBy φ₀ Gs) {k : ℕ}
    (f : Fin k → FlagVector 𝕋 (emptyType S)) (F : (Fin k → ℝ) → ℝ) (hF : ContDiff ℝ 1 F)
    (hmax : ∀ φ : PositiveHom 𝕋 (emptyType S), F (fun i => φ ⟦f i⟧) ≤ F fun i => φ₀ ⟦f i⟧)
    {s : ℕ → ℕ} (hs : StrictMono s) {ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ₁)}
    (hlim : Tendsto (fun k => empiricalSeq σ₁ Gs (s k)) atTop (𝓝 ℙ)) :
    ∀ᵐ (a : FlagDensitySpace 𝕋 σ₁) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ₁)),
      fderiv ℝ F (fun i => φ₀ ⟦f i⟧) (fun i => profileEval a (partialVertexVec σ₁ (f i))) = 0 :=
  ae_fderiv_partialVertexVec_eq_zero φ₀ Gs h f F
    ((hF.differentiable one_ne_zero) _).hasFDerivAt hmax hs hlim

/-- **Theorem 4.3 for a differentiable objective, realization-free**: every
maximizer is realized by some sequence (`exists_realizedBy`), along which
some subsequence of the empirical rooting measures converges weakly
(`exists_weakLimit`), and the conclusion holds for that limit. -/
theorem exists_weakLimit_ae_fderiv_eq_zero {k : ℕ}
    (f : Fin k → FlagVector 𝕋 (emptyType S)) (F : (Fin k → ℝ) → ℝ)
    {L : (Fin k → ℝ) →L[ℝ] ℝ} (hF : HasFDerivAt F L fun i => φ₀ ⟦f i⟧)
    (hmax : ∀ φ : PositiveHom 𝕋 (emptyType S), F (fun i => φ ⟦f i⟧) ≤ F fun i => φ₀ ⟦f i⟧) :
    ∃ (Gs : ℕ → FinFlag 𝕋 (emptyType S)) (s : ℕ → ℕ)
        (ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ₁)),
      RealizedBy φ₀ Gs ∧ StrictMono s
        ∧ Tendsto (fun k => empiricalSeq σ₁ Gs (s k)) atTop (𝓝 ℙ)
        ∧ ∀ᵐ (a : FlagDensitySpace 𝕋 σ₁) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ₁)),
            L (fun i => profileEval a (partialVertexVec σ₁ (f i))) = 0 := by
  obtain ⟨Gs, hGs⟩ := exists_realizedBy φ₀
  obtain ⟨s, ℙ, hs, hlim⟩ := exists_weakLimit σ₁ Gs
  exact ⟨Gs, s, ℙ, hGs, hs, hlim,
    ae_fderiv_partialVertexVec_eq_zero φ₀ Gs hGs f F hF hmax hs hlim⟩

end Smooth

end FlagAlgebras.Core
