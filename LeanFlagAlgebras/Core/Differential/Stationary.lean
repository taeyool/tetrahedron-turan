import LeanFlagAlgebras.Core.Differential.Maximizer
import LeanFlagAlgebras.Core.Stationarity
import LeanFlagAlgebras.Core.Limit.Sampling

/-! # Core: a maximizer of a model density is stationary for its rootings

The consequence of the differential method that flag-algebra certificates
consume (Razborov's Corollary 4.6(a), in the shape of the paper's
Corollary "maximizers are degree-stationary"). Let `𝕋` be vertex uniform,
`M` a model on `ℓ ≥ 1` vertices with a *single* rooting `d` (so that
`π̃¹ M = d`), and `φ₀` a positive homomorphism maximizing `φ ↦ φ(M)` and
realized by a sequence of hosts. Then `φ₀` is stationary for `d`:

  `φ₀(⟦d⟧₁)² = φ₀(⟦d · d⟧₁)`.

Proof: along the weak limit `ℙ` of the empirical rooting measures, the
random rooted homomorphism `a` satisfies `a(∂₁ M) = 0` (Theorem 4.3) and
`a(π¹ M) = φ₀(M)` (the extension clause), hence `a(d) = a(π̃¹ M) = φ₀(M)`
almost surely; the moments `∫ a(d) dℙ = φ₀(⟦d⟧₁)` and
`∫ a(d)² dℙ = φ₀(⟦d·d⟧₁)` (Theorem 3.5, with `⟦1_{σ₁}⟧₁ = 1` over a vertex
uniform theory) are then both powers of `φ₀(M)`. -/

namespace FlagAlgebras.Core

open Filter Topology MeasureTheory Finset
open scoped ENNReal
open Classical

variable {S : Signature} [S.NullaryFree] {𝕋 : RelTheory S}
variable {σ₁ : Model S (Fin 1)} [hvu : 𝕋.VertexUniform σ₁]

/-! ## The vertex type in the unlabeled algebra -/

section TypeFlag

/-- Over a vertex uniform theory, every one-vertex member model is the vertex
type. -/
theorem Model.eq_vertexType_of_mem {N : Model S (Fin 1)} (hN : 𝕋.Mem N) : N = σ₁ := by
  refine Model.ext ?_
  funext r g
  have h : N.interp r (⇑(constEmb (0 : Fin 1)) ∘ g) ↔ σ₁.interp r g :=
    RelTheory.VertexUniform.interp_const N hN 0 r g
  have hg : ⇑(constEmb (0 : Fin 1)) ∘ g = g := funext fun i => by
    show (0 : Fin 1) = g i
    exact Subsingleton.elim _ _
  rw [hg] at h
  exact propext h

include σ₁ hvu in
/-- All one-vertex flags are isomorphic. -/
theorem flagWithSize_one_subsingleton (X Y : FlagWithSize 𝕋 (emptyType S) 1) : X = Y := by
  refine Quotient.inductionOn₂ X Y fun x y => Quotient.sound ⟨LabeledFlagIso.ofEmptyType ?_⟩
  have hx : x.toModel = σ₁ := Model.eq_vertexType_of_mem x.mem
  have hy : y.toModel = σ₁ := Model.eq_vertexType_of_mem y.mem
  exact ⟨Equiv.refl _, fun r f => by rw [hx, hy]; rfl⟩

variable [𝕋.IsType (emptyType S)]

include σ₁ hvu in
/-- A one-vertex flag is the unit of the unlabeled algebra. -/
theorem basisVector_quot_eq_one_of_size_one (F : FinFlag 𝕋 (emptyType S)) (hF : F.1 = 1) :
    (⟦basisVector F⟧ : FlagAlgebra 𝕋 (emptyType S)) = 1 := by
  obtain ⟨n, X⟩ := F
  change n = 1 at hF
  subst hF
  haveI : Subsingleton (FlagWithSize 𝕋 (emptyType S) 1) :=
    ⟨flagWithSize_one_subsingleton (σ₁ := σ₁)⟩
  rw [← sum_flagWithSize_eq_one (𝕋 := 𝕋) (σ := emptyType S) 1 (by simp),
    Fintype.sum_subsingleton _ X]

variable [𝕋.IsType σ₁]

omit hvu [𝕋.IsType (emptyType S)] in
theorem typeFlag_fst : (typeFlag σ₁ : FinFlag 𝕋 (emptyType S)).1 = 1 := by
  show Fintype.card (Fin 1) = 1
  exact Fintype.card_fin 1

/-- The unlabeled vertex type is `1`. -/
theorem typeFlag_quot_eq_one :
    (⟦basisVector (typeFlag σ₁)⟧ : FlagAlgebra 𝕋 (emptyType S)) = 1 :=
  basisVector_quot_eq_one_of_size_one (σ₁ := σ₁) _ typeFlag_fst

omit hvu [𝕋.IsType (emptyType S)] in
/-- The labeling factor of the unit flag of the vertex type is `1`: a single
vertex has exactly one labeling. -/
theorem qFactor_one_vertex : ((1 : FinFlag 𝕋 σ₁).qFactor : ℚ) = 1 := by
  unfold FinFlag.qFactor labelingFactor
  have hcard : Fintype.card (Fin 1 ↪ Fin (1 : FinFlag 𝕋 σ₁).1) = 1 := by
    rw [Fintype.card_embedding_eq, finFlag_one_fst]
    simp
  have hle := labelingCount_le_card (Quotient.out (1 : FinFlag 𝕋 σ₁).2).unlabel
    (Quotient.out (1 : FinFlag 𝕋 σ₁).2)
  have hpos := labelingCount_self_pos (Quotient.out (1 : FinFlag 𝕋 σ₁).2)
  rw [hcard] at hle ⊢
  have h1 : labelingCount (Quotient.out (1 : FinFlag 𝕋 σ₁).2).unlabel
      (Quotient.out (1 : FinFlag 𝕋 σ₁).2) = 1 := by omega
  rw [h1]
  norm_num

/-- `φ₀(⟦1_{σ₁}⟧₁) = 1` over a vertex uniform theory. -/
theorem positiveHom_downward_one_vertex (φ₀ : PositiveHom 𝕋 (emptyType S)) :
    φ₀ (downward (1 : FlagAlgebra 𝕋 σ₁)) = 1 := by
  rw [positiveHom_downward_one, qFactor_one_vertex, typeFlag_quot_eq_one, PositiveHom.map_one]
  norm_num

theorem positiveHom_typeFlag_pos (φ₀ : PositiveHom 𝕋 (emptyType S)) :
    0 < φ₀ ⟦basisVector (typeFlag σ₁)⟧ := by
  rw [typeFlag_quot_eq_one, PositiveHom.map_one]
  exact zero_lt_one

end TypeFlag

/-! ## Moments of the weak limit, for flag vectors -/

section Moments

variable [𝕋.IsType σ₁] [𝕋.IsType (emptyType S)]
variable (φ₀ : PositiveHom 𝕋 (emptyType S)) (Gs : ℕ → FinFlag 𝕋 (emptyType S))

omit [S.NullaryFree] hvu [𝕋.IsType σ₁] [𝕋.IsType (emptyType S)] in
theorem profileEval_eq_limitLin {T : Type} [Fintype T] {σ : Model S T}
    (a : FlagDensitySpace 𝕋 σ) (g : FlagVector 𝕋 σ) :
    profileEval a g = limitLin (a : FinFlag 𝕋 σ → ℝ) g :=
  (limitLin_apply _ _).symm

/-- **Theorem 3.5 for flag vectors**: the mean of `a ↦ a(g)` under the weak
limit is `φ₀(⟦g⟧₁)/φ₀(⟦1⟧₁)`. -/
theorem integral_profileEval_weakLimit {s : ℕ → ℕ} (hs : StrictMono s)
    {ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ₁)}
    (hlim : Tendsto (fun k => empiricalSeq σ₁ Gs (s k)) atTop (𝓝 ℙ))
    (h : RealizedBy φ₀ Gs) (hσ : 0 < φ₀ ⟦basisVector (typeFlag σ₁)⟧) (g : FlagVector 𝕋 σ₁) :
    ∫ a, profileEval a g ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ₁))
      = φ₀ (downward ⟦g⟧) / φ₀ (downward (1 : FlagAlgebra 𝕋 σ₁)) := by
  unfold profileEval
  have hint : ∀ F : FinFlag 𝕋 σ₁, Integrable (fun a : FlagDensitySpace 𝕋 σ₁ =>
      (a : FinFlag 𝕋 σ₁ → ℝ) F) (ℙ : Measure (FlagDensitySpace 𝕋 σ₁)) :=
    fun F => (evalBCF σ₁ F).integrable _
  rw [integral_finset_sum _ fun F _ => (hint F).const_mul (g F)]
  rw [Finset.sum_congr rfl fun F _ => by
    rw [integral_const_mul, integral_eval_weakLimit σ₁ φ₀ Gs hs hlim h hσ F]]
  rw [quot_eq_sum_basis g, downward_sum, PositiveHom.map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [downward_smul, PositiveHom.map_smul, downwardRatio, mul_div_assoc]

end Moments

/-! ## Stationarity of a maximizer -/

section Stationary

variable [𝕋.IsType σ₁] [𝕋.IsType (emptyType S)]
variable (φ₀ : PositiveHom 𝕋 (emptyType S)) (Gs : ℕ → FinFlag 𝕋 (emptyType S))

/-- **A realized maximizer of a model density is stationary for the model's
rooting.** If `M` has the single rooting `d` (`π̃¹ M = d`) and `φ₀`, realized
by `Gs`, maximizes `φ ↦ φ(M)`, then `φ₀(⟦d⟧₁)² = φ₀(⟦d·d⟧₁)`. -/
theorem isStationary_of_maximizer (h : RealizedBy φ₀ Gs) (M : FinFlag 𝕋 (emptyType S))
    (hM : 0 < M.1)
    (hmax : ∀ φ : PositiveHom 𝕋 (emptyType S), φ ⟦basisVector M⟧ ≤ φ₀ ⟦basisVector M⟧)
    (d : FinFlag 𝕋 σ₁) (hd : muVec σ₁ M = basisVector d) :
    IsStationary φ₀ (⟦basisVector d⟧ : FlagAlgebra 𝕋 σ₁) := by
  obtain ⟨s, ℙ, hs, hlim⟩ := exists_weakLimit σ₁ Gs
  have hσ : 0 < φ₀ ⟦basisVector (typeFlag σ₁)⟧ := positiveHom_typeFlag_pos φ₀
  have hone : φ₀ (downward (1 : FlagAlgebra 𝕋 σ₁)) = 1 := positiveHom_downward_one_vertex φ₀
  set x : FlagAlgebra 𝕋 σ₁ := ⟦basisVector d⟧ with hx
  set c : ℝ := φ₀ ⟦basisVector M⟧ with hc
  -- almost surely `a(d) = φ₀(M)`
  have hae_d : ∀ᵐ (a : FlagDensitySpace 𝕋 σ₁) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ₁)),
      (a : FinFlag 𝕋 σ₁ → ℝ) d = c := by
    filter_upwards [ae_profileEval_partialVertexVec_eq_zero φ₀ Gs h (basisVector M) hmax hs hlim,
      ae_profileEval_piVec φ₀ Gs h hs hlim M] with a h1 h2
    rw [partialVertexVec_basisVector, profileEval_eq_limitLin, map_smul, map_sub, smul_eq_mul,
      mul_eq_zero, sub_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 (by exact_mod_cast hM.ne')
    · rw [hd, limitLin_basis] at h1
      rw [← h1, ← profileEval_eq_limitLin, h2]
  -- almost surely `a(d · d) = a(d)²`
  have hae_sq : ∀ᵐ (a : FlagDensitySpace 𝕋 σ₁) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ₁)),
      profileEval a (flagMul d d) = (a : FinFlag 𝕋 σ₁ → ℝ) d * (a : FinFlag 𝕋 σ₁ → ℝ) d := by
    filter_upwards [ae_mulClosed σ₁ φ₀ Gs hs hlim h hσ] with a hmul
    have := hmul d d
    rw [← this, profileEval_eq_limitLin, flagMul, flagMulWithSize, map_sum]
    refine Finset.sum_congr rfl fun G _ => ?_
    rw [map_smul, limitLin_basis, smul_eq_mul]
  -- the moments
  have hm1 : φ₀ (downward x) = c := by
    have := integral_profileEval_weakLimit φ₀ Gs hs hlim h hσ (basisVector d)
    rw [hone, div_one] at this
    rw [hx, ← this]
    have hcongr : (fun a : FlagDensitySpace 𝕋 σ₁ => profileEval a (basisVector d))
        =ᵐ[(ℙ : Measure (FlagDensitySpace 𝕋 σ₁))] fun _ => c := by
      filter_upwards [hae_d] with a ha
      rw [profileEval_eq_limitLin, limitLin_basis, ha]
    rw [integral_congr_ae hcongr, integral_const]
    simp
  have hm2 : φ₀ (downward (x * x)) = c * c := by
    have := integral_profileEval_weakLimit φ₀ Gs hs hlim h hσ (flagMul d d)
    rw [hone, div_one] at this
    rw [hx, basisVector_quot_mul_eq_flagMul_quot, ← this]
    have hcongr : (fun a : FlagDensitySpace 𝕋 σ₁ => profileEval a (flagMul d d))
        =ᵐ[(ℙ : Measure (FlagDensitySpace 𝕋 σ₁))] fun _ => c * c := by
      filter_upwards [hae_d, hae_sq] with a ha hsq
      rw [hsq, ha]
    rw [integral_congr_ae hcongr, integral_const]
    simp
  show φ₀ (stationarity x) = 0
  rw [stationarity, PositiveHom.map_sub, PositiveHom.map_mul, hm1, hm2, sub_self]

/-- **Corollary 4.6(a) without a realization hypothesis**: by the sampling
direction of Theorem 3.3 every maximizer is realized, so every maximizer of
a model with a single rooting `d` is stationary for `d`. -/
theorem isStationary_of_maximizer' (M : FinFlag 𝕋 (emptyType S)) (hM : 0 < M.1)
    (hmax : ∀ φ : PositiveHom 𝕋 (emptyType S), φ ⟦basisVector M⟧ ≤ φ₀ ⟦basisVector M⟧)
    (d : FinFlag 𝕋 σ₁) (hd : muVec σ₁ M = basisVector d) :
    IsStationary φ₀ (⟦basisVector d⟧ : FlagAlgebra 𝕋 σ₁) := by
  obtain ⟨Gs, hGs⟩ := exists_realizedBy φ₀
  exact isStationary_of_maximizer φ₀ Gs hGs M hM hmax d hd

end Stationary

end FlagAlgebras.Core
