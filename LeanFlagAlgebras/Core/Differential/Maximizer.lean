import LeanFlagAlgebras.Core.Differential.Telescope
import LeanFlagAlgebras.Core.Ensemble.Extension

/-! # Core: Razborov's Theorem 4.3 for a linear objective (realized form)

Let `φ₀` maximize `φ ↦ φ(f)` over the positive homomorphisms of a vertex
uniform theory, and let `ℙ` be a weak limit of the empirical rooting
measures along a sequence of hosts realizing `φ₀` (the measure whose
restriction to the homomorphism space is the random extension `ℙ[φ₀]` of
`Core/Ensemble/RandomHom`). Then, `ℙ`-almost surely, the vertex differential
of the objective evaluates to zero at the random rooted homomorphism:

* `ae_profileEval_partialVertexVec_nonpos` — `∂₁ f ≤ 0` almost surely: if the
  set where `∂₁ f > ε` had positive measure, the empirical measures would put
  a `δ` fraction of the vertices of the large hosts there (weak convergence
  tested against a continuous bump), and deleting a small constant fraction
  of those vertices would raise `p(f, ·)` by a constant
  (`hostEval_restrict_sdiff_ge`), beating the maximum on large hosts
  (`eventually_densityEval_le`);
* `ae_profileEval_partialVertexVec_eq_zero` — equality, since the
  differential has mean zero over the root (`sum_hostEval_partialVertexVec`).

Alongside, the extension clause of Theorem 3.5: almost surely the random
rooted homomorphism agrees with `φ₀` on the upward image of every model
(`ae_profileEval_piVec`), because `p^{(N,v)}(π¹ M) = p(M, N − v)` is within
`O(1/|N|)` of `p(M, N)`. -/

namespace FlagAlgebras.Core

open Filter Topology MeasureTheory Finset
open scoped ENNReal
open Classical

variable {S : Signature} [S.NullaryFree] {𝕋 : RelTheory S}

/-! ## Evaluation of flag vectors at profiles -/

section ProfileEval

variable {T : Type} [Fintype T] {σ : Model S T}

omit [S.NullaryFree] in
/-- The evaluation of a flag vector at a density profile. -/
noncomputable def profileEval (a : FlagDensitySpace 𝕋 σ) (g : FlagVector 𝕋 σ) : ℝ :=
  ∑ F ∈ g.support, g F * (a : FinFlag 𝕋 σ → ℝ) F

omit [S.NullaryFree] in
theorem continuous_profileEval (g : FlagVector 𝕋 σ) :
    Continuous fun a : FlagDensitySpace 𝕋 σ => profileEval a g :=
  continuous_finset_sum _ fun F _ => continuous_const.mul (FlagDensitySpace.continuous_eval F)

omit [S.NullaryFree] in
theorem profileEval_toDensity (G : FinFlag 𝕋 σ) (g : FlagVector 𝕋 σ) :
    profileEval (FinFlag.toDensity G) g = densityEval g G := by
  rw [densityEval_apply]
  rfl

omit [S.NullaryFree] in
theorem profileEval_toDensity_toFlag {n : ℕ} (G : LabeledFlag 𝕋 σ (Fin n))
    (g : FlagVector 𝕋 σ) :
    profileEval (FinFlag.toDensity ⟨n, G.toFlag⟩) g = hostEval G g := by
  rw [profileEval_toDensity, hostEval_toFlag]

omit [S.NullaryFree] in
theorem PositiveHomSpace.toPosHom_quot [𝕋.IsType σ] (a : PositiveHomSpace 𝕋 σ)
    (g : FlagVector 𝕋 σ) :
    PositiveHomSpace.toPosHom a ⟦g⟧ = profileEval (a : FlagDensitySpace 𝕋 σ) g :=
  PositiveHomSpace.toPosHom_apply a g

omit [S.NullaryFree] in
/-- The evaluation as a bounded continuous function on the profile space. -/
noncomputable def profileEvalBCF (g : FlagVector 𝕋 σ) :
    BoundedContinuousFunction (FlagDensitySpace 𝕋 σ) ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun a => profileEval a g, continuous_profileEval g⟩

omit [S.NullaryFree] in
@[simp]
theorem profileEvalBCF_apply (g : FlagVector 𝕋 σ) (a : FlagDensitySpace 𝕋 σ) :
    profileEvalBCF g a = profileEval a g :=
  rfl

end ProfileEval

/-! ## Vertex uniformity and the empirical rooting measure -/

section Vertex

variable {σ₁ : Model S (Fin 1)} [𝕋.VertexUniform σ₁]

omit [S.NullaryFree] in
/-- Over a vertex uniform theory every embedding of the one-point type is a
`σ₁`-labeling. -/
theorem isSigmaLabeling_vertexUniform {V : Type} (N : LabeledFlag 𝕋 (emptyType S) V)
    (θ : Fin 1 ↪ V) : IsSigmaLabeling σ₁ N θ := by
  intro r f
  have hθ : ⇑θ ∘ f = ⇑(constEmb (θ 0)) ∘ f := funext fun i => by
    show θ (f i) = θ 0
    exact congrArg θ (Subsingleton.elim _ _)
  rw [hθ]
  exact RelTheory.VertexUniform.interp_const N.toModel N.mem (θ 0) r f

theorem sigmaLabelings_vertexUniform {V : Type} [Fintype V]
    (N : LabeledFlag 𝕋 (emptyType S) V) : sigmaLabelings σ₁ N = Finset.univ := by
  ext θ
  simp only [Finset.mem_univ, iff_true]
  exact mem_sigmaLabelings.mpr (isSigmaLabeling_vertexUniform N θ)

theorem card_sigmaLabelings_vertex {n : ℕ} (N : LabeledFlag 𝕋 (emptyType S) (Fin n)) :
    (sigmaLabelings σ₁ N).card = n := by
  rw [sigmaLabelings_vertexUniform, Finset.card_univ, Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_fin, Nat.descFactorial_one]

theorem sigmaLabelings_vertex_nonempty {n : ℕ} (N : LabeledFlag 𝕋 (emptyType S) (Fin n))
    (hn : 0 < n) : (sigmaLabelings σ₁ N).Nonempty := by
  rw [← Finset.card_pos, card_sigmaLabelings_vertex]
  exact hn

variable (σ₁) in
/-- The density profile of the host rooted at `v`. -/
noncomputable def rootedPoint {n : ℕ} (N : LabeledFlag 𝕋 (emptyType S) (Fin n)) (v : Fin n) :
    FlagDensitySpace 𝕋 σ₁ :=
  FinFlag.toDensity ⟨n, (rootedAt σ₁ N v).toFlag⟩

omit [S.NullaryFree] in
theorem profileEval_rootedPoint {n : ℕ} (N : LabeledFlag 𝕋 (emptyType S) (Fin n)) (v : Fin n)
    (g : FlagVector 𝕋 σ₁) :
    profileEval (rootedPoint σ₁ N v) g = hostEval (rootedAt σ₁ N v) g :=
  profileEval_toDensity_toFlag _ _

/-- Sums over the `σ₁`-labelings are sums over the vertices. -/
theorem sum_sigmaLabelings_vertex {n : ℕ} (N : LabeledFlag 𝕋 (emptyType S) (Fin n))
    (G : (Fin 1 ↪ Fin n) → ℝ) :
    ∑ θ ∈ sigmaLabelings σ₁ N, G θ = ∑ v : Fin n, G (constEmb v) := by
  rw [sigmaLabelings_vertexUniform]
  refine Fintype.sum_equiv Equiv.uniqueEmbeddingEquivResult G (fun v => G (constEmb v))
    fun θ => ?_
  congr 1
  exact Function.Embedding.ext fun i => congrArg θ (Subsingleton.elim _ _)

variable [𝕋.IsType σ₁]

omit [S.NullaryFree] in
theorem labelPoint_constEmb {n : ℕ} (N : LabeledFlag 𝕋 (emptyType S) (Fin n)) (v : Fin n) :
    labelPoint σ₁ N (constEmb v) = rootedPoint σ₁ N v := by
  unfold labelPoint
  rw [dif_pos (isSigmaLabeling_vertexUniform N (constEmb v))]
  rfl

/-- Integrals against the empirical rooting measure are vertex averages. -/
theorem integral_empiricalMeasure_vertex {n : ℕ} (N : LabeledFlag 𝕋 (emptyType S) (Fin n))
    {g : FlagDensitySpace 𝕋 σ₁ → ℝ} (hg : Continuous g) :
    ∫ a, g a ∂(empiricalMeasure σ₁ N)
      = (n : ℝ)⁻¹ * ∑ v : Fin n, g (rootedPoint σ₁ N v) := by
  rw [integral_empiricalMeasure σ₁ N hg, card_sigmaLabelings_vertex, sum_sigmaLabelings_vertex]
  simp_rw [labelPoint_constEmb]

variable [𝕋.IsType (emptyType S)]
variable (Gs : ℕ → FinFlag 𝕋 (emptyType S))

theorem integral_empiricalSeq_vertex (k : ℕ) (hk : 0 < (Gs k).1)
    {g : FlagDensitySpace 𝕋 σ₁ → ℝ} (hg : Continuous g) :
    ∫ a, g a ∂(empiricalSeq σ₁ Gs k : Measure (FlagDensitySpace 𝕋 σ₁))
      = ((Gs k).1 : ℝ)⁻¹ * ∑ v : Fin (Gs k).1, g (rootedPoint σ₁ (hostAt Gs k) v) := by
  rw [empiricalSeq_of_nonempty σ₁ Gs k (sigmaLabelings_vertex_nonempty _ hk), empiricalProb_coe,
    integral_empiricalMeasure_vertex _ hg]

end Vertex

/-! ## The extension clause: `φ¹(π¹ M) = φ₀(M)` almost surely -/

section Extension

variable {σ₁ : Model S (Fin 1)} [𝕋.VertexUniform σ₁] [𝕋.IsType σ₁] [𝕋.IsType (emptyType S)]
variable (φ₀ : PositiveHom 𝕋 (emptyType S)) (Gs : ℕ → FinFlag 𝕋 (emptyType S))

omit [𝕋.IsType σ₁] [𝕋.IsType (emptyType S)] in
/-- At a rooted host on `n ≥ |M| + 1` vertices, the evaluation of `π¹ M` is
within `partialBound M / n` of the density of `M` in the host. -/
theorem abs_hostEval_piVec_sub_le {n : ℕ} (N : LabeledFlag 𝕋 (emptyType S) (Fin n))
    (v : Fin n) (M : FinFlag 𝕋 (emptyType S)) (hM : M.1 + 1 ≤ n) :
    |hostEval (rootedAt σ₁ N v) (piVec σ₁ M) - ((flagDensity (Quotient.out M.2) N : ℚ) : ℝ)|
      ≤ partialBound σ₁ M / (n : ℝ) := by
  have hV : Fintype.card (Fin n) = (n - 1) + 1 := by rw [Fintype.card_fin]; omega
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rw [hostEval_piVec, sum_rootExtensions_flagDensity N v M.2 hV,
    vertex_deletion_density (σ₁ := σ₁) N v M hV (by omega), add_sub_cancel_left, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (((n - 1 : ℕ) : ℝ) + 1)), hcast]
  calc 1 / (n : ℝ) * |hostEval (rootedAt σ₁ N v) (partialVertexVec σ₁ (basisVector M))|
      ≤ 1 / (n : ℝ) * partialBound σ₁ M :=
        mul_le_mul_of_nonneg_left (abs_hostEval_partialVertexVec_basisVector_le _ M)
          (by positivity)
    _ = partialBound σ₁ M / (n : ℝ) := by ring

/-- The deviation of the upward evaluation from the base value, as a bounded
continuous function. -/
noncomputable def piBCF (M : FinFlag 𝕋 (emptyType S)) :
    BoundedContinuousFunction (FlagDensitySpace 𝕋 σ₁) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun a => |profileEval a (piVec σ₁ M) - φ₀ ⟦basisVector M⟧|,
      ((continuous_profileEval _).sub continuous_const).abs⟩

omit [𝕋.VertexUniform σ₁] [𝕋.IsType σ₁] in
@[simp]
theorem piBCF_apply (M : FinFlag 𝕋 (emptyType S)) (a : FlagDensitySpace 𝕋 σ₁) :
    piBCF (σ₁ := σ₁) φ₀ M a = |profileEval a (piVec σ₁ M) - φ₀ ⟦basisVector M⟧| :=
  rfl

theorem integral_piBCF_le (M : FinFlag 𝕋 (emptyType S)) (k : ℕ) (hk : M.1 + 1 ≤ (Gs k).1) :
    ∫ a, piBCF (σ₁ := σ₁) φ₀ M a ∂(empiricalSeq σ₁ Gs k : Measure (FlagDensitySpace 𝕋 σ₁))
      ≤ |((subflagDensity M.2 (Gs k).2 : ℚ) : ℝ) - φ₀ ⟦basisVector M⟧|
        + partialBound σ₁ M / ((Gs k).1 : ℝ) := by
  have hn : 0 < (Gs k).1 := by omega
  have hnR : (0 : ℝ) < ((Gs k).1 : ℝ) := by exact_mod_cast hn
  rw [integral_empiricalSeq_vertex Gs k hn (piBCF φ₀ M).continuous]
  have hterm : ∀ v : Fin (Gs k).1,
      piBCF (σ₁ := σ₁) φ₀ M (rootedPoint σ₁ (hostAt Gs k) v)
        ≤ |((subflagDensity M.2 (Gs k).2 : ℚ) : ℝ) - φ₀ ⟦basisVector M⟧|
          + partialBound σ₁ M / ((Gs k).1 : ℝ) := by
    intro v
    rw [piBCF_apply, profileEval_rootedPoint]
    have h1 := abs_hostEval_piVec_sub_le (σ₁ := σ₁) (hostAt Gs k) v M hk
    have h2 : ((flagDensity (Quotient.out M.2) (hostAt Gs k) : ℚ) : ℝ)
        = ((subflagDensity M.2 (Gs k).2 : ℚ) : ℝ) := by
      rw [subflagDensity_out]
      rfl
    rw [h2] at h1
    calc |hostEval (rootedAt σ₁ (hostAt Gs k) v) (piVec σ₁ M) - φ₀ ⟦basisVector M⟧|
        = |(hostEval (rootedAt σ₁ (hostAt Gs k) v) (piVec σ₁ M)
              - ((subflagDensity M.2 (Gs k).2 : ℚ) : ℝ))
            + (((subflagDensity M.2 (Gs k).2 : ℚ) : ℝ) - φ₀ ⟦basisVector M⟧)| := by ring_nf
      _ ≤ |hostEval (rootedAt σ₁ (hostAt Gs k) v) (piVec σ₁ M)
              - ((subflagDensity M.2 (Gs k).2 : ℚ) : ℝ)|
            + |((subflagDensity M.2 (Gs k).2 : ℚ) : ℝ) - φ₀ ⟦basisVector M⟧| := abs_add_le _ _
      _ ≤ _ := by linarith [h1]
  calc ((Gs k).1 : ℝ)⁻¹ * ∑ v : Fin (Gs k).1, piBCF (σ₁ := σ₁) φ₀ M (rootedPoint σ₁ (hostAt Gs k) v)
      ≤ ((Gs k).1 : ℝ)⁻¹ * ∑ _v : Fin (Gs k).1,
          (|((subflagDensity M.2 (Gs k).2 : ℚ) : ℝ) - φ₀ ⟦basisVector M⟧|
            + partialBound σ₁ M / ((Gs k).1 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => hterm v) (by positivity)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          inv_mul_cancel_left₀ hnR.ne']

/-- **The extension clause of Theorem 3.5.** Along a realizing sequence, the
weak limit of the empirical rooting measures almost surely agrees with `φ₀`
on the upward image of every model. -/
theorem ae_profileEval_piVec (h : RealizedBy φ₀ Gs) {s : ℕ → ℕ} (hs : StrictMono s)
    {ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ₁)}
    (hlim : Tendsto (fun k => empiricalSeq σ₁ Gs (s k)) atTop (𝓝 ℙ))
    (M : FinFlag 𝕋 (emptyType S)) :
    ∀ᵐ (a : FlagDensitySpace 𝕋 σ₁) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ₁)),
      profileEval a (piVec σ₁ M) = φ₀ ⟦basisVector M⟧ := by
  have hz := ae_eq_zero_of_tendsto_integral σ₁ Gs hlim (piBCF φ₀ M) (fun a => abs_nonneg _) ?_
  · filter_upwards [hz] with a ha
    rw [piBCF_apply, abs_eq_zero, sub_eq_zero] at ha
    exact ha
  · have hsz : Tendsto (fun k => (Gs (s k)).1) atTop atTop := h.1.comp hs.tendsto_atTop
    have hszR : Tendsto (fun k => ((Gs (s k)).1 : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hsz
    have hconv : Tendsto (fun k => ((subflagDensity M.2 (Gs (s k)).2 : ℚ) : ℝ)) atTop
        (𝓝 (φ₀ ⟦basisVector M⟧)) := (h.2 M).comp hs.tendsto_atTop
    have hbound : Tendsto (fun k =>
        |((subflagDensity M.2 (Gs (s k)).2 : ℚ) : ℝ) - φ₀ ⟦basisVector M⟧|
          + partialBound σ₁ M / ((Gs (s k)).1 : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k =>
          |((subflagDensity M.2 (Gs (s k)).2 : ℚ) : ℝ) - φ₀ ⟦basisVector M⟧|) atTop (𝓝 0) := by
        have := (hconv.sub (tendsto_const_nhds (x := φ₀ ⟦basisVector M⟧))).abs
        rwa [sub_self, abs_zero] at this
      have h2 : Tendsto (fun k => partialBound σ₁ M / ((Gs (s k)).1 : ℝ)) atTop (𝓝 0) :=
        Tendsto.div_atTop tendsto_const_nhds hszR
      simpa using h1.add h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
      (Eventually.of_forall fun k => integral_nonneg fun a => abs_nonneg _) ?_
    filter_upwards [hsz.eventually_ge_atTop (M.1 + 1)] with k hk
    exact integral_piBCF_le φ₀ Gs M (s k) hk

end Extension

/-! ## Theorem 4.3 -/

section Bump

/-- A continuous bump: `0` below `ε/2`, `1` above `ε`. -/
noncomputable def bump (ε x : ℝ) : ℝ :=
  max 0 (min 1 ((x - ε / 2) / (ε / 2)))

theorem bump_nonneg (ε x : ℝ) : 0 ≤ bump ε x :=
  le_max_left _ _

theorem bump_le_one (ε x : ℝ) : bump ε x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem bump_eq_one {ε x : ℝ} (hε : 0 < ε) (h : ε ≤ x) : bump ε x = 1 := by
  unfold bump
  rw [min_eq_left, max_eq_right zero_le_one]
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem bump_eq_zero {ε x : ℝ} (hε : 0 < ε) (h : x < ε / 2) : bump ε x = 0 := by
  unfold bump
  have hneg : (x - ε / 2) / (ε / 2) < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
  rw [min_eq_right (by linarith), max_eq_left hneg.le]

theorem continuous_bump (ε : ℝ) : Continuous (bump ε) :=
  continuous_const.max (continuous_const.min ((continuous_id.sub continuous_const).div_const _))

end Bump

section Maximizer

variable {σ₁ : Model S (Fin 1)} [𝕋.VertexUniform σ₁] [𝕋.IsType σ₁] [𝕋.IsType (emptyType S)]
variable (φ₀ : PositiveHom 𝕋 (emptyType S)) (Gs : ℕ → FinFlag 𝕋 (emptyType S))

/-- The bump of the evaluation of a flag vector, as a bounded continuous
function on the profile space. -/
noncomputable def bumpBCF (ε : ℝ) (D : FlagVector 𝕋 σ₁) :
    BoundedContinuousFunction (FlagDensitySpace 𝕋 σ₁) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun a => bump ε (profileEval a D), (continuous_bump ε).comp (continuous_profileEval D)⟩

omit [S.NullaryFree] [𝕋.VertexUniform σ₁] [𝕋.IsType σ₁] [𝕋.IsType (emptyType S)] in
@[simp]
theorem bumpBCF_apply (ε : ℝ) (D : FlagVector 𝕋 σ₁) (a : FlagDensitySpace 𝕋 σ₁) :
    bumpBCF ε D a = bump ε (profileEval a D) :=
  rfl

omit [S.NullaryFree] [𝕋.VertexUniform σ₁] [𝕋.IsType σ₁] [𝕋.IsType (emptyType S)] in
/-- A function positive on a set of positive measure exceeds some positive
`ε` on a set of positive measure. -/
theorem exists_pos_measure_gt {ℙ : Measure (FlagDensitySpace 𝕋 σ₁)}
    (g : FlagDensitySpace 𝕋 σ₁ → ℝ) (h : ℙ {a | 0 < g a} ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ℙ {a | ε < g a} ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply h
  have hunion : {a : FlagDensitySpace 𝕋 σ₁ | 0 < g a}
      = ⋃ m : ℕ, {a | 1 / ((m : ℝ) + 1) < g a} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro ha
      exact exists_nat_one_div_lt ha
    · rintro ⟨m, hm⟩
      exact lt_trans (by positivity) hm
  rw [hunion, measure_iUnion_null_iff]
  intro m
  exact hcon _ (by positivity)

/-- **The deletion core of Theorem 4.3.** If a weak limit `ℙ` of the
empirical rooting measures gives positive measure to `∂₁ f > 0`, then there
is `ε > 0` such that for every `K₀` there is `K ≥ max K₀ 2` with: eventually
along the sequence, some set `E` of `n / K` vertices of the host on `n`
vertices can be deleted to raise `p(f, ·)` by at least `ε / (8K)`. No
maximality is assumed here; the endgames (linear or `C¹` objective) play the
maximality of `φ₀` against this gain. -/
theorem exists_deletion_of_pos_measure (h : RealizedBy φ₀ Gs)
    (f : FlagVector 𝕋 (emptyType S))
    {s : ℕ → ℕ} (hs : StrictMono s) {ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ₁)}
    (hlim : Tendsto (fun k => empiricalSeq σ₁ Gs (s k)) atTop (𝓝 ℙ))
    (hpos : (ℙ : Measure (FlagDensitySpace 𝕋 σ₁))
      {a | 0 < profileEval a (partialVertexVec σ₁ f)} ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ K₀ : ℕ, ∃ K : ℕ, K₀ ≤ K ∧ 2 ≤ K ∧
      ∀ᶠ k : ℕ in atTop, ∃ E : Finset (Fin (Gs (s k)).1),
        E.card = (Gs (s k)).1 / K ∧
        hostEval (hostAt Gs (s k)) f + ε / (8 * K)
          ≤ hostEval ((hostAt Gs (s k)).restrict (Finset.univ \ E)
              (emptyType_root_mem (hostAt Gs (s k)) _)) f := by
  set D := partialVertexVec σ₁ f with hD
  obtain ⟨ε, hε, hne⟩ := exists_pos_measure_gt (fun a => profileEval a D) hpos
  set U := {a : FlagDensitySpace 𝕋 σ₁ | ε < profileEval a D} with hU
  have hUmeas : MeasurableSet U :=
    (isOpen_lt continuous_const (continuous_profileEval D)).measurableSet
  set δ := (ℙ : Measure (FlagDensitySpace 𝕋 σ₁)).real U with hδ
  have hδpos : 0 < δ := by
    rw [hδ, measureReal_def]
    exact ENNReal.toReal_pos hne (measure_ne_top _ _)
  -- the bump integral against the limit is at least `δ`
  have hint : δ ≤ ∫ a, bumpBCF ε D a ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ₁)) := by
    rw [hδ, ← integral_indicator_one hUmeas]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hUmeas)
      ((bumpBCF ε D).integrable _) fun a => ?_
    by_cases ha : a ∈ U
    · rw [Set.indicator_of_mem ha, Pi.one_apply, bumpBCF_apply, bump_eq_one hε (le_of_lt ha)]
    · rw [Set.indicator_of_notMem ha]
      exact bump_nonneg _ _
  -- so eventually the empirical bump averages are at least `δ/2`
  have hconv := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) (bumpBCF ε D)
  have hev : ∀ᶠ k in atTop, δ / 2
      ≤ ∫ a, bumpBCF ε D a ∂(empiricalSeq σ₁ Gs (s k) : Measure (FlagDensitySpace 𝕋 σ₁)) :=
    (hconv.eventually (lt_mem_nhds (by linarith : δ / 2 < _))).mono fun k hk => hk.le
  -- the constants
  set C := sizeNorm D with hC
  have hC0 : 0 ≤ C := sizeNorm_nonneg D
  set B := f.support.sup (fun M => M.1) with hB
  have hBsupp : ∀ M ∈ f.support, M.1 ≤ B := fun M hM => Finset.le_sup (f := fun M => M.1) hM
  refine ⟨ε, hε, fun K₀ => ?_⟩
  obtain ⟨K, hK⟩ := exists_nat_ge (max 2 (max (2 / δ) (max (16 * C / ε) (K₀ : ℝ))))
  have hK2 : (2 : ℝ) ≤ K := (le_max_left _ _).trans hK
  have hKδ : 2 / δ ≤ K := ((le_max_left _ _).trans (le_max_right _ _)).trans hK
  have hKC : 16 * C / ε ≤ K :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hK
  have hKK₀ : (K₀ : ℝ) ≤ K :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hK2N : 2 ≤ K := by exact_mod_cast hK2
  have hKposN : 0 < K := by omega
  have hKK₀N : K₀ ≤ K := by exact_mod_cast hKK₀
  have hδK : 2 ≤ δ * K := by
    rw [div_le_iff₀ hδpos] at hKδ
    linarith
  have hCK : 16 * C ≤ ε * K := by
    rw [div_le_iff₀ hε] at hKC
    linarith
  refine ⟨K, hKK₀N, hK2N, ?_⟩
  have hsz : Tendsto (fun k => (Gs (s k)).1) atTop atTop := h.1.comp hs.tendsto_atTop
  filter_upwards [hev, hsz.eventually_ge_atTop (4 * K + 2 * B + 2)] with k hk1 hk2
  set n := (Gs (s k)).1 with hn
  set H := hostAt Gs (s k) with hH
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn4 : (4 : ℝ) ≤ n := by
    have : 4 ≤ n := by omega
    exact_mod_cast this
  have hn2K : 2 * (K : ℝ) ≤ n := by
    have : 2 * K ≤ n := by omega
    exact_mod_cast this
  -- the good vertices
  rw [integral_empiricalSeq_vertex Gs (s k) hn0 (bumpBCF ε D).continuous] at hk1
  simp only [bumpBCF_apply, profileEval_rootedPoint] at hk1
  set Good := Finset.univ.filter (fun v : Fin n => ε / 2 ≤ hostEval (rootedAt σ₁ H v) D)
    with hGood
  have hGoodcard : (δ / 2) * n ≤ (Good.card : ℝ) := by
    have hsum : (δ / 2) * (Fintype.card (Fin n) : ℝ)
        ≤ ∑ v : Fin n, bump ε (hostEval (rootedAt σ₁ H v) D) := by
      rw [Fintype.card_fin]
      rw [le_inv_mul_iff₀ hnR] at hk1
      linarith
    have := card_filter_ge_of_avg (fun v => bump ε (hostEval (rootedAt σ₁ H v) D))
      (fun v => bump_le_one _ _) (fun v : Fin n => ε / 2 ≤ hostEval (rootedAt σ₁ H v) D)
      (fun v hv => bump_eq_zero hε (not_le.mp hv)) hsum
    rwa [Fintype.card_fin] at this
  -- the number of vertices to delete
  set t := n / K with ht
  have htK : t * K ≤ n := Nat.div_mul_le_self n K
  have hnt : n < (t + 1) * K := by
    have hdiv := Nat.div_add_mod n K
    have hmod := Nat.mod_lt n hKposN
    calc n = K * t + n % K := hdiv.symm
      _ < K * t + K := Nat.add_lt_add_left hmod _
      _ = (t + 1) * K := by ring
  have htKR : (t : ℝ) * K ≤ n := by exact_mod_cast htK
  have hntR : (n : ℝ) < (t + 1) * K := by exact_mod_cast hnt
  have ht2 : t * 2 ≤ n := (Nat.mul_le_mul_left t hK2N).trans htK
  have ht2R : (t : ℝ) * 2 ≤ n := by exact_mod_cast ht2
  have htGood : t ≤ Good.card := by
    have h1 : (t : ℝ) * 2 ≤ (t : ℝ) * (δ * K) :=
      mul_le_mul_of_nonneg_left hδK (Nat.cast_nonneg t)
    have h2 : (t : ℝ) * (δ * K) = δ * ((t : ℝ) * K) := by ring
    have h3 : δ * ((t : ℝ) * K) ≤ δ * n := mul_le_mul_of_nonneg_left htKR hδpos.le
    have h4 : (t : ℝ) ≤ (Good.card : ℝ) := by linarith only [h1, h2, h3, hGoodcard]
    exact_mod_cast h4
  obtain ⟨E, hEGood, hEcard⟩ := Finset.exists_subset_card_eq htGood
  -- the telescoping deletion
  have hstab : (t : ℝ) * sizeNorm D ≤ (ε / 2 / 2) * ((Fintype.card (Fin n) - t - 1 : ℕ) : ℝ) := by
    rw [Fintype.card_fin]
    have hcast : ((n - t - 1 : ℕ) : ℝ) = (n : ℝ) - t - 1 := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hcast]
    have h1 : (t : ℝ) * C * K ≤ (n : ℝ) * C := by
      calc (t : ℝ) * C * K = (t : ℝ) * K * C := by ring
        _ ≤ (n : ℝ) * C := mul_le_mul_of_nonneg_right htKR hC0
    have h2 : (n : ℝ) * C * 16 ≤ (n : ℝ) * (ε * K) := by
      calc (n : ℝ) * C * 16 = (n : ℝ) * (16 * C) := by ring
        _ ≤ (n : ℝ) * (ε * K) := mul_le_mul_of_nonneg_left hCK hnR.le
    have h3 : 16 * ((t : ℝ) * C) * K ≤ (n : ℝ) * ε * K := by
      calc 16 * ((t : ℝ) * C) * K = 16 * ((t : ℝ) * C * K) := by ring
        _ ≤ 16 * ((n : ℝ) * C) := by linarith only [h1]
        _ = (n : ℝ) * C * 16 := by ring
        _ ≤ (n : ℝ) * (ε * K) := h2
        _ = (n : ℝ) * ε * K := by ring
    have h4 : 16 * ((t : ℝ) * C) ≤ (n : ℝ) * ε := le_of_mul_le_mul_right h3 hKpos
    have h5 : (n : ℝ) / 4 ≤ (n : ℝ) - t - 1 := by linarith only [ht2R, hn4]
    have h6 : ε / 4 * ((n : ℝ) / 4) ≤ ε / 4 * ((n : ℝ) - t - 1) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    linarith only [h4, h6]
  have hgood' : ∀ v ∈ Good, ε / 2 ≤ hostEval (rootedAt σ₁ H v) D :=
    fun v hv => (Finset.mem_filter.mp hv).2
  have htele := hostEval_restrict_sdiff_ge H f (by positivity : 0 < ε / 2) Good hgood'
    (by rw [Fintype.card_fin]; omega)
    (fun M hM => by rw [Fintype.card_fin]; have := hBsupp M hM; omega) hstab E hEGood hEcard.le
  rw [Fintype.card_fin, hEcard] at htele
  -- the gain
  have hgain : ε / (8 * K) ≤ (t : ℝ) * (ε / 2 / 2) / n := by
    have h1 : (n : ℝ) ≤ 2 * K * t := by linarith only [hntR, hn2K]
    rw [div_le_div_iff₀ (by positivity) hnR]
    linarith only [mul_le_mul_of_nonneg_left h1 hε.le]
  exact ⟨E, hEcard, by linarith only [htele, hgain]⟩

/-- **Razborov's Theorem 4.3, linear objective, realized weak-limit form.**
If `φ₀` maximizes `φ ↦ φ(f)` and `ℙ` is a weak limit of the empirical
rooting measures along a sequence realizing `φ₀`, then `ℙ`-almost surely the
vertex differential of `f` evaluates to at most zero: otherwise the deletion
core would raise `p(f, ·)` on large hosts above the maximum. -/
theorem ae_profileEval_partialVertexVec_nonpos (h : RealizedBy φ₀ Gs)
    (f : FlagVector 𝕋 (emptyType S))
    (hmax : ∀ φ : PositiveHom 𝕋 (emptyType S), φ ⟦f⟧ ≤ φ₀ ⟦f⟧)
    {s : ℕ → ℕ} (hs : StrictMono s) {ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ₁)}
    (hlim : Tendsto (fun k => empiricalSeq σ₁ Gs (s k)) atTop (𝓝 ℙ)) :
    ∀ᵐ (a : FlagDensitySpace 𝕋 σ₁) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ₁)),
      profileEval a (partialVertexVec σ₁ f) ≤ 0 := by
  by_contra hcon
  rw [ae_iff] at hcon
  simp only [not_le] at hcon
  obtain ⟨ε, hε, hK⟩ := exists_deletion_of_pos_measure φ₀ Gs h f hs hlim hcon
  obtain ⟨K, -, hK2N, hev⟩ := hK 0
  have hKpos : (0 : ℝ) < K := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK2N
    linarith
  set η := ε / (32 * K) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨m₀, hm₀⟩ := eventually_densityEval_le φ₀ f hmax hηpos
  have hsz : Tendsto (fun k => (Gs (s k)).1) atTop atTop := h.1.comp hs.tendsto_atTop
  have hreal : Tendsto (fun k => densityEval f (Gs (s k))) atTop (𝓝 (φ₀ ⟦f⟧)) := by
    have := (realized_apply h f).comp hs.tendsto_atTop
    simpa only [densityEval_apply] using this
  have hnear := hreal.eventually (Metric.ball_mem_nhds _ hηpos)
  -- the contradiction at a large host
  have hfalse : ∀ᶠ k : ℕ in atTop, False := by
    filter_upwards [hev, hsz.eventually_ge_atTop (2 * m₀ + 2), hnear] with k hk1 hk2 hk3
    set n := (Gs (s k)).1 with hn
    set H := hostAt Gs (s k) with hH
    obtain ⟨E, hEcard, htele⟩ := hk1
    set t := n / K with ht
    have ht2 : t * 2 ≤ n := (Nat.mul_le_mul_left _ hK2N).trans (Nat.div_mul_le_self n K)
    have htele' : hostEval H f + ε / (8 * K)
        ≤ hostEval (H.restrict (Finset.univ \ E) (emptyType_root_mem H _)) f := htele
    -- the upper bound at the deleted host
    have hup : hostEval (H.restrict (Finset.univ \ E) (emptyType_root_mem H _)) f
        ≤ φ₀ ⟦f⟧ + η := by
      rw [hostEval_eq_densityEval_reindex]
      refine hm₀ _ ?_
      dsimp only
      rw [Fintype.card_coe, Finset.card_univ_diff, hEcard, Fintype.card_fin]
      omega
    -- the lower bound at the host
    have hlow : φ₀ ⟦f⟧ - η < hostEval H f := by
      have h1 : hostEval H f = densityEval f (Gs (s k)) := (densityEval_out f (Gs (s k)).2).symm
      rw [Real.dist_eq, abs_sub_lt_iff] at hk3
      linarith [h1, hk3.2]
    have hlt' : ε / (16 * K) < ε / (8 * K) :=
      div_lt_div_of_pos_left hε (by positivity) (by linarith)
    have h2η : 2 * η = ε / (16 * K) := by
      rw [hη]
      field_simp
      ring
    linarith only [hlow, htele', hup, hlt', h2η]
  obtain ⟨k, hk⟩ := hfalse.exists
  exact hk

/-- The mean of the vertex differential under the weak limit is zero. -/
theorem integral_profileEval_partialVertexVec (h : RealizedBy φ₀ Gs)
    (f : FlagVector 𝕋 (emptyType S)) {s : ℕ → ℕ} (hs : StrictMono s)
    {ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ₁)}
    (hlim : Tendsto (fun k => empiricalSeq σ₁ Gs (s k)) atTop (𝓝 ℙ)) :
    ∫ a, profileEval a (partialVertexVec σ₁ f) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ₁)) = 0 := by
  set D := partialVertexVec σ₁ f with hD
  set B := f.support.sup (fun M => M.1) with hB
  have hBsupp : ∀ M ∈ f.support, M.1 ≤ B := fun M hM => Finset.le_sup (f := fun M => M.1) hM
  have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) (profileEvalBCF D)
  have h2 : Tendsto (fun k => ∫ a, profileEvalBCF D a
      ∂(empiricalSeq σ₁ Gs (s k) : Measure (FlagDensitySpace 𝕋 σ₁))) atTop (𝓝 0) := by
    have hsz : Tendsto (fun k => (Gs (s k)).1) atTop atTop := h.1.comp hs.tendsto_atTop
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hsz.eventually_ge_atTop (B + 1)] with k hk
    rw [integral_empiricalSeq_vertex Gs (s k) (by omega) (profileEvalBCF D).continuous]
    simp only [profileEvalBCF_apply, profileEval_rootedPoint]
    rw [sum_hostEval_partialVertexVec (σ₁ := σ₁) (hostAt Gs (s k)) f (L := (Gs (s k)).1 - 1)
      (by rw [Fintype.card_fin]; omega) (fun M hM => by have := hBsupp M hM; omega), mul_zero]
  have h3 := tendsto_nhds_unique h1 h2
  simpa only [profileEvalBCF_apply] using h3

omit [S.NullaryFree] [𝕋.VertexUniform σ₁] [𝕋.IsType σ₁] [𝕋.IsType (emptyType S)] in
/-- An almost surely nonpositive evaluation with zero mean vanishes almost
surely. -/
theorem ae_profileEval_eq_zero_of_nonpos {ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ₁)}
    (D : FlagVector 𝕋 σ₁)
    (hle : ∀ᵐ (a : FlagDensitySpace 𝕋 σ₁) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ₁)),
      profileEval a D ≤ 0)
    (hint : ∫ a, profileEval a D ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ₁)) = 0) :
    ∀ᵐ (a : FlagDensitySpace 𝕋 σ₁) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ₁)),
      profileEval a D = 0 := by
  have hneg : ∫ a, (-profileEval a D) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ₁)) = 0 := by
    rw [integral_neg, hint, neg_zero]
  have hnonneg : 0 ≤ᵐ[(ℙ : Measure (FlagDensitySpace 𝕋 σ₁))] fun a => -profileEval a D :=
    hle.mono fun a ha => by
      show (0 : ℝ) ≤ -profileEval a D
      linarith
  have hinteg : Integrable (fun a => -profileEval a D) (ℙ : Measure (FlagDensitySpace 𝕋 σ₁)) :=
    ((profileEvalBCF D).integrable _).neg
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hinteg).mp hneg
  filter_upwards [hzero] with a ha
  have : -profileEval a D = 0 := ha
  linarith

/-- **Theorem 4.3, equality form**: the vertex differential of the objective
vanishes `ℙ`-almost surely at a maximizer. -/
theorem ae_profileEval_partialVertexVec_eq_zero (h : RealizedBy φ₀ Gs)
    (f : FlagVector 𝕋 (emptyType S))
    (hmax : ∀ φ : PositiveHom 𝕋 (emptyType S), φ ⟦f⟧ ≤ φ₀ ⟦f⟧)
    {s : ℕ → ℕ} (hs : StrictMono s) {ℙ : ProbabilityMeasure (FlagDensitySpace 𝕋 σ₁)}
    (hlim : Tendsto (fun k => empiricalSeq σ₁ Gs (s k)) atTop (𝓝 ℙ)) :
    ∀ᵐ (a : FlagDensitySpace 𝕋 σ₁) ∂(ℙ : Measure (FlagDensitySpace 𝕋 σ₁)),
      profileEval a (partialVertexVec σ₁ f) = 0 :=
  ae_profileEval_eq_zero_of_nonpos _
    (ae_profileEval_partialVertexVec_nonpos φ₀ Gs h f hmax hs hlim)
    (integral_profileEval_partialVertexVec φ₀ Gs h f hs hlim)

end Maximizer

end FlagAlgebras.Core
