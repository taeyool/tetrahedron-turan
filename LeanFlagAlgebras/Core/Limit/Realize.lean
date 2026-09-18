import LeanFlagAlgebras.Core.Limit.Compact
import LeanFlagAlgebras.Core.Downward

/-! # Core: realization — the limit half of Razborov's Theorem 3.3

Along a sequence of finite flags whose sizes blow up and whose flag
densities converge, the limit profile has the four properties of
`Core/Limit/Profile`: it is chain closed (the finite chain rule is exact
at every size and survives the limit), multiplicatively closed (pair
densities converge to products, by the product approximation whose defect
is `O(1/|G|)`), normalised, and nonnegative. Packaged, that is a positive
homomorphism *realized* by the sequence, and with subsequence compactness
every size-blowing sequence of finite flags has a realized subsequence.

The value of a realized homomorphism at any class is the limit of the
finite density combinations (`realized_apply`): no sampling direction of
realization is needed to read values off finite models.

Generalises `Core/Examples/TetrahedronLimitLin`, `TetrahedronLimitMul`,
`TetrahedronLimitHom` and `TetrahedronRealizedApply` from the
tetrahedron-free theory over the empty type to an arbitrary theory and
type. -/

namespace FlagAlgebras.Core

open Filter

variable {S : Signature} {T : Type} [Fintype T]
variable {𝕋 : RelTheory S} {σ : Model S T}

/-- A sequence of finite flags realizes a homomorphism: the sizes blow
up and every flag density converges to the homomorphism's value. -/
def RealizedBy [𝕋.IsType σ] (φ : PositiveHom 𝕋 σ) (Gs : ℕ → FinFlag 𝕋 σ) :
    Prop :=
  Tendsto (fun k => (Gs k).1) atTop atTop
    ∧ ∀ F : FinFlag 𝕋 σ,
        Tendsto (fun k => ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ))
          atTop (nhds (φ ⟦basisVector F⟧))

section Limits

variable (Gs : ℕ → FinFlag 𝕋 σ) (L : FinFlag 𝕋 σ → ℝ)

/-- **A density-vector limit is chain closed**: the finite chain rule is
exact at each size and survives the limit. -/
theorem chainClosed_of_tendsto
    (hsz : Tendsto (fun k => (Gs k).1) atTop atTop)
    (hconv : ∀ F : FinFlag 𝕋 σ,
      Tendsto (fun k => ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ))
        atTop (nhds (L F))) :
    ChainClosed L := by
  intro F ℓ hFℓ
  have hRHS : Tendsto
      (fun k => ∑ F' : FlagWithSize 𝕋 σ ℓ,
        ((subflagDensity F.2 F' : ℚ) : ℝ)
          * ((subflagDensity F' (Gs k).2 : ℚ) : ℝ))
      atTop
      (nhds (∑ F' : FlagWithSize 𝕋 σ ℓ,
        ((subflagDensity F.2 F' : ℚ) : ℝ) * L ⟨ℓ, F'⟩)) := by
    refine tendsto_finset_sum _ fun F' _ => ?_
    exact (hconv ⟨ℓ, F'⟩).const_mul _
  have hev : ∀ᶠ k in atTop,
      ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ)
        = ∑ F' : FlagWithSize 𝕋 σ ℓ,
            ((subflagDensity F.2 F' : ℚ) : ℝ)
              * ((subflagDensity F' (Gs k).2 : ℚ) : ℝ) := by
    filter_upwards [hsz.eventually_ge_atTop ℓ] with k hk
    have hchain := subflagDensity_chain (W' := Fin ℓ)
      (by simpa using hFℓ) (by simpa using hk) F.2 (Gs k).2
    rw [hchain]
    push_cast
    rfl
  have h2 := hRHS.congr' (hev.mono fun k hk => hk.symm)
  exact tendsto_nhds_unique (hconv F) h2

/-- The pair density on classes is the labeled pair density of
representatives. -/
private lemma pairDensity_out {U₁ U₂ V : Type} [Fintype U₁] [Fintype U₂]
    [Fintype V] (A : Flag 𝕋 σ U₁) (B : Flag 𝕋 σ U₂) (C : Flag 𝕋 σ V) :
    subflagPairDensity A B C
      = flagPairDensity (Quotient.out A) (Quotient.out B)
        (Quotient.out C) := by
  conv_lhs => rw [← Quotient.out_eq A, ← Quotient.out_eq B,
    ← Quotient.out_eq C]
  rfl

/-- The product approximation on classes, general sizes, cast to `ℝ`. -/
lemma abs_subflagPairDensity_sub_mul_le {m₁ m₂ n : ℕ}
    (F₁ : FlagWithSize 𝕋 σ m₁) (F₂ : FlagWithSize 𝕋 σ m₂)
    (G : FlagWithSize 𝕋 σ n)
    (h : m₁ + m₂ ≤ n + Fintype.card T) (hn : Fintype.card T < n) :
    |((subflagPairDensity F₁ F₂ G : ℚ) : ℝ)
        - ((subflagDensity F₁ G : ℚ) : ℝ)
          * ((subflagDensity F₂ G : ℚ) : ℝ)|
      ≤ (((m₁ - Fintype.card T) * (m₂ - Fintype.card T) : ℕ) : ℝ)
          / ((n - Fintype.card T : ℕ) : ℝ) := by
  have hq : |subflagPairDensity F₁ F₂ G
      - subflagDensity F₁ G * subflagDensity F₂ G|
      ≤ (((m₁ - Fintype.card T) * (m₂ - Fintype.card T) : ℕ) : ℚ)
          / ((n - Fintype.card T : ℕ) : ℚ) := by
    rw [pairDensity_out, subflagDensity_out, subflagDensity_out]
    have h0 := abs_flagPairDensity_sub_mul_le (Quotient.out F₁)
      (Quotient.out F₂) (Quotient.out G) (by simpa using h)
      (by simpa using hn)
    simpa using h0
  have h' := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at h'
  push_cast
  exact h'

/-- **Pair densities converge to the product of the limit values.** -/
theorem pair_tendsto
    (hsz : Tendsto (fun k => (Gs k).1) atTop atTop)
    (hconv : ∀ F : FinFlag 𝕋 σ,
      Tendsto (fun k => ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ))
        atTop (nhds (L F)))
    (F₁ F₂ : FinFlag 𝕋 σ) :
    Tendsto
      (fun k => ((subflagPairDensity F₁.2 F₂.2 (Gs k).2 : ℚ) : ℝ))
      atTop (nhds (L F₁ * L F₂)) := by
  have hprod := (hconv F₁).mul (hconv F₂)
  have hszN : Tendsto (fun k => (Gs k).1 - Fintype.card T) atTop atTop :=
    (tendsto_sub_atTop_nat (Fintype.card T)).comp hsz
  have hszR : Tendsto (fun k => (((Gs k).1 - Fintype.card T : ℕ) : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hszN
  have hzero : Tendsto
      (fun k => (((F₁.1 - Fintype.card T) * (F₂.1 - Fintype.card T) : ℕ) : ℝ)
        / (((Gs k).1 - Fintype.card T : ℕ) : ℝ))
      atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hszR
  have hbound : ∀ᶠ k in atTop,
      |((subflagPairDensity F₁.2 F₂.2 (Gs k).2 : ℚ) : ℝ)
        - ((subflagDensity F₁.2 (Gs k).2 : ℚ) : ℝ)
          * ((subflagDensity F₂.2 (Gs k).2 : ℚ) : ℝ)|
      ≤ (((F₁.1 - Fintype.card T) * (F₂.1 - Fintype.card T) : ℕ) : ℝ)
          / (((Gs k).1 - Fintype.card T : ℕ) : ℝ) := by
    filter_upwards [hsz.eventually_ge_atTop (F₁.1 + F₂.1),
      hsz.eventually_ge_atTop (Fintype.card T + 1)] with k hk hk1
    exact abs_subflagPairDensity_sub_mul_le F₁.2 F₂.2 (Gs k).2 (by omega) (by omega)
  have hnegzero : Tendsto
      (fun k => -((((F₁.1 - Fintype.card T) * (F₂.1 - Fintype.card T) : ℕ) : ℝ)
        / (((Gs k).1 - Fintype.card T : ℕ) : ℝ)))
      atTop (nhds 0) := by
    simpa using hzero.neg
  have hdiff : Tendsto
      (fun k => ((subflagPairDensity F₁.2 F₂.2 (Gs k).2 : ℚ) : ℝ)
        - ((subflagDensity F₁.2 (Gs k).2 : ℚ) : ℝ)
          * ((subflagDensity F₂.2 (Gs k).2 : ℚ) : ℝ))
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hnegzero hzero
      (hbound.mono fun k hk => neg_le_of_abs_le hk)
      (hbound.mono fun k hk => le_of_abs_le hk)
  have hsum := hdiff.add hprod
  rw [zero_add] at hsum
  refine hsum.congr fun k => ?_
  ring

/-- **A density-vector limit is multiplicatively closed**: the pair chain
rule at the product size, exact at every finite size, survives the limit
and identifies the structure constants against the limit values with the
product of the limit values. -/
theorem mulClosed_of_tendsto
    (hsz : Tendsto (fun k => (Gs k).1) atTop atTop)
    (hconv : ∀ F : FinFlag 𝕋 σ,
      Tendsto (fun k => ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ))
        atTop (nhds (L F))) :
    MulClosed L := by
  intro F₁ F₂
  have hk₁ := finFlag_size_ge F₁
  have hk₂ := finFlag_size_ge F₂
  have hRHS : Tendsto
      (fun k => ∑ G : FlagWithSize 𝕋 σ (F₁.1 + F₂.1 - Fintype.card T),
        ((subflagPairDensity F₁.2 F₂.2 G : ℚ) : ℝ)
          * ((subflagDensity G (Gs k).2 : ℚ) : ℝ))
      atTop
      (nhds (∑ G : FlagWithSize 𝕋 σ (F₁.1 + F₂.1 - Fintype.card T),
        ((subflagPairDensity F₁.2 F₂.2 G : ℚ) : ℝ)
          * L ⟨F₁.1 + F₂.1 - Fintype.card T, G⟩)) := by
    refine tendsto_finset_sum _ fun G _ => ?_
    exact (hconv ⟨F₁.1 + F₂.1 - Fintype.card T, G⟩).const_mul _
  have hev : ∀ᶠ k in atTop,
      ((subflagPairDensity F₁.2 F₂.2 (Gs k).2 : ℚ) : ℝ)
        = ∑ G : FlagWithSize 𝕋 σ (F₁.1 + F₂.1 - Fintype.card T),
            ((subflagPairDensity F₁.2 F₂.2 G : ℚ) : ℝ)
              * ((subflagDensity G (Gs k).2 : ℚ) : ℝ) := by
    filter_upwards [hsz.eventually_ge_atTop (F₁.1 + F₂.1 - Fintype.card T)]
      with k hk
    have hchain := subflagPairDensity_chain_host
      (W' := Fin (F₁.1 + F₂.1 - Fintype.card T))
      (by simp only [Fintype.card_fin]; omega)
      (by simpa using hk) F₁.2 F₂.2 (Gs k).2
    rw [hchain]
    push_cast
    rfl
  have h2 := hRHS.congr' (hev.mono fun k hk => hk.symm)
  exact tendsto_nhds_unique h2 (pair_tendsto Gs L hsz hconv F₁ F₂)

/-- **The unit value is one** along a realizing sequence. -/
lemma limit_one [𝕋.IsType σ]
    (hconv : ∀ F : FinFlag 𝕋 σ,
      Tendsto (fun k => ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ))
        atTop (nhds (L F))) :
    L 1 = 1 := by
  refine tendsto_nhds_unique (hconv 1) ?_
  have hone : ∀ k : ℕ,
      ((subflagDensity (1 : FinFlag 𝕋 σ).2 (Gs k).2 : ℚ) : ℝ) = 1 := by
    intro k
    rw [finFlag_one_snd, subflagDensity_unitFlag]
    norm_num
  refine Tendsto.congr (fun k => (hone k).symm) ?_
  exact tendsto_const_nhds

/-- Density-vector limits are nonnegative coordinatewise. -/
lemma limit_nonneg
    (hconv : ∀ F : FinFlag 𝕋 σ,
      Tendsto (fun k => ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ))
        atTop (nhds (L F)))
    (F : FinFlag 𝕋 σ) : 0 ≤ L F := by
  refine ge_of_tendsto (hconv F) ?_
  filter_upwards with k
  exact_mod_cast subflagDensity_nonneg F.2 (Gs k).2

end Limits

section Hom

variable [𝕋.IsType σ]

/-- **The limit homomorphism**: the profile of a convergent, size-blowing
sequence, packaged as a positive homomorphism. -/
noncomputable def limitHom (Gs : ℕ → FinFlag 𝕋 σ) (L : FinFlag 𝕋 σ → ℝ)
    (hsz : Tendsto (fun k => (Gs k).1) atTop atTop)
    (hconv : ∀ F : FinFlag 𝕋 σ,
      Tendsto (fun k => ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ))
        atTop (nhds (L F))) : PositiveHom 𝕋 σ :=
  homOfProfile L (chainClosed_of_tendsto Gs L hsz hconv)
    (mulClosed_of_tendsto Gs L hsz hconv) (limit_one Gs L hconv)
    (limit_nonneg Gs L hconv)

@[simp]
lemma limitHom_basis (Gs : ℕ → FinFlag 𝕋 σ) (L : FinFlag 𝕋 σ → ℝ)
    (hsz : Tendsto (fun k => (Gs k).1) atTop atTop)
    (hconv : ∀ F : FinFlag 𝕋 σ,
      Tendsto (fun k => ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ))
        atTop (nhds (L F)))
    (F : FinFlag 𝕋 σ) :
    limitHom Gs L hsz hconv ⟦basisVector F⟧ = L F :=
  homOfProfile_basis L _ _ _ _ F

/-- **The limit homomorphism is realized by the sequence.** -/
theorem limitHom_realizedBy (Gs : ℕ → FinFlag 𝕋 σ) (L : FinFlag 𝕋 σ → ℝ)
    (hsz : Tendsto (fun k => (Gs k).1) atTop atTop)
    (hconv : ∀ F : FinFlag 𝕋 σ,
      Tendsto (fun k => ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ))
        atTop (nhds (L F))) :
    RealizedBy (limitHom Gs L hsz hconv) Gs := by
  refine ⟨hsz, fun F => ?_⟩
  rw [limitHom_basis]
  exact hconv F

/-- **The limit half of realization** (Razborov, Theorem 3.3 (a)): every
size-blowing sequence of finite flags has a subsequence realizing a
positive homomorphism. -/
theorem exists_realized_subseq (Gs : ℕ → FinFlag 𝕋 σ)
    (hsz : Tendsto (fun k => (Gs k).1) atTop atTop) :
    ∃ s : ℕ → ℕ, StrictMono s
      ∧ ∃ ψ : PositiveHom 𝕋 σ, RealizedBy ψ (fun k => Gs (s k)) := by
  obtain ⟨s, hs, hsz', L, hconv⟩ := exists_convergent_subseq Gs hsz
  exact ⟨s, hs, limitHom (fun k => Gs (s k)) L hsz' hconv,
    limitHom_realizedBy (fun k => Gs (s k)) L hsz' hconv⟩

/-- **The value of a realized homomorphism at any class is the limit of
the finite density combinations.** -/
theorem realized_apply {φ : PositiveHom 𝕋 σ} {Gs : ℕ → FinFlag 𝕋 σ}
    (h : RealizedBy φ Gs) (f : FlagVector 𝕋 σ) :
    Tendsto
      (fun k => ∑ F ∈ f.support,
        f F * ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ))
      atTop (nhds (φ ⟦f⟧)) := by
  rw [PositiveHom.apply_quot]
  exact tendsto_finset_sum _ fun F _ => (h.2 F).const_mul (f F)

/-- A realized homomorphism's profile is the limit of the density
vectors. -/
theorem RealizedBy.tendsto_densityVec {φ : PositiveHom 𝕋 σ}
    {Gs : ℕ → FinFlag 𝕋 σ} (h : RealizedBy φ Gs) (F : FinFlag 𝕋 σ) :
    Tendsto (fun k => densityVec (Gs k) F) atTop (nhds (φ.profile F)) :=
  h.2 F

end Hom

end FlagAlgebras.Core
