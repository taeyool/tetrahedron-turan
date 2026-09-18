import LeanFlagAlgebras.Core.Examples.TetrahedronLimitLin

/-! # Pair densities in the limit

The multiplicative half of the limit homomorphism, analytic part. Along
a realizing sequence the pair density of two flags converges to the
product of the limit values: the product approximation bounds the
defect against the single densities by `O(1/|G|)`, which vanishes as
the sizes blow up. Feeding the exact pair chain rule through that limit
identifies the flag product's structure constants with the product of
the limit values — the equation `limitQuot` needs to be multiplicative
on basis classes. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core Filter

/-- The pair density on classes is the labeled pair density of
representatives. -/
private lemma pairDensity_out {U₁ U₂ V : Type} [Fintype U₁] [Fintype U₂]
    [Fintype V] (A : Flag TetraFree emptyType U₁)
    (B : Flag TetraFree emptyType U₂) (C : Flag TetraFree emptyType V) :
    subflagPairDensity A B C
      = flagPairDensity (Quotient.out A) (Quotient.out B)
        (Quotient.out C) := by
  conv_lhs => rw [← Quotient.out_eq A, ← Quotient.out_eq B,
    ← Quotient.out_eq C]
  rfl

/-- The product approximation on classes, general sizes, cast to `ℝ`. -/
private lemma abs_pair_est {m₁ m₂ n : ℕ}
    (F₁ : FlagWithSize TetraFree emptyType m₁)
    (F₂ : FlagWithSize TetraFree emptyType m₂)
    (G : FlagWithSize TetraFree emptyType n)
    (h : m₁ + m₂ ≤ n) (hn : 0 < n) :
    |((subflagPairDensity F₁ F₂ G : ℚ) : ℝ)
        - ((subflagDensity F₁ G : ℚ) : ℝ)
          * ((subflagDensity F₂ G : ℚ) : ℝ)|
      ≤ ((m₁ * m₂ : ℕ) : ℝ) / (n : ℝ) := by
  have hq : |subflagPairDensity F₁ F₂ G
      - subflagDensity F₁ G * subflagDensity F₂ G|
      ≤ ((m₁ * m₂ : ℕ) : ℚ) / ((n : ℕ) : ℚ) := by
    rw [pairDensity_out, subflagDensity_out, subflagDensity_out]
    have h0 := abs_flagPairDensity_sub_mul_le (Quotient.out F₁)
      (Quotient.out F₂) (Quotient.out G) (by simpa using h)
      (by simpa using hn)
    simpa using h0
  have h' := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at h'
  push_cast
  exact h'

variable (Gs : ℕ → FinFlag TetraFree emptyType)
    (L : FinFlag TetraFree emptyType → ℝ)

/-- **Pair densities converge to the product of the limit values.** -/
theorem pair_tendsto
    (hsz : Tendsto (fun k => (Gs k).1) atTop atTop)
    (hconv : ∀ F : FinFlag TetraFree emptyType,
      Tendsto (fun k => ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ))
        atTop (nhds (L F)))
    (F₁ F₂ : FinFlag TetraFree emptyType) :
    Tendsto
      (fun k => ((subflagPairDensity F₁.2 F₂.2 (Gs k).2 : ℚ) : ℝ))
      atTop (nhds (L F₁ * L F₂)) := by
  have hprod := (hconv F₁).mul (hconv F₂)
  have hszR : Tendsto (fun k => ((Gs k).1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsz
  have hzero : Tendsto
      (fun k => ((F₁.1 * F₂.1 : ℕ) : ℝ) / ((Gs k).1 : ℝ))
      atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hszR
  have hbound : ∀ᶠ k in atTop,
      |((subflagPairDensity F₁.2 F₂.2 (Gs k).2 : ℚ) : ℝ)
        - ((subflagDensity F₁.2 (Gs k).2 : ℚ) : ℝ)
          * ((subflagDensity F₂.2 (Gs k).2 : ℚ) : ℝ)|
      ≤ ((F₁.1 * F₂.1 : ℕ) : ℝ) / ((Gs k).1 : ℝ) := by
    filter_upwards [hsz.eventually_ge_atTop (F₁.1 + F₂.1),
      hsz.eventually_ge_atTop 1] with k hk hk1
    exact abs_pair_est F₁.2 F₂.2 (Gs k).2 hk (by omega)
  have hnegzero : Tendsto
      (fun k => -(((F₁.1 * F₂.1 : ℕ) : ℝ) / ((Gs k).1 : ℝ)))
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

/-- **The pair chain rule in the limit**: the flag product's structure
constants against the limit values give the product of the limit
values. -/
theorem pairChain_limit
    (hsz : Tendsto (fun k => (Gs k).1) atTop atTop)
    (hconv : ∀ F : FinFlag TetraFree emptyType,
      Tendsto (fun k => ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ))
        atTop (nhds (L F)))
    (F₁ F₂ : FinFlag TetraFree emptyType) :
    (∑ G : FlagWithSize TetraFree emptyType (F₁.1 + F₂.1),
      ((subflagPairDensity F₁.2 F₂.2 G : ℚ) : ℝ) * L ⟨F₁.1 + F₂.1, G⟩)
      = L F₁ * L F₂ := by
  have hRHS : Tendsto
      (fun k => ∑ G : FlagWithSize TetraFree emptyType (F₁.1 + F₂.1),
        ((subflagPairDensity F₁.2 F₂.2 G : ℚ) : ℝ)
          * ((subflagDensity G (Gs k).2 : ℚ) : ℝ))
      atTop
      (nhds (∑ G : FlagWithSize TetraFree emptyType (F₁.1 + F₂.1),
        ((subflagPairDensity F₁.2 F₂.2 G : ℚ) : ℝ)
          * L ⟨F₁.1 + F₂.1, G⟩)) := by
    refine tendsto_finset_sum _ fun G _ => ?_
    exact (hconv ⟨F₁.1 + F₂.1, G⟩).const_mul _
  have hev : ∀ᶠ k in atTop,
      ((subflagPairDensity F₁.2 F₂.2 (Gs k).2 : ℚ) : ℝ)
        = ∑ G : FlagWithSize TetraFree emptyType (F₁.1 + F₂.1),
            ((subflagPairDensity F₁.2 F₂.2 G : ℚ) : ℝ)
              * ((subflagDensity G (Gs k).2 : ℚ) : ℝ) := by
    filter_upwards [hsz.eventually_ge_atTop (F₁.1 + F₂.1)] with k hk
    have hchain := subflagPairDensity_chain_host
      (W' := Fin (F₁.1 + F₂.1)) (by simpa)
      (by simpa using hk) F₁.2 F₂.2 (Gs k).2
    rw [hchain]
    push_cast
    rfl
  have h2 := hRHS.congr' (hev.mono fun k hk => hk.symm)
  exact tendsto_nhds_unique h2 (pair_tendsto Gs L hsz hconv F₁ F₂)

end FlagAlgebras.Core.Tetrahedron
