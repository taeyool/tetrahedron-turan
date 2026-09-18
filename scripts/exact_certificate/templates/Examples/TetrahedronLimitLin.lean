import LeanFlagAlgebras.Core.Examples.TetrahedronCompact

/-! # The limit functional, linear layer

The first half of the limit-homomorphism construction: a density-vector
limit satisfies the averaging relations *exactly*, because the finite
chain rule holds exactly at every finite size and passes to the limit.
So the limit functional, extended linearly to flag vectors, kills the
`ZeroSpace` generators and descends to the flag-algebra quotient.

Multiplicativity — the second half — rides on the product
approximation and is the sequel. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

/-- A functional on finite flags is *chain closed* when it satisfies
every averaging relation. -/
def ChainClosed (L : FinFlag TetraFree emptyType → ℝ) : Prop :=
  ∀ (F : FinFlag TetraFree emptyType) (ℓ : ℕ), F.1 ≤ ℓ →
    L F = ∑ F' : FlagWithSize TetraFree emptyType ℓ,
      ((subflagDensity F.2 F' : ℚ) : ℝ) * L ⟨ℓ, F'⟩

/-- **A density-vector limit is chain closed**: the finite chain rule is
exact at each size and survives the limit. -/
theorem chainClosed_of_tendsto (Gs : ℕ → FinFlag TetraFree emptyType)
    (L : FinFlag TetraFree emptyType → ℝ)
    (hsz : Filter.Tendsto (fun k => (Gs k).1) Filter.atTop Filter.atTop)
    (hconv : ∀ F : FinFlag TetraFree emptyType,
      Filter.Tendsto (fun k => ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ))
        Filter.atTop (nhds (L F))) :
    ChainClosed L := by
  intro F ℓ hFℓ
  have hRHS : Filter.Tendsto
      (fun k => ∑ F' : FlagWithSize TetraFree emptyType ℓ,
        ((subflagDensity F.2 F' : ℚ) : ℝ)
          * ((subflagDensity F' (Gs k).2 : ℚ) : ℝ))
      Filter.atTop
      (nhds (∑ F' : FlagWithSize TetraFree emptyType ℓ,
        ((subflagDensity F.2 F' : ℚ) : ℝ) * L ⟨ℓ, F'⟩)) := by
    refine tendsto_finset_sum _ fun F' _ => ?_
    exact (hconv ⟨ℓ, F'⟩).const_mul _
  have hev : ∀ᶠ k in Filter.atTop,
      ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ)
        = ∑ F' : FlagWithSize TetraFree emptyType ℓ,
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

/-- The linear extension of a limit functional to flag vectors. -/
noncomputable def limitLin (L : FinFlag TetraFree emptyType → ℝ) :
    FlagVector TetraFree emptyType →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ L

@[simp]
lemma limitLin_basis (L : FinFlag TetraFree emptyType → ℝ)
    (F : FinFlag TetraFree emptyType) :
    limitLin L (basisVector F) = L F := by
  rw [limitLin, basisVector, Finsupp.linearCombination_single, one_smul]

/-- A chain-closed functional kills every generator. -/
lemma limitLin_zeroElement {L : FinFlag TetraFree emptyType → ℝ}
    (hC : ChainClosed L) (F : FinFlag TetraFree emptyType) (ℓ : ℕ)
    (hFℓ : F.1 ≤ ℓ) :
    limitLin L (zeroElement F ℓ) = 0 := by
  rw [zeroElement, map_sub, limitLin_basis, flagExpansion, map_sum]
  rw [Finset.sum_congr rfl fun F' (_ : F' ∈ Finset.univ) => by
    rw [map_smul, limitLin_basis]]
  rw [hC F ℓ hFℓ, sub_eq_zero]
  rfl

/-- A chain-closed functional kills the whole `ZeroSpace`. -/
lemma limitLin_zeroSpace {L : FinFlag TetraFree emptyType → ℝ}
    (hC : ChainClosed L) {k : FlagVector TetraFree emptyType}
    (hk : k ∈ ZeroSpace TetraFree emptyType) :
    limitLin L k = 0 := by
  have hle : ZeroSpace TetraFree emptyType
      ≤ LinearMap.ker (limitLin L) := by
    rw [ZeroSpace, Submodule.span_le]
    rintro x ⟨F, ℓ, hFℓ, rfl⟩
    exact LinearMap.mem_ker.mpr (limitLin_zeroElement hC F ℓ hFℓ)
  exact LinearMap.mem_ker.mp (hle hk)

/-! ## Descent to the quotient -/

/-- The limit functional descends to the flag algebra: flag-equal
vectors differ by `ZeroSpace`, which the functional kills. -/
noncomputable def limitQuot {L : FinFlag TetraFree emptyType → ℝ}
    (hC : ChainClosed L) : FlagAlgebra TetraFree emptyType → ℝ :=
  Quotient.lift (fun f => limitLin L f) fun f g hfg => by
    have h0 := limitLin_zeroSpace hC hfg
    rw [map_sub] at h0
    linarith

@[simp]
lemma limitQuot_mk {L : FinFlag TetraFree emptyType → ℝ}
    (hC : ChainClosed L) (f : FlagVector TetraFree emptyType) :
    limitQuot hC ⟦f⟧ = limitLin L f := rfl

@[simp]
lemma limitQuot_basis {L : FinFlag TetraFree emptyType → ℝ}
    (hC : ChainClosed L) (F : FinFlag TetraFree emptyType) :
    limitQuot hC ⟦basisVector F⟧ = L F := by
  rw [limitQuot_mk, limitLin_basis]

/-- The descent is additive. -/
lemma limitQuot_add {L : FinFlag TetraFree emptyType → ℝ}
    (hC : ChainClosed L) (x y : FlagAlgebra TetraFree emptyType) :
    limitQuot hC (x + y) = limitQuot hC x + limitQuot hC y := by
  refine Quotient.inductionOn₂ x y fun f g => ?_
  rw [← add_quot, limitQuot_mk, limitQuot_mk, limitQuot_mk, map_add]

/-- The descent respects scalars. -/
lemma limitQuot_smul {L : FinFlag TetraFree emptyType → ℝ}
    (hC : ChainClosed L) (r : ℝ) (x : FlagAlgebra TetraFree emptyType) :
    limitQuot hC (r • x) = r * limitQuot hC x := by
  refine Quotient.inductionOn x fun f => ?_
  rw [← smul_quot, limitQuot_mk, limitQuot_mk, map_smul, smul_eq_mul]

/-- The descent sends the unit to the value at the unit flag. -/
lemma limitQuot_one {L : FinFlag TetraFree emptyType → ℝ}
    (hC : ChainClosed L) :
    limitQuot hC (1 : FlagAlgebra TetraFree emptyType) = L 1 := by
  show limitQuot hC ⟦(1 : FlagVector TetraFree emptyType)⟧ = L 1
  rw [show (1 : FlagVector TetraFree emptyType)
      = basisVector 1 from rfl, limitQuot_basis]

/-! ## The limit values along a realizing sequence -/

/-- Density-vector limits are nonnegative coordinatewise. -/
lemma limit_nonneg (Gs : ℕ → FinFlag TetraFree emptyType)
    (L : FinFlag TetraFree emptyType → ℝ)
    (hconv : ∀ F : FinFlag TetraFree emptyType,
      Filter.Tendsto (fun k => ((subflagDensity F.2 (Gs k).2 : ℚ) : ℝ))
        Filter.atTop (nhds (L F)))
    (F : FinFlag TetraFree emptyType) : 0 ≤ L F := by
  refine ge_of_tendsto (hconv F) ?_
  filter_upwards with k
  exact_mod_cast subflagDensity_nonneg F.2 (Gs k).2

end FlagAlgebras.Core.Tetrahedron
