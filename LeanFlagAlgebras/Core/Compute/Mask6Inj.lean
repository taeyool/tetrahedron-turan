import LeanFlagAlgebras.Core.Compute.MaskInj

/-! # Injectivity of six-vertex mask decoding

The twenty low bits are exactly the ranks of the sorted triples.
This proof uses ordinary kernel reduction for the finite rank cover.
-/

namespace FlagAlgebras.Core

private lemma triCover6 : ∀ k < 20, ∃ a b c : Fin 6, a < b ∧ b < c
    ∧ triIdx 6 a.val b.val c.val = k := by decide

/-- Decoding six-vertex masks is injective below `2^20`. -/
lemma graphOfMask6_inj {m₁ m₂ : ℕ} (h₁ : m₁ < 2 ^ 20) (h₂ : m₂ < 2 ^ 20)
    (h : graphOfMask 6 m₁ = graphOfMask 6 m₂) : m₁ = m₂ := by
  refine eq_of_lt_two_pow h₁ h₂ fun k hk => ?_
  obtain ⟨a, b, c, hab, hbc, hidx⟩ := triCover6 k hk
  rw [← hidx]
  cases hm1 : m₁.testBit (triIdx 6 a.val b.val c.val) with
  | true =>
    have hmem := (testBit_iff_mem_edges' hab hbc).mp hm1
    rw [h] at hmem
    exact ((testBit_iff_mem_edges' hab hbc).mpr hmem).symm
  | false =>
    cases hm2 : m₂.testBit (triIdx 6 a.val b.val c.val) with
    | true =>
      have hmem := (testBit_iff_mem_edges' hab hbc).mp hm2
      rw [← h] at hmem
      have hres := (testBit_iff_mem_edges' hab hbc).mpr hmem
      rw [hres] at hm1
      cases hm1
    | false => rfl

end FlagAlgebras.Core
