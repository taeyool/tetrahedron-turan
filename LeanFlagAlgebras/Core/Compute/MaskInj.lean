import LeanFlagAlgebras.Core.Compute.Mask3

/-! # Decoding masks is injective

Distinct masks below the triple-count bound decode to distinct graphs:
each bit position is the rank of a sorted triple, and that triple's
membership as a hyperedge reads the bit back. Stated at the vertex
counts the certificate uses.

Kept in a thin file on top of `Mask3` alone: the identical proofs
exhaust the heartbeat budget inside the heavy example chains. -/

namespace FlagAlgebras.Core

variable {n : ℕ}

/-- Numbers below a power of two agree when their low bits do. -/
lemma eq_of_lt_two_pow {k x y : ℕ} (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (h : ∀ i < k, x.testBit i = y.testBit i) : x = y := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < k
  · exact h i hi
  · have hpow : (2 : ℕ) ^ k ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy hpow)]

/-- A sorted triple's bit is set exactly when its vertex set is a
hyperedge of the decoding. -/
lemma testBit_iff_mem_edges' {m : ℕ} {a b c : Fin n} (hab : a < b)
    (hbc : b < c) :
    m.testBit (triIdx n a.val b.val c.val) = true
      ↔ ({a, b, c} : Finset (Fin n)) ∈ (graphOfMask n m).edges := by
  constructor
  · intro hm
    exact mem_graphOfMask_edges.mpr ⟨a, b, c, hab, hbc, hm, rfl⟩
  · intro hm
    obtain ⟨x, y, z, hxy, hyz, hbit, heq⟩ := mem_graphOfMask_edges.mp hm
    obtain ⟨e1, e2, e3⟩ := sorted_triple_eq hab hbc hxy hyz heq
    rw [e1, e2, e3]
    exact hbit

/-- Bit positions below ten are ranks of sorted five-vertex triples. -/
private lemma triCover5 : ∀ k < 10, ∃ a b c : Fin 5, a < b ∧ b < c
    ∧ triIdx 5 a.val b.val c.val = k := by decide

/-- Bit positions below four are ranks of sorted four-vertex triples. -/
private lemma triCover4 : ∀ k < 4, ∃ a b c : Fin 4, a < b ∧ b < c
    ∧ triIdx 4 a.val b.val c.val = k := by decide

/-- Decoding five-vertex masks is injective below `2^10`. -/
lemma graphOfMask5_inj {m₁ m₂ : ℕ} (h₁ : m₁ < 2 ^ 10) (h₂ : m₂ < 2 ^ 10)
    (h : graphOfMask 5 m₁ = graphOfMask 5 m₂) : m₁ = m₂ := by
  refine eq_of_lt_two_pow h₁ h₂ fun k hk => ?_
  obtain ⟨a, b, c, hab, hbc, hidx⟩ := triCover5 k hk
  rw [← hidx]
  cases hm1 : m₁.testBit (triIdx 5 a.val b.val c.val) with
  | true =>
    have hmem := (testBit_iff_mem_edges' hab hbc).mp hm1
    rw [h] at hmem
    exact ((testBit_iff_mem_edges' hab hbc).mpr hmem).symm
  | false =>
    cases hm2 : m₂.testBit (triIdx 5 a.val b.val c.val) with
    | true =>
      have hmem := (testBit_iff_mem_edges' hab hbc).mp hm2
      rw [← h] at hmem
      have hres := (testBit_iff_mem_edges' hab hbc).mpr hmem
      rw [hres] at hm1
      cases hm1
    | false => rfl

/-- Decoding four-vertex masks is injective below `2^4`. -/
lemma graphOfMask4_inj {m₁ m₂ : ℕ} (h₁ : m₁ < 2 ^ 4) (h₂ : m₂ < 2 ^ 4)
    (h : graphOfMask 4 m₁ = graphOfMask 4 m₂) : m₁ = m₂ := by
  refine eq_of_lt_two_pow h₁ h₂ fun k hk => ?_
  obtain ⟨a, b, c, hab, hbc, hidx⟩ := triCover4 k hk
  rw [← hidx]
  cases hm1 : m₁.testBit (triIdx 4 a.val b.val c.val) with
  | true =>
    have hmem := (testBit_iff_mem_edges' hab hbc).mp hm1
    rw [h] at hmem
    exact ((testBit_iff_mem_edges' hab hbc).mpr hmem).symm
  | false =>
    cases hm2 : m₂.testBit (triIdx 4 a.val b.val c.val) with
    | true =>
      have hmem := (testBit_iff_mem_edges' hab hbc).mp hm2
      rw [← h] at hmem
      have hres := (testBit_iff_mem_edges' hab hbc).mpr hmem
      rw [hres] at hm1
      cases hm1
    | false => rfl

end FlagAlgebras.Core
