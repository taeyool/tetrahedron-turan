import LeanFlagAlgebras.Core.Compute.Mask3

/-! Packed bit extraction used by the five-root evaluator. This module has no
certificate or flag-algebra dependency beyond the generic mask representation. -/

namespace FlagAlgebras.Core.Tetrahedron.FullSevenLong

def s5GatherAux (g m : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | i + 1, acc => s5GatherAux g m i
      (if m.testBit ((g >>> (6 * i)) &&& 63) then acc ||| (1 <<< i) else acc)

def s5Gather (g cnt m : ℕ) : ℕ := s5GatherAux g m cnt 0
def s5Source (g k : ℕ) : ℕ := (g >>> (6 * k)) &&& 63

private lemma one_shift_bit (i k : ℕ) :
    ((1 <<< i : ℕ)).testBit k = decide (i = k) := by
  rw [Nat.one_shiftLeft]
  rcases eq_or_ne i k with rfl | hne
  · rw [Nat.testBit_two_pow_self, decide_eq_true rfl]
  · rw [Nat.testBit_two_pow_of_ne hne, decide_eq_false hne]

lemma s5GatherAux_testBit (g m : ℕ) : ∀ i acc k,
    (s5GatherAux g m i acc).testBit k =
      (acc.testBit k || (decide (k < i) && m.testBit (s5Source g k))) := by
  intro i
  induction i with
  | zero => intro acc k; simp [s5GatherAux]
  | succ i ih =>
    intro acc k
    rw [s5GatherAux, ih]
    rcases lt_trichotomy k i with hlt | rfl | hgt
    · have h1 : decide (k < i) = true := decide_eq_true hlt
      have h2 : decide (k < i + 1) = true := decide_eq_true (by omega)
      have hne : ¬i = k := by omega
      rw [h1, h2]
      by_cases hb : m.testBit ((g >>> (6 * i)) &&& 63) = true
      · rw [if_pos hb, Nat.testBit_lor, one_shift_bit, decide_eq_false hne]
        simp
      · rw [if_neg hb]
    · have h1 : decide (k < k) = false := decide_eq_false (by omega)
      have h2 : decide (k < k + 1) = true := decide_eq_true (by omega)
      rw [h1, h2]
      by_cases hb : m.testBit ((g >>> (6 * k)) &&& 63) = true
      · rw [if_pos hb, Nat.testBit_lor, one_shift_bit, decide_eq_true rfl]
        simp [s5Source, hb]
      · rw [if_neg hb]
        simp [s5Source, Bool.eq_false_iff.mpr hb]
    · have h1 : decide (k < i) = false := decide_eq_false (by omega)
      have h2 : decide (k < i + 1) = false := decide_eq_false (by omega)
      have hne : ¬i = k := by omega
      rw [h1, h2]
      by_cases hb : m.testBit ((g >>> (6 * i)) &&& 63) = true
      · rw [if_pos hb, Nat.testBit_lor, one_shift_bit, decide_eq_false hne]
        simp
      · rw [if_neg hb]

lemma s5Gather_testBit (g cnt m k : ℕ) :
    (s5Gather g cnt m).testBit k =
      (decide (k < cnt) && m.testBit (s5Source g k)) := by
  rw [s5Gather, s5GatherAux_testBit]
  simp

lemma s5Gather_lt (g cnt m : ℕ) : s5Gather g cnt m < 2 ^ cnt := by
  have h : s5Gather g cnt m % 2 ^ cnt = s5Gather g cnt m := by
    apply Nat.eq_of_testBit_eq
    intro k
    simp [Nat.testBit_mod_two_pow, s5Gather_testBit, Bool.and_assoc]
  rw [← h]
  exact Nat.mod_lt _ (by positivity)

lemma s5Gather_eq_of_sources (g h cnt m : ℕ)
    (hs : ∀ k < cnt, s5Source g k = s5Source h k) :
    s5Gather g cnt m = s5Gather h cnt m := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [s5Gather_testBit, s5Gather_testBit]
  by_cases hk : k < cnt
  · rw [hs k hk]
  · simp [hk]

/-- Composition is certified on the small source-position words, for every
possible host mask simultaneously. -/
lemma s5Gather_comp (outer inner composed width innerWidth m : ℕ)
    (hb : ∀ k < width, s5Source outer k < innerWidth)
    (hs : ∀ k < width,
      s5Source composed k = s5Source inner (s5Source outer k)) :
    s5Gather outer width (s5Gather inner innerWidth m) =
      s5Gather composed width m := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [s5Gather_testBit]
  by_cases hk : k < width
  · rw [decide_eq_true hk, decide_eq_true (hb k hk), hs k hk]
    rfl
  · simp [hk]

end FlagAlgebras.Core.Tetrahedron.FullSevenLong
