import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootOrderedColumn
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootFlags
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootTableFacts

/-! Integer Gram entries and canonical cache semantics for the five-root
column evaluator. These proofs connect the optimized arrays to exact sums of
the original factor rows; no projection of factor vectors is used. -/

namespace FlagAlgebras.Core.Tetrahedron.FullSevenLong

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private lemma sum_array_map (xs : Array ℕ) (f : ℕ → ℤ) :
    (xs.toList.map f).sum = ∑ a : Fin xs.size, f (xs.getD a.val 0) := by
  rw [← List.ofFn_getElem_eq_map, List.ofFn_eq_map,
    ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Array.getElem_toList, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem a.isLt, Option.getD_some]

private lemma sum_filter_zero (xs : List ℕ) (p : ℕ → Prop) [DecidablePred p]
    (f : ℕ → ℤ) (hz : ∀ a, ¬p a → f a = 0) :
    (xs.map f).sum = ((xs.filter fun a => decide (p a)).map f).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    by_cases ha : p a
    · simp only [List.map_cons, List.sum_cons, List.filter_cons, ha,
        decide_true, ite_true, ih]
    · simp only [List.map_cons, List.sum_cons, List.filter_cons, ha,
        decide_false, Bool.false_eq_true, ite_false, hz a ha, zero_add, ih]

lemma s5SumPerms_eq_matching (b : Fin 18) (root left right : ℕ) :
    (∑ p : Fin 120, s5LinkCell b (s5PermuteRoot p.val root)
      (s5PermuteLink p.val left) (s5PermuteLink p.val right)) =
    ((s5MatchingPerms root b).map fun p =>
      s5LinkCell b (s5PermuteRoot p root)
        (s5PermuteLink p left) (s5PermuteLink p right)).sum := by
  rw [Fin.sum_univ_eq_sum_range
      (fun p => s5LinkCell b (s5PermuteRoot p root)
        (s5PermuteLink p left) (s5PermuteLink p right)) 120,
    ← List.toFinset_range 120,
    List.sum_toFinset _ List.nodup_range]
  exact sum_filter_zero _ _ _ (fun p hp => by simp only [s5LinkCell, if_neg hp])

private lemma foldl_range_sum (g : ℕ → ℤ) (n : ℕ) :
    (List.range n).foldl (fun acc r => acc + g r) 0 =
      ∑ r : Fin n, g r.val := by
  rw [Fin.sum_univ_eq_sum_range]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, Finset.sum_range_succ, ih]

lemma s5RawGram_getD (d : FiveRootData) (i j : ℕ)
    (hi : i < d.dimension) (hj : j < d.dimension) :
    (s5RawGram d).getD (i * d.dimension + j) 0 =
      ∑ r : Fin d.rows,
        d.factors.getD (r.val * d.dimension + i) 0 *
          d.factors.getD (r.val * d.dimension + j) 0 := by
  have hd : 0 < d.dimension := lt_of_le_of_lt (Nat.zero_le i) hi
  have hflat : i * d.dimension + j < d.dimension * d.dimension := by
    nlinarith
  have hdiv : (i * d.dimension + j) / d.dimension = i := by
    rw [Nat.mul_comm i d.dimension, Nat.mul_add_div hd,
      Nat.div_eq_of_lt hj, Nat.add_zero]
  have hmod : (i * d.dimension + j) % d.dimension = j := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hj]
  simp only [s5RawGram, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
    dif_pos hflat, Option.getD_some, hdiv, hmod]
  exact foldl_range_sum _ _

lemma s5RawGram_block_getD (b : Fin 18) (i j : ℕ)
    (hi : i < s5Dim b) (hj : j < s5Dim b) :
    (s5RawGram (s5Block b)).getD (i * s5Dim b + j) 0 =
      s5FactorPair b i j := by
  exact s5RawGram_getD (s5Block b) i j hi hj

lemma s5CanonicalIndices_getD (root link : ℕ)
    (hr : root < 1024) (hl : link < 1024) (fallback : ℕ) :
    s5CanonicalIndices.getD (root * 1024 + link) fallback =
      s5CanonicalIndex root link := by
  have hflat : root * 1024 + link < 1024 * 1024 := by omega
  have hdiv : (root * 1024 + link) / 1024 = root := by omega
  have hmod : (root * 1024 + link) % 1024 = link := by omega
  simp only [s5CanonicalIndices, Array.getD_eq_getD_getElem?,
    Array.getElem?_ofFn, dif_pos hflat, Option.getD_some, hdiv, hmod]

lemma s5AveragedGram_getD (b : Fin 18) (i j : ℕ)
    (hi : i < s5Dim b) (hj : j < s5Dim b)
    (hact : ∀ a < (s5Block b).autos.size, ∀ k < s5Dim b,
      (s5Block b).action.getD (a * s5Dim b + k) (s5Dim b) < s5Dim b) :
    (s5AveragedGram (s5Block b)).getD (i * s5Dim b + j) 0 =
      ∑ a : Fin (s5Block b).autos.size,
        s5FactorPair b
          ((s5Block b).action.getD (a.val * s5Dim b + i) (s5Dim b))
          ((s5Block b).action.getD (a.val * s5Dim b + j) (s5Dim b)) := by
  have hd : 0 < s5Dim b := lt_of_le_of_lt (Nat.zero_le i) hi
  have hflat : i * s5Dim b + j < s5Dim b * s5Dim b := by nlinarith
  have hdiv : (i * s5Dim b + j) / s5Dim b = i := by
    rw [Nat.mul_comm i (s5Dim b), Nat.mul_add_div hd,
      Nat.div_eq_of_lt hj, Nat.add_zero]
  have hmod : (i * s5Dim b + j) % s5Dim b = j := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hj]
  have hdim : (s5Block b).dimension = s5Dim b := rfl
  simp only [s5AveragedGram, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
    hdim, dif_pos hflat, Option.getD_some, hdiv, hmod]
  rw [foldl_range_sum]
  apply Finset.sum_congr rfl
  intro a _
  simpa only [Array.getD_eq_getD_getElem?] using
    s5RawGram_block_getD b _ _ (hact a.val a.isLt i hi) (hact a.val a.isLt j hj)

lemma s5GramTables_getD (b : Fin 18) :
    s5GramTables.getD b.val #[] = s5AveragedGram (s5Block b) := by
  have hb : b.val < s5Data.size := b.isLt
  simp only [s5GramTables, s5Block, Array.getD_eq_getD_getElem?,
    Array.getElem?_map, Array.getElem?_eq_getElem hb, Option.map_some, Option.getD_some]

lemma s5AveragedGram_eq_sum_linkCell (b : Fin 18) (left right : ℕ)
    (hl : left < 1024) (hr : right < 1024) :
    (if (s5Block b).linkIndex.getD left (s5Dim b) < s5Dim b ∧
        (s5Block b).linkIndex.getD right (s5Dim b) < s5Dim b then
      2 * (s5AveragedGram (s5Block b)).getD
        ((s5Block b).linkIndex.getD left (s5Dim b) * s5Dim b +
          (s5Block b).linkIndex.getD right (s5Dim b)) 0
     else 0) =
      ∑ a : Fin (s5Block b).autos.size,
        s5LinkCell b (s5Block b).sigma
          (s5PermuteLink ((s5Block b).autos.getD a.val 0) left)
          (s5PermuteLink ((s5Block b).autos.getD a.val 0) right) := by
  by_cases hvalid : (s5Block b).linkIndex.getD left (s5Dim b) < s5Dim b ∧
      (s5Block b).linkIndex.getD right (s5Dim b) < s5Dim b
  · rw [if_pos hvalid, s5AveragedGram_getD b _ _ hvalid.1 hvalid.2
        (fun a ha => (s5Auto_bounds b a ha).2), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    have hl' := s5Auto_link_spec b a.val a.isLt left hl hvalid.1
    have hr' := s5Auto_link_spec b a.val a.isLt right hr hvalid.2
    have hil := (s5Auto_bounds b a.val a.isLt).2 _ hvalid.1
    have hir := (s5Auto_bounds b a.val a.isLt).2 _ hvalid.2
    simp only [s5LinkCell, hl', hr', hil, hir, and_self, ite_true]
  · rw [if_neg hvalid]
    symm
    apply Finset.sum_eq_zero
    intro a _
    have hl' := s5Auto_link_valid_iff b a.val a.isLt left hl
    have hr' := s5Auto_link_valid_iff b a.val a.isLt right hr
    simp only [s5LinkCell, hl', hr', if_neg hvalid, ite_true]

lemma s5SumPerms_eq_canonical_auts (b : Fin 18) (root left right : ℕ)
    (hroot : root < 1024) :
    (∑ p : Fin 120, s5LinkCell b (s5PermuteRoot p.val root)
      (s5PermuteLink p.val left) (s5PermuteLink p.val right)) =
    if (s5RootInfo.getD root (18, 0)).1 = b.val then
      ∑ a : Fin (s5Block b).autos.size,
        s5LinkCell b
          (s5PermuteRoot
            (s5PermComposition.getD
              ((s5RootInfo.getD root (18, 0)).2 * 120 +
                (s5Block b).autos.getD a.val 0) 0) root)
          (s5PermuteLink
            (s5PermComposition.getD
              ((s5RootInfo.getD root (18, 0)).2 * 120 +
                (s5Block b).autos.getD a.val 0) 0) left)
          (s5PermuteLink
            (s5PermComposition.getD
              ((s5RootInfo.getD root (18, 0)).2 * 120 +
                (s5Block b).autos.getD a.val 0) 0) right)
    else 0 := by
  rw [s5SumPerms_eq_matching]
  rw [(s5RootInfo_perm_spec root hroot b).map
    (fun p => s5LinkCell b (s5PermuteRoot p root)
      (s5PermuteLink p left) (s5PermuteLink p right)) |>.sum_eq]
  split_ifs
  · rw [List.map_map]
    exact sum_array_map _ _
  · rfl

lemma s5SumPerms_eq_canonical_cell (b : Fin 18) (root left right : ℕ)
    (hroot : root < 1024) :
    (∑ p : Fin 120, s5LinkCell b (s5PermuteRoot p.val root)
      (s5PermuteLink p.val left) (s5PermuteLink p.val right)) =
    if (s5RootInfo.getD root (18, 0)).1 = b.val then
      let left' := s5PermuteLink (s5RootInfo.getD root (18, 0)).2 left
      let right' := s5PermuteLink (s5RootInfo.getD root (18, 0)).2 right
      let i := (s5Block b).linkIndex.getD left' (s5Dim b)
      let j := (s5Block b).linkIndex.getD right' (s5Dim b)
      if i < s5Dim b ∧ j < s5Dim b then
        2 * (s5AveragedGram (s5Block b)).getD (i * s5Dim b + j) 0
      else 0
    else 0 := by
  rw [s5SumPerms_eq_canonical_auts b root left right hroot]
  by_cases hb : (s5RootInfo.getD root (18, 0)).1 = b.val
  · simp only [if_pos hb]
    rw [s5AveragedGram_eq_sum_linkCell b
      (s5PermuteLink (s5RootInfo.getD root (18, 0)).2 left)
      (s5PermuteLink (s5RootInfo.getD root (18, 0)).2 right)
      (s5Gather_lt _ 10 _) (s5Gather_lt _ 10 _)]
    apply Finset.sum_congr rfl
    intro a _
    have hp := (s5RootInfo_spec root hroot).2.1
    have ha := (s5Auto_bounds b a.val a.isLt).1
    rw [← s5PermuteRoot_comp hp ha root,
      ← s5PermuteLink_comp hp ha left, ← s5PermuteLink_comp hp ha right,
      (s5RootInfo_spec root hroot).2.2 b hb,
      s5Auto_root_spec b a.val a.isLt]
  · simp only [if_neg hb]

lemma s5RootCell_eq_sum_perms (w : ℕ) (s : FiveRootSample) :
    s5RootCell w s =
      ∑ b : Fin 18, ∑ p : Fin 120,
        s5LinkCell b
          (s5PermuteRoot p.val (s5Gather s.rootGather 10 w))
          (s5PermuteLink p.val (s5Gather s.leftGather 10 w))
          (s5PermuteLink p.val (s5Gather s.rightGather 10 w)) := by
  let root := s5Gather s.rootGather 10 w
  let left := s5Gather s.leftGather 10 w
  let right := s5Gather s.rightGather 10 w
  have hrootdef : s5Gather s.rootGather 10 w = root := rfl
  have hleftdef : s5Gather s.leftGather 10 w = left := rfl
  have hrightdef : s5Gather s.rightGather 10 w = right := rfl
  have hroot : root < 1024 := s5Gather_lt _ 10 _
  have hleft : left < 1024 := s5Gather_lt _ 10 _
  have hright : right < 1024 := s5Gather_lt _ 10 _
  change s5RootCell w s = ∑ b : Fin 18, ∑ p : Fin 120,
    s5LinkCell b (s5PermuteRoot p.val root)
      (s5PermuteLink p.val left) (s5PermuteLink p.val right)
  simp_rw [s5SumPerms_eq_canonical_cell _ root left right hroot]
  by_cases hb : (s5RootInfo.getD root (18, 0)).1 < 18
  · let b : Fin 18 := ⟨(s5RootInfo.getD root (18, 0)).1, hb⟩
    rw [Finset.sum_eq_single b]
    · have heq : (s5RootInfo.getD root (18, 0)).1 = b.val := rfl
      have hdim : (s5Data.getD b.val default).dimension = s5Dim b := rfl
      simp only [s5RootCell, hrootdef, hleftdef, hrightdef,
        ite_true, hdim, s5CanonicalIndices_getD root left hroot hleft,
        s5CanonicalIndices_getD root right hroot hright,
        s5CanonicalIndex, heq, s5GramTables_getD b]
      rw [if_pos b.isLt]
      rfl
    · intro c _ hcb
      have hc : (s5RootInfo.getD root (18, 0)).1 ≠ c.val := by
        intro hc
        apply hcb
        apply Fin.ext
        exact hc.symm
      simp only [if_neg hc]
    · simp
  · have hzero : ∀ b : Fin 18, (s5RootInfo.getD root (18, 0)).1 ≠ b.val := by
      intro b heq
      exact hb (heq ▸ b.isLt)
    simp only [hzero, ite_false, Finset.sum_const_zero]
    simp only [s5RootCell, hrootdef, if_neg hb]

end FlagAlgebras.Core.Tetrahedron.FullSevenLong
