import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootSamples

namespace FlagAlgebras.Core.Tetrahedron.FullSevenLong

open scoped BigOperators

deriving instance DecidableEq for FiveRootSample

private lemma s5Samples_toList : s5Samples.toList =
    (List.range 21).map (fun i => s5Samples.getD i default) := by decide

private lemma foldl_range_sum (g : ℕ → ℤ) (n : ℕ) :
    (List.range n).foldl (fun acc r => acc + g r) 0 =
      ∑ r : Fin n, g r.val := by
  rw [Fin.sum_univ_eq_sum_range]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, Finset.sum_range_succ, ih]

lemma s5ColumnNum_eq_sum_samples (w : ℕ) :
    s5ColumnNum w = ∑ s : Fin 21, s5RootCell w (s5Samples.getD s.val default) := by
  rw [s5ColumnNum, ← Array.foldl_toList, s5Samples_toList, List.foldl_map]
  exact foldl_range_sum _ _

def s5SampleIndexEquiv : (Fin 21 × Fin 120) ≃ Fin 2520 where
  toFun q := s5SampleIndex q.1 q.2
  invFun k := (⟨k.val / 120, by omega⟩, ⟨k.val % 120, by omega⟩)
  left_inv := by
    rintro ⟨s, p⟩
    apply Prod.ext <;> apply Fin.ext <;> dsimp [s5SampleIndex] <;> omega
  right_inv := by
    intro k
    apply Fin.ext
    dsimp [s5SampleIndex]
    omega

/-- Assemble the fast-to-ordered identity from its per-root-set counterpart. -/
theorem s5ColumnNum_eq_ordered_of_cell (w : ℕ)
    (hcell : ∀ s : Fin 21,
      s5RootCell w (s5Samples.getD s.val default) =
        ∑ b : Fin 18, ∑ p : Fin 120,
          s5LinkCell b
            (s5PermuteRoot p.val
              (s5Gather (s5Samples.getD s.val default).rootGather 10 w))
            (s5PermuteLink p.val
              (s5Gather (s5Samples.getD s.val default).leftGather 10 w))
            (s5PermuteLink p.val
              (s5Gather (s5Samples.getD s.val default).rightGather 10 w))) :
    s5ColumnNum w = s5OrderedColumnNum w := by
  rw [s5ColumnNum_eq_sum_samples]
  simp_rw [hcell]
  rw [Finset.sum_comm]
  unfold s5OrderedColumnNum
  apply Finset.sum_congr rfl
  intro b _
  let f : Fin 21 × Fin 120 → ℤ := fun q =>
    s5LinkCell b
      (s5PermuteRoot q.2.val (s5Gather (s5Samples.getD q.1.val default).rootGather 10 w))
      (s5PermuteLink q.2.val (s5Gather (s5Samples.getD q.1.val default).leftGather 10 w))
      (s5PermuteLink q.2.val (s5Gather (s5Samples.getD q.1.val default).rightGather 10 w))
  change (∑ s : Fin 21, ∑ p : Fin 120, f (s, p)) = _
  rw [← Fintype.sum_prod_type f]
  apply Fintype.sum_equiv s5SampleIndexEquiv
  intro q
  change _ = s5LinkCell b
    (s5Gather (s5OrderedSample (s5SampleIndex q.1 q.2)).rootGather 10 w)
    (s5LinkMask6 (s5Gather (s5OrderedSample (s5SampleIndex q.1 q.2)).leftGather 20 w))
    (s5LinkMask6 (s5Gather (s5OrderedSample (s5SampleIndex q.1 q.2)).rightGather 20 w))
  rw [s5OrderedGather_root, s5OrderedGather_left, s5OrderedGather_right]

end FlagAlgebras.Core.Tetrahedron.FullSevenLong
