import LeanFlagAlgebras.Core.Compute.Mask3

/-! # The first six vertices inside the seven-vertex range

Small order-theoretic facts about the inclusion `Fin 6 ↪ Fin 7` and about
sorting a triple whose last entry dominates.

These live in their own thin file on purpose. Their proofs go through
`Finset (Fin 7)` and through `min`/`max`, and in the heavily loaded
context where they are used the instance search for those blows past the
elaboration budget; proved here, against `Mask3` alone, they take
seconds, and applying them later costs nothing. -/

namespace FlagAlgebras.Core

/-- The first six vertices, inside the seven-vertex range. -/
def embed6 (x : Fin 6) : Fin 7 := ⟨x.val, by omega⟩

lemma embed6_val (x : Fin 6) : (embed6 x).val = x.val := rfl

lemma embed6_lt_six (x : Fin 6) : (embed6 x).val < 6 := x.isLt

lemma embed6_lt {x y : Fin 6} (h : x < y) : embed6 x < embed6 y := h

lemma embed6_min (x y : Fin 6) :
    min (embed6 x) (embed6 y) = embed6 (min x y) := by
  simp only [min_def, Fin.le_def, embed6_val]
  split_ifs <;> rfl

lemma embed6_max (x y : Fin 6) :
    max (embed6 x) (embed6 y) = embed6 (max x y) := by
  simp only [max_def, Fin.le_def, embed6_val]
  split_ifs <;> rfl

/-- Sorting commutes with the inclusion. -/
lemma sort3_embed6 (x y z : Fin 6) :
    sort3 (embed6 x) (embed6 y) (embed6 z)
      = (embed6 (sort3 x y z).1, embed6 (sort3 x y z).2.1,
         embed6 (sort3 x y z).2.2) := by
  simp only [sort3, Fin.le_def, embed6_val]
  split_ifs <;> rfl

/-- When one entry dominates, sorting leaves it last. -/
lemma sort3_last {x y z : Fin 7} (hxy : x ≠ y) (hxz : x < z) (hyz : y < z) :
    sort3 x y z = (min x y, max x y, z) := by
  obtain ⟨hs1, hs2⟩ := sort3_sorted hxy hxz.ne hyz.ne
  have hmm : min x y < max x y := by
    rcases lt_or_gt_of_ne hxy with hh | hh
    · rwa [min_eq_left hh.le, max_eq_right hh.le]
    · rwa [min_eq_right hh.le, max_eq_left hh.le]
  have hmz : max x y < z := by
    rcases lt_or_gt_of_ne hxy with hh | hh
    · rwa [max_eq_right hh.le]
    · rwa [max_eq_left hh.le]
  have hset : ({(sort3 x y z).1, (sort3 x y z).2.1, (sort3 x y z).2.2}
      : Finset (Fin 7)) = {min x y, max x y, z} := by
    rw [sort3_finset]
    rcases lt_or_gt_of_ne hxy with hh | hh
    · rw [min_eq_left hh.le, max_eq_right hh.le]
    · rw [min_eq_right hh.le, max_eq_left hh.le, Finset.insert_comm]
  obtain ⟨e1, e2, e3⟩ := sorted_triple_eq hs1 hs2 hmm hmz hset
  have hsplit : sort3 x y z
      = ((sort3 x y z).1, (sort3 x y z).2.1, (sort3 x y z).2.2) := rfl
  rw [hsplit, e1, e2, e3]

/-! ## Relabelling by a self-map of the first six vertices

The pieces the realization argument needs: a self-map of the first six
vertices extended by fixing the last, and the last vertex's link
transported along it. -/

/-- Extend a self-map of the first six vertices by fixing the last. -/
def extendFn (f : Fin 6 → Fin 6) (x : Fin 7) : Fin 7 :=
  if h : x.val < 6 then embed6 (f ⟨x.val, h⟩) else ⟨6, by omega⟩

lemma extendFn_val (f : Fin 6 → Fin 6) (x : Fin 7) :
    (extendFn f x).val = if h : x.val < 6 then (f ⟨x.val, h⟩).val else 6 := by
  unfold extendFn
  split_ifs <;> rfl

lemma extendFn_embed6 (f : Fin 6 → Fin 6) (x : Fin 6) :
    extendFn f (embed6 x) = embed6 (f x) := by
  unfold extendFn
  rw [dif_pos (embed6_lt_six x)]
  exact congrArg embed6 (congrArg f (Fin.ext rfl))

lemma extendFn_last (f : Fin 6 → Fin 6) {x : Fin 7} (hx : x.val = 6) :
    (extendFn f x).val = 6 := by
  rw [extendFn_val, dif_neg (by omega)]

lemma extendFn_injective {f : Fin 6 → Fin 6} (hf : Function.Injective f) :
    Function.Injective (extendFn f) := by
  intro x y hxy
  have hv := congrArg Fin.val hxy
  rw [extendFn_val, extendFn_val] at hv
  by_cases hx : x.val < 6 <;> by_cases hy : y.val < 6
  · rw [dif_pos hx, dif_pos hy] at hv
    have hfe : (⟨x.val, hx⟩ : Fin 6) = ⟨y.val, hy⟩ := hf (Fin.ext hv)
    have hval : (⟨x.val, hx⟩ : Fin 6).val = (⟨y.val, hy⟩ : Fin 6).val :=
      congrArg Fin.val hfe
    exact Fin.ext hval
  · rw [dif_pos hx, dif_neg hy] at hv
    exact absurd hv (by have := (f ⟨x.val, hx⟩).isLt; omega)
  · rw [dif_neg hx, dif_pos hy] at hv
    exact absurd hv (by have := (f ⟨y.val, hy⟩).isLt; omega)
  · exact Fin.ext (by omega)

/-! ## The link, pulled back -/

/-- The sorted image of a pair under `f`. -/
def imgPair (f : Fin 6 → Fin 6) (q : Fin 6 × Fin 6) : ℕ :=
  pairIdx 6 (min (f q.1) (f q.2)).val (max (f q.1) (f q.2)).val

/-- Transport the last vertex's link along `f`. -/
def pullLink (f : Fin 6 → Fin 6) (m : ℕ) : ℕ :=
  (finPairs 6).foldl (fun acc q =>
    if m.testBit (triIdx 7 q.1.val q.2.val 6) then acc ||| (1 <<< imgPair f q)
    else acc) 0

lemma pullLink_testBit (f : Fin 6 → Fin 6) (m k : ℕ) :
    (pullLink f m).testBit k
      = (finPairs 6).any fun q =>
          decide (m.testBit (triIdx 7 q.1.val q.2.val 6) = true)
            && decide (imgPair f q = k) := by
  unfold pullLink
  rw [testBit_foldl_or (fun q => m.testBit (triIdx 7 q.1.val q.2.val 6) = true)
    (fun q => imgPair f q) (finPairs 6) 0 k]
  simp [Nat.zero_testBit]

lemma mem_finPairs {n : ℕ} {a b : Fin n} : (a, b) ∈ finPairs n ↔ a < b := by
  constructor
  · intro hp
    obtain ⟨a', -, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨b', -, hp⟩ := List.mem_filterMap.mp hp
    by_cases h : a' < b'
    · rw [if_pos h] at hp
      have heq := Option.some.inj hp
      simp only [Prod.ext_iff] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact h
    · rw [if_neg h] at hp
      cases hp
  · intro hab
    refine List.mem_flatMap.mpr ⟨a, List.mem_finRange a, ?_⟩
    exact List.mem_filterMap.mpr ⟨b, List.mem_finRange b, by rw [if_pos hab]⟩

/-- Sorted pairs have distinct ranks. -/
lemma pairIdx6_inj : ∀ a b c d : Fin 6, a < b → c < d →
    pairIdx 6 a.val b.val = pairIdx 6 c.val d.val → a = c ∧ b = d := by decide

/-- The pulled-back link records exactly the pairs of the image. -/
lemma pullLink_testBit_img {f : Fin 6 → Fin 6} (hf : Function.Injective f)
    (m : ℕ) {a b : Fin 6} (hab : a < b) :
    (pullLink f m).testBit (imgPair f (a, b))
      = m.testBit (triIdx 7 a.val b.val 6) := by
  rw [pullLink_testBit]
  cases hm : m.testBit (triIdx 7 a.val b.val 6) with
  | true =>
    refine List.any_eq_true.mpr ⟨(a, b), mem_finPairs.mpr hab, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true hm, decide_eq_true rfl⟩
  | false =>
    refine Bool.eq_false_iff.mpr fun hany => ?_
    obtain ⟨q, hq, hcond⟩ := List.any_eq_true.mp hany
    rw [Bool.and_eq_true] at hcond
    have hqlt : q.1 < q.2 := mem_finPairs.mp hq
    have himg : imgPair f q = imgPair f (a, b) := of_decide_eq_true hcond.2
    -- the sorted images agree, so by injectivity the pairs agree
    have hsq : min (f q.1) (f q.2) < max (f q.1) (f q.2) := by
      rcases lt_or_gt_of_ne (fun e => hqlt.ne (hf e)) with h | h
      · rwa [min_eq_left h.le, max_eq_right h.le]
      · rwa [min_eq_right h.le, max_eq_left h.le]
    have hsa : min (f a) (f b) < max (f a) (f b) := by
      rcases lt_or_gt_of_ne (fun e => hab.ne (hf e)) with h | h
      · rwa [min_eq_left h.le, max_eq_right h.le]
      · rwa [min_eq_right h.le, max_eq_left h.le]
    obtain ⟨h1, h2⟩ := pairIdx6_inj _ _ _ _ hsq hsa himg
    -- the two images agree as unordered pairs
    have hcases : (f q.1 = f a ∧ f q.2 = f b) ∨ (f q.1 = f b ∧ f q.2 = f a) := by
      rcases le_total (f q.1) (f q.2) with hq | hq <;>
        rcases le_total (f a) (f b) with ha | ha
      · rw [min_eq_left hq, min_eq_left ha] at h1
        rw [max_eq_right hq, max_eq_right ha] at h2
        exact Or.inl ⟨h1, h2⟩
      · rw [min_eq_left hq, min_eq_right ha] at h1
        rw [max_eq_right hq, max_eq_left ha] at h2
        exact Or.inr ⟨h1, h2⟩
      · rw [min_eq_right hq, min_eq_left ha] at h1
        rw [max_eq_left hq, max_eq_right ha] at h2
        exact Or.inr ⟨h2, h1⟩
      · rw [min_eq_right hq, min_eq_right ha] at h1
        rw [max_eq_left hq, max_eq_left ha] at h2
        exact Or.inl ⟨h2, h1⟩
    have hq1 : q.1 = a ∧ q.2 = b := by
      rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact ⟨hf e1, hf e2⟩
      · exfalso
        rw [hf e1, hf e2] at hqlt
        exact absurd (hab.trans hqlt) (lt_irrefl a)
    rw [hq1.1, hq1.2] at hcond
    rw [of_decide_eq_true hcond.1] at hm
    cases hm

/-! ## The transported link stays in range -/

lemma pairIdx6_lt : ∀ a b : Fin 6, a < b → pairIdx 6 a.val b.val < 15 := by decide

lemma imgPair_lt {f : Fin 6 → Fin 6} (hf : Function.Injective f)
    {q : Fin 6 × Fin 6} (hq : q ∈ finPairs 6) : imgPair f q < 15 := by
  have hlt : q.1 < q.2 := mem_finPairs.mp hq
  have hne : f q.1 ≠ f q.2 := fun e => hlt.ne (hf e)
  rcases lt_or_gt_of_ne hne with h | h
  · rw [imgPair, min_eq_left h.le, max_eq_right h.le]
    exact pairIdx6_lt _ _ h
  · rw [imgPair, min_eq_right h.le, max_eq_left h.le]
    exact pairIdx6_lt _ _ h

/-- The fold stays below `2 ^ 15`. Proved by direct induction rather than
through the generic bound: matching the generic statement against this
fold body is an expensive higher-order unification. -/
private lemma pullLink_fold_lt (f : Fin 6 → Fin 6) (m : ℕ) :
    ∀ (l : List (Fin 6 × Fin 6)) (acc : ℕ), acc < 2 ^ 15 →
      (∀ q ∈ l, imgPair f q < 15) →
      (l.foldl (fun acc q =>
        if m.testBit (triIdx 7 q.1.val q.2.val 6) then acc ||| (1 <<< imgPair f q)
        else acc) acc) < 2 ^ 15
  | [], acc, hacc, _ => hacc
  | q :: qs, acc, hacc, hg => by
    refine pullLink_fold_lt f m qs _ ?_ fun r hr => hg r (List.mem_cons_of_mem q hr)
    show (if m.testBit (triIdx 7 q.1.val q.2.val 6) then acc ||| (1 <<< imgPair f q)
      else acc) < 2 ^ 15
    by_cases hb : m.testBit (triIdx 7 q.1.val q.2.val 6) = true
    · rw [if_pos hb]
      refine Nat.or_lt_two_pow hacc ?_
      rw [Nat.one_shiftLeft]
      exact Nat.pow_lt_pow_right (by omega) (hg q (by simp))
    · rw [if_neg hb]
      exact hacc

lemma pullLink_lt {f : Fin 6 → Fin 6} (hf : Function.Injective f) (m : ℕ) :
    pullLink f m < 2 ^ 15 :=
  pullLink_fold_lt f m (finPairs 6) 0 (Nat.two_pow_pos 15)
    fun q hq => imgPair_lt hf hq

/-! ## Where the relabelling sends a sorted triple

The two shapes the realization argument meets. Both are stated with the
six-vertex vertices as inputs: a `Fin 7` vertex below six is turned into
one by `obtain ⟨a', rfl⟩ : ∃ a', a = embed6 a'` at the call site — never
by rewriting with `a = embed6 ⟨a.val, _⟩`, whose right-hand side
mentions `a` and sends `rw` in circles. -/

/-- A triple avoiding the last vertex stays inside the first six, sorted
by the image. -/
theorem relabel_sort_lt {f : Fin 6 → Fin 6} (hf : Function.Injective f)
    {a b c : Fin 6} (hab : a < b) (hbc : b < c) :
    sort3 (extendFn f (embed6 a)) (extendFn f (embed6 b))
        (extendFn f (embed6 c))
      = (embed6 (sort3 (f a) (f b) (f c)).1,
         embed6 (sort3 (f a) (f b) (f c)).2.1,
         embed6 (sort3 (f a) (f b) (f c)).2.2)
    ∧ (sort3 (f a) (f b) (f c)).1 < (sort3 (f a) (f b) (f c)).2.1
    ∧ (sort3 (f a) (f b) (f c)).2.1 < (sort3 (f a) (f b) (f c)).2.2 := by
  have hd1 : f a ≠ f b := fun e => hab.ne (hf e)
  have hd2 : f a ≠ f c := fun e => (hab.trans hbc).ne (hf e)
  have hd3 : f b ≠ f c := fun e => hbc.ne (hf e)
  obtain ⟨hs1, hs2⟩ := sort3_sorted hd1 hd2 hd3
  refine ⟨?_, hs1, hs2⟩
  rw [extendFn_embed6, extendFn_embed6, extendFn_embed6, sort3_embed6]

/-- A triple through the last vertex keeps it last, the other two sorted
by the image. -/
theorem relabel_sort_last {f : Fin 6 → Fin 6} (hf : Function.Injective f)
    {a b : Fin 6} (hab : a < b) {c : Fin 7} (hc : c.val = 6) :
    sort3 (extendFn f (embed6 a)) (extendFn f (embed6 b)) (extendFn f c)
      = (embed6 (min (f a) (f b)), embed6 (max (f a) (f b)),
         ⟨6, by omega⟩)
    ∧ min (f a) (f b) < max (f a) (f b) := by
  have hne : f a ≠ f b := fun e => hab.ne (hf e)
  have hlt1 : embed6 (f a) < (⟨6, by omega⟩ : Fin 7) :=
    Fin.lt_def.mpr (by simpa [embed6] using (f a).isLt)
  have hlt2 : embed6 (f b) < (⟨6, by omega⟩ : Fin 7) :=
    Fin.lt_def.mpr (by simpa [embed6] using (f b).isLt)
  have hnee : embed6 (f a) ≠ embed6 (f b) := fun e => by
    have hval : (embed6 (f a)).val = (embed6 (f b)).val := congrArg Fin.val e
    exact hne (Fin.ext hval)
  have hminmax : min (f a) (f b) < max (f a) (f b) := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rwa [min_eq_left hlt.le, max_eq_right hlt.le]
    · rwa [min_eq_right hlt.le, max_eq_left hlt.le]
  refine ⟨?_, hminmax⟩
  rw [extendFn_embed6, extendFn_embed6,
    show extendFn f c = (⟨6, by omega⟩ : Fin 7) from Fin.ext (extendFn_last f hc),
    sort3_last hnee hlt1 hlt2, embed6_min, embed6_max]

end FlagAlgebras.Core
