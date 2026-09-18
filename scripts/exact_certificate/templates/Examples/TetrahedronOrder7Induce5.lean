import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7BlockFlags
import Mathlib.Tactic.FinCases

/-! # The block tables' induced mask is the pullback

The certificate's block folds read five-vertex induced flags off a
six-vertex mask through `inducedFrom`: a packed vertex list, `sort3` on
each triple, one bit per position. This file proves that computation is
the semantic induced subgraph — decoding the induced mask gives exactly
the pullback of the decoded host along the vertex tuple.

The proof is the same shape as the deck identity: `testBit_foldl_or`
describes the fold, two `decide`s pin the triple table, and
`Sym3Graph.ext` with the sorted-triple bookkeeping does the rest. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

/-- Pack five vertices, three bits each. -/
def pack5 (f : Fin 5 → Fin 6) : ℕ :=
  f 0 + 8 * f 1 + 64 * f 2 + 512 * f 3 + 4096 * f 4

/-- Reading a slot of a packed five-tuple. -/
lemma vertAt_pack5 (f : Fin 5 → Fin 6) (i : Fin 5) :
    vertAt (pack5 f) i.val = f i := by
  have h0 := (f 0).isLt
  have h1 := (f 1).isLt
  have h2 := (f 2).isLt
  have h3 := (f 3).isLt
  have h4 := (f 4).isLt
  have hmask : ∀ m : ℕ, m &&& 7 = m % 8 := fun m => by
    rw [show (7 : ℕ) = 2 ^ 3 - 1 from by norm_num,
      Nat.and_two_pow_sub_one_eq_mod]
  fin_cases i
  · show vertAt (pack5 f) 0 = ((f 0 : Fin 6) : ℕ)
    simp only [vertAt, hmask, Nat.shiftRight_eq_div_pow, pack5]
    norm_num
    all_goals omega
  · show vertAt (pack5 f) 1 = ((f 1 : Fin 6) : ℕ)
    simp only [vertAt, hmask, Nat.shiftRight_eq_div_pow, pack5]
    norm_num
    all_goals omega
  · show vertAt (pack5 f) 2 = ((f 2 : Fin 6) : ℕ)
    simp only [vertAt, hmask, Nat.shiftRight_eq_div_pow, pack5]
    norm_num
    all_goals omega
  · show vertAt (pack5 f) 3 = ((f 3 : Fin 6) : ℕ)
    simp only [vertAt, hmask, Nat.shiftRight_eq_div_pow, pack5]
    norm_num
    all_goals omega
  · show vertAt (pack5 f) 4 = ((f 4 : Fin 6) : ℕ)
    simp only [vertAt, hmask, Nat.shiftRight_eq_div_pow, pack5]
    norm_num
    all_goals omega

/-! ## The fold description -/

/-- The fold of `inducedFrom`, without its `let`. -/
private lemma inducedFrom_eq (tbl : List (ℕ × ℕ × ℕ × ℕ)) (m vs : ℕ) :
    inducedFrom tbl m vs
      = tbl.foldl (fun acc t =>
          if m.testBit (triIdx 6
              (sort3 (vertAt vs t.1) (vertAt vs t.2.1)
                (vertAt vs t.2.2.1)).1
              (sort3 (vertAt vs t.1) (vertAt vs t.2.1)
                (vertAt vs t.2.2.1)).2.1
              (sort3 (vertAt vs t.1) (vertAt vs t.2.1)
                (vertAt vs t.2.2.1)).2.2)
          then acc ||| (1 <<< t.2.2.2) else acc) 0 := rfl

private lemma inducedFrom_testBit (tbl : List (ℕ × ℕ × ℕ × ℕ))
    (m vs k : ℕ) :
    (inducedFrom tbl m vs).testBit k
      = tbl.any fun t =>
          decide (m.testBit (triIdx 6
              (sort3 (vertAt vs t.1) (vertAt vs t.2.1)
                (vertAt vs t.2.2.1)).1
              (sort3 (vertAt vs t.1) (vertAt vs t.2.1)
                (vertAt vs t.2.2.1)).2.1
              (sort3 (vertAt vs t.1) (vertAt vs t.2.1)
                (vertAt vs t.2.2.1)).2.2) = true)
            && decide (t.2.2.2 = k) := by
  rw [inducedFrom_eq, testBit_foldl_or
    (fun t : ℕ × ℕ × ℕ × ℕ => m.testBit (triIdx 6
      (sort3 (vertAt vs t.1) (vertAt vs t.2.1) (vertAt vs t.2.2.1)).1
      (sort3 (vertAt vs t.1) (vertAt vs t.2.1) (vertAt vs t.2.2.1)).2.1
      (sort3 (vertAt vs t.1) (vertAt vs t.2.1)
        (vertAt vs t.2.2.1)).2.2) = true)
    (fun t => t.2.2.2)]
  rw [Nat.zero_testBit]
  simp

/-! ## The triple table -/

/-- Every sorted five-vertex triple is listed with its rank. -/
private lemma tri5_complete : ∀ a b c : Fin 5, a < b → b < c →
    (a.val, b.val, c.val, triIdx 5 a.val b.val c.val) ∈ tri5 := by
  decide

/-- A listed entry whose rank matches a sorted triple is that triple. -/
private lemma tri5_inj : ∀ t ∈ tri5, ∀ a b c : Fin 5, a < b → b < c →
    t.2.2.2 = triIdx 5 a.val b.val c.val →
    t.1 = a.val ∧ t.2.1 = b.val ∧ t.2.2.1 = c.val := by
  decide

/-! ## The pullback identity -/

/-- **The induced mask is the pullback**: decoding the certificate's
five-vertex induced mask of a six-vertex host along an injective tuple
gives the semantic induced subgraph. -/
theorem graphOfMask_inducedFrom (r : ℕ) (f : Fin 5 → Fin 6)
    (hf : Function.Injective f) :
    graphOfMask 5 (inducedFrom tri5 r (pack5 f))
      = (graphOfMask 6 r).pullback f := by
  have hbit : ∀ a b c : Fin 5, a < b → b < c →
      (inducedFrom tri5 r (pack5 f)).testBit (triIdx 5 a.val b.val c.val)
        = r.testBit (triIdx 6
            (sort3 (f a).val (f b).val (f c).val).1
            (sort3 (f a).val (f b).val (f c).val).2.1
            (sort3 (f a).val (f b).val (f c).val).2.2) := by
    intro a b c hab hbc
    rw [inducedFrom_testBit]
    cases hr : r.testBit (triIdx 6
        (sort3 (f a).val (f b).val (f c).val).1
        (sort3 (f a).val (f b).val (f c).val).2.1
        (sort3 (f a).val (f b).val (f c).val).2.2) with
    | true =>
      refine List.any_eq_true.mpr ⟨(a.val, b.val, c.val, _),
        tri5_complete a b c hab hbc, ?_⟩
      rw [Bool.and_eq_true, vertAt_pack5 f a, vertAt_pack5 f b,
        vertAt_pack5 f c]
      exact ⟨decide_eq_true hr, decide_eq_true rfl⟩
    | false =>
      refine Bool.eq_false_iff.mpr fun hany => ?_
      obtain ⟨t, htmem, hcond⟩ := List.any_eq_true.mp hany
      rw [Bool.and_eq_true] at hcond
      obtain ⟨e1, e2, e3⟩ := tri5_inj t htmem a b c hab hbc
        (of_decide_eq_true hcond.2)
      have hc := of_decide_eq_true hcond.1
      rw [e1, e2, e3, vertAt_pack5 f a, vertAt_pack5 f b,
        vertAt_pack5 f c] at hc
      rw [hc] at hr
      cases hr
  have hvals : ∀ {a b : Fin 5}, a ≠ b → (f a).val ≠ (f b).val :=
    fun hne h => hne (hf (Fin.val_injective h))
  refine Sym3Graph.ext ?_
  ext e
  rw [mem_graphOfMask_edges]
  show _ ↔ e ∈ Finset.univ.filter _
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨a, b, c, hab, hbc, hbit', rfl⟩
    refine ⟨Finset.mem_univ _, card_triple_sorted hab hbc, ?_⟩
    rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton]
    rw [hbit a b c hab hbc] at hbit'
    obtain ⟨hs12, hs23⟩ := sort3_sorted (hvals hab.ne)
      (hvals (hab.trans hbc).ne) (hvals hbc.ne)
    have hset := sort3_finset (f a).val (f b).val (f c).val
    have hmem : ∀ x ∈ ({(sort3 (f a).val (f b).val (f c).val).1,
        (sort3 (f a).val (f b).val (f c).val).2.1,
        (sort3 (f a).val (f b).val (f c).val).2.2} : Finset ℕ), x < 6 := by
      intro x hx
      rw [hset] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (f a).isLt
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (f b).isLt
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact (f c).isLt
    have h1 := hmem _ (Finset.mem_insert_self _ _)
    have h2 := hmem _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have h3 := hmem _ (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    refine mem_graphOfMask_edges.mpr ⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩,
      Fin.lt_def.mpr hs12, Fin.lt_def.mpr hs23, hbit', ?_⟩
    refine Finset.image_injective (f := Fin.val) Fin.val_injective ?_
    rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton,
      Finset.image_insert, Finset.image_insert, Finset.image_singleton]
    exact hset.symm
  · rintro ⟨-, hcard, himg⟩
    obtain ⟨a, b, c, hab, hbc, rfl⟩ := exists_sorted_triple hcard
    refine ⟨a, b, c, hab, hbc, ?_, rfl⟩
    rw [Finset.image_insert, Finset.image_insert,
      Finset.image_singleton] at himg
    obtain ⟨x, y, z, hxy, hyz, hbit', heq⟩ := mem_graphOfMask_edges.mp himg
    rw [hbit a b c hab hbc]
    obtain ⟨hs12, hs23⟩ := sort3_sorted (hvals hab.ne)
      (hvals (hab.trans hbc).ne) (hvals hbc.ne)
    have hset : ({(sort3 (f a).val (f b).val (f c).val).1,
        (sort3 (f a).val (f b).val (f c).val).2.1,
        (sort3 (f a).val (f b).val (f c).val).2.2} : Finset ℕ)
        = {x.val, y.val, z.val} := by
      rw [sort3_finset]
      have := congrArg (Finset.image Fin.val) heq
      rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton,
        Finset.image_insert, Finset.image_insert,
        Finset.image_singleton] at this
      exact this
    obtain ⟨e1, e2, e3⟩ := sorted_triple_eq hs12 hs23
      (Fin.lt_def.mp hxy) (Fin.lt_def.mp hyz) hset
    rw [e1, e2, e3]
    exact hbit'

end FlagAlgebras.Core.Tetrahedron
