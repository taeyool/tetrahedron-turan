import LeanFlagAlgebras.Core.Compute.MaskInj
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7FoldSum
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Split
import Mathlib.Tactic.FinCases

/-! # The gather words compute pullback masks

`mkGather4` and `mkGather5` pack, six bits per slot, the seven-vertex
rank of each pattern triple's image under a vertex tuple. Reading a
seven-vertex mask through such a word therefore yields exactly the
induced mask of the pullback along that tuple — the level-7 analogue of
`graphOfMask_inducedFrom`.

The slot arithmetic is a finite fact about the packing, and rather than
reasoning about shifts by hand we decide it: for every vertex tuple over
`Fin 7` and every slot, the packed source is the rank of that slot's
triple image. Both tuple spaces are small enough (`7⁴` and `7⁵` with a
handful of slots each) that the check is a routine kernel evaluation. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

/-! ## The packed slot sources -/

/-- The rank a gather packs for a triple of host vertices. -/
def pos7 (a b c : ℕ) : ℕ :=
  triIdx 7 (sort3 a b c).1 (sort3 a b c).2.1 (sort3 a b c).2.2

/-- The source position the gather `g` reads at slot `k`. -/
def srcAt7 (g k : ℕ) : ℕ := (g >>> (6 * k)) &&& 63

set_option maxRecDepth 65536 in
/-- **The four-slot packing**: each slot of a `mkGather4` word holds the
rank of the corresponding `tri4` triple's image. -/
lemma srcAt7_mkGather4 : ∀ v0 v1 v2 v3 : Fin 7, ∀ t ∈ tri4,
    srcAt7 (mkGather4 v0.val v1.val v2.val v3.val) t.2.2.2
      = pos7 ([v0.val, v1.val, v2.val, v3.val].getD t.1 0)
          ([v0.val, v1.val, v2.val, v3.val].getD t.2.1 0)
          ([v0.val, v1.val, v2.val, v3.val].getD t.2.2.1 0) := by
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- **The ten-slot packing**, for `mkGather5` and `tri5`. -/
lemma srcAt7_mkGather5 : ∀ v0 v1 v2 v3 v4 : Fin 7, ∀ t ∈ tri5,
    srcAt7 (mkGather5 v0.val v1.val v2.val v3.val v4.val) t.2.2.2
      = pos7 ([v0.val, v1.val, v2.val, v3.val, v4.val].getD t.1 0)
          ([v0.val, v1.val, v2.val, v3.val, v4.val].getD t.2.1 0)
          ([v0.val, v1.val, v2.val, v3.val, v4.val].getD t.2.2.1 0) := by
  decide

/-! ## Reading a gather word

`gatherBits` sets bit `k` from the source packed at slot `k`, so a
gather word built by `mkGather4`/`mkGather5` reads a seven-vertex mask
into the induced mask of the pullback. The two lemmas below package the
bit description; the pullback identity follows by the same
sorted-triple argument as at level six. -/

private lemma gather_testBit4 (v0 v1 v2 v3 w : ℕ) {t : ℕ × ℕ × ℕ × ℕ}
    (ht : t.2.2.2 < 4) :
    (gatherBits (mkGather4 v0 v1 v2 v3) 4 w).testBit t.2.2.2
      = w.testBit (srcAt7 (mkGather4 v0 v1 v2 v3) t.2.2.2) := by
  rw [gatherBits_testBit, decide_eq_true ht]
  rfl

private lemma gather_testBit5 (v0 v1 v2 v3 v4 w : ℕ) {t : ℕ × ℕ × ℕ × ℕ}
    (ht : t.2.2.2 < 10) :
    (gatherBits (mkGather5 v0 v1 v2 v3 v4) 10 w).testBit t.2.2.2
      = w.testBit (srcAt7 (mkGather5 v0 v1 v2 v3 v4) t.2.2.2) := by
  rw [gatherBits_testBit, decide_eq_true ht]
  rfl

/-- Every sorted four-vertex triple is listed in `tri4` with its rank,
and every listed entry with a matching rank is that triple. -/
private lemma tri4_complete : ∀ a b c : Fin 4, a < b → b < c →
    (a.val, b.val, c.val, triIdx 4 a.val b.val c.val) ∈ tri4 := by
  decide

private lemma tri4_inj : ∀ t ∈ tri4, ∀ a b c : Fin 4, a < b → b < c →
    t.2.2.2 = triIdx 4 a.val b.val c.val →
    t.1 = a.val ∧ t.2.1 = b.val ∧ t.2.2.1 = c.val := by
  decide

private lemma tri4_slot_lt : ∀ t ∈ tri4, t.2.2.2 < 4 := by decide

private lemma tri5_complete' : ∀ a b c : Fin 5, a < b → b < c →
    (a.val, b.val, c.val, triIdx 5 a.val b.val c.val) ∈ tri5 := by
  decide

private lemma tri5_inj' : ∀ t ∈ tri5, ∀ a b c : Fin 5, a < b → b < c →
    t.2.2.2 = triIdx 5 a.val b.val c.val →
    t.1 = a.val ∧ t.2.1 = b.val ∧ t.2.2.1 = c.val := by
  decide

private lemma tri5_slot_lt : ∀ t ∈ tri5, t.2.2.2 < 10 := by decide

/-! ## The pullback identities -/

/-- **The four-slot gather is the pullback**: reading a seven-vertex
mask through a `mkGather4` word decodes to the induced subgraph along
the tuple. -/
theorem graphOfMask_gather4 (w : ℕ) (f : Fin 4 → Fin 7)
    (hf : Function.Injective f) :
    graphOfMask 4 (gatherBits
        (mkGather4 (f 0).val (f 1).val (f 2).val (f 3).val) 4 w)
      = (graphOfMask 7 w).pullback f := by
  have hlist : ∀ i : Fin 4,
      [(f 0).val, (f 1).val, (f 2).val, (f 3).val].getD i.val 0
        = (f i).val := by
    intro i; fin_cases i <;> rfl
  have hbit : ∀ a b c : Fin 4, a < b → b < c →
      (gatherBits (mkGather4 (f 0).val (f 1).val (f 2).val (f 3).val) 4
          w).testBit (triIdx 4 a.val b.val c.val)
        = w.testBit (triIdx 7
            (sort3 (f a).val (f b).val (f c).val).1
            (sort3 (f a).val (f b).val (f c).val).2.1
            (sort3 (f a).val (f b).val (f c).val).2.2) := by
    intro a b c hab hbc
    have hmem := tri4_complete a b c hab hbc
    have hslot := tri4_slot_lt _ hmem
    have hsrc := srcAt7_mkGather4 (f 0) (f 1) (f 2) (f 3) _ hmem
    rw [gather_testBit4 (t := (a.val, b.val, c.val,
      triIdx 4 a.val b.val c.val)) _ _ _ _ w hslot, hsrc]
    simp only [hlist]
    rfl
  refine Sym3Graph.ext ?_
  ext e
  rw [mem_graphOfMask_edges]
  show _ ↔ e ∈ Finset.univ.filter _
  rw [Finset.mem_filter]
  have hvals : ∀ {a b : Fin 4}, a ≠ b → (f a).val ≠ (f b).val :=
    fun hne h => hne (hf (Fin.val_injective h))
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
        (sort3 (f a).val (f b).val (f c).val).2.2} : Finset ℕ), x < 7 := by
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
      have himg2 := congrArg (Finset.image Fin.val) heq
      rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton,
        Finset.image_insert, Finset.image_insert,
        Finset.image_singleton] at himg2
      exact himg2
    obtain ⟨e1, e2, e3⟩ := sorted_triple_eq hs12 hs23
      (Fin.lt_def.mp hxy) (Fin.lt_def.mp hyz) hset
    rw [e1, e2, e3]
    exact hbit'

/-- **The ten-slot gather is the pullback**, for five-vertex tuples. -/
theorem graphOfMask_gather5 (w : ℕ) (f : Fin 5 → Fin 7)
    (hf : Function.Injective f) :
    graphOfMask 5 (gatherBits
        (mkGather5 (f 0).val (f 1).val (f 2).val (f 3).val (f 4).val)
        10 w)
      = (graphOfMask 7 w).pullback f := by
  have hlist : ∀ i : Fin 5,
      [(f 0).val, (f 1).val, (f 2).val, (f 3).val, (f 4).val].getD i.val 0
        = (f i).val := by
    intro i; fin_cases i <;> rfl
  have hbit : ∀ a b c : Fin 5, a < b → b < c →
      (gatherBits (mkGather5 (f 0).val (f 1).val (f 2).val (f 3).val
            (f 4).val) 10 w).testBit (triIdx 5 a.val b.val c.val)
        = w.testBit (triIdx 7
            (sort3 (f a).val (f b).val (f c).val).1
            (sort3 (f a).val (f b).val (f c).val).2.1
            (sort3 (f a).val (f b).val (f c).val).2.2) := by
    intro a b c hab hbc
    have hmem := tri5_complete' a b c hab hbc
    have hslot := tri5_slot_lt _ hmem
    have hsrc := srcAt7_mkGather5 (f 0) (f 1) (f 2) (f 3) (f 4) _ hmem
    rw [gather_testBit5 (t := (a.val, b.val, c.val,
      triIdx 5 a.val b.val c.val)) _ _ _ _ _ w hslot, hsrc]
    simp only [hlist]
    rfl
  refine Sym3Graph.ext ?_
  ext e
  rw [mem_graphOfMask_edges]
  show _ ↔ e ∈ Finset.univ.filter _
  rw [Finset.mem_filter]
  have hvals : ∀ {a b : Fin 5}, a ≠ b → (f a).val ≠ (f b).val :=
    fun hne h => hne (hf (Fin.val_injective h))
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
        (sort3 (f a).val (f b).val (f c).val).2.2} : Finset ℕ), x < 7 := by
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
      have himg2 := congrArg (Finset.image Fin.val) heq
      rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton,
        Finset.image_insert, Finset.image_insert,
        Finset.image_singleton] at himg2
      exact himg2
    obtain ⟨e1, e2, e3⟩ := sorted_triple_eq hs12 hs23
      (Fin.lt_def.mp hxy) (Fin.lt_def.mp hyz) hset
    rw [e1, e2, e3]
    exact hbit'

end FlagAlgebras.Core.Tetrahedron
