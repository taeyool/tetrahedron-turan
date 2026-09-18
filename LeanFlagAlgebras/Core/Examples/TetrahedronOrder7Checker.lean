import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Data
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Witness
import LeanFlagAlgebras.Core.Examples.TetrahedronMask

/-! # The six-vertex completeness checker

The per-mask verdict of the canonicalization sweep, engineered for the
kernel: a tetrahedron-free mask passes if its packed witness permutation
index is in range, the image mask reconstructed through the permutation's
precomputed *rank map* is a listed representative, and the per-triple bit
correspondence holds — twenty bit comparisons, no `Finset`, no `Fin`
arithmetic in the hot path.

The vertex-level meaning is recovered by a one-time check
(`permsConsistentAll`): for each of the 720 permutations, the packed
vertex map is injective and its rank map is pointwise the rank of the
sorted image triple. Combining the two, `leafOK_iso` turns a true leaf
verdict into an isomorphism with a listed representative through
`isIso_graphOfMask_of_bits`. The sweep itself is split into 32 subrange
lemmas (separate files, so they build in parallel) and assembled by
`sweepMasks_of_pieces`. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

/-- The quadruple-position table of the six-vertex range (the literal
form of `quadIdxList 6`). -/
def qs6 : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 1, 4, 10), (0, 2, 5, 11), (0, 3, 6, 12), (1, 2, 7, 13),
   (1, 3, 8, 14), (2, 3, 9, 15), (4, 5, 7, 16), (4, 6, 8, 17),
   (5, 6, 9, 18), (7, 8, 9, 19), (10, 11, 13, 16), (10, 12, 14, 17),
   (11, 12, 15, 18), (13, 14, 15, 19), (16, 17, 18, 19)]

lemma qs6_eq : qs6 = quadIdxList 6 := by decide

set_option maxRecDepth 8192 in
/-- Rank injectivity on the listed six-vertex triples. -/
lemma finTriples6_rank_inj : ∀ t₁ ∈ finTriples 6, ∀ t₂ ∈ finTriples 6,
    triIdx 6 t₁.1.val t₁.2.1.val t₁.2.2.val
      = triIdx 6 t₂.1.val t₂.2.1.val t₂.2.2.val → t₁ = t₂ := by decide

set_option maxRecDepth 8192 in
/-- Rank bound on the listed six-vertex triples. -/
lemma finTriples6_rank_lt :
    ∀ t ∈ finTriples 6, triIdx 6 t.1.val t.2.1.val t.2.2.val < 20 := by
  decide

/-- Entry `i` of a packed permutation (three bits per vertex). -/
def pv (w i : ℕ) : ℕ := (w >>> (3 * i)) &&& 7

/-- The packed permutation as a vertex map. -/
def permFn (w : ℕ) : Fin 6 → Fin 6 := fun i =>
  ⟨pv w i.val % 6, Nat.mod_lt _ (by norm_num)⟩

/-- The packed vertex map of the permutation with index `i`. -/
def getPerm (i : ℕ) : ℕ := (w6Perms.getD (i / 30) []).getD (i % 30) 0

/-- The packed rank map of the permutation with index `i`. -/
def getRank (i : ℕ) : ℕ := (w6RankMaps.getD (i / 30) []).getD (i % 30) 0

/-- The witness permutation index of a mask, from the packed chunks. -/
def pidxOf (m : ℕ) : ℕ :=
  (((w6Chunks.getD (m >>> 15) []).getD ((m >>> 10) &&& 31) 0)
    >>> (10 * (m &&& 1023))) &&& 1023

/-- Image-mask reconstruction through a rank map: transport each present
rank bit. -/
def rankApply (r m : ℕ) : ℕ :=
  (List.range 20).foldl (fun acc rk =>
    if m.testBit rk then acc ||| (1 <<< ((r >>> (5 * rk)) &&& 31))
    else acc) 0

/-- The per-triple bit correspondence along a rank map. -/
def scanOK (m r h : ℕ) : Bool :=
  (List.range 20).all fun rk =>
    m.testBit rk == h.testBit ((r >>> (5 * rk)) &&& 31)

/-- Per-mask verdict of the completeness sweep. -/
def leafOK (m : ℕ) : Bool :=
  cond (k4FreeMask qs6 m)
    (decide (pidxOf m < 720)
      && decide (rankApply (getRank (pidxOf m)) m ∈ h6Reps)
      && scanOK m (getRank (pidxOf m)) (rankApply (getRank (pidxOf m)) m))
    true

/-- Consistency of one packed permutation with its rank map: the vertex
map is injective, and each rank-map entry is the rank of the sorted
image triple. -/
def permConsistent (w r : ℕ) : Bool :=
  decide (Function.Injective (permFn w))
    && decide (∀ a b c : Fin 6, a < b → b < c →
        (r >>> (5 * triIdx 6 a.val b.val c.val)) &&& 31
          = triIdx 6 (sort3 (permFn w a) (permFn w b) (permFn w c)).1.val
              (sort3 (permFn w a) (permFn w b) (permFn w c)).2.1.val
              (sort3 (permFn w a) (permFn w b) (permFn w c)).2.2.val)

/-- One row (30 permutations) of the table validation. -/
def rowConsistent (r : ℕ) : Bool :=
  (List.range 30).all fun i =>
    permConsistent (getPerm (30 * r + i)) (getRank (30 * r + i))

set_option maxRecDepth 65536 in
lemma rowConsistent_0 : rowConsistent 0 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_1 : rowConsistent 1 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_2 : rowConsistent 2 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_3 : rowConsistent 3 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_4 : rowConsistent 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_5 : rowConsistent 5 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_6 : rowConsistent 6 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_7 : rowConsistent 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_8 : rowConsistent 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_9 : rowConsistent 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_10 : rowConsistent 10 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_11 : rowConsistent 11 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_12 : rowConsistent 12 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_13 : rowConsistent 13 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_14 : rowConsistent 14 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_15 : rowConsistent 15 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_16 : rowConsistent 16 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_17 : rowConsistent 17 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_18 : rowConsistent 18 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_19 : rowConsistent 19 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_20 : rowConsistent 20 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_21 : rowConsistent 21 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_22 : rowConsistent 22 = true := by decide +kernel
set_option maxRecDepth 65536 in
lemma rowConsistent_23 : rowConsistent 23 = true := by decide +kernel

/-- The one-time table validation, indexed: each of the 720 permutations
is consistent with its rank map. -/
lemma permConsistent_of_lt {i : ℕ} (hi : i < 720) :
    permConsistent (getPerm i) (getRank i) = true := by
  have hrow : rowConsistent (i / 30) = true := by
    have hr : i / 30 < 24 := by omega
    match hq : i / 30 with
    | 0 => exact rowConsistent_0
    | 1 => exact rowConsistent_1
    | 2 => exact rowConsistent_2
    | 3 => exact rowConsistent_3
    | 4 => exact rowConsistent_4
    | 5 => exact rowConsistent_5
    | 6 => exact rowConsistent_6
    | 7 => exact rowConsistent_7
    | 8 => exact rowConsistent_8
    | 9 => exact rowConsistent_9
    | 10 => exact rowConsistent_10
    | 11 => exact rowConsistent_11
    | 12 => exact rowConsistent_12
    | 13 => exact rowConsistent_13
    | 14 => exact rowConsistent_14
    | 15 => exact rowConsistent_15
    | 16 => exact rowConsistent_16
    | 17 => exact rowConsistent_17
    | 18 => exact rowConsistent_18
    | 19 => exact rowConsistent_19
    | 20 => exact rowConsistent_20
    | 21 => exact rowConsistent_21
    | 22 => exact rowConsistent_22
    | 23 => exact rowConsistent_23
    | n + 24 => exact absurd (hq ▸ hr) (by omega)
  have hmem := List.all_eq_true.mp hrow (i % 30)
    (List.mem_range.mpr (by omega))
  rwa [Nat.div_add_mod] at hmem

/-- The rank bound, in the quantifier shape the reflection consumes
(kernel-checked; deliberately avoids `finTriples`-membership, whose
unification blows up under metavariables). -/
lemma triIdx6_lt : ∀ a b c : Fin 6, a < b → b < c →
    triIdx 6 a.val b.val c.val < 20 := by decide

/-- Abstract reflection: consistency of a packed permutation with its
rank map plus the scan verdict give the isomorphism — stated over plain
variables so no table literal is ever unfolded during elaboration. -/
lemma leafParts_iso {m p r h : ℕ}
    (hcons : permConsistent p r = true)
    (hscan : scanOK m r h = true) :
    (graphOfMask 6 m).IsIso (graphOfMask 6 h) := by
  unfold permConsistent at hcons
  rw [Bool.and_eq_true] at hcons
  have hinj := of_decide_eq_true hcons.1
  have hcons' := of_decide_eq_true hcons.2
  unfold scanOK at hscan
  have hscan' := List.all_eq_true.mp hscan
  refine isIso_graphOfMask_of_bits hinj ?_
  intro a b c hab hbc
  have hs := hscan' _ (List.mem_range.mpr (triIdx6_lt a b c hab hbc))
  simp only [beq_iff_eq] at hs
  rw [hs, hcons' a b c hab hbc]

/-- Reflection of one leaf: a true verdict on a tetrahedron-free mask
yields a listed representative isomorphic to it. -/
lemma leafOK_iso {m : ℕ} (hk4 : k4FreeMask qs6 m = true)
    (hleaf : leafOK m = true) :
    rankApply (getRank (pidxOf m)) m ∈ h6Reps
      ∧ (graphOfMask 6 m).IsIso
          (graphOfMask 6 (rankApply (getRank (pidxOf m)) m)) := by
  unfold leafOK at hleaf
  rw [hk4] at hleaf
  have h3 : (decide (pidxOf m < 720)
      && decide (rankApply (getRank (pidxOf m)) m ∈ h6Reps)
      && scanOK m (getRank (pidxOf m)) (rankApply (getRank (pidxOf m)) m))
      = true := hleaf
  rw [Bool.and_eq_true, Bool.and_eq_true] at h3
  obtain ⟨⟨hpidx, hmem⟩, hscan⟩ := h3
  exact ⟨of_decide_eq_true hmem,
    leafParts_iso (permConsistent_of_lt (of_decide_eq_true hpidx)) hscan⟩

end FlagAlgebras.Core.Tetrahedron
