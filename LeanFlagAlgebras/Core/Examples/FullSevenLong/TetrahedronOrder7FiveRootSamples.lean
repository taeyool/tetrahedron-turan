import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootPullback
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootOrderedColumn
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootTableFacts
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Ext56

namespace FlagAlgebras.Core.Tetrahedron.FullSevenLong

open FlagAlgebras.Core

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def s5OrderedVertex (k : Fin 2520) (i : Fin 7) : Fin 7 :=
  ⟨(((s5OrderedSample k).vertices >>> (3 * i.val)) &&& 7) % 7,
    Nat.mod_lt _ (by decide)⟩

def s5OrderedRoot (k : Fin 2520) (i : Fin 5) : Fin 7 :=
  s5OrderedVertex k ⟨i.val, by omega⟩
def s5OrderedLeft (k : Fin 2520) : Fin 7 := s5OrderedVertex k 5
def s5OrderedRight (k : Fin 2520) : Fin 7 := s5OrderedVertex k 6

def s5OrderedLeftTuple (k : Fin 2520) : Fin 6 → Fin 7 :=
  ![s5OrderedRoot k 0, s5OrderedRoot k 1, s5OrderedRoot k 2,
    s5OrderedRoot k 3, s5OrderedRoot k 4, s5OrderedLeft k]
def s5OrderedRightTuple (k : Fin 2520) : Fin 6 → Fin 7 :=
  ![s5OrderedRoot k 0, s5OrderedRoot k 1, s5OrderedRoot k 2,
    s5OrderedRoot k 3, s5OrderedRoot k 4, s5OrderedRight k]

lemma s5OrderedRoot_inj : ∀ k, Function.Injective (s5OrderedRoot k) := by native_decide
lemma s5OrderedLeftTuple_inj : ∀ k, Function.Injective (s5OrderedLeftTuple k) := by
  native_decide
lemma s5OrderedRightTuple_inj : ∀ k, Function.Injective (s5OrderedRightTuple k) := by
  native_decide

/-- The 2520 generated root tuples have no repetitions. -/
lemma s5OrderedRoot_index_injective : Function.Injective s5OrderedRoot := by native_decide

lemma s5OrderedLeft_outside : ∀ k,
    s5OrderedLeft k ∉ Finset.univ.image (s5OrderedRoot k) := by native_decide
lemma s5OrderedRight_outside : ∀ k,
    s5OrderedRight k ∉ Finset.univ.image (s5OrderedRoot k) := by native_decide
lemma s5OrderedOutside_ne : ∀ k, s5OrderedLeft k ≠ s5OrderedRight k := by native_decide

private lemma s5_rank5_lt : ∀ a b c : Fin 5, a < b → b < c →
    triIdx 5 a.val b.val c.val < 10 := by decide
private lemma s5_rank6_lt : ∀ a b c : Fin 6, a < b → b < c →
    triIdx 6 a.val b.val c.val < 20 := by decide

private lemma s5OrderedRoot_sources : ∀ k, ∀ a b c : Fin 5, a < b → b < c →
    s5Source (s5OrderedSample k).rootGather (triIdx 5 a.val b.val c.val) =
      triIdx 7 (sort3 (s5OrderedRoot k a).val (s5OrderedRoot k b).val
          (s5OrderedRoot k c).val).1
        (sort3 (s5OrderedRoot k a).val (s5OrderedRoot k b).val
          (s5OrderedRoot k c).val).2.1
        (sort3 (s5OrderedRoot k a).val (s5OrderedRoot k b).val
          (s5OrderedRoot k c).val).2.2 := by native_decide

private lemma s5OrderedLeft_sources : ∀ k, ∀ a b c : Fin 6, a < b → b < c →
    s5Source (s5OrderedSample k).leftGather (triIdx 6 a.val b.val c.val) =
      triIdx 7 (sort3 (s5OrderedLeftTuple k a).val (s5OrderedLeftTuple k b).val
          (s5OrderedLeftTuple k c).val).1
        (sort3 (s5OrderedLeftTuple k a).val (s5OrderedLeftTuple k b).val
          (s5OrderedLeftTuple k c).val).2.1
        (sort3 (s5OrderedLeftTuple k a).val (s5OrderedLeftTuple k b).val
          (s5OrderedLeftTuple k c).val).2.2 := by native_decide

private lemma s5OrderedRight_sources : ∀ k, ∀ a b c : Fin 6, a < b → b < c →
    s5Source (s5OrderedSample k).rightGather (triIdx 6 a.val b.val c.val) =
      triIdx 7 (sort3 (s5OrderedRightTuple k a).val (s5OrderedRightTuple k b).val
          (s5OrderedRightTuple k c).val).1
        (sort3 (s5OrderedRightTuple k a).val (s5OrderedRightTuple k b).val
          (s5OrderedRightTuple k c).val).2.1
        (sort3 (s5OrderedRightTuple k a).val (s5OrderedRightTuple k b).val
          (s5OrderedRightTuple k c).val).2.2 := by native_decide

lemma s5OrderedRoot_graph (k : Fin 2520) (w : ℕ) :
    graphOfMask 5 (s5Gather (s5OrderedSample k).rootGather 10 w) =
      (graphOfMask 7 w).pullback (s5OrderedRoot k) :=
  s5Graph_gather _ _ _ _ (s5OrderedRoot_inj k) s5_rank5_lt (s5OrderedRoot_sources k)

lemma s5OrderedLeft_graph (k : Fin 2520) (w : ℕ) :
    graphOfMask 6 (s5Gather (s5OrderedSample k).leftGather 20 w) =
      (extFlag6 (graphOfMask 7 w) (s5OrderedRoot k) (s5OrderedLeft k)).graph :=
  s5Graph_gather _ _ _ _ (s5OrderedLeftTuple_inj k) s5_rank6_lt (s5OrderedLeft_sources k)

lemma s5OrderedRight_graph (k : Fin 2520) (w : ℕ) :
    graphOfMask 6 (s5Gather (s5OrderedSample k).rightGather 20 w) =
      (extFlag6 (graphOfMask 7 w) (s5OrderedRoot k) (s5OrderedRight k)).graph :=
  s5Graph_gather _ _ _ _ (s5OrderedRightTuple_inj k) s5_rank6_lt (s5OrderedRight_sources k)

private lemma s5Extract6_bounds : ∀ i < 10,
    s5Source s5RootGather6 i < 20 ∧ s5Source s5LinkGather6 i < 20 := by decide

private lemma s5OrderedRoot6_sources : ∀ k, ∀ i < 10,
    s5Source (s5OrderedSample k).rootGather i =
      s5Source (s5OrderedSample k).leftGather (s5Source s5RootGather6 i) ∧
    s5Source (s5OrderedSample k).rootGather i =
      s5Source (s5OrderedSample k).rightGather (s5Source s5RootGather6 i) := by
  native_decide

lemma s5OrderedLeft_rootMask (k : Fin 2520) (w : ℕ) :
    s5RootMask6 (s5Gather (s5OrderedSample k).leftGather 20 w) =
      s5Gather (s5OrderedSample k).rootGather 10 w := by
  apply s5Gather_comp
  · exact fun i hi => (s5Extract6_bounds i hi).1
  · exact fun i hi => (s5OrderedRoot6_sources k i hi).1

lemma s5OrderedRight_rootMask (k : Fin 2520) (w : ℕ) :
    s5RootMask6 (s5Gather (s5OrderedSample k).rightGather 20 w) =
      s5Gather (s5OrderedSample k).rootGather 10 w := by
  apply s5Gather_comp
  · exact fun i hi => (s5Extract6_bounds i hi).1
  · exact fun i hi => (s5OrderedRoot6_sources k i hi).2

def s5SampleIndex (s : Fin 21) (p : Fin 120) : Fin 2520 :=
  ⟨s.val * 120 + p.val, by omega⟩

private lemma s5OrderedPerm_sources : ∀ (s : Fin 21) (p : Fin 120), ∀ i < 10,
    s5Source (s5OrderedSample (s5SampleIndex s p)).rootGather i =
      s5Source (s5Samples.getD s.val default).rootGather
        (s5Source (s5PermRootGathers.getD p.val 0) i) ∧
    s5Source (s5OrderedSample (s5SampleIndex s p)).leftGather (s5Source s5LinkGather6 i) =
      s5Source (s5Samples.getD s.val default).leftGather
        (s5Source (s5PermLinkGathers.getD p.val 0) i) ∧
    s5Source (s5OrderedSample (s5SampleIndex s p)).rightGather (s5Source s5LinkGather6 i) =
      s5Source (s5Samples.getD s.val default).rightGather
        (s5Source (s5PermLinkGathers.getD p.val 0) i) := by native_decide

lemma s5OrderedGather_root (s : Fin 21) (p : Fin 120) (w : ℕ) :
    s5Gather (s5OrderedSample (s5SampleIndex s p)).rootGather 10 w =
      s5PermuteRoot p.val (s5Gather (s5Samples.getD s.val default).rootGather 10 w) := by
  symm
  apply s5Gather_comp
  · exact fun i hi => (s5Perm_sources_lt p.val p.isLt i hi).1
  · exact fun i hi => (s5OrderedPerm_sources s p i hi).1

lemma s5OrderedGather_left (s : Fin 21) (p : Fin 120) (w : ℕ) :
    s5LinkMask6 (s5Gather (s5OrderedSample (s5SampleIndex s p)).leftGather 20 w) =
      s5PermuteLink p.val (s5Gather (s5Samples.getD s.val default).leftGather 10 w) := by
  apply s5Gather_comp_congr
  · exact fun i hi => (s5Extract6_bounds i hi).2
  · exact fun i hi => (s5Perm_sources_lt p.val p.isLt i hi).2
  · exact fun i hi => (s5OrderedPerm_sources s p i hi).2.1

lemma s5OrderedGather_right (s : Fin 21) (p : Fin 120) (w : ℕ) :
    s5LinkMask6 (s5Gather (s5OrderedSample (s5SampleIndex s p)).rightGather 20 w) =
      s5PermuteLink p.val (s5Gather (s5Samples.getD s.val default).rightGather 10 w) := by
  apply s5Gather_comp_congr
  · exact fun i hi => (s5Extract6_bounds i hi).2
  · exact fun i hi => (s5Perm_sources_lt p.val p.isLt i hi).2
  · exact fun i hi => (s5OrderedPerm_sources s p i hi).2.2

end FlagAlgebras.Core.Tetrahedron.FullSevenLong
