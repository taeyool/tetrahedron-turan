import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootFlags
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootOrderedData

namespace FlagAlgebras.Core.Tetrahedron.FullSevenLong

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

lemma s5Perm_sources_lt : ∀ p < 120, ∀ k < 10,
    s5Source (s5PermRootGathers.getD p 0) k < 10 ∧
      s5Source (s5PermLinkGathers.getD p 0) k < 10 := by native_decide

lemma s5Perm_composition_spec : ∀ p < 120, ∀ q < 120,
    s5PermComposition.getD (p * 120 + q) 0 < 120 ∧
    ∀ k < 10,
      s5Source (s5PermRootGathers.getD
        (s5PermComposition.getD (p * 120 + q) 0) 0) k =
          s5Source (s5PermRootGathers.getD p 0)
            (s5Source (s5PermRootGathers.getD q 0) k) ∧
      s5Source (s5PermLinkGathers.getD
        (s5PermComposition.getD (p * 120 + q) 0) 0) k =
          s5Source (s5PermLinkGathers.getD p 0)
            (s5Source (s5PermLinkGathers.getD q 0) k) := by native_decide

lemma s5PermuteRoot_comp {p q : ℕ} (hp : p < 120) (hq : q < 120) (m : ℕ) :
    s5PermuteRoot q (s5PermuteRoot p m) =
      s5PermuteRoot (s5PermComposition.getD (p * 120 + q) 0) m := by
  apply s5Gather_comp
  · exact fun k hk => (s5Perm_sources_lt q hq k hk).1
  · exact fun k hk => ((s5Perm_composition_spec p hp q hq).2 k hk).1

lemma s5PermuteLink_comp {p q : ℕ} (hp : p < 120) (hq : q < 120) (m : ℕ) :
    s5PermuteLink q (s5PermuteLink p m) =
      s5PermuteLink (s5PermComposition.getD (p * 120 + q) 0) m := by
  apply s5Gather_comp
  · exact fun k hk => (s5Perm_sources_lt q hq k hk).2
  · exact fun k hk => ((s5Perm_composition_spec p hp q hq).2 k hk).2

lemma s5RootInfo_spec : ∀ root < 1024,
    let bp := s5RootInfo.getD root (18, 0)
    bp.1 ≤ 18 ∧ bp.2 < 120 ∧
    ∀ b : Fin 18, bp.1 = b.val → s5PermuteRoot bp.2 root = (s5Block b).sigma := by
  native_decide

def s5MatchingPerms (root : ℕ) (b : Fin 18) : List ℕ :=
  (List.range 120).filter fun p => s5PermuteRoot p root = (s5Block b).sigma

/-- The canonical transport followed by every automorphism is exactly the
full list of root permutations producing the specified labeled type. -/
lemma s5RootInfo_perm_spec : ∀ root < 1024, ∀ b : Fin 18,
    let bp := s5RootInfo.getD root (18, 0)
    (s5MatchingPerms root b).Perm
      (if bp.1 = b.val then
        (s5Block b).autos.toList.map fun a =>
          s5PermComposition.getD (bp.2 * 120 + a) 0
      else []) := by native_decide

lemma s5Auto_bounds : ∀ (b : Fin 18) (a : ℕ), a < (s5Block b).autos.size →
    (s5Block b).autos.getD a 0 < 120 ∧
    ∀ i < s5Dim b,
      (s5Block b).action.getD (a * s5Dim b + i) (s5Dim b) < s5Dim b := by
  native_decide

lemma s5Auto_root_spec : ∀ (b : Fin 18) (a : ℕ), a < (s5Block b).autos.size →
    s5PermuteRoot ((s5Block b).autos.getD a 0) (s5Block b).sigma =
      (s5Block b).sigma := by native_decide

/-- Every automorphism acts on all labeled flags through the stated ten-bit
link permutation. This also certifies the action table's index orientation. -/
lemma s5Auto_link_spec : ∀ (b : Fin 18) (a : ℕ), a < (s5Block b).autos.size →
    ∀ link < 1024,
      let i := (s5Block b).linkIndex.getD link (s5Dim b)
      i < s5Dim b →
      (s5Block b).linkIndex.getD
          (s5PermuteLink ((s5Block b).autos.getD a 0) link) (s5Dim b) =
        (s5Block b).action.getD (a * s5Dim b + i) (s5Dim b) := by
  native_decide

lemma s5Auto_link_valid_iff : ∀ (b : Fin 18) (a : ℕ), a < (s5Block b).autos.size →
    ∀ link < 1024,
      ((s5Block b).linkIndex.getD
        (s5PermuteLink ((s5Block b).autos.getD a 0) link) (s5Dim b) < s5Dim b ↔
        (s5Block b).linkIndex.getD link (s5Dim b) < s5Dim b) := by native_decide

end FlagAlgebras.Core.Tetrahedron.FullSevenLong
