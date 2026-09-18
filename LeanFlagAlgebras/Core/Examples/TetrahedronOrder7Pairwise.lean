import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Orbit00
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Orbit01
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Orbit02
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Orbit03
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Orbit04
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Orbit05
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Orbit06
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Orbit07
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Orbit08
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Orbit09

/-! # The 964 representatives are pairwise non-isomorphic

Every listed representative is the least mask in its own orbit (checked
block by block in the `TetrahedronOrder7Orbit*` files), and the orbit of
a mask is exactly its isomorphism class, so distinct representatives name
distinct isomorphism classes. Together with the completeness theorem of
`TetrahedronOrder7Complete`, the 964 masks are a faithful listing of the
tetrahedron-free six-vertex classes: every class appears, and none
appears twice. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

set_option maxRecDepth 8192 in
/-- Every representative lies in the mask range. -/
lemma h6Reps_lt : (h6Reps.all fun x => decide (x < 2 ^ 20)) = true := by
  decide

lemma h6Reps_lt_of_mem {x : ℕ} (hx : x ∈ h6Reps) : x < 2 ^ 20 :=
  of_decide_eq_true (List.all_eq_true.mp h6Reps_lt x hx)

/-- The blocks cover the listing; past the last block the range is
empty. -/
lemma h6BlockOK : ∀ j, ∀ y ∈ (h6Reps.drop (10 * j)).take 10, orbitMin y = y
  | 0 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_00 y hy
  | 1 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_01 y hy
  | 2 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_02 y hy
  | 3 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_03 y hy
  | 4 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_04 y hy
  | 5 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_05 y hy
  | 6 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_06 y hy
  | 7 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_07 y hy
  | 8 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_08 y hy
  | 9 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_09 y hy
  | 10 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_10 y hy
  | 11 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_11 y hy
  | 12 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_12 y hy
  | 13 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_13 y hy
  | 14 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_14 y hy
  | 15 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_15 y hy
  | 16 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_16 y hy
  | 17 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_17 y hy
  | 18 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_18 y hy
  | 19 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_19 y hy
  | 20 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_20 y hy
  | 21 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_21 y hy
  | 22 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_22 y hy
  | 23 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_23 y hy
  | 24 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_24 y hy
  | 25 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_25 y hy
  | 26 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_26 y hy
  | 27 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_27 y hy
  | 28 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_28 y hy
  | 29 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_29 y hy
  | 30 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_30 y hy
  | 31 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_31 y hy
  | 32 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_32 y hy
  | 33 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_33 y hy
  | 34 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_34 y hy
  | 35 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_35 y hy
  | 36 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_36 y hy
  | 37 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_37 y hy
  | 38 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_38 y hy
  | 39 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_39 y hy
  | 40 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_40 y hy
  | 41 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_41 y hy
  | 42 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_42 y hy
  | 43 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_43 y hy
  | 44 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_44 y hy
  | 45 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_45 y hy
  | 46 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_46 y hy
  | 47 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_47 y hy
  | 48 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_48 y hy
  | 49 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_49 y hy
  | 50 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_50 y hy
  | 51 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_51 y hy
  | 52 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_52 y hy
  | 53 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_53 y hy
  | 54 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_54 y hy
  | 55 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_55 y hy
  | 56 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_56 y hy
  | 57 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_57 y hy
  | 58 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_58 y hy
  | 59 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_59 y hy
  | 60 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_60 y hy
  | 61 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_61 y hy
  | 62 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_62 y hy
  | 63 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_63 y hy
  | 64 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_64 y hy
  | 65 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_65 y hy
  | 66 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_66 y hy
  | 67 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_67 y hy
  | 68 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_68 y hy
  | 69 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_69 y hy
  | 70 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_70 y hy
  | 71 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_71 y hy
  | 72 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_72 y hy
  | 73 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_73 y hy
  | 74 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_74 y hy
  | 75 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_75 y hy
  | 76 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_76 y hy
  | 77 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_77 y hy
  | 78 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_78 y hy
  | 79 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_79 y hy
  | 80 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_80 y hy
  | 81 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_81 y hy
  | 82 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_82 y hy
  | 83 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_83 y hy
  | 84 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_84 y hy
  | 85 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_85 y hy
  | 86 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_86 y hy
  | 87 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_87 y hy
  | 88 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_88 y hy
  | 89 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_89 y hy
  | 90 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_90 y hy
  | 91 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_91 y hy
  | 92 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_92 y hy
  | 93 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_93 y hy
  | 94 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_94 y hy
  | 95 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_95 y hy
  | 96 => fun y hy => by
      simpa using List.all_eq_true.mp orbitMinBlock_96 y hy
  | _ + 97 => fun y hy => by
      rw [List.drop_eq_nil_of_le (by rw [h6Reps_length]; omega)] at hy
      simp at hy

/-- Every representative is the least mask in its orbit. -/
theorem h6Reps_orbitMin {x : ℕ} (hx : x ∈ h6Reps) : orbitMin x = x := by
  obtain ⟨j, hj⟩ := mem_take_drop_of_mem (n := 10) (by norm_num) hx
  exact h6BlockOK j x hj

/-- **Distinctness**: distinct representatives are non-isomorphic. -/
theorem h6Reps_not_isIso {a b : ℕ} (ha : a ∈ h6Reps) (hb : b ∈ h6Reps)
    (hne : a ≠ b) :
    ¬(graphOfMask 6 a).IsIso (graphOfMask 6 b) :=
  not_isIso_of_orbitMin (h6Reps_lt_of_mem ha) (h6Reps_lt_of_mem hb)
    (h6Reps_orbitMin ha) (h6Reps_orbitMin hb) hne

/-- Distinct representatives carry distinct flag classes. -/
theorem h6Reps_toFlag_ne {a b : ℕ} (ha : a ∈ h6Reps) (hb : b ∈ h6Reps)
    (hne : a ≠ b) :
    (graphOfMask 6 a).toFlag (h6Reps_mem ha)
      ≠ (graphOfMask 6 b).toFlag (h6Reps_mem hb) := fun heq =>
  h6Reps_not_isIso ha hb hne
    ((Sym3Graph.toFlag_eq_toFlag_iff (h6Reps_mem ha) (h6Reps_mem hb)).mp heq)

end FlagAlgebras.Core.Tetrahedron
