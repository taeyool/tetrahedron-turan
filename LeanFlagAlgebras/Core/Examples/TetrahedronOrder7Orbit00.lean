import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Distinct

/-! Orbit-minimum block 0 of 10: representatives 0–99.

Machine-generated. Each declaration checks ten representatives, keeping
the kernel evaluation cache of a single declaration to a few gigabytes;
`TetrahedronOrder7Pairwise` collects the blocks. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

set_option maxRecDepth 65536 in
lemma orbitMinBlock_00 :
    (((h6Reps.drop (10 * 0)).take 10).all fun x =>
      decide (orbitMin x = x)) = true := by
  decide +kernel

set_option maxRecDepth 65536 in
lemma orbitMinBlock_01 :
    (((h6Reps.drop (10 * 1)).take 10).all fun x =>
      decide (orbitMin x = x)) = true := by
  decide +kernel

set_option maxRecDepth 65536 in
lemma orbitMinBlock_02 :
    (((h6Reps.drop (10 * 2)).take 10).all fun x =>
      decide (orbitMin x = x)) = true := by
  decide +kernel

set_option maxRecDepth 65536 in
lemma orbitMinBlock_03 :
    (((h6Reps.drop (10 * 3)).take 10).all fun x =>
      decide (orbitMin x = x)) = true := by
  decide +kernel

set_option maxRecDepth 65536 in
lemma orbitMinBlock_04 :
    (((h6Reps.drop (10 * 4)).take 10).all fun x =>
      decide (orbitMin x = x)) = true := by
  decide +kernel

set_option maxRecDepth 65536 in
lemma orbitMinBlock_05 :
    (((h6Reps.drop (10 * 5)).take 10).all fun x =>
      decide (orbitMin x = x)) = true := by
  decide +kernel

set_option maxRecDepth 65536 in
lemma orbitMinBlock_06 :
    (((h6Reps.drop (10 * 6)).take 10).all fun x =>
      decide (orbitMin x = x)) = true := by
  decide +kernel

set_option maxRecDepth 65536 in
lemma orbitMinBlock_07 :
    (((h6Reps.drop (10 * 7)).take 10).all fun x =>
      decide (orbitMin x = x)) = true := by
  decide +kernel

set_option maxRecDepth 65536 in
lemma orbitMinBlock_08 :
    (((h6Reps.drop (10 * 8)).take 10).all fun x =>
      decide (orbitMin x = x)) = true := by
  decide +kernel

set_option maxRecDepth 65536 in
lemma orbitMinBlock_09 :
    (((h6Reps.drop (10 * 9)).take 10).all fun x =>
      decide (orbitMin x = x)) = true := by
  decide +kernel

end FlagAlgebras.Core.Tetrahedron
