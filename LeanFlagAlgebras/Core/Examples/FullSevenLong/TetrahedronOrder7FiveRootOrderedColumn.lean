import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootColumn
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootOrderedData
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

namespace FlagAlgebras.Core.Tetrahedron.FullSevenLong

open scoped BigOperators

/-- Unaveraged Gram entry, stated as the exact integer square-factor sum. -/
def s5FactorPair (b : Fin 18) (i j : ℕ) : ℤ :=
  ∑ r : Fin (s5Rows b), fS5 b r.val i * fS5 b r.val j

/-- One ordered rooting, with both ordered outside pairs. The three inputs
are the root's ten-bit mask and the two ten-bit links in that root order. -/
def s5LinkCell (b : Fin 18) (root left right : ℕ) : ℤ :=
  if root = (s5Block b).sigma then
    let i := (s5Block b).linkIndex.getD left (s5Dim b)
    let j := (s5Block b).linkIndex.getD right (s5Dim b)
    if i < s5Dim b ∧ j < s5Dim b then 2 * s5FactorPair b i j else 0
  else 0

def s5OrderedSample (k : Fin 2520) : FiveRootSample :=
  s5OrderedSamples.getD k.val default

/-- Reference evaluator over all 2520 ordered rootings. Its equality to the
21-root-set evaluator is proved separately from the flag-density bridge. -/
def s5OrderedColumnNum (w : ℕ) : ℤ :=
  ∑ b : Fin 18, ∑ k : Fin 2520,
    let s := s5OrderedSample k
    s5LinkCell b (s5Gather s.rootGather 10 w)
      (s5LinkMask6 (s5Gather s.leftGather 20 w))
      (s5LinkMask6 (s5Gather s.rightGather 20 w))

end FlagAlgebras.Core.Tetrahedron.FullSevenLong
