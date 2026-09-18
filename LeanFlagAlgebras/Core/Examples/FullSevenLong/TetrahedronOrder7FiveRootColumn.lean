import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootData
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootTables

/-! The five-root numerator. Grams are computed from the integer factors and
summed over the full type automorphism group. No invariant-vector projection is
performed. The inner host loop contains only 21 root sets and table lookups. -/

namespace FlagAlgebras.Core.Tetrahedron.FullSevenLong

def s5RawGram (d : FiveRootData) : Array ℤ :=
  Array.ofFn fun k : Fin (d.dimension * d.dimension) =>
    (List.range d.rows).foldl (fun acc r =>
      acc + d.factors.getD (r * d.dimension + k.val / d.dimension) 0 *
        d.factors.getD (r * d.dimension + k.val % d.dimension) 0) 0

def s5AveragedGram (d : FiveRootData) : Array ℤ :=
  let q := s5RawGram d
  Array.ofFn fun k : Fin (d.dimension * d.dimension) =>
    (List.range d.autos.size).foldl (fun acc a =>
      let i := d.action.getD (a * d.dimension + k.val / d.dimension) d.dimension
      let j := d.action.getD (a * d.dimension + k.val % d.dimension) d.dimension
      acc + q.getD (i * d.dimension + j) 0) 0

def s5GramTables : Array (Array ℤ) := s5Data.map s5AveragedGram

def s5CanonicalIndex (root link : ℕ) : ℕ :=
  let bp := s5RootInfo.getD root (18, 0)
  let d := s5Data.getD bp.1 default
  d.linkIndex.getD (s5PermuteLink bp.2 link) d.dimension

/-- The canonical-link lookup is a definitionally generated cache of the
1024 possible root masks and 1024 possible links. -/
def s5CanonicalIndices : Array ℕ :=
  Array.ofFn fun k : Fin (1024 * 1024) =>
    s5CanonicalIndex (k.val / 1024) (k.val % 1024)

def s5RootCell (w : ℕ) (s : FiveRootSample) : ℤ :=
  let root := s5Gather s.rootGather 10 w
  let b := (s5RootInfo.getD root (18, 0)).1
  if b < 18 then
    let d := s5Data.getD b default
    let left := s5Gather s.leftGather 10 w
    let right := s5Gather s.rightGather 10 w
    let i := s5CanonicalIndices.getD (root * 1024 + left) d.dimension
    let j := s5CanonicalIndices.getD (root * 1024 + right) d.dimension
    if i < d.dimension ∧ j < d.dimension then
      2 * (s5GramTables.getD b #[]).getD (i * d.dimension + j) 0
    else 0
  else 0

/-- Integer numerator of all active five-root factors, over the shared
denominator `5040 * scale^2`. The factor two counts both outside-vertex orders. -/
def s5ColumnNum (w : ℕ) : ℤ :=
  s5Samples.foldl (fun acc s => acc + s5RootCell w s) 0

end FlagAlgebras.Core.Tetrahedron.FullSevenLong
