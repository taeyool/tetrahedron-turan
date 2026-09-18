import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Column

/-! # The per-representative certificate check

The certificate's claim is a statement about every admissible labeled
seven-vertex extension: its column value never exceeds the bound. This
file packages that claim representative by representative, so the sweep
can be split into blocks checked independently.

`linkOK h link` is the claim for one extension — vacuously true when the
extension is not tetrahedron-free — and `sweepRep h` runs it over all
`2 ^ 15` links of one representative. `sweepBlockOf n` covers twenty
consecutive representatives, the unit the sweep files use. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

set_option maxRecDepth 100000

/-- One extension: an admissible column must not exceed the bound.

Written without a `let` binding: the bound extraction below rewrites
inside this body, and a `let` would survive unfolding as an opaque
binder. Recomputing the mask costs a fraction of a percent of a
column. -/
def linkOK (h link : ℕ) : Bool :=
  if k4FreeMask qs7 (extendMask h link) then
    decide (columnValue (extendMask h link) ≤ columnBound)
  else true

def sweepRepAux (h : ℕ) : ℕ → Bool → Bool
  | 0, acc => acc
  | n + 1, acc => sweepRepAux h n (acc && linkOK h n)

/-- All `2 ^ 15` links of one representative. -/
def sweepRep (h : ℕ) : Bool := sweepRepAux h 32768 true

/-- Twenty consecutive representatives — the unit of the sweep. -/
def sweepBlockOf (n : ℕ) : Bool :=
  (((h6Reps.drop (20 * n)).take 20).map sweepRep).all id

/-- The accumulator carries the conjunction: a true verdict means the
seed held and every link below the bound was checked. -/
lemma sweepRepAux_spec (h : ℕ) :
    ∀ n acc, sweepRepAux h n acc = true → acc = true ∧ ∀ k < n, linkOK h k = true := by
  intro n
  induction n with
  | zero =>
    intro acc hacc
    exact ⟨hacc, fun k hk => absurd hk (by omega)⟩
  | succ n ih =>
    intro acc hacc
    obtain ⟨hand, hlow⟩ := ih (acc && linkOK h n) hacc
    rw [Bool.and_eq_true] at hand
    refine ⟨hand.1, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
    · exact hlow k hlt
    · exact hand.2

/-- Reading a block verdict back: every representative it covers passes.

The rewrites are kept explicit: any step that asks Lean to unfold
`sweepRep` up to definitional equality would expand its `2 ^ 15`-deep
recursion and overflow the elaborator. -/
lemma sweepRep_of_block {n : ℕ} (hb : sweepBlockOf n = true) :
    ∀ x ∈ (h6Reps.drop (20 * n)).take 20, sweepRep x = true := by
  intro x hx
  have h1 := List.all_eq_true.mp hb (sweepRep x) (List.mem_map.mpr ⟨x, hx, rfl⟩)
  rwa [id_eq] at h1

/-- **The certificate bound, for one admissible extension of a
representative that passed its sweep.** -/
lemma columnValue_le_of_sweepRep {h link : ℕ} (hs : sweepRep h = true)
    (hlink : link < 32768)
    (hadm : k4FreeMask qs7 (extendMask h link) = true) :
    columnValue (extendMask h link) ≤ columnBound := by
  unfold sweepRep at hs
  have hlk := (sweepRepAux_spec h 32768 true hs).2 link hlink
  unfold linkOK at hlk
  rw [hadm] at hlk
  exact of_decide_eq_true (by simpa using hlk)

end FlagAlgebras.Core.Tetrahedron
