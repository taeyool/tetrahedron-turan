import LeanFlagAlgebras.Core.Expand
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7BlockCheck

/-! # The block SOS element

The certificate's order-6 semidefinite part, as an element: one
downward square per stored factor row, summed over the five block
families. Its expansion coefficients are the fiber sums the bridges
computed, so — through the sweep — the coefficient of every six-vertex
class is the certificate's block number over its denominator.

This file defines the element and proves its expansion; the
identification with `blockElt6` and the nonnegativity conclusion sit on
top. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

open Classical

/-! ## Instantiation prerequisites -/

lemma wf24F : ∀ i : Fin 11, (blk24Flag i.val).WellFormed pairType2 :=
  fun i => blk24Flag_wf i.val i.isLt

lemma mem24F : ∀ i : Fin 11,
    TetraFree.Mem (blk24Flag i.val).graph.toModel :=
  fun i => blk24Flag_mem i.val i.isLt

lemma wf45F_0 : ∀ i : Fin flags45_0.length,
    (blk45Flag flags45_0 i.val).WellFormed (rmType 0) :=
  fun i => blk45Flag_wf_0 i.val (flags45_0_length ▸ i.isLt)

lemma wf45F_1 : ∀ i : Fin flags45_1.length,
    (blk45Flag flags45_1 i.val).WellFormed (rmType 1) :=
  fun i => blk45Flag_wf_1 i.val (flags45_1_length ▸ i.isLt)

lemma wf45F_3 : ∀ i : Fin flags45_3.length,
    (blk45Flag flags45_3 i.val).WellFormed (rmType 3) :=
  fun i => blk45Flag_wf_3 i.val (flags45_3_length ▸ i.isLt)

lemma wf45F_7 : ∀ i : Fin flags45_7.length,
    (blk45Flag flags45_7 i.val).WellFormed (rmType 7) :=
  fun i => blk45Flag_wf_7 i.val (flags45_7_length ▸ i.isLt)

lemma mem45F_0 : ∀ i : Fin flags45_0.length,
    TetraFree.Mem (blk45Flag flags45_0 i.val).graph.toModel :=
  fun i => blk45Flag_mem_0 (flags45_0_length ▸ i.isLt)

lemma mem45F_1 : ∀ i : Fin flags45_1.length,
    TetraFree.Mem (blk45Flag flags45_1 i.val).graph.toModel :=
  fun i => blk45Flag_mem_1 (flags45_1_length ▸ i.isLt)

lemma mem45F_3 : ∀ i : Fin flags45_3.length,
    TetraFree.Mem (blk45Flag flags45_3 i.val).graph.toModel :=
  fun i => blk45Flag_mem_3 (flags45_3_length ▸ i.isLt)

lemma mem45F_7 : ∀ i : Fin flags45_7.length,
    TetraFree.Mem (blk45Flag flags45_7 i.val).graph.toModel :=
  fun i => blk45Flag_mem_7 (flags45_7_length ▸ i.isLt)

set_option maxRecDepth 65536 in
lemma flags45_0_lt : ∀ i < flags45_0.length,
    flags45_0.getD i 0 < 2 ^ 10 := by decide

set_option maxRecDepth 65536 in
lemma flags45_1_lt : ∀ i < flags45_1.length,
    flags45_1.getD i 0 < 2 ^ 10 := by decide

set_option maxRecDepth 65536 in
lemma flags45_3_lt : ∀ i < flags45_3.length,
    flags45_3.getD i 0 < 2 ^ 10 := by decide

set_option maxRecDepth 65536 in
lemma flags45_7_lt : ∀ i < flags45_7.length,
    flags45_7.getD i 0 < 2 ^ 10 := by decide

/-! ## The row elements -/

/-- A 24-row element of the pair-typed algebra. -/
noncomputable def x24 (row : List ℤ) :
    FlagAlgebra TetraFree pairType2.toModel :=
  ∑ i : Fin 11, ((row.getD i.val 0 : ℤ) : ℝ) •
    ⟦basisVector ⟨4, (blk24Flag i.val).toFlag (wf24F i) (mem24F i)⟩⟧

/-- A 45-row element, one definition per family so the instances
resolve. -/
noncomputable def x45_0 (row : List ℤ) :
    FlagAlgebra TetraFree (rmType 0).toModel :=
  ∑ i : Fin flags45_0.length, ((row.getD i.val 0 : ℤ) : ℝ) •
    ⟦basisVector ⟨5, (blk45Flag flags45_0 i.val).toFlag
      (wf45F_0 i) (mem45F_0 i)⟩⟧

noncomputable def x45_1 (row : List ℤ) :
    FlagAlgebra TetraFree (rmType 1).toModel :=
  ∑ i : Fin flags45_1.length, ((row.getD i.val 0 : ℤ) : ℝ) •
    ⟦basisVector ⟨5, (blk45Flag flags45_1 i.val).toFlag
      (wf45F_1 i) (mem45F_1 i)⟩⟧

noncomputable def x45_3 (row : List ℤ) :
    FlagAlgebra TetraFree (rmType 3).toModel :=
  ∑ i : Fin flags45_3.length, ((row.getD i.val 0 : ℤ) : ℝ) •
    ⟦basisVector ⟨5, (blk45Flag flags45_3 i.val).toFlag
      (wf45F_3 i) (mem45F_3 i)⟩⟧

noncomputable def x45_7 (row : List ℤ) :
    FlagAlgebra TetraFree (rmType 7).toModel :=
  ∑ i : Fin flags45_7.length, ((row.getD i.val 0 : ℤ) : ℝ) •
    ⟦basisVector ⟨5, (blk45Flag flags45_7 i.val).toFlag
      (wf45F_7 i) (mem45F_7 i)⟩⟧

/-- **The block SOS element**: one downward square per stored factor
row. -/
noncomputable def blockSOS : FlagAlgebra TetraFree emptyType :=
  (facs24L.map fun row => downward (x24 row * x24 row)).sum
    + (facs45_0L.map fun row => downward (x45_0 row * x45_0 row)).sum
    + (facs45_1L.map fun row => downward (x45_1 row * x45_1 row)).sum
    + (facs45_3L.map fun row => downward (x45_3 row * x45_3 row)).sum
    + (facs45_7L.map fun row => downward (x45_7 row * x45_7 row)).sum

/-! ## Nonnegativity -/

private lemma list_sum_nonneg {l : List (FlagAlgebra TetraFree emptyType)}
    (h : ∀ x ∈ l, (0 : FlagAlgebra TetraFree emptyType) ≤ x) :
    (0 : FlagAlgebra TetraFree emptyType) ≤ l.sum := by
  induction l with
  | nil => exact le_refl _
  | cons a t ih =>
    rw [List.sum_cons]
    have ha := h a (List.mem_cons_self)
    have ht := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    calc (0 : FlagAlgebra TetraFree emptyType)
        = 0 + 0 := (add_zero _).symm
      _ ≤ a + t.sum := by
          intro φ
          have h1 := ha φ
          have h2 := ht φ
          rw [sub_zero] at h1 h2
          rw [PositiveHom.map_sub, PositiveHom.map_add,
            PositiveHom.map_add, PositiveHom.map_zero]
          linarith

/-- The block SOS element is nonnegative: every summand is a downward
square. -/
theorem blockSOS_nonneg :
    (0 : FlagAlgebra TetraFree emptyType) ≤ blockSOS := by
  have hpart : ∀ (l : List (FlagAlgebra TetraFree emptyType)),
      (∀ x ∈ l, (0 : FlagAlgebra TetraFree emptyType) ≤ x) →
      (0 : FlagAlgebra TetraFree emptyType) ≤ l.sum := fun l h =>
    list_sum_nonneg h
  have h24 := hpart (facs24L.map fun row => downward (x24 row * x24 row))
    (fun x hx => by
      obtain ⟨row, -, rfl⟩ := List.mem_map.mp hx
      exact downward_square_nonneg _)
  have h0 := hpart (facs45_0L.map fun row =>
      downward (x45_0 row * x45_0 row))
    (fun x hx => by
      obtain ⟨row, -, rfl⟩ := List.mem_map.mp hx
      exact downward_square_nonneg _)
  have h1 := hpart (facs45_1L.map fun row =>
      downward (x45_1 row * x45_1 row))
    (fun x hx => by
      obtain ⟨row, -, rfl⟩ := List.mem_map.mp hx
      exact downward_square_nonneg _)
  have h3 := hpart (facs45_3L.map fun row =>
      downward (x45_3 row * x45_3 row))
    (fun x hx => by
      obtain ⟨row, -, rfl⟩ := List.mem_map.mp hx
      exact downward_square_nonneg _)
  have h7 := hpart (facs45_7L.map fun row =>
      downward (x45_7 row * x45_7 row))
    (fun x hx => by
      obtain ⟨row, -, rfl⟩ := List.mem_map.mp hx
      exact downward_square_nonneg _)
  intro φ
  rw [sub_zero]
  have g24 := h24 φ; rw [sub_zero] at g24
  have g0 := h0 φ; rw [sub_zero] at g0
  have g1 := h1 φ; rw [sub_zero] at g1
  have g3 := h3 φ; rw [sub_zero] at g3
  have g7 := h7 φ; rw [sub_zero] at g7
  show 0 ≤ φ blockSOS
  rw [blockSOS, PositiveHom.map_add, PositiveHom.map_add,
    PositiveHom.map_add, PositiveHom.map_add]
  linarith

end FlagAlgebras.Core.Tetrahedron
