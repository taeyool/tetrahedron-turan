import LeanFlagAlgebras.Core.Expand
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7RootAcct
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7FoldSum

/-! # The order-7 root SOS element

The certificate's order-7 semidefinite part, as an element: one downward
square per stored factor row, over the three rooted families — the
one-root family at the single-vertex type and the two three-root
families at the empty-triple and hyperedge types.

This file defines the element and proves it nonnegative, mirroring
`blockSOS` at level six. The coefficient identification with `rootElt`
is the sequel. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

open Classical

/-! ## Instantiation prerequisites -/

lemma wfS1F : ∀ i : Fin 7, (s1Flag i.val).WellFormed vertexGraph :=
  fun i => s1Flag_wf i.val i.isLt

lemma memS1F : ∀ i : Fin 7,
    TetraFree.Mem (s1Flag i.val).graph.toModel :=
  fun i => s1Flag_mem i.isLt

lemma wfS30F : ∀ i : Fin 236, (s30Flag i.val).WellFormed (s3Type 0) :=
  fun i => s30Flag_wf i.val i.isLt

lemma memS30F : ∀ i : Fin 236,
    TetraFree.Mem (s30Flag i.val).graph.toModel :=
  fun i => s30Flag_mem i.isLt

lemma wfS31F : ∀ i : Fin 191, (s31Flag i.val).WellFormed (s3Type 1) :=
  fun i => s31Flag_wf i.val i.isLt

lemma memS31F : ∀ i : Fin 191,
    TetraFree.Mem (s31Flag i.val).graph.toModel :=
  fun i => s31Flag_mem i.isLt

/-! ## The row elements -/

/-- A one-root row element. -/
noncomputable def xS1 (r : ℕ) :
    FlagAlgebra TetraFree vertexGraph.toModel :=
  ∑ i : Fin 7, ((fS1 r i.val : ℤ) : ℝ) •
    ⟦basisVector ⟨4, (s1Flag i.val).toFlag (wfS1F i) (memS1F i)⟩⟧

/-- A nonedge-root row element. -/
noncomputable def xS30 (r : ℕ) :
    FlagAlgebra TetraFree (s3Type 0).toModel :=
  ∑ i : Fin 236, ((fS30 r i.val : ℤ) : ℝ) •
    ⟦basisVector ⟨5, (s30Flag i.val).toFlag (wfS30F i) (memS30F i)⟩⟧

/-- An edge-root row element. -/
noncomputable def xS31 (r : ℕ) :
    FlagAlgebra TetraFree (s3Type 1).toModel :=
  ∑ i : Fin 191, ((fS31 r i.val : ℤ) : ℝ) •
    ⟦basisVector ⟨5, (s31Flag i.val).toFlag (wfS31F i) (memS31F i)⟩⟧

/-- **The order-7 root SOS element**: one downward square per stored
factor row over the three rooted families. No family multipliers: the
certificate's `36` and `4` are exactly the fiber normalizers
`36/5040 = (1/7)(1/20)` and `4/5040 = (1/210)(1/6)` that the downward
expansion already produces, so the squares enter with weight one. -/
noncomputable def rootSOS : FlagAlgebra TetraFree emptyType :=
  ((List.range 6).map fun r => downward (xS1 r * xS1 r)).sum
    + ((List.range 60).map fun r => downward (xS30 r * xS30 r)).sum
    + ((List.range 46).map fun r => downward (xS31 r * xS31 r)).sum

/-! ## Nonnegativity -/

private lemma list_sum_nonneg' {l : List (FlagAlgebra TetraFree emptyType)}
    (h : ∀ x ∈ l, (0 : FlagAlgebra TetraFree emptyType) ≤ x) :
    (0 : FlagAlgebra TetraFree emptyType) ≤ l.sum := by
  induction l with
  | nil => exact le_refl _
  | cons a t ih =>
    rw [List.sum_cons]
    have ha := h a List.mem_cons_self
    have ht := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    intro φ
    have h1 := ha φ
    have h2 := ht φ
    rw [sub_zero] at h1 h2 ⊢
    rw [PositiveHom.map_add]
    linarith

/-- The root SOS element is nonnegative: every summand is a downward
square. -/
theorem rootSOS_nonneg :
    (0 : FlagAlgebra TetraFree emptyType) ≤ rootSOS := by
  have h1 := list_sum_nonneg'
    (l := (List.range 6).map fun r => downward (xS1 r * xS1 r))
    (fun x hx => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
      exact downward_square_nonneg _)
  have h30 := list_sum_nonneg'
    (l := (List.range 60).map fun r => downward (xS30 r * xS30 r))
    (fun x hx => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
      exact downward_square_nonneg _)
  have h31 := list_sum_nonneg'
    (l := (List.range 46).map fun r => downward (xS31 r * xS31 r))
    (fun x hx => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
      exact downward_square_nonneg _)
  intro φ
  have e1 := h1 φ; rw [sub_zero] at e1
  have e30 := h30 φ; rw [sub_zero] at e30
  have e31 := h31 φ; rw [sub_zero] at e31
  rw [sub_zero]
  show 0 ≤ φ rootSOS
  rw [rootSOS, PositiveHom.map_add, PositiveHom.map_add]
  linarith

end FlagAlgebras.Core.Tetrahedron
