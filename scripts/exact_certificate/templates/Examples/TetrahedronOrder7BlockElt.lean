import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7BlockSOS
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Pieces

/-! # The block element is the scaled SOS element

Expanding each downward square of `blockSOS` over the six-vertex
classes, evaluating the fiber sums through the bridges at each class's
representative, and replacing the rooting sums by the certificate's
folds through the sweep, the coefficient of every class comes out as
the certificate's block number over `720 · D²`. That is `blockElt6`'s
coefficient times `D²`, so

  `blockElt6 = (1 / D²) • blockSOS`,

and with `blockSOS ≥ 0` this closes `0 ≤ blockElt6`. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

open Classical

private lemma sum_list_swap {α : Type}
    (l : List α) (g : α → FlagWithSize TetraFree emptyType 6 →
      FlagAlgebra TetraFree emptyType) :
    (l.map fun a => ∑ H : FlagWithSize TetraFree emptyType 6, g a H).sum
      = ∑ H : FlagWithSize TetraFree emptyType 6,
          (l.map fun a => g a H).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [List.map_cons, List.sum_cons]

/-! ## The per-row expansions -/

private lemma expand24 (row : List ℤ) :
    downward (x24 row * x24 row)
      = ∑ H : FlagWithSize TetraFree emptyType 6,
          (∑ X ∈ Finset.univ.filter
              (fun X : FlagWithSize TetraFree pairType2.toModel 6 =>
                Flag.unlabel X = H),
            (∑ i : Fin 11, ∑ j : Fin 11,
                ((row.getD i.val 0 : ℤ) : ℝ) * ((row.getD j.val 0 : ℤ) : ℝ)
                  * ((subflagPairDensity
                      ((blk24Flag i.val).toFlag (wf24F i) (mem24F i))
                      ((blk24Flag j.val).toFlag (wf24F j) (mem24F j))
                      X : ℚ) : ℝ))
              * (labelingFactor (Quotient.out X).unlabel
                  (Quotient.out X) : ℝ)) •
            ⟦basisVector ⟨6, H⟩⟧ := by
  have hx : x24 row = ∑ i : Fin 11, ((row.getD i.val 0 : ℤ) : ℝ) •
      ⟦basisVector ⟨4, (blk24Flag i.val).toFlag (wf24F i) (mem24F i)⟩⟧ :=
    rfl
  rw [hx]
  exact downward_linear_sq
    (fun i : Fin 11 => ((row.getD i.val 0 : ℤ) : ℝ))
    (fun i => (blk24Flag i.val).toFlag (wf24F i) (mem24F i))
    (by simp)

private lemma expand45_0 (row : List ℤ) :
    downward (x45_0 row * x45_0 row)
      = ∑ H : FlagWithSize TetraFree emptyType 6,
          (∑ X ∈ Finset.univ.filter
              (fun X : FlagWithSize TetraFree (rmType 0).toModel 6 =>
                Flag.unlabel X = H),
            (∑ i : Fin flags45_0.length, ∑ j : Fin flags45_0.length,
                ((row.getD i.val 0 : ℤ) : ℝ) * ((row.getD j.val 0 : ℤ) : ℝ)
                  * ((subflagPairDensity
                      ((blk45Flag flags45_0 i.val).toFlag
                        (wf45F_0 i) (mem45F_0 i))
                      ((blk45Flag flags45_0 j.val).toFlag
                        (wf45F_0 j) (mem45F_0 j))
                      X : ℚ) : ℝ))
              * (labelingFactor (Quotient.out X).unlabel
                  (Quotient.out X) : ℝ)) •
            ⟦basisVector ⟨6, H⟩⟧ := by
  have hx : x45_0 row = ∑ i : Fin flags45_0.length,
      ((row.getD i.val 0 : ℤ) : ℝ) •
      ⟦basisVector ⟨5, (blk45Flag flags45_0 i.val).toFlag
        (wf45F_0 i) (mem45F_0 i)⟩⟧ := rfl
  rw [hx]
  exact downward_linear_sq
    (fun i : Fin flags45_0.length => ((row.getD i.val 0 : ℤ) : ℝ))
    (fun i => (blk45Flag flags45_0 i.val).toFlag (wf45F_0 i) (mem45F_0 i))
    (by simp)

private lemma expand45_1 (row : List ℤ) :
    downward (x45_1 row * x45_1 row)
      = ∑ H : FlagWithSize TetraFree emptyType 6,
          (∑ X ∈ Finset.univ.filter
              (fun X : FlagWithSize TetraFree (rmType 1).toModel 6 =>
                Flag.unlabel X = H),
            (∑ i : Fin flags45_1.length, ∑ j : Fin flags45_1.length,
                ((row.getD i.val 0 : ℤ) : ℝ) * ((row.getD j.val 0 : ℤ) : ℝ)
                  * ((subflagPairDensity
                      ((blk45Flag flags45_1 i.val).toFlag
                        (wf45F_1 i) (mem45F_1 i))
                      ((blk45Flag flags45_1 j.val).toFlag
                        (wf45F_1 j) (mem45F_1 j))
                      X : ℚ) : ℝ))
              * (labelingFactor (Quotient.out X).unlabel
                  (Quotient.out X) : ℝ)) •
            ⟦basisVector ⟨6, H⟩⟧ := by
  have hx : x45_1 row = ∑ i : Fin flags45_1.length,
      ((row.getD i.val 0 : ℤ) : ℝ) •
      ⟦basisVector ⟨5, (blk45Flag flags45_1 i.val).toFlag
        (wf45F_1 i) (mem45F_1 i)⟩⟧ := rfl
  rw [hx]
  exact downward_linear_sq
    (fun i : Fin flags45_1.length => ((row.getD i.val 0 : ℤ) : ℝ))
    (fun i => (blk45Flag flags45_1 i.val).toFlag (wf45F_1 i) (mem45F_1 i))
    (by simp)

private lemma expand45_3 (row : List ℤ) :
    downward (x45_3 row * x45_3 row)
      = ∑ H : FlagWithSize TetraFree emptyType 6,
          (∑ X ∈ Finset.univ.filter
              (fun X : FlagWithSize TetraFree (rmType 3).toModel 6 =>
                Flag.unlabel X = H),
            (∑ i : Fin flags45_3.length, ∑ j : Fin flags45_3.length,
                ((row.getD i.val 0 : ℤ) : ℝ) * ((row.getD j.val 0 : ℤ) : ℝ)
                  * ((subflagPairDensity
                      ((blk45Flag flags45_3 i.val).toFlag
                        (wf45F_3 i) (mem45F_3 i))
                      ((blk45Flag flags45_3 j.val).toFlag
                        (wf45F_3 j) (mem45F_3 j))
                      X : ℚ) : ℝ))
              * (labelingFactor (Quotient.out X).unlabel
                  (Quotient.out X) : ℝ)) •
            ⟦basisVector ⟨6, H⟩⟧ := by
  have hx : x45_3 row = ∑ i : Fin flags45_3.length,
      ((row.getD i.val 0 : ℤ) : ℝ) •
      ⟦basisVector ⟨5, (blk45Flag flags45_3 i.val).toFlag
        (wf45F_3 i) (mem45F_3 i)⟩⟧ := rfl
  rw [hx]
  exact downward_linear_sq
    (fun i : Fin flags45_3.length => ((row.getD i.val 0 : ℤ) : ℝ))
    (fun i => (blk45Flag flags45_3 i.val).toFlag (wf45F_3 i) (mem45F_3 i))
    (by simp)

private lemma expand45_7 (row : List ℤ) :
    downward (x45_7 row * x45_7 row)
      = ∑ H : FlagWithSize TetraFree emptyType 6,
          (∑ X ∈ Finset.univ.filter
              (fun X : FlagWithSize TetraFree (rmType 7).toModel 6 =>
                Flag.unlabel X = H),
            (∑ i : Fin flags45_7.length, ∑ j : Fin flags45_7.length,
                ((row.getD i.val 0 : ℤ) : ℝ) * ((row.getD j.val 0 : ℤ) : ℝ)
                  * ((subflagPairDensity
                      ((blk45Flag flags45_7 i.val).toFlag
                        (wf45F_7 i) (mem45F_7 i))
                      ((blk45Flag flags45_7 j.val).toFlag
                        (wf45F_7 j) (mem45F_7 j))
                      X : ℚ) : ℝ))
              * (labelingFactor (Quotient.out X).unlabel
                  (Quotient.out X) : ℝ)) •
            ⟦basisVector ⟨6, H⟩⟧ := by
  have hx : x45_7 row = ∑ i : Fin flags45_7.length,
      ((row.getD i.val 0 : ℤ) : ℝ) •
      ⟦basisVector ⟨5, (blk45Flag flags45_7 i.val).toFlag
        (wf45F_7 i) (mem45F_7 i)⟩⟧ := rfl
  rw [hx]
  exact downward_linear_sq
    (fun i : Fin flags45_7.length => ((row.getD i.val 0 : ℤ) : ℝ))
    (fun i => (blk45Flag flags45_7 i.val).toFlag (wf45F_7 i) (mem45F_7 i))
    (by simp)

/-! ## The per-class coefficients through the sweep -/

private lemma coeff24 (row : List ℤ) (H : FlagWithSize TetraFree emptyType 6) :
    (∑ X ∈ Finset.univ.filter
        (fun X : FlagWithSize TetraFree pairType2.toModel 6 =>
          Flag.unlabel X = H),
      (∑ i : Fin 11, ∑ j : Fin 11,
          ((row.getD i.val 0 : ℤ) : ℝ) * ((row.getD j.val 0 : ℤ) : ℝ)
            * ((subflagPairDensity
                ((blk24Flag i.val).toFlag (wf24F i) (mem24F i))
                ((blk24Flag j.val).toFlag (wf24F j) (mem24F j))
                X : ℚ) : ℝ))
        * (labelingFactor (Quotient.out X).unlabel (Quotient.out X) : ℝ))
      = ((s24C row (repMask H) / 180 : ℚ) : ℝ) := by
  have h := fiberSum24_eq row wf24F mem24F (repMask_memT H)
  rw [toFlag_repMask H (repMask_memT H)] at h
  exact h

private lemma coeff45_0 (row : List ℤ)
    (H : FlagWithSize TetraFree emptyType 6) :
    (∑ X ∈ Finset.univ.filter
        (fun X : FlagWithSize TetraFree (rmType 0).toModel 6 =>
          Flag.unlabel X = H),
      (∑ i : Fin flags45_0.length, ∑ j : Fin flags45_0.length,
          ((row.getD i.val 0 : ℤ) : ℝ) * ((row.getD j.val 0 : ℤ) : ℝ)
            * ((subflagPairDensity
                ((blk45Flag flags45_0 i.val).toFlag
                  (wf45F_0 i) (mem45F_0 i))
                ((blk45Flag flags45_0 j.val).toFlag
                  (wf45F_0 j) (mem45F_0 j))
                X : ℚ) : ℝ))
        * (labelingFactor (Quotient.out X).unlabel (Quotient.out X) : ℝ))
      = ((s45C 0 flags45_0 row (repMask H) / 720 : ℚ) : ℝ) := by
  have h := fiberSum45_eq (rm := 0) flags45_0 row wf45F_0 mem45F_0
    flags45_0_lt (repMask_memT H)
  rw [toFlag_repMask H (repMask_memT H)] at h
  exact h

private lemma coeff45_1 (row : List ℤ)
    (H : FlagWithSize TetraFree emptyType 6) :
    (∑ X ∈ Finset.univ.filter
        (fun X : FlagWithSize TetraFree (rmType 1).toModel 6 =>
          Flag.unlabel X = H),
      (∑ i : Fin flags45_1.length, ∑ j : Fin flags45_1.length,
          ((row.getD i.val 0 : ℤ) : ℝ) * ((row.getD j.val 0 : ℤ) : ℝ)
            * ((subflagPairDensity
                ((blk45Flag flags45_1 i.val).toFlag
                  (wf45F_1 i) (mem45F_1 i))
                ((blk45Flag flags45_1 j.val).toFlag
                  (wf45F_1 j) (mem45F_1 j))
                X : ℚ) : ℝ))
        * (labelingFactor (Quotient.out X).unlabel (Quotient.out X) : ℝ))
      = ((s45C 1 flags45_1 row (repMask H) / 720 : ℚ) : ℝ) := by
  have h := fiberSum45_eq (rm := 1) flags45_1 row wf45F_1 mem45F_1
    flags45_1_lt (repMask_memT H)
  rw [toFlag_repMask H (repMask_memT H)] at h
  exact h

private lemma coeff45_3 (row : List ℤ)
    (H : FlagWithSize TetraFree emptyType 6) :
    (∑ X ∈ Finset.univ.filter
        (fun X : FlagWithSize TetraFree (rmType 3).toModel 6 =>
          Flag.unlabel X = H),
      (∑ i : Fin flags45_3.length, ∑ j : Fin flags45_3.length,
          ((row.getD i.val 0 : ℤ) : ℝ) * ((row.getD j.val 0 : ℤ) : ℝ)
            * ((subflagPairDensity
                ((blk45Flag flags45_3 i.val).toFlag
                  (wf45F_3 i) (mem45F_3 i))
                ((blk45Flag flags45_3 j.val).toFlag
                  (wf45F_3 j) (mem45F_3 j))
                X : ℚ) : ℝ))
        * (labelingFactor (Quotient.out X).unlabel (Quotient.out X) : ℝ))
      = ((s45C 3 flags45_3 row (repMask H) / 720 : ℚ) : ℝ) := by
  have h := fiberSum45_eq (rm := 3) flags45_3 row wf45F_3 mem45F_3
    flags45_3_lt (repMask_memT H)
  rw [toFlag_repMask H (repMask_memT H)] at h
  exact h

private lemma coeff45_7 (row : List ℤ)
    (H : FlagWithSize TetraFree emptyType 6) :
    (∑ X ∈ Finset.univ.filter
        (fun X : FlagWithSize TetraFree (rmType 7).toModel 6 =>
          Flag.unlabel X = H),
      (∑ i : Fin flags45_7.length, ∑ j : Fin flags45_7.length,
          ((row.getD i.val 0 : ℤ) : ℝ) * ((row.getD j.val 0 : ℤ) : ℝ)
            * ((subflagPairDensity
                ((blk45Flag flags45_7 i.val).toFlag
                  (wf45F_7 i) (mem45F_7 i))
                ((blk45Flag flags45_7 j.val).toFlag
                  (wf45F_7 j) (mem45F_7 j))
                X : ℚ) : ℝ))
        * (labelingFactor (Quotient.out X).unlabel (Quotient.out X) : ℝ))
      = ((s45C 7 flags45_7 row (repMask H) / 720 : ℚ) : ℝ) := by
  have h := fiberSum45_eq (rm := 7) flags45_7 row wf45F_7 mem45F_7
    flags45_7_lt (repMask_memT H)
  rw [toFlag_repMask H (repMask_memT H)] at h
  exact h

/-! ## The assembly -/

private lemma map_smul_sum {α : Type} (l : List α) (c : α → ℝ)
    (x : FlagAlgebra TetraFree emptyType) :
    (l.map fun a => c a • x).sum = (l.map c).sum • x := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons,
      add_smul]

private lemma map_cast_sum {α : Type} (l : List α) (f : α → ℚ) :
    (l.map fun a => ((f a : ℚ) : ℝ)).sum = (((l.map f).sum : ℚ) : ℝ) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons,
      Rat.cast_add]

private lemma map_div_sum {α : Type} (l : List α) (f : α → ℚ) (n : ℚ) :
    (l.map fun a => f a / n).sum = (l.map f).sum / n := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons,
      add_div]

/-- The block SOS element, expanded over the six-vertex classes with
the sweep-evaluated coefficients. -/
private lemma blockSOS_expand : blockSOS
    = ∑ H : FlagWithSize TetraFree emptyType 6,
        (((((s24C · (repMask H)) <$> facs24L).map (· / 180)).sum
          + (((s45C 0 flags45_0 · (repMask H)) <$> facs45_0L).map
              (· / 720)).sum
          + (((s45C 1 flags45_1 · (repMask H)) <$> facs45_1L).map
              (· / 720)).sum
          + (((s45C 3 flags45_3 · (repMask H)) <$> facs45_3L).map
              (· / 720)).sum
          + (((s45C 7 flags45_7 · (repMask H)) <$> facs45_7L).map
              (· / 720)).sum : ℚ) : ℝ) •
          (⟦basisVector (⟨6, H⟩ : FinFlag TetraFree emptyType)⟧
            : FlagAlgebra TetraFree emptyType) := by
  have hs : blockSOS
      = (facs24L.map fun row => downward (x24 row * x24 row)).sum
        + (facs45_0L.map fun row => downward (x45_0 row * x45_0 row)).sum
        + (facs45_1L.map fun row => downward (x45_1 row * x45_1 row)).sum
        + (facs45_3L.map fun row => downward (x45_3 row * x45_3 row)).sum
        + (facs45_7L.map fun row =>
            downward (x45_7 row * x45_7 row)).sum := rfl
  rw [hs,
    List.map_congr_left fun row (_ : row ∈ facs24L) => by
      rw [expand24 row,
        Finset.sum_congr rfl fun H (_ : H ∈ Finset.univ) => by
          rw [coeff24 row H]],
    List.map_congr_left fun row (_ : row ∈ facs45_0L) => by
      rw [expand45_0 row,
        Finset.sum_congr rfl fun H (_ : H ∈ Finset.univ) => by
          rw [coeff45_0 row H]],
    List.map_congr_left fun row (_ : row ∈ facs45_1L) => by
      rw [expand45_1 row,
        Finset.sum_congr rfl fun H (_ : H ∈ Finset.univ) => by
          rw [coeff45_1 row H]],
    List.map_congr_left fun row (_ : row ∈ facs45_3L) => by
      rw [expand45_3 row,
        Finset.sum_congr rfl fun H (_ : H ∈ Finset.univ) => by
          rw [coeff45_3 row H]],
    List.map_congr_left fun row (_ : row ∈ facs45_7L) => by
      rw [expand45_7 row,
        Finset.sum_congr rfl fun H (_ : H ∈ Finset.univ) => by
          rw [coeff45_7 row H]],
    sum_list_swap, sum_list_swap, sum_list_swap, sum_list_swap,
    sum_list_swap,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [map_smul_sum, map_smul_sum, map_smul_sum, map_smul_sum,
    map_smul_sum, ← add_smul, ← add_smul, ← add_smul, ← add_smul]
  have hc : ((facs24L.map fun row =>
        ((s24C row (repMask H) / 180 : ℚ) : ℝ)).sum
      + (facs45_0L.map fun row =>
          ((s45C 0 flags45_0 row (repMask H) / 720 : ℚ) : ℝ)).sum
      + (facs45_1L.map fun row =>
          ((s45C 1 flags45_1 row (repMask H) / 720 : ℚ) : ℝ)).sum
      + (facs45_3L.map fun row =>
          ((s45C 3 flags45_3 row (repMask H) / 720 : ℚ) : ℝ)).sum
      + (facs45_7L.map fun row =>
          ((s45C 7 flags45_7 row (repMask H) / 720 : ℚ) : ℝ)).sum)
      = ((((((s24C · (repMask H)) <$> facs24L).map (· / 180)).sum
          + (((s45C 0 flags45_0 · (repMask H)) <$> facs45_0L).map
              (· / 720)).sum
          + (((s45C 1 flags45_1 · (repMask H)) <$> facs45_1L).map
              (· / 720)).sum
          + (((s45C 3 flags45_3 · (repMask H)) <$> facs45_3L).map
              (· / 720)).sum
          + (((s45C 7 flags45_7 · (repMask H)) <$> facs45_7L).map
              (· / 720)).sum : ℚ)) : ℝ) := by
    rw [map_cast_sum, map_cast_sum, map_cast_sum, map_cast_sum,
      map_cast_sum]
    push_cast
    rfl
  rw [hc]

/-- **The block element is the scaled SOS element.** -/
theorem blockElt6_eq_smul_SOS :
    blockElt6 = ((1 : ℝ) / 10000000000) • blockSOS := by
  have helt : blockElt6 = ∑ H : FlagWithSize TetraFree emptyType 6,
      ((blockNumOf H / 7200000000000 : ℚ) : ℝ) •
        (⟦basisVector (⟨6, H⟩ : FinFlag TetraFree emptyType)⟧
          : FlagAlgebra TetraFree emptyType) := rfl
  rw [helt, blockSOS_expand, Finset.smul_sum]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [smul_smul]
  have hbn : blockNumOf H = 4 * blockValue24 (repMask H)
      + blockValue45 (repMask H) := rfl
  have h24 : (blockValue24 (repMask H) : ℚ) = S24C (repMask H) :=
    blockValue24_eq_of_mem (repMask_mem H)
  have h45 : (blockValue45 (repMask H) : ℚ) = S45C (repMask H) :=
    blockValue45_eq_of_mem (repMask_mem H)
  have hS24 : S24C (repMask H)
      = ((s24C · (repMask H)) <$> facs24L).sum := rfl
  have hS45 : S45C (repMask H)
      = ((s45C 0 flags45_0 · (repMask H)) <$> facs45_0L).sum
        + ((s45C 1 flags45_1 · (repMask H)) <$> facs45_1L).sum
        + ((s45C 3 flags45_3 · (repMask H)) <$> facs45_3L).sum
        + ((s45C 7 flags45_7 · (repMask H)) <$> facs45_7L).sum := rfl
  have hcoeff : (blockNumOf H / 7200000000000 : ℚ)
      = (1 / 10000000000 : ℚ)
        * ((((s24C · (repMask H)) <$> facs24L).map (· / 180)).sum
          + (((s45C 0 flags45_0 · (repMask H)) <$> facs45_0L).map
              (· / 720)).sum
          + (((s45C 1 flags45_1 · (repMask H)) <$> facs45_1L).map
              (· / 720)).sum
          + (((s45C 3 flags45_3 · (repMask H)) <$> facs45_3L).map
              (· / 720)).sum
          + (((s45C 7 flags45_7 · (repMask H)) <$> facs45_7L).map
              (· / 720)).sum) := by
    rw [map_div_sum, map_div_sum, map_div_sum, map_div_sum, map_div_sum]
    simp only [List.map_id']
    rw [hbn]
    push_cast
    rw [h24, h45, hS24, hS45]
    ring
  rw [show ((blockNumOf H / 7200000000000 : ℚ) : ℝ)
      = ((1 / 10000000000 : ℚ) : ℝ)
        * ((((((s24C · (repMask H)) <$> facs24L).map (· / 180)).sum
          + (((s45C 0 flags45_0 · (repMask H)) <$> facs45_0L).map
              (· / 720)).sum
          + (((s45C 1 flags45_1 · (repMask H)) <$> facs45_1L).map
              (· / 720)).sum
          + (((s45C 3 flags45_3 · (repMask H)) <$> facs45_3L).map
              (· / 720)).sum
          + (((s45C 7 flags45_7 · (repMask H)) <$> facs45_7L).map
              (· / 720)).sum : ℚ)) : ℝ) from by
    rw [← Rat.cast_mul]
    exact congrArg _ hcoeff]
  rw [show ((1 / 10000000000 : ℚ) : ℝ) = ((1 : ℝ) / 10000000000) from by
    norm_num]

/-- **The block element is nonnegative** — the order-6 semidefinite part
of the certificate is discharged. -/
theorem blockElt6_nonneg :
    (0 : FlagAlgebra TetraFree emptyType) ≤ blockElt6 := by
  rw [blockElt6_eq_smul_SOS]
  exact smul_nonneg_of_nonneg (by norm_num) blockSOS_nonneg

end FlagAlgebras.Core.Tetrahedron
