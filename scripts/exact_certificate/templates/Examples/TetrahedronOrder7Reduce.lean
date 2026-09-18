import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7ClassNum
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Slack

/-! # Reducing the expansion identity to its parts

The expansion identity says `certBound • 1` decomposes as the edge plus
a semidefinite part plus the stationarity multiple plus the remainder.
This file performs the reductions that need no new mathematics:

* the bound splits off the remainder, leaving the column element — one
  coefficient per seven-vertex class, the certificate's column over the
  common denominator (`certBound_smul_one`);
* the column element splits into its deck part and its rooted part;
* the deck part **is** the order-6 certificate element: the chain rule
  turns the per-class deck sum into the level-7 expansion of the class
  numbers over their own denominator (`deckElt_eq_certElt6`).

What remains after this file is the order-6 element's own decomposition
(edge, blocks, stationarity — its definition as `classNum`) and the
identification of the rooted part with the order-7 squares.

PROOF-ENGINEERING NOTE. The coefficients here contain `columnValue`,
`deckValue`, `classNums` — computable functions over million-entry
tables, applied to `choose`-terms they cannot reduce on. Any tactic that
attempts a definitional-equality check across a *mismatched* pair of
such terms (`congr`, `unfold` on the defs, `rw` with a def name) sends
the kernel into evaluating the tables and blows the recursion limit.
Every proof below therefore expands definitions only through explicit
`show`/`rfl`-equations and rewrites with stated lemmas. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

open Classical

/-! ## The per-class coefficients -/

/-- The certificate column of a seven-vertex class, over the common
denominator. -/
noncomputable def columnCoeff (H : FlagWithSize TetraFree emptyType 7) : ℚ :=
  (columnValue (boundedRep H) : ℚ) / columnDenom

/-- Its deck part. -/
noncomputable def deckCoeff (H : FlagWithSize TetraFree emptyType 7) : ℚ :=
  (deckValue (boundedRep H) : ℚ) / columnDenom

/-- Its rooted part: the order-7 one-root and three-root forms. -/
noncomputable def rootCoeff (H : FlagWithSize TetraFree emptyType 7) : ℚ :=
  ((36 * s1Value (boundedRep H) + 4 * s3Value (boundedRep H) : ℤ) : ℚ)
    / columnDenom

lemma columnCoeff_split (H : FlagWithSize TetraFree emptyType 7) :
    columnCoeff H = deckCoeff H + rootCoeff H := by
  have hnum : (columnValue (boundedRep H) : ℚ)
      = (deckValue (boundedRep H) : ℚ)
        + ((36 * s1Value (boundedRep H) + 4 * s3Value (boundedRep H) : ℤ)
            : ℚ) := by
    have h : columnValue (boundedRep H)
        = deckValue (boundedRep H) + 36 * s1Value (boundedRep H)
          + 4 * s3Value (boundedRep H) := rfl
    rw [h]
    push_cast
    ring
  show (columnValue (boundedRep H) : ℚ) / columnDenom
    = (deckValue (boundedRep H) : ℚ) / columnDenom
      + ((36 * s1Value (boundedRep H) + 4 * s3Value (boundedRep H) : ℤ) : ℚ)
          / columnDenom
  rw [hnum, add_div]

/-! ## The elements -/

/-- The column element: the certificate's per-class column values. -/
noncomputable def columnElt : FlagAlgebra TetraFree emptyType :=
  ∑ H : FlagWithSize TetraFree emptyType 7,
    (columnCoeff H : ℝ) •
      ⟦basisVector (⟨7, H⟩ : FinFlag TetraFree emptyType)⟧

/-- The rooted element: the order-7 one-root and three-root forms. -/
noncomputable def rootElt : FlagAlgebra TetraFree emptyType :=
  ∑ H : FlagWithSize TetraFree emptyType 7,
    (rootCoeff H : ℝ) •
      ⟦basisVector (⟨7, H⟩ : FinFlag TetraFree emptyType)⟧

/-- The order-6 certificate element: each class number over its own
denominator `720 * scale ^ 2`. -/
noncomputable def certElt6 : FlagAlgebra TetraFree emptyType :=
  ∑ H : FlagWithSize TetraFree emptyType 6,
    ((classNumOf H / 7200000000000 : ℚ) : ℝ) •
      ⟦basisVector (⟨6, H⟩ : FinFlag TetraFree emptyType)⟧

/-! ## The bound splits off the remainder -/

/-- The verified sweep, as an identity of elements: the bound is the
column element plus the (nonnegative) remainder. -/
theorem certBound_smul_one :
    ((certBound : ℚ) : ℝ) • (1 : FlagAlgebra TetraFree emptyType)
      = columnElt + remainder7 := by
  have hcol : columnElt = ∑ H : FlagWithSize TetraFree emptyType 7,
      (columnCoeff H : ℝ) •
        (⟦basisVector (⟨7, H⟩ : FinFlag TetraFree emptyType)⟧
          : FlagAlgebra TetraFree emptyType) := rfl
  have hrem : remainder7 = ∑ H : FlagWithSize TetraFree emptyType 7,
      slack7 H •
        (⟦basisVector (⟨7, H⟩ : FinFlag TetraFree emptyType)⟧
          : FlagAlgebra TetraFree emptyType) := rfl
  rw [← sum_flagWithSize_eq_one (𝕋 := TetraFree) (σ := emptyType) 7 (by simp),
    Finset.smul_sum, hcol, hrem, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun H _ => ?_
  have hc : ((certBound : ℚ) : ℝ) = (columnCoeff H : ℝ) + slack7 H := by
    have h1 : columnCoeff H
        = (columnValue (boundedRep H) : ℚ) / columnDenom := rfl
    have h2 : slack7 H
        = ((columnBound - columnValue (boundedRep H) : ℤ) : ℝ)
            / ((columnDenom : ℚ) : ℝ) := rfl
    have h3 : certBound = (columnBound : ℚ) / columnDenom := rfl
    have h4 : columnDenom = (50400000000000 : ℚ) := rfl
    rw [h1, h2, h3, h4]
    push_cast
    ring
  rw [hc, add_smul]

/-! ## The deck part is the order-6 element -/

lemma deckCoeff_eq_sum (H : FlagWithSize TetraFree emptyType 7) :
    deckCoeff H
      = ∑ H₆ : FlagWithSize TetraFree emptyType 6,
          (classNumOf H₆ / 7200000000000) * subflagDensity H₆ H := by
  have hm := boundedRep_mem H
  have hk4 : k4FreeMask (quadIdxList 7) (boundedRep H) = true :=
    k4FreeMask_iff_mem.mpr hm
  have h := deckValue_eq_expansion hk4 hm
  simp only [toFlag_boundedRep H hm] at h
  show (deckValue (boundedRep H) : ℚ) / columnDenom = _
  rw [h,
    show (columnDenom : ℚ) = 7 * 7200000000000 from by
      rw [show columnDenom = (50400000000000 : ℚ) from rfl]; norm_num,
    mul_div_mul_left _ _ (by norm_num : (7 : ℚ) ≠ 0), Finset.sum_div]
  exact Finset.sum_congr rfl fun H₆ _ => by ring

/-- **The deck element is the order-6 certificate element**: expanding
each six-vertex class over the seven-vertex classes recovers exactly the
per-class deck coefficients. -/
theorem deckElt_eq_certElt6 :
    (∑ H : FlagWithSize TetraFree emptyType 7,
        (deckCoeff H : ℝ) •
          (⟦basisVector (⟨7, H⟩ : FinFlag TetraFree emptyType)⟧
            : FlagAlgebra TetraFree emptyType))
      = certElt6 := by
  have hexp : ∀ H₆ : FlagWithSize TetraFree emptyType 6,
      ((classNumOf H₆ / 7200000000000 : ℚ) : ℝ) •
          (⟦basisVector (⟨6, H₆⟩ : FinFlag TetraFree emptyType)⟧
            : FlagAlgebra TetraFree emptyType)
        = ∑ H : FlagWithSize TetraFree emptyType 7,
            (((classNumOf H₆ / 7200000000000) * subflagDensity H₆ H : ℚ) : ℝ) •
              ⟦basisVector (⟨7, H⟩ : FinFlag TetraFree emptyType)⟧ := by
    intro H₆
    rw [basisVector_quot_eq_sum (⟨6, H₆⟩ : FinFlag TetraFree emptyType) 7
      (by norm_num), Finset.smul_sum]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [smul_smul, ← Rat.cast_mul]
  have hcert : certElt6 = ∑ H₆ : FlagWithSize TetraFree emptyType 6,
      ((classNumOf H₆ / 7200000000000 : ℚ) : ℝ) •
        (⟦basisVector (⟨6, H₆⟩ : FinFlag TetraFree emptyType)⟧
          : FlagAlgebra TetraFree emptyType) := rfl
  rw [hcert, Finset.sum_congr rfl fun H₆ _ => hexp H₆, Finset.sum_comm]
  refine Finset.sum_congr rfl fun H _ => ?_
  have hc : ((deckCoeff H : ℚ) : ℝ)
      = ∑ H₆ : FlagWithSize TetraFree emptyType 6,
          (((classNumOf H₆ / 7200000000000) * subflagDensity H₆ H : ℚ) : ℝ) := by
    rw [deckCoeff_eq_sum]
    exact Rat.cast_sum _ _
  rw [← Finset.sum_smul, hc]

/-- The column element splits into the order-6 element and the rooted
part. -/
theorem columnElt_split : columnElt = certElt6 + rootElt := by
  rw [← deckElt_eq_certElt6]
  have hcol : columnElt = ∑ H : FlagWithSize TetraFree emptyType 7,
      (columnCoeff H : ℝ) •
        (⟦basisVector (⟨7, H⟩ : FinFlag TetraFree emptyType)⟧
          : FlagAlgebra TetraFree emptyType) := rfl
  have hroot : rootElt = ∑ H : FlagWithSize TetraFree emptyType 7,
      (rootCoeff H : ℝ) •
        (⟦basisVector (⟨7, H⟩ : FinFlag TetraFree emptyType)⟧
          : FlagAlgebra TetraFree emptyType) := rfl
  rw [hcol, hroot, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun H _ => ?_
  have hc : ((columnCoeff H : ℚ) : ℝ)
      = ((deckCoeff H : ℚ) : ℝ) + ((rootCoeff H : ℚ) : ℝ) := by
    rw [columnCoeff_split]
    exact Rat.cast_add _ _
  rw [hc, add_smul]

/-- **The reduction**: the bound is the order-6 certificate element plus
the order-7 rooted element plus the remainder. -/
theorem certBound_one_split :
    ((certBound : ℚ) : ℝ) • (1 : FlagAlgebra TetraFree emptyType)
      = certElt6 + rootElt + remainder7 := by
  rw [certBound_smul_one, columnElt_split]

end FlagAlgebras.Core.Tetrahedron
