"""Structural extensions of the old-family Lean proof templates.

Numeric literals retain the original template values here. The main generator
substitutes the selected certificate's scale and factors afterwards.
"""
import re


def extend_template(name, text):
    if name == "TetrahedronOrder7Reduce":
        text = text.replace("noncomputable def rootCoeff", "noncomputable def oldRootCoeff", 1)
        start = text.index("lemma columnCoeff_split")
        end = text.index("/-! ## The elements", start)
        text = text[:start] + '''/-- The five-root contribution, with the ordered-root denominator. -/
noncomputable def fiveRootCoeff (H : FlagWithSize TetraFree emptyType 7) : ℚ :=
  (s5ColumnNum (boundedRep H) : ℚ) / columnDenom

/-- All order-seven rooted families. -/
noncomputable def rootCoeff (H : FlagWithSize TetraFree emptyType 7) : ℚ :=
  oldRootCoeff H + fiveRootCoeff H

lemma columnCoeff_split (H : FlagWithSize TetraFree emptyType 7) :
    columnCoeff H = deckCoeff H + rootCoeff H := by
  have hv : columnValue (boundedRep H)
      = deckValue (boundedRep H) + 36 * s1Value (boundedRep H)
        + 4 * s3Value (boundedRep H) + s5ColumnNum (boundedRep H) := rfl
  show (columnValue (boundedRep H) : ℚ) / columnDenom
    = (deckValue (boundedRep H) : ℚ) / columnDenom
      + (((36 * s1Value (boundedRep H) + 4 * s3Value (boundedRep H) : ℤ) : ℚ)
          / columnDenom + (s5ColumnNum (boundedRep H) : ℚ) / columnDenom)
  rw [hv]
  push_cast
  ring

''' + text[end:]
        pos = text.index("/-- The order-6 certificate element")
        text = text[:pos] + '''/-- The previously established one-root and three-root contribution. -/
noncomputable def oldRootElt : FlagAlgebra TetraFree emptyType :=
  ∑ H : FlagWithSize TetraFree emptyType 7,
    (oldRootCoeff H : ℝ) •
      ⟦basisVector (⟨7, H⟩ : FinFlag TetraFree emptyType)⟧

/-- The new five-root contribution. -/
noncomputable def fiveRootElt : FlagAlgebra TetraFree emptyType :=
  ∑ H : FlagWithSize TetraFree emptyType 7,
    (fiveRootCoeff H : ℝ) •
      ⟦basisVector (⟨7, H⟩ : FinFlag TetraFree emptyType)⟧

lemma rootElt_split : rootElt = oldRootElt + fiveRootElt := by
  change (∑ H : FlagWithSize TetraFree emptyType 7,
    ((oldRootCoeff H + fiveRootCoeff H : ℚ) : ℝ) •
      (⟦basisVector (⟨7, H⟩ : FinFlag TetraFree emptyType)⟧
        : FlagAlgebra TetraFree emptyType)) = _
  simp only [Rat.cast_add, add_smul, Finset.sum_add_distrib]
  rfl

''' + text[pos:]
        text = text.replace("/-- The rooted element: the order-7 one-root and three-root forms. -/",
                            "/-- The rooted element: all active one-, three-, and five-root forms. -/")
    if name == "TetrahedronOrder7RootSOS":
        text = "import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootSOS\n" + text
        text = re.sub(r"\brootSOS\b", "oldRootSOS", text)
        text = text.replace("theorem rootSOS_nonneg", "theorem oldRootSOS_nonneg")
        pos = text.index("end FlagAlgebras.Core.Tetrahedron")
        text = text[:pos] + '''/-- The complete order-seven SOS, including all active five-root types. -/
noncomputable def rootSOS : FlagAlgebra TetraFree emptyType :=
  oldRootSOS + fiveRootSOS

theorem rootSOS_nonneg : (0 : FlagAlgebra TetraFree emptyType) ≤ rootSOS := by
  intro φ
  have h₁ := oldRootSOS_nonneg φ
  have h₂ := fiveRootSOS_nonneg φ
  rw [sub_zero] at h₁ h₂ ⊢
  change 0 ≤ φ (oldRootSOS + fiveRootSOS)
  rw [PositiveHom.map_add]
  linarith

''' + text[pos:]
    if name == "TetrahedronOrder7RootScaled":
        text = "import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootExpand\n" + text
        start = text.index("theorem isRootScaled")
        end = text.index("/-! ## The unconditional consequences", start)
        old = text[start:end]
        old = old.replace("theorem isRootScaled : IsRootScaled := by",
            "theorem oldRootElt_eq_scaled :\n    oldRootElt = ((1 : ℝ) / 10000000000) • oldRootSOS := by")
        for src, dst in [("rootElt", "oldRootElt"), ("rootSOS", "oldRootSOS"),
                         ("rootCoeff", "oldRootCoeff")]:
            old = re.sub(r"\b" + src + r"\b", dst, old)
        text = text[:start] + old + '''/-- The full coefficient identity, including the five-root families. -/
theorem isRootScaled : IsRootScaled := by
  show rootElt = ((1 : ℝ) / 10000000000) • rootSOS
  rw [rootElt_split, oldRootElt_eq_scaled, fiveRootElt_eq_scaled]
  exact (smul_add _ oldRootSOS fiveRootSOS).symm

''' + text[end:]
    return text
