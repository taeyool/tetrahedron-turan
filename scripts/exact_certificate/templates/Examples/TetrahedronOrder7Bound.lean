import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Verified

/-! # What the verified column bound says as a number

The sweep bounds an integer, the column value over the common
denominator `5040 * scale ^ 2`. This file records the rational number it
amounts to and compares it with the published record, so the arithmetic
of the final claim is fixed independently of the algebraic assembly still
to come.

The verified column bound is `28208330834196 / 50400000000000`, which
reduces to `2350694236183 / 4200000000000`, about `0.5596891`. The best
published bound on the tetrahedron Turán density is `1123 / 2000`, that
is `0.5615`; the gap is `0.0018108...`, so the certificate's value is the
smaller of the two by a clear margin.

Everything here is exact rational arithmetic and kernel-checked. -/

namespace FlagAlgebras.Core.Tetrahedron

/-- The denominator the column values are taken over: `5040 * scale ^ 2`. -/
def columnDenom : ℚ := 50400000000000

/-- The bound on the edge density that the verified sweep delivers. -/
def certBound : ℚ := (columnBound : ℚ) / columnDenom

/-- The best published bound on the tetrahedron Turán density. -/
def publishedBound : ℚ := 1123 / 2000

/-- The certificate's bound in lowest terms. -/
lemma certBound_eq : certBound = 2350694236183 / 4200000000000 := by
  unfold certBound columnDenom columnBound
  norm_num

/-- **The certificate's bound is below the published record.** -/
theorem certBound_lt_published : certBound < publishedBound := by
  rw [certBound_eq, publishedBound]
  norm_num

/-- The exact margin. -/
lemma published_sub_certBound :
    publishedBound - certBound = 7605763817 / 4200000000000 := by
  rw [certBound_eq, publishedBound]
  norm_num

/-- The bound is above `5/9`, the density of the iterated blow-up
construction that is conjectured to be extremal. -/
theorem five_ninths_lt_certBound : (5 : ℚ) / 9 < certBound := by
  rw [certBound_eq]
  norm_num

end FlagAlgebras.Core.Tetrahedron
