import LeanFlagAlgebras.Core.Expand
import LeanFlagAlgebras.Core.SquarePositivity
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Ext56
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootFlags

/-! # The five-root sum of downward squares

The eighteen active types have different flag dimensions and numbers of rows.
Dependent finite indices retain all labeled flags within each type. No
projection onto automorphism-invariant row vectors is used.
-/

namespace FlagAlgebras.Core.Tetrahedron.FullSevenLong

open FlagAlgebras.Core Classical

lemma wfS5F (b : Fin 18) (i : Fin (s5Dim b)) :
    (s5Flag b i.val).WellFormed (s5Type b) :=
  s5Flag_wf b i.val i.isLt

lemma memS5F (b : Fin 18) (i : Fin (s5Dim b)) :
    TetraFree.Mem (s5Flag b i.val).graph.toModel :=
  s5Flag_mem b i.isLt

/-- The rational coefficients of one integer factor row. -/
def cS5 (b : Fin 18) (r : Fin (s5Rows b)) (i : Fin (s5Dim b)) : ℚ :=
  (fS5 b r.val i.val : ℚ)

/-- One six-vertex flag expression over a five-vertex type. -/
noncomputable def xS5 (b : Fin 18) (r : Fin (s5Rows b)) :
    FlagAlgebra TetraFree (s5Type b).toModel :=
  ∑ i : Fin (s5Dim b), (cS5 b r i : ℝ) •
    ⟦basisVector ⟨6, (s5Flag b i.val).toFlag (wfS5F b i) (memS5F b i)⟩⟧

/-- All 360 active five-root rows, before division by the factor scale. -/
noncomputable def fiveRootSOS : FlagAlgebra TetraFree emptyType :=
  ∑ b : Fin 18, ∑ r : Fin (s5Rows b), downward (xS5 b r * xS5 b r)

theorem fiveRootSOS_nonneg :
    (0 : FlagAlgebra TetraFree emptyType) ≤ fiveRootSOS := by
  exact sum_nonneg' fun b _ => sum_nonneg' fun r _ => downward_square_nonneg _

/-- The labeling-weighted coefficient of a single downward square. -/
noncomputable def gammaS5 (b : Fin 18) (r : Fin (s5Rows b))
    (H : FlagWithSize TetraFree emptyType 7) : ℝ :=
  ∑ X ∈ Finset.univ.filter
      (fun X : FlagWithSize TetraFree (s5Type b).toModel 7 => Flag.unlabel X = H),
    (∑ i : Fin (s5Dim b), ∑ j : Fin (s5Dim b),
      (cS5 b r i : ℝ) * (cS5 b r j : ℝ) *
        ((subflagPairDensity
          ((s5Flag b i.val).toFlag (wfS5F b i) (memS5F b i))
          ((s5Flag b j.val).toFlag (wfS5F b j) (memS5F b j)) X : ℚ) : ℝ)) *
      (labelingFactor (Quotient.out X).unlabel (Quotient.out X) : ℝ)

/-- Expand one actual factor row at the seven-vertex level. -/
lemma expandS5 (b : Fin 18) (r : Fin (s5Rows b)) :
    downward (xS5 b r * xS5 b r) =
      ∑ H : FlagWithSize TetraFree emptyType 7,
        gammaS5 b r H • ⟦basisVector ⟨7, H⟩⟧ := by
  exact downward_linear_sq (fun i : Fin (s5Dim b) => (cS5 b r i : ℝ))
    (fun i => (s5Flag b i.val).toFlag (wfS5F b i) (memS5F b i)) (by simp)

/-- The coefficient at any literal host is its ordered five-root sum. -/
lemma gammaS5_toFlag (b : Fin 18) (r : Fin (s5Rows b))
    {G : Sym3Graph 7} (hG : TetraFree.Mem G.toModel) :
    gammaS5 b r (G.toFlag hG) = (1 / 5040 : ℝ) *
      ∑ θ ∈ rootingsOf (s5Type b) G,
        (extPairSum56 (cS5 b r) (fun i : Fin (s5Dim b) => s5Flag b i.val) G θ : ℝ) := by
  exact gamma56_eq_rooting5040 (cS5 b r)
    (fun i : Fin (s5Dim b) => s5Flag b i.val) (wfS5F b) (memS5F b) hG

/-- Regroup all rows by their seven-vertex coefficient. -/
lemma fiveRootSOS_expand : fiveRootSOS =
    ∑ H : FlagWithSize TetraFree emptyType 7,
      (∑ b : Fin 18, ∑ r : Fin (s5Rows b), gammaS5 b r H) •
        ⟦basisVector ⟨7, H⟩⟧ := by
  change (∑ b : Fin 18, ∑ r : Fin (s5Rows b), downward (xS5 b r * xS5 b r)) = _
  simp_rw [expandS5]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => Finset.sum_comm,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_smul]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
/-- Convert any exact integer ordered-root numerator into its SOS coefficient.
The representative and numerator assumptions are explicit, so this algebraic
step is checked independently of the exhaustive bound and evaluator modules. -/
lemma fiveRootScaledCoeff_of_ordered_sum
    (H : FlagWithSize TetraFree emptyType 7) (w : ℕ)
    (hw : TetraFree.Mem (graphOfMask 7 w).toModel)
    (hrep : (graphOfMask 7 w).toFlag hw = H) (num : ℤ)
    (hnum : (num : ℚ) = ∑ b : Fin 18, ∑ r : Fin (s5Rows b),
      ∑ θ ∈ rootingsOf (s5Type b) (graphOfMask 7 w),
        extPairSum56 (cS5 b r) (fun i : Fin (s5Dim b) => s5Flag b i.val)
          (graphOfMask 7 w) θ) :
    (((num : ℚ) / 20160000000000000 : ℚ) : ℝ) =
      (1 / 4000000000000 : ℝ) * ∑ b : Fin 18, ∑ r : Fin (s5Rows b), gammaS5 b r H := by
  have hnumR : (num : ℝ) = ∑ b : Fin 18, ∑ r : Fin (s5Rows b),
      ∑ θ ∈ rootingsOf (s5Type b) (graphOfMask 7 w),
        (extPairSum56 (cS5 b r) (fun i : Fin (s5Dim b) => s5Flag b i.val)
          (graphOfMask 7 w) θ : ℝ) := by
    exact_mod_cast hnum
  have hgamma : ∀ (b : Fin 18) (r : Fin (s5Rows b)), gammaS5 b r H =
      (1 / 5040 : ℝ) * ∑ θ ∈ rootingsOf (s5Type b) (graphOfMask 7 w),
        (extPairSum56 (cS5 b r) (fun i : Fin (s5Dim b) => s5Flag b i.val)
          (graphOfMask 7 w) θ : ℝ) := by
    intro b r
    have h := gammaS5_toFlag b r hw
    rw [hrep] at h
    exact h
  have htotal : (∑ b : Fin 18, ∑ r : Fin (s5Rows b), gammaS5 b r H) =
      (1 / 5040 : ℝ) * (num : ℝ) := by
    rw [hnumR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => hgamma b r
  rw [htotal]
  push_cast
  ring

end FlagAlgebras.Core.Tetrahedron.FullSevenLong
