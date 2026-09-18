import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7RootSOS
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7ExtS1
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7ExtS3
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Slack

/-! # Expanding the root SOS element over the seven-vertex classes

Each downward square of `rootSOS` expands, by `downward_linear_sq` at
level seven, into a sum over the seven-vertex classes whose coefficient
is the labeling-weighted fiber sum of the row's quadratic form. This
file records those expansions and evaluates each fiber sum at the
class's chosen mask representative through the fiber identities — the
level-7 mirror of the order-6 coefficient lemmas.

What is left after this is the numeric side: matching those rooting
sums against the certificate's folds. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

open Classical

/-! ## The per-row expansions -/

lemma expandS1 (r : ℕ) :
    downward (xS1 r * xS1 r)
      = ∑ H : FlagWithSize TetraFree emptyType 7,
          (∑ X ∈ Finset.univ.filter
              (fun X : FlagWithSize TetraFree vertexGraph.toModel 7 =>
                Flag.unlabel X = H),
            (∑ i : Fin 7, ∑ j : Fin 7,
                ((fS1 r i.val : ℤ) : ℝ) * ((fS1 r j.val : ℤ) : ℝ)
                  * ((subflagPairDensity
                      ((s1Flag i.val).toFlag (wfS1F i) (memS1F i))
                      ((s1Flag j.val).toFlag (wfS1F j) (memS1F j))
                      X : ℚ) : ℝ))
              * (labelingFactor (Quotient.out X).unlabel
                  (Quotient.out X) : ℝ)) •
            ⟦basisVector ⟨7, H⟩⟧ := by
  have hx : xS1 r = ∑ i : Fin 7, ((fS1 r i.val : ℤ) : ℝ) •
      ⟦basisVector ⟨4, (s1Flag i.val).toFlag (wfS1F i) (memS1F i)⟩⟧ := rfl
  rw [hx]
  exact downward_linear_sq
    (fun i : Fin 7 => ((fS1 r i.val : ℤ) : ℝ))
    (fun i => (s1Flag i.val).toFlag (wfS1F i) (memS1F i))
    (by simp)

lemma expandS30 (r : ℕ) :
    downward (xS30 r * xS30 r)
      = ∑ H : FlagWithSize TetraFree emptyType 7,
          (∑ X ∈ Finset.univ.filter
              (fun X : FlagWithSize TetraFree (s3Type 0).toModel 7 =>
                Flag.unlabel X = H),
            (∑ i : Fin 236, ∑ j : Fin 236,
                ((fS30 r i.val : ℤ) : ℝ) * ((fS30 r j.val : ℤ) : ℝ)
                  * ((subflagPairDensity
                      ((s30Flag i.val).toFlag (wfS30F i) (memS30F i))
                      ((s30Flag j.val).toFlag (wfS30F j) (memS30F j))
                      X : ℚ) : ℝ))
              * (labelingFactor (Quotient.out X).unlabel
                  (Quotient.out X) : ℝ)) •
            ⟦basisVector ⟨7, H⟩⟧ := by
  have hx : xS30 r = ∑ i : Fin 236, ((fS30 r i.val : ℤ) : ℝ) •
      ⟦basisVector ⟨5, (s30Flag i.val).toFlag (wfS30F i) (memS30F i)⟩⟧ :=
    rfl
  rw [hx]
  exact downward_linear_sq
    (fun i : Fin 236 => ((fS30 r i.val : ℤ) : ℝ))
    (fun i => (s30Flag i.val).toFlag (wfS30F i) (memS30F i))
    (by simp)

lemma expandS31 (r : ℕ) :
    downward (xS31 r * xS31 r)
      = ∑ H : FlagWithSize TetraFree emptyType 7,
          (∑ X ∈ Finset.univ.filter
              (fun X : FlagWithSize TetraFree (s3Type 1).toModel 7 =>
                Flag.unlabel X = H),
            (∑ i : Fin 191, ∑ j : Fin 191,
                ((fS31 r i.val : ℤ) : ℝ) * ((fS31 r j.val : ℤ) : ℝ)
                  * ((subflagPairDensity
                      ((s31Flag i.val).toFlag (wfS31F i) (memS31F i))
                      ((s31Flag j.val).toFlag (wfS31F j) (memS31F j))
                      X : ℚ) : ℝ))
              * (labelingFactor (Quotient.out X).unlabel
                  (Quotient.out X) : ℝ)) •
            ⟦basisVector ⟨7, H⟩⟧ := by
  have hx : xS31 r = ∑ i : Fin 191, ((fS31 r i.val : ℤ) : ℝ) •
      ⟦basisVector ⟨5, (s31Flag i.val).toFlag (wfS31F i) (memS31F i)⟩⟧ :=
    rfl
  rw [hx]
  exact downward_linear_sq
    (fun i : Fin 191 => ((fS31 r i.val : ℤ) : ℝ))
    (fun i => (s31Flag i.val).toFlag (wfS31F i) (memS31F i))
    (by simp)

/-! ## The coefficients at a class representative

Each fiber sum, evaluated at the mask the coverage theorem chose for a
class, is the rooting average of the outside-witness weight products.
These are the fiber identities instantiated at the certificate's factor
rows. -/

lemma coeffS1 (r : ℕ) (H : FlagWithSize TetraFree emptyType 7) :
    (∑ X ∈ Finset.univ.filter
        (fun X : FlagWithSize TetraFree vertexGraph.toModel 7 =>
          Flag.unlabel X = H),
      (∑ i : Fin 7, ∑ j : Fin 7,
          ((fS1 r i.val : ℤ) : ℝ) * ((fS1 r j.val : ℤ) : ℝ)
            * ((subflagPairDensity
                ((s1Flag i.val).toFlag (wfS1F i) (memS1F i))
                ((s1Flag j.val).toFlag (wfS1F j) (memS1F j))
                X : ℚ) : ℝ))
        * (labelingFactor (Quotient.out X).unlabel (Quotient.out X) : ℝ))
      = (1 / 7 : ℝ) * ∑ θ ∈ rootingsOf vertexGraph
            (graphOfMask 7 (boundedRep H)),
          ((((∑ p ∈ outsideTriples θ,
              (∑ i : Fin 7, ((fS1 r i.val : ℤ) : ℚ)
                  * (if (s1Flag i.val).IsIso (extFlagS1
                      (graphOfMask 7 (boundedRep H)) θ
                      p.1.1 p.1.2.1 p.1.2.2) then 1 else 0))
                * (∑ j : Fin 7, ((fS1 r j.val : ℤ) : ℚ)
                    * (if (s1Flag j.val).IsIso (extFlagS1
                        (graphOfMask 7 (boundedRep H)) θ
                        p.2.1 p.2.2.1 p.2.2.2) then 1 else 0)))
              / 20 : ℚ)) : ℝ) := by
  have hcast : ∀ i : Fin 7,
      ((fS1 r i.val : ℤ) : ℝ) = (((fS1 r i.val : ℤ) : ℚ) : ℝ) :=
    fun i => by push_cast; rfl
  have h := gammaS1_eq_rooting
    (fun i : Fin 7 => ((fS1 r i.val : ℤ) : ℚ))
    (fun i => s1Flag i.val) wfS1F memS1F (boundedRep_mem H)
  rw [toFlag_boundedRep H (boundedRep_mem H)] at h
  rw [Finset.sum_congr rfl fun X _ => by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by
        rw [hcast i, hcast j]]]
  exact h

lemma coeffS30 (r : ℕ) (H : FlagWithSize TetraFree emptyType 7) :
    (∑ X ∈ Finset.univ.filter
        (fun X : FlagWithSize TetraFree (s3Type 0).toModel 7 =>
          Flag.unlabel X = H),
      (∑ i : Fin 236, ∑ j : Fin 236,
          ((fS30 r i.val : ℤ) : ℝ) * ((fS30 r j.val : ℤ) : ℝ)
            * ((subflagPairDensity
                ((s30Flag i.val).toFlag (wfS30F i) (memS30F i))
                ((s30Flag j.val).toFlag (wfS30F j) (memS30F j))
                X : ℚ) : ℝ))
        * (labelingFactor (Quotient.out X).unlabel (Quotient.out X) : ℝ))
      = (1 / 210 : ℝ) * ∑ θ ∈ rootingsOf (s3Type 0)
            (graphOfMask 7 (boundedRep H)),
          ((((∑ p ∈ outsidePairsS3 θ,
              (∑ i : Fin 236, ((fS30 r i.val : ℤ) : ℚ)
                  * (if (s30Flag i.val).IsIso (extFlagS3
                      (graphOfMask 7 (boundedRep H)) θ p.1.1 p.1.2)
                    then 1 else 0))
                * (∑ j : Fin 236, ((fS30 r j.val : ℤ) : ℚ)
                    * (if (s30Flag j.val).IsIso (extFlagS3
                        (graphOfMask 7 (boundedRep H)) θ p.2.1 p.2.2)
                      then 1 else 0))) / 6 : ℚ)) : ℝ) := by
  have hcast : ∀ i : Fin 236,
      ((fS30 r i.val : ℤ) : ℝ) = (((fS30 r i.val : ℤ) : ℚ) : ℝ) :=
    fun i => by push_cast; rfl
  have h := gammaS3_eq_rooting (rm := 0)
    (fun i : Fin 236 => ((fS30 r i.val : ℤ) : ℚ))
    (fun i => s30Flag i.val) wfS30F memS30F (boundedRep_mem H)
  rw [toFlag_boundedRep H (boundedRep_mem H)] at h
  rw [Finset.sum_congr rfl fun X _ => by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by
        rw [hcast i, hcast j]]]
  exact h

lemma coeffS31 (r : ℕ) (H : FlagWithSize TetraFree emptyType 7) :
    (∑ X ∈ Finset.univ.filter
        (fun X : FlagWithSize TetraFree (s3Type 1).toModel 7 =>
          Flag.unlabel X = H),
      (∑ i : Fin 191, ∑ j : Fin 191,
          ((fS31 r i.val : ℤ) : ℝ) * ((fS31 r j.val : ℤ) : ℝ)
            * ((subflagPairDensity
                ((s31Flag i.val).toFlag (wfS31F i) (memS31F i))
                ((s31Flag j.val).toFlag (wfS31F j) (memS31F j))
                X : ℚ) : ℝ))
        * (labelingFactor (Quotient.out X).unlabel (Quotient.out X) : ℝ))
      = (1 / 210 : ℝ) * ∑ θ ∈ rootingsOf (s3Type 1)
            (graphOfMask 7 (boundedRep H)),
          ((((∑ p ∈ outsidePairsS3 θ,
              (∑ i : Fin 191, ((fS31 r i.val : ℤ) : ℚ)
                  * (if (s31Flag i.val).IsIso (extFlagS3
                      (graphOfMask 7 (boundedRep H)) θ p.1.1 p.1.2)
                    then 1 else 0))
                * (∑ j : Fin 191, ((fS31 r j.val : ℤ) : ℚ)
                    * (if (s31Flag j.val).IsIso (extFlagS3
                        (graphOfMask 7 (boundedRep H)) θ p.2.1 p.2.2)
                      then 1 else 0))) / 6 : ℚ)) : ℝ) := by
  have hcast : ∀ i : Fin 191,
      ((fS31 r i.val : ℤ) : ℝ) = (((fS31 r i.val : ℤ) : ℚ) : ℝ) :=
    fun i => by push_cast; rfl
  have h := gammaS3_eq_rooting (rm := 1)
    (fun i : Fin 191 => ((fS31 r i.val : ℤ) : ℚ))
    (fun i => s31Flag i.val) wfS31F memS31F (boundedRep_mem H)
  rw [toFlag_boundedRep H (boundedRep_mem H)] at h
  rw [Finset.sum_congr rfl fun X _ => by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by
        rw [hcast i, hcast j]]]
  exact h

end FlagAlgebras.Core.Tetrahedron
