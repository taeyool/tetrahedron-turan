import LeanFlagAlgebras.Core.Density
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! # Core: joint subflag densities

Razborov's Definition 2 for `t = 2, 3`, theory-generically: the probability
that two (three) uniformly chosen vertex subsets of prescribed sizes, pairwise
disjoint outside the roots, simultaneously induce prescribed flags. The pair
density is the structure constant of the flag-algebra product; the triple
density drives its associativity.

This file provides the definitions (`pairWitnesses`/`tripleWitnesses`, counts,
`flagPairDensity`/`flagTripleDensity` with the `pairChoose`/`tripleChoose`
binomial normalizers), the mem-interfaces shielding the classical `filter`
instances, nonnegativity, symmetry of the pair density, insertion of the unit
flag (collapsing a joint density to lower arity), isomorphism invariance in
every slot, and the descents `subflagPairDensity`/`subflagTripleDensity` to
`Flag` quotients. The chain rules relating joint densities across arities
follow in a later slice. -/

namespace FlagAlgebras.Core

open Classical

variable {S : Signature} {T U₁ U₂ U₃ U₁' U₂' U₃' V V' : Type}
variable {𝕋 : RelTheory S} {σ : Model S T}

/-! ## Binomial normalizers -/

/-- The number of ways to choose two disjoint subsets of sizes `r₁`, `r₂`
from an `a`-element set: the normalizer of the pair density. -/
def pairChoose (a r₁ r₂ : ℕ) : ℕ :=
  a.choose r₁ * (a - r₁).choose r₂

/-- The number of ways to choose three pairwise disjoint subsets of sizes
`r₁`, `r₂`, `r₃` from an `a`-element set: the normalizer of the triple
density. -/
def tripleChoose (a r₁ r₂ r₃ : ℕ) : ℕ :=
  a.choose r₁ * (a - r₁).choose r₂ * (a - r₁ - r₂).choose r₃

lemma pairChoose_zero_right (a r₁ : ℕ) : pairChoose a r₁ 0 = a.choose r₁ := by
  rw [pairChoose, Nat.choose_zero_right, mul_one]

lemma tripleChoose_zero_middle (a r₁ r₃ : ℕ) :
    tripleChoose a r₁ 0 r₃ = pairChoose a r₁ r₃ := by
  rw [tripleChoose, pairChoose, Nat.choose_zero_right, mul_one, Nat.sub_zero]

lemma tripleChoose_zero_right (a r₁ r₂ : ℕ) :
    tripleChoose a r₁ r₂ 0 = pairChoose a r₁ r₂ := by
  rw [tripleChoose, pairChoose, Nat.choose_zero_right, mul_one]

/-- Choosing two disjoint subsets in either order gives the same count. -/
lemma pairChoose_comm (a r₁ r₂ : ℕ) : pairChoose a r₁ r₂ = pairChoose a r₂ r₁ := by
  show a.choose r₁ * (a - r₁).choose r₂ = a.choose r₂ * (a - r₂).choose r₁
  by_cases h : r₁ + r₂ ≤ a
  · have h₁ := choose_mul_choose (a := a) (b := r₁ + r₂) (c := r₁)
      (Nat.le_add_right _ _) h
    have h₂ := choose_mul_choose (a := a) (b := r₁ + r₂) (c := r₂)
      (Nat.le_add_left _ _) h
    rw [Nat.add_sub_cancel_left] at h₁
    rw [Nat.add_sub_cancel] at h₂
    have hsymm : (r₁ + r₂).choose r₁ = (r₁ + r₂).choose r₂ := by
      have hs := Nat.choose_symm (Nat.le_add_left r₂ r₁)
      rwa [Nat.add_sub_cancel] at hs
    rw [← h₁, ← h₂, hsymm]
  · rcases Nat.lt_or_ge a r₁ with h₁ | h₁
    · rw [Nat.choose_eq_zero_of_lt h₁, zero_mul,
        Nat.choose_eq_zero_of_lt (show a - r₂ < r₁ by omega), mul_zero]
    · rw [Nat.choose_eq_zero_of_lt (show a - r₁ < r₂ by omega), mul_zero]
      rcases Nat.lt_or_ge a r₂ with h₂ | h₂
      · rw [Nat.choose_eq_zero_of_lt h₂, zero_mul]
      · rw [Nat.choose_eq_zero_of_lt (show a - r₂ < r₁ by omega), mul_zero]

/-! ## Pair witnesses and the pair density -/

/-- Two subsets overlap only in the roots. Stated via memberships (rather
than an equation between intersections) so that it is independent of the
`DecidableEq` instances on the carrier; together with root-containment of
both sets it is equivalent to `W₁ ∩ W₂ = G.rootFinset`. -/
def OnlyRootsShared [Fintype T] [Fintype V] (G : LabeledFlag 𝕋 σ V)
    (W₁ W₂ : Finset V) : Prop :=
  ∀ x ∈ W₁, x ∈ W₂ → x ∈ G.rootFinset

lemma OnlyRootsShared.symm [Fintype T] [Fintype V] {G : LabeledFlag 𝕋 σ V}
    {W₁ W₂ : Finset V} (h : OnlyRootsShared G W₁ W₂) :
    OnlyRootsShared G W₂ W₁ :=
  fun x hx₂ hx₁ => h x hx₁ hx₂

/-- For root-containing subsets, sharing only roots is the intersection
equation (with whatever `Decidable` instances are ambient). -/
lemma OnlyRootsShared.inter_eq [Fintype T] [Fintype V]
    {G : LabeledFlag 𝕋 σ V}
    {W₁ W₂ : Finset V} (h : OnlyRootsShared G W₁ W₂)
    (h₁ : G.rootFinset ⊆ W₁) (h₂ : G.rootFinset ⊆ W₂) :
    W₁ ∩ W₂ = G.rootFinset := by
  refine Finset.Subset.antisymm ?_ (Finset.subset_inter h₁ h₂)
  intro x hx
  rw [Finset.mem_inter] at hx
  exact h x hx.1 hx.2

/-- The pairs of vertex subsets witnessing induced copies of `F₁` and `F₂`
simultaneously, disjointly outside the roots. -/
noncomputable def pairWitnesses [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁) (F₂ : LabeledFlag 𝕋 σ U₂)
    (G : LabeledFlag 𝕋 σ V) : Finset (Finset V × Finset V) :=
  Finset.univ.filter fun P =>
    P.1 ∈ flagWitnesses F₁ G ∧ P.2 ∈ flagWitnesses F₂ G ∧
      OnlyRootsShared G P.1 P.2

/-- Membership in the pair-witness set, stated without exposing the classical
`filter` instances. -/
lemma mem_pairWitnesses [Fintype T] [Fintype U₁] [Fintype U₂] [Fintype V]
    {F₁ : LabeledFlag 𝕋 σ U₁} {F₂ : LabeledFlag 𝕋 σ U₂}
    {G : LabeledFlag 𝕋 σ V} {P : Finset V × Finset V} :
    P ∈ pairWitnesses F₁ F₂ G ↔
      P.1 ∈ flagWitnesses F₁ G ∧ P.2 ∈ flagWitnesses F₂ G ∧
        OnlyRootsShared G P.1 P.2 := by
  unfold pairWitnesses
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The number of witnessing pairs. -/
noncomputable def pairCount [Fintype T] [Fintype U₁] [Fintype U₂] [Fintype V]
    (F₁ : LabeledFlag 𝕋 σ U₁) (F₂ : LabeledFlag 𝕋 σ U₂)
    (G : LabeledFlag 𝕋 σ V) : ℕ :=
  (pairWitnesses F₁ F₂ G).card

/-- The joint density `p(F₁, F₂; G)` of two flags in a common host, disjoint
outside the roots (Razborov Definition 2, `t = 2`). -/
noncomputable def flagPairDensity [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁) (F₂ : LabeledFlag 𝕋 σ U₂)
    (G : LabeledFlag 𝕋 σ V) : ℚ :=
  (pairCount F₁ F₂ G : ℚ) /
    (pairChoose (Fintype.card V - Fintype.card T)
      (Fintype.card U₁ - Fintype.card T)
      (Fintype.card U₂ - Fintype.card T) : ℚ)

lemma flagPairDensity_nonneg [Fintype T] [Fintype U₁] [Fintype U₂] [Fintype V]
    (F₁ : LabeledFlag 𝕋 σ U₁) (F₂ : LabeledFlag 𝕋 σ U₂)
    (G : LabeledFlag 𝕋 σ V) : 0 ≤ flagPairDensity F₁ F₂ G :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-! ## Triple witnesses and the triple density -/

/-- The triples of vertex subsets witnessing induced copies of `F₁`, `F₂`,
`F₃` simultaneously, pairwise disjointly outside the roots. -/
noncomputable def tripleWitnesses [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype U₃] [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁)
    (F₂ : LabeledFlag 𝕋 σ U₂) (F₃ : LabeledFlag 𝕋 σ U₃)
    (G : LabeledFlag 𝕋 σ V) : Finset (Finset V × Finset V × Finset V) :=
  Finset.univ.filter fun P =>
    P.1 ∈ flagWitnesses F₁ G ∧ P.2.1 ∈ flagWitnesses F₂ G ∧
      P.2.2 ∈ flagWitnesses F₃ G ∧ OnlyRootsShared G P.1 P.2.1 ∧
      OnlyRootsShared G P.1 P.2.2 ∧ OnlyRootsShared G P.2.1 P.2.2

/-- Membership in the triple-witness set, stated without exposing the
classical `filter` instances. -/
lemma mem_tripleWitnesses [Fintype T] [Fintype U₁] [Fintype U₂] [Fintype U₃]
    [Fintype V] {F₁ : LabeledFlag 𝕋 σ U₁} {F₂ : LabeledFlag 𝕋 σ U₂}
    {F₃ : LabeledFlag 𝕋 σ U₃} {G : LabeledFlag 𝕋 σ V}
    {P : Finset V × Finset V × Finset V} :
    P ∈ tripleWitnesses F₁ F₂ F₃ G ↔
      P.1 ∈ flagWitnesses F₁ G ∧ P.2.1 ∈ flagWitnesses F₂ G ∧
        P.2.2 ∈ flagWitnesses F₃ G ∧ OnlyRootsShared G P.1 P.2.1 ∧
        OnlyRootsShared G P.1 P.2.2 ∧ OnlyRootsShared G P.2.1 P.2.2 := by
  unfold tripleWitnesses
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The number of witnessing triples. -/
noncomputable def tripleCount [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype U₃] [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁)
    (F₂ : LabeledFlag 𝕋 σ U₂) (F₃ : LabeledFlag 𝕋 σ U₃)
    (G : LabeledFlag 𝕋 σ V) : ℕ :=
  (tripleWitnesses F₁ F₂ F₃ G).card

/-- The joint density `p(F₁, F₂, F₃; G)` of three flags in a common host,
pairwise disjoint outside the roots (Razborov Definition 2, `t = 3`). -/
noncomputable def flagTripleDensity [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype U₃] [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁)
    (F₂ : LabeledFlag 𝕋 σ U₂) (F₃ : LabeledFlag 𝕋 σ U₃)
    (G : LabeledFlag 𝕋 σ V) : ℚ :=
  (tripleCount F₁ F₂ F₃ G : ℚ) /
    (tripleChoose (Fintype.card V - Fintype.card T)
      (Fintype.card U₁ - Fintype.card T)
      (Fintype.card U₂ - Fintype.card T)
      (Fintype.card U₃ - Fintype.card T) : ℚ)

lemma flagTripleDensity_nonneg [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype U₃] [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁)
    (F₂ : LabeledFlag 𝕋 σ U₂) (F₃ : LabeledFlag 𝕋 σ U₃)
    (G : LabeledFlag 𝕋 σ V) : 0 ≤ flagTripleDensity F₁ F₂ F₃ G :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-! ## Symmetry of the pair density -/

lemma pairCount_comm [Fintype T] [Fintype U₁] [Fintype U₂] [Fintype V]
    (F₁ : LabeledFlag 𝕋 σ U₁) (F₂ : LabeledFlag 𝕋 σ U₂)
    (G : LabeledFlag 𝕋 σ V) : pairCount F₁ F₂ G = pairCount F₂ F₁ G := by
  unfold pairCount
  refine Finset.card_bij' (fun P _ => (P.2, P.1)) (fun P _ => (P.2, P.1))
    ?_ ?_ ?_ ?_
  · intro P hP
    obtain ⟨h₁, h₂, hint⟩ := mem_pairWitnesses.mp hP
    exact mem_pairWitnesses.mpr ⟨h₂, h₁, hint.symm⟩
  · intro P hP
    obtain ⟨h₁, h₂, hint⟩ := mem_pairWitnesses.mp hP
    exact mem_pairWitnesses.mpr ⟨h₂, h₁, hint.symm⟩
  · intro P _
    rfl
  · intro P _
    rfl

/-- The pair density is symmetric. -/
lemma flagPairDensity_comm [Fintype T] [Fintype U₁] [Fintype U₂] [Fintype V]
    (F₁ : LabeledFlag 𝕋 σ U₁) (F₂ : LabeledFlag 𝕋 σ U₂)
    (G : LabeledFlag 𝕋 σ V) :
    flagPairDensity F₁ F₂ G = flagPairDensity F₂ F₁ G := by
  rw [flagPairDensity, flagPairDensity, pairCount_comm, pairChoose_comm]

/-! ## Cyclic symmetry of the triple density -/

lemma tripleChoose_swap_left (a r₁ r₂ r₃ : ℕ) :
    tripleChoose a r₁ r₂ r₃ = tripleChoose a r₂ r₁ r₃ := by
  have h3 : a - r₁ - r₂ = a - r₂ - r₁ := by omega
  rw [tripleChoose, tripleChoose, h3]
  exact congrArg (· * (a - r₂ - r₁).choose r₃) (pairChoose_comm a r₁ r₂)

lemma tripleChoose_swap_right (a r₁ r₂ r₃ : ℕ) :
    tripleChoose a r₁ r₂ r₃ = tripleChoose a r₁ r₃ r₂ := by
  rw [tripleChoose, tripleChoose, mul_assoc, mul_assoc]
  exact congrArg (a.choose r₁ * ·) (pairChoose_comm (a - r₁) r₂ r₃)

lemma tripleChoose_rotate (a r₁ r₂ r₃ : ℕ) :
    tripleChoose a r₁ r₂ r₃ = tripleChoose a r₂ r₃ r₁ :=
  (tripleChoose_swap_left a r₁ r₂ r₃).trans
    (tripleChoose_swap_right a r₂ r₁ r₃)

lemma tripleCount_rotate [Fintype T] [Fintype U₁] [Fintype U₂] [Fintype U₃]
    [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁) (F₂ : LabeledFlag 𝕋 σ U₂)
    (F₃ : LabeledFlag 𝕋 σ U₃) (G : LabeledFlag 𝕋 σ V) :
    tripleCount F₁ F₂ F₃ G = tripleCount F₂ F₃ F₁ G := by
  unfold tripleCount
  refine Finset.card_bij' (fun P _ => (P.2.1, P.2.2, P.1))
    (fun P _ => (P.2.2, P.1, P.2.1)) ?_ ?_ ?_ ?_
  · intro P hP
    obtain ⟨h₁, h₂, h₃, h₁₂, h₁₃, h₂₃⟩ := mem_tripleWitnesses.mp hP
    exact mem_tripleWitnesses.mpr ⟨h₂, h₃, h₁, h₂₃, h₁₂.symm, h₁₃.symm⟩
  · intro P hP
    obtain ⟨h₁, h₂, h₃, h₁₂, h₁₃, h₂₃⟩ := mem_tripleWitnesses.mp hP
    exact mem_tripleWitnesses.mpr ⟨h₃, h₁, h₂, h₁₃.symm, h₂₃.symm, h₁₂⟩
  · intro P _
    rfl
  · intro P _
    rfl

/-- The triple density is invariant under cyclically rotating its three
pattern slots; the engine behind associativity of the flag product. -/
lemma flagTripleDensity_rotate [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype U₃] [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁)
    (F₂ : LabeledFlag 𝕋 σ U₂) (F₃ : LabeledFlag 𝕋 σ U₃)
    (G : LabeledFlag 𝕋 σ V) :
    flagTripleDensity F₁ F₂ F₃ G = flagTripleDensity F₂ F₃ F₁ G := by
  rw [flagTripleDensity, flagTripleDensity, tripleCount_rotate,
    tripleChoose_rotate]

/-! ## Inserting the unit flag -/

lemma pairCount_ofType_right [Fintype T] [Fintype U₁] [Fintype V]
    (hσ : 𝕋.Mem σ) (F₁ : LabeledFlag 𝕋 σ U₁) (G : LabeledFlag 𝕋 σ V) :
    pairCount F₁ (LabeledFlag.ofType 𝕋 σ hσ) G = flagCount F₁ G := by
  unfold pairCount flagCount
  refine Finset.card_bij' (fun P _ => P.1) (fun W _ => (W, G.rootFinset))
    ?_ ?_ ?_ ?_
  · intro P hP
    exact (mem_pairWitnesses.mp hP).1
  · intro W hW
    refine mem_pairWitnesses.mpr ⟨hW, ?_, fun _ _ hx => hx⟩
    rw [flagWitnesses_ofType]
    exact Finset.mem_singleton_self _
  · intro P hP
    obtain ⟨-, h₂, -⟩ := mem_pairWitnesses.mp hP
    rw [flagWitnesses_ofType] at h₂
    have h : P.2 = G.rootFinset := Finset.mem_singleton.mp h₂
    dsimp only
    rw [← h]
  · intro W _
    rfl

/-- Inserting the unit flag on the right collapses the pair density to the
single density. -/
lemma flagPairDensity_ofType_right [Fintype T] [Fintype U₁] [Fintype V]
    (hσ : 𝕋.Mem σ) (F₁ : LabeledFlag 𝕋 σ U₁) (G : LabeledFlag 𝕋 σ V) :
    flagPairDensity F₁ (LabeledFlag.ofType 𝕋 σ hσ) G = flagDensity F₁ G := by
  rw [flagPairDensity, flagDensity, pairCount_ofType_right, Nat.sub_self,
    pairChoose_zero_right]

/-- Inserting the unit flag on the left collapses the pair density to the
single density. -/
lemma flagPairDensity_ofType_left [Fintype T] [Fintype U₂] [Fintype V]
    (hσ : 𝕋.Mem σ) (F₂ : LabeledFlag 𝕋 σ U₂) (G : LabeledFlag 𝕋 σ V) :
    flagPairDensity (LabeledFlag.ofType 𝕋 σ hσ) F₂ G = flagDensity F₂ G := by
  rw [flagPairDensity_comm, flagPairDensity_ofType_right]

lemma tripleCount_ofType_middle [Fintype T] [Fintype U₁] [Fintype U₃]
    [Fintype V] (hσ : 𝕋.Mem σ) (F₁ : LabeledFlag 𝕋 σ U₁)
    (F₃ : LabeledFlag 𝕋 σ U₃) (G : LabeledFlag 𝕋 σ V) :
    tripleCount F₁ (LabeledFlag.ofType 𝕋 σ hσ) F₃ G = pairCount F₁ F₃ G := by
  unfold tripleCount pairCount
  refine Finset.card_bij' (fun P _ => (P.1, P.2.2))
    (fun P _ => (P.1, G.rootFinset, P.2)) ?_ ?_ ?_ ?_
  · intro P hP
    obtain ⟨h₁, -, h₃, -, h₁₃, -⟩ := mem_tripleWitnesses.mp hP
    exact mem_pairWitnesses.mpr ⟨h₁, h₃, h₁₃⟩
  · intro P hP
    obtain ⟨h₁, h₂, hint⟩ := mem_pairWitnesses.mp hP
    refine mem_tripleWitnesses.mpr
      ⟨h₁, ?_, h₂, fun _ _ hx => hx, hint, fun x hxR _ => hxR⟩
    rw [flagWitnesses_ofType]
    exact Finset.mem_singleton_self _
  · intro P hP
    obtain ⟨-, h₂, -, -, -, -⟩ := mem_tripleWitnesses.mp hP
    rw [flagWitnesses_ofType] at h₂
    have h : P.2.1 = G.rootFinset := Finset.mem_singleton.mp h₂
    dsimp only
    rw [← h]
  · intro P _
    rfl

/-- Inserting the unit flag in the middle collapses the triple density to the
pair density. -/
lemma flagTripleDensity_ofType_middle [Fintype T] [Fintype U₁] [Fintype U₃]
    [Fintype V] (hσ : 𝕋.Mem σ) (F₁ : LabeledFlag 𝕋 σ U₁)
    (F₃ : LabeledFlag 𝕋 σ U₃) (G : LabeledFlag 𝕋 σ V) :
    flagTripleDensity F₁ (LabeledFlag.ofType 𝕋 σ hσ) F₃ G
      = flagPairDensity F₁ F₃ G := by
  rw [flagTripleDensity, flagPairDensity, tripleCount_ofType_middle,
    Nat.sub_self, tripleChoose_zero_middle]

lemma tripleCount_ofType_right [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype V] (hσ : 𝕋.Mem σ) (F₁ : LabeledFlag 𝕋 σ U₁)
    (F₂ : LabeledFlag 𝕋 σ U₂) (G : LabeledFlag 𝕋 σ V) :
    tripleCount F₁ F₂ (LabeledFlag.ofType 𝕋 σ hσ) G = pairCount F₁ F₂ G := by
  unfold tripleCount pairCount
  refine Finset.card_bij' (fun P _ => (P.1, P.2.1))
    (fun P _ => (P.1, P.2, G.rootFinset)) ?_ ?_ ?_ ?_
  · intro P hP
    obtain ⟨h₁, h₂, -, h₁₂, -, -⟩ := mem_tripleWitnesses.mp hP
    exact mem_pairWitnesses.mpr ⟨h₁, h₂, h₁₂⟩
  · intro P hP
    obtain ⟨h₁, h₂, hint⟩ := mem_pairWitnesses.mp hP
    refine mem_tripleWitnesses.mpr
      ⟨h₁, h₂, ?_, hint, fun _ _ hx => hx, fun _ _ hx => hx⟩
    rw [flagWitnesses_ofType]
    exact Finset.mem_singleton_self _
  · intro P hP
    obtain ⟨-, -, h₃, -, -, -⟩ := mem_tripleWitnesses.mp hP
    rw [flagWitnesses_ofType] at h₃
    have h : P.2.2 = G.rootFinset := Finset.mem_singleton.mp h₃
    dsimp only
    rw [← h]
  · intro P _
    rfl

/-- Inserting the unit flag on the right collapses the triple density to the
pair density. -/
lemma flagTripleDensity_ofType_right [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype V] (hσ : 𝕋.Mem σ) (F₁ : LabeledFlag 𝕋 σ U₁)
    (F₂ : LabeledFlag 𝕋 σ U₂) (G : LabeledFlag 𝕋 σ V) :
    flagTripleDensity F₁ F₂ (LabeledFlag.ofType 𝕋 σ hσ) G
      = flagPairDensity F₁ F₂ G := by
  rw [flagTripleDensity, flagPairDensity, tripleCount_ofType_right,
    Nat.sub_self, tripleChoose_zero_right]

/-! ## Isomorphism invariance -/

lemma pairWitnesses_congr_left₁ [Fintype T] [Fintype U₁] [Fintype U₁']
    [Fintype U₂] [Fintype V] {F₁ : LabeledFlag 𝕋 σ U₁}
    {F₁' : LabeledFlag 𝕋 σ U₁'} (e₁ : F₁ ≃ᶠ F₁')
    (F₂ : LabeledFlag 𝕋 σ U₂) (G : LabeledFlag 𝕋 σ V) :
    pairWitnesses F₁ F₂ G = pairWitnesses F₁' F₂ G := by
  ext P
  rw [mem_pairWitnesses, mem_pairWitnesses, flagWitnesses_congr_left e₁]

lemma pairWitnesses_congr_left₂ [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype U₂'] [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁)
    {F₂ : LabeledFlag 𝕋 σ U₂} {F₂' : LabeledFlag 𝕋 σ U₂'} (e₂ : F₂ ≃ᶠ F₂')
    (G : LabeledFlag 𝕋 σ V) :
    pairWitnesses F₁ F₂ G = pairWitnesses F₁ F₂' G := by
  ext P
  rw [mem_pairWitnesses, mem_pairWitnesses, flagWitnesses_congr_left e₂]

/-- Transport of the shared-roots condition along a host isomorphism. -/
lemma LabeledFlagIso.onlyRootsShared_map [Fintype T] [Fintype V] [Fintype V']
    {G : LabeledFlag 𝕋 σ V} {G' : LabeledFlag 𝕋 σ V'} (e : G ≃ᶠ G')
    {W₁ W₂ : Finset V} (h : OnlyRootsShared G W₁ W₂) :
    OnlyRootsShared G' (W₁.map e.toIso.toEquiv.toEmbedding)
      (W₂.map e.toIso.toEquiv.toEmbedding) := by
  intro y hy₁ hy₂
  obtain ⟨x, hx₁, rfl⟩ := Finset.mem_map.mp hy₁
  obtain ⟨x', hx₂, heq⟩ := Finset.mem_map.mp hy₂
  have hx₂' : x ∈ W₂ :=
    (e.toIso.toEquiv.toEmbedding.injective heq : x' = x) ▸ hx₂
  have hr := Finset.mem_map_of_mem e.toIso.toEquiv.toEmbedding (h x hx₁ hx₂')
  rwa [e.rootFinset_map] at hr

lemma pairCount_congr_right [Fintype T] [Fintype U₁] [Fintype U₂] [Fintype V]
    [Fintype V'] (F₁ : LabeledFlag 𝕋 σ U₁) (F₂ : LabeledFlag 𝕋 σ U₂)
    {G : LabeledFlag 𝕋 σ V} {G' : LabeledFlag 𝕋 σ V'} (e : G ≃ᶠ G') :
    pairCount F₁ F₂ G = pairCount F₁ F₂ G' := by
  unfold pairCount
  refine Finset.card_bij'
    (fun P _ => (P.1.map e.toIso.toEquiv.toEmbedding,
      P.2.map e.toIso.toEquiv.toEmbedding))
    (fun Q _ => (Q.1.map e.symm.toIso.toEquiv.toEmbedding,
      Q.2.map e.symm.toIso.toEquiv.toEmbedding)) ?_ ?_ ?_ ?_
  · intro P hP
    obtain ⟨h₁, h₂, hint⟩ := mem_pairWitnesses.mp hP
    exact mem_pairWitnesses.mpr ⟨e.mem_flagWitnesses_map h₁,
      e.mem_flagWitnesses_map h₂, e.onlyRootsShared_map hint⟩
  · intro Q hQ
    obtain ⟨h₁, h₂, hint⟩ := mem_pairWitnesses.mp hQ
    exact mem_pairWitnesses.mpr ⟨e.symm.mem_flagWitnesses_map h₁,
      e.symm.mem_flagWitnesses_map h₂, e.symm.onlyRootsShared_map hint⟩
  · intro P _
    dsimp only
    rw [Finset.map_map, Finset.map_map,
      show e.toIso.toEquiv.toEmbedding.trans e.symm.toIso.toEquiv.toEmbedding
          = Function.Embedding.refl V from
        Function.Embedding.ext fun a => e.toIso.toEquiv.symm_apply_apply a,
      Finset.map_refl, Finset.map_refl]
  · intro Q _
    dsimp only
    rw [Finset.map_map, Finset.map_map,
      show e.symm.toIso.toEquiv.toEmbedding.trans e.toIso.toEquiv.toEmbedding
          = Function.Embedding.refl V' from
        Function.Embedding.ext fun a => e.toIso.toEquiv.apply_symm_apply a,
      Finset.map_refl, Finset.map_refl]

/-- The pair density depends only on the isomorphism classes of its three
arguments. -/
lemma flagPairDensity_congr [Fintype T] [Fintype U₁] [Fintype U₁']
    [Fintype U₂] [Fintype U₂'] [Fintype V] [Fintype V']
    {F₁ : LabeledFlag 𝕋 σ U₁} {F₁' : LabeledFlag 𝕋 σ U₁'}
    {F₂ : LabeledFlag 𝕋 σ U₂} {F₂' : LabeledFlag 𝕋 σ U₂'}
    {G : LabeledFlag 𝕋 σ V} {G' : LabeledFlag 𝕋 σ V'}
    (e₁ : F₁ ≃ᶠ F₁') (e₂ : F₂ ≃ᶠ F₂') (eg : G ≃ᶠ G') :
    flagPairDensity F₁ F₂ G = flagPairDensity F₁' F₂' G' := by
  have h₁ : Fintype.card U₁ = Fintype.card U₁' :=
    Fintype.card_congr e₁.toIso.toEquiv
  have h₂ : Fintype.card U₂ = Fintype.card U₂' :=
    Fintype.card_congr e₂.toIso.toEquiv
  have hv : Fintype.card V = Fintype.card V' :=
    Fintype.card_congr eg.toIso.toEquiv
  rw [flagPairDensity, flagPairDensity]
  rw [show pairCount F₁ F₂ G = pairCount F₁' F₂' G' by
    unfold pairCount
    rw [pairWitnesses_congr_left₁ e₁, pairWitnesses_congr_left₂ _ e₂]
    exact pairCount_congr_right F₁' F₂' eg]
  rw [h₁, h₂, hv]

lemma tripleWitnesses_congr_left₁ [Fintype T] [Fintype U₁] [Fintype U₁']
    [Fintype U₂] [Fintype U₃] [Fintype V] {F₁ : LabeledFlag 𝕋 σ U₁}
    {F₁' : LabeledFlag 𝕋 σ U₁'} (e₁ : F₁ ≃ᶠ F₁')
    (F₂ : LabeledFlag 𝕋 σ U₂) (F₃ : LabeledFlag 𝕋 σ U₃)
    (G : LabeledFlag 𝕋 σ V) :
    tripleWitnesses F₁ F₂ F₃ G = tripleWitnesses F₁' F₂ F₃ G := by
  ext P
  rw [mem_tripleWitnesses, mem_tripleWitnesses, flagWitnesses_congr_left e₁]

lemma tripleWitnesses_congr_left₂ [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype U₂'] [Fintype U₃] [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁)
    {F₂ : LabeledFlag 𝕋 σ U₂} {F₂' : LabeledFlag 𝕋 σ U₂'} (e₂ : F₂ ≃ᶠ F₂')
    (F₃ : LabeledFlag 𝕋 σ U₃) (G : LabeledFlag 𝕋 σ V) :
    tripleWitnesses F₁ F₂ F₃ G = tripleWitnesses F₁ F₂' F₃ G := by
  ext P
  rw [mem_tripleWitnesses, mem_tripleWitnesses, flagWitnesses_congr_left e₂]

lemma tripleWitnesses_congr_left₃ [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype U₃] [Fintype U₃'] [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁)
    (F₂ : LabeledFlag 𝕋 σ U₂) {F₃ : LabeledFlag 𝕋 σ U₃}
    {F₃' : LabeledFlag 𝕋 σ U₃'} (e₃ : F₃ ≃ᶠ F₃') (G : LabeledFlag 𝕋 σ V) :
    tripleWitnesses F₁ F₂ F₃ G = tripleWitnesses F₁ F₂ F₃' G := by
  ext P
  rw [mem_tripleWitnesses, mem_tripleWitnesses, flagWitnesses_congr_left e₃]

lemma tripleCount_congr_right [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype U₃] [Fintype V] [Fintype V'] (F₁ : LabeledFlag 𝕋 σ U₁)
    (F₂ : LabeledFlag 𝕋 σ U₂) (F₃ : LabeledFlag 𝕋 σ U₃)
    {G : LabeledFlag 𝕋 σ V} {G' : LabeledFlag 𝕋 σ V'} (e : G ≃ᶠ G') :
    tripleCount F₁ F₂ F₃ G = tripleCount F₁ F₂ F₃ G' := by
  unfold tripleCount
  refine Finset.card_bij'
    (fun P _ => (P.1.map e.toIso.toEquiv.toEmbedding,
      P.2.1.map e.toIso.toEquiv.toEmbedding,
      P.2.2.map e.toIso.toEquiv.toEmbedding))
    (fun Q _ => (Q.1.map e.symm.toIso.toEquiv.toEmbedding,
      Q.2.1.map e.symm.toIso.toEquiv.toEmbedding,
      Q.2.2.map e.symm.toIso.toEquiv.toEmbedding)) ?_ ?_ ?_ ?_
  · intro P hP
    obtain ⟨h₁, h₂, h₃, h₁₂, h₁₃, h₂₃⟩ := mem_tripleWitnesses.mp hP
    exact mem_tripleWitnesses.mpr ⟨e.mem_flagWitnesses_map h₁,
      e.mem_flagWitnesses_map h₂, e.mem_flagWitnesses_map h₃,
      e.onlyRootsShared_map h₁₂, e.onlyRootsShared_map h₁₃,
      e.onlyRootsShared_map h₂₃⟩
  · intro Q hQ
    obtain ⟨h₁, h₂, h₃, h₁₂, h₁₃, h₂₃⟩ := mem_tripleWitnesses.mp hQ
    exact mem_tripleWitnesses.mpr ⟨e.symm.mem_flagWitnesses_map h₁,
      e.symm.mem_flagWitnesses_map h₂, e.symm.mem_flagWitnesses_map h₃,
      e.symm.onlyRootsShared_map h₁₂, e.symm.onlyRootsShared_map h₁₃,
      e.symm.onlyRootsShared_map h₂₃⟩
  · intro P _
    dsimp only
    rw [Finset.map_map, Finset.map_map, Finset.map_map,
      show e.toIso.toEquiv.toEmbedding.trans e.symm.toIso.toEquiv.toEmbedding
          = Function.Embedding.refl V from
        Function.Embedding.ext fun a => e.toIso.toEquiv.symm_apply_apply a,
      Finset.map_refl, Finset.map_refl, Finset.map_refl]
  · intro Q _
    dsimp only
    rw [Finset.map_map, Finset.map_map, Finset.map_map,
      show e.symm.toIso.toEquiv.toEmbedding.trans e.toIso.toEquiv.toEmbedding
          = Function.Embedding.refl V' from
        Function.Embedding.ext fun a => e.toIso.toEquiv.apply_symm_apply a,
      Finset.map_refl, Finset.map_refl, Finset.map_refl]

/-- The triple density depends only on the isomorphism classes of its four
arguments. -/
lemma flagTripleDensity_congr [Fintype T] [Fintype U₁] [Fintype U₁']
    [Fintype U₂] [Fintype U₂'] [Fintype U₃] [Fintype U₃'] [Fintype V]
    [Fintype V'] {F₁ : LabeledFlag 𝕋 σ U₁} {F₁' : LabeledFlag 𝕋 σ U₁'}
    {F₂ : LabeledFlag 𝕋 σ U₂} {F₂' : LabeledFlag 𝕋 σ U₂'}
    {F₃ : LabeledFlag 𝕋 σ U₃} {F₃' : LabeledFlag 𝕋 σ U₃'}
    {G : LabeledFlag 𝕋 σ V} {G' : LabeledFlag 𝕋 σ V'}
    (e₁ : F₁ ≃ᶠ F₁') (e₂ : F₂ ≃ᶠ F₂') (e₃ : F₃ ≃ᶠ F₃') (eg : G ≃ᶠ G') :
    flagTripleDensity F₁ F₂ F₃ G = flagTripleDensity F₁' F₂' F₃' G' := by
  have h₁ : Fintype.card U₁ = Fintype.card U₁' :=
    Fintype.card_congr e₁.toIso.toEquiv
  have h₂ : Fintype.card U₂ = Fintype.card U₂' :=
    Fintype.card_congr e₂.toIso.toEquiv
  have h₃ : Fintype.card U₃ = Fintype.card U₃' :=
    Fintype.card_congr e₃.toIso.toEquiv
  have hv : Fintype.card V = Fintype.card V' :=
    Fintype.card_congr eg.toIso.toEquiv
  rw [flagTripleDensity, flagTripleDensity]
  rw [show tripleCount F₁ F₂ F₃ G = tripleCount F₁' F₂' F₃' G' by
    unfold tripleCount
    rw [tripleWitnesses_congr_left₁ e₁, tripleWitnesses_congr_left₂ _ e₂,
      tripleWitnesses_congr_left₃ _ _ e₃]
    exact tripleCount_congr_right F₁' F₂' F₃' eg]
  rw [h₁, h₂, h₃, hv]

/-! ## Descent to isomorphism classes -/

/-- The pair density on isomorphism classes: the descent of
`flagPairDensity` to the `Flag` quotients. -/
noncomputable def subflagPairDensity [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype V] (F₁ : Flag 𝕋 σ U₁) (F₂ : Flag 𝕋 σ U₂) (G : Flag 𝕋 σ V) : ℚ :=
  Quotient.liftOn F₁
    (fun f₁ => Quotient.liftOn₂ F₂ G (fun f₂ g => flagPairDensity f₁ f₂ g)
      fun _ _ _ _ h₂ hg => by
        obtain ⟨e₂⟩ := h₂
        obtain ⟨eg⟩ := hg
        exact flagPairDensity_congr (LabeledFlagIso.refl _) e₂ eg)
    fun f₁ f₁' h₁ => by
      obtain ⟨e₁⟩ := h₁
      refine Quotient.inductionOn₂ F₂ G fun f₂ g => ?_
      exact flagPairDensity_congr e₁ (LabeledFlagIso.refl _)
        (LabeledFlagIso.refl _)

@[simp]
lemma subflagPairDensity_mk [Fintype T] [Fintype U₁] [Fintype U₂] [Fintype V]
    (F₁ : LabeledFlag 𝕋 σ U₁) (F₂ : LabeledFlag 𝕋 σ U₂)
    (G : LabeledFlag 𝕋 σ V) :
    subflagPairDensity F₁.toFlag F₂.toFlag G.toFlag
      = flagPairDensity F₁ F₂ G :=
  rfl

lemma subflagPairDensity_nonneg [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype V] (F₁ : Flag 𝕋 σ U₁) (F₂ : Flag 𝕋 σ U₂) (G : Flag 𝕋 σ V) :
    0 ≤ subflagPairDensity F₁ F₂ G := by
  refine Quotient.inductionOn₂ F₁ F₂ fun f₁ f₂ =>
    Quotient.inductionOn G fun g => ?_
  exact flagPairDensity_nonneg f₁ f₂ g

lemma subflagPairDensity_comm [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype V] (F₁ : Flag 𝕋 σ U₁) (F₂ : Flag 𝕋 σ U₂) (G : Flag 𝕋 σ V) :
    subflagPairDensity F₁ F₂ G = subflagPairDensity F₂ F₁ G := by
  refine Quotient.inductionOn₂ F₁ F₂ fun f₁ f₂ =>
    Quotient.inductionOn G fun g => ?_
  exact flagPairDensity_comm f₁ f₂ g

lemma subflagPairDensity_ofType_right [Fintype T] [Fintype U₁] [Fintype V]
    (hσ : 𝕋.Mem σ) (F₁ : Flag 𝕋 σ U₁) (G : Flag 𝕋 σ V) :
    subflagPairDensity F₁ (LabeledFlag.ofType 𝕋 σ hσ).toFlag G
      = subflagDensity F₁ G := by
  refine Quotient.inductionOn₂ F₁ G fun f₁ g => ?_
  exact flagPairDensity_ofType_right hσ f₁ g

lemma subflagPairDensity_ofType_left [Fintype T] [Fintype U₂] [Fintype V]
    (hσ : 𝕋.Mem σ) (F₂ : Flag 𝕋 σ U₂) (G : Flag 𝕋 σ V) :
    subflagPairDensity (LabeledFlag.ofType 𝕋 σ hσ).toFlag F₂ G
      = subflagDensity F₂ G := by
  refine Quotient.inductionOn₂ F₂ G fun f₂ g => ?_
  exact flagPairDensity_ofType_left hσ f₂ g

/-- The triple density on isomorphism classes: the descent of
`flagTripleDensity` to the `Flag` quotients. -/
noncomputable def subflagTripleDensity [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype U₃] [Fintype V] (F₁ : Flag 𝕋 σ U₁) (F₂ : Flag 𝕋 σ U₂)
    (F₃ : Flag 𝕋 σ U₃) (G : Flag 𝕋 σ V) : ℚ :=
  Quotient.liftOn₂ F₁ F₂
    (fun f₁ f₂ => Quotient.liftOn₂ F₃ G
      (fun f₃ g => flagTripleDensity f₁ f₂ f₃ g)
      fun _ _ _ _ h₃ hg => by
        obtain ⟨e₃⟩ := h₃
        obtain ⟨eg⟩ := hg
        exact flagTripleDensity_congr (LabeledFlagIso.refl _)
          (LabeledFlagIso.refl _) e₃ eg)
    fun f₁ f₂ f₁' f₂' h₁ h₂ => by
      obtain ⟨e₁⟩ := h₁
      obtain ⟨e₂⟩ := h₂
      refine Quotient.inductionOn₂ F₃ G fun f₃ g => ?_
      exact flagTripleDensity_congr e₁ e₂ (LabeledFlagIso.refl _)
        (LabeledFlagIso.refl _)

@[simp]
lemma subflagTripleDensity_mk [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype U₃] [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁)
    (F₂ : LabeledFlag 𝕋 σ U₂) (F₃ : LabeledFlag 𝕋 σ U₃)
    (G : LabeledFlag 𝕋 σ V) :
    subflagTripleDensity F₁.toFlag F₂.toFlag F₃.toFlag G.toFlag
      = flagTripleDensity F₁ F₂ F₃ G :=
  rfl

lemma subflagTripleDensity_nonneg [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype U₃] [Fintype V] (F₁ : Flag 𝕋 σ U₁) (F₂ : Flag 𝕋 σ U₂)
    (F₃ : Flag 𝕋 σ U₃) (G : Flag 𝕋 σ V) :
    0 ≤ subflagTripleDensity F₁ F₂ F₃ G := by
  refine Quotient.inductionOn₂ F₁ F₂ fun f₁ f₂ =>
    Quotient.inductionOn₂ F₃ G fun f₃ g => ?_
  exact flagTripleDensity_nonneg f₁ f₂ f₃ g

lemma subflagTripleDensity_rotate [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype U₃] [Fintype V] (F₁ : Flag 𝕋 σ U₁) (F₂ : Flag 𝕋 σ U₂)
    (F₃ : Flag 𝕋 σ U₃) (G : Flag 𝕋 σ V) :
    subflagTripleDensity F₁ F₂ F₃ G = subflagTripleDensity F₂ F₃ F₁ G := by
  refine Quotient.inductionOn₂ F₁ F₂ fun f₁ f₂ =>
    Quotient.inductionOn₂ F₃ G fun f₃ g => ?_
  exact flagTripleDensity_rotate f₁ f₂ f₃ g

lemma subflagTripleDensity_ofType_middle [Fintype T] [Fintype U₁]
    [Fintype U₃] [Fintype V] (hσ : 𝕋.Mem σ) (F₁ : Flag 𝕋 σ U₁)
    (F₃ : Flag 𝕋 σ U₃) (G : Flag 𝕋 σ V) :
    subflagTripleDensity F₁ (LabeledFlag.ofType 𝕋 σ hσ).toFlag F₃ G
      = subflagPairDensity F₁ F₃ G := by
  refine Quotient.inductionOn₂ F₁ F₃ fun f₁ f₃ =>
    Quotient.inductionOn G fun g => ?_
  exact flagTripleDensity_ofType_middle hσ f₁ f₃ g

lemma subflagTripleDensity_ofType_right [Fintype T] [Fintype U₁]
    [Fintype U₂] [Fintype V] (hσ : 𝕋.Mem σ) (F₁ : Flag 𝕋 σ U₁)
    (F₂ : Flag 𝕋 σ U₂) (G : Flag 𝕋 σ V) :
    subflagTripleDensity F₁ F₂ (LabeledFlag.ofType 𝕋 σ hσ).toFlag G
      = subflagPairDensity F₁ F₂ G := by
  refine Quotient.inductionOn₂ F₁ F₂ fun f₁ f₂ =>
    Quotient.inductionOn G fun g => ?_
  exact flagTripleDensity_ofType_right hσ f₁ f₂ g

/-! ### Inserting the canonical unit flag

The same insertion lemmas for the reindexed unit `unitFlag` on `Fin |T|`,
the representative the flag algebra's unit uses. -/

lemma subflagPairDensity_unitFlag_right [Fintype T] [Fintype U₁] [Fintype V]
    (hσ : 𝕋.Mem σ) (F₁ : Flag 𝕋 σ U₁) (G : Flag 𝕋 σ V) :
    subflagPairDensity F₁ (unitFlag 𝕋 σ hσ).toFlag G
      = subflagDensity F₁ G := by
  refine Quotient.inductionOn₂ F₁ G fun f₁ g => ?_
  show flagPairDensity f₁ (unitFlag 𝕋 σ hσ) g = flagDensity f₁ g
  rw [← flagPairDensity_congr (LabeledFlagIso.refl f₁)
    (unitFlagIso 𝕋 σ hσ) (LabeledFlagIso.refl g)]
  exact flagPairDensity_ofType_right hσ f₁ g

lemma subflagPairDensity_unitFlag_left [Fintype T] [Fintype U₂] [Fintype V]
    (hσ : 𝕋.Mem σ) (F₂ : Flag 𝕋 σ U₂) (G : Flag 𝕋 σ V) :
    subflagPairDensity (unitFlag 𝕋 σ hσ).toFlag F₂ G
      = subflagDensity F₂ G := by
  refine Quotient.inductionOn₂ F₂ G fun f₂ g => ?_
  show flagPairDensity (unitFlag 𝕋 σ hσ) f₂ g = flagDensity f₂ g
  rw [← flagPairDensity_congr (unitFlagIso 𝕋 σ hσ)
    (LabeledFlagIso.refl f₂) (LabeledFlagIso.refl g)]
  exact flagPairDensity_ofType_left hσ f₂ g

lemma subflagTripleDensity_unitFlag_middle [Fintype T] [Fintype U₁]
    [Fintype U₃] [Fintype V] (hσ : 𝕋.Mem σ) (F₁ : Flag 𝕋 σ U₁)
    (F₃ : Flag 𝕋 σ U₃) (G : Flag 𝕋 σ V) :
    subflagTripleDensity F₁ (unitFlag 𝕋 σ hσ).toFlag F₃ G
      = subflagPairDensity F₁ F₃ G := by
  refine Quotient.inductionOn₂ F₁ F₃ fun f₁ f₃ =>
    Quotient.inductionOn G fun g => ?_
  show flagTripleDensity f₁ (unitFlag 𝕋 σ hσ) f₃ g = flagPairDensity f₁ f₃ g
  rw [← flagTripleDensity_congr (LabeledFlagIso.refl f₁)
    (unitFlagIso 𝕋 σ hσ) (LabeledFlagIso.refl f₃) (LabeledFlagIso.refl g)]
  exact flagTripleDensity_ofType_middle hσ f₁ f₃ g

lemma subflagTripleDensity_unitFlag_right [Fintype T] [Fintype U₁]
    [Fintype U₂] [Fintype V] (hσ : 𝕋.Mem σ) (F₁ : Flag 𝕋 σ U₁)
    (F₂ : Flag 𝕋 σ U₂) (G : Flag 𝕋 σ V) :
    subflagTripleDensity F₁ F₂ (unitFlag 𝕋 σ hσ).toFlag G
      = subflagPairDensity F₁ F₂ G := by
  refine Quotient.inductionOn₂ F₁ F₂ fun f₁ f₂ =>
    Quotient.inductionOn G fun g => ?_
  show flagTripleDensity f₁ f₂ (unitFlag 𝕋 σ hσ) g = flagPairDensity f₁ f₂ g
  rw [← flagTripleDensity_congr (LabeledFlagIso.refl f₁)
    (LabeledFlagIso.refl f₂) (unitFlagIso 𝕋 σ hσ) (LabeledFlagIso.refl g)]
  exact flagTripleDensity_ofType_right hσ f₁ f₂ g

/-! ## The chain rules (Razborov Lemma 2.2, `t = 2, 3`)

The master identity expands a triple density over an intermediate flag
covering the first two slots: `p(F₁,F₂,F₃;G) = ∑_{F'} p(F₁,F₂;F')·p(F',F₃;G)`.
Its proof factors through two independent reductions: expanding a *pair*
density over the host (the `t = 1` double-counting argument of
`Core/Density.lean`, run with pairs of witnesses below the intermediate
subset), and fibering a joint density over the witnesses of its last slot
(each fiber is a count in the induced sub-flag on the complement of the
witness's non-root part). Inserting the unit flag then specializes the master
identity to the mixed chain rules `₂₁` and `₁₂` consumed by the flag
algebra. -/

private lemma map_subtype_subset {A : Finset V} (B : Finset {x // x ∈ A}) :
    B.map (Function.Embedding.subtype _) ⊆ A := by
  intro x hx
  obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp hx
  exact b.property

private lemma subset_sdiff_of_onlyRootsShared [Fintype T] [Fintype V]
    {G : LabeledFlag 𝕋 σ V} {W W₃ : Finset V}
    (h : OnlyRootsShared G W W₃) :
    W ⊆ Finset.univ \ (W₃ \ G.rootFinset) := by
  intro x hx
  rw [Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, fun hmem => ?_⟩
  rw [Finset.mem_sdiff] at hmem
  exact hmem.2 (h x hx hmem.1)

private lemma onlyRootsShared_of_subset_sdiff [Fintype T] [Fintype V]
    {G : LabeledFlag 𝕋 σ V} {W W₃ : Finset V}
    (hWD : W ⊆ Finset.univ \ (W₃ \ G.rootFinset)) :
    OnlyRootsShared G W W₃ := by
  intro x hx hx₃
  have hmem := hWD hx
  rw [Finset.mem_sdiff] at hmem
  by_contra hxR
  exact hmem.2 (Finset.mem_sdiff.mpr ⟨hx₃, hxR⟩)

/-- The root set of an induced sub-flag maps onto the ambient root set. -/
lemma LabeledFlag.restrict_rootFinset_map [Fintype T] [Fintype V]
    (G : LabeledFlag 𝕋 σ V) {A : Finset V}
    (hA : ∀ t, G.rootEmbed.toEmbedding t ∈ A) :
    ((G.restrict A hA).rootFinset).map (Function.Embedding.subtype _)
      = G.rootFinset := by
  rw [LabeledFlag.rootFinset, LabeledFlag.rootFinset, Finset.map_map]
  congr 1

/-- Membership in the root set of an induced sub-flag, read in the ambient
host. -/
lemma LabeledFlag.mem_restrict_rootFinset [Fintype T] [Fintype V]
    {G : LabeledFlag 𝕋 σ V} {A : Finset V}
    {hA : ∀ t, G.rootEmbed.toEmbedding t ∈ A} {b : {x // x ∈ A}} :
    b ∈ (G.restrict A hA).rootFinset ↔ (b : V) ∈ G.rootFinset := by
  simp only [LabeledFlag.rootFinset, Finset.mem_map, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, congrArg Subtype.val ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, Subtype.ext ht⟩

/-- Transport of the shared-roots condition along `Finset.map` out of an
induced sub-flag. -/
private lemma onlyRootsShared_map_subtype [Fintype T] [Fintype V]
    {G : LabeledFlag 𝕋 σ V} {A : Finset V}
    {hA : ∀ t, G.rootEmbed.toEmbedding t ∈ A} {B₁ B₂ : Finset {x // x ∈ A}}
    (h : OnlyRootsShared (G.restrict A hA) B₁ B₂) :
    OnlyRootsShared G (B₁.map (Function.Embedding.subtype _))
      (B₂.map (Function.Embedding.subtype _)) := by
  intro y hy₁ hy₂
  obtain ⟨b, hb₁, rfl⟩ := Finset.mem_map.mp hy₁
  obtain ⟨b', hb₂, heq⟩ := Finset.mem_map.mp hy₂
  have hb₂' : b ∈ B₂ := (Subtype.ext heq : b' = b) ▸ hb₂
  exact LabeledFlag.mem_restrict_rootFinset.mp (h b hb₁ hb₂')

/-- Transport of the shared-roots condition along `Finset.subtype` into an
induced sub-flag. -/
private lemma onlyRootsShared_subtype [Fintype T] [Fintype V]
    {G : LabeledFlag 𝕋 σ V} {A : Finset V}
    (hA : ∀ t, G.rootEmbed.toEmbedding t ∈ A) {W₁ W₂ : Finset V}
    (h : OnlyRootsShared G W₁ W₂) :
    OnlyRootsShared (G.restrict A hA) (W₁.subtype (· ∈ A))
      (W₂.subtype (· ∈ A)) := by
  intro b hb₁ hb₂
  rw [Finset.mem_subtype] at hb₁ hb₂
  exact LabeledFlag.mem_restrict_rootFinset.mpr (h b hb₁ hb₂)

lemma pairChoose_pos {a r₁ r₂ : ℕ} (h : r₁ + r₂ ≤ a) :
    0 < pairChoose a r₁ r₂ :=
  Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))

lemma tripleChoose_pos {a r₁ r₂ r₃ : ℕ} (h : r₁ + r₂ + r₃ ≤ a) :
    0 < tripleChoose a r₁ r₂ r₃ :=
  Nat.mul_pos (Nat.mul_pos (Nat.choose_pos (by omega))
    (Nat.choose_pos (by omega))) (Nat.choose_pos (by omega))

/-- The normalizer identity behind the master chain rule: completing two
disjoint choices to an intermediate set and choosing the third part outside
it recombines into the pair normalizers. -/
private lemma tripleChoose_mul_choose {a a' r₁ r₂ r₃ : ℕ}
    (hr₁₂ : r₁ + r₂ ≤ a') (ha' : a' ≤ a) :
    tripleChoose a r₁ r₂ r₃ * (a - r₁ - r₂ - r₃).choose (a' - r₁ - r₂)
      = pairChoose a' r₁ r₂ * pairChoose a a' r₃ := by
  have s3 : (a - r₁ - r₂).choose r₃ * (a - r₁ - r₂ - r₃).choose (a' - r₁ - r₂)
      = (a - r₁ - r₂).choose (a' - r₁ - r₂) *
        (a - r₁ - r₂ - (a' - r₁ - r₂)).choose r₃ :=
    pairChoose_comm (a - r₁ - r₂) r₃ (a' - r₁ - r₂)
  have e₃ : a - r₁ - r₂ - (a' - r₁ - r₂) = a - a' := by omega
  have s2 : (a - r₁).choose (a' - r₁) * (a' - r₁).choose r₂
      = (a - r₁).choose r₂ * (a - r₁ - r₂).choose (a' - r₁ - r₂) :=
    choose_mul_choose (by omega) (by omega)
  have s1 : a.choose a' * a'.choose r₁
      = a.choose r₁ * (a - r₁).choose (a' - r₁) :=
    choose_mul_choose (by omega) ha'
  calc tripleChoose a r₁ r₂ r₃ * (a - r₁ - r₂ - r₃).choose (a' - r₁ - r₂)
      = a.choose r₁ * (a - r₁).choose r₂ *
          ((a - r₁ - r₂).choose r₃ *
            (a - r₁ - r₂ - r₃).choose (a' - r₁ - r₂)) := by
        rw [tripleChoose]; ring
    _ = a.choose r₁ * (a - r₁).choose r₂ *
          ((a - r₁ - r₂).choose (a' - r₁ - r₂) *
            (a - r₁ - r₂ - (a' - r₁ - r₂)).choose r₃) := by
        rw [s3]
    _ = a.choose r₁ * ((a - r₁).choose r₂ *
          (a - r₁ - r₂).choose (a' - r₁ - r₂)) * (a - a').choose r₃ := by
        rw [e₃]; ring
    _ = a.choose r₁ * ((a - r₁).choose (a' - r₁) * (a' - r₁).choose r₂) *
          (a - a').choose r₃ := by
        rw [s2]
    _ = a.choose r₁ * (a - r₁).choose (a' - r₁) * (a' - r₁).choose r₂ *
          (a - a').choose r₃ := by
        ring
    _ = a.choose a' * a'.choose r₁ * (a' - r₁).choose r₂ *
          (a - a').choose r₃ := by
        rw [← s1]
    _ = pairChoose a' r₁ r₂ * pairChoose a a' r₃ := by
        rw [pairChoose, pairChoose]; ring

/-- The number of witnessing pairs below a given subset (fixing the classical
`filter` instances once). -/
noncomputable def pairRestrictCount [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁) (F₂ : LabeledFlag 𝕋 σ U₂)
    (G : LabeledFlag 𝕋 σ V) (A : Finset V) : ℕ :=
  ((pairWitnesses F₁ F₂ G).filter (fun P => P.1 ⊆ A ∧ P.2 ⊆ A)).card

/-- Counting pairs inside a restriction is counting pairs below the subset. -/
lemma pairCount_restrict [Fintype T] [Fintype U₁] [Fintype U₂] [Fintype V]
    (F₁ : LabeledFlag 𝕋 σ U₁) (F₂ : LabeledFlag 𝕋 σ U₂)
    (G : LabeledFlag 𝕋 σ V) {A : Finset V}
    (hA : ∀ t, G.rootEmbed.toEmbedding t ∈ A) :
    pairCount F₁ F₂ (G.restrict A hA) = pairRestrictCount F₁ F₂ G A := by
  unfold pairCount pairRestrictCount
  refine Finset.card_bij'
    (fun B _ => (B.1.map (Function.Embedding.subtype _),
      B.2.map (Function.Embedding.subtype _)))
    (fun P _ => (P.1.subtype (· ∈ A), P.2.subtype (· ∈ A))) ?_ ?_ ?_ ?_
  · rintro ⟨B₁, B₂⟩ hB
    obtain ⟨h₁, h₂, hint⟩ := mem_pairWitnesses.mp hB
    exact Finset.mem_filter.mpr ⟨mem_pairWitnesses.mpr
      ⟨mem_flagWitnesses_map_subtype hA h₁,
        mem_flagWitnesses_map_subtype hA h₂,
        onlyRootsShared_map_subtype hint⟩,
      map_subtype_subset _, map_subtype_subset _⟩
  · rintro ⟨P₁, P₂⟩ hP
    obtain ⟨hmem, hA₁, hA₂⟩ := Finset.mem_filter.mp hP
    obtain ⟨h₁, h₂, hint⟩ := mem_pairWitnesses.mp hmem
    exact mem_pairWitnesses.mpr ⟨mem_flagWitnesses_subtype hA h₁ hA₁,
      mem_flagWitnesses_subtype hA h₂ hA₂,
      onlyRootsShared_subtype hA hint⟩
  · rintro ⟨B₁, B₂⟩ _
    dsimp only
    rw [Prod.mk.injEq]
    constructor
    · ext x
      rw [Finset.mem_subtype]
      exact Finset.mem_map' _
    · ext x
      rw [Finset.mem_subtype]
      exact Finset.mem_map' _
  · rintro ⟨P₁, P₂⟩ hP
    obtain ⟨-, hA₁, hA₂⟩ := Finset.mem_filter.mp hP
    dsimp only
    rw [Prod.mk.injEq]
    constructor
    · rw [Finset.subtype_map, Finset.filter_true_of_mem fun x hx => hA₁ hx]
    · rw [Finset.subtype_map, Finset.filter_true_of_mem fun x hx => hA₂ hx]

/-- Double counting pairs of witnesses against their root-containing
`m`-supersets. -/
private lemma sum_pairRestrictCount_index [Fintype T] [Fintype U₁]
    [Fintype U₂] [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁)
    (F₂ : LabeledFlag 𝕋 σ U₂) (G : LabeledFlag 𝕋 σ V) {m : ℕ}
    (hm : Fintype.card U₁ + Fintype.card U₂ - Fintype.card T ≤ m)
    (p : Finset V → Prop) [DecidablePred p]
    (hp : ∀ A, p A ↔ (∀ t, G.rootEmbed.toEmbedding t ∈ A) ∧ A.card = m) :
    ∑ A ∈ Finset.univ.filter p, pairRestrictCount F₁ F₂ G A
      = pairCount F₁ F₂ G *
        (Fintype.card V
            - (Fintype.card U₁ + Fintype.card U₂ - Fintype.card T)).choose
          (m - (Fintype.card U₁ + Fintype.card U₂ - Fintype.card T)) := by
  have hsummand : ∀ A, pairRestrictCount F₁ F₂ G A
      = ∑ Q ∈ pairWitnesses F₁ F₂ G, if Q.1 ⊆ A ∧ Q.2 ⊆ A then 1 else 0 := by
    intro A
    rw [pairRestrictCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun A _ => hsummand A, Finset.sum_comm]
  have hper : ∀ Q ∈ pairWitnesses F₁ F₂ G,
      (∑ A ∈ Finset.univ.filter p, if Q.1 ⊆ A ∧ Q.2 ⊆ A then 1 else 0)
        = (Fintype.card V
            - (Fintype.card U₁ + Fintype.card U₂ - Fintype.card T)).choose
          (m - (Fintype.card U₁ + Fintype.card U₂ - Fintype.card T)) := by
    intro Q hQ
    obtain ⟨h₁, h₂, hint⟩ := mem_pairWitnesses.mp hQ
    obtain ⟨hroot₁, hcard₁, -⟩ := mem_flagWitnesses.mp h₁
    obtain ⟨hroot₂, hcard₂, -⟩ := mem_flagWitnesses.mp h₂
    have hinter : Q.1 ∩ Q.2 = G.rootFinset :=
      hint.inter_eq (LabeledFlag.rootFinset_subset hroot₁)
        (LabeledFlag.rootFinset_subset hroot₂)
    have hUcard : (Q.1 ∪ Q.2).card
        = Fintype.card U₁ + Fintype.card U₂ - Fintype.card T := by
      have hadd := Finset.card_union_add_card_inter Q.1 Q.2
      rw [hinter, G.card_rootFinset, hcard₁, hcard₂] at hadd
      omega
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones, Finset.filter_filter]
    have hcount := card_superset_filter (R := Q.1 ∪ Q.2) (m := m)
      (by rw [hUcard]; exact hm)
      (fun A => p A ∧ (Q.1 ⊆ A ∧ Q.2 ⊆ A))
      (fun A => by
        show p A ∧ (Q.1 ⊆ A ∧ Q.2 ⊆ A) ↔ Q.1 ∪ Q.2 ⊆ A ∧ A.card = m
        rw [hp A]
        constructor
        · rintro ⟨⟨-, hAcard⟩, hQ₁, hQ₂⟩
          exact ⟨Finset.union_subset hQ₁ hQ₂, hAcard⟩
        · rintro ⟨hsub, hAcard⟩
          obtain ⟨hQ₁, hQ₂⟩ := Finset.union_subset_iff.mp hsub
          exact ⟨⟨fun t => hQ₁ (hroot₁ t), hAcard⟩, hQ₁, hQ₂⟩)
    rw [hcount, hUcard]
  rw [Finset.sum_congr rfl hper, Finset.sum_const, smul_eq_mul]
  rfl

/-- Grouping the intermediate subsets by the isomorphism class of the induced
sub-flag, with pairs of witnesses counted below each subset. -/
private lemma sum_over_pair_classes {W' : Type} [Fintype T] [Fintype U₁]
    [Fintype U₂] [Fintype V] [Fintype W'] (F₁ : LabeledFlag 𝕋 σ U₁)
    (F₂ : LabeledFlag 𝕋 σ U₂) (G : LabeledFlag 𝕋 σ V)
    (p : Finset V → Prop) [DecidablePred p]
    (hp : ∀ A, p A ↔ (∀ t, G.rootEmbed.toEmbedding t ∈ A)
      ∧ A.card = Fintype.card W') :
    ∑ A ∈ Finset.univ.filter p, pairRestrictCount F₁ F₂ G A
      = ∑ F' : Flag 𝕋 σ W', flagCount F'.out G * pairCount F₁ F₂ F'.out := by
  rw [index_eq_biUnion G p hp, Finset.sum_biUnion ?hdisj]
  case hdisj =>
    intro G₁ _ G₂ _ hne
    refine Finset.disjoint_left.mpr fun A hA₁ hA₂ => hne ?_
    obtain ⟨hr₁, -, ⟨i₁⟩⟩ := mem_flagWitnesses.mp hA₁
    obtain ⟨hr₂, -, ⟨i₂⟩⟩ := mem_flagWitnesses.mp hA₂
    calc G₁ = Quotient.mk _ G₁.out := (Quotient.out_eq G₁).symm
      _ = Quotient.mk _ G₂.out := Quotient.sound ⟨i₁.symm.trans i₂⟩
      _ = G₂ := Quotient.out_eq G₂
  refine Finset.sum_congr rfl fun F' _ => ?_
  have hconst : ∀ A ∈ flagWitnesses F'.out G,
      pairRestrictCount F₁ F₂ G A = pairCount F₁ F₂ F'.out := by
    intro A hA
    obtain ⟨hroot, -, ⟨i⟩⟩ := mem_flagWitnesses.mp hA
    rw [← pairCount_restrict F₁ F₂ G hroot]
    exact pairCount_congr_right F₁ F₂ i
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
  rfl

/-- Expanding a pair count over the isomorphism classes of an intermediate
size: the `t = 2` host-expansion at the level of counts. -/
private lemma pairCount_host_expansion {W' : Type} [Fintype T] [Fintype U₁]
    [Fintype U₂] [Fintype V] [Fintype W'] (F₁ : LabeledFlag 𝕋 σ U₁)
    (F₂ : LabeledFlag 𝕋 σ U₂) (G : LabeledFlag 𝕋 σ V)
    (hm : Fintype.card U₁ + Fintype.card U₂ - Fintype.card T
      ≤ Fintype.card W') :
    pairCount F₁ F₂ G *
        (Fintype.card V
            - (Fintype.card U₁ + Fintype.card U₂ - Fintype.card T)).choose
          (Fintype.card W'
            - (Fintype.card U₁ + Fintype.card U₂ - Fintype.card T))
      = ∑ F' : Flag 𝕋 σ W', flagCount F'.out G * pairCount F₁ F₂ F'.out := by
  classical
  rw [← sum_pairRestrictCount_index F₁ F₂ G hm
      (fun A => (∀ t, G.rootEmbed.toEmbedding t ∈ A)
        ∧ A.card = Fintype.card W')
      (fun _ => Iff.rfl),
    sum_over_pair_classes F₁ F₂ G _ (fun _ => Iff.rfl)]

/-- The roots lie in the complement of any witness's non-root part. -/
lemma LabeledFlag.root_mem_compl [Fintype T] [Fintype V]
    (G : LabeledFlag 𝕋 σ V) (W : Finset V) :
    ∀ t, G.rootEmbed.toEmbedding t ∈ Finset.univ \ (W \ G.rootFinset) := by
  intro t
  rw [Finset.mem_sdiff]
  exact ⟨Finset.mem_univ _, fun hmem =>
    (Finset.mem_sdiff.mp hmem).2
      (Finset.mem_map.mpr ⟨t, Finset.mem_univ t, rfl⟩)⟩

/-- Fibering the triple count over the witnesses of the last slot: each fiber
is a pair count in the induced sub-flag avoiding the witness's non-root
part. -/
private lemma tripleCount_fiber [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype U₃] [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁)
    (F₂ : LabeledFlag 𝕋 σ U₂) (F₃ : LabeledFlag 𝕋 σ U₃)
    (G : LabeledFlag 𝕋 σ V) :
    tripleCount F₁ F₂ F₃ G
      = ∑ W₃ ∈ flagWitnesses F₃ G,
          pairCount F₁ F₂
            (G.restrict (Finset.univ \ (W₃ \ G.rootFinset))
              (G.root_mem_compl W₃)) := by
  unfold tripleCount
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun P => P.2.2) (t := flagWitnesses F₃ G)
    (fun P hP => Finset.mem_coe.mpr
      (mem_tripleWitnesses.mp (Finset.mem_coe.mp hP)).2.2.1)]
  refine Finset.sum_congr rfl fun W₃ hW₃ => ?_
  rw [pairCount_restrict F₁ F₂ G (G.root_mem_compl W₃)]
  unfold pairRestrictCount
  refine Finset.card_bij' (fun P _ => (P.1, P.2.1))
    (fun Q _ => (Q.1, Q.2, W₃)) ?_ ?_ ?_ ?_
  · rintro ⟨P₁, P₂, P₃⟩ hP
    obtain ⟨hmem, heq⟩ := Finset.mem_filter.mp hP
    obtain ⟨h₁, h₂, -, h₁₂, h₁₃, h₂₃⟩ := mem_tripleWitnesses.mp hmem
    dsimp only at heq ⊢
    subst heq
    exact Finset.mem_filter.mpr ⟨mem_pairWitnesses.mpr ⟨h₁, h₂, h₁₂⟩,
      subset_sdiff_of_onlyRootsShared h₁₃,
      subset_sdiff_of_onlyRootsShared h₂₃⟩
  · rintro ⟨Q₁, Q₂⟩ hQ
    obtain ⟨hmem, hs₁, hs₂⟩ := Finset.mem_filter.mp hQ
    obtain ⟨h₁, h₂, h₁₂⟩ := mem_pairWitnesses.mp hmem
    exact Finset.mem_filter.mpr ⟨mem_tripleWitnesses.mpr
      ⟨h₁, h₂, hW₃, h₁₂,
        onlyRootsShared_of_subset_sdiff hs₁,
        onlyRootsShared_of_subset_sdiff hs₂⟩, rfl⟩
  · rintro ⟨P₁, P₂, P₃⟩ hP
    obtain ⟨-, heq⟩ := Finset.mem_filter.mp hP
    dsimp only at heq ⊢
    rw [← heq]
  · rintro ⟨Q₁, Q₂⟩ _
    rfl

/-- Fibering a pair count over the witnesses of its last slot. -/
private lemma pairCount_fiber [Fintype T] [Fintype U₁] [Fintype U₃]
    [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁) (F₃ : LabeledFlag 𝕋 σ U₃)
    (G : LabeledFlag 𝕋 σ V) :
    pairCount F₁ F₃ G
      = ∑ W₃ ∈ flagWitnesses F₃ G,
          flagCount F₁
            (G.restrict (Finset.univ \ (W₃ \ G.rootFinset))
              (G.root_mem_compl W₃)) := by
  unfold pairCount
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun P => P.2) (t := flagWitnesses F₃ G)
    (fun P hP => Finset.mem_coe.mpr
      (mem_pairWitnesses.mp (Finset.mem_coe.mp hP)).2.1)]
  refine Finset.sum_congr rfl fun W₃ hW₃ => ?_
  rw [flagCount_restrict F₁ G (G.root_mem_compl W₃)]
  refine Finset.card_bij' (fun P _ => P.1) (fun W _ => (W, W₃)) ?_ ?_ ?_ ?_
  · rintro ⟨P₁, P₂⟩ hP
    obtain ⟨hmem, heq⟩ := Finset.mem_filter.mp hP
    obtain ⟨h₁, -, h₁₂⟩ := mem_pairWitnesses.mp hmem
    dsimp only at heq ⊢
    subst heq
    exact Finset.mem_filter.mpr ⟨h₁, subset_sdiff_of_onlyRootsShared h₁₂⟩
  · intro W hW
    obtain ⟨hmem, hsub⟩ := Finset.mem_filter.mp hW
    exact Finset.mem_filter.mpr ⟨mem_pairWitnesses.mpr
      ⟨hmem, hW₃, onlyRootsShared_of_subset_sdiff hsub⟩, rfl⟩
  · rintro ⟨P₁, P₂⟩ hP
    obtain ⟨-, heq⟩ := Finset.mem_filter.mp hP
    dsimp only at heq ⊢
    rw [← heq]
  · intro W _
    rfl

/-- The master chain rule at the level of counts. -/
private lemma tripleCount_chain {W' : Type} [Fintype T] [Fintype U₁]
    [Fintype U₂] [Fintype U₃] [Fintype V] [Fintype W']
    (F₁ : LabeledFlag 𝕋 σ U₁) (F₂ : LabeledFlag 𝕋 σ U₂)
    (F₃ : LabeledFlag 𝕋 σ U₃) (G : LabeledFlag 𝕋 σ V)
    (hm : Fintype.card U₁ + Fintype.card U₂ - Fintype.card T
      ≤ Fintype.card W') :
    ∑ F' : Flag 𝕋 σ W', pairCount F₁ F₂ F'.out * pairCount F'.out F₃ G
      = tripleCount F₁ F₂ F₃ G *
        ((Fintype.card V - (Fintype.card U₃ - Fintype.card T))
            - (Fintype.card U₁ + Fintype.card U₂ - Fintype.card T)).choose
          (Fintype.card W'
            - (Fintype.card U₁ + Fintype.card U₂ - Fintype.card T)) := by
  have hDcard : ∀ W₃ ∈ flagWitnesses F₃ G,
      ∀ inst : Fintype {x // x ∈ Finset.univ \ (W₃ \ G.rootFinset)},
      @Fintype.card _ inst
        = Fintype.card V - (Fintype.card U₃ - Fintype.card T) := by
    intro W₃ hW₃ inst
    obtain ⟨hroot, hcard, -⟩ := mem_flagWitnesses.mp hW₃
    rw [Subsingleton.elim inst
      (inferInstance : Fintype {x // x ∈ Finset.univ \ (W₃ \ G.rootFinset)})]
    rw [Fintype.card_coe, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, Finset.card_sdiff,
      Finset.inter_eq_left.mpr (LabeledFlag.rootFinset_subset hroot),
      hcard, G.card_rootFinset]
  calc ∑ F' : Flag 𝕋 σ W', pairCount F₁ F₂ F'.out * pairCount F'.out F₃ G
      = ∑ F' : Flag 𝕋 σ W', ∑ W₃ ∈ flagWitnesses F₃ G,
          flagCount F'.out
              (G.restrict (Finset.univ \ (W₃ \ G.rootFinset))
                (G.root_mem_compl W₃)) * pairCount F₁ F₂ F'.out := by
        refine Finset.sum_congr rfl fun F' _ => ?_
        rw [mul_comm, pairCount_fiber F'.out F₃ G, Finset.sum_mul]
    _ = ∑ W₃ ∈ flagWitnesses F₃ G, ∑ F' : Flag 𝕋 σ W',
          flagCount F'.out
              (G.restrict (Finset.univ \ (W₃ \ G.rootFinset))
                (G.root_mem_compl W₃)) * pairCount F₁ F₂ F'.out :=
        Finset.sum_comm
    _ = ∑ W₃ ∈ flagWitnesses F₃ G,
          pairCount F₁ F₂
              (G.restrict (Finset.univ \ (W₃ \ G.rootFinset))
                (G.root_mem_compl W₃)) *
            ((Fintype.card V - (Fintype.card U₃ - Fintype.card T))
                - (Fintype.card U₁ + Fintype.card U₂
                  - Fintype.card T)).choose
              (Fintype.card W'
                - (Fintype.card U₁ + Fintype.card U₂ - Fintype.card T)) := by
        refine Finset.sum_congr rfl fun W₃ hW₃ => ?_
        rw [← pairCount_host_expansion F₁ F₂ _ hm, hDcard W₃ hW₃ _]
    _ = _ := by
        rw [← Finset.sum_mul, ← tripleCount_fiber]

/-- The master chain rule for labeled flags (Razborov Lemma 2.2): a triple
density is the sum over intermediate flags covering the first two slots of a
product of pair densities. -/
theorem flagTripleDensity_chain {W' : Type} [Fintype T] [Fintype U₁]
    [Fintype U₂] [Fintype U₃] [Fintype V] [Fintype W']
    (h₁ : Fintype.card U₁ + Fintype.card U₂
      ≤ Fintype.card W' + Fintype.card T)
    (h₂ : Fintype.card W' + Fintype.card U₃
      ≤ Fintype.card V + Fintype.card T)
    (F₁ : LabeledFlag 𝕋 σ U₁) (F₂ : LabeledFlag 𝕋 σ U₂)
    (F₃ : LabeledFlag 𝕋 σ U₃) (G : LabeledFlag 𝕋 σ V) :
    flagTripleDensity F₁ F₂ F₃ G
      = ∑ F' : Flag 𝕋 σ W',
          flagPairDensity F₁ F₂ F'.out * flagPairDensity F'.out F₃ G := by
  have hk₁ : Fintype.card T ≤ Fintype.card U₁ :=
    Fintype.card_le_of_injective _ F₁.rootEmbed.toEmbedding.injective
  have hk₂ : Fintype.card T ≤ Fintype.card U₂ :=
    Fintype.card_le_of_injective _ F₂.rootEmbed.toEmbedding.injective
  have hk₃ : Fintype.card T ≤ Fintype.card U₃ :=
    Fintype.card_le_of_injective _ F₃.rootEmbed.toEmbedding.injective
  have c1 : ((tripleChoose (Fintype.card V - Fintype.card T)
      (Fintype.card U₁ - Fintype.card T) (Fintype.card U₂ - Fintype.card T)
      (Fintype.card U₃ - Fintype.card T) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (tripleChoose_pos (by omega)).ne'
  have c2 : ((pairChoose (Fintype.card W' - Fintype.card T)
      (Fintype.card U₁ - Fintype.card T)
      (Fintype.card U₂ - Fintype.card T) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (pairChoose_pos (by omega)).ne'
  have c3 : ((pairChoose (Fintype.card V - Fintype.card T)
      (Fintype.card W' - Fintype.card T)
      (Fintype.card U₃ - Fintype.card T) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (pairChoose_pos (by omega)).ne'
  have keyN := tripleChoose_mul_choose
    (a := Fintype.card V - Fintype.card T)
    (a' := Fintype.card W' - Fintype.card T)
    (r₁ := Fintype.card U₁ - Fintype.card T)
    (r₂ := Fintype.card U₂ - Fintype.card T)
    (r₃ := Fintype.card U₃ - Fintype.card T)
    (by omega) (by omega)
  have hCeq : ((Fintype.card V - (Fintype.card U₃ - Fintype.card T))
        - (Fintype.card U₁ + Fintype.card U₂ - Fintype.card T)).choose
        (Fintype.card W'
          - (Fintype.card U₁ + Fintype.card U₂ - Fintype.card T))
      = ((Fintype.card V - Fintype.card T)
          - (Fintype.card U₁ - Fintype.card T)
          - (Fintype.card U₂ - Fintype.card T)
          - (Fintype.card U₃ - Fintype.card T)).choose
        ((Fintype.card W' - Fintype.card T)
          - (Fintype.card U₁ - Fintype.card T)
          - (Fintype.card U₂ - Fintype.card T)) := by
    congr 1 <;> omega
  have hN := tripleCount_chain (W' := W') F₁ F₂ F₃ G (by omega)
  rw [hCeq] at hN
  have keyQ : ((tripleChoose (Fintype.card V - Fintype.card T)
        (Fintype.card U₁ - Fintype.card T)
        (Fintype.card U₂ - Fintype.card T)
        (Fintype.card U₃ - Fintype.card T) : ℕ) : ℚ) *
        (((Fintype.card V - Fintype.card T)
            - (Fintype.card U₁ - Fintype.card T)
            - (Fintype.card U₂ - Fintype.card T)
            - (Fintype.card U₃ - Fintype.card T)).choose
          ((Fintype.card W' - Fintype.card T)
            - (Fintype.card U₁ - Fintype.card T)
            - (Fintype.card U₂ - Fintype.card T)) : ℕ)
      = ((pairChoose (Fintype.card W' - Fintype.card T)
          (Fintype.card U₁ - Fintype.card T)
          (Fintype.card U₂ - Fintype.card T) : ℕ) : ℚ) *
        ((pairChoose (Fintype.card V - Fintype.card T)
          (Fintype.card W' - Fintype.card T)
          (Fintype.card U₃ - Fintype.card T) : ℕ) : ℚ) := by
    exact_mod_cast keyN
  have hchainQ : ∑ F' : Flag 𝕋 σ W',
        (pairCount F₁ F₂ F'.out : ℚ) * (pairCount F'.out F₃ G : ℚ)
      = (tripleCount F₁ F₂ F₃ G : ℚ) *
        (((Fintype.card V - Fintype.card T)
            - (Fintype.card U₁ - Fintype.card T)
            - (Fintype.card U₂ - Fintype.card T)
            - (Fintype.card U₃ - Fintype.card T)).choose
          ((Fintype.card W' - Fintype.card T)
            - (Fintype.card U₁ - Fintype.card T)
            - (Fintype.card U₂ - Fintype.card T)) : ℕ) := by
    calc ∑ F' : Flag 𝕋 σ W',
          (pairCount F₁ F₂ F'.out : ℚ) * (pairCount F'.out F₃ G : ℚ)
        = ((∑ F' : Flag 𝕋 σ W',
            pairCount F₁ F₂ F'.out * pairCount F'.out F₃ G : ℕ) : ℚ) := by
          push_cast
          rfl
      _ = _ := by
          rw [hN]
          push_cast
          ring
  have hsummand : ∀ F' : Flag 𝕋 σ W',
      flagPairDensity F₁ F₂ F'.out * flagPairDensity F'.out F₃ G
        = ((pairCount F₁ F₂ F'.out : ℚ) * (pairCount F'.out F₃ G : ℚ)) /
          (((pairChoose (Fintype.card W' - Fintype.card T)
              (Fintype.card U₁ - Fintype.card T)
              (Fintype.card U₂ - Fintype.card T) : ℕ) : ℚ) *
            ((pairChoose (Fintype.card V - Fintype.card T)
              (Fintype.card W' - Fintype.card T)
              (Fintype.card U₃ - Fintype.card T) : ℕ) : ℚ)) := by
    intro F'
    simp only [flagPairDensity]
    rw [div_mul_div_comm]
  have lhs_eq : flagTripleDensity F₁ F₂ F₃ G
      = (tripleCount F₁ F₂ F₃ G : ℚ) /
        ((tripleChoose (Fintype.card V - Fintype.card T)
          (Fintype.card U₁ - Fintype.card T)
          (Fintype.card U₂ - Fintype.card T)
          (Fintype.card U₃ - Fintype.card T) : ℕ) : ℚ) := rfl
  rw [lhs_eq, Finset.sum_congr rfl fun F' _ => hsummand F',
    ← Finset.sum_div, hchainQ, div_eq_div_iff c1 (mul_ne_zero c2 c3)]
  linear_combination (-(tripleCount F₁ F₂ F₃ G : ℚ)) * keyQ

/-- **The master chain rule** (Razborov Lemma 2.2): a triple density of flags
is the sum, over intermediate flags of any size accommodating the first two
slots, of the pair density of those slots in the intermediate flag times the
pair density of the intermediate flag with the last slot. -/
theorem subflagTripleDensity_chain {W' : Type} [Fintype T] [Fintype U₁]
    [Fintype U₂] [Fintype U₃] [Fintype V] [Fintype W']
    (h₁ : Fintype.card U₁ + Fintype.card U₂
      ≤ Fintype.card W' + Fintype.card T)
    (h₂ : Fintype.card W' + Fintype.card U₃
      ≤ Fintype.card V + Fintype.card T)
    (F₁ : Flag 𝕋 σ U₁) (F₂ : Flag 𝕋 σ U₂) (F₃ : Flag 𝕋 σ U₃)
    (G : Flag 𝕋 σ V) :
    subflagTripleDensity F₁ F₂ F₃ G
      = ∑ F' : Flag 𝕋 σ W',
          subflagPairDensity F₁ F₂ F' * subflagPairDensity F' F₃ G := by
  refine Quotient.inductionOn₂ F₁ F₂ fun f₁ f₂ =>
    Quotient.inductionOn₂ F₃ G fun f₃ g => ?_
  show flagTripleDensity f₁ f₂ f₃ g = _
  rw [flagTripleDensity_chain h₁ h₂ f₁ f₂ f₃ g]
  refine Finset.sum_congr rfl fun F' _ => ?_
  conv_rhs => rw [← Quotient.out_eq F']
  rfl

/-- The chain rule `₂₁`: expanding the host of a pair density over
intermediate flags. -/
theorem subflagPairDensity_chain_host {W' : Type} [Fintype T] [Fintype U₁]
    [Fintype U₂] [Fintype V] [Fintype W']
    (h₁ : Fintype.card U₁ + Fintype.card U₂
      ≤ Fintype.card W' + Fintype.card T)
    (h₂ : Fintype.card W' ≤ Fintype.card V)
    (F₁ : Flag 𝕋 σ U₁) (F₂ : Flag 𝕋 σ U₂) (G : Flag 𝕋 σ V) :
    subflagPairDensity F₁ F₂ G
      = ∑ F' : Flag 𝕋 σ W',
          subflagPairDensity F₁ F₂ F' * subflagDensity F' G := by
  have hσ : 𝕋.Mem σ := F₁.out.type_mem
  rw [← subflagTripleDensity_ofType_right hσ F₁ F₂ G,
    subflagTripleDensity_chain h₁
      (by simpa using Nat.add_le_add_right h₂ (Fintype.card T)) F₁ F₂ _ G]
  refine Finset.sum_congr rfl fun F' _ => ?_
  rw [subflagPairDensity_ofType_right]

/-! ## The product approximation: counting layer

In a large host, the pair density differs from the product of the single
densities by `O(1/|G|)`: the finite products-vs-pairs estimate powering
square positivity. This section provides the counting layer — the pair
count is sandwiched between the product of the witness counts and that
product minus a per-witness collision defect. -/

private lemma root_subset_iff [Fintype T] [Fintype V]
    (G : LabeledFlag 𝕋 σ V) (W : Finset V) :
    (∀ t, G.rootEmbed.toEmbedding t ∈ W) ↔ G.rootFinset ⊆ W :=
  ⟨LabeledFlag.rootFinset_subset,
    fun h t => h (Finset.mem_map.mpr ⟨t, Finset.mem_univ t, rfl⟩)⟩

/-- The number of root-containing `m`-subsets sharing only roots with a
fixed root-containing set `W₁`: choose the non-root part outside `W₁`. -/
lemma card_onlyRootsShared [Fintype T] [Fintype V] (G : LabeledFlag 𝕋 σ V)
    {W₁ : Finset V} (hW₁ : G.rootFinset ⊆ W₁) {m : ℕ}
    (hm : Fintype.card T ≤ m) (q : Finset V → Prop) [DecidablePred q]
    (hq : ∀ W, q W ↔ (∀ t, G.rootEmbed.toEmbedding t ∈ W) ∧ W.card = m
      ∧ OnlyRootsShared G W₁ W) :
    (Finset.univ.filter q).card
      = (Fintype.card V - W₁.card).choose (m - Fintype.card T) := by
  have hcard : ((Finset.univ \ W₁).powersetCard (m - Fintype.card T)).card
      = (Fintype.card V - W₁.card).choose (m - Fintype.card T) := by
    rw [Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ]
  rw [← hcard]
  refine Finset.card_bij' (fun W _ => W \ G.rootFinset)
    (fun X _ => X ∪ G.rootFinset) ?_ ?_ ?_ ?_
  · intro W hW
    obtain ⟨hroot, hcardW, hcond⟩ := (hq W).mp (Finset.mem_filter.mp hW).2
    have hRW : G.rootFinset ⊆ W := LabeledFlag.rootFinset_subset hroot
    rw [Finset.mem_powersetCard]
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [Finset.mem_sdiff] at hx ⊢
      exact ⟨Finset.mem_univ _, fun hxW₁ => hx.2 (hcond x hxW₁ hx.1)⟩
    · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hRW, hcardW,
        G.card_rootFinset]
  · intro X hX
    obtain ⟨hXsub, hXcard⟩ := Finset.mem_powersetCard.mp hX
    have hdisj : ∀ x ∈ X, x ∉ G.rootFinset := fun x hxX hxR =>
      (Finset.mem_sdiff.mp (hXsub hxX)).2 (hW₁ hxR)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hq _).mpr ⟨fun t => ?_, ?_, fun x hxW₁ hxU => ?_⟩⟩
    · exact Finset.mem_union_right _
        (Finset.mem_map.mpr ⟨t, Finset.mem_univ t, rfl⟩)
    · rw [Finset.card_union_of_disjoint (Finset.disjoint_left.mpr hdisj),
        hXcard, G.card_rootFinset]
      omega
    · rcases Finset.mem_union.mp hxU with hxX | hxR
      · exact absurd hxW₁ ((Finset.mem_sdiff.mp (hXsub hxX)).2)
      · exact hxR
  · intro W hW
    obtain ⟨hroot, -, -⟩ := (hq W).mp (Finset.mem_filter.mp hW).2
    dsimp only
    exact Finset.sdiff_union_of_subset (LabeledFlag.rootFinset_subset hroot)
  · intro X hX
    obtain ⟨hXsub, -⟩ := Finset.mem_powersetCard.mp hX
    dsimp only
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact h1
      · exact absurd h1 h2
    · intro hx
      exact ⟨Or.inl hx, fun hxR =>
        (Finset.mem_sdiff.mp (hXsub hx)).2 (hW₁ hxR)⟩

/-- The fiber of the pair witnesses over a fixed first witness is the set
of compatible second witnesses. -/
private lemma pair_fiber_card [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁) (F₂ : LabeledFlag 𝕋 σ U₂)
    (G : LabeledFlag 𝕋 σ V) {W₁ : Finset V}
    (hW₁ : W₁ ∈ flagWitnesses F₁ G) :
    ((pairWitnesses F₁ F₂ G).filter (fun p => p.1 = W₁)).card
      = ((flagWitnesses F₂ G).filter
          (fun W₂ => OnlyRootsShared G W₁ W₂)).card := by
  refine Finset.card_bij' (fun p _ => p.2) (fun W₂ _ => (W₁, W₂)) ?_ ?_ ?_ ?_
  · rintro ⟨p₁, p₂⟩ hp
    obtain ⟨hmem, hfst⟩ := Finset.mem_filter.mp hp
    obtain ⟨h1, h2, hcond⟩ := mem_pairWitnesses.mp hmem
    dsimp only at hfst ⊢
    subst hfst
    exact Finset.mem_filter.mpr ⟨h2, hcond⟩
  · intro W₂ hW₂
    obtain ⟨hmem, hcond⟩ := Finset.mem_filter.mp hW₂
    exact Finset.mem_filter.mpr
      ⟨mem_pairWitnesses.mpr ⟨hW₁, hmem, hcond⟩, rfl⟩
  · rintro ⟨p₁, p₂⟩ hp
    obtain ⟨-, hfst⟩ := Finset.mem_filter.mp hp
    dsimp only at hfst ⊢
    rw [hfst]
  · intro W₂ _
    rfl

/-- The deferred upper bound: the pair count is at most the pair
normalizer. -/
theorem pairCount_le_pairChoose [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁) (F₂ : LabeledFlag 𝕋 σ U₂)
    (G : LabeledFlag 𝕋 σ V) :
    pairCount F₁ F₂ G
      ≤ pairChoose (Fintype.card V - Fintype.card T)
          (Fintype.card U₁ - Fintype.card T)
          (Fintype.card U₂ - Fintype.card T) := by
  classical
  have hk₁ : Fintype.card T ≤ Fintype.card U₁ :=
    Fintype.card_le_of_injective _ F₁.rootEmbed.toEmbedding.injective
  have hk₂ : Fintype.card T ≤ Fintype.card U₂ :=
    Fintype.card_le_of_injective _ F₂.rootEmbed.toEmbedding.injective
  rw [pairCount, Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := flagWitnesses F₁ G)
    (fun p hp => Finset.mem_coe.mpr
      (mem_pairWitnesses.mp (Finset.mem_coe.mp hp)).1)]
  calc ∑ W₁ ∈ flagWitnesses F₁ G,
        ((pairWitnesses F₁ F₂ G).filter (fun p => p.1 = W₁)).card
      ≤ ∑ _W₁ ∈ flagWitnesses F₁ G,
          (Fintype.card V - Fintype.card U₁).choose
            (Fintype.card U₂ - Fintype.card T) := by
        refine Finset.sum_le_sum fun W₁ hW₁ => ?_
        obtain ⟨hroot₁, hcard₁, -⟩ := mem_flagWitnesses.mp hW₁
        rw [pair_fiber_card F₁ F₂ G hW₁,
          show (Fintype.card V - Fintype.card U₁).choose
              (Fintype.card U₂ - Fintype.card T)
            = (Fintype.card V - W₁.card).choose
              (Fintype.card U₂ - Fintype.card T) by rw [hcard₁],
          ← card_onlyRootsShared G (LabeledFlag.rootFinset_subset hroot₁)
            hk₂ (fun W₂ => (∀ t, G.rootEmbed.toEmbedding t ∈ W₂)
              ∧ W₂.card = Fintype.card U₂ ∧ OnlyRootsShared G W₁ W₂)
            (fun _ => Iff.rfl)]
        apply Finset.card_le_card
        intro W₂ hW₂
        obtain ⟨hmem, hcond⟩ := Finset.mem_filter.mp hW₂
        obtain ⟨hroot₂, hcard₂, -⟩ := mem_flagWitnesses.mp hmem
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hroot₂, hcard₂, hcond⟩
    _ = flagCount F₁ G *
          (Fintype.card V - Fintype.card U₁).choose
            (Fintype.card U₂ - Fintype.card T) := by
        rw [Finset.sum_const, smul_eq_mul]
        rfl
    _ ≤ (Fintype.card V - Fintype.card T).choose
          (Fintype.card U₁ - Fintype.card T) *
          (Fintype.card V - Fintype.card U₁).choose
            (Fintype.card U₂ - Fintype.card T) :=
        Nat.mul_le_mul_right _ (flagCount_le_choose F₁ G)
    _ = _ := by
        rw [pairChoose]
        congr 2
        omega

/-- The sandwich defect: the product of the witness counts exceeds the
pair count by at most a per-witness collision term. -/
theorem mul_flagCount_sub_pairCount_le [Fintype T] [Fintype U₁] [Fintype U₂]
    [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁) (F₂ : LabeledFlag 𝕋 σ U₂)
    (G : LabeledFlag 𝕋 σ V) :
    flagCount F₁ G * flagCount F₂ G - pairCount F₁ F₂ G
      ≤ flagCount F₁ G *
        ((Fintype.card V - Fintype.card T).choose
            (Fintype.card U₂ - Fintype.card T)
          - (Fintype.card V - Fintype.card U₁).choose
            (Fintype.card U₂ - Fintype.card T)) := by
  classical
  have hk₂ : Fintype.card T ≤ Fintype.card U₂ :=
    Fintype.card_le_of_injective _ F₂.rootEmbed.toEmbedding.injective
  rw [pairCount, Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := flagWitnesses F₁ G)
    (fun p hp => Finset.mem_coe.mpr
      (mem_pairWitnesses.mp (Finset.mem_coe.mp hp)).1)]
  rw [show flagCount F₁ G * flagCount F₂ G
      = ∑ _W₁ ∈ flagWitnesses F₁ G, flagCount F₂ G by
    rw [Finset.sum_const, smul_eq_mul]; rfl]
  rw [← Finset.sum_tsub_distrib _ (fun W₁ hW₁ => by
    rw [pair_fiber_card F₁ F₂ G hW₁]
    exact Finset.card_le_card (Finset.filter_subset _ _))]
  rw [show flagCount F₁ G *
      ((Fintype.card V - Fintype.card T).choose
          (Fintype.card U₂ - Fintype.card T)
        - (Fintype.card V - Fintype.card U₁).choose
          (Fintype.card U₂ - Fintype.card T))
      = ∑ _W₁ ∈ flagWitnesses F₁ G,
          ((Fintype.card V - Fintype.card T).choose
              (Fintype.card U₂ - Fintype.card T)
            - (Fintype.card V - Fintype.card U₁).choose
              (Fintype.card U₂ - Fintype.card T)) by
    rw [Finset.sum_const, smul_eq_mul]; rfl]
  refine Finset.sum_le_sum fun W₁ hW₁ => ?_
  obtain ⟨hroot₁, hcard₁, -⟩ := mem_flagWitnesses.mp hW₁
  rw [pair_fiber_card F₁ F₂ G hW₁]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := flagWitnesses F₂ G) (p := fun W₂ => OnlyRootsShared G W₁ W₂)
  have hcand : ((Finset.univ.filter
      (fun W₂ : Finset V => (∀ t, G.rootEmbed.toEmbedding t ∈ W₂)
        ∧ W₂.card = Fintype.card U₂)).card)
      = (Fintype.card V - Fintype.card T).choose
        (Fintype.card U₂ - Fintype.card T) := by
    rw [← G.card_rootFinset]
    refine card_superset_filter (R := G.rootFinset)
      (m := Fintype.card U₂) (by rw [G.card_rootFinset]; exact hk₂) _
      fun W₂ => ?_
    rw [root_subset_iff]
  have hcandD : ((Finset.univ.filter
      (fun W₂ : Finset V => ((∀ t, G.rootEmbed.toEmbedding t ∈ W₂)
        ∧ W₂.card = Fintype.card U₂) ∧ OnlyRootsShared G W₁ W₂)).card)
      = (Fintype.card V - Fintype.card U₁).choose
        (Fintype.card U₂ - Fintype.card T) := by
    rw [show (Fintype.card V - Fintype.card U₁).choose
        (Fintype.card U₂ - Fintype.card T)
      = (Fintype.card V - W₁.card).choose
        (Fintype.card U₂ - Fintype.card T) by rw [hcard₁]]
    refine card_onlyRootsShared G (LabeledFlag.rootFinset_subset hroot₁)
      hk₂ _ fun W₂ => ?_
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  have hsplitCand := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter
      (fun W₂ : Finset V => (∀ t, G.rootEmbed.toEmbedding t ∈ W₂)
        ∧ W₂.card = Fintype.card U₂))
    (p := fun W₂ => OnlyRootsShared G W₁ W₂)
  have hsub : ((flagWitnesses F₂ G).filter
      (fun W₂ => ¬OnlyRootsShared G W₁ W₂)).card
      ≤ ((Finset.univ.filter
        (fun W₂ : Finset V => (∀ t, G.rootEmbed.toEmbedding t ∈ W₂)
          ∧ W₂.card = Fintype.card U₂)).filter
        (fun W₂ => ¬OnlyRootsShared G W₁ W₂)).card := by
    apply Finset.card_le_card
    intro W₂ hW₂
    obtain ⟨hmem, hcond⟩ := Finset.mem_filter.mp hW₂
    obtain ⟨hroot₂, hcard₂, -⟩ := mem_flagWitnesses.mp hmem
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hroot₂, hcard₂⟩, hcond⟩
  have hfilter_eq : ((Finset.univ.filter
      (fun W₂ : Finset V => (∀ t, G.rootEmbed.toEmbedding t ∈ W₂)
        ∧ W₂.card = Fintype.card U₂)).filter
      (fun W₂ => OnlyRootsShared G W₁ W₂)).card
      = ((Finset.univ.filter
        (fun W₂ : Finset V => ((∀ t, G.rootEmbed.toEmbedding t ∈ W₂)
          ∧ W₂.card = Fintype.card U₂) ∧ OnlyRootsShared G W₁ W₂)).card) := by
    rw [Finset.filter_filter]
  have hN₂ : flagCount F₂ G = (flagWitnesses F₂ G).card := rfl
  omega

/-- The pair count is at most the product of the witness counts. -/
theorem pairCount_le_mul [Fintype T] [Fintype U₁] [Fintype U₂] [Fintype V]
    (F₁ : LabeledFlag 𝕋 σ U₁) (F₂ : LabeledFlag 𝕋 σ U₂)
    (G : LabeledFlag 𝕋 σ V) :
    pairCount F₁ F₂ G ≤ flagCount F₁ G * flagCount F₂ G := by
  calc pairCount F₁ F₂ G
      ≤ ((flagWitnesses F₁ G) ×ˢ (flagWitnesses F₂ G)).card := by
        apply Finset.card_le_card
        intro p hp
        obtain ⟨h1, h2, -⟩ := mem_pairWitnesses.mp hp
        exact Finset.mem_product.mpr ⟨h1, h2⟩
    _ = _ := Finset.card_product _ _

/-- Telescoping bound: shifting a binomial's population by `s` changes it
by at most `s` times the one-smaller coefficient. -/
private lemma choose_sub_choose_le {a m : ℕ} :
    ∀ s : ℕ, s ≤ a →
      a.choose m - (a - s).choose m ≤ s * (a - 1).choose (m - 1) := by
  intro s
  induction s with
  | zero =>
    intro _
    simp
  | succ n ih =>
    intro hs
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    have h1 := ih (by omega)
    obtain ⟨m', rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hm)
    have hb : a - n = (a - n - 1) + 1 := by omega
    have hpas : (a - n).choose (m' + 1)
        = (a - n - 1).choose m' + (a - n - 1).choose (m' + 1) := by
      rw [hb, Nat.choose_succ_succ]
      simp only [Nat.add_sub_cancel]
    have hmono : (a - n - 1).choose m' ≤ (a - 1).choose m' :=
      Nat.choose_le_choose _ (by omega)
    rw [show a - (n + 1) = a - n - 1 from by omega]
    simp only [Nat.succ_sub_one] at h1 ⊢
    calc a.choose (m' + 1) - (a - n - 1).choose (m' + 1)
        ≤ (a.choose (m' + 1) - (a - n).choose (m' + 1))
          + (a - n - 1).choose m' := by omega
      _ ≤ n * (a - 1).choose m' + (a - 1).choose m' :=
          Nat.add_le_add h1 hmono
      _ = (n + 1) * (a - 1).choose m' := by ring

/-- Absorption form of the telescoping bound, scaled to clear
denominators: `a·(C(a,m) − C(a−s,m)) ≤ s·m·C(a,m)`. -/
private lemma mul_choose_sub_choose_le {a m : ℕ} (s : ℕ) (hs : s ≤ a) :
    a * (a.choose m - (a - s).choose m) ≤ s * m * a.choose m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simp
  have h1 := choose_sub_choose_le (a := a) (m := m) s hs
  have habs : a * (a - 1).choose (m - 1) = a.choose m * m := by
    have h := Nat.add_one_mul_choose_eq (a - 1) (m - 1)
    rw [show a - 1 + 1 = a from by omega,
      show m - 1 + 1 = m from by omega] at h
    exact h
  calc a * (a.choose m - (a - s).choose m)
      ≤ a * (s * (a - 1).choose (m - 1)) := Nat.mul_le_mul_left _ h1
    _ = s * (a * (a - 1).choose (m - 1)) := by ring
    _ = s * (a.choose m * m) := by rw [habs]
    _ = s * m * a.choose m := by ring

/-- The rational core of the product approximation, over abstract counts:
if the numerator defect is bounded both ways by `C₁·D₂·(C₂−D₂)`, the
densities differ by at most `(C₂−D₂)/C₂`. -/
private lemma abs_div_sub_div_le {P N₁ N₂ C₁ C₂ D₂ : ℕ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hD₂ : 0 < D₂)
    (h₁ : P * C₂ ≤ N₁ * N₂ * D₂ + C₁ * D₂ * (C₂ - D₂))
    (h₂ : N₁ * N₂ * D₂ ≤ P * C₂ + C₁ * D₂ * (C₂ - D₂)) :
    |(P : ℚ) / ((C₁ * D₂ : ℕ) : ℚ)
        - (N₁ : ℚ) / ((C₁ : ℕ) : ℚ) * ((N₂ : ℚ) / ((C₂ : ℕ) : ℚ))|
      ≤ ((C₂ - D₂ : ℕ) : ℚ) / ((C₂ : ℕ) : ℚ) := by
  have hC₁Q : (0 : ℚ) < (C₁ : ℚ) := by exact_mod_cast hC₁
  have hC₂Q : (0 : ℚ) < (C₂ : ℚ) := by exact_mod_cast hC₂
  have hD₂Q : (0 : ℚ) < (D₂ : ℚ) := by exact_mod_cast hD₂
  have hden : (0 : ℚ) < (C₁ : ℚ) * C₂ * D₂ :=
    mul_pos (mul_pos hC₁Q hC₂Q) hD₂Q
  have hrepr : (P : ℚ) / ((C₁ * D₂ : ℕ) : ℚ)
      - (N₁ : ℚ) / ((C₁ : ℕ) : ℚ) * ((N₂ : ℚ) / ((C₂ : ℕ) : ℚ))
      = ((P : ℚ) * C₂ - (N₁ : ℚ) * N₂ * D₂)
        / ((C₁ : ℚ) * C₂ * D₂) := by
    push_cast
    field_simp
  rw [hrepr, abs_div, abs_of_pos hden]
  rw [div_le_div_iff₀ hden hC₂Q]
  have habs : |(P : ℚ) * C₂ - (N₁ : ℚ) * N₂ * D₂|
      ≤ ((C₁ * D₂ * (C₂ - D₂) : ℕ) : ℚ) := by
    rw [abs_sub_le_iff]
    constructor
    · rw [sub_le_iff_le_add, add_comm]
      exact_mod_cast h₁
    · rw [sub_le_iff_le_add, add_comm]
      exact_mod_cast h₂
  calc |(P : ℚ) * C₂ - (N₁ : ℚ) * N₂ * D₂| * (C₂ : ℚ)
      ≤ ((C₁ * D₂ * (C₂ - D₂) : ℕ) : ℚ) * (C₂ : ℚ) :=
        mul_le_mul_of_nonneg_right habs (le_of_lt hC₂Q)
    _ = ((C₂ - D₂ : ℕ) : ℚ) * ((C₁ : ℚ) * C₂ * D₂) := by
        push_cast
        ring

private lemma div_le_div_of_mul_le {x y a b : ℕ} (hy : 0 < y) (ha : 0 < a)
    (hmul : a * x ≤ b * y) :
    ((x : ℕ) : ℚ) / ((y : ℕ) : ℚ) ≤ ((b : ℕ) : ℚ) / ((a : ℕ) : ℚ) := by
  rw [div_le_div_iff₀ (by exact_mod_cast hy) (by exact_mod_cast ha)]
  rw [show ((x : ℕ) : ℚ) * ((a : ℕ) : ℚ) = ((a * x : ℕ) : ℚ) by
    push_cast; ring]
  rw [show ((b : ℕ) : ℚ) * ((y : ℕ) : ℚ) = ((b * y : ℕ) : ℚ) by
    push_cast; ring]
  exact_mod_cast hmul

/-- **The product approximation**: in a host with room for disjoint
copies, the pair density differs from the product of the single densities
by at most `(|F₁|−|σ|)·(|F₂|−|σ|) / (|G|−|σ|)`. The finite estimate
behind square positivity. -/
theorem abs_flagPairDensity_sub_mul_le [Fintype T] [Fintype U₁]
    [Fintype U₂] [Fintype V] (F₁ : LabeledFlag 𝕋 σ U₁)
    (F₂ : LabeledFlag 𝕋 σ U₂) (G : LabeledFlag 𝕋 σ V)
    (h : Fintype.card U₁ + Fintype.card U₂
      ≤ Fintype.card V + Fintype.card T)
    (hV : Fintype.card T < Fintype.card V) :
    |flagPairDensity F₁ F₂ G - flagDensity F₁ G * flagDensity F₂ G|
      ≤ (((Fintype.card U₁ - Fintype.card T) *
            (Fintype.card U₂ - Fintype.card T) : ℕ) : ℚ) /
        ((Fintype.card V - Fintype.card T : ℕ) : ℚ) := by
  classical
  have hk₁ : Fintype.card T ≤ Fintype.card U₁ :=
    Fintype.card_le_of_injective _ F₁.rootEmbed.toEmbedding.injective
  have hk₂ : Fintype.card T ≤ Fintype.card U₂ :=
    Fintype.card_le_of_injective _ F₂.rootEmbed.toEmbedding.injective
  have hDrw : Fintype.card V - Fintype.card T
      - (Fintype.card U₁ - Fintype.card T)
      = Fintype.card V - Fintype.card U₁ := by omega
  have hC₁ : 0 < (Fintype.card V - Fintype.card T).choose
      (Fintype.card U₁ - Fintype.card T) := Nat.choose_pos (by omega)
  have hC₂ : 0 < (Fintype.card V - Fintype.card T).choose
      (Fintype.card U₂ - Fintype.card T) := Nat.choose_pos (by omega)
  have hD₂ : 0 < (Fintype.card V - Fintype.card U₁).choose
      (Fintype.card U₂ - Fintype.card T) := Nat.choose_pos (by omega)
  have hD₂C₂ : (Fintype.card V - Fintype.card U₁).choose
      (Fintype.card U₂ - Fintype.card T)
      ≤ (Fintype.card V - Fintype.card T).choose
        (Fintype.card U₂ - Fintype.card T) :=
    Nat.choose_le_choose _ (by omega)
  have hP_le := pairCount_le_pairChoose F₁ F₂ G
  rw [pairChoose, hDrw] at hP_le
  have hP_mul := pairCount_le_mul F₁ F₂ G
  have hsand := mul_flagCount_sub_pairCount_le F₁ F₂ G
  have hN₁ := flagCount_le_choose F₁ G
  have master₁ : pairCount F₁ F₂ G *
      (Fintype.card V - Fintype.card T).choose
        (Fintype.card U₂ - Fintype.card T)
      ≤ flagCount F₁ G * flagCount F₂ G *
          (Fintype.card V - Fintype.card U₁).choose
            (Fintype.card U₂ - Fintype.card T)
        + (Fintype.card V - Fintype.card T).choose
            (Fintype.card U₁ - Fintype.card T) *
          (Fintype.card V - Fintype.card U₁).choose
            (Fintype.card U₂ - Fintype.card T) *
          ((Fintype.card V - Fintype.card T).choose
              (Fintype.card U₂ - Fintype.card T)
            - (Fintype.card V - Fintype.card U₁).choose
              (Fintype.card U₂ - Fintype.card T)) := by
    nth_rewrite 1 [show (Fintype.card V - Fintype.card T).choose
        (Fintype.card U₂ - Fintype.card T)
      = (Fintype.card V - Fintype.card U₁).choose
          (Fintype.card U₂ - Fintype.card T)
        + ((Fintype.card V - Fintype.card T).choose
            (Fintype.card U₂ - Fintype.card T)
          - (Fintype.card V - Fintype.card U₁).choose
            (Fintype.card U₂ - Fintype.card T)) from by omega]
    rw [Nat.mul_add]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ hP_mul)
      (Nat.mul_le_mul_right _ hP_le)
  have master₂ : flagCount F₁ G * flagCount F₂ G *
      (Fintype.card V - Fintype.card U₁).choose
        (Fintype.card U₂ - Fintype.card T)
      ≤ pairCount F₁ F₂ G *
          (Fintype.card V - Fintype.card T).choose
            (Fintype.card U₂ - Fintype.card T)
        + (Fintype.card V - Fintype.card T).choose
            (Fintype.card U₁ - Fintype.card T) *
          (Fintype.card V - Fintype.card U₁).choose
            (Fintype.card U₂ - Fintype.card T) *
          ((Fintype.card V - Fintype.card T).choose
              (Fintype.card U₂ - Fintype.card T)
            - (Fintype.card V - Fintype.card U₁).choose
              (Fintype.card U₂ - Fintype.card T)) := by
    rw [show flagCount F₁ G * flagCount F₂ G
      = pairCount F₁ F₂ G
        + (flagCount F₁ G * flagCount F₂ G - pairCount F₁ F₂ G) from by
        omega,
      Nat.add_mul]
    refine Nat.add_le_add (Nat.mul_le_mul_left _ hD₂C₂) ?_
    calc (flagCount F₁ G * flagCount F₂ G - pairCount F₁ F₂ G) *
          (Fintype.card V - Fintype.card U₁).choose
            (Fintype.card U₂ - Fintype.card T)
        ≤ flagCount F₁ G *
            ((Fintype.card V - Fintype.card T).choose
                (Fintype.card U₂ - Fintype.card T)
              - (Fintype.card V - Fintype.card U₁).choose
                (Fintype.card U₂ - Fintype.card T)) *
            (Fintype.card V - Fintype.card U₁).choose
              (Fintype.card U₂ - Fintype.card T) :=
          Nat.mul_le_mul_right _ hsand
      _ ≤ (Fintype.card V - Fintype.card T).choose
            (Fintype.card U₁ - Fintype.card T) *
            ((Fintype.card V - Fintype.card T).choose
                (Fintype.card U₂ - Fintype.card T)
              - (Fintype.card V - Fintype.card U₁).choose
                (Fintype.card U₂ - Fintype.card T)) *
            (Fintype.card V - Fintype.card U₁).choose
              (Fintype.card U₂ - Fintype.card T) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hN₁)
      _ = _ := by ring
  have hbound := abs_div_sub_div_le hC₁ hC₂ hD₂ master₁ master₂
  have htail : (((Fintype.card V - Fintype.card T).choose
        (Fintype.card U₂ - Fintype.card T)
      - (Fintype.card V - Fintype.card U₁).choose
        (Fintype.card U₂ - Fintype.card T) : ℕ) : ℚ) /
      (((Fintype.card V - Fintype.card T).choose
        (Fintype.card U₂ - Fintype.card T) : ℕ) : ℚ)
      ≤ (((Fintype.card U₁ - Fintype.card T) *
            (Fintype.card U₂ - Fintype.card T) : ℕ) : ℚ) /
        ((Fintype.card V - Fintype.card T : ℕ) : ℚ) := by
    refine div_le_div_of_mul_le hC₂ (by omega) ?_
    have := mul_choose_sub_choose_le
      (a := Fintype.card V - Fintype.card T)
      (m := Fintype.card U₂ - Fintype.card T)
      (Fintype.card U₁ - Fintype.card T) (by omega)
    rwa [hDrw] at this
  rw [flagPairDensity, flagDensity, flagDensity, pairChoose, hDrw]
  exact hbound.trans htail

/-- The chain rule `₁₂`: expanding the first slot of a pair density over
intermediate flags. -/
theorem subflagPairDensity_chain_left {W' : Type} [Fintype T] [Fintype U₁]
    [Fintype U₂] [Fintype V] [Fintype W']
    (h₁ : Fintype.card U₁ ≤ Fintype.card W')
    (h₂ : Fintype.card W' + Fintype.card U₂
      ≤ Fintype.card V + Fintype.card T)
    (F₁ : Flag 𝕋 σ U₁) (F₂ : Flag 𝕋 σ U₂) (G : Flag 𝕋 σ V) :
    subflagPairDensity F₁ F₂ G
      = ∑ F' : Flag 𝕋 σ W',
          subflagDensity F₁ F' * subflagPairDensity F' F₂ G := by
  have hσ : 𝕋.Mem σ := F₁.out.type_mem
  rw [← subflagTripleDensity_ofType_middle hσ F₁ F₂ G,
    subflagTripleDensity_chain
      (by simpa using Nat.add_le_add_right h₁ (Fintype.card T)) h₂
      F₁ _ F₂ G]
  refine Finset.sum_congr rfl fun F' _ => ?_
  rw [subflagPairDensity_ofType_right]

end FlagAlgebras.Core
