import LeanFlagAlgebras.Core.JointDensity
import LeanFlagAlgebras.Utils.LinExtension
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Core: the flag algebra `A^σ`, theory-generically

Razborov's flag algebra over an arbitrary universal relational theory.
`FinFlag 𝕋 σ` are size-tagged flags on canonical carriers `Fin n`;
`FlagVector 𝕋 σ` their formal real combinations; `flagMul` the product
expanded by pair densities; `ZeroSpace` the span of the averaging relations;
and `FlagAlgebra 𝕋 σ` the quotient, a commutative `ℝ`-algebra.

Mirrors the `SimpleGraph`-based `FlagAlgebra/FlagAlgebra.lean` with the
`Core` joint densities as structure constants: the four chain rules of
`Core/JointDensity.lean` drive well-definedness, unitality, and
associativity. The unit flag requires `𝕋.IsType σ` (the type is a member
model); nontriviality additionally requires `𝕋.PadClosed` (flags of every
size exist). -/

namespace FlagAlgebras.Core

open Finset

variable {S : Signature} {T : Type} [Fintype T]
variable {𝕋 : RelTheory S} {σ : Model S T}

/-- A flag on the canonical `n`-element carrier. -/
abbrev FlagWithSize (𝕋 : RelTheory S) (σ : Model S T) (n : ℕ) : Type :=
  Flag 𝕋 σ (Fin n)

/-- A flag together with its size: a dependent pair `⟨n, F⟩` of a vertex
count and a flag on `Fin n`. The basis index of `FlagVector`. -/
def FinFlag (𝕋 : RelTheory S) (σ : Model S T) : Type :=
  Σ n : ℕ, FlagWithSize 𝕋 σ n

/-- The unit: the canonical unit flag at size `|T|`. -/
noncomputable def unitFinFlag (𝕋 : RelTheory S) (σ : Model S T) [Fintype T]
    [𝕋.IsType σ] : FinFlag 𝕋 σ :=
  ⟨Fintype.card T, (unitFlag 𝕋 σ RelTheory.IsType.mem).toFlag⟩

noncomputable instance [𝕋.IsType σ] : One (FinFlag 𝕋 σ) :=
  ⟨unitFinFlag 𝕋 σ⟩

theorem finFlag_one_fst [𝕋.IsType σ] :
    (1 : FinFlag 𝕋 σ).1 = Fintype.card T :=
  rfl

theorem finFlag_one_snd [𝕋.IsType σ] :
    (1 : FinFlag 𝕋 σ).2
      = (unitFlag 𝕋 σ RelTheory.IsType.mem).toFlag :=
  rfl

/-- Every flag's size is at least the type's. -/
theorem finFlag_size_ge (F : FinFlag 𝕋 σ) : Fintype.card T ≤ F.1 := by
  obtain ⟨n, F⟩ := F
  simpa using Fintype.card_le_of_injective _
    (Quotient.out F).rootEmbed.toEmbedding.injective

/-! ## Chain rules on canonical carriers

`Fin`-specialized wrappers of the `Core/JointDensity.lean` chain rules,
absorbing the `Fintype.card (Fin n) = n` bookkeeping once. -/

private lemma chain₁₁ {m n : ℕ} (ℓ' : ℕ) (F : FlagWithSize 𝕋 σ m)
    (G : FlagWithSize 𝕋 σ n) (h₁ : m ≤ ℓ') (h₂ : ℓ' ≤ n) :
    subflagDensity F G
      = ∑ F' : FlagWithSize 𝕋 σ ℓ', subflagDensity F F' * subflagDensity F' G :=
  subflagDensity_chain (W' := Fin ℓ') (by simpa using h₁) (by simpa using h₂)
    F G

private lemma chain₂₁ {m₁ m₂ n : ℕ} (ℓ' : ℕ) (F₁ : FlagWithSize 𝕋 σ m₁)
    (F₂ : FlagWithSize 𝕋 σ m₂) (G : FlagWithSize 𝕋 σ n)
    (h₁ : m₁ + m₂ ≤ ℓ' + Fintype.card T) (h₂ : ℓ' ≤ n) :
    subflagPairDensity F₁ F₂ G
      = ∑ F' : FlagWithSize 𝕋 σ ℓ',
          subflagPairDensity F₁ F₂ F' * subflagDensity F' G :=
  subflagPairDensity_chain_host (W' := Fin ℓ') (by simpa using h₁)
    (by simpa using h₂) F₁ F₂ G

private lemma chain₁₂ {m₁ m₂ n : ℕ} (ℓ' : ℕ) (F₁ : FlagWithSize 𝕋 σ m₁)
    (F₂ : FlagWithSize 𝕋 σ m₂) (G : FlagWithSize 𝕋 σ n)
    (h₁ : m₁ ≤ ℓ') (h₂ : ℓ' + m₂ ≤ n + Fintype.card T) :
    subflagPairDensity F₁ F₂ G
      = ∑ F' : FlagWithSize 𝕋 σ ℓ',
          subflagDensity F₁ F' * subflagPairDensity F' F₂ G :=
  subflagPairDensity_chain_left (W' := Fin ℓ') (by simpa using h₁)
    (by simpa using h₂) F₁ F₂ G

private lemma chain₂₂ {m₁ m₂ m₃ n : ℕ} (ℓ' : ℕ) (F₁ : FlagWithSize 𝕋 σ m₁)
    (F₂ : FlagWithSize 𝕋 σ m₂) (F₃ : FlagWithSize 𝕋 σ m₃)
    (G : FlagWithSize 𝕋 σ n) (h₁ : m₁ + m₂ ≤ ℓ' + Fintype.card T)
    (h₂ : ℓ' + m₃ ≤ n + Fintype.card T) :
    subflagTripleDensity F₁ F₂ F₃ G
      = ∑ F' : FlagWithSize 𝕋 σ ℓ',
          subflagPairDensity F₁ F₂ F' * subflagPairDensity F' F₃ G :=
  subflagTripleDensity_chain (W' := Fin ℓ') (by simpa using h₁)
    (by simpa using h₂) F₁ F₂ F₃ G

/-! ## Flag vectors -/

/-- A formal real combination of size-tagged flags: the underlying module of
the flag algebra, before quotienting by the averaging relations. -/
abbrev FlagVector (𝕋 : RelTheory S) (σ : Model S T) : Type :=
  FinFlag 𝕋 σ →₀ ℝ

/-- The basis vector for a single flag `F`. -/
noncomputable def basisVector (F : FinFlag 𝕋 σ) : FlagVector 𝕋 σ :=
  Finsupp.single F 1

omit [Fintype T] in
@[simp]
theorem basisVector_apply_self (F : FinFlag 𝕋 σ) : (basisVector F) F = 1 := by
  simp [basisVector]

omit [Fintype T] in
@[simp]
theorem basisVector_support (F : FinFlag 𝕋 σ) :
    (basisVector F).support = {F} := by
  dsimp only [basisVector]
  rw [Finsupp.support_single_ne_zero _ (by simp)]

omit [Fintype T] in
theorem basisVector_apply_other (F F' : FinFlag 𝕋 σ) (hF : F ≠ F') :
    (basisVector F) F' = 0 := by
  simp [basisVector, hF]

omit [Fintype T] in
/-- Every flag vector expands as the finite sum of its coefficients times
the corresponding `basisVector`s. -/
theorem flagVector_eq_sum_basisVector (f : FlagVector 𝕋 σ) :
    f = ∑ F ∈ f.support, f F • basisVector F := by
  conv_lhs => rw [← Finsupp.sum_single f]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [basisVector, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The unit flag vector. -/
noncomputable instance [𝕋.IsType σ] : One (FlagVector 𝕋 σ) where
  one := basisVector 1

@[simp]
theorem flagVector_one_support [𝕋.IsType σ] :
    (1 : FlagVector 𝕋 σ).support = {(1 : FinFlag 𝕋 σ)} := by
  show (basisVector 1).support = {(1 : FinFlag 𝕋 σ)}
  simp

@[simp]
theorem flagVector_one_apply_one [𝕋.IsType σ] :
    (1 : FlagVector 𝕋 σ) 1 = 1 := by
  show (basisVector 1) 1 = 1
  simp

/-! ## The flag product -/

/-- Product of two flags expanded onto flags of a chosen size `ℓ`: the
formal combination `∑_G p(F, F'; G) • G` over all size-`ℓ` flags `G`, with
`p` the pair density. Up to `∼v` it is independent of `ℓ` (large enough). -/
noncomputable def flagMulWithSize (F F' : FinFlag 𝕋 σ) (ℓ : ℕ) :
    FlagVector 𝕋 σ :=
  ∑ G : FlagWithSize 𝕋 σ ℓ,
    (subflagPairDensity F.2 F'.2 G : ℝ) • basisVector ⟨ℓ, G⟩

theorem flagMulWithSize_comm (F F' : FinFlag 𝕋 σ) (ℓ : ℕ) :
    flagMulWithSize F F' ℓ = flagMulWithSize F' F ℓ := by
  dsimp [flagMulWithSize]
  refine Finset.sum_congr rfl fun G _ => ?_
  rw [subflagPairDensity_comm]

theorem flagMulWithSize_one [𝕋.IsType σ] (F : FinFlag 𝕋 σ) :
    flagMulWithSize F 1 F.1 = basisVector F := by
  classical
  dsimp [flagMulWithSize]
  rw [finFlag_one_snd]
  have h_univ_split : (univ : Finset (FlagWithSize 𝕋 σ F.1))
      = insert F.2 (univ.erase F.2) := (insert_erase (mem_univ _)).symm
  rw [h_univ_split, sum_insert (notMem_erase _ _)]
  rw [subflagPairDensity_unitFlag_right, subflagDensity_self]
  rw [← add_zero (basisVector F)]
  congr 1
  · norm_num
  · apply sum_eq_zero
    intro F' hF'
    rw [subflagPairDensity_unitFlag_right]
    have hF'_ne : F.2 ≠ F' := by
      intro h
      exact (mem_erase.mp hF').1 h.symm
    rw [subflagDensity_eq_zero_of_ne hF'_ne]
    norm_num

/-- The flag product of `F` and `F'`, at the minimal size
`F.1 + F'.1 - |T|` (the natural target size for the pair density). -/
noncomputable def flagMul (F F' : FinFlag 𝕋 σ) : FlagVector 𝕋 σ :=
  flagMulWithSize F F' (F.1 + F'.1 - Fintype.card T)

theorem flagMul_comm (F F' : FinFlag 𝕋 σ) : flagMul F F' = flagMul F' F := by
  simp [flagMul, add_comm, flagMulWithSize_comm]

theorem flagMul_one [𝕋.IsType σ] (F : FinFlag 𝕋 σ) :
    flagMul F 1 = basisVector F := by
  dsimp [flagMul]
  rw [finFlag_one_fst, ← Nat.eq_sub_of_add_eq rfl]
  exact flagMulWithSize_one F

/-- Multiplication on flag vectors: the bilinear extension of `flagMul`. -/
noncomputable instance : Mul (FlagVector 𝕋 σ) where
  mul := bilinearExtension flagMul

theorem flagVector_mul_eq_nested_sum (f g : FlagVector 𝕋 σ) :
    f * g = ∑ F ∈ f.support, ∑ G ∈ g.support, (f F * g G) • flagMul F G :=
  bilinearExtension_eq_nested_sum _ _ _

theorem flagVector_mul_comm (f g : FlagVector 𝕋 σ) : f * g = g * f := by
  simp only [flagVector_mul_eq_nested_sum]
  rw [sum_comm]
  repeat (apply sum_congr rfl; rintro _ -)
  rw [mul_comm, flagMul_comm]

noncomputable instance : CommMagma (FlagVector 𝕋 σ) where
  mul_comm := flagVector_mul_comm

instance : IsScalarTower ℝ (FlagVector 𝕋 σ) (FlagVector 𝕋 σ) where
  smul_assoc := bilinearExtension_smul_left flagMul

noncomputable instance : HasDistribNeg (FlagVector 𝕋 σ) where
  neg_mul := bilinearExtension_neg_left flagMul
  mul_neg := bilinearExtension_neg_right flagMul

/-- Flag vectors form a non-unital non-associative ring; unitality and
associativity hold only up to `∼v` and are established on the quotient. -/
noncomputable instance : NonUnitalNonAssocRing (FlagVector 𝕋 σ) where
  left_distrib := bilinearExtension_add_right flagMul
  right_distrib := bilinearExtension_add_left flagMul
  zero_mul := bilinearExtension_zero_left flagMul
  mul_zero := bilinearExtension_zero_right flagMul

theorem flagVector_mul_one [𝕋.IsType σ] (f : FlagVector 𝕋 σ) :
    f * 1 = f := by
  conv_rhs => rw [flagVector_eq_sum_basisVector f]
  rw [flagVector_mul_eq_nested_sum]
  rw [flagVector_one_support]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [sum_singleton, flagVector_one_apply_one, mul_one, flagMul_one]

noncomputable instance [𝕋.IsType σ] : MulOneClass (FlagVector 𝕋 σ) where
  one_mul g := by
    rw [mul_comm, flagVector_mul_one]
  mul_one := flagVector_mul_one

theorem flagVector_smul_mul_smul_comm (f g : FlagVector 𝕋 σ) (a b : ℝ) :
    a • f * b • g = (a * b) • (f * g) := by
  show bilinearExtension flagMul (a • f) (b • g)
      = (a * b) • bilinearExtension flagMul f g
  rw [bilinearExtension_smul_left, bilinearExtension_smul_right, smul_smul]

/-! ## The averaging relations and the zero space -/

/-- The averaged expansion of a flag `F` onto size-`ℓ` flags:
`∑_{F'} p(F; F') • F'`. Setting `F` equal to this sum is Razborov's
relation. -/
noncomputable def flagExpansion (F : FinFlag 𝕋 σ) (ℓ : ℕ) :
    FlagVector 𝕋 σ :=
  ∑ F' : FlagWithSize 𝕋 σ ℓ,
    (subflagDensity F.2 F' : ℝ) • basisVector ⟨ℓ, F'⟩

/-- A generating relation of the flag algebra: `F − ∑_{F'} p(F; F') • F'`,
identified with `0` (the averaging identity). -/
noncomputable def zeroElement (F : FinFlag 𝕋 σ) (ℓ : ℕ) : FlagVector 𝕋 σ :=
  basisVector F - flagExpansion F ℓ

/-- The set of all generating relations `zeroElement F ℓ` with `F.1 ≤ ℓ`. -/
noncomputable def zeroSet (𝕋 : RelTheory S) (σ : Model S T) :
    Set (FlagVector 𝕋 σ) :=
  {k | ∃ (F : FinFlag 𝕋 σ) (ℓ : ℕ), F.1 ≤ ℓ ∧ k = zeroElement F ℓ}

@[simp]
theorem mem_zeroSet {k : FlagVector 𝕋 σ} :
    k ∈ zeroSet 𝕋 σ ↔ ∃ F ℓ, F.1 ≤ ℓ ∧ k = zeroElement F ℓ :=
  Iff.rfl

/-- The submodule spanned by all averaging relations; quotienting by it
yields the flag algebra. -/
noncomputable def ZeroSpace (𝕋 : RelTheory S) (σ : Model S T) :
    Submodule ℝ (FlagVector 𝕋 σ) :=
  Submodule.span ℝ (zeroSet 𝕋 σ)

theorem zeroElement_in_zeroSpace {F : FinFlag 𝕋 σ} {ℓ : ℕ} (hℓ : F.1 ≤ ℓ) :
    zeroElement F ℓ ∈ ZeroSpace 𝕋 σ := by
  apply Submodule.mem_span.mpr fun p a => a ?_
  exact ⟨F, ℓ, hℓ, rfl⟩

theorem zeroSpace_eq_sum_spanElement (k : FlagVector 𝕋 σ)
    (h_zero : k ∈ ZeroSpace 𝕋 σ) :
    ∃ (I : Type) (_ : Fintype I) (c : I → ℝ) (v : I → FlagVector 𝕋 σ),
      (∀ i, v i ∈ zeroSet 𝕋 σ) ∧ (k = ∑ i, c i • v i) := by
  rcases Submodule.mem_span_set'.mp h_zero with ⟨n, c, v', h⟩
  refine ⟨Fin n, inferInstance, c, fun i => (v' i).val,
    fun i => (v' i).property, ?_⟩
  rw [← h]

theorem zeroSpace_closed_under_add (f f' : FlagVector 𝕋 σ)
    (hf : f ∈ ZeroSpace 𝕋 σ) (hf' : f' ∈ ZeroSpace 𝕋 σ) :
    f + f' ∈ ZeroSpace 𝕋 σ :=
  Submodule.add_mem _ hf hf'

theorem zeroSpace_closed_under_sum {α : Type} (s : Finset α)
    (v : α → FlagVector 𝕋 σ) (h : ∀ a ∈ s, v a ∈ ZeroSpace 𝕋 σ) :
    ∑ a ∈ s, v a ∈ ZeroSpace 𝕋 σ :=
  Submodule.sum_mem _ h

theorem zeroSpace_closed_under_smul (r : ℝ) (f : FlagVector 𝕋 σ)
    (hf : f ∈ ZeroSpace 𝕋 σ) : r • f ∈ ZeroSpace 𝕋 σ :=
  SMulMemClass.smul_mem _ hf

/-! ## Flag-equality and the setoid -/

/-- Flag-equality `f ∼v g`: `f` and `g` differ by an element of
`ZeroSpace`, i.e. they represent the same element of the flag algebra. -/
def flagVectorEqv (f g : FlagVector 𝕋 σ) : Prop :=
  f - g ∈ ZeroSpace 𝕋 σ

@[inherit_doc] scoped infixl:50 " ∼v " => flagVectorEqv

theorem basisVector_eqv_flagExpansion (F : FinFlag 𝕋 σ) (ℓ : ℕ)
    (hℓ : F.1 ≤ ℓ) : basisVector F ∼v flagExpansion F ℓ :=
  zeroElement_in_zeroSpace hℓ

@[refl]
theorem flagVectorEqv.refl (f : FlagVector 𝕋 σ) : f ∼v f := by
  dsimp [flagVectorEqv]
  rw [sub_self]
  exact Submodule.zero_mem _

@[simp]
theorem flagVectorEqv.rfl {f : FlagVector 𝕋 σ} : f ∼v f :=
  .refl f

@[symm]
theorem flagVectorEqv.symm {f f' : FlagVector 𝕋 σ} (h : f ∼v f') :
    f' ∼v f := by
  dsimp [flagVectorEqv] at *
  exact sub_mem_comm_iff.mp h

theorem flagVectorEqv.trans {f f' f'' : FlagVector 𝕋 σ} (h : f ∼v f')
    (h' : f' ∼v f'') : f ∼v f'' := by
  dsimp [flagVectorEqv] at *
  rw [← sub_add_sub_cancel]
  exact zeroSpace_closed_under_add (f - f') (f' - f'') h h'

instance : Trans (flagVectorEqv (𝕋 := 𝕋) (σ := σ))
    (flagVectorEqv (𝕋 := 𝕋) (σ := σ)) (flagVectorEqv (𝕋 := 𝕋) (σ := σ)) where
  trans := flagVectorEqv.trans

theorem flagVector_eq_eqv {f f' : FlagVector 𝕋 σ} (h : f = f') : f ∼v f' :=
  h ▸ .rfl

theorem flagVectorEqv_sum {α : Type} {s : Finset α}
    {v v' : α → FlagVector 𝕋 σ} (h : ∀ a ∈ s, v a ∼v v' a) :
    ∑ a ∈ s, v a ∼v ∑ a ∈ s, v' a := by
  show _ - _ ∈ _
  rw [← Finset.sum_sub_distrib]
  exact zeroSpace_closed_under_sum _ _ h

theorem flagVectorEqv_smul (r : ℝ) {f f' : FlagVector 𝕋 σ} (h : f ∼v f') :
    r • f ∼v r • f' := by
  show _ - _ ∈ _
  rw [← smul_sub]
  exact zeroSpace_closed_under_smul _ _ h

/-- The setoid on flag vectors given by flag-equality `∼v`; its quotient is
`FlagAlgebra 𝕋 σ`. -/
instance flagVectorSetoid (𝕋 : RelTheory S) (σ : Model S T) [Fintype T] :
    Setoid (FlagVector 𝕋 σ) where
  r := flagVectorEqv
  iseqv :=
    ⟨flagVectorEqv.refl, flagVectorEqv.symm, flagVectorEqv.trans⟩

/-! ## Size-independence of the product -/

/-- The size at which a flag product is expanded does not matter modulo
`∼v`, as long as it is large enough. -/
theorem flagMulWithSize_indep_on_size {F₁ F₂ : FinFlag 𝕋 σ} {ℓ₁ ℓ₂ : ℕ}
    (hℓ₁ : F₁.1 + F₂.1 ≤ ℓ₁ + Fintype.card T)
    (hℓ₂ : F₁.1 + F₂.1 ≤ ℓ₂ + Fintype.card T) :
    flagMulWithSize F₁ F₂ ℓ₁ ∼v flagMulWithSize F₁ F₂ ℓ₂ := by
  wlog hℓ : ℓ₁ ≤ ℓ₂ generalizing ℓ₁ ℓ₂
  · exact (this hℓ₂ hℓ₁ (Nat.le_of_not_ge hℓ)).symm
  simp only [flagMulWithSize]
  calc
    _ ∼v (∑ F' : FlagWithSize 𝕋 σ ℓ₁,
        (subflagPairDensity F₁.2 F₂.2 F' : ℝ) • flagExpansion ⟨ℓ₁, F'⟩ ℓ₂) := by
      apply flagVectorEqv_sum; rintro _ -
      apply flagVectorEqv_smul
      exact basisVector_eqv_flagExpansion _ _ hℓ
    _ ∼v (∑ F' : FlagWithSize 𝕋 σ ℓ₁, ∑ G' : FlagWithSize 𝕋 σ ℓ₂,
        (subflagPairDensity F₁.2 F₂.2 F' : ℝ) •
          (subflagDensity F' G' : ℝ) • basisVector ⟨ℓ₂, G'⟩) := by
      apply flagVectorEqv_sum; rintro _ -
      dsimp only [flagExpansion]
      rw [Finset.smul_sum]
    _ ∼v _ := by
      rw [sum_comm]
      apply flagVectorEqv_sum
      rintro G' -
      refine flagVector_eq_eqv ?_
      rw [show subflagPairDensity F₁.2 F₂.2 G'
          = ∑ F' : FlagWithSize 𝕋 σ ℓ₁,
              subflagPairDensity F₁.2 F₂.2 F' * subflagDensity F' G' from
        chain₂₁ ℓ₁ F₁.2 F₂.2 G' hℓ₁ hℓ]
      rw [Rat.cast_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun F' _ => ?_
      rw [Rat.cast_mul, ← smul_smul]

theorem flagMul_indep_on_size {F₁ F₂ : FinFlag 𝕋 σ} {ℓ' : ℕ}
    (hℓ' : F₁.1 + F₂.1 ≤ ℓ' + Fintype.card T) :
    flagMul F₁ F₂ ∼v flagMulWithSize F₁ F₂ ℓ' := by
  refine flagMulWithSize_indep_on_size ?_ hℓ'
  rw [Nat.sub_add_cancel]
  exact Nat.le_add_right_of_le (finFlag_size_ge _)

/-- Two basis vectors multiply to the flag product. -/
theorem basisVector_mul_basisVector (F F' : FinFlag 𝕋 σ) :
    basisVector F * basisVector F' = flagMul F F' := by
  simp_rw [flagVector_mul_eq_nested_sum, basisVector_support, sum_singleton,
    basisVector_apply_self, mul_one, one_smul]

/-! ## The ideal property -/

/-- Multiplying a single flag by a generating relation stays in
`ZeroSpace`: the heart of well-definedness of the quotient product, via the
`₁₂` chain rule. -/
theorem flag_mul_zeroElement (F G : FinFlag 𝕋 σ) (ℓ : ℕ) (hℓ : G.1 ≤ ℓ) :
    (basisVector F) * (zeroElement G ℓ) ∈ ZeroSpace 𝕋 σ := by
  have hkF := finFlag_size_ge F
  have hkG := finFlag_size_ge G
  rw [zeroElement, mul_sub]
  show _ ∼v _
  simp only [flagExpansion, Finset.mul_sum]
  symm
  calc
    _ ∼v (∑ F' : FlagWithSize 𝕋 σ ℓ,
        (subflagDensity G.2 F' : ℝ) •
          (basisVector F * basisVector ⟨ℓ, F'⟩)) := by
      apply flagVectorEqv_sum; rintro _ -
      refine flagVector_eq_eqv ?_
      rw [mul_comm (basisVector F), smul_mul_assoc, mul_comm]
    _ ∼v (∑ F' : FlagWithSize 𝕋 σ ℓ,
        (subflagDensity G.2 F' : ℝ) •
          flagMulWithSize F ⟨ℓ, F'⟩ (F.1 + G.1 + ℓ)) := by
      apply flagVectorEqv_sum; rintro F' -
      apply flagVectorEqv_smul
      rw [basisVector_mul_basisVector]
      apply flagMul_indep_on_size
      show F.1 + ℓ ≤ F.1 + G.1 + ℓ + Fintype.card T
      omega
    _ ∼v (∑ G' : FlagWithSize 𝕋 σ (F.1 + G.1 + ℓ),
        ∑ F' : FlagWithSize 𝕋 σ ℓ,
          (subflagDensity G.2 F' : ℝ) •
            (subflagPairDensity F.2 F' G' : ℝ) •
              basisVector ⟨F.1 + G.1 + ℓ, G'⟩) := by
      rw [sum_comm]
      apply flagVectorEqv_sum; rintro _ -
      refine flagVector_eq_eqv ?_
      dsimp only [flagMulWithSize]
      rw [Finset.smul_sum]
    _ ∼v (∑ G' : FlagWithSize 𝕋 σ (F.1 + G.1 + ℓ),
        (∑ F' : FlagWithSize 𝕋 σ ℓ,
          (subflagDensity G.2 F' : ℝ) * (subflagPairDensity F.2 F' G' : ℝ)) •
            basisVector ⟨F.1 + G.1 + ℓ, G'⟩) := by
      apply flagVectorEqv_sum; rintro _ -
      refine flagVector_eq_eqv ?_
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl fun F' _ => smul_smul _ _ _
    _ ∼v flagMulWithSize F G (F.1 + G.1 + ℓ) := by
      dsimp only [flagMulWithSize]
      apply flagVectorEqv_sum
      rintro G' -
      have key : subflagPairDensity F.2 G.2 G'
          = ∑ F' : FlagWithSize 𝕋 σ ℓ,
              subflagDensity G.2 F' * subflagPairDensity F.2 F' G' := by
        rw [subflagPairDensity_comm, chain₁₂ ℓ G.2 F.2 G' hℓ (by omega)]
        refine Finset.sum_congr rfl fun F' _ => ?_
        rw [subflagPairDensity_comm]
      refine flagVector_eq_eqv ?_
      congr 1
      rw [key]
      push_cast
      rfl
    _ ∼v (basisVector F * basisVector G) := by
      rw [basisVector_mul_basisVector]
      symm
      apply flagMul_indep_on_size
      omega

/-- `ZeroSpace` is an ideal: multiplying any flag vector by a relation
stays inside. This makes multiplication well defined on the quotient. -/
theorem flagVector_mul_zeroSpace (f : FlagVector 𝕋 σ) {k : FlagVector 𝕋 σ}
    (hk : k ∈ ZeroSpace 𝕋 σ) : f * k ∈ ZeroSpace 𝕋 σ := by
  rw [flagVector_eq_sum_basisVector f, Finset.sum_mul]
  apply zeroSpace_closed_under_sum
  intro F _
  rcases zeroSpace_eq_sum_spanElement k hk with ⟨I, hI, c, v, hv, hk_sum⟩
  haveI := hI
  rw [hk_sum, Finset.mul_sum]
  apply zeroSpace_closed_under_sum
  intro i _
  rw [smul_mul_assoc]
  apply zeroSpace_closed_under_smul
  rw [mul_comm, smul_mul_assoc]
  apply zeroSpace_closed_under_smul
  obtain ⟨H, ℓ, hℓ, hvi⟩ := mem_zeroSet.mp (hv i)
  rw [hvi, mul_comm]
  exact flag_mul_zeroElement F H ℓ hℓ

/-! ## Associativity via the triple density -/

/-- A product of three single-flag basis vectors equals (mod `∼v`) the sum
over size-`ℓ` flags weighted by the triple density; the engine behind
associativity. -/
theorem three_flag_mul_eqv_sum_tripleDensity (F₁ F₂ F₃ : FinFlag 𝕋 σ)
    {ℓ : ℕ}
    (hℓ : ℓ = F₁.1 + F₂.1 + F₃.1 - Fintype.card T - Fintype.card T) :
    (basisVector F₁ * basisVector F₂ * basisVector F₃) ∼v
      (∑ G : FlagWithSize 𝕋 σ ℓ,
        (subflagTripleDensity F₁.2 F₂.2 F₃.2 G : ℝ) • basisVector ⟨ℓ, G⟩) := by
  have hk₁ := finFlag_size_ge F₁
  have hk₂ := finFlag_size_ge F₂
  have hk₃ := finFlag_size_ge F₃
  rw [basisVector_mul_basisVector]
  calc flagMul F₁ F₂ * basisVector F₃
      ∼v ∑ F : FlagWithSize 𝕋 σ (F₁.1 + F₂.1 - Fintype.card T),
          (subflagPairDensity F₁.2 F₂.2 F : ℝ) •
            (basisVector ⟨F₁.1 + F₂.1 - Fintype.card T, F⟩ *
              basisVector F₃) := by
        refine flagVector_eq_eqv ?_
        dsimp only [flagMul, flagMulWithSize]
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun F _ => smul_mul_assoc _ _ _
    _ ∼v ∑ F : FlagWithSize 𝕋 σ (F₁.1 + F₂.1 - Fintype.card T),
          (subflagPairDensity F₁.2 F₂.2 F : ℝ) •
            flagMulWithSize ⟨F₁.1 + F₂.1 - Fintype.card T, F⟩ F₃ ℓ := by
        apply flagVectorEqv_sum; rintro F -
        apply flagVectorEqv_smul
        rw [basisVector_mul_basisVector]
        apply flagMul_indep_on_size
        show (F₁.1 + F₂.1 - Fintype.card T) + F₃.1 ≤ ℓ + Fintype.card T
        omega
    _ ∼v ∑ G : FlagWithSize 𝕋 σ ℓ,
          ∑ F : FlagWithSize 𝕋 σ (F₁.1 + F₂.1 - Fintype.card T),
            (subflagPairDensity F₁.2 F₂.2 F : ℝ) •
              (subflagPairDensity F F₃.2 G : ℝ) • basisVector ⟨ℓ, G⟩ := by
        rw [sum_comm]
        apply flagVectorEqv_sum; rintro _ -
        refine flagVector_eq_eqv ?_
        dsimp only [flagMulWithSize]
        rw [Finset.smul_sum]
    _ ∼v ∑ G : FlagWithSize 𝕋 σ ℓ,
          (∑ F : FlagWithSize 𝕋 σ (F₁.1 + F₂.1 - Fintype.card T),
            (subflagPairDensity F₁.2 F₂.2 F : ℝ) *
              (subflagPairDensity F F₃.2 G : ℝ)) • basisVector ⟨ℓ, G⟩ := by
        apply flagVectorEqv_sum; rintro _ -
        refine flagVector_eq_eqv ?_
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun F _ => smul_smul _ _ _
    _ ∼v _ := by
        apply flagVectorEqv_sum
        rintro G -
        have key : subflagTripleDensity F₁.2 F₂.2 F₃.2 G
            = ∑ F : FlagWithSize 𝕋 σ (F₁.1 + F₂.1 - Fintype.card T),
                subflagPairDensity F₁.2 F₂.2 F *
                  subflagPairDensity F F₃.2 G :=
          chain₂₂ _ F₁.2 F₂.2 F₃.2 G (by omega) (by omega)
        refine flagVector_eq_eqv ?_
        congr 1
        rw [key]
        push_cast
        rfl

theorem basisVector_mul_assoc (F₁ F₂ F₃ : FinFlag 𝕋 σ) :
    (basisVector F₁ * basisVector F₂ * basisVector F₃) ∼v
      (basisVector F₁ * (basisVector F₂ * basisVector F₃)) := by
  have hk₁ := finFlag_size_ge F₁
  have hk₂ := finFlag_size_ge F₂
  have hk₃ := finFlag_size_ge F₃
  nth_rw 2 [mul_comm (basisVector F₁)]
  calc
    _ ∼v (∑ G : FlagWithSize 𝕋 σ
            (F₁.1 + F₂.1 + F₃.1 - Fintype.card T - Fintype.card T),
          (subflagTripleDensity F₁.2 F₂.2 F₃.2 G : ℝ) • basisVector ⟨_, G⟩) :=
      three_flag_mul_eqv_sum_tripleDensity F₁ F₂ F₃ rfl
    _ ∼v (∑ G : FlagWithSize 𝕋 σ
            (F₁.1 + F₂.1 + F₃.1 - Fintype.card T - Fintype.card T),
          (subflagTripleDensity F₂.2 F₃.2 F₁.2 G : ℝ) • basisVector ⟨_, G⟩) := by
      apply flagVectorEqv_sum; rintro G -
      rw [subflagTripleDensity_rotate]
    _ ∼v basisVector F₂ * basisVector F₃ * basisVector F₁ :=
      (three_flag_mul_eqv_sum_tripleDensity F₂ F₃ F₁ (by omega)).symm

/-- Associativity of the flag product holds modulo `∼v`. -/
theorem flagVector_mul_assoc (f g h : FlagVector 𝕋 σ) :
    (f * g * h) ∼v (f * (g * h)) := by
  rw [flagVector_eq_sum_basisVector f, flagVector_eq_sum_basisVector g,
    flagVector_eq_sum_basisVector h]
  simp only [Finset.mul_sum, Finset.sum_mul, flagVector_smul_mul_smul_comm,
    mul_assoc]
  iterate 3 (apply flagVectorEqv_sum; rintro _ -)
  exact flagVectorEqv_smul _ (basisVector_mul_assoc _ _ _)

/-! ## The flag algebra -/

/-- The flag algebra `A^σ`: flag vectors modulo the averaging relations.
Carries a commutative `ℝ`-algebra structure (built below). -/
abbrev FlagAlgebra (𝕋 : RelTheory S) (σ : Model S T) [Fintype T] : Type :=
  Quotient (flagVectorSetoid 𝕋 σ)

instance : Zero (FlagAlgebra 𝕋 σ) where
  zero := ⟦0⟧

noncomputable instance [𝕋.IsType σ] : One (FlagAlgebra 𝕋 σ) where
  one := ⟦1⟧

noncomputable instance : Add (FlagAlgebra 𝕋 σ) where
  add := Quotient.map₂ (· + ·) fun f f' hf g g' hg => by
    show (f + g) - (f' + g') ∈ ZeroSpace 𝕋 σ
    rw [show f + g - (f' + g') = (f - f') + (g - g') by abel]
    exact zeroSpace_closed_under_add _ _ hf hg

noncomputable instance : SMul ℝ (FlagAlgebra 𝕋 σ) where
  smul r := Quotient.map (r • ·) fun g g' hg => by
    show r • g - r • g' ∈ ZeroSpace 𝕋 σ
    rw [← smul_sub]
    exact zeroSpace_closed_under_smul _ _ hg

noncomputable instance : Neg (FlagAlgebra 𝕋 σ) where
  neg := ((-1 : ℝ) • ·)

theorem add_quot (f f' : FlagVector 𝕋 σ) :
    (⟦f + f'⟧ : FlagAlgebra 𝕋 σ) = ⟦f⟧ + ⟦f'⟧ :=
  rfl

theorem smul_quot (r : ℝ) (f : FlagVector 𝕋 σ) :
    (⟦r • f⟧ : FlagAlgebra 𝕋 σ) = r • ⟦f⟧ :=
  rfl

theorem neg_quot (f : FlagVector 𝕋 σ) :
    (⟦-f⟧ : FlagAlgebra 𝕋 σ) = -⟦f⟧ := by
  show (⟦-f⟧ : FlagAlgebra 𝕋 σ) = (-1 : ℝ) • ⟦f⟧
  rw [← smul_quot]
  apply Quotient.sound
  rw [neg_one_smul]

/-- Multiplication on the flag algebra, descended via the ideal property. -/
noncomputable instance : Mul (FlagAlgebra 𝕋 σ) where
  mul := Quotient.map₂ (· * ·) fun f f' hf g g' hg => by
    show f * g - f' * g' ∈ ZeroSpace 𝕋 σ
    have h : f * g - f' * g' = f * (g - g') + (f - f') * g' := by
      rw [mul_sub, sub_mul]
      abel
    rw [h]
    refine zeroSpace_closed_under_add _ _ (flagVector_mul_zeroSpace f hg) ?_
    rw [mul_comm]
    exact flagVector_mul_zeroSpace g' hf

theorem mul_quot (f f' : FlagVector 𝕋 σ) :
    (⟦f * f'⟧ : FlagAlgebra 𝕋 σ) = ⟦f⟧ * ⟦f'⟧ :=
  rfl

theorem flagAlgebra_mul_comm (f g : FlagAlgebra 𝕋 σ) : f * g = g * f := by
  rw [← Quotient.out_eq f, ← Quotient.out_eq g, ← mul_quot, ← mul_quot]
  rw [mul_comm]

theorem flagAlgebra_mul_assoc (f g h : FlagAlgebra 𝕋 σ) :
    f * g * h = f * (g * h) := by
  rw [← Quotient.out_eq f, ← Quotient.out_eq g, ← Quotient.out_eq h]
  exact Quotient.sound (flagVector_mul_assoc _ _ _)

theorem flagAlgebra_mul_one [𝕋.IsType σ] (f : FlagAlgebra 𝕋 σ) :
    f * 1 = f := by
  rw [← Quotient.out_eq f]
  show (⟦f.out⟧ : FlagAlgebra 𝕋 σ) * ⟦(1 : FlagVector 𝕋 σ)⟧ = ⟦f.out⟧
  rw [← mul_quot, flagVector_mul_one]

/-- The flag algebra is a commutative ring: all axioms descend from
`FlagVector` since the defects (unitality, associativity) vanish modulo
`ZeroSpace`. -/
noncomputable instance [𝕋.IsType σ] : CommRing (FlagAlgebra 𝕋 σ) where
  add_assoc a b c := by
    rw [← Quotient.out_eq a, ← Quotient.out_eq b, ← Quotient.out_eq c,
      ← add_quot, ← add_quot, ← add_quot, ← add_quot]
    rw [add_assoc]
  zero_add a := by
    rw [← Quotient.out_eq a]
    show (⟦0⟧ : FlagAlgebra 𝕋 σ) + ⟦a.out⟧ = ⟦a.out⟧
    rw [← add_quot, zero_add]
  add_zero a := by
    rw [← Quotient.out_eq a]
    show (⟦a.out⟧ : FlagAlgebra 𝕋 σ) + ⟦0⟧ = ⟦a.out⟧
    rw [← add_quot, add_zero]
  add_comm a b := by
    rw [← Quotient.out_eq a, ← Quotient.out_eq b, ← add_quot, ← add_quot]
    rw [add_comm]
  neg_add_cancel a := by
    rw [← Quotient.out_eq a]
    show -(⟦a.out⟧ : FlagAlgebra 𝕋 σ) + ⟦a.out⟧ = ⟦0⟧
    rw [← neg_quot, ← add_quot, neg_add_cancel]
  mul_assoc := flagAlgebra_mul_assoc
  zero_mul a := by
    rw [← Quotient.out_eq a]
    show (⟦0⟧ : FlagAlgebra 𝕋 σ) * ⟦a.out⟧ = ⟦0⟧
    rw [← mul_quot, zero_mul]
  mul_zero a := by
    rw [← Quotient.out_eq a]
    show (⟦a.out⟧ : FlagAlgebra 𝕋 σ) * ⟦0⟧ = ⟦0⟧
    rw [← mul_quot, mul_zero]
  one_mul a := by
    rw [flagAlgebra_mul_comm]
    exact flagAlgebra_mul_one a
  mul_one := flagAlgebra_mul_one
  left_distrib a b c := by
    rw [← Quotient.out_eq a, ← Quotient.out_eq b, ← Quotient.out_eq c,
      ← add_quot, ← mul_quot, ← mul_quot, ← mul_quot, ← add_quot]
    rw [left_distrib]
  right_distrib a b c := by
    rw [← Quotient.out_eq a, ← Quotient.out_eq b, ← Quotient.out_eq c,
      ← add_quot, ← mul_quot, ← mul_quot, ← mul_quot, ← add_quot]
    rw [right_distrib]
  mul_comm := flagAlgebra_mul_comm
  nsmul n g := (n : ℝ) • g
  nsmul_zero g := by
    rw [← Quotient.out_eq g]
    show ((0 : ℕ) : ℝ) • (⟦g.out⟧ : FlagAlgebra 𝕋 σ) = ⟦0⟧
    rw [← smul_quot]
    apply Quotient.sound
    rw [Nat.cast_zero, zero_smul]
  nsmul_succ n g := by
    rw [← Quotient.out_eq g]
    show ((n + 1 : ℕ) : ℝ) • (⟦g.out⟧ : FlagAlgebra 𝕋 σ)
      = ((n : ℕ) : ℝ) • ⟦g.out⟧ + ⟦g.out⟧
    rw [← smul_quot, ← smul_quot, ← add_quot]
    apply Quotient.sound
    rw [Nat.cast_succ, add_smul, one_smul]
  zsmul z g := (z : ℝ) • g
  zsmul_zero' g := by
    rw [← Quotient.out_eq g]
    show ((0 : ℤ) : ℝ) • (⟦g.out⟧ : FlagAlgebra 𝕋 σ) = ⟦0⟧
    rw [← smul_quot]
    apply Quotient.sound
    rw [Int.cast_zero, zero_smul]
  zsmul_succ' n g := by
    rw [← Quotient.out_eq g]
    show ((Int.ofNat n.succ : ℤ) : ℝ) • (⟦g.out⟧ : FlagAlgebra 𝕋 σ)
      = ((Int.ofNat n : ℤ) : ℝ) • ⟦g.out⟧ + ⟦g.out⟧
    rw [← smul_quot, ← smul_quot, ← add_quot]
    apply Quotient.sound
    refine flagVector_eq_eqv ?_
    rw [show ((Int.ofNat n.succ : ℤ) : ℝ) = ((Int.ofNat n : ℤ) : ℝ) + 1 by
      norm_cast]
    rw [add_smul, one_smul]
  zsmul_neg' n g := by
    rw [← Quotient.out_eq g]
    show ((Int.negSucc n : ℤ) : ℝ) • (⟦g.out⟧ : FlagAlgebra 𝕋 σ)
      = -(((n.succ : ℤ) : ℝ) • ⟦g.out⟧)
    rw [← smul_quot, ← smul_quot, ← neg_quot]
    apply Quotient.sound
    refine flagVector_eq_eqv ?_
    rw [show ((Int.negSucc n : ℤ) : ℝ) = -(((n.succ : ℤ) : ℝ)) by
      rw [Int.cast_negSucc]; norm_cast]
    rw [neg_smul]

theorem sum_quot {ι : Type} (s : Finset ι) (f : ι → FlagVector 𝕋 σ)
    [𝕋.IsType σ] :
    (⟦∑ i ∈ s, f i⟧ : FlagAlgebra 𝕋 σ)
      = ∑ i ∈ s, (⟦f i⟧ : FlagAlgebra 𝕋 σ) := by
  classical
  refine Finset.induction_on s rfl ?_
  intro i s his ih
  simp only [Finset.sum_insert his, add_quot, ih]

theorem flagAlgebra_smul_mul_smul_comm (f g : FlagAlgebra 𝕋 σ) (a b : ℝ) :
    a • f * b • g = (a * b) • (f * g) := by
  rw [← Quotient.out_eq f, ← Quotient.out_eq g, ← smul_quot, ← smul_quot,
    ← mul_quot, ← mul_quot, ← smul_quot]
  rw [flagVector_smul_mul_smul_comm]

/-- The `ℝ`-algebra structure on the flag algebra, with
`algebraMap r = r • 1`. -/
noncomputable instance [𝕋.IsType σ] : Algebra ℝ (FlagAlgebra 𝕋 σ) where
  algebraMap :=
    { toFun r := r • 1
      map_zero' := by
        show (⟦(0 : ℝ) • (1 : FlagVector 𝕋 σ)⟧ : FlagAlgebra 𝕋 σ) = ⟦0⟧
        apply Quotient.sound
        rw [zero_smul]
      map_one' := by
        show (⟦(1 : ℝ) • (1 : FlagVector 𝕋 σ)⟧ : FlagAlgebra 𝕋 σ) = ⟦1⟧
        apply Quotient.sound
        rw [one_smul]
      map_add' := fun x y => by
        show (⟦(x + y) • (1 : FlagVector 𝕋 σ)⟧ : FlagAlgebra 𝕋 σ)
          = ⟦x • (1 : FlagVector 𝕋 σ)⟧ + ⟦y • (1 : FlagVector 𝕋 σ)⟧
        rw [← add_quot]
        apply Quotient.sound
        rw [add_smul]
      map_mul' := fun x y => by
        show (x * y) • (1 : FlagAlgebra 𝕋 σ) = (x • 1) * (y • 1)
        rw [flagAlgebra_smul_mul_smul_comm, mul_one]
      }
  smul_def' r g := by
    show r • g = (r • 1) * g
    have hone : ((1 : ℝ) • g : FlagAlgebra 𝕋 σ) = g := by
      rw [← Quotient.out_eq g, ← smul_quot]
      exact Quotient.sound (flagVector_eq_eqv (one_smul _ _))
    rw [show ((r • 1) * g : FlagAlgebra 𝕋 σ) = r • 1 * (1 : ℝ) • g by
        rw [hone],
      flagAlgebra_smul_mul_smul_comm, mul_one, one_mul]
  commutes' r g := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [flagAlgebra_mul_comm]

/-! ## Averaging identities in the algebra -/

/-- In the flag algebra, a single flag equals its density expansion onto
larger flags: the averaging relation as an equation. -/
theorem basisVector_quot_eq_sum [𝕋.IsType σ] (F : FinFlag 𝕋 σ) (ℓ : ℕ)
    (hℓ : F.1 ≤ ℓ) :
    (⟦basisVector F⟧ : FlagAlgebra 𝕋 σ)
      = ∑ F' : FlagWithSize 𝕋 σ ℓ,
          (subflagDensity F.2 F' : ℝ) • (⟦basisVector ⟨ℓ, F'⟩⟧ : FlagAlgebra 𝕋 σ) := by
  simp_rw [← smul_quot, ← sum_quot]
  exact Quotient.sound (basisVector_eqv_flagExpansion _ _ hℓ)

/-- Every element of the flag algebra is a real combination of flags of a
single size. -/
theorem exists_level_expansion [𝕋.IsType σ] (x : FlagAlgebra 𝕋 σ) :
    ∃ (n : ℕ) (c : FlagWithSize 𝕋 σ n → ℝ),
      x = ∑ F' : FlagWithSize 𝕋 σ n, c F' • ⟦basisVector ⟨n, F'⟩⟧ := by
  obtain ⟨v, rfl⟩ := Quotient.exists_rep x
  refine ⟨v.support.sup (fun F => F.1),
    fun F' => ∑ F ∈ v.support, v F * (subflagDensity F.2 F' : ℝ), ?_⟩
  conv_lhs => rw [flagVector_eq_sum_basisVector v]
  rw [sum_quot]
  rw [Finset.sum_congr rfl fun F hF => by
    rw [smul_quot,
      basisVector_quot_eq_sum F _ (Finset.le_sup (f := fun F => F.1) hF),
      Finset.smul_sum]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun F' _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun F hF => ?_
  rw [smul_smul]

/-- The sum of all flags of any fixed size `ℓ ≥ |T|` equals `1` in the flag
algebra: the basic normalization identity. -/
theorem sum_flagWithSize_eq_one [𝕋.IsType σ] (ℓ : ℕ)
    (hℓ : Fintype.card T ≤ ℓ) :
    ∑ F : FlagWithSize 𝕋 σ ℓ, (⟦basisVector ⟨ℓ, F⟩⟧ : FlagAlgebra 𝕋 σ)
      = (1 : FlagAlgebra 𝕋 σ) := by
  show _ = ⟦basisVector 1⟧
  rw [basisVector_quot_eq_sum 1 ℓ hℓ]
  refine (Finset.sum_congr rfl fun F _ => ?_).symm
  rw [finFlag_one_snd, subflagDensity_unitFlag]
  norm_num

theorem basisVector_quot_mul_eq_flagMulWithSize_quot (F G : FinFlag 𝕋 σ)
    (ℓ : ℕ) (hℓ : F.1 + G.1 ≤ ℓ + Fintype.card T) :
    (⟦basisVector F⟧ * ⟦basisVector G⟧ : FlagAlgebra 𝕋 σ)
      = ⟦flagMulWithSize F G ℓ⟧ := by
  rw [← mul_quot, basisVector_mul_basisVector]
  exact Quotient.sound (flagMul_indep_on_size hℓ)

/-- The product of two flags in the algebra is the density-weighted
expansion: links the ring product to pair densities. -/
theorem basisVector_quot_mul_eq_flagMul_quot (F G : FinFlag 𝕋 σ) :
    (⟦basisVector F⟧ * ⟦basisVector G⟧ : FlagAlgebra 𝕋 σ) = ⟦flagMul F G⟧ := by
  rw [← mul_quot, basisVector_mul_basisVector]

omit [Fintype T] in
theorem linearExtension_basisVector {R : Type} [AddCommGroup R] [Module ℝ R]
    (f : FinFlag 𝕋 σ → R) (F : FinFlag 𝕋 σ) :
    linearExtension f (basisVector F) = f F := by
  simp only [basisVector, linearExtension_single_one]

/-! ## Nontriviality

`0 ≠ 1`: a linear density functional against a large flag (which exists by
pad-closure) separates the unit from every generating relation. -/

theorem flagAlgebra_zero_ne_one [𝕋.IsType σ] [𝕋.PadClosed] :
    (0 : FlagAlgebra 𝕋 σ) ≠ 1 := by
  intro h_zero_eq_one
  have h_one_zero : (1 : FlagVector 𝕋 σ) ∈ ZeroSpace 𝕋 σ := by
    rw [← sub_zero (1 : FlagVector 𝕋 σ)]
    exact Quotient.exact h_zero_eq_one.symm
  rcases zeroSpace_eq_sum_spanElement 1 h_one_zero with ⟨I, hI, c, v, hv, hx⟩
  haveI := hI
  choose G ℓ hG using hv
  classical
  set L := max (Finset.sup (Finset.univ : Finset I) ℓ) (Fintype.card T)
    with hLdef
  have hL : Fintype.card T ≤ L := le_max_right _ _
  obtain ⟨Fd⟩ := LabeledFlag.nonempty_of_card_le (V := Fin L)
    (RelTheory.IsType.mem (𝕋 := 𝕋) (σ := σ)) (by simpa using hL)
  set Fdef : FlagWithSize 𝕋 σ L := Fd.toFlag with hFdef
  set D : FinFlag 𝕋 σ → ℝ :=
    fun G' => (subflagDensity G'.2 Fdef : ℝ) with hDdef
  have hφ : ∀ i, linearExtension D (v i) = 0 := by
    intro i
    obtain ⟨hℓ', hG2⟩ := hG i
    have hℓL : ℓ i ≤ L := le_max_iff.mpr (Or.inl (Finset.le_sup (mem_univ _)))
    rw [hG2, zeroElement, sub_eq_add_neg, linearExtension_add,
      linearExtension_neg, ← sub_eq_add_neg, sub_eq_zero,
      linearExtension_basisVector, flagExpansion, linearExtension_sum]
    have hchain := chain₁₁ (ℓ i) (G i).2 Fdef hℓ' hℓL
    show (subflagDensity (G i).2 Fdef : ℝ) = _
    rw [hchain]
    push_cast
    refine Finset.sum_congr rfl fun F' _ => ?_
    rw [linearExtension_smul, linearExtension_basisVector, smul_eq_mul]
  have h_φ_1 : linearExtension D (1 : FlagVector 𝕋 σ) = 1 := by
    show linearExtension D (basisVector 1) = 1
    rw [linearExtension_basisVector]
    show (subflagDensity (1 : FinFlag 𝕋 σ).2 Fdef : ℝ) = 1
    rw [finFlag_one_snd, subflagDensity_unitFlag]
    norm_num
  rw [hx, linearExtension_sum] at h_φ_1
  simp only [linearExtension_smul, hφ, smul_zero,
    Finset.sum_const_zero] at h_φ_1
  exact zero_ne_one h_φ_1

instance [𝕋.IsType σ] [𝕋.PadClosed] : NeZero (1 : FlagAlgebra 𝕋 σ) where
  out := flagAlgebra_zero_ne_one.symm

/-- The flag algebra is nontrivial over a pad-closed theory. -/
instance [𝕋.IsType σ] [𝕋.PadClosed] : Nontrivial (FlagAlgebra 𝕋 σ) where
  exists_pair_ne := ⟨0, 1, flagAlgebra_zero_ne_one⟩

end FlagAlgebras.Core
