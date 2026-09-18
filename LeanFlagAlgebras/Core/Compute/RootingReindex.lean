import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators

/-! # Ordered rootings grouped by their sorted image

Every injection from `Fin k` into a finite linear order has a unique image
subset of size `k` and a unique permutation relative to its increasing
enumeration. This gives a sum reindexing independent of any graph, flag,
certificate, or automorphism group.
-/

namespace FlagAlgebras.Core

open Classical
open scoped BigOperators

/-- A root set of the prescribed size. -/
abbrev RootSubset (k : ℕ) (α : Type*) := {s : Finset α // s.card = k}

variable {α : Type*} [LinearOrder α] {k : ℕ}

/-- The increasing enumeration of a root set. -/
def sortedRootEmbedding (s : RootSubset k α) : Fin k ↪ α :=
  (s.val.orderEmbOfFin s.property).toEmbedding

/-- A root set and a permutation specify the complete ordered rooting. -/
def rootSubsetPermMap (q : RootSubset k α × Equiv.Perm (Fin k)) : Fin k ↪ α :=
  q.2.toEmbedding.trans (sortedRootEmbedding q.1)

lemma rootSubsetPermMap_image (q : RootSubset k α × Equiv.Perm (Fin k)) :
    Finset.univ.image (rootSubsetPermMap q) = q.1.val := by
  change Finset.univ.image ((sortedRootEmbedding q.1) ∘ q.2) = q.1.val
  rw [← Finset.image_image, Finset.image_univ_of_surjective q.2.surjective]
  exact Finset.image_orderEmbOfFin_univ q.1.val q.1.property

lemma rootSubsetPermMap_injective :
    Function.Injective (rootSubsetPermMap (α := α) (k := k)) := by
  rintro ⟨s, p⟩ ⟨t, q⟩ h
  have himage := congrArg (fun e : Fin k ↪ α => Finset.univ.image e) h
  dsimp only at himage
  rw [rootSubsetPermMap_image, rootSubsetPermMap_image] at himage
  have hst : s = t := Subtype.ext himage
  subst t
  have hpq : p = q := by
    apply Equiv.ext
    intro i
    exact (sortedRootEmbedding s).injective (congrArg (fun e : Fin k ↪ α => e i) h)
  subst q
  rfl

lemma rootSubsetPermMap_surjective :
    Function.Surjective (rootSubsetPermMap (α := α) (k := k)) := by
  intro f
  let s : RootSubset k α := ⟨Finset.univ.image f, by
    rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ, Fintype.card_fin]⟩
  let e : Fin k ≃ s.val := Equiv.ofBijective
    (fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
    (by
      constructor
      · intro i j h
        exact f.injective (congrArg Subtype.val h)
      · intro x
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.property
        exact ⟨i, Subtype.ext hi⟩)
  let p : Equiv.Perm (Fin k) := e.trans (s.val.orderIsoOfFin s.property).symm.toEquiv
  refine ⟨(s, p), ?_⟩
  apply Function.Embedding.ext
  intro i
  change ((s.val.orderIsoOfFin s.property)
    ((s.val.orderIsoOfFin s.property).symm (e i))).val = f i
  simp only [OrderIso.apply_symm_apply]
  rfl

/-- The image-set/permutation decomposition of all ordered root embeddings. -/
noncomputable def rootSubsetPermEquiv :
    (RootSubset k α × Equiv.Perm (Fin k)) ≃ (Fin k ↪ α) :=
  Equiv.ofBijective rootSubsetPermMap
    ⟨rootSubsetPermMap_injective, rootSubsetPermMap_surjective⟩

variable [Fintype α]

/-- Sum over ordered embeddings by first choosing their increasing image set. -/
theorem sum_embeddings_eq_rootSubset_perm {M : Type*} [AddCommMonoid M]
    (f : (Fin k ↪ α) → M) :
    (∑ θ : Fin k ↪ α, f θ) =
      ∑ s : RootSubset k α, ∑ p : Equiv.Perm (Fin k), f (rootSubsetPermMap (s, p)) := by
  rw [← (rootSubsetPermEquiv (α := α) (k := k)).sum_comp f]
  exact Fintype.sum_prod_type _

/-- The same reindexing for the filtered function-space sum used by rootings. -/
theorem sum_injective_eq_rootSubset_perm {M : Type*} [AddCommMonoid M]
    (f : (Fin k → α) → M) :
    (∑ θ ∈ Finset.univ.filter Function.Injective, f θ) =
      ∑ s : RootSubset k α, ∑ p : Equiv.Perm (Fin k),
        f (fun i => sortedRootEmbedding s (p i)) := by
  classical
  have hsub : (∑ θ ∈ Finset.univ.filter Function.Injective, f θ) =
      ∑ θ : {θ : Fin k → α // Function.Injective θ}, f θ.val := by
    simpa only [Finset.subtype_univ] using
      (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
        (p := fun θ : Fin k → α => Function.Injective θ) f).symm
  rw [hsub]
  have he := (Equiv.subtypeInjectiveEquivEmbedding (Fin k) α).sum_comp
    (fun e : Fin k ↪ α => f e)
  change (∑ θ : {θ : Fin k → α // Function.Injective θ}, f θ.val) = _ at he
  rw [he, sum_embeddings_eq_rootSubset_perm]
  rfl

/-- Extra rooting restrictions can be retained as an indicator after reindexing. -/
theorem sum_injective_filter_eq_rootSubset_perm {M : Type*} [AddCommMonoid M]
    (P : (Fin k → α) → Prop) (f : (Fin k → α) → M) :
    (∑ θ ∈ Finset.univ.filter (fun θ => Function.Injective θ ∧ P θ), f θ) =
      ∑ s : RootSubset k α, ∑ p : Equiv.Perm (Fin k),
        if P (fun i => sortedRootEmbedding s (p i))
        then f (fun i => sortedRootEmbedding s (p i)) else 0 := by
  classical
  calc
    _ = ∑ θ ∈ Finset.univ.filter Function.Injective, if P θ then f θ else 0 := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro θ _
      by_cases hi : Function.Injective θ <;> by_cases hp : P θ <;> simp [hi, hp]
    _ = _ := sum_injective_eq_rootSubset_perm (fun θ => if P θ then f θ else 0)

/-- There are 21 possible five-root image sets in seven vertices. -/
lemma card_rootSubset_five_seven : Fintype.card (RootSubset 5 (Fin 7)) = 21 := by
  decide

/-- Each five-root image set has 120 orderings. -/
lemma card_rootPerm_five : Fintype.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Fintype.card_perm, Fintype.card_fin]
  decide

end FlagAlgebras.Core
