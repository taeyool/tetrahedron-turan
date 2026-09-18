import LeanFlagAlgebras.Core.Compute.MaskInj
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7ExtS3

/-! # Which three-root family a rooting belongs to

The certificate splits its three-root records by one bit: the rank of
the rooting's sorted triple in the host mask. This file identifies that
bit with the well-formedness condition of the two three-vertex types —
a rooting is well formed over `s3Type 1` exactly when its root triple
is a hyperedge, and over `s3Type 0` exactly when it is not.

That is what lets the single mixed enumeration `myS3` be split into the
two family rooting sums the fiber identities expect. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

/-- The rank of a rooting's sorted triple. -/
def rootRank (θ : Fin 3 → Fin 7) : ℕ :=
  triIdx 7 (sort3 (θ 0).val (θ 1).val (θ 2).val).1
    (sort3 (θ 0).val (θ 1).val (θ 2).val).2.1
    (sort3 (θ 0).val (θ 1).val (θ 2).val).2.2

/-- The two three-vertex types, decoded. -/
lemma s3Type_zero_edges : (s3Type 0).edges = ∅ := by decide

lemma s3Type_one_edges :
    (s3Type 1).edges = {({0, 1, 2} : Finset (Fin 3))} := by decide

/-- The pullback of a rooting is one of the two three-vertex types, and
which one is decided by the root-triple bit. -/
lemma pullback_eq_s3Type {w : ℕ} {θ : Fin 3 → Fin 7}
    (hinj : Function.Injective θ) :
    ((graphOfMask 7 w).pullback θ = s3Type 1 ↔ w.testBit (rootRank θ) = true)
      ∧ ((graphOfMask 7 w).pullback θ = s3Type 0
          ↔ w.testBit (rootRank θ) = false) := by
  have hvals : ∀ {a b : Fin 3}, a ≠ b → (θ a).val ≠ (θ b).val :=
    fun hne h => hne (hinj (Fin.val_injective h))
  have huniv : ({0, 1, 2} : Finset (Fin 3)) = Finset.univ := by decide
  -- the single candidate triple of the pullback is the whole vertex set,
  -- and its image is the root triple's vertex set
  have himg : ({0, 1, 2} : Finset (Fin 3)).image θ
      = {θ 0, θ 1, θ 2} := by
    rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton]
  have hsort : ({(sort3 (θ 0).val (θ 1).val (θ 2).val).1,
      (sort3 (θ 0).val (θ 1).val (θ 2).val).2.1,
      (sort3 (θ 0).val (θ 1).val (θ 2).val).2.2} : Finset ℕ)
      = {(θ 0).val, (θ 1).val, (θ 2).val} :=
    sort3_finset _ _ _
  obtain ⟨hs12, hs23⟩ := sort3_sorted
    (hvals (show (0 : Fin 3) ≠ 1 by decide))
    (hvals (show (0 : Fin 3) ≠ 2 by decide))
    (hvals (show (1 : Fin 3) ≠ 2 by decide))
  have hlt : ∀ x ∈ ({(sort3 (θ 0).val (θ 1).val (θ 2).val).1,
      (sort3 (θ 0).val (θ 1).val (θ 2).val).2.1,
      (sort3 (θ 0).val (θ 1).val (θ 2).val).2.2} : Finset ℕ), x < 7 := by
    intro x hx
    rw [hsort] at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (θ 0).isLt
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (θ 1).isLt
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact (θ 2).isLt
  have h1 := hlt _ (Finset.mem_insert_self _ _)
  have h2 := hlt _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h3 := hlt _ (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  -- the root triple, as a sorted triple of Fin 7
  have hbit : w.testBit (rootRank θ) = true
      ↔ ({θ 0, θ 1, θ 2} : Finset (Fin 7)) ∈ (graphOfMask 7 w).edges := by
    rw [rootRank]
    rw [testBit_iff_mem_edges' (a := (⟨_, h1⟩ : Fin 7)) (b := ⟨_, h2⟩)
      (c := ⟨_, h3⟩) (Fin.lt_def.mpr hs12) (Fin.lt_def.mpr hs23)]
    constructor
    · intro hm
      have hset : ({(⟨_, h1⟩ : Fin 7), ⟨_, h2⟩, ⟨_, h3⟩} : Finset (Fin 7))
          = {θ 0, θ 1, θ 2} := by
        refine Finset.image_injective (f := Fin.val) Fin.val_injective ?_
        rw [Finset.image_insert, Finset.image_insert,
          Finset.image_singleton, Finset.image_insert,
          Finset.image_insert, Finset.image_singleton]
        exact hsort
      rwa [hset] at hm
    · intro hm
      have hset : ({(⟨_, h1⟩ : Fin 7), ⟨_, h2⟩, ⟨_, h3⟩} : Finset (Fin 7))
          = {θ 0, θ 1, θ 2} := by
        refine Finset.image_injective (f := Fin.val) Fin.val_injective ?_
        rw [Finset.image_insert, Finset.image_insert,
          Finset.image_singleton, Finset.image_insert,
          Finset.image_insert, Finset.image_singleton]
        exact hsort
      rwa [hset]
  -- the pullback's edge set is either empty or the full triple
  have hpull : ((graphOfMask 7 w).pullback θ).edges
      = if ({θ 0, θ 1, θ 2} : Finset (Fin 7)) ∈ (graphOfMask 7 w).edges
        then {({0, 1, 2} : Finset (Fin 3))} else ∅ := by
    ext e
    show e ∈ Finset.univ.filter _ ↔ _
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨-, hc, hmem⟩
      have he : e = ({0, 1, 2} : Finset (Fin 3)) := by
        rw [huniv]
        exact Finset.eq_univ_of_card e (by rw [hc]; decide)
      subst he
      rw [himg] at hmem
      rw [if_pos hmem]
      exact Finset.mem_singleton_self _
    · intro he
      by_cases hm : ({θ 0, θ 1, θ 2} : Finset (Fin 7))
          ∈ (graphOfMask 7 w).edges
      · rw [if_pos hm, Finset.mem_singleton] at he
        subst he
        refine ⟨Finset.mem_univ _, by decide, ?_⟩
        rw [himg]
        exact hm
      · rw [if_neg hm] at he
        exact absurd he (Finset.notMem_empty _)
  constructor
  · rw [hbit]
    constructor
    · intro hp
      have := congrArg Sym3Graph.edges hp
      rw [hpull, s3Type_one_edges] at this
      by_cases hm : ({θ 0, θ 1, θ 2} : Finset (Fin 7))
          ∈ (graphOfMask 7 w).edges
      · exact hm
      · rw [if_neg hm] at this
        exact absurd this.symm (by simp)
    · intro hm
      refine Sym3Graph.ext ?_
      rw [hpull, if_pos hm, s3Type_one_edges]
  · rw [Bool.eq_false_iff, ne_eq, hbit]
    constructor
    · intro hp hm
      have := congrArg Sym3Graph.edges hp
      rw [hpull, if_pos hm, s3Type_zero_edges] at this
      exact absurd this (by simp)
    · intro hm
      refine Sym3Graph.ext ?_
      rw [hpull, if_neg hm, s3Type_zero_edges]

/-- **The parity split**: a rooting is well formed over the edge type
exactly when its root triple is a hyperedge, and over the nonedge type
exactly when it is not. -/
theorem wellFormed_s3Type_iff {w : ℕ} {θ : Fin 3 → Fin 7}
    (hinj : Function.Injective θ) :
    ((Sym3Flag.mk (graphOfMask 7 w) θ).WellFormed (s3Type 1)
        ↔ w.testBit (rootRank θ) = true)
      ∧ ((Sym3Flag.mk (graphOfMask 7 w) θ).WellFormed (s3Type 0)
        ↔ w.testBit (rootRank θ) = false) := by
  obtain ⟨h1, h0⟩ := pullback_eq_s3Type (w := w) hinj
  constructor
  · constructor
    · intro hwf
      exact h1.mp hwf.2
    · intro hb
      exact ⟨hinj, h1.mpr hb⟩
  · constructor
    · intro hwf
      exact h0.mp hwf.2
    · intro hb
      exact ⟨hinj, h0.mpr hb⟩

end FlagAlgebras.Core.Tetrahedron
