import LeanFlagAlgebras.Core.Compute.Sym3Clone
import LeanFlagAlgebras.Core.Examples.Tetrahedron

/-! # Cloning stays in the tetrahedron-free theory

The bridge between the combinatorial tetrahedron predicate of the
cloning layer and the theory membership the flag algebra runs on: a
three-graph has a tetrahedron on a vertex set exactly when its model
contains the `tetra` pattern, so the pullback theorem makes cloning
preserve membership in `TetraFree`. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

variable {n : ℕ}

/-- The set form and the model form of having a tetrahedron agree. -/
theorem hasTetraSet_iff_contains (G : Sym3Graph n) :
    G.HasTetraSet ↔ G.toModel.Contains tetra := by
  constructor
  · rintro ⟨S, hS4, hall⟩
    have hfin := S.orderIsoOfFin hS4
    refine ⟨⟨fun i => (hfin i : Fin n),
      fun a b hab => hfin.injective (Subtype.ext hab)⟩, ?_⟩
    intro r g hg
    show Function.Injective _ ∧ Finset.univ.image _ ∈ G.edges
    simp only [Function.Embedding.coeFn_mk]
    have hginj : Function.Injective g := hg
    constructor
    · intro a b hab
      exact hginj (hfin.injective (Subtype.ext hab))
    · rw [← Finset.image_image]
      refine hall _ ?_ ?_
      · intro y hy
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
        exact (hfin i).2
      · rw [Finset.card_image_of_injective _
            (fun a b hab => hfin.injective (Subtype.ext hab)),
          Finset.card_image_of_injective _ hginj, Finset.card_univ,
          Fintype.card_fin]
  · rintro ⟨f, hall⟩
    refine ⟨Finset.univ.image f, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ f.injective,
        Finset.card_univ, Fintype.card_fin]
    · intro t ht hc
      have htpre : ∀ y ∈ t, ∃ i : Fin 4, f i = y := by
        intro y hy
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (ht hy)
        exact ⟨i, hi⟩
      set t' := Finset.univ.filter fun i : Fin 4 => f i ∈ t with ht'
      have himg : t'.image f = t := by
        ext y
        constructor
        · intro hy
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
          exact (Finset.mem_filter.mp hi).2
        · intro hy
          obtain ⟨i, hi⟩ := htpre y hy
          exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hi.symm ▸ hy⟩, hi⟩
      have hc' : t'.card = 3 := by
        rw [← hc, ← himg,
          Finset.card_image_of_injective _ f.injective]
      have hfin := t'.orderIsoOfFin hc'
      have hgoal := hall () fun i => ((hfin i : t') : Fin 4)
      have htetra : tetra.interp ()
          (fun i => ((hfin i : t') : Fin 4)) := by
        show Function.Injective _
        intro a b hab
        exact hfin.injective (Subtype.ext hab)
      have hint := hgoal htetra
      obtain ⟨-, hmem⟩ := hint
      have himg2 : Finset.univ.image
          (f ∘ fun i => ((hfin i : t') : Fin 4)) = t := by
        rw [← himg]
        have h1 : Finset.univ.image
            (fun i => ((hfin i : t') : Fin 4)) = t' := by
          ext j
          constructor
          · intro hj
            obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
            exact ((hfin i : t')).2
          · intro hj
            obtain ⟨i, hi⟩ := hfin.surjective ⟨j, hj⟩
            exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _,
              by rw [hi]⟩
        rw [← Finset.image_image, h1]
      rw [himg2] at hmem
      exact hmem

/-- **Cloning stays tetrahedron-free.** -/
theorem cloneAt_mem {G : Sym3Graph n} {u v : Fin n} (huv : u ≠ v)
    (hG : TetraFree.Mem G.toModel) :
    TetraFree.Mem ((G.cloneAt u v huv)).toModel := by
  refine ⟨(G.cloneAt u v huv).toModel_mem, ?_⟩
  intro hcont
  exact hG.2 ((hasTetraSet_iff_contains G).mp
    (Sym3Graph.hasTetraSet_of_cloneAt huv
      ((hasTetraSet_iff_contains _).mpr hcont)))

end FlagAlgebras.Core.Tetrahedron
