import LeanFlagAlgebras.Core.Examples.TetrahedronTuran
import LeanFlagAlgebras.Core.Compute.Sym3Delete

/-! # The maximal densities are antitone

The first of the two finite statements: deleting a minimum-degree
vertex from a maximizer at one size produces a flag at the previous
size with at least the same edge density, so the maxima do not
increase. The count inequality is the deletion layer's; this file
converts it to densities through the edge count — a three-subset
induces an edge exactly when it is one. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

/-- A three-subset induces an edge exactly when it is an edge: the edge
count of the pattern is the edge count of the host. -/
lemma edge_flagCountC {n : ℕ} (G : Sym3Graph n) :
    edgeGraph.flagCountC G = G.edges.card := by
  rw [Sym3Graph.flagCountC]
  have h3 : ∀ e : Finset (Fin 3), e.card = 3
      → e = ({0, 1, 2} : Finset (Fin 3)) := by decide
  refine Finset.card_bij (fun W _ => W.val) ?_ ?_ ?_
  · rintro ⟨W, hW⟩ hmem
    have hiso := (Finset.mem_filter.mp hmem).2
    have hcard := (Finset.mem_powersetCard.mp hW).2
    -- the isomorphism forces the pulled-back triple to be an edge
    obtain ⟨p, hedges⟩ := hiso
    have h1 : ({0, 1, 2} : Finset (Fin 3))
        ∈ (G.pullback (subsetTuple W hcard)).edges := by
      have h0 : ({0, 1, 2} : Finset (Fin 3)).image ⇑p
          ∈ (G.pullback (subsetTuple W hcard)).edges := by
        rw [← hedges]
        refine Finset.mem_image.mpr ⟨{0, 1, 2}, ?_, rfl⟩
        decide
      have himg : ({0, 1, 2} : Finset (Fin 3)).image ⇑p
          = ({0, 1, 2} : Finset (Fin 3)) :=
        h3 _ (by
          rw [Finset.card_image_of_injective _ p.injective]
          decide)
      rwa [himg] at h0
    have h2 := (Finset.mem_filter.mp (show ({0, 1, 2} : Finset (Fin 3))
        ∈ Finset.univ.filter _ from h1)).2.2
    have himg2 : ({0, 1, 2} : Finset (Fin 3)).image
        (subsetTuple W hcard) = W := by
      have hsub : ∀ i : Fin 3, subsetTuple W hcard i ∈ W :=
        subsetTuple_mem W hcard
      have huniv : ({0, 1, 2} : Finset (Fin 3)) = Finset.univ := by
        decide
      rw [huniv]
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro y hy
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
        exact hsub i
      · rw [Finset.card_image_of_injective _
          (subsetTuple_injective W hcard), Finset.card_univ,
          Fintype.card_fin, hcard]
    rwa [himg2] at h2
  · intro a₁ ha₁ a₂ ha₂ heq
    exact Subtype.ext heq
  · intro e he
    have hcard := G.edges_valid e he
    have hmem : e ∈ (Finset.univ.powersetCard 3
        : Finset (Finset (Fin n))) :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
    refine ⟨⟨e, hmem⟩, ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ?_⟩
    -- the pulled-back triple is exactly the edge
    have himg2 : ({0, 1, 2} : Finset (Fin 3)).image
        (subsetTuple e hcard) = e := by
      have hsub : ∀ i : Fin 3, subsetTuple e hcard i ∈ e :=
        subsetTuple_mem e hcard
      have huniv : ({0, 1, 2} : Finset (Fin 3)) = Finset.univ := by
        decide
      rw [huniv]
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro y hy
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
        exact hsub i
      · rw [Finset.card_image_of_injective _
          (subsetTuple_injective e hcard), Finset.card_univ,
          Fintype.card_fin, hcard]
    refine ⟨(1 : Equiv.Perm (Fin 3)), ?_⟩
    · have hpull : (G.pullback (subsetTuple e hcard)).edges
          = ({({0, 1, 2} : Finset (Fin 3))}
            : Finset (Finset (Fin 3))) := by
        ext t
        show t ∈ Finset.univ.filter _ ↔ _
        rw [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨-, hc, -⟩
          exact h3 t hc
        · rintro rfl
          refine ⟨Finset.mem_univ _, by decide, ?_⟩
          rw [himg2]
          exact he
      have hedge : edgeGraph.edges
          = ({({0, 1, 2} : Finset (Fin 3))}
            : Finset (Finset (Fin 3))) := by decide
      rw [hedge, hpull]
      ext t
      constructor
      · intro ht
        obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
        rw [Finset.mem_singleton] at ht₀
        subst ht₀
        rw [Finset.mem_singleton]
        refine h3 _ ?_
        rw [Finset.card_image_of_injective _ ((1 : Equiv.Perm (Fin 3)).injective)]
        decide
      · intro ht
        rw [Finset.mem_singleton] at ht
        subst ht
        refine Finset.mem_image.mpr ⟨{0, 1, 2}, Finset.mem_singleton_self _, ?_⟩
        refine h3 _ ?_
        rw [Finset.card_image_of_injective _ ((1 : Equiv.Perm (Fin 3)).injective)]
        decide

/-- The edge density of a literal flag is its edge count over the
binomial. -/
lemma edgeDens_toFlag {m : ℕ} (H : Sym3Graph m)
    (hH : TetraFree.Mem H.toModel) :
    edgeDens ⟨m, H.toFlag hH⟩
      = (H.edges.card : ℝ) / (m.choose 3 : ℝ) := by
  show ((subflagDensity edgeFin.2 (H.toFlag hH) : ℚ) : ℝ) = _
  rw [show edgeFin.2 = edgeGraph.toFlag edgeGraph_mem from rfl,
    Sym3Graph.subflagDensity_toFlag, edge_flagCountC]
  push_cast
  rfl

/-- **The maximal densities are antitone**: minimum-degree deletion
transfers a maximizer down a size without losing density. -/
theorem maxDensAntitone : MaxDensAntitone := by
  intro n
  obtain ⟨Gstar, hstar⟩ := exists_maxDens (n + 1 + 3)
  obtain ⟨Gy, hGy, heq⟩ := exists_sym3Graph_toFlag
    (fun (M : Model hypergraph3Sig (Fin (n + 1 + 3)))
      (h : TetraFree.Mem M) => h.1) Gstar
  obtain ⟨v, hv⟩ := exists_deleteVertex_count_ge
    (n := n + 3) Gy (by omega)
  have hMem : TetraFree.Mem ((Gy.deleteVertex v)).toModel := by
    rw [Sym3Graph.deleteVertex_toModel]
    exact TetraFree.mem_comap _ hGy
  have hC3 : (0 : ℝ) < ((n + 3).choose 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hC4 : (0 : ℝ) < ((n + 1 + 3).choose 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hstep : (Gy.edges.card : ℝ) / ((n + 1 + 3).choose 3 : ℝ)
      ≤ ((Gy.deleteVertex v).edges.card : ℝ)
        / ((n + 3).choose 3 : ℝ) := by
    rw [div_le_div_iff₀ hC4 hC3]
    exact_mod_cast hv
  calc maxDens (n + 1 + 3)
      = edgeDens ⟨n + 1 + 3, Gstar⟩ := hstar.symm
    _ = edgeDens ⟨n + 1 + 3, Gy.toFlag hGy⟩ := by rw [heq]
    _ = (Gy.edges.card : ℝ) / ((n + 1 + 3).choose 3 : ℝ) :=
        edgeDens_toFlag Gy hGy
    _ ≤ ((Gy.deleteVertex v).edges.card : ℝ)
        / ((n + 3).choose 3 : ℝ) := hstep
    _ = edgeDens ⟨n + 3, (Gy.deleteVertex v).toFlag hMem⟩ :=
        (edgeDens_toFlag _ hMem).symm
    _ ≤ maxDens (n + 3) := le_maxDens _

end FlagAlgebras.Core.Tetrahedron
