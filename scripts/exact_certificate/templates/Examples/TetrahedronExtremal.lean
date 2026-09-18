import LeanFlagAlgebras.Core.Examples.TetrahedronAntitone
import LeanFlagAlgebras.Core.Examples.TetrahedronClone

/-! # The extremal-number form of the Turán bound

The headline theorem, restated in elementary terms. `exTetra n` is the
largest number of hyperedges of a 3-graph on `n` vertices in which no
four vertices span all four triples — a definition whose reading
requires only finite sets and binomial coefficients, none of the flag
machinery. The maximal flag density at every size *is* the extremal
density, so the Turán density is the limit of `exTetra n / C(n,3)`.
`tetraTuranDensity` names that limit in the style of Mathlib's
`SimpleGraph.turanDensity` (a `limUnder`, made meaningful by the
convergence theorem). The certified bound is stated for it in
`TetrahedronDifferential` (the headline `tetraTuranDensity_le_certValue`,
through Razborov's differential method) and independently in
`TetrahedronBoost` (`tetraTuranDensity_le_certValue_finite`, through the
finite cloning argument); this module depends on neither. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core Filter

variable {n : ℕ}

instance : Fintype (Sym3Graph n) :=
  Fintype.ofList (allSym3Graphs n) mem_allSym3Graphs

instance (G : Sym3Graph n) : Decidable G.HasTetraSet :=
  decidable_of_iff
    (∃ S : Finset (Fin n), S.card = 4
      ∧ ∀ t ⊆ S, t.card = 3 → t ∈ G.edges) Iff.rfl

/-- **The extremal number**: the largest edge count of a 3-graph on `n`
vertices in which no four vertices span all four triples. -/
def exTetra (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Sym3Graph n)).filter
    fun G => ¬ G.HasTetraSet).sup fun G => G.edges.card

/-- Theory membership of a literal is exactly the absence of a tetra
set. -/
lemma tetraFree_iff (G : Sym3Graph n) :
    TetraFree.Mem G.toModel ↔ ¬ G.HasTetraSet := by
  constructor
  · rintro ⟨-, hnc⟩ hset
    exact hnc ((hasTetraSet_iff_contains G).mp hset)
  · intro hns
    exact ⟨G.toModel_mem, fun hc =>
      hns ((hasTetraSet_iff_contains G).mpr hc)⟩

private lemma filter_nonempty (n : ℕ) :
    ((Finset.univ : Finset (Sym3Graph n)).filter
      fun G => ¬ G.HasTetraSet).Nonempty := by
  refine ⟨⟨∅, fun e he => absurd he (Finset.notMem_empty e)⟩, ?_⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rintro ⟨S, hS4, hall⟩
  obtain ⟨t, hts, ht3⟩ :=
    Finset.exists_subset_card_eq (show 3 ≤ S.card by omega)
  exact absurd (hall t hts ht3) (Finset.notMem_empty t)

/-- Tetra-free edge counts are at most the extremal number. -/
lemma edges_card_le_exTetra {G : Sym3Graph n} (hG : ¬ G.HasTetraSet) :
    G.edges.card ≤ exTetra n := by
  rw [exTetra]
  refine Finset.le_sup (f := fun G : Sym3Graph n => G.edges.card) ?_
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG⟩

/-- The extremal number is attained. -/
lemma exists_exTetra (n : ℕ) :
    ∃ G : Sym3Graph n, ¬ G.HasTetraSet ∧ G.edges.card = exTetra n := by
  obtain ⟨G, hmem, hsup⟩ := Finset.exists_mem_eq_sup _ (filter_nonempty n)
    (fun G : Sym3Graph n => G.edges.card)
  exact ⟨G, (Finset.mem_filter.mp hmem).2, hsup.symm⟩

/-- **The maximal flag density is the extremal density**: both sides
are the best edge count over the binomial, one phrased through flags
and one through finite sets. -/
theorem maxDens_eq_exTetra (n : ℕ) :
    maxDens n = (exTetra n : ℝ) / (n.choose 3 : ℝ) := by
  refine le_antisymm ?_ ?_
  · obtain ⟨Gstar, hstar⟩ := exists_maxDens n
    obtain ⟨G₀, hG₀, hGeq⟩ := exists_sym3Graph_toFlag
      (fun (M : Model hypergraph3Sig (Fin n))
        (h : TetraFree.Mem M) => h.1) Gstar
    rw [← hstar, hGeq, edgeDens_toFlag]
    have hle : G₀.edges.card ≤ exTetra n :=
      edges_card_le_exTetra ((tetraFree_iff G₀).mp hG₀)
    have hcast : (G₀.edges.card : ℝ) ≤ (exTetra n : ℝ) := by
      exact_mod_cast hle
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hcast
      (inv_nonneg.mpr (Nat.cast_nonneg _))
  · obtain ⟨G₀, hfree, hcard⟩ := exists_exTetra n
    have hmem : TetraFree.Mem G₀.toModel := (tetraFree_iff G₀).mpr hfree
    have h := le_maxDens (G₀.toFlag hmem)
    rw [edgeDens_toFlag, hcard] at h
    exact h

/-- **The Turán density is the limit of the extremal densities** — the
textbook formulation. -/
theorem exTetra_tendsto :
    Tendsto (fun n : ℕ => (exTetra n : ℝ) / (n.choose 3 : ℝ)) atTop
      (nhds turanDensity) := by
  rw [← tendsto_add_atTop_iff_nat 3]
  have htend : Tendsto (fun n : ℕ => maxDens (n + 3)) atTop
      (nhds turanDensity) :=
    tendsto_atTop_ciInf
      (antitone_nat_of_succ_le fun k => maxDensAntitone k)
      bddBelow_maxDens
  exact Tendsto.congr (fun k => maxDens_eq_exTetra (k + 3)) htend

/-- Every extremal density bounds the Turán density from above. -/
lemma turanDensity_le_exTetra (n : ℕ) :
    turanDensity ≤ (exTetra (n + 3) : ℝ) / ((n + 3).choose 3 : ℝ) := by
  rw [← maxDens_eq_exTetra]
  exact ciInf_le bddBelow_maxDens n

/-- **The Turán density of the tetrahedron**, in the style of Mathlib's
`SimpleGraph.turanDensity`: the limit of the extremal densities
`exTetra n / C(n,3)`.

See `tendsto_tetraTuranDensity` for the proof that it is well-defined,
and `tetraTuranDensity_eq` for the agreement with the flag-algebra
`turanDensity`. -/
noncomputable def tetraTuranDensity : ℝ :=
  limUnder atTop fun n : ℕ => (exTetra n : ℝ) / (n.choose 3 : ℝ)

/-- The elementary constant is the flag-algebra Turán density. -/
theorem tetraTuranDensity_eq : tetraTuranDensity = turanDensity :=
  exTetra_tendsto.limUnder_eq

/-- The Turán density of the tetrahedron is well-defined: the extremal
densities converge to it. -/
theorem tendsto_tetraTuranDensity :
    Tendsto (fun n : ℕ => (exTetra n : ℝ) / (n.choose 3 : ℝ)) atTop
      (nhds tetraTuranDensity) := by
  rw [tetraTuranDensity_eq]
  exact exTetra_tendsto

end FlagAlgebras.Core.Tetrahedron
