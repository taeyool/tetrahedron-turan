import LeanFlagAlgebras.Core.Compute.Sym3

/-! # Deleting a vertex of a three-graph

The first, measure-free layer of the maximizer program: removing a
vertex of a `Sym3Graph`, with the edge bookkeeping the deletion
estimates need. Deletion is the pullback along the order embedding that
skips the vertex, so membership facts flow from the pullback API; the
new content is the edge count — the deleted graph keeps exactly the
edges avoiding the vertex, and the host's edges split as those plus the
vertex's degree. -/

namespace FlagAlgebras.Core

variable {n : ℕ}

/-- Delete a vertex: pull back along the embedding that skips it. -/
def Sym3Graph.deleteVertex (G : Sym3Graph (n + 1)) (v : Fin (n + 1)) :
    Sym3Graph n :=
  G.pullback v.succAbove

/-- The degree of a vertex: the number of hyperedges through it. -/
def Sym3Graph.degree {m : ℕ} (G : Sym3Graph m) (v : Fin m) : ℕ :=
  (G.edges.filter fun e => v ∈ e).card

/-- Membership in the deleted graph: the image triple avoids the vertex
and is an edge of the host. -/
lemma Sym3Graph.mem_deleteVertex_edges (G : Sym3Graph (n + 1))
    (v : Fin (n + 1)) (e : Finset (Fin n)) :
    e ∈ (G.deleteVertex v).edges
      ↔ e.card = 3 ∧ e.image v.succAbove ∈ G.edges := by
  show e ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The edges of the deleted graph biject with the host's edges
avoiding the vertex. -/
lemma Sym3Graph.deleteVertex_edges_card (G : Sym3Graph (n + 1))
    (v : Fin (n + 1)) :
    (G.deleteVertex v).edges.card
      = (G.edges.filter fun e => v ∉ e).card := by
  refine Finset.card_bij
    (fun e _ => e.image v.succAbove) ?_ ?_ ?_
  · intro e he
    obtain ⟨hc, hm⟩ := (mem_deleteVertex_edges G v e).mp he
    refine Finset.mem_filter.mpr ⟨hm, ?_⟩
    intro hv
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hv
    exact absurd hx (Fin.succAbove_ne v x)
  · intro e₁ h₁ e₂ h₂ heq
    exact Finset.image_injective (Fin.succAbove_right_injective) heq
  · intro e he
    obtain ⟨hm, hv⟩ := Finset.mem_filter.mp he
    have hcard := G.edges_valid e hm
    have himg : (Finset.univ.filter
        fun x : Fin n => v.succAbove x ∈ e).image v.succAbove = e := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact (Finset.mem_filter.mp hx).2
      · intro hy
        obtain ⟨x, hx⟩ := Fin.exists_succAbove_eq
          (x := y) (y := v) (fun h => hv (h ▸ hy))
        exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hx.symm ▸ hy⟩, hx⟩
    refine ⟨Finset.univ.filter fun x : Fin n => v.succAbove x ∈ e,
      ?_, himg⟩
    refine (mem_deleteVertex_edges G v _).mpr
      ⟨?_, by rw [himg]; exact hm⟩
    rw [← hcard]
    conv_rhs => rw [← himg]
    exact (Finset.card_image_of_injective _
      Fin.succAbove_right_injective).symm

/-- **The deletion split**: the host's edge count is the deleted
graph's plus the vertex's degree. -/
theorem Sym3Graph.card_edges_deleteVertex (G : Sym3Graph (n + 1))
    (v : Fin (n + 1)) :
    G.edges.card = (G.deleteVertex v).edges.card + G.degree v := by
  rw [deleteVertex_edges_card]
  show _ = _ + (G.edges.filter fun e => v ∈ e).card
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := G.edges) (p := fun e => v ∈ e)
  omega

/-- Deletion is a comap: theory membership transfers along it. -/
lemma Sym3Graph.deleteVertex_toModel (G : Sym3Graph (n + 1))
    (v : Fin (n + 1)) :
    (G.deleteVertex v).toModel
      = G.toModel.comap ⟨v.succAbove, Fin.succAbove_right_injective⟩ :=
  G.pullback_toModel Fin.succAbove_right_injective

/-! ## The degree sum -/

/-- **Double counting**: the degrees sum to three times the edge
count. -/
theorem Sym3Graph.sum_degree {m : ℕ} (G : Sym3Graph m) :
    (∑ v : Fin m, G.degree v) = 3 * G.edges.card := by
  have hswap : (∑ v : Fin m, G.degree v)
      = ∑ e ∈ G.edges, e.card := by
    show (∑ v : Fin m, (G.edges.filter fun e => v ∈ e).card) = _
    rw [Finset.sum_congr rfl fun v (_ : v ∈ Finset.univ) =>
      Finset.card_filter (fun e => v ∈ e) G.edges]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.card_eq_sum_ones e, Finset.sum_ite_mem,
      Finset.univ_inter]
  rw [hswap, Finset.sum_congr rfl fun e he => G.edges_valid e he,
    Finset.sum_const, smul_eq_mul, mul_comm]

/-- Some vertex has at most the average degree. -/
lemma Sym3Graph.exists_degree_le (G : Sym3Graph (n + 1)) :
    ∃ v : Fin (n + 1), (n + 1) * G.degree v ≤ 3 * G.edges.card := by
  obtain ⟨v, -, hv⟩ := Finset.exists_min_image Finset.univ G.degree
    ⟨0, Finset.mem_univ 0⟩
  refine ⟨v, ?_⟩
  have hle : (n + 1) * G.degree v ≤ ∑ u : Fin (n + 1), G.degree u := by
    calc (n + 1) * G.degree v
        = ∑ _u : Fin (n + 1), G.degree v := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
      _ ≤ ∑ u : Fin (n + 1), G.degree u :=
          Finset.sum_le_sum fun u _ => hv u (Finset.mem_univ u)
  rw [sum_degree] at hle
  exact hle

/-! ## Minimum-degree deletion does not decrease the density -/

/-- The binomial identity behind the density comparison:
`(n+1)·C(n,3) = (n−2)·C(n+1,3)`. -/
lemma choose_three_step (n : ℕ) (hn : 3 ≤ n) :
    (n + 1) * n.choose 3 = (n - 2) * (n + 1).choose 3 := by
  have h1 : n.choose 3 * 3 = n.choose 2 * (n - 2) := by
    have := Nat.choose_succ_right_eq n 2
    simpa using this
  have h2 : (n + 1) * n.choose 2 = (n + 1).choose 3 * 3 := by
    have := Nat.succ_mul_choose_eq n 2
    simpa [Nat.succ_eq_add_one] using this
  have h3 : ((n + 1) * n.choose 3) * 3
      = ((n - 2) * (n + 1).choose 3) * 3 := by
    calc ((n + 1) * n.choose 3) * 3 = (n + 1) * (n.choose 3 * 3) := by ring
      _ = (n + 1) * (n.choose 2 * (n - 2)) := by rw [h1]
      _ = ((n + 1) * n.choose 2) * (n - 2) := by ring
      _ = ((n + 1).choose 3 * 3) * (n - 2) := by rw [h2]
      _ = ((n - 2) * (n + 1).choose 3) * 3 := by ring
  omega

/-- **Deleting a minimum-degree vertex does not decrease the edge
density** — the count form: the deleted graph's count times the host's
binomial dominates the host's count times the deleted binomial. -/
theorem exists_deleteVertex_count_ge (G : Sym3Graph (n + 1))
    (hn : 3 ≤ n) :
    ∃ v : Fin (n + 1),
      G.edges.card * n.choose 3
        ≤ (G.deleteVertex v).edges.card * (n + 1).choose 3 := by
  obtain ⟨v, hv⟩ := G.exists_degree_le
  refine ⟨v, ?_⟩
  have hsplit := G.card_edges_deleteVertex v
  have hstep := choose_three_step n hn
  have hchoose_pos : 0 < (n + 1).choose 3 :=
    Nat.choose_pos (by omega)
  -- (n+1)·(deleted count) ≥ (n−2)·(host count)
  have hexpand : (n + 1) * G.edges.card
      = (n + 1) * (G.deleteVertex v).edges.card
        + (n + 1) * G.degree v := by
    rw [hsplit]
    ring
  have hsplit3 : (n - 2) * G.edges.card + 3 * G.edges.card
      = (n + 1) * G.edges.card := by
    rw [← add_mul]
    congr 1
    omega
  have hcount : (n - 2) * G.edges.card
      ≤ (n + 1) * (G.deleteVertex v).edges.card := by
    omega
  -- multiply through the binomial identity
  have hmul : ((n - 2) * G.edges.card) * (n + 1).choose 3
      ≤ ((n + 1) * (G.deleteVertex v).edges.card) * (n + 1).choose 3 :=
    Nat.mul_le_mul_right _ hcount
  have hlhs : ((n - 2) * G.edges.card) * (n + 1).choose 3
      = (n + 1) * (G.edges.card * n.choose 3) := by
    calc ((n - 2) * G.edges.card) * (n + 1).choose 3
        = G.edges.card * ((n - 2) * (n + 1).choose 3) := by ring
      _ = G.edges.card * ((n + 1) * n.choose 3) := by rw [← hstep]
      _ = (n + 1) * (G.edges.card * n.choose 3) := by ring
  have hrhs : ((n + 1) * (G.deleteVertex v).edges.card) * (n + 1).choose 3
      = (n + 1) * ((G.deleteVertex v).edges.card * (n + 1).choose 3) := by
    ring
  rw [hlhs, hrhs] at hmul
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

end FlagAlgebras.Core
