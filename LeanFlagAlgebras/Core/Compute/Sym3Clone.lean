import LeanFlagAlgebras.Core.Compute.Sym3Delete

/-! # Cloning a vertex's link in a three-graph

The symmetrization step of the maximizer program: `cloneAt G u v`
replaces `v`'s link by `u`'s — the edges avoiding `v` stay, and every
edge through `u` avoiding `v` contributes its copy with `u` swapped for
`v`. The three facts the route needs:

* the edge count splits as the `v`-avoiding part plus `u`'s exclusive
  degree, which is the gain/loss ledger of the scout;
* a tetrahedron of the clone pulls back to one of the host — the swap
  direction when the clone set misses `u`, and the impossibility of a
  tetrahedron through both `u` and `v` because every clone edge through
  `v` avoids `u`;
* so tetrahedron-freeness is preserved.

Tetrahedra are phrased on vertex sets (every three-subset of a
four-set is an edge), which keeps the swap arithmetic in
`insert`/`erase` vocabulary. -/

namespace FlagAlgebras.Core

variable {n : ℕ}

/-- Swap `u` for `v` in an edge. -/
private def swapEdge (u v : Fin n) (e : Finset (Fin n)) : Finset (Fin n) :=
  insert v (e.erase u)

/-- Clone `u`'s link onto `v`: keep the edges avoiding `v`, and add the
swapped copies of the edges through `u` avoiding `v`. -/
def Sym3Graph.cloneAt (G : Sym3Graph n) (u v : Fin n) (huv : u ≠ v) :
    Sym3Graph n :=
  ⟨(G.edges.filter fun e => v ∉ e)
    ∪ ((G.edges.filter fun e => u ∈ e ∧ v ∉ e)).image (swapEdge u v),
   by
    intro e he
    rcases Finset.mem_union.mp he with h | h
    · exact G.edges_valid e (Finset.mem_filter.mp h).1
    · obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.mp h
      have hmf := Finset.mem_filter.mp he₀
      have hcard := G.edges_valid e₀ hmf.1
      rw [swapEdge, Finset.card_insert_of_notMem
          (fun hmem => hmf.2.2 (Finset.mem_of_mem_erase hmem)),
        Finset.card_erase_of_mem hmf.2.1, hcard]⟩

/-- Membership in the clone. -/
lemma Sym3Graph.mem_cloneAt {G : Sym3Graph n} {u v : Fin n} {huv : u ≠ v}
    {e : Finset (Fin n)} :
    e ∈ (G.cloneAt u v huv).edges
      ↔ (e ∈ G.edges ∧ v ∉ e)
        ∨ (∃ e₀ ∈ G.edges, u ∈ e₀ ∧ v ∉ e₀ ∧ e = swapEdge u v e₀) := by
  show e ∈ _ ∪ _ ↔ _
  rw [Finset.mem_union]
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨(Finset.mem_filter.mp h).1, (Finset.mem_filter.mp h).2⟩
    · obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hm, hcond⟩ := Finset.mem_filter.mp he₀
      exact Or.inr ⟨e₀, hm, hcond.1, hcond.2, rfl⟩
  · rintro (⟨hm, hv⟩ | ⟨e₀, hm, hu, hv, rfl⟩)
    · exact Or.inl (Finset.mem_filter.mpr ⟨hm, hv⟩)
    · exact Or.inr (Finset.mem_image.mpr
        ⟨e₀, Finset.mem_filter.mpr ⟨hm, hu, hv⟩, rfl⟩)

/-- A swapped edge avoids `u`. -/
private lemma swapEdge_not_mem_u {u v : Fin n} (huv : u ≠ v)
    (e : Finset (Fin n)) : u ∉ swapEdge u v e := by
  rw [swapEdge, Finset.mem_insert]
  rintro (h | h)
  · exact huv h
  · exact absurd h (Finset.notMem_erase u e)

/-- A swapped edge contains `v`. -/
private lemma swapEdge_mem_v {u v : Fin n} (e : Finset (Fin n)) :
    v ∈ swapEdge u v e :=
  Finset.mem_insert_self v _

/-- Swapping back recovers the edge. -/
private lemma swapEdge_swapEdge {u v : Fin n} (huv : u ≠ v)
    {e : Finset (Fin n)} (hu : u ∈ e) (hv : v ∉ e) :
    swapEdge v u (swapEdge u v e) = e := by
  rw [swapEdge, swapEdge, Finset.erase_insert
      (fun hmem => hv (Finset.mem_of_mem_erase hmem)),
    Finset.insert_erase hu]

/-! ## The count ledger -/

/-- The exclusive degree: edges through `u` avoiding `v`. -/
def Sym3Graph.degreeAvoiding (G : Sym3Graph n) (u v : Fin n) : ℕ :=
  ((G.edges.filter fun e => u ∈ e ∧ v ∉ e)).card

/-- The number of edges avoiding a vertex. -/
def Sym3Graph.countAvoiding (G : Sym3Graph n) (v : Fin n) : ℕ :=
  (G.edges.filter fun e => v ∉ e).card

/-- **The clone's edge count**: the avoiding part plus the exclusive
degree. -/
theorem Sym3Graph.card_cloneAt (G : Sym3Graph n) (u v : Fin n)
    (huv : u ≠ v) :
    (G.cloneAt u v huv).edges.card
      = G.countAvoiding v + G.degreeAvoiding u v := by
  show ((G.edges.filter fun e => v ∉ e)
      ∪ ((G.edges.filter fun e => u ∈ e ∧ v ∉ e)).image
          (swapEdge u v)).card = _
  rw [Finset.card_union_of_disjoint, countAvoiding, degreeAvoiding,
    Finset.card_image_of_injOn]
  · intro e₁ h₁ e₂ h₂ heq
    have hu₁ := (Finset.mem_filter.mp h₁).2.1
    have hv₁ := (Finset.mem_filter.mp h₁).2.2
    have hu₂ := (Finset.mem_filter.mp h₂).2.1
    have hv₂ := (Finset.mem_filter.mp h₂).2.2
    have := congrArg (swapEdge v u) heq
    rwa [swapEdge_swapEdge huv hu₁ hv₁,
      swapEdge_swapEdge huv hu₂ hv₂] at this
  · rw [Finset.disjoint_right]
    intro e he hmem
    obtain ⟨e₀, -, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp hmem).2 (swapEdge_mem_v e₀)

/-! ## The gain estimate -/

/-- The codegree: edges through both vertices. -/
def Sym3Graph.codegree (G : Sym3Graph n) (u v : Fin n) : ℕ :=
  (G.edges.filter fun e => u ∈ e ∧ v ∈ e).card

/-- The exclusive degree and the codegree partition the degree. -/
lemma Sym3Graph.degreeAvoiding_add_codegree (G : Sym3Graph n)
    (u v : Fin n) :
    G.degreeAvoiding u v + G.codegree u v
      = (G.edges.filter fun e => u ∈ e).card := by
  rw [degreeAvoiding, codegree]
  rw [show (G.edges.filter fun e => u ∈ e ∧ v ∉ e)
      = (G.edges.filter fun e => u ∈ e).filter fun e => v ∉ e from by
    rw [Finset.filter_filter],
    show (G.edges.filter fun e => u ∈ e ∧ v ∈ e)
      = (G.edges.filter fun e => u ∈ e).filter fun e => v ∈ e from by
    rw [Finset.filter_filter]]
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := G.edges.filter fun e => u ∈ e) (p := fun e => v ∈ e)
  omega

/-- The avoiding count and the degree partition the edge count. -/
lemma Sym3Graph.countAvoiding_add_degree' (G : Sym3Graph n) (v : Fin n) :
    G.countAvoiding v + (G.edges.filter fun e => v ∈ e).card
      = G.edges.card := by
  rw [countAvoiding]
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := G.edges) (p := fun e => v ∈ e)
  omega

/-- The pair is inside every shared edge. -/
private lemma pair_subset_of_mem {u v : Fin n} {e : Finset (Fin n)}
    (hu : u ∈ e) (hv : v ∈ e) : ({u, v} : Finset (Fin n)) ⊆ e := by
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy'
  · exact hu
  · rw [Finset.mem_singleton] at hy'
    exact hy' ▸ hv

/-- **The codegree is at most `n − 2`**: each shared edge is determined
by its third vertex. The counting map sends an edge to its singleton
remainder past the pair; the pair-union recovers the edge, so the map
is injective, and the remainders live among the other vertices. -/
lemma Sym3Graph.codegree_le (G : Sym3Graph n) {u v : Fin n}
    (huv : u ≠ v) : G.codegree u v ≤ n - 2 := by
  classical
  have hle := Finset.card_le_card_of_injOn
    (s := G.edges.filter fun e => u ∈ e ∧ v ∈ e)
    (t := ((Finset.univ.erase u).erase v).image
      (fun w => ({w} : Finset (Fin n))))
    (fun e => e \ {u, v})
    (fun e he => by
      have hm := (Finset.mem_filter.mp he).1
      have hu := (Finset.mem_filter.mp he).2.1
      have hv := (Finset.mem_filter.mp he).2.2
      have hcard := G.edges_valid e hm
      have hsub := pair_subset_of_mem hu hv
      have hsd : (e \ {u, v}).card = 1 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hcard,
          Finset.card_insert_of_notMem
            (fun h => huv (Finset.mem_singleton.mp h)),
          Finset.card_singleton]
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hsd
      have hwm : w ∈ e \ ({u, v} : Finset (Fin n)) := by
        rw [hw]; exact Finset.mem_singleton_self w
      have hwuv := (Finset.mem_sdiff.mp hwm).2
      show e \ {u, v} ∈ _
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, ?_, hw.symm⟩)
      exact Finset.mem_erase.mpr
        ⟨fun h => hwuv (by
            rw [h]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self v)),
         Finset.mem_erase.mpr
          ⟨fun h => hwuv (by
              rw [h]
              exact Finset.mem_insert_self u _),
           Finset.mem_univ _⟩⟩)
    (fun e₁ h₁ e₂ h₂ heq => by
      have hs₁ := pair_subset_of_mem (Finset.mem_filter.mp h₁).2.1
        (Finset.mem_filter.mp h₁).2.2
      have hs₂ := pair_subset_of_mem (Finset.mem_filter.mp h₂).2.1
        (Finset.mem_filter.mp h₂).2.2
      have heq' : e₁ \ ({u, v} : Finset (Fin n)) = e₂ \ {u, v} := heq
      calc e₁ = {u, v} ∪ e₁ \ {u, v} :=
            (Finset.union_sdiff_of_subset hs₁).symm
        _ = {u, v} ∪ e₂ \ {u, v} := by rw [heq']
        _ = e₂ := Finset.union_sdiff_of_subset hs₂)
  refine le_trans hle ?_
  rw [Finset.card_image_of_injective _
      (fun a b hab => Finset.singleton_injective hab),
    Finset.card_erase_of_mem (Finset.mem_erase.mpr
      ⟨Ne.symm huv, Finset.mem_univ _⟩),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  omega

/-- **A degree gap beyond the codegree makes cloning gain edges.** -/
theorem Sym3Graph.card_cloneAt_gt (G : Sym3Graph n) {u v : Fin n}
    (huv : u ≠ v)
    (hgap : (G.edges.filter fun e => v ∈ e).card + G.codegree u v
      < (G.edges.filter fun e => u ∈ e).card) :
    G.edges.card < (G.cloneAt u v huv).edges.card := by
  have h1 := G.card_cloneAt u v huv
  have h2 := G.degreeAvoiding_add_codegree u v
  have h3 := G.countAvoiding_add_degree' v
  omega

/-! ## Cloning preserves tetrahedron-freeness -/

/-- A tetrahedron on a vertex set: every three-subset of some four-set
is an edge. -/
def Sym3Graph.HasTetraSet (G : Sym3Graph n) : Prop :=
  ∃ S : Finset (Fin n), S.card = 4
    ∧ ∀ t ⊆ S, t.card = 3 → t ∈ G.edges

/-- **A tetrahedron of the clone pulls back to the host.** The swap
direction when the clone set misses `u`; impossible through both `u`
and `v` since every clone edge through `v` avoids `u`. -/
theorem Sym3Graph.hasTetraSet_of_cloneAt {G : Sym3Graph n} {u v : Fin n}
    (huv : u ≠ v) (h : (G.cloneAt u v huv).HasTetraSet) :
    G.HasTetraSet := by
  obtain ⟨S, hS4, hall⟩ := h
  by_cases hvS : v ∈ S
  · by_cases huS : u ∈ S
    · -- both ends in the set: the mixed triple is impossible
      exfalso
      have hx : ((S.erase u).erase v).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem
            (Finset.mem_erase.mpr ⟨(Ne.symm huv), hvS⟩),
          Finset.card_erase_of_mem huS, hS4]
        norm_num
      obtain ⟨x, hxm⟩ := hx
      have hxv : x ≠ v := (Finset.mem_erase.mp hxm).1
      have hxu : x ≠ u :=
        (Finset.mem_erase.mp (Finset.mem_of_mem_erase hxm)).1
      have hxS : x ∈ S :=
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hxm)
      have htsub : ({u, v, x} : Finset (Fin n)) ⊆ S := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy'
        · exact huS
        rcases Finset.mem_insert.mp hy' with rfl | hy''
        · exact hvS
        · rw [Finset.mem_singleton] at hy''
          exact hy'' ▸ hxS
      have htcard : ({u, v, x} : Finset (Fin n)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by
            rw [Finset.mem_insert, Finset.mem_singleton]
            rintro (h | h)
            · exact huv h
            · exact hxu h.symm),
          Finset.card_insert_of_notMem (by
            rw [Finset.mem_singleton]
            exact fun h => hxv h.symm),
          Finset.card_singleton]
      have hmem := hall _ htsub htcard
      rcases mem_cloneAt.mp hmem with ⟨-, hv'⟩ | ⟨e₀, -, -, -, heq⟩
      · exact hv' (Finset.mem_insert_of_mem (Finset.mem_insert_self v _))
      · exact swapEdge_not_mem_u huv e₀
          (heq ▸ Finset.mem_insert_self u _)
    · -- swap the clone set back through u
      refine ⟨insert u (S.erase v), ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem
            (fun hmem => huS (Finset.mem_of_mem_erase hmem)),
          Finset.card_erase_of_mem hvS, hS4]
      · intro t' ht' hc'
        by_cases hut' : u ∈ t'
        · -- the swapped triple
          have hvt' : v ∉ t' := by
            intro hvm
            rcases Finset.mem_insert.mp (ht' hvm) with h | h
            · exact huv h.symm
            · exact (Finset.mem_erase.mp h).1 rfl
          have htsub : swapEdge u v t' ⊆ S := by
            intro y hy
            rcases Finset.mem_insert.mp hy with rfl | hy'
            · exact hvS
            · have hyt := Finset.mem_of_mem_erase hy'
              have hyu := (Finset.mem_erase.mp hy').1
              rcases Finset.mem_insert.mp (ht' hyt) with h | h
              · exact absurd h hyu
              · exact Finset.mem_of_mem_erase h
          have htcard : (swapEdge u v t').card = 3 := by
            rw [swapEdge, Finset.card_insert_of_notMem
                (fun hmem => hvt' (Finset.mem_of_mem_erase hmem)),
              Finset.card_erase_of_mem hut', hc']
          have hmem := hall _ htsub htcard
          rcases mem_cloneAt.mp hmem with ⟨-, hv'⟩ | ⟨e₀, hm₀, hu₀, hv₀, heq⟩
          · exact absurd (swapEdge_mem_v t') hv'
          · have hrec : e₀ = t' := by
              have h1 := congrArg (swapEdge v u) heq
              rw [swapEdge_swapEdge huv hut' hvt',
                swapEdge_swapEdge huv hu₀ hv₀] at h1
              exact h1.symm
            exact hrec ▸ hm₀
        · -- the untouched triple
          have hsub : t' ⊆ S := by
            intro y hy
            rcases Finset.mem_insert.mp (ht' hy) with rfl | h
            · exact absurd hy hut'
            · exact Finset.mem_of_mem_erase h
          have hvt' : v ∉ t' := by
            intro hvm
            rcases Finset.mem_insert.mp (ht' hvm) with h | h
            · exact huv h.symm
            · exact (Finset.mem_erase.mp h).1 rfl
          have hmem := hall _ hsub hc'
          rcases mem_cloneAt.mp hmem with ⟨hm, -⟩ | ⟨e₀, -, -, -, heq⟩
          · exact hm
          · exact absurd (heq ▸ swapEdge_mem_v e₀) hvt'
  · -- the clone set avoids v: everything is a host edge
    refine ⟨S, hS4, fun t ht hc => ?_⟩
    have hvt : v ∉ t := fun hvm => hvS (ht hvm)
    rcases mem_cloneAt.mp (hall t ht hc) with ⟨hm, -⟩ | ⟨e₀, -, -, -, heq⟩
    · exact hm
    · exact absurd (heq ▸ swapEdge_mem_v e₀) hvt

end FlagAlgebras.Core
