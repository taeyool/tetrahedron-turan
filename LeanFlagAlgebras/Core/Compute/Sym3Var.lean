import LeanFlagAlgebras.Core.Compute.Sym3Delete

/-! # Degree statistics as pattern counts

The first exact identity of the variance bridge: the sum of squared
degrees double-counts ordered edge pairs by the size of their
intersection. Since a pair of hyperedges spans at most six vertices,
every term is a pattern count on at most six vertices — which is what
lets the empirical degree variance be read as a flag-density
combination later on. -/

namespace FlagAlgebras.Core

variable {n : ℕ}

/-- Ordered edge pairs with intersection of a given size. -/
def Sym3Graph.pairCountInter (G : Sym3Graph n) (k : ℕ) : ℕ :=
  ((G.edges ×ˢ G.edges).filter fun p => (p.1 ∩ p.2).card = k).card

/-- The diagonal: pairs meeting in all three vertices are the equal
pairs. -/
lemma Sym3Graph.pairCountInter_three (G : Sym3Graph n) :
    G.pairCountInter 3 = G.edges.card := by
  rw [pairCountInter]
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · rintro ⟨e, f⟩ hp
    have hm := (Finset.mem_filter.mp hp).1
    exact (Finset.mem_product.mp hm).1
  · rintro ⟨e₁, f₁⟩ h₁ ⟨e₂, f₂⟩ h₂ heq
    have hc₁ := (Finset.mem_filter.mp h₁).2
    have hc₂ := (Finset.mem_filter.mp h₂).2
    have hm₁ := Finset.mem_product.mp (Finset.mem_filter.mp h₁).1
    have hm₂ := Finset.mem_product.mp (Finset.mem_filter.mp h₂).1
    have hef₁ : e₁ = f₁ := by
      have h3 := G.edges_valid e₁ hm₁.1
      have hsub : e₁ ∩ f₁ ⊆ e₁ := Finset.inter_subset_left
      have hcard : (e₁ ∩ f₁).card = e₁.card := by rw [hc₁, h3]
      have he : e₁ ∩ f₁ = e₁ :=
        Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
      have hsub2 : e₁ ⊆ f₁ := by
        rw [← he]
        exact Finset.inter_subset_right
      exact Finset.eq_of_subset_of_card_le hsub2
        (le_of_eq ((G.edges_valid f₁ hm₁.2).trans h3.symm))
    have hef₂ : e₂ = f₂ := by
      have h3 := G.edges_valid e₂ hm₂.1
      have hsub : e₂ ∩ f₂ ⊆ e₂ := Finset.inter_subset_left
      have hcard : (e₂ ∩ f₂).card = e₂.card := by rw [hc₂, h3]
      have he : e₂ ∩ f₂ = e₂ :=
        Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
      have hsub2 : e₂ ⊆ f₂ := by
        rw [← he]
        exact Finset.inter_subset_right
      exact Finset.eq_of_subset_of_card_le hsub2
        (le_of_eq ((G.edges_valid f₂ hm₂.2).trans h3.symm))
    dsimp at heq
    rw [Prod.mk.injEq]
    exact ⟨heq, by rw [← hef₁, ← hef₂, heq]⟩
  · intro e he
    refine ⟨(e, e), ?_, rfl⟩
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨he, he⟩, ?_⟩
    rw [Finset.inter_self]
    exact G.edges_valid e he

/-- The pair counts are isomorphism invariants: the permutation carries
ordered edge pairs to ordered edge pairs and preserves intersection
sizes. -/
lemma Sym3Graph.IsIso.pairCountInter_eq {G H : Sym3Graph n}
    (h : G.IsIso H) (k : ℕ) :
    G.pairCountInter k = H.pairCountInter k := by
  obtain ⟨p, hp⟩ := h
  have hmemH : ∀ e ∈ G.edges, e.image ⇑p ∈ H.edges := fun e he => by
    rw [← hp]
    exact Finset.mem_image_of_mem _ he
  have hmemG : ∀ e ∈ H.edges, e.image ⇑p.symm ∈ G.edges := fun e he => by
    rw [← hp] at he
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.mp he
    rwa [Finset.image_image, Equiv.symm_comp_self, Finset.image_id]
  rw [Sym3Graph.pairCountInter, Sym3Graph.pairCountInter]
  refine Finset.card_bij (fun q _ => (q.1.image ⇑p, q.2.image ⇑p)) ?_ ?_ ?_
  · rintro ⟨e, f⟩ hq
    obtain ⟨hmem, hc⟩ := Finset.mem_filter.mp hq
    have hm := Finset.mem_product.mp hmem
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hmemH e hm.1, hmemH f hm.2⟩, ?_⟩
    show (e.image ⇑p ∩ f.image ⇑p).card = k
    rw [← Finset.image_inter _ _ p.injective,
      Finset.card_image_of_injective _ p.injective]
    exact hc
  · rintro ⟨e₁, f₁⟩ h₁ ⟨e₂, f₂⟩ h₂ heq
    rw [Prod.mk.injEq] at heq ⊢
    exact ⟨Finset.image_injective p.injective heq.1,
      Finset.image_injective p.injective heq.2⟩
  · rintro ⟨e, f⟩ hq
    obtain ⟨hmem, hc⟩ := Finset.mem_filter.mp hq
    have hm := Finset.mem_product.mp hmem
    have hround : ∀ e : Finset (Fin n), (e.image ⇑p.symm).image ⇑p = e :=
      fun e => by
        rw [Finset.image_image, Equiv.self_comp_symm, Finset.image_id]
    refine ⟨(e.image ⇑p.symm, f.image ⇑p.symm), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hmemG e hm.1, hmemG f hm.2⟩, ?_⟩, ?_⟩
    · show (e.image ⇑p.symm ∩ f.image ⇑p.symm).card = k
      rw [← Finset.image_inter _ _ p.symm.injective,
        Finset.card_image_of_injective _ p.symm.injective]
      exact hc
    · rw [Prod.mk.injEq]
      exact ⟨hround e, hround f⟩

/-- Pullbacks along injections stay in the theory: the pullback is the
comap, and theories are hereditary. -/
lemma Sym3Graph.pullback_mem {𝕋 : RelTheory hypergraph3Sig} {m : ℕ}
    {G : Sym3Graph n} (hG : 𝕋.Mem G.toModel) {f : Fin m → Fin n}
    (hf : Function.Injective f) : 𝕋.Mem (G.pullback f).toModel := by
  rw [G.pullback_toModel hf]
  exact 𝕋.mem_comap ⟨f, hf⟩ hG

/-- A `k`-intersecting edge pair spans `6 - k` vertices. -/
lemma Sym3Graph.union_mem_powersetCard {G : Sym3Graph n} {k m : ℕ}
    (hkm : k + m = 6) {q : Finset (Fin n) × Finset (Fin n)}
    (hq : q ∈ (G.edges ×ˢ G.edges).filter
      fun q => (q.1 ∩ q.2).card = k) :
    q.1 ∪ q.2 ∈ (Finset.univ.powersetCard m : Finset (Finset (Fin n))) := by
  obtain ⟨hmem, hc⟩ := Finset.mem_filter.mp hq
  have hm := Finset.mem_product.mp hmem
  refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
  have hu := Finset.card_union_add_card_inter q.1 q.2
  rw [hc, G.edges_valid _ hm.1, G.edges_valid _ hm.2] at hu
  omega

/-- **Within a fixed union, the intersecting pairs are the pullback's**:
a pair with intersection size `k` inside an `m = 6 - k`-subset spans it,
so the host pairs with that union correspond exactly to the pullback's
pairs. -/
lemma Sym3Graph.pairCount_union_eq_pullback (G : Sym3Graph n)
    {k m : ℕ} (hkm : k + m = 6) {W : Finset (Fin n)} (hW : W.card = m) :
    ((G.edges ×ˢ G.edges).filter
        fun q => (q.1 ∩ q.2).card = k ∧ q.1 ∪ q.2 = W).card
      = (G.pullback (subsetTuple W hW)).pairCountInter k := by
  have hsinj : Function.Injective (subsetTuple W hW) :=
    subsetTuple_injective W hW
  -- the image of the coordinate preimage recovers any subset of `W`
  have himg : ∀ e : Finset (Fin n), e ⊆ W →
      (Finset.univ.filter fun i => subsetTuple W hW i ∈ e).image
        (subsetTuple W hW) = e := by
    intro e he
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hi).2
    · intro hy
      have hyW : y ∈ W := he hy
      rw [← subsetTuple_image_univ W hW] at hyW
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hyW
      exact Finset.mem_image_of_mem _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hy⟩)
  rw [Sym3Graph.pairCountInter]
  refine (Finset.card_bij
    (fun q _ => (q.1.image (subsetTuple W hW),
      q.2.image (subsetTuple W hW))) ?_ ?_ ?_).symm
  · rintro ⟨e, f⟩ hq
    obtain ⟨hmem, hc⟩ := Finset.mem_filter.mp hq
    have hm := Finset.mem_product.mp hmem
    have he3 := (G.pullback (subsetTuple W hW)).edges_valid _ hm.1
    have hf3 := (G.pullback (subsetTuple W hW)).edges_valid _ hm.2
    have heG : e.image (subsetTuple W hW) ∈ G.edges :=
      (Finset.mem_filter.mp (show e ∈ Finset.univ.filter _ from hm.1)).2.2
    have hfG : f.image (subsetTuple W hW) ∈ G.edges :=
      (Finset.mem_filter.mp (show f ∈ Finset.univ.filter _ from hm.2)).2.2
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨heG, hfG⟩, ?_, ?_⟩
    · show (e.image (subsetTuple W hW) ∩ f.image (subsetTuple W hW)).card = k
      rw [← Finset.image_inter _ _ hsinj,
        Finset.card_image_of_injective _ hsinj]
      exact hc
    · show e.image (subsetTuple W hW) ∪ f.image (subsetTuple W hW) = W
      rw [← Finset.image_union]
      have huniv : e ∪ f = Finset.univ := by
        refine Finset.eq_univ_of_card _ ?_
        have hu := Finset.card_union_add_card_inter e f
        rw [hc, he3, hf3] at hu
        rw [Fintype.card_fin]
        omega
      rw [huniv]
      exact subsetTuple_image_univ W hW
  · rintro ⟨e₁, f₁⟩ h₁ ⟨e₂, f₂⟩ h₂ heq
    rw [Prod.mk.injEq] at heq ⊢
    exact ⟨Finset.image_injective hsinj heq.1,
      Finset.image_injective hsinj heq.2⟩
  · rintro ⟨e, f⟩ hq
    obtain ⟨hmem, hc, huw⟩ := Finset.mem_filter.mp hq
    have hm := Finset.mem_product.mp hmem
    have heW : e ⊆ W := huw ▸ Finset.subset_union_left
    have hfW : f ⊆ W := huw ▸ Finset.subset_union_right
    have hpull : ∀ e ∈ G.edges, e ⊆ W →
        (Finset.univ.filter fun i => subsetTuple W hW i ∈ e)
          ∈ (G.pullback (subsetTuple W hW)).edges := by
      intro e he hsub
      show _ ∈ Finset.univ.filter fun e' : Finset (Fin m) =>
        e'.card = 3 ∧ e'.image (subsetTuple W hW) ∈ G.edges
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [← Finset.card_image_of_injective _ hsinj, himg e hsub]
        exact G.edges_valid e he
      · rw [himg e hsub]
        exact he
    refine ⟨(Finset.univ.filter fun i => subsetTuple W hW i ∈ e,
      Finset.univ.filter fun i => subsetTuple W hW i ∈ f),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨hpull e hm.1 heW, hpull f hm.2 hfW⟩, ?_⟩, ?_⟩
    · show ((Finset.univ.filter fun i => subsetTuple W hW i ∈ e)
          ∩ Finset.univ.filter fun i => subsetTuple W hW i ∈ f).card = k
      have hfi : (Finset.univ.filter fun i => subsetTuple W hW i ∈ e)
          ∩ (Finset.univ.filter fun i => subsetTuple W hW i ∈ f)
          = Finset.univ.filter fun i => subsetTuple W hW i ∈ e ∩ f := by
        ext i
        simp [Finset.mem_inter]
      rw [hfi, ← Finset.card_image_of_injective _ hsinj,
        himg (e ∩ f) (Finset.inter_subset_left.trans heW)]
      exact hc
    · rw [Prod.mk.injEq]
      exact ⟨himg e heW, himg f hfW⟩

/-- **The union fibration**: the `k`-intersecting ordered edge pairs
split by their union over the `(6 - k)`-subsets, and within each subset
they are the pullback's pairs. -/
theorem Sym3Graph.pairCountInter_eq_sum_pullback (G : Sym3Graph n)
    {k m : ℕ} (hkm : k + m = 6) :
    G.pairCountInter k
      = ∑ W ∈ (Finset.univ.powersetCard m :
            Finset (Finset (Fin n))).attach,
          (G.pullback (subsetTuple W.val
              (Finset.mem_powersetCard.mp W.property).2)).pairCountInter k := by
  rw [Sym3Graph.pairCountInter,
    Finset.card_eq_sum_card_fiberwise
      (fun q hq => Sym3Graph.union_mem_powersetCard hkm hq),
    ← Finset.sum_attach (Finset.univ.powersetCard m)
      (fun W => (((G.edges ×ˢ G.edges).filter
        fun q => (q.1 ∩ q.2).card = k).filter
          fun q => q.1 ∪ q.2 = W).card)]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finset.filter_filter]
  exact G.pairCount_union_eq_pullback hkm
    (Finset.mem_powersetCard.mp W.property).2

/-! ## The pattern decomposition over canonical representatives

Summing the union fibration by the isomorphism type of the induced
subgraph: the `k`-intersecting pairs of a host are counted by the listed
`(6 - k)`-vertex member patterns, each weighted by its own local pair
count. This is the finite form in which the degree statistics enter the
flag-density comparison. -/

private lemma list_sum_finset_sum_comm {α β M : Type} [AddCommMonoid M]
    (t : Finset β) (g : α → β → M) :
    ∀ L : List α,
      (L.map fun a => ∑ b ∈ t, g a b).sum
        = ∑ b ∈ t, (L.map fun a => g a b).sum := by
  intro L
  induction L with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

private lemma list_sum_map_of_unique {α M : Type} [AddCommMonoid M]
    {P : α → Prop} [DecidablePred P] {c : α → M} {v : M}
    (hc : ∀ a, P a → c a = v) :
    ∀ L : List α, L.Pairwise (fun a b => ¬ (P a ∧ P b)) →
      (∃ a ∈ L, P a) →
      (L.map fun a => if P a then c a else 0).sum = v := by
  intro L
  induction L with
  | nil =>
    rintro - ⟨a, ha, -⟩
    simp at ha
  | cons a l ih =>
    rintro hpw hex
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpw
    by_cases hPa : P a
    · rw [List.map_cons, List.sum_cons, if_pos hPa, hc a hPa]
      have hz : (l.map fun x => if P x then c x else 0).sum = 0 := by
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        rw [if_neg fun hPy => hhead y hy ⟨hPa, hPy⟩]
      rw [hz, add_zero]
    · obtain ⟨b, hb, hPb⟩ := hex
      rcases List.mem_cons.mp hb with rfl | hbl
      · exact absurd hPb hPa
      · rw [List.map_cons, List.sum_cons, if_neg hPa, zero_add]
        exact ih htail ⟨b, hbl, hPb⟩

/-- **Pattern decomposition over the canonical representatives**: for a
host in a theory, the `k`-intersecting ordered edge pairs are counted by
the listed `m = 6 - k`-vertex member patterns, each weighted by its
local pair count. Every induced subgraph is isomorphic to exactly one
listed representative, and the pair counts transport along the
isomorphism. -/
theorem Sym3Graph.sum_reps_pairCountInter {𝕋 : RelTheory hypergraph3Sig}
    {m : ℕ} [DecidablePred fun H : Sym3Graph m => 𝕋.Mem H.toModel]
    (G : Sym3Graph n) (hG : 𝕋.Mem G.toModel) {k : ℕ} (hkm : k + m = 6) :
    (((sym3Reps m).filter fun H => decide (𝕋.Mem H.toModel)).map
        fun H => H.pairCountInter k * H.flagCountC G).sum
      = G.pairCountInter k := by
  classical
  rw [G.pairCountInter_eq_sum_pullback hkm]
  have hopen : ∀ H : Sym3Graph m,
      H.pairCountInter k * H.flagCountC G
        = ∑ W ∈ (Finset.univ.powersetCard m :
            Finset (Finset (Fin n))).attach,
            if H.IsIso (G.pullback (subsetTuple W.val
                (Finset.mem_powersetCard.mp W.property).2))
            then H.pairCountInter k else 0 := by
    intro H
    rw [Sym3Graph.flagCountC, Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun W _ => ?_
    by_cases hiso : H.IsIso (G.pullback (subsetTuple W.val
        (Finset.mem_powersetCard.mp W.property).2)) <;>
      simp [hiso]
  rw [List.map_congr_left fun H _ => hopen H, list_sum_finset_sum_comm]
  refine Finset.sum_congr rfl fun W _ => ?_
  have hpWmem : 𝕋.Mem (G.pullback (subsetTuple W.val
      (Finset.mem_powersetCard.mp W.property).2)).toModel :=
    Sym3Graph.pullback_mem hG (subsetTuple_injective _ _)
  obtain ⟨R, hRreps, hRiso⟩ := sym3Reps_complete
    (G.pullback (subsetTuple W.val
      (Finset.mem_powersetCard.mp W.property).2))
  have hRmem : 𝕋.Mem R.toModel := by
    obtain ⟨e⟩ := (Sym3Graph.isIso_iff_nonempty_modelIso _ R).mp hRiso
    exact 𝕋.mem_iso e hpWmem
  refine list_sum_map_of_unique
    (fun H hH => hH.pairCountInter_eq k) _ ?_ ?_
  · exact ((sym3Reps_pairwise m).filter _).imp fun hnab hPab =>
      hnab (hPab.1.trans hPab.2.symm)
  · exact ⟨R, List.mem_filter.mpr ⟨hRreps, decide_eq_true hRmem⟩,
      hRiso.symm⟩

/-- **The squared-degree identity**: the degrees' squares double-count
ordered edge pairs by intersection size. -/
theorem Sym3Graph.sum_degree_sq (G : Sym3Graph n) :
    (∑ v : Fin n, G.degree v ^ 2)
      = 3 * G.edges.card + 2 * G.pairCountInter 2
        + G.pairCountInter 1 := by
  have hswap : (∑ v : Fin n, G.degree v ^ 2)
      = ∑ p ∈ G.edges ×ˢ G.edges, (p.1 ∩ p.2).card := by
    have h1 : ∀ v : Fin n, G.degree v ^ 2
        = ∑ p ∈ G.edges ×ˢ G.edges,
            (if v ∈ p.1 ∩ p.2 then 1 else 0) := by
      intro v
      rw [show G.degree v ^ 2 = G.degree v * G.degree v from sq (G.degree v) ▸ rfl]
      rw [Sym3Graph.degree, Finset.card_filter,
        Finset.sum_mul_sum, Finset.sum_product]
      refine Finset.sum_congr rfl fun e _ => ?_
      refine Finset.sum_congr rfl fun f _ => ?_
      by_cases h1 : v ∈ e <;> by_cases h2 : v ∈ f <;>
        simp [h1, h2, Finset.mem_inter]
    rw [Finset.sum_congr rfl fun v (_ : v ∈ Finset.univ) => h1 v,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.card_eq_sum_ones (p.1 ∩ p.2), Finset.sum_ite_mem,
      Finset.univ_inter]
  rw [hswap]
  have hle : ∀ p ∈ G.edges ×ˢ G.edges, (p.1 ∩ p.2).card < 4 := by
    rintro ⟨e, f⟩ hp
    have hm := Finset.mem_product.mp hp
    have h3 := G.edges_valid e hm.1
    calc (e ∩ f).card ≤ e.card := Finset.card_le_card
          Finset.inter_subset_left
      _ = 3 := h3
      _ < 4 := by norm_num
  rw [show (∑ p ∈ G.edges ×ˢ G.edges, (p.1 ∩ p.2).card)
      = ∑ k ∈ Finset.range 4,
          ∑ p ∈ (G.edges ×ˢ G.edges).filter
            (fun p => (p.1 ∩ p.2).card = k), (p.1 ∩ p.2).card from
    (Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_range.mpr (hle p hp)) _).symm]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  have hval : ∀ k, (∑ p ∈ (G.edges ×ˢ G.edges).filter
      (fun p => (p.1 ∩ p.2).card = k), (p.1 ∩ p.2).card)
      = k * G.pairCountInter k := by
    intro k
    rw [pairCountInter, Finset.card_eq_sum_ones, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [(Finset.mem_filter.mp hp).2, mul_one]
  rw [hval 0, hval 1, hval 2, hval 3, pairCountInter_three]
  ring

/-- **The pair partition**: the ordered edge pairs split by intersection
size, so the squared edge count is the four pair counts. The companion
of `sum_degree_sq` for the mean side of the variance. -/
theorem Sym3Graph.sum_pairCountInter (G : Sym3Graph n) :
    G.pairCountInter 0 + G.pairCountInter 1 + G.pairCountInter 2
      + G.edges.card = G.edges.card * G.edges.card := by
  have hle : ∀ p ∈ G.edges ×ˢ G.edges, (p.1 ∩ p.2).card < 4 := by
    rintro ⟨e, f⟩ hp
    have hm := Finset.mem_product.mp hp
    have h3 := G.edges_valid e hm.1
    calc (e ∩ f).card ≤ e.card := Finset.card_le_card
          Finset.inter_subset_left
      _ = 3 := h3
      _ < 4 := by norm_num
  rw [← Finset.card_product,
    Finset.card_eq_sum_card_fiberwise
      (f := fun p => (p.1 ∩ p.2).card) (t := Finset.range 4)
      (fun p hp => Finset.mem_range.mpr (hle p hp)),
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  have h0 : ((G.edges ×ˢ G.edges).filter
      fun p => (p.1 ∩ p.2).card = 0).card = G.pairCountInter 0 := rfl
  have h1 : ((G.edges ×ˢ G.edges).filter
      fun p => (p.1 ∩ p.2).card = 1).card = G.pairCountInter 1 := rfl
  have h2 : ((G.edges ×ˢ G.edges).filter
      fun p => (p.1 ∩ p.2).card = 2).card = G.pairCountInter 2 := rfl
  have h3 : ((G.edges ×ˢ G.edges).filter
      fun p => (p.1 ∩ p.2).card = 3).card = G.pairCountInter 3 := rfl
  rw [h0, h1, h2, h3, pairCountInter_three]
  omega

end FlagAlgebras.Core
