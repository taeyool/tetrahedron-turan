import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootSamples
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootOrderedColumn
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootFlags
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Ext56
import LeanFlagAlgebras.Core.Compute.Mask6Inj
import LeanFlagAlgebras.Core.Compute.RootingReindex
import Mathlib.Data.Fintype.CardEmbedding

/-! # The ordered five-root evaluator is a flag-square coefficient

Literal ordered records are reindexed by root injections. The compact link
lookup selects the unique labeled flag, and the two outside orders give twice
the factor product. These identities are independent of the fast evaluator's
automorphism and canonicalization implementation.
-/

namespace FlagAlgebras.Core.Tetrahedron.FullSevenLong

open FlagAlgebras.Core Classical

set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

lemma s5OutsideSum_two (θ : Fin 5 → Fin 7) (u v : Fin 7)
    (hθ : Function.Injective θ) (hu : u ∉ Finset.univ.image θ)
    (hv : v ∉ Finset.univ.image θ) (hne : u ≠ v) (f : Fin 7 → ℚ) :
    (∑ p ∈ Finset.univ.filter (fun p : Fin 7 × Fin 7 =>
      p.1 ∉ Finset.univ.image θ ∧ p.2 ∉ Finset.univ.image θ ∧ p.1 ≠ p.2),
      f p.1 * f p.2) = 2 * f u * f v := by
  have hcard : (Finset.univ \ Finset.univ.image θ).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_image_of_injective _ hθ, Finset.card_univ, Finset.card_univ]
    rfl
  have hout : Finset.univ \ Finset.univ.image θ = ({u, v} : Finset (Fin 7)) := by
    apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu⟩
      · rw [Finset.mem_singleton] at hx
        subst x
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩
    · rw [hcard, Finset.card_pair hne]
  have hmem : ∀ x : Fin 7, x ∉ Finset.univ.image θ ↔ x = u ∨ x = v := by
    intro x
    have h := Finset.ext_iff.mp hout x
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton] using h
  have hpairs : Finset.univ.filter (fun p : Fin 7 × Fin 7 =>
      p.1 ∉ Finset.univ.image θ ∧ p.2 ∉ Finset.univ.image θ ∧ p.1 ≠ p.2) =
      {(u, v), (v, u)} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem,
      Finset.mem_insert, Finset.mem_singleton]
    rcases p with ⟨a, b⟩
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨ha | ha, hb | hb, hn⟩
      · exact (hn (ha.trans hb.symm)).elim
      · exact Or.inl ⟨ha, hb⟩
      · exact Or.inr ⟨ha, hb⟩
      · exact (hn (ha.trans hb.symm)).elim
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨Or.inl rfl, Or.inr rfl, hne⟩
      · exact ⟨Or.inr rfl, Or.inl rfl, hne.symm⟩
  rw [hpairs]
  have hpne : (u, v) ≠ (v, u) := fun h => hne (congrArg Prod.fst h)
  rw [Finset.sum_pair hpne]
  ring

/-- The weight a factor row assigns to a literal standard-root extension. -/
noncomputable def s5RowWeight (b : Fin 18) (r : Fin (s5Rows b)) (X : Sym3Flag 5 6) : ℚ :=
  ∑ i : Fin (s5Dim b), (fS5 b r.val i.val : ℚ) *
    (if (s5Flag b i.val).IsIso X then 1 else 0)

/-- Exact lookup identifies the single flag realizing a valid link. -/
lemma s5RowWeight_lookup (b : Fin 18) (r : Fin (s5Rows b))
    (X : Sym3Flag 5 6) (m link : ℕ)
    (hstd : X.roots = ![0, 1, 2, 3, 4])
    (hgraph : graphOfMask 6 m = X.graph)
    (hmem : TetraFree.Mem X.graph.toModel)
    (hm : m < 2 ^ 20) (hlink : link < 1024)
    (hencode : s5Encode (s5Block b).sigma link = m) :
    s5RowWeight b r X =
      (fS5 b r.val ((s5Block b).linkIndex.getD link (s5Dim b)) : ℚ) := by
  have hbits : k4FreeMask (quadIdxList 6) (s5Encode (s5Block b).sigma link) = true := by
    rw [hencode]
    apply k4FreeMask_iff_mem.mpr
    rw [hgraph]
    exact hmem
  have hspec := s5_link_table_spec b link hlink hbits
  dsimp only at hspec
  let idx := (s5Block b).linkIndex.getD link (s5Dim b)
  have hi : idx < s5Dim b := hspec.1
  have himask : s5FlagMask b idx = m := hspec.2.trans hencode
  let I : Fin (s5Dim b) := ⟨idx, hi⟩
  have hiso : ∀ j : Fin (s5Dim b), (s5Flag b j.val).IsIso X ↔ j = I := by
    intro j
    rw [standardRoots6_isIso_iff _ X rfl hstd]
    change graphOfMask 6 (s5FlagMask b j.val) = X.graph ↔ j = I
    rw [← hgraph]
    constructor
    · intro h
      have hmask := graphOfMask6_inj (s5FlagMask_lt b j.val j.isLt) hm h
      exact Fin.ext (s5FlagMask_distinct b j.val j.isLt idx hi (hmask.trans himask.symm))
    · intro h
      subst j
      change graphOfMask 6 (s5FlagMask b idx) = graphOfMask 6 m
      rw [himask]
  change (∑ j : Fin (s5Dim b), (fS5 b r.val j.val : ℚ) *
    (if (s5Flag b j.val).IsIso X then 1 else 0)) = _
  simp only [hiso, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rfl

/-- A matching typed cell equals the sum of the actual ordered factor products. -/
lemma s5LinkCell_eq_extPairSum (b : Fin 18) (G : Sym3Graph 7)
    (θ : Fin 5 → Fin 7) (u v : Fin 7) (root left right ml mr : ℕ)
    (hG : TetraFree.Mem G.toModel) (hθ : Function.Injective θ)
    (hu : u ∉ Finset.univ.image θ) (hv : v ∉ Finset.univ.image θ) (hne : u ≠ v)
    (hroot : root = (s5Block b).sigma)
    (hgl : graphOfMask 6 ml = (extFlag6 G θ u).graph)
    (hgr : graphOfMask 6 mr = (extFlag6 G θ v).graph)
    (hml : ml < 2 ^ 20) (hmr : mr < 2 ^ 20)
    (hl : left < 1024) (hr : right < 1024)
    (hel : s5Encode (s5Block b).sigma left = ml)
    (her : s5Encode (s5Block b).sigma right = mr) :
    (s5LinkCell b root left right : ℚ) =
      ∑ r : Fin (s5Rows b), extPairSum56
        (fun i : Fin (s5Dim b) => (fS5 b r.val i.val : ℚ))
        (fun i => s5Flag b i.val) G θ := by
  have hmeml := extFlag6_graph_mem hθ hu hG
  have hmemr := extFlag6_graph_mem hθ hv hG
  have hbitsl : k4FreeMask (quadIdxList 6) (s5Encode (s5Block b).sigma left) = true := by
    rw [hel]
    apply k4FreeMask_iff_mem.mpr
    rw [hgl]
    exact hmeml
  have hbitsr : k4FreeMask (quadIdxList 6) (s5Encode (s5Block b).sigma right) = true := by
    rw [her]
    apply k4FreeMask_iff_mem.mpr
    rw [hgr]
    exact hmemr
  have hil := (s5_link_table_spec b left hl hbitsl).1
  have hir := (s5_link_table_spec b right hr hbitsr).1
  rw [s5LinkCell, if_pos hroot]
  dsimp only
  rw [if_pos ⟨hil, hir⟩]
  change ((2 * ∑ r : Fin (s5Rows b),
    fS5 b r.val ((s5Block b).linkIndex.getD left (s5Dim b)) *
      fS5 b r.val ((s5Block b).linkIndex.getD right (s5Dim b)) : ℤ) : ℚ) = _
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hp : extPairSum56
      (fun i : Fin (s5Dim b) => (fS5 b r.val i.val : ℚ))
      (fun i => s5Flag b i.val) G θ =
      2 * s5RowWeight b r (extFlag6 G θ u) * s5RowWeight b r (extFlag6 G θ v) := by
    exact s5OutsideSum_two θ u v hθ hu hv hne
      (fun x => s5RowWeight b r (extFlag6 G θ x))
  rw [hp, s5RowWeight_lookup b r _ ml left rfl hgl hmeml hml hl hel,
    s5RowWeight_lookup b r _ mr right rfl hgr hmemr hmr hr her]
  ring

private lemma s5Sigma_lt : ∀ b : Fin 18, (s5Block b).sigma < 2 ^ 10 := by
  native_decide

/-- The record indices enumerate the root injections bijectively. -/
noncomputable def s5OrderedRootEquiv : Fin 2520 ≃ (Fin 5 ↪ Fin 7) :=
  Equiv.ofBijective (fun k => ⟨s5OrderedRoot k, s5OrderedRoot_inj k⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro k l h
      exact s5OrderedRoot_index_injective (congrArg (fun e : Fin 5 ↪ Fin 7 => (e : Fin 5 → Fin 7)) h),
      by rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]; rfl⟩)

/-- Reindex the stored ordered records by all root injections. -/
lemma sum_s5OrderedRoots {M : Type*} [AddCommMonoid M]
    (f : (Fin 5 → Fin 7) → M) :
    (∑ k : Fin 2520, f (s5OrderedRoot k)) =
      ∑ θ ∈ Finset.univ.filter Function.Injective, f θ := by
  have h := s5OrderedRootEquiv.sum_comp (fun e : Fin 5 ↪ Fin 7 => f e)
  change (∑ k : Fin 2520, f (s5OrderedRoot k)) = ∑ e : Fin 5 ↪ Fin 7, f e at h
  rw [h, sum_embeddings_eq_rootSubset_perm, sum_injective_eq_rootSubset_perm]
  rfl

/-- A stored ordered cell is the corresponding typed factor-square sum, with
zero contribution when the rooting induces a different type. -/
lemma s5OrderedCell_sem (b : Fin 18) (k : Fin 2520) (w : ℕ)
    (hmem : TetraFree.Mem (graphOfMask 7 w).toModel) :
    (s5LinkCell b (s5Gather (s5OrderedSample k).rootGather 10 w)
      (s5LinkMask6 (s5Gather (s5OrderedSample k).leftGather 20 w))
      (s5LinkMask6 (s5Gather (s5OrderedSample k).rightGather 20 w)) : ℚ) =
    if (graphOfMask 7 w).pullback (s5OrderedRoot k) = s5Type b then
      ∑ r : Fin (s5Rows b), extPairSum56
        (fun i : Fin (s5Dim b) => (fS5 b r.val i.val : ℚ))
        (fun i => s5Flag b i.val) (graphOfMask 7 w) (s5OrderedRoot k)
    else 0 := by
  let root := s5Gather (s5OrderedSample k).rootGather 10 w
  let ml := s5Gather (s5OrderedSample k).leftGather 20 w
  let mr := s5Gather (s5OrderedSample k).rightGather 20 w
  have hml : ml < 2 ^ 20 := s5Gather_lt _ _ _
  have hmr : mr < 2 ^ 20 := s5Gather_lt _ _ _
  have hroot : root = (s5Block b).sigma ↔
      (graphOfMask 7 w).pullback (s5OrderedRoot k) = s5Type b := by
    rw [← s5OrderedRoot_graph]
    constructor
    · intro h
      exact congrArg (graphOfMask 5) h
    · exact graphOfMask5_inj (s5Gather_lt _ _ _) (s5Sigma_lt b)
  by_cases ht : root = (s5Block b).sigma
  · rw [if_pos (hroot.mp ht)]
    apply s5LinkCell_eq_extPairSum b (graphOfMask 7 w) (s5OrderedRoot k)
      (s5OrderedLeft k) (s5OrderedRight k) root (s5LinkMask6 ml) (s5LinkMask6 mr) ml mr
      hmem (s5OrderedRoot_inj k) (s5OrderedLeft_outside k) (s5OrderedRight_outside k)
      (s5OrderedOutside_ne k) ht (s5OrderedLeft_graph k w) (s5OrderedRight_graph k w)
      hml hmr (s5Gather_lt _ _ _) (s5Gather_lt _ _ _)
    · have h := s5Encode_roundtrip hml
      rw [s5OrderedLeft_rootMask k w] at h
      change s5Encode root (s5LinkMask6 ml) = ml at h
      rw [ht] at h
      exact h
    · have h := s5Encode_roundtrip hmr
      rw [s5OrderedRight_rootMask k w] at h
      change s5Encode root (s5LinkMask6 mr) = mr at h
      rw [ht] at h
      exact h
  · rw [if_neg (fun h => ht (hroot.mpr h))]
    change (s5LinkCell b root (s5LinkMask6 ml) (s5LinkMask6 mr) : ℚ) = 0
    rw [s5LinkCell, if_neg ht]
    rfl

/-- The ordered integer evaluator is exactly the unnormalized five-root SOS
coefficient, for every tetrahedron-free seven-vertex host. -/
theorem s5OrderedColumnNum_eq_ordered_sum (w : ℕ)
    (hmem : TetraFree.Mem (graphOfMask 7 w).toModel) :
    (s5OrderedColumnNum w : ℚ) =
      ∑ b : Fin 18, ∑ r : Fin (s5Rows b),
        ∑ θ ∈ rootingsOf (s5Type b) (graphOfMask 7 w), extPairSum56
          (fun i : Fin (s5Dim b) => (fS5 b r.val i.val : ℚ))
          (fun i => s5Flag b i.val) (graphOfMask 7 w) θ := by
  change ((∑ b : Fin 18, ∑ k : Fin 2520,
    s5LinkCell b (s5Gather (s5OrderedSample k).rootGather 10 w)
      (s5LinkMask6 (s5Gather (s5OrderedSample k).leftGather 20 w))
      (s5LinkMask6 (s5Gather (s5OrderedSample k).rightGather 20 w)) : ℤ) : ℚ) = _
  push_cast
  refine Finset.sum_congr rfl fun b _ => ?_
  simp_rw [s5OrderedCell_sem b _ w hmem]
  rw [sum_s5OrderedRoots (fun θ =>
    if (graphOfMask 7 w).pullback θ = s5Type b then
      ∑ r : Fin (s5Rows b), extPairSum56
        (fun i : Fin (s5Dim b) => (fS5 b r.val i.val : ℚ))
        (fun i => s5Flag b i.val) (graphOfMask 7 w) θ else 0)]
  rw [← Finset.sum_filter, Finset.filter_filter]
  change (∑ θ ∈ rootingsOf (s5Type b) (graphOfMask 7 w),
    ∑ r : Fin (s5Rows b), extPairSum56
      (fun i : Fin (s5Dim b) => (fS5 b r.val i.val : ℚ))
      (fun i => s5Flag b i.val) (graphOfMask 7 w) θ) = _
  exact Finset.sum_comm

end FlagAlgebras.Core.Tetrahedron.FullSevenLong
