import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Complete

/-! # The converse bridge and canonical forms

Slice 35 showed every tetrahedron-free six-vertex graph is isomorphic to
a listed representative. This file supplies the other half — that the
listed representatives are pairwise *non*-isomorphic — by turning the
packed permutation table into a complete description of isomorphism.

The key step is the converse of `isIso_graphOfMask_of_bits`: an
isomorphism of decoded masks is *always* witnessed by one of the 720
listed packed permutations (`exists_scan_of_isIso`). It follows because
the listed permutations are pairwise distinct and there are exactly
`6! = 720` of them, so they exhaust `Equiv.Perm (Fin 6)`.

With both directions available, the orbit of a mask under the table is
exactly its isomorphism class, so the least element of that orbit is a
complete invariant. Masks that are their own orbit minimum and are
distinct are therefore non-isomorphic (`not_isIso_of_orbitMin`) — the
form in which the 964 representatives are separated, once the orbit
minima are computed. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

/-! ## Validation of the packed permutation table -/

/-- The rank map entries of `r`, read off the twenty triple positions. -/
def rankList (r : ℕ) : List ℕ :=
  (List.range 20).map fun t => (r >>> (5 * t)) &&& 31

set_option maxRecDepth 65536 in
/-- Each listed rank map is injective on ranks. -/
lemma rankLists_nodup :
    ((List.range 720).all fun i => decide ((rankList (getRank i)).Nodup))
      = true := by
  decide +kernel

set_option maxRecDepth 65536 in
/-- Each listed rank map lands in the twenty triple positions. -/
lemma rankLists_lt :
    ((List.range 720).all fun i =>
      (rankList (getRank i)).all fun v => decide (v < 20)) = true := by
  decide +kernel

set_option maxRecDepth 65536 in
/-- The 720 listed packed permutations are pairwise distinct as vertex
maps. -/
lemma permGraphs_nodup :
    ((List.range 720).map fun i =>
      (List.finRange 6).map (permFn (getPerm i))).Nodup := by
  decide +kernel

lemma rankList_nodup_of_lt {i : ℕ} (hi : i < 720) :
    (rankList (getRank i)).Nodup :=
  of_decide_eq_true (List.all_eq_true.mp rankLists_nodup i
    (List.mem_range.mpr hi))

lemma rankList_lt_of_lt {i : ℕ} (hi : i < 720) :
    ∀ t ∈ List.range 20, (getRank i >>> (5 * t)) &&& 31 < 20 := by
  intro t ht
  have h := List.all_eq_true.mp rankLists_lt i (List.mem_range.mpr hi)
  exact of_decide_eq_true
    (List.all_eq_true.mp h _ (List.mem_map.mpr ⟨t, ht, rfl⟩))

/-! ## The listed permutations exhaust `Equiv.Perm (Fin 6)` -/

/-- Total version of the listed permutation, junk outside the table. -/
noncomputable def permEquivOf (i : ℕ) : Equiv.Perm (Fin 6) :=
  if h : Function.Injective (permFn (getPerm i)) then
    Equiv.ofBijective _ ⟨h, Finite.surjective_of_injective h⟩
  else 1

lemma permFn_injective_of_lt {i : ℕ} (hi : i < 720) :
    Function.Injective (permFn (getPerm i)) := by
  have h := permConsistent_of_lt hi
  unfold permConsistent at h
  rw [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

lemma coe_permEquivOf {i : ℕ} (hi : i < 720) :
    ⇑(permEquivOf i) = permFn (getPerm i) := by
  unfold permEquivOf
  rw [dif_pos (permFn_injective_of_lt hi)]
  rfl

/-- Every permutation of the six vertices is a listed packed
permutation: the table is complete. -/
lemma exists_getPerm_eq (p : Equiv.Perm (Fin 6)) :
    ∃ i, i < 720 ∧ permFn (getPerm i) = ⇑p := by
  have hinjOn : Set.InjOn permEquivOf (Finset.range 720) := by
    intro a ha b hb hab
    have ha' : a < 720 := Finset.mem_range.mp (by exact_mod_cast ha)
    have hb' : b < 720 := Finset.mem_range.mp (by exact_mod_cast hb)
    have hfun : permFn (getPerm a) = permFn (getPerm b) := by
      rw [← coe_permEquivOf ha', ← coe_permEquivOf hb', hab]
    exact List.inj_on_of_nodup_map permGraphs_nodup (List.mem_range.mpr ha')
      (List.mem_range.mpr hb') (by rw [hfun])
  have hcard : ((Finset.range 720).image permEquivOf).card = 720 := by
    rw [Finset.card_image_of_injOn hinjOn, Finset.card_range]
  have huniv : (Finset.range 720).image permEquivOf = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [hcard, Fintype.card_perm, Fintype.card_fin]
    rfl
  obtain ⟨i, hi, hip⟩ :=
    Finset.mem_image.mp (huniv ▸ Finset.mem_univ p)
  refine ⟨i, Finset.mem_range.mp hi, ?_⟩
  rw [← coe_permEquivOf (Finset.mem_range.mp hi), hip]

/-! ## Bits of the fast image, and the correspondence it satisfies -/

lemma rankApply_testBit (r m k : ℕ) :
    (rankApply r m).testBit k
      = (List.range 20).any fun t =>
          decide (m.testBit t = true)
            && decide ((r >>> (5 * t)) &&& 31 = k) := by
  rw [rankApply, testBit_foldl_or (c := fun t => m.testBit t = true)
    (g := fun t => (r >>> (5 * t)) &&& 31)]
  simp

lemma rank_inj_of_nodup {r : ℕ} (hnd : (rankList r).Nodup) {s t : ℕ}
    (hs : s < 20) (ht : t < 20)
    (h : (r >>> (5 * s)) &&& 31 = (r >>> (5 * t)) &&& 31) : s = t :=
  List.inj_on_of_nodup_map hnd (List.mem_range.mpr hs)
    (List.mem_range.mpr ht) h

/-- The fast image always passes the correspondence check. -/
lemma scanOK_rankApply {r m : ℕ} (hnd : (rankList r).Nodup) :
    scanOK m r (rankApply r m) = true := by
  unfold scanOK
  rw [List.all_eq_true]
  intro rk hrk
  have hrk' : rk < 20 := List.mem_range.mp hrk
  rw [beq_iff_eq, rankApply_testBit]
  cases hm : m.testBit rk with
  | true =>
    refine (List.any_eq_true.mpr ⟨rk, hrk, ?_⟩).symm
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true hm, decide_eq_true rfl⟩
  | false =>
    refine (Bool.eq_false_iff.mpr fun hany => ?_).symm
    obtain ⟨t, htmem, hcond⟩ := List.any_eq_true.mp hany
    rw [Bool.and_eq_true] at hcond
    have ht' : t < 20 := List.mem_range.mp htmem
    have hte := rank_inj_of_nodup hnd ht' hrk' (of_decide_eq_true hcond.2)
    rw [hte] at hcond
    rw [of_decide_eq_true hcond.1] at hm
    cases hm

lemma rankApply_lt {r m : ℕ}
    (hlt : ∀ t ∈ List.range 20, (r >>> (5 * t)) &&& 31 < 20) :
    rankApply r m < 2 ^ 20 :=
  foldl_or_lt_two_pow _ _ _ _ _ (Nat.two_pow_pos 20) hlt

/-! ## The converse bridge -/

/-- A sorted triple's bit is set exactly when its vertex set is an
edge. -/
lemma testBit_iff_mem_edges {m : ℕ} {a b c : Fin 6} (hab : a < b)
    (hbc : b < c) :
    m.testBit (triIdx 6 a.val b.val c.val) = true
      ↔ ({a, b, c} : Finset (Fin 6)) ∈ (graphOfMask 6 m).edges := by
  constructor
  · intro hbit
    exact mem_graphOfMask_edges.mpr ⟨a, b, c, hab, hbc, hbit, rfl⟩
  · intro hmem
    obtain ⟨x, y, z, hxy, hyz, hbit, heq⟩ := mem_graphOfMask_edges.mp hmem
    obtain ⟨rfl, rfl, rfl⟩ := sorted_triple_eq hxy hyz hab hbc heq.symm
    exact hbit

/-- Every rank below twenty is the rank of a sorted triple. -/
lemma exists_triple_of_rank : ∀ rk < 20,
    ∃ a b c : Fin 6, a < b ∧ b < c ∧ triIdx 6 a.val b.val c.val = rk := by
  decide

/-- **The converse bridge**: an isomorphism of decoded masks is always
witnessed by one of the listed packed permutations. -/
lemma exists_scan_of_isIso {m h : ℕ}
    (hiso : (graphOfMask 6 m).IsIso (graphOfMask 6 h)) :
    ∃ i, i < 720 ∧ scanOK m (getRank i) h = true := by
  obtain ⟨p, hp⟩ := hiso
  obtain ⟨i, hi, hpi⟩ := exists_getPerm_eq p
  refine ⟨i, hi, ?_⟩
  have hc := permConsistent_of_lt hi
  unfold permConsistent at hc
  rw [Bool.and_eq_true] at hc
  have hinj := of_decide_eq_true hc.1
  have hmapAll := of_decide_eq_true hc.2
  unfold scanOK
  rw [List.all_eq_true]
  intro rk hrk
  obtain ⟨a, b, c, hab, hbc, rfl⟩ :=
    exists_triple_of_rank rk (List.mem_range.mp hrk)
  rw [beq_iff_eq, hmapAll a b c hab hbc]
  set s := sort3 (permFn (getPerm i) a) (permFn (getPerm i) b)
    (permFn (getPerm i) c) with hs
  have hd₁ : permFn (getPerm i) a ≠ permFn (getPerm i) b :=
    fun e => hab.ne (hinj e)
  have hd₂ : permFn (getPerm i) a ≠ permFn (getPerm i) c :=
    fun e => (hab.trans hbc).ne (hinj e)
  have hd₃ : permFn (getPerm i) b ≠ permFn (getPerm i) c :=
    fun e => hbc.ne (hinj e)
  obtain ⟨hs₁, hs₂⟩ := sort3_sorted hd₁ hd₂ hd₃
  have hset : ({s.1, s.2.1, s.2.2} : Finset (Fin 6))
      = Finset.image ⇑p {a, b, c} := by
    rw [hs, sort3_finset, Finset.image_insert, Finset.image_insert,
      Finset.image_singleton, hpi]
  rw [Bool.eq_iff_iff, testBit_iff_mem_edges hab hbc,
    testBit_iff_mem_edges hs₁ hs₂, hset]
  constructor
  · intro hmem
    rw [← hp]
    exact Finset.mem_image_of_mem _ hmem
  · intro hmem
    rw [← hp] at hmem
    obtain ⟨Y, hY, hYeq⟩ := Finset.mem_image.mp hmem
    have hYabc : Y = {a, b, c} := Finset.image_injective p.injective hYeq
    rwa [← hYabc]

/-! ## Canonical forms -/

/-- The orbit of a mask under the listed permutations. -/
def orbitOf (m : ℕ) : List ℕ :=
  (List.range 720).map fun k => rankApply (getRank k) m

/-- The canonical form: the least mask in the orbit. -/
def orbitMin (m : ℕ) : ℕ := (orbitOf m).foldr min m

lemma foldr_min_le_of_mem :
    ∀ {l : List ℕ} {x d : ℕ}, x ∈ l → l.foldr min d ≤ x
  | [], _, _, hx => absurd hx (by simp)
  | _ :: _, _, _, hx => by
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (foldr_min_le_of_mem hmem)

lemma orbitMin_le_of_mem {m x : ℕ} (hx : x ∈ orbitOf m) : orbitMin m ≤ x :=
  foldr_min_le_of_mem hx

/-- Two masks below `2 ^ 20` agreeing on the low twenty bits are
equal. -/
lemma eq_of_low_bits {x y : ℕ} (hx : x < 2 ^ 20) (hy : y < 2 ^ 20)
    (h : ∀ k < 20, x.testBit k = y.testBit k) : x = y := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  by_cases hk : k < 20
  · exact h k hk
  · have h20 : (2 : ℕ) ^ 20 ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx h20),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy h20)]

/-- A certified correspondence pins the image mask. -/
lemma eq_rankApply_of_scanOK {r m h : ℕ} (hnd : (rankList r).Nodup)
    (hlt : ∀ t ∈ List.range 20, (r >>> (5 * t)) &&& 31 < 20)
    (hh : h < 2 ^ 20) (hscan : scanOK m r h = true) :
    h = rankApply r m := by
  have hscan' := List.all_eq_true.mp hscan
  have hself := List.all_eq_true.mp (scanOK_rankApply (m := m) hnd)
  refine eq_of_low_bits hh (rankApply_lt hlt) fun k hk => ?_
  obtain ⟨t, htmem, hteq⟩ :
      ∃ t ∈ List.range 20, (r >>> (5 * t)) &&& 31 = k := by
    have hsurj : ((rankList r).toFinset : Finset ℕ)
        = (List.range 20).toFinset := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        rw [List.mem_toFinset] at hx ⊢
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
        exact List.mem_range.mpr (hlt t ht)
      · rw [List.toFinset_card_of_nodup hnd,
          List.toFinset_card_of_nodup (List.nodup_range)]
        simp [rankList]
    have hk' : k ∈ (rankList r).toFinset := by
      rw [hsurj, List.mem_toFinset]
      exact List.mem_range.mpr hk
    rw [List.mem_toFinset] at hk'
    obtain ⟨t, ht, hteq⟩ := List.mem_map.mp hk'
    exact ⟨t, ht, hteq⟩
  have h₁ := hscan' t htmem
  have h₂ := hself t htmem
  rw [beq_iff_eq, hteq] at h₁ h₂
  rw [← h₁, ← h₂]

/-- Isomorphism of computational 3-graphs is symmetric. -/
lemma isIso_symm {n : ℕ} {G H : Sym3Graph n} (h : G.IsIso H) : H.IsIso G := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p⁻¹, ?_⟩
  have hid : (Finset.image ⇑p⁻¹ ∘ Finset.image ⇑p) = id := by
    funext X
    simp [Finset.image_image]
  rw [← hp, Finset.image_image, hid, Finset.image_id]

/-- The orbit contains every mask isomorphic to its source. -/
lemma mem_orbitOf_of_isIso {m h : ℕ} (hh : h < 2 ^ 20)
    (hiso : (graphOfMask 6 m).IsIso (graphOfMask 6 h)) :
    h ∈ orbitOf m := by
  obtain ⟨i, hi, hscan⟩ := exists_scan_of_isIso hiso
  rw [eq_rankApply_of_scanOK (rankList_nodup_of_lt hi)
    (rankList_lt_of_lt hi) hh hscan]
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

/-- **Separation by canonical form**: distinct masks that are each the
least element of their own orbit are non-isomorphic. -/
theorem not_isIso_of_orbitMin {a b : ℕ} (ha20 : a < 2 ^ 20)
    (hb20 : b < 2 ^ 20) (hamin : orbitMin a = a) (hbmin : orbitMin b = b)
    (hne : a ≠ b) :
    ¬(graphOfMask 6 a).IsIso (graphOfMask 6 b) := by
  intro hiso
  have hba : b ∈ orbitOf a := mem_orbitOf_of_isIso hb20 hiso
  have hab : a ∈ orbitOf b := mem_orbitOf_of_isIso ha20 (isIso_symm hiso)
  have h₁ : a ≤ b := hamin ▸ orbitMin_le_of_mem hba
  have h₂ : b ≤ a := hbmin ▸ orbitMin_le_of_mem hab
  exact hne (le_antisymm h₁ h₂)

/-- Every element of a list lies in one of its length-`n` blocks. -/
lemma mem_take_drop_of_mem {α : Type} {l : List α} {x : α} {n : ℕ}
    (hn : 0 < n) (hx : x ∈ l) : ∃ j, x ∈ (l.drop (n * j)).take n := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hsplit : n * (i / n) + i % n = i := Nat.div_add_mod i n
  have hmod : i % n < n := Nat.mod_lt i hn
  refine ⟨i / n, List.mem_iff_getElem.mpr ⟨i % n, ?_, ?_⟩⟩
  · rw [List.length_take, List.length_drop]
    omega
  · rw [List.getElem_take, List.getElem_drop]
    simp only [hsplit]

end FlagAlgebras.Core.Tetrahedron
