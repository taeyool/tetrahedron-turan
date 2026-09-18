import LeanFlagAlgebras.Core.Compute.Sym3Fiber
import LeanFlagAlgebras.Core.Examples.TetrahedronMask
import LeanFlagAlgebras.Core.Examples.TetrahedronStationarity
import Mathlib.Tactic.FinCases

/-! # The extension flags of a one-rooting of a seven-vertex host

The order-7 one-root family lives at the single-vertex type: a witness
subset carries the root and **three** of the six outside vertices, so
the extension flag takes an ordered sorted triple, and a root-preserving
isomorphism can permute the three freely — no rigidity, the isomorphism
test stays decidable.

With six outside vertices the only-roots-shared condition forces the
two witness subsets to split them three and three, so the witness pairs
are the disjoint sorted triples — `pairChoose 6 3 3 = 20` per rooting,
`140 = 7 · 20` in all, which is exactly the certificate's `s1Gathers`
table. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

open Classical

/-- The extension flag of a one-rooting at three outside vertices. -/
def extFlagS1 (G : Sym3Graph 7) (θ : Fin 1 → Fin 7) (a b c : Fin 7) :
    Sym3Flag 1 4 :=
  ⟨G.pullback ![θ 0, a, b, c], ![0]⟩

section ExtS1

variable {G : Sym3Graph 7} {θ : Fin 1 → Fin 7} {a b c : Fin 7}

lemma extTupleS1_injective
    (ha : a ∉ Finset.univ.image θ) (hb : b ∉ Finset.univ.image θ)
    (hc : c ∉ Finset.univ.image θ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![θ 0, a, b, c] := by
  have hnea : θ 0 ≠ a := fun h =>
    ha (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, h⟩)
  have hneb : θ 0 ≠ b := fun h =>
    hb (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, h⟩)
  have hnec : θ 0 ≠ c := fun h =>
    hc (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, h⟩)
  intro x y hxy
  fin_cases x <;> fin_cases y <;>
    first
      | rfl
      | exact absurd hxy hnea
      | exact absurd hxy.symm hnea
      | exact absurd hxy hneb
      | exact absurd hxy.symm hneb
      | exact absurd hxy hnec
      | exact absurd hxy.symm hnec
      | exact absurd hxy hab
      | exact absurd hxy.symm hab
      | exact absurd hxy hac
      | exact absurd hxy.symm hac
      | exact absurd hxy hbc
      | exact absurd hxy.symm hbc

lemma extFlagS1_wellFormed
    (hwf : (Sym3Flag.mk G θ).WellFormed vertexGraph) :
    (extFlagS1 G θ a b c).WellFormed vertexGraph := by
  constructor
  · have h : Function.Injective (![0] : Fin 1 → Fin 4) := by decide
    exact fun x y hxy => h hxy
  · show (G.pullback ![θ 0, a, b, c]).pullback ![0] = vertexGraph
    rw [Sym3Graph.pullback_pullback]
    have hcomp : (![θ 0, a, b, c] ∘ ![(0 : Fin 4)]) = θ := by
      funext t
      fin_cases t <;> rfl
    rw [hcomp]
    exact hwf.2

lemma extFlagS1_graph_mem
    (ha : a ∉ Finset.univ.image θ) (hb : b ∉ Finset.univ.image θ)
    (hc : c ∉ Finset.univ.image θ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hG : TetraFree.Mem G.toModel) :
    TetraFree.Mem (extFlagS1 G θ a b c).graph.toModel := by
  show TetraFree.Mem (G.pullback ![θ 0, a, b, c]).toModel
  rw [Sym3Graph.pullback_toModel _
    (extTupleS1_injective ha hb hc hab hac hbc)]
  exact TetraFree.mem_comap _ hG

/-- Isomorphism tests against equal classes agree. -/
lemma isIso_congr_classS1 {F A B : Sym3Flag 1 4}
    (hwfF : F.WellFormed vertexGraph) (hwfA : A.WellFormed vertexGraph)
    (hwfB : B.WellFormed vertexGraph) (hF : TetraFree.Mem F.graph.toModel)
    (hA : TetraFree.Mem A.graph.toModel)
    (hB : TetraFree.Mem B.graph.toModel)
    (hAB : A.toFlag hwfA hA = B.toFlag hwfB hB) :
    F.IsIso A ↔ F.IsIso B := by
  rw [← Sym3Flag.toFlag_eq_toFlag_iff hwfF hwfA hF hA,
    ← Sym3Flag.toFlag_eq_toFlag_iff hwfF hwfB hF hB, hAB]

lemma insert3_card_four
    (ha : a ∉ Finset.univ.image θ) (hb : b ∉ Finset.univ.image θ)
    (hc : c ∉ Finset.univ.image θ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (insert a (insert b (insert c (Finset.univ.image θ)))).card = 4 := by
  have himg : (Finset.univ.image θ).card = 1 := by
    rw [show (Finset.univ : Finset (Fin 1)) = {0} from by decide,
      Finset.image_singleton, Finset.card_singleton]
  rw [Finset.card_insert_of_notMem (fun h => by
      rcases Finset.mem_insert.mp h with h' | h'
      · exact hab h'
      rcases Finset.mem_insert.mp h' with h'' | h''
      · exact hac h''
      · exact ha h''),
    Finset.card_insert_of_notMem (fun h => by
      rcases Finset.mem_insert.mp h with h' | h'
      · exact hbc h'
      · exact hb h'),
    Finset.card_insert_of_notMem hc, himg]

/-- A four-element root-containing subset is the root plus a sorted
triple of outside vertices. -/
lemma eq_insert3_of_card_four
    {W : Finset (Fin 7)} (hsub : Finset.univ.image θ ⊆ W)
    (hcard : W.card = 4) :
    ∃ x y z : Fin 7, x < y ∧ y < z
      ∧ x ∉ Finset.univ.image θ ∧ y ∉ Finset.univ.image θ
      ∧ z ∉ Finset.univ.image θ
      ∧ W = insert x (insert y (insert z (Finset.univ.image θ))) := by
  have himg : (Finset.univ.image θ).card = 1 := by
    rw [show (Finset.univ : Finset (Fin 1)) = {0} from by decide,
      Finset.image_singleton, Finset.card_singleton]
  have hsd : (W \ Finset.univ.image θ).card = 3 := by
    have h := Finset.card_sdiff (s := Finset.univ.image θ) (t := W)
    rw [Finset.inter_eq_left.mpr hsub] at h
    omega
  obtain ⟨x, y, z, hxy, hyz, hS⟩ := exists_sorted_triple hsd
  have hxm : x ∈ W \ Finset.univ.image θ := by
    rw [hS]; exact Finset.mem_insert_self _ _
  have hym : y ∈ W \ Finset.univ.image θ := by
    rw [hS]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hzm : z ∈ W \ Finset.univ.image θ := by
    rw [hS]
    exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  refine ⟨x, y, z, hxy, hyz, (Finset.mem_sdiff.mp hxm).2,
    (Finset.mem_sdiff.mp hym).2, (Finset.mem_sdiff.mp hzm).2, ?_⟩
  ext w
  constructor
  · intro hw
    by_cases hwi : w ∈ Finset.univ.image θ
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem hwi))
    · have hwd : w ∈ W \ Finset.univ.image θ :=
        Finset.mem_sdiff.mpr ⟨hw, hwi⟩
      rw [hS] at hwd
      rcases Finset.mem_insert.mp hwd with rfl | hwd'
      · exact Finset.mem_insert_self _ _
      rcases Finset.mem_insert.mp hwd' with rfl | hwd''
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · rw [Finset.mem_singleton] at hwd''
        subst hwd''
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_self _ _))
  · intro hw
    rcases Finset.mem_insert.mp hw with rfl | hw'
    · exact (Finset.mem_sdiff.mp hxm).1
    rcases Finset.mem_insert.mp hw' with rfl | hw''
    · exact (Finset.mem_sdiff.mp hym).1
    rcases Finset.mem_insert.mp hw'' with rfl | hw'''
    · exact (Finset.mem_sdiff.mp hzm).1
    · exact hsub hw'''

/-- The extension flag is the restriction of the rooted host to the
root plus the three outside vertices, as labeled flags. -/
noncomputable def extFlagIsoS1
    (hwf : (Sym3Flag.mk G θ).WellFormed vertexGraph)
    (ha : a ∉ Finset.univ.image θ) (hb : b ∉ Finset.univ.image θ)
    (hc : c ∉ Finset.univ.image θ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hG : TetraFree.Mem G.toModel)
    (hroot' : ∀ t, ((Sym3Flag.mk G θ).toLabeledFlag
      hwf hG).rootEmbed.toEmbedding t
        ∈ insert a (insert b (insert c (Finset.univ.image θ))))
    (hwfE : (extFlagS1 G θ a b c).WellFormed vertexGraph)
    (hmemE : TetraFree.Mem (extFlagS1 G θ a b c).graph.toModel) :
    (extFlagS1 G θ a b c).toLabeledFlag hwfE hmemE
      ≃ᶠ ((Sym3Flag.mk G θ).toLabeledFlag hwf hG).restrict
          (insert a (insert b (insert c (Finset.univ.image θ)))) hroot' := by
  have hmem : ∀ i : Fin 4,
      ![θ 0, a, b, c] i
        ∈ insert a (insert b (insert c (Finset.univ.image θ))) := by
    intro i
    fin_cases i
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)))
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hcard : (insert a (insert b (insert c
      (Finset.univ.image θ)))).card = 4 :=
    insert3_card_four ha hb hc hab hac hbc
  refine ⟨⟨Equiv.ofBijective
    (fun i => ⟨![θ 0, a, b, c] i, hmem i⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun x y hxy => extTupleS1_injective ha hb hc hab hac hbc
        (congrArg Subtype.val hxy),
       by rw [Fintype.card_fin, Fintype.card_coe, hcard]⟩),
    fun r f => ?_⟩, fun t => ?_⟩
  · show (G.toModel.comap (Function.Embedding.subtype _)).interp r _
      ↔ (G.pullback ![θ 0, a, b, c]).toModel.interp r f
    rw [Sym3Graph.pullback_toModel _
      (extTupleS1_injective ha hb hc hab hac hbc)]
    exact Iff.rfl
  · refine Subtype.ext ?_
    fin_cases t <;> rfl

/-- The induced typed sub-flag on the root plus three outside vertices
is the canonical extension flag, as classes. -/
lemma pullbackFlag_insert3_class_eq
    (hwf : (Sym3Flag.mk G θ).WellFormed vertexGraph)
    (ha : a ∉ Finset.univ.image θ) (hb : b ∉ Finset.univ.image θ)
    (hc : c ∉ Finset.univ.image θ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hG : TetraFree.Mem G.toModel)
    (hcard : (insert a (insert b (insert c
      (Finset.univ.image θ)))).card = 4)
    (hroots : ∀ i, (Sym3Flag.mk G θ).roots i
      ∈ insert a (insert b (insert c (Finset.univ.image θ))))
    (hwfP : ((Sym3Flag.mk G θ).pullbackFlag _ hcard hroots).WellFormed
      vertexGraph)
    (hmemP : TetraFree.Mem ((Sym3Flag.mk G θ).pullbackFlag _ hcard
      hroots).graph.toModel)
    (hwfE : (extFlagS1 G θ a b c).WellFormed vertexGraph)
    (hmemE : TetraFree.Mem (extFlagS1 G θ a b c).graph.toModel) :
    ((Sym3Flag.mk G θ).pullbackFlag _ hcard hroots).toFlag hwfP hmemP
      = (extFlagS1 G θ a b c).toFlag hwfE hmemE := by
  refine Quotient.sound ⟨?_⟩
  exact (pullbackFlagIso hwf hG hcard hroots (fun t => hroots t)
      hwfP hmemP).trans
    (extFlagIsoS1 hwf ha hb hc hab hac hbc hG (fun t => hroots t)
      hwfE hmemE).symm

/-- Induced sub-flags on equal subsets have equal classes. -/
lemma pullbackFlag_congr_WS1 {Gσ : Sym3Flag 1 7} {W W' : Finset (Fin 7)}
    (hWW : W = W')
    {hcard : W.card = 4} {hroots : ∀ t, Gσ.roots t ∈ W}
    {hcard' : W'.card = 4} {hroots' : ∀ t, Gσ.roots t ∈ W'}
    {hwfP : (Gσ.pullbackFlag W hcard hroots).WellFormed vertexGraph}
    {hmemP : TetraFree.Mem (Gσ.pullbackFlag W hcard
      hroots).graph.toModel}
    {hwfP' : (Gσ.pullbackFlag W' hcard' hroots').WellFormed vertexGraph}
    {hmemP' : TetraFree.Mem (Gσ.pullbackFlag W' hcard'
      hroots').graph.toModel} :
    (Gσ.pullbackFlag W hcard hroots).toFlag hwfP hmemP
      = (Gσ.pullbackFlag W' hcard' hroots').toFlag hwfP' hmemP' := by
  subst hWW
  rfl

/-- Peeling the root image off equal three-insert sets. -/
lemma insert3_set_eq {x y z x' y' z' : Fin 7}
    (hx : x ∉ Finset.univ.image θ) (hy : y ∉ Finset.univ.image θ)
    (hz : z ∉ Finset.univ.image θ)
    (hx' : x' ∉ Finset.univ.image θ) (hy' : y' ∉ Finset.univ.image θ)
    (hz' : z' ∉ Finset.univ.image θ)
    (h : insert x (insert y (insert z (Finset.univ.image θ)))
      = insert x' (insert y' (insert z' (Finset.univ.image θ)))) :
    ({x, y, z} : Finset (Fin 7)) = {x', y', z'} := by
  have hout : ∀ {w : Fin 7}, w ∈ ({x, y, z} : Finset (Fin 7)) →
      w ∉ Finset.univ.image θ := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw'
    · exact hx
    rcases Finset.mem_insert.mp hw' with rfl | hw''
    · exact hy
    · rw [Finset.mem_singleton] at hw''
      subst hw''
      exact hz
  have hout' : ∀ {w : Fin 7}, w ∈ ({x', y', z'} : Finset (Fin 7)) →
      w ∉ Finset.univ.image θ := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw'
    · exact hx'
    rcases Finset.mem_insert.mp hw' with rfl | hw''
    · exact hy'
    · rw [Finset.mem_singleton] at hw''
      subst hw''
      exact hz'
  have hbig : ∀ {w : Fin 7}, w ∈ ({x, y, z} : Finset (Fin 7)) →
      w ∈ insert x' (insert y' (insert z' (Finset.univ.image θ))) := by
    intro w hw
    rw [← h]
    rcases Finset.mem_insert.mp hw with rfl | hw'
    · exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hw' with rfl | hw''
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [Finset.mem_singleton] at hw''
      subst hw''
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hbig' : ∀ {w : Fin 7}, w ∈ ({x', y', z'} : Finset (Fin 7)) →
      w ∈ insert x (insert y (insert z (Finset.univ.image θ))) := by
    intro w hw
    rw [h]
    rcases Finset.mem_insert.mp hw with rfl | hw'
    · exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hw' with rfl | hw''
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [Finset.mem_singleton] at hw''
      subst hw''
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  ext w
  constructor
  · intro hw
    have hwm := hbig hw
    have hwo := hout hw
    rcases Finset.mem_insert.mp hwm with rfl | hwm'
    · exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hwm' with rfl | hwm''
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    rcases Finset.mem_insert.mp hwm'' with rfl | hwm'''
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    · exact absurd hwm''' hwo
  · intro hw
    have hwm := hbig' hw
    have hwo := hout' hw
    rcases Finset.mem_insert.mp hwm with rfl | hwm'
    · exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hwm' with rfl | hwm''
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    rcases Finset.mem_insert.mp hwm'' with rfl | hwm'''
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    · exact absurd hwm''' hwo

/-- The sorted disjoint outside-triple pairs of a one-rooting. -/
def outsideTriples (θ : Fin 1 → Fin 7) :
    Finset ((Fin 7 × Fin 7 × Fin 7) × (Fin 7 × Fin 7 × Fin 7)) :=
  Finset.univ.filter fun p =>
    p.1.1 < p.1.2.1 ∧ p.1.2.1 < p.1.2.2
      ∧ p.2.1 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2
      ∧ p.1.1 ∉ Finset.univ.image θ ∧ p.1.2.1 ∉ Finset.univ.image θ
      ∧ p.1.2.2 ∉ Finset.univ.image θ
      ∧ p.2.1 ∉ Finset.univ.image θ ∧ p.2.2.1 ∉ Finset.univ.image θ
      ∧ p.2.2.2 ∉ Finset.univ.image θ
      ∧ p.1.1 ≠ p.2.1 ∧ p.1.1 ≠ p.2.2.1 ∧ p.1.1 ≠ p.2.2.2
      ∧ p.1.2.1 ≠ p.2.1 ∧ p.1.2.1 ≠ p.2.2.1 ∧ p.1.2.1 ≠ p.2.2.2
      ∧ p.1.2.2 ≠ p.2.1 ∧ p.1.2.2 ≠ p.2.2.1 ∧ p.1.2.2 ≠ p.2.2.2

set_option maxRecDepth 8192 in
/-- **The typed pair count at a one-rooting** is the count of sorted
disjoint outside-triple pairs whose extension flags realize the two
patterns. -/
lemma flagPairCountC_eq_extPairsS1 {F₁ F₂ : Sym3Flag 1 4}
    (hwf₁ : F₁.WellFormed vertexGraph) (hwf₂ : F₂.WellFormed vertexGraph)
    (h₁ : TetraFree.Mem F₁.graph.toModel)
    (h₂ : TetraFree.Mem F₂.graph.toModel)
    (hwf : (Sym3Flag.mk G θ).WellFormed vertexGraph)
    (hG : TetraFree.Mem G.toModel) :
    F₁.flagPairCountC F₂ (Sym3Flag.mk G θ)
      = ((outsideTriples θ).filter (fun p =>
          F₁.IsIso (extFlagS1 G θ p.1.1 p.1.2.1 p.1.2.2)
            ∧ F₂.IsIso (extFlagS1 G θ p.2.1 p.2.2.1 p.2.2.2))).card := by
  classical
  rw [Sym3Flag.flagPairCountC]
  have hins : ∀ {x y z : Fin 7}, x ∉ Finset.univ.image θ →
      y ∉ Finset.univ.image θ → z ∉ Finset.univ.image θ →
      x ≠ y → x ≠ z → y ≠ z →
      insert x (insert y (insert z (Finset.univ.image θ)))
        ∈ (Finset.univ.powersetCard 4 : Finset (Finset (Fin 7))) :=
    fun {x y z} hx hy hz hxy hxz hyz => Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, insert3_card_four hx hy hz hxy hxz hyz⟩
  have hrootsub : ∀ {x y z : Fin 7},
      ∀ t, (Sym3Flag.mk G θ).roots t
        ∈ insert x (insert y (insert z (Finset.univ.image θ))) :=
    fun {x y z} t => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩)))
  refine (Finset.card_bij
    (fun p hp => ⟨(insert p.1.1 (insert p.1.2.1
        (insert p.1.2.2 (Finset.univ.image θ))),
      insert p.2.1 (insert p.2.2.1
        (insert p.2.2.2 (Finset.univ.image θ)))),
      Finset.mem_product.mpr
        ⟨hins ((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).2.2.2.2.1
          ((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).2.2.2.2.2.1
          ((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).2.2.2.2.2.2.1
          ((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).1.ne
          (((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).1.trans
            ((Finset.mem_filter.mp
              ((Finset.mem_filter.mp hp).1)).2).2.1).ne
          ((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).2.1.ne,
         hins ((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).2.2.2.2.2.2.2.1
          ((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).2.2.2.2.2.2.2.2.1
          ((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).2.2.2.2.2.2.2.2.2.1
          ((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).2.2.1.ne
          (((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).2.2.1.trans
            ((Finset.mem_filter.mp
              ((Finset.mem_filter.mp hp).1)).2).2.2.2.1).ne
          ((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).2.2.2.1.ne⟩⟩)
    ?_ ?_ ?_).symm
  · rintro p hp
    obtain ⟨hout, hiso₁, hiso₂⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, h12, h23, h45, h56, ho1, ho2, ho3, ho4, ho5, ho6,
      hd14, hd15, hd16, hd24, hd25, hd26, hd34, hd35, hd36⟩ :=
      Finset.mem_filter.mp hout
    refine Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ?_, ?_, ?_⟩
    · intro x hx₁ hx₂
      have hmemB : ∀ {w : Fin 7},
          w ∈ insert p.2.1 (insert p.2.2.1
            (insert p.2.2.2 (Finset.univ.image θ))) →
          w ≠ p.2.1 → w ≠ p.2.2.1 → w ≠ p.2.2.2 →
          ∃ i, θ i = w := by
        intro w hw hn1 hn2 hn3
        rcases Finset.mem_insert.mp hw with h | hw'
        · exact absurd h hn1
        rcases Finset.mem_insert.mp hw' with h | hw''
        · exact absurd h hn2
        rcases Finset.mem_insert.mp hw'' with h | hw'''
        · exact absurd h hn3
        · obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hw'''
          exact ⟨t, ht⟩
      rcases Finset.mem_insert.mp hx₁ with rfl | hx₁'
      · exact hmemB hx₂ hd14 hd15 hd16
      rcases Finset.mem_insert.mp hx₁' with rfl | hx₁''
      · exact hmemB hx₂ hd24 hd25 hd26
      rcases Finset.mem_insert.mp hx₁'' with rfl | hx₁'''
      · exact hmemB hx₂ hd34 hd35 hd36
      · obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hx₁'''
        exact ⟨t, ht⟩
    · refine ⟨hrootsub, ?_⟩
      exact (isIso_congr_classS1 hwf₁
        (Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
        (extFlagS1_wellFormed hwf) h₁
        (Sym3Flag.pullbackFlag_graph_mem hG _ hrootsub)
        (extFlagS1_graph_mem ho1 ho2 ho3 h12.ne (h12.trans h23).ne
          h23.ne hG)
        (pullbackFlag_insert3_class_eq hwf ho1 ho2 ho3 h12.ne
          (h12.trans h23).ne h23.ne hG _ hrootsub _ _ _ _)).mpr hiso₁
    · refine ⟨hrootsub, ?_⟩
      exact (isIso_congr_classS1 hwf₂
        (Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
        (extFlagS1_wellFormed hwf) h₂
        (Sym3Flag.pullbackFlag_graph_mem hG _ hrootsub)
        (extFlagS1_graph_mem ho4 ho5 ho6 h45.ne (h45.trans h56).ne
          h56.ne hG)
        (pullbackFlag_insert3_class_eq hwf ho4 ho5 ho6 h45.ne
          (h45.trans h56).ne h56.ne hG _ hrootsub _ _ _ _)).mpr hiso₂
  · rintro p hp q hq heq
    obtain ⟨houtp, -, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨houtq, -, -⟩ := Finset.mem_filter.mp hq
    obtain ⟨-, h12p, h23p, h45p, h56p, ho1p, ho2p, ho3p, ho4p, ho5p,
      ho6p, -⟩ := Finset.mem_filter.mp houtp
    obtain ⟨-, h12q, h23q, h45q, h56q, ho1q, ho2q, ho3q, ho4q, ho5q,
      ho6q, -⟩ := Finset.mem_filter.mp houtq
    have hpair := congrArg Subtype.val heq
    have h1 := congrArg Prod.fst hpair
    have h2 := congrArg Prod.snd hpair
    obtain ⟨e1, e2, e3⟩ := sorted_triple_eq h12p h23p h12q h23q
      (insert3_set_eq ho1p ho2p ho3p ho1q ho2q ho3q h1)
    obtain ⟨e4, e5, e6⟩ := sorted_triple_eq h45p h56p h45q h56q
      (insert3_set_eq ho4p ho5p ho6p ho4q ho5q ho6q h2)
    exact Prod.ext (Prod.ext e1 (Prod.ext e2 e3))
      (Prod.ext e4 (Prod.ext e5 e6))
  · rintro b hb
    obtain ⟨-, hshared, ⟨hr₁, hiso₁⟩, ⟨hr₂, hiso₂⟩⟩ :=
      Finset.mem_filter.mp hb
    have hmem := Finset.mem_product.mp b.property
    have himg₁ : Finset.univ.image θ ⊆ b.val.1 := fun x hx => by
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hx
      exact hr₁ t
    have himg₂ : Finset.univ.image θ ⊆ b.val.2 := fun x hx => by
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hx
      exact hr₂ t
    obtain ⟨x₁, y₁, z₁, hxy₁, hyz₁, ho1, ho2, ho3, hW₁⟩ :=
      eq_insert3_of_card_four himg₁
        (Finset.mem_powersetCard.mp hmem.1).2
    obtain ⟨x₂, y₂, z₂, hxy₂, hyz₂, ho4, ho5, ho6, hW₂⟩ :=
      eq_insert3_of_card_four himg₂
        (Finset.mem_powersetCard.mp hmem.2).2
    have hnotB : ∀ {w : Fin 7}, w ∉ Finset.univ.image θ → w ∈ b.val.1 →
        w ∉ b.val.2 := by
      intro w hwo hw1 hw2
      obtain ⟨t, ht⟩ := hshared w hw1 hw2
      exact hwo (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩)
    have hx₁m : x₁ ∈ b.val.1 := by
      rw [hW₁]; exact Finset.mem_insert_self _ _
    have hy₁m : y₁ ∈ b.val.1 := by
      rw [hW₁]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hz₁m : z₁ ∈ b.val.1 := by
      rw [hW₁]
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hx₂m : x₂ ∈ b.val.2 := by
      rw [hW₂]; exact Finset.mem_insert_self _ _
    have hy₂m : y₂ ∈ b.val.2 := by
      rw [hW₂]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hz₂m : z₂ ∈ b.val.2 := by
      rw [hW₂]
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hd14 : x₁ ≠ x₂ := fun h => hnotB ho1 hx₁m (h ▸ hx₂m)
    have hd15 : x₁ ≠ y₂ := fun h => hnotB ho1 hx₁m (h ▸ hy₂m)
    have hd16 : x₁ ≠ z₂ := fun h => hnotB ho1 hx₁m (h ▸ hz₂m)
    have hd24 : y₁ ≠ x₂ := fun h => hnotB ho2 hy₁m (h ▸ hx₂m)
    have hd25 : y₁ ≠ y₂ := fun h => hnotB ho2 hy₁m (h ▸ hy₂m)
    have hd26 : y₁ ≠ z₂ := fun h => hnotB ho2 hy₁m (h ▸ hz₂m)
    have hd34 : z₁ ≠ x₂ := fun h => hnotB ho3 hz₁m (h ▸ hx₂m)
    have hd35 : z₁ ≠ y₂ := fun h => hnotB ho3 hz₁m (h ▸ hy₂m)
    have hd36 : z₁ ≠ z₂ := fun h => hnotB ho3 hz₁m (h ▸ hz₂m)
    have hiso₁' : F₁.IsIso (extFlagS1 G θ x₁ y₁ z₁) :=
      (isIso_congr_classS1 hwf₁
        (Sym3Flag.pullbackFlag_wellFormed hwf _ hr₁)
        (extFlagS1_wellFormed hwf) h₁
        (Sym3Flag.pullbackFlag_graph_mem hG _ hr₁)
        (extFlagS1_graph_mem ho1 ho2 ho3 hxy₁.ne
          (hxy₁.trans hyz₁).ne hyz₁.ne hG)
        ((pullbackFlag_congr_WS1 hW₁
            (hcard' := insert3_card_four ho1 ho2 ho3 hxy₁.ne
              (hxy₁.trans hyz₁).ne hyz₁.ne)
            (hroots' := hrootsub)
            (hwfP' := Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
            (hmemP' := Sym3Flag.pullbackFlag_graph_mem hG _
              hrootsub)).trans
          (pullbackFlag_insert3_class_eq hwf ho1 ho2 ho3 hxy₁.ne
            (hxy₁.trans hyz₁).ne hyz₁.ne hG
            (insert3_card_four ho1 ho2 ho3 hxy₁.ne
              (hxy₁.trans hyz₁).ne hyz₁.ne) hrootsub
            (Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
            (Sym3Flag.pullbackFlag_graph_mem hG _ hrootsub)
            (extFlagS1_wellFormed hwf)
            (extFlagS1_graph_mem ho1 ho2 ho3 hxy₁.ne
              (hxy₁.trans hyz₁).ne hyz₁.ne hG)))).mp hiso₁
    have hiso₂' : F₂.IsIso (extFlagS1 G θ x₂ y₂ z₂) :=
      (isIso_congr_classS1 hwf₂
        (Sym3Flag.pullbackFlag_wellFormed hwf _ hr₂)
        (extFlagS1_wellFormed hwf) h₂
        (Sym3Flag.pullbackFlag_graph_mem hG _ hr₂)
        (extFlagS1_graph_mem ho4 ho5 ho6 hxy₂.ne
          (hxy₂.trans hyz₂).ne hyz₂.ne hG)
        ((pullbackFlag_congr_WS1 hW₂
            (hcard' := insert3_card_four ho4 ho5 ho6 hxy₂.ne
              (hxy₂.trans hyz₂).ne hyz₂.ne)
            (hroots' := hrootsub)
            (hwfP' := Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
            (hmemP' := Sym3Flag.pullbackFlag_graph_mem hG _
              hrootsub)).trans
          (pullbackFlag_insert3_class_eq hwf ho4 ho5 ho6 hxy₂.ne
            (hxy₂.trans hyz₂).ne hyz₂.ne hG
            (insert3_card_four ho4 ho5 ho6 hxy₂.ne
              (hxy₂.trans hyz₂).ne hyz₂.ne) hrootsub
            (Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
            (Sym3Flag.pullbackFlag_graph_mem hG _ hrootsub)
            (extFlagS1_wellFormed hwf)
            (extFlagS1_graph_mem ho4 ho5 ho6 hxy₂.ne
              (hxy₂.trans hyz₂).ne hyz₂.ne hG)))).mp hiso₂
    refine ⟨((x₁, y₁, z₁), (x₂, y₂, z₂)), Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hxy₁, hyz₁, hxy₂, hyz₂, ho1, ho2, ho3, ho4, ho5, ho6,
        hd14, hd15, hd16, hd24, hd25, hd26, hd34, hd35, hd36⟩,
       hiso₁', hiso₂'⟩, ?_⟩
    exact Subtype.ext (Prod.ext hW₁.symm hW₂.symm)

/-- **The sparsity collapse at a one-rooting.** -/
lemma sum_pairCount_eq_pairSumS1 {ι : Type} [Fintype ι]
    (c : ι → ℚ) (F : ι → Sym3Flag 1 4)
    (hwfF : ∀ i, (F i).WellFormed vertexGraph)
    (hF : ∀ i, TetraFree.Mem (F i).graph.toModel)
    (hwf : (Sym3Flag.mk G θ).WellFormed vertexGraph)
    (hG : TetraFree.Mem G.toModel) :
    (∑ i, ∑ j, c i * c j
      * ((F i).flagPairCountC (F j) (Sym3Flag.mk G θ) : ℚ))
      = ∑ p ∈ outsideTriples θ,
          (∑ i, c i * (if (F i).IsIso
              (extFlagS1 G θ p.1.1 p.1.2.1 p.1.2.2) then 1 else 0))
            * (∑ j, c j * (if (F j).IsIso
                (extFlagS1 G θ p.2.1 p.2.2.1 p.2.2.2)
                then 1 else 0)) := by
  classical
  have hcount : ∀ i j : ι,
      ((F i).flagPairCountC (F j) (Sym3Flag.mk G θ) : ℚ)
      = ∑ p ∈ outsideTriples θ,
          ((if (F i).IsIso (extFlagS1 G θ p.1.1 p.1.2.1 p.1.2.2)
              then 1 else 0)
            * (if (F j).IsIso (extFlagS1 G θ p.2.1 p.2.2.1 p.2.2.2)
                then 1 else 0) : ℚ) := by
    intro i j
    rw [flagPairCountC_eq_extPairsS1 (hwfF i) (hwfF j) (hF i) (hF j)
      hwf hG, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with h1 h2 h3 h4 h5 <;> simp_all
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by
      rw [hcount i j, Finset.mul_sum],
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => Finset.sum_comm,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by ring

/-- The typed pair density at a one-rooting is the pair count over
`pairChoose 6 3 3 = 20`. -/
lemma pairDensity_toCountS1 {F₁ F₂ : Sym3Flag 1 4}
    (hwf₁ : F₁.WellFormed vertexGraph) (hwf₂ : F₂.WellFormed vertexGraph)
    (h₁ : TetraFree.Mem F₁.graph.toModel)
    (h₂ : TetraFree.Mem F₂.graph.toModel)
    (hwf : (Sym3Flag.mk G θ).WellFormed vertexGraph)
    (hG : TetraFree.Mem G.toModel) :
    subflagPairDensity (F₁.toFlag hwf₁ h₁) (F₂.toFlag hwf₂ h₂)
        ((Sym3Flag.mk G θ).toFlag hwf hG)
      = (F₁.flagPairCountC F₂ (Sym3Flag.mk G θ) : ℚ) / 20 := by
  rw [Sym3Flag.subflagPairDensity_toFlag hwf₁ hwf₂ hwf h₁ h₂ hG]
  rfl

/-- **The s1-family coefficient as a rooting sum of weight products**:
`1/7` times the rooting sum of the outside-triple weight products over
`20`. -/
theorem gammaS1_eq_rooting {ι : Type} [Fintype ι]
    (c : ι → ℚ) (F : ι → Sym3Flag 1 4)
    (hwfF : ∀ i, (F i).WellFormed vertexGraph)
    (hF : ∀ i, TetraFree.Mem (F i).graph.toModel)
    {G : Sym3Graph 7} (hG : TetraFree.Mem G.toModel) :
    (∑ X ∈ Finset.univ.filter
        (fun X : FlagWithSize TetraFree vertexGraph.toModel 7 =>
          Flag.unlabel X = G.toFlag hG),
      (∑ i, ∑ j, (c i : ℝ) * (c j : ℝ)
          * ((subflagPairDensity ((F i).toFlag (hwfF i) (hF i))
              ((F j).toFlag (hwfF j) (hF j)) X : ℚ) : ℝ))
        * (labelingFactor (Quotient.out X).unlabel (Quotient.out X) : ℝ))
      = (1 / 7 : ℝ) * ∑ θ ∈ rootingsOf vertexGraph G,
          ((((∑ p ∈ outsideTriples θ,
              (∑ i, c i * (if (F i).IsIso
                  (extFlagS1 G θ p.1.1 p.1.2.1 p.1.2.2) then 1 else 0))
                * (∑ j, c j * (if (F j).IsIso
                    (extFlagS1 G θ p.2.1 p.2.2.1 p.2.2.2)
                    then 1 else 0))) / 20 : ℚ)) : ℝ) := by
  have h := fiber_sum_eq_rooting_sum (𝕋 := TetraFree)
    (σg := vertexGraph) (by norm_num : 1 ≤ 7)
    (fun X : FlagWithSize TetraFree vertexGraph.toModel 7 =>
      ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ)
        * ((subflagPairDensity ((F i).toFlag (hwfF i) (hF i))
            ((F j).toFlag (hwfF j) (hF j)) X : ℚ) : ℝ)) hG
  rw [show Nat.descFactorial 7 1 = 7 from rfl] at h
  rw [h]
  congr 1
  have hper : ∀ θ ∈ (rootingsOf vertexGraph G).attach,
      (∑ i, ∑ j, (c i : ℝ) * (c j : ℝ)
        * ((subflagPairDensity ((F i).toFlag (hwfF i) (hF i))
            ((F j).toFlag (hwfF j) (hF j))
            ((Sym3Flag.mk G θ.val).toFlag
              (mem_rootingsOf.mp θ.property) hG) : ℚ) : ℝ))
      = ((((∑ p ∈ outsideTriples θ.val,
          (∑ i, c i * (if (F i).IsIso
              (extFlagS1 G θ.val p.1.1 p.1.2.1 p.1.2.2) then 1 else 0))
            * (∑ j, c j * (if (F j).IsIso
                (extFlagS1 G θ.val p.2.1 p.2.2.1 p.2.2.2)
                then 1 else 0))) / 20 : ℚ)) : ℝ) := by
    intro θ _
    have hwfθ : (Sym3Flag.mk G θ.val).WellFormed vertexGraph :=
      mem_rootingsOf.mp θ.property
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by
        rw [pairDensity_toCountS1 (hwf₁ := hwfF i) (hwf₂ := hwfF j)
          (h₁ := hF i) (h₂ := hF j) (hwf := hwfθ) (hG := hG)]]
    rw [show (∑ i, ∑ j, (c i : ℝ) * (c j : ℝ)
        * ((((F i).flagPairCountC (F j) (Sym3Flag.mk G θ.val) : ℚ)
            / 20 : ℚ) : ℝ))
        = (((∑ i, ∑ j, c i * c j
            * ((F i).flagPairCountC (F j) (Sym3Flag.mk G θ.val) : ℚ))
              / 20 : ℚ) : ℝ) from by
      push_cast
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring]
    rw [sum_pairCount_eq_pairSumS1 c F hwfF hF hwfθ hG]
  rw [Finset.sum_congr rfl hper]
  exact Finset.sum_attach (rootingsOf vertexGraph G) fun θ =>
    ((((∑ p ∈ outsideTriples θ,
        (∑ i, c i * (if (F i).IsIso
            (extFlagS1 G θ p.1.1 p.1.2.1 p.1.2.2) then 1 else 0))
          * (∑ j, c j * (if (F j).IsIso
              (extFlagS1 G θ p.2.1 p.2.2.1 p.2.2.2)
              then 1 else 0))) / 20 : ℚ)) : ℝ)

end ExtS1

end FlagAlgebras.Core.Tetrahedron
