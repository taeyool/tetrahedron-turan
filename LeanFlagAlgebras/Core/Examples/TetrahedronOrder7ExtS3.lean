import LeanFlagAlgebras.Core.Compute.Sym3Fiber
import LeanFlagAlgebras.Core.Examples.TetrahedronMask
import Mathlib.Tactic.FinCases

/-! # The extension flags of a three-rooting of a seven-vertex host

The order-7 three-root families live at the two three-vertex types — the
empty triple and the hyperedge. A witness subset carries the three roots
and two of the four outside vertices, so this is the 24-block shape one
arity up: extension flags take an ordered pair of outside vertices, a
root-preserving isomorphism can swap them, and the isomorphism test
stays decidable.

Everything is stated for arbitrary five-vertex patterns over the type,
so the same lemmas serve the nonedge-root and edge-root families. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

open Classical

/-- The three-vertex type of an s3 family: the root-induced mask
decoded. -/
def s3Type (rm : ℕ) : Sym3Graph 3 := graphOfMask 3 rm

lemma s3Type_mem_0 : TetraFree.Mem (s3Type 0).toModel :=
  k4FreeMask_iff_mem.mp (by decide)
lemma s3Type_mem_1 : TetraFree.Mem (s3Type 1).toModel :=
  k4FreeMask_iff_mem.mp (by decide)

instance : TetraFree.IsType (s3Type 0).toModel := ⟨s3Type_mem_0⟩
instance : TetraFree.IsType (s3Type 1).toModel := ⟨s3Type_mem_1⟩

/-- The extension flag of a three-rooting at two outside vertices. -/
def extFlagS3 (G : Sym3Graph 7) (θ : Fin 3 → Fin 7) (v w : Fin 7) :
    Sym3Flag 3 5 :=
  ⟨G.pullback ![θ 0, θ 1, θ 2, v, w], ![0, 1, 2]⟩

section ExtS3

variable {G : Sym3Graph 7} {θ : Fin 3 → Fin 7} {v w : Fin 7}

lemma extTupleS3_injective (hθ : Function.Injective θ)
    (hv : v ∉ Finset.univ.image θ) (hw : w ∉ Finset.univ.image θ)
    (hvw : v ≠ w) :
    Function.Injective ![θ 0, θ 1, θ 2, v, w] := by
  have hnev : ∀ i : Fin 3, θ i ≠ v := fun i h =>
    hv (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
  have hnew : ∀ i : Fin 3, θ i ≠ w := fun i h =>
    hw (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    first
      | rfl
      | exact absurd (hθ hab) (by decide)
      | exact absurd hab (hnev _)
      | exact absurd hab.symm (hnev _)
      | exact absurd hab (hnew _)
      | exact absurd hab.symm (hnew _)
      | exact absurd hab hvw
      | exact absurd hab.symm hvw

lemma extFlagS3_wellFormed {rm : ℕ}
    (hwf : (Sym3Flag.mk G θ).WellFormed (s3Type rm)) :
    (extFlagS3 G θ v w).WellFormed (s3Type rm) := by
  constructor
  · have h : Function.Injective (![0, 1, 2] : Fin 3 → Fin 5) := by decide
    exact fun a b hab => h hab
  · show (G.pullback ![θ 0, θ 1, θ 2, v, w]).pullback ![0, 1, 2]
      = s3Type rm
    rw [Sym3Graph.pullback_pullback]
    have hcomp : (![θ 0, θ 1, θ 2, v, w] ∘ ![(0 : Fin 5), 1, 2]) = θ := by
      funext t
      fin_cases t <;> rfl
    rw [hcomp]
    exact hwf.2

lemma extFlagS3_graph_mem (hθ : Function.Injective θ)
    (hv : v ∉ Finset.univ.image θ) (hw : w ∉ Finset.univ.image θ)
    (hvw : v ≠ w) (hG : TetraFree.Mem G.toModel) :
    TetraFree.Mem (extFlagS3 G θ v w).graph.toModel := by
  show TetraFree.Mem (G.pullback ![θ 0, θ 1, θ 2, v, w]).toModel
  rw [Sym3Graph.pullback_toModel _ (extTupleS3_injective hθ hv hw hvw)]
  exact TetraFree.mem_comap _ hG

/-- Isomorphism tests against equal classes agree. -/
lemma isIso_congr_classS3 {rm : ℕ}
    [TetraFree.IsType (s3Type rm).toModel] {F A B : Sym3Flag 3 5}
    (hwfF : F.WellFormed (s3Type rm)) (hwfA : A.WellFormed (s3Type rm))
    (hwfB : B.WellFormed (s3Type rm)) (hF : TetraFree.Mem F.graph.toModel)
    (hA : TetraFree.Mem A.graph.toModel)
    (hB : TetraFree.Mem B.graph.toModel)
    (hAB : A.toFlag hwfA hA = B.toFlag hwfB hB) :
    F.IsIso A ↔ F.IsIso B := by
  rw [← Sym3Flag.toFlag_eq_toFlag_iff hwfF hwfA hF hA,
    ← Sym3Flag.toFlag_eq_toFlag_iff hwfF hwfB hF hB, hAB]

lemma insert2_card_five (hθ : Function.Injective θ)
    (hv : v ∉ Finset.univ.image θ) (hw : w ∉ Finset.univ.image θ)
    (hvw : v ≠ w) :
    (insert v (insert w (Finset.univ.image θ))).card = 5 := by
  rw [Finset.card_insert_of_notMem (fun h => by
      rcases Finset.mem_insert.mp h with h' | h'
      · exact hvw h'
      · exact hv h'),
    Finset.card_insert_of_notMem hw,
    Finset.card_image_of_injective _ hθ, Finset.card_univ,
    Fintype.card_fin]

/-- A five-element root-containing subset is the roots plus a sorted
pair of outside vertices. -/
lemma eq_insert2_of_card_five (hθ : Function.Injective θ)
    {W : Finset (Fin 7)} (hsub : Finset.univ.image θ ⊆ W)
    (hcard : W.card = 5) :
    ∃ a b : Fin 7, a < b ∧ a ∉ Finset.univ.image θ
      ∧ b ∉ Finset.univ.image θ
      ∧ W = insert a (insert b (Finset.univ.image θ)) := by
  have himg : (Finset.univ.image θ).card = 3 := by
    rw [Finset.card_image_of_injective _ hθ, Finset.card_univ,
      Fintype.card_fin]
  have hsd : (W \ Finset.univ.image θ).card = 2 := by
    have h := Finset.card_sdiff (s := Finset.univ.image θ) (t := W)
    rw [Finset.inter_eq_left.mpr hsub] at h
    omega
  obtain ⟨x, y, hxy, hS⟩ := Finset.card_eq_two.mp hsd
  have hxm : x ∈ W \ Finset.univ.image θ := by
    rw [hS]; exact Finset.mem_insert_self _ _
  have hym : y ∈ W \ Finset.univ.image θ := by
    rw [hS]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hWeq : ∀ {a b : Fin 7}, ({a, b} : Finset (Fin 7)) = {x, y} →
      W = insert a (insert b (Finset.univ.image θ)) := by
    intro a b hab
    ext z
    constructor
    · intro hz
      by_cases hzi : z ∈ Finset.univ.image θ
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hzi)
      · have hzd : z ∈ W \ Finset.univ.image θ :=
          Finset.mem_sdiff.mpr ⟨hz, hzi⟩
        rw [hS, ← hab] at hzd
        rcases Finset.mem_insert.mp hzd with rfl | hzd'
        · exact Finset.mem_insert_self _ _
        · rw [Finset.mem_singleton] at hzd'
          subst hzd'
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · intro hz
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · have hzx : z ∈ ({x, y} : Finset (Fin 7)) := by
          rw [← hab]; exact Finset.mem_insert_self _ _
        rcases Finset.mem_insert.mp hzx with rfl | h'
        · exact (Finset.mem_sdiff.mp hxm).1
        · rw [Finset.mem_singleton] at h'
          subst h'
          exact (Finset.mem_sdiff.mp hym).1
      rcases Finset.mem_insert.mp hz' with rfl | hz''
      · have hzx : z ∈ ({x, y} : Finset (Fin 7)) := by
          rw [← hab]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        rcases Finset.mem_insert.mp hzx with rfl | h'
        · exact (Finset.mem_sdiff.mp hxm).1
        · rw [Finset.mem_singleton] at h'
          subst h'
          exact (Finset.mem_sdiff.mp hym).1
      · exact hsub hz''
  rcases lt_or_gt_of_ne hxy with h | h
  · exact ⟨x, y, h, (Finset.mem_sdiff.mp hxm).2,
      (Finset.mem_sdiff.mp hym).2, hWeq rfl⟩
  · exact ⟨y, x, h, (Finset.mem_sdiff.mp hym).2,
      (Finset.mem_sdiff.mp hxm).2, hWeq (Finset.pair_comm x y ▸ rfl)⟩

/-- The extension flag is the restriction of the rooted host to the
roots plus the two outside vertices, as labeled flags. -/
noncomputable def extFlagIsoS3 {rm : ℕ}
    [TetraFree.IsType (s3Type rm).toModel]
    (hwf : (Sym3Flag.mk G θ).WellFormed (s3Type rm))
    (hv : v ∉ Finset.univ.image θ) (hw : w ∉ Finset.univ.image θ)
    (hvw : v ≠ w) (hG : TetraFree.Mem G.toModel)
    (hroot' : ∀ t, ((Sym3Flag.mk G θ).toLabeledFlag
      hwf hG).rootEmbed.toEmbedding t
        ∈ insert v (insert w (Finset.univ.image θ)))
    (hwfE : (extFlagS3 G θ v w).WellFormed (s3Type rm))
    (hmemE : TetraFree.Mem (extFlagS3 G θ v w).graph.toModel) :
    (extFlagS3 G θ v w).toLabeledFlag hwfE hmemE
      ≃ᶠ ((Sym3Flag.mk G θ).toLabeledFlag hwf hG).restrict
          (insert v (insert w (Finset.univ.image θ))) hroot' := by
  have hmem : ∀ i : Fin 5,
      ![θ 0, θ 1, θ 2, v, w] i
        ∈ insert v (insert w (Finset.univ.image θ)) := by
    intro i
    fin_cases i
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩))
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩))
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩))
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hcard : (insert v (insert w (Finset.univ.image θ))).card = 5 :=
    insert2_card_five hwf.1 hv hw hvw
  refine ⟨⟨Equiv.ofBijective
    (fun i => ⟨![θ 0, θ 1, θ 2, v, w] i, hmem i⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun a b hab => extTupleS3_injective hwf.1 hv hw hvw
        (congrArg Subtype.val hab),
       by rw [Fintype.card_fin, Fintype.card_coe, hcard]⟩),
    fun r f => ?_⟩, fun t => ?_⟩
  · show (G.toModel.comap (Function.Embedding.subtype _)).interp r _
      ↔ (G.pullback ![θ 0, θ 1, θ 2, v, w]).toModel.interp r f
    rw [Sym3Graph.pullback_toModel _
      (extTupleS3_injective hwf.1 hv hw hvw)]
    exact Iff.rfl
  · refine Subtype.ext ?_
    fin_cases t <;> rfl

/-- The induced typed sub-flag on the roots plus two outside vertices is
the canonical extension flag, as classes. -/
lemma pullbackFlag_insert2_class_eqS3 {rm : ℕ}
    [TetraFree.IsType (s3Type rm).toModel]
    (hwf : (Sym3Flag.mk G θ).WellFormed (s3Type rm))
    (hv : v ∉ Finset.univ.image θ) (hw : w ∉ Finset.univ.image θ)
    (hvw : v ≠ w) (hG : TetraFree.Mem G.toModel)
    (hcard : (insert v (insert w (Finset.univ.image θ))).card = 5)
    (hroots : ∀ i, (Sym3Flag.mk G θ).roots i
      ∈ insert v (insert w (Finset.univ.image θ)))
    (hwfP : ((Sym3Flag.mk G θ).pullbackFlag _ hcard hroots).WellFormed
      (s3Type rm))
    (hmemP : TetraFree.Mem ((Sym3Flag.mk G θ).pullbackFlag _ hcard
      hroots).graph.toModel)
    (hwfE : (extFlagS3 G θ v w).WellFormed (s3Type rm))
    (hmemE : TetraFree.Mem (extFlagS3 G θ v w).graph.toModel) :
    ((Sym3Flag.mk G θ).pullbackFlag _ hcard hroots).toFlag hwfP hmemP
      = (extFlagS3 G θ v w).toFlag hwfE hmemE := by
  refine Quotient.sound ⟨?_⟩
  exact (pullbackFlagIso hwf hG hcard hroots (fun t => hroots t)
      hwfP hmemP).trans
    (extFlagIsoS3 hwf hv hw hvw hG (fun t => hroots t) hwfE hmemE).symm

/-- Induced sub-flags on equal subsets have equal classes. -/
lemma pullbackFlag_congr_WS3 {rm : ℕ}
    [TetraFree.IsType (s3Type rm).toModel]
    {Gσ : Sym3Flag 3 7} {W W' : Finset (Fin 7)}
    (hWW : W = W')
    {hcard : W.card = 5} {hroots : ∀ t, Gσ.roots t ∈ W}
    {hcard' : W'.card = 5} {hroots' : ∀ t, Gσ.roots t ∈ W'}
    {hwfP : (Gσ.pullbackFlag W hcard hroots).WellFormed (s3Type rm)}
    {hmemP : TetraFree.Mem (Gσ.pullbackFlag W hcard
      hroots).graph.toModel}
    {hwfP' : (Gσ.pullbackFlag W' hcard' hroots').WellFormed (s3Type rm)}
    {hmemP' : TetraFree.Mem (Gσ.pullbackFlag W' hcard'
      hroots').graph.toModel} :
    (Gσ.pullbackFlag W hcard hroots).toFlag hwfP hmemP
      = (Gσ.pullbackFlag W' hcard' hroots').toFlag hwfP' hmemP' := by
  subst hWW
  rfl

/-- Two strictly sorted pairs with the same vertex set are equal. -/
lemma sorted_pair_eq7 {a b c d : Fin 7} (hab : a < b) (hcd : c < d)
    (h : ({a, b} : Finset (Fin 7)) = {c, d}) : a = c ∧ b = d := by
  have hac : a ∈ ({c, d} : Finset (Fin 7)) := by
    rw [← h]; exact Finset.mem_insert_self _ _
  have hbc : b ∈ ({c, d} : Finset (Fin 7)) := by
    rw [← h]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rcases Finset.mem_insert.mp hac with rfl | ha'
  · rcases Finset.mem_insert.mp hbc with h' | h'
    · exact absurd h'.symm hab.ne
    · rw [Finset.mem_singleton] at h'
      exact ⟨rfl, h'⟩
  · rw [Finset.mem_singleton] at ha'
    subst ha'
    rcases Finset.mem_insert.mp hbc with h' | h'
    · subst h'
      exact absurd (hab.trans hcd) (lt_irrefl _)
    · rw [Finset.mem_singleton] at h'
      subst h'
      exact absurd hab (lt_irrefl _)

/-- The sorted disjoint outside-vertex pair pairs of a three-rooting. -/
def outsidePairsS3 (θ : Fin 3 → Fin 7) :
    Finset ((Fin 7 × Fin 7) × (Fin 7 × Fin 7)) :=
  Finset.univ.filter fun p =>
    p.1.1 < p.1.2 ∧ p.2.1 < p.2.2
      ∧ p.1.1 ∉ Finset.univ.image θ ∧ p.1.2 ∉ Finset.univ.image θ
      ∧ p.2.1 ∉ Finset.univ.image θ ∧ p.2.2 ∉ Finset.univ.image θ
      ∧ p.1.1 ≠ p.2.1 ∧ p.1.1 ≠ p.2.2 ∧ p.1.2 ≠ p.2.1 ∧ p.1.2 ≠ p.2.2

/-- **The typed pair count at a three-rooting** is the count of sorted
disjoint outside-pair pairs whose extension flags realize the two
patterns. -/
lemma flagPairCountC_eq_extPairsS3 {rm : ℕ}
    [TetraFree.IsType (s3Type rm).toModel]
    {F₁ F₂ : Sym3Flag 3 5}
    (hwf₁ : F₁.WellFormed (s3Type rm)) (hwf₂ : F₂.WellFormed (s3Type rm))
    (h₁ : TetraFree.Mem F₁.graph.toModel)
    (h₂ : TetraFree.Mem F₂.graph.toModel)
    (hwf : (Sym3Flag.mk G θ).WellFormed (s3Type rm))
    (hG : TetraFree.Mem G.toModel) :
    F₁.flagPairCountC F₂ (Sym3Flag.mk G θ)
      = ((outsidePairsS3 θ).filter (fun p =>
          F₁.IsIso (extFlagS3 G θ p.1.1 p.1.2)
            ∧ F₂.IsIso (extFlagS3 G θ p.2.1 p.2.2))).card := by
  classical
  rw [Sym3Flag.flagPairCountC]
  have hins : ∀ {a b : Fin 7}, a ∉ Finset.univ.image θ →
      b ∉ Finset.univ.image θ → a ≠ b →
      insert a (insert b (Finset.univ.image θ))
        ∈ (Finset.univ.powersetCard 5 : Finset (Finset (Fin 7))) :=
    fun {a b} ha hb hab => Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, insert2_card_five hwf.1 ha hb hab⟩
  have hrootsub : ∀ {a b : Fin 7},
      ∀ t, (Sym3Flag.mk G θ).roots t
        ∈ insert a (insert b (Finset.univ.image θ)) :=
    fun {a b} t => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩))
  refine (Finset.card_bij
    (fun p hp => ⟨(insert p.1.1 (insert p.1.2 (Finset.univ.image θ)),
        insert p.2.1 (insert p.2.2 (Finset.univ.image θ))),
      Finset.mem_product.mpr
        ⟨hins ((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).2.2.1
          ((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).2.2.2.1
          ((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).1.ne,
         hins ((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).2.2.2.2.1
          ((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).2.2.2.2.2.1
          ((Finset.mem_filter.mp
            ((Finset.mem_filter.mp hp).1)).2).2.1.ne⟩⟩)
    ?_ ?_ ?_).symm
  · rintro p hp
    obtain ⟨hout, hiso₁, hiso₂⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, h12, h34, ho1, ho2, ho3, ho4, hd13, hd14, hd23, hd24⟩ :=
      Finset.mem_filter.mp hout
    refine Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ?_, ?_, ?_⟩
    · intro x hx₁ hx₂
      rcases Finset.mem_insert.mp hx₁ with rfl | hx₁'
      · rcases Finset.mem_insert.mp hx₂ with heq | hx₂'
        · exact absurd heq hd13
        rcases Finset.mem_insert.mp hx₂' with heq | hx₂''
        · exact absurd heq hd14
        · exact absurd hx₂'' ho1
      rcases Finset.mem_insert.mp hx₁' with rfl | hx₁''
      · rcases Finset.mem_insert.mp hx₂ with heq | hx₂'
        · exact absurd heq hd23
        rcases Finset.mem_insert.mp hx₂' with heq | hx₂''
        · exact absurd heq hd24
        · exact absurd hx₂'' ho2
      · obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hx₁''
        exact ⟨t, ht⟩
    · refine ⟨hrootsub, ?_⟩
      exact (isIso_congr_classS3 hwf₁
        (Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
        (extFlagS3_wellFormed hwf) h₁
        (Sym3Flag.pullbackFlag_graph_mem hG _ hrootsub)
        (extFlagS3_graph_mem hwf.1 ho1 ho2 h12.ne hG)
        (pullbackFlag_insert2_class_eqS3 hwf ho1 ho2 h12.ne hG _
          hrootsub _ _ _ _)).mpr hiso₁
    · refine ⟨hrootsub, ?_⟩
      exact (isIso_congr_classS3 hwf₂
        (Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
        (extFlagS3_wellFormed hwf) h₂
        (Sym3Flag.pullbackFlag_graph_mem hG _ hrootsub)
        (extFlagS3_graph_mem hwf.1 ho3 ho4 h34.ne hG)
        (pullbackFlag_insert2_class_eqS3 hwf ho3 ho4 h34.ne hG _
          hrootsub _ _ _ _)).mpr hiso₂
  · rintro p hp q hq heq
    obtain ⟨houtp, -, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨houtq, -, -⟩ := Finset.mem_filter.mp hq
    obtain ⟨-, h12p, h34p, ho1p, ho2p, ho3p, ho4p, -⟩ :=
      Finset.mem_filter.mp houtp
    obtain ⟨-, h12q, h34q, ho1q, ho2q, ho3q, ho4q, -⟩ :=
      Finset.mem_filter.mp houtq
    have hpair := congrArg Subtype.val heq
    have h1 : insert p.1.1 (insert p.1.2 (Finset.univ.image θ))
        = insert q.1.1 (insert q.1.2 (Finset.univ.image θ)) :=
      congrArg Prod.fst hpair
    have h2 : insert p.2.1 (insert p.2.2 (Finset.univ.image θ))
        = insert q.2.1 (insert q.2.2 (Finset.univ.image θ)) :=
      congrArg Prod.snd hpair
    have hset : ∀ {a b c d : Fin 7},
        a ∉ Finset.univ.image θ → b ∉ Finset.univ.image θ →
        c ∉ Finset.univ.image θ → d ∉ Finset.univ.image θ →
        insert a (insert b (Finset.univ.image θ))
          = insert c (insert d (Finset.univ.image θ)) →
        ({a, b} : Finset (Fin 7)) = {c, d} := by
      intro a b c d ha hb hc hd h
      ext z
      constructor
      · intro hz
        have hzm : z ∈ insert c (insert d (Finset.univ.image θ)) := by
          rw [← h]
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact Finset.mem_insert_self _ _
          · rw [Finset.mem_singleton] at hz'
            subst hz'
            exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        have hzo : z ∉ Finset.univ.image θ := by
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact ha
          · rw [Finset.mem_singleton] at hz'
            subst hz'
            exact hb
        rcases Finset.mem_insert.mp hzm with rfl | hzm'
        · exact Finset.mem_insert_self _ _
        rcases Finset.mem_insert.mp hzm' with rfl | hzm''
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        · exact absurd hzm'' hzo
      · intro hz
        have hzm : z ∈ insert a (insert b (Finset.univ.image θ)) := by
          rw [h]
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact Finset.mem_insert_self _ _
          · rw [Finset.mem_singleton] at hz'
            subst hz'
            exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        have hzo : z ∉ Finset.univ.image θ := by
          rcases Finset.mem_insert.mp hz with rfl | hz'
          · exact hc
          · rw [Finset.mem_singleton] at hz'
            subst hz'
            exact hd
        rcases Finset.mem_insert.mp hzm with rfl | hzm'
        · exact Finset.mem_insert_self _ _
        rcases Finset.mem_insert.mp hzm' with rfl | hzm''
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        · exact absurd hzm'' hzo
    obtain ⟨e1, e2⟩ := sorted_pair_eq7 h12p h12q
      (hset ho1p ho2p ho1q ho2q h1)
    obtain ⟨e3, e4⟩ := sorted_pair_eq7 h34p h34q
      (hset ho3p ho4p ho3q ho4q h2)
    exact Prod.ext (Prod.ext e1 e2) (Prod.ext e3 e4)
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
    obtain ⟨a₁, b₁, hab₁, ho1, ho2, hW₁⟩ := eq_insert2_of_card_five hwf.1
      himg₁ (Finset.mem_powersetCard.mp hmem.1).2
    obtain ⟨a₂, b₂, hab₂, ho3, ho4, hW₂⟩ := eq_insert2_of_card_five hwf.1
      himg₂ (Finset.mem_powersetCard.mp hmem.2).2
    have hnotB : ∀ {z : Fin 7}, z ∉ Finset.univ.image θ → z ∈ b.val.1 →
        z ∉ b.val.2 := by
      intro z hzo hz1 hz2
      obtain ⟨t, ht⟩ := hshared z hz1 hz2
      exact hzo (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩)
    have ha₁m : a₁ ∈ b.val.1 := by
      rw [hW₁]; exact Finset.mem_insert_self _ _
    have hb₁m : b₁ ∈ b.val.1 := by
      rw [hW₁]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have ha₂m : a₂ ∈ b.val.2 := by
      rw [hW₂]; exact Finset.mem_insert_self _ _
    have hb₂m : b₂ ∈ b.val.2 := by
      rw [hW₂]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hd13 : a₁ ≠ a₂ := fun h => hnotB ho1 ha₁m (h ▸ ha₂m)
    have hd14 : a₁ ≠ b₂ := fun h => hnotB ho1 ha₁m (h ▸ hb₂m)
    have hd23 : b₁ ≠ a₂ := fun h => hnotB ho2 hb₁m (h ▸ ha₂m)
    have hd24 : b₁ ≠ b₂ := fun h => hnotB ho2 hb₁m (h ▸ hb₂m)
    have hiso₁' : F₁.IsIso (extFlagS3 G θ a₁ b₁) :=
      (isIso_congr_classS3 hwf₁
        (Sym3Flag.pullbackFlag_wellFormed hwf _ hr₁)
        (extFlagS3_wellFormed hwf) h₁
        (Sym3Flag.pullbackFlag_graph_mem hG _ hr₁)
        (extFlagS3_graph_mem hwf.1 ho1 ho2 hab₁.ne hG)
        ((pullbackFlag_congr_WS3 hW₁
            (hcard' := insert2_card_five hwf.1 ho1 ho2 hab₁.ne)
            (hroots' := hrootsub)
            (hwfP' := Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
            (hmemP' := Sym3Flag.pullbackFlag_graph_mem hG _
              hrootsub)).trans
          (pullbackFlag_insert2_class_eqS3 hwf ho1 ho2 hab₁.ne hG
            (insert2_card_five hwf.1 ho1 ho2 hab₁.ne) hrootsub
            (Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
            (Sym3Flag.pullbackFlag_graph_mem hG _ hrootsub)
            (extFlagS3_wellFormed hwf)
            (extFlagS3_graph_mem hwf.1 ho1 ho2 hab₁.ne hG)))).mp hiso₁
    have hiso₂' : F₂.IsIso (extFlagS3 G θ a₂ b₂) :=
      (isIso_congr_classS3 hwf₂
        (Sym3Flag.pullbackFlag_wellFormed hwf _ hr₂)
        (extFlagS3_wellFormed hwf) h₂
        (Sym3Flag.pullbackFlag_graph_mem hG _ hr₂)
        (extFlagS3_graph_mem hwf.1 ho3 ho4 hab₂.ne hG)
        ((pullbackFlag_congr_WS3 hW₂
            (hcard' := insert2_card_five hwf.1 ho3 ho4 hab₂.ne)
            (hroots' := hrootsub)
            (hwfP' := Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
            (hmemP' := Sym3Flag.pullbackFlag_graph_mem hG _
              hrootsub)).trans
          (pullbackFlag_insert2_class_eqS3 hwf ho3 ho4 hab₂.ne hG
            (insert2_card_five hwf.1 ho3 ho4 hab₂.ne) hrootsub
            (Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
            (Sym3Flag.pullbackFlag_graph_mem hG _ hrootsub)
            (extFlagS3_wellFormed hwf)
            (extFlagS3_graph_mem hwf.1 ho3 ho4 hab₂.ne hG)))).mp hiso₂
    refine ⟨((a₁, b₁), (a₂, b₂)), Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hab₁, hab₂, ho1, ho2, ho3, ho4, hd13, hd14, hd23, hd24⟩,
       hiso₁', hiso₂'⟩, ?_⟩
    exact Subtype.ext (Prod.ext hW₁.symm hW₂.symm)

/-- **The sparsity collapse at a three-rooting.** -/
lemma sum_pairCount_eq_pairSumS3 {rm : ℕ}
    [TetraFree.IsType (s3Type rm).toModel]
    {ι : Type} [Fintype ι]
    (c : ι → ℚ) (F : ι → Sym3Flag 3 5)
    (hwfF : ∀ i, (F i).WellFormed (s3Type rm))
    (hF : ∀ i, TetraFree.Mem (F i).graph.toModel)
    (hwf : (Sym3Flag.mk G θ).WellFormed (s3Type rm))
    (hG : TetraFree.Mem G.toModel) :
    (∑ i, ∑ j, c i * c j
      * ((F i).flagPairCountC (F j) (Sym3Flag.mk G θ) : ℚ))
      = ∑ p ∈ outsidePairsS3 θ,
          (∑ i, c i * (if (F i).IsIso (extFlagS3 G θ p.1.1 p.1.2)
              then 1 else 0))
            * (∑ j, c j * (if (F j).IsIso (extFlagS3 G θ p.2.1 p.2.2)
                then 1 else 0)) := by
  classical
  have hcount : ∀ i j : ι,
      ((F i).flagPairCountC (F j) (Sym3Flag.mk G θ) : ℚ)
      = ∑ p ∈ outsidePairsS3 θ,
          ((if (F i).IsIso (extFlagS3 G θ p.1.1 p.1.2) then 1 else 0)
            * (if (F j).IsIso (extFlagS3 G θ p.2.1 p.2.2)
                then 1 else 0) : ℚ) := by
    intro i j
    rw [flagPairCountC_eq_extPairsS3 (hwfF i) (hwfF j) (hF i) (hF j)
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

/-- The typed pair density at a three-rooting is the pair count over
`pairChoose 4 2 2 = 6`. -/
lemma pairDensity_toCountS3 {rm : ℕ}
    [TetraFree.IsType (s3Type rm).toModel]
    {F₁ F₂ : Sym3Flag 3 5}
    (hwf₁ : F₁.WellFormed (s3Type rm)) (hwf₂ : F₂.WellFormed (s3Type rm))
    (h₁ : TetraFree.Mem F₁.graph.toModel)
    (h₂ : TetraFree.Mem F₂.graph.toModel)
    (hwf : (Sym3Flag.mk G θ).WellFormed (s3Type rm))
    (hG : TetraFree.Mem G.toModel) :
    subflagPairDensity (F₁.toFlag hwf₁ h₁) (F₂.toFlag hwf₂ h₂)
        ((Sym3Flag.mk G θ).toFlag hwf hG)
      = (F₁.flagPairCountC F₂ (Sym3Flag.mk G θ) : ℚ) / 6 := by
  rw [Sym3Flag.subflagPairDensity_toFlag hwf₁ hwf₂ hwf h₁ h₂ hG]
  rfl

/-- **The s3-family coefficient as a rooting sum of weight products**:
`1/210` times the rooting sum of the outside-pair weight products over
`6`. -/
theorem gammaS3_eq_rooting {rm : ℕ}
    [TetraFree.IsType (s3Type rm).toModel]
    {ι : Type} [Fintype ι]
    (c : ι → ℚ) (F : ι → Sym3Flag 3 5)
    (hwfF : ∀ i, (F i).WellFormed (s3Type rm))
    (hF : ∀ i, TetraFree.Mem (F i).graph.toModel)
    {G : Sym3Graph 7} (hG : TetraFree.Mem G.toModel) :
    (∑ X ∈ Finset.univ.filter
        (fun X : FlagWithSize TetraFree (s3Type rm).toModel 7 =>
          Flag.unlabel X = G.toFlag hG),
      (∑ i, ∑ j, (c i : ℝ) * (c j : ℝ)
          * ((subflagPairDensity ((F i).toFlag (hwfF i) (hF i))
              ((F j).toFlag (hwfF j) (hF j)) X : ℚ) : ℝ))
        * (labelingFactor (Quotient.out X).unlabel (Quotient.out X) : ℝ))
      = (1 / 210 : ℝ) * ∑ θ ∈ rootingsOf (s3Type rm) G,
          ((((∑ p ∈ outsidePairsS3 θ,
              (∑ i, c i * (if (F i).IsIso (extFlagS3 G θ p.1.1 p.1.2)
                  then 1 else 0))
                * (∑ j, c j * (if (F j).IsIso (extFlagS3 G θ p.2.1 p.2.2)
                    then 1 else 0))) / 6 : ℚ)) : ℝ) := by
  have h := fiber_sum_eq_rooting_sum (𝕋 := TetraFree)
    (σg := s3Type rm) (by norm_num : 3 ≤ 7)
    (fun X : FlagWithSize TetraFree (s3Type rm).toModel 7 =>
      ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ)
        * ((subflagPairDensity ((F i).toFlag (hwfF i) (hF i))
            ((F j).toFlag (hwfF j) (hF j)) X : ℚ) : ℝ)) hG
  rw [show Nat.descFactorial 7 3 = 210 from rfl] at h
  rw [h]
  congr 1
  have hper : ∀ θ ∈ (rootingsOf (s3Type rm) G).attach,
      (∑ i, ∑ j, (c i : ℝ) * (c j : ℝ)
        * ((subflagPairDensity ((F i).toFlag (hwfF i) (hF i))
            ((F j).toFlag (hwfF j) (hF j))
            ((Sym3Flag.mk G θ.val).toFlag
              (mem_rootingsOf.mp θ.property) hG) : ℚ) : ℝ))
      = ((((∑ p ∈ outsidePairsS3 θ.val,
          (∑ i, c i * (if (F i).IsIso (extFlagS3 G θ.val p.1.1 p.1.2)
              then 1 else 0))
            * (∑ j, c j * (if (F j).IsIso (extFlagS3 G θ.val p.2.1 p.2.2)
                then 1 else 0))) / 6 : ℚ)) : ℝ) := by
    intro θ _
    have hwfθ : (Sym3Flag.mk G θ.val).WellFormed (s3Type rm) :=
      mem_rootingsOf.mp θ.property
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by
        rw [pairDensity_toCountS3 (hwf₁ := hwfF i) (hwf₂ := hwfF j)
          (h₁ := hF i) (h₂ := hF j) (hwf := hwfθ) (hG := hG)]]
    rw [show (∑ i, ∑ j, (c i : ℝ) * (c j : ℝ)
        * ((((F i).flagPairCountC (F j) (Sym3Flag.mk G θ.val) : ℚ)
            / 6 : ℚ) : ℝ))
        = (((∑ i, ∑ j, c i * c j
            * ((F i).flagPairCountC (F j) (Sym3Flag.mk G θ.val) : ℚ))
              / 6 : ℚ) : ℝ) from by
      push_cast
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring]
    rw [sum_pairCount_eq_pairSumS3 c F hwfF hF hwfθ hG]
  rw [Finset.sum_congr rfl hper]
  exact Finset.sum_attach (rootingsOf (s3Type rm) G) fun θ =>
    ((((∑ p ∈ outsidePairsS3 θ,
        (∑ i, c i * (if (F i).IsIso (extFlagS3 G θ p.1.1 p.1.2)
            then 1 else 0))
          * (∑ j, c j * (if (F j).IsIso (extFlagS3 G θ p.2.1 p.2.2)
              then 1 else 0))) / 6 : ℚ)) : ℝ)

end ExtS3

end FlagAlgebras.Core.Tetrahedron
