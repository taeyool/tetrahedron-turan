import LeanFlagAlgebras.Core.Compute.MaskInj
import LeanFlagAlgebras.Core.Compute.Sym3Fiber
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7BlockFlags
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Induce5
import Mathlib.Tactic.FinCases

/-! # The canonical extension flag of a four-rooting

The typed five-vertex flag induced at a four-rooting by one outside
vertex, with roots at `(0,1,2,3)` and the extra vertex at `4` by
construction — so that isomorphism against a block basis flag forces the
identity permutation and reduces to equality of edge patterns.

This is the order-5 `extFlag` pattern one arity up: with four ordered
roots and a single non-root vertex, a root-preserving isomorphism has
nowhere to move anything. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

open Classical

/-- The extension flag of a four-rooting at an outside vertex. -/
def extFlag5 (G : Sym3Graph 6) (θ : Fin 4 → Fin 6) (u : Fin 6) :
    Sym3Flag 4 5 :=
  ⟨G.pullback ![θ 0, θ 1, θ 2, θ 3, u], ![0, 1, 2, 3]⟩

section Ext45

variable {G : Sym3Graph 6} {θ : Fin 4 → Fin 6} {u : Fin 6}

lemma extTuple5_injective (hθ : Function.Injective θ)
    (hu : u ∉ Finset.univ.image θ) :
    Function.Injective ![θ 0, θ 1, θ 2, θ 3, u] := by
  have hne : ∀ i : Fin 4, θ i ≠ u := fun i h =>
    hu (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    first
      | rfl
      | exact absurd (hθ hab) (by decide)
      | exact absurd hab (hne _)
      | exact absurd hab.symm (hne _)

lemma extFlag5_wellFormed {rm : ℕ}
    (hwf : (Sym3Flag.mk G θ).WellFormed (rmType rm)) :
    (extFlag5 G θ u).WellFormed (rmType rm) := by
  constructor
  · have h : Function.Injective (![0, 1, 2, 3] : Fin 4 → Fin 5) := by
      decide
    exact fun a b hab => h hab
  · show (G.pullback ![θ 0, θ 1, θ 2, θ 3, u]).pullback ![0, 1, 2, 3]
      = rmType rm
    rw [Sym3Graph.pullback_pullback]
    have hcomp : (![θ 0, θ 1, θ 2, θ 3, u] ∘ ![(0 : Fin 5), 1, 2, 3]) = θ := by
      funext t
      fin_cases t <;> rfl
    rw [hcomp]
    exact hwf.2

lemma extFlag5_graph_mem (hθ : Function.Injective θ)
    (hu : u ∉ Finset.univ.image θ) (hG : TetraFree.Mem G.toModel) :
    TetraFree.Mem (extFlag5 G θ u).graph.toModel := by
  show TetraFree.Mem (G.pullback ![θ 0, θ 1, θ 2, θ 3, u]).toModel
  rw [Sym3Graph.pullback_toModel _ (extTuple5_injective hθ hu)]
  exact TetraFree.mem_comap _ hG

/-- **Rigidity**: a root-preserving isomorphism of four-rooted
five-vertex flags with standard roots is the identity, so the
isomorphism test is equality of edge patterns. -/
lemma blk45_isIso_extFlag5_iff (flags : List ℕ) (i : ℕ) :
    (blk45Flag flags i).IsIso (extFlag5 G θ u)
      ↔ (blk45Flag flags i).graph.edges = (extFlag5 G θ u).graph.edges := by
  constructor
  · rintro ⟨p, hedges, hroots⟩
    have hroots' : ⇑p ∘ (![0, 1, 2, 3] : Fin 4 → Fin 5) = ![0, 1, 2, 3] :=
      hroots
    have h0 : p 0 = 0 := congrFun hroots' 0
    have h1 : p 1 = 1 := congrFun hroots' 1
    have h2 : p 2 = 2 := congrFun hroots' 2
    have h3 : p 3 = 3 := congrFun hroots' 3
    have h4 : p 4 = 4 := by
      obtain ⟨y, hy⟩ := p.surjective 4
      fin_cases y
      · exact absurd (h0.symm.trans hy) (by decide)
      · exact absurd (h1.symm.trans hy) (by decide)
      · exact absurd (h2.symm.trans hy) (by decide)
      · exact absurd (h3.symm.trans hy) (by decide)
      · exact hy
    have hp : p = 1 := by
      refine Equiv.ext fun x => ?_
      fin_cases x
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    rw [hp] at hedges
    rwa [show Finset.image (⇑(1 : Equiv.Perm (Fin 5))) = id from
      funext fun e => by simp, Finset.image_id] at hedges
  · intro h
    refine ⟨1, ?_, ?_⟩
    · rw [show Finset.image (⇑(1 : Equiv.Perm (Fin 5))) = id from
        funext fun e => by simp, Finset.image_id]
      exact h
    · rfl

/-- Isomorphism tests against equal classes agree. -/
lemma isIso_congr_class45 {rm : ℕ} {F A B : Sym3Flag 4 5}
    (hwfF : F.WellFormed (rmType rm)) (hwfA : A.WellFormed (rmType rm))
    (hwfB : B.WellFormed (rmType rm)) (hF : TetraFree.Mem F.graph.toModel)
    (hA : TetraFree.Mem A.graph.toModel)
    (hB : TetraFree.Mem B.graph.toModel)
    [TetraFree.IsType (rmType rm).toModel]
    (hAB : A.toFlag hwfA hA = B.toFlag hwfB hB) :
    F.IsIso A ↔ F.IsIso B := by
  rw [← Sym3Flag.toFlag_eq_toFlag_iff hwfF hwfA hF hA,
    ← Sym3Flag.toFlag_eq_toFlag_iff hwfF hwfB hF hB, hAB]

lemma insert_card_five (hθ : Function.Injective θ)
    (hu : u ∉ Finset.univ.image θ) :
    (insert u (Finset.univ.image θ)).card = 5 := by
  rw [Finset.card_insert_of_notMem hu,
    Finset.card_image_of_injective _ hθ, Finset.card_univ,
    Fintype.card_fin]

/-- A five-element root-containing subset is the roots plus one outside
vertex. -/
lemma eq_insert_of_card_five (hθ : Function.Injective θ)
    {W : Finset (Fin 6)} (hsub : Finset.univ.image θ ⊆ W)
    (hcard : W.card = 5) :
    ∃ u, u ∉ Finset.univ.image θ
      ∧ W = insert u (Finset.univ.image θ) := by
  have himg : (Finset.univ.image θ).card = 4 := by
    rw [Finset.card_image_of_injective _ hθ, Finset.card_univ,
      Fintype.card_fin]
  have hsd : (W \ Finset.univ.image θ).card = 1 := by
    have h := Finset.card_sdiff (s := Finset.univ.image θ) (t := W)
    rw [Finset.inter_eq_left.mpr hsub] at h
    omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hsd
  have hvmem : v ∈ W \ Finset.univ.image θ := by
    rw [hv]
    exact Finset.mem_singleton_self v
  refine ⟨v, (Finset.mem_sdiff.mp hvmem).2, ?_⟩
  ext x
  constructor
  · intro hx
    by_cases hxi : x ∈ Finset.univ.image θ
    · exact Finset.mem_insert_of_mem hxi
    · have hxd : x ∈ W \ Finset.univ.image θ :=
        Finset.mem_sdiff.mpr ⟨hx, hxi⟩
      rw [hv, Finset.mem_singleton] at hxd
      subst hxd
      exact Finset.mem_insert_self _ _
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hxi
    · exact (Finset.mem_sdiff.mp hvmem).1
    · exact hsub hxi

/-- The extension flag is the restriction of the rooted host to the
roots plus the outside vertex, as labeled flags. -/
noncomputable def extFlagIso45 {rm : ℕ} [TetraFree.IsType (rmType rm).toModel]
    (hwf : (Sym3Flag.mk G θ).WellFormed (rmType rm))
    (hu : u ∉ Finset.univ.image θ) (hG : TetraFree.Mem G.toModel)
    (hroot' : ∀ t, ((Sym3Flag.mk G θ).toLabeledFlag
      hwf hG).rootEmbed.toEmbedding t ∈ insert u (Finset.univ.image θ))
    (hwfE : (extFlag5 G θ u).WellFormed (rmType rm))
    (hmemE : TetraFree.Mem (extFlag5 G θ u).graph.toModel) :
    (extFlag5 G θ u).toLabeledFlag hwfE hmemE
      ≃ᶠ ((Sym3Flag.mk G θ).toLabeledFlag hwf hG).restrict
          (insert u (Finset.univ.image θ)) hroot' := by
  have hmem : ∀ i : Fin 5,
      ![θ 0, θ 1, θ 2, θ 3, u] i ∈ insert u (Finset.univ.image θ) := by
    intro i
    fin_cases i
    · exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_self _ _
  have hcard : (insert u (Finset.univ.image θ)).card = 5 :=
    insert_card_five hwf.1 hu
  refine ⟨⟨Equiv.ofBijective
    (fun i => ⟨![θ 0, θ 1, θ 2, θ 3, u] i, hmem i⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun a b hab => extTuple5_injective hwf.1 hu
        (congrArg Subtype.val hab),
       by rw [Fintype.card_fin, Fintype.card_coe, hcard]⟩),
    fun r f => ?_⟩, fun t => ?_⟩
  · show (G.toModel.comap (Function.Embedding.subtype _)).interp r _
      ↔ (G.pullback ![θ 0, θ 1, θ 2, θ 3, u]).toModel.interp r f
    rw [Sym3Graph.pullback_toModel _ (extTuple5_injective hwf.1 hu)]
    exact Iff.rfl
  · refine Subtype.ext ?_
    fin_cases t <;> rfl

/-- The induced typed sub-flag on the roots plus an outside vertex is
the canonical extension flag, as classes. -/
lemma pullbackFlag_insert_class_eq45 {rm : ℕ}
    [TetraFree.IsType (rmType rm).toModel]
    (hwf : (Sym3Flag.mk G θ).WellFormed (rmType rm))
    (hu : u ∉ Finset.univ.image θ) (hG : TetraFree.Mem G.toModel)
    (hcard : (insert u (Finset.univ.image θ)).card = 5)
    (hroots : ∀ i, (Sym3Flag.mk G θ).roots i
      ∈ insert u (Finset.univ.image θ))
    (hwfP : ((Sym3Flag.mk G θ).pullbackFlag _ hcard hroots).WellFormed
      (rmType rm))
    (hmemP : TetraFree.Mem ((Sym3Flag.mk G θ).pullbackFlag _ hcard
      hroots).graph.toModel)
    (hwfE : (extFlag5 G θ u).WellFormed (rmType rm))
    (hmemE : TetraFree.Mem (extFlag5 G θ u).graph.toModel) :
    ((Sym3Flag.mk G θ).pullbackFlag _ hcard hroots).toFlag hwfP hmemP
      = (extFlag5 G θ u).toFlag hwfE hmemE := by
  refine Quotient.sound ⟨?_⟩
  exact (pullbackFlagIso hwf hG hcard hroots (fun t => hroots t)
      hwfP hmemP).trans
    (extFlagIso45 hwf hu hG (fun t => hroots t) hwfE hmemE).symm

/-- Induced sub-flags on equal subsets have equal classes. -/
lemma pullbackFlag_congr_W45 {rm : ℕ}
    [TetraFree.IsType (rmType rm).toModel]
    {Gσ : Sym3Flag 4 6} {W W' : Finset (Fin 6)}
    (hWW : W = W')
    {hcard : W.card = 5} {hroots : ∀ t, Gσ.roots t ∈ W}
    {hcard' : W'.card = 5} {hroots' : ∀ t, Gσ.roots t ∈ W'}
    {hwfP : (Gσ.pullbackFlag W hcard hroots).WellFormed (rmType rm)}
    {hmemP : TetraFree.Mem (Gσ.pullbackFlag W hcard
      hroots).graph.toModel}
    {hwfP' : (Gσ.pullbackFlag W' hcard' hroots').WellFormed (rmType rm)}
    {hmemP' : TetraFree.Mem (Gσ.pullbackFlag W' hcard'
      hroots').graph.toModel} :
    (Gσ.pullbackFlag W hcard hroots).toFlag hwfP hmemP
      = (Gσ.pullbackFlag W' hcard' hroots').toFlag hwfP' hmemP' := by
  subst hWW
  rfl

/-- **The typed pair count at a four-rooting** is the count of ordered
pairs of distinct outside vertices whose extension flags realize the two
patterns. Stated for arbitrary five-vertex patterns so the same lemma
serves every 45-family. -/
lemma flagPairCountC_eq_extPairs45 {rm : ℕ}
    [TetraFree.IsType (rmType rm).toModel]
    {F₁ F₂ : Sym3Flag 4 5}
    (hwf₁ : F₁.WellFormed (rmType rm)) (hwf₂ : F₂.WellFormed (rmType rm))
    (h₁ : TetraFree.Mem F₁.graph.toModel)
    (h₂ : TetraFree.Mem F₂.graph.toModel)
    (hwf : (Sym3Flag.mk G θ).WellFormed (rmType rm))
    (hG : TetraFree.Mem G.toModel) :
    F₁.flagPairCountC F₂ (Sym3Flag.mk G θ)
      = (Finset.univ.filter (fun p : Fin 6 × Fin 6 =>
          (p.1 ∉ Finset.univ.image θ ∧ p.2 ∉ Finset.univ.image θ
            ∧ p.1 ≠ p.2)
          ∧ F₁.IsIso (extFlag5 G θ p.1)
          ∧ F₂.IsIso (extFlag5 G θ p.2))).card := by
  classical
  rw [Sym3Flag.flagPairCountC]
  have hins : ∀ {v : Fin 6}, v ∉ Finset.univ.image θ →
      insert v (Finset.univ.image θ)
        ∈ (Finset.univ.powersetCard 5 : Finset (Finset (Fin 6))) :=
    fun {v} hv => Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, insert_card_five hwf.1 hv⟩
  have hrootsub : ∀ {v : Fin 6},
      ∀ t, (Sym3Flag.mk G θ).roots t ∈ insert v (Finset.univ.image θ) :=
    fun {v} t => Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩)
  refine (Finset.card_bij
    (fun p hp => ⟨(insert p.1 (Finset.univ.image θ),
        insert p.2 (Finset.univ.image θ)),
      Finset.mem_product.mpr
        ⟨hins ((Finset.mem_filter.mp hp).2.1).1,
         hins ((Finset.mem_filter.mp hp).2.1).2.1⟩⟩)
    ?_ ?_ ?_).symm
  · rintro p hp
    obtain ⟨-, ⟨hu₁, hu₂, hne⟩, hiso₁, hiso₂⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ?_, ?_, ?_⟩
    · intro x hx₁ hx₂
      rcases Finset.mem_insert.mp hx₁ with rfl | hxi
      · rcases Finset.mem_insert.mp hx₂ with heq | hxi₂
        · exact absurd heq hne
        · exact absurd hxi₂ hu₁
      · obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hxi
        exact ⟨t, ht⟩
    · refine ⟨hrootsub, ?_⟩
      exact (isIso_congr_class45 hwf₁
        (Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
        (extFlag5_wellFormed hwf) h₁
        (Sym3Flag.pullbackFlag_graph_mem hG _ hrootsub)
        (extFlag5_graph_mem hwf.1 hu₁ hG)
        (pullbackFlag_insert_class_eq45 hwf hu₁ hG _ hrootsub _ _ _ _)).mpr
        hiso₁
    · refine ⟨hrootsub, ?_⟩
      exact (isIso_congr_class45 hwf₂
        (Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
        (extFlag5_wellFormed hwf) h₂
        (Sym3Flag.pullbackFlag_graph_mem hG _ hrootsub)
        (extFlag5_graph_mem hwf.1 hu₂ hG)
        (pullbackFlag_insert_class_eq45 hwf hu₂ hG _ hrootsub _ _ _ _)).mpr
        hiso₂
  · rintro p hp q hq heq
    obtain ⟨-, ⟨hup₁, hup₂, -⟩, -, -⟩ := Finset.mem_filter.mp hp
    have hpair := congrArg Subtype.val heq
    have h1 : insert p.1 (Finset.univ.image θ)
        = insert q.1 (Finset.univ.image θ) := congrArg Prod.fst hpair
    have h2 : insert p.2 (Finset.univ.image θ)
        = insert q.2 (Finset.univ.image θ) := congrArg Prod.snd hpair
    have hfst : p.1 = q.1 := by
      have hm := Finset.mem_insert_self p.1 (Finset.univ.image θ)
      rw [h1] at hm
      rcases Finset.mem_insert.mp hm with h | h
      · exact h
      · exact absurd h hup₁
    have hsnd : p.2 = q.2 := by
      have hm := Finset.mem_insert_self p.2 (Finset.univ.image θ)
      rw [h2] at hm
      rcases Finset.mem_insert.mp hm with h | h
      · exact h
      · exact absurd h hup₂
    exact Prod.ext hfst hsnd
  · rintro b hb
    obtain ⟨-, hshared, ⟨hr₁, hiso₁⟩, ⟨hr₂, hiso₂⟩⟩ := Finset.mem_filter.mp hb
    have hmem := Finset.mem_product.mp b.property
    have himg₁ : Finset.univ.image θ ⊆ b.val.1 := fun x hx => by
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hx
      exact hr₁ t
    have himg₂ : Finset.univ.image θ ⊆ b.val.2 := fun x hx => by
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hx
      exact hr₂ t
    obtain ⟨u₁, hu₁, hW₁⟩ := eq_insert_of_card_five hwf.1 himg₁
      (Finset.mem_powersetCard.mp hmem.1).2
    obtain ⟨u₂, hu₂, hW₂⟩ := eq_insert_of_card_five hwf.1 himg₂
      (Finset.mem_powersetCard.mp hmem.2).2
    have hne : u₁ ≠ u₂ := by
      intro h
      subst h
      have hm₁ : u₁ ∈ b.val.1 := by
        rw [hW₁]; exact Finset.mem_insert_self _ _
      have hm₂ : u₁ ∈ b.val.2 := by
        rw [hW₂]; exact Finset.mem_insert_self _ _
      obtain ⟨t, ht⟩ := hshared u₁ hm₁ hm₂
      exact hu₁ (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩)
    have hiso₁' : F₁.IsIso (extFlag5 G θ u₁) :=
      (isIso_congr_class45 hwf₁
        (Sym3Flag.pullbackFlag_wellFormed hwf _ hr₁)
        (extFlag5_wellFormed hwf) h₁
        (Sym3Flag.pullbackFlag_graph_mem hG _ hr₁)
        (extFlag5_graph_mem hwf.1 hu₁ hG)
        ((pullbackFlag_congr_W45 hW₁
            (hcard' := insert_card_five hwf.1 hu₁)
            (hroots' := hrootsub)
            (hwfP' := Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
            (hmemP' := Sym3Flag.pullbackFlag_graph_mem hG _
              hrootsub)).trans
          (pullbackFlag_insert_class_eq45 hwf hu₁ hG
            (insert_card_five hwf.1 hu₁) hrootsub
            (Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
            (Sym3Flag.pullbackFlag_graph_mem hG _ hrootsub)
            (extFlag5_wellFormed hwf)
            (extFlag5_graph_mem hwf.1 hu₁ hG)))).mp hiso₁
    have hiso₂' : F₂.IsIso (extFlag5 G θ u₂) :=
      (isIso_congr_class45 hwf₂
        (Sym3Flag.pullbackFlag_wellFormed hwf _ hr₂)
        (extFlag5_wellFormed hwf) h₂
        (Sym3Flag.pullbackFlag_graph_mem hG _ hr₂)
        (extFlag5_graph_mem hwf.1 hu₂ hG)
        ((pullbackFlag_congr_W45 hW₂
            (hcard' := insert_card_five hwf.1 hu₂)
            (hroots' := hrootsub)
            (hwfP' := Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
            (hmemP' := Sym3Flag.pullbackFlag_graph_mem hG _
              hrootsub)).trans
          (pullbackFlag_insert_class_eq45 hwf hu₂ hG
            (insert_card_five hwf.1 hu₂) hrootsub
            (Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
            (Sym3Flag.pullbackFlag_graph_mem hG _ hrootsub)
            (extFlag5_wellFormed hwf)
            (extFlag5_graph_mem hwf.1 hu₂ hG)))).mp hiso₂
    refine ⟨(u₁, u₂), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨hu₁, hu₂, hne⟩, hiso₁', hiso₂'⟩, ?_⟩
    exact Subtype.ext (Prod.ext hW₁.symm hW₂.symm)

/-- **The sparsity collapse**: the quadratic form of pair counts at a
rooting factorizes over the ordered pairs of outside vertices into a
product of per-vertex weights — each weight the coefficient sum of the
patterns realized by that vertex's extension flag. -/
lemma sum_pairCount_eq_pairSum45 {rm : ℕ}
    [TetraFree.IsType (rmType rm).toModel]
    {ι : Type} [Fintype ι] (c : ι → ℚ) (F : ι → Sym3Flag 4 5)
    (hwfF : ∀ i, (F i).WellFormed (rmType rm))
    (hF : ∀ i, TetraFree.Mem (F i).graph.toModel)
    (hwf : (Sym3Flag.mk G θ).WellFormed (rmType rm))
    (hG : TetraFree.Mem G.toModel) :
    (∑ i, ∑ j, c i * c j
      * ((F i).flagPairCountC (F j) (Sym3Flag.mk G θ) : ℚ))
      = ∑ p ∈ Finset.univ.filter (fun p : Fin 6 × Fin 6 =>
          p.1 ∉ Finset.univ.image θ ∧ p.2 ∉ Finset.univ.image θ
            ∧ p.1 ≠ p.2),
          (∑ i, c i * (if (F i).IsIso (extFlag5 G θ p.1) then 1 else 0))
            * (∑ j, c j * (if (F j).IsIso (extFlag5 G θ p.2)
                then 1 else 0)) := by
  classical
  have hcount : ∀ i j : ι,
      ((F i).flagPairCountC (F j) (Sym3Flag.mk G θ) : ℚ)
      = ∑ p ∈ Finset.univ.filter (fun p : Fin 6 × Fin 6 =>
          p.1 ∉ Finset.univ.image θ ∧ p.2 ∉ Finset.univ.image θ
            ∧ p.1 ≠ p.2),
          ((if (F i).IsIso (extFlag5 G θ p.1) then 1 else 0)
            * (if (F j).IsIso (extFlag5 G θ p.2) then 1 else 0) : ℚ) := by
    intro i j
    rw [flagPairCountC_eq_extPairs45 (hwfF i) (hwfF j) (hF i) (hF j)
      hwf hG, ← Finset.filter_filter, Finset.card_filter]
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

/-! ## The isomorphism test as a mask comparison -/

/-- The induced mask stays below `2^10`. -/
lemma inducedFrom_tri5_lt (m vs : ℕ) : inducedFrom tri5 m vs < 2 ^ 10 := by
  have heq : inducedFrom tri5 m vs
      = tri5.foldl (fun acc t =>
          if m.testBit (triIdx 6
              (sort3 (vertAt vs t.1) (vertAt vs t.2.1)
                (vertAt vs t.2.2.1)).1
              (sort3 (vertAt vs t.1) (vertAt vs t.2.1)
                (vertAt vs t.2.2.1)).2.1
              (sort3 (vertAt vs t.1) (vertAt vs t.2.1)
                (vertAt vs t.2.2.1)).2.2)
          then acc ||| (1 <<< t.2.2.2) else acc) 0 := rfl
  rw [heq]
  exact foldl_or_lt_two_pow _ _ _ _ _ (Nat.two_pow_pos 10)
    (by decide)

/-- **The isomorphism test is a mask comparison**: a block flag matches
the extension flag at an outside vertex exactly when its stored mask is
the induced mask the certificate's fold computes. -/
lemma blk45_isIso_iff_mask {r : ℕ} {θ : Fin 4 → Fin 6} {u : Fin 6}
    (hθ : Function.Injective θ) (hu : u ∉ Finset.univ.image θ)
    (flags : List ℕ) (i : ℕ) (hflag : flags.getD i 0 < 2 ^ 10) :
    (blk45Flag flags i).IsIso (extFlag5 (graphOfMask 6 r) θ u)
      ↔ flags.getD i 0
          = inducedFrom tri5 r (pack5 ![θ 0, θ 1, θ 2, θ 3, u]) := by
  rw [blk45_isIso_extFlag5_iff]
  have hext : (extFlag5 (graphOfMask 6 r) θ u).graph
      = graphOfMask 5 (inducedFrom tri5 r (pack5 ![θ 0, θ 1, θ 2, θ 3, u])) := by
    show (graphOfMask 6 r).pullback _ = _
    rw [graphOfMask_inducedFrom r ![θ 0, θ 1, θ 2, θ 3, u]
      (extTuple5_injective hθ hu)]
  constructor
  · intro h
    refine graphOfMask5_inj hflag (inducedFrom_tri5_lt _ _) ?_
    refine Sym3Graph.ext ?_
    rw [show (graphOfMask 5 (flags.getD i 0)).edges
        = (blk45Flag flags i).graph.edges from rfl, h, hext]
  · intro h
    show (blk45Flag flags i).graph.edges = _
    rw [show (blk45Flag flags i).graph = graphOfMask 5 (flags.getD i 0)
      from rfl, h, hext]

/-- The typed pair density at a four-rooting is the pair count over
`pairChoose 2 1 1 = 2`. -/
lemma pairDensity_toCount45 {rm : ℕ}
    [TetraFree.IsType (rmType rm).toModel]
    {F₁ F₂ : Sym3Flag 4 5}
    (hwf₁ : F₁.WellFormed (rmType rm)) (hwf₂ : F₂.WellFormed (rmType rm))
    (h₁ : TetraFree.Mem F₁.graph.toModel)
    (h₂ : TetraFree.Mem F₂.graph.toModel)
    (hwf : (Sym3Flag.mk G θ).WellFormed (rmType rm))
    (hG : TetraFree.Mem G.toModel) :
    subflagPairDensity (F₁.toFlag hwf₁ h₁) (F₂.toFlag hwf₂ h₂)
        ((Sym3Flag.mk G θ).toFlag hwf hG)
      = (F₁.flagPairCountC F₂ (Sym3Flag.mk G θ) : ℚ) / 2 := by
  rw [Sym3Flag.subflagPairDensity_toFlag hwf₁ hwf₂ hwf h₁ h₂ hG]
  rfl

/-- **The family coefficient as a rooting sum of weight products**: the
labeling-weighted fiber sum of the quadratic form over a literal host is
the average, over the well-formed four-rootings, of the outside-pair
weight products — each weight the coefficient sum of the matching
patterns. -/
theorem gamma45_eq_rooting {rm : ℕ}
    [TetraFree.IsType (rmType rm).toModel]
    {ι : Type} [Fintype ι] (c : ι → ℚ) (F : ι → Sym3Flag 4 5)
    (hwfF : ∀ i, (F i).WellFormed (rmType rm))
    (hF : ∀ i, TetraFree.Mem (F i).graph.toModel)
    {G : Sym3Graph 6} (hG : TetraFree.Mem G.toModel) :
    (∑ X ∈ Finset.univ.filter
        (fun X : FlagWithSize TetraFree (rmType rm).toModel 6 =>
          Flag.unlabel X = G.toFlag hG),
      (∑ i, ∑ j, (c i : ℝ) * (c j : ℝ)
          * ((subflagPairDensity ((F i).toFlag (hwfF i) (hF i))
              ((F j).toFlag (hwfF j) (hF j)) X : ℚ) : ℝ))
        * (labelingFactor (Quotient.out X).unlabel (Quotient.out X) : ℝ))
      = (1 / 360 : ℝ) * ∑ θ ∈ rootingsOf (rmType rm) G,
          ((((∑ p ∈ Finset.univ.filter (fun p : Fin 6 × Fin 6 =>
              p.1 ∉ Finset.univ.image θ ∧ p.2 ∉ Finset.univ.image θ
                ∧ p.1 ≠ p.2),
              (∑ i, c i * (if (F i).IsIso (extFlag5 G θ p.1)
                  then 1 else 0))
                * (∑ j, c j * (if (F j).IsIso (extFlag5 G θ p.2)
                    then 1 else 0))) / 2 : ℚ)) : ℝ) := by
  have h := fiber_sum_eq_rooting_sum (𝕋 := TetraFree)
    (σg := rmType rm) (by norm_num : 4 ≤ 6)
    (fun X : FlagWithSize TetraFree (rmType rm).toModel 6 =>
      ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ)
        * ((subflagPairDensity ((F i).toFlag (hwfF i) (hF i))
            ((F j).toFlag (hwfF j) (hF j)) X : ℚ) : ℝ)) hG
  rw [show Nat.descFactorial 6 4 = 360 from rfl] at h
  rw [h]
  congr 1
  have hper : ∀ θ ∈ (rootingsOf (rmType rm) G).attach,
      (∑ i, ∑ j, (c i : ℝ) * (c j : ℝ)
        * ((subflagPairDensity ((F i).toFlag (hwfF i) (hF i))
            ((F j).toFlag (hwfF j) (hF j))
            ((Sym3Flag.mk G θ.val).toFlag
              (mem_rootingsOf.mp θ.property) hG) : ℚ) : ℝ))
      = ((((∑ p ∈ Finset.univ.filter (fun p : Fin 6 × Fin 6 =>
          p.1 ∉ Finset.univ.image θ.val ∧ p.2 ∉ Finset.univ.image θ.val
            ∧ p.1 ≠ p.2),
          (∑ i, c i * (if (F i).IsIso (extFlag5 G θ.val p.1)
              then 1 else 0))
            * (∑ j, c j * (if (F j).IsIso (extFlag5 G θ.val p.2)
                then 1 else 0))) / 2 : ℚ)) : ℝ) := by
    intro θ _
    have hwfθ : (Sym3Flag.mk G θ.val).WellFormed (rmType rm) :=
      mem_rootingsOf.mp θ.property
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by
        rw [pairDensity_toCount45 (hwfF i) (hwfF j) (hF i) (hF j)
          hwfθ hG]]
    rw [show (∑ i, ∑ j, (c i : ℝ) * (c j : ℝ)
        * ((((F i).flagPairCountC (F j) (Sym3Flag.mk G θ.val) : ℚ)
            / 2 : ℚ) : ℝ))
        = (((∑ i, ∑ j, c i * c j
            * ((F i).flagPairCountC (F j) (Sym3Flag.mk G θ.val) : ℚ))
              / 2 : ℚ) : ℝ) from by
      push_cast
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring]
    rw [sum_pairCount_eq_pairSum45 c F hwfF hF hwfθ hG]
  rw [Finset.sum_congr rfl hper]
  exact Finset.sum_attach (rootingsOf (rmType rm) G) fun θ =>
    ((((∑ p ∈ Finset.univ.filter (fun p : Fin 6 × Fin 6 =>
        p.1 ∉ Finset.univ.image θ ∧ p.2 ∉ Finset.univ.image θ
          ∧ p.1 ≠ p.2),
        (∑ i, c i * (if (F i).IsIso (extFlag5 G θ p.1) then 1 else 0))
          * (∑ j, c j * (if (F j).IsIso (extFlag5 G θ p.2)
              then 1 else 0))) / 2 : ℚ)) : ℝ)

end Ext45

end FlagAlgebras.Core.Tetrahedron
