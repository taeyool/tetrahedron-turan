import LeanFlagAlgebras.Core.Compute.Sym3Fiber
import LeanFlagAlgebras.Core.Examples.Tetrahedron
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-! # The order-5 semidefinite certificate for the tetrahedron problem

The rank-one sum-of-squares certificate found by exact rational search:
with the seven edge-rooted flags of size four as basis, the vector
`v = (1, −3, −1, 3, −1, 0, 1)` and weight `q = 3/26` prove

`⟦edge⟧ ≤ (42/65) • 1`,

strictly below the order-5 averaging bound `7/10`. This file constructs
the certificate element, expands its downward square over the unlabeled
five-vertex classes, and assembles the bound conditionally on the
per-class slack inequalities (`slackC_nonneg`), which are discharged by
the literal tables in the sequel. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

open Classical

/-- The seven edge-rooted flags of size four: the root edge plus any
proper subset of the three triples through root pairs and the extra
vertex, in the order `[∅; {01}; {02}; {12}; {01,02}; {01,12}; {02,12}]`
of pair subsets. -/
def certBasis : Fin 7 → Sym3Flag 3 4 :=
  ![⟨⟨{{0,1,2}}, by decide⟩, ![0,1,2]⟩,
    ⟨⟨{{0,1,2},{0,1,3}}, by decide⟩, ![0,1,2]⟩,
    ⟨⟨{{0,1,2},{0,2,3}}, by decide⟩, ![0,1,2]⟩,
    ⟨⟨{{0,1,2},{1,2,3}}, by decide⟩, ![0,1,2]⟩,
    ⟨⟨{{0,1,2},{0,1,3},{0,2,3}}, by decide⟩, ![0,1,2]⟩,
    ⟨⟨{{0,1,2},{0,1,3},{1,2,3}}, by decide⟩, ![0,1,2]⟩,
    ⟨⟨{{0,1,2},{0,2,3},{1,2,3}}, by decide⟩, ![0,1,2]⟩]

set_option maxRecDepth 8192 in
lemma certBasis_wf : ∀ i, (certBasis i).WellFormed edgeGraph := by decide

set_option maxRecDepth 16384 in
lemma certBasis_mem :
    ∀ i, TetraFree.Mem (certBasis i).graph.toModel := by decide

/-- The certificate vector. -/
def vC : Fin 7 → ℚ := ![1, -3, -1, 3, -1, 0, 1]

/-- The certificate element of the edge-typed algebra. -/
noncomputable def xCert : FlagAlgebra TetraFree edgeGraph.toModel :=
  ∑ i, (vC i : ℝ) • ⟦basisVector
    ⟨4, (certBasis i).toFlag (certBasis_wf i) (certBasis_mem i)⟩⟧

/-- The quadratic-form weight of a typed five-vertex class. -/
noncomputable def wCert
    (X : FlagWithSize TetraFree edgeGraph.toModel 5) : ℝ :=
  ∑ i, ∑ j, ((vC i : ℝ) * (vC j : ℝ))
    * ((subflagPairDensity
        ((certBasis i).toFlag (certBasis_wf i) (certBasis_mem i))
        ((certBasis j).toFlag (certBasis_wf j) (certBasis_mem j)) X : ℚ) : ℝ)

/-- The coefficient of an unlabeled five-vertex class in the downward
square: the labeling-weighted quadratic form over its typed fiber. -/
noncomputable def gammaC (H : FlagWithSize TetraFree emptyType 5) : ℝ :=
  ∑ X ∈ Finset.univ.filter
      (fun X : FlagWithSize TetraFree edgeGraph.toModel 5 =>
        Flag.unlabel X = H),
    wCert X * (labelingFactor (Quotient.out X).unlabel
      (Quotient.out X) : ℝ)

/-- The downward square of the certificate element expands over the
unlabeled five-vertex classes with the `gammaC` coefficients. -/
theorem downward_xCert_sq :
    downward (xCert * xCert)
      = ∑ H : FlagWithSize TetraFree emptyType 5,
          gammaC H • ⟦basisVector ⟨5, H⟩⟧ := by
  have hexp : xCert * xCert
      = ∑ i, ∑ j, ((vC i : ℝ) * (vC j : ℝ))
          • ((⟦basisVector ⟨4, (certBasis i).toFlag
                (certBasis_wf i) (certBasis_mem i)⟩⟧ :
              FlagAlgebra TetraFree edgeGraph.toModel)
            * ⟦basisVector ⟨4, (certBasis j).toFlag
                (certBasis_wf j) (certBasis_mem j)⟩⟧) := by
    rw [xCert, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      flagAlgebra_smul_mul_smul_comm _ _ _ _
  rw [hexp, downward_sum,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => downward_sum _ _,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) =>
        downward_smul _ _,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by
        rw [downward_basisVector_mul (ℓ := 5) _ _ (by simp),
          Finset.smul_sum,
          Finset.sum_congr rfl fun X (_ : X ∈ Finset.univ) =>
            smul_smul _ _ _],
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => Finset.sum_comm,
    Finset.sum_comm]
  rw [show (∑ X : FlagWithSize TetraFree edgeGraph.toModel 5, ∑ i, ∑ j,
      (((vC i : ℝ) * (vC j : ℝ))
        * ((subflagPairDensity
            ((certBasis i).toFlag (certBasis_wf i) (certBasis_mem i))
            ((certBasis j).toFlag (certBasis_wf j) (certBasis_mem j))
            X : ℚ) : ℝ))
        • downward ⟦basisVector ⟨5, X⟩⟧)
      = ∑ X : FlagWithSize TetraFree edgeGraph.toModel 5,
          wCert X • downward ⟦basisVector ⟨5, X⟩⟧ from
    Finset.sum_congr rfl fun X _ => by
      rw [wCert, Finset.sum_smul,
        Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
          Finset.sum_smul]]
  rw [sum_smul_downward_basis_regroup]
  rfl

/-! ## The fiber identity

The abstract coefficient `gammaC` of an unlabeled class realized by a
literal host is the average of the quadratic form over the host's
well-formed edge rootings: the typed fiber is partitioned by rootings,
with fiber sizes given by the computable labeling counts. -/

/-- The well-formed edge rootings of a five-vertex host. -/
def rootings (G : Sym3Graph 5) : Finset (Fin 3 → Fin 5) :=
  Finset.univ.filter fun θ => (Sym3Flag.mk G θ).WellFormed edgeGraph

lemma mem_rootings {G : Sym3Graph 5} {θ : Fin 3 → Fin 5} :
    θ ∈ rootings G ↔ (Sym3Flag.mk G θ).WellFormed edgeGraph := by
  rw [rootings, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- Realization: every typed class over the unlabeling of a literal host
is the class of one of its rootings. -/
lemma exists_rooting_class {G : Sym3Graph 5} (hG : TetraFree.Mem G.toModel)
    {X : FlagWithSize TetraFree edgeGraph.toModel 5}
    (hX : Flag.unlabel X = G.toFlag hG) :
    ∃ θ, ∃ hwf : (Sym3Flag.mk G θ).WellFormed edgeGraph,
      (Sym3Flag.mk G θ).toFlag hwf hG = X := by
  have hout : (Quotient.out X).unlabel.toFlag = G.toFlag hG := by
    rw [out_unlabel_toFlag_eq]
    exact hX
  obtain ⟨i⟩ := Quotient.exact hout
  have e : (Quotient.out X).toModel ≃ᵣ G.toModel := i.toIso
  have hinj : Function.Injective
      (fun t => e.toEquiv ((Quotient.out X).rootEmbed.toEmbedding t)) :=
    fun a b hab => (Quotient.out X).rootEmbed.toEmbedding.injective
      (e.toEquiv.injective hab)
  have hwf : (Sym3Flag.mk G
      (fun t => e.toEquiv
        ((Quotient.out X).rootEmbed.toEmbedding t))).WellFormed
      edgeGraph := by
    refine ⟨hinj, ?_⟩
    apply Sym3Graph.toModel_injective
    rw [Sym3Graph.pullback_toModel _ hinj]
    refine Model.ext ?_
    funext r f
    cases r
    exact propext (Iff.trans (e.interp_iff () _)
      ((Quotient.out X).rootEmbed.interp_iff () f))
  refine ⟨_, hwf, ?_⟩
  have hiso : (Sym3Flag.mk G _).toLabeledFlag hwf hG
      ≃ᶠ Quotient.out X :=
    ⟨e.symm, fun t => e.toEquiv.symm_apply_apply _⟩
  calc (Sym3Flag.mk G _).toFlag hwf hG
      = ⟦Quotient.out X⟧ := Quotient.sound ⟨hiso⟩
    _ = X := Quotient.out_eq X

/-- **The fiber identity**: the abstract class coefficient is the rooting
average of the quadratic form. -/
theorem gammaC_eq_rooting_sum {G : Sym3Graph 5}
    (hG : TetraFree.Mem G.toModel) :
    gammaC (G.toFlag hG)
      = (1 / 60 : ℝ) * ∑ θ ∈ (rootings G).attach,
          wCert ((Sym3Flag.mk G θ.val).toFlag
            (mem_rootings.mp θ.property) hG) := by
  classical
  set k : {θ // θ ∈ rootings G} →
      FlagWithSize TetraFree edgeGraph.toModel 5 :=
    fun θ => (Sym3Flag.mk G θ.val).toFlag
      (mem_rootings.mp θ.property) hG with hk
  have hfibcard : ∀ X : FlagWithSize TetraFree edgeGraph.toModel 5,
      Flag.unlabel X = G.toFlag hG →
      (((rootings G).attach.filter fun θ => k θ = X).card : ℚ)
        = 60 * labelingFactor (Quotient.out X).unlabel (Quotient.out X)
      := by
    intro X hX
    obtain ⟨θ₀, hwf₀, hXeq⟩ := exists_rooting_class hG hX
    rw [← hXeq, Sym3Flag.labelingFactor_out hwf₀ hG,
      show Nat.descFactorial 5 3 = 60 from by decide]
    rw [show (((rootings G).attach.filter fun θ =>
        k θ = (Sym3Flag.mk G θ₀).toFlag hwf₀ hG).card)
        = (Sym3Flag.mk G θ₀).labelingCountC edgeGraph from ?_]
    · push_cast
      ring
    · rw [Sym3Flag.labelingCountC]
      refine Finset.card_bij (fun θ _ => θ.val) ?_ ?_ ?_
      · rintro θ hθ
        have hkθ := (Finset.mem_filter.mp hθ).2
        have hwfθ := mem_rootings.mp θ.property
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwfθ, ?_⟩
        exact (Sym3Flag.toFlag_eq_toFlag_iff hwfθ hwf₀ hG hG).mp hkθ
      · rintro θ _ θ' _ h
        exact Subtype.ext h
      · rintro θ' hθ'
        obtain ⟨-, hwf', hiso'⟩ := Finset.mem_filter.mp hθ'
        refine ⟨⟨θ', mem_rootings.mpr hwf'⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ?_⟩, rfl⟩
        exact (Sym3Flag.toFlag_eq_toFlag_iff hwf' hwf₀ hG hG).mpr hiso'
  have hfibzero : ∀ X : FlagWithSize TetraFree edgeGraph.toModel 5,
      ¬(Flag.unlabel X = G.toFlag hG) →
      ((rootings G).attach.filter fun θ => k θ = X) = ∅ := by
    intro X hX
    refine Finset.eq_empty_iff_forall_notMem.mpr fun θ hθ => hX ?_
    have hkθ := (Finset.mem_filter.mp hθ).2
    rw [← hkθ, hk]
    exact Sym3Flag.unlabel_toFlag _ hG
  rw [gammaC,
    Finset.sum_congr rfl fun X hX => by
      rw [show (labelingFactor (Quotient.out X).unlabel
          (Quotient.out X) : ℝ)
          = (((rootings G).attach.filter fun θ => k θ = X).card : ℝ) / 60
        from by
          have h := hfibcard X (Finset.mem_filter.mp hX).2
          have h' := congrArg (fun q : ℚ => (q : ℝ)) h
          push_cast at h'
          linarith]]
  rw [show (∑ X ∈ Finset.univ.filter
      (fun X : FlagWithSize TetraFree edgeGraph.toModel 5 =>
        Flag.unlabel X = G.toFlag hG),
      wCert X * ((((rootings G).attach.filter
        fun θ => k θ = X).card : ℝ) / 60))
      = ∑ X : FlagWithSize TetraFree edgeGraph.toModel 5,
        wCert X * ((((rootings G).attach.filter
          fun θ => k θ = X).card : ℝ) / 60) from
    Finset.sum_subset (Finset.filter_subset _ _) fun X _ hX => by
      rw [hfibzero X (by simpa using hX), Finset.card_empty]
      norm_num]
  calc ∑ X : FlagWithSize TetraFree edgeGraph.toModel 5,
        wCert X * ((((rootings G).attach.filter
          fun θ => k θ = X).card : ℝ) / 60)
      = ∑ X : FlagWithSize TetraFree edgeGraph.toModel 5,
          (1 / 60 : ℝ) * ∑ θ ∈ (rootings G).attach.filter
            (fun θ => k θ = X), wCert (k θ) := by
        refine Finset.sum_congr rfl fun X _ => ?_
        rw [Finset.sum_congr rfl fun θ hθ => by
            rw [(Finset.mem_filter.mp hθ).2],
          Finset.sum_const, nsmul_eq_mul]
        ring
    _ = (1 / 60 : ℝ) * ∑ X : FlagWithSize TetraFree edgeGraph.toModel 5,
          ∑ θ ∈ (rootings G).attach.filter (fun θ => k θ = X),
            wCert (k θ) := by
        rw [Finset.mul_sum]
    _ = (1 / 60 : ℝ) * ∑ θ ∈ (rootings G).attach, wCert (k θ) :=
        congrArg (fun z => (1 / 60 : ℝ) * z)
          (@Finset.sum_fiberwise _ _ _ _ _ _ (rootings G).attach k
            fun θ => wCert (k θ))

/-! ## The canonical extension flag

The typed four-vertex flag induced at a rooting by one outside vertex,
with roots at `(0,1,2)` and the extra vertex at `3` by construction —
so that isomorphism against the certificate basis forces the identity
permutation and reduces to equality of edge patterns. -/

/-- The extension flag of a rooting at an outside vertex. -/
def extFlag (G : Sym3Graph 5) (θ : Fin 3 → Fin 5) (u : Fin 5) :
    Sym3Flag 3 4 :=
  ⟨G.pullback ![θ 0, θ 1, θ 2, u], ![0, 1, 2]⟩

section ExtFlag

variable {G : Sym3Graph 5} {θ : Fin 3 → Fin 5} {u : Fin 5}

lemma extTuple_injective (hθ : Function.Injective θ)
    (hu : u ∉ Finset.univ.image θ) :
    Function.Injective ![θ 0, θ 1, θ 2, u] := by
  have hne : ∀ i : Fin 3, θ i ≠ u := fun i h =>
    hu (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    first
      | rfl
      | exact absurd (hθ hab) (by decide)
      | exact absurd hab (hne _)
      | exact absurd hab.symm (hne _)

lemma extFlag_wellFormed (hwf : (Sym3Flag.mk G θ).WellFormed edgeGraph) :
    (extFlag G θ u).WellFormed edgeGraph := by
  constructor
  · have h : Function.Injective (![0, 1, 2] : Fin 3 → Fin 4) := by decide
    exact fun a b hab => h hab
  · show (G.pullback ![θ 0, θ 1, θ 2, u]).pullback ![0, 1, 2] = edgeGraph
    rw [Sym3Graph.pullback_pullback]
    have hcomp : (![θ 0, θ 1, θ 2, u] ∘ ![(0 : Fin 4), 1, 2]) = θ := by
      funext t
      fin_cases t <;> rfl
    rw [hcomp]
    exact hwf.2

lemma extFlag_graph_mem (hwf : (Sym3Flag.mk G θ).WellFormed edgeGraph)
    (hu : u ∉ Finset.univ.image θ) (hG : TetraFree.Mem G.toModel) :
    TetraFree.Mem (extFlag G θ u).graph.toModel := by
  show TetraFree.Mem (G.pullback ![θ 0, θ 1, θ 2, u]).toModel
  rw [Sym3Graph.pullback_toModel _ (extTuple_injective hwf.1 hu)]
  exact TetraFree.mem_comap _ hG

/-- The extension flag is the restriction of the rooted host to the
roots plus the outside vertex, as labeled flags. -/
noncomputable def extFlagIso (hwf : (Sym3Flag.mk G θ).WellFormed edgeGraph)
    (hu : u ∉ Finset.univ.image θ) (hG : TetraFree.Mem G.toModel)
    (hroot' : ∀ t, ((Sym3Flag.mk G θ).toLabeledFlag
      hwf hG).rootEmbed.toEmbedding t ∈ insert u (Finset.univ.image θ))
    (hwfE : (extFlag G θ u).WellFormed edgeGraph)
    (hmemE : TetraFree.Mem (extFlag G θ u).graph.toModel) :
    (extFlag G θ u).toLabeledFlag hwfE hmemE
      ≃ᶠ ((Sym3Flag.mk G θ).toLabeledFlag hwf hG).restrict
          (insert u (Finset.univ.image θ)) hroot' := by
  have hmem : ∀ i : Fin 4,
      ![θ 0, θ 1, θ 2, u] i ∈ insert u (Finset.univ.image θ) := by
    intro i
    fin_cases i
    · exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_insert_self _ _
  have hcard : (insert u (Finset.univ.image θ)).card = 4 := by
    rw [Finset.card_insert_of_notMem hu,
      Finset.card_image_of_injective _ hwf.1, Finset.card_univ,
      Fintype.card_fin]
  refine ⟨⟨Equiv.ofBijective
    (fun i => ⟨![θ 0, θ 1, θ 2, u] i, hmem i⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun a b hab => extTuple_injective hwf.1 hu
        (congrArg Subtype.val hab),
       by rw [Fintype.card_fin, Fintype.card_coe, hcard]⟩),
    fun r f => ?_⟩, fun t => ?_⟩
  · show (G.toModel.comap (Function.Embedding.subtype _)).interp r _
      ↔ (G.pullback ![θ 0, θ 1, θ 2, u]).toModel.interp r f
    rw [Sym3Graph.pullback_toModel _ (extTuple_injective hwf.1 hu)]
    exact Iff.rfl
  · refine Subtype.ext ?_
    fin_cases t <;> rfl

/-- Isomorphism tests against equal classes agree. -/
lemma isIso_congr_class {F A B : Sym3Flag 3 4}
    (hwfF : F.WellFormed edgeGraph) (hwfA : A.WellFormed edgeGraph)
    (hwfB : B.WellFormed edgeGraph) (hF : TetraFree.Mem F.graph.toModel)
    (hA : TetraFree.Mem A.graph.toModel)
    (hB : TetraFree.Mem B.graph.toModel)
    (hAB : A.toFlag hwfA hA = B.toFlag hwfB hB) :
    F.IsIso A ↔ F.IsIso B := by
  rw [← Sym3Flag.toFlag_eq_toFlag_iff hwfF hwfA hF hA,
    ← Sym3Flag.toFlag_eq_toFlag_iff hwfF hwfB hF hB, hAB]

lemma insert_card_four (hθ : Function.Injective θ)
    (hu : u ∉ Finset.univ.image θ) :
    (insert u (Finset.univ.image θ)).card = 4 := by
  rw [Finset.card_insert_of_notMem hu,
    Finset.card_image_of_injective _ hθ, Finset.card_univ,
    Fintype.card_fin]

/-- A four-element root-containing subset is the roots plus one outside
vertex. -/
lemma eq_insert_of_card_four (hθ : Function.Injective θ)
    {W : Finset (Fin 5)} (hsub : Finset.univ.image θ ⊆ W)
    (hcard : W.card = 4) :
    ∃ u, u ∉ Finset.univ.image θ
      ∧ W = insert u (Finset.univ.image θ) := by
  have himg : (Finset.univ.image θ).card = 3 := by
    rw [Finset.card_image_of_injective _ hθ, Finset.card_univ,
      Fintype.card_fin]
  have hsd : (W \ Finset.univ.image θ).card = 1 := by
    have h := Finset.card_sdiff (s := Finset.univ.image θ) (t := W)
    rw [Finset.inter_eq_left.mpr hsub] at h
    omega
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hsd
  have humem : u ∈ W \ Finset.univ.image θ := by
    rw [hu]
    exact Finset.mem_singleton_self u
  refine ⟨u, (Finset.mem_sdiff.mp humem).2, ?_⟩
  ext x
  constructor
  · intro hx
    by_cases hxi : x ∈ Finset.univ.image θ
    · exact Finset.mem_insert_of_mem hxi
    · have : x ∈ W \ Finset.univ.image θ := Finset.mem_sdiff.mpr ⟨hx, hxi⟩
      rw [hu, Finset.mem_singleton] at this
      subst this
      exact Finset.mem_insert_self _ _
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hxi
    · exact (Finset.mem_sdiff.mp humem).1
    · exact hsub hxi

/-- The induced typed sub-flag on the roots plus an outside vertex is the
canonical extension flag, as classes. -/
lemma pullbackFlag_insert_class_eq
    (hwf : (Sym3Flag.mk G θ).WellFormed edgeGraph)
    (hu : u ∉ Finset.univ.image θ) (hG : TetraFree.Mem G.toModel)
    (hcard : (insert u (Finset.univ.image θ)).card = 4)
    (hroots : ∀ i, (Sym3Flag.mk G θ).roots i
      ∈ insert u (Finset.univ.image θ))
    (hwfP : ((Sym3Flag.mk G θ).pullbackFlag _ hcard hroots).WellFormed
      edgeGraph)
    (hmemP : TetraFree.Mem ((Sym3Flag.mk G θ).pullbackFlag _ hcard
      hroots).graph.toModel)
    (hwfE : (extFlag G θ u).WellFormed edgeGraph)
    (hmemE : TetraFree.Mem (extFlag G θ u).graph.toModel) :
    ((Sym3Flag.mk G θ).pullbackFlag _ hcard hroots).toFlag hwfP hmemP
      = (extFlag G θ u).toFlag hwfE hmemE := by
  refine Quotient.sound ⟨?_⟩
  exact (pullbackFlagIso hwf hG hcard hroots (fun t => hroots t)
      hwfP hmemP).trans
    (extFlagIso hwf hu hG (fun t => hroots t) hwfE hmemE).symm

/-- Induced sub-flags on equal subsets have equal classes (all proof
arguments are irrelevant). -/
lemma pullbackFlag_congr_W {Gσ : Sym3Flag 3 5} {W W' : Finset (Fin 5)}
    (hWW : W = W')
    {hcard : W.card = 4} {hroots : ∀ t, Gσ.roots t ∈ W}
    {hcard' : W'.card = 4} {hroots' : ∀ t, Gσ.roots t ∈ W'}
    {hwfP : (Gσ.pullbackFlag W hcard hroots).WellFormed edgeGraph}
    {hmemP : TetraFree.Mem (Gσ.pullbackFlag W hcard
      hroots).graph.toModel}
    {hwfP' : (Gσ.pullbackFlag W' hcard' hroots').WellFormed edgeGraph}
    {hmemP' : TetraFree.Mem (Gσ.pullbackFlag W' hcard'
      hroots').graph.toModel} :
    (Gσ.pullbackFlag W hcard hroots).toFlag hwfP hmemP
      = (Gσ.pullbackFlag W' hcard' hroots').toFlag hwfP' hmemP' := by
  subst hWW
  rfl

/-- The typed pair count at a five-vertex rooting is the count of ordered
pairs of distinct outside vertices whose extension flags realize the two
patterns. -/
lemma flagPairCountC_eq_extPairs
    (hwf : (Sym3Flag.mk G θ).WellFormed edgeGraph)
    (hG : TetraFree.Mem G.toModel) (i j : Fin 7) :
    (certBasis i).flagPairCountC (certBasis j) (Sym3Flag.mk G θ)
      = (Finset.univ.filter (fun p : Fin 5 × Fin 5 =>
          (p.1 ∉ Finset.univ.image θ ∧ p.2 ∉ Finset.univ.image θ
            ∧ p.1 ≠ p.2)
          ∧ (certBasis i).IsIso (extFlag G θ p.1)
          ∧ (certBasis j).IsIso (extFlag G θ p.2))).card := by
  classical
  rw [Sym3Flag.flagPairCountC]
  have hins : ∀ {u : Fin 5}, u ∉ Finset.univ.image θ →
      insert u (Finset.univ.image θ)
        ∈ (Finset.univ.powersetCard 4 : Finset (Finset (Fin 5))) :=
    fun {u} hu => Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, insert_card_four hwf.1 hu⟩
  have hrootsub : ∀ {u : Fin 5},
      ∀ t, (Sym3Flag.mk G θ).roots t ∈ insert u (Finset.univ.image θ) :=
    fun {u} t => Finset.mem_insert_of_mem
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
      exact (isIso_congr_class (certBasis_wf i)
        (Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
        (extFlag_wellFormed hwf) (certBasis_mem i)
        (Sym3Flag.pullbackFlag_graph_mem hG _ hrootsub)
        (extFlag_graph_mem hwf hu₁ hG)
        (pullbackFlag_insert_class_eq hwf hu₁ hG _ hrootsub _ _ _ _)).mpr
        hiso₁
    · refine ⟨hrootsub, ?_⟩
      exact (isIso_congr_class (certBasis_wf j)
        (Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
        (extFlag_wellFormed hwf) (certBasis_mem j)
        (Sym3Flag.pullbackFlag_graph_mem hG _ hrootsub)
        (extFlag_graph_mem hwf hu₂ hG)
        (pullbackFlag_insert_class_eq hwf hu₂ hG _ hrootsub _ _ _ _)).mpr
        hiso₂
  · rintro p hp q hq heq
    obtain ⟨-, ⟨hup₁, hup₂, -⟩, -, -⟩ := Finset.mem_filter.mp hp
    have h1 : insert p.1 (Finset.univ.image θ)
        = insert q.1 (Finset.univ.image θ) :=
      congrArg Prod.fst (congrArg Subtype.val heq)
    have h2 : insert p.2 (Finset.univ.image θ)
        = insert q.2 (Finset.univ.image θ) :=
      congrArg Prod.snd (congrArg Subtype.val heq)
    have hfst : p.1 = q.1 := by
      have := Finset.mem_insert_self p.1 (Finset.univ.image θ)
      rw [h1] at this
      rcases Finset.mem_insert.mp this with h | h
      · exact h
      · exact absurd h hup₁
    have hsnd : p.2 = q.2 := by
      have := Finset.mem_insert_self p.2 (Finset.univ.image θ)
      rw [h2] at this
      rcases Finset.mem_insert.mp this with h | h
      · exact h
      · exact absurd h hup₂
    exact Prod.ext hfst hsnd
  · rintro b hb
    obtain ⟨-, hshared, ⟨h₁, hiso₁⟩, ⟨h₂, hiso₂⟩⟩ := Finset.mem_filter.mp hb
    have hmem := Finset.mem_product.mp b.property
    have himg₁ : Finset.univ.image θ ⊆ b.val.1 := fun x hx => by
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hx
      exact h₁ t
    have himg₂ : Finset.univ.image θ ⊆ b.val.2 := fun x hx => by
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hx
      exact h₂ t
    obtain ⟨u₁, hu₁, hW₁⟩ := eq_insert_of_card_four hwf.1 himg₁
      (Finset.mem_powersetCard.mp hmem.1).2
    obtain ⟨u₂, hu₂, hW₂⟩ := eq_insert_of_card_four hwf.1 himg₂
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
    have hiso₁' : (certBasis i).IsIso (extFlag G θ u₁) :=
      (isIso_congr_class (certBasis_wf i)
        (Sym3Flag.pullbackFlag_wellFormed hwf _ h₁)
        (extFlag_wellFormed hwf) (certBasis_mem i)
        (Sym3Flag.pullbackFlag_graph_mem hG _ h₁)
        (extFlag_graph_mem hwf hu₁ hG)
        ((pullbackFlag_congr_W hW₁
            (hcard' := insert_card_four hwf.1 hu₁)
            (hroots' := hrootsub)
            (hwfP' := Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
            (hmemP' := Sym3Flag.pullbackFlag_graph_mem hG _
              hrootsub)).trans
          (pullbackFlag_insert_class_eq hwf hu₁ hG
            (insert_card_four hwf.1 hu₁) hrootsub
            (Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
            (Sym3Flag.pullbackFlag_graph_mem hG _ hrootsub)
            (extFlag_wellFormed hwf)
            (extFlag_graph_mem hwf hu₁ hG)))).mp hiso₁
    have hiso₂' : (certBasis j).IsIso (extFlag G θ u₂) :=
      (isIso_congr_class (certBasis_wf j)
        (Sym3Flag.pullbackFlag_wellFormed hwf _ h₂)
        (extFlag_wellFormed hwf) (certBasis_mem j)
        (Sym3Flag.pullbackFlag_graph_mem hG _ h₂)
        (extFlag_graph_mem hwf hu₂ hG)
        ((pullbackFlag_congr_W hW₂
            (hcard' := insert_card_four hwf.1 hu₂)
            (hroots' := hrootsub)
            (hwfP' := Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
            (hmemP' := Sym3Flag.pullbackFlag_graph_mem hG _
              hrootsub)).trans
          (pullbackFlag_insert_class_eq hwf hu₂ hG
            (insert_card_four hwf.1 hu₂) hrootsub
            (Sym3Flag.pullbackFlag_wellFormed hwf _ hrootsub)
            (Sym3Flag.pullbackFlag_graph_mem hG _ hrootsub)
            (extFlag_wellFormed hwf)
            (extFlag_graph_mem hwf hu₂ hG)))).mp hiso₂
    refine ⟨(u₁, u₂), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨hu₁, hu₂, hne⟩, hiso₁', hiso₂'⟩, ?_⟩
    exact Subtype.ext (Prod.ext hW₁.symm hW₂.symm)

lemma certBasis_roots_eq : ∀ i : Fin 7, (certBasis i).roots = ![0, 1, 2] :=
  by decide

/-- A triple tuple pulls back to the edge type exactly when its image is
an edge: the cheap well-formedness test. -/
lemma pullback_eq_edgeGraph_iff {n : ℕ} {G : Sym3Graph n}
    {f : Fin 3 → Fin n} :
    G.pullback f = edgeGraph ↔ Finset.univ.image f ∈ G.edges := by
  have huniv : ({0, 1, 2} : Finset (Fin 3)) = Finset.univ := by decide
  constructor
  · intro h
    have h1 : ({0, 1, 2} : Finset (Fin 3)) ∈ (G.pullback f).edges := by
      rw [h]
      decide
    obtain ⟨-, -, hmem⟩ := Finset.mem_filter.mp h1
    rwa [huniv] at hmem
  · intro hmem
    apply Sym3Graph.ext
    ext e
    constructor
    · intro he
      obtain ⟨-, hc, -⟩ := Finset.mem_filter.mp he
      have he3 : e = Finset.univ := Finset.eq_univ_of_card e (by
        rw [hc]; decide)
      subst he3
      rw [← huniv]
      decide
    · intro he
      have he3 : e = ({0, 1, 2} : Finset (Fin 3)) :=
        Finset.mem_singleton.mp he
      subst he3
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide, ?_⟩
      rwa [huniv]

/-- Well-formedness of a rooting is the cheap test: injectivity plus the
root triple being an edge. -/
lemma wf_iff_cheap {G : Sym3Graph 5} {θ : Fin 3 → Fin 5} :
    (Sym3Flag.mk G θ).WellFormed edgeGraph
      ↔ Function.Injective θ ∧ Finset.univ.image θ ∈ G.edges := by
  constructor
  · rintro ⟨hinj, hpull⟩
    exact ⟨hinj, pullback_eq_edgeGraph_iff.mp hpull⟩
  · rintro ⟨hinj, hmem⟩
    exact ⟨hinj, pullback_eq_edgeGraph_iff.mpr hmem⟩

/-- Edge-witnesses are exactly the edges. -/
lemma edge_flagCountC_eq_card {n : ℕ} (G : Sym3Graph n) :
    edgeGraph.flagCountC G = G.edges.card := by
  refine le_antisymm (edge_flagCountC_le_card G) ?_
  rw [Sym3Graph.flagCountC]
  refine Finset.card_le_card_of_surjOn (fun W => W.val) ?_
  intro e he
  rw [Finset.mem_coe] at he
  have hmem : e ∈ (Finset.univ.powersetCard 3 : Finset (Finset (Fin n))) :=
    Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, G.edges_valid e he⟩
  have hiso : edgeGraph.IsIso (G.pullback (subsetTuple e
      (Finset.mem_powersetCard.mp hmem).2)) := by
    rw [show G.pullback (subsetTuple e
        (Finset.mem_powersetCard.mp hmem).2) = edgeGraph from
      pullback_eq_edgeGraph_iff.mpr (by
        rwa [subsetTuple_image_univ])]
    exact Sym3Graph.IsIso.refl edgeGraph
  exact ⟨⟨e, hmem⟩, Finset.mem_coe.mpr
    (Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hiso⟩), rfl⟩

/-- Isomorphism of a certificate basis flag against an extension flag
forces the identity permutation, so it is equality of edge sets. -/
lemma certBasis_isIso_extFlag_iff (i : Fin 7) :
    (certBasis i).IsIso (extFlag G θ u)
      ↔ (certBasis i).graph.edges = (extFlag G θ u).graph.edges := by
  constructor
  · rintro ⟨p, hedges, hroots⟩
    rw [certBasis_roots_eq i] at hroots
    have h0 : p 0 = 0 := congrFun hroots 0
    have h1 : p 1 = 1 := congrFun hroots 1
    have h2 : p 2 = 2 := congrFun hroots 2
    have h3 : p 3 = 3 := by
      obtain ⟨y, hy⟩ := p.surjective 3
      fin_cases y
      · exact absurd (h0.symm.trans hy) (by decide)
      · exact absurd (h1.symm.trans hy) (by decide)
      · exact absurd (h2.symm.trans hy) (by decide)
      · exact hy
    have hp : p = 1 := by
      refine Equiv.ext fun x => ?_
      fin_cases x
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    rw [hp] at hedges
    rwa [show Finset.image (⇑(1 : Equiv.Perm (Fin 4))) = id from
      funext fun e => by simp, Finset.image_id] at hedges
  · intro h
    refine ⟨1, ?_, ?_⟩
    · rw [show Finset.image (⇑(1 : Equiv.Perm (Fin 4))) = id from
        funext fun e => by simp, Finset.image_id]
      exact h
    · rw [certBasis_roots_eq i]
      rfl

end ExtFlag

/-- The quadratic form at a rooting class, in terms of computable typed
pair counts. -/
lemma wCert_toFlag {G : Sym3Graph 5} {θ : Fin 3 → Fin 5}
    (hwf : (Sym3Flag.mk G θ).WellFormed edgeGraph)
    (hG : TetraFree.Mem G.toModel) :
    wCert ((Sym3Flag.mk G θ).toFlag hwf hG)
      = ∑ i, ∑ j, ((vC i : ℝ) * (vC j : ℝ))
          * ((((certBasis i).flagPairCountC (certBasis j)
              (Sym3Flag.mk G θ) : ℚ) : ℝ) / 2) := by
  rw [wCert]
  refine Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  rw [Sym3Flag.subflagPairDensity_toFlag (certBasis_wf i)
    (certBasis_wf j) hwf (certBasis_mem i) (certBasis_mem j) hG,
    show pairChoose (5 - 3) (4 - 3) (4 - 3) = 2 from by decide]
  push_cast
  ring

/-! ## The integer certificate value and the kernel table -/

/-- The certificate vector, integer form. -/
def vCZ : Fin 7 → ℤ := ![1, -3, -1, 3, -1, 0, 1]

lemma vCZ_cast : ∀ i, ((vCZ i : ℤ) : ℚ) = vC i := by decide

/-- The certificate weight of an outside vertex at a rooting: the vector
entry of the unique matching basis pattern. -/
def typeWeight (G : Sym3Graph 5) (θ : Fin 3 → Fin 5) (u : Fin 5) : ℤ :=
  ∑ i, if (certBasis i).graph.edges = (extFlag G θ u).graph.edges
    then vCZ i else 0

/-- The rooting contribution: the quadratic form over ordered pairs of
distinct outside vertices. -/
def pairSumZ (G : Sym3Graph 5) (θ : Fin 3 → Fin 5) : ℤ :=
  ∑ p ∈ Finset.univ.filter (fun p : Fin 5 × Fin 5 =>
      p.1 ∉ Finset.univ.image θ ∧ p.2 ∉ Finset.univ.image θ
        ∧ p.1 ≠ p.2),
    typeWeight G θ p.1 * typeWeight G θ p.2

/-- The integer certificate value of a host. -/
def gVal (G : Sym3Graph 5) : ℤ := ∑ θ ∈ rootings G, pairSumZ G θ

/-- The quadratic form of pair counts collapses to the integer
certificate value of the rooting. -/
lemma sum_pairCount_eq_pairSumZ {G : Sym3Graph 5} {θ : Fin 3 → Fin 5}
    (hwf : (Sym3Flag.mk G θ).WellFormed edgeGraph)
    (hG : TetraFree.Mem G.toModel) :
    (∑ i, ∑ j, vC i * vC j
      * ((certBasis i).flagPairCountC (certBasis j)
          (Sym3Flag.mk G θ) : ℚ))
      = ((pairSumZ G θ : ℤ) : ℚ) := by
  classical
  have hcount : ∀ i j : Fin 7,
      ((certBasis i).flagPairCountC (certBasis j)
          (Sym3Flag.mk G θ) : ℚ)
      = ∑ p ∈ Finset.univ.filter (fun p : Fin 5 × Fin 5 =>
          p.1 ∉ Finset.univ.image θ ∧ p.2 ∉ Finset.univ.image θ
            ∧ p.1 ≠ p.2),
          ((if (certBasis i).graph.edges
              = (extFlag G θ p.1).graph.edges then 1 else 0)
            * (if (certBasis j).graph.edges
              = (extFlag G θ p.2).graph.edges then 1 else 0) : ℚ) := by
    intro i j
    rw [flagPairCountC_eq_extPairs hwf hG i j, ← Finset.filter_filter,
      Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [certBasis_isIso_extFlag_iff]
    split_ifs with h1 h2 h3 h4 h5 <;> simp_all
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by
      rw [hcount i j, Finset.mul_sum],
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => Finset.sum_comm,
    Finset.sum_comm, pairSumZ]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show (∑ i, ∑ j, vC i * vC j
      * ((if (certBasis i).graph.edges
          = (extFlag G θ p.1).graph.edges then 1 else 0)
        * (if (certBasis j).graph.edges
          = (extFlag G θ p.2).graph.edges then 1 else 0) : ℚ))
      = (∑ i, vC i * (if (certBasis i).graph.edges
          = (extFlag G θ p.1).graph.edges then 1 else 0))
        * (∑ j, vC j * (if (certBasis j).graph.edges
          = (extFlag G θ p.2).graph.edges then 1 else 0)) from by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring]
  congr 1
  · rw [typeWeight]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← vCZ_cast i]
    split_ifs <;> simp
  · rw [typeWeight]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← vCZ_cast j]
    split_ifs <;> simp

/-- The per-class slack of the certificate. -/
noncomputable def slackC (H : FlagWithSize TetraFree emptyType 5) : ℝ :=
  (42 / 65 : ℝ)
    - ((subflagDensity
        (⟨3, edgeGraph.toFlag edgeGraph_mem⟩ :
          FinFlag TetraFree emptyType).2 H : ℚ) : ℝ)
    - (3 / 26 : ℝ) * gammaC H

/-- The slack of a literal host is nonnegative given the integer
certificate check. -/
lemma slackC_nonneg_of_check {G : Sym3Graph 5}
    (hG : TetraFree.Mem G.toModel)
    (hcheck : gVal G ≤ 672 - 104 * (edgeGraph.flagCountC G : ℤ)) :
    0 ≤ slackC (G.toFlag hG) := by
  have hsum : (∑ θ ∈ (rootings G).attach,
      wCert ((Sym3Flag.mk G θ.val).toFlag
        (mem_rootings.mp θ.property) hG))
      = ((gVal G : ℤ) : ℝ) / 2 := by
    have h1 : ∀ θ : {θ // θ ∈ rootings G},
        wCert ((Sym3Flag.mk G θ.val).toFlag
          (mem_rootings.mp θ.property) hG)
        = ((pairSumZ G θ.val : ℤ) : ℝ) / 2 := by
      intro θ
      rw [wCert_toFlag (mem_rootings.mp θ.property) hG]
      have h2 := congrArg (fun q : ℚ => (q : ℝ))
        (sum_pairCount_eq_pairSumZ (mem_rootings.mp θ.property) hG)
      push_cast at h2
      rw [← h2, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring
    rw [Finset.sum_congr rfl fun θ _ => h1 θ, ← Finset.sum_div, gVal]
    rw [show (∑ θ ∈ (rootings G).attach,
        ((pairSumZ G θ.val : ℤ) : ℝ))
        = ∑ θ ∈ rootings G, ((pairSumZ G θ : ℤ) : ℝ) from
      Finset.sum_attach (rootings G)
        (fun θ => ((pairSumZ G θ : ℤ) : ℝ))]
    push_cast
    rfl
  rw [slackC, gammaC_eq_rooting_sum hG, hsum,
    Sym3Graph.subflagDensity_toFlag,
    show Nat.choose 5 3 = 10 from by decide]
  have hch : ((gVal G : ℤ) : ℝ)
      ≤ 672 - 104 * ((edgeGraph.flagCountC G : ℕ) : ℝ) := by
    exact_mod_cast hcheck
  push_cast
  nlinarith [hch]

/-- The lookup form of the certificate weight: the vector entry selected
by the three pattern-triple memberships. -/
def twLookup (b₀ b₁ b₂ : Bool) : ℤ :=
  match b₀, b₁, b₂ with
  | false, false, false => 1
  | true,  false, false => -3
  | false, true,  false => -1
  | false, false, true  => 3
  | true,  true,  false => -1
  | true,  false, true  => 0
  | false, true,  true  => 1
  | true,  true,  true  => 0

/-- The cheap certificate weight: three edge-membership tests. -/
def twFast (E : Finset (Finset (Fin 5))) (θ : Fin 3 → Fin 5)
    (u : Fin 5) : ℤ :=
  twLookup (decide ({θ 0, θ 1, u} ∈ E)) (decide ({θ 0, θ 2, u} ∈ E))
    (decide ({θ 1, θ 2, u} ∈ E))

/-- The cheap certificate value of an edge set. -/
def gFast (E : Finset (Finset (Fin 5))) : ℤ :=
  ∑ θ ∈ Finset.univ.filter (fun θ : Fin 3 → Fin 5 =>
      Function.Injective θ ∧ Finset.univ.image θ ∈ E),
    ∑ p ∈ Finset.univ.filter (fun p : Fin 5 × Fin 5 =>
        p.1 ∉ Finset.univ.image θ ∧ p.2 ∉ Finset.univ.image θ
          ∧ p.1 ≠ p.2),
      twFast E θ p.1 * twFast E θ p.2

/-- The kernel leaf: the cheap integer certificate check, or a
tetrahedron. -/
def certLeaf (E : Finset (Finset (Fin 5))) : Bool :=
  decide (gFast E ≤ 672 - 104 * ((E.filter fun e => e.card = 3).card : ℤ)
    ∨ (⟨E.filter fun e => e.card = 3,
        fun _ he => (Finset.mem_filter.mp he).2⟩ :
      Sym3Graph 5).toModel.Contains tetra)

set_option maxRecDepth 262144 in
set_option maxHeartbeats 0 in
/-- **The certificate table**: on every five-vertex edge set, either the
cheap certificate value passes the slack check or the graph contains a
tetrahedron. One depth-ten kernel sweep over all `2¹⁰` graphs. -/
lemma certTable :
    allEdgeSetsSat certLeaf (allTriples 5) ∅ = true := by decide

/-- The extension flag's edge set, explicitly: the root edge plus the
pattern triples present in the host. -/
lemma extFlag_edges {G : Sym3Graph 5} {θ : Fin 3 → Fin 5} {u : Fin 5}
    (hroot : Finset.univ.image θ ∈ G.edges) :
    (extFlag G θ u).graph.edges
      = insert ({0, 1, 2} : Finset (Fin 4))
          (((if ({θ 0, θ 1, u} : Finset (Fin 5)) ∈ G.edges
              then {({0, 1, 3} : Finset (Fin 4))} else ∅)
            ∪ (if ({θ 0, θ 2, u} : Finset (Fin 5)) ∈ G.edges
              then {({0, 2, 3} : Finset (Fin 4))} else ∅))
            ∪ (if ({θ 1, θ 2, u} : Finset (Fin 5)) ∈ G.edges
              then {({1, 2, 3} : Finset (Fin 4))} else ∅)) := by
  have htri : ∀ e : Finset (Fin 4), e.card = 3 →
      e = {0, 1, 2} ∨ e = {0, 1, 3} ∨ e = {0, 2, 3} ∨ e = {1, 2, 3} :=
    by decide
  have himg : ∀ e : Finset (Fin 4),
      e.image ![θ 0, θ 1, θ 2, u]
        = e.image (fun i => ![θ 0, θ 1, θ 2, u] i) := fun _ => rfl
  have huniv3 : ({0, 1, 2} : Finset (Fin 3)) = Finset.univ := by decide
  have hrootim : ({0, 1, 2} : Finset (Fin 4)).image ![θ 0, θ 1, θ 2, u]
      = Finset.univ.image θ := by
    rw [← huniv3]
    simp [Finset.image_insert]
  have h013 : ({0, 1, 3} : Finset (Fin 4)).image ![θ 0, θ 1, θ 2, u]
      = {θ 0, θ 1, u} := by
    simp [Finset.image_insert]
  have h023 : ({0, 2, 3} : Finset (Fin 4)).image ![θ 0, θ 1, θ 2, u]
      = {θ 0, θ 2, u} := by
    simp [Finset.image_insert]
  have h123 : ({1, 2, 3} : Finset (Fin 4)).image ![θ 0, θ 1, θ 2, u]
      = {θ 1, θ 2, u} := by
    simp [Finset.image_insert]
  show (G.pullback ![θ 0, θ 1, θ 2, u]).edges = _
  ext e
  rw [show (G.pullback ![θ 0, θ 1, θ 2, u]).edges
      = Finset.univ.filter (fun e : Finset (Fin 4) =>
          e.card = 3 ∧ e.image ![θ 0, θ 1, θ 2, u] ∈ G.edges) from rfl,
    Finset.mem_filter]
  constructor
  · rintro ⟨-, hc, hmem⟩
    rcases htri e hc with rfl | rfl | rfl | rfl
    · exact Finset.mem_insert_self _ _
    · rw [h013] at hmem
      refine Finset.mem_insert_of_mem (Finset.mem_union_left _
        (Finset.mem_union_left _ ?_))
      rw [if_pos hmem]
      exact Finset.mem_singleton_self _
    · rw [h023] at hmem
      refine Finset.mem_insert_of_mem (Finset.mem_union_left _
        (Finset.mem_union_right _ ?_))
      rw [if_pos hmem]
      exact Finset.mem_singleton_self _
    · rw [h123] at hmem
      refine Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_)
      rw [if_pos hmem]
      exact Finset.mem_singleton_self _
  · intro he
    rcases Finset.mem_insert.mp he with rfl | he'
    · refine ⟨Finset.mem_univ _, by decide, ?_⟩
      rw [hrootim]
      exact hroot
    rcases Finset.mem_union.mp he' with he'' | h3
    · rcases Finset.mem_union.mp he'' with h1 | h2
      · by_cases hb : ({θ 0, θ 1, u} : Finset (Fin 5)) ∈ G.edges
        · rw [if_pos hb, Finset.mem_singleton] at h1
          subst h1
          refine ⟨Finset.mem_univ _, by decide, ?_⟩
          rw [h013]
          exact hb
        · rw [if_neg hb] at h1
          exact absurd h1 (Finset.notMem_empty _)
      · by_cases hb : ({θ 0, θ 2, u} : Finset (Fin 5)) ∈ G.edges
        · rw [if_pos hb, Finset.mem_singleton] at h2
          subst h2
          refine ⟨Finset.mem_univ _, by decide, ?_⟩
          rw [h023]
          exact hb
        · rw [if_neg hb] at h2
          exact absurd h2 (Finset.notMem_empty _)
    · by_cases hb : ({θ 1, θ 2, u} : Finset (Fin 5)) ∈ G.edges
      · rw [if_pos hb, Finset.mem_singleton] at h3
        subst h3
        refine ⟨Finset.mem_univ _, by decide, ?_⟩
        rw [h123]
        exact hb
      · rw [if_neg hb] at h3
        exact absurd h3 (Finset.notMem_empty _)

/-- The certificate weight computes by the lookup. -/
lemma typeWeight_eq_twFast {G : Sym3Graph 5} {θ : Fin 3 → Fin 5}
    {u : Fin 5} (hroot : Finset.univ.image θ ∈ G.edges) :
    typeWeight G θ u = twFast G.edges θ u := by
  rw [typeWeight, twFast]
  have he := extFlag_edges (u := u) hroot
  by_cases hb₀ : ({θ 0, θ 1, u} : Finset (Fin 5)) ∈ G.edges <;>
    by_cases hb₁ : ({θ 0, θ 2, u} : Finset (Fin 5)) ∈ G.edges <;>
      by_cases hb₂ : ({θ 1, θ 2, u} : Finset (Fin 5)) ∈ G.edges <;>
    simp only [hb₀, hb₁, hb₂, if_pos, if_neg, not_false_iff,
      decide_true, decide_false] at he ⊢ <;>
    · rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by
        rw [he]]
      decide

/-- The cheap certificate value agrees with the certificate value. -/
lemma gFast_eq_gVal (G : Sym3Graph 5) : gFast G.edges = gVal G := by
  rw [gFast, gVal, rootings,
    show (Finset.univ.filter fun θ : Fin 3 → Fin 5 =>
        Function.Injective θ ∧ Finset.univ.image θ ∈ G.edges)
      = Finset.univ.filter (fun θ : Fin 3 → Fin 5 =>
        (Sym3Flag.mk G θ).WellFormed edgeGraph) from by
      ext θ
      rw [Finset.mem_filter, Finset.mem_filter, wf_iff_cheap]]
  refine Finset.sum_congr rfl fun θ hθ => ?_
  have hwf : (Sym3Flag.mk G θ).WellFormed edgeGraph :=
    (Finset.mem_filter.mp hθ).2
  have hroot : Finset.univ.image θ ∈ G.edges := (wf_iff_cheap.mp hwf).2
  rw [pairSumZ]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [typeWeight_eq_twFast hroot, typeWeight_eq_twFast hroot]

lemma certLeaf_spec {G : Sym3Graph 5} (h : certLeaf G.edges = true) :
    gVal G ≤ 672 - 104 * (edgeGraph.flagCountC G : ℤ)
      ∨ G.toModel.Contains tetra := by
  have hEf : G.edges.filter (fun e => e.card = 3) = G.edges :=
    Finset.filter_true_of_mem G.edges_valid
  have hGf : (⟨G.edges.filter fun e => e.card = 3,
      fun _ he => (Finset.mem_filter.mp he).2⟩ : Sym3Graph 5) = G :=
    Sym3Graph.ext hEf
  rw [certLeaf, hGf, hEf, gFast_eq_gVal, ← edge_flagCountC_eq_card] at h
  exact of_decide_eq_true h

/-- Every slack is nonnegative: the table discharges the certificate. -/
theorem slackC_nonneg : ∀ H, 0 ≤ slackC H := by
  intro H
  obtain ⟨G, hG, rfl⟩ := exists_sym3Graph_toFlag
    (fun M (hM : TetraFree.Mem M) => hM.1) H
  refine slackC_nonneg_of_check hG ?_
  rcases certLeaf_spec (forall_sym3Graph_of_allEdgeSetsSat
    (P := certLeaf) certTable G) with h | h
  · exact h
  · exact absurd h hG.2

/-- **The conditional order-5 certificate assembly**: nonnegative
per-class slacks give the bound `⟦edge⟧ ≤ (42/65) • 1`. -/
theorem edge_le_of_slackC_nonneg (hd : ∀ H, 0 ≤ slackC H) :
    (⟦basisVector (⟨3, edgeGraph.toFlag edgeGraph_mem⟩ :
        FinFlag TetraFree emptyType)⟧ :
      FlagAlgebra TetraFree emptyType)
      ≤ (42 / 65 : ℝ) • 1 := by
  refine le_smul_one_of_sos_decomp
    (Finset.univ : Finset (Fin 1)) (Finset.univ)
    (fun _ => (3 / 26 : ℝ)) (fun _ _ => by norm_num)
    (fun _ => xCert)
    slackC (fun H _ => hd H)
    (fun H => ⟦basisVector ⟨5, H⟩⟧) (fun H _ => flag_nonneg _)
    _ ?_
  rw [Fin.sum_univ_one, downward_xCert_sq,
    basisVector_quot_eq_sum
      (⟨3, edgeGraph.toFlag edgeGraph_mem⟩ : FinFlag TetraFree emptyType)
      5 (by norm_num),
    ← sum_flagWithSize_eq_one (𝕋 := TetraFree) (σ := emptyType) 5
      (by simp),
    Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [smul_smul, ← add_smul, ← add_smul]
  congr 1
  rw [slackC]
  ring

/-- **The order-5 semidefinite bound** (the first fully formalized
hypergraph SOS bound beyond pure averaging): in the tetrahedron-free
theory the edge flag is at most `42/65 ≈ 0.6462` of the unit. -/
theorem edge_le_42_65 :
    (⟦basisVector (⟨3, edgeGraph.toFlag edgeGraph_mem⟩ :
        FinFlag TetraFree emptyType)⟧ :
      FlagAlgebra TetraFree emptyType)
      ≤ (42 / 65 : ℝ) • 1 :=
  edge_le_of_slackC_nonneg slackC_nonneg

/-- Every positive homomorphism assigns the edge flag a value at most
`42/65`. -/
theorem positiveHom_edge_le_42_65
    (φ : PositiveHom TetraFree emptyType) :
    φ ⟦basisVector (⟨3, edgeGraph.toFlag edgeGraph_mem⟩ :
        FinFlag TetraFree emptyType)⟧ ≤ 42 / 65 := by
  have h := edge_le_42_65 φ
  rw [PositiveHom.map_sub, PositiveHom.map_smul, PositiveHom.map_one] at h
  linarith

end FlagAlgebras.Core.Tetrahedron
