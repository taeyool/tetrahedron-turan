import LeanFlagAlgebras.Core.SquarePositivity
import LeanFlagAlgebras.Core.Forbid
import LeanFlagAlgebras.Core.Instances.Hypergraph3
import LeanFlagAlgebras.Core.Compute.Sym3
import LeanFlagAlgebras.Core.Compute.Sym3Downward
import Mathlib.Tactic.Linarith

/-! # Core example: the averaging bound for tetrahedron-free 3-graphs

The first fully formalized hypergraph flag-algebra bound: in the theory of
`K₄⁽³⁾`-free 3-uniform hypergraphs, the edge flag is at most `3/4` of the
unit in the semantic order of the flag algebra, hence every positive
homomorphism assigns the edge density a value `≤ 3/4`.

The proof is the pure averaging argument, run end-to-end through the
generic stack: expand the edge over the 4-vertex flags
(`basisVector_quot_eq_sum`, the chain rule in algebra form), bound each
coefficient by `3/4` — a 4-vertex flag with all four hyperedges would *be*
a tetrahedron, contradicting membership in the forbidding theory — and
collapse the remaining sum with the normalization
`sum_flagWithSize_eq_one`. No squares, no computation: every step is
structural, exercising the theory instance, padding, flags, densities,
chain rules, algebra, and order layers together. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

/-- The complete 3-uniform hypergraph on `V`: every injective triple is a
hyperedge. -/
abbrev complete3 (V : Type) : Model hypergraph3Sig V where
  interp _ g := Function.Injective g

lemma complete3_isUniform (V : Type) : (complete3 V).IsUniform :=
  fun _ => ⟨fun e g => Equiv.injective_comp e g, fun _ hg => hg⟩

/-- The tetrahedron pattern `K₄⁽³⁾`: the complete 3-graph on four
vertices. -/
abbrev tetra : Model hypergraph3Sig (Fin 4) := complete3 (Fin 4)

lemma tetra_noIsolated : tetra.NoIsolated := by
  unfold Model.NoIsolated
  decide

/-- Freeness witnesses at every size, via the discrete model. -/
lemma tetra_free_inhabited :
    ∀ n : ℕ, ∃ M : Model hypergraph3Sig (Fin n),
      THypergraph3.Mem M ∧ ¬M.Contains tetra :=
  forbid_inhabited_of_discrete THypergraph3
    (fun _ => Model.discrete_isUniform) ⟨(), ![0, 1, 2], by decide⟩

/-- The theory of tetrahedron-free 3-uniform hypergraphs. -/
def TetraFree : RelTheory hypergraph3Sig :=
  THypergraph3.forbid tetra tetra_free_inhabited

instance : THypergraph3.PadClosed :=
  inferInstanceAs (uniformTheory hypergraph3Sig).PadClosed

instance : TetraFree.PadClosed :=
  RelTheory.forbid_padClosed tetra_noIsolated

/-- The empty type: no labels (the generic empty type, specialized). -/
abbrev emptyType : Model hypergraph3Sig (Fin 0) :=
  FlagAlgebras.Core.emptyType hypergraph3Sig

instance : TetraFree.IsType emptyType where
  mem := ⟨Model.discrete_isUniform, fun ⟨f, _⟩ => (f 0).elim0⟩

/-- The edge flag: a single hyperedge on three vertices, as an unlabeled
flag of the tetrahedron-free theory. -/
def edgeFlag : LabeledFlag TetraFree emptyType (Fin 3) :=
  LabeledFlag.ofEmptyType
    ⟨complete3_isUniform (Fin 3), fun ⟨f, _⟩ =>
      absurd (Fintype.card_le_of_embedding f) (by decide)⟩

/-- A 4-vertex flag of the tetrahedron-free theory has at most three of its
four triples as hyperedges: were all four subsets witnesses of the edge
flag, the flag itself would contain a tetrahedron. -/
lemma flagCount_edge_le (G : LabeledFlag TetraFree emptyType (Fin 4)) :
    flagCount edgeFlag G ≤ 3 := by
  by_contra hlt
  push_neg at hlt
  have hle := flagCount_le_choose edgeFlag G
  rw [show (Fintype.card (Fin 4) - Fintype.card (Fin 0)).choose
      (Fintype.card (Fin 3) - Fintype.card (Fin 0)) = 4 from by decide] at hle
  have hsub : flagWitnesses edgeFlag G ⊆ Finset.univ.powersetCard 3 := by
    intro W hW
    obtain ⟨-, hcard, -⟩ := mem_flagWitnesses.mp hW
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, by simpa using hcard⟩
  have hall : flagWitnesses edgeFlag G = Finset.univ.powersetCard 3 := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [show (Finset.univ.powersetCard 3 : Finset (Finset (Fin 4))).card = 4
      from by rw [Finset.card_powersetCard, Finset.card_univ]; decide]
    exact hlt
  have hedge : ∀ g : Fin 3 → Fin 4, Function.Injective g →
      G.toModel.interp () g := by
    intro g hg
    have hgW : ∀ j, g j ∈ Finset.univ.image g :=
      fun j => Finset.mem_image_of_mem g (Finset.mem_univ j)
    have hWmem : Finset.univ.image g ∈ flagWitnesses edgeFlag G := by
      rw [hall]
      refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_image_of_injective _ hg, Finset.card_univ]
      decide
    obtain ⟨hroot, -, ⟨i⟩⟩ := mem_flagWitnesses.mp hWmem
    have hĝinj : Function.Injective
        (fun j => (⟨g j, hgW j⟩ : {x // x ∈ Finset.univ.image g})) :=
      fun a b hab => hg (congrArg Subtype.val hab)
    have h1 : edgeFlag.toModel.interp ()
        (i.toIso.toEquiv ∘ fun j => ⟨g j, hgW j⟩) :=
      i.toIso.toEquiv.injective.comp hĝinj
    exact (i.toIso.interp_iff () (fun j => ⟨g j, hgW j⟩)).mp h1
  refine G.mem.2 ⟨Function.Embedding.refl (Fin 4), fun r g hginj => ?_⟩
  exact hedge g hginj

/-- The edge density of any 4-vertex flag of the tetrahedron-free theory is
at most `3/4`. -/
lemma subflagDensity_edge_le (F' : FlagWithSize TetraFree emptyType 4) :
    subflagDensity edgeFlag.toFlag F' ≤ 3 / 4 := by
  refine Quotient.inductionOn F' fun G => ?_
  show flagDensity edgeFlag G ≤ 3 / 4
  rw [flagDensity,
    show (Fintype.card (Fin 4) - Fintype.card (Fin 0)).choose
      (Fintype.card (Fin 3) - Fintype.card (Fin 0)) = 4 from by decide]
  have h3 : (flagCount edgeFlag G : ℚ) ≤ 3 := by
    exact_mod_cast flagCount_edge_le G
  push_cast
  linarith

/-- **The averaging bound** (the S1 pipeline demonstration): in the
tetrahedron-free theory the edge flag is at most `3/4` of the unit in the
semantic order of the flag algebra. -/
theorem edge_le_three_quarters :
    (⟦basisVector (⟨3, edgeFlag.toFlag⟩ : FinFlag TetraFree emptyType)⟧ :
        FlagAlgebra TetraFree emptyType)
      ≤ (3 / 4 : ℝ) • 1 := by
  rw [basisVector_quot_eq_sum
      (⟨3, edgeFlag.toFlag⟩ : FinFlag TetraFree emptyType) 4 (by decide),
    ← sum_flagWithSize_eq_one (𝕋 := TetraFree) (σ := emptyType) 4 (by decide),
    Finset.smul_sum]
  refine flag_sum_le_sum fun F' _ => ?_
  refine flag_smul_le_smul ?_ (flag_nonneg _)
  calc ((subflagDensity edgeFlag.toFlag F' : ℚ) : ℝ)
      ≤ ((3 / 4 : ℚ) : ℝ) := by exact_mod_cast subflagDensity_edge_le F'
    _ = 3 / 4 := by norm_num

/-- Every positive homomorphism of the tetrahedron-free flag algebra
assigns the edge flag a value at most `3/4`. -/
theorem positiveHom_edge_le (φ : PositiveHom TetraFree emptyType) :
    φ ⟦basisVector (⟨3, edgeFlag.toFlag⟩ : FinFlag TetraFree emptyType)⟧
      ≤ 3 / 4 := by
  have h := edge_le_three_quarters φ
  rw [PositiveHom.map_sub, PositiveHom.map_smul, PositiveHom.map_one] at h
  linarith

/-! ## Nonzero types

The two label types the `K₄⁽³⁾` semidefinite certificates quantify over:
a single labeled vertex and a labeled hyperedge. Each is a
tetrahedron-free model in its own right, so it is a type of the theory
and carries its own flag algebra `A^σ`, with the downward (averaging)
operator back into the unlabeled algebra. -/

/-- The vertex type: one labeled vertex, no hyperedges. -/
abbrev vertexType : Model hypergraph3Sig (Fin 1) :=
  Model.discrete hypergraph3Sig (Fin 1)

instance : TetraFree.IsType vertexType where
  mem := ⟨Model.discrete_isUniform, fun ⟨f, _⟩ =>
    absurd (Fintype.card_le_of_embedding f) (by decide)⟩

/-- The edge type: three labeled vertices spanning one hyperedge. -/
abbrev edgeType : Model hypergraph3Sig (Fin 3) :=
  complete3 (Fin 3)

instance : TetraFree.IsType edgeType where
  mem := ⟨complete3_isUniform (Fin 3), fun ⟨f, _⟩ =>
    absurd (Fintype.card_le_of_embedding f) (by decide)⟩

/-- Square positivity, instantiated: any square in the vertex-typed
algebra averages to a nonnegative element of the unlabeled algebra. -/
example (x : FlagAlgebra TetraFree vertexType) :
    (0 : FlagAlgebra TetraFree emptyType) ≤ downward (x * x) :=
  downward_square_nonneg x

/-- Square positivity, instantiated at the edge type. -/
example (x : FlagAlgebra TetraFree edgeType) :
    (0 : FlagAlgebra TetraFree emptyType) ≤ downward (x * x) :=
  downward_square_nonneg x

/-! ## Executable theory membership

Membership of a computational 3-graph in the tetrahedron-free theory is
decidable by executable instances: uniformity unfolds to finite
quantifiers, and containment quantifies over plain functions with an
injectivity conjunct — avoiding the noncomputable `Fintype` of
embeddings. This is the filter predicate of the canonical flag listing
`sym3FlagReps`, and it kernel-evaluates (see the `decide` tests below). -/

instance {n : ℕ} (G : Sym3Graph n) : Decidable (G.toModel.Contains tetra) :=
  decidable_of_iff
    (∃ f : Fin 4 → Fin n, Function.Injective f ∧
      ∀ (r : Unit) (g : Fin 3 → Fin 4),
        tetra.interp r g → G.toModel.interp r (f ∘ g))
    ⟨fun ⟨f, hf, h⟩ => ⟨⟨f, hf⟩, h⟩,
     fun ⟨f, h⟩ => ⟨f, f.injective, h⟩⟩

instance {n : ℕ} (G : Sym3Graph n) : Decidable (TetraFree.Mem G.toModel) :=
  decidable_of_iff (G.toModel.IsUniform ∧ ¬G.toModel.Contains tetra) Iff.rfl

set_option maxRecDepth 8192 in
/-- The empty 3-graph is tetrahedron-free, by kernel computation. -/
example : TetraFree.Mem (Sym3Graph.mk (n := 4) ∅ (by decide)).toModel := by
  decide

set_option maxRecDepth 8192 in
/-- The complete 3-graph on four vertices contains the tetrahedron — it
*is* the tetrahedron — so it is not a member, by kernel computation. -/
example : ¬ TetraFree.Mem
    (Sym3Graph.mk (n := 4) (Finset.univ.powersetCard 3)
      (fun _ he => (Finset.mem_powersetCard.mp he).2)).toModel := by
  decide

set_option maxRecDepth 8192 in
/-- Three of the four triples on four vertices: a genuine tetrahedron-free
member with hyperedges, by kernel computation. -/
example : TetraFree.Mem
    (Sym3Graph.mk (n := 4) {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}}
      (by decide)).toModel := by
  decide

set_option maxRecDepth 65536 in
/-- The full literal pipeline in the kernel: of the five isomorphism
classes of 3-graphs on four vertices, exactly four are tetrahedron-free —
the complete one (the tetrahedron itself) is excluded. This is the
canonical listing of `FlagWithSize TetraFree emptyType 4`. -/
example : (sym3FlagReps TetraFree 4).length = 4 := by decide

/-! ## Literal density evaluation

Densities of literal flags computed in the kernel, connected to the
specification-layer `subflagDensity` by the agreement theorem. -/

/-- The single-hyperedge pattern on three vertices, as a literal. -/
def edgeGraph : Sym3Graph 3 := ⟨{{0, 1, 2}}, by decide⟩

set_option maxRecDepth 8192 in
lemma edgeGraph_mem : TetraFree.Mem edgeGraph.toModel := by decide

/-- The host with three of the four triples on four vertices. -/
def threeTriples : Sym3Graph 4 :=
  ⟨{{0, 1, 2}, {0, 1, 3}, {0, 2, 3}}, by decide⟩

set_option maxRecDepth 8192 in
lemma threeTriples_mem : TetraFree.Mem threeTriples.toModel := by decide

set_option maxRecDepth 8192 in
/-- The literal count kernel-computes: three of the four vertex triples
of the host induce a copy of the edge. -/
example : edgeGraph.flagCountC threeTriples = 3 := by decide

set_option maxRecDepth 8192 in
/-- **Literal density evaluation, end to end**: the edge density of the
three-triple host is exactly `3/4` — the kernel counts the witnesses, and
the agreement theorem lifts the count to the specification-layer
density. -/
example : subflagDensity (edgeGraph.toFlag edgeGraph_mem)
    (threeTriples.toFlag threeTriples_mem) = 3 / 4 := by
  rw [Sym3Graph.subflagDensity_toFlag,
    show edgeGraph.flagCountC threeTriples = 3 from by decide,
    show Nat.choose 4 3 = 4 from by decide]
  norm_num

/-- A single labeled-free vertex, as a literal. -/
def vertexGraph : Sym3Graph 1 := ⟨∅, by decide⟩

set_option maxRecDepth 8192 in
lemma vertexGraph_mem : TetraFree.Mem vertexGraph.toModel := by decide

set_option maxRecDepth 8192 in
/-- The literal pair count kernel-computes: each of the three edge copies
leaves exactly one disjoint vertex in the four-vertex host. -/
example : edgeGraph.flagPairCountC vertexGraph threeTriples = 3 := by decide

set_option maxRecDepth 8192 in
/-- Pair densities on literals, end to end: the (edge, vertex) pair
density of the three-triple host is `3/4`. -/
example : subflagPairDensity (edgeGraph.toFlag edgeGraph_mem)
    (vertexGraph.toFlag vertexGraph_mem)
    (threeTriples.toFlag threeTriples_mem) = 3 / 4 := by
  rw [Sym3Graph.subflagPairDensity_toFlag,
    show edgeGraph.flagPairCountC vertexGraph threeTriples = 3 from by decide,
    show pairChoose 4 3 1 = 4 from by decide]
  norm_num

/-! ## Typed literal flags

The literal edge type `edgeGraph.toModel` is itself a type of the
theory, so it carries a flag algebra; typed literal flags over it are
3-graphs with a root triple inducing the edge. -/

instance : TetraFree.IsType edgeGraph.toModel := ⟨edgeGraph_mem⟩

/-- The full S2 machinery instantiates over the literal type: square
positivity in the algebra of edge-rooted flags. -/
example (x : FlagAlgebra TetraFree edgeGraph.toModel) :
    (0 : FlagAlgebra TetraFree emptyType) ≤ downward (x * x) :=
  downward_square_nonneg x

/-- The three-triple host rooted at its first edge. -/
def rootedThreeTriples : Sym3Flag 3 4 := ⟨threeTriples, ![0, 1, 2]⟩

/-- The same host rooted at its second edge. -/
def rootedThreeTriples' : Sym3Flag 3 4 := ⟨threeTriples, ![0, 1, 3]⟩

set_option maxRecDepth 8192 in
lemma rootedThreeTriples_wf : rootedThreeTriples.WellFormed edgeGraph := by
  decide

set_option maxRecDepth 8192 in
lemma rootedThreeTriples'_wf : rootedThreeTriples'.WellFormed edgeGraph := by
  decide

set_option maxRecDepth 8192 in
/-- Typed flag classes decide in the kernel: the two rootings at
different edges give the *same* edge-rooted flag — the transposition
`2 ↔ 3` carries one to the other. -/
example : rootedThreeTriples.toFlag (𝕋 := TetraFree)
      rootedThreeTriples_wf threeTriples_mem
    = rootedThreeTriples'.toFlag rootedThreeTriples'_wf threeTriples_mem := by
  rw [Sym3Flag.toFlag_eq_toFlag_iff]
  decide

set_option maxRecDepth 32768 in
/-- The typed enumeration kernel-computes: on three vertices there is
exactly one edge-rooted tetrahedron-free flag class (the edge itself,
fully rooted). -/
example : (sym3TypedFlagReps TetraFree edgeGraph 3).length = 1 := by decide

set_option maxRecDepth 262144 in
set_option maxHeartbeats 8000000 in
/-- The SDP block index set at order four: exactly seven edge-rooted
tetrahedron-free flag classes on four vertices — the extra vertex forms
any subset of the three triples through pairs of roots, except all three
(which would close a tetrahedron): `2³ − 1 = 7`. -/
example : (sym3TypedFlagReps TetraFree edgeGraph 4).length = 7 := by decide

/-! ## Typed literal densities -/

/-- The edge-rooted pattern whose extra vertex forms one triple through
the first two roots. -/
def edgeExtOne : Sym3Flag 3 4 := ⟨⟨{{0, 1, 2}, {0, 1, 3}}, by decide⟩, ![0, 1, 2]⟩

/-- A five-vertex host: the rooted edge plus two further triples through
the first two roots. -/
def edgeStar : Sym3Flag 3 5 :=
  ⟨⟨{{0, 1, 2}, {0, 1, 3}, {0, 1, 4}}, by decide⟩, ![0, 1, 2]⟩

set_option maxRecDepth 8192 in
lemma edgeExtOne_wf : edgeExtOne.WellFormed edgeGraph := by decide

set_option maxRecDepth 8192 in
lemma edgeStar_wf : edgeStar.WellFormed edgeGraph := by decide

set_option maxRecDepth 8192 in
lemma edgeExtOne_mem : TetraFree.Mem edgeExtOne.graph.toModel := by decide

set_option maxRecDepth 16384 in
lemma edgeStar_mem : TetraFree.Mem edgeStar.graph.toModel := by decide

set_option maxRecDepth 16384 in
/-- The typed count kernel-computes: both root-containing 4-subsets of
the star induce the one-extra-triple pattern. -/
example : edgeExtOne.flagCountC edgeStar = 2 := by decide

set_option maxRecDepth 16384 in
/-- **Typed literal density, end to end**: in the star host every
root-containing extension realizes the pattern — density `1`. -/
example : subflagDensity (edgeExtOne.toFlag edgeExtOne_wf edgeExtOne_mem)
    (edgeStar.toFlag edgeStar_wf edgeStar_mem) = 1 := by
  have h1 : edgeExtOne.flagCountC edgeStar = 2 := by decide
  have h2 : Nat.choose (5 - 3) (4 - 3) = 2 := by decide
  rw [Sym3Flag.subflagDensity_toFlag, h1, h2]
  norm_num

set_option maxRecDepth 16384 in
/-- The typed pair count kernel-computes: the two extensions of the star
split into an ordered pair of witnesses in both orders. -/
example : edgeExtOne.flagPairCountC edgeExtOne edgeStar = 2 := by decide

set_option maxRecDepth 16384 in
/-- **Typed pair density, end to end**: the quadratic-form coefficient
`p₂` of the one-extra-triple pattern with itself in the star host is
`1`, computed in the kernel. -/
example : subflagPairDensity
    (edgeExtOne.toFlag edgeExtOne_wf edgeExtOne_mem)
    (edgeExtOne.toFlag edgeExtOne_wf edgeExtOne_mem)
    (edgeStar.toFlag edgeStar_wf edgeStar_mem) = 1 := by
  have h1 : edgeExtOne.flagPairCountC edgeExtOne edgeStar = 2 := by decide
  have h2 : pairChoose (5 - 3) (4 - 3) (4 - 3) = 2 := by decide
  rw [Sym3Flag.subflagPairDensity_toFlag, h1, h2]
  norm_num

/-! ## The Cauchy–Schwarz inequality on typed literals

The S2 capstone: Razborov's Cauchy–Schwarz inequality — proved from
measure-free square positivity by the discriminant argument — applied
to an edge-rooted literal flag of the tetrahedron-free theory. -/

/-- The one-extra-triple flag as an element of the edge-typed algebra. -/
noncomputable def edgeExtOneElt : FlagAlgebra TetraFree edgeGraph.toModel :=
  ⟦basisVector ⟨4, edgeExtOne.toFlag edgeExtOne_wf edgeExtOne_mem⟩⟧

/-- Cauchy–Schwarz for the edge-rooted literal: under every positive
homomorphism, the squared averaged density of the one-extra-triple flag
is at most the averaged density of its square. -/
example (φ : PositiveHom TetraFree emptyType) :
    φ (downward edgeExtOneElt) ^ 2
      ≤ φ (downward (edgeExtOneElt * edgeExtOneElt)) :=
  positiveHom_downward_sq_le φ edgeExtOneElt

/-- The full Cauchy–Schwarz form, with the downward unit. -/
example (φ : PositiveHom TetraFree emptyType) :
    φ (downward edgeExtOneElt) ^ 2
      ≤ φ (downward (edgeExtOneElt * edgeExtOneElt))
        * φ (downward (1 : FlagAlgebra TetraFree edgeGraph.toModel)) :=
  positiveHom_downward_cauchy_schwarz φ edgeExtOneElt

/-! ## The downward operator on literals -/

set_option maxRecDepth 16384 in
/-- The labeling count kernel-computes: of the twelve root orderings
along edges of the one-extra-triple graph, exactly the four in the
automorphism orbit of the base rooting realize the typed class — the
orderings matter, roots are matched pointwise. -/
example : edgeExtOne.labelingCountC edgeGraph = 4 := by decide

set_option maxRecDepth 16384 in
/-- **The first fully evaluated downward image**: the one-extra-triple
flag averages to a *sixth* of its unlabeled class — four of the
`(4)₃ = 24` root placements realize the edge-rooted structure. -/
example : downward edgeExtOneElt
    = (1 / 6 : ℝ) • ⟦basisVector
        ⟨4, Sym3Graph.toFlag edgeExtOne.graph edgeExtOne_mem⟩⟧ := by
  rw [edgeExtOneElt, Sym3Flag.downward_basisVector edgeExtOne_wf
    edgeExtOne_mem]
  have h1 : edgeExtOne.labelingCountC edgeGraph = 4 := by decide
  have h2 : Nat.descFactorial 4 3 = 24 := by decide
  rw [h1, h2]
  norm_num

set_option maxRecDepth 32768 in
/-- The labeling count of the star: the automorphism orbit of the base
rooting has six elements (swap the root pair, permute the apexes). -/
example : edgeStar.labelingCountC edgeGraph = 6 := by decide

set_option maxRecDepth 32768 in
/-- The star averages to a tenth of its unlabeled class: six of the
`(5)₃ = 60` root placements. -/
example : downward (⟦basisVector
      ⟨5, edgeStar.toFlag edgeStar_wf edgeStar_mem⟩⟧ :
      FlagAlgebra TetraFree edgeGraph.toModel)
    = (1 / 10 : ℝ) • ⟦basisVector
        ⟨5, Sym3Graph.toFlag edgeStar.graph edgeStar_mem⟩⟧ := by
  rw [Sym3Flag.downward_basisVector edgeStar_wf edgeStar_mem]
  have h1 : edgeStar.labelingCountC edgeGraph = 6 := by decide
  have h2 : Nat.descFactorial 5 3 = 60 := by decide
  rw [h1, h2]
  norm_num

/-- **The product table shape**: the downward square of the
one-extra-triple flag expands over the level-5 typed classes with
pair-density coefficients — each summand now a literal-evaluable
quantity (`subflagPairDensity` by `flagPairCountC`, the downward basis
by `labelingCountC`). -/
example : downward (edgeExtOneElt * edgeExtOneElt)
    = ∑ H : FlagWithSize TetraFree edgeGraph.toModel 5,
        ((subflagPairDensity
            (edgeExtOne.toFlag edgeExtOne_wf edgeExtOne_mem)
            (edgeExtOne.toFlag edgeExtOne_wf edgeExtOne_mem) H : ℚ) : ℝ)
          • downward ⟦basisVector ⟨5, H⟩⟧ :=
  downward_basisVector_mul _ _ (by simp)

/-! ## The order-5 averaging bound

The first stage of the order-5 assembly: expand the edge over the
five-vertex classes and bound every coefficient in the kernel. A
tetrahedron-free 3-graph on five vertices has at most seven hyperedges
— eight force a tetrahedron — so the edge density is at most `7/10`,
strictly below the order-4 averaging bound `3/4`. -/

/-- Containment of a pattern is monotone in the edge set. -/
lemma Sym3Graph.contains_mono {n : ℕ} {G H : Sym3Graph n}
    (hsub : G.edges ⊆ H.edges) {V₀ : Type} {P : Model hypergraph3Sig V₀}
    (h : G.toModel.Contains P) : H.toModel.Contains P := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, fun r g hg => ?_⟩
  obtain ⟨hinj, hmem⟩ := hf r g hg
  exact ⟨hinj, hsub hmem⟩

/-- Edge-witnesses are edges: the count is bounded by the edge count. -/
lemma edge_flagCountC_le_card {n : ℕ} (G : Sym3Graph n) :
    edgeGraph.flagCountC G ≤ G.edges.card := by
  rw [Sym3Graph.flagCountC]
  refine Finset.card_le_card_of_injOn (fun W => W.val) ?_ ?_
  · intro W hW
    obtain ⟨p, hp⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hW)).2
    have he₀ : ({0, 1, 2} : Finset (Fin 3)) ∈ edgeGraph.edges := by decide
    have hmem : ({0, 1, 2} : Finset (Fin 3)).image ⇑p
        ∈ (G.pullback (subsetTuple W.val
          (Finset.mem_powersetCard.mp W.property).2)).edges := by
      rw [← hp]
      exact Finset.mem_image_of_mem _ he₀
    obtain ⟨-, -, hGe⟩ := Finset.mem_filter.mp hmem
    have huniv : ({0, 1, 2} : Finset (Fin 3)).image ⇑p = Finset.univ := by
      refine Finset.eq_univ_of_card _ ?_
      rw [Finset.card_image_of_injective _ p.injective]
      decide
    rw [huniv, subsetTuple_image_univ] at hGe
    exact Finset.mem_coe.mpr hGe
  · intro W₁ _ W₂ _ heq
    exact Subtype.ext heq

private lemma complement_valid (R : Finset (Finset (Fin 5))) :
    ∀ e ∈ (allTriples 5).toFinset \ R, e.card = 3 := fun _ he =>
  mem_allTriples.mp (List.mem_toFinset.mp (Finset.mem_sdiff.mp he).1)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
/-- The kernel table: deleting at most two triples from the complete
edge set on five vertices always leaves a tetrahedron. One hundred
shallow containment checks, each on a graph with at least eight
edges. -/
lemma pair_complement_contains :
    ∀ t₁ ∈ allTriples 5, ∀ t₂ ∈ allTriples 5,
      (Sym3Graph.mk ((allTriples 5).toFinset \ {t₁, t₂})
        (complement_valid _)).toModel.Contains tetra := by decide

/-- Eight edges on five vertices leave a complement covered by two
triples. -/
lemma exists_pair_complement {G : Sym3Graph 5} (h8 : 8 ≤ G.edges.card) :
    ∃ t₁ ∈ allTriples 5, ∃ t₂ ∈ allTriples 5,
      (allTriples 5).toFinset \ {t₁, t₂} ⊆ G.edges := by
  have hsubT : G.edges ⊆ (allTriples 5).toFinset := fun e he =>
    List.mem_toFinset.mpr (mem_allTriples.mpr (G.edges_valid e he))
  set C := (allTriples 5).toFinset \ G.edges with hC
  have hCcard : C.card ≤ 2 := by
    have h10 : (allTriples 5).toFinset.card = 10 := by decide
    have hsd : C.card = (allTriples 5).toFinset.card
        - (G.edges ∩ (allTriples 5).toFinset).card := Finset.card_sdiff
    rw [Finset.inter_eq_left.mpr hsubT] at hsd
    omega
  have hdef : ({0, 1, 2} : Finset (Fin 5)) ∈ allTriples 5 :=
    mem_allTriples.mpr (by decide)
  obtain ⟨t₁, t₂, hcover, ht₁, ht₂⟩ :
      ∃ t₁ t₂, C ⊆ {t₁, t₂} ∧ t₁ ∈ allTriples 5 ∧ t₂ ∈ allTriples 5 := by
    rcases Finset.eq_empty_or_nonempty C with hE | ⟨t₁, ht₁⟩
    · exact ⟨_, _, by rw [hE]; exact Finset.empty_subset _, hdef, hdef⟩
    have ht₁T : t₁ ∈ allTriples 5 :=
      List.mem_toFinset.mp (Finset.mem_sdiff.mp ht₁).1
    rcases Finset.eq_empty_or_nonempty (C.erase t₁) with hE | ⟨t₂, ht₂⟩
    · refine ⟨t₁, t₁, fun x hx => ?_, ht₁T, ht₁T⟩
      have hxt : x = t₁ := by
        by_contra hne
        exact absurd (Finset.mem_erase.mpr ⟨hne, hx⟩)
          (by rw [hE]; exact Finset.notMem_empty x)
      simp [hxt]
    have ht₂T : t₂ ∈ allTriples 5 :=
      List.mem_toFinset.mp
        (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase ht₂)).1
    refine ⟨t₁, t₂, fun x hx => ?_, ht₁T, ht₂T⟩
    by_cases hx1 : x = t₁
    · simp [hx1]
    by_cases hx2 : x = t₂
    · simp [hx2]
    have hx' : x ∈ (C.erase t₁).erase t₂ :=
      Finset.mem_erase.mpr ⟨hx2, Finset.mem_erase.mpr ⟨hx1, hx⟩⟩
    have hc1 := Finset.card_erase_of_mem ht₁
    have hc2 := Finset.card_erase_of_mem ht₂
    have hpos := Finset.card_pos.mpr ⟨x, hx'⟩
    omega
  refine ⟨t₁, ht₁, t₂, ht₂, fun x hx => ?_⟩
  obtain ⟨hxT, hxnot⟩ := Finset.mem_sdiff.mp hx
  by_contra hxe
  exact hxnot (hcover (Finset.mem_sdiff.mpr ⟨hxT, hxe⟩))

/-- A tetrahedron-free host on five vertices carries at most seven
edge-witnesses. -/
lemma edge_flagCountC_le_seven {G : Sym3Graph 5}
    (hG : TetraFree.Mem G.toModel) : edgeGraph.flagCountC G ≤ 7 := by
  have hcard : G.edges.card ≤ 7 := by
    by_contra h
    push_neg at h
    obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := exists_pair_complement h
    exact hG.2 (Sym3Graph.contains_mono hsub
      (pair_complement_contains t₁ ht₁ t₂ ht₂))
  exact le_trans (edge_flagCountC_le_card G) hcard

/-- **The order-5 averaging bound**: in the tetrahedron-free theory the
edge flag is at most `7/10` of the unit — strictly better than the
order-4 bound `3/4`. -/
theorem edge_le_seven_tenths :
    (⟦basisVector (⟨3, edgeGraph.toFlag edgeGraph_mem⟩ :
        FinFlag TetraFree emptyType)⟧ : FlagAlgebra TetraFree emptyType)
      ≤ (((7 : ℚ)/10 : ℚ) : ℝ) • 1 := by
  refine basisVector_quot_le_smul_one _ 5 (by norm_num) (by simp)
    fun H => ?_
  obtain ⟨G, hG, rfl⟩ := exists_sym3Graph_toFlag
    (fun M (hM : TetraFree.Mem M) => hM.1) H
  rw [Sym3Graph.subflagDensity_toFlag,
    show Nat.choose 5 3 = 10 from by decide]
  have h' : (edgeGraph.flagCountC G : ℚ) ≤ 7 := by
    exact_mod_cast edge_flagCountC_le_seven hG
  refine (div_le_div_iff₀ (by norm_num) (by norm_num)).mpr ?_
  push_cast
  linarith

/-- Every positive homomorphism assigns the edge flag a value at most
`7/10`. -/
theorem positiveHom_edge_le_seven_tenths
    (φ : PositiveHom TetraFree emptyType) :
    φ ⟦basisVector (⟨3, edgeGraph.toFlag edgeGraph_mem⟩ :
        FinFlag TetraFree emptyType)⟧ ≤ 7 / 10 := by
  have h := edge_le_seven_tenths φ
  rw [PositiveHom.map_sub, PositiveHom.map_smul, PositiveHom.map_one] at h
  push_cast at h
  linarith

/-- The canonical listing of the tetrahedron-free flag classes elaborates:
the decidability instances above feed the filter. -/
noncomputable example (n : ℕ) : List (Flag TetraFree emptyType (Fin n)) :=
  sym3FlagReps TetraFree n

/-- Every tetrahedron-free flag class on four vertices appears in the
canonical listing. -/
example (F : Flag TetraFree emptyType (Fin 4)) :
    F ∈ sym3FlagReps TetraFree 4 :=
  mem_sym3FlagReps TetraFree (fun _ hM => hM.1) F

end FlagAlgebras.Core.Tetrahedron
