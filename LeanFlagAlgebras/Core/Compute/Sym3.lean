import LeanFlagAlgebras.Core.Instances.Hypergraph3
import LeanFlagAlgebras.Core.JointDensity
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Core compute layer: 3-uniform hypergraphs on `Fin n`

The computational representation behind the 3-graph instance: hyperedges as
3-element `Finset (Fin n)`s, with decidable equality and decidable model
interpretation — the form that kernel-`decide` enumeration and isomorphism
checking will consume.

The bridge to the specification layer: `Sym3Graph.toModel` factors through
`ofTripleSet` (so theory membership is inherited), and is injective — the
computational representation is faithful.

Following the roadmap, the abstract "compute instance" interface is extracted
only once a second consumer exists; this file is deliberately concrete. -/

namespace FlagAlgebras.Core

variable {n : ℕ}

/-- A computational 3-uniform hypergraph on `Fin n`: a set of 3-element
hyperedges. The counterpart of the 2-graph stack's `Sym2Graph`. -/
structure Sym3Graph (n : ℕ) where
  /-- The hyperedges. -/
  edges : Finset (Finset (Fin n))
  /-- Every hyperedge has exactly three vertices. -/
  edges_valid : ∀ e ∈ edges, e.card = 3

@[ext]
lemma Sym3Graph.ext {G H : Sym3Graph n} (h : G.edges = H.edges) : G = H := by
  cases G
  cases H
  subst h
  rfl

instance : DecidableEq (Sym3Graph n) := fun G H =>
  decidable_of_iff (G.edges = H.edges)
    ⟨fun h => Sym3Graph.ext h, fun h => congrArg Sym3Graph.edges h⟩

/-- The model of a computational 3-graph: a triple is a hyperedge iff it is
injective and its vertex set is an edge. -/
def Sym3Graph.toModel (G : Sym3Graph n) : Model hypergraph3Sig (Fin n) where
  interp _ f := Function.Injective f ∧ Finset.univ.image f ∈ G.edges

instance (G : Sym3Graph n) (r : hypergraph3Sig.Rel) (f : Fin 3 → Fin n) :
    Decidable ((G.toModel).interp r f) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Membership in the 3-uniform hypergraph theory is decidable for
computational 3-graphs (unfold `IsUniform` to its finite quantifiers). -/
instance (G : Sym3Graph n) : Decidable (G.toModel.IsUniform) :=
  decidable_of_iff
    (∀ r : Unit, (∀ (e : Equiv.Perm (Fin 3)) (f : Fin 3 → Fin n),
        G.toModel.interp r (f ∘ e) ↔ G.toModel.interp r f)
      ∧ ∀ f : Fin 3 → Fin n, G.toModel.interp r f → Function.Injective f)
    Iff.rfl

/-- Every index in `Fin 3` is `0`, `1` or `2`. -/
private lemma fin_three : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

/-- A tuple of three distinct values is injective. -/
lemma vec3_injective {α : Type} {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : Function.Injective ![a, b, c] := by
  intro i j hij
  rcases fin_three i with rfl | rfl | rfl <;>
    rcases fin_three j with rfl | rfl | rfl <;> simp_all

/-- The image of a three-element tuple is the corresponding vertex set. -/
lemma image_vec3 {α : Type} [DecidableEq α] (a b c : α) :
    Finset.univ.image ![a, b, c] = {a, b, c} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    rcases fin_three i with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-- The computational model is the edge-set model of the coerced edge
family. -/
lemma Sym3Graph.toModel_eq_ofTripleSet (G : Sym3Graph n) :
    G.toModel = ofTripleSet {s | ∃ e ∈ G.edges, (e : Set (Fin n)) = s} := by
  refine Model.ext ?_
  funext r f
  show (Function.Injective f ∧ Finset.univ.image f ∈ G.edges)
    = (Function.Injective f ∧ Set.range f ∈ _)
  have hcoe : (↑(Finset.univ.image f) : Set (Fin n)) = Set.range f := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  apply propext
  refine and_congr_right fun _ => ⟨fun h => ⟨_, h, hcoe⟩, ?_⟩
  rintro ⟨e, he, hes⟩
  have : e = Finset.univ.image f := Finset.coe_injective (by rw [hes, hcoe])
  rwa [← this]

/-- The computational model satisfies the 3-uniform hypergraph theory. -/
lemma Sym3Graph.toModel_mem (G : Sym3Graph n) : THypergraph3.Mem G.toModel :=
  G.toModel_eq_ofTripleSet ▸ ofTripleSet_mem _

/-- Computational isomorphism: some permutation of the vertices carries the
edges of `G` onto the edges of `H`. Decidable, since the permutations of
`Fin n` form a `Fintype`. -/
def Sym3Graph.IsIso (G H : Sym3Graph n) : Prop :=
  ∃ p : Equiv.Perm (Fin n), G.edges.image (Finset.image ⇑p) = H.edges

instance (G H : Sym3Graph n) : Decidable (G.IsIso H) :=
  decidable_of_iff
    (∃ p : Equiv.Perm (Fin n), G.edges.image (Finset.image ⇑p) = H.edges)
    Iff.rfl

/-- The model isomorphism of an edge-carrying permutation; the underlying
equivalence is the permutation itself, definitionally. -/
def Sym3Graph.modelIsoOfPerm {G H : Sym3Graph n} (p : Equiv.Perm (Fin n))
    (hp : G.edges.image (Finset.image ⇑p) = H.edges) :
    G.toModel ≃ᵣ H.toModel :=
  ⟨p, fun r f => by
    show (Function.Injective (⇑p ∘ f) ∧ Finset.univ.image (⇑p ∘ f) ∈ H.edges)
      ↔ (Function.Injective f ∧ Finset.univ.image f ∈ G.edges)
    refine and_congr ⟨fun h => h.of_comp, fun h => p.injective.comp h⟩ ?_
    rw [← hp, ← Finset.image_image]
    constructor
    · intro h
      obtain ⟨Y, hY, hYX⟩ := Finset.mem_image.mp h
      rwa [← Finset.image_injective p.injective hYX]
    · exact fun h => Finset.mem_image_of_mem _ h⟩

/-- Any model isomorphism carries the edge set onto the edge set. -/
lemma Sym3Graph.image_edges_of_modelIso {G H : Sym3Graph n}
    (e : G.toModel ≃ᵣ H.toModel) :
    G.edges.image (Finset.image ⇑e.toEquiv) = H.edges := by
  ext X
  constructor
  · intro hX
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ :=
      Finset.card_eq_three.mp (G.edges_valid _ hY)
    have hint : (G.toModel).interp () ![a, b, c] :=
      ⟨vec3_injective hab hac hbc, by rw [image_vec3]; exact hY⟩
    have hint' := (e.interp_iff () ![a, b, c]).mpr hint
    have hcomp : ⇑e.toEquiv ∘ ![a, b, c]
        = ![e.toEquiv a, e.toEquiv b, e.toEquiv c] := by
      funext i
      rcases fin_three i with rfl | rfl | rfl <;> rfl
    rw [hcomp] at hint'
    obtain ⟨-, himg⟩ := hint'
    rw [image_vec3] at himg
    have himage : ({a, b, c} : Finset (Fin n)).image ⇑e.toEquiv
        = {e.toEquiv a, e.toEquiv b, e.toEquiv c} := by
      simp [Finset.image_insert]
    rwa [himage]
  · intro hX
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ :=
      Finset.card_eq_three.mp (H.edges_valid _ hX)
    have hint : (H.toModel).interp () ![a, b, c] :=
      ⟨vec3_injective hab hac hbc, by rw [image_vec3]; exact hX⟩
    have hint' := (e.interp_iff' () ![a, b, c]).mp hint
    have hcomp : ⇑e.toEquiv.symm ∘ ![a, b, c]
        = ![e.toEquiv.symm a, e.toEquiv.symm b, e.toEquiv.symm c] := by
      funext i
      rcases fin_three i with rfl | rfl | rfl <;> rfl
    rw [hcomp] at hint'
    obtain ⟨-, himg⟩ := hint'
    rw [image_vec3] at himg
    refine Finset.mem_image.mpr ⟨_, himg, ?_⟩
    simp [Finset.image_insert, Equiv.apply_symm_apply]

/-- The computational isomorphism test is complete for the semantic one:
`G.IsIso H` holds exactly when the models are isomorphic. -/
lemma Sym3Graph.isIso_iff_nonempty_modelIso (G H : Sym3Graph n) :
    G.IsIso H ↔ Nonempty (G.toModel ≃ᵣ H.toModel) :=
  ⟨fun ⟨p, hp⟩ => ⟨Sym3Graph.modelIsoOfPerm p hp⟩,
   fun ⟨e⟩ => ⟨e.toEquiv, Sym3Graph.image_edges_of_modelIso e⟩⟩

/-- Computational isomorphism is reflexive. -/
lemma Sym3Graph.IsIso.refl (G : Sym3Graph n) : G.IsIso G :=
  (Sym3Graph.isIso_iff_nonempty_modelIso G G).mpr ⟨ModelIso.refl _⟩

/-- Computational isomorphism is symmetric. -/
lemma Sym3Graph.IsIso.symm {G H : Sym3Graph n} (h : G.IsIso H) : H.IsIso G := by
  obtain ⟨e⟩ := (Sym3Graph.isIso_iff_nonempty_modelIso G H).mp h
  exact (Sym3Graph.isIso_iff_nonempty_modelIso H G).mpr ⟨e.symm⟩

/-- Computational isomorphism is transitive. -/
lemma Sym3Graph.IsIso.trans {G H K : Sym3Graph n} (h₁ : G.IsIso H)
    (h₂ : H.IsIso K) : G.IsIso K := by
  obtain ⟨e₁⟩ := (Sym3Graph.isIso_iff_nonempty_modelIso G H).mp h₁
  obtain ⟨e₂⟩ := (Sym3Graph.isIso_iff_nonempty_modelIso H K).mp h₂
  exact (Sym3Graph.isIso_iff_nonempty_modelIso G K).mpr ⟨e₁.trans e₂⟩

/-- The computational representation is faithful: the model determines the
edge set. -/
lemma Sym3Graph.toModel_injective :
    Function.Injective (Sym3Graph.toModel (n := n)) := by
  have haux : ∀ (G H : Sym3Graph n), G.toModel = H.toModel →
      ∀ e ∈ G.edges, e ∈ H.edges := by
    intro G H h e he
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ :=
      Finset.card_eq_three.mp (G.edges_valid _ he)
    have hint : (G.toModel).interp () ![a, b, c] :=
      ⟨vec3_injective hab hac hbc, by rw [image_vec3]; exact he⟩
    rw [h] at hint
    obtain ⟨-, himg⟩ := hint
    rwa [image_vec3] at himg
  intro G H h
  ext e
  exact ⟨haux G H h e, haux H G h.symm e⟩

/-! ### Canonical enumeration

Brute force over all edge sets with a verified deduplication — entirely
adequate for the small vertex counts of the first certificates; the
augmentation-based enumeration with keyed deduplication (as in the 2-graph
stack) is a later scaling concern. -/

/-- Keep one representative of every `r`-class of `l`. Coverage needs only
reflexivity of `r`. -/
def keepReps {α : Type} (r : α → α → Prop) [DecidableRel r] : List α → List α :=
  List.foldr
    (fun a acc => if acc.any fun b => decide (r a b) then acc else a :: acc) []

private lemma keepReps_coverage {α : Type} {r : α → α → Prop} [DecidableRel r]
    (hrefl : ∀ a, r a a) (l : List α) :
    ∀ a ∈ l, ∃ b ∈ keepReps r l, r a b := by
  induction l with
  | nil => intro a ha; simp at ha
  | cons x l ih =>
    intro a ha
    have hcons : keepReps r (x :: l)
        = if (keepReps r l).any (fun b => decide (r x b)) then keepReps r l
          else x :: keepReps r l := rfl
    rcases List.mem_cons.mp ha with rfl | hmem
    · by_cases hany : (keepReps r l).any (fun b => decide (r a b)) = true
      · rw [hcons, if_pos hany]
        obtain ⟨b, hb, hrb⟩ := List.any_eq_true.mp hany
        exact ⟨b, hb, of_decide_eq_true hrb⟩
      · rw [hcons, if_neg hany]
        exact ⟨a, List.mem_cons_self, hrefl a⟩
    · obtain ⟨b, hb, hrb⟩ := ih a hmem
      by_cases hany : (keepReps r l).any (fun b => decide (r x b)) = true
      · rw [hcons, if_pos hany]
        exact ⟨b, hb, hrb⟩
      · rw [hcons, if_neg hany]
        exact ⟨b, List.mem_cons_of_mem _ hb, hrb⟩

private lemma keepReps_pairwise {α : Type} {r : α → α → Prop} [DecidableRel r]
    (l : List α) : (keepReps r l).Pairwise fun a b => ¬ r a b := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x l ih =>
    have hcons : keepReps r (x :: l)
        = if (keepReps r l).any (fun b => decide (r x b)) then keepReps r l
          else x :: keepReps r l := rfl
    rw [hcons]
    by_cases hany : (keepReps r l).any (fun b => decide (r x b)) = true
    · rw [if_pos hany]
      exact ih
    · rw [if_neg hany]
      refine List.Pairwise.cons (fun b hb hrxb => ?_) ih
      exact hany (List.any_eq_true.mpr ⟨b, hb, decide_eq_true hrxb⟩)

private lemma keepReps_subset {α : Type} {r : α → α → Prop} [DecidableRel r]
    (l : List α) : ∀ a ∈ keepReps r l, a ∈ l := by
  induction l with
  | nil =>
    intro a ha
    simp [keepReps] at ha
  | cons x l ih =>
    intro a ha
    have hcons : keepReps r (x :: l)
        = if (keepReps r l).any (fun b => decide (r x b)) then keepReps r l
          else x :: keepReps r l := rfl
    rw [hcons] at ha
    by_cases hany : (keepReps r l).any (fun b => decide (r x b)) = true
    · rw [if_pos hany] at ha
      exact List.mem_cons_of_mem _ (ih a ha)
    · rw [if_neg hany] at ha
      rcases List.mem_cons.mp ha with rfl | hmem
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih a hmem)

/-- All 3-element subsets of `Fin n`, listed computably: the length-3
sublists of the canonical enumeration, as finsets. -/
def allTriples (n : ℕ) : List (Finset (Fin n)) :=
  ((List.finRange n).sublistsLen 3).map List.toFinset

lemma mem_allTriples {e : Finset (Fin n)} :
    e ∈ allTriples n ↔ e.card = 3 := by
  constructor
  · intro he
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
    obtain ⟨hsub, hlen⟩ := List.mem_sublistsLen.mp ht
    rw [List.toFinset_card_of_nodup (hsub.nodup (List.nodup_finRange n))]
    exact hlen
  · intro hcard
    have hnodup : ((List.finRange n).filter
        fun v => decide (v ∈ e)).Nodup :=
      (List.nodup_finRange n).filter _
    have htf : ((List.finRange n).filter
        fun v => decide (v ∈ e)).toFinset = e := by
      ext v
      simp
    refine List.mem_map.mpr
      ⟨(List.finRange n).filter fun v => decide (v ∈ e),
        List.mem_sublistsLen.mpr ⟨List.filter_sublist, ?_⟩, htf⟩
    calc ((List.finRange n).filter fun v => decide (v ∈ e)).length
        = ((List.finRange n).filter
            fun v => decide (v ∈ e)).toFinset.card :=
          (List.toFinset_card_of_nodup hnodup).symm
      _ = e.card := by rw [htf]
      _ = 3 := hcard

/-- All edge sets over a triple list, by structural recursion — the
kernel-friendly enumeration shape (`List.sublists` at a thousand entries
overflows the kernel stack; this flatMap recursion does not). -/
def edgeSetsOf : List (Finset (Fin n)) → List (Finset (Finset (Fin n)))
  | [] => [∅]
  | t :: ts => (edgeSetsOf ts).flatMap fun E => [E, insert t E]

lemma edgeSetsOf_subset {ts : List (Finset (Fin n))}
    {E : Finset (Finset (Fin n))} (hE : E ∈ edgeSetsOf ts) :
    ∀ e ∈ E, e ∈ ts := by
  induction ts generalizing E with
  | nil =>
    rw [show edgeSetsOf ([] : List (Finset (Fin n))) = [∅] from rfl,
      List.mem_singleton] at hE
    subst hE
    intro e he
    exact absurd he (Finset.notMem_empty e)
  | cons t ts ih =>
    rw [show edgeSetsOf (t :: ts) = (edgeSetsOf ts).flatMap
        (fun E => [E, insert t E]) from rfl, List.mem_flatMap] at hE
    obtain ⟨E', hE', hmem⟩ := hE
    intro e he
    rcases List.mem_cons.mp hmem with rfl | h2
    · exact List.mem_cons_of_mem _ (ih hE' e he)
    · rw [List.mem_singleton] at h2
      subst h2
      rcases Finset.mem_insert.mp he with rfl | he'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hE' e he')

lemma mem_edgeSetsOf {ts : List (Finset (Fin n))}
    {E : Finset (Finset (Fin n))} (hE : ∀ e ∈ E, e ∈ ts) :
    E ∈ edgeSetsOf ts := by
  induction ts generalizing E with
  | nil =>
    rw [show edgeSetsOf ([] : List (Finset (Fin n))) = [∅] from rfl,
      List.mem_singleton]
    exact Finset.eq_empty_iff_forall_notMem.mpr fun e he =>
      List.not_mem_nil (hE e he)
  | cons t ts ih =>
    rw [show edgeSetsOf (t :: ts) = (edgeSetsOf ts).flatMap
        (fun E => [E, insert t E]) from rfl, List.mem_flatMap]
    by_cases ht : t ∈ E
    · refine ⟨E.erase t, ih fun e he => ?_, ?_⟩
      · have hne := Finset.ne_of_mem_erase he
        rcases List.mem_cons.mp (hE e (Finset.mem_of_mem_erase he)) with
          rfl | h
        · exact absurd rfl hne
        · exact h
      · exact List.mem_cons_of_mem _
          (List.mem_singleton.mpr (Finset.insert_erase ht).symm)
    · refine ⟨E, ih fun e he => ?_, List.mem_cons_self⟩
      rcases List.mem_cons.mp (hE e he) with rfl | h
      · exact absurd he ht
      · exact h

/-- Check a Boolean predicate on every edge set built from a triple list
over an accumulator, by branching recursion. The kernel evaluation stack
depth is the LENGTH of the triple list — not the number of edge sets —
so exhaustive checks over `2^k` graphs reduce at depth `k`. -/
def allEdgeSetsSat (P : Finset (Finset (Fin n)) → Bool) :
    List (Finset (Fin n)) → Finset (Finset (Fin n)) → Bool
  | [], E => P E
  | t :: ts, E => allEdgeSetsSat P ts E && allEdgeSetsSat P ts (insert t E)

lemma allEdgeSetsSat_iff (P : Finset (Finset (Fin n)) → Bool)
    (ts : List (Finset (Fin n))) (E₀ : Finset (Finset (Fin n))) :
    allEdgeSetsSat P ts E₀ = true
      ↔ ∀ S ∈ edgeSetsOf ts, P (S ∪ E₀) = true := by
  induction ts generalizing E₀ with
  | nil =>
    rw [show allEdgeSetsSat P [] E₀ = P E₀ from rfl,
      show edgeSetsOf ([] : List (Finset (Fin n))) = [∅] from rfl]
    constructor
    · intro h S hS
      rw [List.mem_singleton] at hS
      subst hS
      rwa [Finset.empty_union]
    · intro h
      have := h ∅ (List.mem_singleton_self ∅)
      rwa [Finset.empty_union] at this
  | cons t ts ih =>
    rw [show allEdgeSetsSat P (t :: ts) E₀
        = (allEdgeSetsSat P ts E₀ && allEdgeSetsSat P ts (insert t E₀))
        from rfl, Bool.and_eq_true, ih, ih,
      show edgeSetsOf (t :: ts) = (edgeSetsOf ts).flatMap
        (fun E => [E, insert t E]) from rfl]
    constructor
    · rintro ⟨h₁, h₂⟩ S hS
      rw [List.mem_flatMap] at hS
      obtain ⟨S', hS', hmem⟩ := hS
      rcases List.mem_cons.mp hmem with rfl | h2
      · exact h₁ _ hS'
      · rw [List.mem_singleton] at h2
        subst h2
        rw [Finset.insert_union, ← Finset.union_insert]
        exact h₂ _ hS'
    · intro h
      refine ⟨fun S hS => ?_, fun S hS => ?_⟩
      · exact h S (List.mem_flatMap.mpr ⟨S, hS, List.mem_cons_self⟩)
      · have := h (insert t S) (List.mem_flatMap.mpr
          ⟨S, hS, List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)⟩)
        rwa [Finset.insert_union, ← Finset.union_insert] at this

/-- The user-facing form: a depth-shallow exhaustive check over all edge
sets covers every 3-graph. -/
theorem forall_sym3Graph_of_allEdgeSetsSat
    {P : Finset (Finset (Fin n)) → Bool}
    (h : allEdgeSetsSat P (allTriples n) ∅ = true)
    (G : Sym3Graph n) : P G.edges = true := by
  have hmem : G.edges ∈ edgeSetsOf (allTriples n) :=
    mem_edgeSetsOf fun e he => mem_allTriples.mpr (G.edges_valid e he)
  have := (allEdgeSetsSat_iff P (allTriples n) ∅).mp h G.edges hmem
  rwa [Finset.union_empty] at this

/-- All 3-graphs on `Fin n`, listed computably and kernel-reducibly. -/
def allSym3Graphs (n : ℕ) : List (Sym3Graph n) :=
  (edgeSetsOf (allTriples n)).attach.map fun S =>
    ⟨S.val, fun _ he =>
      mem_allTriples.mp (edgeSetsOf_subset S.property _ he)⟩

lemma mem_allSym3Graphs (G : Sym3Graph n) : G ∈ allSym3Graphs n := by
  have hmem : G.edges ∈ edgeSetsOf (allTriples n) :=
    mem_edgeSetsOf fun e he => mem_allTriples.mpr (G.edges_valid e he)
  exact List.mem_map.mpr ⟨⟨G.edges, hmem⟩, List.mem_attach _ _,
    Sym3Graph.ext rfl⟩

/-- Representatives of the isomorphism classes of 3-graphs on `Fin n`. -/
def sym3Reps (n : ℕ) : List (Sym3Graph n) :=
  keepReps Sym3Graph.IsIso (allSym3Graphs n)

set_option maxRecDepth 8192 in
/-- The enumeration kernel-computes: on three vertices there are exactly
two 3-graphs up to isomorphism (the empty one and the single triple). -/
example : (sym3Reps 3).length = 2 := by decide

set_option maxRecDepth 32768 in
/-- On four vertices there are exactly five 3-graphs up to isomorphism
(zero to four hyperedges). -/
example : (sym3Reps 4).length = 5 := by decide

/-- Completeness: every 3-graph is isomorphic to a listed representative. -/
theorem sym3Reps_complete (G : Sym3Graph n) : ∃ H ∈ sym3Reps n, G.IsIso H :=
  keepReps_coverage Sym3Graph.IsIso.refl _ G (mem_allSym3Graphs G)

/-- Distinctness: no two listed representatives are isomorphic. -/
theorem sym3Reps_pairwise (n : ℕ) :
    (sym3Reps n).Pairwise fun G H => ¬ G.IsIso H :=
  keepReps_pairwise _

/-- Every model of the 3-uniform hypergraph theory on `Fin n` arises from a
computational 3-graph. -/
lemma exists_sym3Graph_toModel_eq {M : Model hypergraph3Sig (Fin n)}
    (hM : THypergraph3.Mem M) : ∃ G : Sym3Graph n, G.toModel = M := by
  classical
  refine ⟨⟨Finset.univ.filter fun e : Finset (Fin n) =>
    ∃ f : Fin 3 → Fin n, Function.Injective f ∧ Finset.univ.image f = e
      ∧ M.interp () f, ?_⟩, ?_⟩
  · intro e he
    obtain ⟨f, hf, rfl, -⟩ := (Finset.mem_filter.mp he).2
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  · refine Model.ext ?_
    funext r f
    cases r
    show (Function.Injective f ∧ _ ∈ _) = M.interp () f
    apply propext
    constructor
    · rintro ⟨hinj, hmem⟩
      obtain ⟨g, hg, hge, hgint⟩ := (Finset.mem_filter.mp hmem).2
      have hrange : Set.range g = Set.range f := by
        have := congrArg (fun s : Finset (Fin n) => (↑s : Set (Fin n))) hge
        simpa [Finset.coe_image, Set.image_univ] using this
      exact (THypergraph3_interp_congr hM hg hinj hrange).mp hgint
    · intro hint
      have hinj : Function.Injective f := (hM ()).2 f hint
      exact ⟨hinj, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, f, hinj, rfl, hint⟩⟩

/-- Every model of the theory on `Fin n` is isomorphic to the model of a
listed representative: the enumeration is complete at the semantic level. -/
theorem exists_rep_modelIso {M : Model hypergraph3Sig (Fin n)}
    (hM : THypergraph3.Mem M) :
    ∃ H ∈ sym3Reps n, Nonempty (M ≃ᵣ H.toModel) := by
  obtain ⟨G, rfl⟩ := exists_sym3Graph_toModel_eq hM
  obtain ⟨H, hH, hiso⟩ := sym3Reps_complete G
  exact ⟨H, hH, (Sym3Graph.isIso_iff_nonempty_modelIso G H).mp hiso⟩

/-! ## The flag bridge

Canonical representatives enumerate the empty-type flag classes of any
subtheory of the 3-uniform hypergraph theory: `toFlag` sends a member
representative to its class, equality of classes is the decidable
isomorphism test, and every class is hit by exactly one listed
representative. -/

/-- A computational 3-graph satisfying a theory, as an unlabeled flag. -/
def Sym3Graph.toFlag {𝕋 : RelTheory hypergraph3Sig} (G : Sym3Graph n)
    (hG : 𝕋.Mem G.toModel) : Flag 𝕋 (emptyType hypergraph3Sig) (Fin n) :=
  (LabeledFlag.ofEmptyType hG).toFlag

/-- Two representatives give the same flag class iff the computable
isomorphism test succeeds: the flag-equality decision procedure. -/
theorem Sym3Graph.toFlag_eq_toFlag_iff {𝕋 : RelTheory hypergraph3Sig}
    {G H : Sym3Graph n} (hG : 𝕋.Mem G.toModel) (hH : 𝕋.Mem H.toModel) :
    G.toFlag hG = H.toFlag hH ↔ G.IsIso H := by
  constructor
  · intro h
    exact (Sym3Graph.isIso_iff_nonempty_modelIso G H).mpr
      (LabeledFlag.toFlag_eq_toFlag_iff_modelIso.mp h)
  · intro h
    exact LabeledFlag.toFlag_eq_toFlag_iff_modelIso.mpr
      ((Sym3Graph.isIso_iff_nonempty_modelIso G H).mp h)

/-- Completeness of the enumeration at the flag level: every empty-type
flag class of a subtheory of the 3-uniform hypergraph theory is realized
by a listed canonical representative. -/
theorem exists_sym3Rep_toFlag {𝕋 : RelTheory hypergraph3Sig}
    (hsub : ∀ M : Model hypergraph3Sig (Fin n), 𝕋.Mem M → THypergraph3.Mem M)
    (F : Flag 𝕋 (emptyType hypergraph3Sig) (Fin n)) :
    ∃ H ∈ sym3Reps n, ∃ hH : 𝕋.Mem H.toModel, F = H.toFlag hH := by
  obtain ⟨N, rfl⟩ := Quotient.exists_rep F
  obtain ⟨H, hHreps, ⟨e⟩⟩ := exists_rep_modelIso (hsub N.toModel N.mem)
  exact ⟨H, hHreps, 𝕋.mem_iso e N.mem,
    Quotient.sound ⟨LabeledFlagIso.ofEmptyType e⟩⟩

/-- Every empty-type flag class of a subtheory is realized by some
literal (not necessarily a canonical representative). -/
theorem exists_sym3Graph_toFlag {𝕋 : RelTheory hypergraph3Sig}
    (hsub : ∀ M : Model hypergraph3Sig (Fin n), 𝕋.Mem M → THypergraph3.Mem M)
    (F : Flag 𝕋 (emptyType hypergraph3Sig) (Fin n)) :
    ∃ (G : Sym3Graph n) (hG : 𝕋.Mem G.toModel), F = G.toFlag hG := by
  obtain ⟨H, -, hH, heq⟩ := exists_sym3Rep_toFlag hsub F
  exact ⟨H, hH, heq⟩

/-- Distinctness of the enumeration at the flag level: distinct listed
representatives give distinct flag classes, in any theory. -/
theorem sym3Reps_toFlag_pairwise (𝕋 : RelTheory hypergraph3Sig) (n : ℕ) :
    (sym3Reps n).Pairwise fun G H =>
      ∀ (hG : 𝕋.Mem G.toModel) (hH : 𝕋.Mem H.toModel),
        G.toFlag hG ≠ H.toFlag hH :=
  (sym3Reps_pairwise n).imp fun hne hG hH heq =>
    hne ((Sym3Graph.toFlag_eq_toFlag_iff hG hH).mp heq)

section FlagList

variable (𝕋 : RelTheory hypergraph3Sig)
variable [DecidablePred fun G : Sym3Graph n => 𝕋.Mem G.toModel]

/-- The canonical listing of the empty-type flag classes of a theory:
the member representatives, as flags. -/
def sym3FlagReps (n : ℕ)
    [DecidablePred fun G : Sym3Graph n => 𝕋.Mem G.toModel] :
    List (Flag 𝕋 (emptyType hypergraph3Sig) (Fin n)) :=
  ((sym3Reps n).filter fun G => decide (𝕋.Mem G.toModel)).pmap
    (fun G hG => G.toFlag hG)
    (fun _ hG => of_decide_eq_true (List.mem_filter.mp hG).2)

/-- The listing has no duplicates. -/
theorem sym3FlagReps_nodup (n : ℕ)
    [DecidablePred fun G : Sym3Graph n => 𝕋.Mem G.toModel] :
    (sym3FlagReps 𝕋 n).Nodup := by
  rw [List.Nodup, sym3FlagReps]
  refine List.Pairwise.pmap
    ((sym3Reps_toFlag_pairwise 𝕋 n).filter _) _ ?_
  intro G hG H hH hne
  exact hne _ _

/-- The listing is complete for subtheories of the 3-uniform hypergraph
theory: every flag class appears. -/
theorem mem_sym3FlagReps
    (hsub : ∀ M : Model hypergraph3Sig (Fin n), 𝕋.Mem M → THypergraph3.Mem M)
    (F : Flag 𝕋 (emptyType hypergraph3Sig) (Fin n)) :
    F ∈ sym3FlagReps 𝕋 n := by
  obtain ⟨H, hHreps, hH, rfl⟩ := exists_sym3Rep_toFlag hsub F
  rw [sym3FlagReps, List.mem_pmap]
  exact ⟨H, List.mem_filter.mpr ⟨hHreps, decide_eq_true hH⟩, rfl⟩

/-- **Sum transport**: a sum over all empty-type flag classes is the sum
over the canonical listing — the step that turns class-indexed identities
into literal computations. -/
theorem sum_flag_eq_sum_sym3FlagReps {A : Type} [AddCommMonoid A]
    (hsub : ∀ M : Model hypergraph3Sig (Fin n), 𝕋.Mem M → THypergraph3.Mem M)
    (f : Flag 𝕋 (emptyType hypergraph3Sig) (Fin n) → A) :
    ∑ F : Flag 𝕋 (emptyType hypergraph3Sig) (Fin n), f F
      = ((sym3FlagReps 𝕋 n).map f).sum := by
  classical
  rw [← List.sum_toFinset f (sym3FlagReps_nodup 𝕋 n)]
  refine (Finset.sum_subset (Finset.subset_univ _) fun F _ hF => ?_).symm
  exact absurd (List.mem_toFinset.mpr (mem_sym3FlagReps 𝕋 hsub F)) hF

end FlagList

/-! ## Literal density evaluation

The computable subflag count `flagCountC` — subsets of the host inducing
a copy of the pattern, tested by the decidable isomorphism check on
induced subgraphs — and its agreement with the specification-layer
`flagCount`. Together with the flag bridge this turns densities of
literal 3-graphs into kernel computations. -/

section Density

variable {m : ℕ}

/-- The induced subgraph along a vertex tuple: a triple is an edge iff its
image is. For an injective tuple this is the comap model, computably. -/
def Sym3Graph.pullback (G : Sym3Graph n) (f : Fin m → Fin n) : Sym3Graph m :=
  ⟨Finset.univ.filter fun e : Finset (Fin m) =>
    e.card = 3 ∧ e.image f ∈ G.edges,
   fun _ he => (Finset.mem_filter.mp he).2.1⟩

lemma Sym3Graph.pullback_toModel (G : Sym3Graph n) {f : Fin m → Fin n}
    (hf : Function.Injective f) :
    (G.pullback f).toModel = G.toModel.comap ⟨f, hf⟩ := by
  refine Model.ext ?_
  funext r g
  cases r
  apply propext
  show Function.Injective g ∧ Finset.univ.image g ∈ (G.pullback f).edges
    ↔ Function.Injective (f ∘ g) ∧ Finset.univ.image (f ∘ g) ∈ G.edges
  constructor
  · rintro ⟨hg, hmem⟩
    obtain ⟨-, -, hGe⟩ := Finset.mem_filter.mp hmem
    rw [Finset.image_image] at hGe
    exact ⟨hf.comp hg, hGe⟩
  · rintro ⟨hfg, hmem⟩
    have hg : Function.Injective g := fun a b hab => hfg (congrArg f hab)
    refine ⟨hg, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
    · rw [Finset.card_image_of_injective _ hg, Finset.card_univ,
        Fintype.card_fin]
    · rw [Finset.image_image]
      exact hmem

lemma length_filter_finRange (W : Finset (Fin n)) :
    ((List.finRange n).filter fun v => decide (v ∈ W)).length = W.card := by
  have hnodup := (List.nodup_finRange n).filter fun v => decide (v ∈ W)
  have htf : ((List.finRange n).filter
      fun v => decide (v ∈ W)).toFinset = W := by
    ext v
    simp
  rw [← List.toFinset_card_of_nodup hnodup, htf]

/-- A canonical enumeration of an `m`-element subset, kernel-reducible: the
elements of the ambient enumeration that lie in the subset (no sorting
machinery, whose well-founded recursion the kernel cannot unfold). -/
def subsetTuple (W : Finset (Fin n)) (hcard : W.card = m) : Fin m → Fin n :=
  fun i => ((List.finRange n).filter fun v => decide (v ∈ W)).get
    (Fin.cast ((length_filter_finRange W).trans hcard).symm i)

lemma subsetTuple_injective (W : Finset (Fin n)) (hcard : W.card = m) :
    Function.Injective (subsetTuple W hcard) := by
  intro a b hab
  have hget := List.nodup_iff_injective_get.mp
    ((List.nodup_finRange n).filter fun v => decide (v ∈ W)) hab
  exact Fin.cast_injective _ hget

lemma subsetTuple_mem (W : Finset (Fin n)) (hcard : W.card = m)
    (i : Fin m) : subsetTuple W hcard i ∈ W := by
  have h := List.get_mem ((List.finRange n).filter fun v => decide (v ∈ W))
    (Fin.cast ((length_filter_finRange W).trans hcard).symm i)
  exact of_decide_eq_true (List.mem_filter.mp h).2

/-- The canonical enumeration covers the subset exactly. -/
lemma subsetTuple_image_univ (W : Finset (Fin n)) (hcard : W.card = m) :
    Finset.univ.image (subsetTuple W hcard) = W := by
  refine Finset.eq_of_subset_of_card_le
    (fun x hx => ?_) ?_
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact subsetTuple_mem W hcard i
  · rw [hcard, Finset.card_image_of_injective _
      (subsetTuple_injective W hcard), Finset.card_univ, Fintype.card_fin]

/-- The computable subflag count: the number of `m`-element vertex subsets
of the host inducing a copy of the pattern. -/
def Sym3Graph.flagCountC (F : Sym3Graph m) (G : Sym3Graph n) : ℕ :=
  ((Finset.univ.powersetCard m : Finset (Finset (Fin n))).attach.filter
    fun W => F.IsIso (G.pullback
      (subsetTuple W.val (Finset.mem_powersetCard.mp W.property).2))).card

/-- The induced sub-flag on a subset is the pullback along the canonical
enumeration, as models. -/
private noncomputable def restrict_modelIso_pullback
    {𝕋 : RelTheory hypergraph3Sig}
    {G : Sym3Graph n} (hG : 𝕋.Mem G.toModel) {W : Finset (Fin n)}
    (hcard : W.card = m)
    (hroot : ∀ t, (LabeledFlag.ofEmptyType (𝕋 := 𝕋) hG).rootEmbed.toEmbedding
      t ∈ W) :
    ((LabeledFlag.ofEmptyType (𝕋 := 𝕋) hG).restrict W hroot).toModel
      ≃ᵣ (G.pullback (subsetTuple W hcard)).toModel := by
  rw [Sym3Graph.pullback_toModel G (subsetTuple_injective W hcard)]
  refine (ModelIso.comapCongr (ModelIso.refl G.toModel)
    ⟨_, subsetTuple_injective W hcard⟩
    (Function.Embedding.subtype _)
    (Equiv.ofBijective
      (fun i => ⟨subsetTuple W hcard i, subsetTuple_mem W hcard i⟩)
      ((Fintype.bijective_iff_injective_and_card _).mpr
        ⟨fun a b hab => subsetTuple_injective W hcard
          (congrArg Subtype.val hab), by simp [hcard]⟩))
    fun a => rfl).symm

/-- **Agreement**: the computable count is the specification-layer subflag
count of the corresponding unlabeled flags, in any theory. -/
private lemma mem_flagWitnesses_of_isIso {𝕋 : RelTheory hypergraph3Sig}
    {F : Sym3Graph m} {G : Sym3Graph n}
    (hF : 𝕋.Mem F.toModel) (hG : 𝕋.Mem G.toModel) {W : Finset (Fin n)}
    (hcard : W.card = m)
    (hiso : F.IsIso (G.pullback (subsetTuple W hcard))) :
    W ∈ flagWitnesses (LabeledFlag.ofEmptyType hF)
      (LabeledFlag.ofEmptyType hG) := by
  refine mem_flagWitnesses.mpr ⟨fun t => t.elim0, by simpa using hcard, ?_⟩
  obtain ⟨e⟩ := (Sym3Graph.isIso_iff_nonempty_modelIso _ _).mp hiso
  exact ⟨LabeledFlagIso.ofEmptyType
    ((restrict_modelIso_pullback hG hcard _).trans e.symm)⟩

private lemma card_of_mem_flagWitnesses {𝕋 : RelTheory hypergraph3Sig}
    {F : Sym3Graph m} {G : Sym3Graph n}
    {hF : 𝕋.Mem F.toModel} {hG : 𝕋.Mem G.toModel} {W : Finset (Fin n)}
    (hW : W ∈ flagWitnesses (LabeledFlag.ofEmptyType hF)
      (LabeledFlag.ofEmptyType hG)) : W.card = m := by
  obtain ⟨-, hcard, -⟩ := mem_flagWitnesses.mp hW
  simpa using hcard

private lemma isIso_of_mem_flagWitnesses {𝕋 : RelTheory hypergraph3Sig}
    {F : Sym3Graph m} {G : Sym3Graph n}
    {hF : 𝕋.Mem F.toModel} {hG : 𝕋.Mem G.toModel} {W : Finset (Fin n)}
    (hW : W ∈ flagWitnesses (LabeledFlag.ofEmptyType hF)
      (LabeledFlag.ofEmptyType hG)) (hcard : W.card = m) :
    F.IsIso (G.pullback (subsetTuple W hcard)) := by
  obtain ⟨hroot, -, ⟨i⟩⟩ := mem_flagWitnesses.mp hW
  refine (Sym3Graph.isIso_iff_nonempty_modelIso _ _).mpr ?_
  exact ⟨i.toIso.symm.trans (restrict_modelIso_pullback hG hcard hroot)⟩

theorem Sym3Graph.flagCountC_eq_flagCount {𝕋 : RelTheory hypergraph3Sig}
    {F : Sym3Graph m} {G : Sym3Graph n}
    (hF : 𝕋.Mem F.toModel) (hG : 𝕋.Mem G.toModel) :
    F.flagCountC G
      = flagCount (LabeledFlag.ofEmptyType hF)
          (LabeledFlag.ofEmptyType hG) := by
  rw [Sym3Graph.flagCountC, flagCount]
  refine Finset.card_bij (fun W _ => W.val) ?_ ?_ ?_
  · rintro W hW
    exact mem_flagWitnesses_of_isIso hF hG
      (Finset.mem_powersetCard.mp W.property).2 (Finset.mem_filter.mp hW).2
  · rintro W _ W' _ h
    exact Subtype.ext h
  · rintro W hW
    have hcard : W.card = m := card_of_mem_flagWitnesses hW
    have hmem : W ∈ (Finset.univ.powersetCard m : Finset (Finset (Fin n))) :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
    exact ⟨⟨W, hmem⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,
      isIso_of_mem_flagWitnesses hW _⟩, rfl⟩

/-- The density of literal flags is the computable count over the binomial
normalizer. -/
theorem Sym3Graph.subflagDensity_toFlag {𝕋 : RelTheory hypergraph3Sig}
    {F : Sym3Graph m} {G : Sym3Graph n}
    (hF : 𝕋.Mem F.toModel) (hG : 𝕋.Mem G.toModel) :
    subflagDensity (F.toFlag hF) (G.toFlag hG)
      = (F.flagCountC G : ℚ) / (n.choose m : ℚ) := by
  rw [Sym3Graph.toFlag, Sym3Graph.toFlag, subflagDensity_mk, flagDensity,
    ← Sym3Graph.flagCountC_eq_flagCount hF hG]
  simp

/-! ### Pair densities on literals

Over the empty type the pair-witness disjointness condition
`OnlyRootsShared` is plain disjointness, so the pair count is a
computable count over pairs of disjoint subsets. -/

private lemma not_mem_rootFinset_ofEmptyType {𝕋 : RelTheory hypergraph3Sig}
    {G : Sym3Graph n} (hG : 𝕋.Mem G.toModel) (x : Fin n) :
    x ∉ (LabeledFlag.ofEmptyType (𝕋 := 𝕋) hG).rootFinset := by
  intro hx
  rw [LabeledFlag.rootFinset, Finset.mem_map] at hx
  obtain ⟨t, -, -⟩ := hx
  exact t.elim0

variable {m₁ m₂ : ℕ}

/-- The computable pair count: pairs of disjoint vertex subsets inducing
copies of the two patterns. -/
def Sym3Graph.flagPairCountC (F₁ : Sym3Graph m₁) (F₂ : Sym3Graph m₂)
    (G : Sym3Graph n) : ℕ :=
  (((Finset.univ.powersetCard m₁ : Finset (Finset (Fin n))) ×ˢ
      (Finset.univ.powersetCard m₂ : Finset (Finset (Fin n)))).attach.filter
    fun P => Disjoint P.val.1 P.val.2
      ∧ F₁.IsIso (G.pullback (subsetTuple P.val.1
          (Finset.mem_powersetCard.mp
            (Finset.mem_product.mp P.property).1).2))
      ∧ F₂.IsIso (G.pullback (subsetTuple P.val.2
          (Finset.mem_powersetCard.mp
            (Finset.mem_product.mp P.property).2).2))).card

/-- **Agreement** for pairs: the computable pair count is the
specification-layer pair count, in any theory. -/
theorem Sym3Graph.flagPairCountC_eq_pairCount {𝕋 : RelTheory hypergraph3Sig}
    {F₁ : Sym3Graph m₁} {F₂ : Sym3Graph m₂} {G : Sym3Graph n}
    (hF₁ : 𝕋.Mem F₁.toModel) (hF₂ : 𝕋.Mem F₂.toModel)
    (hG : 𝕋.Mem G.toModel) :
    F₁.flagPairCountC F₂ G
      = pairCount (LabeledFlag.ofEmptyType hF₁)
          (LabeledFlag.ofEmptyType hF₂) (LabeledFlag.ofEmptyType hG) := by
  rw [Sym3Graph.flagPairCountC, pairCount]
  refine Finset.card_bij (fun P _ => P.val) ?_ ?_ ?_
  · rintro P hP
    obtain ⟨-, hdisj, hiso₁, hiso₂⟩ := Finset.mem_filter.mp hP
    refine mem_pairWitnesses.mpr ⟨mem_flagWitnesses_of_isIso hF₁ hG _ hiso₁,
      mem_flagWitnesses_of_isIso hF₂ hG _ hiso₂, fun x hx₁ hx₂ =>
        absurd (Finset.disjoint_left.mp hdisj hx₁) (not_not_intro hx₂)⟩
  · rintro P _ P' _ h
    exact Subtype.ext h
  · rintro P hP
    obtain ⟨hW₁, hW₂, hshared⟩ := mem_pairWitnesses.mp hP
    have hc₁ : P.1.card = m₁ := card_of_mem_flagWitnesses hW₁
    have hc₂ : P.2.card = m₂ := card_of_mem_flagWitnesses hW₂
    have hdisj : Disjoint P.1 P.2 :=
      Finset.disjoint_left.mpr fun x hx₁ hx₂ =>
        not_mem_rootFinset_ofEmptyType hG x (hshared x hx₁ hx₂)
    have hmem : P ∈ (Finset.univ.powersetCard m₁ :
        Finset (Finset (Fin n))) ×ˢ
        (Finset.univ.powersetCard m₂ : Finset (Finset (Fin n))) :=
      Finset.mem_product.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hc₁⟩,
         Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hc₂⟩⟩
    exact ⟨⟨P, hmem⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hdisj,
      isIso_of_mem_flagWitnesses hW₁ _,
      isIso_of_mem_flagWitnesses hW₂ _⟩, rfl⟩

/-- The pair density of literal flags is the computable pair count over
the pair normalizer. -/
theorem Sym3Graph.subflagPairDensity_toFlag {𝕋 : RelTheory hypergraph3Sig}
    {F₁ : Sym3Graph m₁} {F₂ : Sym3Graph m₂} {G : Sym3Graph n}
    (hF₁ : 𝕋.Mem F₁.toModel) (hF₂ : 𝕋.Mem F₂.toModel)
    (hG : 𝕋.Mem G.toModel) :
    subflagPairDensity (F₁.toFlag hF₁) (F₂.toFlag hF₂) (G.toFlag hG)
      = (F₁.flagPairCountC F₂ G : ℚ) / (pairChoose n m₁ m₂ : ℚ) := by
  rw [Sym3Graph.toFlag, Sym3Graph.toFlag, Sym3Graph.toFlag,
    subflagPairDensity_mk, flagPairDensity,
    ← Sym3Graph.flagPairCountC_eq_pairCount hF₁ hF₂ hG]
  simp

end Density

/-! ## Typed flags on literals

A `σ`-rooted literal flag: a 3-graph with a distinguished root tuple
inducing the type. This is the representation the SDP block indices
enumerate; the type itself is a literal 3-graph on the label carrier. -/

section Typed

variable {k m : ℕ}

/-- A literal flag: a 3-graph together with a root tuple. -/
structure Sym3Flag (k n : ℕ) where
  /-- The underlying 3-graph. -/
  graph : Sym3Graph n
  /-- The root labeling. -/
  roots : Fin k → Fin n

/-- Well-formedness over a literal type: the roots are injective and
induce exactly the type. Decidable. -/
def Sym3Flag.WellFormed (σg : Sym3Graph k) (F : Sym3Flag k n) : Prop :=
  Function.Injective F.roots ∧ F.graph.pullback F.roots = σg

instance (σg : Sym3Graph k) (F : Sym3Flag k n) :
    Decidable (F.WellFormed σg) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The specification-layer labeled flag of a well-formed literal flag,
over the literal type. -/
def Sym3Flag.toLabeledFlag {𝕋 : RelTheory hypergraph3Sig}
    {σg : Sym3Graph k} {F : Sym3Flag k n} (hwf : F.WellFormed σg)
    (hmem : 𝕋.Mem F.graph.toModel) :
    LabeledFlag 𝕋 σg.toModel (Fin n) where
  toModel := F.graph.toModel
  mem := hmem
  rootEmbed := ⟨⟨F.roots, hwf.1⟩, fun r f => by
    conv_rhs => rw [← hwf.2, Sym3Graph.pullback_toModel _ hwf.1]
    exact Iff.rfl⟩

/-- Typed computational isomorphism: a permutation carrying edges to
edges and roots to roots. Decidable. -/
def Sym3Flag.IsIso (F H : Sym3Flag k n) : Prop :=
  ∃ p : Equiv.Perm (Fin n),
    F.graph.edges.image (Finset.image ⇑p) = H.graph.edges
      ∧ ⇑p ∘ F.roots = H.roots

instance (F H : Sym3Flag k n) : Decidable (F.IsIso H) :=
  decidable_of_iff (∃ p : Equiv.Perm (Fin n),
    F.graph.edges.image (Finset.image ⇑p) = H.graph.edges
      ∧ ⇑p ∘ F.roots = H.roots) Iff.rfl

/-- The typed computational isomorphism test is sound and complete for
flag isomorphism over the literal type. -/
theorem Sym3Flag.isIso_iff_nonempty_flagIso {𝕋 : RelTheory hypergraph3Sig}
    {σg : Sym3Graph k} {F H : Sym3Flag k n}
    (hwfF : F.WellFormed σg) (hwfH : H.WellFormed σg)
    (hF : 𝕋.Mem F.graph.toModel) (hH : 𝕋.Mem H.graph.toModel) :
    F.IsIso H ↔
      Nonempty (F.toLabeledFlag (𝕋 := 𝕋) hwfF hF
        ≃ᶠ H.toLabeledFlag hwfH hH) := by
  constructor
  · rintro ⟨p, hedges, hroots⟩
    exact ⟨⟨Sym3Graph.modelIsoOfPerm p hedges,
      fun t => congrFun hroots t⟩⟩
  · rintro ⟨i⟩
    refine ⟨i.toIso.toEquiv, Sym3Graph.image_edges_of_modelIso i.toIso, ?_⟩
    funext t
    exact i.root_preserve t

/-- The typed flag class of a well-formed literal flag. -/
def Sym3Flag.toFlag {𝕋 : RelTheory hypergraph3Sig}
    {σg : Sym3Graph k} {F : Sym3Flag k n} (hwf : F.WellFormed σg)
    (hmem : 𝕋.Mem F.graph.toModel) : Flag 𝕋 σg.toModel (Fin n) :=
  (F.toLabeledFlag hwf hmem).toFlag

/-- Equality of typed flag classes is the decidable typed isomorphism
test. -/
theorem Sym3Flag.toFlag_eq_toFlag_iff {𝕋 : RelTheory hypergraph3Sig}
    {σg : Sym3Graph k} {F H : Sym3Flag k n}
    (hwfF : F.WellFormed σg) (hwfH : H.WellFormed σg)
    (hF : 𝕋.Mem F.graph.toModel) (hH : 𝕋.Mem H.graph.toModel) :
    F.toFlag (𝕋 := 𝕋) hwfF hF = H.toFlag hwfH hH ↔ F.IsIso H := by
  constructor
  · intro h
    exact (Sym3Flag.isIso_iff_nonempty_flagIso hwfF hwfH hF hH).mpr
      (Quotient.exact h)
  · intro h
    exact Quotient.sound
      ((Sym3Flag.isIso_iff_nonempty_flagIso hwfF hwfH hF hH).mp h)

/-! ### Typed enumeration

All well-formed literal flags over a literal type, deduplicated by the
decidable typed isomorphism test: the canonical listing of the typed
flag classes — the SDP block index set. -/

lemma Sym3Flag.IsIso.refl (F : Sym3Flag k n) : F.IsIso F := by
  refine ⟨1, ?_, ?_⟩
  · have h1 : Finset.image (⇑(1 : Equiv.Perm (Fin n))) = id := by
      funext e
      simp
    rw [h1, Finset.image_id]
  · funext t
    simp

/-- All tuples `Fin k → Fin n`, listed by recursion on `k`. -/
def allTuples (n : ℕ) : (k : ℕ) → List (Fin k → Fin n)
  | 0 => [fun i => i.elim0]
  | k + 1 => (allTuples n k).flatMap fun f =>
      (List.finRange n).map fun v => Fin.cons v f

lemma mem_allTuples {k : ℕ} (g : Fin k → Fin n) : g ∈ allTuples n k := by
  induction k with
  | zero =>
    exact List.mem_singleton.mpr (funext fun i => i.elim0)
  | succ k ih =>
    refine List.mem_flatMap.mpr ⟨Fin.tail g, ih (Fin.tail g), ?_⟩
    exact List.mem_map.mpr ⟨g 0, List.mem_finRange _, Fin.cons_self_tail g⟩

/-- All well-formed literal flags over a literal type. -/
def allSym3Flags (σg : Sym3Graph k) (n : ℕ) : List (Sym3Flag k n) :=
  ((allSym3Graphs n).flatMap fun G =>
    (allTuples n k).map fun r => Sym3Flag.mk G r).filter
      fun F => decide (F.WellFormed σg)

lemma mem_allSym3Flags {σg : Sym3Graph k} {F : Sym3Flag k n}
    (hwf : F.WellFormed σg) : F ∈ allSym3Flags σg n := by
  refine List.mem_filter.mpr ⟨?_, decide_eq_true hwf⟩
  refine List.mem_flatMap.mpr ⟨F.graph, mem_allSym3Graphs F.graph, ?_⟩
  exact List.mem_map.mpr ⟨F.roots, mem_allTuples F.roots, rfl⟩

lemma wellFormed_of_mem_allSym3Flags {σg : Sym3Graph k} {F : Sym3Flag k n}
    (h : F ∈ allSym3Flags σg n) : F.WellFormed σg :=
  of_decide_eq_true (List.mem_filter.mp h).2

/-- Representatives of the typed isomorphism classes. -/
def sym3TypedReps (σg : Sym3Graph k) (n : ℕ) : List (Sym3Flag k n) :=
  keepReps Sym3Flag.IsIso (allSym3Flags σg n)

theorem sym3TypedReps_complete {σg : Sym3Graph k} {F : Sym3Flag k n}
    (hwf : F.WellFormed σg) : ∃ H ∈ sym3TypedReps σg n, F.IsIso H :=
  keepReps_coverage Sym3Flag.IsIso.refl _ F (mem_allSym3Flags hwf)

theorem sym3TypedReps_pairwise (σg : Sym3Graph k) (n : ℕ) :
    (sym3TypedReps σg n).Pairwise fun F H => ¬ F.IsIso H :=
  keepReps_pairwise _

theorem wellFormed_of_mem_sym3TypedReps {σg : Sym3Graph k}
    {F : Sym3Flag k n} (h : F ∈ sym3TypedReps σg n) : F.WellFormed σg :=
  wellFormed_of_mem_allSym3Flags (keepReps_subset _ F h)

section TypedFlagList

variable (𝕋 : RelTheory hypergraph3Sig) {σg : Sym3Graph k}
variable [DecidablePred fun F : Sym3Flag k n => 𝕋.Mem F.graph.toModel]

/-- The canonical listing of the typed flag classes over a literal type:
the well-formed member representatives, as flags. -/
def sym3TypedFlagReps (σg : Sym3Graph k) (n : ℕ)
    [DecidablePred fun F : Sym3Flag k n => 𝕋.Mem F.graph.toModel] :
    List (Flag 𝕋 σg.toModel (Fin n)) :=
  ((sym3TypedReps σg n).filter fun F =>
    decide (𝕋.Mem F.graph.toModel)).pmap
    (fun F (hF : F.WellFormed σg ∧ 𝕋.Mem F.graph.toModel) =>
      F.toFlag hF.1 hF.2)
    (fun _ hF => ⟨wellFormed_of_mem_sym3TypedReps
        (List.mem_filter.mp hF).1,
      of_decide_eq_true (List.mem_filter.mp hF).2⟩)

/-- The typed listing has no duplicates. -/
theorem sym3TypedFlagReps_nodup (σg : Sym3Graph k) (n : ℕ)
    [DecidablePred fun F : Sym3Flag k n => 𝕋.Mem F.graph.toModel] :
    (sym3TypedFlagReps 𝕋 σg n).Nodup := by
  rw [List.Nodup, sym3TypedFlagReps]
  refine List.Pairwise.pmap ((sym3TypedReps_pairwise σg n).filter _) _ ?_
  intro F hF H hH hne heq
  exact hne ((Sym3Flag.toFlag_eq_toFlag_iff _ _ _ _).mp heq)

/-- The typed listing is complete for subtheories of the 3-uniform
hypergraph theory: every typed flag class appears. -/
theorem mem_sym3TypedFlagReps
    (hsub : ∀ M : Model hypergraph3Sig (Fin n), 𝕋.Mem M → THypergraph3.Mem M)
    (F : Flag 𝕋 σg.toModel (Fin n)) : F ∈ sym3TypedFlagReps 𝕋 σg n := by
  obtain ⟨N, rfl⟩ := Quotient.exists_rep F
  obtain ⟨G, hGeq⟩ := exists_sym3Graph_toModel_eq (hsub N.toModel N.mem)
  set F₀ : Sym3Flag k n := ⟨G, fun i => N.rootEmbed.toEmbedding i⟩ with hF₀
  have hinj : Function.Injective F₀.roots := fun a b hab =>
    N.rootEmbed.toEmbedding.injective hab
  have hemb : (⟨F₀.roots, hinj⟩ : Fin k ↪ Fin n)
      = N.rootEmbed.toEmbedding :=
    Function.Embedding.ext fun x => rfl
  have hpull : F₀.graph.pullback F₀.roots = σg := by
    apply Sym3Graph.toModel_injective
    rw [Sym3Graph.pullback_toModel _ hinj]
    show G.toModel.comap _ = _
    rw [hGeq, hemb, N.comap_rootEmbed]
  have hwf : F₀.WellFormed σg := ⟨hinj, hpull⟩
  have hmem : 𝕋.Mem F₀.graph.toModel := by
    show 𝕋.Mem G.toModel
    rw [hGeq]
    exact N.mem
  have hflag : F₀.toFlag (𝕋 := 𝕋) hwf hmem = ⟦N⟧ := by
    refine Quotient.sound ⟨⟨Equiv.refl _, fun r f => ?_⟩, fun t => rfl⟩
    show N.toModel.interp r (⇑(Equiv.refl _) ∘ f) ↔ G.toModel.interp r f
    rw [hGeq]
    exact Iff.rfl
  obtain ⟨R, hR, hiso⟩ := sym3TypedReps_complete hwf
  have hRwf := wellFormed_of_mem_sym3TypedReps hR
  have hRmem : 𝕋.Mem R.graph.toModel := by
    obtain ⟨p, hedges, -⟩ := hiso
    exact 𝕋.mem_iso (Sym3Graph.modelIsoOfPerm p hedges) hmem
  rw [← hflag,
    (Sym3Flag.toFlag_eq_toFlag_iff hwf hRwf hmem hRmem).mpr hiso,
    sym3TypedFlagReps, List.mem_pmap]
  exact ⟨R, List.mem_filter.mpr ⟨hR, decide_eq_true hRmem⟩, rfl⟩

/-- **Typed sum transport**: a sum over all typed flag classes is the sum
over the canonical listing. -/
theorem sum_typedFlag_eq_sum_sym3TypedFlagReps {A : Type} [AddCommMonoid A]
    (hsub : ∀ M : Model hypergraph3Sig (Fin n), 𝕋.Mem M → THypergraph3.Mem M)
    (f : Flag 𝕋 σg.toModel (Fin n) → A) :
    ∑ F : Flag 𝕋 σg.toModel (Fin n), f F
      = ((sym3TypedFlagReps 𝕋 σg n).map f).sum := by
  classical
  rw [← List.sum_toFinset f (sym3TypedFlagReps_nodup 𝕋 σg n)]
  refine (Finset.sum_subset (Finset.subset_univ _) fun F _ hF => ?_).symm
  exact absurd (List.mem_toFinset.mpr (mem_sym3TypedFlagReps 𝕋 hsub F)) hF

end TypedFlagList

/-! ### Typed literal densities

The computable typed subflag count: root-containing subsets of the host
inducing a root-preserving copy of the pattern. The induced sub-flag is
literal again — the pullback graph with the roots relocated through the
inverse of the canonical subset enumeration. -/

/-- Pullbacks compose. -/
lemma Sym3Graph.pullback_pullback {l : ℕ} (G : Sym3Graph n)
    (f : Fin m → Fin n) (g : Fin l → Fin m) :
    (G.pullback f).pullback g = G.pullback (f ∘ g) := by
  refine Sym3Graph.ext ?_
  ext e
  show e ∈ Finset.univ.filter _ ↔ e ∈ Finset.univ.filter _
  rw [Finset.mem_filter, Finset.mem_filter]
  refine and_congr_right fun _ => and_congr_right fun hcard => ?_
  constructor
  · intro h
    obtain ⟨-, -, hmem⟩ := Finset.mem_filter.mp h
    rwa [Finset.image_image] at hmem
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · refine le_antisymm (le_trans Finset.card_image_le (le_of_eq hcard)) ?_
      have h3 := G.edges_valid _ h
      calc (3 : ℕ) = ((e.image g).image f).card := by
            rw [Finset.image_image, h3]
      _ ≤ (e.image g).card := Finset.card_image_le
    · rwa [Finset.image_image]

/-- The index of a subset member in the canonical enumeration: the inverse
of `subsetTuple`, kernel-reducible. -/
def invIdx (W : Finset (Fin n)) (hcard : W.card = m) (v : Fin n)
    (hv : v ∈ W) : Fin m :=
  ⟨((List.finRange n).filter fun x => decide (x ∈ W)).idxOf v,
   by
    rw [← ((length_filter_finRange W).trans hcard)]
    exact List.idxOf_lt_length_of_mem (List.mem_filter.mpr
      ⟨List.mem_finRange v, decide_eq_true hv⟩)⟩

lemma subsetTuple_invIdx (W : Finset (Fin n)) (hcard : W.card = m)
    {v : Fin n} (hv : v ∈ W) :
    subsetTuple W hcard (invIdx W hcard v hv) = v := by
  show ((List.finRange n).filter fun x => decide (x ∈ W)).get _ = v
  simp [invIdx, List.getElem_idxOf]

/-- The induced typed sub-flag on a root-containing subset: the pullback
graph with the roots relocated. -/
def Sym3Flag.pullbackFlag (Gσ : Sym3Flag k n) (W : Finset (Fin n))
    (hcard : W.card = m) (hroots : ∀ i, Gσ.roots i ∈ W) : Sym3Flag k m :=
  ⟨Gσ.graph.pullback (subsetTuple W hcard),
   fun i => invIdx W hcard (Gσ.roots i) (hroots i)⟩

lemma Sym3Flag.pullbackFlag_wellFormed {σg : Sym3Graph k}
    {Gσ : Sym3Flag k n} (hwfG : Gσ.WellFormed σg) {W : Finset (Fin n)}
    (hcard : W.card = m) (hroots : ∀ i, Gσ.roots i ∈ W) :
    (Gσ.pullbackFlag W hcard hroots).WellFormed σg := by
  constructor
  · intro a b hab
    have hab' : invIdx W hcard (Gσ.roots a) (hroots a)
        = invIdx W hcard (Gσ.roots b) (hroots b) := hab
    have h := congrArg (subsetTuple W hcard) hab'
    rw [subsetTuple_invIdx, subsetTuple_invIdx] at h
    exact hwfG.1 h
  · show (Gσ.graph.pullback (subsetTuple W hcard)).pullback _ = σg
    rw [Sym3Graph.pullback_pullback]
    have hcomp : (subsetTuple W hcard
        ∘ (Gσ.pullbackFlag W hcard hroots).roots) = Gσ.roots :=
      funext fun i => subsetTuple_invIdx W hcard (hroots i)
    rw [hcomp]
    exact hwfG.2

lemma Sym3Flag.pullbackFlag_graph_mem {𝕋 : RelTheory hypergraph3Sig}
    {Gσ : Sym3Flag k n} (hG : 𝕋.Mem Gσ.graph.toModel) {W : Finset (Fin n)}
    (hcard : W.card = m) (hroots : ∀ i, Gσ.roots i ∈ W) :
    𝕋.Mem (Gσ.pullbackFlag W hcard hroots).graph.toModel := by
  show 𝕋.Mem (Gσ.graph.pullback (subsetTuple W hcard)).toModel
  rw [Sym3Graph.pullback_toModel _ (subsetTuple_injective W hcard)]
  exact 𝕋.mem_comap _ hG

/-- The induced typed sub-flag is the restriction, as labeled flags. -/
noncomputable def pullbackFlagIso {𝕋 : RelTheory hypergraph3Sig}
    {σg : Sym3Graph k} {Gσ : Sym3Flag k n} (hwfG : Gσ.WellFormed σg)
    (hG : 𝕋.Mem Gσ.graph.toModel) {W : Finset (Fin n)} (hcard : W.card = m)
    (hroots : ∀ i, Gσ.roots i ∈ W)
    (hroot' : ∀ t, (Gσ.toLabeledFlag hwfG hG).rootEmbed.toEmbedding t ∈ W)
    (hwfP : (Gσ.pullbackFlag W hcard hroots).WellFormed σg)
    (hmemP : 𝕋.Mem (Gσ.pullbackFlag W hcard hroots).graph.toModel) :
    (Gσ.pullbackFlag W hcard hroots).toLabeledFlag hwfP hmemP
      ≃ᶠ (Gσ.toLabeledFlag hwfG hG).restrict W hroot' := by
  refine ⟨⟨Equiv.ofBijective
    (fun i => ⟨subsetTuple W hcard i, subsetTuple_mem W hcard i⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun a b hab => subsetTuple_injective W hcard
        (congrArg Subtype.val hab), by simp [hcard]⟩), fun r f => ?_⟩,
    fun t => ?_⟩
  · show (Gσ.graph.toModel.comap (Function.Embedding.subtype _)).interp r _
      ↔ (Gσ.graph.pullback (subsetTuple W hcard)).toModel.interp r f
    rw [Sym3Graph.pullback_toModel _ (subsetTuple_injective W hcard)]
    exact Iff.rfl
  · exact Subtype.ext (subsetTuple_invIdx W hcard (hroots t))

instance (Fσ : Sym3Flag k m) (Gσ : Sym3Flag k n) (W : Finset (Fin n))
    (hcard : W.card = m) :
    Decidable (∃ h : ∀ i, Gσ.roots i ∈ W,
      Fσ.IsIso (Gσ.pullbackFlag W hcard h)) :=
  if h : ∀ i, Gσ.roots i ∈ W then
    decidable_of_iff (Fσ.IsIso (Gσ.pullbackFlag W hcard h))
      ⟨fun hi => ⟨h, hi⟩, fun ⟨_, hi⟩ => hi⟩
  else isFalse fun ⟨h', _⟩ => h h'

/-- The computable typed subflag count: root-containing `m`-subsets of the
host inducing a root-preserving copy of the pattern. -/
def Sym3Flag.flagCountC (Fσ : Sym3Flag k m) (Gσ : Sym3Flag k n) : ℕ :=
  ((Finset.univ.powersetCard m : Finset (Finset (Fin n))).attach.filter
    fun W => ∃ h : ∀ i, Gσ.roots i ∈ W.val,
      Fσ.IsIso (Gσ.pullbackFlag W.val
        (Finset.mem_powersetCard.mp W.property).2 h)).card

private lemma typed_mem_flagWitnesses_of_isIso {𝕋 : RelTheory hypergraph3Sig}
    {σg : Sym3Graph k} {Fσ : Sym3Flag k m} {Gσ : Sym3Flag k n}
    (hwfF : Fσ.WellFormed σg) (hwfG : Gσ.WellFormed σg)
    (hF : 𝕋.Mem Fσ.graph.toModel) (hG : 𝕋.Mem Gσ.graph.toModel)
    {W : Finset (Fin n)} (hcard : W.card = m)
    (hroots : ∀ i, Gσ.roots i ∈ W)
    (hiso : Fσ.IsIso (Gσ.pullbackFlag W hcard hroots)) :
    W ∈ flagWitnesses (Fσ.toLabeledFlag hwfF hF)
      (Gσ.toLabeledFlag hwfG hG) := by
  have hwfP := Sym3Flag.pullbackFlag_wellFormed hwfG hcard hroots
  have hmemP := Sym3Flag.pullbackFlag_graph_mem hG hcard hroots
  obtain ⟨j⟩ := (Sym3Flag.isIso_iff_nonempty_flagIso
    hwfF hwfP hF hmemP).mp hiso
  exact mem_flagWitnesses.mpr ⟨fun t => hroots t, by simpa using hcard,
    ⟨((pullbackFlagIso hwfG hG hcard hroots _ hwfP hmemP).symm.trans
      j.symm)⟩⟩

private lemma typed_card_of_mem_flagWitnesses
    {𝕋 : RelTheory hypergraph3Sig}
    {σg : Sym3Graph k} {Fσ : Sym3Flag k m} {Gσ : Sym3Flag k n}
    {hwfF : Fσ.WellFormed σg} {hwfG : Gσ.WellFormed σg}
    {hF : 𝕋.Mem Fσ.graph.toModel} {hG : 𝕋.Mem Gσ.graph.toModel}
    {W : Finset (Fin n)}
    (hW : W ∈ flagWitnesses (Fσ.toLabeledFlag hwfF hF)
      (Gσ.toLabeledFlag hwfG hG)) : W.card = m := by
  obtain ⟨-, hcard, -⟩ := mem_flagWitnesses.mp hW
  simpa using hcard

private lemma typed_pred_of_mem_flagWitnesses
    {𝕋 : RelTheory hypergraph3Sig}
    {σg : Sym3Graph k} {Fσ : Sym3Flag k m} {Gσ : Sym3Flag k n}
    {hwfF : Fσ.WellFormed σg} {hwfG : Gσ.WellFormed σg}
    {hF : 𝕋.Mem Fσ.graph.toModel} {hG : 𝕋.Mem Gσ.graph.toModel}
    {W : Finset (Fin n)}
    (hW : W ∈ flagWitnesses (Fσ.toLabeledFlag hwfF hF)
      (Gσ.toLabeledFlag hwfG hG)) (hcard : W.card = m) :
    ∃ h : ∀ i, Gσ.roots i ∈ W,
      Fσ.IsIso (Gσ.pullbackFlag W hcard h) := by
  obtain ⟨hroot, -, ⟨i⟩⟩ := mem_flagWitnesses.mp hW
  have hroots : ∀ i, Gσ.roots i ∈ W := fun i => hroot i
  have hwfP := Sym3Flag.pullbackFlag_wellFormed hwfG hcard hroots
  have hmemP := Sym3Flag.pullbackFlag_graph_mem hG hcard hroots
  refine ⟨hroots,
    (Sym3Flag.isIso_iff_nonempty_flagIso hwfF hwfP hF hmemP).mpr ?_⟩
  exact ⟨i.symm.trans
    (pullbackFlagIso hwfG hG hcard hroots hroot hwfP hmemP).symm⟩

/-- **Typed agreement**: the computable typed count is the
specification-layer subflag count of the typed labeled flags. -/
theorem Sym3Flag.flagCountC_eq_flagCount {𝕋 : RelTheory hypergraph3Sig}
    {σg : Sym3Graph k} {Fσ : Sym3Flag k m} {Gσ : Sym3Flag k n}
    (hwfF : Fσ.WellFormed σg) (hwfG : Gσ.WellFormed σg)
    (hF : 𝕋.Mem Fσ.graph.toModel) (hG : 𝕋.Mem Gσ.graph.toModel) :
    Fσ.flagCountC Gσ
      = flagCount (Fσ.toLabeledFlag hwfF hF)
          (Gσ.toLabeledFlag hwfG hG) := by
  rw [Sym3Flag.flagCountC, flagCount]
  refine Finset.card_bij (fun W _ => W.val) ?_ ?_ ?_
  · rintro W hW
    obtain ⟨hroots, hiso⟩ := (Finset.mem_filter.mp hW).2
    exact typed_mem_flagWitnesses_of_isIso hwfF hwfG hF hG
      (Finset.mem_powersetCard.mp W.property).2 hroots hiso
  · rintro W _ W' _ h
    exact Subtype.ext h
  · rintro W hW
    have hcard : W.card = m := typed_card_of_mem_flagWitnesses hW
    have hmem : W ∈ (Finset.univ.powersetCard m : Finset (Finset (Fin n))) :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
    exact ⟨⟨W, hmem⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,
      typed_pred_of_mem_flagWitnesses hW _⟩, rfl⟩

/-- The typed density of literal flags is the computable typed count over
the binomial normalizer. -/
theorem Sym3Flag.subflagDensity_toFlag {𝕋 : RelTheory hypergraph3Sig}
    {σg : Sym3Graph k} {Fσ : Sym3Flag k m} {Gσ : Sym3Flag k n}
    (hwfF : Fσ.WellFormed σg) (hwfG : Gσ.WellFormed σg)
    (hF : 𝕋.Mem Fσ.graph.toModel) (hG : 𝕋.Mem Gσ.graph.toModel) :
    subflagDensity (Fσ.toFlag hwfF hF) (Gσ.toFlag hwfG hG)
      = (Fσ.flagCountC Gσ : ℚ) / ((n - k).choose (m - k) : ℚ) := by
  rw [Sym3Flag.toFlag, Sym3Flag.toFlag, subflagDensity_mk, flagDensity,
    ← Sym3Flag.flagCountC_eq_flagCount hwfF hwfG hF hG]
  simp

/-! #### Typed pair densities

The quadratic-form coefficients `p₂(F₁, F₂; H)` of semidefinite
certificates, on literals: pairs of root-containing subsets sharing only
the roots, each inducing a root-preserving copy. -/

private lemma mem_rootFinset_toLabeledFlag_iff
    {𝕋 : RelTheory hypergraph3Sig} {σg : Sym3Graph k} {Gσ : Sym3Flag k n}
    {hwfG : Gσ.WellFormed σg} {hG : 𝕋.Mem Gσ.graph.toModel} {x : Fin n} :
    x ∈ (Gσ.toLabeledFlag hwfG hG).rootFinset ↔ ∃ i, Gσ.roots i = x := by
  rw [LabeledFlag.rootFinset]
  constructor
  · intro hx
    obtain ⟨i, -, hi⟩ := Finset.mem_map.mp hx
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, hi⟩

variable {m₁ m₂ : ℕ} in
/-- The computable typed pair count: pairs of root-containing subsets
sharing only the roots, each inducing a root-preserving copy. -/
def Sym3Flag.flagPairCountC (F₁ : Sym3Flag k m₁) (F₂ : Sym3Flag k m₂)
    (Gσ : Sym3Flag k n) : ℕ :=
  (((Finset.univ.powersetCard m₁ : Finset (Finset (Fin n))) ×ˢ
      (Finset.univ.powersetCard m₂ : Finset (Finset (Fin n)))).attach.filter
    fun P => (∀ x ∈ P.val.1, x ∈ P.val.2 → ∃ i, Gσ.roots i = x)
      ∧ (∃ h : ∀ i, Gσ.roots i ∈ P.val.1,
          F₁.IsIso (Gσ.pullbackFlag P.val.1
            (Finset.mem_powersetCard.mp
              (Finset.mem_product.mp P.property).1).2 h))
      ∧ (∃ h : ∀ i, Gσ.roots i ∈ P.val.2,
          F₂.IsIso (Gσ.pullbackFlag P.val.2
            (Finset.mem_powersetCard.mp
              (Finset.mem_product.mp P.property).2).2 h))).card

variable {m₁ m₂ : ℕ} in
/-- **Typed pair agreement**: the computable typed pair count is the
specification-layer pair count of the typed labeled flags. -/
theorem Sym3Flag.flagPairCountC_eq_pairCount
    {𝕋 : RelTheory hypergraph3Sig} {σg : Sym3Graph k}
    {F₁ : Sym3Flag k m₁} {F₂ : Sym3Flag k m₂} {Gσ : Sym3Flag k n}
    (hwf₁ : F₁.WellFormed σg) (hwf₂ : F₂.WellFormed σg)
    (hwfG : Gσ.WellFormed σg)
    (h₁ : 𝕋.Mem F₁.graph.toModel) (h₂ : 𝕋.Mem F₂.graph.toModel)
    (hG : 𝕋.Mem Gσ.graph.toModel) :
    F₁.flagPairCountC F₂ Gσ
      = pairCount (F₁.toLabeledFlag hwf₁ h₁) (F₂.toLabeledFlag hwf₂ h₂)
          (Gσ.toLabeledFlag hwfG hG) := by
  rw [Sym3Flag.flagPairCountC, pairCount]
  refine Finset.card_bij (fun P _ => P.val) ?_ ?_ ?_
  · rintro P hP
    obtain ⟨hshared, ⟨hr₁, hiso₁⟩, hr₂, hiso₂⟩ := (Finset.mem_filter.mp hP).2
    refine mem_pairWitnesses.mpr
      ⟨typed_mem_flagWitnesses_of_isIso hwf₁ hwfG h₁ hG _ hr₁ hiso₁,
       typed_mem_flagWitnesses_of_isIso hwf₂ hwfG h₂ hG _ hr₂ hiso₂,
       fun x hx₁ hx₂ => mem_rootFinset_toLabeledFlag_iff.mpr
         (hshared x hx₁ hx₂)⟩
  · rintro P _ P' _ h
    exact Subtype.ext h
  · rintro P hP
    obtain ⟨hW₁, hW₂, hshared⟩ := mem_pairWitnesses.mp hP
    have hc₁ : P.1.card = m₁ := typed_card_of_mem_flagWitnesses hW₁
    have hc₂ : P.2.card = m₂ := typed_card_of_mem_flagWitnesses hW₂
    have hmem : P ∈ (Finset.univ.powersetCard m₁ :
        Finset (Finset (Fin n))) ×ˢ
        (Finset.univ.powersetCard m₂ : Finset (Finset (Fin n))) :=
      Finset.mem_product.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hc₁⟩,
         Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hc₂⟩⟩
    refine ⟨⟨P, hmem⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,
      fun x hx₁ hx₂ => mem_rootFinset_toLabeledFlag_iff.mp
        (hshared x hx₁ hx₂),
      typed_pred_of_mem_flagWitnesses hW₁ _,
      typed_pred_of_mem_flagWitnesses hW₂ _⟩, rfl⟩

variable {m₁ m₂ : ℕ} in
/-- The typed pair density of literal flags is the computable typed pair
count over the pair normalizer. -/
theorem Sym3Flag.subflagPairDensity_toFlag
    {𝕋 : RelTheory hypergraph3Sig} {σg : Sym3Graph k}
    {F₁ : Sym3Flag k m₁} {F₂ : Sym3Flag k m₂} {Gσ : Sym3Flag k n}
    (hwf₁ : F₁.WellFormed σg) (hwf₂ : F₂.WellFormed σg)
    (hwfG : Gσ.WellFormed σg)
    (h₁ : 𝕋.Mem F₁.graph.toModel) (h₂ : 𝕋.Mem F₂.graph.toModel)
    (hG : 𝕋.Mem Gσ.graph.toModel) :
    subflagPairDensity (F₁.toFlag hwf₁ h₁) (F₂.toFlag hwf₂ h₂)
        (Gσ.toFlag hwfG hG)
      = (F₁.flagPairCountC F₂ Gσ : ℚ)
        / (pairChoose (n - k) (m₁ - k) (m₂ - k) : ℚ) := by
  rw [Sym3Flag.toFlag, Sym3Flag.toFlag, Sym3Flag.toFlag,
    subflagPairDensity_mk, flagPairDensity,
    ← Sym3Flag.flagPairCountC_eq_pairCount hwf₁ hwf₂ hwfG h₁ h₂ hG]
  simp

end Typed

end FlagAlgebras.Core
