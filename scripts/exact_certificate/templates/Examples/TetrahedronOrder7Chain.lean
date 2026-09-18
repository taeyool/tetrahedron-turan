import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Induced

/-! # The level-6 to level-7 chain rule

A six-vertex class sits inside a seven-vertex class with a density: the
fraction of six-element vertex subsets inducing it. In a seven-vertex
graph there are exactly seven such subsets, one per deleted vertex, and
the induced subgraph on each is a deck. So the density is simply how
many of the seven decks land in the class, over seven.

That is the rule the certificate's deck sum implements, and this file
proves it. The only real step is the correspondence between six-element
subsets and vertices — a subset of size six in a seven-element set is
the complement of a single vertex — which turns the subflag count into
a count over `Fin 7`. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

/-- The complement of a vertex, as a six-element subset. -/
private def complSub (v : Fin 7) :
    {W : Finset (Fin 7) // W ∈ Finset.univ.powersetCard 6} :=
  ⟨{v}ᶜ, Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, card_compl_singleton7 v⟩⟩

private lemma pullback_complSub (m : ℕ) (v : Fin 7)
    (hc : (complSub v).val.card = 6) :
    (graphOfMask 7 m).pullback (subsetTuple (complSub v).val hc)
      = graphOfMask 6 (deckMask v m) :=
  pullback_compl_singleton v m hc

/-- **The subflag count is a deck count**: a six-vertex pattern occurs in
a seven-vertex mask once for each deck isomorphic to it. -/
theorem flagCountC_graphOfMask7 (F : Sym3Graph 6) (m : ℕ) :
    F.flagCountC (graphOfMask 7 m)
      = (Finset.univ.filter fun v : Fin 7 =>
          F.IsIso (graphOfMask 6 (deckMask v m))).card := by
  rw [Sym3Graph.flagCountC]
  refine (Finset.card_bij (fun v _ => complSub v) ?_ ?_ ?_).symm
  · intro v hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ?_⟩
    show F.IsIso ((graphOfMask 7 m).pullback (subsetTuple (complSub v).val _))
    rw [pullback_complSub]
    exact (Finset.mem_filter.mp hv).2
  · intro v₁ _ v₂ _ h
    have hv : ({v₁}ᶜ : Finset (Fin 7)) = {v₂}ᶜ := congrArg Subtype.val h
    have hs : ({v₁} : Finset (Fin 7)) = {v₂} := by
      simpa using congrArg (fun s : Finset (Fin 7) => sᶜ) hv
    simpa using hs
  · intro W hW
    have hcard : W.val.card = 6 := (Finset.mem_powersetCard.mp W.property).2
    have hc : W.valᶜ.card = 1 := by
      rw [Finset.card_compl, hcard, Fintype.card_fin]
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
    have hWv : W.val = ({v}ᶜ : Finset (Fin 7)) := by
      conv_lhs => rw [← compl_compl W.val]
      rw [hv]
    have hW' : W = complSub v := Subtype.ext hWv
    subst hW'
    refine ⟨v, ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h2 := (Finset.mem_filter.mp hW).2
    rwa [pullback_complSub] at h2

/-- **The level-6 to level-7 chain rule**: the density of a six-vertex
class in a seven-vertex class is the fraction of the seven decks lying
in it.

This is what makes the certificate's deck sum an average. Each of the
seven `classNum` lookups is taken over `720 * scale ^ 2`, and the column
over `5040 * scale ^ 2 = 7 * 720 * scale ^ 2`; the factor of seven is
exactly the normalizer here. -/
theorem subflagDensity_deck {F : Sym3Graph 6} (hF : TetraFree.Mem F.toModel)
    {m : ℕ} (hm : TetraFree.Mem (graphOfMask 7 m).toModel) :
    subflagDensity (F.toFlag hF) ((graphOfMask 7 m).toFlag hm)
      = ((Finset.univ.filter fun v : Fin 7 =>
            F.IsIso (graphOfMask 6 (deckMask v m))).card : ℚ) / 7 := by
  rw [Sym3Graph.subflagDensity_toFlag, flagCountC_graphOfMask7,
    show Nat.choose 7 6 = 7 from rfl]
  norm_num

end FlagAlgebras.Core.Tetrahedron
