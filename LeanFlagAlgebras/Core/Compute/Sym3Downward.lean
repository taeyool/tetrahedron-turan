import LeanFlagAlgebras.Core.Compute.Sym3
import LeanFlagAlgebras.Core.Downward

/-! # Core compute layer: the downward operator on literals

The labeling count of a typed literal flag — the number of root tuples
of its graph realizing the same typed class — computably, with the
agreement theorem, and the resulting literal formula for the downward
image of a basis vector:

`⟦F⟧↓ = (labelingCountC / (n)_k) • ⟦F.graph⟧`.

This is the `q`-half of the product-expansion tables of semidefinite
certificates. -/

namespace FlagAlgebras.Core

open Classical

variable {n k : ℕ}

/-- The computable labeling count: root tuples of the graph realizing the
same typed class. -/
def Sym3Flag.labelingCountC (σg : Sym3Graph k) (Fσ : Sym3Flag k n) : ℕ :=
  (Finset.univ.filter fun θ : Fin k → Fin n =>
    (Sym3Flag.mk Fσ.graph θ).WellFormed σg
      ∧ (Sym3Flag.mk Fσ.graph θ).IsIso Fσ).card

/-- **Agreement**: the computable labeling count is the specification
layer's labeling count of the typed labeled flag over its own
unlabeling. -/
theorem Sym3Flag.labelingCountC_eq_labelingCount
    {𝕋 : RelTheory hypergraph3Sig} {σg : Sym3Graph k} {Fσ : Sym3Flag k n}
    (hwf : Fσ.WellFormed σg) (hmem : 𝕋.Mem Fσ.graph.toModel) :
    Fσ.labelingCountC σg
      = labelingCount (Fσ.toLabeledFlag hwf hmem).unlabel
          (Fσ.toLabeledFlag (𝕋 := 𝕋) hwf hmem) := by
  rw [Sym3Flag.labelingCountC, labelingCount]
  refine Finset.card_bij
    (fun θ hθ => ⟨θ, ((Finset.mem_filter.mp hθ).2.1).1⟩) ?_ ?_ ?_
  · intro θ hθ
    obtain ⟨-, hwf', hiso⟩ := Finset.mem_filter.mp hθ
    have hvalid : ∀ (r : hypergraph3Sig.Rel) (f : Fin 3 → Fin k),
        (Fσ.toLabeledFlag hwf hmem).unlabel.toModel.interp r
          (⇑(⟨θ, hwf'.1⟩ : Fin k ↪ Fin n) ∘ f) ↔ σg.toModel.interp r f :=
      fun r f =>
        ((Sym3Flag.mk Fσ.graph θ).toLabeledFlag (𝕋 := 𝕋)
          hwf' hmem).rootEmbed.interp_iff r f
    refine mem_flagLabelings.mpr ⟨hvalid, ?_⟩
    obtain ⟨j⟩ := (Sym3Flag.isIso_iff_nonempty_flagIso
      hwf' hwf hmem hmem).mp hiso
    exact ⟨j⟩
  · intro θ₁ h₁ θ₂ h₂ heq
    exact congrArg (fun e : Fin k ↪ Fin n => (e : Fin k → Fin n)) heq
  · intro θ hθ
    obtain ⟨hvalid, ⟨i⟩⟩ := mem_flagLabelings.mp hθ
    have hwf' : (Sym3Flag.mk Fσ.graph ⇑θ).WellFormed σg := by
      refine ⟨θ.injective, ?_⟩
      apply Sym3Graph.toModel_injective
      rw [Sym3Graph.pullback_toModel _ θ.injective]
      refine Model.ext ?_
      funext r f
      cases r
      exact propext (hvalid () f)
    have hiso : (Sym3Flag.mk Fσ.graph ⇑θ).IsIso Fσ :=
      (Sym3Flag.isIso_iff_nonempty_flagIso hwf' hwf hmem hmem).mpr ⟨i⟩
    exact ⟨⇑θ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwf', hiso⟩,
      Function.Embedding.ext fun x => rfl⟩

/-- The unlabeling of the typed literal class is the literal class of its
graph. -/
theorem Sym3Flag.out_unlabel_toFlag {𝕋 : RelTheory hypergraph3Sig}
    {σg : Sym3Graph k} {Fσ : Sym3Flag k n}
    (hwf : Fσ.WellFormed σg) (hmem : 𝕋.Mem Fσ.graph.toModel) :
    (Quotient.out (Fσ.toFlag (𝕋 := 𝕋) hwf hmem)).unlabel.toFlag
      = Fσ.graph.toFlag hmem := by
  have h1 : (Quotient.out (Fσ.toFlag (𝕋 := 𝕋) hwf hmem)).unlabel.toFlag
      = Flag.unlabel (Fσ.toFlag (𝕋 := 𝕋) hwf hmem) := by
    conv_rhs => rw [← Quotient.out_eq (Fσ.toFlag (𝕋 := 𝕋) hwf hmem)]
    rfl
  rw [h1]
  rfl

/-- The labeling factor of a typed literal class, evaluated: the
computable labeling count over the falling factorial. -/
theorem Sym3Flag.labelingFactor_out {𝕋 : RelTheory hypergraph3Sig}
    {σg : Sym3Graph k} {Fσ : Sym3Flag k n}
    (hwf : Fσ.WellFormed σg) (hmem : 𝕋.Mem Fσ.graph.toModel) :
    labelingFactor
      (Quotient.out (Fσ.toFlag (𝕋 := 𝕋) hwf hmem)).unlabel
      (Quotient.out (Fσ.toFlag (𝕋 := 𝕋) hwf hmem))
      = (Fσ.labelingCountC σg : ℚ) / (n.descFactorial k : ℚ) := by
  obtain ⟨e⟩ := Quotient.exact
    ((Fσ.toFlag (𝕋 := 𝕋) hwf hmem).out_eq)
  rw [labelingFactor_congr e.unlabel e, labelingFactor,
    ← Sym3Flag.labelingCountC_eq_labelingCount hwf hmem,
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]

/-- **The literal downward formula**: the downward image of a typed
literal basis vector is the computable labeling factor times the basis
vector of its graph. -/
theorem Sym3Flag.downward_basisVector {𝕋 : RelTheory hypergraph3Sig}
    [𝕋.IsType (emptyType hypergraph3Sig)]
    {σg : Sym3Graph k} [𝕋.IsType σg.toModel] {Fσ : Sym3Flag k n}
    (hwf : Fσ.WellFormed σg) (hmem : 𝕋.Mem Fσ.graph.toModel) :
    downward (⟦basisVector ⟨n, Fσ.toFlag hwf hmem⟩⟧ :
        FlagAlgebra 𝕋 σg.toModel)
      = (((Fσ.labelingCountC σg : ℚ) / (n.descFactorial k : ℚ) : ℚ) : ℝ)
        • ⟦basisVector ⟨n, Fσ.graph.toFlag hmem⟩⟧ := by
  rw [downward_basis, Sym3Flag.labelingFactor_out hwf hmem,
    Sym3Flag.out_unlabel_toFlag hwf hmem]
