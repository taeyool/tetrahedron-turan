import LeanFlagAlgebras.Core.Theory

/-! # Core: forbidden-substructure subtheories

Turán-type theories: given a base theory `𝕋` and a pattern model `P`,
`RelTheory.forbid` carves out the members containing no (not necessarily
induced) copy of `P`. Freeness is hereditary and isomorphism-invariant for
free; inhabitedness at every size is a hypothesis (discharged by the
discrete model whenever the base theory contains it and the pattern has at
least one relation instance). Pad-closure — the property powering flags of
every size in the flag algebra — persists exactly when the pattern has no
isolated vertices, since a copy of such a pattern in a padding must live
inside the embedded part. -/

namespace FlagAlgebras.Core

variable {S : Signature} {V V₀ W : Type}

/-- `M` contains a (not necessarily induced) copy of the pattern `P`:
an injection carrying every relation instance of `P` to one of `M`. -/
def Model.Contains (M : Model S W) (P : Model S V₀) : Prop :=
  ∃ f : V₀ ↪ W, ∀ (r : S.Rel) (g : Fin (S.ar r) → V₀),
    P.interp r g → M.interp r (f ∘ g)

/-- Containment transports along model isomorphisms. -/
lemma Model.Contains.of_iso {M : Model S V} {N : Model S W}
    (e : M ≃ᵣ N) {P : Model S V₀} (h : M.Contains P) : N.Contains P := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f.trans e.toEquiv.toEmbedding, fun r g hg => ?_⟩
  exact (e.interp_iff r (f ∘ g)).mpr (hf r g hg)

/-- Containment is reflected by induced substructures. -/
lemma Model.Contains.of_comap {M : Model S W} (f : V ↪ W) {P : Model S V₀}
    (h : (M.comap f).Contains P) : M.Contains P := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g.trans f, fun r t ht => hg r t ht⟩

/-- Every vertex of the pattern occurs in some relation instance. For
uniform patterns this says: no isolated vertices. -/
def Model.NoIsolated (P : Model S V₀) : Prop :=
  ∀ v : V₀, ∃ (r : S.Rel) (g : Fin (S.ar r) → V₀) (i : Fin (S.ar r)),
    P.interp r g ∧ g i = v

/-- A copy of an isolated-vertex-free pattern inside a padding lives in the
embedded part, hence reflects to the original model. -/
lemma Model.Contains.of_pad {M : Model S V} {f : V ↪ W} {P : Model S V₀}
    (hno : P.NoIsolated) (h : (M.pad f).Contains P) : M.Contains P := by
  classical
  obtain ⟨g, hg⟩ := h
  have hrange : ∀ v : V₀, g v ∈ Set.range f := by
    intro v
    obtain ⟨r, t, i, ht, hti⟩ := hno v
    obtain ⟨t', hft', -⟩ := hg r t ht
    rw [← hti]
    exact ⟨t' i, congrFun hft' i⟩
  choose g₀ hg₀ using hrange
  have hginj : Function.Injective g₀ := by
    intro a b hab
    apply g.injective
    rw [← hg₀ a, ← hg₀ b, hab]
  refine ⟨⟨g₀, hginj⟩, fun r t ht => ?_⟩
  obtain ⟨t', hft', hMt'⟩ := hg r t ht
  have ht' : t' = g₀ ∘ t := by
    funext i
    apply f.injective
    have h1 : f (t' i) = g (t i) := congrFun hft' i
    rw [h1]
    exact (hg₀ (t i)).symm
  exact ht' ▸ hMt'

/-- The subtheory of `𝕋` forbidding the pattern `P`, given a witness family
of `P`-free members at every size. -/
def RelTheory.forbid (𝕋 : RelTheory S) {V₀ : Type} (P : Model S V₀)
    (hinh : ∀ n : ℕ, ∃ M : Model S (Fin n), 𝕋.Mem M ∧ ¬M.Contains P) :
    RelTheory S where
  Mem _ M := 𝕋.Mem M ∧ ¬M.Contains P
  mem_iso := fun {_ _ _ _} e h =>
    ⟨𝕋.mem_iso e h.1, fun hc => h.2 (hc.of_iso e.symm)⟩
  mem_comap := fun {_ _} f {_} h =>
    ⟨𝕋.mem_comap f h.1, fun hc => h.2 (hc.of_comap f)⟩
  mem_inhabited := hinh

@[simp]
lemma RelTheory.mem_forbid_iff {𝕋 : RelTheory S} {P : Model S V₀}
    {hinh : ∀ n : ℕ, ∃ M : Model S (Fin n), 𝕋.Mem M ∧ ¬M.Contains P}
    (M : Model S V) :
    (𝕋.forbid P hinh).Mem M ↔ 𝕋.Mem M ∧ ¬M.Contains P :=
  Iff.rfl

/-- Forbidding an isolated-vertex-free pattern preserves pad-closure. -/
theorem RelTheory.forbid_padClosed {𝕋 : RelTheory S} [𝕋.PadClosed]
    {P : Model S V₀}
    {hinh : ∀ n : ℕ, ∃ M : Model S (Fin n), 𝕋.Mem M ∧ ¬M.Contains P}
    (hno : P.NoIsolated) : (𝕋.forbid P hinh).PadClosed where
  mem_pad := fun {_ _} f {_} h =>
    ⟨RelTheory.PadClosed.mem_pad f h.1, fun hc => h.2 (hc.of_pad hno)⟩

/-- Freeness witnesses from the discrete model: available whenever the base
theory contains it and the pattern has at least one relation instance. -/
lemma forbid_inhabited_of_discrete (𝕋 : RelTheory S)
    (hdisc : ∀ n : ℕ, 𝕋.Mem (Model.discrete S (Fin n)))
    {P : Model S V₀} (hP : ∃ r g, P.interp r g) :
    ∀ n : ℕ, ∃ M : Model S (Fin n), 𝕋.Mem M ∧ ¬M.Contains P := by
  intro n
  refine ⟨Model.discrete S (Fin n), hdisc n, ?_⟩
  rintro ⟨f, hf⟩
  obtain ⟨r, g, hg⟩ := hP
  exact Model.discrete_interp r (f ∘ g) (hf r g hg)

end FlagAlgebras.Core
