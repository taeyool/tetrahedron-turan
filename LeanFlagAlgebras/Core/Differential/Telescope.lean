import LeanFlagAlgebras.Core.Differential.Deletion
import LeanFlagAlgebras.Core.Differential.Stability
import LeanFlagAlgebras.Core.Limit.Realize

/-! # Core: deleting the vertices at which the derivative is positive

The finite core of Razborov's Theorem 4.3. For a host `H` on `n` vertices
and an objective `f`, call a vertex *good* when the rooted evaluation of the
vertex differential `∂₁ f` at it is at least `ε`. Deleting a good vertex
raises `p(f, ·)` by at least `ε/(2n)` (Lemma 4.2(a) in set form,
`vertex_deletion_hostEval_restrict`, together with the restriction
stability of `Core/Differential/Stability`), and deleting up to `t` good
vertices one after another raises it by `t · ε/(2n)`
(`hostEval_restrict_sdiff_ge`). Against this, every host of size at least
`m₀` evaluates `f` to at most `sup φ(f) + η` for any `η > 0`
(`eventually_densityEval_le`, from realization and compactness), which is
what makes a positive-measure set of good vertices impossible at a
maximizer. -/

namespace FlagAlgebras.Core

open Finset Filter
open Classical

variable {S : Signature} [S.NullaryFree] {𝕋 : RelTheory S}

/-! ## Lemma 4.2(a) in set form -/

section SetForm

variable {σ₁ : Model S (Fin 1)} [𝕋.VertexUniform σ₁]
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Deleting `v` from the induced sub-flag on `A ∋ v` is restricting to
`A ∖ v`. -/
noncomputable def deleteVertex_restrict_iso (N : LabeledFlag 𝕋 (emptyType S) V)
    {A : Finset V} {v : V} (hv : v ∈ A) :
    deleteVertex (N.restrict A (emptyType_root_mem N A)) ⟨v, hv⟩
      ≃ᶠ N.restrict (A.erase v) (emptyType_root_mem N _) := by
  unfold deleteVertex
  refine (N.restrictRestrict _ _).trans (N.restrictCongr ?_ _ _)
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    have hy' := (Finset.mem_erase.mp hy).1
    exact Finset.mem_erase.mpr ⟨fun h => hy' (Subtype.ext h), y.property⟩
  · intro hx
    obtain ⟨hxv, hxA⟩ := Finset.mem_erase.mp hx
    exact Finset.mem_map.mpr ⟨⟨x, hxA⟩,
      Finset.mem_erase.mpr ⟨fun h => hxv (congrArg Subtype.val h), Finset.mem_univ _⟩, rfl⟩

omit [Fintype V] in
/-- **Lemma 4.2(a) in set form**: for a root-containing set `A ∋ v` of
size `L + 1`,
`p(f, N|_{A∖v}) = p(f, N|_A) + (1/(L+1)) · p^{(N,v)|_A}(∂₁ f)`. -/
theorem vertex_deletion_hostEval_restrict (N : LabeledFlag 𝕋 (emptyType S) V)
    (f : FlagVector 𝕋 (emptyType S)) {A : Finset V} {v : V} (hv : v ∈ A) {L : ℕ}
    (hA : A.card = L + 1) (hf : ∀ M ∈ f.support, M.1 ≤ L) :
    hostEval (N.restrict (A.erase v) (emptyType_root_mem N _)) f
      = hostEval (N.restrict A (emptyType_root_mem N A)) f
        + (1 / ((L : ℝ) + 1))
          * hostEval ((rootedAt σ₁ N v).restrict A (fun _ => hv)) (partialVertexVec σ₁ f) := by
  have h := vertex_deletion_hostEval (σ₁ := σ₁) (N.restrict A (emptyType_root_mem N A)) ⟨v, hv⟩
    f (by rw [Fintype.card_coe, hA]) hf
  rw [hostEval_congr (deleteVertex_restrict_iso N hv) f, rootedAt_restrict] at h
  exact h

end SetForm

/-! ## Deleting good vertices -/

section Telescope

variable {σ₁ : Model S (Fin 1)} [𝕋.VertexUniform σ₁]
variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The telescoping deletion.** If every vertex of `Good` has rooted
`∂₁ f`-evaluation at least `ε`, then deleting any `E ⊆ Good` of at most `t`
vertices raises `p(f, ·)` by at least `|E| · ε/(2n)`, provided `t` is small
enough for the restriction stability to keep the rooted evaluations above
`ε/2`. -/
theorem hostEval_restrict_sdiff_ge (H : LabeledFlag 𝕋 (emptyType S) V)
    (f : FlagVector 𝕋 (emptyType S)) {ε : ℝ} (hε : 0 < ε) (Good : Finset V)
    (hGood : ∀ v ∈ Good, ε ≤ hostEval (rootedAt σ₁ H v) (partialVertexVec σ₁ f))
    {t : ℕ} (ht : t + 1 < Fintype.card V)
    (hsupp : ∀ M ∈ f.support, M.1 + t + 1 ≤ Fintype.card V)
    (hstab : (t : ℝ) * sizeNorm (partialVertexVec σ₁ f)
      ≤ (ε / 2) * ((Fintype.card V - t - 1 : ℕ) : ℝ)) :
    ∀ E : Finset V, E ⊆ Good → E.card ≤ t →
      hostEval H f + (E.card : ℝ) * (ε / 2) / (Fintype.card V : ℝ)
        ≤ hostEval (H.restrict (Finset.univ \ E) (emptyType_root_mem H _)) f := by
  intro E
  induction E using Finset.induction_on with
  | empty =>
    intro _ _
    rw [Finset.card_empty, Nat.cast_zero, zero_mul, zero_div, add_zero, Finset.sdiff_empty,
      hostEval_congr (H.restrictUniv _)]
  | insert u E hu ih =>
    intro hsub hcard
    have hE : E ⊆ Good := (Finset.subset_insert u E).trans hsub
    have hEcard : E.card ≤ t := by
      have := Finset.card_insert_of_notMem hu
      omega
    have hIH := ih hE hEcard
    set n := Fintype.card V with hn
    set A := Finset.univ \ E with hAdef
    have hAcard : A.card = n - E.card := Finset.card_univ_diff E
    have huA : u ∈ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, hu⟩
    have hAL : A.card = (n - E.card - 1) + 1 := by omega
    have hf : ∀ M ∈ f.support, M.1 ≤ n - E.card - 1 := fun M hM => by
      have := hsupp M hM
      omega
    have hdel := vertex_deletion_hostEval_restrict (σ₁ := σ₁) H f huA hAL hf
    rw [Finset.sdiff_insert]
    change hostEval H f + ((insert u E).card : ℝ) * (ε / 2) / (n : ℝ)
      ≤ hostEval (H.restrict (A.erase u) (emptyType_root_mem H _)) f
    rw [hdel, Finset.card_insert_of_notMem hu]
    -- the rooted evaluation stays above `ε/2`
    have hpos : (0 : ℝ) < ((A.card - 1 : ℕ) : ℝ) := by
      have : 1 < A.card := by omega
      exact_mod_cast Nat.sub_pos_of_lt this
    have hstab' := abs_hostEval_restrict_sub_le (rootedAt σ₁ H u) (partialVertexVec σ₁ f) E.card
      (fun _ => huA) (by omega) (by rw [Fintype.card_fin]; omega)
    have hbound : (E.card : ℝ) * sizeNorm (partialVertexVec σ₁ f) / ((A.card - 1 : ℕ) : ℝ)
        ≤ ε / 2 := by
      rw [div_le_iff₀ hpos]
      have h1 : (E.card : ℝ) * sizeNorm (partialVertexVec σ₁ f)
          ≤ (t : ℝ) * sizeNorm (partialVertexVec σ₁ f) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hEcard) (sizeNorm_nonneg _)
      have h2 : ((n - t - 1 : ℕ) : ℝ) ≤ ((A.card - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show n - t - 1 ≤ A.card - 1 by omega)
      calc (E.card : ℝ) * sizeNorm (partialVertexVec σ₁ f)
          ≤ (t : ℝ) * sizeNorm (partialVertexVec σ₁ f) := h1
        _ ≤ (ε / 2) * ((n - t - 1 : ℕ) : ℝ) := hstab
        _ ≤ (ε / 2) * ((A.card - 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left h2 (by linarith)
    have hroot : ε / 2 ≤ hostEval ((rootedAt σ₁ H u).restrict A (fun _ => huA))
        (partialVertexVec σ₁ f) := by
      have hg := hGood u (hsub (Finset.mem_insert_self u E))
      have habs := hstab'.trans hbound
      rw [abs_le] at habs
      linarith [habs.1]
    -- assemble
    have hL1 : (0 : ℝ) < ((n - E.card - 1 : ℕ) : ℝ) + 1 := by positivity
    have hLn : ((n - E.card - 1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
      have : n - E.card - 1 + 1 ≤ n := by omega
      exact_mod_cast this
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hgain : (ε / 2) / (n : ℝ)
        ≤ (1 / (((n - E.card - 1 : ℕ) : ℝ) + 1))
          * hostEval ((rootedAt σ₁ H u).restrict A (fun _ => huA)) (partialVertexVec σ₁ f) := by
      rw [one_div_mul_eq_div]
      exact div_le_div₀ (by linarith) hroot hL1 hLn
    have key : hostEval H f + ((E.card + 1 : ℕ) : ℝ) * (ε / 2) / (n : ℝ)
        = (hostEval H f + (E.card : ℝ) * (ε / 2) / (n : ℝ)) + (ε / 2) / (n : ℝ) := by
      push_cast
      ring
    rw [key]
    exact add_le_add hIH hgain

end Telescope

/-! ## The maximality bound at large finite hosts -/

section Bound

variable [𝕋.IsType (emptyType S)]

omit [S.NullaryFree] in
/-- **Every large host evaluates the objective to at most its maximum plus
`η`.** Otherwise a sequence of violating hosts would realize a homomorphism
beating the maximizer. -/
theorem eventually_densityEval_le (φ₀ : PositiveHom 𝕋 (emptyType S))
    (f : FlagVector 𝕋 (emptyType S))
    (hmax : ∀ φ : PositiveHom 𝕋 (emptyType S), φ ⟦f⟧ ≤ φ₀ ⟦f⟧) {η : ℝ} (hη : 0 < η) :
    ∃ m₀ : ℕ, ∀ G : FinFlag 𝕋 (emptyType S), m₀ ≤ G.1 → densityEval f G ≤ φ₀ ⟦f⟧ + η := by
  by_contra hcon
  push_neg at hcon
  choose G hG using hcon
  have hsz : Tendsto (fun m => (G m).1) atTop atTop :=
    tendsto_atTop_mono (fun m => (hG m).1) tendsto_id
  obtain ⟨s, hs, ψ, hψ⟩ := exists_realized_subseq G hsz
  have hlim := realized_apply hψ f
  have hge : φ₀ ⟦f⟧ + η ≤ ψ ⟦f⟧ := by
    refine ge_of_tendsto hlim (Eventually.of_forall fun k => ?_)
    have := (hG (s k)).2
    rw [densityEval_apply] at this
    exact this.le
  linarith [hmax ψ]

omit [S.NullaryFree] [𝕋.IsType (emptyType S)] in
/-- A host evaluation on any finite carrier is the class evaluation of its
canonical relabeling. -/
theorem hostEval_eq_densityEval_reindex {T U : Type} [Fintype T] {σ : Model S T} [Fintype U]
    (G : LabeledFlag 𝕋 σ U) (f : FlagVector 𝕋 σ) :
    hostEval G f
      = densityEval f ⟨Fintype.card U, (G.reindex (Fintype.equivFin U)).toFlag⟩ := by
  rw [hostEval_congr (G.reindexIso (Fintype.equivFin U)), hostEval_toFlag]

end Bound

/-! ## Good vertices from an average -/

omit [S.NullaryFree] in
/-- If the average of a `[0,1]`-valued function vanishing off `P` is at least
`δ`, then `P` holds on at least a `δ` fraction of the points. -/
theorem card_filter_ge_of_avg {V : Type} [Fintype V] (g : V → ℝ) (hg1 : ∀ v, g v ≤ 1)
    (P : V → Prop) [DecidablePred P] (hP : ∀ v, ¬ P v → g v = 0) {δ : ℝ}
    (h : δ * Fintype.card V ≤ ∑ v, g v) :
    δ * Fintype.card V ≤ ((Finset.univ.filter P).card : ℝ) := by
  refine h.trans ?_
  calc ∑ v, g v
      = ∑ v ∈ Finset.univ.filter P, g v + ∑ v ∈ Finset.univ.filter (fun v => ¬ P v), g v :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ = ∑ v ∈ Finset.univ.filter P, g v := by
        rw [Finset.sum_eq_zero fun v hv => hP v (Finset.mem_filter.mp hv).2, add_zero]
    _ ≤ ∑ _v ∈ Finset.univ.filter P, (1 : ℝ) := Finset.sum_le_sum fun v _ => hg1 v
    _ = ((Finset.univ.filter P).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end FlagAlgebras.Core
