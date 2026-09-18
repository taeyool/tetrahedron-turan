import LeanFlagAlgebras.Core.Compute.Sym3

/-! # Typed literal isomorphism is an equivalence

`Sym3Flag.IsIso` carries a root-preserving permutation; composing and
inverting those permutations gives symmetry and transitivity. Reflexivity
is already available.

Kept in a thin file on top of `Sym3` so the heavy example chains can use
these without pulling anything else in. -/

namespace FlagAlgebras.Core

variable {k n : ℕ}

/-- Typed literal isomorphism is symmetric. -/
lemma Sym3Flag.IsIso.symm {F H : Sym3Flag k n} (h : F.IsIso H) :
    H.IsIso F := by
  obtain ⟨p, hedges, hroots⟩ := h
  refine ⟨p⁻¹, ?_, ?_⟩
  · rw [← hedges, Finset.image_image]
    have hid : (Finset.image ⇑p⁻¹ ∘ Finset.image ⇑p) = id := by
      funext e
      simp [Finset.image_image]
    rw [hid, Finset.image_id]
  · funext t
    have ht : p (F.roots t) = H.roots t := congrFun hroots t
    show p⁻¹ (H.roots t) = F.roots t
    rw [← ht]
    exact p.symm_apply_apply _

/-- Typed literal isomorphism is transitive. -/
lemma Sym3Flag.IsIso.trans {F H K : Sym3Flag k n} (h₁ : F.IsIso H)
    (h₂ : H.IsIso K) : F.IsIso K := by
  obtain ⟨p, hedges, hroots⟩ := h₁
  obtain ⟨q, hedges', hroots'⟩ := h₂
  refine ⟨p.trans q, ?_, ?_⟩
  · rw [← hedges', ← hedges, Finset.image_image]
    refine Finset.image_congr fun e _ => ?_
    show Finset.image (⇑(p.trans q)) e = Finset.image ⇑q (Finset.image ⇑p e)
    rw [Finset.image_image]
    rfl
  · funext t
    have ht : p (F.roots t) = H.roots t := congrFun hroots t
    have ht' : q (H.roots t) = K.roots t := congrFun hroots' t
    show q (p (F.roots t)) = K.roots t
    rw [ht, ht']

end FlagAlgebras.Core
