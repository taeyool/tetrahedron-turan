import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Realize
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Verified

/-! # Coverage: the bound reaches every seven-vertex graph

The sweep bounded the certificate column on every admissible extension of
a listed representative; the realization theorem says every
tetrahedron-free seven-vertex graph is isomorphic to such an extension.
Putting the two together: every tetrahedron-free seven-vertex graph is
isomorphic to one whose column obeys the bound.

That is the form the flag-algebra assembly will consume, since a flag
class is exactly an isomorphism class. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

/-- Tetrahedron-freeness is an isomorphism invariant, read at the level
of masks. -/
lemma k4FreeMask_of_isIso {a b : ℕ}
    (hiso : (graphOfMask 7 a).IsIso (graphOfMask 7 b))
    (ha : k4FreeMask (quadIdxList 7) a = true) :
    k4FreeMask (quadIdxList 7) b = true := by
  rw [k4FreeMask_iff_mem] at ha ⊢
  obtain ⟨e⟩ := (Sym3Graph.isIso_iff_nonempty_modelIso _ _).mp hiso
  exact ⟨(graphOfMask 7 b).toModel_mem,
    fun hc => ha.2 (Model.Contains.of_iso e.symm hc)⟩

/-- **Coverage**: every tetrahedron-free seven-vertex graph is isomorphic
to one whose certificate column obeys the bound. -/
theorem exists_bounded_isIso {m : ℕ}
    (hk4 : k4FreeMask (quadIdxList 7) m = true) :
    ∃ e : ℕ, (graphOfMask 7 m).IsIso (graphOfMask 7 e)
      ∧ columnValue e ≤ columnBound := by
  obtain ⟨h, hh, link, hlink, hiso⟩ := exists_extension_isIso hk4
  refine ⟨extendMask h link, hiso, columnValue_le_columnBound hh hlink ?_⟩
  rw [qs7_eq]
  exact k4FreeMask_of_isIso hiso hk4

/-! ## The same statement about graphs

Masks are an encoding; the flag layer speaks about `Sym3Graph`. Every
seven-vertex graph is the decoding of a mask, so the coverage statement
transfers verbatim. -/

set_option maxRecDepth 65536 in
/-- Rank injectivity on the listed seven-vertex triples. -/
lemma finTriples7_rank_inj : ∀ t₁ ∈ finTriples 7, ∀ t₂ ∈ finTriples 7,
    triIdx 7 t₁.1.val t₁.2.1.val t₁.2.2.val
      = triIdx 7 t₂.1.val t₂.2.1.val t₂.2.2.val → t₁ = t₂ := by decide

set_option maxRecDepth 65536 in
/-- Rank bound on the listed seven-vertex triples. -/
lemma finTriples7_rank_lt :
    ∀ t ∈ finTriples 7, triIdx 7 t.1.val t.2.1.val t.2.2.val < 35 := by decide

/-- **Coverage, for graphs**: every tetrahedron-free seven-vertex
3-graph is isomorphic to a decoded mask whose certificate column obeys
the bound. -/
theorem exists_bounded_graph (G : Sym3Graph 7) (hG : TetraFree.Mem G.toModel) :
    ∃ e : ℕ, G.IsIso (graphOfMask 7 e) ∧ columnValue e ≤ columnBound := by
  obtain ⟨m, -, hm⟩ :=
    exists_mask_graphOfMask (k := 35) finTriples7_rank_inj finTriples7_rank_lt G
  obtain ⟨e, hiso, hle⟩ :=
    exists_bounded_isIso (m := m) (k4FreeMask_iff_mem.mpr (by rw [hm]; exact hG))
  exact ⟨e, by rw [← hm]; exact hiso, hle⟩

end FlagAlgebras.Core.Tetrahedron
