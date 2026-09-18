import LeanFlagAlgebras.Core.Compute.Sym3FlagIso
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7GatherPull
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7RootFlags
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7ExtS1
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7ExtS3

/-! # The index lookups are isomorphism indicators

A cell of the `s1`/`s3` folds looks up two flag indices in a table and
reads a Gram entry. The lookup is an isomorphism test in disguise: the
gather word already *is* the pullback mask
(`graphOfMask_gather4`/`graphOfMask_gather5`), the extension flags are
that pullback with standard roots, and the table specifications say the
index names an isomorphic flag. Distinctness of the canonical flags
makes the index unique, so the lookup and the indicator agree.

Nothing here computes; the three facts compose. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

open Classical

/-! ## One root -/

/-- The one-root gather mask decodes to the extension flag's graph. -/
lemma gather4_graph_eq {w : ℕ} {u a b c : Fin 7}
    (hinj : Function.Injective ![u, a, b, c]) :
    graphOfMask 4 (gatherBits (mkGather4 u.val a.val b.val c.val) 4 w)
      = (extFlagS1 (graphOfMask 7 w) ![u] a b c).graph := by
  have h := graphOfMask_gather4 w ![u, a, b, c] hinj
  have hnorm : ∀ i : Fin 4, (![u, a, b, c] i : Fin 7)
      = ![u, a, b, c] i := fun _ => rfl
  show graphOfMask 4 (gatherBits (mkGather4
      ((![u, a, b, c] : Fin 4 → Fin 7) 0).val
      ((![u, a, b, c] : Fin 4 → Fin 7) 1).val
      ((![u, a, b, c] : Fin 4 → Fin 7) 2).val
      ((![u, a, b, c] : Fin 4 → Fin 7) 3).val) 4 w) = _
  rw [h]
  rfl

/-- **The one-root index is the isomorphism indicator.** -/
lemma s1Idx_iso {w : ℕ} {u a b c : Fin 7} {i : ℕ} (hi : i < 7)
    (hmask : gatherBits (mkGather4 u.val a.val b.val c.val) 4 w < 16)
    (hinj : Function.Injective ![u, a, b, c])
    (hk4 : k4FreeMask (quadIdxList 4)
      (gatherBits (mkGather4 u.val a.val b.val c.val) 4 w) = true) :
    (s1IdxT.getD (gatherBits (mkGather4 u.val a.val b.val c.val) 4 w) 999
        = i)
      ↔ (s1Flag i).IsIso (extFlagS1 (graphOfMask 7 w) ![u] a b c) := by
  obtain ⟨hlt, hiso⟩ := s1_table_spec _ hmask hk4
  have hgr := gather4_graph_eq (w := w) hinj
  have hext : (Sym3Flag.mk
        (graphOfMask 4 (gatherBits
          (mkGather4 u.val a.val b.val c.val) 4 w)) ![0])
      = extFlagS1 (graphOfMask 7 w) ![u] a b c := by
    rw [Sym3Flag.mk.injEq]
    exact ⟨hgr, rfl⟩
  rw [hext] at hiso
  constructor
  · rintro rfl
    exact hiso.symm
  · intro hiso'
    by_contra hne
    exact s1Flag_pairwise _ hlt i hi (fun h => hne h)
      (hiso.symm.trans hiso'.symm)

/-! ## Three roots -/

/-- The three-root gather mask decodes to the extension flag's graph. -/
lemma gather5_graph_eq {w : ℕ} {r0 r1 r2 v x : Fin 7}
    (hinj : Function.Injective ![r0, r1, r2, v, x]) :
    graphOfMask 5 (gatherBits
        (mkGather5 r0.val r1.val r2.val v.val x.val) 10 w)
      = (extFlagS3 (graphOfMask 7 w) ![r0, r1, r2] v x).graph := by
  have h := graphOfMask_gather5 w ![r0, r1, r2, v, x] hinj
  show graphOfMask 5 (gatherBits (mkGather5
      ((![r0, r1, r2, v, x] : Fin 5 → Fin 7) 0).val
      ((![r0, r1, r2, v, x] : Fin 5 → Fin 7) 1).val
      ((![r0, r1, r2, v, x] : Fin 5 → Fin 7) 2).val
      ((![r0, r1, r2, v, x] : Fin 5 → Fin 7) 3).val
      ((![r0, r1, r2, v, x] : Fin 5 → Fin 7) 4).val) 10 w) = _
  rw [h]
  rfl

/-- **The nonedge-root index is the isomorphism indicator.** -/
lemma s30Idx_iso {w : ℕ} {r0 r1 r2 v x : Fin 7} {i : ℕ} (hi : i < 236)
    (hmask : gatherBits (mkGather5 r0.val r1.val r2.val v.val x.val)
      10 w < 1024)
    (hinj : Function.Injective ![r0, r1, r2, v, x])
    (hk4 : k4FreeMask (quadIdxList 5) (gatherBits
      (mkGather5 r0.val r1.val r2.val v.val x.val) 10 w) = true)
    (hbit : (gatherBits (mkGather5 r0.val r1.val r2.val v.val x.val)
      10 w).testBit 0 = false) :
    (s3Idx0T.getD (gatherBits
        (mkGather5 r0.val r1.val r2.val v.val x.val) 10 w) 999 = i)
      ↔ (s30Flag i).IsIso
          (extFlagS3 (graphOfMask 7 w) ![r0, r1, r2] v x) := by
  obtain ⟨hlt, hiso⟩ := s30_table_spec _ hmask hk4 hbit
  have hgr := gather5_graph_eq (w := w) hinj
  have hext : (Sym3Flag.mk
        (graphOfMask 5 (gatherBits
          (mkGather5 r0.val r1.val r2.val v.val x.val) 10 w)) ![0, 1, 2])
      = extFlagS3 (graphOfMask 7 w) ![r0, r1, r2] v x := by
    rw [Sym3Flag.mk.injEq]
    exact ⟨hgr, rfl⟩
  rw [hext] at hiso
  constructor
  · rintro rfl
    exact hiso.symm
  · intro hiso'
    by_contra hne
    exact s30Flag_pairwise _ hlt i hi (fun h => hne h)
      (hiso.symm.trans hiso'.symm)

/-- **The edge-root index is the isomorphism indicator.** -/
lemma s31Idx_iso {w : ℕ} {r0 r1 r2 v x : Fin 7} {i : ℕ} (hi : i < 191)
    (hmask : gatherBits (mkGather5 r0.val r1.val r2.val v.val x.val)
      10 w < 1024)
    (hinj : Function.Injective ![r0, r1, r2, v, x])
    (hk4 : k4FreeMask (quadIdxList 5) (gatherBits
      (mkGather5 r0.val r1.val r2.val v.val x.val) 10 w) = true)
    (hbit : (gatherBits (mkGather5 r0.val r1.val r2.val v.val x.val)
      10 w).testBit 0 = true) :
    (s3Idx1T.getD (gatherBits
        (mkGather5 r0.val r1.val r2.val v.val x.val) 10 w) 999 = i)
      ↔ (s31Flag i).IsIso
          (extFlagS3 (graphOfMask 7 w) ![r0, r1, r2] v x) := by
  obtain ⟨hlt, hiso⟩ := s31_table_spec _ hmask hk4 hbit
  have hgr := gather5_graph_eq (w := w) hinj
  have hext : (Sym3Flag.mk
        (graphOfMask 5 (gatherBits
          (mkGather5 r0.val r1.val r2.val v.val x.val) 10 w)) ![0, 1, 2])
      = extFlagS3 (graphOfMask 7 w) ![r0, r1, r2] v x := by
    rw [Sym3Flag.mk.injEq]
    exact ⟨hgr, rfl⟩
  rw [hext] at hiso
  constructor
  · rintro rfl
    exact hiso.symm
  · intro hiso'
    by_contra hne
    exact s31Flag_pairwise _ hlt i hi (fun h => hne h)
      (hiso.symm.trans hiso'.symm)

end FlagAlgebras.Core.Tetrahedron
