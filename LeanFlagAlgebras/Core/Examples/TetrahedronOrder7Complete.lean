import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Checker
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep00
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep01
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep02
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep03
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep04
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep05
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep06
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep07
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep08
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep09
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep10
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep11
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep12
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep13
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep14
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep15
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep16
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep17
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep18
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep19
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep20
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep21
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep22
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep23
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep24
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep25
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep26
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep27
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep28
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep29
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep30
import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Sweep31

/-! # Six-vertex completeness of the order-7 representative listing

Every tetrahedron-free 3-graph on six vertices is isomorphic to a listed
representative — the load-bearing bridge between the abstract flag layer
and the 964-class tables of the order-7 certificate.

The proof is a kernel sweep over all `2^20` masks, split into 32
subrange pieces (separate files, built in parallel) and assembled by
`sweepMasks_of_pieces`. Each tetrahedron-free mask is matched to a
listed representative through its packed witness permutation, with
everything re-verified by computation — the witness tables carry no
trust. Reflection of the verdict (`sweepMasks_spec` + `leafOK_iso`)
yields the completeness theorem; combined with surjectivity of the mask
decoding it realizes every six-vertex flag class of the theory as a
listed class (`exists_rep_flag`). -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

/-- The full kernel sweep, assembled from the 32 subrange pieces. -/
lemma h6Sweep : sweepMasks leafOK 20 0 = true := by
  refine sweepMasks_of_pieces leafOK 15 5 0 fun j hj => ?_
  match j, hj with
  | 0, _ => exact h6Sweep_00
  | 1, _ => exact h6Sweep_01
  | 2, _ => exact h6Sweep_02
  | 3, _ => exact h6Sweep_03
  | 4, _ => exact h6Sweep_04
  | 5, _ => exact h6Sweep_05
  | 6, _ => exact h6Sweep_06
  | 7, _ => exact h6Sweep_07
  | 8, _ => exact h6Sweep_08
  | 9, _ => exact h6Sweep_09
  | 10, _ => exact h6Sweep_10
  | 11, _ => exact h6Sweep_11
  | 12, _ => exact h6Sweep_12
  | 13, _ => exact h6Sweep_13
  | 14, _ => exact h6Sweep_14
  | 15, _ => exact h6Sweep_15
  | 16, _ => exact h6Sweep_16
  | 17, _ => exact h6Sweep_17
  | 18, _ => exact h6Sweep_18
  | 19, _ => exact h6Sweep_19
  | 20, _ => exact h6Sweep_20
  | 21, _ => exact h6Sweep_21
  | 22, _ => exact h6Sweep_22
  | 23, _ => exact h6Sweep_23
  | 24, _ => exact h6Sweep_24
  | 25, _ => exact h6Sweep_25
  | 26, _ => exact h6Sweep_26
  | 27, _ => exact h6Sweep_27
  | 28, _ => exact h6Sweep_28
  | 29, _ => exact h6Sweep_29
  | 30, _ => exact h6Sweep_30
  | 31, _ => exact h6Sweep_31
  | n + 32, h => exact absurd h (by omega)

/-- **Completeness of the representative listing**: every
tetrahedron-free six-vertex mask decodes to a graph isomorphic to a
listed representative. -/
theorem h6Reps_complete {m : ℕ} (hm : m < 2 ^ 20)
    (hk4 : k4FreeMask (quadIdxList 6) m = true) :
    ∃ h ∈ h6Reps, (graphOfMask 6 m).IsIso (graphOfMask 6 h) := by
  have hleaf : leafOK m = true := by
    have := sweepMasks_spec leafOK 20 0 h6Sweep m hm
    simpa using this
  rw [← qs6_eq] at hk4
  obtain ⟨hmem, hiso⟩ := leafOK_iso hk4 hleaf
  exact ⟨_, hmem, hiso⟩

/-! ## Realization: every six-vertex flag class is a listed class -/

/-- Every listed representative decodes to a model of the theory. -/
lemma h6Reps_mem {h : ℕ} (hh : h ∈ h6Reps) :
    TetraFree.Mem (graphOfMask 6 h).toModel :=
  k4FreeMask_iff_mem.mp (List.all_eq_true.mp h6Reps_k4free h hh)

/-- **Realization**: every tetrahedron-free six-vertex graph has the
flag class of a listed representative. -/
theorem exists_rep_flag (G : Sym3Graph 6) (hG : TetraFree.Mem G.toModel) :
    ∃ h ∈ h6Reps, ∃ hh : TetraFree.Mem (graphOfMask 6 h).toModel,
      G.toFlag hG = (graphOfMask 6 h).toFlag hh := by
  obtain ⟨m, hmlt, hdec⟩ :=
    exists_mask_graphOfMask finTriples6_rank_inj finTriples6_rank_lt G
  have hmem : TetraFree.Mem (graphOfMask 6 m).toModel := by
    rw [hdec]
    exact hG
  have hk4 : k4FreeMask (quadIdxList 6) m = true := k4FreeMask_iff_mem.mpr hmem
  obtain ⟨h, hmemList, hiso⟩ := h6Reps_complete hmlt hk4
  refine ⟨h, hmemList, h6Reps_mem hmemList, ?_⟩
  rw [Sym3Graph.toFlag_eq_toFlag_iff hG (h6Reps_mem hmemList)]
  rw [← hdec]
  exact hiso

end FlagAlgebras.Core.Tetrahedron
