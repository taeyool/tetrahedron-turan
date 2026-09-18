import LeanFlagAlgebras.Core.Examples.TetrahedronOrder7Blocks
import LeanFlagAlgebras.Core.Examples.TetrahedronMask

/-! # The block flags as typed literals

The certificate's order-6 semidefinite part lives at five rooted types:
the two-rooted four-vertex family (block 24, over the empty pair type)
and the four-rooted five-vertex families (blocks 45, one per K4-free
four-vertex type `rm ∈ {0, 1, 3, 7}`). The block tables store these
flags as masks; this file promotes them to typed literal flags and
discharges, by decision, that the stored conventions are what they claim
to be — the roots are the initial vertices, each flag induces its type
on them, and every flag is tetrahedron-free.

A failed `decide` here would mean the root convention was guessed wrong,
so these checks pin the convention. -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

/-! ## The types -/

/-- The two-vertex empty type of the 24-block. -/
def pairType2 : Sym3Graph 2 := ⟨∅, by decide⟩

lemma pairType2_mem : TetraFree.Mem pairType2.toModel := by decide

instance : TetraFree.IsType pairType2.toModel := ⟨pairType2_mem⟩

/-- The four-vertex type of a 45-block: the root-induced mask decoded. -/
def rmType (rm : ℕ) : Sym3Graph 4 := graphOfMask 4 rm

lemma rmType_mem_0 : TetraFree.Mem (rmType 0).toModel :=
  k4FreeMask_iff_mem.mp (by decide)
lemma rmType_mem_1 : TetraFree.Mem (rmType 1).toModel :=
  k4FreeMask_iff_mem.mp (by decide)
lemma rmType_mem_3 : TetraFree.Mem (rmType 3).toModel :=
  k4FreeMask_iff_mem.mp (by decide)
lemma rmType_mem_7 : TetraFree.Mem (rmType 7).toModel :=
  k4FreeMask_iff_mem.mp (by decide)

instance : TetraFree.IsType (rmType 0).toModel := ⟨rmType_mem_0⟩
instance : TetraFree.IsType (rmType 1).toModel := ⟨rmType_mem_1⟩
instance : TetraFree.IsType (rmType 3).toModel := ⟨rmType_mem_3⟩
instance : TetraFree.IsType (rmType 7).toModel := ⟨rmType_mem_7⟩

/-! ## The flags -/

/-- A 24-block flag: four vertices, the first two rooted. -/
def blk24Flag (i : ℕ) : Sym3Flag 2 4 :=
  ⟨graphOfMask 4 (flags24.getD i 0), ![0, 1]⟩

/-- A 45-block flag: five vertices, the first four rooted. -/
def blk45Flag (flags : List ℕ) (i : ℕ) : Sym3Flag 4 5 :=
  ⟨graphOfMask 5 (flags.getD i 0), ![0, 1, 2, 3]⟩

set_option maxRecDepth 8192 in
/-- The 24-block flags are well formed over the pair type: the roots are
the first two vertices and induce no hyperedge. -/
lemma blk24Flag_wf : ∀ i < 11, (blk24Flag i).WellFormed pairType2 := by
  decide

set_option maxRecDepth 8192 in
/-- The 24-block flags are tetrahedron-free. -/
lemma blk24Flag_mem :
    ∀ i < 11, TetraFree.Mem (blk24Flag i).graph.toModel := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- The `rm = 0` flags are well formed over their type. -/
lemma blk45Flag_wf_0 :
    ∀ i < 64, (blk45Flag flags45_0 i).WellFormed (rmType 0) := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
lemma blk45Flag_wf_1 :
    ∀ i < 56, (blk45Flag flags45_1 i).WellFormed (rmType 1) := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
lemma blk45Flag_wf_3 :
    ∀ i < 50, (blk45Flag flags45_3 i).WellFormed (rmType 3) := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
lemma blk45Flag_wf_7 :
    ∀ i < 45, (blk45Flag flags45_7 i).WellFormed (rmType 7) := by decide

set_option maxRecDepth 65536 in
/-- The 45-block flags are tetrahedron-free: the bit check on each
mask. -/
lemma blk45Flag_bits_0 :
    ∀ i < 64, k4FreeMask (quadIdxList 5) (flags45_0.getD i 0) = true := by
  decide

set_option maxRecDepth 65536 in
lemma blk45Flag_bits_1 :
    ∀ i < 56, k4FreeMask (quadIdxList 5) (flags45_1.getD i 0) = true := by
  decide

set_option maxRecDepth 65536 in
lemma blk45Flag_bits_3 :
    ∀ i < 50, k4FreeMask (quadIdxList 5) (flags45_3.getD i 0) = true := by
  decide

set_option maxRecDepth 65536 in
lemma blk45Flag_bits_7 :
    ∀ i < 45, k4FreeMask (quadIdxList 5) (flags45_7.getD i 0) = true := by
  decide

lemma blk45Flag_mem_0 {i : ℕ} (hi : i < 64) :
    TetraFree.Mem (blk45Flag flags45_0 i).graph.toModel :=
  k4FreeMask_iff_mem.mp (blk45Flag_bits_0 i hi)

lemma blk45Flag_mem_1 {i : ℕ} (hi : i < 56) :
    TetraFree.Mem (blk45Flag flags45_1 i).graph.toModel :=
  k4FreeMask_iff_mem.mp (blk45Flag_bits_1 i hi)

lemma blk45Flag_mem_3 {i : ℕ} (hi : i < 50) :
    TetraFree.Mem (blk45Flag flags45_3 i).graph.toModel :=
  k4FreeMask_iff_mem.mp (blk45Flag_bits_3 i hi)

lemma blk45Flag_mem_7 {i : ℕ} (hi : i < 45) :
    TetraFree.Mem (blk45Flag flags45_7 i).graph.toModel :=
  k4FreeMask_iff_mem.mp (blk45Flag_bits_7 i hi)

/-! ## The family dimensions -/

lemma flags24_length : flags24.length = 11 := by decide
lemma flags45_0_length : flags45_0.length = 64 := by decide
lemma flags45_1_length : flags45_1.length = 56 := by decide
lemma flags45_3_length : flags45_3.length = 50 := by decide
lemma flags45_7_length : flags45_7.length = 45 := by decide

end FlagAlgebras.Core.Tetrahedron
