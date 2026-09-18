import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootData
import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootTables
import LeanFlagAlgebras.Core.Examples.TetrahedronMask
import LeanFlagAlgebras.Core.Compute.MaskInj

namespace FlagAlgebras.Core.Tetrahedron.FullSevenLong

open FlagAlgebras.Core

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

lemma s5Data_dimensions : ∀ b : Fin 18,
    0 < s5Dim b ∧ (s5Block b).flags.size = s5Dim b ∧
      (s5Block b).links.size = s5Dim b ∧
      (s5Block b).linkIndex.size = 1024 ∧
      (s5Block b).factors.size = s5Rows b * s5Dim b := by native_decide

lemma s5Type_bits : ∀ b : Fin 18,
    k4FreeMask (quadIdxList 5) (s5Block b).sigma = true := by native_decide

lemma s5Type_mem (b : Fin 18) : TetraFree.Mem (s5Type b).toModel :=
  k4FreeMask_iff_mem.mp (s5Type_bits b)

instance (b : Fin 18) : TetraFree.IsType (s5Type b).toModel := ⟨s5Type_mem b⟩

lemma s5Flag_wf : ∀ (b : Fin 18) (i : ℕ), i < s5Dim b →
    (s5Flag b i).WellFormed (s5Type b) := by native_decide

lemma s5Flag_bits : ∀ (b : Fin 18) (i : ℕ), i < s5Dim b →
    k4FreeMask (quadIdxList 6) (s5FlagMask b i) = true := by native_decide

lemma s5Flag_mem (b : Fin 18) {i : ℕ} (hi : i < s5Dim b) :
    TetraFree.Mem (s5Flag b i).graph.toModel :=
  k4FreeMask_iff_mem.mp (s5Flag_bits b i hi)

/-- The compact ten-bit lookup is complete for every admissible link, and
returns the exact labeled mask, not an automorphism quotient. -/
lemma s5_link_table_spec : ∀ (b : Fin 18) (link : ℕ), link < 1024 →
    k4FreeMask (quadIdxList 6) (s5Encode (s5Block b).sigma link) = true →
    let i := (s5Block b).linkIndex.getD link (s5Dim b)
    i < s5Dim b ∧ s5FlagMask b i = s5Encode (s5Block b).sigma link := by
  native_decide

lemma s5FlagMask_lt : ∀ (b : Fin 18) (i : ℕ), i < s5Dim b →
    s5FlagMask b i < 2 ^ 20 := by native_decide

lemma s5FlagMask_distinct : ∀ (b : Fin 18) (i : ℕ), i < s5Dim b →
    ∀ j < s5Dim b, s5FlagMask b i = s5FlagMask b j → i = j := by native_decide

end FlagAlgebras.Core.Tetrahedron.FullSevenLong
