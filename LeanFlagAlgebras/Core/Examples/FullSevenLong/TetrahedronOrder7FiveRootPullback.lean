import LeanFlagAlgebras.Core.Examples.FullSevenLong.TetrahedronOrder7FiveRootTables
import LeanFlagAlgebras.Core.Compute.MaskInj

namespace FlagAlgebras.Core.Tetrahedron.FullSevenLong

open FlagAlgebras.Core

/-- A packed gather computes the graph pullback whenever its slot sources are
the ranks of the corresponding image triples. -/
theorem s5Graph_gather {n N : ℕ} (g cnt w : ℕ) (f : Fin n → Fin N)
    (hf : Function.Injective f)
    (hrank : ∀ a b c : Fin n, a < b → b < c → triIdx n a.val b.val c.val < cnt)
    (hsource : ∀ a b c : Fin n, a < b → b < c →
      s5Source g (triIdx n a.val b.val c.val) =
        triIdx N (sort3 (f a).val (f b).val (f c).val).1
          (sort3 (f a).val (f b).val (f c).val).2.1
          (sort3 (f a).val (f b).val (f c).val).2.2) :
    graphOfMask n (s5Gather g cnt w) = (graphOfMask N w).pullback f := by
  have hbit : ∀ a b c : Fin n, a < b → b < c →
      (s5Gather g cnt w).testBit (triIdx n a.val b.val c.val) =
        w.testBit (triIdx N (sort3 (f a).val (f b).val (f c).val).1
          (sort3 (f a).val (f b).val (f c).val).2.1
          (sort3 (f a).val (f b).val (f c).val).2.2) := by
    intro a b c hab hbc
    rw [s5Gather_testBit, decide_eq_true (hrank a b c hab hbc),
      Bool.true_and, hsource a b c hab hbc]
  refine Sym3Graph.ext ?_
  ext e
  rw [mem_graphOfMask_edges]
  show _ ↔ e ∈ Finset.univ.filter _
  rw [Finset.mem_filter]
  have hvals : ∀ {a b : Fin n}, a ≠ b → (f a).val ≠ (f b).val :=
    fun hne h => hne (hf (Fin.val_injective h))
  constructor
  · rintro ⟨a, b, c, hab, hbc, hbit', rfl⟩
    refine ⟨Finset.mem_univ _, card_triple_sorted hab hbc, ?_⟩
    rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton]
    rw [hbit a b c hab hbc] at hbit'
    obtain ⟨hs12, hs23⟩ := sort3_sorted (hvals hab.ne)
      (hvals (hab.trans hbc).ne) (hvals hbc.ne)
    have hset := sort3_finset (f a).val (f b).val (f c).val
    have hmem : ∀ x ∈ ({(sort3 (f a).val (f b).val (f c).val).1,
        (sort3 (f a).val (f b).val (f c).val).2.1,
        (sort3 (f a).val (f b).val (f c).val).2.2} : Finset ℕ), x < N := by
      intro x hx
      rw [hset] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (f a).isLt
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (f b).isLt
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact (f c).isLt
    have h1 := hmem _ (Finset.mem_insert_self _ _)
    have h2 := hmem _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have h3 := hmem _ (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    refine mem_graphOfMask_edges.mpr ⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩,
      Fin.lt_def.mpr hs12, Fin.lt_def.mpr hs23, hbit', ?_⟩
    refine Finset.image_injective (f := Fin.val) Fin.val_injective ?_
    rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton,
      Finset.image_insert, Finset.image_insert, Finset.image_singleton]
    exact hset.symm
  · rintro ⟨-, hcard, himg⟩
    obtain ⟨a, b, c, hab, hbc, rfl⟩ := exists_sorted_triple hcard
    refine ⟨a, b, c, hab, hbc, ?_, rfl⟩
    rw [Finset.image_insert, Finset.image_insert,
      Finset.image_singleton] at himg
    obtain ⟨x, y, z, hxy, hyz, hbit', heq⟩ := mem_graphOfMask_edges.mp himg
    rw [hbit a b c hab hbc]
    obtain ⟨hs12, hs23⟩ := sort3_sorted (hvals hab.ne)
      (hvals (hab.trans hbc).ne) (hvals hbc.ne)
    have hset : ({(sort3 (f a).val (f b).val (f c).val).1,
        (sort3 (f a).val (f b).val (f c).val).2.1,
        (sort3 (f a).val (f b).val (f c).val).2.2} : Finset ℕ)
        = {x.val, y.val, z.val} := by
      rw [sort3_finset]
      have himg2 := congrArg (Finset.image Fin.val) heq
      rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton,
        Finset.image_insert, Finset.image_insert,
        Finset.image_singleton] at himg2
      exact himg2
    obtain ⟨e1, e2, e3⟩ := sorted_triple_eq hs12 hs23
      (Fin.lt_def.mp hxy) (Fin.lt_def.mp hyz) hset
    rw [e1, e2, e3]
    exact hbit'


/-- Equality of composed gathers can be checked on their source words. -/
lemma s5Gather_comp_congr (g₁ h₁ g₂ h₂ width n₁ n₂ w : ℕ)
    (hb₁ : ∀ k < width, s5Source g₁ k < n₁)
    (hb₂ : ∀ k < width, s5Source g₂ k < n₂)
    (hs : ∀ k < width,
      s5Source h₁ (s5Source g₁ k) = s5Source h₂ (s5Source g₂ k)) :
    s5Gather g₁ width (s5Gather h₁ n₁ w) =
      s5Gather g₂ width (s5Gather h₂ n₂ w) := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [s5Gather_testBit]
  by_cases hk : k < width
  · rw [decide_eq_true hk, decide_eq_true (hb₁ k hk),
      decide_eq_true (hb₂ k hk), hs k hk]
  · simp [hk]

private lemma s5Join_sources : ∀ k < 20,
    s5Source s5JoinGather k < 20 ∧
      (if s5Source s5JoinGather k < 10 then
        s5Source s5RootGather6 (s5Source s5JoinGather k)
      else s5Source s5LinkGather6 (s5Source s5JoinGather k - 10)) = k := by decide

/-- The ten root bits and ten link bits determine the labeled six-vertex mask. -/
lemma s5Encode_roundtrip {m : ℕ} (hm : m < 2 ^ 20) :
    s5Encode (s5RootMask6 m) (s5LinkMask6 m) = m := by
  apply eq_of_lt_two_pow (s5Gather_lt _ _ _) hm
  intro k hk
  have hsrc := s5Join_sources k hk
  by_cases hs : s5Source s5JoinGather k < 10
  · have hn : ¬s5Source s5JoinGather k ≥ 10 := by omega
    simp only [if_pos hs] at hsrc
    simp [s5Encode, s5RootMask6, s5LinkMask6, s5Gather_testBit,
      Nat.testBit_lor, Nat.testBit_shiftLeft, hk, hs, hn, hsrc.2]
  · have hn : s5Source s5JoinGather k ≥ 10 := by omega
    have hsub : s5Source s5JoinGather k - 10 < 10 := by omega
    simp only [if_neg hs] at hsrc
    simp [s5Encode, s5RootMask6, s5LinkMask6, s5Gather_testBit,
      Nat.testBit_lor, Nat.testBit_shiftLeft, hk, hs, hn, hsub, hsrc.2]

end FlagAlgebras.Core.Tetrahedron.FullSevenLong
