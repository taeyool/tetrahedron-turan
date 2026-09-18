import LeanFlagAlgebras.Core.Differential.Eval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # Core: stability of densities under deleting non-root vertices

Adding one non-root vertex to the induced sub-flag on a root-containing set
`A` of a `σ`-flag changes the density of a pattern on `s` vertices by at most
`(s − k)/(|A| + 1 − k)`, where `k = |σ|`
(`abs_flagDensity_restrict_insert_sub_le`): the witnesses gained are those
through the new vertex, and at most an `(s−k)/(|A|+1−k)` fraction of the
root-containing `s`-subsets pass through any fixed vertex. Extended
linearly to flag vectors (`abs_hostEval_restrict_insert_sub_le`) and
iterated over the deletion of any vertex set
(`abs_hostEval_restrict_sub_le`), this is the estimate that lets Razborov's
differential method delete a constant fraction of the vertices of a large
host while keeping the rooted densities under control. -/

namespace FlagAlgebras.Core

open Finset
open Classical

variable {S : Signature} {T : Type} [Fintype T] {𝕋 : RelTheory S} {σ : Model S T}
variable {U : Type} [Fintype U]

/-! ## Counting supersets inside a set -/

omit [Fintype T] in
/-- The number of `m`-element sets between `R` and `B`. -/
lemma card_superset_filter_subset {R B : Finset U} (hRB : R ⊆ B) {m : ℕ}
    (hm : R.card ≤ m) (q : Finset U → Prop) [DecidablePred q]
    (hq : ∀ A, q A ↔ R ⊆ A ∧ A.card = m ∧ A ⊆ B) :
    (Finset.univ.filter q).card = (B.card - R.card).choose (m - R.card) := by
  have hcard : ((B \ R).powersetCard (m - R.card)).card
      = (B.card - R.card).choose (m - R.card) := by
    rw [Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_eq_left.mpr hRB]
  rw [← hcard]
  refine Finset.card_bij' (fun A _ => A \ R) (fun X _ => X ∪ R) ?_ ?_ ?_ ?_
  · intro A hA
    obtain ⟨hRA, hAcard, hAB⟩ := (hq A).mp (Finset.mem_filter.mp hA).2
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.sdiff_subset_sdiff hAB subset_rfl,
      by rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hRA, hAcard]⟩
  · intro X hX
    obtain ⟨hXsub, hXcard⟩ := Finset.mem_powersetCard.mp hX
    have hdisj : Disjoint X R := Finset.disjoint_left.mpr fun x hxX hxR =>
      (Finset.mem_sdiff.mp (hXsub hxX)).2 hxR
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hq _).mpr
      ⟨Finset.subset_union_right, ?_, ?_⟩⟩
    · rw [Finset.card_union_of_disjoint hdisj, hXcard]
      omega
    · exact Finset.union_subset (hXsub.trans Finset.sdiff_subset) hRB
  · intro A hA
    obtain ⟨hRA, -, -⟩ := (hq A).mp (Finset.mem_filter.mp hA).2
    exact Finset.sdiff_union_of_subset hRA
  · intro X hX
    obtain ⟨hXsub, -⟩ := Finset.mem_powersetCard.mp hX
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact h1
      · exact absurd h1 h2
    · intro hx
      exact ⟨Or.inl hx, fun hxR => (Finset.mem_sdiff.mp (hXsub hx)).2 hxR⟩

/-! ## Adding one vertex to a restriction -/

/-- The rational inequality behind the single-vertex estimate. -/
lemma abs_div_sub_div_le {X' Y a b : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b)
    (hX0 : 0 ≤ X') (hX : X' ≤ a) (hY0 : 0 ≤ Y) (hY : Y ≤ b - a) :
    |X' / a - (X' + Y) / b| ≤ (b - a) / b := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hX' : X' = 0 := le_antisymm hX hX0
    rw [hX', div_zero, zero_add, zero_sub, abs_neg, abs_of_nonneg (div_nonneg hY0 hb.le),
      sub_zero]
    exact div_le_div_of_nonneg_right (by linarith) hb.le
  · have h1 : 0 ≤ 1 / a - 1 / b := by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le ha' hab
    have hd : X' / a - (X' + Y) / b = X' * (1 / a - 1 / b) - Y / b := by ring
    have hkey : a * (1 / a - 1 / b) = (b - a) / b := by
      field_simp
    rw [hd, abs_le]
    constructor
    · have h2 : Y / b ≤ (b - a) / b := div_le_div_of_nonneg_right hY hb.le
      nlinarith [mul_nonneg hX0 h1]
    · have h2 : X' * (1 / a - 1 / b) ≤ a * (1 / a - 1 / b) := mul_le_mul_of_nonneg_right hX h1
      nlinarith [div_nonneg hY0 hb.le]

lemma LabeledFlag.card_le_of_flag {W : Type} [Fintype W] (F : LabeledFlag 𝕋 σ W) :
    Fintype.card T ≤ Fintype.card W :=
  Fintype.card_le_of_injective _ F.rootEmbed.toEmbedding.injective

omit [Fintype T] [Fintype U] in
/-- The roots stay in an enlarged subset. -/
theorem LabeledFlag.root_mem_insert (X : LabeledFlag 𝕋 σ U) {A : Finset U}
    (hA : ∀ t, X.rootEmbed.toEmbedding t ∈ A) (u : U) :
    ∀ t, X.rootEmbed.toEmbedding t ∈ insert u A :=
  fun t => Finset.mem_insert_of_mem (hA t)

/-- **Single-vertex stability.** Adding one non-root vertex `u` to a
root-containing set `A` changes the density of a pattern on `s` vertices in
the induced sub-flag by at most `(s − k)/(|A| + 1 − k)`. -/
theorem abs_flagDensity_restrict_insert_sub_le {W : Type} [Fintype W]
    (F : LabeledFlag 𝕋 σ W) (X : LabeledFlag 𝕋 σ U) {A : Finset U}
    (hA : ∀ t, X.rootEmbed.toEmbedding t ∈ A) {u : U} (hu : u ∉ A)
    (hk : Fintype.card T < A.card) :
    |flagDensity F (X.restrict A hA)
        - flagDensity F (X.restrict (insert u A) (X.root_mem_insert hA u))|
      ≤ ((Fintype.card W - Fintype.card T : ℕ) : ℚ)
        / ((A.card + 1 - Fintype.card T : ℕ) : ℚ) := by
  set k := Fintype.card T with hkdef
  set s := Fintype.card W with hsdef
  have hks : k ≤ s := LabeledFlag.card_le_of_flag F
  set N := A.card + 1 - k with hNdef
  set r := s - k with hrdef
  have hN : 0 < N := by omega
  have hNr : ((N : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have e1 : A.card - Fintype.card T = N - 1 := by omega
  have e1' : A.card - k = N - 1 := e1
  have hBcard : (insert u A).card = A.card + 1 := Finset.card_insert_of_notMem hu
  set B := insert u A with hBdef
  have hAB : A ⊆ B := Finset.subset_insert u A
  have hB : ∀ t, X.rootEmbed.toEmbedding t ∈ B := X.root_mem_insert hA u
  -- trivial when the bound is at least one
  rcases lt_or_ge N r with hlt | hle
  · have hbig : (1 : ℚ) ≤ (r : ℚ) / (N : ℚ) := by
      rw [le_div_iff₀ (by exact_mod_cast hN), one_mul]
      exact_mod_cast hlt.le
    refine le_trans ?_ hbig
    rw [abs_le]
    have h1 := flagDensity_nonneg F (X.restrict A hA)
    have h2 := flagDensity_le_one F (X.restrict A hA)
    have h3 := flagDensity_nonneg F (X.restrict B hB)
    have h4 := flagDensity_le_one F (X.restrict B hB)
    constructor <;> linarith
  -- the counts
  set wit := flagWitnesses F X with hwit
  have hXA : flagCount F (X.restrict A hA) = (wit.filter (· ⊆ A)).card :=
    flagCount_restrict F X hA
  have hXB : flagCount F (X.restrict B hB) = (wit.filter (· ⊆ B)).card :=
    flagCount_restrict F X hB
  have hsplit : ((wit.filter (· ⊆ B)).filter (· ⊆ A)).card
      + ((wit.filter (· ⊆ B)).filter (fun W => ¬ W ⊆ A)).card
      = (wit.filter (· ⊆ B)).card :=
    Finset.card_filter_add_card_filter_not _
  have hAA : (wit.filter (· ⊆ B)).filter (· ⊆ A) = wit.filter (· ⊆ A) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun W _ =>
      ⟨fun h => h.2, fun h => ⟨h.trans hAB, h⟩⟩
  rw [hAA] at hsplit
  -- the superset counts
  have hRcard : X.rootFinset.card = k := X.card_rootFinset
  have hRA : X.rootFinset ⊆ A := LabeledFlag.rootFinset_subset hA
  have hb : (Finset.univ.filter fun W : Finset U =>
      X.rootFinset ⊆ W ∧ W.card = s ∧ W ⊆ B).card = N.choose r := by
    rw [card_superset_filter_subset (hRA.trans hAB) (by rw [hRcard]; exact hks) _
      (fun W => Iff.rfl), hRcard, hBcard]
  have ha : ((Finset.univ.filter fun W : Finset U =>
      X.rootFinset ⊆ W ∧ W.card = s ∧ W ⊆ B).filter fun W => W ⊆ A).card
      = (N - 1).choose r := by
    rw [Finset.filter_filter, card_superset_filter_subset hRA (by rw [hRcard]; exact hks) _
      (fun W => ⟨fun h => ⟨h.1.1, h.1.2.1, h.2⟩, fun h => ⟨⟨h.1, h.2.1, h.2.2.trans hAB⟩, h.2.2⟩⟩),
      hRcard, e1']
  have hsplit2 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun W : Finset U => X.rootFinset ⊆ W ∧ W.card = s ∧ W ⊆ B)
    (fun W => W ⊆ A)
  rw [hb, ha] at hsplit2
  -- witnesses inside `B` not inside `A` are supersets of the roots through `u`
  have hY : ((wit.filter (· ⊆ B)).filter (fun W => ¬ W ⊆ A)).card
      ≤ ((Finset.univ.filter fun W : Finset U =>
        X.rootFinset ⊆ W ∧ W.card = s ∧ W ⊆ B).filter fun W => ¬ W ⊆ A).card := by
    refine Finset.card_le_card fun W hW => ?_
    obtain ⟨hWB, hWA⟩ := Finset.mem_filter.mp hW
    obtain ⟨hWwit, hWB'⟩ := Finset.mem_filter.mp hWB
    obtain ⟨hroot, hcard, -⟩ := mem_flagWitnesses.mp hWwit
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      LabeledFlag.rootFinset_subset hroot, hcard, hWB'⟩, hWA⟩
  have hXle : (wit.filter (· ⊆ A)).card ≤ (N - 1).choose r := by
    rw [← hXA]
    have h := flagCount_le_choose F (X.restrict A hA)
    rw [Fintype.card_coe, e1] at h
    exact h
  -- the densities
  have hdA : flagDensity F (X.restrict A hA)
      = ((wit.filter (· ⊆ A)).card : ℚ) / ((N - 1).choose r : ℚ) := by
    rw [flagDensity, hXA, Fintype.card_coe, e1]
  have hdB : flagDensity F (X.restrict B hB)
      = (((wit.filter (· ⊆ A)).card : ℚ)
          + (((wit.filter (· ⊆ B)).filter (fun W => ¬ W ⊆ A)).card : ℚ))
        / (N.choose r : ℚ) := by
    rw [flagDensity, hXB, ← hsplit, Fintype.card_coe, hBcard]
    push_cast
    rfl
  rw [hdA, hdB]
  have hb0 : (0 : ℚ) < N.choose r := by exact_mod_cast Nat.choose_pos hle
  have hab : ((N - 1).choose r : ℚ) ≤ N.choose r := by
    exact_mod_cast Nat.choose_le_choose r (Nat.sub_le N 1)
  have hYq : (((wit.filter (· ⊆ B)).filter (fun W => ¬ W ⊆ A)).card : ℚ)
      ≤ (N.choose r : ℚ) - ((N - 1).choose r : ℚ) := by
    have : ((wit.filter (· ⊆ B)).filter (fun W => ¬ W ⊆ A)).card + (N - 1).choose r
        ≤ N.choose r := by omega
    have h' : ((((wit.filter (· ⊆ B)).filter (fun W => ¬ W ⊆ A)).card
        + (N - 1).choose r : ℕ) : ℚ) ≤ (N.choose r : ℚ) := by exact_mod_cast this
    push_cast at h'
    linarith
  refine le_trans (abs_div_sub_div_le (Nat.cast_nonneg _) hab hb0 (Nat.cast_nonneg _)
    (by exact_mod_cast hXle) (Nat.cast_nonneg _) hYq) (le_of_eq ?_)
  -- `(C(N,r) − C(N−1,r)) / C(N,r) = r / N`
  have hmul : ((N - 1).choose r : ℚ) * (N : ℚ) = (N.choose r : ℚ) * ((N - r : ℕ) : ℚ) := by
    have h := Nat.choose_mul_succ_eq (N - 1) r
    rw [Nat.sub_add_cancel hN] at h
    exact_mod_cast h
  rw [Nat.cast_sub hle] at hmul
  rw [div_eq_div_iff hb0.ne' hNr]
  linear_combination -hmul

/-! ## Linear extension and iteration -/

/-- The size-weighted `ℓ¹`-norm of a flag vector. -/
noncomputable def sizeNorm (g : FlagVector 𝕋 σ) : ℝ :=
  ∑ F ∈ g.support, |g F| * (F.1 : ℝ)

omit [Fintype T] [Fintype U] in
theorem sizeNorm_nonneg (g : FlagVector 𝕋 σ) : 0 ≤ sizeNorm g :=
  Finset.sum_nonneg fun _F _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)

/-- Single-vertex stability for flag vectors: the host evaluation moves by
at most `sizeNorm g / (|A| + 1 − k)`. -/
theorem abs_hostEval_restrict_insert_sub_le (X : LabeledFlag 𝕋 σ U) {A : Finset U}
    (hA : ∀ t, X.rootEmbed.toEmbedding t ∈ A) {u : U} (hu : u ∉ A)
    (hk : Fintype.card T < A.card) (g : FlagVector 𝕋 σ) :
    |hostEval (X.restrict A hA) g - hostEval (X.restrict (insert u A) (X.root_mem_insert hA u)) g|
      ≤ sizeNorm g / ((A.card + 1 - Fintype.card T : ℕ) : ℝ) := by
  have hN : (0 : ℝ) < ((A.card + 1 - Fintype.card T : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (by omega)
  rw [hostEval_apply, hostEval_apply, ← Finset.sum_sub_distrib, sizeNorm, Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun F _ => ?_)
  rw [← mul_sub, abs_mul, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h := abs_flagDensity_restrict_insert_sub_le (Quotient.out F.2) X hA hu hk
  have h' : |((flagDensity (Quotient.out F.2) (X.restrict A hA) : ℚ) : ℝ)
      - ((flagDensity (Quotient.out F.2) (X.restrict (insert u A) (X.root_mem_insert hA u)) : ℚ) : ℝ)|
      ≤ ((Fintype.card (Fin F.1) - Fintype.card T : ℕ) : ℝ)
        / ((A.card + 1 - Fintype.card T : ℕ) : ℝ) := by
    rw [← Rat.cast_sub, ← Rat.cast_abs]
    have := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at this ⊢
    exact this
  refine h'.trans (div_le_div_of_nonneg_right ?_ hN.le)
  rw [Fintype.card_fin]
  exact_mod_cast Nat.sub_le F.1 (Fintype.card T)

/-- **Restriction stability.** Restricting a host on `n` vertices to a
root-containing subset `A` with `|A| > k` moves every host evaluation by at
most `(n − |A|) · sizeNorm g / (|A| − k)`. -/
theorem abs_hostEval_restrict_sub_le (X : LabeledFlag 𝕋 σ U) (g : FlagVector 𝕋 σ) :
    ∀ (j : ℕ) {A : Finset U} (hA : ∀ t, X.rootEmbed.toEmbedding t ∈ A),
      Fintype.card U - A.card = j → Fintype.card T < A.card →
      |hostEval (X.restrict A hA) g - hostEval X g|
        ≤ (j : ℝ) * sizeNorm g / ((A.card - Fintype.card T : ℕ) : ℝ) := by
  intro j
  induction j with
  | zero =>
    intro A hA hj hk
    have hAuniv : A = Finset.univ := Finset.eq_univ_of_card A (by
      have := Finset.card_le_univ A
      omega)
    subst hAuniv
    rw [hostEval_congr (X.restrictUniv hA), sub_self, abs_zero, Nat.cast_zero, zero_mul,
      zero_div]
  | succ j ih =>
    intro A hA hj hk
    have hlt : A.card < Fintype.card U := by omega
    obtain ⟨u, -, hu⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (by rw [Finset.card_univ]; exact hlt : A.card < (Finset.univ : Finset U).card)
    have hB : ∀ t, X.rootEmbed.toEmbedding t ∈ insert u A := X.root_mem_insert hA u
    have hBcard : (insert u A).card = A.card + 1 := Finset.card_insert_of_notMem hu
    have hjB : Fintype.card U - (insert u A).card = j := by omega
    have hkB : Fintype.card T < (insert u A).card := by omega
    have hIH := ih hB hjB hkB
    rw [hBcard] at hIH
    have hstep := abs_hostEval_restrict_insert_sub_le X hA hu hk g
    have hpos : (0 : ℝ) < ((A.card - Fintype.card T : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hk
    have hmono : sizeNorm g / ((A.card + 1 - Fintype.card T : ℕ) : ℝ)
        ≤ sizeNorm g / ((A.card - Fintype.card T : ℕ) : ℝ) := by
      refine div_le_div_of_nonneg_left (sizeNorm_nonneg g) hpos ?_
      exact_mod_cast Nat.sub_le_sub_right (Nat.le_succ _) _
    have hmono' : (j : ℝ) * sizeNorm g / ((A.card + 1 - Fintype.card T : ℕ) : ℝ)
        ≤ (j : ℝ) * sizeNorm g / ((A.card - Fintype.card T : ℕ) : ℝ) := by
      refine div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (sizeNorm_nonneg g))
        hpos ?_
      exact_mod_cast Nat.sub_le_sub_right (Nat.le_succ _) _
    calc |hostEval (X.restrict A hA) g - hostEval X g|
        = |(hostEval (X.restrict A hA) g - hostEval (X.restrict (insert u A) hB) g)
            + (hostEval (X.restrict (insert u A) hB) g - hostEval X g)| := by ring_nf
      _ ≤ |hostEval (X.restrict A hA) g - hostEval (X.restrict (insert u A) hB) g|
            + |hostEval (X.restrict (insert u A) hB) g - hostEval X g| := abs_add_le _ _
      _ ≤ sizeNorm g / ((A.card - Fintype.card T : ℕ) : ℝ)
            + (j : ℝ) * sizeNorm g / ((A.card - Fintype.card T : ℕ) : ℝ) :=
          add_le_add (hstep.trans hmono) (hIH.trans hmono')
      _ = ((j + 1 : ℕ) : ℝ) * sizeNorm g / ((A.card - Fintype.card T : ℕ) : ℝ) := by
          push_cast
          ring

end FlagAlgebras.Core
