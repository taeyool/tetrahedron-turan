import LeanFlagAlgebras.Core.Compute.Mask3
import LeanFlagAlgebras.Core.Examples.Tetrahedron

/-! # Bitmask tetrahedron-freeness agrees with theory membership

The order-7 sweep decides tetrahedron-freeness of millions of masks with
`k4FreeMask` — pure bit tests against a precomputed quadruple table. This
file proves that verdict *means* membership in the tetrahedron-free
theory: a mask passes `k4FreeMask (quadIdxList n)` iff its decoded
3-graph `graphOfMask n m` is a `TetraFree` model.

The equivalence goes through the sorted-quadruple description of
containment: a tetrahedron embedding exists iff some strictly sorted
vertex quadruple has all four of its triples present, and the latter is
exactly what the mask check refutes. Once this bridge is in place, no
semantic (`Model`-level) computation ever runs in a sweep — the kernel
touches only bits, and the meaning is recovered by theorem, not by
evaluation (see the counting example at the end). -/

namespace FlagAlgebras.Core.Tetrahedron

open FlagAlgebras.Core

private lemma fin_three' : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

private lemma fin_four : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  decide

/-- The 3-element subsets of a 4-element index set, exhaustively. -/
private lemma card_three_fin4 : ∀ s : Finset (Fin 4), s.card = 3 →
    s = {0, 1, 2} ∨ s = {0, 1, 3} ∨ s = {0, 2, 3} ∨ s = {1, 2, 3} := by
  decide

/-- Composition acts entrywise on a three-entry tuple. -/
lemma comp_vec3 {α β : Type} (f : α → β) (i j k : α) :
    f ∘ ![i, j, k] = ![f i, f j, f k] := by
  funext x
  rcases fin_three' x with rfl | rfl | rfl <;> rfl

/-- A tuple of four distinct values is injective. -/
lemma vec4_injective {α : Type} {a b c d : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective ![a, b, c, d] := by
  intro i j hij
  rcases fin_four i with rfl | rfl | rfl | rfl <;>
    rcases fin_four j with rfl | rfl | rfl | rfl <;>
    simp_all [Matrix.cons_val_two, Matrix.cons_val_three]

/-- Containment of the tetrahedron in a decoded mask, described by bits:
some strictly sorted vertex quadruple has all four of its triples
present. -/
theorem graphOfMask_contains_tetra_iff {n m : ℕ} :
    (graphOfMask n m).toModel.Contains tetra ↔
      ∃ a b c d : Fin n, a < b ∧ b < c ∧ c < d
        ∧ m.testBit (triIdx n a.val b.val c.val) = true
        ∧ m.testBit (triIdx n a.val b.val d.val) = true
        ∧ m.testBit (triIdx n a.val c.val d.val) = true
        ∧ m.testBit (triIdx n b.val c.val d.val) = true := by
  constructor
  · rintro ⟨f, hf⟩
    -- the image of any 3-subset of the four embedded vertices is an edge
    have h3 : ∀ s : Finset (Fin 4), s.card = 3 →
        s.image ⇑f ∈ (graphOfMask n m).edges := by
      intro s hs
      have hmem : ∀ i j k : Fin 4, Function.Injective ![i, j, k] →
          ({i, j, k} : Finset (Fin 4)).image ⇑f
            ∈ (graphOfMask n m).edges := by
        intro i j k hinj
        have h2 := (hf () ![i, j, k] hinj).2
        rw [comp_vec3, image_vec3] at h2
        rwa [Finset.image_insert, Finset.image_insert,
          Finset.image_singleton]
      rcases card_three_fin4 s hs with rfl | rfl | rfl | rfl
      · exact hmem 0 1 2 (by decide)
      · exact hmem 0 1 3 (by decide)
      · exact hmem 0 2 3 (by decide)
      · exact hmem 1 2 3 (by decide)
    have hW : (Finset.univ.image ⇑f).card = 4 := by
      rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ,
        Fintype.card_fin]
    obtain ⟨a, b, c, d, hab, hbc, hcd, hWeq⟩ := exists_sorted_quad hW
    -- every card-3 subset of the sorted quadruple is an edge
    have hsub : ∀ s : Finset (Fin n),
        s ⊆ ({a, b, c, d} : Finset (Fin n)) → s.card = 3 →
        s ∈ (graphOfMask n m).edges := by
      intro s hssub hscard
      have hsW : s ⊆ Finset.univ.image ⇑f := by
        rw [hWeq]
        exact hssub
      set t := Finset.univ.filter (fun i : Fin 4 => f i ∈ s) with ht
      have himg : t.image ⇑f = s := by
        ext y
        simp only [ht, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and]
        constructor
        · rintro ⟨i, his, rfl⟩
          exact his
        · intro hy
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hsW hy)
          exact ⟨i, hy, rfl⟩
      have htcard : t.card = 3 := by
        have hc := Finset.card_image_of_injective t f.injective
        rw [himg, hscard] at hc
        exact hc.symm
      exact himg ▸ h3 t htcard
    -- extract the four bits from the four sorted triples
    have hbit : ∀ x y z : Fin n, x < y → y < z →
        ({x, y, z} : Finset (Fin n)) ∈ (graphOfMask n m).edges →
        m.testBit (triIdx n x.val y.val z.val) = true := by
      intro x y z hxy hyz hmem
      obtain ⟨x', y', z', hxy', hyz', hbit', heq⟩ :=
        mem_graphOfMask_edges.mp hmem
      obtain ⟨rfl, rfl, rfl⟩ := sorted_triple_eq hxy hyz hxy' hyz' heq
      exact hbit'
    refine ⟨a, b, c, d, hab, hbc, hcd, ?_, ?_, ?_, ?_⟩
    · refine hbit a b c hab hbc (hsub _ ?_ (card_triple_sorted hab hbc))
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
      rcases hw with rfl | rfl | rfl
      exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl))]
    · refine hbit a b d hab (hbc.trans hcd)
        (hsub _ ?_ (card_triple_sorted hab (hbc.trans hcd)))
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
      rcases hw with rfl | rfl | rfl
      exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inr rfl))]
    · refine hbit a c d (hab.trans hbc) hcd
        (hsub _ ?_ (card_triple_sorted (hab.trans hbc) hcd))
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
      rcases hw with rfl | rfl | rfl
      exacts [Or.inl rfl, Or.inr (Or.inr (Or.inl rfl)),
        Or.inr (Or.inr (Or.inr rfl))]
    · refine hbit b c d hbc hcd (hsub _ ?_ (card_triple_sorted hbc hcd))
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
      rcases hw with rfl | rfl | rfl
      exacts [Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)),
        Or.inr (Or.inr (Or.inr rfl))]
  · rintro ⟨a, b, c, d, hab, hbc, hcd, h₁, h₂, h₃, h₄⟩
    have hvinj : Function.Injective (![a, b, c, d] : Fin 4 → Fin n) :=
      vec4_injective hab.ne (hab.trans hbc).ne
        ((hab.trans hbc).trans hcd).ne hbc.ne (hbc.trans hcd).ne hcd.ne
    have hv0 : (![a, b, c, d] : Fin 4 → Fin n) 0 = a := rfl
    have hv1 : (![a, b, c, d] : Fin 4 → Fin n) 1 = b := rfl
    have hv2 : (![a, b, c, d] : Fin 4 → Fin n) 2 = c := rfl
    have hv3 : (![a, b, c, d] : Fin 4 → Fin n) 3 = d := rfl
    refine ⟨⟨![a, b, c, d], hvinj⟩, fun r g hg => ?_⟩
    have hginj : Function.Injective g := hg
    refine ⟨hvinj.comp hginj, ?_⟩
    show Finset.univ.image (![a, b, c, d] ∘ g) ∈ (graphOfMask n m).edges
    rw [← Finset.image_image]
    have hgcard : (Finset.univ.image g).card = 3 := by
      rw [Finset.card_image_of_injective _ hginj, Finset.card_univ,
        Fintype.card_fin]
    rcases card_three_fin4 _ hgcard with hs | hs | hs | hs <;>
      rw [hs, Finset.image_insert, Finset.image_insert,
        Finset.image_singleton]
    · rw [hv0, hv1, hv2]
      exact mem_graphOfMask_edges.mpr ⟨a, b, c, hab, hbc, h₁, rfl⟩
    · rw [hv0, hv1, hv3]
      exact mem_graphOfMask_edges.mpr
        ⟨a, b, d, hab, hbc.trans hcd, h₂, rfl⟩
    · rw [hv0, hv2, hv3]
      exact mem_graphOfMask_edges.mpr
        ⟨a, c, d, hab.trans hbc, hcd, h₃, rfl⟩
    · rw [hv1, hv2, hv3]
      exact mem_graphOfMask_edges.mpr ⟨b, c, d, hbc, hcd, h₄, rfl⟩

/-- The mask check is exactly non-containment of the tetrahedron. -/
theorem k4FreeMask_iff_not_contains {n m : ℕ} :
    k4FreeMask (quadIdxList n) m = true ↔
      ¬(graphOfMask n m).toModel.Contains tetra := by
  rw [k4FreeMask_iff_testBit, graphOfMask_contains_tetra_iff]
  constructor
  · rintro h ⟨a, b, c, d, hab, hbc, hcd, h₁, h₂, h₃, h₄⟩
    exact h a.val b.val c.val d.val hab hbc hcd d.isLt ⟨h₁, h₂, h₃, h₄⟩
  · intro h a b c d hab hbc hcd hdn hbits
    exact h ⟨⟨a, ((hab.trans hbc).trans hcd).trans hdn⟩,
      ⟨b, (hbc.trans hcd).trans hdn⟩, ⟨c, hcd.trans hdn⟩, ⟨d, hdn⟩,
      hab, hbc, hcd, hbits.1, hbits.2.1, hbits.2.2.1, hbits.2.2.2⟩

/-- The mask check is exactly membership in the tetrahedron-free theory:
the bit-level verdict of a sweep *is* the semantic statement. -/
theorem k4FreeMask_iff_mem {n m : ℕ} :
    k4FreeMask (quadIdxList n) m = true ↔
      TetraFree.Mem (graphOfMask n m).toModel := by
  rw [k4FreeMask_iff_not_contains]
  exact ⟨fun h => ⟨(graphOfMask n m).toModel_mem, h⟩, fun h => h.2⟩

/-! ## Kernel demonstrations

The mask sweep counts are pure bit arithmetic — no `Finset`, no models —
and the bridge theorem converts them to semantic counts for free. -/

/-- On four vertices, every mask except the complete one is
tetrahedron-free: `15` of `16`. -/
example : ((List.range 16).countP fun m => k4FreeMask (quadIdxList 4) m)
    = 15 := by decide

set_option maxRecDepth 65536 in
/-- On five vertices, `768` of the `1024` labeled 3-graphs are
tetrahedron-free (the mask-level sweep of the order-5 ground set). -/
example : ((List.range 1024).countP fun m => k4FreeMask (quadIdxList 5) m)
    = 768 := by decide

/-- The three-triple mask on four vertices decodes to a tetrahedron-free
model — semantic membership established by the bridge theorem from a
one-bit-table kernel check. -/
example : TetraFree.Mem (graphOfMask 4 0b0111).toModel :=
  k4FreeMask_iff_mem.mp (by decide)

/-- The full mask on four vertices *is* the tetrahedron: not a member. -/
example : ¬TetraFree.Mem (graphOfMask 4 0b1111).toModel := fun h =>
  absurd (k4FreeMask_iff_mem.mpr h) (by decide)

set_option maxRecDepth 65536 in
/-- The bit-level count *is* the semantic count, with no model-level
kernel evaluation: `countP` transports along the bridge theorem. -/
example : ((List.range 1024).countP fun m => k4FreeMask (quadIdxList 5) m)
    = ((List.range 1024).countP fun m =>
        decide (TetraFree.Mem (graphOfMask 5 m).toModel)) := by
  refine List.countP_congr fun m _ => ?_
  by_cases h : TetraFree.Mem (graphOfMask 5 m).toModel
  · rw [decide_eq_true h, k4FreeMask_iff_mem.mpr h]
  · rw [decide_eq_false h]
    exact ⟨fun ht => absurd (k4FreeMask_iff_mem.mp ht) h,
      fun hf => absurd hf (by simp)⟩

end FlagAlgebras.Core.Tetrahedron
