import LeanFlagAlgebras.Core.Compute.Sym3
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Bitwise

/-! # Bitmask literals for 3-uniform hypergraphs

The order-7 certificate pipeline sweeps millions of labeled 3-graphs; the
`Finset`-backed `Sym3Graph` representation is far too heavy for that. This
file introduces the machine representation the sweep actually uses — a
3-graph on `n` vertices is a natural number whose bit `triIdx n a b c`
records the hyperedge `{a, b, c}` (for `a < b < c`), with triples ranked
in lexicographic order — together with the bridge back to `Sym3Graph`, so
that every mask-level check can be transported to a statement about flags.

The lexicographic rank is a closed formula (validated below against the
enumeration order for every vertex count the certificate uses), so hot
loops pay a handful of `ℕ`-operations per incidence test and never touch
`Finset` internals. The tetrahedron-freeness test is parameterized by a
precomputed table of quadruple positions, in the shape the depth-shallow
sweep checker consumes.

Everything here is generic in `n`; the tetrahedron-specific bridge (mask
freeness ↔ theory membership) lives with the tetrahedron examples. -/

namespace FlagAlgebras.Core

/-! ## Lexicographic ranks of pairs and triples

`triIdx n a b c` is the position of `(a, b, c)` (with `a < b < c < n`) in
the lexicographic enumeration of all sorted triples from `{0, …, n − 1}`;
`pairIdx` is the pair analogue. Both are closed telescoping formulas:
under the sortedness guards every subtraction is nonnegative and every
division exact, so the `ℕ`-valued expressions compute the true ranks. -/

/-- Lexicographic rank of the sorted triple `(a, b, c)` among the triples
of `{0, …, n − 1}`. Meaningful for `a < b < c < n`. -/
def triIdx (n a b c : ℕ) : ℕ :=
  (n * (n - 1) * (n - 2) - (n - a) * (n - a - 1) * (n - a - 2)) / 6
    + ((n - 1 - a) * (n - 2 - a) - (n - b) * (n - b - 1)) / 2
    + c - b - 1

/-- Lexicographic rank of the sorted pair `(a, b)` among the pairs of
`{0, …, n − 1}`. Meaningful for `a < b < n`. -/
def pairIdx (n a b : ℕ) : ℕ :=
  ((n - 1) * n - (n - a) * (n - 1 - a)) / 2 + b - a - 1

/-- The sorted triples of `Fin n`, in lexicographic order. -/
def finTriples (n : ℕ) : List (Fin n × Fin n × Fin n) :=
  (List.finRange n).flatMap fun a =>
    (List.finRange n).flatMap fun b =>
      (List.finRange n).filterMap fun c =>
        if a < b ∧ b < c then some (a, b, c) else none

/-- The sorted pairs of `Fin n`, in lexicographic order. -/
def finPairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun a =>
    (List.finRange n).filterMap fun b =>
      if a < b then some (a, b) else none

/-- The sorted quadruples of `{0, …, n − 1}`, in lexicographic order. -/
def quadsLex (n : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range n).flatMap fun a =>
    (List.range n).flatMap fun b =>
      (List.range n).flatMap fun c =>
        (List.range n).filterMap fun d =>
          if a < b ∧ b < c ∧ c < d then some (a, b, c, d) else none

lemma mem_finTriples {n : ℕ} {a b c : Fin n} :
    (a, b, c) ∈ finTriples n ↔ a < b ∧ b < c := by
  constructor
  · intro ht
    obtain ⟨a', -, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b', -, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨c', -, ht⟩ := List.mem_filterMap.mp ht
    by_cases h : a' < b' ∧ b' < c'
    · rw [if_pos h] at ht
      have heq := Option.some.inj ht
      simp only [Prod.ext_iff] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact h
    · rw [if_neg h] at ht
      cases ht
  · rintro ⟨hab, hbc⟩
    refine List.mem_flatMap.mpr ⟨a, List.mem_finRange a, ?_⟩
    refine List.mem_flatMap.mpr ⟨b, List.mem_finRange b, ?_⟩
    exact List.mem_filterMap.mpr ⟨c, List.mem_finRange c, by rw [if_pos ⟨hab, hbc⟩]⟩

lemma mem_quadsLex {n : ℕ} {a b c d : ℕ} :
    (a, b, c, d) ∈ quadsLex n ↔ a < b ∧ b < c ∧ c < d ∧ d < n := by
  constructor
  · intro hq
    obtain ⟨a', -, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨b', -, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨c', -, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨d', hd', hq⟩ := List.mem_filterMap.mp hq
    by_cases h : a' < b' ∧ b' < c' ∧ c' < d'
    · rw [if_pos h] at hq
      have heq := Option.some.inj hq
      simp only [Prod.ext_iff] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      exact ⟨h.1, h.2.1, h.2.2, List.mem_range.mp hd'⟩
    · rw [if_neg h] at hq
      cases hq
  · rintro ⟨hab, hbc, hcd, hdn⟩
    refine List.mem_flatMap.mpr
      ⟨a, List.mem_range.mpr (((hab.trans hbc).trans hcd).trans hdn), ?_⟩
    refine List.mem_flatMap.mpr
      ⟨b, List.mem_range.mpr ((hbc.trans hcd).trans hdn), ?_⟩
    refine List.mem_flatMap.mpr ⟨c, List.mem_range.mpr (hcd.trans hdn), ?_⟩
    exact List.mem_filterMap.mpr
      ⟨d, List.mem_range.mpr hdn, by rw [if_pos ⟨hab, hbc, hcd⟩]⟩

/-! The closed formulas agree with the enumeration order at every vertex
count the certificate pipeline uses (kernel-checked): mapping the rank
over the lexicographic listing yields `0, 1, 2, …` on the nose. This
simultaneously certifies correctness of the rank, its injectivity on
sorted tuples, and surjectivity onto the index range. -/

example : (finTriples 4).map (fun t => triIdx 4 t.1.val t.2.1.val t.2.2.val)
    = List.range 4 := by decide
example : (finTriples 5).map (fun t => triIdx 5 t.1.val t.2.1.val t.2.2.val)
    = List.range 10 := by decide
example : (finTriples 6).map (fun t => triIdx 6 t.1.val t.2.1.val t.2.2.val)
    = List.range 20 := by decide
example : (finTriples 7).map (fun t => triIdx 7 t.1.val t.2.1.val t.2.2.val)
    = List.range 35 := by decide
example : (finPairs 6).map (fun p => pairIdx 6 p.1.val p.2.val)
    = List.range 15 := by decide
example : (finPairs 7).map (fun p => pairIdx 7 p.1.val p.2.val)
    = List.range 21 := by decide

/-! ## Sorted-tuple toolkit

Small facts about strictly sorted tuples and their vertex sets, used to
canonicalize between mask bits (indexed by sorted tuples) and hyperedges
(unordered vertex sets). -/

/-- The vertex set of a strictly sorted triple has three elements. -/
lemma card_triple_sorted {α : Type} [DecidableEq α] [Preorder α]
    {a b c : α} (hab : a < b) (hbc : b < c) :
    ({a, b, c} : Finset α).card = 3 := by
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  · simp only [Finset.mem_singleton]
    exact hbc.ne
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hab.ne, (hab.trans hbc).ne⟩

/-- Two strictly sorted triples with the same vertex set are equal. -/
lemma sorted_triple_eq {α : Type} [LinearOrder α] {a b c x y z : α}
    (hab : a < b) (hbc : b < c) (hxy : x < y) (hyz : y < z)
    (h : ({a, b, c} : Finset α) = ({x, y, z} : Finset α)) :
    a = x ∧ b = y ∧ c = z := by
  have hmem : ∀ w : α,
      w ∈ ({a, b, c} : Finset α) ↔ w ∈ ({x, y, z} : Finset α) :=
    fun w => by rw [h]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have ha : a = x ∨ a = y ∨ a = z := (hmem a).mp (Or.inl rfl)
  have hb : b = x ∨ b = y ∨ b = z := (hmem b).mp (Or.inr (Or.inl rfl))
  have hc : c = x ∨ c = y ∨ c = z := (hmem c).mp (Or.inr (Or.inr rfl))
  have hx : x = a ∨ x = b ∨ x = c := (hmem x).mpr (Or.inl rfl)
  have hz : z = a ∨ z = b ∨ z = c := (hmem z).mpr (Or.inr (Or.inr rfl))
  have hxlow : ∀ w, w = x ∨ w = y ∨ w = z → x ≤ w := by
    rintro w (rfl | rfl | rfl)
    exacts [le_refl _, hxy.le, (hxy.trans hyz).le]
  have halow : ∀ w, w = a ∨ w = b ∨ w = c → a ≤ w := by
    rintro w (rfl | rfl | rfl)
    exacts [le_refl _, hab.le, (hab.trans hbc).le]
  have hzhigh : ∀ w, w = x ∨ w = y ∨ w = z → w ≤ z := by
    rintro w (rfl | rfl | rfl)
    exacts [(hxy.trans hyz).le, hyz.le, le_refl _]
  have hchigh : ∀ w, w = a ∨ w = b ∨ w = c → w ≤ c := by
    rintro w (rfl | rfl | rfl)
    exacts [(hab.trans hbc).le, hbc.le, le_refl _]
  have hax : a = x := le_antisymm (halow x hx) (hxlow a ha)
  have hcz : c = z := le_antisymm (hzhigh c hc) (hchigh z hz)
  refine ⟨hax, ?_, hcz⟩
  rcases hb with hbx | hby | hbz
  · exact absurd (hbx.trans hax.symm) hab.ne'
  · exact hby
  · exact absurd (hbz.trans hcz.symm) hbc.ne

/-- A three-element finite set is a strictly sorted triple. -/
lemma exists_sorted_triple {α : Type} [LinearOrder α] {W : Finset α}
    (h : W.card = 3) :
    ∃ a b c : α, a < b ∧ b < c ∧ W = {a, b, c} := by
  have hlen : (W.sort (· ≤ ·)).length = 3 := by rw [Finset.length_sort, h]
  have hsorted := W.sortedLT_sort.pairwise
  rcases hl : W.sort (· ≤ ·)
    with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨x, rest⟩⟩⟩⟩ <;>
    rw [hl] at hlen
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · rw [hl] at hsorted
    obtain ⟨h₁, hsorted⟩ := List.pairwise_cons.mp hsorted
    obtain ⟨h₂, -⟩ := List.pairwise_cons.mp hsorted
    refine ⟨a, b, c, h₁ b (by simp), h₂ c (by simp), ?_⟩
    ext w
    rw [show (w ∈ ({a, b, c} : Finset α)) ↔ w ∈ [a, b, c] from by
        simp, ← hl, Finset.mem_sort]
  · simp only [List.length_cons] at hlen
    omega

/-- A four-element finite set is a strictly sorted quadruple. -/
lemma exists_sorted_quad {α : Type} [LinearOrder α] {W : Finset α}
    (h : W.card = 4) :
    ∃ a b c d : α, a < b ∧ b < c ∧ c < d ∧ W = {a, b, c, d} := by
  have hlen : (W.sort (· ≤ ·)).length = 4 := by rw [Finset.length_sort, h]
  have hsorted := W.sortedLT_sort.pairwise
  rcases hl : W.sort (· ≤ ·)
    with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨x, rest⟩⟩⟩⟩⟩ <;>
    rw [hl] at hlen
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · rw [hl] at hsorted
    obtain ⟨h₁, hsorted⟩ := List.pairwise_cons.mp hsorted
    obtain ⟨h₂, hsorted⟩ := List.pairwise_cons.mp hsorted
    obtain ⟨h₃, -⟩ := List.pairwise_cons.mp hsorted
    refine ⟨a, b, c, d, h₁ b (by simp), h₂ c (by simp), h₃ d (by simp), ?_⟩
    ext w
    rw [show (w ∈ ({a, b, c, d} : Finset α)) ↔ w ∈ [a, b, c, d] from by
        simp, ← hl, Finset.mem_sort]
  · simp only [List.length_cons] at hlen
    omega

/-! ## The mask-to-graph bridge

`graphOfMask n m` reads a bitmask back as a `Sym3Graph`: the hyperedges
are the vertex sets of the sorted triples whose bit is set. This is the
specification-side meaning of a mask; the sweeps never evaluate it. -/

/-- The 3-graph encoded by a bitmask: hyperedge `{a, b, c}` (with
`a < b < c`) present iff bit `triIdx n a b c` is set. -/
def graphOfMask (n m : ℕ) : Sym3Graph n where
  edges :=
    ((finTriples n).filter fun t =>
      m.testBit (triIdx n t.1.val t.2.1.val t.2.2.val)).toFinset.image
      fun t => {t.1, t.2.1, t.2.2}
  edges_valid := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨t, ht, rfl⟩ := he
    rw [List.mem_toFinset, List.mem_filter] at ht
    obtain ⟨a, b, c⟩ := t
    obtain ⟨hab, hbc⟩ := mem_finTriples.mp ht.1
    exact card_triple_sorted hab hbc

/-- Membership description of the edges of `graphOfMask`. -/
lemma mem_graphOfMask_edges {n m : ℕ} {e : Finset (Fin n)} :
    e ∈ (graphOfMask n m).edges ↔
      ∃ a b c : Fin n, a < b ∧ b < c
        ∧ m.testBit (triIdx n a.val b.val c.val) = true
        ∧ e = {a, b, c} := by
  show e ∈ Finset.image _ _ ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [List.mem_toFinset, List.mem_filter] at ht
    obtain ⟨a, b, c⟩ := t
    obtain ⟨hab, hbc⟩ := mem_finTriples.mp ht.1
    exact ⟨a, b, c, hab, hbc, ht.2, rfl⟩
  · rintro ⟨a, b, c, hab, hbc, hbit, rfl⟩
    refine ⟨(a, b, c), ?_, rfl⟩
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨mem_finTriples.mpr ⟨hab, hbc⟩, hbit⟩

/-! ## The tetrahedron-freeness mask check

`k4FreeMask qs m` scans a precomputed list of quadruple-index tables: an
entry `(i₁, i₂, i₃, i₄)` records the four triple positions inside one
vertex quadruple, and the mask fails iff some quadruple has all four bits
set. The table for the full vertex range is `quadIdxList n`; sweeps pass
it in once, so the per-leaf cost is pure bit tests. -/

/-- The four triple ranks of each sorted vertex quadruple. -/
def quadIdxList (n : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (quadsLex n).map fun q =>
    (triIdx n q.1 q.2.1 q.2.2.1, triIdx n q.1 q.2.1 q.2.2.2,
     triIdx n q.1 q.2.2.1 q.2.2.2, triIdx n q.2.1 q.2.2.1 q.2.2.2)

/-- Bit-level tetrahedron-freeness: no listed quadruple has all four of
its triples present. -/
def k4FreeMask (qs : List (ℕ × ℕ × ℕ × ℕ)) (m : ℕ) : Bool :=
  qs.all fun q =>
    !(m.testBit q.1 && m.testBit q.2.1 && m.testBit q.2.2.1
      && m.testBit q.2.2.2)

/-- The mask check says exactly: no sorted vertex quadruple spans four
present triples. -/
lemma k4FreeMask_iff_testBit {n m : ℕ} :
    k4FreeMask (quadIdxList n) m = true ↔
      ∀ a b c d : ℕ, a < b → b < c → c < d → d < n →
        ¬(m.testBit (triIdx n a b c) = true
          ∧ m.testBit (triIdx n a b d) = true
          ∧ m.testBit (triIdx n a c d) = true
          ∧ m.testBit (triIdx n b c d) = true) := by
  rw [k4FreeMask, List.all_eq_true]
  constructor
  · intro h a b c d hab hbc hcd hdn hbits
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hbits
    have hfalse := h _ (List.mem_map.mpr
      ⟨(a, b, c, d), mem_quadsLex.mpr ⟨hab, hbc, hcd, hdn⟩, rfl⟩)
    simp [h₁, h₂, h₃, h₄] at hfalse
  · intro h q hq
    obtain ⟨⟨a, b, c, d⟩, hmem, rfl⟩ := List.mem_map.mp hq
    obtain ⟨hab, hbc, hcd, hdn⟩ := mem_quadsLex.mp hmem
    have hnot := h a b c d hab hbc hcd hdn
    cases h₁ : m.testBit (triIdx n a b c) <;>
      cases h₂ : m.testBit (triIdx n a b d) <;>
        cases h₃ : m.testBit (triIdx n a c d) <;>
          cases h₄ : m.testBit (triIdx n b c d) <;>
            simp
    exact hnot ⟨h₁, h₂, h₃, h₄⟩

/-! ## Mask-level isomorphism transport

The canonicalization sweep matches a mask against a listed representative
by exhibiting a vertex bijection under which the triple bits correspond.
`sort3` renormalizes an image triple to its sorted form; the bridge
theorem converts the bit-level correspondence into `Sym3Graph.IsIso` of
the decoded graphs — and hence equality of their flag classes. The
correspondence hypothesis is decidable, so a sweep discharges it per
(mask, representative, map) by kernel computation alone. -/

/-- Sort three values with a comparison network. -/
def sort3 {α : Type} [LinearOrder α] (a b c : α) : α × α × α :=
  if a ≤ b then
    if b ≤ c then (a, b, c)
    else if a ≤ c then (a, c, b) else (c, a, b)
  else
    if a ≤ c then (b, a, c)
    else if b ≤ c then (b, c, a) else (c, b, a)

/-- On pairwise distinct inputs the network output is strictly sorted. -/
lemma sort3_sorted {α : Type} [LinearOrder α] {a b c : α} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    (sort3 a b c).1 < (sort3 a b c).2.1
      ∧ (sort3 a b c).2.1 < (sort3 a b c).2.2 := by
  unfold sort3
  split_ifs with h₁ h₂ h₃ h₄ h₅
  · exact ⟨h₁.lt_of_ne hab, h₂.lt_of_ne hbc⟩
  · exact ⟨h₃.lt_of_ne hac, not_le.mp h₂⟩
  · exact ⟨not_le.mp h₃, h₁.lt_of_ne hab⟩
  · exact ⟨not_le.mp h₁, h₄.lt_of_ne hac⟩
  · exact ⟨h₅.lt_of_ne hbc, not_le.mp h₄⟩
  · exact ⟨not_le.mp h₅, not_le.mp h₁⟩

/-- The network permutes its inputs: the output vertex set is the input
vertex set. -/
lemma sort3_finset {α : Type} [LinearOrder α] (a b c : α) :
    ({(sort3 a b c).1, (sort3 a b c).2.1, (sort3 a b c).2.2} : Finset α)
      = {a, b, c} := by
  unfold sort3
  split_ifs
  · rfl
  · show ({a, c, b} : Finset α) = {a, b, c}
    rw [Finset.pair_comm c b]
  · show ({c, a, b} : Finset α) = {a, b, c}
    rw [Finset.insert_comm c a, Finset.pair_comm c b]
  · show ({b, a, c} : Finset α) = {a, b, c}
    rw [Finset.insert_comm b a]
  · show ({b, c, a} : Finset α) = {a, b, c}
    rw [Finset.pair_comm c a, Finset.insert_comm b a]
  · show ({c, b, a} : Finset α) = {a, b, c}
    rw [Finset.pair_comm b a, Finset.insert_comm c a, Finset.pair_comm c b]

/-- The load-bearing transport for canonicalization sweeps: an injective
vertex map under which every triple bit of `m` equals the bit of the
sorted image triple in `h` decodes to an isomorphism of the graphs. The
hypothesis is decidable for literal `n`, `f`, `m`, `h`. -/
theorem isIso_graphOfMask_of_bits {n : ℕ} {f : Fin n → Fin n}
    (hf : Function.Injective f) {m h : ℕ}
    (hbits : ∀ a b c : Fin n, a < b → b < c →
      m.testBit (triIdx n a.val b.val c.val)
        = h.testBit (triIdx n (sort3 (f a) (f b) (f c)).1.val
            (sort3 (f a) (f b) (f c)).2.1.val
            (sort3 (f a) (f b) (f c)).2.2.val)) :
    (graphOfMask n m).IsIso (graphOfMask n h) := by
  have hbij : Function.Bijective f := ⟨hf, Finite.surjective_of_injective hf⟩
  refine ⟨Equiv.ofBijective f hbij, ?_⟩
  ext e
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨e₀, he₀, rfl⟩
    obtain ⟨a, b, c, hab, hbc, hbit, rfl⟩ := mem_graphOfMask_edges.mp he₀
    have himg : Finset.image (⇑(Equiv.ofBijective f hbij)) {a, b, c}
        = ({f a, f b, f c} : Finset (Fin n)) := by
      rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton]
      rfl
    rw [himg]
    have hfab : f a ≠ f b := fun hEq => hab.ne (hf hEq)
    have hfac : f a ≠ f c := fun hEq => (hab.trans hbc).ne (hf hEq)
    have hfbc : f b ≠ f c := fun hEq => hbc.ne (hf hEq)
    obtain ⟨hs₁, hs₂⟩ := sort3_sorted hfab hfac hfbc
    refine mem_graphOfMask_edges.mpr
      ⟨(sort3 (f a) (f b) (f c)).1, (sort3 (f a) (f b) (f c)).2.1,
        (sort3 (f a) (f b) (f c)).2.2, hs₁, hs₂, ?_,
        (sort3_finset _ _ _).symm⟩
    rw [← hbits a b c hab hbc]
    exact hbit
  · intro he
    obtain ⟨x, y, z, hxy, hyz, hbit, rfl⟩ := mem_graphOfMask_edges.mp he
    set p := Equiv.ofBijective f hbij with hp
    have hd₁ : p.symm x ≠ p.symm y := fun hEq => hxy.ne (p.symm.injective hEq)
    have hd₂ : p.symm x ≠ p.symm z :=
      fun hEq => (hxy.trans hyz).ne (p.symm.injective hEq)
    have hd₃ : p.symm y ≠ p.symm z := fun hEq => hyz.ne (p.symm.injective hEq)
    obtain ⟨ht₁, ht₂⟩ := sort3_sorted hd₁ hd₂ hd₃
    set s := sort3 (p.symm x) (p.symm y) (p.symm z) with hs
    have himgset : Finset.image f {s.1, s.2.1, s.2.2}
        = ({x, y, z} : Finset (Fin n)) := by
      rw [hs, sort3_finset, Finset.image_insert, Finset.image_insert,
        Finset.image_singleton]
      show ({p (p.symm x), p (p.symm y), p (p.symm z)} : Finset (Fin n)) = _
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
    have hfd₁ : f s.1 ≠ f s.2.1 := fun hEq => ht₁.ne (hf hEq)
    have hfd₂ : f s.1 ≠ f s.2.2 := fun hEq => (ht₁.trans ht₂).ne (hf hEq)
    have hfd₃ : f s.2.1 ≠ f s.2.2 := fun hEq => ht₂.ne (hf hEq)
    obtain ⟨hu₁, hu₂⟩ := sort3_sorted hfd₁ hfd₂ hfd₃
    have htriple : ({(sort3 (f s.1) (f s.2.1) (f s.2.2)).1,
        (sort3 (f s.1) (f s.2.1) (f s.2.2)).2.1,
        (sort3 (f s.1) (f s.2.1) (f s.2.2)).2.2} : Finset (Fin n))
          = {x, y, z} := by
      rw [sort3_finset,
        show ({f s.1, f s.2.1, f s.2.2} : Finset (Fin n))
          = Finset.image f {s.1, s.2.1, s.2.2} from by
            rw [Finset.image_insert, Finset.image_insert,
              Finset.image_singleton]]
      exact himgset
    obtain ⟨he₁, he₂, he₃⟩ := sorted_triple_eq hu₁ hu₂ hxy hyz htriple
    refine ⟨{s.1, s.2.1, s.2.2}, ?_, ?_⟩
    · refine mem_graphOfMask_edges.mpr ⟨s.1, s.2.1, s.2.2, ht₁, ht₂, ?_, rfl⟩
      have hb := hbits s.1 s.2.1 s.2.2 ht₁ ht₂
      rw [he₁, he₂, he₃] at hb
      rw [hb]
      exact hbit
    · show Finset.image f {s.1, s.2.1, s.2.2} = {x, y, z}
      exact himgset

/-- Bit-level isomorphism transports to equality of flag classes: the
sweep's per-mask verdicts identify flags with listed representatives. -/
theorem graphOfMask_toFlag_eq_of_bits {𝕋 : RelTheory hypergraph3Sig}
    {n : ℕ} {f : Fin n → Fin n} (hf : Function.Injective f) {m h : ℕ}
    (hbits : ∀ a b c : Fin n, a < b → b < c →
      m.testBit (triIdx n a.val b.val c.val)
        = h.testBit (triIdx n (sort3 (f a) (f b) (f c)).1.val
            (sort3 (f a) (f b) (f c)).2.1.val
            (sort3 (f a) (f b) (f c)).2.2.val))
    (hm : 𝕋.Mem (graphOfMask n m).toModel)
    (hh : 𝕋.Mem (graphOfMask n h).toModel) :
    (graphOfMask n m).toFlag hm = (graphOfMask n h).toFlag hh :=
  (Sym3Graph.toFlag_eq_toFlag_iff hm hh).mpr
    (isIso_graphOfMask_of_bits hf hbits)

/-- A kernel-checked instance of the bridge, in the exact shape the
canonicalization sweep emits: the single-triple masks `{0,1,2}` and
`{1,2,3}` on four vertices are isomorphic via the cyclic vertex map. -/
example : (graphOfMask 4 1).IsIso (graphOfMask 4 8) :=
  isIso_graphOfMask_of_bits (f := ![1, 2, 3, 0]) (by decide) (by decide)

/-! ## Encoding graphs as masks

`maskOfGraph` inverts `graphOfMask`: fold the sorted triples, setting the
rank bit of each hyperedge. The generic `testBit` description of such
folds, a bound keeping the result inside the mask range, and the
roundtrip give surjectivity of the decoding — every computational
3-graph is the decoding of a mask, which is how sweeps over masks reach
every graph. -/

/-- Bits of an or-accumulating fold: bit `i` is set iff it was set in
the seed or some listed element satisfies the guard and maps to `i`. -/
lemma testBit_foldl_or {α : Type} (c : α → Prop) [DecidablePred c]
    (g : α → ℕ) (l : List α) (acc : ℕ) (i : ℕ) :
    (l.foldl (fun a t => if c t then a ||| (1 <<< g t) else a) acc).testBit i
      = (acc.testBit i || l.any fun t => decide (c t) && decide (g t = i)) := by
  induction l generalizing acc with
  | nil => simp
  | cons t ts ih =>
    rw [List.foldl_cons, ih, List.any_cons]
    have hshift : ((1 <<< g t : ℕ)).testBit i = decide (g t = i) := by
      rw [Nat.one_shiftLeft]
      rcases eq_or_ne (g t) i with heq | hne
      · rw [heq, Nat.testBit_two_pow_self, decide_eq_true rfl]
      · rw [Nat.testBit_two_pow_of_ne hne, decide_eq_false hne]
    by_cases hc : c t
    · rw [if_pos hc, decide_eq_true hc, Nat.testBit_lor, hshift]
      cases acc.testBit i <;> cases hgt : (decide (g t = i)) <;> simp
    · rw [if_neg hc, decide_eq_false hc]
      simp

/-- An or-accumulating fold over bit positions below `k` stays below
`2 ^ k`. -/
lemma foldl_or_lt_two_pow {α : Type} (c : α → Prop) [DecidablePred c]
    (g : α → ℕ) (l : List α) (acc k : ℕ) (hacc : acc < 2 ^ k)
    (hg : ∀ t ∈ l, g t < k) :
    l.foldl (fun a t => if c t then a ||| (1 <<< g t) else a) acc < 2 ^ k := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons t ts ih =>
    rw [List.foldl_cons]
    have hg' : ∀ t' ∈ ts, g t' < k := fun t' ht' =>
      hg t' (List.mem_cons_of_mem t ht')
    have hacc' : (if c t then acc ||| (1 <<< g t) else acc) < 2 ^ k := by
      by_cases hc : c t
      · rw [if_pos hc]
        refine Nat.or_lt_two_pow hacc ?_
        rw [Nat.one_shiftLeft]
        exact Nat.pow_lt_pow_right (by omega) (hg t List.mem_cons_self)
      · rwa [if_neg hc]
    exact ih _ hacc' hg'

/-- Encode a computational 3-graph as its bitmask. -/
def maskOfGraph {n : ℕ} (G : Sym3Graph n) : ℕ :=
  (finTriples n).foldl (fun acc t =>
    if ({t.1, t.2.1, t.2.2} : Finset (Fin n)) ∈ G.edges then
      acc ||| (1 <<< triIdx n t.1.val t.2.1.val t.2.2.val)
    else acc) 0

/-- Roundtrip: decoding the encoding recovers the graph, given
injectivity of the rank on the listed triples (kernel-checkable for each
fixed vertex count). -/
lemma graphOfMask_maskOfGraph {n : ℕ}
    (hinj : ∀ t₁ ∈ finTriples n, ∀ t₂ ∈ finTriples n,
      triIdx n t₁.1.val t₁.2.1.val t₁.2.2.val
        = triIdx n t₂.1.val t₂.2.1.val t₂.2.2.val → t₁ = t₂)
    (G : Sym3Graph n) : graphOfMask n (maskOfGraph G) = G := by
  refine Sym3Graph.ext ?_
  ext e
  rw [mem_graphOfMask_edges]
  constructor
  · rintro ⟨a, b, c, hab, hbc, hbit, rfl⟩
    rw [maskOfGraph, testBit_foldl_or] at hbit
    rcases Bool.or_eq_true_iff.mp hbit with hz | hany
    · rw [Nat.zero_testBit] at hz
      cases hz
    · obtain ⟨t, htmem, hcond⟩ := List.any_eq_true.mp hany
      rw [Bool.and_eq_true] at hcond
      have hedge := of_decide_eq_true hcond.1
      have hrank := of_decide_eq_true hcond.2
      have hteq : t = (a, b, c) :=
        hinj t htmem (a, b, c) (mem_finTriples.mpr ⟨hab, hbc⟩) hrank
      rw [hteq] at hedge
      exact hedge
  · intro he
    have hcard := G.edges_valid e he
    obtain ⟨a, b, c, hab, hbc, rfl⟩ := exists_sorted_triple hcard
    refine ⟨a, b, c, hab, hbc, ?_, rfl⟩
    rw [maskOfGraph, testBit_foldl_or]
    refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
    refine List.any_eq_true.mpr ⟨(a, b, c), mem_finTriples.mpr ⟨hab, hbc⟩, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true he, decide_eq_true rfl⟩

/-- Every computational 3-graph is the decoding of a mask below
`2 ^ C(n,3)`, given rank injectivity and the rank bound on the listed
triples. -/
lemma exists_mask_graphOfMask {n k : ℕ}
    (hinj : ∀ t₁ ∈ finTriples n, ∀ t₂ ∈ finTriples n,
      triIdx n t₁.1.val t₁.2.1.val t₁.2.2.val
        = triIdx n t₂.1.val t₂.2.1.val t₂.2.2.val → t₁ = t₂)
    (hbound : ∀ t ∈ finTriples n, triIdx n t.1.val t.2.1.val t.2.2.val < k)
    (G : Sym3Graph n) : ∃ m, m < 2 ^ k ∧ graphOfMask n m = G :=
  ⟨maskOfGraph G,
    foldl_or_lt_two_pow _ _ _ _ _ (Nat.two_pow_pos k) hbound,
    graphOfMask_maskOfGraph hinj G⟩

/-! ## The depth-shallow mask sweep

Exhaustive checks over all masks below a power of two, as a binary tree
on the bits: recursion depth is the bit count while the leaves cover the
whole range, the same shape that keeps `allEdgeSetsSat` inside the kernel
stack. The reflection lemma turns the single `Bool` verdict into the
per-mask statement. -/

/-- Check `P` on every mask `m₀ * 2^d + r` with `r < 2^d`, at recursion
depth `d`. -/
def sweepMasks (P : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, m => P m
  | d + 1, m => sweepMasks P d (2 * m) && sweepMasks P d (2 * m + 1)

/-- Reflection: a true sweep verdict yields `P` on every mask in the
range. -/
lemma sweepMasks_spec (P : ℕ → Bool) (d : ℕ) :
    ∀ m₀, sweepMasks P d m₀ = true →
      ∀ r, r < 2 ^ d → P (m₀ * 2 ^ d + r) = true := by
  induction d with
  | zero =>
    intro m₀ hs r hr
    have hr0 : r = 0 := by omega
    subst hr0
    simpa [sweepMasks] using hs
  | succ d ih =>
    intro m₀ hs r hr
    rw [sweepMasks, Bool.and_eq_true] at hs
    obtain ⟨h₁, h₂⟩ := hs
    have h2p : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by
      rw [pow_succ]
      omega
    by_cases hcase : r < 2 ^ d
    · have hh := ih (2 * m₀) h₁ r hcase
      have heq : m₀ * 2 ^ (d + 1) + r = 2 * m₀ * 2 ^ d + r := by
        rw [h2p]
        ring
      rw [heq]
      exact hh
    · have hh := ih (2 * m₀ + 1) h₂ (r - 2 ^ d) (by omega)
      have hexp : (2 * m₀ + 1) * 2 ^ d = 2 * m₀ * 2 ^ d + 2 ^ d := by ring
      have heq : m₀ * 2 ^ (d + 1) + r
          = (2 * m₀ + 1) * 2 ^ d + (r - 2 ^ d) := by
        rw [hexp, h2p]
        have : 2 ^ d ≤ r := not_lt.mp hcase
        have hdistrib : m₀ * (2 ^ d + 2 ^ d) = 2 * m₀ * 2 ^ d := by ring
        omega
      rw [heq]
      exact hh

/-- Glue: a sweep of depth `d + e` follows from the `2^e` sweeps of
depth `d` over the subranges — the shape that lets the pieces build in
parallel and assemble into one verdict. -/
lemma sweepMasks_of_pieces (P : ℕ → Bool) (d : ℕ) :
    ∀ (e m₀ : ℕ), (∀ j, j < 2 ^ e → sweepMasks P d (m₀ * 2 ^ e + j) = true) →
      sweepMasks P (d + e) m₀ = true := by
  intro e
  induction e with
  | zero =>
    intro m₀ h
    simpa using h 0 (by omega)
  | succ e ih =>
    intro m₀ h
    have h2p : 2 ^ (e + 1) = 2 ^ e + 2 ^ e := by
      rw [pow_succ]
      omega
    show sweepMasks P (d + e + 1) m₀ = true
    rw [sweepMasks, Bool.and_eq_true]
    constructor
    · refine ih (2 * m₀) fun j hj => ?_
      have heq : 2 * m₀ * 2 ^ e + j = m₀ * 2 ^ (e + 1) + j := by
        rw [h2p]
        ring
      rw [heq]
      exact h j (by omega)
    · refine ih (2 * m₀ + 1) fun j hj => ?_
      have hexp : (2 * m₀ + 1) * 2 ^ e = 2 * m₀ * 2 ^ e + 2 ^ e := by ring
      have heq : (2 * m₀ + 1) * 2 ^ e + j = m₀ * 2 ^ (e + 1) + (2 ^ e + j) := by
        rw [hexp, h2p]
        have hdistrib : m₀ * (2 ^ e + 2 ^ e) = 2 * m₀ * 2 ^ e := by ring
        omega
      rw [heq]
      exact h (2 ^ e + j) (by omega)

end FlagAlgebras.Core
