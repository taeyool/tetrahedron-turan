import LeanFlagAlgebras.Core.Compute.Sym3Downward

/-! # The fiber identity, at any rooted type

The downward expansion assigns each unlabeled class a coefficient that
sums over its typed fiber. For a class realized by a literal host, that
fiber is enumerated by the host's well-formed rootings: each typed class
over the host is the class of a rooting, and the number of rootings
giving one typed class is exactly its computable labeling count — which
is the numerator of the labeling factor.

So the fiber sum of any weight, with the labeling factors, is the plain
rooting average of the weight. The order-5 certificate proved this for
its one rooted type; the order-7 certificate needs it at four, so this
file states it generically over the type graph.

`Sym3Flag.unlabel_toFlag` used to live in the order-5 example; it was
always generic and moves here. -/

namespace FlagAlgebras.Core

open Classical

variable {k n : ℕ}

/-- The unlabeling of a typed literal class is the literal class of its
graph, at the class level. -/
lemma Sym3Flag.unlabel_toFlag {𝕋 : RelTheory hypergraph3Sig}
    [𝕋.IsType (emptyType hypergraph3Sig)]
    {σg : Sym3Graph k} [𝕋.IsType σg.toModel]
    {Fσ : Sym3Flag k n} (hwf : Fσ.WellFormed σg)
    (hmem : 𝕋.Mem Fσ.graph.toModel) :
    Flag.unlabel (Fσ.toFlag (𝕋 := 𝕋) hwf hmem) = Fσ.graph.toFlag hmem :=
  rfl

/-- The well-formed rootings of a host over a literal type. -/
def rootingsOf (σg : Sym3Graph k) (G : Sym3Graph n) :
    Finset (Fin k → Fin n) :=
  Finset.univ.filter fun θ => (Sym3Flag.mk G θ).WellFormed σg

lemma mem_rootingsOf {σg : Sym3Graph k} {G : Sym3Graph n}
    {θ : Fin k → Fin n} :
    θ ∈ rootingsOf σg G ↔ (Sym3Flag.mk G θ).WellFormed σg := by
  rw [rootingsOf, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- Realization: every typed class over the unlabeling of a literal host
is the class of one of its rootings. -/
lemma exists_rooting_class' {𝕋 : RelTheory hypergraph3Sig}
    [𝕋.IsType (emptyType hypergraph3Sig)]
    {σg : Sym3Graph k} [𝕋.IsType σg.toModel]
    {G : Sym3Graph n} (hG : 𝕋.Mem G.toModel)
    {X : FlagWithSize 𝕋 σg.toModel n}
    (hX : Flag.unlabel X = G.toFlag hG) :
    ∃ θ, ∃ hwf : (Sym3Flag.mk G θ).WellFormed σg,
      (Sym3Flag.mk G θ).toFlag hwf hG = X := by
  have hout : (Quotient.out X).unlabel.toFlag = G.toFlag hG := by
    rw [out_unlabel_toFlag_eq]
    exact hX
  obtain ⟨i⟩ := Quotient.exact hout
  have e : (Quotient.out X).toModel ≃ᵣ G.toModel := i.toIso
  have hinj : Function.Injective
      (fun t => e.toEquiv ((Quotient.out X).rootEmbed.toEmbedding t)) :=
    fun a b hab => (Quotient.out X).rootEmbed.toEmbedding.injective
      (e.toEquiv.injective hab)
  have hwf : (Sym3Flag.mk G
      (fun t => e.toEquiv
        ((Quotient.out X).rootEmbed.toEmbedding t))).WellFormed σg := by
    refine ⟨hinj, ?_⟩
    apply Sym3Graph.toModel_injective
    rw [Sym3Graph.pullback_toModel _ hinj]
    refine Model.ext ?_
    funext r f
    cases r
    exact propext (Iff.trans (e.interp_iff () _)
      ((Quotient.out X).rootEmbed.interp_iff () f))
  refine ⟨_, hwf, ?_⟩
  have hiso : (Sym3Flag.mk G _).toLabeledFlag hwf hG
      ≃ᶠ Quotient.out X :=
    ⟨e.symm, fun t => e.toEquiv.symm_apply_apply _⟩
  calc (Sym3Flag.mk G _).toFlag hwf hG
      = ⟦Quotient.out X⟧ := Quotient.sound ⟨hiso⟩
    _ = X := Quotient.out_eq X

/-- **The fiber identity**: the labeling-weighted fiber sum of any
weight over a literal host is the plain rooting average. -/
theorem fiber_sum_eq_rooting_sum {𝕋 : RelTheory hypergraph3Sig}
    [𝕋.IsType (emptyType hypergraph3Sig)]
    {σg : Sym3Graph k} [𝕋.IsType σg.toModel] (hkn : k ≤ n)
    (w : FlagWithSize 𝕋 σg.toModel n → ℝ)
    {G : Sym3Graph n} (hG : 𝕋.Mem G.toModel) :
    (∑ X ∈ Finset.univ.filter
        (fun X : FlagWithSize 𝕋 σg.toModel n =>
          Flag.unlabel X = G.toFlag hG),
      w X * (labelingFactor (Quotient.out X).unlabel
        (Quotient.out X) : ℝ))
      = (1 / (n.descFactorial k : ℝ)) * ∑ θ ∈ (rootingsOf σg G).attach,
          w ((Sym3Flag.mk G θ.val).toFlag
            (mem_rootingsOf.mp θ.property) hG) := by
  classical
  have hdesc : (n.descFactorial k : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hkn).ne'
  have hdescR : (n.descFactorial k : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hkn).ne'
  set kmap : {θ // θ ∈ rootingsOf σg G} →
      FlagWithSize 𝕋 σg.toModel n :=
    fun θ => (Sym3Flag.mk G θ.val).toFlag
      (mem_rootingsOf.mp θ.property) hG with hkmap
  have hfibcard : ∀ X : FlagWithSize 𝕋 σg.toModel n,
      Flag.unlabel X = G.toFlag hG →
      ((((rootingsOf σg G).attach.filter fun θ => kmap θ = X).card : ℚ))
        = (n.descFactorial k : ℚ)
          * labelingFactor (Quotient.out X).unlabel (Quotient.out X) := by
    intro X hX
    obtain ⟨θ₀, hwf₀, hXeq⟩ := exists_rooting_class' hG hX
    rw [← hXeq, Sym3Flag.labelingFactor_out hwf₀ hG]
    rw [show (((rootingsOf σg G).attach.filter fun θ =>
        kmap θ = (Sym3Flag.mk G θ₀).toFlag hwf₀ hG).card)
        = (Sym3Flag.mk G θ₀).labelingCountC σg from ?_]
    · rw [mul_comm, div_mul_cancel₀ _ hdesc]
    · rw [Sym3Flag.labelingCountC]
      refine Finset.card_bij (fun θ _ => θ.val) ?_ ?_ ?_
      · rintro θ hθ
        have hkθ := (Finset.mem_filter.mp hθ).2
        have hwfθ := mem_rootingsOf.mp θ.property
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwfθ, ?_⟩
        exact (Sym3Flag.toFlag_eq_toFlag_iff hwfθ hwf₀ hG hG).mp hkθ
      · rintro θ _ θ' _ h
        exact Subtype.ext h
      · rintro θ' hθ'
        obtain ⟨-, hwf', hiso'⟩ := Finset.mem_filter.mp hθ'
        refine ⟨⟨θ', mem_rootingsOf.mpr hwf'⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ?_⟩, rfl⟩
        exact (Sym3Flag.toFlag_eq_toFlag_iff hwf' hwf₀ hG hG).mpr hiso'
  have hfibzero : ∀ X : FlagWithSize 𝕋 σg.toModel n,
      ¬(Flag.unlabel X = G.toFlag hG) →
      ((rootingsOf σg G).attach.filter fun θ => kmap θ = X) = ∅ := by
    intro X hX
    refine Finset.eq_empty_iff_forall_notMem.mpr fun θ hθ => hX ?_
    have hkθ := (Finset.mem_filter.mp hθ).2
    rw [← hkθ, hkmap]
    exact Sym3Flag.unlabel_toFlag _ hG
  rw [Finset.sum_congr rfl fun X hX => by
      rw [show (labelingFactor (Quotient.out X).unlabel
          (Quotient.out X) : ℝ)
          = ((((rootingsOf σg G).attach.filter
              fun θ => kmap θ = X).card : ℝ)) / (n.descFactorial k : ℝ)
        from by
          have h := hfibcard X (Finset.mem_filter.mp hX).2
          have h' := congrArg (fun q : ℚ => (q : ℝ)) h
          push_cast at h'
          rw [eq_div_iff hdescR, mul_comm]
          exact h'.symm]]
  rw [show (∑ X ∈ Finset.univ.filter
      (fun X : FlagWithSize 𝕋 σg.toModel n =>
        Flag.unlabel X = G.toFlag hG),
      w X * (((((rootingsOf σg G).attach.filter
        fun θ => kmap θ = X).card : ℝ)) / (n.descFactorial k : ℝ)))
      = ∑ X : FlagWithSize 𝕋 σg.toModel n,
        w X * (((((rootingsOf σg G).attach.filter
          fun θ => kmap θ = X).card : ℝ)) / (n.descFactorial k : ℝ)) from
    Finset.sum_subset (Finset.filter_subset _ _) fun X _ hX => by
      rw [hfibzero X (by simpa using hX), Finset.card_empty]
      simp]
  calc ∑ X : FlagWithSize 𝕋 σg.toModel n,
        w X * (((((rootingsOf σg G).attach.filter
          fun θ => kmap θ = X).card : ℝ)) / (n.descFactorial k : ℝ))
      = ∑ X : FlagWithSize 𝕋 σg.toModel n,
          (1 / (n.descFactorial k : ℝ)) * ∑ θ ∈ (rootingsOf σg G).attach.filter
            (fun θ => kmap θ = X), w (kmap θ) := by
        refine Finset.sum_congr rfl fun X _ => ?_
        rw [Finset.sum_congr rfl fun θ hθ => by
            rw [(Finset.mem_filter.mp hθ).2],
          Finset.sum_const, nsmul_eq_mul]
        ring
    _ = (1 / (n.descFactorial k : ℝ)) * ∑ X : FlagWithSize 𝕋 σg.toModel n,
          ∑ θ ∈ (rootingsOf σg G).attach.filter (fun θ => kmap θ = X),
            w (kmap θ) := by
        rw [Finset.mul_sum]
    _ = (1 / (n.descFactorial k : ℝ))
          * ∑ θ ∈ (rootingsOf σg G).attach, w (kmap θ) :=
        congrArg (fun z => (1 / (n.descFactorial k : ℝ)) * z)
          (@Finset.sum_fiberwise _ _ _ _ _ _ (rootingsOf σg G).attach kmap
            fun θ => w (kmap θ))

end FlagAlgebras.Core
