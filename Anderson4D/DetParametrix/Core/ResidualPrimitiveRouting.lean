import Anderson4D.DetParametrix.Core.ResidualCollapse
import Anderson4D.Continuum.PrimitiveProposition41

/-!
# Primitive analytic bounds for the residual R-324 blocks

Paper §4.2 Step 3 successively reduces the nested residual blocks left after
the two within-copy reductions.  `ResidualCollapse.lean` proves that every
such sparse block is fully paired and relatively primitive.  This file
connects those certificates to the actual Proposition 4.1 estimate:

* a sparse block is increasingly reindexed by `Fin B.card`;
* its restricted pairing is full and primitive after this reindexing;
* its cardinality is even, giving the canonical order `q = B.card / 2`;
* the resulting pairing belongs to `primitiveFullPairings q`;
* for nonnegative dominating inputs, its concrete ordinary and inserted
  integral terms satisfy the pointwise (4.3)--(4.4) majorants.

The final theorem is a term-level analytic bound obtained from the proved
`proposition41`; it is not an R-324 output predicate and does not assume
either branch of (3.24).
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## Increasing transport of a sparse paired block -/

/-- Restrict a pairing to a closed sparse block and transport it along an
increasing enumeration of that block. -/
def orderedBlockPairing {n k : ℕ} (κ : PartialPairing (Fin n))
    (B : Finset (Fin n)) (hB : IsFullyPairedOn κ B)
    (e : Fin k ≃o B) : PartialPairing (Fin k) :=
  PartialPairing.congr e.symm.toEquiv
    (PartialPairing.restrictTo κ hB.2)

@[simp]
theorem orderedBlockPairing_apply
    {n k : ℕ} (κ : PartialPairing (Fin n))
    (B : Finset (Fin n)) (hB : IsFullyPairedOn κ B)
    (e : Fin k ≃o B) (i : Fin k) :
    (e (orderedBlockPairing κ B hB e i)).1 = κ (e i).1 := by
  change
    (e (e.symm
      (PartialPairing.restrictTo κ hB.2 (e i)))).1 =
        κ (e i).1
  rw [e.apply_symm_apply]
  rfl

/-- Closure and absence of fixed points are preserved by the increasing
reindexing. -/
theorem orderedBlockPairing_isFull
    {n k : ℕ} (κ : PartialPairing (Fin n))
    (B : Finset (Fin n)) (hB : IsFullyPairedOn κ B)
    (e : Fin k ≃o B) :
    (orderedBlockPairing κ B hB e).IsFull := by
  have hr : (PartialPairing.restrictTo κ hB.2).IsFull := by
    intro i hi
    exact hB.ne_of_mem i.2 (congrArg Subtype.val hi)
  exact hr.congr e.symm.toEquiv

/-- Relative primitivity on the sparse carrier becomes ordinary paper
primitivity after increasing reindexing. -/
theorem orderedBlockPairing_isPrimitive
    {n k : ℕ} (κ : PartialPairing (Fin n))
    (B : Finset (Fin n)) (hB : IsFullyPairedOn κ B)
    (hprim : IsRelPrimitiveOn κ B) (e : Fin k ≃o B) :
    IsPrimitive (orderedBlockPairing κ B hB e) := by
  intro a b hab hI
  have hRel : IsRelFullyPaired κ B (e a).1 (e b).1 := by
    refine ⟨(e a).2, (e b).2, e.le_iff_le.mpr hab, ?_⟩
    constructor
    · intro i hi
      let ib : B := ⟨i, (mem_relIcc.mp hi).1⟩
      let x : Fin k := e.symm ib
      have hex : e x = ib := by
        exact e.apply_symm_apply ib
      have hx : x ∈ Finset.Icc a b := by
        rw [Finset.mem_Icc]
        exact
          ⟨e.le_iff_le.mp (by
              rw [hex]
              exact (mem_relIcc.mp hi).2.1),
            e.le_iff_le.mp (by
              rw [hex]
              exact (mem_relIcc.mp hi).2.2)⟩
      have hne := hI.ne_of_mem hx
      intro hfix
      apply hne
      apply e.injective
      apply Subtype.ext
      rw [orderedBlockPairing_apply]
      rw [hex]
      exact hfix
    · intro i hi
      let ib : B := ⟨i, (mem_relIcc.mp hi).1⟩
      let x : Fin k := e.symm ib
      have hex : e x = ib := by
        exact e.apply_symm_apply ib
      have hx : x ∈ Finset.Icc a b := by
        rw [Finset.mem_Icc]
        exact
          ⟨e.le_iff_le.mp (by
              rw [hex]
              exact (mem_relIcc.mp hi).2.1),
            e.le_iff_le.mp (by
              rw [hex]
              exact (mem_relIcc.mp hi).2.2)⟩
      have hmove := hI.apply_mem hx
      rw [Finset.mem_Icc] at hmove
      rw [mem_relIcc]
      refine ⟨hB.apply_mem (mem_relIcc.mp hi).1, ?_, ?_⟩
      · have hm := e.le_iff_le.mpr hmove.1
        calc
          (e a).1 ≤
              (e (orderedBlockPairing κ B hB e x)).1 := hm
          _ = κ (e x).1 :=
            orderedBlockPairing_apply κ B hB e x
          _ = κ i := by rw [hex]
      · have hm := e.le_iff_le.mpr hmove.2
        calc
          κ i = κ (e x).1 := by rw [hex]
          _ = (e (orderedBlockPairing κ B hB e x)).1 :=
            (orderedBlockPairing_apply κ B hB e x).symm
          _ ≤ (e b).1 := hm
  have hall := hprim (e a).1 (e b).1 hRel
  ext x
  simp only [Finset.mem_Icc, Finset.mem_univ, iff_true]
  have hx : (e x).1 ∈ relIcc B (e a).1 (e b).1 := by
    rw [hall]
    exact (e x).2
  exact
    ⟨e.le_iff_le.mp (mem_relIcc.mp hx).2.1,
      e.le_iff_le.mp (mem_relIcc.mp hx).2.2⟩

/-- A fully paired sparse block has even cardinality. -/
theorem residualBlock_card_even
    {n : ℕ} (κ : PartialPairing (Fin n))
    (B : Finset (Fin n)) (hB : IsFullyPairedOn κ B) :
    Even B.card := by
  let e : Fin B.card ≃o B := B.orderIsoOfFin rfl
  simpa using (orderedBlockPairing_isFull κ B hB e).even_card

/-- The perturbative order carried by a residual block. -/
def residualBlockOrder {n : ℕ} (B : Finset (Fin n)) : ℕ :=
  B.card / 2

/-- Canonical increasing enumeration of an even residual block. -/
def residualPrimitiveBlockOrderIso {n : ℕ}
    (κ : PartialPairing (Fin n)) (B : Finset (Fin n))
    (hB : IsFullyPairedOn κ B) :
    Fin (2 * residualBlockOrder B) ≃o B :=
  B.orderIsoOfFin
    (Nat.two_mul_div_two_of_even
      (residualBlock_card_even κ B hB)).symm

/-- The canonical standard-index pairing carried by a residual block. -/
def residualPrimitiveBlockPairing {n : ℕ}
    (κ : PartialPairing (Fin n)) (B : Finset (Fin n))
    (hB : IsFullyPairedOn κ B) :
    PartialPairing (Fin (2 * residualBlockOrder B)) :=
  orderedBlockPairing κ B hB
    (residualPrimitiveBlockOrderIso κ B hB)

/-- A certified residual block is a genuine member of the primitive-pairing
sum in Proposition 4.1 at its exact half-cardinality order. -/
theorem residualPrimitiveBlockPairing_mem
    {n : ℕ} (κ : PartialPairing (Fin n))
    (B : Finset (Fin n)) (hB : IsFullyPairedOn κ B)
    (hprim : IsRelPrimitiveOn κ B) :
    residualPrimitiveBlockPairing κ B hB ∈
      primitiveFullPairings (residualBlockOrder B) := by
  rw [mem_primitiveFullPairings]
  exact
    ⟨orderedBlockPairing_isFull κ B hB _,
      orderedBlockPairing_isPrimitive κ B hB hprim _⟩

/-! ## Disjointness and the exact order ledger -/

/-- Membership in the union of a list of finite blocks. -/
theorem mem_finsetUnionList_iff
    {α : Type*} [DecidableEq α] {x : α}
    (blocks : List (Finset α)) :
    x ∈ finsetUnionList blocks ↔
      ∃ B ∈ blocks, x ∈ B := by
  induction blocks with
  | nil =>
      simp [finsetUnionList]
  | cons B blocks ih =>
      simp only [finsetUnionList, Finset.mem_union, List.mem_cons]
      constructor
      · rintro (hx | hx)
        · exact ⟨B, Or.inl rfl, hx⟩
        · obtain ⟨C, hC, hxC⟩ := ih.mp hx
          exact ⟨C, Or.inr hC, hxC⟩
      · rintro ⟨C, rfl | hC, hxC⟩
        · exact Or.inl hxC
        · exact Or.inr (ih.mpr ⟨C, hC, hxC⟩)

/-- The current trace is disjoint from every subsequent shell and from the
final exterior. -/
theorem residualIntervalTrace_disjoint_nestedResidualShells
    {n : ℕ} (active : Finset (Fin n))
    (previous : Fin n × Fin n)
    (rest : List (Fin n × Fin n))
    (hpair :
      (previous :: rest).Pairwise LaterCrossCutIntervalContains) :
    ∀ B ∈ nestedResidualShells active previous rest,
      Disjoint (residualIntervalTrace active previous) B := by
  induction rest generalizing previous with
  | nil =>
      intro B hB
      simp only [nestedResidualShells, List.mem_singleton] at hB
      subst B
      exact Finset.disjoint_sdiff
  | cons next rest ih =>
      have hcons := List.pairwise_cons.mp hpair
      have hnext :
          LaterCrossCutIntervalContains previous next :=
        hcons.1 next (by simp)
      have htail :
          (next :: rest).Pairwise LaterCrossCutIntervalContains :=
        hcons.2
      intro B hB
      simp only [nestedResidualShells, List.mem_cons] at hB
      rcases hB with rfl | hB
      · exact Finset.disjoint_sdiff
      · exact Disjoint.mono_left
          (residualIntervalTrace_subset hnext)
          (ih next htail B hB)

/-- Successive shells and the exterior of a nested interval chain are
pairwise disjoint. -/
theorem nestedResidualShells_pairwise_disjoint
    {n : ℕ} (active : Finset (Fin n))
    (previous : Fin n × Fin n)
    (rest : List (Fin n × Fin n))
    (hpair :
      (previous :: rest).Pairwise LaterCrossCutIntervalContains) :
    (nestedResidualShells active previous rest).Pairwise Disjoint := by
  induction rest generalizing previous with
  | nil =>
      simp [nestedResidualShells]
  | cons next rest ih =>
      have hcons := List.pairwise_cons.mp hpair
      have hnext :
          LaterCrossCutIntervalContains previous next :=
        hcons.1 next (by simp)
      have htail :
          (next :: rest).Pairwise LaterCrossCutIntervalContains :=
        hcons.2
      rw [nestedResidualShells, List.pairwise_cons]
      constructor
      · intro B hB
        exact Disjoint.mono Finset.sdiff_subset (by rfl)
          (residualIntervalTrace_disjoint_nestedResidualShells
            active next rest htail B hB)
      · exact ih next htail

/-- The trace/shell/exterior decomposition associated with a nested chain is
pairwise disjoint. -/
theorem residualCollapseBlocks_pairwise_disjoint
    {n : ℕ} (active : Finset (Fin n))
    (chain : List (Fin n × Fin n))
    (hpair : chain.Pairwise LaterCrossCutIntervalContains) :
    (residualCollapseBlocks active chain).Pairwise Disjoint := by
  cases chain with
  | nil =>
      simp [residualCollapseBlocks]
  | cons first rest =>
      rw [residualCollapseBlocks, List.pairwise_cons]
      exact
        ⟨residualIntervalTrace_disjoint_nestedResidualShells
            active first rest hpair,
          nestedResidualShells_pairwise_disjoint
            active first rest hpair⟩

/-- Pairwise-disjoint finite blocks have additive cardinality under
`finsetUnionList`. -/
theorem card_finsetUnionList_eq_sum_card
    {α : Type*} [DecidableEq α]
    (blocks : List (Finset α))
    (hdisjoint : blocks.Pairwise Disjoint) :
    (finsetUnionList blocks).card =
      (blocks.map Finset.card).sum := by
  induction blocks with
  | nil =>
      simp [finsetUnionList]
  | cons B blocks ih =>
      have hcons := List.pairwise_cons.mp hdisjoint
      have hBunion : Disjoint B (finsetUnionList blocks) := by
        rw [Finset.disjoint_left]
        intro x hxB hxUnion
        obtain ⟨C, hC, hxC⟩ :=
          (mem_finsetUnionList_iff blocks).mp hxUnion
        exact (Finset.disjoint_left.mp (hcons.1 C hC)) hxB hxC
      rw [finsetUnionList, Finset.card_union_of_disjoint hBunion,
        List.map_cons, List.sum_cons, ih hcons.2]

/-- Exact cardinality ledger for the concrete R-324 collapse blocks. -/
theorem sum_card_momentResidualCollapseBlocks
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    ((momentResidualCollapseBlocks κp κm π).map Finset.card).sum =
      (momentResidualActive κp κm).card := by
  have hdisjoint :
      (momentResidualCollapseBlocks κp κm π).Pairwise Disjoint :=
    residualCollapseBlocks_pairwise_disjoint
      (momentResidualActive κp κm)
      (momentResidualIntervalChain κp κm π)
      (momentResidualIntervalChain_pairwise_laterContains κp κm π)
  calc
    ((momentResidualCollapseBlocks κp κm π).map Finset.card).sum =
        (finsetUnionList
          (momentResidualCollapseBlocks κp κm π)).card :=
      (card_finsetUnionList_eq_sum_card _ hdisjoint).symm
    _ = (momentResidualActive κp κm).card := by
      rw [finsetUnionList_momentResidualCollapseBlocks]

/-- For a list of even blocks, twice the sum of their half-cardinality orders
is the sum of their cardinalities. -/
theorem two_mul_sum_residualBlockOrder_eq_sum_card
    {n : ℕ} (blocks : List (Finset (Fin n)))
    (heven : blocks.Forall fun B => Even B.card) :
    2 * (blocks.map residualBlockOrder).sum =
      (blocks.map Finset.card).sum := by
  induction blocks with
  | nil =>
      simp
  | cons B blocks ih =>
      rw [List.forall_cons] at heven
      simp only [List.map_cons, List.sum_cons, mul_add]
      have hhead : 2 * residualBlockOrder B = B.card := by
        unfold residualBlockOrder
        exact Nat.two_mul_div_two_of_even heven.1
      rw [hhead, ih heven.2]

/-- Exact perturbative-order ledger for the concrete residual collapse:
the block orders add to half the number of residual variables. -/
theorem two_mul_sum_momentResidualBlockOrders
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    2 * ((momentResidualCollapseBlocks κp κm π).map
        residualBlockOrder).sum =
      (momentResidualActive κp κm).card := by
  have heven :
      (momentResidualCollapseBlocks κp κm π).Forall
        (fun B => Even B.card) :=
    (momentResidualCollapseBlocks_forall_isFullyPairedOn
      κp κm π).imp fun B hB =>
        residualBlock_card_even
          (momentCombinedPairing κp κm π) B hB
  exact
    (two_mul_sum_residualBlockOrder_eq_sum_card _ heven).trans
      (sum_card_momentResidualCollapseBlocks κp κm π)

/-! ## Concrete primitive-pairing terms -/

/-- One ordinary primitive-pairing summand, including its exact coupling. -/
def primitivePairingKernelTerm
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin (2 * n))) (z w : T4) : ℝ :=
  lamEps lam ε ^ (2 * n) *
    ∫ v : Fin (2 * n - 2) → T4,
      primitiveIntegrand ρ ε n hn G κ
        (primitiveAssemble n hn z w v)
      ∂(Measure.pi fun _ => paperMeasure)

/-- One inserted primitive-pairing summand, including its exact coupling. -/
def primitivePairingKernelInsertedTerm
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin (2 * n))) (z w : T4) : ℝ :=
  lamEps lam ε ^ (2 * n) *
    ∫ v : Fin (2 * n - 2) → T4,
      primitiveInsertedIntegrand ρ ε n hn G κ
        (primitiveAssemble n hn z w v)
      ∂(Measure.pi fun _ => paperMeasure)

theorem primitivePairingKernelTerm_nonneg
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j z, 0 ≤ G j z)
    (κ : PartialPairing (Fin (2 * n))) (z w : T4) :
    0 ≤ primitivePairingKernelTerm ρ lam ε n hn G κ z w := by
  apply mul_nonneg
  · exact (even_two_mul n).pow_nonneg _
  · exact integral_nonneg fun v =>
      primitiveIntegrand_nonneg ρ ε n hn G hG κ
        (primitiveAssemble n hn z w v)

theorem primitivePairingKernelInsertedTerm_nonneg
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j z, 0 ≤ G j z)
    (κ : PartialPairing (Fin (2 * n))) (z w : T4) :
    0 ≤ primitivePairingKernelInsertedTerm ρ lam ε n hn G κ z w := by
  apply mul_nonneg
  · exact (even_two_mul n).pow_nonneg _
  · exact integral_nonneg fun v =>
      primitiveInsertedIntegrand_nonneg ρ ε n hn G hG κ
        (primitiveAssemble n hn z w v)

/-- A nonnegative concrete primitive term is bounded by the complete
primitive sum containing it. -/
theorem primitivePairingKernelTerm_le_kernel
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j z, 0 ≤ G j z)
    (κ : PartialPairing (Fin (2 * n)))
    (hκ : κ ∈ primitiveFullPairings n) (z w : T4) :
    primitivePairingKernelTerm ρ lam ε n hn G κ z w ≤
      primitiveKernel ρ lam ε n hn G z w := by
  unfold primitivePairingKernelTerm primitiveKernel
  apply mul_le_mul_of_nonneg_left
  · apply Finset.single_le_sum (fun κ' _ => ?_) hκ
    exact integral_nonneg fun v =>
      primitiveIntegrand_nonneg ρ ε n hn G hG κ'
        (primitiveAssemble n hn z w v)
  · exact (even_two_mul n).pow_nonneg _

/-- Inserted counterpart of `primitivePairingKernelTerm_le_kernel`. -/
theorem primitivePairingKernelInsertedTerm_le_kernel
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j z, 0 ≤ G j z)
    (κ : PartialPairing (Fin (2 * n)))
    (hκ : κ ∈ primitiveFullPairings n) (z w : T4) :
    primitivePairingKernelInsertedTerm ρ lam ε n hn G κ z w ≤
      primitiveKernelInserted ρ lam ε n hn G z w := by
  unfold primitivePairingKernelInsertedTerm primitiveKernelInserted
  apply mul_le_mul_of_nonneg_left
  · apply Finset.single_le_sum (fun κ' _ => ?_) hκ
    exact integral_nonneg fun v =>
      primitiveInsertedIntegrand_nonneg ρ ε n hn G hG κ'
        (primitiveAssemble n hn z w v)
  · exact (even_two_mul n).pow_nonneg _

/-! ## Proposition 4.1 applied to every certified residual block -/

/-- Every certified nonempty residual primitive block satisfies the actual
ordinary and inserted Proposition 4.1 bounds, for its canonical transported
pairing.

The constants are chosen once by the proved `proposition41`, before the
ambient carrier, the block, the perturbative parameters, and the input
kernels.  The extra nonnegativity assumption is exactly the dominating
`|G_j|` branch used after taking absolute values in (4.19)--(4.20). -/
theorem exists_residualPrimitiveBlockPairing_term_bounds
    (ρ : SmoothCutoff) :
    ∃ orderConstant supportConstant C : ℝ,
      0 < orderConstant ∧ 0 < supportConstant ∧ 0 < C ∧
      ∀ {n : ℕ} (κ : PartialPairing (Fin n))
        (B : Finset (Fin n)) (hB : IsFullyPairedOn κ B),
        IsRelPrimitiveOn κ B →
        ∀ (lam ε : ℝ)
          (G : Fin (2 * residualBlockOrder B - 1) → T4 → ℝ),
          (hreg : PrimitiveEstimateRegime (residualBlockOrder B) lam ε
              orderConstant supportConstant C) →
          (hinput : IsAdmissiblePrimitiveInput (residualBlockOrder B) G) →
          (hnonneg : ∀ j z, 0 ≤ G j z) →
          ∀ z : T4,
            |primitivePairingKernelTerm ρ lam ε
                (residualBlockOrder B) hreg.1 G
                (residualPrimitiveBlockPairing κ B hB) z 0| ≤
              primitiveKernelMajorant C lam ε supportConstant
                (residualBlockOrder B) z ∧
            |primitivePairingKernelInsertedTerm ρ lam ε
                (residualBlockOrder B) hreg.1 G
                (residualPrimitiveBlockPairing κ B hB) z 0| ≤
              primitiveInsertedMajorant C lam ε supportConstant
                (residualBlockOrder B) z := by
  obtain ⟨orderConstant, supportConstant, C,
      horder, hsupport, hC, hprop⟩ := proposition41 ρ
  refine
    ⟨orderConstant, supportConstant, C,
      horder, hsupport, hC, ?_⟩
  intro n κ B hB hprim lam ε G hreg hG hGnonneg z
  let q := residualBlockOrder B
  have hq : 1 ≤ q := hreg.1
  have hmem : residualPrimitiveBlockPairing κ B hB ∈
      primitiveFullPairings q :=
    residualPrimitiveBlockPairing_mem κ B hB hprim
  have hbounds := (hprop lam ε q hq G hreg hG).2.2 z
  constructor
  · calc
      |primitivePairingKernelTerm ρ lam ε q hq G
          (residualPrimitiveBlockPairing κ B hB) z 0| =
          primitivePairingKernelTerm ρ lam ε q hq G
            (residualPrimitiveBlockPairing κ B hB) z 0 :=
        abs_of_nonneg
          (primitivePairingKernelTerm_nonneg
            ρ lam ε q hq G hGnonneg _ z 0)
      _ ≤ primitiveKernel ρ lam ε q hq G z 0 :=
        primitivePairingKernelTerm_le_kernel
          ρ lam ε q hq G hGnonneg _ hmem z 0
      _ ≤ |primitiveKernelDiff ρ lam ε q hq G z| :=
        le_abs_self _
      _ ≤ primitiveKernelMajorant C lam ε supportConstant q z :=
        hbounds.1
  · calc
      |primitivePairingKernelInsertedTerm ρ lam ε q hq G
          (residualPrimitiveBlockPairing κ B hB) z 0| =
          primitivePairingKernelInsertedTerm ρ lam ε q hq G
            (residualPrimitiveBlockPairing κ B hB) z 0 :=
        abs_of_nonneg
          (primitivePairingKernelInsertedTerm_nonneg
            ρ lam ε q hq G hGnonneg _ z 0)
      _ ≤ primitiveKernelInserted ρ lam ε q hq G z 0 :=
        primitivePairingKernelInsertedTerm_le_kernel
          ρ lam ε q hq G hGnonneg _ hmem z 0
      _ ≤ |primitiveKernelInsertedDiff ρ lam ε q hq G z| :=
        le_abs_self _
      _ ≤ primitiveInsertedMajorant C lam ε supportConstant q z :=
        hbounds.2

/-! ## Specialization to the canonical R-324 block list -/

/-- Extract the closure certificate for a particular block in the canonical
R-324 residual decomposition. -/
theorem momentResidualCollapseBlock_isFullyPairedOn_of_mem
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentResidualCollapseBlocks κp κm π) :
    IsFullyPairedOn (momentCombinedPairing κp κm π) B :=
  (List.forall_iff_forall_mem.mp
    (momentResidualCollapseBlocks_forall_isFullyPairedOn κp κm π)) B hB

/-- Extract the relative-primitivity certificate for a particular block in
the canonical R-324 residual decomposition. -/
theorem momentResidualCollapseBlock_isRelPrimitiveOn_of_mem
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentResidualCollapseBlocks κp κm π) :
    IsRelPrimitiveOn (momentCombinedPairing κp κm π) B :=
  (List.forall_iff_forall_mem.mp
    (momentResidualCollapseBlocks_forall_isRelPrimitiveOn κp κm π)) B hB

/-- Every concrete block in `momentResidualCollapseBlocks` has the ordinary
and inserted Proposition 4.1 term bounds after its canonical increasing
reindexing.

This is the direct analytic consumer of the coverage/fullness/primitivity
theorems in `ResidualCollapse.lean`.  In particular, no
`MomentFiberReductionData` or desired density domination is assumed. -/
theorem exists_momentResidualCollapseBlock_term_bounds
    (ρ : SmoothCutoff) :
    ∃ orderConstant supportConstant C : ℝ,
      0 < orderConstant ∧ 0 < supportConstant ∧ 0 < C ∧
      ∀ {m : ℕ} (κp κm : PartialPairing (Fin m))
        (π : κp.singles ≃ κm.singles)
        (B : Finset (Fin (2 * m)))
        (hmem : B ∈ momentResidualCollapseBlocks κp κm π),
        let hB := momentResidualCollapseBlock_isFullyPairedOn_of_mem
          κp κm π B hmem
        ∀ (lam ε : ℝ)
          (G : Fin (2 * residualBlockOrder B - 1) → T4 → ℝ),
          (hreg : PrimitiveEstimateRegime (residualBlockOrder B) lam ε
              orderConstant supportConstant C) →
          (hinput : IsAdmissiblePrimitiveInput (residualBlockOrder B) G) →
          (hnonneg : ∀ j z, 0 ≤ G j z) →
          ∀ z : T4,
            |primitivePairingKernelTerm ρ lam ε
                (residualBlockOrder B) hreg.1 G
                (residualPrimitiveBlockPairing
                  (momentCombinedPairing κp κm π) B hB) z 0| ≤
              primitiveKernelMajorant C lam ε supportConstant
                (residualBlockOrder B) z ∧
            |primitivePairingKernelInsertedTerm ρ lam ε
                (residualBlockOrder B) hreg.1 G
                (residualPrimitiveBlockPairing
                  (momentCombinedPairing κp κm π) B hB) z 0| ≤
              primitiveInsertedMajorant C lam ε supportConstant
                (residualBlockOrder B) z := by
  obtain ⟨orderConstant, supportConstant, C,
      horder, hsupport, hC, hbound⟩ :=
    exists_residualPrimitiveBlockPairing_term_bounds ρ
  refine
    ⟨orderConstant, supportConstant, C,
      horder, hsupport, hC, ?_⟩
  intro m κp κm π B hmem
  let hB := momentResidualCollapseBlock_isFullyPairedOn_of_mem
    κp κm π B hmem
  have hprim := momentResidualCollapseBlock_isRelPrimitiveOn_of_mem
    κp κm π B hmem
  exact hbound (momentCombinedPairing κp κm π) B hB hprim

end

end Anderson4D
