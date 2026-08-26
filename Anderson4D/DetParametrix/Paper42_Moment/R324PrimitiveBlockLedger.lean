import Anderson4D.DetParametrix.Paper42_Moment.R324CompleteBlockFactorization

/-!
# The complete primitive-block ledger for R-324

For one doubled contraction, paper Section 4.2 successively removes three
families of primitive blocks: the Definition 3.1 blocks in the left copy,
the corresponding blocks in the right copy, and the nested residual blocks
which cross the central cut.  This file packages the three families into a
single nonempty block list and proves the exact perturbative-order ledger.

The resulting list is the finite analytic schedule for the constructive
R-324 collapse.  Its block orders sum to exactly `m`; in particular no
pairing-count or unused coupling power is hidden in the schedule.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- All three canonical primitive-block families, before deleting
analytically vacuous empty residual shells. -/
def momentAllPrimitiveBlocks
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    List (Finset (Fin (2 * m))) :=
  momentLeftExtractionBlocks κp ++
    momentRightExtractionBlocks κm ++
      momentResidualCollapseBlocks κp κm π

/-- The actual R-324 analytic schedule.  Proposition 4.1 starts at order
one, so empty residual shells are removed. -/
def momentNonemptyPrimitiveBlocks
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    List (Finset (Fin (2 * m))) :=
  (momentAllPrimitiveBlocks κp κm π).filter
    fun B => B.Nonempty

@[simp]
theorem mem_momentAllPrimitiveBlocks
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {B : Finset (Fin (2 * m))} :
    B ∈ momentAllPrimitiveBlocks κp κm π ↔
      B ∈ momentLeftExtractionBlocks κp ∨
        B ∈ momentRightExtractionBlocks κm ∨
          B ∈ momentResidualCollapseBlocks κp κm π := by
  simp [momentAllPrimitiveBlocks]

@[simp]
theorem mem_momentNonemptyPrimitiveBlocks
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {B : Finset (Fin (2 * m))} :
    B ∈ momentNonemptyPrimitiveBlocks κp κm π ↔
      (B ∈ momentLeftExtractionBlocks κp ∨
        B ∈ momentRightExtractionBlocks κm ∨
          B ∈ momentResidualCollapseBlocks κp κm π) ∧
        B.Nonempty := by
  simp [momentNonemptyPrimitiveBlocks]

/-- A left extraction block lies in the complete left removed region. -/
theorem momentLeftExtractionBlock_subset_removed
    {m : ℕ} {κp : PartialPairing (Fin m)}
    {B : Finset (Fin (2 * m))}
    (hB : B ∈ momentLeftExtractionBlocks κp) :
    B ⊆ momentLeftRemoved κp := by
  intro x hx
  exact (mem_finsetUnionList_iff
    (momentLeftExtractionBlocks κp)).mpr
      ⟨B, hB, hx⟩

/-- A right extraction block lies in the complete right removed region. -/
theorem momentRightExtractionBlock_subset_removed
    {m : ℕ} {κm : PartialPairing (Fin m)}
    {B : Finset (Fin (2 * m))}
    (hB : B ∈ momentRightExtractionBlocks κm) :
    B ⊆ momentRightRemoved κm := by
  intro x hx
  exact (mem_finsetUnionList_iff
    (momentRightExtractionBlocks κm)).mpr
      ⟨B, hB, hx⟩

/-- A residual collapse block lies in the terminal doubled carrier. -/
theorem momentResidualCollapseBlock_subset_active
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {B : Finset (Fin (2 * m))}
    (hB : B ∈ momentResidualCollapseBlocks κp κm π) :
    B ⊆ momentResidualActive κp κm := by
  intro x hx
  rw [← finsetUnionList_momentResidualCollapseBlocks
    κp κm π]
  exact (mem_finsetUnionList_iff
    (momentResidualCollapseBlocks κp κm π)).mpr
      ⟨B, hB, hx⟩

/-- The three canonical block families are mutually disjoint as well as
internally pairwise disjoint. -/
theorem momentAllPrimitiveBlocks_pairwise_disjoint
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (momentAllPrimitiveBlocks κp κm π).Pairwise Disjoint := by
  rw [momentAllPrimitiveBlocks, List.pairwise_append,
    List.pairwise_append]
  refine ⟨⟨momentLeftExtractionBlocks_pairwise_disjoint κp,
      momentRightExtractionBlocks_pairwise_disjoint κm,
      ?_⟩, ?_, ?_⟩
  · intro B hB C hC
    exact Disjoint.mono
      (momentLeftExtractionBlock_subset_removed hB)
      (momentRightExtractionBlock_subset_removed hC)
      (momentLeftRemoved_disjoint_rightRemoved κp κm)
  · exact residualCollapseBlocks_pairwise_disjoint
      (momentResidualActive κp κm)
      (momentResidualIntervalChain κp κm π)
      (momentResidualIntervalChain_pairwise_laterContains
        κp κm π)
  · intro B hB C hC
    rcases List.mem_append.mp hB with hleft | hright
    · exact Disjoint.mono
        (momentLeftExtractionBlock_subset_removed hleft)
        (momentResidualCollapseBlock_subset_active hC)
        (momentLeftRemoved_disjoint_residual κp κm)
    · exact Disjoint.mono
        (momentRightExtractionBlock_subset_removed hright)
        (momentResidualCollapseBlock_subset_active hC)
        (momentRightRemoved_disjoint_residual κp κm)

theorem momentNonemptyPrimitiveBlocks_pairwise_disjoint
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (momentNonemptyPrimitiveBlocks κp κm π).Pairwise
      Disjoint := by
  exact
    (momentAllPrimitiveBlocks_pairwise_disjoint
      κp κm π).filter _

/-- `finsetUnionList` sends concatenation to finite-set union. -/
theorem finsetUnionList_append
    {α : Type*} [DecidableEq α]
    (left right : List (Finset α)) :
    finsetUnionList (left ++ right) =
      finsetUnionList left ∪ finsetUnionList right := by
  induction left with
  | nil =>
      simp [finsetUnionList]
  | cons B left ih =>
      simp only [List.cons_append, finsetUnionList, ih]
      exact
        (Finset.union_assoc B
          (finsetUnionList left)
          (finsetUnionList right)).symm

/-- The nonempty analytic schedule covers the entire doubled carrier. -/
theorem finsetUnionList_momentNonemptyPrimitiveBlocks
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    finsetUnionList
        (momentNonemptyPrimitiveBlocks κp κm π) =
      (Finset.univ : Finset (Fin (2 * m))) := by
  unfold momentNonemptyPrimitiveBlocks
  rw [finsetUnionList_filter_nonempty]
  unfold momentAllPrimitiveBlocks
  rw [finsetUnionList_append, finsetUnionList_append]
  change
    (momentLeftRemoved κp ∪ momentRightRemoved κm) ∪
        finsetUnionList
          (momentResidualCollapseBlocks κp κm π) =
      (Finset.univ : Finset (Fin (2 * m)))
  rw [finsetUnionList_momentResidualCollapseBlocks]
  exact momentRemoved_union_residual_eq_univ κp κm

/-- Every block in the complete list is closed and fully paired under the
doubled contraction pairing. -/
theorem momentAllPrimitiveBlocks_forall_isFullyPairedOn
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (momentAllPrimitiveBlocks κp κm π).Forall
      (IsFullyPairedOn
        (momentCombinedPairing κp κm π)) := by
  apply List.forall_iff_forall_mem.mpr
  intro B hB
  rcases mem_momentAllPrimitiveBlocks.mp hB with
    hleft | hright | hresidual
  · exact momentLeftExtractionBlock_isFullyPairedOn_of_mem
      κp κm π B hleft
  · exact momentRightExtractionBlock_isFullyPairedOn_of_mem
      κp κm π B hright
  · exact momentResidualCollapseBlock_isFullyPairedOn_of_mem
      κp κm π B hresidual

/-- Every block in the complete list is relatively primitive on its sparse
ordered carrier. -/
theorem momentAllPrimitiveBlocks_forall_isRelPrimitiveOn
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (momentAllPrimitiveBlocks κp κm π).Forall
      (IsRelPrimitiveOn
        (momentCombinedPairing κp κm π)) := by
  apply List.forall_iff_forall_mem.mpr
  intro B hB
  rcases mem_momentAllPrimitiveBlocks.mp hB with
    hleft | hright | hresidual
  · exact momentLeftExtractionBlock_isRelPrimitiveOn_of_mem
      κp κm π B hleft
  · exact momentRightExtractionBlock_isRelPrimitiveOn_of_mem
      κp κm π B hright
  · exact momentResidualCollapseBlock_isRelPrimitiveOn_of_mem
      κp κm π B hresidual

theorem momentNonemptyPrimitiveBlocks_forall_isFullyPairedOn
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (momentNonemptyPrimitiveBlocks κp κm π).Forall
      (IsFullyPairedOn
        (momentCombinedPairing κp κm π)) := by
  apply List.forall_iff_forall_mem.mpr
  intro B hB
  exact
    List.forall_iff_forall_mem.mp
      (momentAllPrimitiveBlocks_forall_isFullyPairedOn
        κp κm π) B
      (List.mem_of_mem_filter hB)

theorem momentNonemptyPrimitiveBlocks_forall_isRelPrimitiveOn
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (momentNonemptyPrimitiveBlocks κp κm π).Forall
      (IsRelPrimitiveOn
        (momentCombinedPairing κp κm π)) := by
  apply List.forall_iff_forall_mem.mpr
  intro B hB
  exact
    List.forall_iff_forall_mem.mp
      (momentAllPrimitiveBlocks_forall_isRelPrimitiveOn
        κp κm π) B
      (List.mem_of_mem_filter hB)

theorem momentNonemptyPrimitiveBlocks_forall_nonempty
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (momentNonemptyPrimitiveBlocks κp κm π).Forall
      Finset.Nonempty := by
  apply List.forall_iff_forall_mem.mpr
  intro B hB
  exact (mem_momentNonemptyPrimitiveBlocks.mp hB).2

/-- Every analytic block has positive primitive order. -/
theorem one_le_residualBlockOrder_of_mem_momentNonemptyPrimitiveBlocks
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentNonemptyPrimitiveBlocks κp κm π) :
    1 ≤ residualBlockOrder B := by
  exact one_le_residualBlockOrder_of_nonempty
    (momentCombinedPairing κp κm π) B
    ((List.forall_iff_forall_mem.mp
      (momentNonemptyPrimitiveBlocks_forall_isFullyPairedOn
        κp κm π)) B hB)
    ((List.forall_iff_forall_mem.mp
      (momentNonemptyPrimitiveBlocks_forall_nonempty
        κp κm π)) B hB)

/-- Removing empty blocks does not change the sum of half-cardinality
orders. -/
theorem sum_residualBlockOrder_filter_nonempty
    {n : ℕ} (blocks : List (Finset (Fin n))) :
    ((blocks.filter fun B => B.Nonempty).map
        residualBlockOrder).sum =
      (blocks.map residualBlockOrder).sum := by
  induction blocks with
  | nil =>
      simp
  | cons B blocks ih =>
      by_cases hB : B.Nonempty
      · rw [List.filter_cons_of_pos (by simpa)]
        simp only [List.map_cons, List.sum_cons, ih]
      · have hBempty : B = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hB
        rw [List.filter_cons_of_neg (by simpa)]
        simp [hBempty, residualBlockOrder, ih]

/-- The three block families account for every one of the `2m` covariance
variables. -/
theorem sum_card_momentAllPrimitiveBlocks
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    ((momentAllPrimitiveBlocks κp κm π).map
        Finset.card).sum =
      2 * m := by
  have hleft :
      ((momentLeftExtractionBlocks κp).map
          Finset.card).sum =
        (momentLeftRemoved κp).card :=
    (card_finsetUnionList_eq_sum_card
      (momentLeftExtractionBlocks κp)
      (momentLeftExtractionBlocks_pairwise_disjoint κp)).symm
  have hright :
      ((momentRightExtractionBlocks κm).map
          Finset.card).sum =
        (momentRightRemoved κm).card :=
    (card_finsetUnionList_eq_sum_card
      (momentRightExtractionBlocks κm)
      (momentRightExtractionBlocks_pairwise_disjoint κm)).symm
  have hresidual :
      ((momentResidualCollapseBlocks κp κm π).map
          Finset.card).sum =
        (momentResidualActive κp κm).card :=
    sum_card_momentResidualCollapseBlocks κp κm π
  have hleftRight :
      Disjoint (momentLeftRemoved κp)
        (momentRightRemoved κm) :=
    momentLeftRemoved_disjoint_rightRemoved κp κm
  have hremovedResidual :
      Disjoint
        (momentLeftRemoved κp ∪ momentRightRemoved κm)
        (momentResidualActive κp κm) :=
    Finset.disjoint_union_left.mpr
      ⟨momentLeftRemoved_disjoint_residual κp κm,
        momentRightRemoved_disjoint_residual κp κm⟩
  calc
    ((momentAllPrimitiveBlocks κp κm π).map
        Finset.card).sum =
        ((momentLeftExtractionBlocks κp).map
            Finset.card).sum +
          ((momentRightExtractionBlocks κm).map
            Finset.card).sum +
          ((momentResidualCollapseBlocks κp κm π).map
            Finset.card).sum := by
      simp [momentAllPrimitiveBlocks, add_assoc]
    _ = (momentLeftRemoved κp).card +
          (momentRightRemoved κm).card +
          (momentResidualActive κp κm).card := by
      rw [hleft, hright, hresidual]
    _ = (momentLeftRemoved κp ∪
          momentRightRemoved κm).card +
        (momentResidualActive κp κm).card := by
      rw [Finset.card_union_of_disjoint hleftRight]
    _ = ((momentLeftRemoved κp ∪
          momentRightRemoved κm) ∪
        momentResidualActive κp κm).card := by
      rw [Finset.card_union_of_disjoint hremovedResidual]
    _ = (Finset.univ :
          Finset (Fin (2 * m))).card := by
      rw [momentRemoved_union_residual_eq_univ]
    _ = 2 * m := by simp

/-- Exact coupling-power ledger for all blocks before removing empty
shells. -/
theorem two_mul_sum_momentAllPrimitiveBlockOrders
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    2 * ((momentAllPrimitiveBlocks κp κm π).map
        residualBlockOrder).sum =
      2 * m := by
  have heven :
      (momentAllPrimitiveBlocks κp κm π).Forall
        (fun B => Even B.card) :=
    (momentAllPrimitiveBlocks_forall_isFullyPairedOn
      κp κm π).imp fun B hB =>
        residualBlock_card_even
          (momentCombinedPairing κp κm π) B hB
  exact
    (two_mul_sum_residualBlockOrder_eq_sum_card
      (momentAllPrimitiveBlocks κp κm π) heven).trans
        (sum_card_momentAllPrimitiveBlocks κp κm π)

/-- Exact coupling-power ledger for the actual nonempty analytic schedule. -/
theorem two_mul_sum_momentNonemptyPrimitiveBlockOrders
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    2 * ((momentNonemptyPrimitiveBlocks κp κm π).map
        residualBlockOrder).sum =
      2 * m := by
  unfold momentNonemptyPrimitiveBlocks
  rw [sum_residualBlockOrder_filter_nonempty]
  exact two_mul_sum_momentAllPrimitiveBlockOrders κp κm π

/-- The half-cardinality orders themselves sum to the perturbative order
`m`. -/
theorem sum_momentNonemptyPrimitiveBlockOrders
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    ((momentNonemptyPrimitiveBlocks κp κm π).map
        residualBlockOrder).sum =
      m := by
  have h :=
    two_mul_sum_momentNonemptyPrimitiveBlockOrders
      κp κm π
  omega

private theorem List.le_sum_of_mem_nat
    {n : ℕ} {values : List ℕ}
    (hn : n ∈ values) :
    n ≤ values.sum := by
  induction values with
  | nil =>
      simp at hn
  | cons a values ih =>
      simp only [List.mem_cons] at hn
      simp only [List.sum_cons]
      rcases hn with rfl | hn
      · omega
      · have htail := ih hn
        omega

/-- Each block order is bounded by the total perturbative order. -/
theorem residualBlockOrder_le_of_mem_momentNonemptyPrimitiveBlocks
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentNonemptyPrimitiveBlocks κp κm π) :
    residualBlockOrder B ≤ m := by
  calc
    residualBlockOrder B ≤
        ((momentNonemptyPrimitiveBlocks κp κm π).map
          residualBlockOrder).sum := by
      apply List.le_sum_of_mem_nat
      exact List.mem_map.mpr ⟨B, hB, rfl⟩
    _ = m :=
      sum_momentNonemptyPrimitiveBlockOrders κp κm π

/-- Consequently a global truncation assumption licenses Proposition 4.1
on every block in the concrete R-324 schedule. -/
theorem residualBlockOrder_le_truncOrder_of_mem
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentNonemptyPrimitiveBlocks κp κm π)
    (ε : ℝ) (hm : m ≤ truncOrder ε) :
    residualBlockOrder B ≤ truncOrder ε :=
  (residualBlockOrder_le_of_mem_momentNonemptyPrimitiveBlocks
    κp κm π B hB).trans hm

/-- The complete covariance product is the product over the unified
nonempty primitive schedule. -/
theorem
    primitiveCovarianceProduct_momentCombinedPairing_eq_prod_primitiveBlocks
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) :
    primitiveCovarianceProduct ρ ε m
        (momentCombinedPairing κp κm π) v =
      ((momentNonemptyPrimitiveBlocks κp κm π).map fun B =>
        pairingCovarianceProductOn ρ ε
          (momentCombinedPairing κp κm π) B v).prod := by
  unfold momentNonemptyPrimitiveBlocks
  rw [prod_pairingCovarianceProductOn_filter_nonempty]
  simp only [momentAllPrimitiveBlocks, List.map_append,
    List.prod_append]
  exact
    primitiveCovarianceProduct_momentCombinedPairing_eq_prod_all_blocks
      ρ ε m κp κm π v

end

end Anderson4D
