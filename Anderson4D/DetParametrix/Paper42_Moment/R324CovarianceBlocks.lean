import Anderson4D.DetParametrix.Paper42_Moment.R324BlockCollapse
import Anderson4D.DetParametrix.Core.ResidualPrimitiveRouting

/-!
# Covariance-product decomposition over R-324 collapse blocks

The successive primitive reductions in paper §4.2 use pairwise-disjoint
closed blocks.  This file provides the exact algebraic bridge between the
ambient doubled covariance product and the standard, increasingly reindexed
primitive covariance product on each block.

No estimate is used here: all statements are finite-product identities.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- The covariance product whose lower endpoints lie in an ambient block.
The strict inequality already excludes fixed points, so no separate
`pairSupport` filter is needed. -/
def pairingCovarianceProductOn
    {n : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin n)) (B : Finset (Fin n))
    (v : Fin n → T4) : ℝ :=
  ∏ i ∈ B.filter (fun i => i < κ i),
    ρ.etaEpsT4 ε (v i - v (κ i))

theorem pairingCovarianceProductOn_empty
    {n : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin n)) (v : Fin n → T4) :
    pairingCovarianceProductOn ρ ε κ ∅ v = 1 := by
  simp [pairingCovarianceProductOn]

/-- A covariance product over a disjoint union is the product of the two
block products. -/
theorem pairingCovarianceProductOn_union
    {n : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin n))
    (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (v : Fin n → T4) :
    pairingCovarianceProductOn ρ ε κ (A ∪ B) v =
      pairingCovarianceProductOn ρ ε κ A v *
        pairingCovarianceProductOn ρ ε κ B v := by
  have hfilter :
      (A ∪ B).filter (fun i => i < κ i) =
        A.filter (fun i => i < κ i) ∪
          B.filter (fun i => i < κ i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  have hdisjoint :
      Disjoint
        (A.filter (fun i => i < κ i))
        (B.filter (fun i => i < κ i)) := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    exact
      (Finset.disjoint_left.mp hAB)
        (Finset.mem_filter.mp hiA).1
        (Finset.mem_filter.mp hiB).1
  unfold pairingCovarianceProductOn
  rw [hfilter, Finset.prod_union hdisjoint]

/-- A block disjoint from every member of a list is disjoint from their
finite union. -/
theorem disjoint_finsetUnionList_of_forall_mem
    {α : Type*} [DecidableEq α]
    (A : Finset α) (blocks : List (Finset α))
    (hA : ∀ B ∈ blocks, Disjoint A B) :
    Disjoint A (finsetUnionList blocks) := by
  rw [Finset.disjoint_left]
  intro x hxA hxUnion
  obtain ⟨B, hB, hxB⟩ :=
    (mem_finsetUnionList_iff blocks).mp hxUnion
  exact (Finset.disjoint_left.mp (hA B hB)) hxA hxB

/-- Exact multiplicative decomposition over a pairwise-disjoint block
list. -/
theorem pairingCovarianceProductOn_finsetUnionList
    {n : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin n))
    (blocks : List (Finset (Fin n)))
    (hblocks : blocks.Pairwise Disjoint)
    (v : Fin n → T4) :
    pairingCovarianceProductOn ρ ε κ
        (finsetUnionList blocks) v =
      (blocks.map fun B =>
        pairingCovarianceProductOn ρ ε κ B v).prod := by
  induction blocks with
  | nil =>
      exact pairingCovarianceProductOn_empty ρ ε κ v
  | cons A blocks ih =>
      have hpair := List.pairwise_cons.mp hblocks
      rw [finsetUnionList, List.map_cons, List.prod_cons,
        pairingCovarianceProductOn_union]
      · rw [ih hpair.2]
      · exact disjoint_finsetUnionList_of_forall_mem
          A blocks hpair.1

/-- On the whole carrier, the block product is exactly the covariance
product used in Proposition 4.1. -/
theorem pairingCovarianceProductOn_univ
    (ρ : SmoothCutoff) (ε : ℝ) (q : ℕ)
    (κ : PartialPairing (Fin (2 * q)))
    (v : Fin (2 * q) → T4) :
    pairingCovarianceProductOn ρ ε κ Finset.univ v =
      primitiveCovarianceProduct ρ ε q κ v := by
  unfold pairingCovarianceProductOn primitiveCovarianceProduct
  apply Finset.prod_congr
  · ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      PartialPairing.mem_pairSupport]
    constructor
    · intro hi
      exact ⟨ne_of_gt hi, hi⟩
    · exact fun hi => hi.2
  · intro i _hi
    rfl

/-- Restricting a covariance product to a certified closed block and
increasingly reindexing that block gives the standard primitive covariance
product at the exact half-cardinality order. -/
theorem pairingCovarianceProductOn_eq_residualPrimitiveBlock
    {n : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin n))
    (B : Finset (Fin n)) (hB : IsFullyPairedOn κ B)
    (v : Fin n → T4) :
    pairingCovarianceProductOn ρ ε κ B v =
      primitiveCovarianceProduct ρ ε (residualBlockOrder B)
        (residualPrimitiveBlockPairing κ B hB)
        (fun i =>
          v ((residualPrimitiveBlockOrderIso κ B hB i).1)) := by
  let e := residualPrimitiveBlockOrderIso κ B hB
  let κB := residualPrimitiveBlockPairing κ B hB
  have hfull : κB.IsFull :=
    orderedBlockPairing_isFull κ B hB e
  have hκB_apply (i : Fin (2 * residualBlockOrder B)) :
      (e (κB i)).1 = κ (e i).1 := by
    exact orderedBlockPairing_apply κ B hB e i
  unfold pairingCovarianceProductOn primitiveCovarianceProduct
  have hsource :
      κB.pairSupport.filter (fun i => i < κB i) =
        Finset.univ.filter (fun i => i < κB i) := by
    rw [PartialPairing.isFull_iff_pairSupport_eq_univ.mp hfull]
  rw [hsource]
  symm
  apply Finset.prod_bij
      (fun i _hi => (e i).1)
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨(e i).2, ?_⟩
    rw [← hκB_apply i]
    exact e.lt_iff_lt.mpr hi.2
  · intro i₁ _hi₁ i₂ _hi₂ hii
    exact e.injective (Subtype.ext hii)
  · intro b hb
    rw [Finset.mem_filter] at hb
    let bB : B := ⟨b, hb.1⟩
    let i : Fin (2 * residualBlockOrder B) := e.symm bB
    have hei : e i = bB := e.apply_symm_apply bB
    refine ⟨i, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ i, ?_⟩
      apply e.lt_iff_lt.mp
      change (e i).1 < (e (κB i)).1
      rw [hκB_apply, hei]
      exact hb.2
    · exact congrArg Subtype.val hei
  · intro i hi
    congr 2
    change v (e (κB i)).1 = v (κ (e i).1)
    rw [hκB_apply]

/-- The residual doubled covariance product is exactly the product of its
canonical R-324 residual block factors.  Each factor is identified with a
standard primitive covariance product by
`pairingCovarianceProductOn_eq_residualPrimitiveBlock`. -/
theorem pairingCovarianceProductOn_momentResidualActive_eq_prod_blocks
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) :
    pairingCovarianceProductOn ρ ε
        (momentCombinedPairing κp κm π)
        (momentResidualActive κp κm) v =
      ((momentResidualCollapseBlocks κp κm π).map fun B =>
        pairingCovarianceProductOn ρ ε
          (momentCombinedPairing κp κm π) B v).prod := by
  rw [← finsetUnionList_momentResidualCollapseBlocks κp κm π]
  exact pairingCovarianceProductOn_finsetUnionList
    ρ ε (momentCombinedPairing κp κm π)
      (momentResidualCollapseBlocks κp κm π)
      (residualCollapseBlocks_pairwise_disjoint
        (momentResidualActive κp κm)
        (momentResidualIntervalChain κp κm π)
        (momentResidualIntervalChain_pairwise_laterContains
          κp κm π))
      v

/-! ## Removing analytically vacuous empty residual blocks -/

/-- Empty shells contribute the multiplicative identity and must not be
sent to Proposition 4.1, whose primitive order starts at one. -/
def nonemptyMomentResidualCollapseBlocks
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    List (Finset (Fin (2 * m))) :=
  (momentResidualCollapseBlocks κp κm π).filter
    fun B => B.Nonempty

@[simp]
theorem mem_nonemptyMomentResidualCollapseBlocks
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {B : Finset (Fin (2 * m))} :
    B ∈ nonemptyMomentResidualCollapseBlocks κp κm π ↔
      B ∈ momentResidualCollapseBlocks κp κm π ∧
        B.Nonempty := by
  simp [nonemptyMomentResidualCollapseBlocks]

/-- Filtering empty blocks does not change their union. -/
theorem finsetUnionList_filter_nonempty
    {α : Type*} [DecidableEq α]
    (blocks : List (Finset α)) :
    finsetUnionList (blocks.filter fun B => B.Nonempty) =
      finsetUnionList blocks := by
  induction blocks with
  | nil =>
      simp [finsetUnionList]
  | cons B blocks ih =>
      by_cases hB : B.Nonempty
      · rw [List.filter_cons_of_pos (by simp [hB])]
        simp only [finsetUnionList, ih]
      · have hBempty : B = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hB
        rw [List.filter_cons_of_neg (by simp [hB])]
        simp only [finsetUnionList, hBempty,
          Finset.empty_union, ih]

/-- Filtering empty blocks does not change their covariance-product
factorization. -/
theorem prod_pairingCovarianceProductOn_filter_nonempty
    {n : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin n))
    (blocks : List (Finset (Fin n)))
    (v : Fin n → T4) :
    ((blocks.filter fun B => B.Nonempty).map fun B =>
        pairingCovarianceProductOn ρ ε κ B v).prod =
      (blocks.map fun B =>
        pairingCovarianceProductOn ρ ε κ B v).prod := by
  induction blocks with
  | nil =>
      simp
  | cons B blocks ih =>
      by_cases hB : B.Nonempty
      · rw [List.filter_cons_of_pos (by simp [hB])]
        simp only [List.map_cons, List.prod_cons, ih]
      · have hBempty : B = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hB
        rw [List.filter_cons_of_neg (by simp [hB])]
        simp only [List.map_cons, List.prod_cons, hBempty,
          pairingCovarianceProductOn_empty, one_mul, ih]

theorem nonemptyMomentResidualCollapseBlocks_pairwise_disjoint
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (nonemptyMomentResidualCollapseBlocks κp κm π).Pairwise
      Disjoint := by
  exact
    (residualCollapseBlocks_pairwise_disjoint
      (momentResidualActive κp κm)
      (momentResidualIntervalChain κp κm π)
      (momentResidualIntervalChain_pairwise_laterContains
        κp κm π)).filter _

theorem
    pairingCovarianceProductOn_momentResidualActive_eq_prod_nonemptyBlocks
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) :
    pairingCovarianceProductOn ρ ε
        (momentCombinedPairing κp κm π)
        (momentResidualActive κp κm) v =
      ((nonemptyMomentResidualCollapseBlocks κp κm π).map fun B =>
        pairingCovarianceProductOn ρ ε
          (momentCombinedPairing κp κm π) B v).prod := by
  rw [
    pairingCovarianceProductOn_momentResidualActive_eq_prod_blocks]
  exact
    (prod_pairingCovarianceProductOn_filter_nonempty
      ρ ε (momentCombinedPairing κp κm π)
      (momentResidualCollapseBlocks κp κm π) v).symm

/-- Every nonempty fully-paired block has positive half-cardinality order,
as required by Proposition 4.1. -/
theorem one_le_residualBlockOrder_of_nonempty
    {n : ℕ} (κ : PartialPairing (Fin n))
    (B : Finset (Fin n)) (hB : IsFullyPairedOn κ B)
    (hne : B.Nonempty) :
    1 ≤ residualBlockOrder B := by
  have heven : Even B.card :=
    residualBlock_card_even κ B hB
  have hcardPos : 0 < B.card :=
    Finset.card_pos.mpr hne
  unfold residualBlockOrder
  obtain ⟨q, hq⟩ := heven
  omega

theorem one_le_residualBlockOrder_of_mem_nonemptyMomentResidual
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ nonemptyMomentResidualCollapseBlocks κp κm π) :
    1 ≤ residualBlockOrder B := by
  have hmem :=
    (mem_nonemptyMomentResidualCollapseBlocks.mp hB).1
  have hne :=
    (mem_nonemptyMomentResidualCollapseBlocks.mp hB).2
  exact one_le_residualBlockOrder_of_nonempty
    (momentCombinedPairing κp κm π) B
    (momentResidualCollapseBlock_isFullyPairedOn_of_mem
      κp κm π B hmem)
    hne

end

end Anderson4D
