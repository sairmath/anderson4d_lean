import Anderson4D.DetParametrix.Core.PrimitiveBlockPartition
import Anderson4D.DetParametrix.Paper42_Moment.R324PrimitiveBlockLedger

/-!
# The R-324 schedule as a complete primitive partition

This file is the thin interface between the concrete left/right/residual
schedule of paper Section 4.2 and the generic multiplicity-free block-product
engine.  All five hypotheses of that engine are discharged by the concrete
R-324 ledger.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- The complete R-324 primitive schedule, packaged for generic exact
block-coordinate reindexing. -/
def momentPrimitiveBlockPartition
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    PrimitiveBlockPartition
      (momentCombinedPairing κp κm π) where
  blocks := momentNonemptyPrimitiveBlocks κp κm π
  pairwise_disjoint :=
    momentNonemptyPrimitiveBlocks_pairwise_disjoint κp κm π
  cover :=
    finsetUnionList_momentNonemptyPrimitiveBlocks κp κm π
  nonempty :=
    momentNonemptyPrimitiveBlocks_forall_nonempty κp κm π
  fullyPaired :=
    momentNonemptyPrimitiveBlocks_forall_isFullyPairedOn κp κm π
  primitive :=
    momentNonemptyPrimitiveBlocks_forall_isRelPrimitiveOn κp κm π

@[simp]
theorem momentPrimitiveBlockPartition_blocks
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (momentPrimitiveBlockPartition κp κm π).blocks =
      momentNonemptyPrimitiveBlocks κp κm π :=
  rfl

/-- The generic order ledger specializes to the exact perturbative order
`m`, rather than merely an upper bound. -/
theorem momentPrimitiveBlockPartition_sum_orders
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    ((momentPrimitiveBlockPartition κp κm π).blocks.map
        residualBlockOrder).sum = m := by
  simpa only [momentPrimitiveBlockPartition_blocks] using
    sum_momentNonemptyPrimitiveBlockOrders κp κm π

/-- Every block in the packaged R-324 partition is licensed at the global
truncation order. -/
theorem momentPrimitiveBlockPartition_order_le_truncOrder
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    {B : Finset (Fin (2 * m))}
    (hB : B ∈ (momentPrimitiveBlockPartition κp κm π).blocks)
    (ε : ℝ) (hm : m ≤ truncOrder ε) :
    residualBlockOrder B ≤ truncOrder ε := by
  exact residualBlockOrder_le_truncOrder_of_mem
    κp κm π B hB ε hm

end

end Anderson4D
