import Anderson4D.DetParametrix.Paper42_Moment.R324SelectedCellDecomposition
import Anderson4D.DetParametrix.Core.ResidualPrimitiveRouting

/-!
# The open word on the marked R-324 primitive block

The genuine selected cell word is indexed on the full doubled moment.
Only the unique residual primitive block containing the selected cross
edge enters the R-324 high-frequency permutation estimate.  This file
restricts the full word along the canonical increasing enumeration of
that block.

The restricted pairing is full and primitive, the selected endpoints
remain a genuine ordered pairing edge, and every other edge still has
equal cell labels.  No multiplicity lower bound is imposed on the input
word: singleton endpoint labels are allowed before dummy augmentation.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-! ## Canonical marked-block data -/

/-- Closedness of the unique marked residual block. -/
theorem r324MarkedResidualBlock_isFullyPairedOn
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    IsFullyPairedOn
      (momentCombinedPairing κp κm π)
      (r324MarkedResidualBlock κp κm π selected) := by
  exact
    momentResidualCollapseBlock_isFullyPairedOn_of_mem
      κp κm π
      (r324MarkedResidualBlock κp κm π selected)
      ((mem_nonemptyMomentResidualCollapseBlocks.mp
        (r324MarkedResidualBlock_mem
          κp κm π selected)).1)

/-- Relative primitivity of the unique marked residual block. -/
theorem r324MarkedResidualBlock_isRelPrimitiveOn
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    IsRelPrimitiveOn
      (momentCombinedPairing κp κm π)
      (r324MarkedResidualBlock κp κm π selected) := by
  exact
    momentResidualCollapseBlock_isRelPrimitiveOn_of_mem
      κp κm π
      (r324MarkedResidualBlock κp κm π selected)
      ((mem_nonemptyMomentResidualCollapseBlocks.mp
        (r324MarkedResidualBlock_mem
          κp κm π selected)).1)

/-- Position of the selected lower endpoint in the canonical increasing
enumeration of the marked residual block. -/
def r324MarkedResidualLowerPosition
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    Fin
      (2 * residualBlockOrder
        (r324MarkedResidualBlock κp κm π selected)) :=
  (residualPrimitiveBlockOrderIso
      (momentCombinedPairing κp κm π)
      (r324MarkedResidualBlock κp κm π selected)
      (r324MarkedResidualBlock_isFullyPairedOn
        κp κm π selected)).symm
    ⟨r324ResidualMarkedLowerEndpoint selected,
      r324ResidualMarkedLowerEndpoint_mem_markedBlock
        κp κm π selected⟩

/-- Position of the selected upper endpoint in the canonical increasing
enumeration of the marked residual block. -/
def r324MarkedResidualUpperPosition
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    Fin
      (2 * residualBlockOrder
        (r324MarkedResidualBlock κp κm π selected)) :=
  (residualPrimitiveBlockOrderIso
      (momentCombinedPairing κp κm π)
      (r324MarkedResidualBlock κp κm π selected)
      (r324MarkedResidualBlock_isFullyPairedOn
        κp κm π selected)).symm
    ⟨r324ResidualMarkedUpperEndpoint π selected,
      r324ResidualMarkedUpperEndpoint_mem_markedBlock
        κp κm π selected⟩

@[simp]
theorem r324MarkedResidualBlockOrderIso_lower
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    ((residualPrimitiveBlockOrderIso
        (momentCombinedPairing κp κm π)
        (r324MarkedResidualBlock κp κm π selected)
        (r324MarkedResidualBlock_isFullyPairedOn
          κp κm π selected))
      (r324MarkedResidualLowerPosition
        κp κm π selected)).1 =
      r324ResidualMarkedLowerEndpoint selected := by
  exact congrArg Subtype.val
    ((residualPrimitiveBlockOrderIso
        (momentCombinedPairing κp κm π)
        (r324MarkedResidualBlock κp κm π selected)
        (r324MarkedResidualBlock_isFullyPairedOn
          κp κm π selected)).apply_symm_apply
      ⟨r324ResidualMarkedLowerEndpoint selected,
        r324ResidualMarkedLowerEndpoint_mem_markedBlock
          κp κm π selected⟩)

@[simp]
theorem r324MarkedResidualBlockOrderIso_upper
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    ((residualPrimitiveBlockOrderIso
        (momentCombinedPairing κp κm π)
        (r324MarkedResidualBlock κp κm π selected)
        (r324MarkedResidualBlock_isFullyPairedOn
          κp κm π selected))
      (r324MarkedResidualUpperPosition
        κp κm π selected)).1 =
      r324ResidualMarkedUpperEndpoint π selected := by
  exact congrArg Subtype.val
    ((residualPrimitiveBlockOrderIso
        (momentCombinedPairing κp κm π)
        (r324MarkedResidualBlock κp κm π selected)
        (r324MarkedResidualBlock_isFullyPairedOn
          κp κm π selected)).apply_symm_apply
      ⟨r324ResidualMarkedUpperEndpoint π selected,
        r324ResidualMarkedUpperEndpoint_mem_markedBlock
          κp κm π selected⟩)

/-- The selected endpoints remain a genuine edge after canonical
restriction to the marked primitive block. -/
theorem r324MarkedResidualBlockPairing_lower
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    residualPrimitiveBlockPairing
        (momentCombinedPairing κp κm π)
        (r324MarkedResidualBlock κp κm π selected)
        (r324MarkedResidualBlock_isFullyPairedOn
          κp κm π selected)
        (r324MarkedResidualLowerPosition
          κp κm π selected) =
      r324MarkedResidualUpperPosition
        κp κm π selected := by
  let e :=
    residualPrimitiveBlockOrderIso
      (momentCombinedPairing κp κm π)
      (r324MarkedResidualBlock κp κm π selected)
      (r324MarkedResidualBlock_isFullyPairedOn
        κp κm π selected)
  have happly :
      (e
        (residualPrimitiveBlockPairing
          (momentCombinedPairing κp κm π)
          (r324MarkedResidualBlock κp κm π selected)
          (r324MarkedResidualBlock_isFullyPairedOn
            κp κm π selected)
          (r324MarkedResidualLowerPosition
            κp κm π selected))).1 =
        momentCombinedPairing κp κm π
          (e
            (r324MarkedResidualLowerPosition
              κp κm π selected)).1 := by
    exact
      orderedBlockPairing_apply
        (momentCombinedPairing κp κm π)
        (r324MarkedResidualBlock κp κm π selected)
        (r324MarkedResidualBlock_isFullyPairedOn
          κp κm π selected)
        e
        (r324MarkedResidualLowerPosition
          κp κm π selected)
  apply e.injective
  apply Subtype.ext
  rw [happly,
    r324MarkedResidualBlockOrderIso_lower,
    momentCombinedPairing_r324ResidualMarkedLowerEndpoint,
    r324MarkedResidualBlockOrderIso_upper]

/-- The selected edge remains ordered after increasing reindexing. -/
theorem r324MarkedResidualLowerPosition_lt_upper
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    r324MarkedResidualLowerPosition κp κm π selected <
      r324MarkedResidualUpperPosition κp κm π selected := by
  let e :=
    residualPrimitiveBlockOrderIso
      (momentCombinedPairing κp κm π)
      (r324MarkedResidualBlock κp κm π selected)
      (r324MarkedResidualBlock_isFullyPairedOn
        κp κm π selected)
  have hElower :
      (e
        (r324MarkedResidualLowerPosition
          κp κm π selected)).1 =
        r324ResidualMarkedLowerEndpoint selected := by
    exact r324MarkedResidualBlockOrderIso_lower
      κp κm π selected
  have hEupper :
      (e
        (r324MarkedResidualUpperPosition
          κp κm π selected)).1 =
        r324ResidualMarkedUpperEndpoint π selected := by
    exact r324MarkedResidualBlockOrderIso_upper
      κp κm π selected
  apply e.lt_iff_lt.mp
  change
    (e
      (r324MarkedResidualLowerPosition
        κp κm π selected)).1 <
      (e
        (r324MarkedResidualUpperPosition
          κp κm π selected)).1
  rw [hElower, hEupper]
  exact
    r324ResidualMarkedLowerEndpoint_lt_upper
      κp κm π selected

/-- Restrict an ambient doubled-moment cell word to the unique marked
primitive block in canonical increasing order. -/
def r324MarkedResidualBlockWord
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (y : Fin (2 * m) → Z4) :
    Fin
      (2 * residualBlockOrder
        (r324MarkedResidualBlock κp κm π selected)) → Z4 :=
  fun i =>
    y
      ((residualPrimitiveBlockOrderIso
          (momentCombinedPairing κp κm π)
          (r324MarkedResidualBlock κp κm π selected)
          (r324MarkedResidualBlock_isFullyPairedOn
            κp κm π selected)) i).1

/-! ## Transport of the open-edge constraint -/

/-- Restricting an ambient open-edge word to the marked primitive block
preserves the equality on every unmarked local pairing edge. -/
theorem r324MarkedResidualBlockWord_respectsExcept
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (y : Fin (2 * m) → Z4)
    (hy :
      RespectsPairingExcept
        (momentCombinedPairing κp κm π)
        (r324ResidualMarkedLowerEndpoint selected)
        (r324ResidualMarkedUpperEndpoint π selected)
        y) :
    RespectsPairingExcept
      (residualPrimitiveBlockPairing
        (momentCombinedPairing κp κm π)
        (r324MarkedResidualBlock κp κm π selected)
        (r324MarkedResidualBlock_isFullyPairedOn
          κp κm π selected))
      (r324MarkedResidualLowerPosition κp κm π selected)
      (r324MarkedResidualUpperPosition κp κm π selected)
      (r324MarkedResidualBlockWord
        κp κm π selected y) := by
  intro i hia hib
  let e :=
    residualPrimitiveBlockOrderIso
      (momentCombinedPairing κp κm π)
      (r324MarkedResidualBlock κp κm π selected)
      (r324MarkedResidualBlock_isFullyPairedOn
        κp κm π selected)
  have hElower :
      (e
        (r324MarkedResidualLowerPosition
          κp κm π selected)).1 =
        r324ResidualMarkedLowerEndpoint selected := by
    exact r324MarkedResidualBlockOrderIso_lower
      κp κm π selected
  have hEupper :
      (e
        (r324MarkedResidualUpperPosition
          κp κm π selected)).1 =
        r324ResidualMarkedUpperEndpoint π selected := by
    exact r324MarkedResidualBlockOrderIso_upper
      κp κm π selected
  have hambientA :
      (e i).1 ≠ r324ResidualMarkedLowerEndpoint selected := by
    intro h
    apply hia
    apply e.injective
    apply Subtype.ext
    exact h.trans hElower.symm
  have hambientB :
      (e i).1 ≠ r324ResidualMarkedUpperEndpoint π selected := by
    intro h
    apply hib
    apply e.injective
    apply Subtype.ext
    exact h.trans hEupper.symm
  have happly :
      (e
        (residualPrimitiveBlockPairing
          (momentCombinedPairing κp κm π)
          (r324MarkedResidualBlock κp κm π selected)
          (r324MarkedResidualBlock_isFullyPairedOn
            κp κm π selected) i)).1 =
        momentCombinedPairing κp κm π (e i).1 := by
    exact
      orderedBlockPairing_apply
        (momentCombinedPairing κp κm π)
        (r324MarkedResidualBlock κp κm π selected)
        (r324MarkedResidualBlock_isFullyPairedOn
          κp κm π selected)
        e i
  change
    y
        (e
          (residualPrimitiveBlockPairing
            (momentCombinedPairing κp κm π)
            (r324MarkedResidualBlock κp κm π selected)
            (r324MarkedResidualBlock_isFullyPairedOn
              κp κm π selected) i)).1 =
      y (e i).1
  rw [happly]
  exact hy (e i).1 hambientA hambientB

/-- The marked block pairing belongs to the exact primitive full-pairing
fibre required by the permutation estimate. -/
theorem r324MarkedResidualBlockPairing_mem_primitiveFullPairings
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    residualPrimitiveBlockPairing
        (momentCombinedPairing κp κm π)
        (r324MarkedResidualBlock κp κm π selected)
        (r324MarkedResidualBlock_isFullyPairedOn
          κp κm π selected) ∈
      primitiveFullPairings
        (residualBlockOrder
          (r324MarkedResidualBlock κp κm π selected)) := by
  exact
    residualPrimitiveBlockPairing_mem
      (momentCombinedPairing κp κm π)
      (r324MarkedResidualBlock κp κm π selected)
      (r324MarkedResidualBlock_isFullyPairedOn
        κp κm π selected)
      (r324MarkedResidualBlock_isRelPrimitiveOn
        κp κm π selected)

end

end Anderson4D
