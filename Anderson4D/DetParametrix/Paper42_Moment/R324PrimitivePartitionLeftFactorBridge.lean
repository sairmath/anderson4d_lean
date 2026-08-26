import Anderson4D.DetParametrix.Paper42_Moment.R324PrimitivePartitionRightFactorBridge

/-!
# Left-block compatibility for the R-324 primitive partition

The left family in the doubled primitive partition is obtained by applying
`leftMomentIndex` to the ordinary extraction blocks of the first half.
This file proves that the canonical increasing enumeration is transported
by that embedding and consequently that the complete ambient block sum is
literally the existing R-322 extraction-block sum.

Everything remains signed and pointwise: no norm or integration is taken.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

/-! ## Canonical order transport -/

@[simp]
theorem r324LeftBlockOrder_image
    {m : ℕ} (B : Finset (Fin m)) :
    residualBlockOrder (B.image leftMomentIndex) =
      residualBlockOrder B := by
  unfold residualBlockOrder
  rw [Finset.card_image_of_injective _
    leftMomentIndex_injective]

/-- The canonical increasing enumeration of an extraction block commutes
with the order-preserving embedding into the left doubled copy. -/
theorem r324LeftBlockOrderIso_transport
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : ExtractionBlockIndex κp)
    (himage :
      IsFullyPairedOn
        (momentCombinedPairing κp κm π)
        (B.1.image leftMomentIndex))
    (j :
      Fin (2 * residualBlockOrder
        (B.1.image leftMomentIndex))) :
    (residualPrimitiveBlockOrderIso
        (momentCombinedPairing κp κm π)
        (B.1.image leftMomentIndex) himage j).1 =
      leftMomentIndex
        ((residualPrimitiveBlockOrderIso
          κp B.1
          (extractionBlock_isFullyPairedOn_of_mem
            κp B.1 B.2)
          ((Fin.castOrderIso
            (congrArg (fun n : ℕ => 2 * n)
              (r324LeftBlockOrder_image B.1))) j)).1) := by
  let horder :
      residualBlockOrder (B.1.image leftMomentIndex) =
        residualBlockOrder B.1 :=
    r324LeftBlockOrder_image B.1
  let f :
      Fin (2 * residualBlockOrder
        (B.1.image leftMomentIndex)) →
        Fin (2 * m) :=
    fun i =>
      leftMomentIndex
        ((residualPrimitiveBlockOrderIso
          κp B.1
          (extractionBlock_isFullyPairedOn_of_mem
            κp B.1 B.2)
          ((Fin.castOrderIso
            (congrArg (fun n : ℕ => 2 * n) horder)) i)).1)
  have hfmem :
      ∀ i, f i ∈ B.1.image leftMomentIndex := by
    intro i
    exact Finset.mem_image.mpr
      ⟨(residualPrimitiveBlockOrderIso
          κp B.1
          (extractionBlock_isFullyPairedOn_of_mem
            κp B.1 B.2)
          ((Fin.castOrderIso
            (congrArg (fun n : ℕ => 2 * n) horder)) i)).1,
        (residualPrimitiveBlockOrderIso
          κp B.1
          (extractionBlock_isFullyPairedOn_of_mem
            κp B.1 B.2)
          ((Fin.castOrderIso
            (congrArg (fun n : ℕ => 2 * n) horder)) i)).2,
        rfl⟩
  have hfmono : StrictMono f := by
    intro i k hik
    rw [leftMomentIndex_lt_leftMomentIndex_iff]
    exact
      (residualPrimitiveBlockOrderIso
        κp B.1
        (extractionBlock_isFullyPairedOn_of_mem
          κp B.1 B.2)).strictMono
        ((Fin.castOrderIso
          (congrArg (fun n : ℕ => 2 * n) horder)).strictMono hik)
  let hcard :
      (B.1.image leftMomentIndex).card =
        2 * residualBlockOrder
          (B.1.image leftMomentIndex) :=
    (Nat.two_mul_div_two_of_even
      (residualBlock_card_even
        (momentCombinedPairing κp κm π)
        (B.1.image leftMomentIndex) himage)).symm
  have henum :
      f =
        (B.1.image leftMomentIndex).orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard hfmem hfmono
  change
    (((B.1.image leftMomentIndex).orderIsoOfFin _ j :
      B.1.image leftMomentIndex).1) = f j
  rw [Finset.coe_orderIsoOfFin_apply]
  exact (congrFun henum j).symm

/-! ## Exact complete-sum compatibility -/

/-- Every ordinary left extraction block is a block of the concrete
doubled primitive partition. -/
theorem r324LeftExtractionBlock_mem_primitivePartition
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : ExtractionBlockIndex κp) :
    B.1.image leftMomentIndex ∈
      (momentPrimitiveBlockPartition κp κm π).blocks := by
  rw [momentPrimitiveBlockPartition_blocks,
    mem_momentNonemptyPrimitiveBlocks]
  constructor
  · left
    exact List.mem_map.mpr ⟨B.1, B.2, rfl⟩
  · have hne : B.1.Nonempty :=
      List.forall_iff_forall_mem.mp
        (extractionBlocks_forall_nonempty κp)
        B.1 B.2
    obtain ⟨i, hi⟩ := hne
    exact
      ⟨leftMomentIndex i,
        Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩

/-- Proof-only transport between the complete primitive-coordinate types
of a left image block and its original extraction block. -/
def leftExtractionPrimitiveCoordinateEquiv
    {m : ℕ} (B : Finset (Fin m)) :
    {τ : PartialPairing
        (Fin (2 * residualBlockOrder
          (B.image leftMomentIndex))) //
      τ ∈ primitiveFullPairings
        (residualBlockOrder
          (B.image leftMomentIndex))} ≃
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder B)) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder B)} :=
  r324PrimitiveCoordinateCastEquiv
    (r324LeftBlockOrder_image B)

/-- The ambient complete primitive sum on a left doubled block is exactly
the ordinary R-322 complete extraction-block sum on the first-half tuple. -/
theorem r324PrimitivePartitionBlockSum_image_leftMomentIndex
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : ExtractionBlockIndex κp)
    (v : Fin (2 * m) → T4) :
    r324PrimitivePartitionBlockSum
        ρ ε κp κm π
        (B.1.image leftMomentIndex) v =
      r322ExtractionBlockPrimitiveSum
        ρ ε κp B
        (fun i => v (leftMomentIndex i)) := by
  have hmem :=
    r324LeftExtractionBlock_mem_primitivePartition
      κp κm π B
  rw [r324PrimitivePartitionBlockSum_of_mem
    ρ ε κp κm π
    (B.1.image leftMomentIndex) hmem v]
  unfold r322ExtractionBlockPrimitiveSum
  unfold primitivePartitionBlockCovarianceFactor
    extractionBlockPrimitiveCovarianceFactor
  apply Fintype.sum_equiv
    (leftExtractionPrimitiveCoordinateEquiv B.1)
  intro σ
  apply primitiveCovarianceProduct_castOrder_eq
    ρ ε (r324LeftBlockOrder_image B.1) σ
  intro i
  congr 1
  exact
    r324LeftBlockOrderIso_transport
      κp κm π B
      ((momentPrimitiveBlockPartition
        κp κm π).block_fullyPaired hmem)
      i

end

end Anderson4D
