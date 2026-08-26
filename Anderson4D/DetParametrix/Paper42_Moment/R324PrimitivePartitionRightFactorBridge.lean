import Anderson4D.DetParametrix.Paper42_Moment.R324PrimitivePartitionThreeWaySplit

/-!
# Right within-half factors in the unified R-324 partition

The right-copy blocks in the unified primitive partition are literal images
of the Definition 3.1 extraction blocks under `rightMomentIndex`.  This file
identifies their canonical increasing enumerations and, consequently, their
complete primitive covariance sums with the existing R-322 block sums.

Everything here is an exact signed finite-sum identity.  No norm or
integration is used.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## The right block as an ambient partition block -/

/-- A right extraction block occurs literally in the unified primitive
partition. -/
theorem rightExtractionBlock_image_mem_momentPrimitiveBlockPartition
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : ExtractionBlockIndex κm) :
    B.1.image rightMomentIndex ∈
      (momentPrimitiveBlockPartition κp κm π).blocks := by
  rw [momentPrimitiveBlockPartition_blocks,
    mem_momentNonemptyPrimitiveBlocks]
  refine ⟨Or.inr (Or.inl ?_), ?_⟩
  · unfold momentRightExtractionBlocks
    exact List.mem_map.mpr ⟨B.1, B.2, rfl⟩
  · exact
      (List.forall_iff_forall_mem.mp
          (extractionBlocks_forall_nonempty κm)
          B.1 B.2).image rightMomentIndex

/-- The perturbative order is unchanged by the right-copy embedding. -/
@[simp]
theorem residualBlockOrder_image_rightMomentIndex_bridge
    {m : ℕ} (B : Finset (Fin m)) :
    residualBlockOrder (B.image rightMomentIndex) =
      residualBlockOrder B := by
  unfold residualBlockOrder
  rw [Finset.card_image_of_injective _
    rightMomentIndex_injective]

/-! ## Compatibility of the canonical increasing enumerations -/

/-- The canonical increasing enumeration of an image block is obtained by
enumerating the original block and then applying `rightMomentIndex`.

The `Fin.castOrderIso` is the proof-relevant transport between the two
definitionally different, but propositionally equal, primitive-order
domains. -/
theorem residualPrimitiveBlockOrderIso_image_rightMomentIndex_apply
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : ExtractionBlockIndex κm)
    (i :
      Fin
        (2 *
          residualBlockOrder
            (B.1.image rightMomentIndex))) :
    ((residualPrimitiveBlockOrderIso
        (momentCombinedPairing κp κm π)
        (B.1.image rightMomentIndex)
        (momentRightExtractionBlock_isFullyPairedOn_of_mem
          κp κm π
          (B.1.image rightMomentIndex)
          (by
            unfold momentRightExtractionBlocks
            exact List.mem_map.mpr
              ⟨B.1, B.2, rfl⟩))
        i).1) =
      rightMomentIndex
        ((residualPrimitiveBlockOrderIso
            κm B.1
            (extractionBlock_isFullyPairedOn_of_mem
              κm B.1 B.2)
            ((Fin.castOrderIso
              (congrArg (2 * ·)
                (residualBlockOrder_image_rightMomentIndex_bridge
                  B.1))) i)).1) := by
  let hright :
      B.1.image rightMomentIndex ∈
        momentRightExtractionBlocks κm := by
    unfold momentRightExtractionBlocks
    exact List.mem_map.mpr ⟨B.1, B.2, rfl⟩
  let hfullAmbient :
      IsFullyPairedOn
        (momentCombinedPairing κp κm π)
        (B.1.image rightMomentIndex) :=
    momentRightExtractionBlock_isFullyPairedOn_of_mem
      κp κm π (B.1.image rightMomentIndex) hright
  let hfull :
      IsFullyPairedOn κm B.1 :=
    extractionBlock_isFullyPairedOn_of_mem
      κm B.1 B.2
  let horder :
      residualBlockOrder (B.1.image rightMomentIndex) =
        residualBlockOrder B.1 :=
    residualBlockOrder_image_rightMomentIndex_bridge B.1
  let castOrder :
      Fin
          (2 *
            residualBlockOrder
              (B.1.image rightMomentIndex)) ≃o
        Fin (2 * residualBlockOrder B.1) :=
    Fin.castOrderIso (congrArg (2 * ·) horder)
  let f :
      Fin
          (2 *
            residualBlockOrder
              (B.1.image rightMomentIndex)) →
        Fin (2 * m) :=
    fun j =>
      rightMomentIndex
        ((residualPrimitiveBlockOrderIso
          κm B.1 hfull (castOrder j)).1)
  have hfmem :
      ∀ j, f j ∈ B.1.image rightMomentIndex := by
    intro j
    exact Finset.mem_image.mpr
      ⟨(residualPrimitiveBlockOrderIso
          κm B.1 hfull (castOrder j)).1,
        (residualPrimitiveBlockOrderIso
          κm B.1 hfull (castOrder j)).2,
        rfl⟩
  have hfmono : StrictMono f := by
    intro a b hab
    rw [rightMomentIndex_lt_rightMomentIndex_iff]
    exact
      (residualPrimitiveBlockOrderIso
          κm B.1 hfull).strictMono
        (castOrder.strictMono hab)
  have hcard :
      (B.1.image rightMomentIndex).card =
        2 *
          residualBlockOrder
            (B.1.image rightMomentIndex) :=
    (Nat.two_mul_div_two_of_even
      (residualBlock_card_even
        (momentCombinedPairing κp κm π)
        (B.1.image rightMomentIndex)
        hfullAmbient)).symm
  have henum :
      f =
        (B.1.image rightMomentIndex).orderEmbOfFin
          hcard :=
    Finset.orderEmbOfFin_unique hcard hfmem hfmono
  change
    (((B.1.image rightMomentIndex).orderIsoOfFin
        _ i :
      B.1.image rightMomentIndex).1) =
      rightMomentIndex
        (((B.1.orderIsoOfFin _)
          ((Fin.castOrderIso _) i) : B.1).1)
  rw [Finset.coe_orderIsoOfFin_apply]
  exact (congrFun henum i).symm

/-! ## Equality of the complete primitive sums -/

/-- The complete primitive-pairing coordinate type at order `n`. -/
abbrev R324PrimitiveCoordinate (n : ℕ) :=
  {τ : PartialPairing (Fin (2 * n)) //
    τ ∈ primitiveFullPairings n}

/-- Pure equality transport of complete primitive-pairing coordinates. -/
def r324PrimitiveCoordinateCastEquiv
    {a b : ℕ} (h : a = b) :
    R324PrimitiveCoordinate a ≃
      R324PrimitiveCoordinate b :=
  Equiv.cast (congrArg R324PrimitiveCoordinate h)

/-- `primitiveCovarianceProduct` is compatible with equality transport of
its perturbative order and the corresponding cast of tuple coordinates. -/
theorem primitiveCovarianceProduct_castOrder_eq
    (ρ : SmoothCutoff) (ε : ℝ)
    {a b : ℕ} (h : a = b)
    (σ : R324PrimitiveCoordinate a)
    (x : Fin (2 * a) → T4)
    (y : Fin (2 * b) → T4)
    (hxy :
      ∀ i,
        x i =
          y ((Fin.castOrderIso
            (congrArg (2 * ·) h)) i)) :
    primitiveCovarianceProduct ρ ε a σ.1 x =
      primitiveCovarianceProduct ρ ε b
        ((r324PrimitiveCoordinateCastEquiv h σ).1) y := by
  subst b
  simp only [
      r324PrimitiveCoordinateCastEquiv,
      Equiv.cast_refl,
      Equiv.refl_apply,
      Fin.castOrderIso_refl,
      OrderIso.refl_apply] at hxy ⊢
  exact congrArg
    (primitiveCovarianceProduct ρ ε a σ.1)
    (funext hxy)

/-- Proof-only transport between the primitive-coordinate types carried by
a right-copy image block and by its original extraction block. -/
def rightExtractionPrimitiveCoordinateEquiv
    {m : ℕ} (B : Finset (Fin m)) :
    {τ : PartialPairing
        (Fin
          (2 *
            residualBlockOrder
              (B.image rightMomentIndex))) //
      τ ∈ primitiveFullPairings
        (residualBlockOrder
          (B.image rightMomentIndex))} ≃
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder B)) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder B)} :=
  r324PrimitiveCoordinateCastEquiv
    (residualBlockOrder_image_rightMomentIndex_bridge B)

/-- The complete ambient primitive-partition sum on a right-copy block is
exactly the R-322 extraction-block primitive sum evaluated on the right
half of the doubled coordinate tuple. -/
theorem r324PrimitivePartitionBlockSum_image_rightMomentIndex_eq
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : ExtractionBlockIndex κm)
    (v : Fin (2 * m) → T4) :
    r324PrimitivePartitionBlockSum
        ρ ε κp κm π
        (B.1.image rightMomentIndex) v =
      r322ExtractionBlockPrimitiveSum
        ρ ε κm B
        (fun i => v (rightMomentIndex i)) := by
  let hB :=
    rightExtractionBlock_image_mem_momentPrimitiveBlockPartition
      κp κm π B
  rw [r324PrimitivePartitionBlockSum_of_mem
    ρ ε κp κm π
    (B.1.image rightMomentIndex) hB v]
  unfold primitivePartitionBlockCovarianceFactor
    r322ExtractionBlockPrimitiveSum
    extractionBlockPrimitiveCovarianceFactor
  apply Fintype.sum_equiv
    (rightExtractionPrimitiveCoordinateEquiv B.1)
  intro σ
  apply primitiveCovarianceProduct_castOrder_eq
    ρ ε
    (residualBlockOrder_image_rightMomentIndex_bridge
      B.1)
    σ
  intro i
  congr 1
  exact
    residualPrimitiveBlockOrderIso_image_rightMomentIndex_apply
      κp κm π B i

end

end Anderson4D
