import Anderson4D.DetParametrix.Paper42_Moment.R324ResidualPrimitiveCoordinateExpansion

/-!
# Realizing residual primitive coordinates in one refined R-324 fibre

The residual-coordinate Fubini expansion is useful analytically only if
every selected tuple is represented by an actual contraction in the same
residual-refined fibre.  We fill the residual block coordinates with the
selected tuple, retain the baseline coordinates on every other primitive
block, and invert the two exact coordinate equivalences.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- Primitive coordinates which agree with the baseline contraction away
from the residual block family and use the prescribed tuple on that family. -/
def r324PrimitiveCoordinatesWithResidual
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2) :
    PrimitivePartitionCoordinates
      (momentPrimitiveBlockPartition
        e₀.1 e₀.2.1 e₀.2.2) :=
  fun B =>
    if hB :
        B.1 ∈ nonemptyMomentResidualCollapseBlocks
          e₀.1 e₀.2.1 e₀.2.2 then
      coordinates ⟨B.1, hB⟩
    else
      primitivePartitionFiberCoordinates
        (momentPrimitiveBlockPartition
          e₀.1 e₀.2.1 e₀.2.2)
        (momentRefinedFiberEquivPrimitivePartitionFiber
          e₀ he₀ ⟨e₀, he₀⟩) B

/-- Evaluation of the completed coordinate tuple on a residual block. -/
@[simp]
theorem r324PrimitiveCoordinatesWithResidual_apply_residual
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2)
    (B : R324ResidualPrimitiveBlockIndex
      e₀.1 e₀.2.1 e₀.2.2) :
    r324PrimitiveCoordinatesWithResidual
        e₀ he₀ coordinates
        ⟨B.1,
          r324ResidualPrimitiveBlock_mem_partition
            e₀.1 e₀.2.1 e₀.2.2 B⟩ =
      coordinates B := by
  unfold r324PrimitiveCoordinatesWithResidual
  rw [dif_pos B.2]

/-- Evaluation away from the residual block family retains the baseline
primitive coordinate. -/
theorem r324PrimitiveCoordinatesWithResidual_apply_nonresidual
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2)
    (B : PrimitivePartitionBlockIndex
      (momentPrimitiveBlockPartition
        e₀.1 e₀.2.1 e₀.2.2))
    (hB :
      B.1 ∉ nonemptyMomentResidualCollapseBlocks
        e₀.1 e₀.2.1 e₀.2.2) :
    r324PrimitiveCoordinatesWithResidual
        e₀ he₀ coordinates B =
      primitivePartitionFiberCoordinates
        (momentPrimitiveBlockPartition
          e₀.1 e₀.2.1 e₀.2.2)
        (momentRefinedFiberEquivPrimitivePartitionFiber
          e₀ he₀ ⟨e₀, he₀⟩) B := by
  unfold r324PrimitiveCoordinatesWithResidual
  rw [dif_neg hB]

/-- A left extraction block cannot also be a nonempty residual block. -/
theorem momentLeftExtractionBlock_not_mem_nonemptyResidual
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentLeftExtractionBlocks κp) :
    B ∉ nonemptyMomentResidualCollapseBlocks κp κm π := by
  intro hResidual
  have hResidualData :=
    mem_nonemptyMomentResidualCollapseBlocks.mp hResidual
  have hdisjoint : Disjoint B B :=
    Disjoint.mono
      (momentLeftExtractionBlock_subset_removed hB)
      (momentResidualCollapseBlock_subset_active
        hResidualData.1)
      (momentLeftRemoved_disjoint_residual κp κm)
  obtain ⟨i, hi⟩ := hResidualData.2
  exact (Finset.disjoint_left.mp hdisjoint) hi hi

/-- A right extraction block cannot also be a nonempty residual block. -/
theorem momentRightExtractionBlock_not_mem_nonemptyResidual
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentRightExtractionBlocks κm) :
    B ∉ nonemptyMomentResidualCollapseBlocks κp κm π := by
  intro hResidual
  have hResidualData :=
    mem_nonemptyMomentResidualCollapseBlocks.mp hResidual
  have hdisjoint : Disjoint B B :=
    Disjoint.mono
      (momentRightExtractionBlock_subset_removed hB)
      (momentResidualCollapseBlock_subset_active
        hResidualData.1)
      (momentRightRemoved_disjoint_residual κp κm)
  obtain ⟨i, hi⟩ := hResidualData.2
  exact (Finset.disjoint_left.mp hdisjoint) hi hi

/-- Every left extraction-block coordinate is retained from the baseline. -/
theorem r324PrimitiveCoordinatesWithResidual_apply_left
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2)
    (B : PrimitivePartitionBlockIndex
      (momentPrimitiveBlockPartition
        e₀.1 e₀.2.1 e₀.2.2))
    (hB : B.1 ∈ momentLeftExtractionBlocks e₀.1) :
    r324PrimitiveCoordinatesWithResidual
        e₀ he₀ coordinates B =
      primitivePartitionFiberCoordinates
        (momentPrimitiveBlockPartition
          e₀.1 e₀.2.1 e₀.2.2)
        (momentRefinedFiberEquivPrimitivePartitionFiber
          e₀ he₀ ⟨e₀, he₀⟩) B := by
  exact
    r324PrimitiveCoordinatesWithResidual_apply_nonresidual
      e₀ he₀ coordinates B
      (momentLeftExtractionBlock_not_mem_nonemptyResidual
        e₀.1 e₀.2.1 e₀.2.2 B.1 hB)

/-- Every right extraction-block coordinate is retained from the baseline. -/
theorem r324PrimitiveCoordinatesWithResidual_apply_right
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2)
    (B : PrimitivePartitionBlockIndex
      (momentPrimitiveBlockPartition
        e₀.1 e₀.2.1 e₀.2.2))
    (hB : B.1 ∈ momentRightExtractionBlocks e₀.2.1) :
    r324PrimitiveCoordinatesWithResidual
        e₀ he₀ coordinates B =
      primitivePartitionFiberCoordinates
        (momentPrimitiveBlockPartition
          e₀.1 e₀.2.1 e₀.2.2)
        (momentRefinedFiberEquivPrimitivePartitionFiber
          e₀ he₀ ⟨e₀, he₀⟩) B := by
  exact
    r324PrimitiveCoordinatesWithResidual_apply_nonresidual
      e₀ he₀ coordinates B
      (momentRightExtractionBlock_not_mem_nonemptyResidual
        e₀.1 e₀.2.1 e₀.2.2 B.1 hB)

/-- The contraction in the fixed refined fibre realizing an arbitrary
tuple of residual primitive coordinates. -/
def r324RefinedContractionOfResidualCoordinates
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2) :
    MomentRefinedContractionFiberAt m s r :=
  (momentRefinedFiberEquivPrimitivePartitionFiber
      e₀ he₀).symm
    ((primitivePartitionFiberEquivCoordinates
      (momentPrimitiveBlockPartition
        e₀.1 e₀.2.1 e₀.2.2)).symm
      (r324PrimitiveCoordinatesWithResidual
        e₀ he₀ coordinates))

/-- The realized contraction belongs to the original residual-refined
fibre by construction. -/
theorem r324RefinedContractionOfResidualCoordinates_mem
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2) :
    (r324RefinedContractionOfResidualCoordinates
        e₀ he₀ coordinates).1 ∈
      momentRefinedContractionFiber m s r :=
  (r324RefinedContractionOfResidualCoordinates
    e₀ he₀ coordinates).2

/-- Applying both forward coordinate maps to the realized contraction
recovers the completed primitive-coordinate tuple. -/
theorem r324RefinedContractionOfResidualCoordinates_coordinates
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2) :
    primitivePartitionFiberCoordinates
        (momentPrimitiveBlockPartition
          e₀.1 e₀.2.1 e₀.2.2)
        (momentRefinedFiberEquivPrimitivePartitionFiber
          e₀ he₀
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates)) =
      r324PrimitiveCoordinatesWithResidual
        e₀ he₀ coordinates := by
  let P :=
    momentPrimitiveBlockPartition
      e₀.1 e₀.2.1 e₀.2.2
  let E :=
    momentRefinedFiberEquivPrimitivePartitionFiber e₀ he₀
  let C :=
    primitivePartitionFiberEquivCoordinates P
  change C (E (E.symm (C.symm
    (r324PrimitiveCoordinatesWithResidual
      e₀ he₀ coordinates)))) =
      r324PrimitiveCoordinatesWithResidual
        e₀ he₀ coordinates
  rw [E.apply_symm_apply, C.apply_symm_apply]

/-- The primitive coordinate seen on each residual block of the realized
contraction is exactly the prescribed one. -/
theorem r324RefinedContractionOfResidualCoordinates_apply_residual
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2)
    (B : R324ResidualPrimitiveBlockIndex
      e₀.1 e₀.2.1 e₀.2.2) :
    primitivePartitionFiberCoordinates
        (momentPrimitiveBlockPartition
          e₀.1 e₀.2.1 e₀.2.2)
        (momentRefinedFiberEquivPrimitivePartitionFiber
          e₀ he₀
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates))
        ⟨B.1,
          r324ResidualPrimitiveBlock_mem_partition
            e₀.1 e₀.2.1 e₀.2.2 B⟩ =
      coordinates B := by
  rw [
    r324RefinedContractionOfResidualCoordinates_coordinates,
    r324PrimitiveCoordinatesWithResidual_apply_residual]

/-- The realized contraction has the baseline coordinate on every left
extraction block. -/
theorem r324RefinedContractionOfResidualCoordinates_apply_left
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2)
    (B : PrimitivePartitionBlockIndex
      (momentPrimitiveBlockPartition
        e₀.1 e₀.2.1 e₀.2.2))
    (hB : B.1 ∈ momentLeftExtractionBlocks e₀.1) :
    primitivePartitionFiberCoordinates
        (momentPrimitiveBlockPartition
          e₀.1 e₀.2.1 e₀.2.2)
        (momentRefinedFiberEquivPrimitivePartitionFiber
          e₀ he₀
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates)) B =
      primitivePartitionFiberCoordinates
        (momentPrimitiveBlockPartition
          e₀.1 e₀.2.1 e₀.2.2)
        (momentRefinedFiberEquivPrimitivePartitionFiber
          e₀ he₀ ⟨e₀, he₀⟩) B := by
  rw [r324RefinedContractionOfResidualCoordinates_coordinates]
  exact
    r324PrimitiveCoordinatesWithResidual_apply_left
      e₀ he₀ coordinates B hB

/-- The realized contraction has the baseline coordinate on every right
extraction block. -/
theorem r324RefinedContractionOfResidualCoordinates_apply_right
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2)
    (B : PrimitivePartitionBlockIndex
      (momentPrimitiveBlockPartition
        e₀.1 e₀.2.1 e₀.2.2))
    (hB : B.1 ∈ momentRightExtractionBlocks e₀.2.1) :
    primitivePartitionFiberCoordinates
        (momentPrimitiveBlockPartition
          e₀.1 e₀.2.1 e₀.2.2)
        (momentRefinedFiberEquivPrimitivePartitionFiber
          e₀ he₀
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates)) B =
      primitivePartitionFiberCoordinates
        (momentPrimitiveBlockPartition
          e₀.1 e₀.2.1 e₀.2.2)
        (momentRefinedFiberEquivPrimitivePartitionFiber
          e₀ he₀ ⟨e₀, he₀⟩) B := by
  rw [r324RefinedContractionOfResidualCoordinates_coordinates]
  exact
    r324PrimitiveCoordinatesWithResidual_apply_right
      e₀ he₀ coordinates B hB

/-! ## The realized residual covariance product -/

/-- On one residual block, the prescribed coordinate factor is the actual
ambient covariance factor of the realized contraction. -/
theorem r324ResidualPrimitiveCoordinateFactor_eq_realized
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (ρ : SmoothCutoff) (ε : ℝ)
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2)
    (B : R324ResidualPrimitiveBlockIndex
      e₀.1 e₀.2.1 e₀.2.2)
    (v : Fin (2 * m) → T4) :
    r324ResidualPrimitiveCoordinateFactor
        ρ ε e₀.1 e₀.2.1 e₀.2.2
        B (coordinates B) v =
      pairingCovarianceProductOn ρ ε
        (momentCombinedPairing
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates).1.1
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates).1.2.1
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates).1.2.2)
        B.1 v := by
  let P :=
    momentPrimitiveBlockPartition
      e₀.1 e₀.2.1 e₀.2.2
  let realized :=
    r324RefinedContractionOfResidualCoordinates
      e₀ he₀ coordinates
  let τ : PrimitivePartitionFiber P :=
    momentRefinedFiberEquivPrimitivePartitionFiber
      e₀ he₀ realized
  let BI : PrimitivePartitionBlockIndex P :=
    ⟨B.1,
      r324ResidualPrimitiveBlock_mem_partition
        e₀.1 e₀.2.1 e₀.2.2 B⟩
  have hcoordinate :
      primitivePartitionFiberCoordinates P τ BI =
        coordinates B := by
    exact
      r324RefinedContractionOfResidualCoordinates_apply_residual
        e₀ he₀ coordinates B
  change
    primitivePartitionBlockCovarianceFactor
        ρ ε P BI (coordinates B) v =
      pairingCovarianceProductOn ρ ε τ.1 BI.1 v
  rw [pairingCovarianceProductOn_primitivePartitionFiber_eq_blockCoordinate]
  rw [hcoordinate]

/-- The complete prescribed residual-coordinate product is the covariance
product of the realized contraction on the baseline residual carrier. -/
theorem r324ResidualPrimitiveCoordinateProduct_eq_realized_on_baseline
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (ρ : SmoothCutoff) (ε : ℝ)
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2)
    (v : Fin (2 * m) → T4) :
    r324ResidualPrimitiveCoordinateProduct
        ρ ε e₀.1 e₀.2.1 e₀.2.2 coordinates v =
      pairingCovarianceProductOn ρ ε
        (momentCombinedPairing
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates).1.1
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates).1.2.1
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates).1.2.2)
        (momentResidualActive e₀.1 e₀.2.1) v := by
  let blocks :=
    nonemptyMomentResidualCollapseBlocks
      e₀.1 e₀.2.1 e₀.2.2
  let realized :=
    r324RefinedContractionOfResidualCoordinates
      e₀ he₀ coordinates
  let κ :=
    momentCombinedPairing
      realized.1.1 realized.1.2.1 realized.1.2.2
  have hcover :
      finsetUnionList blocks =
        momentResidualActive e₀.1 e₀.2.1 := by
    dsimp only [blocks]
    unfold nonemptyMomentResidualCollapseBlocks
    rw [finsetUnionList_filter_nonempty,
      finsetUnionList_momentResidualCollapseBlocks]
  have hfactor :
      pairingCovarianceProductOn ρ ε κ
          (momentResidualActive e₀.1 e₀.2.1) v =
        (blocks.map fun B =>
          pairingCovarianceProductOn ρ ε κ B v).prod := by
    rw [← hcover]
    exact
      pairingCovarianceProductOn_finsetUnionList
        ρ ε κ blocks
        (nonemptyMomentResidualCollapseBlocks_pairwise_disjoint
          e₀.1 e₀.2.1 e₀.2.2) v
  change
    (∏ B : R324ResidualPrimitiveBlockIndex
        e₀.1 e₀.2.1 e₀.2.2,
      r324ResidualPrimitiveCoordinateFactor
        ρ ε e₀.1 e₀.2.1 e₀.2.2
        B (coordinates B) v) =
      pairingCovarianceProductOn ρ ε κ
        (momentResidualActive e₀.1 e₀.2.1) v
  calc
    (∏ B : R324ResidualPrimitiveBlockIndex
        e₀.1 e₀.2.1 e₀.2.2,
      r324ResidualPrimitiveCoordinateFactor
        ρ ε e₀.1 e₀.2.1 e₀.2.2
        B (coordinates B) v) =
        ∏ B : {B : Finset (Fin (2 * m)) // B ∈ blocks},
          pairingCovarianceProductOn ρ ε κ B.1 v := by
      apply Fintype.prod_congr
      intro B
      exact
        r324ResidualPrimitiveCoordinateFactor_eq_realized
          ρ ε e₀ he₀ coordinates B v
    _ =
        (blocks.map fun B =>
          pairingCovarianceProductOn ρ ε κ B v).prod := by
      exact
        (list_map_prod_eq_fintype_prod_subtype
          blocks
          (nonemptyMomentResidualCollapseBlocks_nodup
            e₀.1 e₀.2.1 e₀.2.2)
          fun B =>
            pairingCovarianceProductOn ρ ε κ B v).symm
    _ =
        pairingCovarianceProductOn ρ ε κ
          (momentResidualActive e₀.1 e₀.2.1) v :=
      hfactor.symm

/-! ## Structural invariants of the realization -/

/-- Filling residual coordinates does not change the fixed within-half
endpoint signature. -/
theorem
    r324RefinedContractionOfResidualCoordinates_momentSignature
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2) :
    momentContractionSignature
        (r324RefinedContractionOfResidualCoordinates
          e₀ he₀ coordinates).1 =
      momentContractionSignature e₀ := by
  have hrealized :=
    mem_momentRefinedContractionFiber.mp
      (r324RefinedContractionOfResidualCoordinates
        e₀ he₀ coordinates).2
  have hbaseline :=
    mem_momentRefinedContractionFiber.mp he₀
  exact hrealized.1.trans hbaseline.1.symm

/-- Filling residual coordinates also preserves the fixed residual-chain
endpoint signature. -/
theorem
    r324RefinedContractionOfResidualCoordinates_residualChainSignature
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2) :
    momentResidualChainSignature
        (r324RefinedContractionOfResidualCoordinates
          e₀ he₀ coordinates).1.1
        (r324RefinedContractionOfResidualCoordinates
          e₀ he₀ coordinates).1.2.1
        (r324RefinedContractionOfResidualCoordinates
          e₀ he₀ coordinates).1.2.2 =
      momentResidualChainSignature
        e₀.1 e₀.2.1 e₀.2.2 := by
  have hrealized :=
    mem_momentRefinedContractionFiber.mp
      (r324RefinedContractionOfResidualCoordinates
        e₀ he₀ coordinates).2
  have hbaseline :=
    mem_momentRefinedContractionFiber.mp he₀
  exact hrealized.2.trans hbaseline.2.symm

/-- The left and right extraction-block families remain literally the same
after realizing residual coordinates. -/
theorem
    r324RefinedContractionOfResidualCoordinates_extractionBlocks
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2) :
    momentLeftExtractionBlocks
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates).1.1 =
        momentLeftExtractionBlocks e₀.1 ∧
      momentRightExtractionBlocks
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates).1.2.1 =
        momentRightExtractionBlocks e₀.2.1 := by
  exact
    momentExtractionBlocks_eq_of_momentContractionSignature_eq
      (r324RefinedContractionOfResidualCoordinates
        e₀ he₀ coordinates).1
      e₀
      (r324RefinedContractionOfResidualCoordinates_momentSignature
        e₀ he₀ coordinates)

/-- Both signed Green skeletons are unchanged by residual-coordinate
realization. -/
theorem
    r324RefinedContractionOfResidualCoordinates_greenSkeletons
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2) :
    renormalizedGreenSkeleton
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates).1.1 =
        renormalizedGreenSkeleton e₀.1 ∧
      renormalizedGreenSkeleton
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates).1.2.1 =
        renormalizedGreenSkeleton e₀.2.1 := by
  exact
    renormalizedGreenSkeletons_eq_of_momentContractionSignature_eq
      (r324RefinedContractionOfResidualCoordinates
        e₀ he₀ coordinates).1
      e₀
      (r324RefinedContractionOfResidualCoordinates_momentSignature
        e₀ he₀ coordinates)

/-- The residual active carrier of the realized contraction is the baseline
carrier on which its prescribed residual coordinates were installed. -/
theorem
    r324RefinedContractionOfResidualCoordinates_residualActive
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2) :
    momentResidualActive
        (r324RefinedContractionOfResidualCoordinates
          e₀ he₀ coordinates).1.1
        (r324RefinedContractionOfResidualCoordinates
          e₀ he₀ coordinates).1.2.1 =
      momentResidualActive e₀.1 e₀.2.1 := by
  obtain ⟨hleft, hright⟩ :=
    momentFinalActive_eq_of_momentContractionSignature_eq
      (r324RefinedContractionOfResidualCoordinates
        e₀ he₀ coordinates).1
      e₀
      (r324RefinedContractionOfResidualCoordinates_momentSignature
        e₀ he₀ coordinates)
  unfold momentResidualActive
  rw [hleft, hright]

/-- Every residual coordinate tuple is realized by an actual contraction
in the same refined fibre, and its coordinate product is exactly the
covariance product on that contraction's own residual active carrier. -/
theorem r324ResidualPrimitiveCoordinateProduct_eq_pairingCovarianceProductOn
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (ρ : SmoothCutoff) (ε : ℝ)
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (coordinates :
      R324ResidualPrimitiveCoordinates
        e₀.1 e₀.2.1 e₀.2.2)
    (v : Fin (2 * m) → T4) :
    r324ResidualPrimitiveCoordinateProduct
        ρ ε e₀.1 e₀.2.1 e₀.2.2 coordinates v =
      pairingCovarianceProductOn ρ ε
        (momentCombinedPairing
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates).1.1
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates).1.2.1
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates).1.2.2)
        (momentResidualActive
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates).1.1
          (r324RefinedContractionOfResidualCoordinates
            e₀ he₀ coordinates).1.2.1)
        v := by
  rw [
    r324RefinedContractionOfResidualCoordinates_residualActive
      e₀ he₀ coordinates]
  exact
    r324ResidualPrimitiveCoordinateProduct_eq_realized_on_baseline
      ρ ε e₀ he₀ coordinates v

end

end Anderson4D
