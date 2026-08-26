import Anderson4D.DetParametrix.Paper42_Moment.R324WholeRootPointwiseNormalization
import Anderson4D.DetParametrix.Paper42_Moment.R324MarkedResidualBlockProductClosure

/-!
# Independent residual primitive coordinates at one refined R-324 root

After the two within-half products have been identified with their signed
R-322 traces, the remaining cross-block product is still a product of
complete finite primitive sums.  This module performs only the exact finite
Fubini interchange that exposes one independent coordinate on every residual
block.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- A nonempty residual block of the fixed three-way primitive schedule. -/
abbrev R324ResidualPrimitiveBlockIndex
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :=
  {B : Finset (Fin (2 * m)) //
    B ∈ nonemptyMomentResidualCollapseBlocks κp κm π}

/-- Complete primitive pairing coordinate on one residual block. -/
abbrev R324ResidualPrimitiveCoordinate
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (B : R324ResidualPrimitiveBlockIndex κp κm π) :=
  R324PrimitiveCoordinate (residualBlockOrder B.1)

/-- One independently selected complete primitive pairing on every
nonempty residual block. -/
abbrev R324ResidualPrimitiveCoordinates
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :=
  ∀ B : R324ResidualPrimitiveBlockIndex κp κm π,
    R324ResidualPrimitiveCoordinate B

/-- Every residual schedule block is a literal block of the fixed primitive
partition. -/
theorem r324ResidualPrimitiveBlock_mem_partition
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : R324ResidualPrimitiveBlockIndex κp κm π) :
    B.1 ∈ (momentPrimitiveBlockPartition κp κm π).blocks := by
  rw [momentPrimitiveBlockPartition_blocks,
    momentNonemptyPrimitiveBlocks_eq_threeFamilies]
  exact List.mem_append.mpr (Or.inr B.2)

/-- Covariance factor selected by one primitive coordinate on one residual
block. -/
def r324ResidualPrimitiveCoordinateFactor
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : R324ResidualPrimitiveBlockIndex κp κm π)
    (coordinate : R324ResidualPrimitiveCoordinate B)
    (v : Fin (2 * m) → T4) : ℝ :=
  primitivePartitionBlockCovarianceFactor
    ρ ε (momentPrimitiveBlockPartition κp κm π)
    ⟨B.1,
      r324ResidualPrimitiveBlock_mem_partition
        κp κm π B⟩
    coordinate v

/-- Covariance product selected by one complete residual coordinate tuple. -/
def r324ResidualPrimitiveCoordinateProduct
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (coordinates :
      R324ResidualPrimitiveCoordinates κp κm π)
    (v : Fin (2 * m) → T4) : ℝ :=
  ∏ B : R324ResidualPrimitiveBlockIndex κp κm π,
    r324ResidualPrimitiveCoordinateFactor
      ρ ε κp κm π B (coordinates B) v

/-- Exact finite Fubini expansion of the residual product into independent
primitive coordinates. -/
theorem r324ResidualPrimitiveSumProduct_eq_sum_coordinates
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) :
    r324ResidualPrimitiveSumProduct
        ρ ε κp κm π v =
      ∑ coordinates :
          R324ResidualPrimitiveCoordinates κp κm π,
        r324ResidualPrimitiveCoordinateProduct
          ρ ε κp κm π coordinates v := by
  unfold r324ResidualPrimitiveSumProduct
  rw [list_map_prod_eq_fintype_prod_subtype
    (nonemptyMomentResidualCollapseBlocks κp κm π)
    (nonemptyMomentResidualCollapseBlocks_nodup κp κm π)]
  calc
    (∏ B : R324ResidualPrimitiveBlockIndex κp κm π,
        r324PrimitivePartitionBlockSum
          ρ ε κp κm π B.1 v) =
        ∏ B : R324ResidualPrimitiveBlockIndex κp κm π,
          ∑ σ : R324ResidualPrimitiveCoordinate B,
            r324ResidualPrimitiveCoordinateFactor
              ρ ε κp κm π B σ v := by
      apply Fintype.prod_congr
      intro B
      unfold r324ResidualPrimitiveCoordinateFactor
      exact
        r324PrimitivePartitionBlockSum_of_mem
          ρ ε κp κm π B.1
          (r324ResidualPrimitiveBlock_mem_partition
            κp κm π B) v
    _ =
        ∑ coordinates :
            R324ResidualPrimitiveCoordinates κp κm π,
          ∏ B : R324ResidualPrimitiveBlockIndex κp κm π,
            r324ResidualPrimitiveCoordinateFactor
              ρ ε κp κm π B (coordinates B) v := by
      exact
        Fintype.prod_sum fun B σ =>
            r324ResidualPrimitiveCoordinateFactor
              ρ ε κp κm π B σ v
    _ = _ := rfl

/-! ## Pointwise residual-coordinate expansion -/

/-- The exact refined physical root is a finite signed sum over residual
primitive coordinates, with both certified within-half initial traces still
outside the sum. -/
theorem momentRefinedPhysicalIntegrand_eq_sum_residualCoordinates
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4)
    (s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    momentRefinedPhysicalIntegrand
        ρ ε m α β s r x y z w v =
      ∑ coordinates :
          R324ResidualPrimitiveCoordinates
            e₀.1 e₀.2.1 e₀.2.2,
        momentFourierPhase α β x y z w *
          ((R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).residualIntegrand
            ρ ε x y
            (fun i => v (leftMomentIndex i)) : ℂ) *
          ((R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.2.1).residualIntegrand
            ρ ε z w
            (fun i => v (rightMomentIndex i)) : ℂ) *
          (r324ResidualPrimitiveCoordinateProduct
            ρ ε e₀.1 e₀.2.1 e₀.2.2 coordinates v : ℂ) := by
  rw [
    momentRefinedPhysicalIntegrand_eq_twoInitialResiduals_mul_cross
      ρ lam ε m α β s r e₀ he₀ x y z w v,
    r324ResidualPrimitiveSumProduct_eq_sum_coordinates]
  push_cast
  rw [Finset.mul_sum]

end

end Anderson4D
