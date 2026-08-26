import Anderson4D.DetParametrix.Paper42_Moment.R324PrimitivePartitionLeftFactorBridge

/-!
# Exact pointwise normalization of one refined R-324 root

Before taking a norm or integrating any endpoint, the exact primitive
coordinate fibre splits into the two Definition 3.1 within-half factors and
the remaining cross-cut factors.  This module rewrites the two within-half
products as the certified initial R-322 residual traces.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## The two embedded within-half list products -/

/-- The left family in the unified doubled partition is exactly the complete
R-322 primitive product of the first contraction. -/
theorem r324LeftPrimitiveBlockProduct_eq_r322
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) :
    ((momentLeftExtractionBlocks κp).map
      (fun B =>
        r324PrimitivePartitionBlockSum
          ρ ε κp κm π B v)).prod =
      ∏ B : ExtractionBlockIndex κp,
        r322ExtractionBlockPrimitiveSum
          ρ ε κp B
          (fun i => v (leftMomentIndex i)) := by
  unfold momentLeftExtractionBlocks
  rw [List.map_map]
  rw [list_map_prod_eq_fintype_prod_subtype
    (extractionBlocks κp) (extractionBlocks_nodup κp)]
  apply Fintype.prod_congr
  intro B
  exact
    r324PrimitivePartitionBlockSum_image_leftMomentIndex
      ρ ε κp κm π B v

/-- The right family in the unified doubled partition is exactly the complete
R-322 primitive product of the second contraction. -/
theorem r324RightPrimitiveBlockProduct_eq_r322
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) :
    ((momentRightExtractionBlocks κm).map
      (fun B =>
        r324PrimitivePartitionBlockSum
          ρ ε κp κm π B v)).prod =
      ∏ B : ExtractionBlockIndex κm,
        r322ExtractionBlockPrimitiveSum
          ρ ε κm B
          (fun i => v (rightMomentIndex i)) := by
  unfold momentRightExtractionBlocks
  rw [List.map_map]
  rw [list_map_prod_eq_fintype_prod_subtype
    (extractionBlocks κm) (extractionBlocks_nodup κm)]
  apply Fintype.prod_congr
  intro B
  exact
    r324PrimitivePartitionBlockSum_image_rightMomentIndex_eq
      ρ ε κp κm π B v

/-! ## The exact refined root -/

/-- Product of the complete primitive sums on the remaining nonempty
cross-cut blocks. -/
def r324ResidualPrimitiveSumProduct
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) : ℝ :=
  ((nonemptyMomentResidualCollapseBlocks κp κm π).map
    (fun B =>
      r324PrimitivePartitionBlockSum
        ρ ε κp κm π B v)).prod

/-- The exact real covariance sum in one residual-refined fibre is the
product of the two complete within-half R-322 factors and the remaining
cross-cut factors. -/
theorem sum_refinedCovariance_eq_twoHalfProducts_mul_residual
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (v : Fin (2 * m) → T4) :
    (∑ e ∈ momentRefinedContractionFiber m s r,
      primitiveCovarianceProduct ρ ε m
        (momentCombinedPairing e.1 e.2.1 e.2.2) v) =
      (∏ B : ExtractionBlockIndex e₀.1,
        r322ExtractionBlockPrimitiveSum
          ρ ε e₀.1 B
          (fun i => v (leftMomentIndex i))) *
      (∏ B : ExtractionBlockIndex e₀.2.1,
        r322ExtractionBlockPrimitiveSum
          ρ ε e₀.2.1 B
          (fun i => v (rightMomentIndex i))) *
      r324ResidualPrimitiveSumProduct
        ρ ε e₀.1 e₀.2.1 e₀.2.2 v := by
  rw [sum_refinedCovariance_eq_sum_primitivePartitionFiber
    ρ ε m e₀ he₀ v]
  rw [sum_primitivePartitionFiber_covariance_eq_prod_primitiveSums
    ρ ε m
    (momentCombinedPairing e₀.1 e₀.2.1 e₀.2.2)
    (momentPrimitiveBlockPartition e₀.1 e₀.2.1 e₀.2.2)
    v]
  rw [prod_primitivePartitionBlockSums_eq_threeFamilies
    ρ ε e₀.1 e₀.2.1 e₀.2.2 v]
  rw [
    r324LeftPrimitiveBlockProduct_eq_r322
      ρ ε e₀.1 e₀.2.1 e₀.2.2 v,
    r324RightPrimitiveBlockProduct_eq_r322
      ρ ε e₀.1 e₀.2.1 e₀.2.2 v]
  rfl

/-- Pointwise signed normal form of one exact refined root.  The two
within-half factors are the genuine initial R-322 residual integrands; the
cross-cut primitive sums remain outside for the subsequent §4.2 routing. -/
theorem momentRefinedPhysicalIntegrand_eq_twoInitialResiduals_mul_cross
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4)
    (s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    momentRefinedPhysicalIntegrand
        ρ ε m α β s r x y z w v =
      momentFourierPhase α β x y z w *
        ((R324WithinHalfResidualPrefix.initial
            ρ lam ε e₀.1).residualIntegrand
          ρ ε x y
          (fun i => v (leftMomentIndex i)) : ℂ) *
        ((R324WithinHalfResidualPrefix.initial
            ρ lam ε e₀.2.1).residualIntegrand
          ρ ε z w
          (fun i => v (rightMomentIndex i)) : ℂ) *
        (r324ResidualPrimitiveSumProduct
          ρ ε e₀.1 e₀.2.1 e₀.2.2 v : ℂ) := by
  have he₀Coarse :
      e₀ ∈ momentContractionFiber m s :=
    mem_momentContractionFiber.mpr
      (mem_momentRefinedContractionFiber.mp he₀).1
  rw [
    momentRefinedPhysicalIntegrand_eq_commonSkeletons_mul_sum_covariance
      ρ ε m α β s r e₀ he₀Coarse x y z w v]
  have hsumCast :
      (∑ e ∈ momentRefinedContractionFiber m s r,
        (primitiveCovarianceProduct ρ ε m
          (momentCombinedPairing e.1 e.2.1 e.2.2) v : ℂ)) =
        ((∑ e ∈ momentRefinedContractionFiber m s r,
          primitiveCovarianceProduct ρ ε m
            (momentCombinedPairing
              e.1 e.2.1 e.2.2) v : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hsumCast]
  rw [sum_refinedCovariance_eq_twoHalfProducts_mul_residual
    ρ ε m e₀ he₀ v]
  rw [
    R324WithinHalfResidualPrefix.initial_residualIntegrand_complex_eq,
    R324WithinHalfResidualPrefix.initial_residualIntegrand_complex_eq]
  push_cast
  ring

/-! ## Schedule form for the next routing stage -/

/-- The residual product can be read directly along the canonical nested
cross schedule. -/
theorem r324ResidualPrimitiveSumProduct_eq_nestedSchedule
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) :
    r324ResidualPrimitiveSumProduct
        ρ ε κp κm π v =
      ((r324NestedCrossSchedule κp κm π).map
        (fun block =>
          r324PrimitivePartitionBlockSum
            ρ ε κp κm π block.carrier v)).prod := by
  unfold r324ResidualPrimitiveSumProduct
  rw [← r324NestedCrossSchedule_carriers κp κm π]
  simp only [List.map_map, Function.comp_def]

end

end Anderson4D
