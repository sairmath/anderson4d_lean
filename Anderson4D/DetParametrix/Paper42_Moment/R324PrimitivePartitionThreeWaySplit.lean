import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedFiberExact
import Anderson4D.DetParametrix.Paper42_Moment.R324InitialTwoHalfRootIntegrability

/-!
# Three-way block split of the exact R-324 primitive partition

The exact primitive-coordinate fibre of one residual-refined R-324
signature is indexed by the concatenation of three literal block families:
the left extraction blocks, the right extraction blocks, and the nonempty
residual cross blocks.  This file records that concatenation and the
corresponding exact product split while all factors are still signed.

This is algebraic bookkeeping only.  It does not take a norm, integrate an
endpoint, or claim that the concatenation order is the analytic Phase-A
order inside either half.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## The literal three-family list -/

/-- Removing empty blocks affects only the residual family: extraction
blocks in either half are already nonempty. -/
theorem momentNonemptyPrimitiveBlocks_eq_threeFamilies
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    momentNonemptyPrimitiveBlocks κp κm π =
      momentLeftExtractionBlocks κp ++
        momentRightExtractionBlocks κm ++
          nonemptyMomentResidualCollapseBlocks κp κm π := by
  unfold momentNonemptyPrimitiveBlocks
    momentAllPrimitiveBlocks
    nonemptyMomentResidualCollapseBlocks
  rw [List.filter_append, List.filter_append]
  have hleft :
      (momentLeftExtractionBlocks κp).filter
          (fun B => B.Nonempty) =
        momentLeftExtractionBlocks κp := by
    apply List.filter_eq_self.mpr
    intro B hB
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
    exact decide_eq_true
      ((List.forall_iff_forall_mem.mp
          (extractionBlocks_forall_nonempty κp) A hA)
        |>.image leftMomentIndex)
  have hright :
      (momentRightExtractionBlocks κm).filter
          (fun B => B.Nonempty) =
        momentRightExtractionBlocks κm := by
    apply List.filter_eq_self.mpr
    intro B hB
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
    exact decide_eq_true
      ((List.forall_iff_forall_mem.mp
          (extractionBlocks_forall_nonempty κm) A hA)
        |>.image rightMomentIndex)
  rw [hleft, hright]

/-! ## A proof-independent complete sum attached to an ambient block -/

/-- Complete primitive-pairing sum on one block of the concrete R-324
partition.  The default branch is irrelevant on the literal schedule and
makes the function convenient for list products. -/
def r324PrimitivePartitionBlockSum
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (v : Fin (2 * m) → T4) : ℝ :=
  if hB :
      B ∈ (momentPrimitiveBlockPartition κp κm π).blocks then
    ∑ σ :
        {τ : PartialPairing
            (Fin (2 * residualBlockOrder B)) //
          τ ∈ primitiveFullPairings
            (residualBlockOrder B)},
      primitivePartitionBlockCovarianceFactor
        ρ ε (momentPrimitiveBlockPartition κp κm π)
        ⟨B, hB⟩ σ v
  else
    1

theorem r324PrimitivePartitionBlockSum_of_mem
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB :
      B ∈ (momentPrimitiveBlockPartition κp κm π).blocks)
    (v : Fin (2 * m) → T4) :
    r324PrimitivePartitionBlockSum
        ρ ε κp κm π B v =
      ∑ σ :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder B)) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder B)},
        primitivePartitionBlockCovarianceFactor
          ρ ε (momentPrimitiveBlockPartition κp κm π)
          ⟨B, hB⟩ σ v := by
  unfold r324PrimitivePartitionBlockSum
  rw [dif_pos hB]

/-! ## Exact split of the dependent block product -/

/-- The dependent complete-coordinate product is exactly the product of
the left, right, and residual list products. -/
theorem prod_primitivePartitionBlockSums_eq_threeFamilies
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) :
    (∏ B :
        PrimitivePartitionBlockIndex
          (momentPrimitiveBlockPartition κp κm π),
      ∑ σ :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder B.1)) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder B.1)},
        primitivePartitionBlockCovarianceFactor
          ρ ε (momentPrimitiveBlockPartition κp κm π)
          B σ v) =
      ((momentLeftExtractionBlocks κp).map
          (fun B =>
            r324PrimitivePartitionBlockSum
              ρ ε κp κm π B v)).prod *
        ((momentRightExtractionBlocks κm).map
          (fun B =>
            r324PrimitivePartitionBlockSum
              ρ ε κp κm π B v)).prod *
        ((nonemptyMomentResidualCollapseBlocks
            κp κm π).map
          (fun B =>
            r324PrimitivePartitionBlockSum
              ρ ε κp κm π B v)).prod := by
  let P := momentPrimitiveBlockPartition κp κm π
  let f : Finset (Fin (2 * m)) → ℝ :=
    fun B =>
      r324PrimitivePartitionBlockSum
        ρ ε κp κm π B v
  calc
    (∏ B : PrimitivePartitionBlockIndex P,
        ∑ σ :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder B.1)) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder B.1)},
          primitivePartitionBlockCovarianceFactor
            ρ ε P B σ v) =
        ∏ B : PrimitivePartitionBlockIndex P, f B.1 := by
      apply Fintype.prod_congr
      intro B
      exact
        (r324PrimitivePartitionBlockSum_of_mem
          ρ ε κp κm π B.1 B.2 v).symm
    _ = (P.blocks.map f).prod := by
      exact
        (primitiveBlockPartition_list_prod_eq_fintype_prod
          P f).symm
    _ = _ := by
      rw [show P.blocks =
          momentNonemptyPrimitiveBlocks κp κm π by rfl]
      rw [momentNonemptyPrimitiveBlocks_eq_threeFamilies]
      simp only [List.map_append, List.prod_append]
      rfl

end

end Anderson4D
