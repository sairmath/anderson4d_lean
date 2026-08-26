import Anderson4D.DetParametrix.Core.ReductionExtractionBlocks

/-!
# Complete primitive-block factorization of an R-324 contraction

For one contraction triple, Definition 3.1 first removes primitive blocks
inside each copy.  The remaining doubled carrier is then partitioned by the
canonical residual nested blocks.  This file proves that these three block
families are disjoint, cover the whole doubled carrier, and factor the full
covariance product exactly.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- Definition 3.1 blocks in the left copy of the doubled carrier. -/
def momentLeftExtractionBlocks
    {m : ℕ} (κp : PartialPairing (Fin m)) :
    List (Finset (Fin (2 * m))) :=
  (extractionBlocks κp).map fun B =>
    B.image leftMomentIndex

/-- Definition 3.1 blocks in the right copy of the doubled carrier. -/
def momentRightExtractionBlocks
    {m : ℕ} (κm : PartialPairing (Fin m)) :
    List (Finset (Fin (2 * m))) :=
  (extractionBlocks κm).map fun B =>
    B.image rightMomentIndex

/-- Union of all within-left removed blocks. -/
def momentLeftRemoved
    {m : ℕ} (κp : PartialPairing (Fin m)) :
    Finset (Fin (2 * m)) :=
  finsetUnionList (momentLeftExtractionBlocks κp)

/-- Union of all within-right removed blocks. -/
def momentRightRemoved
    {m : ℕ} (κm : PartialPairing (Fin m)) :
    Finset (Fin (2 * m)) :=
  finsetUnionList (momentRightExtractionBlocks κm)

theorem momentLeftExtractionBlocks_pairwise_disjoint
    {m : ℕ} (κp : PartialPairing (Fin m)) :
    (momentLeftExtractionBlocks κp).Pairwise Disjoint := by
  exact list_map_image_pairwise_disjoint
    leftMomentIndex leftMomentIndex_injective
      (extractionBlocks κp)
      (extractionBlocks_pairwise_disjoint κp)

theorem momentRightExtractionBlocks_pairwise_disjoint
    {m : ℕ} (κm : PartialPairing (Fin m)) :
    (momentRightExtractionBlocks κm).Pairwise Disjoint := by
  exact list_map_image_pairwise_disjoint
    rightMomentIndex rightMomentIndex_injective
      (extractionBlocks κm)
      (extractionBlocks_pairwise_disjoint κm)

/-- Relative primitivity is preserved by the order-preserving embedding
into the left doubled copy. -/
theorem IsRelPrimitiveOn.image_leftMomentIndex
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {B : Finset (Fin m)}
    (hB : IsRelPrimitiveOn κp B) :
    IsRelPrimitiveOn (momentCombinedPairing κp κm π)
      (B.image leftMomentIndex) := by
  intro a' b' hab
  obtain ⟨a, ha, rfl⟩ :=
    Finset.mem_image.mp hab.left_mem
  obtain ⟨b, hb, rfl⟩ :=
    Finset.mem_image.mp hab.right_mem
  have habOriginal :
      IsRelFullyPaired κp B a b :=
    isRelFullyPaired_image_leftMomentIndex_iff.mp hab
  rw [← image_leftMomentIndex_relIcc,
    hB a b habOriginal]

/-- Relative primitivity is preserved by the order-preserving embedding
into the right doubled copy. -/
theorem IsRelPrimitiveOn.image_rightMomentIndex
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {B : Finset (Fin m)}
    (hB : IsRelPrimitiveOn κm B) :
    IsRelPrimitiveOn (momentCombinedPairing κp κm π)
      (B.image rightMomentIndex) := by
  intro a' b' hab
  obtain ⟨a, ha, rfl⟩ :=
    Finset.mem_image.mp hab.left_mem
  obtain ⟨b, hb, rfl⟩ :=
    Finset.mem_image.mp hab.right_mem
  have habOriginal :
      IsRelFullyPaired κm B a b :=
    isRelFullyPaired_image_rightMomentIndex_iff.mp hab
  rw [← image_rightMomentIndex_relIcc,
    hB a b habOriginal]

theorem momentLeftExtractionBlock_isFullyPairedOn_of_mem
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentLeftExtractionBlocks κp) :
    IsFullyPairedOn (momentCombinedPairing κp κm π) B := by
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
  exact
    (extractionBlock_isFullyPairedOn_of_mem κp A hA)
      |>.image_leftMomentIndex

theorem momentLeftExtractionBlock_isRelPrimitiveOn_of_mem
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentLeftExtractionBlocks κp) :
    IsRelPrimitiveOn (momentCombinedPairing κp κm π) B := by
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
  exact
    (extractionBlock_isRelPrimitiveOn_of_mem κp A hA)
      |>.image_leftMomentIndex

theorem momentRightExtractionBlock_isFullyPairedOn_of_mem
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentRightExtractionBlocks κm) :
    IsFullyPairedOn (momentCombinedPairing κp κm π) B := by
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
  exact
    (extractionBlock_isFullyPairedOn_of_mem κm A hA)
      |>.image_rightMomentIndex

theorem momentRightExtractionBlock_isRelPrimitiveOn_of_mem
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentRightExtractionBlocks κm) :
    IsRelPrimitiveOn (momentCombinedPairing κp κm π) B := by
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
  exact
    (extractionBlock_isRelPrimitiveOn_of_mem κm A hA)
      |>.image_rightMomentIndex

/-- Every within-left collapse block is a genuine standard primitive
pairing after increasing reindexing. -/
theorem momentLeftExtractionBlock_primitivePairing_mem
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentLeftExtractionBlocks κp) :
    let hfull :=
      momentLeftExtractionBlock_isFullyPairedOn_of_mem
        κp κm π B hB
    residualPrimitiveBlockPairing
        (momentCombinedPairing κp κm π) B hfull ∈
      primitiveFullPairings (residualBlockOrder B) := by
  exact residualPrimitiveBlockPairing_mem
    (momentCombinedPairing κp κm π) B
    (momentLeftExtractionBlock_isFullyPairedOn_of_mem
      κp κm π B hB)
    (momentLeftExtractionBlock_isRelPrimitiveOn_of_mem
      κp κm π B hB)

/-- Every within-right collapse block is a genuine standard primitive
pairing after increasing reindexing. -/
theorem momentRightExtractionBlock_primitivePairing_mem
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentRightExtractionBlocks κm) :
    let hfull :=
      momentRightExtractionBlock_isFullyPairedOn_of_mem
        κp κm π B hB
    residualPrimitiveBlockPairing
        (momentCombinedPairing κp κm π) B hfull ∈
      primitiveFullPairings (residualBlockOrder B) := by
  exact residualPrimitiveBlockPairing_mem
    (momentCombinedPairing κp κm π) B
    (momentRightExtractionBlock_isFullyPairedOn_of_mem
      κp κm π B hB)
    (momentRightExtractionBlock_isRelPrimitiveOn_of_mem
      κp κm π B hB)

/-- The two doubled halves are disjoint, even after restricting either
half to arbitrary finsets. -/
theorem disjoint_image_leftMomentIndex_rightMomentIndex
    {m : ℕ} (A B : Finset (Fin m)) :
    Disjoint
      (A.image leftMomentIndex)
      (B.image rightMomentIndex) := by
  rw [Finset.disjoint_left]
  intro k hkL hkR
  obtain ⟨i, _hi, hik⟩ := Finset.mem_image.mp hkL
  obtain ⟨j, _hj, hjk⟩ := Finset.mem_image.mp hkR
  have hval := congrArg Fin.val (hik.trans hjk.symm)
  simp only [leftMomentIndex, rightMomentIndex] at hval
  have hi := i.isLt
  omega

/-- Every doubled index lies in exactly one of the two canonical copies. -/
theorem image_univ_leftMomentIndex_union_rightMomentIndex
    (m : ℕ) :
    (Finset.univ : Finset (Fin m)).image leftMomentIndex ∪
        (Finset.univ : Finset (Fin m)).image rightMomentIndex =
      (Finset.univ : Finset (Fin (2 * m))) := by
  ext k
  simp only [Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · intro _hk
    trivial
  · intro _hk
    by_cases hleft : k.val < m
    · left
      let i : Fin m := ⟨k.val, hleft⟩
      exact ⟨i, Fin.ext rfl⟩
    · right
      have hkLower : m ≤ k.val := Nat.le_of_not_gt hleft
      have hkUpper : k.val - m < m := by
        have hk := k.isLt
        omega
      let j : Fin m := ⟨k.val - m, hkUpper⟩
      refine ⟨j, Fin.ext ?_⟩
      simp only [rightMomentIndex, j]
      omega

theorem momentLeftRemoved_union_final
    {m : ℕ} (κp : PartialPairing (Fin m)) :
    momentLeftRemoved κp ∪
        (finalActive κp).image leftMomentIndex =
      (Finset.univ : Finset (Fin m)).image leftMomentIndex := by
  unfold momentLeftRemoved momentLeftExtractionBlocks
  rw [finsetUnionList_map_image, ← Finset.image_union,
    finsetUnionList_extractionBlocks_union_finalActive]

theorem momentRightRemoved_union_final
    {m : ℕ} (κm : PartialPairing (Fin m)) :
    momentRightRemoved κm ∪
        (finalActive κm).image rightMomentIndex =
      (Finset.univ : Finset (Fin m)).image rightMomentIndex := by
  unfold momentRightRemoved momentRightExtractionBlocks
  rw [finsetUnionList_map_image, ← Finset.image_union,
    finsetUnionList_extractionBlocks_union_finalActive]

theorem momentLeftRemoved_disjoint_final
    {m : ℕ} (κp : PartialPairing (Fin m)) :
    Disjoint (momentLeftRemoved κp)
      ((finalActive κp).image leftMomentIndex) := by
  unfold momentLeftRemoved momentLeftExtractionBlocks
  rw [finsetUnionList_map_image,
    Finset.disjoint_image leftMomentIndex_injective]
  exact extractionBlocks_disjoint_finalActive κp

theorem momentRightRemoved_disjoint_final
    {m : ℕ} (κm : PartialPairing (Fin m)) :
    Disjoint (momentRightRemoved κm)
      ((finalActive κm).image rightMomentIndex) := by
  unfold momentRightRemoved momentRightExtractionBlocks
  rw [finsetUnionList_map_image,
    Finset.disjoint_image rightMomentIndex_injective]
  exact extractionBlocks_disjoint_finalActive κm

theorem momentLeftRemoved_disjoint_rightRemoved
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    Disjoint (momentLeftRemoved κp)
      (momentRightRemoved κm) := by
  unfold momentLeftRemoved momentRightRemoved
    momentLeftExtractionBlocks momentRightExtractionBlocks
  rw [finsetUnionList_map_image, finsetUnionList_map_image]
  exact disjoint_image_leftMomentIndex_rightMomentIndex _ _

theorem momentLeftRemoved_disjoint_residual
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    Disjoint (momentLeftRemoved κp)
      (momentResidualActive κp κm) := by
  unfold momentResidualActive
  rw [Finset.disjoint_union_right]
  exact
    ⟨momentLeftRemoved_disjoint_final κp,
      by
        unfold momentLeftRemoved momentLeftExtractionBlocks
        rw [finsetUnionList_map_image]
        exact disjoint_image_leftMomentIndex_rightMomentIndex _ _⟩

theorem momentRightRemoved_disjoint_residual
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    Disjoint (momentRightRemoved κm)
      (momentResidualActive κp κm) := by
  unfold momentResidualActive
  rw [Finset.disjoint_union_right]
  constructor
  · exact
      (by
        unfold momentRightRemoved momentRightExtractionBlocks
        rw [finsetUnionList_map_image]
        exact
          (disjoint_image_leftMomentIndex_rightMomentIndex
            (finalActive κp)
            (finsetUnionList (extractionBlocks κm))).symm)
  · exact momentRightRemoved_disjoint_final κm

/-- The left removed region, right removed region, and residual carrier
partition the entire doubled carrier. -/
theorem momentRemoved_union_residual_eq_univ
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    (momentLeftRemoved κp ∪ momentRightRemoved κm) ∪
        momentResidualActive κp κm =
      (Finset.univ : Finset (Fin (2 * m))) := by
  unfold momentResidualActive
  calc
    (momentLeftRemoved κp ∪ momentRightRemoved κm) ∪
        ((finalActive κp).image leftMomentIndex ∪
          (finalActive κm).image rightMomentIndex) =
      (momentLeftRemoved κp ∪
          (finalActive κp).image leftMomentIndex) ∪
        (momentRightRemoved κm ∪
          (finalActive κm).image rightMomentIndex) := by
      ac_rfl
    _ =
      (Finset.univ : Finset (Fin m)).image leftMomentIndex ∪
        (Finset.univ : Finset (Fin m)).image rightMomentIndex := by
      rw [momentLeftRemoved_union_final,
        momentRightRemoved_union_final]
    _ = Finset.univ :=
      image_univ_leftMomentIndex_union_rightMomentIndex m

/-- The complete covariance product of one contraction factors into:
the within-left Definition 3.1 blocks, the within-right blocks, and the
canonical residual nested blocks. -/
theorem
    primitiveCovarianceProduct_momentCombinedPairing_eq_prod_all_blocks
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) :
    primitiveCovarianceProduct ρ ε m
        (momentCombinedPairing κp κm π) v =
      ((momentLeftExtractionBlocks κp).map fun B =>
        pairingCovarianceProductOn ρ ε
          (momentCombinedPairing κp κm π) B v).prod *
      ((momentRightExtractionBlocks κm).map fun B =>
        pairingCovarianceProductOn ρ ε
          (momentCombinedPairing κp κm π) B v).prod *
      ((momentResidualCollapseBlocks κp κm π).map fun B =>
        pairingCovarianceProductOn ρ ε
          (momentCombinedPairing κp κm π) B v).prod := by
  let κ := momentCombinedPairing κp κm π
  have hremovedResidual :
      Disjoint
        (momentLeftRemoved κp ∪ momentRightRemoved κm)
        (momentResidualActive κp κm) :=
    Finset.disjoint_union_left.mpr
      ⟨momentLeftRemoved_disjoint_residual κp κm,
        momentRightRemoved_disjoint_residual κp κm⟩
  rw [← pairingCovarianceProductOn_univ ρ ε m κ v,
    ← momentRemoved_union_residual_eq_univ κp κm,
    pairingCovarianceProductOn_union ρ ε κ
      (momentLeftRemoved κp ∪ momentRightRemoved κm)
      (momentResidualActive κp κm)
      hremovedResidual v,
    pairingCovarianceProductOn_union ρ ε κ
      (momentLeftRemoved κp) (momentRightRemoved κm)
      (momentLeftRemoved_disjoint_rightRemoved κp κm) v]
  unfold momentLeftRemoved momentRightRemoved
  rw [
    pairingCovarianceProductOn_finsetUnionList
      ρ ε κ (momentLeftExtractionBlocks κp)
      (momentLeftExtractionBlocks_pairwise_disjoint κp) v,
    pairingCovarianceProductOn_finsetUnionList
      ρ ε κ (momentRightExtractionBlocks κm)
      (momentRightExtractionBlocks_pairwise_disjoint κm) v,
    pairingCovarianceProductOn_momentResidualActive_eq_prod_blocks]

/-- Analytic form of the complete factorization, with empty residual
shells removed before invoking Proposition 4.1. -/
theorem
    primitiveCovarianceProduct_momentCombinedPairing_eq_prod_nonempty_blocks
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) :
    primitiveCovarianceProduct ρ ε m
        (momentCombinedPairing κp κm π) v =
      ((momentLeftExtractionBlocks κp).map fun B =>
        pairingCovarianceProductOn ρ ε
          (momentCombinedPairing κp κm π) B v).prod *
      ((momentRightExtractionBlocks κm).map fun B =>
        pairingCovarianceProductOn ρ ε
          (momentCombinedPairing κp κm π) B v).prod *
      ((nonemptyMomentResidualCollapseBlocks κp κm π).map fun B =>
        pairingCovarianceProductOn ρ ε
          (momentCombinedPairing κp κm π) B v).prod := by
  rw [
    primitiveCovarianceProduct_momentCombinedPairing_eq_prod_all_blocks]
  unfold nonemptyMomentResidualCollapseBlocks
  rw [prod_pairingCovarianceProductOn_filter_nonempty]

/-- The complete product of all primitive covariance blocks belonging to
one contraction entity. -/
def momentContractionPrimitiveBlockProduct
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (e : MomentContraction m)
    (v : Fin (2 * m) → T4) : ℝ :=
  ((momentLeftExtractionBlocks e.1).map fun B =>
    pairingCovarianceProductOn ρ ε
      (momentCombinedPairing e.1 e.2.1 e.2.2) B v).prod *
  ((momentRightExtractionBlocks e.2.1).map fun B =>
    pairingCovarianceProductOn ρ ε
      (momentCombinedPairing e.1 e.2.1 e.2.2) B v).prod *
  ((nonemptyMomentResidualCollapseBlocks e.1 e.2.1 e.2.2).map fun B =>
    pairingCovarianceProductOn ρ ε
      (momentCombinedPairing e.1 e.2.1 e.2.2) B v).prod

theorem primitiveCovarianceProduct_momentContraction_eq_blockProduct
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (e : MomentContraction m)
    (v : Fin (2 * m) → T4) :
    primitiveCovarianceProduct ρ ε m
        (momentCombinedPairing e.1 e.2.1 e.2.2) v =
      momentContractionPrimitiveBlockProduct ρ ε m e v := by
  exact
    primitiveCovarianceProduct_momentCombinedPairing_eq_prod_nonempty_blocks
      ρ ε m e.1 e.2.1 e.2.2 v

/-- Full-pairing-indexed form of the complete block factorization. -/
theorem primitiveCovarianceProduct_fullPairing_eq_blockProduct
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κ : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull})
    (v : Fin (2 * m) → T4) :
    primitiveCovarianceProduct ρ ε m κ.1 v =
      momentContractionPrimitiveBlockProduct ρ ε m
        ((momentContractionEquivFullPairing m).symm κ) v := by
  let e := (momentContractionEquivFullPairing m).symm κ
  have hreassemble :
      momentCombinedPairing e.1 e.2.1 e.2.2 = κ.1 :=
    momentCombinedPairing_momentContractionOfFull κ.1 κ.2
  rw [← hreassemble]
  exact
    primitiveCovarianceProduct_momentContraction_eq_blockProduct
      ρ ε m e v

/-- Exact block-product form of the norm of a fixed-signature physical
integrand.  Both Green skeletons remain outside the full-pairing sum; every
summand inside is now explicitly a product of the left, right, and residual
primitive blocks. -/
theorem
    norm_momentSignaturePhysicalIntegrand_eq_commonSkeletons_mul_sum_blockProducts
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentContractionFiber m s)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    ‖momentSignaturePhysicalIntegrand
        ρ ε m α β s x y z w v‖ =
      ‖renormalizedGreenSkeleton e₀.1
          (assemble x y fun i => v (leftMomentIndex i))‖ *
        ‖renormalizedGreenSkeleton e₀.2.1
          (assemble z w fun i => v (rightMomentIndex i))‖ *
        ∑ κ ∈ momentFullPairingFiber m s,
          momentContractionPrimitiveBlockProduct ρ ε m
            ((momentContractionEquivFullPairing m).symm κ) v := by
  rw [
    norm_momentSignaturePhysicalIntegrand_eq_commonSkeletons_mul_sum_covariance
      ρ ε m α β s e₀ he₀ x y z w v]
  congr 1
  apply Finset.sum_congr rfl
  intro κ _hκ
  exact primitiveCovarianceProduct_fullPairing_eq_blockProduct
    ρ ε m κ v

end

end Anderson4D
