import Anderson4D.DetParametrix.Paper42_Moment.R324FirstLeftPhysicalProcessedBridge

/-!
# The actual first-left physical integral at the empty analytic prefix

This module factors the genuine first-left physical moment fibre in the
branch where the selected block is the analytic head.  The selected
production Green factors and the complete primitive covariance sum are
identified with the raw local integrand of the all-Green edge state after
translation by the actual successor.  The state is replaced only under the
selected spatial integral.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Production endpoint factors -/

/-- The first selected extraction pair belongs to the actual extraction
list. -/
theorem r324FirstLeft_selectRel_mem_extract
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :
    selectRel e₀.1 Finset.univ hleft ∈ extract e₀.1 := by
  have hleft' := hleft
  obtain ⟨a, b, hab⟩ := hleft'
  have hm : 0 < m := by
    exact Nat.pos_of_ne_zero fun hm0 => by
      subst m
      exact Fin.elim0 a
  obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  unfold extract
  rw [extractAux_succ_pos fuel hleft]
  simp

/-- At the selected outgoing edge, the production shortcut is exactly the
shortcut from the selected left endpoint. -/
theorem r324ProductionGreenEdgeFactor_outgoing_eq
    {m : ℕ} (κ : PartialPairing (Fin m))
    (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (hsig :
      reductionEndpointSignature κ =
        reductionEndpointSignature e₀.1)
    (xt : Fin (m + 2) → T4) :
    r324ProductionGreenEdgeFactor κ xt
        (r324FirstLeftOutgoingEdge e₀ hleft) =
      (greenFn
          (xt (r324FirstLeftOutgoingEdge e₀ hleft).castSucc -
            xt (r324FirstLeftOutgoingEdge e₀ hleft).succ) : ℂ) -
        (greenFn
          (xt (varIdx
              (selectRel e₀.1 Finset.univ hleft).1) -
            xt (r324FirstLeftOutgoingEdge e₀ hleft).succ) : ℂ) := by
  have hextract :
      extract κ = extract e₀.1 :=
    extract_eq_of_reductionEndpointSignature_eq
      κ e₀.1 hsig
  have hp :
      selectRel e₀.1 Finset.univ hleft ∈ extract κ := by
    rw [hextract]
    exact r324FirstLeft_selectRel_mem_extract e₀ hleft
  unfold r324ProductionGreenEdgeFactor
  change
    originalGreenEdge xt
        (extractedRightEdge
          (selectRel e₀.1 Finset.univ hleft)) -
      extractedShortcutGreenEdge κ xt
        (extractedRightEdge
          (selectRel e₀.1 Finset.univ hleft)) =
      _
  rw [extractedShortcutGreenEdge_extractedRightEdge
    κ (selectRel e₀.1 Finset.univ hleft) hp]
  rfl

/-- The first physical block endpoint is the selected shortcut parent. -/
theorem r324FirstLeftPhysicalBlockTuple_zero
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (x y : T4) (v : Fin (2 * m) → T4) :
    r324FirstLeftPhysicalBlockTuple e₀ hleft v
        ⟨0, by
          have hn := r324FirstLeft_one_le_blockOrder e₀ hleft
          omega⟩ =
      assemble x y (r324LeftPhysicalTuple v)
        (varIdx (selectRel e₀.1 Finset.univ hleft).1) := by
  rw [← r324FirstLeftCarrierTuple_assemble_eq_physicalBlockTuple
    e₀ hleft x y v]
  unfold r324FirstLeftCarrierTuple
  congr 1

/-- The last physical block endpoint is the left endpoint of the selected
outgoing production edge. -/
theorem r324FirstLeftPhysicalBlockTuple_last
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (x y : T4) (v : Fin (2 * m) → T4) :
    r324FirstLeftPhysicalBlockTuple e₀ hleft v
        (primitiveLast
          (residualBlockOrder
            (selectedExtractionBlock e₀.1 Finset.univ hleft))
          (r324FirstLeft_one_le_blockOrder e₀ hleft)) =
      assemble x y (r324LeftPhysicalTuple v)
        (r324FirstLeftOutgoingEdge e₀ hleft).castSucc := by
  rw [← r324FirstLeftCarrierTuple_assemble_eq_physicalBlockTuple
    e₀ hleft x y v]
  unfold r324FirstLeftCarrierTuple primitiveLast
  apply congrArg (assemble x y (r324LeftPhysicalTuple v))
  apply Fin.ext
  change
    (selectRel e₀.1 Finset.univ hleft).1.val + 1 +
        (2 *
            residualBlockOrder
              (selectedExtractionBlock
                e₀.1 Finset.univ hleft) - 1) =
      (selectRel e₀.1 Finset.univ hleft).2.val + 1
  have hspan := r324FirstLeft_endpoint_span e₀ hleft
  have hle :=
    (selectRel_isRelFullyPaired
      e₀.1 Finset.univ hleft).le
  have hn := r324FirstLeft_one_le_blockOrder e₀ hleft
  omega

theorem r324FirstLeftPhysicalBlockTuple_zero_eq_predecessorSucc
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (x y : T4) (v : Fin (2 * m) → T4) :
    r324FirstLeftPhysicalBlockTuple e₀ hleft v
        ⟨0, by
          have hn := r324FirstLeft_one_le_blockOrder e₀ hleft
          omega⟩ =
      assemble x y (r324LeftPhysicalTuple v)
        (r324FirstLeftPredecessorEdge e₀ hleft).succ := by
  rw [r324FirstLeftPhysicalBlockTuple_zero e₀ hleft x y v]
  congr 1

theorem r324FirstLeftTranslatedPhysicalBlockTuple_zero
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (x y : T4) (v : Fin (2 * m) → T4) :
    r324FirstLeftTranslatedPhysicalBlockTuple e₀ hleft x y v
        ⟨0, by
          have hn := r324FirstLeft_one_le_blockOrder e₀ hleft
          omega⟩ =
      assemble x y (r324LeftPhysicalTuple v)
          (r324FirstLeftPredecessorEdge e₀ hleft).succ -
        assemble x y (r324LeftPhysicalTuple v)
          (r324FirstLeftOutgoingEdge e₀ hleft).succ := by
  unfold r324FirstLeftTranslatedPhysicalBlockTuple
    r324FirstLeftPhysicalSuccessor
  rw [r324FirstLeftPhysicalBlockTuple_zero_eq_predecessorSucc
    e₀ hleft x y v]

theorem r324FirstLeftTranslatedPhysicalBlockTuple_zero_eq_shortcutParent
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (x y : T4) (v : Fin (2 * m) → T4) :
    r324FirstLeftTranslatedPhysicalBlockTuple e₀ hleft x y v
        ⟨0, by
          have hn := r324FirstLeft_one_le_blockOrder e₀ hleft
          omega⟩ =
      assemble x y (r324LeftPhysicalTuple v)
          (varIdx (selectRel e₀.1 Finset.univ hleft).1) -
        assemble x y (r324LeftPhysicalTuple v)
          (r324FirstLeftOutgoingEdge e₀ hleft).succ := by
  unfold r324FirstLeftTranslatedPhysicalBlockTuple
    r324FirstLeftPhysicalSuccessor
  rw [r324FirstLeftPhysicalBlockTuple_zero e₀ hleft x y v]

theorem r324FirstLeftTranslatedPhysicalBlockTuple_last
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (x y : T4) (v : Fin (2 * m) → T4) :
    r324FirstLeftTranslatedPhysicalBlockTuple e₀ hleft x y v
        (primitiveLast
          (residualBlockOrder
            (selectedExtractionBlock e₀.1 Finset.univ hleft))
          (r324FirstLeft_one_le_blockOrder e₀ hleft)) =
      assemble x y (r324LeftPhysicalTuple v)
          (r324FirstLeftOutgoingEdge e₀ hleft).castSucc -
        assemble x y (r324LeftPhysicalTuple v)
          (r324FirstLeftOutgoingEdge e₀ hleft).succ := by
  unfold r324FirstLeftTranslatedPhysicalBlockTuple
    r324FirstLeftPhysicalSuccessor
  rw [r324FirstLeftPhysicalBlockTuple_last e₀ hleft x y v]

theorem r324FirstLeftTranslatedIncomingDifference
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (x y : T4) (v : Fin (2 * m) → T4) :
    (r324FirstLeftPhysicalPredecessor e₀ hleft x y v -
        r324FirstLeftPhysicalSuccessor e₀ hleft x y v) -
      r324FirstLeftTranslatedPhysicalBlockTuple e₀ hleft x y v
        ⟨0, by
          have hn := r324FirstLeft_one_le_blockOrder e₀ hleft
          omega⟩ =
      assemble x y (r324LeftPhysicalTuple v)
          (r324FirstLeftPredecessorEdge e₀ hleft).castSucc -
        assemble x y (r324LeftPhysicalTuple v)
          (r324FirstLeftPredecessorEdge e₀ hleft).succ := by
  rw [r324FirstLeftTranslatedPhysicalBlockTuple_zero
    e₀ hleft x y v]
  unfold r324FirstLeftPhysicalPredecessor
    r324FirstLeftPhysicalSuccessor
  abel

/-! ## Translation ledgers -/

theorem primitiveChainProduct_sub_const_r324
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (t : Fin (2 * n) → T4) (a : T4) :
    primitiveChainProduct n hn G (fun i => t i - a) =
      primitiveChainProduct n hn G t := by
  unfold primitiveChainProduct
  apply Finset.prod_congr rfl
  intro j _hj
  apply congrArg (G j)
  change
    (t (primitiveEdgeLeft n hn j) - a) -
        (t (primitiveEdgeRight n hn j) - a) =
      t (primitiveEdgeLeft n hn j) -
        t (primitiveEdgeRight n hn j)
  abel

theorem primitiveCovarianceProduct_sub_const_r324
    (ρ : SmoothCutoff) (ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin (2 * n)))
    (t : Fin (2 * n) → T4) (a : T4) :
    primitiveCovarianceProduct ρ ε n κ (fun i => t i - a) =
      primitiveCovarianceProduct ρ ε n κ t := by
  unfold primitiveCovarianceProduct
  apply Finset.prod_congr rfl
  intro i _hi
  apply congrArg (ρ.etaEpsT4 ε)
  change (t i - a) - (t (κ i) - a) = t i - t (κ i)
  abel

/-! ## The physical outer factor after exposing the selected block -/

/-- Every factor of the actual first-left physical integrand which is
independent of the selected block coordinates. -/
def r324FirstLeftInitialPhysicalOuterFactor
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (α β : Z4) (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  let κ₀ :=
    (firstBlockReferenceEndpointFiber e₀.1 hleft ω.1).1
  let xt := assemble x y (r324LeftPhysicalTuple v)
  momentFourierPhase α β x y z w *
    r324FirstLeftExteriorGreenProduct κ₀ e₀ hleft xt *
    renormalizedGreenSkeleton ω.2.1.1
      (assemble z w fun i => v (rightMomentIndex i)) *
    ((pairingCovarianceProductOn ρ ε κ₀
          ((Finset.univ : Finset (Fin m)) \
            selectedExtractionBlock e₀.1 Finset.univ hleft)
          (fun i => v (leftMomentIndex i)) *
        pairingCovarianceProductOn ρ ε ω.2.1.1 Finset.univ
          (fun i => v (rightMomentIndex i)) *
        momentCrossCovarianceProduct ρ ε m
          κ₀ ω.2.1.1 ω.2.2 v : ℝ) : ℂ)

/-! ## The genuine initial local factor -/

theorem r324FirstLeftInitialStepContext_rawLocalIntegrand
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (tail : List (R322ExtractionStep m))
    (hschedule :
      r322AnalyticSchedule e₀.1 =
        r324FirstLeftSelectedStep e₀ hleft :: tail)
    (u : T4)
    (t :
      Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4) :
    (r324FirstLeftInitialStepContext e₀ hleft tail hschedule).rawLocalIntegrand
        ρ ε u t =
      greenFn
          (u - t ⟨0, by
            have hn := r324FirstLeft_one_le_blockOrder e₀ hleft
            omega⟩) *
        primitiveChainProduct
          (residualBlockOrder
            (selectedExtractionBlock e₀.1 Finset.univ hleft))
          (r324FirstLeft_one_le_blockOrder e₀ hleft)
          (fun _ => greenFn) t *
        (greenFn
            (t (primitiveLast
              (residualBlockOrder
                (selectedExtractionBlock e₀.1 Finset.univ hleft))
              (r324FirstLeft_one_le_blockOrder e₀ hleft))) -
          greenFn
            (t ⟨0, by
              have hn := r324FirstLeft_one_le_blockOrder e₀ hleft
              omega⟩)) *
        ∑ κB : R324FirstLeftBlockCoordinate e₀ hleft,
          primitiveCovarianceProduct ρ ε
            (residualBlockOrder
              (selectedExtractionBlock e₀.1 Finset.univ hleft))
            κB.1 t := by
  rfl

/-- At the empty analytic prefix, the touching production factors and the
complete primitive covariance sum are exactly the translated raw local
integrand.  This is a pre-collapse identity: no processed state is asserted
pointwise. -/
theorem r324FirstLeftTouching_mul_primitiveSum_eq_initialRawLocal
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (tail : List (R322ExtractionStep m))
    (hschedule :
      r322AnalyticSchedule e₀.1 =
        r324FirstLeftSelectedStep e₀ hleft :: tail)
    (x y : T4) (v : Fin (2 * m) → T4) :
    let κ₀ :=
      (firstBlockReferenceEndpointFiber e₀.1 hleft ω.1).1
    let xt := assemble x y (r324LeftPhysicalTuple v)
    let ctx :=
      r324FirstLeftInitialStepContext e₀ hleft tail hschedule
    let u :=
      r324FirstLeftPhysicalPredecessor e₀ hleft x y v -
        r324FirstLeftPhysicalSuccessor e₀ hleft x y v
    let t :=
      r324FirstLeftTranslatedPhysicalBlockTuple
        e₀ hleft x y v
    r324FirstLeftTouchingGreenProduct κ₀ e₀ hleft xt *
        (∑ κB : R324FirstLeftBlockCoordinate e₀ hleft,
          (primitiveCovarianceProduct ρ ε
            (residualBlockOrder
              (selectedExtractionBlock
                e₀.1 Finset.univ hleft))
            κB.1
            (r324FirstLeftPhysicalBlockTuple
              e₀ hleft v) : ℂ)) =
      (ctx.rawLocalIntegrand ρ ε u t : ℂ) := by
  dsimp only
  let κ₀ :=
    (firstBlockReferenceEndpointFiber e₀.1 hleft ω.1).1
  have hsig :
      reductionEndpointSignature κ₀ =
        reductionEndpointSignature e₀.1 :=
    (firstBlockReferenceEndpointFiber e₀.1 hleft ω.1).2
  let xt := assemble x y (r324LeftPhysicalTuple v)
  rw [r324FirstLeftTouchingGreenProduct_eq_primitiveLocal
    κ₀ e₀ hleft hsig xt]
  rw [productionPredecessor_eq_initialStateEdge
    κ₀ e₀ hleft hsig tail hschedule xt]
  rw [r324ProductionGreenEdgeFactor_outgoing_eq
    κ₀ e₀ hleft hsig xt]
  rw [r324FirstLeftCarrierTuple_assemble_eq_physicalBlockTuple
    e₀ hleft x y v]
  rw [← primitiveChainProduct_sub_const_r324
    (residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft))
    (r324FirstLeft_one_le_blockOrder e₀ hleft)
    (fun _ => greenFn)
    (r324FirstLeftPhysicalBlockTuple e₀ hleft v)
    (r324FirstLeftPhysicalSuccessor e₀ hleft x y v)]
  simp_rw [← primitiveCovarianceProduct_sub_const_r324
    ρ ε
    (residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft))
    _ (r324FirstLeftPhysicalBlockTuple e₀ hleft v)
    (r324FirstLeftPhysicalSuccessor e₀ hleft x y v)]
  have ht :
      (fun i =>
        r324FirstLeftPhysicalBlockTuple e₀ hleft v i -
          r324FirstLeftPhysicalSuccessor e₀ hleft x y v) =
        r324FirstLeftTranslatedPhysicalBlockTuple
          e₀ hleft x y v := by
    rfl
  rw [ht]
  rw [r324FirstLeftInitialStepContext_rawLocalIntegrand
    ρ ε e₀ hleft tail hschedule]
  rw [r324FirstLeftTranslatedIncomingDifference
    e₀ hleft x y v]
  rw [← r324FirstLeftTranslatedPhysicalBlockTuple_last
    e₀ hleft x y v]
  rw [← r324FirstLeftTranslatedPhysicalBlockTuple_zero_eq_shortcutParent
    e₀ hleft x y v]
  simp only [r324InitialWithinHalfEdgeState]
  dsimp only [xt]
  push_cast
  ring

/-- The actual first-left physical section is the honest empty-prefix raw
local factor times factors exterior to the selected block. -/
theorem r324FirstLeftOuterFactor_mul_primitiveSum_eq_initialRaw_mul_outer
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (α β : Z4) (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (tail : List (R322ExtractionStep m))
    (hschedule :
      r322AnalyticSchedule e₀.1 =
        r324FirstLeftSelectedStep e₀ hleft :: tail)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    let ctx :=
      r324FirstLeftInitialStepContext e₀ hleft tail hschedule
    let u :=
      r324FirstLeftPhysicalPredecessor e₀ hleft x y v -
        r324FirstLeftPhysicalSuccessor e₀ hleft x y v
    let t :=
      r324FirstLeftTranslatedPhysicalBlockTuple
        e₀ hleft x y v
    r324FirstLeftOuterFactor ρ ε α β e₀ hleft ω
          x y z w v *
        (∑ κB : R324FirstLeftBlockCoordinate e₀ hleft,
          (primitiveCovarianceProduct ρ ε
            (residualBlockOrder
              (selectedExtractionBlock
                e₀.1 Finset.univ hleft))
            κB.1
            (r324FirstLeftPhysicalBlockTuple
              e₀ hleft v) : ℂ)) =
      (ctx.rawLocalIntegrand ρ ε u t : ℂ) *
        r324FirstLeftInitialPhysicalOuterFactor
          ρ ε α β e₀ hleft ω x y z w v := by
  dsimp only
  let κ₀ :=
    (firstBlockReferenceEndpointFiber e₀.1 hleft ω.1).1
  have hlocal :=
    r324FirstLeftTouching_mul_primitiveSum_eq_initialRawLocal
      ρ ε e₀ hleft ω tail hschedule x y v
  dsimp only at hlocal
  calc
    r324FirstLeftOuterFactor ρ ε α β e₀ hleft ω
          x y z w v *
        (∑ κB : R324FirstLeftBlockCoordinate e₀ hleft,
          (primitiveCovarianceProduct ρ ε
            (residualBlockOrder
              (selectedExtractionBlock
                e₀.1 Finset.univ hleft))
            κB.1
            (r324FirstLeftPhysicalBlockTuple
              e₀ hleft v) : ℂ)) =
      (r324FirstLeftTouchingGreenProduct
          κ₀ e₀ hleft
          (assemble x y (r324LeftPhysicalTuple v)) *
        (∑ κB : R324FirstLeftBlockCoordinate e₀ hleft,
          (primitiveCovarianceProduct ρ ε
            (residualBlockOrder
              (selectedExtractionBlock
                e₀.1 Finset.univ hleft))
            κB.1
            (r324FirstLeftPhysicalBlockTuple
              e₀ hleft v) : ℂ))) *
        r324FirstLeftInitialPhysicalOuterFactor
          ρ ε α β e₀ hleft ω x y z w v := by
      unfold r324FirstLeftOuterFactor
        r324FirstLeftInitialPhysicalOuterFactor
      dsimp only [κ₀]
      unfold r324LeftPhysicalTuple
      rw [renormalizedGreenSkeleton_eq_firstLeftTouching_mul_exterior
        (firstBlockReferenceEndpointFiber
          e₀.1 hleft ω.1).1 e₀ hleft
        (assemble x y (fun i => v (leftMomentIndex i)))]
      ring
    _ = _ := by
      rw [hlocal]

end

end Anderson4D
