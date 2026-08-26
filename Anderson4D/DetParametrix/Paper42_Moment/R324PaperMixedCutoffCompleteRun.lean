import Anderson4D.DetParametrix.Paper42_Moment.R324PaperCompleteNestedRun

/-!
# Complete nested run with a separate cross-covariance cutoff

Paper: R-324 — §4.2 Step 4(B), mixed-cutoff complete nested run

The terminal half traces remember the original cutoff used during the
within-half elimination.  After those eliminations, however, the grouped
cross-block covariance product may be replaced by a positive analytic
majorant built from a second cutoff.  This file records that separation:
the two inverse-square terminal chains are unchanged, while every complete
primitive head in the nested cross run uses `sigma`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324TwoHalfTerminalData

variable {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaPlus kappaMinus : PartialPairing (Fin m)}

/-- The literal Steps 2--3 density with the terminal half geometry inherited
from `rho` and the grouped cross covariance heads evaluated with `sigma`. -/
def completeNestedRunDensityWithCrossCutoff
    (terminal : R324TwoHalfTerminalData
      rho lam eps kappaPlus kappaMinus)
    (sigma : SmoothCutoff)
    {pi : kappaPlus.singles ≃ kappaMinus.singles}
    (step : R324NestedCrossStepContext kappaPlus kappaMinus pi)
    (hleft : (r324LeftHalfPullback
      step.residual.activeCarrier).Nonempty)
    (hright : (r324RightHalfPullback
      step.residual.activeCarrier).Nonempty)
    (v : step.SurvivingCoordinate → T4) : Real :=
  lamEps lam eps ^ (2 * step.residual.remainingOrder) *
    ((terminal.nestedLeftHalfInvSqProduct step
          step.residual.activeCarrier hleft v *
        terminal.nestedRightHalfInvSqProduct step
          step.residual.activeCarrier hright v) *
      r324NestedResidualPrimitiveSumProduct
        sigma eps kappaPlus kappaMinus pi step.residual
          (step.reconstruct v))

@[simp]
theorem completeNestedRunDensityWithCrossCutoff_self
    (terminal : R324TwoHalfTerminalData
      rho lam eps kappaPlus kappaMinus)
    {pi : kappaPlus.singles ≃ kappaMinus.singles}
    (step : R324NestedCrossStepContext kappaPlus kappaMinus pi)
    (hleft : (r324LeftHalfPullback
      step.residual.activeCarrier).Nonempty)
    (hright : (r324RightHalfPullback
      step.residual.activeCarrier).Nonempty) :
    terminal.completeNestedRunDensityWithCrossCutoff
        rho step hleft hright =
      terminal.completeNestedRunDensity step hleft hright := by
  rfl

private theorem primitivePartitionBlockSum_nonneg_mixed
    (sigma : SmoothCutoff) (eps : Real)
    (kappaPlus kappaMinus : PartialPairing (Fin m))
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (B : Finset (Fin (2 * m))) (v : Fin (2 * m) → T4) :
    0 ≤ r324PrimitivePartitionBlockSum
      sigma eps kappaPlus kappaMinus pi B v := by
  unfold r324PrimitivePartitionBlockSum
  split_ifs
  · exact Finset.sum_nonneg fun pairing _ =>
      primitiveCovarianceProduct_nonneg sigma eps
        (residualBlockOrder B) pairing.1 _
  · exact zero_le_one

private theorem nestedResidualPrimitiveSumProduct_nonneg_mixed
    (sigma : SmoothCutoff) (eps : Real)
    (kappaPlus kappaMinus : PartialPairing (Fin m))
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (res : R324NestedCrossResidualPrefix kappaPlus kappaMinus pi)
    (v : Fin (2 * m) → T4) :
    0 ≤ r324NestedResidualPrimitiveSumProduct
      sigma eps kappaPlus kappaMinus pi res v := by
  unfold r324NestedResidualPrimitiveSumProduct
  apply List.prod_nonneg
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨B, _hB, rfl⟩ := ha
  exact primitivePartitionBlockSum_nonneg_mixed
    sigma eps kappaPlus kappaMinus pi B.carrier v

private theorem nestedLeftHalfInvSqProduct_nonneg_mixed
    (terminal : R324TwoHalfTerminalData
      rho lam eps kappaPlus kappaMinus)
    {pi : kappaPlus.singles ≃ kappaMinus.singles}
    (step : R324NestedCrossStepContext kappaPlus kappaMinus pi)
    (carrier : Finset (Fin (2 * m)))
    (hcarrier : (r324LeftHalfPullback carrier).Nonempty)
    (v : step.SurvivingCoordinate → T4) :
    0 ≤ terminal.nestedLeftHalfInvSqProduct
      step carrier hcarrier v := by
  unfold nestedLeftHalfInvSqProduct
    R324WithinHalfResidualPrefix.halfInvSqChainProduct
  exact Finset.prod_nonneg fun _ _ => invSqKer_nonneg _

private theorem nestedRightHalfInvSqProduct_nonneg_mixed
    (terminal : R324TwoHalfTerminalData
      rho lam eps kappaPlus kappaMinus)
    {pi : kappaPlus.singles ≃ kappaMinus.singles}
    (step : R324NestedCrossStepContext kappaPlus kappaMinus pi)
    (carrier : Finset (Fin (2 * m)))
    (hcarrier : (r324RightHalfPullback carrier).Nonempty)
    (v : step.SurvivingCoordinate → T4) :
    0 ≤ terminal.nestedRightHalfInvSqProduct
      step carrier hcarrier v := by
  unfold nestedRightHalfInvSqProduct
    R324WithinHalfResidualPrefix.halfInvSqChainProduct
  exact Finset.prod_nonneg fun _ _ => invSqKer_nonneg _

/-- Pointwise positivity does not require identifying a complete budget run. -/
theorem completeNestedRunDensityWithCrossCutoff_nonneg
    (terminal : R324TwoHalfTerminalData
      rho lam eps kappaPlus kappaMinus)
    (sigma : SmoothCutoff)
    {pi : kappaPlus.singles ≃ kappaMinus.singles}
    (step : R324NestedCrossStepContext kappaPlus kappaMinus pi)
    (hleft : (r324LeftHalfPullback
      step.residual.activeCarrier).Nonempty)
    (hright : (r324RightHalfPullback
      step.residual.activeCarrier).Nonempty)
    (v : step.SurvivingCoordinate → T4) :
    0 ≤ terminal.completeNestedRunDensityWithCrossCutoff
      sigma step hleft hright v := by
  unfold completeNestedRunDensityWithCrossCutoff
  exact mul_nonneg
    ((even_two_mul step.residual.remainingOrder).pow_nonneg _)
    (mul_nonneg
      (mul_nonneg
        (nestedLeftHalfInvSqProduct_nonneg_mixed
          terminal step step.residual.activeCarrier hleft v)
        (nestedRightHalfInvSqProduct_nonneg_mixed
          terminal step step.residual.activeCarrier hright v))
      (nestedResidualPrimitiveSumProduct_nonneg_mixed
        sigma eps kappaPlus kappaMinus pi step.residual
          (step.reconstruct v)))

end R324TwoHalfTerminalData

namespace R324NestedCrossProperStepContext

variable {m : Nat} {kappaPlus kappaMinus : PartialPairing (Fin m)}
    {pi : kappaPlus.singles ≃ kappaMinus.singles}

private theorem nestedResidualPrimitiveSumProduct_next_reconstruct_eq_mixed
    (ctx : R324NestedCrossProperStepContext
      kappaPlus kappaMinus pi)
    (sigma : SmoothCutoff) (eps : Real)
    (v : ctx.step.SurvivingCoordinate → T4) :
    r324NestedResidualPrimitiveSumProduct
        sigma eps kappaPlus kappaMinus pi ctx.step.next
          (ctx.step.reconstruct v) =
      r324NestedResidualPrimitiveSumProduct
        sigma eps kappaPlus kappaMinus pi ctx.step.next
          (ctx.nextContext.reconstruct
            (ctx.step.splitSurvivingPiMeasurableEquiv v).2) := by
  exact ctx.nestedResidualPrimitiveSumProduct_next_reconstruct_eq
    sigma eps v

end R324NestedCrossProperStepContext

namespace R324TwoHalfTerminalData

variable {rho sigma : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaPlus kappaMinus : PartialPairing (Fin m)}
    {pi : kappaPlus.singles ≃ kappaMinus.singles}

private theorem finalHeadBlockSum_reconstruct_eq_completePairingSum_mixed
    (step : R324NestedCrossStepContext kappaPlus kappaMinus pi)
    (v : step.SurvivingCoordinate → T4) :
    r324PrimitivePartitionBlockSum
        sigma eps kappaPlus kappaMinus pi step.head.carrier
          (step.reconstruct v) =
      ∑ pairing ∈ primitiveFullPairings step.order,
        primitiveCovarianceProduct sigma eps step.order pairing
          (step.splitSurvivingPiMeasurableEquiv v).1 := by
  let t := (step.splitSurvivingPiMeasurableEquiv v).1
  let post := (step.splitSurvivingPiMeasurableEquiv v).2
  have h := step.r324PrimitivePartitionBlockSum_head_reconstruct_split
    sigma eps t post
  have hv : step.splitSurvivingPiMeasurableEquiv.symm (t, post) = v :=
    step.splitSurvivingPiMeasurableEquiv.symm_apply_apply v
  rw [hv, step.sum_r324PrimitiveCoordinate_covariance_eq] at h
  exact h

private theorem headBlockSum_reconstruct_eq_completePairingSum_mixed
    (ctx : R324NestedCrossProperStepContext
      kappaPlus kappaMinus pi)
    (v : ctx.step.SurvivingCoordinate → T4) :
    r324PrimitivePartitionBlockSum
        sigma eps kappaPlus kappaMinus pi ctx.step.head.carrier
          (ctx.step.reconstruct v) =
      ∑ pairing ∈ primitiveFullPairings ctx.step.order,
        primitiveCovarianceProduct sigma eps ctx.step.order pairing
          (ctx.step.splitSurvivingPiMeasurableEquiv v).1 := by
  let t := (ctx.step.splitSurvivingPiMeasurableEquiv v).1
  let post := (ctx.step.splitSurvivingPiMeasurableEquiv v).2
  have h := ctx.step.r324PrimitivePartitionBlockSum_head_reconstruct_split
    sigma eps t post
  have hv :
      ctx.step.splitSurvivingPiMeasurableEquiv.symm (t, post) = v :=
    ctx.step.splitSurvivingPiMeasurableEquiv.symm_apply_apply v
  rw [hv, ctx.step.sum_r324PrimitiveCoordinate_covariance_eq] at h
  exact h

private theorem ae_headHalfPaths_mul_completeCrossGap_one_eq_completeNormalized_mixed
    (terminal : R324TwoHalfTerminalData
      rho lam eps kappaPlus kappaMinus)
    (sigma : SmoothCutoff)
    (ctx : R324NestedCrossProperStepContext
      kappaPlus kappaMinus pi) :
    ∀ᵐ v : ctx.step.SurvivingCoordinate → T4
        ∂(Measure.pi fun _ => paperMeasure),
      lamEps lam eps ^ (2 * ctx.step.order) *
          ((terminal.nestedLeftHalfInvSqProduct ctx.step
                ctx.step.head.carrier ctx.leftHead_nonempty v *
              terminal.nestedRightHalfInvSqProduct ctx.step
                ctx.step.head.carrier ctx.rightHead_nonempty v) *
            (∑ pairing ∈ primitiveFullPairings ctx.step.order,
              primitiveCovarianceProduct sigma eps ctx.step.order pairing
                (ctx.step.splitSurvivingPiMeasurableEquiv v).1)) =
        ctx.step.completeNormalizedHeadDensity sigma lam eps
          (ctx.step.splitSurvivingPiMeasurableEquiv v).1 := by
  filter_upwards
      [ctx.step.ae_centralGapCancellation_reconstruct_eq_one]
    with v hcancel
  let t := (ctx.step.splitSurvivingPiMeasurableEquiv v).1
  have hleftCoordinate :
      ctx.step.reconstruct v ctx.step.head.leftGap =
        t ctx.step.leftGapIndex := by
    dsimp only [t]
    rw [ctx.step.splitSurvivingPiMeasurableEquiv_apply_fst]
    have hval :
        (ctx.step.headSurvivingCoordinate ctx.step.leftGapIndex).1 =
          ctx.step.head.leftGap :=
      congrArg Subtype.val ctx.step.blockOrderIso_leftGapIndex
    rw [← hval, ctx.step.reconstruct_surviving]
  have hrightCoordinate :
      ctx.step.reconstruct v ctx.step.head.rightGap =
        t ctx.step.rightGapIndex := by
    dsimp only [t]
    rw [ctx.step.splitSurvivingPiMeasurableEquiv_apply_fst]
    have hval :
        (ctx.step.headSurvivingCoordinate ctx.step.rightGapIndex).1 =
          ctx.step.head.rightGap :=
      congrArg Subtype.val ctx.step.blockOrderIso_rightGapIndex
    rw [← hval, ctx.step.reconstruct_surviving]
  have hgap :
      torusDistSq
          (t ctx.step.leftGapIndex - t ctx.step.rightGapIndex) *
        invSqKer
          (t ctx.step.leftGapIndex - t ctx.step.rightGapIndex) = 1 := by
    unfold R324NestedCrossBlock.centralGapNumerator at hcancel
    rw [hleftCoordinate, hrightCoordinate] at hcancel
    exact hcancel
  rw [terminal.nestedLeftHalfInvSqProduct_head_eq_primitiveEdges ctx v,
    terminal.nestedRightHalfInvSqProduct_head_eq_primitiveEdges ctx v]
  unfold R324NestedCrossStepContext.completeNormalizedHeadDensity
  rw [ctx.step.completeCrossGapPrimitiveIntegrand_eq,
    ctx.primitiveChainProduct_normalized_eq_left_central_right]
  change
    lamEps lam eps ^ (2 * ctx.step.order) *
          (((∏ j ∈ ctx.leftPrimitiveEdgeIndices,
              invSqKer
                (t (primitiveEdgeLeft
                    ctx.step.order ctx.step.one_le_order j) -
                  t (primitiveEdgeRight
                    ctx.step.order ctx.step.one_le_order j))) *
            (∏ j ∈ ctx.rightPrimitiveEdgeIndices,
              invSqKer
                (t (primitiveEdgeLeft
                    ctx.step.order ctx.step.one_le_order j) -
                  t (primitiveEdgeRight
                    ctx.step.order ctx.step.one_le_order j)))) *
          (∑ pairing ∈ primitiveFullPairings ctx.step.order,
            primitiveCovarianceProduct sigma eps ctx.step.order pairing t)) = _
  calc
    _ = lamEps lam eps ^ (2 * ctx.step.order) *
        ((torusDistSq
              (t ctx.step.leftGapIndex - t ctx.step.rightGapIndex) *
            invSqKer
              (t ctx.step.leftGapIndex - t ctx.step.rightGapIndex)) *
          (((∏ j ∈ ctx.leftPrimitiveEdgeIndices,
                invSqKer
                  (t (primitiveEdgeLeft
                      ctx.step.order ctx.step.one_le_order j) -
                    t (primitiveEdgeRight
                      ctx.step.order ctx.step.one_le_order j))) *
              (∏ j ∈ ctx.rightPrimitiveEdgeIndices,
                invSqKer
                  (t (primitiveEdgeLeft
                      ctx.step.order ctx.step.one_le_order j) -
                    t (primitiveEdgeRight
                      ctx.step.order ctx.step.one_le_order j)))) *
            (∑ pairing ∈ primitiveFullPairings ctx.step.order,
              primitiveCovarianceProduct sigma eps ctx.step.order pairing t))) := by
          rw [hgap]
          ring
    _ = _ := by ring

private theorem ae_finalHeadHalfPaths_mul_completeCrossGap_one_eq_completeNormalized_mixed
    (terminal : R324TwoHalfTerminalData
      rho lam eps kappaPlus kappaMinus)
    (sigma : SmoothCutoff)
    (step : R324NestedCrossStepContext kappaPlus kappaMinus pi)
    (htail : step.tail = []) :
    ∀ᵐ v : step.SurvivingCoordinate → T4
        ∂(Measure.pi fun _ => paperMeasure),
      lamEps lam eps ^ (2 * step.order) *
          ((terminal.nestedLeftHalfInvSqProduct step
                step.head.carrier step.finalLeftHeadNonempty v *
              terminal.nestedRightHalfInvSqProduct step
                step.head.carrier step.finalRightHeadNonempty v) *
            (∑ pairing ∈ primitiveFullPairings step.order,
              primitiveCovarianceProduct sigma eps step.order pairing
                (step.splitSurvivingPiMeasurableEquiv v).1)) =
        step.completeNormalizedHeadDensity sigma lam eps
          (step.splitSurvivingPiMeasurableEquiv v).1 := by
  filter_upwards [step.ae_centralGapCancellation_reconstruct_eq_one]
    with v hcancel
  let t := (step.splitSurvivingPiMeasurableEquiv v).1
  have hleftCoordinate :
      step.reconstruct v step.head.leftGap =
        t step.leftGapIndex := by
    dsimp only [t]
    rw [step.splitSurvivingPiMeasurableEquiv_apply_fst]
    have hval :
        (step.headSurvivingCoordinate step.leftGapIndex).1 =
          step.head.leftGap :=
      congrArg Subtype.val step.blockOrderIso_leftGapIndex
    rw [← hval, step.reconstruct_surviving]
  have hrightCoordinate :
      step.reconstruct v step.head.rightGap =
        t step.rightGapIndex := by
    dsimp only [t]
    rw [step.splitSurvivingPiMeasurableEquiv_apply_fst]
    have hval :
        (step.headSurvivingCoordinate step.rightGapIndex).1 =
          step.head.rightGap :=
      congrArg Subtype.val step.blockOrderIso_rightGapIndex
    rw [← hval, step.reconstruct_surviving]
  have hgap :
      torusDistSq (t step.leftGapIndex - t step.rightGapIndex) *
        invSqKer (t step.leftGapIndex - t step.rightGapIndex) = 1 := by
    unfold R324NestedCrossBlock.centralGapNumerator at hcancel
    rw [hleftCoordinate, hrightCoordinate] at hcancel
    exact hcancel
  rw [terminal.nestedLeftHalfInvSqProduct_finalHead_eq_primitiveEdges
      step htail v,
    terminal.nestedRightHalfInvSqProduct_finalHead_eq_primitiveEdges
      step htail v]
  unfold R324NestedCrossStepContext.completeNormalizedHeadDensity
  rw [step.completeCrossGapPrimitiveIntegrand_eq,
    step.primitiveChainProduct_normalized_eq_finalParts]
  change
    lamEps lam eps ^ (2 * step.order) *
          (((∏ j ∈ step.finalLeftPrimitiveEdgeIndices,
              invSqKer
                (t (primitiveEdgeLeft step.order step.one_le_order j) -
                  t (primitiveEdgeRight step.order step.one_le_order j))) *
            (∏ j ∈ step.finalRightPrimitiveEdgeIndices,
              invSqKer
                (t (primitiveEdgeLeft step.order step.one_le_order j) -
                  t (primitiveEdgeRight step.order step.one_le_order j)))) *
          (∑ pairing ∈ primitiveFullPairings step.order,
            primitiveCovarianceProduct sigma eps step.order pairing t)) = _
  calc
    _ = lamEps lam eps ^ (2 * step.order) *
        ((torusDistSq
              (t step.leftGapIndex - t step.rightGapIndex) *
            invSqKer
              (t step.leftGapIndex - t step.rightGapIndex)) *
          (((∏ j ∈ step.finalLeftPrimitiveEdgeIndices,
                invSqKer
                  (t (primitiveEdgeLeft step.order step.one_le_order j) -
                    t (primitiveEdgeRight step.order step.one_le_order j))) *
              (∏ j ∈ step.finalRightPrimitiveEdgeIndices,
                invSqKer
                  (t (primitiveEdgeLeft step.order step.one_le_order j) -
                    t (primitiveEdgeRight step.order step.one_le_order j)))) *
            (∑ pairing ∈ primitiveFullPairings step.order,
              primitiveCovarianceProduct sigma eps step.order pairing t))) := by
          rw [hgap]
          ring
    _ = _ := by ring

/-- One proper shell of the mixed-cutoff run.  The terminal chains are
geometric; only the complete grouped primitive head changes to `sigma`. -/
theorem ae_completeNestedRunDensityWithCrossCutoff_eq_head_connector_next
    (terminal : R324TwoHalfTerminalData
      rho lam eps kappaPlus kappaMinus)
    (sigma : SmoothCutoff)
    (ctx : R324NestedCrossProperStepContext
      kappaPlus kappaMinus pi) :
    terminal.completeNestedRunDensityWithCrossCutoff sigma ctx.step
        ctx.leftCurrent_nonempty ctx.rightCurrent_nonempty =ᵐ[
      Measure.pi fun _ : ctx.step.SurvivingCoordinate => paperMeasure]
      fun v =>
        ctx.step.completeNormalizedHeadDensity sigma lam eps
            (ctx.step.splitSurvivingPiMeasurableEquiv v).1 *
          ctx.connector
            (ctx.step.splitSurvivingPiMeasurableEquiv v).1
            (ctx.step.splitSurvivingPiMeasurableEquiv v).2 *
          terminal.completeNestedRunDensityWithCrossCutoff
            sigma ctx.nextContext ctx.leftPost_nonempty
              ctx.rightPost_nonempty
            (fun i : ctx.nextContext.SurvivingCoordinate =>
              (ctx.step.splitSurvivingPiMeasurableEquiv v).2
                ⟨i.1, i.2⟩) := by
  filter_upwards
      [ae_headHalfPaths_mul_completeCrossGap_one_eq_completeNormalized_mixed
        terminal sigma ctx]
    with v hhead
  have hhalf :=
    terminal.nestedHalfInvSqProducts_current_eq_head_connector_post_named
      ctx v
  have hleftPost := terminal.nestedLeftHalfInvSqProduct_post_eq_next ctx v
  have hrightPost := terminal.nestedRightHalfInvSqProduct_post_eq_next ctx v
  have hcovHead := headBlockSum_reconstruct_eq_completePairingSum_mixed
    (sigma := sigma) (eps := eps) ctx v
  have hcovSplit := r324NestedResidualPrimitiveSumProduct_head
    sigma eps ctx.step (ctx.step.reconstruct v)
  have hcovPost :=
    ctx.nestedResidualPrimitiveSumProduct_next_reconstruct_eq_mixed
      sigma eps v
  have horder := ctx.step.remainingOrder_eq_order_add_next
  have hpostEq :
      (fun i : ctx.nextContext.SurvivingCoordinate =>
        (ctx.step.splitSurvivingPiMeasurableEquiv v).2 ⟨i.1, i.2⟩) =
        (ctx.step.splitSurvivingPiMeasurableEquiv v).2 := by
    funext i
    congr 1
  unfold completeNestedRunDensityWithCrossCutoff
  rw [hhalf, hcovSplit, hcovHead, hleftPost, hrightPost, hcovPost,
    horder]
  rw [show 2 * (ctx.step.order + ctx.step.next.remainingOrder) =
      2 * ctx.step.order + 2 * ctx.step.next.remainingOrder by omega,
    pow_add]
  rw [← hhead]
  rw [hpostEq]
  dsimp only [R324NestedCrossProperStepContext.nextContext]
  ring

/-- At the final shell, the mixed density is the complete `sigma` head
pulled back to the surviving coordinates. -/
theorem ae_completeNestedRunDensityWithCrossCutoff_eq_completeHeadPullback_of_tail_eq_nil
    (terminal : R324TwoHalfTerminalData
      rho lam eps kappaPlus kappaMinus)
    (sigma : SmoothCutoff)
    (step : R324NestedCrossStepContext kappaPlus kappaMinus pi)
    (htail : step.tail = [])
    (hleft : (r324LeftHalfPullback
      step.residual.activeCarrier).Nonempty)
    (hright : (r324RightHalfPullback
      step.residual.activeCarrier).Nonempty) :
    terminal.completeNestedRunDensityWithCrossCutoff
        sigma step hleft hright =ᵐ[
      Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure]
      step.completeHeadPullbackDensity sigma lam eps := by
  have hremaining : step.residual.remaining = [step.head] := by
    rw [step.remaining_eq, htail]
  have hactive : step.residual.activeCarrier = step.head.carrier := by
    unfold R324NestedCrossResidualPrefix.activeCarrier
    rw [hremaining]
    simp [finsetUnionList]
  have horder : step.residual.remainingOrder = step.order := by
    unfold R324NestedCrossResidualPrefix.remainingOrder
      R324NestedCrossStepContext.order
    rw [hremaining]
    simp
  filter_upwards
      [ae_finalHeadHalfPaths_mul_completeCrossGap_one_eq_completeNormalized_mixed
        terminal sigma step htail]
    with v hhead
  have hcov :
      r324NestedResidualPrimitiveSumProduct
          sigma eps kappaPlus kappaMinus pi step.residual
            (step.reconstruct v) =
        ∑ pairing ∈ primitiveFullPairings step.order,
          primitiveCovarianceProduct sigma eps step.order pairing
            (step.splitSurvivingPiMeasurableEquiv v).1 := by
    unfold r324NestedResidualPrimitiveSumProduct
    rw [hremaining]
    simp only [List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    exact finalHeadBlockSum_reconstruct_eq_completePairingSum_mixed
      (sigma := sigma) (eps := eps) step v
  unfold completeNestedRunDensityWithCrossCutoff
    R324NestedCrossStepContext.completeHeadPullbackDensity
  rw [horder, hcov]
  have hleftPath :
      terminal.nestedLeftHalfInvSqProduct step
          step.residual.activeCarrier hleft v =
        terminal.nestedLeftHalfInvSqProduct step
          step.head.carrier step.finalLeftHeadNonempty v := by
    simp only [hactive]
  have hrightPath :
      terminal.nestedRightHalfInvSqProduct step
          step.residual.activeCarrier hright v =
        terminal.nestedRightHalfInvSqProduct step
          step.head.carrier step.finalRightHeadNonempty v := by
    simp only [hactive]
  rw [hleftPath, hrightPath]
  exact hhead

/-- Integrability of the mixed run follows by the same literal shell
recursion as the original run, with the proper-head provider chosen from
`sigma`. -/
theorem integrable_completeNestedRunDensityWithCrossCutoff_at_truncation
    (terminal : R324TwoHalfTerminalData
      rho lam eps kappaPlus kappaMinus)
    (sigma : SmoothCutoff)
    (hlam : 0 < lam) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hlog : 1 ≤ |Real.log eps|)
    (hmtrunc : m ≤ truncOrder eps)
    (step : R324NestedCrossStepContext kappaPlus kappaMinus pi)
    (hleft : (r324LeftHalfPullback
      step.residual.activeCarrier).Nonempty)
    (hright : (r324RightHalfPullback
      step.residual.activeCarrier).Nonempty) :
    Integrable
      (terminal.completeNestedRunDensityWithCrossCutoff
        sigma step hleft hright)
      (Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) := by
  cases htail : step.tail with
  | nil =>
      have hid :=
        terminal.ae_completeNestedRunDensityWithCrossCutoff_eq_completeHeadPullback_of_tail_eq_nil
          sigma step htail hleft hright
      exact
        (step.integrable_completeHeadPullbackDensity_at_truncation
          sigma lam eps hlam heps heps1 hmtrunc).congr hid.symm
  | cons nextHead rest =>
      let proper : R324NestedCrossProperStepContext
          kappaPlus kappaMinus pi :=
        { step := step
          nextHead := nextHead
          rest := rest
          tail_eq := htail }
      have hnext :=
        integrable_completeNestedRunDensityWithCrossCutoff_at_truncation
          terminal sigma hlam heps heps1 hlog hmtrunc proper.nextContext
            proper.leftPost_nonempty proper.rightPost_nonempty
      let nextDensity :=
        terminal.completeNestedRunDensityWithCrossCutoff
          sigma proper.nextContext proper.leftPost_nonempty
            proper.rightPost_nonempty
      let currentDensity := fun v : step.SurvivingCoordinate → T4 =>
        step.completeNormalizedHeadDensity sigma lam eps
            (fun j => v (step.headSurvivingCoordinate j)) *
          proper.connector
            (fun j => v (step.headSurvivingCoordinate j))
            (fun i => v (step.postSurvivingCoordinate i)) *
          nextDensity (fun i => v (step.postSurvivingCoordinate i))
      have hcurrent : Integrable currentDensity
          (Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) := by
        dsimp only [currentDensity, nextDensity]
        exact proper.integrable_completeProperDensity_at_truncation
          sigma lam eps hlam heps heps1 hlog hmtrunc _ hnext
      have hlayer :=
        terminal.ae_completeNestedRunDensityWithCrossCutoff_eq_head_connector_next
          sigma proper
      have hidentified :
          terminal.completeNestedRunDensityWithCrossCutoff
              sigma step hleft hright =ᵐ[
            Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure]
            currentDensity := by
        filter_upwards [hlayer] with v hv
        have hheadTuple :
            (step.splitSurvivingPiMeasurableEquiv v).1 =
              fun j => v (step.headSurvivingCoordinate j) := by
          funext j
          exact step.splitSurvivingPiMeasurableEquiv_apply_fst v j
        have hpostTuple :
            (step.splitSurvivingPiMeasurableEquiv v).2 =
              fun i => v (step.postSurvivingCoordinate i) := by
          funext i
          exact step.splitSurvivingPiMeasurableEquiv_apply_snd v i
        have hchildTuple :
            (fun i : proper.nextContext.SurvivingCoordinate =>
              (step.splitSurvivingPiMeasurableEquiv v).2 ⟨i.1, i.2⟩) =
              (step.splitSurvivingPiMeasurableEquiv v).2 := by
          funext i
          congr 1
        rw [hv]
        dsimp only [currentDensity, nextDensity]
        rw [hchildTuple, hpostTuple, hheadTuple]
        rfl
      exact hcurrent.congr hidentified.symm
termination_by step.tail.length
decreasing_by
  rw [htail]
  simp [R324NestedCrossProperStepContext.nextContext]

/-- Quantitative shell removal for the mixed-cutoff density. -/
theorem exists_prefix_terminal_integral_completeNestedRunDensityWithCrossCutoff_le
    (terminal : R324TwoHalfTerminalData
      rho lam eps kappaPlus kappaMinus)
    (sigma : SmoothCutoff) {D : Real}
    (hlam : 0 < lam) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hlog : 1 ≤ |Real.log eps|)
    (hmtrunc : m ≤ truncOrder eps)
    (provider : R324CompleteProperHeadSharpProvider
      sigma lam eps D kappaPlus kappaMinus pi)
    (step : R324NestedCrossStepContext kappaPlus kappaMinus pi)
    (hleft : (r324LeftHalfPullback
      step.residual.activeCarrier).Nonempty)
    (hright : (r324RightHalfPullback
      step.residual.activeCarrier).Nonempty) :
    ∃ prefixOrder terminalOrder : Nat,
      ∃ finalStep : R324NestedCrossStepContext
          kappaPlus kappaMinus pi,
        step.residual.remainingOrder = prefixOrder + terminalOrder ∧
        terminalOrder = finalStep.order ∧
        (∫ v,
            terminal.completeNestedRunDensityWithCrossCutoff
              sigma step hleft hright v
            ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) ≤
          (D * lam) ^ (2 * prefixOrder) *
            ∫ t, finalStep.completeNormalizedHeadDensity sigma lam eps t
              ∂Measure.pi fun _ : Fin (2 * finalStep.order) =>
                paperMeasure := by
  cases htail : step.tail with
  | nil =>
      have hremaining : step.residual.remaining = [step.head] := by
        rw [step.remaining_eq, htail]
      have horder : step.residual.remainingOrder = step.order := by
        unfold R324NestedCrossResidualPrefix.remainingOrder
          R324NestedCrossStepContext.order
        rw [hremaining]
        simp
      refine ⟨0, step.order, step, ?_, rfl, ?_⟩
      · simpa only [zero_add] using horder
      · have hidentified :=
          terminal.ae_completeNestedRunDensityWithCrossCutoff_eq_completeHeadPullback_of_tail_eq_nil
            sigma step htail hleft hright
        calc
          (∫ v,
              terminal.completeNestedRunDensityWithCrossCutoff
                sigma step hleft hright v
              ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) =
              ∫ v, step.completeHeadPullbackDensity sigma lam eps v
                ∂Measure.pi fun _ : step.SurvivingCoordinate =>
                  paperMeasure :=
            integral_congr_ae hidentified
          _ = ∫ t, step.completeNormalizedHeadDensity sigma lam eps t
                ∂Measure.pi fun _ : Fin (2 * step.order) => paperMeasure :=
            step.integral_completeHeadPullbackDensity_eq_of_tail_eq_nil
              sigma lam eps htail
          _ = (D * lam) ^ (2 * 0) *
                ∫ t, step.completeNormalizedHeadDensity sigma lam eps t
                  ∂Measure.pi fun _ : Fin (2 * step.order) =>
                    paperMeasure := by simp
          _ ≤ _ := le_rfl
  | cons nextHead rest =>
      let proper : R324NestedCrossProperStepContext
          kappaPlus kappaMinus pi :=
        { step := step
          nextHead := nextHead
          rest := rest
          tail_eq := htail }
      have hnextIntegrable :=
        terminal.integrable_completeNestedRunDensityWithCrossCutoff_at_truncation
          sigma hlam heps heps1 hlog hmtrunc proper.nextContext
            proper.leftPost_nonempty proper.rightPost_nonempty
      have hnextNonneg :
          ∀ᵐ v ∂Measure.pi fun _ : proper.nextContext.SurvivingCoordinate =>
              paperMeasure,
            0 ≤ terminal.completeNestedRunDensityWithCrossCutoff
              sigma proper.nextContext proper.leftPost_nonempty
                proper.rightPost_nonempty v :=
        Filter.Eventually.of_forall fun v =>
          terminal.completeNestedRunDensityWithCrossCutoff_nonneg
            sigma proper.nextContext proper.leftPost_nonempty
              proper.rightPost_nonempty v
      obtain ⟨nextPrefixOrder, terminalOrder, finalStep,
          hnextOrder, hterminalOrder, hnextBound⟩ :=
        exists_prefix_terminal_integral_completeNestedRunDensityWithCrossCutoff_le
          terminal sigma hlam heps heps1 hlog hmtrunc provider
            proper.nextContext proper.leftPost_nonempty
              proper.rightPost_nonempty
      let nextDensity :=
        terminal.completeNestedRunDensityWithCrossCutoff
          sigma proper.nextContext proper.leftPost_nonempty
            proper.rightPost_nonempty
      let currentDensity := fun v : step.SurvivingCoordinate → T4 =>
        step.completeNormalizedHeadDensity sigma lam eps
              (fun j => v (step.headSurvivingCoordinate j)) *
            proper.connector
              (fun j => v (step.headSurvivingCoordinate j))
              (fun i => v (step.postSurvivingCoordinate i)) *
            nextDensity (fun i => v (step.postSurvivingCoordinate i))
      have hcurrentIntegrable : Integrable currentDensity
          (Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) := by
        dsimp only [currentDensity, nextDensity]
        exact proper.integrable_completeProperDensity_at_truncation
          sigma lam eps hlam heps heps1 hlog hmtrunc _ hnextIntegrable
      have hlayer :=
        terminal.ae_completeNestedRunDensityWithCrossCutoff_eq_head_connector_next
          sigma proper
      have hidentified :
          terminal.completeNestedRunDensityWithCrossCutoff
              sigma step hleft hright =ᵐ[
            Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure]
            currentDensity := by
        filter_upwards [hlayer] with v hv
        have hheadTuple :
            (step.splitSurvivingPiMeasurableEquiv v).1 =
              fun j => v (step.headSurvivingCoordinate j) := by
          funext j
          exact step.splitSurvivingPiMeasurableEquiv_apply_fst v j
        have hpostTuple :
            (step.splitSurvivingPiMeasurableEquiv v).2 =
              fun i => v (step.postSurvivingCoordinate i) := by
          funext i
          exact step.splitSurvivingPiMeasurableEquiv_apply_snd v i
        have hchildTuple :
            (fun i : proper.nextContext.SurvivingCoordinate =>
              (step.splitSurvivingPiMeasurableEquiv v).2 ⟨i.1, i.2⟩) =
              (step.splitSurvivingPiMeasurableEquiv v).2 := by
          funext i
          congr 1
        rw [hv]
        dsimp only [currentDensity, nextDensity]
        rw [hchildTuple, hpostTuple, hheadTuple]
        rfl
      have hexact :=
        R324CompleteNestedCrossBudgetRun.integral_completeProperDensity_of_current_integrable
          proper nextDensity heps heps1 hcurrentIntegrable
      let A : Real := (D * lam) ^ (2 * step.order)
      have hA : 0 ≤ A := by
        dsimp only [A]
        exact (even_two_mul step.order).pow_nonneg _
      have htargetIntegrable : Integrable
          (fun post : step.PostCoordinate → T4 => A * nextDensity post)
          (Measure.pi fun _ => paperMeasure) :=
        hnextIntegrable.const_mul A
      have houterNonneg :
          ∀ᵐ post ∂Measure.pi fun _ : step.PostCoordinate => paperMeasure,
            0 ≤ proper.completeProperHeadIntegral sigma lam eps
                (post proper.nextLeftPostCoordinate)
                (post proper.nextRightPostCoordinate) * nextDensity post := by
        filter_upwards [hnextNonneg] with post hpost
        exact mul_nonneg
          (proper.completeProperHeadIntegral_nonneg sigma lam eps _ _)
          hpost
      have houterLe :
          (∫ post : step.PostCoordinate → T4,
              proper.completeProperHeadIntegral sigma lam eps
                  (post proper.nextLeftPostCoordinate)
                  (post proper.nextRightPostCoordinate) * nextDensity post
              ∂Measure.pi fun _ => paperMeasure) ≤
            A * ∫ post : step.PostCoordinate → T4, nextDensity post
              ∂Measure.pi fun _ => paperMeasure := by
        calc
          _ ≤ ∫ post : step.PostCoordinate → T4, A * nextDensity post
                ∂Measure.pi fun _ => paperMeasure := by
              apply integral_mono_of_nonneg houterNonneg htargetIntegrable
              filter_upwards [hnextNonneg] with post hpost
              exact mul_le_mul_of_nonneg_right
                (provider.headIntegral_le proper
                  (post proper.nextLeftPostCoordinate)
                  (post proper.nextRightPostCoordinate)) hpost
          _ = A * ∫ post : step.PostCoordinate → T4, nextDensity post
                ∂Measure.pi fun _ => paperMeasure := by
              rw [integral_const_mul]
      have hnextOrder' :
          step.next.remainingOrder =
            nextPrefixOrder + terminalOrder := by
        simpa only [proper,
          R324NestedCrossProperStepContext.nextContext] using hnextOrder
      refine ⟨step.order + nextPrefixOrder, terminalOrder, finalStep,
        ?_, hterminalOrder, ?_⟩
      · rw [step.remainingOrder_eq_order_add_next, hnextOrder']
        omega
      · calc
          (∫ v,
              terminal.completeNestedRunDensityWithCrossCutoff
                sigma step hleft hright v
              ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) =
              ∫ v, currentDensity v
                ∂Measure.pi fun _ : step.SurvivingCoordinate =>
                  paperMeasure := integral_congr_ae hidentified
          _ = ∫ post : step.PostCoordinate → T4,
                proper.completeProperHeadIntegral sigma lam eps
                    (post proper.nextLeftPostCoordinate)
                    (post proper.nextRightPostCoordinate) * nextDensity post
                ∂Measure.pi fun _ => paperMeasure := hexact
          _ ≤ A * ∫ post : step.PostCoordinate → T4, nextDensity post
                ∂Measure.pi fun _ => paperMeasure := houterLe
          _ ≤ A * ((D * lam) ^ (2 * nextPrefixOrder) *
                ∫ t, finalStep.completeNormalizedHeadDensity
                    sigma lam eps t
                  ∂Measure.pi fun _ : Fin (2 * finalStep.order) =>
                    paperMeasure) :=
            mul_le_mul_of_nonneg_left hnextBound hA
          _ = (D * lam) ^ (2 * (step.order + nextPrefixOrder)) *
                ∫ t, finalStep.completeNormalizedHeadDensity
                    sigma lam eps t
                  ∂Measure.pi fun _ : Fin (2 * finalStep.order) =>
                    paperMeasure := by
            dsimp only [A]
            rw [show 2 * (step.order + nextPrefixOrder) =
                2 * step.order + 2 * nextPrefixOrder by omega, pow_add]
            ring
termination_by step.tail.length
decreasing_by
  rw [htail]
  simp [R324NestedCrossProperStepContext.nextContext]

/-- Uniform mixed-cutoff closure.  The constants depend only on the
analytic cross cutoff `sigma`; the terminal half geometry may come from an
arbitrary original cutoff `rho`. -/
theorem exists_integral_completeNestedRunDensityWithCrossCutoff_le_primitiveInsertedMajorant
    (sigma : SmoothCutoff) :
    ∃ supportConstant C : Real,
      0 < supportConstant ∧ 0 < C ∧
      ∀ {rho : SmoothCutoff} {lam eps : Real} {m : Nat}
        {kappaPlus kappaMinus : PartialPairing (Fin m)}
        {pi : kappaPlus.singles ≃ kappaMinus.singles}
        (terminal : R324TwoHalfTerminalData
          rho lam eps kappaPlus kappaMinus),
        0 < lam → 0 < eps → eps ≤ 1 →
        1 ≤ |Real.log eps| → m ≤ truncOrder eps →
        ∀ (step : R324NestedCrossStepContext
            kappaPlus kappaMinus pi)
          (hleft : (r324LeftHalfPullback
            step.residual.activeCarrier).Nonempty)
          (hright : (r324RightHalfPullback
            step.residual.activeCarrier).Nonempty),
          (∫ v,
              terminal.completeNestedRunDensityWithCrossCutoff
                sigma step hleft hright v
              ∂Measure.pi fun _ : step.SurvivingCoordinate =>
                paperMeasure) ≤
            ∫ z, primitiveInsertedMajorant
              C lam eps supportConstant step.residual.remainingOrder z
              ∂paperMeasure := by
  obtain ⟨D, hD, hprovider⟩ :=
    exists_r324CompleteProperHeadSharpProvider sigma
  obtain ⟨supportConstant, terminalC, hsupport, hterminalC,
      hterminal⟩ :=
    R324NestedCrossStepContext.exists_completeTerminalHead_bound_at_truncation
      sigma
  refine ⟨supportConstant, r324CompleteAbsorbedBase D terminalC,
    hsupport, r324CompleteAbsorbedBase_pos D terminalC, ?_⟩
  intro rho lam eps m kappaPlus kappaMinus pi terminal
    hlam heps heps1 hlog hmtrunc step hleft hright
  have provider : R324CompleteProperHeadSharpProvider
      sigma lam eps D kappaPlus kappaMinus pi :=
    hprovider lam eps pi hlam heps heps1 hlog hmtrunc
  obtain ⟨prefixOrder, terminalOrder, finalStep,
      htotalOrder, hterminalOrder, hprefix⟩ :=
    terminal.exists_prefix_terminal_integral_completeNestedRunDensityWithCrossCutoff_le
      sigma hlam heps heps1 hlog hmtrunc provider step hleft hright
  have hfinal := hterminal kappaPlus kappaMinus pi finalStep lam eps
    hlam heps heps1 hmtrunc
  have hfinal' :
      (∫ t, finalStep.completeNormalizedHeadDensity sigma lam eps t
          ∂Measure.pi fun _ : Fin (2 * finalStep.order) => paperMeasure) ≤
        (2 * Real.pi) ^ (dim : Nat) *
          ∫ z, primitiveInsertedMajorant
            terminalC lam eps supportConstant terminalOrder z
            ∂paperMeasure := by
    simpa only [hterminalOrder] using hfinal
  have hprefixNonneg :
      0 ≤ (D * lam) ^ (2 * prefixOrder) :=
    (even_two_mul prefixOrder).pow_nonneg _
  have hone : 1 ≤ prefixOrder + terminalOrder := by
    have hstepOrder : 1 ≤ step.order := step.one_le_order
    rw [← htotalOrder, step.remainingOrder_eq_order_add_next]
    omega
  calc
    (∫ v,
        terminal.completeNestedRunDensityWithCrossCutoff
          sigma step hleft hright v
        ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) ≤
        (D * lam) ^ (2 * prefixOrder) *
          ∫ t, finalStep.completeNormalizedHeadDensity sigma lam eps t
            ∂Measure.pi fun _ : Fin (2 * finalStep.order) => paperMeasure :=
      hprefix
    _ ≤ (D * lam) ^ (2 * prefixOrder) *
          ((2 * Real.pi) ^ (dim : Nat) *
            ∫ z, primitiveInsertedMajorant
              terminalC lam eps supportConstant terminalOrder z
              ∂paperMeasure) :=
      mul_le_mul_of_nonneg_left hfinal' hprefixNonneg
    _ ≤ ∫ z, primitiveInsertedMajorant
          (r324CompleteAbsorbedBase D terminalC)
            lam eps supportConstant (prefixOrder + terminalOrder) z
          ∂paperMeasure :=
      r324_complete_prefix_mul_terminalIntegral_le
        hD.le hterminalC.le hlam.le heps prefixOrder terminalOrder hone
    _ = ∫ z, primitiveInsertedMajorant
          (r324CompleteAbsorbedBase D terminalC)
            lam eps supportConstant step.residual.remainingOrder z
          ∂paperMeasure := by rw [htotalOrder]

end R324TwoHalfTerminalData

end

end Anderson4D
