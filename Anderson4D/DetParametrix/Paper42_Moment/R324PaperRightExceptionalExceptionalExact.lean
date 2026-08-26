import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRightRouteExactPackage
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperOutgoingEndpointTargetIntegrability

/-!
# Right exceptional/exceptional endpoint handoff

The completed left density is the untouched parameter while the paired right
incoming head, the intervening intervals, and the retained right outgoing
terminal are removed in the signed paper order.  No norm or new estimate is
introduced.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {alpha beta : Z4}
    {p : R324RefinedScheduleIndex m}
    {e0 : MomentContraction m}
    {leftProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) e0.1 alpha}
    {rightProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) e0.2.1 (-alpha)}
    {leftRoute : R324PaperHalfEndpointRoute leftProviders}

namespace R324PaperRightRouteExactPackage

/-- The literal right `EE` row, before any endpoint estimate. -/
theorem exists_of_exceptionalExceptional
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta)
    (hfirst : (⟨0, rightProviders.hm⟩ : Fin m) ∉ finalActive e0.2.1)
    (houtgoing : Fin.last m ∈ extractedRightEdges e0.2.1)
    (hsingles : e0.2.1.singles.Nonempty)
    (data : R324PaperHalfExceptionalExceptionalRoute rightProviders) :
    Nonempty (R324PaperRightRouteExactPackage left
      (.exceptionalExceptional hfirst houtgoing data)) := by
  let right :=
    R324PaperHalfEndpointUniformBound.ofExceptionalExceptional
      hsingles data
  let Left := left.bound.carrier.SurvivingCoordinate -> T4
  let muLeft : Measure Left := Measure.pi fun _ => paperMeasure
  let coefficient := fun
      (leftPost : Left)
      (rightPost : data.outgoing.terminalPost.SurvivingCoordinate -> T4) =>
    left.bound.density
      (fun _ => left.bound.crossCoefficient right e0.2.2
        leftPost rightPost)
      beta leftPost
  let projectedCoefficient := fun
      (leftPost : Left)
      (post : (data.pack.data.trace.stopPrefix.afterHead
        data.pack.data.terminal data.pack.data.suffix
        data.pack.data.trace.stopPrefix_remaining_eq).SurvivingCoordinate ->
          T4) =>
    left.bound.crossCoefficient right e0.2.2 leftPost
      ((data.outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
        data.outgoing.terminalData.terminal []
        data.outgoing.endpoint.stop_remaining
        (data.outgoing.endpoint.projection post)).2)
  obtain ⟨hcurrent, hregroup⟩ :=
    left.bound
      |>.integrable_and_integral_completedLeft_eq_rightExceptionalInitialSource
        beta data.pack.data e0.2.2 projectedCoefficient
        left.density_mul
        (by
          intro s v
          unfold projectedCoefficient
            R324PaperHalfEndpointUniformBound.crossCoefficient
          exact_mod_cast
            data.pack.data.r324ResidualPrimitiveSumProduct_eq_rightIncomingOutgoingPost
              left.bound.carrier data.outgoing e0.2.2 v s.2)
        left.target_integrable
  have hG : forall j,
      MemEClassT4 (data.pack.data.stopContext.internalEdges j) := by
    intro j
    exact data.pack.data.trace.stopCertificate.memE
      (data.pack.data.stopContext.internalSlot j)
  have hincoming : forall (gap first : T4)
      (kappaB :
        {kappaB : PartialPairing
            (Fin (2 * residualBlockOrder data.pack.data.terminal.2)) //
          kappaB ∈ primitiveFullPairings
            (residualBlockOrder data.pack.data.terminal.2)}),
      Integrable
        (fun r : Fin (2 * residualBlockOrder
            data.pack.data.terminal.2 - 2) -> T4 =>
          detJclosedIntegrandWith rho eps
            (2 * residualBlockOrder data.pack.data.terminal.2)
            kappaB.1 data.pack.data.stopContext.internalEdges
            (primitiveAssemble
              (residualBlockOrder data.pack.data.terminal.2)
              data.pack.data.stopContext.one_le_blockOrder
              first (first + gap) r))
        (Measure.pi fun _ => paperMeasure) := by
    intro gap first kappaB
    exact
      R324WithinHalfEdgeCertificate.integrable_stepClosedIntegrand_section
        (ctx := data.pack.data.stopContext)
        data.pack.data.trace.stopCertificate
        rightProviders.heps rightProviders.heps1
        kappaB first (first + gap)
  have houtgoingInt : forall (gap first : T4)
      (kappaB :
        {kappaB : PartialPairing
            (Fin (2 * residualBlockOrder
              data.outgoing.terminalData.terminal.2)) //
          kappaB ∈ primitiveFullPairings
            (residualBlockOrder data.outgoing.terminalData.terminal.2)}),
      Integrable
        (fun r : Fin (2 * residualBlockOrder
            data.outgoing.terminalData.terminal.2 - 2) -> T4 =>
          detJclosedIntegrandWith rho eps
            (2 * residualBlockOrder
              data.outgoing.terminalData.terminal.2)
            kappaB.1 data.outgoing.terminalContext.internalEdges
            (primitiveAssemble
              (residualBlockOrder data.outgoing.terminalData.terminal.2)
              data.outgoing.terminalContext.one_le_blockOrder
              first (first - gap) r))
        (Measure.pi fun _ => paperMeasure) := by
    intro gap first kappaB
    exact
      R324WithinHalfEdgeCertificate.integrable_stepClosedIntegrand_section
        (ctx := data.outgoing.terminalContext)
        data.stopBudgetCertificate rightProviders.heps rightProviders.heps1
        kappaB first (first - gap)
  let constantPostOuter := fun (omega : T4 × Left)
      (post : (data.pack.data.trace.stopPrefix.afterHead
        data.pack.data.terminal data.pack.data.suffix
        data.pack.data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
          T4) =>
    charT4 (-beta) omega.1 *
      coefficient omega.2
        ((data.outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
          data.outgoing.terminalData.terminal []
          data.outgoing.endpoint.stop_remaining
          (data.outgoing.endpoint.projection post)).2)
  have hpostOuter (omega : T4 × Left)
      (post : (data.pack.data.trace.stopPrefix.afterHead
        data.pack.data.terminal data.pack.data.suffix
        data.pack.data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
          T4) :
      left.bound.rightExceptionalPostOuter beta data.pack.data
          projectedCoefficient omega post =
        constantPostOuter omega post := by
    unfold constantPostOuter projectedCoefficient coefficient
      R324PaperHalfEndpointUniformBound.rightExceptionalPostOuter
    apply congrArg (fun z : ℂ => charT4 (-beta) omega.1 * z)
    apply left.density_congr_at
    rfl
  have hcurrentConstant : Integrable
      (data.pack.data.incomingExceptionalInitialSourceDensity
        (-alpha) (fun omega : T4 × Left => omega.1)
        constantPostOuter)
      ((paperMeasure.prod (paperMeasure.prod muLeft)).prod
        (Measure.pi fun _ :
          (R324WithinHalfResidualPrefix.initial
            rho lam eps e0.2.1).SurvivingCoordinate => paperMeasure)) := by
    apply hcurrent.congr
    filter_upwards with q
    unfold R324IncomingExceptionalStopTraceAssembly.incomingExceptionalInitialSourceDensity
    dsimp only
    rw [hpostOuter]
  have hsource :=
    data.pack.data.integrable_incomingExceptionalStopSourceDensity_of_initial
      (paperMeasure.prod muLeft) (-alpha)
      (fun omega : T4 × Left => omega.1)
      constantPostOuter hcurrentConstant
  have hafter :=
    data.pack.data.integrable_incomingExceptionalAfterHeadPhasedIntegrand
      (paperMeasure.prod muLeft) rightProviders.hm (-alpha)
      (fun omega : T4 × Left => omega.1)
      constantPostOuter hsource hG hincoming
  let split :=
    data.outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
      data.outgoing.terminalData.terminal []
      data.outgoing.endpoint.stop_remaining
  have hendpointWithPhase :=
    data.outgoing.endpoint.integrable_joint
      (paperMeasure.prod muLeft)
      (fun _ : T4 × Left => 0)
      (fun omega : T4 × Left => omega.1) (-alpha)
      (fun omega u =>
        (paperSecondOrderModeDecay (-alpha) : Complex) ^ 2 *
          incomingExceptionalPrimitiveDefect rho lam eps
            (residualBlockOrder data.pack.data.terminal.2)
            data.pack.data.stopContext.one_le_blockOrder
            data.pack.data.stopContext.internalEdges (-alpha) *
          (charT4 (-beta) omega.1 *
            coefficient omega.2 (split u).2))
      hafter
  have houtgoingMultiplier :
      data.outgoing.endpoint.multiplier (-alpha) =
        data.endpoint.endpoint.multiplier (-alpha) := by
    simpa using congrArg
      (fun out => out.endpoint.multiplier (-alpha)) data.outgoing_eq
  have hphaseMeas : Measurable
      (fun q : (T4 × Left) ×
          (data.outgoing.endpoint.stop.SurvivingCoordinate -> T4) =>
        charT4 beta q.1.1) :=
    (continuous_charT4 beta).measurable.comp
      (measurable_fst.comp measurable_fst)
  have hendpointPhaseRemoved :=
    hendpointWithPhase.bdd_mul hphaseMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by rw [norm_charT4])
  have hendpoint : Integrable
      (fun q : (T4 × Left) ×
          (data.outgoing.endpoint.stop.SurvivingCoordinate -> T4) =>
        data.outgoing.endpoint.stop.incomingPhasedResidualDensity
          (data.incomingEndpointCoefficient (coefficient q.1.2)
            (split q.2).2)
          (-alpha) rho eps 0 q.1.1 q.2)
      ((paperMeasure.prod muLeft).prod
        (Measure.pi fun _ => paperMeasure)) := by
    apply hendpointPhaseRemoved.congr
    filter_upwards with q
    have hcoefficient :
        data.outgoing.endpoint.multiplier (-alpha) *
            ((paperSecondOrderModeDecay (-alpha) : Complex) ^ 2 *
              incomingExceptionalPrimitiveDefect rho lam eps
                (residualBlockOrder data.pack.data.terminal.2)
                data.pack.data.stopContext.one_le_blockOrder
                data.pack.data.stopContext.internalEdges (-alpha) *
              (charT4 (-beta) q.1.1 *
                coefficient q.1.2 (split q.2).2)) =
          charT4 (-beta) q.1.1 *
            data.incomingEndpointCoefficient (coefficient q.1.2)
              (split q.2).2 := by
      unfold R324PaperHalfExceptionalExceptionalRoute.incomingEndpointCoefficient
      rw [houtgoingMultiplier]
      ring
    rw [hcoefficient]
    rw [data.outgoing.endpoint.stop.incomingPhasedResidualDensity_const_mul]
    rw [← mul_assoc, charT4_mul_charT4_neg_self, one_mul]
  let StopOutgoing :=
    data.outgoing.endpoint.stop.SurvivingCoordinate -> T4
  let muStopOutgoing : Measure StopOutgoing :=
    Measure.pi fun _ => paperMeasure
  let endpointRegroup : (T4 × Left) × StopOutgoing ≃ᵐ
      Left × (T4 × StopOutgoing) :=
    r324SingleParameterTerminalRegroupMeasurableEquiv
      T4 Left StopOutgoing
  have hpEndpointRegroup : MeasurePreserving endpointRegroup
      ((paperMeasure.prod muLeft).prod muStopOutgoing)
      (muLeft.prod (paperMeasure.prod muStopOutgoing)) := by
    exact
      measurePreserving_r324SingleParameterTerminalRegroupMeasurableEquiv
        paperMeasure muLeft muStopOutgoing
  have hendpointRegroup : Integrable
      (fun q : Left × (T4 × StopOutgoing) =>
        data.outgoing.endpoint.stop.incomingPhasedResidualDensity
          (data.incomingEndpointCoefficient (coefficient q.1)
            (split q.2.2).2)
          (-alpha) rho eps 0 q.2.1 q.2.2)
      (muLeft.prod (paperMeasure.prod muStopOutgoing)) := by
    refine (hpEndpointRegroup.integrable_comp_emb
      endpointRegroup.measurableEmbedding).mp ?_
    apply hendpoint.congr
    filter_upwards with q
    simp only [endpointRegroup,
      r324SingleParameterTerminalRegroupMeasurableEquiv_apply,
      Function.comp_apply]
  have htarget :=
    R324PaperOutgoingEndpointTerminal.integrable_parameter_outgoingEndpointDefectDensity
      data.outgoing
      (data.predecessor_ne_zero_of_singles hsingles)
      (data.terminalPost_active_of_singles hsingles)
      muLeft
      (fun s v => data.incomingEndpointCoefficient (coefficient s) v)
      (-alpha) (-beta) (fun _ => 0)
      (by
        simpa only [StopOutgoing, muStopOutgoing, split] using
          hendpointRegroup)
      houtgoingInt
  have hendpointForTransform : Integrable
      (fun q : (T4 × Left) ×
          (data.outgoing.endpoint.stop.SurvivingCoordinate → T4) =>
        data.outgoing.endpoint.stop.incomingPhasedResidualDensity
          (data.outgoing.endpoint.multiplier (-alpha) *
            ((paperSecondOrderModeDecay (-alpha) : Complex) ^ 2 *
              incomingExceptionalPrimitiveDefect rho lam eps
                (residualBlockOrder data.pack.data.terminal.2)
                data.pack.data.stopContext.one_le_blockOrder
                data.pack.data.stopContext.internalEdges (-alpha) *
              coefficient q.1.2 (split q.2).2))
          (-alpha) rho eps 0 q.1.1 q.2)
      ((paperMeasure.prod muLeft).prod
        (Measure.pi fun _ => paperMeasure)) := by
    apply hendpoint.congr
    filter_upwards with q
    apply congrArg (fun z : ℂ =>
      data.outgoing.endpoint.stop.incomingPhasedResidualDensity
        z (-alpha) rho eps 0 q.1.1 q.2)
    unfold R324PaperHalfExceptionalExceptionalRoute.incomingEndpointCoefficient
    rw [← houtgoingMultiplier]
  let transform :=
    R324PaperHalfEndpointUniformBound.ExactTransform.ofExceptionalExceptional
      hsingles data muLeft coefficient (-beta)
      hG hincoming hcurrentConstant hsource hendpointForTransform houtgoingInt
  refine ⟨{
    bound := right
    transform := transform
    source_eq_left_target := ?_
    endpoint_integrable := ?_
    density_mul := by
      intro a coefficient outgoingMode v
      exact R324PaperHalfEndpointUniformBound.density_mul_ofExceptionalExceptional
        hsingles data a coefficient outgoingMode v
    density_congr_at := by
      intro leftCoefficient rightCoefficient outgoingMode v h
      dsimp only [right,
        R324PaperHalfEndpointUniformBound.ofExceptionalExceptional]
        at leftCoefficient rightCoefficient v h ⊢
      unfold R324PaperHalfExceptionalExceptionalRoute.endpointDensity
      apply integral_congr_ae
      filter_upwards with first
      unfold R324PaperOutgoingEndpointTerminal.outgoingEndpointDefectDensity
        R324PaperOutgoingEndpointTerminal.terminalSplitOuter
        R324PaperHalfExceptionalExceptionalRoute.incomingEndpointCoefficient
      rw [h] }⟩
  · change
      (∫ q,
        data.pack.data.incomingExceptionalInitialSourceDensity
          (-alpha) (fun omega : T4 × Left => omega.1)
          constantPostOuter q
        ∂((paperMeasure.prod (paperMeasure.prod muLeft)).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps e0.2.1).SurvivingCoordinate => paperMeasure))) =
        left.bound.transformTarget
          (r324PaperLeftOuterParameterMeasure rho lam eps e0.2.1)
          (fun s v => r324PaperLeftCanonicalCoefficient
            left.bound.carrier alpha beta e0.2.2 s v) beta
    rw [hregroup]
    apply integral_congr_ae
    filter_upwards with q
    unfold R324IncomingExceptionalStopTraceAssembly.incomingExceptionalInitialSourceDensity
    dsimp only
    rw [hpostOuter]
  · change Integrable
      (fun q : Left ×
          (data.outgoing.terminalPost.SurvivingCoordinate → T4) =>
        data.endpointDensity
          (fun rightPost =>
            left.bound.density
              (fun _ => left.bound.crossCoefficient right e0.2.2
                q.1 rightPost)
              beta q.1)
          (-beta) 0 q.2)
      (muLeft.prod (Measure.pi fun _ => paperMeasure))
    exact htarget

end R324PaperRightRouteExactPackage
end R324WithinHalfResidualPrefix

end

end Anderson4D
