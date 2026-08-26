import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRightRouteExactPackage

/-!
# Right exceptional/direct endpoint handoff

The incoming paired head is collapsed first, the remaining right intervals
are transported exactly, and only then is the direct outgoing Fourier
variable evaluated.  The completed left density is an untouched parameter
throughout.
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

/-- The literal right `ED` row, before any endpoint estimate. -/
theorem exists_of_exceptionalDirect
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta)
    (hfirst : (⟨0, rightProviders.hm⟩ : Fin m) ∉ finalActive e0.2.1)
    (houtgoing : Fin.last m ∉ extractedRightEdges e0.2.1)
    (data : R324PaperHalfExceptionalDirectRoute rightProviders) :
    Nonempty (R324PaperRightRouteExactPackage left
      (.exceptionalDirect hfirst houtgoing data)) := by
  let right :=
    R324PaperHalfEndpointUniformBound.ofExceptionalDirect houtgoing data
  let μLeft : Measure
      (left.bound.carrier.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let coefficient := fun
      (leftPost : left.bound.carrier.SurvivingCoordinate → T4)
      (rightPost : data.transport.final.SurvivingCoordinate → T4) =>
    left.bound.density
      (fun _ => left.bound.crossCoefficient right e0.2.2
        leftPost rightPost)
      beta leftPost
  let projectedCoefficient := fun
      (leftPost : left.bound.carrier.SurvivingCoordinate → T4)
      (post : (data.pack.data.trace.stopPrefix.afterHead
        data.pack.data.terminal data.pack.data.suffix
        data.pack.data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
          T4) =>
    left.bound.crossCoefficient right e0.2.2
      leftPost (data.transport.projection post)
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
            data.pack.data.r324ResidualPrimitiveSumProduct_eq_rightDriverProjection
              left.bound.carrier data.transport e0.2.2 v s.2)
        left.target_integrable
  have hG : ∀ j,
      MemEClassT4 (data.pack.data.stopContext.internalEdges j) := by
    intro j
    exact data.pack.data.trace.stopCertificate.memE
      (data.pack.data.stopContext.internalSlot j)
  have hint : ∀ (gap first : T4)
      (κB : { κB : PartialPairing
          (Fin (2 * residualBlockOrder data.pack.data.terminal.2)) //
        κB ∈ primitiveFullPairings
          (residualBlockOrder data.pack.data.terminal.2) }),
      Integrable
        (fun r : Fin (2 * residualBlockOrder
            data.pack.data.terminal.2 - 2) → T4 =>
          detJclosedIntegrandWith rho eps
            (2 * residualBlockOrder data.pack.data.terminal.2)
            κB.1 data.pack.data.stopContext.internalEdges
            (primitiveAssemble
              (residualBlockOrder data.pack.data.terminal.2)
              data.pack.data.stopContext.one_le_blockOrder
              first (first + gap) r))
        (Measure.pi fun _ => paperMeasure) := by
    intro gap first κB
    exact
      R324WithinHalfEdgeCertificate.integrable_stepClosedIntegrand_section
        (ctx := data.pack.data.stopContext)
        data.pack.data.trace.stopCertificate
        rightProviders.heps rightProviders.heps1 κB first (first + gap)
  let constantPostOuter := fun
      (omega : T4 ×
        (left.bound.carrier.SurvivingCoordinate → T4))
      (post : (data.pack.data.trace.stopPrefix.afterHead
        data.pack.data.terminal data.pack.data.suffix
        data.pack.data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
          T4) =>
    charT4 (-beta) omega.1 *
      coefficient omega.2 (data.transport.projection post)
  have hpostOuter (omega : T4 ×
      (left.bound.carrier.SurvivingCoordinate → T4))
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
        (-alpha)
        (fun omega : T4 ×
          (left.bound.carrier.SurvivingCoordinate → T4) => omega.1)
        constantPostOuter)
      ((paperMeasure.prod (paperMeasure.prod μLeft)).prod
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
      (paperMeasure.prod μLeft) (-alpha)
      (fun ω : T4 ×
        (left.bound.carrier.SurvivingCoordinate → T4) => ω.1)
      constantPostOuter hcurrentConstant
  have hafter :=
    data.pack.data.integrable_incomingExceptionalAfterHeadPhasedIntegrand
      (paperMeasure.prod μLeft) rightProviders.hm (-alpha)
      (fun ω : T4 ×
        (left.bound.carrier.SurvivingCoordinate → T4) => ω.1)
      constantPostOuter hsource hG hint
  have htransported :=
    data.transport.integrable_joint
      (paperMeasure.prod μLeft)
      (fun _ => 0) (fun ω => ω.1) (-alpha)
      (fun ω u =>
        (paperSecondOrderModeDecay (-alpha) : ℂ) ^ 2 *
          incomingExceptionalPrimitiveDefect rho lam eps
            (residualBlockOrder data.pack.data.terminal.2)
            data.pack.data.stopContext.one_le_blockOrder
            data.pack.data.stopContext.internalEdges (-alpha) *
          (charT4 (-beta) ω.1 * coefficient ω.2 u))
      hafter
  have hterminal : Integrable
      (fun q : (T4 ×
            (left.bound.carrier.SurvivingCoordinate → T4)) ×
            (data.transport.final.SurvivingCoordinate → T4) =>
        data.transport.final.incomingPhasedResidualDensity
          (charT4 (-beta) q.1.1 *
            (data.transport.multiplier (-alpha) *
              ((paperSecondOrderModeDecay (-alpha) : ℂ) ^ 2 *
                incomingExceptionalPrimitiveDefect rho lam eps
                  (residualBlockOrder data.pack.data.terminal.2)
                  data.pack.data.stopContext.one_le_blockOrder
                  data.pack.data.stopContext.internalEdges (-alpha) *
                coefficient q.1.2 q.2)))
          (-alpha) rho eps 0 q.1.1 q.2)
      ((paperMeasure.prod μLeft).prod
        (Measure.pi fun _ => paperMeasure)) := by
    apply htransported.congr
    filter_upwards with q
    apply congrArg (fun z : ℂ =>
      data.transport.final.incomingPhasedResidualDensity z
        (-alpha) rho eps 0 q.1.1 q.2)
    ring
  let transform :=
    R324PaperHalfEndpointUniformBound.ExactTransform.ofExceptionalDirect
      houtgoing data μLeft coefficient (-beta)
      hG hint hcurrentConstant hsource hterminal
  let hactive : data.transport.final.state.active.Nonempty :=
    data.transport.final.active_nonempty_of_directOutgoing
      rightProviders.hm data.transport.final_processed_eq_schedule houtgoing
  have hedge :
      data.transport.final.state.edges
          (data.transport.final.terminalOutgoingEdgeSlot hactive) = greenFn :=
    data.transport.final
      |>.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_directOutgoing
        rightProviders.hm data.transport.final_processed_eq_schedule
        houtgoing hactive
  have htarget :=
    integrable_singleParameter_directOutgoingResult
      data.transport.final data.transport.final_remaining hactive hedge
      μLeft
      (fun leftPost rightPost =>
        data.transport.multiplier (-alpha) *
          ((paperSecondOrderModeDecay (-alpha) : ℂ) ^ 2 *
            incomingExceptionalPrimitiveDefect rho lam eps
              (residualBlockOrder data.pack.data.terminal.2)
              data.pack.data.stopContext.one_le_blockOrder
              data.pack.data.stopContext.internalEdges (-alpha) *
            coefficient leftPost rightPost))
      (-beta) (-alpha) hterminal
  refine ⟨{
    bound := right
    transform := transform
    source_eq_left_target := ?_
    endpoint_integrable := ?_
    density_mul := by
      intro a coefficient outgoingMode v
      exact R324PaperHalfEndpointUniformBound.density_mul_ofExceptionalDirect
        houtgoing data a coefficient outgoingMode v
    density_congr_at := by
      intro leftCoefficient rightCoefficient outgoingMode v h
      dsimp only [right,
        R324PaperHalfEndpointUniformBound.ofExceptionalDirect]
      unfold R324PaperHalfExceptionalDirectRoute.endpointDensity
        R324PaperHalfExceptionalDirectRoute.incomingEndpointCoefficient
      rw [h] }⟩
  · change
      (∫ q,
        data.pack.data.incomingExceptionalInitialSourceDensity
          (-alpha)
          (fun omega : T4 ×
            (left.bound.carrier.SurvivingCoordinate → T4) => omega.1)
          constantPostOuter q
        ∂((paperMeasure.prod (paperMeasure.prod μLeft)).prod
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
      (fun q :
          (left.bound.carrier.SurvivingCoordinate → T4) ×
            (data.transport.final.SurvivingCoordinate → T4) =>
        data.endpointDensity
          (data.transport.final.active_nonempty_of_directOutgoing
            rightProviders.hm data.transport.final_processed_eq_schedule
            houtgoing)
          (fun rightPost =>
            left.bound.density
              (fun _ => left.bound.crossCoefficient right e0.2.2
                q.1 rightPost)
              beta q.1)
          (-beta) q.2)
      (μLeft.prod (Measure.pi fun _ => paperMeasure))
    have hactive_eq :
        data.transport.final.active_nonempty_of_directOutgoing
            rightProviders.hm data.transport.final_processed_eq_schedule
            houtgoing = hactive := Subsingleton.elim _ _
    rw [hactive_eq]
    simpa only [coefficient,
      R324PaperHalfExceptionalDirectRoute.endpointDensity,
      R324PaperHalfExceptionalDirectRoute.incomingEndpointCoefficient,
      R324WithinHalfResidualPrefix.incomingExceptionalHeadCollapseFactor,
      R324IncomingExceptionalStopTraceAssembly.stopContext,
      R324WithinHalfResidualPrefix.headContext,
      pow_two, mul_assoc] using htarget

end R324PaperRightRouteExactPackage
end R324WithinHalfResidualPrefix

end

end Anderson4D
