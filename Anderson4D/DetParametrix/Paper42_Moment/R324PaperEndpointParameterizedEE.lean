import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointTwoHalfSplice

/-!
# Parameterized exceptional/exceptional endpoint splice

This is the one parameter-carrier variant missing from the paper Step 4(A)
endpoint table.  The incoming exceptional head and every prefix interval are
removed first.  The retained outgoing terminal is then Fourier-integrated
before any norm is taken.  An arbitrary already-completed opposite-half
carrier remains untouched throughout.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix
namespace R324IncomingExceptionalStopTraceAssembly

variable {rho : SmoothCutoff} {C lam eps K : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) -> Real}

/-- Exact paper-ordered exceptional-incoming/exceptional-outgoing splice
with one arbitrary untouched parameter carrier.  This is the EEEE seam in
the two-half endpoint table: applying it to the second half leaves the
already completed first half outside every signed endpoint integral. -/
theorem
    lamEps_pow_integral_initialResidual_eq_singleParameter_incomingExceptional_outgoingExceptional
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) pairing initialScale)
    (outgoing :
      R324PaperOutgoingEndpointTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U) [SFinite muU]
    (coefficient : U ->
      (outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (incomingMode outgoingMode : Z4)
    (hm : 0 < m)
    (hG : forall j, MemEClassT4 (data.stopContext.internalEdges j))
    (hincoming :
      forall (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder data.terminal.2 - 2) -> T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder data.terminal.2)
              kappaB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hcurrent :
      Integrable
        (data.incomingExceptionalInitialSourceDensity
          incomingMode
          (fun omega : T4 × U => omega.1)
          (fun omega v =>
            charT4 outgoingMode omega.1 *
              coefficient omega.2
                ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
                  outgoing.terminalData.terminal []
                  outgoing.endpoint.stop_remaining
                  (outgoing.endpoint.projection v)).2)))
        ((paperMeasure.prod (paperMeasure.prod muU)).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps pairing).SurvivingCoordinate => paperMeasure)))
    (hsource :
      Integrable
        (data.incomingExceptionalStopSourceDensity
          incomingMode
          (fun omega : T4 × U => omega.1)
          (fun omega v =>
            charT4 outgoingMode omega.1 *
              coefficient omega.2
                ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
                  outgoing.terminalData.terminal []
                  outgoing.endpoint.stop_remaining
                  (outgoing.endpoint.projection v)).2)))
        ((paperMeasure.prod (paperMeasure.prod muU)).prod
          (Measure.pi fun _ :
            data.trace.stopPrefix.SurvivingCoordinate => paperMeasure)))
    (hpred :
      r324WithinHalfPredecessorSlot outgoing.endpoint.stop.state
          outgoing.terminalData.terminal ≠ 0)
    (hactive : outgoing.terminalPost.state.active.Nonempty)
    (hendpoint :
      Integrable
        (fun q : (T4 × U) ×
              (outgoing.endpoint.stop.SurvivingCoordinate -> T4) =>
          outgoing.endpoint.stop.incomingPhasedResidualDensity
            (outgoing.endpoint.multiplier incomingMode *
              ((paperSecondOrderModeDecay incomingMode : Complex) ^ 2 *
                incomingExceptionalPrimitiveDefect rho lam eps
                  (residualBlockOrder data.terminal.2)
                  data.stopContext.one_le_blockOrder
                  data.stopContext.internalEdges incomingMode *
                coefficient q.1.2
                  ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
                    outgoing.terminalData.terminal []
                    outgoing.endpoint.stop_remaining q.2).2)))
            incomingMode rho eps 0 q.1.1 q.2)
        ((paperMeasure.prod muU).prod
          (Measure.pi fun _ => paperMeasure)))
    (houtgoing :
      forall (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder
                outgoing.terminalData.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder outgoing.terminalData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder
              outgoing.terminalData.terminal.2 - 2) -> T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder outgoing.terminalData.terminal.2)
              kappaB.1 outgoing.terminalContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder outgoing.terminalData.terminal.2)
                outgoing.terminalContext.one_le_blockOrder
                first (first - gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam eps : Complex) ^
          (2 * (R324WithinHalfResidualPrefix.initial
            rho lam eps pairing).remainingOrder) *
        (∫ p,
          data.incomingExceptionalInitialSourceDensity
            incomingMode
            (fun omega : T4 × U => omega.1)
            (fun omega v =>
              charT4 outgoingMode omega.1 *
                coefficient omega.2
                  ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
                    outgoing.terminalData.terminal []
                    outgoing.endpoint.stop_remaining
                    (outgoing.endpoint.projection v)).2)) p
          ∂((paperMeasure.prod (paperMeasure.prod muU)).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate => paperMeasure))) =
      ∫ u : U,
        ∫ v : outgoing.terminalPost.SurvivingCoordinate -> T4,
          ∫ first : T4,
            outgoing.outgoingEndpointDefectDensity
              (fun post =>
                outgoing.endpoint.multiplier incomingMode *
                  ((paperSecondOrderModeDecay incomingMode : Complex) ^ 2 *
                    incomingExceptionalPrimitiveDefect rho lam eps
                      (residualBlockOrder data.terminal.2)
                      data.stopContext.one_le_blockOrder
                      data.stopContext.internalEdges incomingMode *
                    coefficient u post))
              incomingMode outgoingMode 0 v first
            ∂paperMeasure
          ∂Measure.pi fun _ => paperMeasure
        ∂muU := by
  let nu := paperMeasure.prod muU
  let split :=
    outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
      outgoing.terminalData.terminal [] outgoing.endpoint.stop_remaining
  let postOuter :
      (T4 × U) ->
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate -> T4) ->
            Complex :=
    fun omega v =>
      charT4 outgoingMode omega.1 *
        coefficient omega.2 (split (outgoing.endpoint.projection v)).2
  let reduced : U ->
      (outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex :=
    fun u post =>
      outgoing.endpoint.multiplier incomingMode *
        ((paperSecondOrderModeDecay incomingMode : Complex) ^ 2 *
          incomingExceptionalPrimitiveDefect rho lam eps
            (residualBlockOrder data.terminal.2)
            data.stopContext.one_le_blockOrder
            data.stopContext.internalEdges incomingMode *
          coefficient u post)
  have hinitial :=
    data.lamEps_pow_integral_initialResidual_eq_incomingExceptionalStopFourier
      nu hm incomingMode (fun omega : T4 × U => omega.1)
      postOuter hcurrent
  have hhead :=
    data.lamEps_pow_integral_incomingExceptionalStopFourierDensity_eq_afterHead
      nu hm incomingMode (fun omega : T4 × U => omega.1)
      postOuter hsource hG hincoming
  have hafter :
      Integrable
        (data.incomingExceptionalAfterHeadPhasedIntegrand
          incomingMode (fun omega : T4 × U => omega.1) postOuter)
        (nu.prod
          (Measure.pi fun _ :
            (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                paperMeasure)) :=
    data.integrable_incomingExceptionalAfterHeadPhasedIntegrand
      nu hm incomingMode (fun omega : T4 × U => omega.1)
      postOuter hsource hG hincoming
  have hphaseMeas : Measurable
      (fun q : (T4 × U) ×
          (outgoing.endpoint.stop.SurvivingCoordinate -> T4) =>
        charT4 outgoingMode q.1.1) :=
    (continuous_charT4 outgoingMode).measurable.comp
      (measurable_fst.comp measurable_fst)
  have hendpointPhase :
      Integrable
        (fun q : (T4 × U) ×
              (outgoing.endpoint.stop.SurvivingCoordinate -> T4) =>
          charT4 outgoingMode q.1.1 *
            outgoing.endpoint.stop.incomingPhasedResidualDensity
              (reduced q.1.2 (split q.2).2)
              incomingMode rho eps 0 q.1.1 q.2)
        ((paperMeasure.prod muU).prod
          (Measure.pi fun _ => paperMeasure)) := by
    exact hendpoint.bdd_mul hphaseMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by rw [norm_charT4])
  have htransport :
      (lamEps lam eps : Complex) ^
            (2 * (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).remainingOrder) *
          (∫ p,
            data.incomingExceptionalAfterHeadPhasedIntegrand
              incomingMode (fun omega : T4 × U => omega.1)
              postOuter p
            ∂(nu.prod
              (Measure.pi fun _ :
                (data.trace.stopPrefix.afterHead
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                    paperMeasure))) =
        (lamEps lam eps : Complex) ^
            (2 * outgoing.endpoint.stop.remainingOrder) *
          (∫ q : (T4 × U) ×
                (outgoing.endpoint.stop.SurvivingCoordinate -> T4),
            charT4 outgoingMode q.1.1 *
              outgoing.endpoint.stop.incomingPhasedResidualDensity
                (reduced q.1.2 (split q.2).2)
                incomingMode rho eps 0 q.1.1 q.2
            ∂((paperMeasure.prod muU).prod
              (Measure.pi fun _ => paperMeasure))) := by
    rw [integral_prod _ hafter, integral_prod _ hendpointPhase,
      ← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hafter.prod_right_ae] with omega homega
    have hsection :=
      outgoing.endpoint.transport 0 omega.1 incomingMode
        (fun stop =>
          (paperSecondOrderModeDecay incomingMode : Complex) ^ 2 *
            incomingExceptionalPrimitiveDefect rho lam eps
              (residualBlockOrder data.terminal.2)
              data.stopContext.one_le_blockOrder
              data.stopContext.internalEdges incomingMode *
            (charT4 outgoingMode omega.1 *
              coefficient omega.2 (split stop).2))
        (by
          simpa only [postOuter,
            incomingExceptionalAfterHeadPhasedIntegrand,
            incomingExceptionalPostCoefficient] using homega)
    calc
      (lamEps lam eps : Complex) ^
            (2 * (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).remainingOrder) *
          (∫ v,
            data.incomingExceptionalAfterHeadPhasedIntegrand
              incomingMode (fun omega' : T4 × U => omega'.1)
              postOuter (omega, v)
            ∂Measure.pi fun _ => paperMeasure) =
        (lamEps lam eps : Complex) ^
            (2 * outgoing.endpoint.stop.remainingOrder) *
          (∫ stop,
            outgoing.endpoint.stop.incomingPhasedResidualDensity
              (outgoing.endpoint.multiplier incomingMode *
                ((paperSecondOrderModeDecay incomingMode : Complex) ^ 2 *
                  incomingExceptionalPrimitiveDefect rho lam eps
                    (residualBlockOrder data.terminal.2)
                    data.stopContext.one_le_blockOrder
                    data.stopContext.internalEdges incomingMode *
                  (charT4 outgoingMode omega.1 *
                    coefficient omega.2 (split stop).2)))
              incomingMode rho eps 0 omega.1 stop
            ∂Measure.pi fun _ => paperMeasure) := hsection
      _ = (lamEps lam eps : Complex) ^
            (2 * outgoing.endpoint.stop.remainingOrder) *
          (∫ stop,
            charT4 outgoingMode omega.1 *
              outgoing.endpoint.stop.incomingPhasedResidualDensity
                (reduced omega.2 (split stop).2)
                incomingMode rho eps 0 omega.1 stop
            ∂Measure.pi fun _ => paperMeasure) := by
        apply congrArg
        apply integral_congr_ae
        filter_upwards with stop
        rw [← outgoing.endpoint.stop.incomingPhasedResidualDensity_const_mul]
        dsimp only [reduced]
        congr 1
        ring
  have hout :=
    outgoing.lamEps_pow_integral_singleParameter_stop_outgoingEndpoint_eq_defect
      hpred hactive muU reduced incomingMode outgoingMode
      (fun _ => 0) hendpoint houtgoing
  calc
    (lamEps lam eps : Complex) ^
          (2 * (R324WithinHalfResidualPrefix.initial
            rho lam eps pairing).remainingOrder) *
        (∫ p,
          data.incomingExceptionalInitialSourceDensity
            incomingMode (fun omega : T4 × U => omega.1)
            postOuter p
          ∂((paperMeasure.prod (paperMeasure.prod muU)).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate => paperMeasure))) =
      (lamEps lam eps : Complex) ^
          (2 * data.trace.stopPrefix.remainingOrder) *
        (∫ p,
          data.incomingExceptionalStopFourierDensity
            incomingMode (fun omega : T4 × U => omega.1)
            postOuter p
          ∂(nu.prod
            ((Measure.pi fun _ :
                Fin (2 * residualBlockOrder data.terminal.2) =>
                  paperMeasure).prod
              (Measure.pi fun _ :
                (data.trace.stopPrefix.afterHead
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                    paperMeasure)))) := hinitial
    _ = (lamEps lam eps : Complex) ^
          (2 * (data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq).remainingOrder) *
        (∫ p,
          data.incomingExceptionalAfterHeadPhasedIntegrand
            incomingMode (fun omega : T4 × U => omega.1)
            postOuter p
          ∂(nu.prod
            (Measure.pi fun _ :
              (data.trace.stopPrefix.afterHead
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                  paperMeasure))) := hhead
    _ = (lamEps lam eps : Complex) ^
          (2 * outgoing.endpoint.stop.remainingOrder) *
        (∫ q : (T4 × U) ×
              (outgoing.endpoint.stop.SurvivingCoordinate -> T4),
          charT4 outgoingMode q.1.1 *
            outgoing.endpoint.stop.incomingPhasedResidualDensity
              (reduced q.1.2 (split q.2).2)
              incomingMode rho eps 0 q.1.1 q.2
          ∂((paperMeasure.prod muU).prod
            (Measure.pi fun _ => paperMeasure))) := htransport
    _ = _ := by
      simpa only [reduced] using hout

end R324IncomingExceptionalStopTraceAssembly
end R324WithinHalfResidualPrefix

end

end Anderson4D
