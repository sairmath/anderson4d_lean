import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfEndpointTransform

/-!
# Exact exceptional/exceptional one-half transform

This file is the literal `EE` instance of the common signed transform
interface.  It only packages the parameter-carrier identity already proved
for the incoming exceptional head and retained outgoing terminal.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix
namespace R324PaperHalfEndpointUniformBound.ExactTransform

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}
    {incomingMode : Z4}
    {providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode}

/-- The paper's complete exceptional/exceptional signed endpoint transform,
with one arbitrary untouched parameter. -/
def ofExceptionalExceptional
    (hsingles : pairing.singles.Nonempty)
    (data : R324PaperHalfExceptionalExceptionalRoute providers)
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U) [SFinite muU]
    (coefficient : U ->
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4)
    (hG : forall j,
      MemEClassT4 (data.pack.data.stopContext.internalEdges j))
    (hincoming :
      forall (gap first : T4)
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
          (Measure.pi fun _ => paperMeasure))
    (hcurrent :
      Integrable
        (data.pack.data.incomingExceptionalInitialSourceDensity
          incomingMode
          (fun omega : T4 × U => omega.1)
          (fun omega v =>
            charT4 outgoingMode omega.1 *
              coefficient omega.2
                ((data.outgoing.endpoint.stop
                  |>.splitSurvivingPiMeasurableEquiv
                    data.outgoing.terminalData.terminal []
                    data.outgoing.endpoint.stop_remaining
                    (data.outgoing.endpoint.projection v)).2)))
        ((paperMeasure.prod (paperMeasure.prod muU)).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps pairing).SurvivingCoordinate => paperMeasure)))
    (hsource :
      Integrable
        (data.pack.data.incomingExceptionalStopSourceDensity
          incomingMode
          (fun omega : T4 × U => omega.1)
          (fun omega v =>
            charT4 outgoingMode omega.1 *
              coefficient omega.2
                ((data.outgoing.endpoint.stop
                  |>.splitSurvivingPiMeasurableEquiv
                    data.outgoing.terminalData.terminal []
                    data.outgoing.endpoint.stop_remaining
                    (data.outgoing.endpoint.projection v)).2)))
        ((paperMeasure.prod (paperMeasure.prod muU)).prod
          (Measure.pi fun _ :
            data.pack.data.trace.stopPrefix.SurvivingCoordinate =>
              paperMeasure)))
    (hendpoint :
      Integrable
        (fun q : (T4 × U) ×
              (data.outgoing.endpoint.stop.SurvivingCoordinate -> T4) =>
          data.outgoing.endpoint.stop.incomingPhasedResidualDensity
            (data.outgoing.endpoint.multiplier incomingMode *
              ((paperSecondOrderModeDecay incomingMode : Complex) ^ 2 *
                incomingExceptionalPrimitiveDefect rho lam eps
                  (residualBlockOrder data.pack.data.terminal.2)
                  data.pack.data.stopContext.one_le_blockOrder
                  data.pack.data.stopContext.internalEdges incomingMode *
                coefficient q.1.2
                  ((data.outgoing.endpoint.stop
                    |>.splitSurvivingPiMeasurableEquiv
                      data.outgoing.terminalData.terminal []
                      data.outgoing.endpoint.stop_remaining q.2).2)))
            incomingMode rho eps 0 q.1.1 q.2)
        ((paperMeasure.prod muU).prod
          (Measure.pi fun _ => paperMeasure)))
    (houtgoing :
      forall (gap first : T4)
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
          (Measure.pi fun _ => paperMeasure)) :
    (R324PaperHalfEndpointUniformBound.ofExceptionalExceptional
      hsingles data).ExactTransform muU coefficient outgoingMode := by
  let source : Complex :=
    ∫ p,
      data.pack.data.incomingExceptionalInitialSourceDensity
        incomingMode
        (fun omega : T4 × U => omega.1)
        (fun omega v =>
          charT4 outgoingMode omega.1 *
            coefficient omega.2
              ((data.outgoing.endpoint.stop
                |>.splitSurvivingPiMeasurableEquiv
                  data.outgoing.terminalData.terminal []
                  data.outgoing.endpoint.stop_remaining
                  (data.outgoing.endpoint.projection v)).2)) p
      ∂((paperMeasure.prod (paperMeasure.prod muU)).prod
        (Measure.pi fun _ :
          (R324WithinHalfResidualPrefix.initial
            rho lam eps pairing).SurvivingCoordinate => paperMeasure))
  refine { source := source, exact_transform := ?_ }
  let hpred := data.predecessor_ne_zero_of_singles hsingles
  let hactive := data.terminalPost_active_of_singles hsingles
  have hexact :=
    data.pack.data
      |>.lamEps_pow_integral_initialResidual_eq_singleParameter_incomingExceptional_outgoingExceptional
        data.outgoing muU coefficient incomingMode outgoingMode providers.hm
        hG hincoming hcurrent hsource hpred hactive hendpoint houtgoing
  have hmultiplier :
      data.outgoing.endpoint.multiplier incomingMode =
        data.endpoint.endpoint.multiplier incomingMode := by
    rw [data.outgoing_eq]
  change (lamEps lam eps : Complex) ^
        (2 * (R324WithinHalfResidualPrefix.initial
          rho lam eps pairing).remainingOrder) * source =
    ∫ u : U,
      ∫ v : data.outgoing.terminalPost.SurvivingCoordinate -> T4,
        ∫ first : T4,
          data.outgoing.outgoingEndpointDefectDensity
            (fun post =>
              data.endpoint.endpoint.multiplier incomingMode *
                ((paperSecondOrderModeDecay incomingMode : Complex) ^ 2 *
                  incomingExceptionalPrimitiveDefect rho lam eps
                    (residualBlockOrder data.pack.data.terminal.2)
                    data.pack.data.stopContext.one_le_blockOrder
                    data.pack.data.stopContext.internalEdges incomingMode *
                  coefficient u post))
            incomingMode outgoingMode 0 v first
          ∂paperMeasure
        ∂Measure.pi fun _ => paperMeasure
      ∂muU
  simpa only [source, hmultiplier]
    using hexact

end R324PaperHalfEndpointUniformBound.ExactTransform
end R324WithinHalfResidualPrefix

end

end Anderson4D
