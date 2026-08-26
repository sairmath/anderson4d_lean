import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfEndpointTransform

/-!
# Exact signed transform adapter for the paper `ED` endpoint half

This file only exposes the already proved single-parameter
exceptional-incoming/direct-outgoing identity through the common endpoint
interface.  In particular, the incoming exceptional head and the outgoing
Fourier leg are both evaluated before the common target is formed; no norm
or new estimate occurs here.
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

/-- The exceptional/direct common-interface instance is exactly the existing
single-parameter signed endpoint identity.  All analytic premises are kept
literal so this adapter performs no hidden interchange or estimate. -/
def ofExceptionalDirect
    (houtgoing : Fin.last m ∉ extractedRightEdges pairing)
    (data : R324PaperHalfExceptionalDirectRoute providers)
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U) [SFinite muU]
    (coefficient : U ->
      (data.transport.final.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4)
    (hG : ∀ j, MemEClassT4 (data.pack.data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
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
              coefficient omega.2 (data.transport.projection v)))
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
              coefficient omega.2 (data.transport.projection v)))
        ((paperMeasure.prod (paperMeasure.prod muU)).prod
          (Measure.pi fun _ :
            data.pack.data.trace.stopPrefix.SurvivingCoordinate =>
              paperMeasure)))
    (hterminal :
      Integrable
        (fun q : (T4 × U) ×
              (data.transport.final.SurvivingCoordinate -> T4) =>
          data.transport.final.incomingPhasedResidualDensity
            (charT4 outgoingMode q.1.1 *
              (data.transport.multiplier incomingMode *
                ((paperSecondOrderModeDecay incomingMode : Complex) ^ 2 *
                  incomingExceptionalPrimitiveDefect rho lam eps
                    (residualBlockOrder data.pack.data.terminal.2)
                    data.pack.data.stopContext.one_le_blockOrder
                    data.pack.data.stopContext.internalEdges incomingMode *
                  coefficient q.1.2 q.2)))
            incomingMode rho eps 0 q.1.1 q.2)
        ((paperMeasure.prod muU).prod
          (Measure.pi fun _ => paperMeasure))) :
    (R324PaperHalfEndpointUniformBound.ofExceptionalDirect
        houtgoing data)
      |>.ExactTransform muU coefficient outgoingMode := by
  let source : Complex :=
    ∫ p,
      data.pack.data.incomingExceptionalInitialSourceDensity
        incomingMode
        (fun omega : T4 × U => omega.1)
        (fun omega v =>
          charT4 outgoingMode omega.1 *
            coefficient omega.2 (data.transport.projection v)) p
      ∂((paperMeasure.prod (paperMeasure.prod muU)).prod
        (Measure.pi fun _ :
          (R324WithinHalfResidualPrefix.initial
            rho lam eps pairing).SurvivingCoordinate => paperMeasure))
  refine { source := source, exact_transform := ?_ }
  let hactive : data.transport.final.state.active.Nonempty :=
    data.transport.final.active_nonempty_of_directOutgoing
      providers.hm data.transport.final_processed_eq_schedule houtgoing
  have hedge :
      data.transport.final.state.edges
          (data.transport.final.terminalOutgoingEdgeSlot hactive) =
        greenFn :=
    data.transport.final
      |>.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_directOutgoing
        providers.hm data.transport.final_processed_eq_schedule
        houtgoing hactive
  have hexact :=
    data.pack.data
      |>.lamEps_pow_integral_initialResidual_eq_singleParameter_incomingExceptional_directOutgoing
        data.transport muU coefficient incomingMode outgoingMode
        providers.hm hG hint hcurrent hsource hactive hedge hterminal
  change (lamEps lam eps : Complex) ^
        (2 * (R324WithinHalfResidualPrefix.initial
          rho lam eps pairing).remainingOrder) * source =
    ∫ u : U,
      ∫ v : data.transport.final.SurvivingCoordinate -> T4,
        data.endpointDensity
          (data.transport.final.active_nonempty_of_directOutgoing
            providers.hm data.transport.final_processed_eq_schedule
            houtgoing)
          (coefficient u) outgoingMode v
        ∂Measure.pi fun _ => paperMeasure
      ∂muU
  have hproof :
      data.transport.final.active_nonempty_of_directOutgoing
          providers.hm data.transport.final_processed_eq_schedule
          houtgoing = hactive :=
    Subsingleton.elim _ _
  rw [hproof]
  simpa only [source,
    R324PaperHalfExceptionalDirectRoute.endpointDensity,
    R324PaperHalfExceptionalDirectRoute.incomingEndpointCoefficient,
    R324WithinHalfResidualPrefix.incomingExceptionalHeadCollapseFactor,
    R324IncomingExceptionalStopTraceAssembly.stopContext,
    R324WithinHalfResidualPrefix.headContext,
    pow_two, mul_assoc] using hexact

end R324PaperHalfEndpointUniformBound.ExactTransform
end R324WithinHalfResidualPrefix

end

end Anderson4D
