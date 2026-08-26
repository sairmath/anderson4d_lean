import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfEndpointUniformBound

/-!
# Exact signed transform interface for one paper endpoint half

The four endpoint branches already have parameter-carrier identities.  This
file records only their common output: an arbitrary untouched parameter is
left outside the completed signed half density.  The source integral remains
branch-literal; no norm, new integrability premise, or new Fubini theorem is
introduced here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}
    {incomingMode : Z4}
    {route : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode}

namespace R324PaperHalfEndpointUniformBound

/-- The signed parameter-carrier integral after one complete endpoint half.
The outer parameter is untouched until both endpoint operations of the half
have finished. -/
def transformTarget
    (bound : R324PaperHalfEndpointUniformBound route)
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U)
    (coefficient : U ->
      (bound.carrier.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4) : Complex :=
  ∫ u : U,
    ∫ v : bound.carrier.SurvivingCoordinate -> T4,
      bound.density (coefficient u) outgoingMode v
      ∂Measure.pi fun _ => paperMeasure
    ∂muU

/-- A concrete application of one of the four existing parameterized signed
endpoint identities.  `source` is deliberately branch-literal: `DD/DE` use
the ordinary initial residual source, while `ED/EE` use the incoming-head
source. -/
structure ExactTransform
    (bound : R324PaperHalfEndpointUniformBound route)
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U)
    (coefficient : U ->
      (bound.carrier.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4) where
  source : Complex
  exact_transform :
    (lamEps lam eps : Complex) ^
          (2 * (R324WithinHalfResidualPrefix.initial
            rho lam eps pairing).remainingOrder) * source =
      bound.transformTarget muU coefficient outgoingMode

end R324PaperHalfEndpointUniformBound

namespace R324PaperHalfEndpointUniformBound.ExactTransform

variable {leftPairing rightPairing : PartialPairing (Fin m)}
    {leftMode rightMode : Z4}
    {leftRoute : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) leftPairing leftMode}
    {rightRoute : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) rightPairing rightMode}
    {leftBound : R324PaperHalfEndpointUniformBound leftRoute}
    {rightBound : R324PaperHalfEndpointUniformBound rightRoute}
    {UL UR : Type*} [MeasurableSpace UL] [MeasurableSpace UR]
    {muL : Measure UL} {muR : Measure UR}
    {leftCoefficient : UL ->
      (leftBound.carrier.SurvivingCoordinate -> T4) -> Complex}
    {rightCoefficient : UR ->
      (rightBound.carrier.SurvivingCoordinate -> T4) -> Complex}
    {leftOutgoingMode rightOutgoingMode : Z4}

/-- Compose two already-proved signed half transforms.  The sole interface
between them is equality of the second source with the first target; in the
paper applications this equality is the existing product-measure regroup.
The proof is only `pow_add` and reassociation. -/
theorem compose
    (left : leftBound.ExactTransform
      muL leftCoefficient leftOutgoingMode)
    (right : rightBound.ExactTransform
      muR rightCoefficient rightOutgoingMode)
    (hsource : right.source =
      leftBound.transformTarget muL leftCoefficient leftOutgoingMode) :
    (lamEps lam eps : Complex) ^
          (2 *
            ((R324WithinHalfResidualPrefix.initial
                rho lam eps leftPairing).remainingOrder +
              (R324WithinHalfResidualPrefix.initial
                rho lam eps rightPairing).remainingOrder)) *
        left.source =
      rightBound.transformTarget muR rightCoefficient rightOutgoingMode := by
  let leftOrder :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps leftPairing).remainingOrder
  let rightOrder :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps rightPairing).remainingOrder
  calc
    (lamEps lam eps : Complex) ^ (2 * (leftOrder + rightOrder)) *
          left.source =
        (lamEps lam eps : Complex) ^ (2 * rightOrder) *
          ((lamEps lam eps : Complex) ^ (2 * leftOrder) *
            left.source) := by
      rw [Nat.mul_add, pow_add]
      ring
    _ = (lamEps lam eps : Complex) ^ (2 * rightOrder) *
        leftBound.transformTarget muL leftCoefficient leftOutgoingMode := by
      rw [left.exact_transform]
    _ = (lamEps lam eps : Complex) ^ (2 * rightOrder) *
        right.source := by rw [hsource]
    _ = rightBound.transformTarget muR rightCoefficient
        rightOutgoingMode := right.exact_transform

end R324PaperHalfEndpointUniformBound.ExactTransform

/-! ## Literal constructors from the four paper endpoint identities -/

namespace R324PaperHalfEndpointUniformBound.ExactTransform

variable {providers : R324PaperHalfRouteProviders
  (rho := rho) (C := C) (lam := lam) (eps := eps)
  (K := K) (A := A) pairing incomingMode}

/-- The direct/direct instance is exactly the existing parameter-carrier
identity, with the direct incoming Fourier decay left in its coefficient.
No estimate or interchange of integrals is performed here. -/
def ofDirectDirect
    (houtgoing : Fin.last m ∉ extractedRightEdges pairing)
    (data : R324PaperHalfDirectDirectRoute providers)
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U) [SFinite muU]
    (coefficient : U ->
      (data.transport.final.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4)
    (hcurrent :
      Integrable
        (fun q : (T4 × U) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate -> T4) =>
          (R324WithinHalfResidualPrefix.initial rho lam eps pairing
            |>.incomingPhasedResidualDensity
              (charT4 outgoingMode q.1.1 *
                ((paperSecondOrderModeDecay incomingMode : Complex) *
                  coefficient q.1.2 (data.transport.projection q.2)))
              incomingMode rho eps 0 q.1.1 q.2))
        ((paperMeasure.prod muU).prod
          (Measure.pi fun _ => paperMeasure)))
    (hedge :
      data.transport.final.state.edges
          (data.transport.final.terminalOutgoingEdgeSlot
            (data.transport.final.active_nonempty_of_directOutgoing
              providers.hm data.transport.final_processed_eq_schedule
              houtgoing)) = greenFn)
    (hterminal :
      Integrable
        (fun q : (T4 × U) ×
              (data.transport.final.SurvivingCoordinate -> T4) =>
          data.transport.final.incomingPhasedResidualDensity
            (charT4 outgoingMode q.1.1 *
              (data.transport.multiplier incomingMode *
                ((paperSecondOrderModeDecay incomingMode : Complex) *
                  coefficient q.1.2 q.2)))
            incomingMode rho eps 0 q.1.1 q.2)
        ((paperMeasure.prod muU).prod
          (Measure.pi fun _ => paperMeasure))) :
    (R324PaperHalfEndpointUniformBound.ofDirectDirect houtgoing data)
      |>.ExactTransform muU coefficient outgoingMode := by
  let source : Complex :=
    ∫ q : (T4 × U) ×
          ((R324WithinHalfResidualPrefix.initial
            rho lam eps pairing).SurvivingCoordinate -> T4),
      (R324WithinHalfResidualPrefix.initial rho lam eps pairing
        |>.incomingPhasedResidualDensity
          (charT4 outgoingMode q.1.1 *
            ((paperSecondOrderModeDecay incomingMode : Complex) *
              coefficient q.1.2 (data.transport.projection q.2)))
          incomingMode rho eps 0 q.1.1 q.2)
      ∂((paperMeasure.prod muU).prod
        (Measure.pi fun _ => paperMeasure))
  refine { source := source, exact_transform := ?_ }
  let hactive : data.transport.final.state.active.Nonempty :=
    data.transport.final.active_nonempty_of_directOutgoing
      providers.hm data.transport.final_processed_eq_schedule houtgoing
  have hexact :=
    data.transport
      |>.lamEps_pow_integral_initialResidual_eq_singleParameter_directDirect
        muU
        (fun u v =>
          (paperSecondOrderModeDecay incomingMode : Complex) *
            coefficient u v)
        incomingMode outgoingMode hcurrent hactive hedge hterminal
  change (lamEps lam eps : Complex) ^
        (2 * (R324WithinHalfResidualPrefix.initial
          rho lam eps pairing).remainingOrder) * source =
    ∫ u : U,
      ∫ v : data.transport.final.SurvivingCoordinate -> T4,
        data.transportEndpointDensity
          (data.transport.final.active_nonempty_of_directOutgoing
            providers.hm data.transport.final_processed_eq_schedule
            houtgoing) (coefficient u) outgoingMode v
        ∂Measure.pi fun _ => paperMeasure
      ∂muU
  have hproof :
      data.transport.final.active_nonempty_of_directOutgoing
          providers.hm data.transport.final_processed_eq_schedule houtgoing =
        hactive := Subsingleton.elim _ _
  rw [hproof]
  simpa only [source,
    R324PaperHalfDirectDirectRoute.transportEndpointDensity,
    R324PaperHalfDirectDirectRoute.directIncomingCoefficient,
    mul_assoc] using hexact

/-- The direct/exceptional instance is the retained-terminal identity with
the already evaluated direct incoming Fourier coefficient. -/
def directExceptionalTarget
    (outgoing : R324PaperOutgoingEndpointTerminal
      (R324WithinHalfResidualPrefix.initial rho lam eps pairing))
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U)
    (coefficient : U ->
      (outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4) : Complex :=
  ∫ u : U,
    ∫ v : outgoing.terminalPost.SurvivingCoordinate -> T4,
      ∫ first : T4,
        outgoing.outgoingEndpointDefectDensity (coefficient u)
          incomingMode outgoingMode 0 v first
        ∂paperMeasure
      ∂Measure.pi fun _ => paperMeasure
    ∂muU

/-- Transporting the terminal presentation transports its completed signed
target and nothing else. -/
theorem directExceptionalTarget_transport
    {left right : R324PaperOutgoingEndpointTerminal
      (R324WithinHalfResidualPrefix.initial rho lam eps pairing)}
    (h : left = right)
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U)
    (coefficient : U ->
      (right.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4) :
    directExceptionalTarget (incomingMode := incomingMode) left muU
        (fun u =>
          Eq.mp
            (congrArg
              (fun outgoing : R324PaperOutgoingEndpointTerminal
                  (R324WithinHalfResidualPrefix.initial
                    rho lam eps pairing) =>
                (outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
              h).symm
            (coefficient u)) outgoingMode =
      directExceptionalTarget (incomingMode := incomingMode) right muU
        coefficient outgoingMode := by
  cases h
  rfl

def directExceptionalGeometryCoefficient
    (data : R324PaperHalfDirectExceptionalRoute providers)
    {U : Type*}
    (coefficient : U ->
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex) :
    U ->
      (data.geometry.paperOutgoingTerminal.terminalPost.SurvivingCoordinate ->
        T4) -> Complex :=
  fun u =>
    Eq.mp
      (congrArg
        (fun outgoing : R324PaperOutgoingEndpointTerminal
            (R324WithinHalfResidualPrefix.initial rho lam eps pairing) =>
          (outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
        data.geometry_paperOutgoingTerminal).symm
      (data.directIncomingEndpointCoefficient (coefficient u))

def ofDirectExceptional
    (data : R324PaperHalfDirectExceptionalRoute providers)
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U) [SFinite muU]
    (coefficient : U ->
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4)
    (hcurrent :
      Integrable
        (fun q : U × (T4 ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate -> T4)) =>
          (R324WithinHalfResidualPrefix.initial rho lam eps pairing
            |>.incomingPhasedResidualDensity
              (directExceptionalGeometryCoefficient data coefficient q.1
                ((data.geometry.transport.stop
                    |>.splitSurvivingPiMeasurableEquiv
                      data.geometry.terminalData.terminal []
                      data.geometry.stop_remaining_eq_singleton
                      (data.geometry.transport.projection q.2.2)).2))
              incomingMode rho eps 0 q.2.1 q.2.2))
        (muU.prod (paperMeasure.prod
          (Measure.pi fun _ => paperMeasure))))
    (hstop :
      Integrable
        (fun q : U ×
            (T4 × (data.geometry.transport.stop.SurvivingCoordinate -> T4)) =>
          data.geometry.transport.stop.incomingPhasedResidualDensity
            (data.geometry.transport.multiplier incomingMode *
              directExceptionalGeometryCoefficient data coefficient q.1
                ((data.geometry.transport.stop
                  |>.splitSurvivingPiMeasurableEquiv
                    data.geometry.terminalData.terminal []
                    data.geometry.stop_remaining_eq_singleton q.2.2).2))
            incomingMode rho eps 0 q.2.1 q.2.2)
        (muU.prod (paperMeasure.prod
          (Measure.pi fun _ => paperMeasure))))
    (hint :
      forall (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder data.geometry.terminalData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder
              data.geometry.terminalData.terminal.2 - 2) -> T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2)
              kappaB.1
              data.geometry.paperOutgoingTerminal.terminalContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.geometry.terminalData.terminal.2)
                data.geometry.paperOutgoingTerminal.terminalContext.one_le_blockOrder
                first (first - gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    (R324PaperHalfEndpointUniformBound.ofDirectExceptional data)
      |>.ExactTransform muU coefficient outgoingMode := by
  let source : Complex :=
    ∫ q : U × (T4 ×
          ((R324WithinHalfResidualPrefix.initial
            rho lam eps pairing).SurvivingCoordinate -> T4)),
      charT4 outgoingMode q.2.1 *
        (R324WithinHalfResidualPrefix.initial rho lam eps pairing
          |>.incomingPhasedResidualDensity
            (directExceptionalGeometryCoefficient data coefficient q.1
              ((data.geometry.transport.stop
                  |>.splitSurvivingPiMeasurableEquiv
                    data.geometry.terminalData.terminal []
                    data.geometry.stop_remaining_eq_singleton
                    (data.geometry.transport.projection q.2.2)).2))
            incomingMode rho eps 0 q.2.1 q.2.2)
      ∂(muU.prod (paperMeasure.prod
        (Measure.pi fun _ => paperMeasure)))
  refine { source := source, exact_transform := ?_ }
  have hexact :=
    data.geometry.lamEps_pow_integral_parameter_initial_outgoingEndpoint_eq_defect
      muU
      (by simpa only [R324PaperHalfDirectExceptionalRoute.geometry] using
        data.predecessor_ne_zero)
      (by simpa only [data.geometry_paperOutgoingTerminal] using
        data.terminalPost_active)
      (directExceptionalGeometryCoefficient data coefficient)
      incomingMode outgoingMode (fun _ => 0) hcurrent hstop hint
  have hmultiplier :
      data.geometry.transport.multiplier incomingMode = 1 := by
    simpa only [R324PaperHalfDirectExceptionalRoute.geometry] using
      data.endpoint_multiplier_eq_one incomingMode
  calc
    (lamEps lam eps : Complex) ^
          (2 * (R324WithinHalfResidualPrefix.initial
            rho lam eps pairing).remainingOrder) * source =
        directExceptionalTarget (incomingMode := incomingMode)
          data.geometry.paperOutgoingTerminal muU
          (directExceptionalGeometryCoefficient data coefficient)
          outgoingMode := by
      simpa only [source, directExceptionalTarget,
        R324WithinHalfEndpointTerminalGeometry.outgoingEndpointDefectDensity,
        R324WithinHalfEndpointTerminalGeometry.paperOutgoingTerminal,
        R324PaperOutgoingEndpointTerminal.outgoingEndpointDefectDensity,
        hmultiplier, one_mul] using hexact
    _ = directExceptionalTarget (incomingMode := incomingMode)
          data.outgoing muU
          (fun u => data.directIncomingEndpointCoefficient (coefficient u))
          outgoingMode :=
      directExceptionalTarget_transport
        (incomingMode := incomingMode)
        data.geometry_paperOutgoingTerminal muU
        (fun u => data.directIncomingEndpointCoefficient (coefficient u))
        outgoingMode
    _ = R324PaperHalfEndpointUniformBound.transformTarget
          (R324PaperHalfEndpointUniformBound.ofDirectExceptional data)
          muU coefficient outgoingMode := by
      rfl

end R324PaperHalfEndpointUniformBound.ExactTransform
end R324WithinHalfResidualPrefix

end

end Anderson4D
