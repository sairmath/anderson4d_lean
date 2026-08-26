import Anderson4D.DetParametrix.Paper42_Moment.R324PaperLeftDirectExactTransformClosed
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperLeftExceptionalExactTransform
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperOutgoingEndpointTargetIntegrability

/-!
# Integrability of the completed left endpoint targets

These are the Fubini licenses used to hand the completed, still signed,
left endpoint half to the right endpoint half in paper Step 4(A).  They are
derived from the same joint integrability statements used by the four exact
left transforms.  No endpoint norm or majorant is introduced here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {alpha beta : Z4}

/-! ## Direct outgoing endpoint -/

/-- The literal completed `DD` left density is jointly integrable in the
untouched right-root parameter and the completed left carrier.  This is the
terminal certificate `L1` statement followed by the exact direct-outgoing
Fourier marginal. -/
theorem integrable_leftDirectDirect_targetDensity
    {providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP alpha}
    (houtgoing : Fin.last m ∉ extractedRightEdges kappaP)
    (data : R324PaperHalfDirectDirectRoute providers)
    (pi : kappaP.singles ≃ kappaM.singles) :
    Integrable
      (fun q :
          R324PaperLeftOuterParameter rho lam eps kappaM ×
            (data.transport.final.SurvivingCoordinate -> T4) =>
        (R324PaperHalfEndpointUniformBound.ofDirectDirect
            houtgoing data).density
          (fun v =>
            r324PaperLeftCanonicalCoefficient data.transport.final
              alpha beta pi q.1 v)
          beta q.2)
      ((r324PaperLeftOuterParameterMeasure rho lam eps kappaM).prod
        (Measure.pi fun _ : data.transport.final.SurvivingCoordinate =>
          paperMeasure)) := by
  let hactive : data.transport.final.state.active.Nonempty :=
    data.transport.final.active_nonempty_of_directOutgoing
      providers.hm data.transport.final_processed_eq_schedule houtgoing
  have hedge :
      data.transport.final.state.edges
          (data.transport.final.terminalOutgoingEdgeSlot hactive) = greenFn :=
    data.transport.final
      |>.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_directOutgoing
        providers.hm data.transport.final_processed_eq_schedule
        houtgoing hactive
  have hterminalCertificate :
      R324WithinHalfEdgeCertificate
        data.transport.final.state data.route.terminalScale := by
    rw [← data.route_final]
    exact data.route.terminalCertificate
  have hterminal :=
    integrable_leftDirectTerminalCanonicalDensity
      (α := alpha) (β := beta)
      data.transport.final data.transport.final_remaining
      data.route.terminalScale hterminalCertificate
      providers.heps providers.heps1
      (data.transport.multiplier alpha) pi
  have hresult :=
    integrable_singleParameter_directOutgoingResult
      data.transport.final data.transport.final_remaining hactive hedge
      (r324PaperLeftOuterParameterMeasure rho lam eps kappaM)
      (fun s v =>
        data.transport.multiplier alpha *
          ((paperSecondOrderModeDecay alpha : Complex) *
            r324PaperLeftCanonicalCoefficient data.transport.final
              alpha beta pi s v))
      beta alpha hterminal
  change Integrable
    (fun q :
        R324PaperLeftOuterParameter rho lam eps kappaM ×
          (data.transport.final.SurvivingCoordinate -> T4) =>
      data.transportEndpointDensity
        (data.transport.final.active_nonempty_of_directOutgoing
          providers.hm data.transport.final_processed_eq_schedule houtgoing)
        (fun v =>
          r324PaperLeftCanonicalCoefficient data.transport.final
            alpha beta pi q.1 v)
        beta q.2)
    ((r324PaperLeftOuterParameterMeasure rho lam eps kappaM).prod
      (Measure.pi fun _ : data.transport.final.SurvivingCoordinate =>
        paperMeasure))
  have hactive_eq :
      data.transport.final.active_nonempty_of_directOutgoing
          providers.hm data.transport.final_processed_eq_schedule houtgoing =
        hactive :=
    Subsingleton.elim _ _
  rw [hactive_eq]
  simpa only [R324PaperHalfDirectDirectRoute.transportEndpointDensity,
    R324PaperHalfDirectDirectRoute.directIncomingCoefficient, mul_assoc]
    using hresult

/-- The literal completed `ED` left density is jointly integrable.  The
incoming exceptional head is first collapsed on its signed driver carrier;
the existing direct-outgoing marginal then gives exactly the common target
density. -/
theorem integrable_leftExceptionalDirect_targetDensity
    {providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP alpha}
    (houtgoing : Fin.last m ∉ extractedRightEdges kappaP)
    (data : R324PaperHalfExceptionalDirectRoute providers)
    (pi : kappaP.singles ≃ kappaM.singles) :
    Integrable
      (fun q :
          R324PaperLeftOuterParameter rho lam eps kappaM ×
            (data.transport.final.SurvivingCoordinate -> T4) =>
        (R324PaperHalfEndpointUniformBound.ofExceptionalDirect
            houtgoing data).density
          (fun v =>
            r324PaperLeftCanonicalCoefficient data.transport.final
              alpha beta pi q.1 v)
          beta q.2)
      ((r324PaperLeftOuterParameterMeasure rho lam eps kappaM).prod
        (Measure.pi fun _ : data.transport.final.SurvivingCoordinate =>
          paperMeasure)) := by
  let hactive : data.transport.final.state.active.Nonempty :=
    data.transport.final.active_nonempty_of_directOutgoing
      providers.hm data.transport.final_processed_eq_schedule houtgoing
  have hcert :
      R324WithinHalfEdgeCertificate data.transport.final.state
        data.route.terminalScale := by
    rw [← data.route_final]
    exact data.route.terminalCertificate
  have hjoint :=
    data.pack.data.driverTerminalJointIntegrable_of_terminal_certificate
      data.transport alpha beta pi providers.heps providers.heps1
      data.route.terminalScale hcert
  have hdirect : r324OutgoingIsShortcut kappaP = false := by
    simp [r324OutgoingIsShortcut, houtgoing]
  have hresult :=
    data.pack.data.integrable_incomingExceptionalLeftDirectIntegrand
      data.transport providers.hm alpha beta pi hjoint hactive hdirect
  change Integrable
    (fun q :
        R324PaperLeftOuterParameter rho lam eps kappaM ×
          (data.transport.final.SurvivingCoordinate -> T4) =>
      data.endpointDensity
        (data.transport.final.active_nonempty_of_directOutgoing
          providers.hm data.transport.final_processed_eq_schedule houtgoing)
        (fun v =>
          r324PaperLeftCanonicalCoefficient data.transport.final
            alpha beta pi q.1 v)
        beta q.2)
    ((r324PaperLeftOuterParameterMeasure rho lam eps kappaM).prod
      (Measure.pi fun _ : data.transport.final.SurvivingCoordinate =>
        paperMeasure))
  have hactive_eq :
      data.transport.final.active_nonempty_of_directOutgoing
          providers.hm data.transport.final_processed_eq_schedule houtgoing =
        hactive :=
    Subsingleton.elim _ _
  rw [hactive_eq]
  apply hresult.congr
  filter_upwards with q
  unfold R324PaperHalfExceptionalDirectRoute.endpointDensity
    R324PaperHalfExceptionalDirectRoute.incomingEndpointCoefficient
    R324IncomingExceptionalStopTraceAssembly.incomingExceptionalRefinedRootDriverReducedCoefficient
    R324WithinHalfResidualPrefix.incomingExceptionalHeadCollapseFactor
    r324PaperLeftCanonicalCoefficient
  simp only [R324IncomingExceptionalStopTraceAssembly.stopContext,
    R324WithinHalfResidualPrefix.headContext]
  ring

end R324WithinHalfResidualPrefix

end

end Anderson4D
