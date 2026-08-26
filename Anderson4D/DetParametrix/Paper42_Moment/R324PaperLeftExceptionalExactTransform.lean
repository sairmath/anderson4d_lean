import Anderson4D.DetParametrix.Paper42_Moment.R324PaperActualEndpointCollapse
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfEndpointTransformED
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfEndpointTransformEE
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperOutgoingEndpointTargetIntegrability

/-!
# The exceptional-incoming left endpoint transforms

This is the remaining left-half part of paper Step 4(A).  It packages the
existing physical-root `ED` and `EE` splices directly as common endpoint
transforms.  In particular the exceptional head, every intervening interval,
and the outgoing endpoint operation are those of the paper proof; no new
summation or estimate is introduced here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {alpha : Z4}

/-! ## The canonical opposite-half coefficient -/

/-- On an exceptional-incoming/exceptional-outgoing half, the refined-root
outer coefficient is the free outgoing character times the same canonical
opposite-half coefficient used by the common endpoint interface.  This is
only the two already-proved projection identities, before any norm. -/
theorem incomingExceptionalRefinedRootPostOuter_eq_char_mul_leftCanonical
    {kappaP kappaM : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) -> Real}
    (data : R324IncomingExceptionalStopTraceAssembly
      (ρ := rho) (C := C) (lam := lam) (ε := eps)
      (K := K) kappaP initialScale)
    (outgoing : R324PaperOutgoingEndpointTerminal
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix data.trace.stopPrefix_remaining_eq))
    (alpha beta : Z4) (pi : kappaP.singles ≃ kappaM.singles)
    (y : T4)
    (s : R324PaperLeftOuterParameter rho lam eps kappaM)
    (v : (data.trace.stopPrefix.afterHead
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq).SurvivingCoordinate -> T4) :
    data.incomingExceptionalRefinedRootPostOuter
        alpha beta pi ((y, s.1), s.2) v =
      charT4 beta y *
        r324PaperLeftCanonicalCoefficient outgoing.terminalPost
          alpha beta pi s
          ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
            outgoing.terminalData.terminal []
            outgoing.endpoint.stop_remaining
            (outgoing.endpoint.projection v)).2) := by
  rw [data.incomingExceptionalRefinedRootPostOuter_eq_endpointProjection
    outgoing.endpoint alpha beta pi ((y, s.1), s.2) v]
  unfold R324IncomingExceptionalStopTraceAssembly.incomingExceptionalRefinedRootEndpointPostOuter
    r324PaperLeftCanonicalCoefficient
  rw [data.r324ResidualPrimitiveSumProduct_eq_leftOutgoingTerminalPost
    outgoing pi (outgoing.endpoint.projection v) s.2]
  ring

/-- After the outgoing exceptional terminal has been removed, the remaining
coefficient is precisely its Fourier multiplier, the two second-order
factors, the incoming primitive defect, and the canonical untouched
opposite-half coefficient. -/
theorem incomingExceptionalRefinedRootOutgoingPostCoefficient_eq_mul_leftCanonical
    {kappaP kappaM : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) -> Real}
    (data : R324IncomingExceptionalStopTraceAssembly
      (ρ := rho) (C := C) (lam := lam) (ε := eps)
      (K := K) kappaP initialScale)
    (outgoing : R324PaperOutgoingEndpointTerminal
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix data.trace.stopPrefix_remaining_eq))
    (alpha beta : Z4) (pi : kappaP.singles ≃ kappaM.singles)
    (s : R324PaperLeftOuterParameter rho lam eps kappaM)
    (v : outgoing.terminalPost.SurvivingCoordinate -> T4) :
    data.incomingExceptionalRefinedRootOutgoingPostCoefficient
        outgoing alpha beta pi s v =
      outgoing.endpoint.multiplier alpha *
        ((paperSecondOrderModeDecay alpha : Complex) ^ 2 *
          incomingExceptionalPrimitiveDefect rho lam eps
            (residualBlockOrder data.terminal.2)
            data.stopContext.one_le_blockOrder
            data.stopContext.internalEdges alpha *
          r324PaperLeftCanonicalCoefficient outgoing.terminalPost
            alpha beta pi s v) := by
  unfold R324IncomingExceptionalStopTraceAssembly.incomingExceptionalRefinedRootOutgoingPostCoefficient
    r324PaperLeftCanonicalCoefficient
  congr 1

/-! The exceptional source has one additional incoming endpoint in front of
the physical root parameter.  The following reassociation is the literal
coordinate change used in paper Step 4(A); it changes no variable and no
integrand, but only moves parentheses so that the common one-half interface
sees the free outgoing endpoint followed by the opposite-half parameter. -/

def r324PaperLeftExceptionalParameterMeasurableEquiv
    (rho : SmoothCutoff) (lam eps : Real) {m : Nat}
    (kappaM : PartialPairing (Fin m))
    (L : Type*) [MeasurableSpace L] :
    (T4 × R324IncomingExceptionalRootParameter rho lam eps kappaM) × L ≃ᵐ
      (T4 × (T4 × R324PaperLeftOuterParameter rho lam eps kappaM)) × L :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl T4)
      (MeasurableEquiv.prodAssoc
        (α := T4) (β := T4 × T4)
        (γ := (R324WithinHalfResidualPrefix.initial
          rho lam eps kappaM).SurvivingCoordinate → T4)))
    (MeasurableEquiv.refl L)

@[simp]
theorem r324PaperLeftExceptionalParameterMeasurableEquiv_apply
    (rho : SmoothCutoff) (lam eps : Real) {m : Nat}
    (kappaM : PartialPairing (Fin m))
    {L : Type*} [MeasurableSpace L]
    (q : (T4 × R324IncomingExceptionalRootParameter
      rho lam eps kappaM) × L) :
    r324PaperLeftExceptionalParameterMeasurableEquiv
        rho lam eps kappaM L q =
      ((q.1.1, (q.1.2.1.1, (q.1.2.1.2, q.1.2.2))), q.2) := by
  rfl

theorem measurePreserving_r324PaperLeftExceptionalParameterMeasurableEquiv
    (rho : SmoothCutoff) (lam eps : Real) {m : Nat}
    (kappaM : PartialPairing (Fin m))
    {L : Type*} [MeasurableSpace L]
    (muL : Measure L) [SFinite muL] :
    MeasurePreserving
      (r324PaperLeftExceptionalParameterMeasurableEquiv
        rho lam eps kappaM L)
      ((paperMeasure.prod
        (r324IncomingExceptionalRootParameterMeasure
          rho lam eps kappaM)).prod muL)
      ((paperMeasure.prod (paperMeasure.prod
        (r324PaperLeftOuterParameterMeasure
          rho lam eps kappaM))).prod muL) := by
  unfold r324PaperLeftExceptionalParameterMeasurableEquiv
    r324IncomingExceptionalRootParameterMeasure
    r324PaperLeftOuterParameterMeasure
  exact
    ((MeasurePreserving.id paperMeasure).prod
      (measurePreserving_prodAssoc paperMeasure
        (paperMeasure.prod paperMeasure)
        (Measure.pi fun _ :
          (R324WithinHalfResidualPrefix.initial
            rho lam eps kappaM).SurvivingCoordinate => paperMeasure))).prod
      (MeasurePreserving.id muL)

/-! ## Exceptional/direct -/

/-- The genuine paired-incoming physical root is the source of the literal
left `ED` transform.  This is only the already proved physical splice read
through the common endpoint interface. -/
theorem leftExceptionalDirect_exactTransform_and_source_eq_physical
    (p : R324RefinedScheduleIndex m)
    (e0 : MomentContraction m)
    (he0 : e0 ∈ momentRefinedContractionFiber m p.1.1 p.2.1)
    {providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) e0.1 alpha}
    (houtgoing : Fin.last m ∉ extractedRightEdges e0.1)
    (data : R324PaperHalfExceptionalDirectRoute providers)
    (beta : Z4) :
    ∃ transform :
        (R324PaperHalfEndpointUniformBound.ofExceptionalDirect
          houtgoing data).ExactTransform
          (r324PaperLeftOuterParameterMeasure rho lam eps e0.2.1)
          (fun s v =>
            r324PaperLeftCanonicalCoefficient data.transport.final
              alpha beta e0.2.2 s v)
          beta,
      transform.source =
        r324RefinedPhysicalIntegral rho eps m alpha beta p := by
  let hactive : data.transport.final.state.active.Nonempty :=
    data.transport.final.active_nonempty_of_directOutgoing
      providers.hm data.transport.final_processed_eq_schedule houtgoing
  have hG : ∀ j,
      MemEClassT4 (data.pack.data.stopContext.internalEdges j) := by
    intro j
    exact data.pack.data.trace.stopCertificate.memE
      (data.pack.data.stopContext.internalSlot j)
  have hint :
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
          (Measure.pi fun _ => paperMeasure) := by
    intro gap first kappaB
    exact
      R324WithinHalfEdgeCertificate.integrable_stepClosedIntegrand_section
        (ctx := data.pack.data.stopContext)
        data.pack.data.trace.stopCertificate
        providers.heps providers.heps1 kappaB first (first + gap)
  have hcert :
      R324WithinHalfEdgeCertificate data.transport.final.state
        data.route.terminalScale := by
    rw [← data.route_final]
    exact data.route.terminalCertificate
  have hjoint :=
    data.pack.data.driverTerminalJointIntegrable_of_terminal_certificate
      data.transport alpha beta e0.2.2 providers.heps providers.heps1
      data.route.terminalScale hcert
  have hdirect : r324OutgoingIsShortcut e0.1 = false := by
    simp [r324OutgoingIsShortcut, houtgoing]
  have hexact :=
    data.pack.data
      |>.lamEps_pow_r324RefinedPhysicalIntegral_eq_incomingExceptional_directOutgoing
        p e0 he0 data.transport providers.hm providers.heps providers.heps1
        hG hint alpha beta hjoint hactive hdirect
  let coefficient := fun
      (s : R324PaperLeftOuterParameter rho lam eps e0.2.1)
      (v : data.transport.final.SurvivingCoordinate -> T4) =>
    r324PaperLeftCanonicalCoefficient data.transport.final
      alpha beta e0.2.2 s v
  let transform :
      (R324PaperHalfEndpointUniformBound.ofExceptionalDirect
        houtgoing data).ExactTransform
        (r324PaperLeftOuterParameterMeasure rho lam eps e0.2.1)
        coefficient beta :=
    { source := r324RefinedPhysicalIntegral rho eps m alpha beta p
      exact_transform := by
        change (lamEps lam eps : Complex) ^
              (2 * (R324WithinHalfResidualPrefix.initial
                rho lam eps e0.1).remainingOrder) *
            r324RefinedPhysicalIntegral rho eps m alpha beta p =
          ∫ s : R324PaperLeftOuterParameter rho lam eps e0.2.1,
            ∫ v : data.transport.final.SurvivingCoordinate -> T4,
              data.endpointDensity hactive (coefficient s) beta v
              ∂Measure.pi fun _ => paperMeasure
            ∂r324PaperLeftOuterParameterMeasure rho lam eps e0.2.1
        rw [hexact]
        apply integral_congr_ae
        filter_upwards with s
        apply integral_congr_ae
        filter_upwards with v
        unfold R324PaperHalfExceptionalDirectRoute.endpointDensity
          R324PaperHalfExceptionalDirectRoute.incomingEndpointCoefficient
          R324IncomingExceptionalStopTraceAssembly.incomingExceptionalRefinedRootDriverReducedCoefficient
          R324WithinHalfResidualPrefix.incomingExceptionalHeadCollapseFactor
        dsimp only [coefficient, r324PaperLeftCanonicalCoefficient]
        simp only [R324IncomingExceptionalStopTraceAssembly.stopContext,
          R324WithinHalfResidualPrefix.headContext]
        ring }
  exact ⟨transform, rfl⟩

/-! ## Exceptional/exceptional -/

/-- The paired-incoming physical root is the source of the literal left
`EE` transform.  Joint integrability at the retained outgoing terminal is
transported by the endpoint witness itself; this is the paper's Fubini
handover, not an additional estimate. -/
theorem leftExceptionalExceptional_exactTransform_and_source_eq_physical_with_targetIntegrable
    (p : R324RefinedScheduleIndex m)
    (e0 : MomentContraction m)
    (he0 : e0 ∈ momentRefinedContractionFiber m p.1.1 p.2.1)
    {providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) e0.1 alpha}
    (hsingles : e0.1.singles.Nonempty)
    (data : R324PaperHalfExceptionalExceptionalRoute providers)
    (beta : Z4) :
    ∃ transform :
        (R324PaperHalfEndpointUniformBound.ofExceptionalExceptional
          hsingles data).ExactTransform
          (r324PaperLeftOuterParameterMeasure rho lam eps e0.2.1)
          (fun s v =>
            r324PaperLeftCanonicalCoefficient data.outgoing.terminalPost
              alpha beta e0.2.2 s v)
          beta,
      transform.source =
          r324RefinedPhysicalIntegral rho eps m alpha beta p ∧
        Integrable
          (fun q :
              R324PaperLeftOuterParameter rho lam eps e0.2.1 ×
                (data.outgoing.terminalPost.SurvivingCoordinate -> T4) =>
            (R324PaperHalfEndpointUniformBound.ofExceptionalExceptional
              hsingles data).density
                (fun v =>
                  r324PaperLeftCanonicalCoefficient
                    data.outgoing.terminalPost alpha beta e0.2.2 q.1 v)
                beta q.2)
          ((r324PaperLeftOuterParameterMeasure rho lam eps e0.2.1).prod
            (Measure.pi fun _ :
              data.outgoing.terminalPost.SurvivingCoordinate =>
                paperMeasure)) := by
  let muU := r324PaperLeftOuterParameterMeasure rho lam eps e0.2.1
  let coefficient := fun
      (s : R324PaperLeftOuterParameter rho lam eps e0.2.1)
      (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4) =>
    r324PaperLeftCanonicalCoefficient data.outgoing.terminalPost
      alpha beta e0.2.2 s v
  have hG : forall j,
      MemEClassT4 (data.pack.data.stopContext.internalEdges j) := by
    intro j
    exact data.pack.data.trace.stopCertificate.memE
      (data.pack.data.stopContext.internalSlot j)
  have hincoming :
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
          (Measure.pi fun _ => paperMeasure) := by
    intro gap first kappaB
    exact
      R324WithinHalfEdgeCertificate.integrable_stepClosedIntegrand_section
        (ctx := data.pack.data.stopContext)
        data.pack.data.trace.stopCertificate
        providers.heps providers.heps1 kappaB first (first + gap)
  have houtgoing :
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
          (Measure.pi fun _ => paperMeasure) := by
    intro gap first kappaB
    exact
      R324WithinHalfEdgeCertificate.integrable_stepClosedIntegrand_section
        (ctx := data.outgoing.terminalContext)
        data.stopBudgetCertificate providers.heps providers.heps1
        kappaB first (first - gap)
  have hcurrentRoot :=
    data.pack.data.integrable_incomingExceptionalRefinedInitialSource
      p e0 he0 providers.heps providers.heps1 alpha beta
  let InitialLeft :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps e0.1).SurvivingCoordinate -> T4
  let muInitialLeft : Measure InitialLeft := Measure.pi fun _ => paperMeasure
  let eCurrent :=
    r324PaperLeftExceptionalParameterMeasurableEquiv
      rho lam eps e0.2.1 InitialLeft
  have heCurrent : MeasurePreserving eCurrent
      ((paperMeasure.prod
        (r324IncomingExceptionalRootParameterMeasure
          rho lam eps e0.2.1)).prod muInitialLeft)
      ((paperMeasure.prod (paperMeasure.prod muU)).prod muInitialLeft) := by
    exact
      measurePreserving_r324PaperLeftExceptionalParameterMeasurableEquiv
        rho lam eps e0.2.1 muInitialLeft
  let FCurrent :=
    data.pack.data.incomingExceptionalInitialSourceDensity
      alpha (fun omega : R324IncomingExceptionalRootParameter
        rho lam eps e0.2.1 => omega.1.1)
      (data.pack.data.incomingExceptionalRefinedRootPostOuter
        alpha beta e0.2.2)
  let GCurrent :=
    data.pack.data.incomingExceptionalInitialSourceDensity
      alpha
      (fun omega : T4 ×
        R324PaperLeftOuterParameter rho lam eps e0.2.1 => omega.1)
      (fun omega v =>
        charT4 beta omega.1 *
          coefficient omega.2
            ((data.outgoing.endpoint.stop
              |>.splitSurvivingPiMeasurableEquiv
                data.outgoing.terminalData.terminal []
                data.outgoing.endpoint.stop_remaining
                (data.outgoing.endpoint.projection v)).2))
  have hpointCurrent (q :
      (T4 × R324IncomingExceptionalRootParameter
        rho lam eps e0.2.1) × InitialLeft) :
      FCurrent q = GCurrent (eCurrent q) := by
    simp only [FCurrent, GCurrent, eCurrent,
      r324PaperLeftExceptionalParameterMeasurableEquiv_apply,
      R324IncomingExceptionalStopTraceAssembly.incomingExceptionalInitialSourceDensity]
    rw [incomingExceptionalRefinedRootPostOuter_eq_char_mul_leftCanonical
      data.pack.data data.outgoing alpha beta e0.2.2 q.1.2.1.1
        (q.1.2.1.2, q.1.2.2)
        ((data.pack.data.trace.stopPrefix
          |>.splitSurvivingPiMeasurableEquiv
            data.pack.data.terminal data.pack.data.suffix
            data.pack.data.trace.stopPrefix_remaining_eq
            (data.pack.data.trace.stopProjection q.2)).2)]
  have hcurrent :
      Integrable
        (data.pack.data.incomingExceptionalInitialSourceDensity
          alpha
          (fun omega : T4 ×
              R324PaperLeftOuterParameter rho lam eps e0.2.1 => omega.1)
          (fun omega v =>
            charT4 beta omega.1 *
              coefficient omega.2
                ((data.outgoing.endpoint.stop
                  |>.splitSurvivingPiMeasurableEquiv
                    data.outgoing.terminalData.terminal []
                    data.outgoing.endpoint.stop_remaining
                    (data.outgoing.endpoint.projection v)).2)))
        ((paperMeasure.prod (paperMeasure.prod muU)).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps e0.1).SurvivingCoordinate => paperMeasure)) := by
    change Integrable GCurrent
      ((paperMeasure.prod (paperMeasure.prod muU)).prod muInitialLeft)
    refine (heCurrent.integrable_comp_emb eCurrent.measurableEmbedding).mp ?_
    apply hcurrentRoot.congr
    filter_upwards with q
    exact hpointCurrent q
  have hsourceRoot :=
    data.pack.data.integrable_incomingExceptionalRefinedRootStopSource
      p e0 he0 providers.heps providers.heps1 alpha beta
  let StopLeft := data.pack.data.trace.stopPrefix.SurvivingCoordinate -> T4
  let muStopLeft : Measure StopLeft := Measure.pi fun _ => paperMeasure
  let eSource :=
    r324PaperLeftExceptionalParameterMeasurableEquiv
      rho lam eps e0.2.1 StopLeft
  have heSource : MeasurePreserving eSource
      ((paperMeasure.prod
        (r324IncomingExceptionalRootParameterMeasure
          rho lam eps e0.2.1)).prod muStopLeft)
      ((paperMeasure.prod (paperMeasure.prod muU)).prod muStopLeft) := by
    exact
      measurePreserving_r324PaperLeftExceptionalParameterMeasurableEquiv
        rho lam eps e0.2.1 muStopLeft
  let FSource :=
    data.pack.data.incomingExceptionalStopSourceDensity
      alpha (fun omega : R324IncomingExceptionalRootParameter
        rho lam eps e0.2.1 => omega.1.1)
      (data.pack.data.incomingExceptionalRefinedRootPostOuter
        alpha beta e0.2.2)
  let GSource :=
    data.pack.data.incomingExceptionalStopSourceDensity
      alpha
      (fun omega : T4 ×
        R324PaperLeftOuterParameter rho lam eps e0.2.1 => omega.1)
      (fun omega v =>
        charT4 beta omega.1 *
          coefficient omega.2
            ((data.outgoing.endpoint.stop
              |>.splitSurvivingPiMeasurableEquiv
                data.outgoing.terminalData.terminal []
                data.outgoing.endpoint.stop_remaining
                (data.outgoing.endpoint.projection v)).2))
  have hpointSource (q :
      (T4 × R324IncomingExceptionalRootParameter
        rho lam eps e0.2.1) × StopLeft) :
      FSource q = GSource (eSource q) := by
    simp only [FSource, GSource, eSource,
      r324PaperLeftExceptionalParameterMeasurableEquiv_apply]
    unfold R324IncomingExceptionalStopTraceAssembly.incomingExceptionalStopSourceDensity
    rw [incomingExceptionalRefinedRootPostOuter_eq_char_mul_leftCanonical
      data.pack.data data.outgoing alpha beta e0.2.2 q.1.2.1.1
        (q.1.2.1.2, q.1.2.2)
        ((data.pack.data.trace.stopPrefix
          |>.splitSurvivingPiMeasurableEquiv
            data.pack.data.terminal data.pack.data.suffix
            data.pack.data.trace.stopPrefix_remaining_eq q.2).2)]
  have hsource :
      Integrable
        (data.pack.data.incomingExceptionalStopSourceDensity
          alpha
          (fun omega : T4 ×
              R324PaperLeftOuterParameter rho lam eps e0.2.1 => omega.1)
          (fun omega v =>
            charT4 beta omega.1 *
              coefficient omega.2
                ((data.outgoing.endpoint.stop
                  |>.splitSurvivingPiMeasurableEquiv
                    data.outgoing.terminalData.terminal []
                    data.outgoing.endpoint.stop_remaining
                    (data.outgoing.endpoint.projection v)).2)))
        ((paperMeasure.prod (paperMeasure.prod muU)).prod
          (Measure.pi fun _ :
            data.pack.data.trace.stopPrefix.SurvivingCoordinate =>
              paperMeasure)) := by
    change Integrable GSource
      ((paperMeasure.prod (paperMeasure.prod muU)).prod muStopLeft)
    refine (heSource.integrable_comp_emb eSource.measurableEmbedding).mp ?_
    apply hsourceRoot.congr
    filter_upwards with q
    exact hpointSource q
  have hafterRoot :=
    data.pack.data.integrable_incomingExceptionalRefinedRootAfterHeadPhasedIntegrand
      p e0 he0 providers.hm providers.heps providers.heps1
      hG hincoming alpha beta
  let AfterLeft :=
    (data.pack.data.trace.stopPrefix.afterHead
      data.pack.data.terminal data.pack.data.suffix
      data.pack.data.trace.stopPrefix_remaining_eq).SurvivingCoordinate -> T4
  let muAfterLeft : Measure AfterLeft := Measure.pi fun _ => paperMeasure
  let eAfter := r324PaperLeftOuterParameterMeasurableEquiv
    rho lam eps e0.2.1 AfterLeft
  have heAfter : MeasurePreserving eAfter
      ((r324IncomingExceptionalRootParameterMeasure
        rho lam eps e0.2.1).prod muAfterLeft)
      ((paperMeasure.prod muU).prod muAfterLeft) := by
    exact measurePreserving_r324PaperLeftOuterParameterMeasurableEquiv
      rho lam eps e0.2.1 muAfterLeft
  let FAfter :=
    data.pack.data.incomingExceptionalAfterHeadPhasedIntegrand
      alpha (fun omega : R324IncomingExceptionalRootParameter
        rho lam eps e0.2.1 => omega.1.1)
      (data.pack.data.incomingExceptionalRefinedRootPostOuter
        alpha beta e0.2.2)
  let GAfter := fun q :
      (T4 × R324PaperLeftOuterParameter rho lam eps e0.2.1) × AfterLeft =>
    (data.pack.data.trace.stopPrefix.afterHead
      data.pack.data.terminal data.pack.data.suffix
      data.pack.data.trace.stopPrefix_remaining_eq)
      |>.incomingPhasedResidualDensity
        (data.pack.data.incomingExceptionalRefinedRootEndpointCoefficient
          data.outgoing.endpoint alpha beta e0.2.2
          ((q.1.1, q.1.2.1), q.1.2.2)
          (data.outgoing.endpoint.projection q.2))
        alpha rho eps 0 q.1.1 q.2
  have hpointAfter (q :
      R324IncomingExceptionalRootParameter rho lam eps e0.2.1 × AfterLeft) :
      FAfter q = GAfter (eAfter q) := by
    simp only [FAfter, GAfter, eAfter,
      r324PaperLeftOuterParameterMeasurableEquiv_apply]
    exact congrFun
      (data.pack.data
        |>.incomingExceptionalAfterHeadPhasedIntegrand_refinedRoot_endpoint_section_eq
          data.outgoing.endpoint alpha beta e0.2.2 q.1) q.2
  have hafter :
      Integrable
        (fun q :
            (T4 × R324PaperLeftOuterParameter rho lam eps e0.2.1) ×
              ((data.pack.data.trace.stopPrefix.afterHead
                data.pack.data.terminal data.pack.data.suffix
                data.pack.data.trace.stopPrefix_remaining_eq)
                |>.SurvivingCoordinate -> T4) =>
          (data.pack.data.trace.stopPrefix.afterHead
            data.pack.data.terminal data.pack.data.suffix
            data.pack.data.trace.stopPrefix_remaining_eq)
            |>.incomingPhasedResidualDensity
              (data.pack.data.incomingExceptionalRefinedRootEndpointCoefficient
                data.outgoing.endpoint alpha beta e0.2.2
                ((q.1.1, q.1.2.1), q.1.2.2)
                (data.outgoing.endpoint.projection q.2))
              alpha rho eps 0 q.1.1 q.2)
        ((paperMeasure.prod muU).prod
          (Measure.pi fun _ => paperMeasure)) := by
    change Integrable GAfter ((paperMeasure.prod muU).prod muAfterLeft)
    refine (heAfter.integrable_comp_emb eAfter.measurableEmbedding).mp ?_
    apply hafterRoot.congr
    filter_upwards with q
    exact hpointAfter q
  have hendpointWithPhase :=
    data.outgoing.endpoint.integrable_joint
      (paperMeasure.prod muU)
      (fun _ : T4 ×
        R324PaperLeftOuterParameter rho lam eps e0.2.1 => 0)
      (fun omega => omega.1) alpha
      (fun omega u =>
        data.pack.data.incomingExceptionalRefinedRootEndpointCoefficient
          data.outgoing.endpoint alpha beta e0.2.2
          ((omega.1, omega.2.1), omega.2.2) u)
      hafter
  have hphaseMeas : Measurable
      (fun q :
          (T4 × R324PaperLeftOuterParameter rho lam eps e0.2.1) ×
            (data.outgoing.endpoint.stop.SurvivingCoordinate -> T4) =>
        charT4 (-beta) q.1.1) :=
    (continuous_charT4 (-beta)).measurable.comp
      (measurable_fst.comp measurable_fst)
  have hendpointBare :=
    hendpointWithPhase.bdd_mul hphaseMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by rw [norm_charT4])
  have hendpoint :
      Integrable
        (fun q :
            (T4 × R324PaperLeftOuterParameter rho lam eps e0.2.1) ×
              (data.outgoing.endpoint.stop.SurvivingCoordinate -> T4) =>
          data.outgoing.endpoint.stop.incomingPhasedResidualDensity
            (data.outgoing.endpoint.multiplier alpha *
              ((paperSecondOrderModeDecay alpha : Complex) ^ 2 *
                incomingExceptionalPrimitiveDefect rho lam eps
                  (residualBlockOrder data.pack.data.terminal.2)
                  data.pack.data.stopContext.one_le_blockOrder
                  data.pack.data.stopContext.internalEdges alpha *
                coefficient q.1.2
                  ((data.outgoing.endpoint.stop
                    |>.splitSurvivingPiMeasurableEquiv
                      data.outgoing.terminalData.terminal []
                      data.outgoing.endpoint.stop_remaining q.2).2)))
            alpha rho eps 0 q.1.1 q.2)
        ((paperMeasure.prod muU).prod
          (Measure.pi fun _ => paperMeasure)) := by
    apply hendpointBare.congr
    filter_upwards with q
    rw [data.pack.data
      |>.incomingPhasedResidualDensity_endpointCoefficient_eq_char_mul_reduced
        data.outgoing.endpoint alpha beta e0.2.2 q.1.1 q.1.2 q.2]
    rw [data.pack.data
      |>.incomingExceptionalRefinedRootEndpointReducedCoefficient_eq_post
        data.outgoing alpha beta e0.2.2 q.1.2 q.2]
    have hchar :
        charT4 (-beta) q.1.1 * charT4 beta q.1.1 = 1 := by
      rw [mul_comm, charT4_mul_charT4_neg_self]
    rw [← mul_assoc, hchar, one_mul]
    congr 1
  let StopOutgoing :=
    data.outgoing.endpoint.stop.SurvivingCoordinate -> T4
  let muStopOutgoing : Measure StopOutgoing :=
    Measure.pi fun _ => paperMeasure
  let endpointRegroup : (T4 ×
        R324PaperLeftOuterParameter rho lam eps e0.2.1) × StopOutgoing ≃ᵐ
      R324PaperLeftOuterParameter rho lam eps e0.2.1 ×
        (T4 × StopOutgoing) :=
    r324SingleParameterTerminalRegroupMeasurableEquiv
      T4 (R324PaperLeftOuterParameter rho lam eps e0.2.1) StopOutgoing
  have hpEndpointRegroup : MeasurePreserving endpointRegroup
      ((paperMeasure.prod muU).prod muStopOutgoing)
      (muU.prod (paperMeasure.prod muStopOutgoing)) := by
    exact
      measurePreserving_r324SingleParameterTerminalRegroupMeasurableEquiv
        paperMeasure muU muStopOutgoing
  have houtgoingMultiplier :
      data.outgoing.endpoint.multiplier alpha =
        data.endpoint.endpoint.multiplier alpha := by
    simpa using congrArg
      (fun out => out.endpoint.multiplier alpha) data.outgoing_eq
  have hendpointRegroup : Integrable
      (fun q : R324PaperLeftOuterParameter rho lam eps e0.2.1 ×
          (T4 × StopOutgoing) =>
        data.outgoing.endpoint.stop.incomingPhasedResidualDensity
          (data.incomingEndpointCoefficient (coefficient q.1)
            ((data.outgoing.endpoint.stop
              |>.splitSurvivingPiMeasurableEquiv
                data.outgoing.terminalData.terminal []
                data.outgoing.endpoint.stop_remaining q.2.2).2))
          alpha rho eps 0 q.2.1 q.2.2)
      (muU.prod (paperMeasure.prod muStopOutgoing)) := by
    refine (hpEndpointRegroup.integrable_comp_emb
      endpointRegroup.measurableEmbedding).mp ?_
    apply hendpoint.congr
    filter_upwards with q
    simp only [endpointRegroup,
      r324SingleParameterTerminalRegroupMeasurableEquiv_apply,
      Function.comp_apply]
    unfold R324PaperHalfExceptionalExceptionalRoute.incomingEndpointCoefficient
    rw [houtgoingMultiplier]
  have htarget :=
    R324PaperOutgoingEndpointTerminal.integrable_parameter_outgoingEndpointDefectDensity
      data.outgoing
      (data.predecessor_ne_zero_of_singles hsingles)
      (data.terminalPost_active_of_singles hsingles)
      muU
      (fun s v => data.incomingEndpointCoefficient (coefficient s) v)
      alpha beta (fun _ => 0)
      (by
        simpa only [StopOutgoing, muStopOutgoing] using hendpointRegroup)
      houtgoing
  let transform :=
    R324PaperHalfEndpointUniformBound.ExactTransform.ofExceptionalExceptional
      hsingles data muU coefficient beta hG hincoming hcurrent hsource
      hendpoint houtgoing
  refine ⟨transform, ?_, ?_⟩
  change (∫ q, GCurrent q
      ∂((paperMeasure.prod (paperMeasure.prod muU)).prod muInitialLeft)) = _
  rw [data.pack.data
    |>.r324RefinedPhysicalIntegral_eq_incomingExceptionalRefinedInitialSource
      p e0 he0 alpha beta]
  symm
  calc
    (∫ q, FCurrent q
        ∂((paperMeasure.prod
          (r324IncomingExceptionalRootParameterMeasure
            rho lam eps e0.2.1)).prod muInitialLeft)) =
      ∫ q, GCurrent (eCurrent q)
        ∂((paperMeasure.prod
          (r324IncomingExceptionalRootParameterMeasure
            rho lam eps e0.2.1)).prod muInitialLeft) := by
        apply integral_congr_ae
        filter_upwards with q
        exact hpointCurrent q
    _ = ∫ q, GCurrent q
        ∂((paperMeasure.prod (paperMeasure.prod muU)).prod muInitialLeft) :=
      heCurrent.integral_comp eCurrent.measurableEmbedding GCurrent
  simpa only [muU, coefficient,
    R324PaperHalfEndpointUniformBound.ofExceptionalExceptional,
    R324PaperHalfExceptionalExceptionalRoute.endpointDensity] using htarget

/-- Compatibility wrapper retaining the original exact-transform API. -/
theorem leftExceptionalExceptional_exactTransform_and_source_eq_physical
    (p : R324RefinedScheduleIndex m)
    (e0 : MomentContraction m)
    (he0 : e0 ∈ momentRefinedContractionFiber m p.1.1 p.2.1)
    {providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) e0.1 alpha}
    (hsingles : e0.1.singles.Nonempty)
    (data : R324PaperHalfExceptionalExceptionalRoute providers)
    (beta : Z4) :
    ∃ transform :
        (R324PaperHalfEndpointUniformBound.ofExceptionalExceptional
          hsingles data).ExactTransform
          (r324PaperLeftOuterParameterMeasure rho lam eps e0.2.1)
          (fun s v =>
            r324PaperLeftCanonicalCoefficient data.outgoing.terminalPost
              alpha beta e0.2.2 s v)
          beta,
      transform.source =
        r324RefinedPhysicalIntegral rho eps m alpha beta p := by
  obtain ⟨transform, hsource, _⟩ :=
    leftExceptionalExceptional_exactTransform_and_source_eq_physical_with_targetIntegrable
      p e0 he0 hsingles data beta
  exact ⟨transform, hsource⟩

end R324WithinHalfResidualPrefix

end

end Anderson4D
