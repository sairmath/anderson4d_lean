import Anderson4D.DetParametrix.Paper42_Moment.R324PaperActualEndpointCollapse
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfEndpointTransform

/-!
# The two direct-incoming left endpoint transforms

This is the literal left-half part of paper Step 4(A).  The genuine refined
physical root has already been written as a direct-incoming source in
`R324PaperActualEndpointCollapse`.  Here that source is fed directly to the
existing `DD` and `DE` signed one-half transforms.  The residual primitive
cross factor stays signed and is merely read on the final carrier through
the already proved coordinate projections.

No norm, endpoint sacrifice, or new summation occurs in this file.
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
    {alpha : Z4}
    {providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP alpha}

/-! ## The two coordinate projections -/

/-- A direct/direct transport changes only the presentation of the left
carrier; the canonical signed coefficient itself is unchanged. -/
theorem r324PaperLeftCanonicalCoefficient_eq_directDriver
    (transport : R324WithinHalfAlternatingTransport
      (R324WithinHalfResidualPrefix.initial rho lam eps kappaP))
    (beta : Z4) (pi : kappaP.singles ≃ kappaM.singles)
    (s : R324PaperLeftOuterParameter rho lam eps kappaM)
    (v : (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaP).SurvivingCoordinate → T4) :
    r324PaperLeftCanonicalCoefficient
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
        alpha beta pi s v =
      r324PaperLeftCanonicalCoefficient transport.final
        alpha beta pi s (transport.projection v) := by
  have hcross :=
    r324ResidualPrimitiveSumProduct_eq_leftDirectDriverProjection
      transport pi v s.2
  unfold r324PaperLeftCanonicalCoefficient
  rw [hcross]

/-- Removing the retained outgoing terminal likewise only changes the
presentation on which the canonical signed coefficient is read. -/
theorem r324PaperLeftCanonicalCoefficient_eq_directOutgoing
    (outgoing : R324PaperOutgoingEndpointTerminal
      (R324WithinHalfResidualPrefix.initial rho lam eps kappaP))
    (beta : Z4) (pi : kappaP.singles ≃ kappaM.singles)
    (s : R324PaperLeftOuterParameter rho lam eps kappaM)
    (v : (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaP).SurvivingCoordinate → T4) :
    r324PaperLeftCanonicalCoefficient
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
        alpha beta pi s v =
      r324PaperLeftCanonicalCoefficient outgoing.terminalPost
        alpha beta pi s
        ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
          outgoing.terminalData.terminal []
          outgoing.endpoint.stop_remaining
          (outgoing.endpoint.projection v)).2) := by
  have hcross :=
    r324ResidualPrimitiveSumProduct_eq_leftDirectOutgoingTerminalPost
      outgoing pi v s.2
  unfold r324PaperLeftCanonicalCoefficient
  rw [hcross]

/-- The coefficient transport in the `DE` constructor is exactly the
outgoing-terminal coordinate projection.  This is only dependent transport
along the structural equality already stored by the route. -/
theorem directExceptionalGeometryCoefficient_initialProjection
    (data : R324PaperHalfDirectExceptionalRoute providers)
    {U : Type*}
    (coefficient : U ->
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (s : U)
    (v : (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaP).SurvivingCoordinate -> T4) :
    R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient
        data coefficient s
          ((data.geometry.transport.stop
            |>.splitSurvivingPiMeasurableEquiv
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton
              (data.geometry.transport.projection v)).2) =
      data.directIncomingEndpointCoefficient (coefficient s)
        ((data.outgoing.endpoint.stop
          |>.splitSurvivingPiMeasurableEquiv
            data.outgoing.terminalData.terminal []
            data.outgoing.endpoint.stop_remaining
            (data.outgoing.endpoint.projection v)).2) := by
  rcases data with
    ⟨terminalData, trace, ordinary, stopBudgetScale, stopReachable,
      stopCertificate, stopScale_le_budget, stopBudgetScale_zero_eq_base,
      endpoint, endpoint_eq, outgoing, outgoing_eq, predecessor_ne_zero,
      terminalPost_active, route, route_cases, route_final⟩
  subst outgoing
  rfl

/-! ## Direct/direct -/

/-- The genuine direct-incoming physical source is exactly the source field
of the literal left `DD` transform.  The only analytic premise not already
contained in the physical entrance is integrability on the completed
terminal carrier, which is supplied by the terminal joint-integrability
producer at the final route call site. -/
theorem leftDirectDirect_exactTransform_and_source_eq_physical
    (houtgoing : Fin.last m ∉ extractedRightEdges kappaP)
    (data : R324PaperHalfDirectDirectRoute providers)
    (beta : Z4) (pi : kappaP.singles ≃ kappaM.singles)
    (physical : Complex)
    (hleft : Integrable
      (r324PaperLeftDirectInitialSourceDensity
        (rho := rho) (lam := lam) (eps := eps)
        (kappaP := kappaP) (kappaM := kappaM) alpha beta pi)
      ((paperMeasure.prod
        (r324PaperLeftOuterParameterMeasure rho lam eps kappaM)).prod
        (Measure.pi fun _ :
          (R324WithinHalfResidualPrefix.initial
            rho lam eps kappaP).SurvivingCoordinate => paperMeasure)))
    (hphysical :
      physical =
        ∫ q,
          r324PaperLeftDirectInitialSourceDensity
            (rho := rho) (lam := lam) (eps := eps)
            (kappaP := kappaP) (kappaM := kappaM)
            alpha beta pi q
          ∂((paperMeasure.prod
            (r324PaperLeftOuterParameterMeasure
              rho lam eps kappaM)).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaP).SurvivingCoordinate => paperMeasure)))
    (hterminal : Integrable
      (fun q :
          (T4 × R324PaperLeftOuterParameter rho lam eps kappaM) ×
            (data.transport.final.SurvivingCoordinate → T4) =>
        data.transport.final.incomingPhasedResidualDensity
          (charT4 beta q.1.1 *
            (data.transport.multiplier alpha *
              ((paperSecondOrderModeDecay alpha : Complex) *
                r324PaperLeftCanonicalCoefficient data.transport.final
                  alpha beta pi q.1.2 q.2)))
          alpha rho eps 0 q.1.1 q.2)
      ((paperMeasure.prod
        (r324PaperLeftOuterParameterMeasure rho lam eps kappaM)).prod
        (Measure.pi fun _ :
          data.transport.final.SurvivingCoordinate => paperMeasure))) :
    ∃ transform :
        (R324PaperHalfEndpointUniformBound.ofDirectDirect
          houtgoing data).ExactTransform
          (r324PaperLeftOuterParameterMeasure rho lam eps kappaM)
          (fun s v =>
            r324PaperLeftCanonicalCoefficient data.transport.final
              alpha beta pi s v)
          beta,
      transform.source = physical := by
  let coefficient := fun
      (s : R324PaperLeftOuterParameter rho lam eps kappaM)
      (v : data.transport.final.SurvivingCoordinate → T4) =>
    r324PaperLeftCanonicalCoefficient data.transport.final
      alpha beta pi s v
  have hcurrent : Integrable
      (fun q :
          (T4 × R324PaperLeftOuterParameter rho lam eps kappaM) ×
            ((R324WithinHalfResidualPrefix.initial
              rho lam eps kappaP).SurvivingCoordinate → T4) =>
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaP
          |>.incomingPhasedResidualDensity
            (charT4 beta q.1.1 *
              ((paperSecondOrderModeDecay alpha : Complex) *
                coefficient q.1.2 (data.transport.projection q.2)))
            alpha rho eps 0 q.1.1 q.2))
      ((paperMeasure.prod
        (r324PaperLeftOuterParameterMeasure rho lam eps kappaM)).prod
        (Measure.pi fun _ :
          (R324WithinHalfResidualPrefix.initial
            rho lam eps kappaP).SurvivingCoordinate => paperMeasure)) := by
    apply hleft.congr
    filter_upwards with q
    unfold r324PaperLeftDirectInitialSourceDensity coefficient
    rw [r324PaperLeftCanonicalCoefficient_eq_directDriver
      data.transport beta pi q.1.2 q.2]
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
  let transform :=
    R324PaperHalfEndpointUniformBound.ExactTransform.ofDirectDirect
      houtgoing data
      (r324PaperLeftOuterParameterMeasure rho lam eps kappaM)
      coefficient beta hcurrent hedge
      (by simpa only [coefficient] using hterminal)
  refine ⟨transform, ?_⟩
  have hsource :
      (∫ q :
          (T4 × R324PaperLeftOuterParameter rho lam eps kappaM) ×
            ((R324WithinHalfResidualPrefix.initial
              rho lam eps kappaP).SurvivingCoordinate → T4),
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaP
          |>.incomingPhasedResidualDensity
            (charT4 beta q.1.1 *
              ((paperSecondOrderModeDecay alpha : Complex) *
                coefficient q.1.2 (data.transport.projection q.2)))
            alpha rho eps 0 q.1.1 q.2)
        ∂((paperMeasure.prod
          (r324PaperLeftOuterParameterMeasure rho lam eps kappaM)).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps kappaP).SurvivingCoordinate => paperMeasure))) =
        ∫ q,
          r324PaperLeftDirectInitialSourceDensity
            (rho := rho) (lam := lam) (eps := eps)
            (kappaP := kappaP) (kappaM := kappaM)
            alpha beta pi q
          ∂((paperMeasure.prod
            (r324PaperLeftOuterParameterMeasure rho lam eps kappaM)).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaP).SurvivingCoordinate => paperMeasure)) := by
    apply integral_congr_ae
    filter_upwards with q
    unfold r324PaperLeftDirectInitialSourceDensity coefficient
    rw [r324PaperLeftCanonicalCoefficient_eq_directDriver
      data.transport beta pi q.1.2 q.2]
  change (∫ q :
      (T4 × R324PaperLeftOuterParameter rho lam eps kappaM) ×
        ((R324WithinHalfResidualPrefix.initial
          rho lam eps kappaP).SurvivingCoordinate → T4),
      (R324WithinHalfResidualPrefix.initial rho lam eps kappaP
        |>.incomingPhasedResidualDensity
          (charT4 beta q.1.1 *
            ((paperSecondOrderModeDecay alpha : Complex) *
              coefficient q.1.2 (data.transport.projection q.2)))
          alpha rho eps 0 q.1.1 q.2)
      ∂((paperMeasure.prod
        (r324PaperLeftOuterParameterMeasure rho lam eps kappaM)).prod
        (Measure.pi fun _ :
          (R324WithinHalfResidualPrefix.initial
            rho lam eps kappaP).SurvivingCoordinate => paperMeasure))) = physical
  exact hsource.trans hphysical.symm

/-! ## Direct/exceptional -/

/-- The direct-incoming physical source is also exactly the source of the
literal left `DE` transform.  The small product regroup below only changes
the order from `(outgoing endpoint, outer parameter, internal carrier)` to
the order consumed by the already proved retained-terminal identity.

The displayed `hcurrent`, `hstop`, and fixed-section integrability premises
are precisely those of `ExactTransform.ofDirectExceptional`; no new
analytic assumption is introduced by this adapter. -/
theorem leftDirectExceptional_exactTransform_and_source_eq_physical
    (data : R324PaperHalfDirectExceptionalRoute providers)
    (beta : Z4) (pi : kappaP.singles ≃ kappaM.singles)
    (physical : Complex)
    (hphysical :
      physical =
        ∫ q,
          r324PaperLeftDirectInitialSourceDensity
            (rho := rho) (lam := lam) (eps := eps)
            (kappaP := kappaP) (kappaM := kappaM)
            alpha beta pi q
          ∂((paperMeasure.prod
            (r324PaperLeftOuterParameterMeasure
              rho lam eps kappaM)).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaP).SurvivingCoordinate => paperMeasure)))
    (hcurrent : Integrable
      (fun q :
          R324PaperLeftOuterParameter rho lam eps kappaM ×
            (T4 ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps kappaP).SurvivingCoordinate → T4)) =>
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaP
          |>.incomingPhasedResidualDensity
            (R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient
              data
                (fun s v =>
                  r324PaperLeftCanonicalCoefficient
                    data.outgoing.terminalPost alpha beta pi s v)
                q.1
                ((data.geometry.transport.stop
                  |>.splitSurvivingPiMeasurableEquiv
                    data.geometry.terminalData.terminal []
                    data.geometry.stop_remaining_eq_singleton
                    (data.geometry.transport.projection q.2.2)).2))
            alpha rho eps 0 q.2.1 q.2.2))
      ((r324PaperLeftOuterParameterMeasure rho lam eps kappaM).prod
        (paperMeasure.prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps kappaP).SurvivingCoordinate => paperMeasure))))
    (hstop : Integrable
      (fun q :
          R324PaperLeftOuterParameter rho lam eps kappaM ×
            (T4 ×
              (data.geometry.transport.stop.SurvivingCoordinate → T4)) =>
        data.geometry.transport.stop.incomingPhasedResidualDensity
          (data.geometry.transport.multiplier alpha *
            (R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient
              data
                (fun s v =>
                  r324PaperLeftCanonicalCoefficient
                    data.outgoing.terminalPost alpha beta pi s v)
                q.1
                ((data.geometry.transport.stop
                  |>.splitSurvivingPiMeasurableEquiv
                    data.geometry.terminalData.terminal []
                    data.geometry.stop_remaining_eq_singleton q.2.2).2)))
          alpha rho eps 0 q.2.1 q.2.2)
      ((r324PaperLeftOuterParameterMeasure rho lam eps kappaM).prod
        (paperMeasure.prod
          (Measure.pi fun _ :
            data.geometry.transport.stop.SurvivingCoordinate =>
              paperMeasure))))
    (hint :
      ∀ (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder data.geometry.terminalData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder
              data.geometry.terminalData.terminal.2 - 2) → T4 =>
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
    ∃ transform :
        (R324PaperHalfEndpointUniformBound.ofDirectExceptional data)
          |>.ExactTransform
            (r324PaperLeftOuterParameterMeasure rho lam eps kappaM)
            (fun s v =>
              r324PaperLeftCanonicalCoefficient
                data.outgoing.terminalPost alpha beta pi s v)
            beta,
      transform.source = physical := by
  let Outer := R324PaperLeftOuterParameter rho lam eps kappaM
  let Initial :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaP).SurvivingCoordinate → T4
  let muOuter : Measure Outer :=
    r324PaperLeftOuterParameterMeasure rho lam eps kappaM
  let muInitial : Measure Initial := Measure.pi fun _ => paperMeasure
  let coefficient := fun
      (s : Outer)
      (v : data.outgoing.terminalPost.SurvivingCoordinate → T4) =>
    r324PaperLeftCanonicalCoefficient data.outgoing.terminalPost
      alpha beta pi s v
  let transform :=
    R324PaperHalfEndpointUniformBound.ExactTransform.ofDirectExceptional
      data muOuter coefficient beta
      (by simpa only [Outer, Initial, muOuter, muInitial, coefficient]
        using hcurrent)
      (by simpa only [Outer, muOuter, coefficient] using hstop)
      hint
  refine ⟨transform, ?_⟩
  let regroup :=
    r324SingleParameterTerminalRegroupMeasurableEquiv
      T4 Outer Initial
  have hp : MeasurePreserving regroup
      ((paperMeasure.prod muOuter).prod muInitial)
      (muOuter.prod (paperMeasure.prod muInitial)) := by
    simpa only [regroup] using
      measurePreserving_r324SingleParameterTerminalRegroupMeasurableEquiv
        paperMeasure muOuter muInitial
  let G : Outer × (T4 × Initial) → Complex := fun q =>
    charT4 beta q.2.1 *
      (R324WithinHalfResidualPrefix.initial rho lam eps kappaP
        |>.incomingPhasedResidualDensity
          (R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient
            data coefficient q.1
              ((data.geometry.transport.stop
                |>.splitSurvivingPiMeasurableEquiv
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton
                  (data.geometry.transport.projection q.2.2)).2))
          alpha rho eps 0 q.2.1 q.2.2)
  have hpoint (q : (T4 × Outer) × Initial) :
      r324PaperLeftDirectInitialSourceDensity
          (rho := rho) (lam := lam) (eps := eps)
          (kappaP := kappaP) (kappaM := kappaM)
          alpha beta pi q = G (regroup q) := by
    simp only [regroup,
      r324SingleParameterTerminalRegroupMeasurableEquiv_apply]
    unfold r324PaperLeftDirectInitialSourceDensity G coefficient
    rw [r324PaperLeftCanonicalCoefficient_eq_directOutgoing
      data.outgoing beta pi q.1.2 q.2]
    rw [directExceptionalGeometryCoefficient_initialProjection data
      coefficient q.1.2 q.2]
    unfold R324PaperHalfDirectExceptionalRoute.directIncomingEndpointCoefficient
    exact
      (R324WithinHalfResidualPrefix.initial rho lam eps kappaP
        |>.incomingPhasedResidualDensity_const_mul
          (charT4 beta q.1.1)
          ((paperSecondOrderModeDecay alpha : Complex) *
            r324PaperLeftCanonicalCoefficient
              data.outgoing.terminalPost alpha beta pi q.1.2
              ((data.outgoing.endpoint.stop
                |>.splitSurvivingPiMeasurableEquiv
                  data.outgoing.terminalData.terminal []
                  data.outgoing.endpoint.stop_remaining
                  (data.outgoing.endpoint.projection q.2)).2))
          alpha rho eps 0 q.1.1 q.2)
  have hreindex :
      (∫ q : (T4 × Outer) × Initial,
          r324PaperLeftDirectInitialSourceDensity
            (rho := rho) (lam := lam) (eps := eps)
            (kappaP := kappaP) (kappaM := kappaM)
            alpha beta pi q
          ∂((paperMeasure.prod muOuter).prod muInitial)) =
        ∫ q : Outer × (T4 × Initial), G q
          ∂(muOuter.prod (paperMeasure.prod muInitial)) := by
    calc
      _ = ∫ q : (T4 × Outer) × Initial, G (regroup q)
          ∂((paperMeasure.prod muOuter).prod muInitial) := by
        apply integral_congr_ae
        filter_upwards with q
        exact hpoint q
      _ = _ := hp.integral_comp regroup.measurableEmbedding G
  dsimp only [transform,
    R324PaperHalfEndpointUniformBound.ExactTransform.ofDirectExceptional]
  simpa only [G, Outer, Initial, muOuter, muInitial, coefficient] using
    hreindex.symm.trans hphysical.symm

end R324WithinHalfResidualPrefix

end

end Anderson4D
