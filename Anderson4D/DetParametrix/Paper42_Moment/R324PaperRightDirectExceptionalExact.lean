import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRightRouteExactPackage
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperOutgoingEndpointTargetIntegrability

/-!
# Right direct/exceptional endpoint handoff

The completed left density stays signed while the direct right incoming
Fourier variable, all intervening intervals, and the retained right outgoing
terminal are removed in the paper order.  No norm or endpoint estimate is
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

/-- The literal right `DE` row, using only the signed completed-left handoff
and the retained-terminal Fubini license. -/
theorem exists_of_directExceptional
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta)
    (hfirst : (⟨0, rightProviders.hm⟩ : Fin m) ∈ finalActive e0.2.1)
    (houtgoing : Fin.last m ∈ extractedRightEdges e0.2.1)
    (data : R324PaperHalfDirectExceptionalRoute rightProviders) :
    Nonempty (R324PaperRightRouteExactPackage left
      (.directExceptional hfirst houtgoing data)) := by
  let right :=
    R324PaperHalfEndpointUniformBound.ofDirectExceptional data
  let Left := left.bound.carrier.SurvivingCoordinate -> T4
  let Initial :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps e0.2.1).SurvivingCoordinate -> T4
  let Stop := data.geometry.transport.stop.SurvivingCoordinate -> T4
  let muLeft : Measure Left := Measure.pi fun _ => paperMeasure
  let muInitial : Measure Initial := Measure.pi fun _ => paperMeasure
  let muStop : Measure Stop := Measure.pi fun _ => paperMeasure
  let project := fun (v : Initial) =>
    (data.outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
      data.outgoing.terminalData.terminal []
      data.outgoing.endpoint.stop_remaining
      (data.outgoing.endpoint.projection v)).2
  let coefficient := fun
      (leftPost : Left)
      (rightPost : data.outgoing.terminalPost.SurvivingCoordinate -> T4) =>
    left.bound.density
      (fun _ => left.bound.crossCoefficient right e0.2.2
        leftPost rightPost)
      beta leftPost
  obtain ⟨hinitial, hregroup⟩ :=
    left.bound.integrable_and_integral_completedLeft_eq_rightDirectInitialSource
      beta e0.2.2 project
      (fun leftPost rightPost =>
        left.bound.crossCoefficient right e0.2.2 leftPost rightPost)
      left.density_mul
      (by
        intro s v
        unfold project R324PaperHalfEndpointUniformBound.crossCoefficient
        exact_mod_cast
          r324ResidualPrimitiveSumProduct_eq_rightDirectOutgoingTerminalPost
            left.bound.carrier data e0.2.2 v s.2)
      left.target_integrable
  let regroup :=
    r324SingleParameterTerminalRegroupMeasurableEquiv
      T4 Left Initial
  have hpRegroup : MeasurePreserving regroup
      ((paperMeasure.prod muLeft).prod muInitial)
      (muLeft.prod (paperMeasure.prod muInitial)) := by
    exact
      measurePreserving_r324SingleParameterTerminalRegroupMeasurableEquiv
        paperMeasure muLeft muInitial
  let current : Left × (T4 × Initial) -> Complex := fun q =>
    (R324WithinHalfResidualPrefix.initial rho lam eps e0.2.1
      |>.incomingPhasedResidualDensity
        (R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient
          data coefficient q.1
            ((data.geometry.transport.stop
              |>.splitSurvivingPiMeasurableEquiv
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton
                (data.geometry.transport.projection q.2.2)).2))
        (-alpha) rho eps 0 q.2.1 q.2.2)
  let withPhase : Left × (T4 × Initial) -> Complex := fun q =>
    charT4 (-beta) q.2.1 * current q
  have hpoint (q : (T4 × Left) × Initial) :
      (R324WithinHalfResidualPrefix.initial rho lam eps e0.2.1
        |>.incomingPhasedResidualDensity
          ((paperSecondOrderModeDecay (-alpha) : Complex) *
            (charT4 (-beta) q.1.1 *
              left.bound.density
                (fun v => left.bound.crossCoefficient right e0.2.2
                  v (project q.2))
                beta q.1.2))
          (-alpha) rho eps 0 q.1.1 q.2) =
        withPhase (regroup q) := by
    have hdensity :
        left.bound.density
            (fun v => left.bound.crossCoefficient right e0.2.2
              v (project q.2))
            beta q.1.2 =
          coefficient q.1.2 (project q.2) := by
      dsimp only [coefficient]
      apply left.density_congr_at
      rfl
    rw [hdensity]
    simp only [regroup,
      r324SingleParameterTerminalRegroupMeasurableEquiv_apply]
    unfold withPhase current project coefficient
    rw [directExceptionalGeometryCoefficient_initialProjection data
        (fun leftPost rightPost =>
          left.bound.density
            (fun _ => left.bound.crossCoefficient right e0.2.2
              leftPost rightPost)
            beta leftPost)
        q.1.2 q.2]
    unfold R324PaperHalfDirectExceptionalRoute.directIncomingEndpointCoefficient
    rw [show
      (paperSecondOrderModeDecay (-alpha) : Complex) *
          (charT4 (-beta) q.1.1 *
            left.bound.density
              (fun v => left.bound.crossCoefficient right e0.2.2
                q.1.2
                  ((data.outgoing.endpoint.stop
                    |>.splitSurvivingPiMeasurableEquiv
                      data.outgoing.terminalData.terminal []
                      data.outgoing.endpoint.stop_remaining
                      (data.outgoing.endpoint.projection q.2)).2))
              beta q.1.2) =
        charT4 (-beta) q.1.1 *
          ((paperSecondOrderModeDecay (-alpha) : Complex) *
            left.bound.density
              (fun v => left.bound.crossCoefficient right e0.2.2
                q.1.2
                  ((data.outgoing.endpoint.stop
                    |>.splitSurvivingPiMeasurableEquiv
                      data.outgoing.terminalData.terminal []
                      data.outgoing.endpoint.stop_remaining
                      (data.outgoing.endpoint.projection q.2)).2))
              beta q.1.2) by ring]
    exact
      (R324WithinHalfResidualPrefix.initial rho lam eps e0.2.1
        |>.incomingPhasedResidualDensity_const_mul
          (charT4 (-beta) q.1.1)
          ((paperSecondOrderModeDecay (-alpha) : Complex) *
            left.bound.density
              (fun v => left.bound.crossCoefficient right e0.2.2
                q.1.2
                  ((data.outgoing.endpoint.stop
                    |>.splitSurvivingPiMeasurableEquiv
                      data.outgoing.terminalData.terminal []
                      data.outgoing.endpoint.stop_remaining
                      (data.outgoing.endpoint.projection q.2)).2))
              beta q.1.2)
          (-alpha) rho eps 0 q.1.1 q.2)
  have hphaseOnSource : Integrable (withPhase ∘ regroup)
      ((paperMeasure.prod muLeft).prod muInitial) := by
    apply hinitial.congr
    filter_upwards with q
    exact hpoint q
  have hwithPhase : Integrable withPhase
      (muLeft.prod (paperMeasure.prod muInitial)) :=
    (hpRegroup.integrable_comp_emb regroup.measurableEmbedding).mp
      hphaseOnSource
  let inversePhase : Left × (T4 × Initial) -> Complex := fun q =>
    charT4 (-(-beta)) q.2.1
  have hinversePhaseMeas : Measurable inversePhase :=
    (continuous_charT4 (-(-beta))).measurable.comp
      (measurable_fst.comp measurable_snd)
  have hcurrentWithInverse :=
    hwithPhase.mul_bdd hinversePhaseMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by
        unfold inversePhase
        rw [norm_charT4])
  have hcurrent : Integrable current
      (muLeft.prod (paperMeasure.prod muInitial)) := by
    apply hcurrentWithInverse.congr
    filter_upwards with q
    unfold withPhase inversePhase
    calc
      (charT4 (-beta) q.2.1 * current q) *
          charT4 (-(-beta)) q.2.1 =
        (charT4 (-beta) q.2.1 * charT4 (-(-beta)) q.2.1) *
          current q := by ring
      _ = current q := by
        rw [charT4_mul_charT4_neg_self, one_mul]
  let assocInitial : (Left × T4) × Initial ≃ᵐ
      Left × (T4 × Initial) := MeasurableEquiv.prodAssoc
  have hpAssocInitial : MeasurePreserving assocInitial
      ((muLeft.prod paperMeasure).prod muInitial)
      (muLeft.prod (paperMeasure.prod muInitial)) :=
    measurePreserving_prodAssoc muLeft paperMeasure muInitial
  have hcurrentAssoc : Integrable
      (fun q : (Left × T4) × Initial => current (assocInitial q))
      ((muLeft.prod paperMeasure).prod muInitial) :=
    (hpAssocInitial.integrable_comp_emb
      assocInitial.measurableEmbedding).mpr hcurrent
  have hendpointInput : Integrable
      (fun q : (Left × T4) × Initial =>
        (R324WithinHalfResidualPrefix.initial rho lam eps e0.2.1
          |>.incomingPhasedResidualDensity
            (R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient
              data coefficient q.1.1
                ((data.endpoint.stop
                  |>.splitSurvivingPiMeasurableEquiv
                    data.terminalData.terminal []
                    data.endpoint.stop_remaining
                    (data.endpoint.projection q.2)).2))
            (-alpha) rho eps 0 q.1.2 q.2))
      ((muLeft.prod paperMeasure).prod muInitial) := by
    convert hcurrentAssoc using 1
    funext q
    rfl
  have hstopAssoc :=
    data.endpoint.integrable_joint
      (muLeft.prod paperMeasure)
      (fun _ : Left × T4 => 0)
      (fun q : Left × T4 => q.2) (-alpha)
      (fun q u =>
        R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient
          data coefficient q.1
            ((data.geometry.transport.stop
              |>.splitSurvivingPiMeasurableEquiv
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton u).2))
      hendpointInput
  let assocStop : (Left × T4) × Stop ≃ᵐ
      Left × (T4 × Stop) := MeasurableEquiv.prodAssoc
  have hpAssocStop : MeasurePreserving assocStop
      ((muLeft.prod paperMeasure).prod muStop)
      (muLeft.prod (paperMeasure.prod muStop)) :=
    measurePreserving_prodAssoc muLeft paperMeasure muStop
  have hstop : Integrable
      (fun q : Left × (T4 × Stop) =>
        data.geometry.transport.stop.incomingPhasedResidualDensity
          (data.geometry.transport.multiplier (-alpha) *
            R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient
              data coefficient q.1
                ((data.geometry.transport.stop
                  |>.splitSurvivingPiMeasurableEquiv
                    data.geometry.terminalData.terminal []
                    data.geometry.stop_remaining_eq_singleton q.2.2).2))
          (-alpha) rho eps 0 q.2.1 q.2.2)
      (muLeft.prod (paperMeasure.prod muStop)) := by
    refine (hpAssocStop.integrable_comp_emb
      assocStop.measurableEmbedding).mp ?_
    dsimp only [Stop, muStop,
      R324PaperHalfDirectExceptionalRoute.geometry]
    convert hstopAssoc using 1 <;> rfl
  have hint : forall (gap first : T4)
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
        (Measure.pi fun _ => paperMeasure) := by
    have hcertificate : R324WithinHalfEdgeCertificate
        data.geometry.paperOutgoingTerminal.terminalContext.state
        data.stopBudgetScale := by
      rw [data.geometry_paperOutgoingTerminal]
      exact data.stopBudgetCertificate
    intro gap first kappaB
    exact
      R324WithinHalfEdgeCertificate.integrable_stepClosedIntegrand_section
        (ctx := data.geometry.paperOutgoingTerminal.terminalContext)
        hcertificate rightProviders.heps rightProviders.heps1
        kappaB first (first - gap)
  have hmultiplier : data.geometry.transport.multiplier (-alpha) = 1 := by
    simpa only [R324PaperHalfDirectExceptionalRoute.geometry] using
      data.endpoint_multiplier_eq_one (-alpha)
  have hpredGeometry :
      r324WithinHalfPredecessorSlot
          data.geometry.paperOutgoingTerminal.endpoint.stop.state
          data.geometry.paperOutgoingTerminal.terminalData.terminal ≠ 0 := by
    change r324WithinHalfPredecessorSlot
      data.endpoint.stop.state data.terminalData.terminal ≠ 0
    exact data.predecessor_ne_zero
  have hactiveGeometry :
      data.geometry.paperOutgoingTerminal.terminalPost.state.active.Nonempty := by
    rw [data.geometry_paperOutgoingTerminal]
    exact data.terminalPost_active
  have htargetGeometry :=
    R324PaperOutgoingEndpointTerminal.integrable_parameter_outgoingEndpointDefectDensity
      data.geometry.paperOutgoingTerminal hpredGeometry hactiveGeometry
      muLeft
      (fun s v =>
        data.geometry.transport.multiplier (-alpha) *
          R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient
            data coefficient s v)
      (-alpha) (-beta) (fun _ => 0)
      (by
        dsimp only [Left, Stop, muLeft, muStop, coefficient,
          R324WithinHalfEndpointTerminalGeometry.paperOutgoingTerminal,
          R324PaperHalfDirectExceptionalRoute.geometry]
        convert hstop using 1 <;> rfl)
      hint
  have htargetGeometry' : Integrable
      (fun q : Left ×
          (data.geometry.paperOutgoingTerminal.terminalPost.SurvivingCoordinate ->
            T4) =>
        ∫ first : T4,
          data.geometry.paperOutgoingTerminal.outgoingEndpointDefectDensity
            (R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient
              data coefficient q.1)
            (-alpha) (-beta) 0 q.2 first
          ∂paperMeasure)
      (muLeft.prod (Measure.pi fun _ :
        data.geometry.paperOutgoingTerminal.terminalPost.SurvivingCoordinate =>
          paperMeasure)) := by
    apply htargetGeometry.congr
    filter_upwards with q
    apply integral_congr_ae
    filter_upwards with first
    apply congrArg
      (fun c =>
        data.geometry.paperOutgoingTerminal.outgoingEndpointDefectDensity
          c (-alpha) (-beta) 0 q.2 first)
    funext v
    rw [hmultiplier, one_mul]
  have htarget : Integrable
      (fun q : Left ×
          (data.outgoing.terminalPost.SurvivingCoordinate -> T4) =>
        data.endpointDensity (coefficient q.1) (-beta) 0 q.2)
      (muLeft.prod (Measure.pi fun _ :
        data.outgoing.terminalPost.SurvivingCoordinate => paperMeasure)) := by
    unfold R324PaperHalfDirectExceptionalRoute.endpointDensity
    exact
      R324PaperOutgoingEndpointTerminal.integrable_parameter_outgoingEndpointDefectDensity_transport
        data.geometry_paperOutgoingTerminal muLeft
        (fun s => data.directIncomingEndpointCoefficient (coefficient s))
        (-alpha) (-beta) (fun _ => 0)
        (by
          simpa only [R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient]
            using htargetGeometry')
  let transform :=
    R324PaperHalfEndpointUniformBound.ExactTransform.ofDirectExceptional
      data muLeft coefficient (-beta)
      (by simpa only [Left, Initial, muLeft, muInitial, current] using hcurrent)
      (by
        dsimp only [Left, Stop, muLeft, muStop, coefficient,
          R324PaperHalfDirectExceptionalRoute.geometry]
        convert hstop using 1 <;> rfl)
      hint
  refine ⟨{
    bound := right
    transform := transform
    source_eq_left_target := ?_
    endpoint_integrable := ?_
    density_mul := by
      intro a coefficient outgoingMode v
      exact R324PaperHalfEndpointUniformBound.density_mul_ofDirectExceptional
        data a coefficient outgoingMode v
    density_congr_at := by
      intro leftCoefficient rightCoefficient outgoingMode v h
      dsimp only [right,
        R324PaperHalfEndpointUniformBound.ofDirectExceptional]
        at leftCoefficient rightCoefficient v h ⊢
      unfold R324PaperHalfDirectExceptionalRoute.endpointDensity
      apply integral_congr_ae
      filter_upwards with first
      unfold R324PaperOutgoingEndpointTerminal.outgoingEndpointDefectDensity
        R324PaperOutgoingEndpointTerminal.terminalSplitOuter
        R324PaperHalfDirectExceptionalRoute.directIncomingEndpointCoefficient
      rw [h] }⟩
  · change transform.source = left.bound.transformTarget
      (r324PaperLeftOuterParameterMeasure rho lam eps e0.2.1)
      (fun s v => r324PaperLeftCanonicalCoefficient
        left.bound.carrier alpha beta e0.2.2 s v) beta
    rw [hregroup]
    calc
      transform.source =
          ∫ q : Left × (T4 × Initial), withPhase q
            ∂(muLeft.prod (paperMeasure.prod muInitial)) := by
              rfl
      _ =
          ∫ q : (T4 × Left) × Initial,
            withPhase (regroup q)
            ∂((paperMeasure.prod muLeft).prod muInitial) := by
              exact
                (hpRegroup.integral_comp
                  regroup.measurableEmbedding withPhase).symm
      _ = ∫ q : (T4 × Left) × Initial,
          (R324WithinHalfResidualPrefix.initial rho lam eps e0.2.1
            |>.incomingPhasedResidualDensity
              ((paperSecondOrderModeDecay (-alpha) : Complex) *
                (charT4 (-beta) q.1.1 *
                  left.bound.density
                    (fun v => left.bound.crossCoefficient right e0.2.2
                      v (project q.2))
                    beta q.1.2))
              (-alpha) rho eps 0 q.1.1 q.2)
          ∂((paperMeasure.prod muLeft).prod muInitial) := by
            apply integral_congr_ae
            filter_upwards with q
            exact (hpoint q).symm
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
