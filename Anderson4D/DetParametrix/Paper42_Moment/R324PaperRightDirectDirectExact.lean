import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRightRouteExactPackage

/-!
# Right direct/direct endpoint handoff

This is the direct/direct row of the second-half table.  The completed left
density remains signed while the right incoming and outgoing Fourier
variables are evaluated.  No norm is taken.
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

/-- The paper's two exact Fourier evaluations on the right, with the
completed left half as the untouched parameter. -/
theorem exists_of_directDirect
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta)
    (hfirst : (⟨0, rightProviders.hm⟩ : Fin m) ∈ finalActive e0.2.1)
    (houtgoing : Fin.last m ∉ extractedRightEdges e0.2.1)
    (data : R324PaperHalfDirectDirectRoute rightProviders) :
    Nonempty (R324PaperRightRouteExactPackage left
      (.directDirect hfirst houtgoing data)) := by
  let right :=
    R324PaperHalfEndpointUniformBound.ofDirectDirect houtgoing data
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
  obtain ⟨hcurrent, hregroup⟩ :=
    left.bound.integrable_and_integral_completedLeft_eq_rightDirectInitialSource
      beta e0.2.2 data.transport.projection
      (fun leftPost rightPost =>
        left.bound.crossCoefficient right e0.2.2 leftPost rightPost)
      left.density_mul
      (by
        intro s v
        unfold R324PaperHalfEndpointUniformBound.crossCoefficient
        exact_mod_cast
          r324ResidualPrimitiveSumProduct_eq_rightDirectTransportProjection
            left.bound.carrier data e0.2.2 v s.2)
      left.target_integrable
  have hcurrent' : Integrable
      (fun q : (T4 ×
            (left.bound.carrier.SurvivingCoordinate → T4)) ×
            ((R324WithinHalfResidualPrefix.initial
              rho lam eps e0.2.1).SurvivingCoordinate → T4) =>
        (R324WithinHalfResidualPrefix.initial rho lam eps e0.2.1
          |>.incomingPhasedResidualDensity
            (charT4 (-beta) q.1.1 *
              ((paperSecondOrderModeDecay (-alpha) : ℂ) *
                coefficient q.1.2 (data.transport.projection q.2)))
            (-alpha) rho eps 0 q.1.1 q.2))
      ((paperMeasure.prod μLeft).prod
        (Measure.pi fun _ => paperMeasure)) := by
    apply hcurrent.congr
    filter_upwards with q
    apply congrArg (fun z : ℂ =>
      (R324WithinHalfResidualPrefix.initial rho lam eps e0.2.1
        |>.incomingPhasedResidualDensity z
          (-alpha) rho eps 0 q.1.1 q.2))
    have hdensity :
        left.bound.density
            (fun v => left.bound.crossCoefficient right e0.2.2
              v (data.transport.projection q.2))
            beta q.1.2 =
          coefficient q.1.2 (data.transport.projection q.2) := by
      dsimp only [coefficient]
      apply left.density_congr_at
      rfl
    rw [hdensity]
    ring
  have htransported :=
    data.transport.integrable_joint
      (paperMeasure.prod μLeft)
      (fun _ => 0) (fun q => q.1) (-alpha)
      (fun q v =>
        charT4 (-beta) q.1 *
          ((paperSecondOrderModeDecay (-alpha) : ℂ) *
            coefficient q.2 v))
      hcurrent'
  have hterminal : Integrable
      (fun q : (T4 ×
            (left.bound.carrier.SurvivingCoordinate → T4)) ×
            (data.transport.final.SurvivingCoordinate → T4) =>
        data.transport.final.incomingPhasedResidualDensity
          (charT4 (-beta) q.1.1 *
            (data.transport.multiplier (-alpha) *
              ((paperSecondOrderModeDecay (-alpha) : ℂ) *
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
  let transform :=
    R324PaperHalfEndpointUniformBound.ExactTransform.ofDirectDirect
      houtgoing data μLeft coefficient (-beta)
      hcurrent' hedge hterminal
  have htarget :=
    integrable_singleParameter_directOutgoingResult
      data.transport.final data.transport.final_remaining hactive hedge
      μLeft
      (fun leftPost rightPost =>
        data.transport.multiplier (-alpha) *
          ((paperSecondOrderModeDecay (-alpha) : ℂ) *
            coefficient leftPost rightPost))
      (-beta) (-alpha) hterminal
  refine ⟨{
    bound := right
    transform := transform
    source_eq_left_target := ?_
    endpoint_integrable := ?_
    density_mul := by
      intro a coefficient outgoingMode v
      exact R324PaperHalfEndpointUniformBound.density_mul_ofDirectDirect
        houtgoing data a coefficient outgoingMode v
    density_congr_at := by
      intro leftCoefficient rightCoefficient outgoingMode v h
      dsimp only [right,
        R324PaperHalfEndpointUniformBound.ofDirectDirect]
      unfold R324PaperHalfDirectDirectRoute.transportEndpointDensity
        R324PaperHalfDirectDirectRoute.directIncomingCoefficient
      rw [h] }⟩
  · change transform.source = left.bound.transformTarget
      (r324PaperLeftOuterParameterMeasure rho lam eps e0.2.1)
      (fun s v => r324PaperLeftCanonicalCoefficient
        left.bound.carrier alpha beta e0.2.2 s v) beta
    rw [hregroup]
    apply integral_congr_ae
    filter_upwards with q
    apply congrArg (fun z : ℂ =>
      (R324WithinHalfResidualPrefix.initial rho lam eps e0.2.1
        |>.incomingPhasedResidualDensity z
          (-alpha) rho eps 0 q.1.1 q.2))
    have hdensity :
        left.bound.density
            (fun v => left.bound.crossCoefficient right e0.2.2
              v (data.transport.projection q.2))
            beta q.1.2 =
          coefficient q.1.2 (data.transport.projection q.2) := by
      dsimp only [coefficient]
      apply left.density_congr_at
      rfl
    rw [hdensity]
    ring
  · change Integrable
      (fun q :
          (left.bound.carrier.SurvivingCoordinate → T4) ×
            (data.transport.final.SurvivingCoordinate → T4) =>
        data.transportEndpointDensity
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
      R324PaperHalfDirectDirectRoute.transportEndpointDensity,
      R324PaperHalfDirectDirectRoute.directIncomingCoefficient,
      mul_assoc] using htarget

end R324PaperRightRouteExactPackage
end R324WithinHalfResidualPrefix

end

end Anderson4D
