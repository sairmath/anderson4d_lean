import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRightRouteExactAllCases
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTwoHalfRouteAssembly
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRefinedStep23Closure
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperCompleteNestedRun
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTwoHalfWeightedExit

/-!
# Paper Step 4(A): the residual endpoint-pattern producer

This file is the final assembly of the literal four-endpoint argument in
paper §4.2.  The two signed half transforms are completed before a norm is
taken.  Their common nested endpoint density is then passed, unchanged,
through the existing grouped majorant, complete nested run, and weighted
exit.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open SmoothCutoff

namespace R324WithinHalfResidualPrefix

/-- Uniform paper Step 4(A) producer for the actual endpoint pattern of the
refined-fibre representative. -/
theorem exists_r324PaperResidualEndpointPatternWeightedMajorantBound
    (rho : SmoothCutoff) :
    ∃ primitiveConstant supportConstant : Real,
      0 < primitiveConstant ∧ 0 < supportConstant ∧
      R324PaperResidualEndpointPatternWeightedMajorantBound
        rho primitiveConstant supportConstant := by
  obtain ⟨routeSupport, C, K, A,
      hrouteSupport, hC, hK, hA, hroutes⟩ :=
    exists_r324PaperTwoHalfEndpointRoutes_at_truncation rho
  obtain ⟨runSupport, B, hrunSupport, hB, hrun⟩ :=
    R324TwoHalfTerminalData.exists_integral_completeNestedRunDensity_le_primitiveInsertedMajorant
      rho
  let finalConstant :=
    R324PaperTwoHalfEndpointRoutes.twoHalfEndpointCompleteAbsorbedBase
      A C K B
  have hfinal : 0 < finalConstant := by
    exact R324PaperTwoHalfEndpointRoutes.twoHalfEndpointCompleteAbsorbedBase_pos
      A C K B
  refine ⟨finalConstant, runSupport, hfinal, hrunSupport, ?_⟩
  intro eps m alpha beta heps hepsSmall hlog hm2 hmtrunc p hsingles
  have heps1 : eps ≤ 1 := hepsSmall.trans (by norm_num)
  have hm0 : 0 < m := by omega
  have hm : 1 ≤ m := by omega
  let e0 := r324RefinedContractionRepresentative m p.1.1 p.2.1
  have he0 : e0 ∈ momentRefinedContractionFiber m p.1.1 p.2.1 := by
    exact r324RefinedContractionRepresentative_mem p.2.2
  have hleftSingles : e0.1.singles.Nonempty := by
    exact r324RefinedContractionRepresentative_singles_nonempty p hsingles
  have hrightSingles : e0.2.1.singles.Nonempty := by
    obtain ⟨i, hi⟩ := hleftSingles
    let j : e0.2.1.singles := e0.2.2 ⟨i, hi⟩
    exact ⟨j.1, j.2⟩
  obtain ⟨head, tail, hremaining⟩ :=
    exists_r324InitialNestedCross_head_of_singles_nonempty
      e0.1 e0.2.1 e0.2.2 hleftSingles
  obtain ⟨leftProviders, rightProviders, routes,
      _leftTrace, _rightTrace, _hterminalTrace⟩ :=
    hroutes 1 eps m e0.1 e0.2.1 alpha (-alpha)
      one_pos heps heps1 hlog hmtrunc hm0 hleftSingles hrightSingles
  obtain ⟨left⟩ :=
    R324PaperLeftRouteExactPackage.exists_of_route
      he0 hleftSingles routes.left beta
  obtain ⟨right⟩ :=
    R324PaperRightRouteExactPackage.exists_of_route
      left hrightSingles routes.right
  let localTerminal := left.bound.twoHalfTerminal right.bound
  have hterminal : localTerminal = routes.terminal :=
    R324PaperHalfEndpointUniformBound.twoHalfTerminal_eq_routes
      routes left.bound right.bound
  have hcollapseLocal :=
    R324PaperRightRouteExactPackage.exactCollapse_to_nested left right
  have hendpointLocal :=
    R324PaperHalfEndpointUniformBound.ae_norm_nestedEndpointProductDensity_le_compensatedGrouped
      (beta := beta) routes left.bound right.bound e0.2.2
  have hpackageLocal :
      ∃ endpointDensity :
          (localTerminal.NestedCoordinate e0.2.2 → T4) → Complex,
        (lamEps 1 eps : Complex) ^
              (2 *
                ((R324WithinHalfResidualPrefix.initial
                    rho 1 eps e0.1).remainingOrder +
                  (R324WithinHalfResidualPrefix.initial
                    rho 1 eps e0.2.1).remainingOrder)) *
            r324RefinedPhysicalIntegral rho eps m alpha beta p =
          (∫ v, endpointDensity v
            ∂(Measure.pi fun _ : localTerminal.NestedCoordinate e0.2.2 =>
              paperMeasure)) ∧
        ∃ hleft : localTerminal.left.state.active.Nonempty,
          ∃ hright : localTerminal.right.state.active.Nonempty,
            (fun v => ‖endpointDensity v‖) ≤ᵐ[
              Measure.pi fun _ : localTerminal.NestedCoordinate e0.2.2 =>
                paperMeasure]
              fun v =>
                (R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation *
                  ((paperFourthOrderModeDecay alpha *
                      paperFourthOrderModeDecay beta) *
                    r324EndpointPrimitiveSacrificeProduct eps
                      routes.cases)) *
                  localTerminal.initialNestedEndpointIntegratedGroupedMajorant
                    routes.left.completedRoute.terminalScale
                    routes.right.completedRoute.terminalScale
                    hleft hright e0.2.2 v := by
    refine ⟨(fun v => left.bound.nestedEndpointProductDensity
        right.bound beta e0.2.2 v), ?_, left.bound.active,
      right.bound.active, ?_⟩
    · simpa only [localTerminal] using hcollapseLocal
    · simpa only [localTerminal] using hendpointLocal
  have hpackage := hterminal ▸ hpackageLocal
  obtain ⟨endpointDensity, hcollapse, hleft, hright, hendpoint⟩ :=
    hpackage
  let step :=
    r324InitialNestedCrossStepContext
      e0.1 e0.2.1 e0.2.2 head tail hremaining
  have hleftInitial :
      (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
    change (r324LeftHalfPullback
      (R324NestedCrossResidualPrefix.initial
        e0.1 e0.2.1 e0.2.2).activeCarrier).Nonempty
    rw [R324TwoHalfTerminalData.initial_leftHalfPullback_eq_terminalActive
      routes.terminal e0.2.2]
    exact hleft
  have hrightInitial :
      (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
    change (r324RightHalfPullback
      (R324NestedCrossResidualPrefix.initial
        e0.1 e0.2.1 e0.2.2).activeCarrier).Nonempty
    rw [R324TwoHalfTerminalData.initial_rightHalfPullback_eq_terminalActive
      routes.terminal e0.2.2]
    exact hright
  have hrunBound :
      (∫ v : step.SurvivingCoordinate → T4,
          routes.terminal.completeNestedRunDensity
            step hleftInitial hrightInitial v
          ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) ≤
        ∫ z : T4, primitiveInsertedMajorant
          B 1 eps runSupport step.residual.remainingOrder z
          ∂paperMeasure :=
    hrun routes.terminal one_pos heps heps1 hlog hmtrunc
      step hleftInitial hrightInitial
  have horder :=
    r324InitialSchedules_remainingOrders_eq_ambient
      rho 1 eps e0.1 e0.2.1 e0.2.2
  have hweighted :=
    R324PaperTwoHalfEndpointRoutes.weighted_norm_le_endpointPatternAmbientMajorant_of_grouped_uniform
      routes
        (zero_le_one.trans hA) hC.le (zero_le_one.trans hK) hB.le
        one_pos hleft hright e0.2.2
        head tail hremaining alpha beta
        (r324RefinedPhysicalIntegral rho eps m alpha beta p)
        endpointDensity
        hendpoint heps heps1 hlog hm hmtrunc hrunBound horder hcollapse
  have hcases :
      routes.cases = r324ActualRefinedEndpointReductionCase p := by
    simpa only [r324ActualRefinedEndpointReductionCase,
      r324PaperActualHalfEndpointCases, Matrix.cons_val_zero,
      Matrix.cons_val_one, e0] using
      routes.cases_eq_actual
  rw [hcases] at hweighted
  simpa only [finalConstant] using hweighted

/-- The public residual Step 4(A) input, obtained only after enlarging the
literal four-endpoint case product to the paper's uniform `eps ^ (-8)`
budget. -/
theorem exists_r324PaperResidualEndpointWeightedMajorantBound
    (rho : SmoothCutoff) :
    ∃ primitiveConstant supportConstant : Real,
      0 < primitiveConstant ∧ 0 < supportConstant ∧
      R324PaperResidualEndpointWeightedMajorantBound
        rho primitiveConstant supportConstant := by
  obtain ⟨primitiveConstant, supportConstant,
      hprimitive, hsupport, hpattern⟩ :=
    exists_r324PaperResidualEndpointPatternWeightedMajorantBound rho
  exact ⟨primitiveConstant, supportConstant, hprimitive, hsupport,
    hpattern.to_uniform⟩

end R324WithinHalfResidualPrefix

end

end Anderson4D
