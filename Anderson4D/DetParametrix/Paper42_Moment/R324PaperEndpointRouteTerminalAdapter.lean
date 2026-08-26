import Anderson4D.DetParametrix.Paper42_Moment.R324PaperDirectDirectParameterized
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointParameterizedEE
import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingBudgetTerminalAdapter

/-!
# Canonical terminal adapter for the paper endpoint routes

The signed physical-root collapse and the endpoint-route construction may
build their completed within-half prefixes independently.  Both prefixes
are algebraically reachable, have consumed the complete analytic schedule,
and retain the empty suffix.  Reachability is deterministic in the processed
list, so the resulting residual prefix is canonical.

Only the residual prefixes are identified here.  Analytic and numerical
scale functions remain deliberately distinct.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}
    {incomingMode : Z4} {analyticScale : Fin (m + 1) -> Real}

/-- A completed endpoint route and a certified analytic trace from the same
pairing have the same literal terminal residual prefix. -/
theorem R324PaperHalfEndpointRoute.completedRoute_final_eq_certifiedTerminal
    {providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode}
    (route : R324PaperHalfEndpointRoute providers)
    (trace : R324WithinHalfCertifiedAnalyticTrace
      (R324WithinHalfResidualPrefix.initial rho lam eps pairing)
      analyticScale) :
    route.completedRoute.final = trace.terminalPrefix :=
  R324WithinHalfResidualPrefix.eq_of_processed_schedule_of_remaining_nil
    route.completedRoute.final trace.terminalPrefix
    (by
      have hschedule := route.completedRoute.final.schedule_eq
      rw [route.completedRoute.final_remaining, List.append_nil]
        at hschedule
      exact hschedule.symm)
    trace.terminalPrefix_processed_eq_schedule
    route.completedRoute.final_remaining
    trace.terminalPrefix_remaining_eq_nil

variable {kappaP kappaM : PartialPairing (Fin m)}
    {leftMode rightMode : Z4}
    {leftScale rightScale : Fin (m + 1) -> Real}

/-- The two independently constructed terminal packages agree after the two
canonical one-half residual prefixes are identified. -/
theorem R324PaperTwoHalfEndpointRoutes.terminal_eq_ofCertifiedTraces
    {leftProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP leftMode}
    {rightProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM rightMode}
    (routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders)
    (leftTrace : R324WithinHalfCertifiedAnalyticTrace
      (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
      leftScale)
    (rightTrace : R324WithinHalfCertifiedAnalyticTrace
      (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
      rightScale) :
    routes.terminal =
      R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace := by
  have hleft :=
    routes.left.completedRoute_final_eq_certifiedTerminal leftTrace
  have hright :=
    routes.right.completedRoute_final_eq_certifiedTerminal rightTrace
  unfold R324PaperTwoHalfEndpointRoutes.terminal
    R324PaperHalfCompletedRoute.twoHalfTerminal
    R324TwoHalfTerminalData.ofCertifiedTraces
  rw [R324TwoHalfTerminalData.mk.injEq]
  exact ⟨hleft, hright⟩

end R324WithinHalfResidualPrefix

end

end Anderson4D
