import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfRouteProvidersUniform
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointRouteTerminalAdapter

/-!
# Uniform two-half endpoint-route assembly

This is the structural entrance to paper Step 4(A).  The constants from
Proposition 4.1 are chosen once, the two literal half routes are selected by
their actual endpoint incidences, and the independently generated analytic
traces are identified with the same canonical terminal residual prefixes.

No endpoint absolute value or uniform `eps ^ (-8)` estimate is taken here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

/-- Uniform structural data for the two literal half routes in paper
Step 4(A).  The endpoint cases remain the actual `DD/DE/ED/EE` cases of the
two pairings; their costs are not yet uniformized. -/
theorem exists_r324PaperTwoHalfEndpointRoutes_at_truncation
    (rho : SmoothCutoff) :
    exists supportConstant C K A : Real,
      0 < supportConstant /\ 0 < C /\ 1 <= K /\ 1 <= A /\
        forall (lam eps : Real) (m : Nat)
          (kappaP kappaM : PartialPairing (Fin m))
          (leftMode rightMode : Z4),
          0 < lam -> 0 < eps -> eps <= 1 ->
          1 <= abs (Real.log eps) -> m <= truncOrder eps ->
          0 < m ->
          kappaP.singles.Nonempty -> kappaM.singles.Nonempty ->
          exists leftProviders : R324PaperHalfRouteProviders
              (rho := rho) (C := C) (lam := lam) (eps := eps)
              (K := K) (A := A) kappaP leftMode,
            exists rightProviders : R324PaperHalfRouteProviders
              (rho := rho) (C := C) (lam := lam) (eps := eps)
              (K := K) (A := A) kappaM rightMode,
              exists routes : R324PaperTwoHalfEndpointRoutes
                  leftProviders rightProviders,
                exists leftTrace : R324WithinHalfCertifiedAnalyticTrace
                    (R324WithinHalfResidualPrefix.initial
                      rho lam eps kappaP) (fun _ => A),
                  exists rightTrace : R324WithinHalfCertifiedAnalyticTrace
                      (R324WithinHalfResidualPrefix.initial
                        rho lam eps kappaM) (fun _ => A),
                    routes.terminal =
                      R324TwoHalfTerminalData.ofCertifiedTraces
                        leftTrace rightTrace := by
  obtain ⟨supportConstant, C, K, A,
      hsupport, hC, hK, hA, hproviders⟩ :=
    exists_r324PaperHalfRouteProviders_at_truncation rho
  refine ⟨supportConstant, C, K, A,
    hsupport, hC, hK, hA, ?_⟩
  intro lam eps m kappaP kappaM leftMode rightMode
    hlam heps heps1 hlog htrunc hm hleftSingles hrightSingles
  obtain ⟨leftProviders⟩ :=
    hproviders lam eps m kappaP leftMode
      hlam heps heps1 hlog htrunc hm
  obtain ⟨rightProviders⟩ :=
    hproviders lam eps m kappaM rightMode
      hlam heps heps1 hlog htrunc hm
  obtain ⟨routes⟩ :=
    R324PaperTwoHalfEndpointRoutes.exists_of_singles
      leftProviders rightProviders hleftSingles hrightSingles
  let leftTrace : R324WithinHalfCertifiedAnalyticTrace
      (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
      (fun _ => A) :=
    R324WithinHalfCertifiedAnalyticTrace.of_localBlockProvider
      heps heps1 leftProviders.analyticProvider
      (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
      (fun _ => A) leftProviders.initialCertificate
  let rightTrace : R324WithinHalfCertifiedAnalyticTrace
      (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
      (fun _ => A) :=
    R324WithinHalfCertifiedAnalyticTrace.of_localBlockProvider
      heps heps1 rightProviders.analyticProvider
      (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
      (fun _ => A) rightProviders.initialCertificate
  exact ⟨leftProviders, rightProviders, routes, leftTrace, rightTrace,
    routes.terminal_eq_ofCertifiedTraces leftTrace rightTrace⟩

end R324WithinHalfResidualPrefix

end

end Anderson4D
