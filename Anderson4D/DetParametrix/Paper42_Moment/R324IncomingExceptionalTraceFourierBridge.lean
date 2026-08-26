import Anderson4D.DetParametrix.Paper42_Moment.R324StopTraceJointIntegrability
import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalPhysicalFubini

/-!
# From the initial R-324 trace to an incoming stop Fourier density

This module composes two exact operations:

* certified integration of every analytic block before an exceptional
  incoming stop; and
* endpoint-first Fourier evaluation at that stop.

The retained exceptional head and its complete suffix remain uncollapsed.
Consequently the right-hand side keeps the exact perturbative power of the
whole stopping suffix.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix
namespace R324IncomingExceptionalStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- The genuine density at the all-Green initial prefix whose incoming
endpoint will be Fourier transformed at the certified exceptional stop.

The character precedes the post-stop outer factor, exactly as in
`incomingExceptionalStopSourceDensity`. -/
def incomingExceptionalInitialSourceDensity
    {Ω : Type*}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (k : Z4) (y : Ω → T4)
    (postOuter :
      Ω →
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4) → ℂ)
    (p :
      (T4 × Ω) ×
        ((R324WithinHalfResidualPrefix.initial
          ρ lam ε κ).SurvivingCoordinate → T4)) : ℂ :=
  let initial :=
    R324WithinHalfResidualPrefix.initial ρ lam ε κ
  let split :=
    data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
  (initial.residualIntegrand
      ρ ε p.1.1 (y p.1.2)
      (initial.reconstruct p.2) : ℂ) *
    (charT4 k p.1.1 *
      postOuter p.1.2
        (split (data.trace.stopProjection p.2)).2)

/-- Exact transport from the all-Green initial residual integral to the
incoming-endpoint Fourier density at an exceptional stop.

One genuine initial joint-integrability premise licenses both the complete
prefix trace and the endpoint Fubini exchange.  No additional stop
integrability or weighted-trace premise is assumed. -/
theorem
    lamEps_pow_integral_initialResidual_eq_incomingExceptionalStopFourier
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [SFinite ν]
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (hm : 0 < m)
    (k : Z4) (y : Ω → T4)
    (postOuter :
      Ω →
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4) → ℂ)
    (hcurrent :
      Integrable
        (data.incomingExceptionalInitialSourceDensity
          k y postOuter)
        ((paperMeasure.prod ν).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κ).SurvivingCoordinate =>
                paperMeasure))) :
    (lamEps lam ε : ℂ) ^
          (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κ).remainingOrder) *
        (∫ p,
          data.incomingExceptionalInitialSourceDensity
            k y postOuter p
          ∂((paperMeasure.prod ν).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε κ).SurvivingCoordinate =>
                  paperMeasure))) =
      (lamEps lam ε : ℂ) ^
          (2 * data.trace.stopPrefix.remainingOrder) *
        (∫ p,
          data.incomingExceptionalStopFourierDensity
            k y postOuter p
          ∂(ν.prod
            ((Measure.pi fun _ :
                Fin (2 * residualBlockOrder data.terminal.2) =>
                  paperMeasure).prod
              (Measure.pi fun _ :
                (data.trace.stopPrefix.afterHead
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                    paperMeasure)))) := by
  let initial :=
    R324WithinHalfResidualPrefix.initial ρ lam ε κ
  let split :=
    data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
  let stopOuter :
      T4 × Ω →
        (data.trace.stopPrefix.SurvivingCoordinate → T4) → ℂ :=
    fun ep w =>
      charT4 k ep.1 *
        postOuter ep.2 (split w).2
  have hcurrent' :
      Integrable
        (fun p :
            (T4 × Ω) ×
              (initial.SurvivingCoordinate → T4) =>
          (initial.residualIntegrand
              ρ ε p.1.1 (y p.1.2)
              (initial.reconstruct p.2) : ℂ) *
            stopOuter p.1
              (data.trace.stopProjection p.2))
        ((paperMeasure.prod ν).prod
          (Measure.pi fun _ :
            initial.SurvivingCoordinate =>
              paperMeasure)) := by
    exact hcurrent
  have hstop :
      Integrable
        (fun p :
            (T4 × Ω) ×
              (data.trace.stopPrefix.SurvivingCoordinate → T4) =>
          (data.trace.stopPrefix.residualIntegrand
              ρ ε p.1.1 (y p.1.2)
              (data.trace.stopPrefix.reconstruct p.2) : ℂ) *
            stopOuter p.1 p.2)
        ((paperMeasure.prod ν).prod
          (Measure.pi fun _ :
            data.trace.stopPrefix.SurvivingCoordinate =>
              paperMeasure)) :=
    data.trace.integrable_joint_residualIntegrand_mul_stopOuter_stopPrefix
      (paperMeasure.prod ν)
      (fun ep : T4 × Ω => ep.1)
      (fun ep : T4 × Ω => y ep.2)
      stopOuter hcurrent'
  have hsource :
      Integrable
        (data.incomingExceptionalStopSourceDensity
          k y postOuter)
        ((paperMeasure.prod ν).prod
          (Measure.pi fun _ :
            data.trace.stopPrefix.SurvivingCoordinate =>
              paperMeasure)) := by
    exact hstop
  have htrace :=
    data.trace.lamEps_pow_integral_joint_mul_stopOuter_eq_stop
      (paperMeasure.prod ν)
      (fun ep : T4 × Ω => ep.1)
      (fun ep : T4 × Ω => y ep.2)
      stopOuter hcurrent'
  have hfubini :=
    data.integral_incomingExceptionalStopSourceDensity_eq_fourierDensity
      ν hm k y postOuter hsource
  calc
    (lamEps lam ε : ℂ) ^
          (2 * initial.remainingOrder) *
        (∫ p,
          data.incomingExceptionalInitialSourceDensity
            k y postOuter p
          ∂((paperMeasure.prod ν).prod
            (Measure.pi fun _ :
              initial.SurvivingCoordinate =>
                paperMeasure))) =
        (lamEps lam ε : ℂ) ^
            (2 * data.trace.stopPrefix.remainingOrder) *
          (∫ p,
            data.incomingExceptionalStopSourceDensity
              k y postOuter p
            ∂((paperMeasure.prod ν).prod
              (Measure.pi fun _ :
                data.trace.stopPrefix.SurvivingCoordinate =>
                  paperMeasure))) := by
      exact htrace
    _ =
        (lamEps lam ε : ℂ) ^
            (2 * data.trace.stopPrefix.remainingOrder) *
          (∫ p,
            data.incomingExceptionalStopFourierDensity
              k y postOuter p
            ∂(ν.prod
              ((Measure.pi fun _ :
                  Fin (2 * residualBlockOrder data.terminal.2) =>
                    paperMeasure).prod
                (Measure.pi fun _ :
                  (data.trace.stopPrefix.afterHead
                    data.terminal data.suffix
                    data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                      paperMeasure)))) := by
      exact congrArg
        (fun z : ℂ =>
          (lamEps lam ε : ℂ) ^
              (2 * data.trace.stopPrefix.remainingOrder) * z)
        hfubini

end R324IncomingExceptionalStopTraceAssembly
end R324WithinHalfResidualPrefix

end

end Anderson4D
