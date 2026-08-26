import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalRootJointIntegrability

/-!
# Physical refined roots at an exceptional incoming stop

This module closes the exact product-space reindex between one literal
residual-refined physical fibre and the initial source density consumed by
an exceptional incoming trace.  It then exposes the existing trace/Fourier
identity with `r324RefinedPhysicalIntegral` itself on the left.

No sum over refined schedule fibres is performed here.
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
    {m : ℕ} {initialScale : Fin (m + 1) → ℝ}

/-- The literal physical integral of one refined schedule fibre is exactly
the reindexed initial source integral used by an exceptional incoming
left trace. -/
theorem
    r324RefinedPhysicalIntegral_eq_incomingExceptionalRefinedInitialSource
    (p : R324RefinedScheduleIndex m)
    (e₀ : MomentContraction m)
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) e₀.1 initialScale)
    (α β : Z4) :
    r324RefinedPhysicalIntegral ρ ε m α β p =
      ∫ q,
        data.incomingExceptionalInitialSourceDensity
          α
          (fun ω :
              R324IncomingExceptionalRootParameter
                ρ lam ε e₀.2.1 =>
            ω.1.1)
          (data.incomingExceptionalRefinedRootPostOuter
            α β e₀.2.2) q
        ∂((paperMeasure.prod
            (r324IncomingExceptionalRootParameterMeasure
              ρ lam ε e₀.2.1)).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).SurvivingCoordinate =>
                paperMeasure)) := by
  let e :=
    r324IncomingExceptionalRootMeasurableEquiv
      ρ lam ε e₀.1 e₀.2.1
  let target :=
    data.incomingExceptionalInitialSourceDensity
      α
      (fun ω :
          R324IncomingExceptionalRootParameter
            ρ lam ε e₀.2.1 =>
        ω.1.1)
      (data.incomingExceptionalRefinedRootPostOuter
        α β e₀.2.2)
  have he :
      MeasurePreserving e
        (r324PhysicalMeasure m)
        ((paperMeasure.prod
            (r324IncomingExceptionalRootParameterMeasure
              ρ lam ε e₀.2.1)).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).SurvivingCoordinate =>
                paperMeasure)) :=
    measurePreserving_r324IncomingExceptionalRootMeasurableEquiv
      ρ lam ε e₀.1 e₀.2.1
  unfold r324RefinedPhysicalIntegral
  calc
    (∫ q,
        r324Flatten
          (momentRefinedPhysicalIntegrand
            ρ ε m α β p.1.1 p.2.1) q
        ∂(r324PhysicalMeasure m)) =
        ∫ q, target (e q)
          ∂(r324PhysicalMeasure m) := by
      apply integral_congr_ae
      filter_upwards with q
      exact
        data.r324Flatten_momentRefinedPhysicalIntegrand_eq_initialSource_reindex
          e₀ α β p.1.1 p.2.1 he₀ q
    _ =
        ∫ q, target q
          ∂((paperMeasure.prod
              (r324IncomingExceptionalRootParameterMeasure
                ρ lam ε e₀.2.1)).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.1).SurvivingCoordinate =>
                  paperMeasure)) :=
      he.integral_comp e.measurableEmbedding target

/-- The exceptional incoming trace/Fourier identity with the genuine
single-fibre physical root integral on the left.  Root integrability and
all Fubini premises are discharged internally. -/
theorem
    lamEps_pow_r324RefinedPhysicalIntegral_eq_incomingExceptionalStopFourier
    (p : R324RefinedScheduleIndex m)
    (e₀ : MomentContraction m)
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) e₀.1 initialScale)
    (hm : 0 < m)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (α β : Z4) :
    (lamEps lam ε : ℂ) ^
          (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).remainingOrder) *
        r324RefinedPhysicalIntegral
          ρ ε m α β p =
      (lamEps lam ε : ℂ) ^
          (2 * data.trace.stopPrefix.remainingOrder) *
        (∫ q,
          data.incomingExceptionalStopFourierDensity
            α
            (fun ω :
                R324IncomingExceptionalRootParameter
                  ρ lam ε e₀.2.1 =>
              ω.1.1)
            (data.incomingExceptionalRefinedRootPostOuter
              α β e₀.2.2) q
          ∂((r324IncomingExceptionalRootParameterMeasure
              ρ lam ε e₀.2.1).prod
            ((Measure.pi fun _ :
                Fin (2 *
                  residualBlockOrder data.terminal.2) =>
                    paperMeasure).prod
              (Measure.pi fun _ :
                (data.trace.stopPrefix.afterHead
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                    paperMeasure)))) := by
  rw [
    data.r324RefinedPhysicalIntegral_eq_incomingExceptionalRefinedInitialSource
      p e₀ he₀ α β]
  exact
    data.lamEps_pow_integral_refinedInitialSource_eq_incomingExceptionalStopFourier
      p e₀ he₀ hm hε hε1 α β

end R324IncomingExceptionalStopTraceAssembly
end R324WithinHalfResidualPrefix

end

end Anderson4D
