import Anderson4D.DetParametrix.Paper42_Moment.R324StopBeforeStepTrace
import Anderson4D.DetParametrix.Paper42_Moment.R324ResidualJointIntegrabilityStep

/-!
# Joint integrability through a stopped R-324 trace

This module propagates genuine joint integrability through every block
actually consumed by an `R324WithinHalfStopBeforeStepTrace`.  The measured
parameter may control both displayed endpoints and the final outer factor.
The proof invokes the concrete one-head joint-integrability theorem at every
step and stops before the named retained block.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix
namespace R324WithinHalfStopBeforeStepTrace

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {terminal : R322ExtractionStep m}
    {suffix : List (R322ExtractionStep m)}

/-- Joint integrability propagates through every genuine head consumed by a
stopped trace.

The hypothesis is the actual current residual density multiplied by the
final stop outer factor pulled back through `stopProjection`.  The
conclusion is the corresponding actual stopped residual density. -/
theorem integrable_joint_residualIntegrand_mul_stopOuter_stopPrefix
    {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [SFinite ν]
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res scale)
    (x y : Y → T4)
    (outer :
      Y →
        (trace.stopPrefix.SurvivingCoordinate → T4) → ℂ)
    (hcurrent :
      Integrable
        (fun p :
            Y × (res.SurvivingCoordinate → T4) =>
          (res.residualIntegrand ρ ε
              (x p.1) (y p.1)
              (res.reconstruct p.2) : ℂ) *
            outer p.1 (trace.stopProjection p.2))
        (ν.prod
          (Measure.pi fun _ :
            res.SurvivingCoordinate => paperMeasure))) :
    Integrable
      (fun p :
          Y ×
            (trace.stopPrefix.SurvivingCoordinate → T4) =>
        (trace.stopPrefix.residualIntegrand
            ρ ε (x p.1) (y p.1)
            (trace.stopPrefix.reconstruct p.2) : ℂ) *
          outer p.1 p.2)
      (ν.prod
        (Measure.pi fun _ :
          trace.stopPrefix.SurvivingCoordinate =>
            paperMeasure)) := by
  induction trace with
  | stop stop scale hremaining certificate =>
      exact hcurrent
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      have hhead :
          Integrable
            (fun p :
                Y ×
                  ((current.afterHead
                    head tail hremaining).SurvivingCoordinate → T4) =>
              ((current.afterHead
                head tail hremaining).residualIntegrand
                  ρ ε (x p.1) (y p.1)
                  ((current.afterHead
                    head tail hremaining).reconstruct p.2) : ℂ) *
                outer p.1 (next.stopProjection p.2))
            (ν.prod
              (Measure.pi fun _ :
                (current.afterHead
                  head tail hremaining).SurvivingCoordinate =>
                    paperMeasure)) := by
        apply
          current.integrable_joint_residualIntegrand_mul_postOuter_afterHead
            ν head tail hremaining x y
            (fun a v => outer a (next.stopProjection v))
            _ internal
        exact hcurrent
      exact ih outer hhead

/-- Scalar specialization of the joint theorem.

This is the exact premise needed to conclude ordinary integrability of the
stopped residual density with a fixed pair of displayed endpoints. -/
theorem integrable_residualIntegrand_mul_stopOuter_stopPrefix
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res scale)
    (x y : T4)
    (outer :
      (trace.stopPrefix.SurvivingCoordinate → T4) → ℂ)
    (hcurrent :
      Integrable
        (fun v : res.SurvivingCoordinate → T4 =>
          (res.residualIntegrand ρ ε x y
              (res.reconstruct v) : ℂ) *
            outer (trace.stopProjection v))
        (Measure.pi fun _ :
          res.SurvivingCoordinate => paperMeasure)) :
    Integrable
      (fun v :
          trace.stopPrefix.SurvivingCoordinate → T4 =>
        (trace.stopPrefix.residualIntegrand
            ρ ε x y
            (trace.stopPrefix.reconstruct v) : ℂ) *
          outer v)
      (Measure.pi fun _ :
        trace.stopPrefix.SurvivingCoordinate =>
          paperMeasure) := by
  let μCurrent :
      Measure (res.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μStop :
      Measure (trace.stopPrefix.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let ν : Measure Unit := Measure.dirac ()
  have hcurrentJoint :
      Integrable
        (fun p :
            Unit × (res.SurvivingCoordinate → T4) =>
          (res.residualIntegrand ρ ε x y
              (res.reconstruct p.2) : ℂ) *
            outer (trace.stopProjection p.2))
        (ν.prod μCurrent) := by
    change
      Integrable
        (fun p :
            Unit × (res.SurvivingCoordinate → T4) =>
          (res.residualIntegrand ρ ε x y
              (res.reconstruct p.2) : ℂ) *
            outer (trace.stopProjection p.2))
        ((Measure.dirac ()).prod μCurrent)
    rw [Measure.dirac_prod]
    rw [
      (measurableEmbedding_prodMk_left ())
        |>.integrable_map_iff]
    change
      Integrable
        (fun v : res.SurvivingCoordinate → T4 =>
          (res.residualIntegrand ρ ε x y
              (res.reconstruct v) : ℂ) *
            outer (trace.stopProjection v))
        μCurrent
    exact hcurrent
  have hstopJoint :=
    trace.integrable_joint_residualIntegrand_mul_stopOuter_stopPrefix
      ν (fun _ : Unit => x) (fun _ : Unit => y)
      (fun _ : Unit => outer) hcurrentJoint
  change
    Integrable
      (fun p :
          Unit ×
            (trace.stopPrefix.SurvivingCoordinate → T4) =>
        (trace.stopPrefix.residualIntegrand
            ρ ε x y
            (trace.stopPrefix.reconstruct p.2) : ℂ) *
          outer p.2)
      ((Measure.dirac ()).prod μStop) at hstopJoint
  rw [Measure.dirac_prod] at hstopJoint
  rw [
    (measurableEmbedding_prodMk_left ())
      |>.integrable_map_iff] at hstopJoint
  change
    Integrable
      (fun v :
          trace.stopPrefix.SurvivingCoordinate → T4 =>
        (trace.stopPrefix.residualIntegrand
            ρ ε x y
            (trace.stopPrefix.reconstruct v) : ℂ) *
          outer v)
      μStop at hstopJoint
  exact hstopJoint

/-- Joint integrability at the current prefix supplies, for almost every
parameter, all scalar weighted-integrability hypotheses traversed by the
stopped trace.

The proof is itself a trace induction.  At each step, product integrability
gives the current scalar section almost everywhere, while the concrete
one-head joint theorem propagates the joint premise to the induction
hypothesis. -/
theorem eventually_weightedIntegrableAlong_of_integrable_joint
    {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [SFinite ν]
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res scale)
    (x y : Y → T4)
    (outer :
      Y →
        (trace.stopPrefix.SurvivingCoordinate → T4) → ℂ)
    (hcurrent :
      Integrable
        (fun p :
            Y × (res.SurvivingCoordinate → T4) =>
          (res.residualIntegrand ρ ε
              (x p.1) (y p.1)
              (res.reconstruct p.2) : ℂ) *
            outer p.1 (trace.stopProjection p.2))
        (ν.prod
          (Measure.pi fun _ :
            res.SurvivingCoordinate => paperMeasure))) :
    ∀ᵐ a ∂ν,
      trace.WeightedIntegrableAlong
        (x a) (y a) (outer a) := by
  induction trace with
  | stop stop scale hremaining certificate =>
      filter_upwards with a
      trivial
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      have hnext :
          Integrable
            (fun p :
                Y ×
                  ((current.afterHead
                    head tail hremaining).SurvivingCoordinate → T4) =>
              ((current.afterHead
                head tail hremaining).residualIntegrand
                  ρ ε (x p.1) (y p.1)
                  ((current.afterHead
                    head tail hremaining).reconstruct p.2) : ℂ) *
                outer p.1 (next.stopProjection p.2))
            (ν.prod
              (Measure.pi fun _ :
                (current.afterHead
                  head tail hremaining).SurvivingCoordinate =>
                    paperMeasure)) := by
        apply
          current.integrable_joint_residualIntegrand_mul_postOuter_afterHead
            ν head tail hremaining x y
            (fun a v => outer a (next.stopProjection v))
            _ internal
        exact hcurrent
      have hnextWeighted :
          ∀ᵐ a ∂ν,
            next.WeightedIntegrableAlong
              (x a) (y a) (outer a) :=
        ih outer hnext
      filter_upwards [hcurrent.prod_right_ae, hnextWeighted]
        with a ha hwa
      exact ⟨ha, hwa⟩

/-- Exact joint integral transport through every block consumed by the
stopped trace.

Both sides are genuine product-space integrals.  The named stop step and
its suffix remain unintegrated, so the right-hand side retains the exact
power `2 * trace.stopPrefix.remainingOrder`. -/
theorem lamEps_pow_integral_joint_mul_stopOuter_eq_stop
    {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [SFinite ν]
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res scale)
    (x y : Y → T4)
    (outer :
      Y →
        (trace.stopPrefix.SurvivingCoordinate → T4) → ℂ)
    (hcurrent :
      Integrable
        (fun p :
            Y × (res.SurvivingCoordinate → T4) =>
          (res.residualIntegrand ρ ε
              (x p.1) (y p.1)
              (res.reconstruct p.2) : ℂ) *
            outer p.1 (trace.stopProjection p.2))
        (ν.prod
          (Measure.pi fun _ :
            res.SurvivingCoordinate => paperMeasure))) :
    (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
        (∫ p :
            Y × (res.SurvivingCoordinate → T4),
          (res.residualIntegrand ρ ε
              (x p.1) (y p.1)
              (res.reconstruct p.2) : ℂ) *
            outer p.1 (trace.stopProjection p.2)
          ∂(ν.prod
            (Measure.pi fun _ :
              res.SurvivingCoordinate => paperMeasure))) =
      (lamEps lam ε : ℂ) ^
          (2 * trace.stopPrefix.remainingOrder) *
        (∫ p :
            Y ×
              (trace.stopPrefix.SurvivingCoordinate → T4),
          (trace.stopPrefix.residualIntegrand
              ρ ε (x p.1) (y p.1)
              (trace.stopPrefix.reconstruct p.2) : ℂ) *
            outer p.1 p.2
          ∂(ν.prod
            (Measure.pi fun _ :
              trace.stopPrefix.SurvivingCoordinate =>
                paperMeasure))) := by
  have hstop :=
    trace.integrable_joint_residualIntegrand_mul_stopOuter_stopPrefix
      ν x y outer hcurrent
  have hweighted :=
    trace.eventually_weightedIntegrableAlong_of_integrable_joint
      ν x y outer hcurrent
  rw [integral_prod _ hcurrent, integral_prod _ hstop]
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hweighted] with a ha
  exact
    trace.lamEps_pow_integral_mul_stopOuter_eq_stop
      (x a) (y a) (outer a) ha

end R324WithinHalfStopBeforeStepTrace
end R324WithinHalfResidualPrefix

end

end Anderson4D
