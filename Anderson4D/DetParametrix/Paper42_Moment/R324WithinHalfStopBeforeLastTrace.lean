import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfResidualIntegrability

/-!
# Certified within-half traces stopping before the last block

This module gives a generic analytic trace which consumes a prescribed
prefix of a within-half residual schedule and stops with one specified block
still present.  It is deliberately independent of any theorem identifying
which block is last in a concrete schedule.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

/-- A certified analytic trace which stops immediately before a specified
last block.

The step constructor stores the same analytic data as
`R324WithinHalfCertifiedAnalyticTrace.step`: internal Fubini evidence, the
updated scale, and a certificate for the updated edge state. -/
inductive R324WithinHalfStopBeforeLastTrace
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (terminal : R322ExtractionStep m) :
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing) →
    (Fin (m + 1) → ℝ) → Type
  | stop
      (res :
        R324WithinHalfResidualPrefix ρ lam ε pairing)
      (scale : Fin (m + 1) → ℝ)
      (hremaining : res.remaining = [terminal])
      (certificate :
        R324WithinHalfEdgeCertificate res.state scale) :
      R324WithinHalfStopBeforeLastTrace terminal res scale
  | step
      (res :
        R324WithinHalfResidualPrefix ρ lam ε pairing)
      (head : R322ExtractionStep m)
      (tail : List (R322ExtractionStep m))
      (hremaining : res.remaining = head :: tail)
      (scale : Fin (m + 1) → ℝ)
      (internal :
        R324WithinHalfResidualInternalReady
          res head tail hremaining)
      (nextScale : Fin (m + 1) → ℝ)
      (nextCertificate :
        R324WithinHalfEdgeCertificate
          (res.afterHead head tail hremaining).state
          nextScale)
      (next :
        R324WithinHalfStopBeforeLastTrace terminal
          (res.afterHead head tail hremaining) nextScale) :
      R324WithinHalfStopBeforeLastTrace terminal res scale

namespace R324WithinHalfStopBeforeLastTrace

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {terminal : R322ExtractionStep m}

/-- Consume exactly the supplied prefix and leave the specified final block
untouched.  In particular, the local provider is never called on
`terminal`. -/
def of_localBlockProvider
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K pairing)
    (terminal : R322ExtractionStep m)
    (pre : List (R322ExtractionStep m))
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing)
    (scale : Fin (m + 1) → ℝ)
    (certificate :
      R324WithinHalfEdgeCertificate res.state scale)
    (hremaining :
      res.remaining = pre ++ [terminal]) :
    R324WithinHalfStopBeforeLastTrace terminal res scale := by
  cases pre with
  | nil =>
      exact
        R324WithinHalfStopBeforeLastTrace.stop
          res scale (by simpa using hremaining) certificate
  | cons head rest =>
      let tail : List (R322ExtractionStep m) :=
        rest ++ [terminal]
      have hhead :
          res.remaining = head :: tail := by
        simpa only [tail, List.cons_append] using hremaining
      obtain ⟨_localBound, nextCertificate⟩ :=
        provider res head tail hhead scale certificate
      let nextScale :=
        r324WithinHalfUpdatedEdgeScale
          (res.headContext head tail hhead)
          scale C lam K
      let internal :
          R324WithinHalfResidualInternalReady
            res head tail hhead :=
        ⟨R324WithinHalfEdgeCertificate.eventually_integrable_stepClosedIntegrand_section
          (ctx := res.headContext head tail hhead)
          certificate hε hε1⟩
      exact
        R324WithinHalfStopBeforeLastTrace.step
          res head tail hhead scale internal
          nextScale nextCertificate
          (of_localBlockProvider hε hε1 provider
            terminal rest
            (res.afterHead head tail hhead)
            nextScale nextCertificate rfl)

/-- The residual prefix at which the trace stops. -/
def stopPrefix
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeLastTrace
        terminal res scale) :
    R324WithinHalfResidualPrefix ρ lam ε pairing :=
  match trace with
  | .stop .. => res
  | @R324WithinHalfStopBeforeLastTrace.step
      _ _ _ _ _ _
      _ _ _ _ _ _ _ _ next => next.stopPrefix

/-- The scale certified at the stopping prefix. -/
def stopScale
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeLastTrace
        terminal res scale) :
    Fin (m + 1) → ℝ :=
  match trace with
  | .stop _ stopScale _ _ => stopScale
  | @R324WithinHalfStopBeforeLastTrace.step
      _ _ _ _ _ _
      _ _ _ _ _ _ _ _ next => next.stopScale

/-- Restrict a surviving tuple through all consumed prefix blocks. -/
def stopProjection
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeLastTrace
        terminal res scale) :
    (res.SurvivingCoordinate → T4) →
      (trace.stopPrefix.SurvivingCoordinate → T4) :=
  match trace with
  | .stop .. => fun v => v
  | @R324WithinHalfStopBeforeLastTrace.step
      _ _ _ _ _ _
      current head tail hremaining _ _ _ _ next =>
      fun v =>
        next.stopProjection
          (current.splitSurvivingPiMeasurableEquiv
            head tail hremaining v).2

/-- Full weighted integrability at exactly the scalar integrals consumed
before the last block. -/
def WeightedIntegrableAlong
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (x y : T4)
    (trace :
      R324WithinHalfStopBeforeLastTrace
        terminal res scale)
    (outer :
      (trace.stopPrefix.SurvivingCoordinate → T4) → ℂ) :
    Prop :=
  match trace with
  | .stop .. => True
  | @R324WithinHalfStopBeforeLastTrace.step
      _ _ _ _ _ _
      current head tail hremaining _ _ _ _ next =>
      Integrable
          (fun v : current.SurvivingCoordinate → T4 =>
            (current.residualIntegrand ρ ε x y
                (current.reconstruct v) : ℂ) *
              outer
                (next.stopProjection
                  (current.splitSurvivingPiMeasurableEquiv
                    head tail hremaining v).2))
          (Measure.pi fun _ => paperMeasure) ∧
        next.WeightedIntegrableAlong x y outer

/-- The stopping prefix has the requested singleton suffix. -/
theorem stopPrefix_remaining_eq_singleton
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeLastTrace
        terminal res scale) :
    trace.stopPrefix.remaining = [terminal] := by
  induction trace with
  | stop stop scale hremaining certificate =>
      change stop.remaining = [terminal]
      exact hremaining
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      exact ih

/-- At the stop, the processed prefix followed by the retained block is the
full analytic schedule. -/
theorem stopPrefix_processed_append_terminal_eq_schedule
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeLastTrace
        terminal res scale) :
    trace.stopPrefix.state.processed ++ [terminal] =
      r322AnalyticSchedule pairing := by
  have hschedule := trace.stopPrefix.schedule_eq
  rw [trace.stopPrefix_remaining_eq_singleton] at hschedule
  exact hschedule.symm

/-- The exact perturbative order retained at the stop is the order of the
single untouched block. -/
theorem stopPrefix_remainingOrder_eq
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeLastTrace
        terminal res scale) :
    trace.stopPrefix.remainingOrder =
      residualBlockOrder terminal.2 := by
  unfold R324WithinHalfResidualPrefix.remainingOrder
  rw [trace.stopPrefix_remaining_eq_singleton]
  rfl

/-- The final edge certificate carried by the trace. -/
theorem stopCertificate
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeLastTrace
        terminal res scale) :
    R324WithinHalfEdgeCertificate
      trace.stopPrefix.state trace.stopScale := by
  induction trace with
  | stop stop scale hremaining certificate =>
      exact certificate
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      exact ih

/-- Exact weighted iteration through the prescribed prefix.

Unlike the full trace theorem, the right-hand side retains the exact
`lamEps` power belonging to the untouched singleton block. -/
theorem lamEps_pow_integral_mul_stopOuter_eq_stop
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (x y : T4)
    (trace :
      R324WithinHalfStopBeforeLastTrace
        terminal res scale)
    (outer :
      (trace.stopPrefix.SurvivingCoordinate → T4) → ℂ)
    (hweighted :
      trace.WeightedIntegrableAlong x y outer) :
    (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
        (∫ v : res.SurvivingCoordinate → T4,
          (res.residualIntegrand ρ ε x y
              (res.reconstruct v) : ℂ) *
            outer (trace.stopProjection v)
          ∂Measure.pi fun _ => paperMeasure) =
      (lamEps lam ε : ℂ) ^
          (2 * trace.stopPrefix.remainingOrder) *
        (∫ v :
            trace.stopPrefix.SurvivingCoordinate → T4,
          ((trace.stopPrefix.residualIntegrand
              ρ ε x y
              (trace.stopPrefix.reconstruct v) : ℂ) *
            outer v)
          ∂Measure.pi fun _ => paperMeasure) := by
  induction trace with
  | stop stop scale hremaining certificate =>
      rfl
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      have hcurrent :
          Integrable
            (fun v : current.SurvivingCoordinate → T4 =>
              (current.residualIntegrand ρ ε x y
                  (current.reconstruct v) : ℂ) *
                outer
                  (next.stopProjection
                    (current.splitSurvivingPiMeasurableEquiv
                      head tail hremaining v).2))
            (Measure.pi fun _ => paperMeasure) :=
        hweighted.1
      have hnext :
          next.WeightedIntegrableAlong x y outer :=
        hweighted.2
      change
        (lamEps lam ε : ℂ) ^
              (2 * current.remainingOrder) *
            (∫ v : current.SurvivingCoordinate → T4,
              (current.residualIntegrand ρ ε x y
                  (current.reconstruct v) : ℂ) *
                outer
                  (next.stopProjection
                    (current.splitSurvivingPiMeasurableEquiv
                      head tail hremaining v).2)
              ∂Measure.pi fun _ => paperMeasure) =
          (lamEps lam ε : ℂ) ^
              (2 * next.stopPrefix.remainingOrder) *
            (∫ v :
                next.stopPrefix.SurvivingCoordinate → T4,
              ((next.stopPrefix.residualIntegrand
                  ρ ε x y
                  (next.stopPrefix.reconstruct v) : ℂ) *
                outer v)
              ∂Measure.pi fun _ => paperMeasure)
      rw [
        current.lamEps_pow_integral_residual_mul_postOuter_eq_afterHead_of_weighted
          head tail hremaining x y
          (fun v => outer (next.stopProjection v))
          hcurrent internal.internal]
      exact ih outer hnext

end R324WithinHalfStopBeforeLastTrace

end R324WithinHalfResidualPrefix

end

end Anderson4D
