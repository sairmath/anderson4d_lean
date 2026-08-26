import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfResidualIntegrability
import Anderson4D.DetParametrix.Paper42_Moment.R324TwoHalfToNestedCrossBridge

/-!
# Certified two-half physical collapse for R-324

This module joins the endpoint-independent certified within-half traces to
the genuine two-half-to-nested physical bridge.  Full integrability remains
attached to the actual weighted scalar integrals traversed by a trace; no
pointwise unweighted local-section premise is introduced.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324TwoHalfTerminalData

/-- Package the actual terminal prefixes of two endpoint-independent
certified traces. -/
def ofCertifiedTraces
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {leftRes :
      R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes :
      R324WithinHalfResidualPrefix ρ lam ε κm}
    {leftScale rightScale : Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        leftRes leftScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        rightRes rightScale) :
    R324TwoHalfTerminalData ρ lam ε κp κm where
  left := leftTrace.terminalPrefix
  right := rightTrace.terminalPrefix
  left_remaining :=
    leftTrace.terminalPrefix_remaining_eq_nil
  right_remaining :=
    rightTrace.terminalPrefix_remaining_eq_nil
  left_processed :=
    leftTrace.terminalPrefix_processed_eq_schedule
  right_processed :=
    rightTrace.terminalPrefix_processed_eq_schedule

/-- The genuine marked cross covariance on an arbitrary completed
two-half terminal datum. -/
def markedCrossFactor
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal :
      R324TwoHalfTerminalData ρ lam ε κp κm)
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ)
    (vl : terminal.left.SurvivingCoordinate → T4)
    (vr : terminal.right.SurvivingCoordinate → T4) : ℂ :=
  ρ.r324MarkedPairingCovarianceProductOn ε L
    (momentCombinedPairing κp κm π)
    (r324ResidualMarkedLowerEndpoint selected)
    (momentResidualActive κp κm)
    (terminal.terminalDoubledReconstruct (vl, vr))

/-- Fubini identifies the terminal product-space physical core with its
right-then-left iterated integral. -/
theorem integral_terminalMarkedPhysicalCore_eq_iterated
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal :
      R324TwoHalfTerminalData ρ lam ε κp κm)
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4)
    (hintegrable :
      Integrable
        (terminal.terminalMarkedPhysicalCore
          π selected L x y z w)
        ((Measure.pi fun _ :
            terminal.left.SurvivingCoordinate =>
              paperMeasure).prod
          (Measure.pi fun _ :
            terminal.right.SurvivingCoordinate =>
              paperMeasure))) :
    (∫ p,
        terminal.terminalMarkedPhysicalCore
          π selected L x y z w p
        ∂((Measure.pi fun _ :
            terminal.left.SurvivingCoordinate =>
              paperMeasure).prod
          (Measure.pi fun _ :
            terminal.right.SurvivingCoordinate =>
              paperMeasure))) =
      ∫ vr :
          terminal.right.SurvivingCoordinate → T4,
        ((terminal.right.residualIntegrand
            ρ ε z w
            (terminal.right.reconstruct vr) : ℂ) *
          (∫ vl :
              terminal.left.SurvivingCoordinate → T4,
            ((terminal.left.residualIntegrand
                ρ ε x y
                (terminal.left.reconstruct vl) : ℂ) *
              terminal.markedCrossFactor
                π selected L vl vr)
            ∂Measure.pi fun _ => paperMeasure))
        ∂Measure.pi fun _ => paperMeasure := by
  letI :
      IsFiniteMeasure
        (Measure.pi fun _ :
          terminal.left.SurvivingCoordinate =>
            paperMeasure) :=
    Measure.pi.instIsFiniteMeasure _
  letI :
      IsFiniteMeasure
        (Measure.pi fun _ :
          terminal.right.SurvivingCoordinate =>
            paperMeasure) :=
    Measure.pi.instIsFiniteMeasure _
  letI :
      SigmaFinite
        (Measure.pi fun _ :
          terminal.left.SurvivingCoordinate =>
            paperMeasure) :=
    IsFiniteMeasure.toSigmaFinite _
  letI :
      SigmaFinite
        (Measure.pi fun _ :
          terminal.right.SurvivingCoordinate =>
            paperMeasure) :=
    IsFiniteMeasure.toSigmaFinite _
  letI :
      SFinite
        (Measure.pi fun _ :
          terminal.left.SurvivingCoordinate =>
            paperMeasure) :=
    inferInstance
  letI :
      SFinite
        (Measure.pi fun _ :
          terminal.right.SurvivingCoordinate =>
            paperMeasure) :=
    inferInstance
  rw [integral_prod_symm
    (μ := Measure.pi fun _ :
      terminal.left.SurvivingCoordinate =>
        paperMeasure)
    (ν := Measure.pi fun _ :
      terminal.right.SurvivingCoordinate =>
        paperMeasure)
    _ hintegrable]
  apply integral_congr_ae
  filter_upwards with vr
  calc
    (∫ vl,
        terminal.terminalMarkedPhysicalCore
          π selected L x y z w (vl, vr)
        ∂Measure.pi fun _ => paperMeasure) =
        ∫ vl,
          (terminal.right.residualIntegrand
              ρ ε z w
              (terminal.right.reconstruct vr) : ℂ) *
            ((terminal.left.residualIntegrand
                ρ ε x y
                (terminal.left.reconstruct vl) : ℂ) *
              terminal.markedCrossFactor
                π selected L vl vr)
          ∂Measure.pi fun _ => paperMeasure := by
      apply integral_congr_ae
      filter_upwards with vl
      unfold terminalMarkedPhysicalCore markedCrossFactor
      ring
    _ =
        (terminal.right.residualIntegrand
            ρ ε z w
            (terminal.right.reconstruct vr) : ℂ) *
          (∫ vl,
            (terminal.left.residualIntegrand
                ρ ε x y
                (terminal.left.reconstruct vl) : ℂ) *
              terminal.markedCrossFactor
                π selected L vl vr
            ∂Measure.pi fun _ => paperMeasure) := by
      simpa only using
        (integral_const_mul
          (μ := Measure.pi fun _ :
            terminal.left.SurvivingCoordinate =>
              paperMeasure)
          (terminal.right.residualIntegrand
              ρ ε z w
              (terminal.right.reconstruct vr) : ℂ)
          (fun vl :
              terminal.left.SurvivingCoordinate → T4 =>
            (terminal.left.residualIntegrand
                ρ ε x y
                (terminal.left.reconstruct vl) : ℂ) *
              terminal.markedCrossFactor
                π selected L vl vr))

end R324TwoHalfTerminalData

namespace R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {x y z w : T4}
    {leftRes :
      R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes :
      R324WithinHalfResidualPrefix ρ lam ε κm}
    {leftScale rightScale : Fin (m + 1) → ℝ}

/-- Exact two-sided weighted iteration through endpoint-independent
certified traces, for an arbitrary terminal cross factor. -/
theorem twoHalf_lamEps_pow_integral_eq_terminal
    (leftTrace :
      R324WithinHalfCertifiedAnalyticTrace
        leftRes leftScale)
    (rightTrace :
      R324WithinHalfCertifiedAnalyticTrace
        rightRes rightScale)
    (cross :
      (leftTrace.terminalPrefix.SurvivingCoordinate → T4) →
        (rightTrace.terminalPrefix.SurvivingCoordinate → T4) → ℂ)
    (hleft :
      ∀ᵐ vr ∂(Measure.pi fun _ :
          rightRes.SurvivingCoordinate => paperMeasure),
        leftTrace.WeightedIntegrableAlong x y
          (fun vl =>
            cross vl (rightTrace.terminalProjection vr)))
    (hright :
      rightTrace.WeightedIntegrableAlong z w
        (fun vr =>
          ∫ vl :
              leftTrace.terminalPrefix.SurvivingCoordinate → T4,
            ((leftTrace.terminalPrefix.residualIntegrand
                ρ ε x y
                (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
              cross vl vr)
            ∂Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^ (2 * rightRes.remainingOrder) *
        (∫ vr : rightRes.SurvivingCoordinate → T4,
          (rightRes.residualIntegrand ρ ε z w
              (rightRes.reconstruct vr) : ℂ) *
            ((lamEps lam ε : ℂ) ^
                (2 * leftRes.remainingOrder) *
              (∫ vl : leftRes.SurvivingCoordinate → T4,
                (leftRes.residualIntegrand ρ ε x y
                    (leftRes.reconstruct vl) : ℂ) *
                  cross
                    (leftTrace.terminalProjection vl)
                    (rightTrace.terminalProjection vr)
                ∂Measure.pi fun _ => paperMeasure))
          ∂Measure.pi fun _ => paperMeasure) =
      ∫ vr :
          rightTrace.terminalPrefix.SurvivingCoordinate → T4,
        ((rightTrace.terminalPrefix.residualIntegrand
            ρ ε z w
            (rightTrace.terminalPrefix.reconstruct vr) : ℂ) *
          (∫ vl :
              leftTrace.terminalPrefix.SurvivingCoordinate → T4,
            ((leftTrace.terminalPrefix.residualIntegrand
                ρ ε x y
                (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
              cross vl vr)
            ∂Measure.pi fun _ => paperMeasure))
          ∂Measure.pi fun _ => paperMeasure := by
  have hleftEq :
      ∀ᵐ vr ∂(Measure.pi fun _ :
          rightRes.SurvivingCoordinate => paperMeasure),
        (lamEps lam ε : ℂ) ^ (2 * leftRes.remainingOrder) *
            (∫ vl : leftRes.SurvivingCoordinate → T4,
              (leftRes.residualIntegrand ρ ε x y
                  (leftRes.reconstruct vl) : ℂ) *
                cross
                  (leftTrace.terminalProjection vl)
                  (rightTrace.terminalProjection vr)
              ∂Measure.pi fun _ => paperMeasure) =
          ∫ vl :
              leftTrace.terminalPrefix.SurvivingCoordinate → T4,
            ((leftTrace.terminalPrefix.residualIntegrand
                ρ ε x y
                (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
              cross vl (rightTrace.terminalProjection vr))
            ∂Measure.pi fun _ => paperMeasure := by
    filter_upwards [hleft] with vr hvr
    exact
      lamEps_pow_integral_mul_terminalOuter_eq_terminal
        x y leftTrace
        (fun vl =>
          cross vl (rightTrace.terminalProjection vr))
        hvr
  have hrightIntegral :
      (∫ vr : rightRes.SurvivingCoordinate → T4,
        (rightRes.residualIntegrand ρ ε z w
            (rightRes.reconstruct vr) : ℂ) *
          ((lamEps lam ε : ℂ) ^
              (2 * leftRes.remainingOrder) *
            (∫ vl : leftRes.SurvivingCoordinate → T4,
              (leftRes.residualIntegrand ρ ε x y
                  (leftRes.reconstruct vl) : ℂ) *
                cross
                  (leftTrace.terminalProjection vl)
                  (rightTrace.terminalProjection vr)
              ∂Measure.pi fun _ => paperMeasure))
        ∂Measure.pi fun _ => paperMeasure) =
        ∫ vr :
            rightRes.SurvivingCoordinate → T4,
          (rightRes.residualIntegrand ρ ε z w
              (rightRes.reconstruct vr) : ℂ) *
            (∫ vl :
                leftTrace.terminalPrefix.SurvivingCoordinate → T4,
              ((leftTrace.terminalPrefix.residualIntegrand
                  ρ ε x y
                  (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
                cross vl (rightTrace.terminalProjection vr))
              ∂Measure.pi fun _ => paperMeasure)
          ∂Measure.pi fun _ => paperMeasure := by
    apply integral_congr_ae
    filter_upwards [hleftEq] with vr hvr
    rw [hvr]
  rw [hrightIntegral]
  exact
    lamEps_pow_integral_mul_terminalOuter_eq_terminal
      z w rightTrace
      (fun vr =>
        ∫ vl :
            leftTrace.terminalPrefix.SurvivingCoordinate → T4,
          ((leftTrace.terminalPrefix.residualIntegrand
              ρ ε x y
              (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
            cross vl vr)
          ∂Measure.pi fun _ => paperMeasure)
      hright

/-- **Exact certified two-half physical collapse.**

The genuine within-half physical residuals are collapsed on both sides,
then Fubini and the proved terminal-to-nested carrier equivalence transport
the same physical integrand to the literal initial nested cross prefix. -/
theorem twoHalf_lamEps_pow_integral_eq_initialNested
    (leftTrace :
      R324WithinHalfCertifiedAnalyticTrace
        leftRes leftScale)
    (rightTrace :
      R324WithinHalfCertifiedAnalyticTrace
        rightRes rightScale)
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ)
    (hleft :
      ∀ᵐ vr ∂(Measure.pi fun _ :
          rightRes.SurvivingCoordinate => paperMeasure),
        leftTrace.WeightedIntegrableAlong x y
          (fun vl =>
            (R324TwoHalfTerminalData.ofCertifiedTraces
              leftTrace rightTrace).markedCrossFactor
                π selected L vl
                (rightTrace.terminalProjection vr)))
    (hright :
      rightTrace.WeightedIntegrableAlong z w
        (fun vr =>
          ∫ vl :
              leftTrace.terminalPrefix.SurvivingCoordinate → T4,
            ((leftTrace.terminalPrefix.residualIntegrand
                ρ ε x y
                (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
              (R324TwoHalfTerminalData.ofCertifiedTraces
                leftTrace rightTrace).markedCrossFactor
                  π selected L vl vr)
            ∂Measure.pi fun _ => paperMeasure))
    (hterminal :
      Integrable
        ((R324TwoHalfTerminalData.ofCertifiedTraces
          leftTrace rightTrace).terminalMarkedPhysicalCore
            π selected L x y z w)
        ((Measure.pi fun _ :
            leftTrace.terminalPrefix.SurvivingCoordinate =>
              paperMeasure).prod
          (Measure.pi fun _ :
            rightTrace.terminalPrefix.SurvivingCoordinate =>
              paperMeasure))) :
    (lamEps lam ε : ℂ) ^ (2 * rightRes.remainingOrder) *
        (∫ vr : rightRes.SurvivingCoordinate → T4,
          (rightRes.residualIntegrand ρ ε z w
              (rightRes.reconstruct vr) : ℂ) *
            ((lamEps lam ε : ℂ) ^
                (2 * leftRes.remainingOrder) *
              (∫ vl : leftRes.SurvivingCoordinate → T4,
                (leftRes.residualIntegrand ρ ε x y
                    (leftRes.reconstruct vl) : ℂ) *
                  (R324TwoHalfTerminalData.ofCertifiedTraces
                    leftTrace rightTrace).markedCrossFactor
                      π selected L
                      (leftTrace.terminalProjection vl)
                      (rightTrace.terminalProjection vr)
                ∂Measure.pi fun _ => paperMeasure))
          ∂Measure.pi fun _ => paperMeasure) =
      ∫ v :
          (R324TwoHalfTerminalData.ofCertifiedTraces
            leftTrace rightTrace).NestedCoordinate π → T4,
        (R324TwoHalfTerminalData.ofCertifiedTraces
          leftTrace rightTrace).initialNestedMarkedPhysicalCore
            π selected L x y z w v
        ∂Measure.pi fun _ => paperMeasure := by
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces
      leftTrace rightTrace
  calc
    _ =
        ∫ vr :
            rightTrace.terminalPrefix.SurvivingCoordinate → T4,
          ((rightTrace.terminalPrefix.residualIntegrand
              ρ ε z w
              (rightTrace.terminalPrefix.reconstruct vr) : ℂ) *
            (∫ vl :
                leftTrace.terminalPrefix.SurvivingCoordinate → T4,
              ((leftTrace.terminalPrefix.residualIntegrand
                  ρ ε x y
                  (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
                terminal.markedCrossFactor
                  π selected L vl vr)
              ∂Measure.pi fun _ => paperMeasure))
          ∂Measure.pi fun _ => paperMeasure :=
      twoHalf_lamEps_pow_integral_eq_terminal
        leftTrace rightTrace
        (terminal.markedCrossFactor π selected L)
        hleft hright
    _ =
        ∫ p,
          terminal.terminalMarkedPhysicalCore
            π selected L x y z w p
          ∂((Measure.pi fun _ :
              leftTrace.terminalPrefix.SurvivingCoordinate =>
                paperMeasure).prod
            (Measure.pi fun _ :
              rightTrace.terminalPrefix.SurvivingCoordinate =>
                paperMeasure)) :=
      (terminal.integral_terminalMarkedPhysicalCore_eq_iterated
        π selected L x y z w hterminal).symm
    _ = _ :=
      terminal.integral_terminalMarkedPhysicalCore_eq_initialNested
        π selected L x y z w

end R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

end

end Anderson4D
