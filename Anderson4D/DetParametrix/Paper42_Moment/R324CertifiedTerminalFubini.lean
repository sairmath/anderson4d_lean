import Anderson4D.DetParametrix.Paper42_Moment.R324TerminalResidualSumJointIntegrability
import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointErasedPhaseABoundary

/-!
# Certified terminal endpoint Fubini for R-324

This module composes the genuine terminal joint-integrability producer with
the endpoint Fubini adapter.  Thus two certified within-half traces and
their terminal edge certificates suffice for both exact endpoint-integration
identities; no separate joint-integrability hypothesis remains.

The complete residual primitive sum stays grouped throughout, and no norm
or estimate is introduced.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}

/-- Certified within-half traces and their terminal edge certificates
discharge the analytic premise of the exact four-endpoint Fubini identity. -/
theorem
    integral_externalModeResidualSumIntegrand_fubini_ofCertifiedTraces
    {leftRes :
      R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes :
      R324WithinHalfResidualPrefix ρ lam ε κm}
    {leftInitialScale rightInitialScale :
      Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        leftRes leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        rightRes rightInitialScale)
    (π : κp.singles ≃ κm.singles)
    (hleft : leftTrace.terminalPrefix.state.active.Nonempty)
    (hright : rightTrace.terminalPrefix.state.active.Nonempty)
    (α β : Z4)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (leftTerminalScale rightTerminalScale :
      Fin (m + 1) → ℝ)
    (hleftCertificate :
      R324WithinHalfEdgeCertificate
        leftTrace.terminalPrefix.state leftTerminalScale)
    (hrightCertificate :
      R324WithinHalfEdgeCertificate
        rightTrace.terminalPrefix.state rightTerminalScale) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces
        leftTrace rightTrace
    (∫ x, ∫ y, ∫ z, ∫ w,
        ∫ p,
          terminal.externalModeResidualSumIntegrand
            π α β p x y z w
          ∂((Measure.pi fun _ :
              terminal.left.SurvivingCoordinate => paperMeasure).prod
            (Measure.pi fun _ :
              terminal.right.SurvivingCoordinate => paperMeasure))
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure) =
      ∫ p,
        terminal.endpointIntegratedResidualDensity
          π hleft hright α β p
        ∂((Measure.pi fun _ :
            terminal.left.SurvivingCoordinate => paperMeasure).prod
          (Measure.pi fun _ :
            terminal.right.SurvivingCoordinate => paperMeasure)) := by
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces
      leftTrace rightTrace
  have hterminal :
      terminal.TerminalResidualSumJointIntegrable π := by
    simpa only [terminal] using
      terminalResidualSumJointIntegrable_ofCertifiedTraces
        leftTrace rightTrace π hε hε1
        leftTerminalScale rightTerminalScale
        hleftCertificate hrightCertificate
  exact
    terminal.integral_externalModeResidualSumIntegrand_fubini_of_terminal
      π hleft hright α β hterminal

/-- The certified endpoint Fubini identity followed by exact
measure-preserving transport to the initial nested-cross carrier. -/
theorem
    integral_externalModeResidualSumIntegrand_fubini_eq_initialNested_ofCertifiedTraces
    {leftRes :
      R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes :
      R324WithinHalfResidualPrefix ρ lam ε κm}
    {leftInitialScale rightInitialScale :
      Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        leftRes leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        rightRes rightInitialScale)
    (π : κp.singles ≃ κm.singles)
    (hleft : leftTrace.terminalPrefix.state.active.Nonempty)
    (hright : rightTrace.terminalPrefix.state.active.Nonempty)
    (α β : Z4)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (leftTerminalScale rightTerminalScale :
      Fin (m + 1) → ℝ)
    (hleftCertificate :
      R324WithinHalfEdgeCertificate
        leftTrace.terminalPrefix.state leftTerminalScale)
    (hrightCertificate :
      R324WithinHalfEdgeCertificate
        rightTrace.terminalPrefix.state rightTerminalScale) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces
        leftTrace rightTrace
    (∫ x, ∫ y, ∫ z, ∫ w,
        ∫ p,
          terminal.externalModeResidualSumIntegrand
            π α β p x y z w
          ∂((Measure.pi fun _ :
              terminal.left.SurvivingCoordinate => paperMeasure).prod
            (Measure.pi fun _ :
              terminal.right.SurvivingCoordinate => paperMeasure))
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure) =
      ∫ v,
        terminal.initialNestedEndpointIntegratedResidualDensity
          π hleft hright α β v
        ∂(Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure) := by
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces
      leftTrace rightTrace
  have hterminal :
      terminal.TerminalResidualSumJointIntegrable π := by
    simpa only [terminal] using
      terminalResidualSumJointIntegrable_ofCertifiedTraces
        leftTrace rightTrace π hε hε1
        leftTerminalScale rightTerminalScale
        hleftCertificate hrightCertificate
  exact
    terminal.integral_externalModeResidualSumIntegrand_fubini_eq_initialNested_of_terminal
      π hleft hright α β hterminal

/-- Tighter certified-trace API for the four-endpoint Fubini identity.
The terminal scales and certificates are the ones genuinely stored by the
two trace constructors. -/
theorem
    integral_externalModeResidualSumIntegrand_fubini_usingStoredCertificates
    {leftRes :
      R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes :
      R324WithinHalfResidualPrefix ρ lam ε κm}
    {leftInitialScale rightInitialScale :
      Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        leftRes leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        rightRes rightInitialScale)
    (π : κp.singles ≃ κm.singles)
    (hleft : leftTrace.terminalPrefix.state.active.Nonempty)
    (hright : rightTrace.terminalPrefix.state.active.Nonempty)
    (α β : Z4)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces
        leftTrace rightTrace
    (∫ x, ∫ y, ∫ z, ∫ w,
        ∫ p,
          terminal.externalModeResidualSumIntegrand
            π α β p x y z w
          ∂((Measure.pi fun _ :
              terminal.left.SurvivingCoordinate => paperMeasure).prod
            (Measure.pi fun _ :
              terminal.right.SurvivingCoordinate => paperMeasure))
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure) =
      ∫ p,
        terminal.endpointIntegratedResidualDensity
          π hleft hright α β p
        ∂((Measure.pi fun _ :
            terminal.left.SurvivingCoordinate => paperMeasure).prod
          (Measure.pi fun _ :
            terminal.right.SurvivingCoordinate => paperMeasure)) :=
  integral_externalModeResidualSumIntegrand_fubini_ofCertifiedTraces
    leftTrace rightTrace π hleft hright α β hε hε1
    leftTrace.terminalScale rightTrace.terminalScale
    leftTrace.terminalCertificate rightTrace.terminalCertificate

/-- Tighter certified-trace API for the exact initial nested-cross
transport, using the terminal certificates stored by the traces. -/
theorem
    integral_externalModeResidualSumIntegrand_fubini_eq_initialNested_usingStoredCertificates
    {leftRes :
      R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes :
      R324WithinHalfResidualPrefix ρ lam ε κm}
    {leftInitialScale rightInitialScale :
      Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        leftRes leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        rightRes rightInitialScale)
    (π : κp.singles ≃ κm.singles)
    (hleft : leftTrace.terminalPrefix.state.active.Nonempty)
    (hright : rightTrace.terminalPrefix.state.active.Nonempty)
    (α β : Z4)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces
        leftTrace rightTrace
    (∫ x, ∫ y, ∫ z, ∫ w,
        ∫ p,
          terminal.externalModeResidualSumIntegrand
            π α β p x y z w
          ∂((Measure.pi fun _ :
              terminal.left.SurvivingCoordinate => paperMeasure).prod
            (Measure.pi fun _ :
              terminal.right.SurvivingCoordinate => paperMeasure))
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure) =
      ∫ v,
        terminal.initialNestedEndpointIntegratedResidualDensity
          π hleft hright α β v
        ∂(Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure) :=
  integral_externalModeResidualSumIntegrand_fubini_eq_initialNested_ofCertifiedTraces
    leftTrace rightTrace π hleft hright α β hε hε1
    leftTrace.terminalScale rightTrace.terminalScale
    leftTrace.terminalCertificate rightTrace.terminalCertificate

end R324TwoHalfTerminalData

end

end Anderson4D
