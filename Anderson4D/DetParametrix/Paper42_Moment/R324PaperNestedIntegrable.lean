import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTraceIntegrable
import Anderson4D.DetParametrix.Paper42_Moment.R324TwoHalfToNestedCrossBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324InitialTwoHalfRootIntegrability

/-!
# Joint integrability of the nested physical core

Paper: R-324 — §4.2 Step 3, the last integrability premise

The two-half physical core on the terminal carriers is
`(left residual)·(right residual)·(marked covariance)`.  The two residual
factors depend on disjoint coordinate groups, and the covariance factor is
bounded at a fixed scale — so the fixed-scale integrability recipe in
`docs/R324_PAPER_PROOF.md` applies verbatim: an integrable product across
the two factors, times a bounded measurable weight.

Transporting along the measure-preserving terminal-to-nested equivalence
then gives the premise `exists_terminalPayload_physicalIntegral_le` takes.
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
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)

/-- **The two-half terminal physical core is jointly integrable.**

The two half residual integrands live on disjoint coordinate groups, so
their product is integrable on the product measure; the marked covariance
is a bounded measurable weight. -/
theorem integrable_terminalMarkedPhysicalCore
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4)
    (hleft :
      Integrable
        (fun v : terminal.left.SurvivingCoordinate → T4 =>
          (terminal.left.residualIntegrand ρ ε x y
            (terminal.left.reconstruct v) : ℂ))
        (Measure.pi fun _ => paperMeasure))
    (hright :
      Integrable
        (fun v : terminal.right.SurvivingCoordinate → T4 =>
          (terminal.right.residualIntegrand ρ ε z w
            (terminal.right.reconstruct v) : ℂ))
        (Measure.pi fun _ => paperMeasure)) :
    Integrable
      (terminal.terminalMarkedPhysicalCore π selected L x y z w)
      ((Measure.pi fun _ :
          terminal.left.SurvivingCoordinate => paperMeasure).prod
        (Measure.pi fun _ :
          terminal.right.SurvivingCoordinate => paperMeasure)) := by
  obtain ⟨B, _hB0, hbound⟩ :=
    ρ.exists_norm_r324MarkedPairingCovarianceProductOn_le hε hε1 L
      (momentCombinedPairing κp κm π)
      (r324ResidualMarkedLowerEndpoint selected)
      (momentResidualActive κp κm)
  have hprod := hleft.mul_prod hright
  have hmeas :
      Measurable
        (fun p :
            (terminal.left.SurvivingCoordinate → T4) ×
              (terminal.right.SurvivingCoordinate → T4) =>
          ρ.r324MarkedPairingCovarianceProductOn ε L
            (momentCombinedPairing κp κm π)
            (r324ResidualMarkedLowerEndpoint selected)
            (momentResidualActive κp κm)
            (terminal.terminalDoubledReconstruct p)) :=
    (ρ.measurable_r324MarkedPairingCovarianceProductOn ε L
      (momentCombinedPairing κp κm π)
      (r324ResidualMarkedLowerEndpoint selected)
      (momentResidualActive κp κm)).comp
      (terminal.measurable_terminalDoubledReconstruct)
  exact hprod.mul_bdd (c := B) hmeas.aestronglyMeasurable
    (.of_forall fun p => hbound _)

/-- **The nested physical core is jointly integrable.**

Transport of the previous statement along the measure-preserving
terminal-to-nested equivalence, using the pointwise losslessness
`initialNestedMarkedPhysicalCore_reindex`.  This is exactly the premise
`exists_terminalPayload_physicalIntegral_le` and
`exists_r324InitialNestedContextFactorization_of_head` take. -/
theorem integrable_initialNestedMarkedPhysicalCore
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4)
    (hleft :
      Integrable
        (fun v : terminal.left.SurvivingCoordinate → T4 =>
          (terminal.left.residualIntegrand ρ ε x y
            (terminal.left.reconstruct v) : ℂ))
        (Measure.pi fun _ => paperMeasure))
    (hright :
      Integrable
        (fun v : terminal.right.SurvivingCoordinate → T4 =>
          (terminal.right.residualIntegrand ρ ε z w
            (terminal.right.reconstruct v) : ℂ))
        (Measure.pi fun _ => paperMeasure)) :
    Integrable
      (terminal.initialNestedMarkedPhysicalCore π selected L x y z w)
      (Measure.pi fun _ :
        terminal.NestedCoordinate π => paperMeasure) := by
  have hp := terminal.measurePreserving_terminalProductPiMeasurableEquivNested π
  have hcore :=
    terminal.integrable_terminalMarkedPhysicalCore hε hε1 π selected L
      x y z w hleft hright
  refine (hp.integrable_comp_emb
    (terminal.terminalProductPiMeasurableEquivNested π).measurableEmbedding
    (g := terminal.initialNestedMarkedPhysicalCore π selected L x y z w)).mp ?_
  refine hcore.congr (.of_forall fun p => ?_)
  exact
    (terminal.initialNestedMarkedPhysicalCore_reindex π selected L
      x y z w p).symm

end R324TwoHalfTerminalData

end

end Anderson4D
