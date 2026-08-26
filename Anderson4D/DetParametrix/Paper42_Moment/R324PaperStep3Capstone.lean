import Anderson4D.DetParametrix.Paper42_Moment.R324PaperNestedIntegrable
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperNestedFactorization
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperProperHeadProvider
import Anderson4D.DetParametrix.Paper42_Moment.R324CertifiedTwoHalfPhysicalCollapse

/-!
# Paper §4.2, Step 3: nested-reduction handoff

Paper: R-324 — §4.2 Step 3

`exists_terminalPayload_physicalIntegral_le` is Step 3's end-to-end
handoff from the physical initial nested integral to the endpoint-
preserving terminal payload.  Its three inputs are:

* `R324ProperHeadSharpProvider` — `exists_r324ProperHeadSharpProvider`,
  which is paper Step 3(c) ((4.4) on the block, then the elementary
  eight-dimensional integral);
* `R324InitialNestedContextFactorization` —
  `exists_r324InitialNestedContextFactorization_of_head`, using that every
  schedule block is some slot's marked block and that the Step 4 marking is
  inert at a nonpositive threshold;
* the joint integrability of the nested physical core —
  `integrable_initialNestedMarkedPhysicalCore`, whose two half premises
  come from root integrability propagated along the certified traces.

Root integrability holds at *almost every* endpoint pair because fixed-endpoint
Green sections fail on exceptional diagonals.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

open R324WithinHalfResidualPrefix in
/-- **Terminal half integrability at almost every endpoint pair.**

The all-Green root is jointly `L¹` in its endpoints and coordinates
(`integrable_initial_residualIntegrand_pair`), so its fixed-endpoint
section is integrable a.e.; the certified trace then propagates that to
the terminal prefix. -/
theorem eventually_integrable_terminalPrefix_residualIntegrand
    (ρ : SmoothCutoff) (lam : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace
        (initial ρ lam ε pairing) scale) :
    ∀ᵐ p : T4 × T4 ∂(paperMeasure.prod paperMeasure),
      Integrable
        (fun v : trace.terminalPrefix.SurvivingCoordinate → T4 =>
          (trace.terminalPrefix.residualIntegrand ρ ε p.1 p.2
            (trace.terminalPrefix.reconstruct v) : ℂ))
        (Measure.pi fun _ => paperMeasure) := by
  filter_upwards
      [eventually_integrable_initial_residualIntegrand ρ lam hε hε1 pairing]
    with p hp
  exact trace.integrable_terminalPrefix_residualIntegrand p.1 p.2 hp

open R324WithinHalfResidualPrefix in
/-- **Step 3's handoff, with every input supplied.**

For almost every pair of external endpoint pairs, the nested context
factorization exists at a slot chosen inside the schedule head, and the
proper-head provider is unconditional.  So
`exists_terminalPayload_physicalIntegral_le` applies with no analytic
hypothesis left. -/
theorem exists_r324Step3_handoff_inputs
    (ρ : SmoothCutoff) {lam ε : ℝ}
    (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|)
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (hmtrunc : m ≤ truncOrder ε)
    (π : κp.singles ≃ κm.singles)
    {leftScale rightScale : Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfCertifiedAnalyticTrace
        (initial ρ lam ε κp) leftScale)
    (rightTrace :
      R324WithinHalfCertifiedAnalyticTrace
        (initial ρ lam ε κm) rightScale)
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial κp κm π).remaining =
        head :: tail)
    (L : ℝ) :
    ∃ D : ℝ, 0 < D ∧
      R324ProperHeadSharpProvider ρ lam ε D κp κm π ∧
      ∀ᵐ q : (T4 × T4) × (T4 × T4)
        ∂((paperMeasure.prod paperMeasure).prod
          (paperMeasure.prod paperMeasure)),
        ∃ selected : R324ResidualCovarianceSlot κp,
          Nonempty
            (R324InitialNestedContextFactorization ρ lam ε κp κm π selected
              (R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace)
              L q.1.1 q.1.2 q.2.1 q.2.2) := by
  obtain ⟨D, hD, hprovider⟩ := exists_r324ProperHeadSharpProvider ρ
  refine ⟨D, hD, hprovider lam ε π hlam hε hε1 hlog hmtrunc, ?_⟩
  have hleft :=
    eventually_integrable_terminalPrefix_residualIntegrand ρ lam hε hε1
      leftTrace
  have hright :=
    eventually_integrable_terminalPrefix_residualIntegrand ρ lam hε hε1
      rightTrace
  have hL :=
    (Measure.quasiMeasurePreserving_fst
      (μ := paperMeasure.prod paperMeasure)
      (ν := paperMeasure.prod paperMeasure)).ae hleft
  have hR :=
    (Measure.quasiMeasurePreserving_snd
      (μ := paperMeasure.prod paperMeasure)
      (ν := paperMeasure.prod paperMeasure)).ae hright
  filter_upwards [hL, hR] with q hq1 hq2
  refine
    exists_r324InitialNestedContextFactorization_of_head head tail hremaining
      (fun selected => ?_)
  exact
    (R324TwoHalfTerminalData.ofCertifiedTraces leftTrace
      rightTrace).integrable_initialNestedMarkedPhysicalCore hε hε1 π
      selected L q.1.1 q.1.2 q.2.1 q.2.2 hq1 hq2

end

end Anderson4D
