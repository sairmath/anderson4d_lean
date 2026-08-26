import Anderson4D.DetParametrix.Paper42_Moment.R324InitialEndpointGroupedToCompleteRun
import Anderson4D.DetParametrix.Paper42_Moment.R324TwoHalfTraceScaleLedger

/-!
# The initial residual endpoint integral after the complete nested run

The first theorem integrates the a.e. endpoint-to-run seam without changing
the order in which norms are taken.  The second theorem chooses every
cutoff-dependent constant before the coupling, scale, pairings and traces,
then combines the two within-half scale ledgers with the exact initial
nested-cross order ledger.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- Pure algebraic/Fubini bridge from a signed two-half collapse equality to
the endpoint-norm form consumed below.  The exact order identity is the only
bookkeeping input; no pointwise estimate is used here. -/
theorem weighted_norm_le_of_collapsed_endpointIntegral
    {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {lam ε : ℝ}
    {m leftOrder rightOrder crossOrder : ℕ}
    (horder : leftOrder + rightOrder + crossOrder = m)
    (term : ℂ) (f : X → ℂ)
    (hcollapse :
      (lamEps lam ε : ℂ) ^ (2 * (leftOrder + rightOrder)) * term =
        ∫ x, f x ∂μ)
    {majorant : ℝ}
    (hendpoint :
      (∫ x, lamEps lam ε ^ (2 * crossOrder) * ‖f x‖ ∂μ) ≤
        majorant) :
    |lamEps lam ε| ^ (2 * m) * ‖term‖ ≤ majorant := by
  let a : ℝ := lamEps lam ε
  have hpow :
      |a| ^ (2 * m) =
        |a| ^ (2 * crossOrder) *
          |a| ^ (2 * (leftOrder + rightOrder)) := by
    rw [← pow_add]
    congr 1
    omega
  have hscaledNorm :
      ‖(a : ℂ) ^ (2 * (leftOrder + rightOrder)) * term‖ =
        |a| ^ (2 * (leftOrder + rightOrder)) * ‖term‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have heven :
      |a| ^ (2 * crossOrder) = a ^ (2 * crossOrder) := by
    rw [← abs_pow, abs_of_nonneg
      ((even_two_mul crossOrder).pow_nonneg a)]
  calc
    |lamEps lam ε| ^ (2 * m) * ‖term‖ =
        |a| ^ (2 * crossOrder) *
          ‖(a : ℂ) ^ (2 * (leftOrder + rightOrder)) * term‖ := by
      dsimp only [a]
      rw [hpow, hscaledNorm]
      ring
    _ = |a| ^ (2 * crossOrder) * ‖∫ x, f x ∂μ‖ := by
      rw [hcollapse]
    _ ≤ |a| ^ (2 * crossOrder) * ∫ x, ‖f x‖ ∂μ :=
      mul_le_mul_of_nonneg_left
        (norm_integral_le_integral_norm f) (pow_nonneg (abs_nonneg a) _)
    _ = ∫ x, |a| ^ (2 * crossOrder) * ‖f x‖ ∂μ := by
      rw [integral_const_mul]
    _ = ∫ x, lamEps lam ε ^ (2 * crossOrder) * ‖f x‖ ∂μ := by
      dsimp only [a] at heven ⊢
      rw [heven]
    _ ≤ majorant := hendpoint

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}

/-- Integrate the pointwise endpoint seam against any supplied complete-run
integral estimate.  This fixed-data lemma keeps the two literal terminal
scale products visible for the subsequent exact order ledger. -/
theorem integral_coupling_mul_norm_initialNestedEndpointIntegratedResidualDensity_le
    {leftRes : R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes : R324WithinHalfResidualPrefix ρ lam ε κm}
    {leftInitialScale rightInitialScale : Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        leftRes leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        rightRes rightInitialScale)
    (π : κp.singles ≃ κm.singles)
    (hleft : leftTrace.terminalPrefix.state.active.Nonempty)
    (hright : rightTrace.terminalPrefix.state.active.Nonempty)
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial κp κm π).remaining =
        head :: tail)
    (α β : Z4)
    (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|)
    (hmtrunc : m ≤ truncOrder ε)
    {B supportConstant : ℝ} :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
    let step :=
      r324InitialNestedCrossStepContext κp κm π head tail hremaining
    ∀ (hleftInitial :
        (r324LeftHalfPullback step.residual.activeCarrier).Nonempty)
      (hrightInitial :
        (r324RightHalfPullback step.residual.activeCarrier).Nonempty),
      (∫ v, terminal.completeNestedRunDensity
          step hleftInitial hrightInitial v
          ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) ≤
        ∫ z, primitiveInsertedMajorant
          B lam ε supportConstant step.residual.remainingOrder z
          ∂paperMeasure →
      (∫ v,
          lamEps lam ε ^ (2 * step.residual.remainingOrder) *
            ‖terminal.initialNestedEndpointIntegratedResidualDensity
              π hleft hright α β v‖
          ∂Measure.pi fun _ : terminal.NestedCoordinate π => paperMeasure) ≤
        (((∏ edge ∈ terminal.left.activeEdgeSlots,
              leftTrace.terminalScale edge) *
            (∏ edge ∈ terminal.right.activeEdgeSlots,
              rightTrace.terminalScale edge)) *
          invSqKerMass ^ 4) *
          ∫ z, primitiveInsertedMajorant
            B lam ε supportConstant step.residual.remainingOrder z
            ∂paperMeasure := by
  dsimp only
  intro hleftInitial hrightInitial hrun
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
  let step :=
    r324InitialNestedCrossStepContext κp κm π head tail hremaining
  let scaleProduct : ℝ :=
    (((∏ edge ∈ terminal.left.activeEdgeSlots,
          leftTrace.terminalScale edge) *
        (∏ edge ∈ terminal.right.activeEdgeSlots,
          rightTrace.terminalScale edge)) *
      invSqKerMass ^ 4)
  have hscaleProduct : 0 ≤ scaleProduct := by
    dsimp only [scaleProduct, terminal]
    exact mul_nonneg
      (mul_nonneg
        (Finset.prod_nonneg fun edge hedge =>
          (leftTrace.terminalCertificate.scale_pos edge).le)
        (Finset.prod_nonneg fun edge hedge =>
          (rightTrace.terminalCertificate.scale_pos edge).le))
      (pow_nonneg invSqKerMass_nonneg _)
  have hrunIntegrable :
      Integrable
        (terminal.completeNestedRunDensity
          step hleftInitial hrightInitial)
        (Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) :=
    terminal.integrable_completeNestedRunDensity_at_truncation
      hlam hε hε1 hlog hmtrunc step hleftInitial hrightInitial
  have hscaledRunIntegrable :
      Integrable
        (fun v => scaleProduct *
          terminal.completeNestedRunDensity
            step hleftInitial hrightInitial v)
        (Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) :=
    hrunIntegrable.const_mul scaleProduct
  have hpointwise :=
    ae_coupling_mul_norm_initialNestedEndpointIntegratedResidualDensity_le_completeNestedRun
      leftTrace rightTrace π hleft hright head tail hremaining α β
  have hpointwise' :
      (fun v : terminal.NestedCoordinate π → T4 =>
        lamEps lam ε ^ (2 * step.residual.remainingOrder) *
          ‖terminal.initialNestedEndpointIntegratedResidualDensity
            π hleft hright α β v‖) ≤ᵐ[
        Measure.pi fun _ : terminal.NestedCoordinate π => paperMeasure]
      (fun v => scaleProduct *
        terminal.completeNestedRunDensity
          step hleftInitial hrightInitial v) := by
    simpa only [terminal, step, scaleProduct] using hpointwise
  have hleftNonneg :
      ∀ᵐ v ∂Measure.pi fun _ : terminal.NestedCoordinate π => paperMeasure,
        0 ≤ lamEps lam ε ^ (2 * step.residual.remainingOrder) *
          ‖terminal.initialNestedEndpointIntegratedResidualDensity
            π hleft hright α β v‖ :=
    Filter.Eventually.of_forall fun v =>
      mul_nonneg ((even_two_mul step.residual.remainingOrder).pow_nonneg _)
        (norm_nonneg _)
  have hintegral :
      (∫ v,
          lamEps lam ε ^ (2 * step.residual.remainingOrder) *
            ‖terminal.initialNestedEndpointIntegratedResidualDensity
              π hleft hright α β v‖
          ∂Measure.pi fun _ : terminal.NestedCoordinate π => paperMeasure) ≤
        ∫ v, scaleProduct *
          terminal.completeNestedRunDensity
            step hleftInitial hrightInitial v
          ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure := by
    exact integral_mono_of_nonneg hleftNonneg hscaledRunIntegrable hpointwise'
  calc
    _ ≤ ∫ v, scaleProduct *
          terminal.completeNestedRunDensity
            step hleftInitial hrightInitial v
          ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure :=
      hintegral
    _ = scaleProduct *
          ∫ v, terminal.completeNestedRunDensity
            step hleftInitial hrightInitial v
            ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure := by
      rw [integral_const_mul]
    _ ≤ scaleProduct *
          ∫ z, primitiveInsertedMajorant
            B lam ε supportConstant step.residual.remainingOrder z
            ∂paperMeasure :=
      mul_le_mul_of_nonneg_left hrun hscaleProduct

end R324TwoHalfTerminalData

/-- Cutoff-uniform residual endpoint closure.  The Phase-A provider and the
complete-run provider are both chosen before all scale and combinatorial
data.  For any two compatible traces, the endpoint integral is controlled
by one inserted majorant at the ambient order. -/
theorem exists_r324InitialResidualEndpointIntegral_le_ambientMajorant
    (ρ : SmoothCutoff) :
    ∃ phaseSupport runSupport C K A B : ℝ,
      0 < phaseSupport ∧ 0 < runSupport ∧
      0 < C ∧ 0 < K ∧ 1 ≤ A ∧ 0 < B ∧
      (∀ (lam ε : ℝ) (m : ℕ)
        (pairing : PartialPairing (Fin m)),
          0 < lam → 0 < ε → ε ≤ 1 →
          1 ≤ |Real.log ε| → m ≤ truncOrder ε →
          Nonempty
            (R324WithinHalfResidualPrefix.R324CompatibleAnalyticBudgetTrace
              (C := C) (K := K) (A := A)
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε pairing) (fun _ => A))) ∧
      ∀ {lam ε : ℝ} {m : ℕ}
        {κp κm : PartialPairing (Fin m)}
        {π : κp.singles ≃ κm.singles}
        (leftData :
          R324WithinHalfResidualPrefix.R324CompatibleAnalyticBudgetTrace
            (C := C) (K := K) (A := A)
            (R324WithinHalfResidualPrefix.initial ρ lam ε κp)
            (fun _ => A))
        (rightData :
          R324WithinHalfResidualPrefix.R324CompatibleAnalyticBudgetTrace
            (C := C) (K := K) (A := A)
            (R324WithinHalfResidualPrefix.initial ρ lam ε κm)
            (fun _ => A)),
        0 < lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| → 1 ≤ m → m ≤ truncOrder ε →
        ∀ (hleft :
            leftData.analytic.terminalPrefix.state.active.Nonempty)
          (hright :
            rightData.analytic.terminalPrefix.state.active.Nonempty)
          (head : R324NestedCrossBlock κp κm π)
          (tail : List (R324NestedCrossBlock κp κm π))
          (hremaining :
            (R324NestedCrossResidualPrefix.initial κp κm π).remaining =
              head :: tail)
          (α β : Z4),
          let terminal :=
            R324TwoHalfTerminalData.ofCertifiedTraces
              leftData.analytic rightData.analytic
          let step :=
            r324InitialNestedCrossStepContext
              κp κm π head tail hremaining
          (∫ v,
              lamEps lam ε ^ (2 * step.residual.remainingOrder) *
                ‖terminal.initialNestedEndpointIntegratedResidualDensity
                  π hleft hright α β v‖
              ∂Measure.pi fun _ : terminal.NestedCoordinate π =>
                paperMeasure) ≤
            ∫ z, primitiveInsertedMajorant
              (r324TwoHalfCompleteAbsorbedBase A C K B)
              lam ε runSupport m z ∂paperMeasure := by
  obtain ⟨phaseSupport, C, K, A,
      hphaseSupport, hC, hK, hA, htraces⟩ :=
    exists_r324InitialCompatibleAnalyticBudgetTrace_at_truncation ρ
  obtain ⟨runSupport, B, hrunSupport, hB, hrun⟩ :=
    R324TwoHalfTerminalData.exists_integral_completeNestedRunDensity_le_primitiveInsertedMajorant
      ρ
  refine ⟨phaseSupport, runSupport, C, K, A, B,
    hphaseSupport, hrunSupport, hC, hK, hA, hB,
    htraces, ?_⟩
  intro lam ε m κp κm π leftData rightData
    hlam hε hε1 hlog hm hmtrunc hleft hright
    head tail hremaining α β
  dsimp only
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces
      leftData.analytic rightData.analytic
  let step :=
    r324InitialNestedCrossStepContext κp κm π head tail hremaining
  have hleftInitial :
      (r324LeftHalfPullback step.residual.activeCarrier).Nonempty :=
    step.finalLeftHeadNonempty.mono fun i hi => by
      apply mem_r324LeftHalfPullback.mpr
      exact step.head_subset_activeCarrier
        (mem_r324LeftHalfPullback.mp hi)
  have hrightInitial :
      (r324RightHalfPullback step.residual.activeCarrier).Nonempty :=
    step.finalRightHeadNonempty.mono fun i hi => by
      apply mem_r324RightHalfPullback.mpr
      exact step.head_subset_activeCarrier
        (mem_r324RightHalfPullback.mp hi)
  have hrunBound :
      (∫ v, terminal.completeNestedRunDensity
          step hleftInitial hrightInitial v
          ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) ≤
        ∫ z, primitiveInsertedMajorant
          B lam ε runSupport step.residual.remainingOrder z
          ∂paperMeasure :=
    hrun terminal hlam hε hε1 hlog hmtrunc
      step hleftInitial hrightInitial
  have hendpoint :=
    R324TwoHalfTerminalData.integral_coupling_mul_norm_initialNestedEndpointIntegratedResidualDensity_le
      leftData.analytic rightData.analytic π hleft hright
      head tail hremaining α β hlam hε hε1 hlog hmtrunc
      hleftInitial hrightInitial hrunBound
  let scaleProduct : ℝ :=
    (((∏ edge ∈ leftData.analytic.terminalPrefix.activeEdgeSlots,
          leftData.analytic.terminalScale edge) *
        (∏ edge ∈ rightData.analytic.terminalPrefix.activeEdgeSlots,
          rightData.analytic.terminalScale edge)) *
      invSqKerMass ^ 4)
  have hpointwise :
      ∀ z,
        scaleProduct *
            primitiveInsertedMajorant B lam ε runSupport
              (R324NestedCrossResidualPrefix.initial
                κp κm π).remainingOrder z ≤
          primitiveInsertedMajorant
            (r324TwoHalfCompleteAbsorbedBase A C K B)
            lam ε runSupport m z := by
    intro z
    exact r324_twoHalf_initial_terminalScale_mul_majorant_le
      (zero_le_one.trans hA) hC.le hK.le hB.le hlam.le
      leftData rightData π hm z
  have htargetIntegrable :
      Integrable
        (primitiveInsertedMajorant
          (r324TwoHalfCompleteAbsorbedBase A C K B)
          lam ε runSupport m) paperMeasure :=
    integrable_primitiveInsertedMajorant
      (r324TwoHalfCompleteAbsorbedBase A C K B)
      lam ε runSupport m hε
  have hsourceNonneg :
      ∀ᵐ z ∂paperMeasure,
        0 ≤ scaleProduct *
          primitiveInsertedMajorant B lam ε runSupport
            (R324NestedCrossResidualPrefix.initial
              κp κm π).remainingOrder z := by
    have hscale : 0 ≤ scaleProduct := by
      dsimp only [scaleProduct]
      exact mul_nonneg
        (mul_nonneg
          (Finset.prod_nonneg fun edge hedge =>
            (leftData.analytic.terminalCertificate.scale_pos edge).le)
          (Finset.prod_nonneg fun edge hedge =>
            (rightData.analytic.terminalCertificate.scale_pos edge).le))
        (pow_nonneg invSqKerMass_nonneg _)
    exact Filter.Eventually.of_forall fun z =>
      mul_nonneg hscale
        (primitiveInsertedMajorant_nonneg'
          B lam ε runSupport
          (R324NestedCrossResidualPrefix.initial
            κp κm π).remainingOrder z)
  have hintegralMajorant :
      (∫ z, scaleProduct *
          primitiveInsertedMajorant B lam ε runSupport
            (R324NestedCrossResidualPrefix.initial
              κp κm π).remainingOrder z ∂paperMeasure) ≤
        ∫ z, primitiveInsertedMajorant
          (r324TwoHalfCompleteAbsorbedBase A C K B)
          lam ε runSupport m z ∂paperMeasure :=
    integral_mono_of_nonneg hsourceNonneg htargetIntegrable
      (Filter.Eventually.of_forall hpointwise)
  calc
    _ ≤ scaleProduct *
          ∫ z, primitiveInsertedMajorant B lam ε runSupport
            (R324NestedCrossResidualPrefix.initial
              κp κm π).remainingOrder z ∂paperMeasure := by
      simpa only [terminal, step, scaleProduct,
        R324TwoHalfTerminalData.ofCertifiedTraces,
        r324InitialNestedCrossStepContext] using hendpoint
    _ = ∫ z, scaleProduct *
          primitiveInsertedMajorant B lam ε runSupport
            (R324NestedCrossResidualPrefix.initial
              κp κm π).remainingOrder z ∂paperMeasure := by
      rw [integral_const_mul]
    _ ≤ _ := hintegralMajorant

end

end Anderson4D
