import Anderson4D.DetParametrix.Paper42_Moment.R324InitialResidualEndpointIntegral
import Anderson4D.DetParametrix.Paper42_Moment.R324CertifiedNonemptyRootEndpointBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTraceIntegrable

/-!
# Exact signed collapse of the grouped initial residual fibre

This file discharges the section-integrability premises of the existing
certified two-half collapse.  It uses only the already proved initial
residual integrability, terminal trace propagation, and the bounded grouped
residual covariance factor.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

/-- The literal head/post restrictions traversed by a certified trace give
a measurable projection onto its terminal sparse carrier. -/
theorem measurable_terminalProjection
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace : R324WithinHalfCertifiedAnalyticTrace res scale) :
    Measurable trace.terminalProjection := by
  induction trace with
  | terminal terminal scale hremaining certificate =>
      exact measurable_id
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      exact ih.comp
        (measurable_snd.comp
          (current.splitSurvivingPiMeasurableEquiv
            head tail hremaining).measurable)

/-- Existing root and terminal integrability closes every analytic premise
of the grouped certified two-half collapse at fixed good endpoint pairs. -/
theorem twoHalf_lamEps_pow_integral_initialRootResidualSum_eq_initialNested_of_sections
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {leftScale rightScale : Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κp) leftScale)
    (rightTrace :
      R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κm) rightScale)
    (π : κp.singles ≃ κm.singles)
    (x y z w : T4)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hleftSection :
      Integrable
        (fun vl :
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κp).SurvivingCoordinate → T4 =>
          ((R324WithinHalfResidualPrefix.initial
            ρ lam ε κp).residualIntegrand
              ρ ε x y
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κp).reconstruct vl) : ℂ))
        (Measure.pi fun _ => paperMeasure))
    (hrightSection :
      Integrable
        (fun vr :
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).SurvivingCoordinate → T4 =>
          ((R324WithinHalfResidualPrefix.initial
            ρ lam ε κm).residualIntegrand
              ρ ε z w
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).reconstruct vr) : ℂ))
        (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^ (2 *
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κm).remainingOrder) *
        (∫ vr :
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).SurvivingCoordinate → T4,
          ((R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).residualIntegrand
            ρ ε z w
            ((R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).reconstruct vr) : ℂ) *
            ((lamEps lam ε : ℂ) ^ (2 *
                (R324WithinHalfResidualPrefix.initial
                  ρ lam ε κp).remainingOrder) *
              (∫ vl :
                  (R324WithinHalfResidualPrefix.initial
                    ρ lam ε κp).SurvivingCoordinate → T4,
                ((R324WithinHalfResidualPrefix.initial
                    ρ lam ε κp).residualIntegrand
                  ρ ε x y
                  ((R324WithinHalfResidualPrefix.initial
                    ρ lam ε κp).reconstruct vl) : ℂ) *
                  (r324ResidualPrimitiveSumProduct
                    ρ ε κp κm π
                    (r324TwoHalfRootDoubledReconstruct
                      (R324WithinHalfResidualPrefix.initial
                        ρ lam ε κp)
                      (R324WithinHalfResidualPrefix.initial
                        ρ lam ε κm) (vl, vr)) : ℂ)
                ∂Measure.pi fun _ => paperMeasure))
          ∂Measure.pi fun _ => paperMeasure) =
      ∫ v :
          (R324TwoHalfTerminalData.ofCertifiedTraces
            leftTrace rightTrace).NestedCoordinate π → T4,
        (R324TwoHalfTerminalData.ofCertifiedTraces
          leftTrace rightTrace).initialNestedResidualSumPhysicalCore
            π x y z w v
        ∂Measure.pi fun _ => paperMeasure := by
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces
      leftTrace rightTrace
  obtain ⟨crossBound, hcrossBound0, hcrossBound⟩ :=
    terminal.exists_norm_residualSumCrossFactor_le hε hε1 π
  have hrootMap :
      Measurable
        (r324TwoHalfRootDoubledReconstruct
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κp)
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κm)) := by
    convert
      (r324InitialTwoHalfProductPiMeasurableEquiv
        ρ lam ε κp κm).measurable using 1
    funext p
    exact
      (r324InitialTwoHalfProductPiMeasurableEquiv_apply
        ρ lam ε κp κm p).symm
  have hrawCrossMeas :
      Measurable fun p :
          ((R324WithinHalfResidualPrefix.initial
              ρ lam ε κp).SurvivingCoordinate → T4) ×
            ((R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).SurvivingCoordinate → T4) =>
        (r324ResidualPrimitiveSumProduct
          ρ ε κp κm π
          (r324TwoHalfRootDoubledReconstruct
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κp)
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm) p) : ℂ) :=
    Complex.measurable_ofReal.comp
      ((ρ.measurable_r324ResidualPrimitiveSumProduct
        ε κp κm π).comp hrootMap)
  obtain ⟨rawBound, _hrawBound0, hrawBound⟩ :=
    ρ.exists_norm_r324ResidualPrimitiveSumProduct_le
      hε hε1 κp κm π
  have hrootProduct :
      Integrable
        (fun p :
            ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κp).SurvivingCoordinate → T4) ×
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).SurvivingCoordinate → T4) =>
          ((R324WithinHalfResidualPrefix.initial
              ρ lam ε κp).residualIntegrand
            ρ ε x y
            ((R324WithinHalfResidualPrefix.initial
              ρ lam ε κp).reconstruct p.1) : ℂ) *
            (((R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).residualIntegrand
              ρ ε z w
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).reconstruct p.2) : ℂ) *
              terminal.residualSumCrossFactor
                π (leftTrace.terminalProjection p.1)
                  (rightTrace.terminalProjection p.2)))
        ((Measure.pi fun _ => paperMeasure).prod
          (Measure.pi fun _ => paperMeasure)) := by
    have hbare := hleftSection.mul_prod hrightSection
    have hraw := hbare.mul_bdd hrawCrossMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p =>
        by
          simpa only [Complex.norm_real] using
            hrawBound
              (r324TwoHalfRootDoubledReconstruct
                (R324WithinHalfResidualPrefix.initial
                  ρ lam ε κp)
                (R324WithinHalfResidualPrefix.initial
                  ρ lam ε κm) p))
    apply hraw.congr
    filter_upwards with p
    unfold terminal R324TwoHalfTerminalData.residualSumCrossFactor
    rw [
      leftTrace.r324ResidualPrimitiveSumProduct_complex_eq_terminalProjection
        rightTrace π p]
    ring
  have hleftRoot :
      ∀ᵐ vr ∂(Measure.pi fun _ :
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κm).SurvivingCoordinate => paperMeasure),
        Integrable
          (fun vl :
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε κp).SurvivingCoordinate → T4 =>
            ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κp).residualIntegrand
              ρ ε x y
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κp).reconstruct vl) : ℂ) *
              terminal.residualSumCrossFactor
                π (leftTrace.terminalProjection vl)
                  (rightTrace.terminalProjection vr))
          (Measure.pi fun _ => paperMeasure) := by
    have hbare := hleftSection.mul_prod
      (integrable_const (1 : ℂ)
        (μ := Measure.pi fun _ :
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κm).SurvivingCoordinate => paperMeasure))
    have hraw := hbare.mul_bdd hrawCrossMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        simpa only [Complex.norm_real] using
          hrawBound
            (r324TwoHalfRootDoubledReconstruct
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε κp)
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε κm) p))
    have hprojected :
        Integrable
          (fun p :
              ((R324WithinHalfResidualPrefix.initial
                  ρ lam ε κp).SurvivingCoordinate → T4) ×
                ((R324WithinHalfResidualPrefix.initial
                  ρ lam ε κm).SurvivingCoordinate → T4) =>
            ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κp).residualIntegrand
              ρ ε x y
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κp).reconstruct p.1) : ℂ) *
              terminal.residualSumCrossFactor
                π (leftTrace.terminalProjection p.1)
                  (rightTrace.terminalProjection p.2))
          ((Measure.pi fun _ => paperMeasure).prod
            (Measure.pi fun _ => paperMeasure)) := by
      apply hraw.congr
      filter_upwards with p
      unfold terminal R324TwoHalfTerminalData.residualSumCrossFactor
      rw [
        leftTrace.r324ResidualPrimitiveSumProduct_complex_eq_terminalProjection
          rightTrace π p]
      ring
    exact hprojected.prod_left_ae
  have hleftTerminal :=
    leftTrace.integrable_terminalPrefix_residualIntegrand
      x y hleftSection
  have hrightTerminal :=
    rightTrace.integrable_terminalPrefix_residualIntegrand
      z w hrightSection
  have hterminal :
      Integrable
        (terminal.terminalResidualSumPhysicalCore π x y z w)
        ((Measure.pi fun _ :
            leftTrace.terminalPrefix.SurvivingCoordinate =>
              paperMeasure).prod
          (Measure.pi fun _ :
            rightTrace.terminalPrefix.SurvivingCoordinate =>
              paperMeasure)) := by
    have hbare := hleftTerminal.mul_prod hrightTerminal
    have hwithCross := hbare.mul_bdd
      (terminal.measurable_residualSumCrossFactor π).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hcrossBound p)
    apply hwithCross.congr
    filter_upwards with p
    unfold R324TwoHalfTerminalData.terminalResidualSumPhysicalCore
    dsimp only [terminal, R324TwoHalfTerminalData.ofCertifiedTraces]
  exact
    leftTrace.twoHalf_lamEps_pow_integral_initialRootResidualSum_eq_initialNested_of_root
      rightTrace π x y z w hleftRoot hrootProduct hterminal

/-- Product-measure form of the preceding theorem, matching the exact
two-half root emitted by `momentRefinedDeterministicTermSum_eq_initialTwoHalfRoot`.
-/
theorem twoHalf_lamEps_pow_integral_initialRootProduct_eq_initialNested_of_sections
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {leftScale rightScale : Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κp) leftScale)
    (rightTrace :
      R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κm) rightScale)
    (π : κp.singles ≃ κm.singles)
    (x y z w : T4)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hleftSection :
      Integrable
        (fun vl :
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κp).SurvivingCoordinate → T4 =>
          ((R324WithinHalfResidualPrefix.initial
            ρ lam ε κp).residualIntegrand
              ρ ε x y
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κp).reconstruct vl) : ℂ))
        (Measure.pi fun _ => paperMeasure))
    (hrightSection :
      Integrable
        (fun vr :
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).SurvivingCoordinate → T4 =>
          ((R324WithinHalfResidualPrefix.initial
            ρ lam ε κm).residualIntegrand
              ρ ε z w
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).reconstruct vr) : ℂ))
        (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^
          (2 * ((R324WithinHalfResidualPrefix.initial
              ρ lam ε κp).remainingOrder +
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).remainingOrder)) *
        (∫ p :
            ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κp).SurvivingCoordinate → T4) ×
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).SurvivingCoordinate → T4),
          ((R324WithinHalfResidualPrefix.initial
              ρ lam ε κp).residualIntegrand
            ρ ε x y
            ((R324WithinHalfResidualPrefix.initial
              ρ lam ε κp).reconstruct p.1) : ℂ) *
            (((R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).residualIntegrand
              ρ ε z w
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).reconstruct p.2) : ℂ) *
              (r324ResidualPrimitiveSumProduct
                ρ ε κp κm π
                (r324TwoHalfRootDoubledReconstruct
                  (R324WithinHalfResidualPrefix.initial
                    ρ lam ε κp)
                  (R324WithinHalfResidualPrefix.initial
                    ρ lam ε κm) p) : ℂ))
          ∂((Measure.pi fun _ => paperMeasure).prod
            (Measure.pi fun _ => paperMeasure))) =
      ∫ v :
          (R324TwoHalfTerminalData.ofCertifiedTraces
            leftTrace rightTrace).NestedCoordinate π → T4,
        (R324TwoHalfTerminalData.ofCertifiedTraces
          leftTrace rightTrace).initialNestedResidualSumPhysicalCore
            π x y z w v
        ∂Measure.pi fun _ => paperMeasure := by
  let leftRes :=
    R324WithinHalfResidualPrefix.initial ρ lam ε κp
  let rightRes :=
    R324WithinHalfResidualPrefix.initial ρ lam ε κm
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces
      leftTrace rightTrace
  obtain ⟨crossBound, hcrossBound0, hcrossBound⟩ :=
    terminal.exists_norm_residualSumCrossFactor_le hε hε1 π
  have hleftProjection := leftTrace.measurable_terminalProjection
  have hrightProjection := rightTrace.measurable_terminalProjection
  have hprojection :
      Measurable fun p :
          (leftRes.SurvivingCoordinate → T4) ×
            (rightRes.SurvivingCoordinate → T4) =>
        (leftTrace.terminalProjection p.1,
          rightTrace.terminalProjection p.2) :=
    (hleftProjection.comp measurable_fst).prodMk
      (hrightProjection.comp measurable_snd)
  have hprojectedIntegrable :
      Integrable
        (fun p :
            (leftRes.SurvivingCoordinate → T4) ×
              (rightRes.SurvivingCoordinate → T4) =>
          (leftRes.residualIntegrand
              ρ ε x y (leftRes.reconstruct p.1) : ℂ) *
            ((rightRes.residualIntegrand
                ρ ε z w (rightRes.reconstruct p.2) : ℂ) *
              terminal.residualSumCrossFactor
                π (leftTrace.terminalProjection p.1)
                  (rightTrace.terminalProjection p.2)))
        ((Measure.pi fun _ => paperMeasure).prod
          (Measure.pi fun _ => paperMeasure)) := by
    have hbare := hleftSection.mul_prod hrightSection
    have hwithCross := hbare.mul_bdd
      ((terminal.measurable_residualSumCrossFactor π).comp
        hprojection).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p =>
        hcrossBound
          (leftTrace.terminalProjection p.1,
            rightTrace.terminalProjection p.2))
    apply hwithCross.congr
    filter_upwards with p
    dsimp only [Function.comp_apply, leftRes, rightRes]
    exact mul_assoc _ _ _
  have hrawIntegrable :
      Integrable
        (fun p :
            (leftRes.SurvivingCoordinate → T4) ×
              (rightRes.SurvivingCoordinate → T4) =>
          (leftRes.residualIntegrand
              ρ ε x y (leftRes.reconstruct p.1) : ℂ) *
            ((rightRes.residualIntegrand
                ρ ε z w (rightRes.reconstruct p.2) : ℂ) *
              (r324ResidualPrimitiveSumProduct
                ρ ε κp κm π
                (r324TwoHalfRootDoubledReconstruct
                  leftRes rightRes p) : ℂ)))
        ((Measure.pi fun _ => paperMeasure).prod
          (Measure.pi fun _ => paperMeasure)) := by
    apply hprojectedIntegrable.congr
    filter_upwards with p
    unfold terminal R324TwoHalfTerminalData.residualSumCrossFactor
    rw [← leftTrace.r324ResidualPrimitiveSumProduct_complex_eq_terminalProjection
      rightTrace π p]
  have hproductEq :
      (∫ p :
          (leftRes.SurvivingCoordinate → T4) ×
            (rightRes.SurvivingCoordinate → T4),
        (leftRes.residualIntegrand
            ρ ε x y (leftRes.reconstruct p.1) : ℂ) *
          ((rightRes.residualIntegrand
              ρ ε z w (rightRes.reconstruct p.2) : ℂ) *
            (r324ResidualPrimitiveSumProduct
              ρ ε κp κm π
              (r324TwoHalfRootDoubledReconstruct
                leftRes rightRes p) : ℂ))
        ∂((Measure.pi fun _ => paperMeasure).prod
          (Measure.pi fun _ => paperMeasure))) =
        ∫ vr : rightRes.SurvivingCoordinate → T4,
          (rightRes.residualIntegrand
              ρ ε z w (rightRes.reconstruct vr) : ℂ) *
            (∫ vl : leftRes.SurvivingCoordinate → T4,
              (leftRes.residualIntegrand
                  ρ ε x y (leftRes.reconstruct vl) : ℂ) *
                (r324ResidualPrimitiveSumProduct
                  ρ ε κp κm π
                  (r324TwoHalfRootDoubledReconstruct
                    leftRes rightRes (vl, vr)) : ℂ)
              ∂Measure.pi fun _ => paperMeasure)
          ∂Measure.pi fun _ => paperMeasure := by
    rw [integral_prod_symm _ hrawIntegrable]
    apply integral_congr_ae
    filter_upwards with vr
    calc
      (∫ vl,
          (leftRes.residualIntegrand
              ρ ε x y (leftRes.reconstruct vl) : ℂ) *
            ((rightRes.residualIntegrand
                ρ ε z w (rightRes.reconstruct vr) : ℂ) *
              (r324ResidualPrimitiveSumProduct
                ρ ε κp κm π
                (r324TwoHalfRootDoubledReconstruct
                  leftRes rightRes (vl, vr)) : ℂ))
          ∂Measure.pi fun _ => paperMeasure) =
          ∫ vl,
            (rightRes.residualIntegrand
                ρ ε z w (rightRes.reconstruct vr) : ℂ) *
              ((leftRes.residualIntegrand
                  ρ ε x y (leftRes.reconstruct vl) : ℂ) *
                (r324ResidualPrimitiveSumProduct
                  ρ ε κp κm π
                  (r324TwoHalfRootDoubledReconstruct
                    leftRes rightRes (vl, vr)) : ℂ))
            ∂Measure.pi fun _ => paperMeasure := by
        apply integral_congr_ae
        filter_upwards with vl
        ring
      _ = _ := by rw [integral_const_mul]
  have hiterated :=
    leftTrace.twoHalf_lamEps_pow_integral_initialRootResidualSum_eq_initialNested_of_sections
      rightTrace π x y z w hε hε1 hleftSection hrightSection
  have houterScale :
      (∫ vr : rightRes.SurvivingCoordinate → T4,
          (rightRes.residualIntegrand
              ρ ε z w (rightRes.reconstruct vr) : ℂ) *
            ((lamEps lam ε : ℂ) ^ (2 * leftRes.remainingOrder) *
              (∫ vl : leftRes.SurvivingCoordinate → T4,
                (leftRes.residualIntegrand
                    ρ ε x y (leftRes.reconstruct vl) : ℂ) *
                  (r324ResidualPrimitiveSumProduct
                    ρ ε κp κm π
                    (r324TwoHalfRootDoubledReconstruct
                      leftRes rightRes (vl, vr)) : ℂ)
                ∂Measure.pi fun _ => paperMeasure))
          ∂Measure.pi fun _ => paperMeasure) =
        (lamEps lam ε : ℂ) ^ (2 * leftRes.remainingOrder) *
          ∫ vr : rightRes.SurvivingCoordinate → T4,
            (rightRes.residualIntegrand
                ρ ε z w (rightRes.reconstruct vr) : ℂ) *
              (∫ vl : leftRes.SurvivingCoordinate → T4,
                (leftRes.residualIntegrand
                    ρ ε x y (leftRes.reconstruct vl) : ℂ) *
                  (r324ResidualPrimitiveSumProduct
                    ρ ε κp κm π
                    (r324TwoHalfRootDoubledReconstruct
                      leftRes rightRes (vl, vr)) : ℂ)
                ∂Measure.pi fun _ => paperMeasure)
            ∂Measure.pi fun _ => paperMeasure := by
    calc
      _ = ∫ vr : rightRes.SurvivingCoordinate → T4,
          (lamEps lam ε : ℂ) ^ (2 * leftRes.remainingOrder) *
            ((rightRes.residualIntegrand
                ρ ε z w (rightRes.reconstruct vr) : ℂ) *
              (∫ vl : leftRes.SurvivingCoordinate → T4,
                (leftRes.residualIntegrand
                    ρ ε x y (leftRes.reconstruct vl) : ℂ) *
                  (r324ResidualPrimitiveSumProduct
                    ρ ε κp κm π
                    (r324TwoHalfRootDoubledReconstruct
                      leftRes rightRes (vl, vr)) : ℂ)
                ∂Measure.pi fun _ => paperMeasure))
          ∂Measure.pi fun _ => paperMeasure := by
        apply integral_congr_ae
        filter_upwards with vr
        ring
      _ = _ := by rw [integral_const_mul]
  have hpow :
      (lamEps lam ε : ℂ) ^
          (2 * (leftRes.remainingOrder + rightRes.remainingOrder)) =
        (lamEps lam ε : ℂ) ^ (2 * rightRes.remainingOrder) *
          (lamEps lam ε : ℂ) ^ (2 * leftRes.remainingOrder) := by
    rw [show 2 * (leftRes.remainingOrder + rightRes.remainingOrder) =
        2 * rightRes.remainingOrder + 2 * leftRes.remainingOrder by omega,
      pow_add]
  calc
    _ = (lamEps lam ε : ℂ) ^ (2 * rightRes.remainingOrder) *
          ((lamEps lam ε : ℂ) ^ (2 * leftRes.remainingOrder) *
            ∫ vr : rightRes.SurvivingCoordinate → T4,
              (rightRes.residualIntegrand
                  ρ ε z w (rightRes.reconstruct vr) : ℂ) *
                (∫ vl : leftRes.SurvivingCoordinate → T4,
                  (leftRes.residualIntegrand
                      ρ ε x y (leftRes.reconstruct vl) : ℂ) *
                    (r324ResidualPrimitiveSumProduct
                      ρ ε κp κm π
                      (r324TwoHalfRootDoubledReconstruct
                        leftRes rightRes (vl, vr)) : ℂ)
                  ∂Measure.pi fun _ => paperMeasure)
              ∂Measure.pi fun _ => paperMeasure) := by
      rw [hproductEq, hpow]
      ring
    _ = (lamEps lam ε : ℂ) ^ (2 * rightRes.remainingOrder) *
          (∫ vr : rightRes.SurvivingCoordinate → T4,
            (rightRes.residualIntegrand
                ρ ε z w (rightRes.reconstruct vr) : ℂ) *
              ((lamEps lam ε : ℂ) ^ (2 * leftRes.remainingOrder) *
                (∫ vl : leftRes.SurvivingCoordinate → T4,
                  (leftRes.residualIntegrand
                      ρ ε x y (leftRes.reconstruct vl) : ℂ) *
                    (r324ResidualPrimitiveSumProduct
                      ρ ε κp κm π
                      (r324TwoHalfRootDoubledReconstruct
                        leftRes rightRes (vl, vr)) : ℂ)
                  ∂Measure.pi fun _ => paperMeasure))
            ∂Measure.pi fun _ => paperMeasure) := by
      rw [← houterScale]
    _ = _ := hiterated

/-- The preceding exact signed collapse holds at almost every pair of
endpoint pairs, with both section premises supplied by the proved all-Green
root integrability theorem. -/
theorem eventually_twoHalf_lamEps_pow_integral_initialRootResidualSum_eq_initialNested
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {leftScale rightScale : Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κp) leftScale)
    (rightTrace :
      R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κm) rightScale)
    (π : κp.singles ≃ κm.singles)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ xy : T4 × T4 ∂(paperMeasure.prod paperMeasure),
      ∀ᵐ zw : T4 × T4 ∂(paperMeasure.prod paperMeasure),
      (lamEps lam ε : ℂ) ^ (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).remainingOrder) *
          (∫ vr :
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).SurvivingCoordinate → T4,
            ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).residualIntegrand
              ρ ε zw.1 zw.2
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).reconstruct vr) : ℂ) *
              ((lamEps lam ε : ℂ) ^ (2 *
                  (R324WithinHalfResidualPrefix.initial
                    ρ lam ε κp).remainingOrder) *
                (∫ vl :
                    (R324WithinHalfResidualPrefix.initial
                      ρ lam ε κp).SurvivingCoordinate → T4,
                  ((R324WithinHalfResidualPrefix.initial
                      ρ lam ε κp).residualIntegrand
                    ρ ε xy.1 xy.2
                    ((R324WithinHalfResidualPrefix.initial
                      ρ lam ε κp).reconstruct vl) : ℂ) *
                    (r324ResidualPrimitiveSumProduct
                      ρ ε κp κm π
                      (r324TwoHalfRootDoubledReconstruct
                        (R324WithinHalfResidualPrefix.initial
                          ρ lam ε κp)
                        (R324WithinHalfResidualPrefix.initial
                          ρ lam ε κm) (vl, vr)) : ℂ)
                  ∂Measure.pi fun _ => paperMeasure))
            ∂Measure.pi fun _ => paperMeasure) =
        ∫ v :
            (R324TwoHalfTerminalData.ofCertifiedTraces
              leftTrace rightTrace).NestedCoordinate π → T4,
          (R324TwoHalfTerminalData.ofCertifiedTraces
            leftTrace rightTrace).initialNestedResidualSumPhysicalCore
              π xy.1 xy.2 zw.1 zw.2 v
          ∂Measure.pi fun _ => paperMeasure := by
  filter_upwards
      [eventually_integrable_initial_residualIntegrand
        ρ lam hε hε1 κp] with xy hleftSection
  filter_upwards
      [eventually_integrable_initial_residualIntegrand
        ρ lam hε hε1 κm] with zw hrightSection
  exact
    leftTrace.twoHalf_lamEps_pow_integral_initialRootResidualSum_eq_initialNested_of_sections
      rightTrace π xy.1 xy.2 zw.1 zw.2 hε hε1
      hleftSection hrightSection

end R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

end

end Anderson4D
