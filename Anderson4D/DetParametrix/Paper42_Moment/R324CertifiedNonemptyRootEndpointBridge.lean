import Anderson4D.DetParametrix.Paper42_Moment.R324CertifiedTerminalFubini
import Anderson4D.DetParametrix.Paper42_Moment.R324InitialTwoHalfRootIntegrability
import Anderson4D.DetParametrix.Paper42_Moment.R324PhaseAOrderLedgerBridge

/-!
# Certified nonempty-root endpoint bridge for R-324

This module carries one residual-refined physical fibre through the two
certified within-half traces and then through the exact four-endpoint Fubini
identity.  Every equality remains signed.  In particular, the complete
residual primitive sum is kept grouped and no norm or pointwise majorization
is introduced.

The analytic premises retained below are the almost-everywhere root
section integrability, the joint root-product integrability, and the
terminal-product integrability genuinely consumed by the certified traces.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## Initial doubled-coordinate reindexing -/

/-- Reindex the two literal initial sparse half carriers as the ambient
`Fin (2m)` tuple used by a residual-refined physical fibre. -/
def r324InitialTwoHalfProductPiMeasurableEquiv
    (ρ : SmoothCutoff) (lam ε : ℝ) {m : ℕ}
    (κp κm : PartialPairing (Fin m)) :
    ((R324WithinHalfResidualPrefix.initial
          ρ lam ε κp).SurvivingCoordinate → T4) ×
        ((R324WithinHalfResidualPrefix.initial
          ρ lam ε κm).SurvivingCoordinate → T4) ≃ᵐ
      (Fin (2 * m) → T4) :=
  (MeasurableEquiv.prodCongr
      (R324WithinHalfResidualPrefix.initialPiMeasurableEquiv
        ρ lam ε κp)
      (R324WithinHalfResidualPrefix.initialPiMeasurableEquiv
        ρ lam ε κm)).trans
    (r324DoublePiMeasurableEquiv m).symm

/-- The initial two-half reindexing preserves the exact product Haar
measure. -/
theorem measurePreserving_r324InitialTwoHalfProductPiMeasurableEquiv
    (ρ : SmoothCutoff) (lam ε : ℝ) {m : ℕ}
    (κp κm : PartialPairing (Fin m)) :
    MeasurePreserving
      (r324InitialTwoHalfProductPiMeasurableEquiv
        ρ lam ε κp κm)
      ((Measure.pi fun _ :
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κp).SurvivingCoordinate => paperMeasure).prod
        (Measure.pi fun _ :
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κm).SurvivingCoordinate => paperMeasure))
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  exact
    (measurePreserving_r324DoublePiMeasurableEquiv m).symm.comp
      ((R324WithinHalfResidualPrefix.measurePreserving_initialPiMeasurableEquiv
          ρ lam ε κp).prod
        (R324WithinHalfResidualPrefix.measurePreserving_initialPiMeasurableEquiv
          ρ lam ε κm))

/-- The preceding measurable equivalence is pointwise the doubled
reconstruction already consumed by the certified two-half collapse. -/
@[simp]
theorem r324InitialTwoHalfProductPiMeasurableEquiv_apply
    (ρ : SmoothCutoff) (lam ε : ℝ) {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (p :
      ((R324WithinHalfResidualPrefix.initial
          ρ lam ε κp).SurvivingCoordinate → T4) ×
        ((R324WithinHalfResidualPrefix.initial
          ρ lam ε κm).SurvivingCoordinate → T4)) :
    r324InitialTwoHalfProductPiMeasurableEquiv
        ρ lam ε κp κm p =
      r324TwoHalfRootDoubledReconstruct
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κp)
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κm) p := by
  apply (r324DoublePiMeasurableEquiv m).injective
  simp only [
    r324InitialTwoHalfProductPiMeasurableEquiv,
    MeasurableEquiv.trans_apply,
    MeasurableEquiv.apply_symm_apply,
    r324DoublePiMeasurableEquiv_apply,
    r324TwoHalfRootDoubledReconstruct,
    momentDoubleFinEquiv_symm_leftMomentIndex,
    momentDoubleFinEquiv_symm_rightMomentIndex]
  change
    ((R324WithinHalfResidualPrefix.initialPiMeasurableEquiv
        ρ lam ε κp) p.1,
      (R324WithinHalfResidualPrefix.initialPiMeasurableEquiv
        ρ lam ε κm) p.2) =
      ((fun i =>
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κp).reconstruct p.1 i),
        fun j =>
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κm).reconstruct p.2 j)
  apply Prod.ext
  · exact
      (R324WithinHalfResidualPrefix.initial_reconstruct_eq
        ρ lam ε κp p.1).symm
  · exact
      (R324WithinHalfResidualPrefix.initial_reconstruct_eq
        ρ lam ε κm p.2).symm

/-! ## Exact refined-root coordinate bridge -/

/-- Integral transport from the ambient doubled tuple to the two initial
sparse half carriers.  No integrability premise is needed for this
measure-preserving identity. -/
theorem integral_ambient_eq_initialTwoHalfProduct
    (ρ : SmoothCutoff) (lam ε : ℝ) {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (F : (Fin (2 * m) → T4) → ℂ) :
    (∫ v : Fin (2 * m) → T4, F v
        ∂Measure.pi fun _ => paperMeasure) =
      ∫ p :
          ((R324WithinHalfResidualPrefix.initial
              ρ lam ε κp).SurvivingCoordinate → T4) ×
            ((R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).SurvivingCoordinate → T4),
        F
          (r324TwoHalfRootDoubledReconstruct
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κp)
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm) p)
        ∂((Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κp).SurvivingCoordinate => paperMeasure).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).SurvivingCoordinate => paperMeasure)) := by
  have hp :=
    measurePreserving_r324InitialTwoHalfProductPiMeasurableEquiv
      ρ lam ε κp κm
  calc
    _ =
        ∫ p :
            ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κp).SurvivingCoordinate → T4) ×
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).SurvivingCoordinate → T4),
          F
            (r324InitialTwoHalfProductPiMeasurableEquiv
              ρ lam ε κp κm p)
          ∂((Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε κp).SurvivingCoordinate => paperMeasure).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).SurvivingCoordinate => paperMeasure)) := by
      symm
      simpa only [Function.comp_apply] using hp.integral_comp' F
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with p
      rw [r324InitialTwoHalfProductPiMeasurableEquiv_apply]

/-- At fixed external endpoints, one residual-refined root is exactly the
product of its two initial certified residual carriers and the still-grouped
cross-cut primitive sum. -/
theorem integral_momentRefinedPhysicalIntegrand_eq_initialTwoHalfRoot
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4)
    (s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (x y z w : T4) :
    (∫ v : Fin (2 * m) → T4,
        momentRefinedPhysicalIntegrand
          ρ ε m α β s r x y z w v
        ∂Measure.pi fun _ => paperMeasure) =
      ∫ p :
          ((R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).SurvivingCoordinate → T4) ×
            ((R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.2.1).SurvivingCoordinate → T4),
        momentFourierPhase α β x y z w *
          ((R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).residualIntegrand
            ρ ε x y
            ((R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).reconstruct p.1) : ℂ) *
          ((R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.2.1).residualIntegrand
            ρ ε z w
            ((R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.2.1).reconstruct p.2) : ℂ) *
          (r324ResidualPrimitiveSumProduct
            ρ ε e₀.1 e₀.2.1 e₀.2.2
            (r324TwoHalfRootDoubledReconstruct
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.1)
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.2.1) p) : ℂ)
        ∂((Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).SurvivingCoordinate => paperMeasure).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.2.1).SurvivingCoordinate => paperMeasure)) := by
  calc
    _ =
        ∫ v : Fin (2 * m) → T4,
          momentFourierPhase α β x y z w *
            ((R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.1).residualIntegrand
              ρ ε x y
              (fun i => v (leftMomentIndex i)) : ℂ) *
            ((R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.2.1).residualIntegrand
              ρ ε z w
              (fun i => v (rightMomentIndex i)) : ℂ) *
            (r324ResidualPrimitiveSumProduct
              ρ ε e₀.1 e₀.2.1 e₀.2.2 v : ℂ)
          ∂Measure.pi fun _ => paperMeasure := by
      apply integral_congr_ae
      filter_upwards with v
      exact
        momentRefinedPhysicalIntegrand_eq_twoInitialResiduals_mul_cross
          ρ lam ε m α β s r e₀ he₀ x y z w v
    _ = _ := by
      rw [integral_ambient_eq_initialTwoHalfProduct
        ρ lam ε e₀.1 e₀.2.1]
      apply integral_congr_ae
      filter_upwards with p
      have hleft :
          (fun i =>
            r324TwoHalfRootDoubledReconstruct
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.1)
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.2.1) p
              (leftMomentIndex i)) =
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).reconstruct p.1 := by
        funext i
        unfold r324TwoHalfRootDoubledReconstruct
        rw [momentDoubleFinEquiv_symm_leftMomentIndex]
      have hright :
          (fun j =>
            r324TwoHalfRootDoubledReconstruct
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.1)
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.2.1) p
              (rightMomentIndex j)) =
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.2.1).reconstruct p.2 := by
        funext j
        unfold r324TwoHalfRootDoubledReconstruct
        rw [momentDoubleFinEquiv_symm_rightMomentIndex]
      rw [hleft, hright]

/-- Fivefold form of the preceding bridge for the genuine signed
`r324RefinedPhysicalIntegral`.  Joint integrability is discharged by the
already proved refined-fibre integrability theorem before any iterated
integral is introduced. -/
theorem r324RefinedPhysicalIntegral_eq_initialTwoHalfRoot
    (ρ : SmoothCutoff) (lam : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (α β : Z4)
    (s :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hs : s ∈ momentContractionSignatures m)
    (r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hr : r ∈ momentResidualChainSignaturesAt m s)
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r) :
    r324RefinedPhysicalIntegral ρ ε m α β
        (⟨⟨s, hs⟩, ⟨r, hr⟩⟩ :
          R324RefinedScheduleIndex m) =
      ∫ x, ∫ y, ∫ z, ∫ w,
        ∫ p :
            ((R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.1).SurvivingCoordinate → T4) ×
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.2.1).SurvivingCoordinate → T4),
          momentFourierPhase α β x y z w *
            ((R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.1).residualIntegrand
              ρ ε x y
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.1).reconstruct p.1) : ℂ) *
            ((R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.2.1).residualIntegrand
              ρ ε z w
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.2.1).reconstruct p.2) : ℂ) *
            (r324ResidualPrimitiveSumProduct
              ρ ε e₀.1 e₀.2.1 e₀.2.2
              (r324TwoHalfRootDoubledReconstruct
                (R324WithinHalfResidualPrefix.initial
                  ρ lam ε e₀.1)
                (R324WithinHalfResidualPrefix.initial
                  ρ lam ε e₀.2.1) p) : ℂ)
          ∂((Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.1).SurvivingCoordinate => paperMeasure).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.2.1).SurvivingCoordinate => paperMeasure))
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure := by
  unfold r324RefinedPhysicalIntegral
  rw [r324_integral_product_eq_five
    (momentRefinedPhysicalIntegrand
      ρ ε m α β s r)
    (integrable_r324RefinedPhysicalIntegrand
      ρ hε hε1 α β
      (⟨⟨s, hs⟩, ⟨r, hr⟩⟩ :
        R324RefinedScheduleIndex m))]
  apply integral_congr_ae
  filter_upwards with x
  apply integral_congr_ae
  filter_upwards with y
  apply integral_congr_ae
  filter_upwards with z
  apply integral_congr_ae
  filter_upwards with w
  exact
    integral_momentRefinedPhysicalIntegrand_eq_initialTwoHalfRoot
      ρ lam ε m α β s r e₀ he₀ x y z w

/-- The same exact fivefold root bridge with the scalar
`momentRefinedDeterministicTermSum` used by the corrected R-324 output. -/
theorem momentRefinedDeterministicTermSum_eq_initialTwoHalfRoot
    (ρ : SmoothCutoff) (lam : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (α β : Z4)
    (s :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hs : s ∈ momentContractionSignatures m)
    (r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hr : r ∈ momentResidualChainSignaturesAt m s)
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r) :
    momentRefinedDeterministicTermSum
        ρ ε m α β s r =
      ∫ x, ∫ y, ∫ z, ∫ w,
        ∫ p :
            ((R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.1).SurvivingCoordinate → T4) ×
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.2.1).SurvivingCoordinate → T4),
          momentFourierPhase α β x y z w *
            ((R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.1).residualIntegrand
              ρ ε x y
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.1).reconstruct p.1) : ℂ) *
            ((R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.2.1).residualIntegrand
              ρ ε z w
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.2.1).reconstruct p.2) : ℂ) *
            (r324ResidualPrimitiveSumProduct
              ρ ε e₀.1 e₀.2.1 e₀.2.2
              (r324TwoHalfRootDoubledReconstruct
                (R324WithinHalfResidualPrefix.initial
                  ρ lam ε e₀.1)
                (R324WithinHalfResidualPrefix.initial
                  ρ lam ε e₀.2.1) p) : ℂ)
          ∂((Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.1).SurvivingCoordinate => paperMeasure).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.2.1).SurvivingCoordinate => paperMeasure))
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure := by
  rw [
    momentRefinedDeterministicTermSum_eq_r324RefinedPhysicalIntegral
      ρ hε hε1 α β s hs r hr]
  exact
    r324RefinedPhysicalIntegral_eq_initialTwoHalfRoot
      ρ lam hε hε1 α β s hs r hr e₀ he₀

/-! ## Certified collapse of the two initial roots -/

namespace R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {leftScale rightScale : Fin (m + 1) → ℝ}

/-- Root section integrability supplies the exact weighted hypotheses for
both certified traces, after which the existing signed two-half iteration
reaches the initial nested-cross carrier.  The endpoint-dependent premises
are intentionally explicit: global product-space integrability yields them
only almost everywhere. -/
theorem
    twoHalf_lamEps_pow_integral_initialRootResidualSum_eq_initialNested_of_root
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
    (hleftRoot :
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
              (R324TwoHalfTerminalData.ofCertifiedTraces
                leftTrace rightTrace).residualSumCrossFactor
                  π
                  (leftTrace.terminalProjection vl)
                  (rightTrace.terminalProjection vr))
          (Measure.pi fun _ => paperMeasure))
    (hjoint :
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
              (R324TwoHalfTerminalData.ofCertifiedTraces
                leftTrace rightTrace).residualSumCrossFactor
                  π
                  (leftTrace.terminalProjection p.1)
                  (rightTrace.terminalProjection p.2)))
        ((Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κp).SurvivingCoordinate => paperMeasure).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).SurvivingCoordinate => paperMeasure)))
    (hterminal :
      Integrable
        ((R324TwoHalfTerminalData.ofCertifiedTraces
          leftTrace rightTrace).terminalResidualSumPhysicalCore
            π x y z w)
        ((Measure.pi fun _ :
            leftTrace.terminalPrefix.SurvivingCoordinate =>
              paperMeasure).prod
          (Measure.pi fun _ :
            rightTrace.terminalPrefix.SurvivingCoordinate =>
              paperMeasure))) :
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
  obtain ⟨hleft, hright⟩ :=
    leftTrace.twoHalf_weightedIntegrableAlong_of_root_integrable
      rightTrace
      ((R324TwoHalfTerminalData.ofCertifiedTraces
        leftTrace rightTrace).residualSumCrossFactor π)
      hleftRoot hjoint
  exact
    leftTrace.twoHalf_lamEps_pow_integral_rootResidualSum_eq_initialNested
      rightTrace π hleft hright hterminal

end R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

/-! ## Endpoint integration after the certified collapse -/

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal :
      R324TwoHalfTerminalData ρ lam ε κp κm)

/-- At fixed endpoints, the external Fourier phase may be kept outside the
lossless terminal-to-nested coordinate transport. -/
theorem integral_externalModeResidualSumIntegrand_eq_phase_mul_initialNested
    (π : κp.singles ≃ κm.singles)
    (α β : Z4) (x y z w : T4) :
    (∫ p,
        terminal.externalModeResidualSumIntegrand
          π α β p x y z w
        ∂((Measure.pi fun _ :
            terminal.left.SurvivingCoordinate => paperMeasure).prod
          (Measure.pi fun _ :
            terminal.right.SurvivingCoordinate => paperMeasure))) =
      momentFourierPhase α β x y z w *
        (∫ v : terminal.NestedCoordinate π → T4,
          terminal.initialNestedResidualSumPhysicalCore
            π x y z w v
          ∂Measure.pi fun _ => paperMeasure) := by
  calc
    _ =
        ∫ p,
          momentFourierPhase α β x y z w *
            terminal.terminalResidualSumPhysicalCore
              π x y z w p
          ∂((Measure.pi fun _ :
              terminal.left.SurvivingCoordinate => paperMeasure).prod
            (Measure.pi fun _ :
              terminal.right.SurvivingCoordinate => paperMeasure)) := by
      apply integral_congr_ae
      filter_upwards with p
      unfold externalModeResidualSumIntegrand momentFourierPhase
      rfl
    _ =
        momentFourierPhase α β x y z w *
          (∫ p,
            terminal.terminalResidualSumPhysicalCore
              π x y z w p
            ∂((Measure.pi fun _ :
                terminal.left.SurvivingCoordinate => paperMeasure).prod
              (Measure.pi fun _ :
                terminal.right.SurvivingCoordinate => paperMeasure))) :=
      by rw [integral_const_mul]
    _ = _ := by
      exact congrArg
        (fun t : ℂ => momentFourierPhase α β x y z w * t)
        (terminal.integral_terminalResidualSumPhysicalCore_eq_initialNested
          π x y z w)

end R324TwoHalfTerminalData

/-- Once the two initial residuals have reached the nested carrier, the
stored terminal certificates discharge the global endpoint/internal Fubini
premise and evaluate all four endpoint modes. -/
theorem
    integral_phase_mul_initialNestedResidualSum_eq_endpointIntegrated_of_storedCertificates
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {leftScale rightScale : Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κp) leftScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κm) rightScale)
    (π : κp.singles ≃ κm.singles)
    (hleft : leftTrace.terminalPrefix.state.active.Nonempty)
    (hright : rightTrace.terminalPrefix.state.active.Nonempty)
    (α β : Z4)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces
        leftTrace rightTrace
    (∫ x, ∫ y, ∫ z, ∫ w,
        momentFourierPhase α β x y z w *
          (∫ v : terminal.NestedCoordinate π → T4,
            terminal.initialNestedResidualSumPhysicalCore
              π x y z w v
            ∂Measure.pi fun _ => paperMeasure)
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure) =
      ∫ v : terminal.NestedCoordinate π → T4,
        terminal.initialNestedEndpointIntegratedResidualDensity
          π hleft hright α β v
        ∂Measure.pi fun _ => paperMeasure := by
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces
      leftTrace rightTrace
  calc
    _ =
        ∫ x, ∫ y, ∫ z, ∫ w,
          ∫ p,
            terminal.externalModeResidualSumIntegrand
              π α β p x y z w
            ∂((Measure.pi fun _ :
                terminal.left.SurvivingCoordinate => paperMeasure).prod
              (Measure.pi fun _ :
                terminal.right.SurvivingCoordinate => paperMeasure))
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with x
      apply integral_congr_ae
      filter_upwards with y
      apply integral_congr_ae
      filter_upwards with z
      apply integral_congr_ae
      filter_upwards with w
      exact
        (terminal.integral_externalModeResidualSumIntegrand_eq_phase_mul_initialNested
          π α β x y z w).symm
    _ = _ :=
      R324TwoHalfTerminalData.integral_externalModeResidualSumIntegrand_fubini_eq_initialNested_usingStoredCertificates
        leftTrace rightTrace π hleft hright α β hε hε1

end

end Anderson4D
