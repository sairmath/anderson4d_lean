import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingGroupedHalfTerminalBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324Step4CosineLoss

/-!
# Quantitative terminal estimate for one full-pairing half

This file joins three already certified pieces of the within-half
reduction without changing the order of summation and integration:

* the exact integration of the complete grouped terminal primitive block;
* the exact `𝓔`-symmetry reduction of the terminal phase to a cosine,
  followed by the frequency-independent Step 4 loss;
* the exact proper-prefix active-scale budget.

The primitive-pairing sum remains inside
`terminalGroupedPrimitiveCore` until its exact integration theorem is
used.  In particular, no absolute value is moved through that finite sum.
The result is a terminal half estimate used in the four-endpoint R-324 estimate.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfResidualPrefix

namespace R324FullPairingBudgetTerminalAdapter

variable {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    {budget :
      R324FullPairingBudgetStopTrace
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) (A := A) κ}

/-- Exact fixed-endpoint form of the grouped terminal integration, with
the heterogeneous primitive kernel written in the gap variable used by
the endpoint Fourier argument. -/
theorem
    lamEps_pow_integral_terminalGroupedPrimitiveCore_eq_predecessor_mul_primitiveKernelDiff
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (x z w : T4)
    (hint :
      ∀ κB :
          {κB : PartialPairing
              (Fin
                (2 * residualBlockOrder
                  data.geometry.terminalData.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)},
        Integrable
          (fun u :
              Fin
                  (2 * residualBlockOrder
                    data.geometry.terminalData.terminal.2 - 2) →
                T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2)
              κB.1
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).internalEdges
              (primitiveAssemble
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                z w u))
          (Measure.pi fun _ => paperMeasure)) :
    lamEps lam ε ^
          (2 * residualBlockOrder
            data.geometry.terminalData.terminal.2) *
        (∫ u :
            Fin
                (2 * residualBlockOrder
                  data.geometry.terminalData.terminal.2 - 2) →
              T4,
          data.geometry.terminalGroupedPrimitiveCore x
            (primitiveAssemble
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
              z w u)
          ∂Measure.pi fun _ => paperMeasure) =
      data.geometry.trace.stopPrefix.state.edges
          (r324WithinHalfPredecessorSlot
            data.geometry.trace.stopPrefix.state
            data.geometry.terminalData.terminal)
          (x - z) *
        primitiveKernelDiff ρ lam ε
          (residualBlockOrder
            data.geometry.terminalData.terminal.2)
          (data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
          (data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).internalEdges
          (z - w) := by
  rw [
    data.lamEps_pow_integral_terminalGroupedPrimitiveCore_eq_predecessor_mul_primitiveKernel
      x z w hint,
    data.geometry.terminalPrimitiveKernel_eq_diff]

/-- Exact gap-integral seam.  The complete signed terminal primitive sum
is integrated before the endpoint phase is introduced.  The predecessor
edge is independent of the gap and therefore factors outside the final
Bochner integral. -/
theorem
    integral_lamEps_pow_terminalGroupedPrimitiveCore_gap_mul_negCharacterSubOne_eq
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (x z : T4)
    (hint :
      ∀ (w : T4)
        (κB :
          {κB : PartialPairing
              (Fin
                (2 * residualBlockOrder
                  data.geometry.terminalData.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)}),
        Integrable
          (fun v :
              Fin
                  (2 * residualBlockOrder
                    data.geometry.terminalData.terminal.2 - 2) →
                T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2)
              κB.1
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).internalEdges
              (primitiveAssemble
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                z w v))
          (Measure.pi fun _ => paperMeasure))
    (β : Z4) :
    (∫ u : T4,
        (((lamEps lam ε ^
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2) *
            (∫ v :
                Fin
                    (2 * residualBlockOrder
                      data.geometry.terminalData.terminal.2 - 2) →
                  T4,
              data.geometry.terminalGroupedPrimitiveCore x
                (primitiveAssemble
                  (residualBlockOrder
                    data.geometry.terminalData.terminal.2)
                  (data.geometry.trace.stopPrefix.headContext
                    data.geometry.terminalData.terminal []
                    data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                  z (z - u) v)
              ∂Measure.pi fun _ => paperMeasure)) : ℝ) : ℂ) *
          (charT4 (-β) u - 1)
        ∂paperMeasure) =
      (data.geometry.trace.stopPrefix.state.edges
          (r324WithinHalfPredecessorSlot
            data.geometry.trace.stopPrefix.state
            data.geometry.terminalData.terminal)
          (x - z) : ℂ) *
        ∫ u : T4,
          (primitiveKernelDiff ρ lam ε
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).internalEdges
              u : ℂ) *
            (charT4 (-β) u - 1)
          ∂paperMeasure := by
  have hint' :
      ∀ (u : T4)
        (κB :
          {κB : PartialPairing
              (Fin
                (2 * residualBlockOrder
                  data.geometry.terminalData.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)}),
        Integrable
          (fun v :
              Fin
                  (2 * residualBlockOrder
                    data.geometry.terminalData.terminal.2 - 2) →
                T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2)
              κB.1
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).internalEdges
              (primitiveAssemble
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                z (z - u) v))
          (Measure.pi fun _ => paperMeasure) := by
    intro u κB
    exact hint (z - u) κB
  calc
    (∫ u : T4,
        (((lamEps lam ε ^
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2) *
            (∫ v :
                Fin
                    (2 * residualBlockOrder
                      data.geometry.terminalData.terminal.2 - 2) →
                  T4,
              data.geometry.terminalGroupedPrimitiveCore x
                (primitiveAssemble
                  (residualBlockOrder
                    data.geometry.terminalData.terminal.2)
                  (data.geometry.trace.stopPrefix.headContext
                    data.geometry.terminalData.terminal []
                    data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                  z (z - u) v)
              ∂Measure.pi fun _ => paperMeasure)) : ℝ) : ℂ) *
          (charT4 (-β) u - 1)
        ∂paperMeasure) =
      ∫ u : T4,
        ((data.geometry.trace.stopPrefix.state.edges
              (r324WithinHalfPredecessorSlot
                data.geometry.trace.stopPrefix.state
                data.geometry.terminalData.terminal)
              (x - z) *
            primitiveKernelDiff ρ lam ε
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).internalEdges
              u : ℝ) : ℂ) *
          (charT4 (-β) u - 1)
        ∂paperMeasure := by
          apply integral_congr_ae
          filter_upwards with u
          rw [
            data.lamEps_pow_integral_terminalGroupedPrimitiveCore_eq_predecessor_mul_primitiveKernelDiff
              x z (z - u) (hint' u)]
          congr 3
          abel_nf
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      push_cast
      ring

/-- The exact cosine identity and the Step 4 domination give a bound for
the genuine complex phase defect, rather than only for its real part. -/
theorem
    norm_integral_terminalPrimitiveKernelDiff_mul_negCharacterSubOne_le_two_mul
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (hε : 0 < ε) (supportConstant primitiveConstant : ℝ)
    (hbound :
      PrimitiveKernelBounds ρ lam ε
        (residualBlockOrder
          data.geometry.terminalData.terminal.2)
        (data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
        (data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).internalEdges
        supportConstant primitiveConstant)
    (β : Z4) :
    ‖∫ u,
        (primitiveKernelDiff ρ lam ε
            (residualBlockOrder
              data.geometry.terminalData.terminal.2)
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).internalEdges u :
          ℂ) *
          (charT4 (-β) u - 1)
        ∂paperMeasure‖ ≤
      2 *
        ∫ u,
          primitiveKernelMajorant primitiveConstant lam ε supportConstant
            (residualBlockOrder
              data.geometry.terminalData.terminal.2) u
          ∂paperMeasure := by
  rw [
    data.integral_terminalPrimitiveKernelDiff_mul_negCharacterSubOne_eq_cos_of_bounds
      hε supportConstant primitiveConstant hbound β]
  exact
    data.norm_integral_terminalPrimitiveKernelDiff_mul_r324CharacterCos_sub_one_le_two_mul
      hε supportConstant primitiveConstant hbound β

/-- Certificate-scaled Step 4 estimate for the genuine heterogeneous
terminal primitive kernel.

The Proposition 4.1 input is used only on normalized admissible kernels.
The raw terminal edges are normalized by their stored positive scales, so
the product of those scales occurs exactly once on the right.  The value at
the identity is discarded through the atomless Haar measure; no pointwise
bound there is assumed. -/
theorem
    norm_integral_terminalPrimitiveKernelDiff_mul_negCharacterSubOne_le_scaled
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (hε : 0 < ε) (supportConstant primitiveConstant : ℝ)
    (hprimitive : 0 ≤ primitiveConstant)
    (hlam : 0 ≤ lam)
    (hprop :
      ∀ H :
          Fin
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2 - 1) →
            T4 → ℝ,
        IsAdmissiblePrimitiveInput
            (residualBlockOrder
              data.geometry.terminalData.terminal.2) H →
          MemEClassT4
              (primitiveKernelDiff ρ lam ε
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff ρ lam ε
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                H) ∧
            PrimitiveKernelBounds ρ lam ε
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
              H supportConstant primitiveConstant)
    (β : Z4) :
    ‖∫ u,
        (primitiveKernelDiff ρ lam ε
            (residualBlockOrder
              data.geometry.terminalData.terminal.2)
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).internalEdges u :
          ℂ) *
          (charT4 (-β) u - 1)
        ∂paperMeasure‖ ≤
      2 *
        r324WithinHalfInternalEdgeScaleProduct
          (data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton)
          budget.stopScale *
        ∫ u,
          primitiveKernelMajorant primitiveConstant lam ε supportConstant
            (residualBlockOrder
              data.geometry.terminalData.terminal.2) u
          ∂paperMeasure := by
  let ctx :=
    data.geometry.trace.stopPrefix.headContext
      data.geometry.terminalData.terminal []
      data.geometry.stop_remaining_eq_singleton
  let J : T4 → ℝ :=
    primitiveKernelDiff ρ lam ε
      (residualBlockOrder data.geometry.terminalData.terminal.2)
      ctx.one_le_blockOrder ctx.internalEdges
  let Jscale : ℝ :=
    r324WithinHalfInternalEdgeScaleProduct ctx budget.stopScale
  let M : T4 → ℝ :=
    primitiveKernelMajorant primitiveConstant lam ε supportConstant
      (residualBlockOrder data.geometry.terminalData.terminal.2)
  letI : NullSingletonClass paperMeasure :=
    ⟨paperMeasure_singleton⟩
  have hJscale : 0 < Jscale :=
    data.certificate.internalEdgeScaleProduct_pos
  have hJoff : ∀ u, u ≠ 0 → |J u| ≤ Jscale * M u := by
    intro u hu
    dsimp only [J, Jscale, M]
    simpa [
      ctx, R324WithinHalfResidualPrefix.headContext,
      R324WithinHalfStepContext.internalEdges,
      r324WithinHalfInternalEdgeScaleProduct] using
      primitiveKernelDiff_le_prod_edgeScales_mul_majorant_offDiagonal
        ρ ctx.one_le_blockOrder ctx.internalEdges
        (fun j => budget.stopScale (ctx.internalSlot j))
        (fun j => data.certificate.scale_pos (ctx.internalSlot j))
        (fun j => data.certificate.memE (ctx.internalSlot j))
        (fun j => data.certificate.bound (ctx.internalSlot j))
        hprop u hu
  have hMnonneg : ∀ u, 0 ≤ M u := by
    intro u
    exact primitiveKernelMajorant_nonneg hprimitive hlam
  have hJrepresentative :
      ∀ u, |offDiagonalRepresentative J u| ≤ Jscale * M u := by
    intro u
    by_cases hu : u = 0
    · subst u
      rw [offDiagonalRepresentative_zero, abs_zero]
      exact mul_nonneg hJscale.le (hMnonneg 0)
    · rw [offDiagonalRepresentative_eq J hu]
      exact hJoff u hu
  have hmajor :
      Integrable M paperMeasure :=
    integrable_primitiveKernelMajorant primitiveConstant lam ε
      supportConstant
      (residualBlockOrder data.geometry.terminalData.terminal.2) hε
  have hphase :
      ‖∫ u,
          (offDiagonalRepresentative J u : ℂ) *
            (charT4 (-β) u - 1)
          ∂paperMeasure‖ ≤
        2 * Jscale * ∫ u, M u ∂paperMeasure := by
    have hscaled :
        Integrable (fun u => 2 * (Jscale * M u)) paperMeasure := by
      exact (hmajor.const_mul Jscale).const_mul 2
    calc
      ‖∫ u,
          (offDiagonalRepresentative J u : ℂ) *
            (charT4 (-β) u - 1)
          ∂paperMeasure‖ ≤
          ∫ u,
            ‖(offDiagonalRepresentative J u : ℂ) *
              (charT4 (-β) u - 1)‖
            ∂paperMeasure :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ u, 2 * (Jscale * M u) ∂paperMeasure := by
        refine integral_mono_of_nonneg
          (.of_forall fun u => norm_nonneg _)
          hscaled
          (.of_forall fun u => ?_)
        change
          ‖(offDiagonalRepresentative J u : ℂ) *
              (charT4 (-β) u - 1)‖ ≤
            2 * (Jscale * M u)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hchar :
            ‖charT4 (-β) u - 1‖ ≤ 2 := by
          calc
            ‖charT4 (-β) u - 1‖ ≤
                ‖charT4 (-β) u‖ + ‖(1 : ℂ)‖ :=
              norm_sub_le _ _
            _ = 2 := by rw [norm_charT4]; norm_num
        calc
          |offDiagonalRepresentative J u| *
                ‖charT4 (-β) u - 1‖ ≤
              |offDiagonalRepresentative J u| * 2 :=
            mul_le_mul_of_nonneg_left hchar (abs_nonneg _)
          _ ≤ (Jscale * M u) * 2 :=
            mul_le_mul_of_nonneg_right (hJrepresentative u) (by norm_num)
          _ = 2 * (Jscale * M u) := by ring
      _ = 2 * Jscale * ∫ u, M u ∂paperMeasure := by
        rw [integral_const_mul, integral_const_mul]
        ring
  have hrepresentativeIntegral :
      (∫ u,
          (J u : ℂ) * (charT4 (-β) u - 1)
          ∂paperMeasure) =
        ∫ u,
          (offDiagonalRepresentative J u : ℂ) *
            (charT4 (-β) u - 1)
          ∂paperMeasure := by
    apply integral_congr_ae
    filter_upwards [paperMeasure.ae_ne 0] with u hu
    rw [offDiagonalRepresentative_eq J hu]
  change
    ‖∫ u, (J u : ℂ) * (charT4 (-β) u - 1)
        ∂paperMeasure‖ ≤ _
  rw [hrepresentativeIntegral]
  simpa only [ctx, Jscale, M] using hphase

/-- **One-half quantitative terminal estimate.**  The genuine signed
terminal gap integral remains unscaled on the left.  On the right, the
predecessor edge is charged once through its stored certificate, while the
raw terminal internal edges are charged once through normalized
Proposition 4.1.  The outgoing Green edge is not charged here: its exact
Fourier multiplier is retained by the four-endpoint routing step. -/
theorem fullPairingHalfTerminalEstimate
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (x z : T4) (hxz : x ≠ z)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (supportConstant primitiveConstant : ℝ)
    (hprimitive : 0 ≤ primitiveConstant)
    (hlam : 0 ≤ lam)
    (hprop :
      ∀ H :
          Fin
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2 - 1) →
            T4 → ℝ,
        IsAdmissiblePrimitiveInput
            (residualBlockOrder
              data.geometry.terminalData.terminal.2) H →
          MemEClassT4
              (primitiveKernelDiff ρ lam ε
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff ρ lam ε
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                H) ∧
            PrimitiveKernelBounds ρ lam ε
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
              H supportConstant primitiveConstant)
    (β : Z4) :
    ‖∫ u : T4,
        (((lamEps lam ε ^
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2) *
            (∫ v :
                Fin
                    (2 * residualBlockOrder
                      data.geometry.terminalData.terminal.2 - 2) →
                  T4,
              data.geometry.terminalGroupedPrimitiveCore x
                (primitiveAssemble
                  (residualBlockOrder
                    data.geometry.terminalData.terminal.2)
                  (data.geometry.trace.stopPrefix.headContext
                    data.geometry.terminalData.terminal []
                    data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                  z (z - u) v)
              ∂Measure.pi fun _ => paperMeasure)) : ℝ) : ℂ) *
          (charT4 (-β) u - 1)
        ∂paperMeasure‖ ≤
      (budget.stopScale
          (r324WithinHalfPredecessorSlot
            data.geometry.trace.stopPrefix.state
            data.geometry.terminalData.terminal) *
        invSqKer (x - z)) *
        (2 *
          r324WithinHalfInternalEdgeScaleProduct
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton)
            budget.stopScale *
          ∫ u,
            primitiveKernelMajorant
              primitiveConstant lam ε supportConstant
              (residualBlockOrder
                data.geometry.terminalData.terminal.2) u
            ∂paperMeasure) := by
  let pred :=
    r324WithinHalfPredecessorSlot
      data.geometry.trace.stopPrefix.state
      data.geometry.terminalData.terminal
  let Jscale :=
    r324WithinHalfInternalEdgeScaleProduct
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton)
      budget.stopScale
  let I :=
    ∫ u,
      primitiveKernelMajorant primitiveConstant lam ε supportConstant
        (residualBlockOrder
          data.geometry.terminalData.terminal.2) u
      ∂paperMeasure
  have hint :
      ∀ (w : T4)
        (κB :
          {κB : PartialPairing
              (Fin
                (2 * residualBlockOrder
                  data.geometry.terminalData.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)}),
        Integrable
          (fun v :
              Fin
                  (2 * residualBlockOrder
                    data.geometry.terminalData.terminal.2 - 2) →
                T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2)
              κB.1
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).internalEdges
              (primitiveAssemble
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                z w v))
          (Measure.pi fun _ => paperMeasure) := by
    intro w κB
    exact data.integrable_terminalClosedIntegrand_section
      hε hε1 κB z w
  have hphase :
      ‖∫ u,
          (primitiveKernelDiff ρ lam ε
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).internalEdges u :
            ℂ) *
            (charT4 (-β) u - 1)
          ∂paperMeasure‖ ≤
        2 * Jscale * I := by
    simpa only [Jscale, I] using
      data.norm_integral_terminalPrimitiveKernelDiff_mul_negCharacterSubOne_le_scaled
        hε supportConstant primitiveConstant hprimitive hlam hprop β
  have hpred :
      |data.geometry.trace.stopPrefix.state.edges pred (x - z)| ≤
        budget.stopScale pred * invSqKer (x - z) := by
    exact data.certificate.bound pred (x - z)
      (sub_ne_zero.mpr hxz)
  have hphaseNonneg : 0 ≤ 2 * Jscale * I := by
    have hJscale :
        0 < Jscale :=
      data.certificate.internalEdgeScaleProduct_pos
    have hInonneg : 0 ≤ I := by
      apply integral_nonneg
      intro u
      exact primitiveKernelMajorant_nonneg hprimitive hlam
    positivity
  rw [
    data.integral_lamEps_pow_terminalGroupedPrimitiveCore_gap_mul_negCharacterSubOne_eq
      x z hint β,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact
    (mul_le_mul_of_nonneg_left hphase (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hpred hphaseNonneg)

end R324FullPairingBudgetTerminalAdapter

end R324WithinHalfResidualPrefix

end

end Anderson4D
