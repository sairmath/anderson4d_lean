import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalStep4HeadBound
import Anderson4D.DetParametrix.Paper42_Moment.R324AlternatingDriver

/-!
# Certificate-scaled ordinary primitive defect

The internal kernels present at a stopped within-half block are not
normalized primitive inputs.  Their individual inverse-square constants are
stored in `R324WithinHalfEdgeCertificate`.  This module extracts the generic
form of the already proved incoming-exceptional estimate: normalize through
that certificate, apply Proposition 4.1, and retain the product of the actual
internal scales exactly once.

The norm is taken only after the complete signed primitive sum has been
integrated.  The value at the identity is discarded using atomlessness of
paper Haar measure.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- Generic certificate-scaled form of the ordinary-`J` Step-4 loss.  This
is the reusable local estimate for both incoming and outgoing shortcut
terminals. -/
theorem norm_incomingExceptionalPrimitiveDefect_le_scaled_of_certificate
    {ρ : SmoothCutoff} {C lam ε supportConstant : ℝ}
    {m : ℕ} {κ : PartialPairing (Fin m)}
    (ctx : R324WithinHalfStepContext κ)
    (scale : Fin (m + 1) → ℝ)
    (certificate : R324WithinHalfEdgeCertificate ctx.state scale)
    (hε : 0 < ε) (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hprop :
      ∀ (H :
          Fin (2 * residualBlockOrder ctx.step.2 - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput
            (residualBlockOrder ctx.step.2) H →
          MemEClassT4
              (primitiveKernelDiff ρ lam ε
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff ρ lam ε
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder H) ∧
            PrimitiveKernelBounds ρ lam ε
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder H supportConstant C)
    (k : Z4) :
    ‖incomingExceptionalPrimitiveDefect ρ lam ε
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder ctx.internalEdges k‖ ≤
      2 * r324WithinHalfInternalEdgeScaleProduct ctx scale *
        ∫ u : T4,
          primitiveKernelMajorant C lam ε supportConstant
            (residualBlockOrder ctx.step.2) u
          ∂paperMeasure := by
  let J : T4 → ℝ :=
    primitiveKernelDiff ρ lam ε
      (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges
  let Jscale : ℝ :=
    r324WithinHalfInternalEdgeScaleProduct ctx scale
  let M : T4 → ℝ :=
    primitiveKernelMajorant C lam ε supportConstant
      (residualBlockOrder ctx.step.2)
  letI : NullSingletonClass paperMeasure :=
    ⟨paperMeasure_singleton⟩
  have hJscale : 0 < Jscale :=
    certificate.internalEdgeScaleProduct_pos
  have hJoff : ∀ u, u ≠ 0 → |J u| ≤ Jscale * M u := by
    intro u hu
    dsimp only [J, Jscale, M]
    simpa [R324WithinHalfStepContext.internalEdges,
      r324WithinHalfInternalEdgeScaleProduct] using
      primitiveKernelDiff_le_prod_edgeScales_mul_majorant_offDiagonal
        ρ ctx.one_le_blockOrder ctx.internalEdges
        (fun j => scale (ctx.internalSlot j))
        (fun j => certificate.scale_pos (ctx.internalSlot j))
        (fun j => certificate.memE (ctx.internalSlot j))
        (fun j => certificate.bound (ctx.internalSlot j))
        hprop u hu
  have hMnonneg : ∀ u, 0 ≤ M u := by
    intro u
    exact primitiveKernelMajorant_nonneg hC hlam
  have hrepresentative :
      ∀ u, |offDiagonalRepresentative J u| ≤ Jscale * M u := by
    intro u
    by_cases hu : u = 0
    · subst u
      rw [offDiagonalRepresentative_zero, abs_zero]
      exact mul_nonneg hJscale.le (hMnonneg 0)
    · rw [offDiagonalRepresentative_eq J hu]
      exact hJoff u hu
  have hmajor : Integrable M paperMeasure :=
    integrable_primitiveKernelMajorant
      C lam ε supportConstant (residualBlockOrder ctx.step.2) hε
  have hphase :
      ‖∫ u : T4,
          (offDiagonalRepresentative J u : ℂ) *
            (charT4 (-k) u - 1)
          ∂paperMeasure‖ ≤
        2 * Jscale * ∫ u : T4, M u ∂paperMeasure := by
    have hscaled :
        Integrable (fun u : T4 => 2 * (Jscale * M u)) paperMeasure :=
      (hmajor.const_mul Jscale).const_mul 2
    calc
      ‖∫ u : T4,
          (offDiagonalRepresentative J u : ℂ) *
            (charT4 (-k) u - 1)
          ∂paperMeasure‖ ≤
          ∫ u : T4,
            ‖(offDiagonalRepresentative J u : ℂ) *
              (charT4 (-k) u - 1)‖
            ∂paperMeasure :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ u : T4, 2 * (Jscale * M u) ∂paperMeasure := by
        refine integral_mono_of_nonneg
          (.of_forall fun u => norm_nonneg _) hscaled
          (.of_forall fun u => ?_)
        dsimp only
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hchar : ‖charT4 (-k) u - 1‖ ≤ 2 := by
          calc
            ‖charT4 (-k) u - 1‖ ≤
                ‖charT4 (-k) u‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by rw [norm_charT4]; norm_num
        calc
          |offDiagonalRepresentative J u| *
                ‖charT4 (-k) u - 1‖ ≤
              |offDiagonalRepresentative J u| * 2 :=
            mul_le_mul_of_nonneg_left hchar (abs_nonneg _)
          _ ≤ (Jscale * M u) * 2 :=
            mul_le_mul_of_nonneg_right (hrepresentative u) (by norm_num)
          _ = 2 * (Jscale * M u) := by ring
      _ = 2 * Jscale * ∫ u : T4, M u ∂paperMeasure := by
        rw [integral_const_mul, integral_const_mul]
        ring
  have hrepresentativeIntegral :
      (∫ u : T4,
          (J u : ℂ) * (charT4 (-k) u - 1)
          ∂paperMeasure) =
        ∫ u : T4,
          (offDiagonalRepresentative J u : ℂ) *
            (charT4 (-k) u - 1)
          ∂paperMeasure := by
    apply integral_congr_ae
    filter_upwards [paperMeasure.ae_ne (0 : T4)] with u hu
    rw [offDiagonalRepresentative_eq J hu]
  unfold incomingExceptionalPrimitiveDefect
  change
    ‖∫ u : T4,
        (J u : ℂ) * (charT4 (-k) u - 1)
        ∂paperMeasure‖ ≤ _
  rw [hrepresentativeIntegral]
  simpa only [Jscale, M] using hphase

/-- Certificate-scaled form of the complete incoming endpoint head factor.
The Fourier multiplier is kept exact until the primitive defect has been
formed; its norm is then bounded by one. -/
theorem R324WithinHalfResidualPrefix.norm_incomingExceptionalHeadCollapseFactor_le_scaled
    {ρ : SmoothCutoff} {C lam ε supportConstant : ℝ}
    {m : ℕ} {κ : PartialPairing (Fin m)}
    (res : R324WithinHalfResidualPrefix ρ lam ε κ)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (scale : Fin (m + 1) → ℝ)
    (certificate : R324WithinHalfEdgeCertificate res.state scale)
    (hε : 0 < ε) (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hprop :
      ∀ (H : Fin (2 * residualBlockOrder head.2 - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput (residualBlockOrder head.2) H →
          MemEClassT4
              (primitiveKernelDiff ρ lam ε
                (residualBlockOrder head.2)
                (res.headContext head tail hremaining).one_le_blockOrder H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff ρ lam ε
                (residualBlockOrder head.2)
                (res.headContext head tail hremaining).one_le_blockOrder H) ∧
            PrimitiveKernelBounds ρ lam ε
              (residualBlockOrder head.2)
              (res.headContext head tail hremaining).one_le_blockOrder
              H supportConstant C)
    (k : Z4) :
    ‖res.incomingExceptionalHeadCollapseFactor
        head tail hremaining k‖ ≤
      2 * r324WithinHalfInternalEdgeScaleProduct
          (res.headContext head tail hremaining) scale *
        ∫ u : T4,
          primitiveKernelMajorant C lam ε supportConstant
            (residualBlockOrder head.2) u
          ∂paperMeasure := by
  have hdefect :=
    norm_incomingExceptionalPrimitiveDefect_le_scaled_of_certificate
      (res.headContext head tail hremaining) scale certificate
      hε hC hlam hprop k
  have hdecay :
      ‖((paperSecondOrderModeDecay k : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (paperSecondOrderModeDecay_nonneg k)]
    unfold paperSecondOrderModeDecay
    have hmode : 0 ≤ paperModeNormSq k := by
      unfold paperModeNormSq
      positivity
    exact (inv_le_one₀ (by linarith)).2 (by linarith)
  unfold incomingExceptionalHeadCollapseFactor
  rw [norm_mul]
  calc
    ‖((paperSecondOrderModeDecay k : ℝ) : ℂ)‖ *
          ‖incomingExceptionalPrimitiveDefect ρ lam ε
            (residualBlockOrder head.2)
            (res.headContext head tail hremaining).one_le_blockOrder
            (res.headContext head tail hremaining).internalEdges k‖ ≤
        1 *
          (2 * r324WithinHalfInternalEdgeScaleProduct
              (res.headContext head tail hremaining) scale *
            ∫ u : T4,
              primitiveKernelMajorant C lam ε supportConstant
                (residualBlockOrder head.2) u
              ∂paperMeasure) := by
      exact mul_le_mul hdecay hdefect (norm_nonneg _)
        (by positivity)
    _ = _ := by ring

end

end Anderson4D
