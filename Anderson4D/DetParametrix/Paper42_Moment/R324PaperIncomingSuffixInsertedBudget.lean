import Anderson4D.DetParametrix.Paper42_Moment.R324FullFullStep1NormalizedClosure

/-!
# The inserted Step-1 budget for later incoming exceptional heads

After the first paired endpoint has supplied the fourth-order external
decay, every later exceptional head in the literal suffix carries exactly
`paperSecondOrderModeDecay k * primitiveDefect k`.  Paper Section 4.2,
Step 1 spends that multiplier on the quadratic cosine defect and therefore
uses the inserted majorant (4.4), with no further `eps^-2` endpoint loss.

The terminal specialization of this estimate already appears as
`paperDecay_mul_norm_integral_terminalPrimitiveKernelDiff_le_scaled_inserted`.
This file exposes precisely the same argument for an arbitrary certified
literal head, so the alternating suffix can consume it one block at a time.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}

/-- Certificate-scaled form of the paper's inserted Step-1 cosine charge at
an arbitrary literal within-half head.  The modulus is taken only after the
primitive sum has been integrated and its sine part has vanished by
`MemEClassT4` symmetry. -/
theorem paperDecay_mul_norm_incomingExceptionalPrimitiveDefect_le_scaled_inserted
    (ctx : R324WithinHalfStepContext pairing)
    (scale : Fin (m + 1) -> Real)
    (certificate : R324WithinHalfEdgeCertificate ctx.state scale)
    (hε : 0 < eps) (supportConstant primitiveConstant : Real)
    (hprimitive : 0 <= primitiveConstant) (hlam : 0 <= lam)
    (hprop :
      forall H :
          Fin (2 * residualBlockOrder ctx.step.2 - 1) -> T4 -> Real,
        IsAdmissiblePrimitiveInput
            (residualBlockOrder ctx.step.2) H ->
          MemEClassT4
              (primitiveKernelDiff rho lam eps
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder H) /\
            MemEClassT4
              (primitiveKernelInsertedDiff rho lam eps
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder H) /\
            PrimitiveKernelBounds rho lam eps
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder H supportConstant primitiveConstant)
    (k : Z4) :
    paperSecondOrderModeDecay k *
        ‖incomingExceptionalPrimitiveDefect rho lam eps
          (residualBlockOrder ctx.step.2) ctx.one_le_blockOrder
          ctx.internalEdges k‖ <=
      r324WithinHalfInternalEdgeScaleProduct ctx scale *
        ((1 / 2 : Real) *
          (max 1 (supportConstant ^ 2) *
            ∫ z : T4,
              primitiveInsertedMajorant primitiveConstant lam eps
                supportConstant (residualBlockOrder ctx.step.2) z
              ∂paperMeasure)) := by
  let J : T4 -> Real :=
    primitiveKernelDiff rho lam eps
      (residualBlockOrder ctx.step.2) ctx.one_le_blockOrder
      ctx.internalEdges
  let Jscale : Real :=
    r324WithinHalfInternalEdgeScaleProduct ctx scale
  let M : T4 -> Real :=
    primitiveKernelMajorant primitiveConstant lam eps supportConstant
      (residualBlockOrder ctx.step.2)
  let Mscaled : T4 -> Real := fun u => Jscale * M u
  have hJscale : 0 < Jscale :=
    certificate.internalEdgeScaleProduct_pos
  have hMnonneg : forall u, 0 <= M u := by
    intro u
    exact primitiveKernelMajorant_nonneg hprimitive hlam
  have hM : Integrable M paperMeasure :=
    integrable_primitiveKernelMajorant primitiveConstant lam eps
      supportConstant (residualBlockOrder ctx.step.2) hε
  have hJoff : forall u, u ≠ 0 -> |J u| <= Jscale * M u := by
    intro u hu
    dsimp only [J, Jscale, M]
    simpa [R324WithinHalfStepContext.internalEdges,
      r324WithinHalfInternalEdgeScaleProduct] using
      primitiveKernelDiff_le_prod_edgeScales_mul_majorant_offDiagonal
        rho ctx.one_le_blockOrder ctx.internalEdges
        (fun j => scale (ctx.internalSlot j))
        (fun j => certificate.scale_pos (ctx.internalSlot j))
        (fun j => certificate.memE (ctx.internalSlot j))
        (fun j => certificate.bound (ctx.internalSlot j))
        hprop u hu
  have hrep :
      forall u, |offDiagonalRepresentative J u| <= Mscaled u := by
    intro u
    by_cases hu : u = 0
    · subst u
      rw [offDiagonalRepresentative_zero, abs_zero]
      exact mul_nonneg hJscale.le (hMnonneg 0)
    · rw [offDiagonalRepresentative_eq J hu]
      exact hJoff u hu
  have hweighted :
      Integrable (fun u => torusDistSq u * Mscaled u) paperMeasure := by
    have hscaled : Integrable Mscaled paperMeasure := hM.const_mul Jscale
    exact integrable_torusDistSq_mul_of_integrable hscaled
  have hcosBound :
      ‖∫ u : T4,
          ((offDiagonalRepresentative J u *
            (r324CharacterCos k u - 1) : Real) : Complex)
          ∂paperMeasure‖ <=
        ((1 / 2 : Real) * paperModeNormSq k) *
          ∫ u : T4, torusDistSq u * Mscaled u ∂paperMeasure :=
    norm_integral_mul_r324CharacterCos_sub_one_le_of_abs_le
      k hrep hweighted
  have hJmeas : Measurable J := by
    dsimp only [J]
    exact measurable_primitiveKernelDiff rho lam eps
      (residualBlockOrder ctx.step.2) ctx.one_le_blockOrder
      ctx.internalEdges
      (fun j => certificate.measurable (ctx.internalSlot j))
  letI : NullSingletonClass paperMeasure :=
    ⟨paperMeasure_singleton⟩
  have hJint : Integrable J paperMeasure := by
    refine (hM.const_mul Jscale).mono hJmeas.aestronglyMeasurable ?_
    filter_upwards [paperMeasure.ae_ne (0 : T4)] with u hu
    simpa only [Mscaled, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hJscale.le (hMnonneg u))] using hJoff u hu
  have hcos :
      Integrable (fun u => J u * (r324CharacterCos k u - 1))
        paperMeasure := by
    have hweight : Measurable fun u : T4 => r324CharacterCos k u - 1 :=
      (Complex.measurable_re.comp
        (continuous_charT4 k).measurable).sub measurable_const
    refine hJint.mul_bdd (c := 2) hweight.aestronglyMeasurable
      (.of_forall fun u => ?_)
    simpa only [Real.norm_eq_abs] using
      abs_r324CharacterCos_sub_one_le_two k u
  have hsin :
      Integrable (fun u => J u * r324CharacterSin (-k) u)
        paperMeasure := by
    have hweight : Measurable (r324CharacterSin (-k)) :=
      Complex.measurable_im.comp (continuous_charT4 (-k)).measurable
    refine hJint.mul_bdd (c := 1) hweight.aestronglyMeasurable
      (.of_forall fun u => ?_)
    unfold r324CharacterSin
    simpa only [Real.norm_eq_abs, norm_charT4] using
      Complex.abs_im_le_norm (charT4 (-k) u)
  have hphaseCos :
      (∫ u : T4, (J u : Complex) * (charT4 (-k) u - 1)
          ∂paperMeasure) =
        ∫ u : T4,
          ((J u * (r324CharacterCos k u - 1) : Real) : Complex)
          ∂paperMeasure :=
    integral_terminalPrimitiveKernelDiff_mul_negCharacterSubOne_eq_cos
      rho lam eps (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges
      (fun j => certificate.memE (ctx.internalSlot j)) k hcos hsin
  have hcosRepresentative :
      (∫ u : T4,
          ((J u * (r324CharacterCos k u - 1) : Real) : Complex)
          ∂paperMeasure) =
        ∫ u : T4,
          ((offDiagonalRepresentative J u *
            (r324CharacterCos k u - 1) : Real) : Complex)
          ∂paperMeasure := by
    apply integral_congr_ae
    filter_upwards [offDiagonalRepresentative_ae_eq J] with u hu
    rw [hu]
  have hMscaledIntegral :
      (∫ u : T4, torusDistSq u * Mscaled u ∂paperMeasure) =
        Jscale * ∫ u : T4, torusDistSq u * M u ∂paperMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    simp only [Mscaled]
    ring
  have hkey :
      ‖∫ u : T4, (J u : Complex) * (charT4 (-k) u - 1)
          ∂paperMeasure‖ <=
        ((1 / 2 : Real) * paperModeNormSq k) *
          (Jscale *
            ∫ u : T4, torusDistSq u * M u ∂paperMeasure) := by
    calc
      _ = ‖∫ u : T4,
          ((offDiagonalRepresentative J u *
            (r324CharacterCos k u - 1) : Real) : Complex)
          ∂paperMeasure‖ := by rw [hphaseCos, hcosRepresentative]
      _ <= ((1 / 2 : Real) * paperModeNormSq k) *
          ∫ u : T4, torusDistSq u * Mscaled u ∂paperMeasure := hcosBound
      _ = _ := by rw [hMscaledIntegral]
  have hdistNonneg :
      0 <= ∫ u : T4, torusDistSq u * M u ∂paperMeasure :=
    integral_nonneg fun u =>
      mul_nonneg (torusDistSq_nonneg u) (hMnonneg u)
  have hbridge :=
    integral_torusDistSq_mul_primitiveKernelMajorant_le_max_one_sq_mul_integral_inserted
      primitiveConstant lam eps supportConstant
      (residualBlockOrder ctx.step.2) hε
  have hmode := r324Step1_modeNormSq_mul_decay_le_one k
  unfold incomingExceptionalPrimitiveDefect
  change paperSecondOrderModeDecay k *
      ‖∫ u : T4, (J u : Complex) * (charT4 (-k) u - 1)
        ∂paperMeasure‖ <= _
  calc
    _ <= paperSecondOrderModeDecay k *
        (((1 / 2 : Real) * paperModeNormSq k) *
          (Jscale *
            ∫ u : T4, torusDistSq u * M u ∂paperMeasure)) :=
      mul_le_mul_of_nonneg_left hkey (paperSecondOrderModeDecay_nonneg k)
    _ = (1 / 2 : Real) *
        ((paperModeNormSq k * paperSecondOrderModeDecay k) *
          (Jscale *
            ∫ u : T4, torusDistSq u * M u ∂paperMeasure)) := by ring
    _ <= (1 / 2 : Real) *
        (1 * (Jscale *
          ∫ u : T4, torusDistSq u * M u ∂paperMeasure)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hmode
          (mul_nonneg hJscale.le hdistNonneg)) (by norm_num)
    _ = Jscale *
        ((1 / 2 : Real) *
          ∫ u : T4, torusDistSq u * M u ∂paperMeasure) := by ring
    _ <= Jscale *
        ((1 / 2 : Real) *
          (max 1 (supportConstant ^ 2) *
            ∫ z : T4,
              primitiveInsertedMajorant primitiveConstant lam eps
                supportConstant (residualBlockOrder ctx.step.2) z
              ∂paperMeasure)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbridge (by norm_num)) hJscale.le

/-- The sharp later-stop estimate in the exact form used by the alternating
driver multiplier. -/
theorem norm_incomingExceptionalHeadCollapseFactor_le_scaled_inserted
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (scale : Fin (m + 1) -> Real)
    (certificate : R324WithinHalfEdgeCertificate res.state scale)
    (hε : 0 < eps) (supportConstant primitiveConstant : Real)
    (hprimitive : 0 <= primitiveConstant) (hlam : 0 <= lam)
    (hprop :
      forall H : Fin (2 * residualBlockOrder head.2 - 1) -> T4 -> Real,
        IsAdmissiblePrimitiveInput (residualBlockOrder head.2) H ->
          MemEClassT4
              (primitiveKernelDiff rho lam eps
                (residualBlockOrder head.2)
                (res.headContext head tail hremaining).one_le_blockOrder H) /\
            MemEClassT4
              (primitiveKernelInsertedDiff rho lam eps
                (residualBlockOrder head.2)
                (res.headContext head tail hremaining).one_le_blockOrder H) /\
            PrimitiveKernelBounds rho lam eps
              (residualBlockOrder head.2)
              (res.headContext head tail hremaining).one_le_blockOrder
              H supportConstant primitiveConstant)
    (k : Z4) :
    ‖res.incomingExceptionalHeadCollapseFactor
        head tail hremaining k‖ <=
      r324WithinHalfInternalEdgeScaleProduct
          (res.headContext head tail hremaining) scale *
        ((1 / 2 : Real) *
          (max 1 (supportConstant ^ 2) *
            ∫ z : T4,
              primitiveInsertedMajorant primitiveConstant lam eps
                supportConstant (residualBlockOrder head.2) z
              ∂paperMeasure)) := by
  have h :=
    paperDecay_mul_norm_incomingExceptionalPrimitiveDefect_le_scaled_inserted
      (res.headContext head tail hremaining) scale certificate hε
      supportConstant primitiveConstant hprimitive hlam hprop k
  unfold incomingExceptionalHeadCollapseFactor
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperSecondOrderModeDecay_nonneg k)]
  exact h

end R324WithinHalfResidualPrefix

end

end Anderson4D
