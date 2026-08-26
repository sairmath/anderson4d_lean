import Anderson4D.DetParametrix.Paper42_Moment.R324ResidualCompletePrimitiveHead
import Anderson4D.DetParametrix.Paper42_Moment.R324NestedCrossIterationClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324ProperInsertedConvolution

/-!
# Complete primitive heads in the nested R-324 iteration

Paper Step 2(f) keeps the complete primitive-pairing sum grouped until the
within-half removals are finished.  This file supplies the corresponding
one-head object for Step 3, analogous to the single-pairing
single-pairing `normalizedHeadDensity` / `properHeadIntegral` interface.

No triangle inequality over primitive pairings occurs here.  The complete
moving-gap term is first compared with the single complete inserted kernel,
and only that kernel is bounded by Proposition 4.1.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324NestedCrossStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- The normalized complete primitive head.  The whole primitive-pairing
sum is retained inside `completeCrossGapPrimitiveIntegrand`. -/
def completeNormalizedHeadDensity
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (t : Fin (2 * ctx.order) → T4) : ℝ :=
  lamEps lam ε ^ (2 * ctx.order) *
    ctx.completeCrossGapPrimitiveIntegrand
      ρ ε ctx.normalizedInput t

theorem completeCrossGapPrimitiveIntegrand_nonneg
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (hG : ∀ j z, 0 ≤ G j z)
    (t : Fin (2 * ctx.order) → T4) :
    0 ≤ ctx.completeCrossGapPrimitiveIntegrand ρ ε G t := by
  unfold completeCrossGapPrimitiveIntegrand
  exact Finset.sum_nonneg fun κ hκ =>
    mul_nonneg (torusDistSq_nonneg _)
      (primitiveIntegrand_nonneg
        ρ ε ctx.order ctx.one_le_order G hG κ t)

theorem completeNormalizedHeadDensity_nonneg
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (t : Fin (2 * ctx.order) → T4) :
    0 ≤ ctx.completeNormalizedHeadDensity ρ lam ε t := by
  unfold completeNormalizedHeadDensity
  exact mul_nonneg ((even_two_mul ctx.order).pow_nonneg _)
    (ctx.completeCrossGapPrimitiveIntegrand_nonneg
      ρ ε ctx.normalizedInput ctx.normalizedInput_nonneg t)

theorem completeNormalizedHeadDensity_measurable
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ) :
    Measurable (ctx.completeNormalizedHeadDensity ρ lam ε) := by
  unfold completeNormalizedHeadDensity completeCrossGapPrimitiveIntegrand
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro κ hκ
  apply Measurable.mul
  · exact measurable_torusDistSq.comp
      ((measurable_pi_apply ctx.leftGapIndex).sub
        (measurable_pi_apply ctx.rightGapIndex))
  · exact measurable_primitiveIntegrand
      ρ ε ctx.order ctx.one_le_order ctx.normalizedInput
      ctx.normalizedInput_measurable κ

/-- Translation invariance of a complete primitive covariance product. -/
private theorem primitiveCovarianceProduct_add_const_complete
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin (2 * ctx.order)))
    (t : Fin (2 * ctx.order) → T4) (a : T4) :
    primitiveCovarianceProduct ρ ε ctx.order κ
        (fun i => t i + a) =
      primitiveCovarianceProduct ρ ε ctx.order κ t := by
  unfold primitiveCovarianceProduct
  apply Finset.prod_congr rfl
  intro i hi
  rw [add_sub_add_right_eq_sub]

/-- The complete moving-gap sum depends only on relative coordinates. -/
theorem completeCrossGapPrimitiveIntegrand_add_const
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (t : Fin (2 * ctx.order) → T4) (a : T4) :
    ctx.completeCrossGapPrimitiveIntegrand ρ ε G
        (fun i => t i + a) =
      ctx.completeCrossGapPrimitiveIntegrand ρ ε G t := by
  unfold completeCrossGapPrimitiveIntegrand primitiveIntegrand
  apply Finset.sum_congr rfl
  intro κ hκ
  rw [add_sub_add_right_eq_sub,
    ctx.primitiveChainProduct_add_const,
    ctx.primitiveCovarianceProduct_add_const_complete]

/-- Complete-sum counterpart of `crossGapPrimitiveTerm_eq_diff`. -/
theorem completeCrossGapPrimitiveTerm_eq_diff
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (z w : T4) :
    ctx.completeCrossGapPrimitiveTerm ρ lam ε G z w =
      ctx.completeCrossGapPrimitiveTerm ρ lam ε G (z - w) 0 := by
  unfold completeCrossGapPrimitiveTerm
  congr 1
  apply Finset.sum_congr rfl
  intro κ hκ
  let f : (Fin (2 * ctx.order - 2) → T4) → ℝ :=
    fun u =>
      torusDistSq
          (primitiveAssemble ctx.order ctx.one_le_order z w u
              ctx.leftGapIndex -
            primitiveAssemble ctx.order ctx.one_le_order z w u
              ctx.rightGapIndex) *
        primitiveIntegrand ρ ε ctx.order ctx.one_le_order G κ
          (primitiveAssemble ctx.order ctx.one_le_order z w u)
  have hp := ctx.measurePreserving_internalTranslation w
  calc
    (∫ u, f u ∂Measure.pi fun _ : Fin (2 * ctx.order - 2) =>
        paperMeasure) =
      ∫ u, f (ctx.internalTranslation w u)
        ∂Measure.pi fun _ : Fin (2 * ctx.order - 2) =>
          paperMeasure := by
      exact (hp.integral_comp' f).symm
    _ =
      ∫ u,
        torusDistSq
            (primitiveAssemble ctx.order ctx.one_le_order
                (z - w) 0 u ctx.leftGapIndex -
              primitiveAssemble ctx.order ctx.one_le_order
                (z - w) 0 u ctx.rightGapIndex) *
          primitiveIntegrand ρ ε ctx.order ctx.one_le_order G κ
            (primitiveAssemble
              ctx.order ctx.one_le_order (z - w) 0 u)
        ∂Measure.pi fun _ : Fin (2 * ctx.order - 2) =>
          paperMeasure := by
      apply integral_congr_ae
      filter_upwards with u
      dsimp only [f, internalTranslation]
      have hassemble :=
        primitiveAssemble_add_const
          ctx.order ctx.one_le_order (z - w) 0 w u
      have hend : z - w + w = z := by simp
      rw [hend, zero_add] at hassemble
      let t :=
        primitiveAssemble ctx.order ctx.one_le_order (z - w) 0 u
      have hcov :=
        ctx.primitiveCovarianceProduct_add_const_complete
          ρ ε κ t w
      have hchain := ctx.primitiveChainProduct_add_const G t w
      change
        torusDistSq
            (primitiveAssemble ctx.order ctx.one_le_order z w
                (fun i => u i + w) ctx.leftGapIndex -
              primitiveAssemble ctx.order ctx.one_le_order z w
                (fun i => u i + w) ctx.rightGapIndex) *
            primitiveIntegrand ρ ε ctx.order ctx.one_le_order G κ
              (primitiveAssemble ctx.order ctx.one_le_order z w
                (fun i => u i + w)) = _
      rw [hassemble]
      unfold primitiveIntegrand
      rw [add_sub_add_right_eq_sub, hchain, hcov]

end R324NestedCrossStepContext

namespace R324NestedCrossProperStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- The endpoint integral of a complete grouped primitive head with its
two flanking inverse-square connectors. -/
def completeProperHeadIntegral
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (left right : T4) : ℝ :=
  ∫ p : T4 × T4,
    invSqKer (left - p.1) *
      ctx.step.completeCrossGapPrimitiveTerm
        ρ lam ε ctx.step.normalizedInput
        (p.1 - p.2) 0 *
      invSqKer (p.2 - right)
    ∂(paperMeasure.prod paperMeasure)

theorem completeProperHeadIntegral_nonneg
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (left right : T4) :
    0 ≤ ctx.completeProperHeadIntegral ρ lam ε left right := by
  exact integral_nonneg fun p =>
    mul_nonneg
      (mul_nonneg (invSqKer_nonneg _)
        (mul_nonneg ((even_two_mul ctx.step.order).pow_nonneg _)
          (Finset.sum_nonneg fun κ hκ => integral_nonneg fun v =>
            mul_nonneg (torusDistSq_nonneg _)
              (primitiveIntegrand_nonneg
                ρ ε ctx.step.order ctx.step.one_le_order
                ctx.step.normalizedInput ctx.step.normalizedInput_nonneg
                κ _))))
      (invSqKer_nonneg _)

/-- Exact Fubini identity for a complete grouped head and its two
connectors. -/
theorem integral_completeNormalizedHeadDensity_mul_connector
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (post : ctx.step.PostCoordinate → T4)
    (hint :
      Integrable
        (fun t : Fin (2 * ctx.step.order) → T4 =>
          ctx.step.completeNormalizedHeadDensity ρ lam ε t *
            ctx.connector t post)
        (Measure.pi fun _ => paperMeasure)) :
    (∫ t : Fin (2 * ctx.step.order) → T4,
        ctx.step.completeNormalizedHeadDensity ρ lam ε t *
          ctx.connector t post
        ∂Measure.pi fun _ => paperMeasure) =
      ctx.completeProperHeadIntegral ρ lam ε
        (post ctx.nextLeftPostCoordinate)
        (post ctx.nextRightPostCoordinate) := by
  rw [integral_standardBlock_eq_integral_endpoints_internal
    ctx.step.order ctx.step.one_le_order _ hint]
  unfold completeProperHeadIntegral
  apply integral_congr_ae
  filter_upwards with p
  change
    (∫ u : Fin (2 * ctx.step.order - 2) → T4,
      ctx.step.completeNormalizedHeadDensity ρ lam ε
          (primitiveAssemble
            ctx.step.order ctx.step.one_le_order p.1 p.2 u) *
        ctx.connector
          (primitiveAssemble
            ctx.step.order ctx.step.one_le_order p.1 p.2 u) post
      ∂Measure.pi fun _ => paperMeasure) = _
  have hconnector :
      ∀ u : Fin (2 * ctx.step.order - 2) → T4,
        ctx.connector
            (primitiveAssemble
              ctx.step.order ctx.step.one_le_order p.1 p.2 u) post =
          invSqKer (post ctx.nextLeftPostCoordinate - p.1) *
            invSqKer (p.2 - post ctx.nextRightPostCoordinate) := by
    intro u
    unfold connector
    rw [primitiveAssemble_zero, primitiveAssemble_last]
  simp_rw [hconnector]
  rw [integral_mul_const]
  unfold R324NestedCrossStepContext.completeNormalizedHeadDensity
  rw [integral_const_mul]
  rw [← ctx.step.completeCrossGapPrimitiveTerm_eq_integral
    ρ lam hε hε1 ctx.step.normalizedInput
    ctx.step.normalizedInput_measurable
    ctx.step.normalizedInput_admissible p.1 p.2]
  rw [← ctx.step.completeCrossGapPrimitiveTerm_eq_diff
    ρ lam ε ctx.step.normalizedInput p.1 p.2]
  ring

end R324NestedCrossProperStepContext

/-- Complete-sum local analytic provider for every proper nested head. -/
structure R324CompleteProperHeadSharpProvider
    (ρ : SmoothCutoff) (lam ε D : ℝ)
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) : Prop where
  headIntegral_le :
    ∀ (ctx : R324NestedCrossProperStepContext κp κm π)
      (left right : T4),
      ctx.completeProperHeadIntegral ρ lam ε left right ≤
        (D * lam) ^ (2 * ctx.step.order)

/-- One fixed scalar cost can be absorbed into the even perturbative
power of every nonempty head. -/
private theorem r324CompleteProperHead_absorb
    {C lam K : ℝ} {n : ℕ}
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hn : 1 ≤ n) :
    (C * lam) ^ (2 * n) * K ≤
      ((C * max K 1) * lam) ^ (2 * n) := by
  have hK1 : (1 : ℝ) ≤ max K 1 := le_max_right _ _
  have hbase : 0 ≤ (C * lam) ^ (2 * n) := by positivity
  have hKt : K ≤ (max K 1) ^ (2 * n) := by
    calc
      K ≤ max K 1 := le_max_left _ _
      _ = (max K 1) ^ 1 := (pow_one _).symm
      _ ≤ (max K 1) ^ (2 * n) :=
        pow_le_pow_right₀ hK1 (by omega)
  calc
    (C * lam) ^ (2 * n) * K ≤
        (C * lam) ^ (2 * n) * (max K 1) ^ (2 * n) :=
      mul_le_mul_of_nonneg_left hKt hbase
    _ = ((C * max K 1) * lam) ^ (2 * n) := by
      rw [← mul_pow]
      congr 1
      ring

/-- Proposition 4.1 and the elementary eight-dimensional convolution
discharge the complete grouped proper-head provider. -/
theorem exists_r324CompleteProperHeadSharpProvider
    (ρ : SmoothCutoff) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (lam ε : ℝ) {m : ℕ}
        {κp κm : PartialPairing (Fin m)}
        (π : κp.singles ≃ κm.singles),
        0 < lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| → m ≤ truncOrder ε →
          R324CompleteProperHeadSharpProvider
            ρ lam ε D κp κm π := by
  obtain ⟨supportConstant, C, hsupport, hC, hprop⟩ :=
    proposition41_at_truncation ρ
  obtain ⟨K, hK, hconv⟩ :=
    exists_r324ProperInsertedConvolution_le hsupport
  refine ⟨C * max K 1, by positivity, ?_⟩
  intro lam ε m κp κm π hlam hε hε1 hlog hmtrunc
  refine ⟨?_⟩
  intro ctx left right
  set n : ℕ := ctx.step.order with hn
  have hn1 : 1 ≤ n := ctx.step.one_le_order
  have hntrunc : n ≤ truncOrder ε :=
    ctx.step.order_le_ambient.trans hmtrunc
  have hmiddle : ∀ z : T4,
      ctx.step.completeCrossGapPrimitiveTerm
          ρ lam ε ctx.step.normalizedInput z 0 ≤
        primitiveInsertedMajorant
          C lam ε supportConstant n z := by
    intro z
    have hkernel :=
      ctx.step.completeCrossGapPrimitiveTerm_le_primitiveKernelInserted
        ρ lam hε hε1 ctx.step.normalizedInput
        ctx.step.normalizedInput_measurable
        ctx.step.normalizedInput_admissible
        ctx.step.normalizedInput_nonneg z 0
    have hmajor :=
      (hprop lam ε n hn1 ctx.step.normalizedInput
        hlam hε hε1 hntrunc
        ctx.step.normalizedInput_admissible).2.2 z |>.2
    exact hkernel.trans ((le_abs_self _).trans hmajor)
  obtain ⟨hint, hbound⟩ :=
    hconv C lam ε n left right hC.le hlam.le hε hε1 hlog
  have hle :
      ctx.completeProperHeadIntegral ρ lam ε left right ≤
        ∫ p : T4 × T4,
          r324ProperInsertedConvolutionIntegrand
            C lam ε supportConstant n left right p
          ∂(paperMeasure.prod paperMeasure) := by
    unfold R324NestedCrossProperStepContext.completeProperHeadIntegral
    refine integral_mono_of_nonneg (.of_forall fun p => ?_) hint
      (.of_forall fun p => ?_)
    · exact mul_nonneg
        (mul_nonneg (invSqKer_nonneg _)
          (mul_nonneg ((even_two_mul n).pow_nonneg _)
            (Finset.sum_nonneg fun κ hκ => integral_nonneg fun v =>
              mul_nonneg (torusDistSq_nonneg _)
                (primitiveIntegrand_nonneg
                  ρ ε n hn1 ctx.step.normalizedInput
                  ctx.step.normalizedInput_nonneg κ _))))
        (invSqKer_nonneg _)
    · unfold r324ProperInsertedConvolutionIntegrand
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hmiddle _) (invSqKer_nonneg _))
        (invSqKer_nonneg _)
  calc
    ctx.completeProperHeadIntegral ρ lam ε left right ≤
        ∫ p : T4 × T4,
          r324ProperInsertedConvolutionIntegrand
            C lam ε supportConstant n left right p
          ∂(paperMeasure.prod paperMeasure) := hle
    _ = ∫ a, ∫ b,
          invSqKer (left - a) *
            primitiveInsertedMajorant
              C lam ε supportConstant n (a - b) *
            invSqKer (b - right)
          ∂paperMeasure ∂paperMeasure := by
      rw [integral_prod _ hint]
      rfl
    _ ≤ (C * lam) ^ (2 * n) * K := hbound
    _ ≤ ((C * max K 1) * lam) ^ (2 * n) :=
      r324CompleteProperHead_absorb hC.le hlam.le hn1

end

end Anderson4D
