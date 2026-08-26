import Anderson4D.DetParametrix.Paper42_Moment.R324CompleteNestedCrossBudgetIteration
import Anderson4D.DetParametrix.Paper42_Moment.R324InteriorLogBudgetProof
import Anderson4D.Parametrix.Identity

/-!
# The final complete nested-cross head

After all proper inner shells have been removed, paper Step 3 applies
Proposition 4.1 once to the complete outermost primitive block.  This file
proves the measure-theoretic bridge needed for that last application: the
complete normalized block is integrable, its full integral is the integral
of its two-endpoint kernel, and a radial endpoint bound costs exactly one
paper volume.
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

/-- Measurability of the complete normalized two-endpoint term. -/
theorem measurable_completeCrossGapPrimitiveTerm_normalized
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Measurable
      (fun p : T4 × T4 =>
        ctx.completeCrossGapPrimitiveTerm
          ρ lam ε ctx.normalizedInput p.1 p.2) := by
  let e := r324PrimitiveBlockTupleMeasurableEquiv
    ctx.order ctx.one_le_order
  have hraw :
      Measurable
        (fun q : (T4 × T4) ×
            (Fin (2 * ctx.order - 2) → T4) =>
          ctx.completeNormalizedHeadDensity ρ lam ε (e.symm q)) :=
    (ctx.completeNormalizedHeadDensity_measurable ρ lam ε).comp
      e.symm.measurable
  have hout :
      StronglyMeasurable
        (fun p : T4 × T4 =>
          ∫ u : Fin (2 * ctx.order - 2) → T4,
            ctx.completeNormalizedHeadDensity ρ lam ε
              (e.symm (p, u))
            ∂Measure.pi fun _ => paperMeasure) :=
    hraw.stronglyMeasurable.integral_prod_right'
  have heq :
      (fun p : T4 × T4 =>
        ∫ u : Fin (2 * ctx.order - 2) → T4,
          ctx.completeNormalizedHeadDensity ρ lam ε
            (e.symm (p, u))
          ∂Measure.pi fun _ => paperMeasure) =
        fun p : T4 × T4 =>
          ctx.completeCrossGapPrimitiveTerm
            ρ lam ε ctx.normalizedInput p.1 p.2 := by
    funext p
    dsimp only [e]
    simp_rw [r324PrimitiveBlockTupleMeasurableEquiv_symm_apply]
    unfold completeNormalizedHeadDensity
    rw [integral_const_mul]
    rw [← ctx.completeCrossGapPrimitiveTerm_eq_integral
      ρ lam hε hε1
      ctx.normalizedInput ctx.normalizedInput_measurable
      ctx.normalizedInput_admissible p.1 p.2]
  rw [← heq]
  exact hout.measurable

end R324NestedCrossStepContext

/-- An integrable radial kernel stays integrable on the two-endpoint paper
carrier after composition with `p ↦ p.1 - p.2`. -/
private theorem integrable_paperDifferenceKernel
    (J : T4 → ℝ) (hJ : Integrable J paperMeasure)
    (hJmeas : Measurable J) :
    Integrable (fun p : T4 × T4 => J (p.1 - p.2))
      (paperMeasure.prod paperMeasure) := by
  have hmeas : Measurable (fun p : T4 × T4 => J (p.1 - p.2)) :=
    hJmeas.comp (measurable_fst.sub measurable_snd)
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall fun x => by
      have hcomp :=
        ((measurePreserving_subLeftT4 x).integrable_comp
          hJ.aestronglyMeasurable).mpr hJ
      refine hcomp.congr (Filter.Eventually.of_forall fun y => ?_)
      rw [Function.comp_apply, subLeftT4MeasurableEquiv_apply]
  · have heq :
        (fun x : T4 => ∫ y : T4, ‖J (x - y)‖ ∂paperMeasure) =
          fun _ : T4 => ∫ z : T4, ‖J z‖ ∂paperMeasure := by
      funext x
      simpa only [subLeftT4MeasurableEquiv_apply] using
        (measurePreserving_subLeftT4 x).integral_comp'
          (fun z : T4 => ‖J z‖)
    rw [heq]
    exact integrable_const _

/-- Exact mass of a radial difference kernel on the endpoint pair. -/
private theorem integral_paperDifferenceKernel
    (J : T4 → ℝ) (hJ : Integrable J paperMeasure)
    (hJmeas : Measurable J) :
    (∫ p : T4 × T4, J (p.1 - p.2)
        ∂(paperMeasure.prod paperMeasure)) =
      (2 * Real.pi) ^ (dim : ℕ) *
        ∫ z : T4, J z ∂paperMeasure := by
  have hprod := integrable_paperDifferenceKernel J hJ hJmeas
  rw [integral_prod _ hprod]
  have heq :
      (fun x : T4 => ∫ y : T4, J (x - y) ∂paperMeasure) =
        fun _ : T4 => ∫ z : T4, J z ∂paperMeasure := by
    funext x
    simpa only [subLeftT4MeasurableEquiv_apply] using
      (measurePreserving_subLeftT4 x).integral_comp' J
  rw [heq, integral_const, measureReal_def, paperMeasure_univ,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

private theorem measurable_primitiveInsertedMajorant_local
    (C lam ε supportConstant : ℝ) (n : ℕ) :
    Measurable (primitiveInsertedMajorant C lam ε supportConstant n) := by
  unfold primitiveInsertedMajorant
  apply Measurable.const_mul
  apply Measurable.add
  · exact
      ((measurable_invSqKer.const_mul _).mul
        (measurable_primitiveSupportIndicator supportConstant ε))
  · exact
      ((measurable_torusDistSq.add_const _).inv.pow_const 2).const_mul _

namespace R324NestedCrossStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- Nonnegativity of the integrated complete head. -/
theorem completeCrossGapPrimitiveTerm_nonneg
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (hG : ∀ j z, 0 ≤ G j z) (z w : T4) :
    0 ≤ ctx.completeCrossGapPrimitiveTerm ρ lam ε G z w := by
  unfold completeCrossGapPrimitiveTerm
  exact mul_nonneg ((even_two_mul ctx.order).pow_nonneg _)
    (Finset.sum_nonneg fun κ hκ => integral_nonneg fun v =>
      mul_nonneg (torusDistSq_nonneg _)
        (primitiveIntegrand_nonneg
          ρ ε ctx.order ctx.one_le_order G hG κ _))

/-- A complete normalized block is integrable whenever its already-integrated
two-endpoint term is dominated by an integrable radial kernel. -/
theorem integrable_completeNormalizedHeadDensity_of_term_le
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (J : T4 → ℝ) (hJ : Integrable J paperMeasure)
    (hJmeas : Measurable J)
    (hle : ∀ z,
      ctx.completeCrossGapPrimitiveTerm
          ρ lam ε ctx.normalizedInput z 0 ≤ J z) :
    Integrable (ctx.completeNormalizedHeadDensity ρ lam ε)
      (Measure.pi fun _ : Fin (2 * ctx.order) => paperMeasure) := by
  let e := r324PrimitiveBlockTupleMeasurableEquiv
    ctx.order ctx.one_le_order
  let μ := Measure.pi fun _ : Fin (2 * ctx.order) => paperMeasure
  let μint := Measure.pi fun _ : Fin (2 * ctx.order - 2) => paperMeasure
  let ν := (paperMeasure.prod paperMeasure).prod μint
  let f :=
    fun q : (T4 × T4) × (Fin (2 * ctx.order - 2) → T4) =>
      ctx.completeNormalizedHeadDensity ρ lam ε (e.symm q)
  have hfmeas : Measurable f :=
    (ctx.completeNormalizedHeadDensity_measurable ρ lam ε).comp
      e.symm.measurable
  have hsections :
      ∀ᵐ p : T4 × T4 ∂(paperMeasure.prod paperMeasure),
        Integrable (fun u => f (p, u)) μint :=
    Filter.Eventually.of_forall fun p => by
      dsimp only [f, e]
      simp_rw [r324PrimitiveBlockTupleMeasurableEquiv_symm_apply]
      unfold completeNormalizedHeadDensity completeCrossGapPrimitiveIntegrand
      apply Integrable.const_mul
      apply integrable_finsetSum
      intro κ hκ
      exact ctx.integrable_completeCrossGapSummand_blockAssemble_of_mem
        ρ hε hε1 ctx.normalizedInput ctx.normalizedInput_measurable
        ctx.normalizedInput_admissible κ hκ p.1 p.2
  have htermMeas :
      Measurable (fun p : T4 × T4 =>
        ctx.completeCrossGapPrimitiveTerm
          ρ lam ε ctx.normalizedInput p.1 p.2) :=
    ctx.measurable_completeCrossGapPrimitiveTerm_normalized
      ρ lam hε hε1
  have hJprod := integrable_paperDifferenceKernel J hJ hJmeas
  have htermIntegrable :
      Integrable (fun p : T4 × T4 =>
        ctx.completeCrossGapPrimitiveTerm
          ρ lam ε ctx.normalizedInput p.1 p.2)
        (paperMeasure.prod paperMeasure) := by
    refine hJprod.mono' htermMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (ctx.completeCrossGapPrimitiveTerm_nonneg
        ρ lam ε ctx.normalizedInput ctx.normalizedInput_nonneg p.1 p.2)]
    rw [ctx.completeCrossGapPrimitiveTerm_eq_diff
      ρ lam ε ctx.normalizedInput p.1 p.2]
    exact hle (p.1 - p.2)
  have houterEq :
      (fun p : T4 × T4 => ∫ u, ‖f (p, u)‖ ∂μint) =
        fun p : T4 × T4 =>
          ctx.completeCrossGapPrimitiveTerm
            ρ lam ε ctx.normalizedInput p.1 p.2 := by
    funext p
    have hnonneg : ∀ u, 0 ≤ f (p, u) := fun u =>
      ctx.completeNormalizedHeadDensity_nonneg ρ lam ε (e.symm (p, u))
    calc
      (∫ u, ‖f (p, u)‖ ∂μint) = ∫ u, f (p, u) ∂μint := by
        apply integral_congr_ae
        filter_upwards with u
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg u)]
      _ = ctx.completeCrossGapPrimitiveTerm
            ρ lam ε ctx.normalizedInput p.1 p.2 := by
        dsimp only [f, e]
        simp_rw [r324PrimitiveBlockTupleMeasurableEquiv_symm_apply]
        unfold completeNormalizedHeadDensity
        rw [integral_const_mul]
        rw [← ctx.completeCrossGapPrimitiveTerm_eq_integral
          ρ lam hε hε1 ctx.normalizedInput
          ctx.normalizedInput_measurable ctx.normalizedInput_admissible
          p.1 p.2]
  have hfint : Integrable f ν := by
    apply (integrable_prod_iff hfmeas.aestronglyMeasurable).2
    refine ⟨hsections, ?_⟩
    rw [houterEq]
    exact htermIntegrable
  have hp := measurePreserving_r324PrimitiveBlockTupleMeasurableEquiv
    ctx.order ctx.one_le_order
  have hcomp : f ∘ e = ctx.completeNormalizedHeadDensity ρ lam ε := by
    funext t
    change ctx.completeNormalizedHeadDensity ρ lam ε (e.symm (e t)) = _
    rw [e.symm_apply_apply]
  have hback :=
    (hp.integrable_comp_emb e.measurableEmbedding (g := f)).mpr hfint
  rw [hcomp] at hback
  exact hback

/-- The final complete block is bounded by one radial endpoint majorant,
with only the translation-volume factor left outside. -/
theorem integral_completeNormalizedHeadDensity_le_of_term_le
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (J : T4 → ℝ) (hJ : Integrable J paperMeasure)
    (hJmeas : Measurable J)
    (hle : ∀ z,
      ctx.completeCrossGapPrimitiveTerm
          ρ lam ε ctx.normalizedInput z 0 ≤ J z) :
    (∫ t, ctx.completeNormalizedHeadDensity ρ lam ε t
        ∂Measure.pi fun _ : Fin (2 * ctx.order) => paperMeasure) ≤
      (2 * Real.pi) ^ (dim : ℕ) *
        ∫ z, J z ∂paperMeasure := by
  have hdensity :=
    ctx.integrable_completeNormalizedHeadDensity_of_term_le
      ρ lam hε hε1 J hJ hJmeas hle
  rw [integral_standardBlock_eq_integral_endpoints_internal
    ctx.order ctx.one_le_order _ hdensity]
  have htermIntegrable :
      Integrable (fun p : T4 × T4 =>
        ctx.completeCrossGapPrimitiveTerm
          ρ lam ε ctx.normalizedInput p.1 p.2)
        (paperMeasure.prod paperMeasure) := by
    have hJprod := integrable_paperDifferenceKernel J hJ hJmeas
    refine hJprod.mono'
      (ctx.measurable_completeCrossGapPrimitiveTerm_normalized
        ρ lam hε hε1).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (ctx.completeCrossGapPrimitiveTerm_nonneg
        ρ lam ε ctx.normalizedInput ctx.normalizedInput_nonneg p.1 p.2)]
    rw [ctx.completeCrossGapPrimitiveTerm_eq_diff
      ρ lam ε ctx.normalizedInput p.1 p.2]
    exact hle (p.1 - p.2)
  calc
    (∫ p : T4 × T4,
        ∫ u : Fin (2 * ctx.order - 2) → T4,
          ctx.completeNormalizedHeadDensity ρ lam ε
            (primitiveAssemble ctx.order ctx.one_le_order p.1 p.2 u)
          ∂Measure.pi fun _ => paperMeasure
        ∂(paperMeasure.prod paperMeasure)) =
      ∫ p : T4 × T4,
        ctx.completeCrossGapPrimitiveTerm
          ρ lam ε ctx.normalizedInput p.1 p.2
        ∂(paperMeasure.prod paperMeasure) := by
      apply integral_congr_ae
      filter_upwards with p
      unfold completeNormalizedHeadDensity
      rw [integral_const_mul]
      rw [← ctx.completeCrossGapPrimitiveTerm_eq_integral
        ρ lam hε hε1 ctx.normalizedInput
        ctx.normalizedInput_measurable ctx.normalizedInput_admissible
        p.1 p.2]
    _ ≤ ∫ p : T4 × T4, J (p.1 - p.2)
          ∂(paperMeasure.prod paperMeasure) := by
      exact integral_mono htermIntegrable
        (integrable_paperDifferenceKernel J hJ hJmeas)
        (fun p => by
          rw [ctx.completeCrossGapPrimitiveTerm_eq_diff
            ρ lam ε ctx.normalizedInput p.1 p.2]
          exact hle (p.1 - p.2))
    _ = (2 * Real.pi) ^ (dim : ℕ) *
          ∫ z, J z ∂paperMeasure :=
      integral_paperDifferenceKernel J hJ hJmeas

/-- Uniform final-head form of Proposition 4.1.  The constants are chosen
once from the cutoff and work for every literal final block in the ambient
truncation range. -/
theorem exists_completeTerminalHead_bound_at_truncation
    (ρ : SmoothCutoff) :
    ∃ supportConstant C : ℝ,
      0 < supportConstant ∧ 0 < C ∧
      ∀ {m : ℕ} (κp κm : PartialPairing (Fin m))
        (π : κp.singles ≃ κm.singles)
        (ctx : R324NestedCrossStepContext κp κm π)
        (lam ε : ℝ),
        0 < lam → 0 < ε → ε ≤ 1 →
        m ≤ truncOrder ε →
          (∫ t, ctx.completeNormalizedHeadDensity ρ lam ε t
              ∂Measure.pi fun _ : Fin (2 * ctx.order) => paperMeasure) ≤
            (2 * Real.pi) ^ (dim : ℕ) *
              ∫ z, primitiveInsertedMajorant
                C lam ε supportConstant ctx.order z
                ∂paperMeasure := by
  obtain ⟨supportConstant, C, hsupport, hC, hprop⟩ :=
    proposition41_at_truncation ρ
  refine ⟨supportConstant, C, hsupport, hC, ?_⟩
  intro m κp κm π ctx lam ε hlam hε hε1 hmtrunc
  have hntrunc : ctx.order ≤ truncOrder ε :=
    ctx.order_le_ambient.trans hmtrunc
  let J := primitiveInsertedMajorant
    C lam ε supportConstant ctx.order
  have hJint : Integrable J paperMeasure :=
    integrable_primitiveInsertedMajorant
      C lam ε supportConstant ctx.order hε
  have hJmeas : Measurable J :=
    measurable_primitiveInsertedMajorant_local
      C lam ε supportConstant ctx.order
  have hmiddle : ∀ z : T4,
      ctx.completeCrossGapPrimitiveTerm
          ρ lam ε ctx.normalizedInput z 0 ≤ J z := by
    intro z
    have hkernel :=
      ctx.completeCrossGapPrimitiveTerm_le_primitiveKernelInserted
        ρ lam hε hε1 ctx.normalizedInput
        ctx.normalizedInput_measurable
        ctx.normalizedInput_admissible
        ctx.normalizedInput_nonneg z 0
    have hmajor :=
      (hprop lam ε ctx.order ctx.one_le_order ctx.normalizedInput
        hlam hε hε1 hntrunc ctx.normalizedInput_admissible).2.2 z |>.2
    exact hkernel.trans ((le_abs_self _).trans hmajor)
  exact ctx.integral_completeNormalizedHeadDensity_le_of_term_le
    ρ lam hε hε1 J hJint hJmeas hmiddle

end R324NestedCrossStepContext

end

end Anderson4D
