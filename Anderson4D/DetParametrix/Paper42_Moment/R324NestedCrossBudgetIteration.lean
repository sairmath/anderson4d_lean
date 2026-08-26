import Anderson4D.DetParametrix.Paper42_Moment.R324InitialNestedContextFactorization
import Anderson4D.DetParametrix.Paper42_Moment.R324ProperInsertedConvolution

/-!
# Quantitative proper-prefix iteration for R-324 Step 3

The physical-to-canonical boundary produces a proof-relevant proper-prefix
factorization and stops at the block carrying the selected projected
covariance.  This file performs only the quantitative integration of the
proper heads preceding that block.

The sole analytic input is a transparent local provider for one proper
head: its exact normalized head/connector density is integrable for every
fixed next-suffix configuration, and its endpoint integral is bounded by
the named even perturbative power.  No final R-324 estimate, frequency
decay, or target-shaped reduction predicate appears here.

The output retains the actual four-endpoint terminal payload exposed by
the stop constructor.  In particular, the Step 4 routing machinery still
sees the original external endpoints and the complete marked/suffix
context.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- Transparent local analytic provider for one proper nested cross head.

The constant `D` is the already-absorbed one-head constant.  A later
consumer obtains such a provider from the sharp proper inserted
convolution estimate, absorbing its fixed scalar cost into `D`. -/
structure R324ProperHeadSharpProvider
    (ρ : SmoothCutoff) (lam ε D : ℝ)
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) : Prop where
  headIntegral_le :
    ∀ (ctx : R324NestedCrossProperStepContext κp κm π)
      (left right : T4),
      ctx.properHeadIntegral ρ lam ε left right ≤
        (D * lam) ^ (2 * ctx.step.order)

namespace R324NestedCrossStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- The exact normalized cross-gap term is measurable in its two free
endpoints.  This is derived from joint measurability of the literal head
density, not assumed as part of the sharp provider. -/
private theorem measurable_crossGapPrimitiveTerm_normalized
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ) :
    Measurable
      (fun p : T4 × T4 =>
        ctx.crossGapPrimitiveTerm
          ρ lam ε ctx.normalizedInput p.1 p.2) := by
  let e :=
    r324PrimitiveBlockTupleMeasurableEquiv
      ctx.order ctx.one_le_order
  have hraw :
      Measurable
        (fun q :
            (T4 × T4) ×
              (Fin (2 * ctx.order - 2) → T4) =>
          ctx.normalizedHeadDensity ρ lam ε
            (e.symm q)) :=
    (ctx.normalizedHeadDensity_measurable
      ρ lam ε).comp e.symm.measurable
  have hout :
      StronglyMeasurable
        (fun p : T4 × T4 =>
          ∫ u : Fin (2 * ctx.order - 2) → T4,
            ctx.normalizedHeadDensity ρ lam ε
              (e.symm (p, u))
            ∂Measure.pi fun _ => paperMeasure) :=
    hraw.stronglyMeasurable.integral_prod_right'
  have heq :
      (fun p : T4 × T4 =>
        ∫ u : Fin (2 * ctx.order - 2) → T4,
          ctx.normalizedHeadDensity ρ lam ε
            (e.symm (p, u))
          ∂Measure.pi fun _ => paperMeasure) =
        fun p : T4 × T4 =>
          ctx.crossGapPrimitiveTerm
            ρ lam ε ctx.normalizedInput p.1 p.2 := by
    funext p
    dsimp only [e]
    simp_rw [r324PrimitiveBlockTupleMeasurableEquiv_symm_apply]
    unfold normalizedHeadDensity crossGapPrimitiveTerm
    rw [integral_const_mul]
  rw [← heq]
  exact hout.measurable

private theorem measurable_crossGapPrimitiveTerm_normalized_zero
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ) :
    Measurable
      (fun z : T4 =>
        ctx.crossGapPrimitiveTerm
          ρ lam ε ctx.normalizedInput z 0) := by
  have hzero :
      Measurable (fun _z : T4 => (0 : T4)) :=
    measurable_const
  show Measurable
    ((fun p : T4 × T4 =>
        ctx.crossGapPrimitiveTerm
          ρ lam ε ctx.normalizedInput p.1 p.2) ∘
      fun z : T4 => (z, 0))
  exact
    (ctx.measurable_crossGapPrimitiveTerm_normalized
        ρ lam ε).comp
      (measurable_id.prodMk hzero)

end R324NestedCrossStepContext

/-- Measurability of an inverse-square/kernel/inverse-square product. -/
private theorem measurable_invSq_kernelTriple
    (q : T4 → ℝ) (hq : Measurable q)
    (left right : T4) :
    Measurable
      (fun p : T4 × T4 =>
        invSqKer (left - p.1) * q (p.1 - p.2) *
          invSqKer (p.2 - right)) := by
  have hleft :
      Measurable
        (fun p : T4 × T4 => invSqKer (left - p.1)) :=
    measurable_invSqKer.comp
      (measurable_const.sub measurable_fst)
  have hmiddle :
      Measurable
        (fun p : T4 × T4 => q (p.1 - p.2)) :=
    hq.comp (measurable_fst.sub measurable_snd)
  have hright :
      Measurable
        (fun p : T4 × T4 => invSqKer (p.2 - right)) :=
    measurable_invSqKer.comp
      (measurable_snd.sub measurable_const)
  exact (hleft.mul hmiddle).mul hright

namespace R324NestedCrossProperStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- Domination of the exact proper head by one inserted-convolution
majorant, including the genuine integrability certificate needed for
Bochner monotonicity. -/
private theorem properHeadIntegral_le_insertedConvolution
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε supportConstant C : ℝ)
    (hε : 0 < ε)
    (left right : T4)
    (hgap :
      ∀ z : T4,
        ctx.step.crossGapPrimitiveTerm
            ρ lam ε ctx.step.normalizedInput z 0 ≤
          primitiveInsertedMajorant
            C lam ε supportConstant ctx.step.order z) :
    Integrable
        (fun p : T4 × T4 =>
          invSqKer (left - p.1) *
            ctx.step.crossGapPrimitiveTerm
              ρ lam ε ctx.step.normalizedInput
              (p.1 - p.2) 0 *
            invSqKer (p.2 - right))
        (paperMeasure.prod paperMeasure) ∧
      ctx.properHeadIntegral ρ lam ε left right ≤
        ∫ a, ∫ b,
          invSqKer (left - a) *
            primitiveInsertedMajorant
              C lam ε supportConstant
                ctx.step.order (a - b) *
            invSqKer (b - right)
          ∂paperMeasure ∂paperMeasure := by
  let exactIntegrand :=
    fun p : T4 × T4 =>
      invSqKer (left - p.1) *
        ctx.step.crossGapPrimitiveTerm
          ρ lam ε ctx.step.normalizedInput
          (p.1 - p.2) 0 *
        invSqKer (p.2 - right)
  let insertedIntegrand :=
    r324ProperInsertedConvolutionIntegrand
      C lam ε supportConstant ctx.step.order
        left right
  have hexactMeas : Measurable exactIntegrand := by
    have hkernel :
        Measurable
          (fun z : T4 =>
            ctx.step.crossGapPrimitiveTerm
              ρ lam ε ctx.step.normalizedInput z 0) := by
      exact
        ctx.step
          |>.measurable_crossGapPrimitiveTerm_normalized_zero
            ρ lam ε
    dsimp only [exactIntegrand]
    exact measurable_invSq_kernelTriple _ hkernel left right
  have hinserted :
      Integrable insertedIntegrand
        (paperMeasure.prod paperMeasure) := by
    dsimp only [insertedIntegrand]
    exact
      integrable_r324ProperInsertedConvolutionIntegrand
        C lam supportConstant ctx.step.order
          hε left right
  have hpoint :
      ∀ p : T4 × T4,
        exactIntegrand p ≤ insertedIntegrand p := by
    intro p
    dsimp only [exactIntegrand, insertedIntegrand,
      r324ProperInsertedConvolutionIntegrand]
    exact
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (hgap (p.1 - p.2))
          (invSqKer_nonneg _))
        (invSqKer_nonneg _)
  have hexactNonneg :
      ∀ p : T4 × T4, 0 ≤ exactIntegrand p := by
    intro p
    dsimp only [exactIntegrand]
    exact mul_nonneg
      (mul_nonneg
        (invSqKer_nonneg _)
        (ctx.step.crossGapPrimitiveTerm_nonneg
          ρ lam ε ctx.step.normalizedInput
          ctx.step.normalizedInput_nonneg _ _))
      (invSqKer_nonneg _)
  have hexact :
      Integrable exactIntegrand
        (paperMeasure.prod paperMeasure) := by
    refine hinserted.mono'
      hexactMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (hexactNonneg p)]
    exact hpoint p
  refine ⟨hexact, ?_⟩
  calc
    ctx.properHeadIntegral ρ lam ε left right =
        ∫ p, exactIntegrand p
          ∂(paperMeasure.prod paperMeasure) := by
      rfl
    _ ≤
        ∫ p, insertedIntegrand p
          ∂(paperMeasure.prod paperMeasure) :=
      integral_mono hexact hinserted hpoint
    _ =
        ∫ a, ∫ b,
          invSqKer (left - a) *
            primitiveInsertedMajorant
              C lam ε supportConstant
                ctx.step.order (a - b) *
            invSqKer (b - right)
          ∂paperMeasure ∂paperMeasure := by
      exact
        integral_r324ProperInsertedConvolutionIntegrand_eq_iterated
          C lam supportConstant ctx.step.order
            hε left right

end R324NestedCrossProperStepContext

namespace R324ProperHeadSharpProvider

/-- Proposition 4.1 together with the sharp proper inserted convolution
produces one fixed-ambient provider throughout the truncation range.

The ambient order is fixed in the provider type because Proposition 4.1
is only available under `m ≤ truncOrder ε`.  The one-head scalar `K` is
absorbed into `D = max 1 K * C`; positivity and the fact that every
literal block has order at least one justify this absorption uniformly
over all heads in the ambient schedule. -/
theorem exists_at_truncation
    (ρ : SmoothCutoff)
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    {lam ε : ℝ}
    (hlam : 0 < lam) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hlog : 1 ≤ |Real.log ε|)
    (hmtrunc : m ≤ truncOrder ε) :
    ∃ D : ℝ, 0 < D ∧
      R324ProperHeadSharpProvider
        ρ lam ε D κp κm π := by
  obtain
    ⟨supportConstant, C, hsupport, hC,
      hgap⟩ :=
    R324NestedCrossStepContext.exists_normalizedCrossGapTerm_le_majorant_at_truncation
      ρ
  obtain ⟨K, hK, hsharp⟩ :=
    exists_r324ProperInsertedConvolution_le hsupport
  let K₁ : ℝ := max 1 K
  let D : ℝ := K₁ * C
  have hK₁ : 1 ≤ K₁ := by
    exact le_max_left _ _
  have hD : 0 < D := by
    dsimp only [D]
    exact mul_pos (zero_lt_one.trans_le hK₁) hC
  refine ⟨D, hD, ?_⟩
  constructor
  intro ctx left right
  have hgapCtx :
      ∀ z : T4,
        ctx.step.crossGapPrimitiveTerm
            ρ lam ε ctx.step.normalizedInput z 0 ≤
          primitiveInsertedMajorant
            C lam ε supportConstant
              ctx.step.order z := by
    intro z
    exact
      (hgap κp κm π ctx.step lam ε
        hlam hε hε1 hmtrunc z).2
  have hdom :=
    ctx.properHeadIntegral_le_insertedConvolution
      ρ lam ε supportConstant C hε
      left right hgapCtx
  have hsharpCtx :=
    (hsharp C lam ε ctx.step.order
      left right hC.le hlam.le hε hε1 hlog).2
  have hexponent :
      1 ≤ 2 * ctx.step.order := by
    have horder := ctx.step.one_le_order
    omega
  have hKlePow :
      K ≤ K₁ ^ (2 * ctx.step.order) := by
    calc
      K ≤ K₁ := by
        dsimp only [K₁]
        exact le_max_right _ _
      _ = K₁ ^ (1 : ℕ) := by
        rw [pow_one]
      _ ≤ K₁ ^ (2 * ctx.step.order) :=
        pow_le_pow_right₀ hK₁ hexponent
  calc
    ctx.properHeadIntegral ρ lam ε left right ≤
        ∫ a, ∫ b,
          invSqKer (left - a) *
            primitiveInsertedMajorant
              C lam ε supportConstant
                ctx.step.order (a - b) *
            invSqKer (b - right)
          ∂paperMeasure ∂paperMeasure :=
      hdom.2
    _ ≤ (C * lam) ^ (2 * ctx.step.order) * K :=
      hsharpCtx
    _ ≤
        (C * lam) ^ (2 * ctx.step.order) *
          K₁ ^ (2 * ctx.step.order) :=
      mul_le_mul_of_nonneg_left hKlePow
        ((even_two_mul
          ctx.step.order).pow_nonneg _)
    _ = (D * lam) ^ (2 * ctx.step.order) := by
      dsimp only [D]
      rw [show
        K₁ * C * lam = (C * lam) * K₁ by ring]
      simp only [mul_pow]

end R324ProperHeadSharpProvider

/-- The canonical majorant data needed by the quantitative iteration,
with the physical `source` comparison erased only after it has generated
the exact constructor-by-constructor majorant.

This auxiliary relation avoids dependent elimination through the a.e.
proof fields of `R324NestedCrossContextFactorization`; no hypothesis is
added. -/
inductive R324NestedCrossBudgetRun
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (stopCarrier : Finset (Fin (2 * m)))
    (x y z w : T4) :
    (res : R324NestedCrossResidualPrefix κp κm π) →
    (({i : Fin (2 * m) // i ∈ res.activeCarrier} → T4) → ℝ) →
    ℕ → ℕ → Prop
  | stop
      (step : R324NestedCrossStepContext κp κm π)
      (hstop : step.head.carrier = stopCarrier)
      (context :
        T4 → T4 → T4 → T4 →
          (step.SurvivingCoordinate → T4) → ℝ)
      (hcontext :
        ∀ v, 0 ≤ context x y z w v)
      (hmajorant :
        Integrable
          (R324NestedCrossTerminalPayload.ofContext
            lam ε step context x y z w).density
          (Measure.pi fun _ :
            step.SurvivingCoordinate => paperMeasure)) :
      R324NestedCrossBudgetRun
        ρ lam ε stopCarrier x y z w
        step.residual
        (R324NestedCrossTerminalPayload.ofContext
          lam ε step context x y z w).density
        0 step.residual.remainingOrder
  | proper
      (ctx : R324NestedCrossProperStepContext κp κm π)
      (hhead : ctx.step.head.carrier ≠ stopCarrier)
      (nextMajorant :
        (ctx.step.PostCoordinate → T4) → ℝ)
      (nextPrefixOrder terminalOrder : ℕ)
      (next :
        R324NestedCrossBudgetRun
          ρ lam ε stopCarrier x y z w
          ctx.step.next nextMajorant
          nextPrefixOrder terminalOrder)
      (hmajorant :
        Integrable
          (fun v =>
            ctx.step.normalizedHeadDensity ρ lam ε
                (fun j =>
                  v (ctx.step.headSurvivingCoordinate j)) *
              ctx.connector
                (fun j =>
                  v (ctx.step.headSurvivingCoordinate j))
                (fun i =>
                  v (ctx.step.postSurvivingCoordinate i)) *
              nextMajorant
                (fun i =>
                  v (ctx.step.postSurvivingCoordinate i)))
          (Measure.pi fun _ :
            ctx.step.SurvivingCoordinate => paperMeasure)) :
      R324NestedCrossBudgetRun
        ρ lam ε stopCarrier x y z w
        ctx.step.residual
        (fun v =>
          ctx.step.normalizedHeadDensity ρ lam ε
              (fun j =>
                v (ctx.step.headSurvivingCoordinate j)) *
            ctx.connector
              (fun j =>
                v (ctx.step.headSurvivingCoordinate j))
              (fun i =>
                v (ctx.step.postSurvivingCoordinate i)) *
            nextMajorant
              (fun i =>
                v (ctx.step.postSurvivingCoordinate i)))
        (ctx.step.order + nextPrefixOrder) terminalOrder

namespace R324NestedCrossContextFactorization

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {ρ : SmoothCutoff} {lam ε D : ℝ}
    {stopCarrier : Finset (Fin (2 * m))}
    {x y z w : T4}
    {res : R324NestedCrossResidualPrefix κp κm π}
    {source majorant :
      (({i : Fin (2 * m) // i ∈ res.activeCarrier} → T4) → ℝ)}
    {prefixOrder terminalOrder : ℕ}

/-- Erase the physical source only after the honest local factorization
has generated its canonical majorant and recursive integrability data. -/
theorem toBudgetRun
    (factorization :
      R324NestedCrossContextFactorization
        ρ lam ε stopCarrier x y z w
        res source majorant prefixOrder terminalOrder) :
    R324NestedCrossBudgetRun
      ρ lam ε stopCarrier x y z w
      res majorant prefixOrder terminalOrder := by
  induction factorization with
  | stop step hstop context source hcontext
      hmajorant hle =>
      exact
        R324NestedCrossBudgetRun.stop
          step hstop context hcontext hmajorant
  | proper ctx hhead source nextSource nextMajorant
      nextPrefixOrder terminalOrder next hle
      hmajorant ih =>
      exact
        R324NestedCrossBudgetRun.proper
          ctx hhead nextMajorant
          nextPrefixOrder terminalOrder ih hmajorant

end R324NestedCrossContextFactorization

namespace R324NestedCrossBudgetRun

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {ρ : SmoothCutoff} {lam ε D : ℝ}
    {stopCarrier : Finset (Fin (2 * m))}
    {x y z w : T4}
    {res : R324NestedCrossResidualPrefix κp κm π}
    {majorant :
      (({i : Fin (2 * m) // i ∈ res.activeCarrier} → T4) → ℝ)}
    {prefixOrder terminalOrder : ℕ}

/-- Every majorant in a budget-ready run is genuinely integrable. -/
theorem majorant_integrable
    (run :
      R324NestedCrossBudgetRun
        ρ lam ε stopCarrier x y z w
        res majorant prefixOrder terminalOrder) :
    Integrable majorant
      (Measure.pi fun _ :
        {i : Fin (2 * m) // i ∈ res.activeCarrier} =>
          paperMeasure) := by
  cases run with
  | stop step hstop context hcontext hmajorant =>
      exact hmajorant
  | proper ctx hhead nextMajorant nextPrefixOrder
      terminalOrder next hmajorant =>
      exact hmajorant

/-- Every majorant in a budget-ready run is pointwise nonnegative. -/
theorem majorant_nonneg
    (run :
      R324NestedCrossBudgetRun
        ρ lam ε stopCarrier x y z w
        res majorant prefixOrder terminalOrder) :
    ∀ v, 0 ≤ majorant v := by
  induction run with
  | stop step hstop context hcontext hmajorant =>
      intro v
      unfold R324NestedCrossTerminalPayload.density
      exact mul_nonneg
        ((even_two_mul
          step.residual.remainingOrder).pow_nonneg _)
        (hcontext v)
  | proper ctx hhead nextMajorant nextPrefixOrder
      terminalOrder next hmajorant ih =>
      intro v
      exact mul_nonneg
        (mul_nonneg
          (ctx.step.normalizedHeadDensity_nonneg
            ρ lam ε _)
          (ctx.connector_nonneg _ _))
        (ih _)

/-- The proper-head Fubini transition needs no separate section
integrability hypothesis.  Joint integrability of the current
head-times-suffix density gives integrability of almost every scaled
head section.  When the suffix value is nonzero, division by that scalar
recovers the bare head; when it is zero, both sides of the desired
section identity vanish. -/
private theorem integral_exactProperDensity_of_current_integrable
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (nextDensity :
      (ctx.step.PostCoordinate → T4) → ℝ)
    (hcurrent :
      Integrable
        (fun v =>
          ctx.step.normalizedHeadDensity ρ lam ε
                (fun j =>
                  v (ctx.step.headSurvivingCoordinate j)) *
              ctx.connector
                (fun j =>
                  v (ctx.step.headSurvivingCoordinate j))
                (fun i =>
                  v (ctx.step.postSurvivingCoordinate i)) *
              nextDensity
                (fun i =>
                  v (ctx.step.postSurvivingCoordinate i)))
        (Measure.pi fun _ :
          ctx.step.SurvivingCoordinate =>
            paperMeasure)) :
    (∫ v,
        ctx.step.normalizedHeadDensity ρ lam ε
              (fun j =>
                v (ctx.step.headSurvivingCoordinate j)) *
            ctx.connector
              (fun j =>
                v (ctx.step.headSurvivingCoordinate j))
              (fun i =>
                v (ctx.step.postSurvivingCoordinate i)) *
            nextDensity
              (fun i =>
                v (ctx.step.postSurvivingCoordinate i))
        ∂Measure.pi fun _ => paperMeasure) =
      ∫ post : ctx.step.PostCoordinate → T4,
        ctx.properHeadIntegral ρ lam ε
            (post ctx.nextLeftPostCoordinate)
            (post ctx.nextRightPostCoordinate) *
          nextDensity post
        ∂Measure.pi fun _ => paperMeasure := by
  let e := ctx.step.splitSurvivingPiMeasurableEquiv
  let μ :=
    Measure.pi fun _ :
      ctx.step.SurvivingCoordinate => paperMeasure
  let μhead :=
    Measure.pi fun _ :
      Fin (2 * ctx.step.order) => paperMeasure
  let μpost :=
    Measure.pi fun _ :
      ctx.step.PostCoordinate => paperMeasure
  let current :=
    fun v : ctx.step.SurvivingCoordinate → T4 =>
      ctx.step.normalizedHeadDensity ρ lam ε
            (fun j =>
              v (ctx.step.headSurvivingCoordinate j)) *
          ctx.connector
            (fun j =>
              v (ctx.step.headSurvivingCoordinate j))
            (fun i =>
              v (ctx.step.postSurvivingCoordinate i)) *
          nextDensity
            (fun i =>
              v (ctx.step.postSurvivingCoordinate i))
  have hp : MeasurePreserving e μ (μhead.prod μpost) :=
    ctx.step.measurePreserving_splitSurvivingPiMeasurableEquiv
  have hsplit :
      Integrable
        (fun p : (Fin (2 * ctx.step.order) → T4) ×
            (ctx.step.PostCoordinate → T4) =>
          current (e.symm p))
        (μhead.prod μpost) := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p => current (e.symm p))
    apply hiff.mp
    have hcomp :
        (fun p => current (e.symm p)) ∘ e =
          current := by
      funext v
      simp only [Function.comp_apply, e.symm_apply_apply]
    rw [hcomp]
    simpa only [current] using hcurrent
  have hsections :
      ∀ᵐ post ∂μpost,
        Integrable
          (fun t =>
            current (e.symm (t, post))) μhead :=
    hsplit.prod_left_ae
  rw [ctx.step.integral_splitSurviving_post_first _ hcurrent]
  apply integral_congr_ae
  filter_upwards [hsections] with post hpost
  have hscaled :
      Integrable
        (fun t : Fin (2 * ctx.step.order) → T4 =>
          (ctx.step.normalizedHeadDensity ρ lam ε t *
              ctx.connector t post) *
            nextDensity post)
        μhead := by
    simpa only [current, e,
      R324NestedCrossStepContext.splitSurvivingPiMeasurableEquiv_symm_head,
      R324NestedCrossStepContext.splitSurvivingPiMeasurableEquiv_symm_post]
      using hpost
  by_cases hsuffix : nextDensity post = 0
  · simp only [
      R324NestedCrossStepContext.splitSurvivingPiMeasurableEquiv_symm_head,
      R324NestedCrossStepContext.splitSurvivingPiMeasurableEquiv_symm_post]
    simp [hsuffix]
  · have hhead :
        Integrable
          (fun t : Fin (2 * ctx.step.order) → T4 =>
            ctx.step.normalizedHeadDensity ρ lam ε t *
              ctx.connector t post)
          μhead := by
      have hdiv :=
        hscaled.const_mul (nextDensity post)⁻¹
      refine hdiv.congr
        (Filter.Eventually.of_forall fun t => ?_)
      dsimp only
      field_simp
    simp only [
      R324NestedCrossStepContext.splitSurvivingPiMeasurableEquiv_symm_head,
      R324NestedCrossStepContext.splitSurvivingPiMeasurableEquiv_symm_post]
    rw [integral_mul_const,
      ctx.integral_normalizedHeadDensity_mul_connector
        ρ lam ε post hhead]

/-- Iterating the proper-head bound leaves the actual endpoint-preserving
terminal payload and charges exactly the total proper-prefix order.

Besides the quantitative integral inequality, the witness records:

* the genuine stop head and its carrier equality;
* all four original external endpoints;
* the exact terminal perturbative order;
* pointwise nonnegativity of the unscaled terminal context; and
* genuine integrability of the weighted terminal density.
-/
theorem exists_terminalPayload_integral_le
    (provider :
      R324ProperHeadSharpProvider
        ρ lam ε D κp κm π)
    (run :
      R324NestedCrossBudgetRun
        ρ lam ε stopCarrier x y z w
        res majorant prefixOrder terminalOrder) :
    ∃ (step : R324NestedCrossStepContext κp κm π),
      ∃ (_ : step.head.carrier = stopCarrier),
        ∃ (payload :
            R324NestedCrossTerminalPayload lam ε step),
          payload.x = x ∧
          payload.y = y ∧
          payload.z = z ∧
          payload.w = w ∧
          terminalOrder = step.residual.remainingOrder ∧
          (∀ v, 0 ≤ payload.unscaledDensity v) ∧
          Integrable payload.density
            (Measure.pi fun _ :
              step.SurvivingCoordinate => paperMeasure) ∧
          (∫ v, majorant v
              ∂Measure.pi fun _ :
                {i : Fin (2 * m) //
                  i ∈ res.activeCarrier} =>
                    paperMeasure) ≤
            (D * lam) ^ (2 * prefixOrder) *
              ∫ v, payload.density v
                ∂Measure.pi fun _ :
                  step.SurvivingCoordinate =>
                    paperMeasure := by
  refine R324NestedCrossBudgetRun.rec
    (motive :=
      fun res majorant prefixOrder terminalOrder _ =>
        ∃ (step : R324NestedCrossStepContext κp κm π),
          ∃ (_ : step.head.carrier = stopCarrier),
            ∃ (payload :
                R324NestedCrossTerminalPayload lam ε step),
              payload.x = x ∧
              payload.y = y ∧
              payload.z = z ∧
              payload.w = w ∧
              terminalOrder =
                  step.residual.remainingOrder ∧
              (∀ v, 0 ≤ payload.unscaledDensity v) ∧
              Integrable payload.density
                (Measure.pi fun _ :
                  step.SurvivingCoordinate =>
                    paperMeasure) ∧
              (∫ v, majorant v
                  ∂Measure.pi fun _ :
                    {i : Fin (2 * m) //
                      i ∈ res.activeCarrier} =>
                        paperMeasure) ≤
                (D * lam) ^ (2 * prefixOrder) *
                  ∫ v, payload.density v
                    ∂Measure.pi fun _ :
                      step.SurvivingCoordinate =>
                        paperMeasure)
    ?_ ?_ run
  · exact fun step hstop context hcontext hmajorant => by
      let payload :=
        R324NestedCrossTerminalPayload.ofContext
          lam ε step context x y z w
      refine
        ⟨step, hstop, payload,
          rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · intro v
        exact hcontext v
      · exact hmajorant
      · change
          (∫ v : step.SurvivingCoordinate → T4,
              payload.density v
              ∂Measure.pi fun _ => paperMeasure) ≤
            (D * lam) ^ (2 * 0) *
              ∫ v : step.SurvivingCoordinate → T4,
                payload.density v
                ∂Measure.pi fun _ => paperMeasure
        simp only [Nat.mul_zero, pow_zero, one_mul]
        exact le_rfl
  · exact fun ctx hhead nextMajorant
      nextPrefixOrder terminalOrder next
      hmajorant ih => by
      obtain
        ⟨terminalStep, hterminalStop, payload,
          hx, hy, hz, hw, hterminalOrder,
          hpayloadNonneg, hpayloadIntegrable,
          hnextBudget⟩ :=
        ih
      have hexact :=
        integral_exactProperDensity_of_current_integrable
          ctx nextMajorant hmajorant
      let A : ℝ :=
        (D * lam) ^ (2 * ctx.step.order)
      have hA : 0 ≤ A := by
        dsimp only [A]
        exact
          (even_two_mul ctx.step.order).pow_nonneg _
      have houterNonneg :
          ∀ post : ctx.step.PostCoordinate → T4,
            0 ≤
              ctx.properHeadIntegral ρ lam ε
                  (post ctx.nextLeftPostCoordinate)
                  (post ctx.nextRightPostCoordinate) *
                nextMajorant post := by
        intro post
        exact mul_nonneg
          (ctx.properHeadIntegral_nonneg
            ρ lam ε
            (post ctx.nextLeftPostCoordinate)
            (post ctx.nextRightPostCoordinate))
          (next.majorant_nonneg post)
      have hconstantIntegrable :
          Integrable
            (fun post :
                ctx.step.PostCoordinate → T4 =>
              A * nextMajorant post)
            (Measure.pi fun _ => paperMeasure) :=
        next.majorant_integrable.const_mul A
      have houterLe :
          (∫ post : ctx.step.PostCoordinate → T4,
              ctx.properHeadIntegral ρ lam ε
                  (post ctx.nextLeftPostCoordinate)
                  (post ctx.nextRightPostCoordinate) *
                nextMajorant post
              ∂Measure.pi fun _ => paperMeasure) ≤
            A *
              ∫ post : ctx.step.PostCoordinate → T4,
                nextMajorant post
                ∂Measure.pi fun _ => paperMeasure := by
        calc
          (∫ post : ctx.step.PostCoordinate → T4,
              ctx.properHeadIntegral ρ lam ε
                  (post ctx.nextLeftPostCoordinate)
                  (post ctx.nextRightPostCoordinate) *
                nextMajorant post
              ∂Measure.pi fun _ => paperMeasure) ≤
              ∫ post : ctx.step.PostCoordinate → T4,
                A * nextMajorant post
                ∂Measure.pi fun _ => paperMeasure := by
            apply integral_mono_of_nonneg
              (Filter.Eventually.of_forall houterNonneg)
              hconstantIntegrable
            filter_upwards with post
            exact mul_le_mul_of_nonneg_right
              (provider.headIntegral_le ctx
                (post ctx.nextLeftPostCoordinate)
                (post ctx.nextRightPostCoordinate))
              (next.majorant_nonneg post)
          _ =
              A *
                ∫ post : ctx.step.PostCoordinate → T4,
                  nextMajorant post
                  ∂Measure.pi fun _ => paperMeasure := by
            rw [integral_const_mul]
      have hbudget :
          (∫ v,
              ctx.step.normalizedHeadDensity ρ lam ε
                  (fun j =>
                    v (ctx.step.headSurvivingCoordinate j)) *
                ctx.connector
                  (fun j =>
                    v (ctx.step.headSurvivingCoordinate j))
                  (fun i =>
                    v (ctx.step.postSurvivingCoordinate i)) *
                nextMajorant
                  (fun i =>
                    v (ctx.step.postSurvivingCoordinate i))
              ∂Measure.pi fun _ => paperMeasure) ≤
            (D * lam) ^
                (2 *
                  (ctx.step.order + nextPrefixOrder)) *
              ∫ v, payload.density v
                ∂Measure.pi fun _ :
                  terminalStep.SurvivingCoordinate =>
                    paperMeasure := by
        calc
          (∫ v,
              ctx.step.normalizedHeadDensity ρ lam ε
                  (fun j =>
                    v (ctx.step.headSurvivingCoordinate j)) *
                ctx.connector
                  (fun j =>
                    v (ctx.step.headSurvivingCoordinate j))
                  (fun i =>
                    v (ctx.step.postSurvivingCoordinate i)) *
                nextMajorant
                  (fun i =>
                    v (ctx.step.postSurvivingCoordinate i))
              ∂Measure.pi fun _ => paperMeasure) =
              ∫ post : ctx.step.PostCoordinate → T4,
                ctx.properHeadIntegral ρ lam ε
                    (post ctx.nextLeftPostCoordinate)
                    (post ctx.nextRightPostCoordinate) *
                  nextMajorant post
                ∂Measure.pi fun _ => paperMeasure :=
            hexact
          _ ≤
              A *
                ∫ post : ctx.step.PostCoordinate → T4,
                  nextMajorant post
                  ∂Measure.pi fun _ => paperMeasure :=
            houterLe
          _ ≤
              A *
                ((D * lam) ^ (2 * nextPrefixOrder) *
                  ∫ v, payload.density v
                    ∂Measure.pi fun _ :
                      terminalStep.SurvivingCoordinate =>
                        paperMeasure) :=
            mul_le_mul_of_nonneg_left hnextBudget hA
          _ =
              (D * lam) ^
                  (2 *
                    (ctx.step.order + nextPrefixOrder)) *
                ∫ v, payload.density v
                  ∂Measure.pi fun _ :
                    terminalStep.SurvivingCoordinate =>
                      paperMeasure := by
            dsimp only [A]
            rw [show
              2 * (ctx.step.order + nextPrefixOrder) =
                2 * ctx.step.order +
                  2 * nextPrefixOrder by omega]
            rw [pow_add]
            ring
      exact
        ⟨terminalStep, hterminalStop, payload,
          hx, hy, hz, hw, hterminalOrder,
          hpayloadNonneg, hpayloadIntegrable,
          hbudget⟩

end R324NestedCrossBudgetRun

namespace R324NestedCrossContextFactorization

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {ρ : SmoothCutoff} {lam ε D : ℝ}
    {stopCarrier : Finset (Fin (2 * m))}
    {x y z w : T4}
    {res : R324NestedCrossResidualPrefix κp κm π}
    {source majorant :
      (({i : Fin (2 * m) // i ∈ res.activeCarrier} → T4) → ℝ)}
    {prefixOrder terminalOrder : ℕ}

/-- Quantitative consumer for the honest physical-to-canonical
factorization.  The source comparison has already been used to construct
`majorant`; the conclusion retains the genuine stop payload. -/
theorem exists_terminalPayload_integral_le
    (provider :
      R324ProperHeadSharpProvider
        ρ lam ε D κp κm π)
    (factorization :
      R324NestedCrossContextFactorization
        ρ lam ε stopCarrier x y z w
        res source majorant prefixOrder terminalOrder) :
    ∃ (step : R324NestedCrossStepContext κp κm π),
      ∃ (_ : step.head.carrier = stopCarrier),
        ∃ (payload :
            R324NestedCrossTerminalPayload lam ε step),
          payload.x = x ∧
          payload.y = y ∧
          payload.z = z ∧
          payload.w = w ∧
          terminalOrder = step.residual.remainingOrder ∧
          (∀ v, 0 ≤ payload.unscaledDensity v) ∧
          Integrable payload.density
            (Measure.pi fun _ :
              step.SurvivingCoordinate => paperMeasure) ∧
          (∫ v, majorant v
              ∂Measure.pi fun _ :
                {i : Fin (2 * m) //
                  i ∈ res.activeCarrier} =>
                    paperMeasure) ≤
            (D * lam) ^ (2 * prefixOrder) *
              ∫ v, payload.density v
                ∂Measure.pi fun _ :
                  step.SurvivingCoordinate =>
                    paperMeasure :=
  factorization.toBudgetRun.exists_terminalPayload_integral_le
    provider

end R324NestedCrossContextFactorization

namespace R324InitialNestedContextFactorization

variable {ρ : SmoothCutoff} {lam ε D : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {selected : R324ResidualCovarianceSlot κp}
    {terminal :
      R324TwoHalfTerminalData ρ lam ε κp κm}
    {L : ℝ} {x y z w : T4}

/-- End-to-end Step 3 handoff from the physical initial nested integral
to the actual endpoint-preserving terminal payload.  This composes the
honest physical-source comparison with the quantitative proper-prefix
iteration; no target-shaped final R-324 estimate is inserted. -/
theorem exists_terminalPayload_physicalIntegral_le
    (provider :
      R324ProperHeadSharpProvider
        ρ lam ε D κp κm π)
    (factorization :
      R324InitialNestedContextFactorization
        ρ lam ε κp κm π selected terminal L x y z w)
    (hphysical :
      Integrable
        (terminal.initialNestedMarkedPhysicalCore
          π selected L x y z w)
        (Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure)) :
    ∃ (step : R324NestedCrossStepContext κp κm π),
      ∃ (_ :
          step.head.carrier =
            r324MarkedResidualBlock κp κm π selected),
        ∃ (payload :
            R324NestedCrossTerminalPayload lam ε step),
          payload.x = x ∧
          payload.y = y ∧
          payload.z = z ∧
          payload.w = w ∧
          factorization.terminalOrder =
              step.residual.remainingOrder ∧
          (∀ v, 0 ≤ payload.unscaledDensity v) ∧
          Integrable payload.density
            (Measure.pi fun _ :
              step.SurvivingCoordinate => paperMeasure) ∧
          (lamEps lam ε ^
                (2 *
                  (R324NestedCrossResidualPrefix.initial
                    κp κm π).remainingOrder) *
              ‖∫ v,
                  terminal.initialNestedMarkedPhysicalCore
                    π selected L x y z w v
                  ∂Measure.pi fun _ :
                    terminal.NestedCoordinate π =>
                      paperMeasure‖) ≤
            (D * lam) ^
                (2 * factorization.prefixOrder) *
              ∫ v, payload.density v
                ∂Measure.pi fun _ :
                  step.SurvivingCoordinate =>
                    paperMeasure := by
  obtain
    ⟨step, hstop, payload,
      hx, hy, hz, hw, hterminalOrder,
      hpayloadNonneg, hpayloadIntegrable,
      hbudget⟩ :=
    factorization.factorization
      |>.exists_terminalPayload_integral_le provider
  refine
    ⟨step, hstop, payload,
      hx, hy, hz, hw, hterminalOrder,
      hpayloadNonneg, hpayloadIntegrable, ?_⟩
  exact
    (factorization
      |>.initialWeight_mul_norm_integral_le_majorant
        hphysical).trans hbudget

end R324InitialNestedContextFactorization

end

end Anderson4D
