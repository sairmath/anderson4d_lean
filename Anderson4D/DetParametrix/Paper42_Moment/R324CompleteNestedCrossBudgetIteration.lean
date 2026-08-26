import Anderson4D.DetParametrix.Paper42_Moment.R324CompleteNestedCrossIteration

/-!
# Quantitative iteration for complete grouped cross heads

Paper Section 4.2, Steps 2(f)--3 keep the complete primitive-pairing sum
grouped while the nested cross blocks are removed.  This file is the
quantitative iterator for that grouped object.  It is deliberately neutral
about the final (outermost) block: a later physical factorization supplies
the terminal density and this iterator charges only the proper heads before
it.

No triangle inequality over primitive pairings occurs here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- A budget-ready nested run whose proper constructors use the complete
primitive-pairing head.  The stop density is kept abstract so that the
outermost block can later be bounded by one final application of Proposition
4.1 rather than by another scalar proper-head estimate. -/
inductive R324CompleteNestedCrossBudgetRun
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (ρ : SmoothCutoff) (lam ε : ℝ) :
    (res : R324NestedCrossResidualPrefix κp κm π) →
    (({i : Fin (2 * m) // i ∈ res.activeCarrier} → T4) → ℝ) →
    ℕ → ℕ → Prop
  | stop
      (res : R324NestedCrossResidualPrefix κp κm π)
      (density :
        ({i : Fin (2 * m) // i ∈ res.activeCarrier} → T4) → ℝ)
      (hnonneg : ∀ v, 0 ≤ density v)
      (hintegrable :
        Integrable density
          (Measure.pi fun _ :
            {i : Fin (2 * m) // i ∈ res.activeCarrier} => paperMeasure)) :
      R324CompleteNestedCrossBudgetRun
        ρ lam ε res density 0 res.remainingOrder
  | proper
      (ctx : R324NestedCrossProperStepContext κp κm π)
      (nextDensity : (ctx.step.PostCoordinate → T4) → ℝ)
      (nextPrefixOrder terminalOrder : ℕ)
      (next :
        R324CompleteNestedCrossBudgetRun
          ρ lam ε ctx.step.next nextDensity
          nextPrefixOrder terminalOrder)
      (hintegrable :
        Integrable
          (fun v : ctx.step.SurvivingCoordinate → T4 =>
            ctx.step.completeNormalizedHeadDensity ρ lam ε
                (fun j => v (ctx.step.headSurvivingCoordinate j)) *
              ctx.connector
                (fun j => v (ctx.step.headSurvivingCoordinate j))
                (fun i => v (ctx.step.postSurvivingCoordinate i)) *
              nextDensity
                (fun i => v (ctx.step.postSurvivingCoordinate i)))
          (Measure.pi fun _ :
            ctx.step.SurvivingCoordinate => paperMeasure)) :
      R324CompleteNestedCrossBudgetRun
        ρ lam ε ctx.step.residual
        (fun v =>
          ctx.step.completeNormalizedHeadDensity ρ lam ε
              (fun j => v (ctx.step.headSurvivingCoordinate j)) *
            ctx.connector
              (fun j => v (ctx.step.headSurvivingCoordinate j))
              (fun i => v (ctx.step.postSurvivingCoordinate i)) *
            nextDensity
              (fun i => v (ctx.step.postSurvivingCoordinate i)))
        (ctx.step.order + nextPrefixOrder) terminalOrder

namespace R324CompleteNestedCrossBudgetRun

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {ρ : SmoothCutoff} {lam ε D : ℝ}
    {res : R324NestedCrossResidualPrefix κp κm π}
    {density :
      (({i : Fin (2 * m) // i ∈ res.activeCarrier} → T4) → ℝ)}
    {prefixOrder terminalOrder : ℕ}

theorem density_integrable
    (run :
      R324CompleteNestedCrossBudgetRun
        ρ lam ε res density prefixOrder terminalOrder) :
    Integrable density
      (Measure.pi fun _ :
        {i : Fin (2 * m) // i ∈ res.activeCarrier} => paperMeasure) := by
  cases run with
  | stop res density hnonneg hintegrable => exact hintegrable
  | proper ctx nextDensity nextPrefixOrder terminalOrder next hintegrable =>
      exact hintegrable

theorem density_nonneg
    (run :
      R324CompleteNestedCrossBudgetRun
        ρ lam ε res density prefixOrder terminalOrder) :
    ∀ v, 0 ≤ density v := by
  induction run with
  | stop res density hnonneg hintegrable => exact hnonneg
  | proper ctx nextDensity nextPrefixOrder terminalOrder next hintegrable ih =>
      intro v
      exact mul_nonneg
        (mul_nonneg
          (ctx.step.completeNormalizedHeadDensity_nonneg ρ lam ε _)
          (ctx.connector_nonneg _ _))
        (ih _)

/-- The proper-prefix and terminal orders partition the literal remaining
cross schedule. -/
theorem remainingOrder_eq
    (run :
      R324CompleteNestedCrossBudgetRun
        ρ lam ε res density prefixOrder terminalOrder) :
    res.remainingOrder = prefixOrder + terminalOrder := by
  induction run with
  | stop res density hnonneg hintegrable => simp
  | proper ctx nextDensity nextPrefixOrder terminalOrder next hintegrable ih =>
      rw [ctx.step.remainingOrder_eq_order_add_next, ih]
      omega

/-- Exact Fubini transition for one complete grouped proper head.  Joint
integrability of the current density supplies the almost-everywhere section
integrability needed to invoke the complete-head endpoint identity. -/
theorem integral_completeProperDensity_of_current_integrable
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (nextDensity : (ctx.step.PostCoordinate → T4) → ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcurrent :
      Integrable
        (fun v : ctx.step.SurvivingCoordinate → T4 =>
          ctx.step.completeNormalizedHeadDensity ρ lam ε
                (fun j => v (ctx.step.headSurvivingCoordinate j)) *
              ctx.connector
                (fun j => v (ctx.step.headSurvivingCoordinate j))
                (fun i => v (ctx.step.postSurvivingCoordinate i)) *
              nextDensity
                (fun i => v (ctx.step.postSurvivingCoordinate i)))
        (Measure.pi fun _ :
          ctx.step.SurvivingCoordinate => paperMeasure)) :
    (∫ v : ctx.step.SurvivingCoordinate → T4,
        ctx.step.completeNormalizedHeadDensity ρ lam ε
              (fun j => v (ctx.step.headSurvivingCoordinate j)) *
            ctx.connector
              (fun j => v (ctx.step.headSurvivingCoordinate j))
              (fun i => v (ctx.step.postSurvivingCoordinate i)) *
            nextDensity
              (fun i => v (ctx.step.postSurvivingCoordinate i))
        ∂Measure.pi fun _ => paperMeasure) =
      ∫ post : ctx.step.PostCoordinate → T4,
        ctx.completeProperHeadIntegral ρ lam ε
            (post ctx.nextLeftPostCoordinate)
            (post ctx.nextRightPostCoordinate) *
          nextDensity post
        ∂Measure.pi fun _ => paperMeasure := by
  let e := ctx.step.splitSurvivingPiMeasurableEquiv
  let μ := Measure.pi fun _ : ctx.step.SurvivingCoordinate => paperMeasure
  let μhead := Measure.pi fun _ : Fin (2 * ctx.step.order) => paperMeasure
  let μpost := Measure.pi fun _ : ctx.step.PostCoordinate => paperMeasure
  let current :=
    fun v : ctx.step.SurvivingCoordinate → T4 =>
      ctx.step.completeNormalizedHeadDensity ρ lam ε
            (fun j => v (ctx.step.headSurvivingCoordinate j)) *
          ctx.connector
            (fun j => v (ctx.step.headSurvivingCoordinate j))
            (fun i => v (ctx.step.postSurvivingCoordinate i)) *
          nextDensity
            (fun i => v (ctx.step.postSurvivingCoordinate i))
  have hp : MeasurePreserving e μ (μhead.prod μpost) :=
    ctx.step.measurePreserving_splitSurvivingPiMeasurableEquiv
  have hsplit :
      Integrable
        (fun p : (Fin (2 * ctx.step.order) → T4) ×
            (ctx.step.PostCoordinate → T4) => current (e.symm p))
        (μhead.prod μpost) := by
    have hiff := hp.integrable_comp_emb e.measurableEmbedding
      (g := fun p => current (e.symm p))
    apply hiff.mp
    have hcomp : (fun p => current (e.symm p)) ∘ e = current := by
      funext v
      simp only [Function.comp_apply, e.symm_apply_apply]
    rw [hcomp]
    simpa only [current, μ] using hcurrent
  have hsections :
      ∀ᵐ post ∂μpost,
        Integrable (fun t => current (e.symm (t, post))) μhead :=
    hsplit.prod_left_ae
  rw [ctx.step.integral_splitSurviving_post_first _ hcurrent]
  apply integral_congr_ae
  filter_upwards [hsections] with post hpost
  have hscaled :
      Integrable
        (fun t : Fin (2 * ctx.step.order) → T4 =>
          (ctx.step.completeNormalizedHeadDensity ρ lam ε t *
              ctx.connector t post) * nextDensity post)
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
            ctx.step.completeNormalizedHeadDensity ρ lam ε t *
              ctx.connector t post)
          μhead := by
      have hdiv := hscaled.const_mul (nextDensity post)⁻¹
      refine hdiv.congr (Filter.Eventually.of_forall fun t => ?_)
      dsimp only
      field_simp
    simp only [
      R324NestedCrossStepContext.splitSurvivingPiMeasurableEquiv_symm_head,
      R324NestedCrossStepContext.splitSurvivingPiMeasurableEquiv_symm_post]
    rw [integral_mul_const,
      ctx.integral_completeNormalizedHeadDensity_mul_connector
        ρ lam ε hε hε1 post hhead]

/-- Iterating the complete proper-head estimate reaches one genuine terminal
density and charges exactly the accumulated proper-prefix order. -/
theorem exists_terminal_integral_le
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324CompleteProperHeadSharpProvider
        ρ lam ε D κp κm π)
    (run :
      R324CompleteNestedCrossBudgetRun
        ρ lam ε res density prefixOrder terminalOrder) :
    ∃ (terminalRes : R324NestedCrossResidualPrefix κp κm π),
      ∃ terminalDensity :
          ({i : Fin (2 * m) // i ∈ terminalRes.activeCarrier} → T4) → ℝ,
        terminalOrder = terminalRes.remainingOrder ∧
        (∀ v, 0 ≤ terminalDensity v) ∧
        Integrable terminalDensity
          (Measure.pi fun _ :
            {i : Fin (2 * m) // i ∈ terminalRes.activeCarrier} =>
              paperMeasure) ∧
        (∫ v, density v
            ∂Measure.pi fun _ :
              {i : Fin (2 * m) // i ∈ res.activeCarrier} =>
                paperMeasure) ≤
          (D * lam) ^ (2 * prefixOrder) *
            ∫ v, terminalDensity v
              ∂Measure.pi fun _ :
                {i : Fin (2 * m) // i ∈ terminalRes.activeCarrier} =>
                  paperMeasure := by
  induction run with
  | stop terminalRes terminalDensity hnonneg hintegrable =>
      refine ⟨terminalRes, terminalDensity, rfl, hnonneg, hintegrable, ?_⟩
      simp only [Nat.mul_zero, pow_zero, one_mul]
      exact le_rfl
  | proper ctx nextDensity nextPrefixOrder terminalOrder next hintegrable ih =>
      obtain ⟨terminalRes, terminalDensity, hterminalOrder,
        hterminalNonneg, hterminalIntegrable, hnextBudget⟩ := ih
      have hexact :=
        integral_completeProperDensity_of_current_integrable
          ctx nextDensity hε hε1 hintegrable
      let A : ℝ := (D * lam) ^ (2 * ctx.step.order)
      have hA : 0 ≤ A := by
        dsimp only [A]
        exact (even_two_mul ctx.step.order).pow_nonneg _
      have houterNonneg :
          ∀ post : ctx.step.PostCoordinate → T4,
            0 ≤ ctx.completeProperHeadIntegral ρ lam ε
                (post ctx.nextLeftPostCoordinate)
                (post ctx.nextRightPostCoordinate) * nextDensity post := by
        intro post
        exact mul_nonneg
          (ctx.completeProperHeadIntegral_nonneg ρ lam ε _ _)
          (next.density_nonneg post)
      have hconstantIntegrable :
          Integrable
            (fun post : ctx.step.PostCoordinate → T4 =>
              A * nextDensity post)
            (Measure.pi fun _ => paperMeasure) :=
        next.density_integrable.const_mul A
      have houterLe :
          (∫ post : ctx.step.PostCoordinate → T4,
              ctx.completeProperHeadIntegral ρ lam ε
                  (post ctx.nextLeftPostCoordinate)
                  (post ctx.nextRightPostCoordinate) * nextDensity post
              ∂Measure.pi fun _ => paperMeasure) ≤
            A * ∫ post : ctx.step.PostCoordinate → T4,
              nextDensity post ∂Measure.pi fun _ => paperMeasure := by
        calc
          _ ≤ ∫ post : ctx.step.PostCoordinate → T4,
                A * nextDensity post
                ∂Measure.pi fun _ => paperMeasure := by
              apply integral_mono_of_nonneg
                (Filter.Eventually.of_forall houterNonneg)
                hconstantIntegrable
              filter_upwards with post
              exact mul_le_mul_of_nonneg_right
                (provider.headIntegral_le ctx
                  (post ctx.nextLeftPostCoordinate)
                  (post ctx.nextRightPostCoordinate))
                (next.density_nonneg post)
          _ = A * ∫ post : ctx.step.PostCoordinate → T4,
                nextDensity post ∂Measure.pi fun _ => paperMeasure := by
              rw [integral_const_mul]
      refine ⟨terminalRes, terminalDensity, hterminalOrder,
        hterminalNonneg, hterminalIntegrable, ?_⟩
      calc
        (∫ v : ctx.step.SurvivingCoordinate → T4,
            ctx.step.completeNormalizedHeadDensity ρ lam ε
                  (fun j => v (ctx.step.headSurvivingCoordinate j)) *
                ctx.connector
                  (fun j => v (ctx.step.headSurvivingCoordinate j))
                  (fun i => v (ctx.step.postSurvivingCoordinate i)) *
                nextDensity
                  (fun i => v (ctx.step.postSurvivingCoordinate i))
            ∂Measure.pi fun _ => paperMeasure) =
          ∫ post : ctx.step.PostCoordinate → T4,
            ctx.completeProperHeadIntegral ρ lam ε
                (post ctx.nextLeftPostCoordinate)
                (post ctx.nextRightPostCoordinate) * nextDensity post
            ∂Measure.pi fun _ => paperMeasure := hexact
        _ ≤ A * ∫ post : ctx.step.PostCoordinate → T4,
              nextDensity post ∂Measure.pi fun _ => paperMeasure := houterLe
        _ ≤ A * ((D * lam) ^ (2 * nextPrefixOrder) *
              ∫ v, terminalDensity v
                ∂Measure.pi fun _ :
                  {i : Fin (2 * m) // i ∈ terminalRes.activeCarrier} =>
                    paperMeasure) :=
          mul_le_mul_of_nonneg_left hnextBudget hA
        _ = (D * lam) ^ (2 * (ctx.step.order + nextPrefixOrder)) *
              ∫ v, terminalDensity v
                ∂Measure.pi fun _ :
                  {i : Fin (2 * m) // i ∈ terminalRes.activeCarrier} =>
                    paperMeasure := by
          dsimp only [A]
          rw [show 2 * (ctx.step.order + nextPrefixOrder) =
              2 * ctx.step.order + 2 * nextPrefixOrder by omega,
            pow_add]
          ring

end R324CompleteNestedCrossBudgetRun

end

end Anderson4D
