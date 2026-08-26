import Anderson4D.DetParametrix.Paper42_Moment.R324NestedCrossIterationClosure

/-!
# Honest physical-to-canonical boundary for the initial R-324 cross suffix

The exact two-half bridge ends with a complex physical core on the literal
initial nested carrier.  The proper cross-prefix iteration, by contrast,
consumes a nonnegative canonical majorant and stops at the block containing
the selected projected covariance.

This file records the missing boundary without identifying those two
objects pointwise:

* the physical core is first replaced by its norm;
* the exact residual perturbative weight is kept on that norm;
* every unmarked proper head is exposed explicitly as
  `normalizedHeadDensity * connector * nextMajorant`;
* the stop constructor retains an arbitrary four-endpoint context with the
  actual named endpoints; and
* every physical comparison is stated almost everywhere, because the
  inserted `distance² * invSqKer` cancellation is false on the totalized
  diagonal.

Thus a value of `R324InitialNestedContextFactorization` is a local,
proof-relevant factorization certificate.  It is not a target-shaped
pointwise density hypothesis and it does not discard the Step 4 endpoint
payload.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## The correctly weighted physical norm boundary -/

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal :
      R324TwoHalfTerminalData ρ lam ε κp κm)

/-- The physical norm density with exactly the perturbative weight carried
by the initial residual cross schedule.  In particular, the weight is not
silently charged to the already completed within-half schedules. -/
def initialNestedWeightedNormDensity
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4)
    (v : terminal.NestedCoordinate π → T4) : ℝ :=
  lamEps lam ε ^
      (2 *
        (R324NestedCrossResidualPrefix.initial
          κp κm π).remainingOrder) *
    terminal.initialNestedMarkedNormDensity
      π selected L x y z w v

theorem initialNestedWeightedNormDensity_nonneg
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4)
    (v : terminal.NestedCoordinate π → T4) :
    0 ≤ terminal.initialNestedWeightedNormDensity
      π selected L x y z w v := by
  unfold initialNestedWeightedNormDensity
  exact mul_nonneg
    ((even_two_mul
      (R324NestedCrossResidualPrefix.initial
        κp κm π).remainingOrder).pow_nonneg _)
    (terminal.initialNestedMarkedNormDensity_nonneg
      π selected L x y z w v)

/-- Absolute-value spelling of the same weight.  The equality uses only
that the perturbative exponent is even. -/
theorem initialNestedWeightedNormDensity_eq_absWeight
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4)
    (v : terminal.NestedCoordinate π → T4) :
    terminal.initialNestedWeightedNormDensity
        π selected L x y z w v =
      |lamEps lam ε| ^
          (2 *
            (R324NestedCrossResidualPrefix.initial
              κp κm π).remainingOrder) *
        terminal.initialNestedMarkedNormDensity
          π selected L x y z w v := by
  unfold initialNestedWeightedNormDensity
  rw [pow_abs_two_mul]

theorem integrable_initialNestedWeightedNormDensity
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4)
    (hphysical :
      Integrable
        (terminal.initialNestedMarkedPhysicalCore
          π selected L x y z w)
        (Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure)) :
    Integrable
      (terminal.initialNestedWeightedNormDensity
        π selected L x y z w)
      (Measure.pi fun _ :
        terminal.NestedCoordinate π => paperMeasure) := by
  exact
    (terminal.integrable_initialNestedMarkedNormDensity
      π selected L x y z w hphysical).const_mul _

/-- The weighted physical integral is bounded by the integral of the
weighted norm density.  This is the last statement which does not mention
any canonical proper-prefix majorant. -/
theorem initialWeight_mul_norm_integral_le_integral_weightedNorm
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4) :
    lamEps lam ε ^
          (2 *
            (R324NestedCrossResidualPrefix.initial
              κp κm π).remainingOrder) *
        ‖∫ v,
            terminal.initialNestedMarkedPhysicalCore
              π selected L x y z w v
            ∂Measure.pi fun _ :
              terminal.NestedCoordinate π => paperMeasure‖ ≤
      ∫ v,
        terminal.initialNestedWeightedNormDensity
          π selected L x y z w v
        ∂Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure := by
  have hweight :
      0 ≤
        lamEps lam ε ^
          (2 *
            (R324NestedCrossResidualPrefix.initial
              κp κm π).remainingOrder) :=
    (even_two_mul
      (R324NestedCrossResidualPrefix.initial
        κp κm π).remainingOrder).pow_nonneg _
  calc
    lamEps lam ε ^
          (2 *
            (R324NestedCrossResidualPrefix.initial
              κp κm π).remainingOrder) *
        ‖∫ v,
            terminal.initialNestedMarkedPhysicalCore
              π selected L x y z w v
            ∂Measure.pi fun _ :
              terminal.NestedCoordinate π => paperMeasure‖ ≤
        lamEps lam ε ^
            (2 *
              (R324NestedCrossResidualPrefix.initial
                κp κm π).remainingOrder) *
          (∫ v,
            terminal.initialNestedMarkedNormDensity
              π selected L x y z w v
            ∂Measure.pi fun _ :
              terminal.NestedCoordinate π => paperMeasure) :=
      mul_le_mul_of_nonneg_left
        (terminal.norm_integral_initialNestedMarkedPhysicalCore_le
          π selected L x y z w) hweight
    _ =
        ∫ v,
          lamEps lam ε ^
              (2 *
                (R324NestedCrossResidualPrefix.initial
                  κp κm π).remainingOrder) *
            terminal.initialNestedMarkedNormDensity
              π selected L x y z w v
          ∂Measure.pi fun _ :
            terminal.NestedCoordinate π => paperMeasure := by
      rw [integral_const_mul]
    _ = _ := rfl

/-- Absolute-value form of the weighted integral boundary. -/
theorem absInitialWeight_mul_norm_integral_le_integral_weightedNorm
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4) :
    |lamEps lam ε| ^
          (2 *
            (R324NestedCrossResidualPrefix.initial
              κp κm π).remainingOrder) *
        ‖∫ v,
            terminal.initialNestedMarkedPhysicalCore
              π selected L x y z w v
            ∂Measure.pi fun _ :
              terminal.NestedCoordinate π => paperMeasure‖ ≤
      ∫ v,
        terminal.initialNestedWeightedNormDensity
          π selected L x y z w v
        ∂Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure := by
  simpa only [pow_abs_two_mul] using
    terminal.initialWeight_mul_norm_integral_le_integral_weightedNorm
      π selected L x y z w

/-- Norm of the genuinely complex perturbative weight.  This equality is
the bridge between the complex coefficient identity and the real
nonnegative factorization below. -/
theorem norm_complexInitialWeight_mul_integral_eq
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4) :
    ‖(lamEps lam ε : ℂ) ^
          (2 *
            (R324NestedCrossResidualPrefix.initial
              κp κm π).remainingOrder) *
        (∫ v,
          terminal.initialNestedMarkedPhysicalCore
            π selected L x y z w v
          ∂Measure.pi fun _ :
            terminal.NestedCoordinate π => paperMeasure)‖ =
      lamEps lam ε ^
          (2 *
            (R324NestedCrossResidualPrefix.initial
              κp κm π).remainingOrder) *
        ‖∫ v,
            terminal.initialNestedMarkedPhysicalCore
              π selected L x y z w v
            ∂Measure.pi fun _ :
              terminal.NestedCoordinate π => paperMeasure‖ := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    (even_two_mul
      (R324NestedCrossResidualPrefix.initial
        κp κm π).remainingOrder).pow_abs]

/-- Direct complex-weight form of the physical-to-weighted-norm boundary. -/
theorem norm_complexInitialWeight_mul_integral_le_integral_weightedNorm
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4) :
    ‖(lamEps lam ε : ℂ) ^
          (2 *
            (R324NestedCrossResidualPrefix.initial
              κp κm π).remainingOrder) *
        (∫ v,
          terminal.initialNestedMarkedPhysicalCore
            π selected L x y z w v
          ∂Measure.pi fun _ :
            terminal.NestedCoordinate π => paperMeasure)‖ ≤
      ∫ v,
        terminal.initialNestedWeightedNormDensity
          π selected L x y z w v
        ∂Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure := by
  rw [terminal.norm_complexInitialWeight_mul_integral_eq
    π selected L x y z w]
  exact
    terminal.initialWeight_mul_norm_integral_le_integral_weightedNorm
      π selected L x y z w

end R324TwoHalfTerminalData

/-! ## An endpoint-preserving local factorization certificate -/

namespace R324NestedCrossTerminalPayload

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

@[simp]
theorem ofContext_unscaledDensity
    (lam ε : ℝ)
    (step : R324NestedCrossStepContext κp κm π)
    (context :
      T4 → T4 → T4 → T4 →
        (step.SurvivingCoordinate → T4) → ℝ)
    (x y z w : T4) :
    (ofContext lam ε step context x y z w).unscaledDensity =
      context x y z w :=
  rfl

@[simp]
theorem ofContext_density
    (lam ε : ℝ)
    (step : R324NestedCrossStepContext κp κm π)
    (context :
      T4 → T4 → T4 → T4 →
        (step.SurvivingCoordinate → T4) → ℝ)
    (x y z w : T4) :
    (ofContext lam ε step context x y z w).density =
      fun v =>
        lamEps lam ε ^ (2 * step.residual.remainingOrder) *
          context x y z w v :=
  rfl

end R324NestedCrossTerminalPayload

namespace R324NestedCrossStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- Pull an a.e. comparison on the next suffix back to the current
surviving carrier.  This is the measure-theoretic step needed to compose
honest one-head comparisons; it is not an additional majorization
hypothesis. -/
theorem ae_post_comp_le
    (ctx : R324NestedCrossStepContext κp κm π)
    {f g : (ctx.PostCoordinate → T4) → ℝ}
    (hfg :
      f ≤ᵐ[
        Measure.pi fun _ :
          ctx.PostCoordinate => paperMeasure]
        g) :
    (fun v : ctx.SurvivingCoordinate → T4 =>
        f (fun i => v (ctx.postSurvivingCoordinate i))) ≤ᵐ[
      Measure.pi fun _ :
        ctx.SurvivingCoordinate => paperMeasure]
      fun v =>
        g (fun i => v (ctx.postSurvivingCoordinate i)) := by
  have hprod :
      ∀ᵐ p :
          (Fin (2 * ctx.order) → T4) ×
            (ctx.PostCoordinate → T4)
          ∂((Measure.pi fun _ :
              Fin (2 * ctx.order) => paperMeasure).prod
            (Measure.pi fun _ :
              ctx.PostCoordinate => paperMeasure)),
        f p.2 ≤ g p.2 :=
    Measure.quasiMeasurePreserving_snd.tendsto_ae hfg
  have hpull :=
    ctx.measurePreserving_splitSurvivingPiMeasurableEquiv
      |>.quasiMeasurePreserving.tendsto_ae hprod
  filter_upwards [hpull] with v hv
  change
    f (ctx.splitSurvivingPiMeasurableEquiv v).2 ≤
      g (ctx.splitSurvivingPiMeasurableEquiv v).2 at hv
  have hsnd :
      (ctx.splitSurvivingPiMeasurableEquiv v).2 =
        fun i => v (ctx.postSurvivingCoordinate i) := by
    funext i
    exact ctx.splitSurvivingPiMeasurableEquiv_apply_snd v i
  simpa only [hsnd] using hv

end R324NestedCrossStepContext

/-- A local, a.e. physical factorization along the proper prefix before a
chosen stop carrier.

The `source` field is the physical density still to be controlled at the
current suffix.  The `majorant` field is forced constructor-by-constructor
to be the canonical run density.  At `stop`, its context still receives
all four external endpoints.  Integrability is stored recursively so every
suffix needed by the later Bochner/Fubini iteration is available. -/
inductive R324NestedCrossContextFactorization
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (stopCarrier : Finset (Fin (2 * m)))
    (x y z w : T4) :
    (res : R324NestedCrossResidualPrefix κp κm π) →
    (({i : Fin (2 * m) // i ∈ res.activeCarrier} → T4) → ℝ) →
    (({i : Fin (2 * m) // i ∈ res.activeCarrier} → T4) → ℝ) →
    ℕ → ℕ → Prop
  | stop
      (step : R324NestedCrossStepContext κp κm π)
      (hstop : step.head.carrier = stopCarrier)
      (context :
        T4 → T4 → T4 → T4 →
          (step.SurvivingCoordinate → T4) → ℝ)
      (source :
        (step.SurvivingCoordinate → T4) → ℝ)
      (hcontext :
        ∀ v, 0 ≤ context x y z w v)
      (hmajorant :
        Integrable
          (R324NestedCrossTerminalPayload.ofContext
            lam ε step context x y z w).density
          (Measure.pi fun _ :
            step.SurvivingCoordinate => paperMeasure))
      (hle :
        source ≤ᵐ[
          Measure.pi fun _ :
            step.SurvivingCoordinate => paperMeasure]
          (R324NestedCrossTerminalPayload.ofContext
            lam ε step context x y z w).density) :
      R324NestedCrossContextFactorization
        ρ lam ε stopCarrier x y z w
        step.residual source
        (R324NestedCrossTerminalPayload.ofContext
          lam ε step context x y z w).density
        0 step.residual.remainingOrder
  | proper
      (ctx : R324NestedCrossProperStepContext κp κm π)
      (hhead : ctx.step.head.carrier ≠ stopCarrier)
      (source :
        (ctx.step.SurvivingCoordinate → T4) → ℝ)
      (nextSource nextMajorant :
        (ctx.step.PostCoordinate → T4) → ℝ)
      (nextPrefixOrder terminalOrder : ℕ)
      (next :
        R324NestedCrossContextFactorization
          ρ lam ε stopCarrier x y z w
          ctx.step.next nextSource nextMajorant
          nextPrefixOrder terminalOrder)
      (hle :
        source ≤ᵐ[
          Measure.pi fun _ :
            ctx.step.SurvivingCoordinate => paperMeasure]
          fun v =>
            ctx.step.normalizedHeadDensity ρ lam ε
                (fun j =>
                  v (ctx.step.headSurvivingCoordinate j)) *
              ctx.connector
                (fun j =>
                  v (ctx.step.headSurvivingCoordinate j))
                (fun i =>
                  v (ctx.step.postSurvivingCoordinate i)) *
              nextSource
                (fun i =>
                  v (ctx.step.postSurvivingCoordinate i)))
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
      R324NestedCrossContextFactorization
        ρ lam ε stopCarrier x y z w
        ctx.step.residual source
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
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {stopCarrier : Finset (Fin (2 * m))}
    {x y z w : T4}
    {res : R324NestedCrossResidualPrefix κp κm π}
    {source majorant :
      (({i : Fin (2 * m) // i ∈ res.activeCarrier} → T4) → ℝ)}
    {prefixOrder terminalOrder : ℕ}

/-- Forgetting the physical comparison leaves exactly the canonical
proper-prefix run consumed by the cross iteration. -/
theorem toProperPrefixRun
    (factorization :
      R324NestedCrossContextFactorization
        ρ lam ε stopCarrier x y z w
        res source majorant prefixOrder terminalOrder) :
    R324NestedCrossProperPrefixRun
      ρ lam ε stopCarrier res majorant
      prefixOrder terminalOrder := by
  induction factorization with
  | stop step hstop context source hcontext hmajorant hle =>
      exact
        R324NestedCrossProperPrefixRun.stop
          step hstop
          (R324NestedCrossTerminalPayload.ofContext
            lam ε step context x y z w)
  | proper ctx hhead source nextSource nextMajorant
      nextPrefixOrder terminalOrder next hle hmajorant ih =>
      exact
        R324NestedCrossProperPrefixRun.proper
          ctx hhead nextMajorant
          nextPrefixOrder terminalOrder ih

/-- The source-to-majorant comparison obtained by composing the honest
one-head comparison with the recursively generated next-suffix
comparison. -/
theorem ae_le
    (factorization :
      R324NestedCrossContextFactorization
        ρ lam ε stopCarrier x y z w
        res source majorant prefixOrder terminalOrder) :
    source ≤ᵐ[
      Measure.pi fun _ :
        {i : Fin (2 * m) // i ∈ res.activeCarrier} =>
          paperMeasure]
      majorant := by
  induction factorization with
  | stop step hstop context source hcontext hmajorant hle =>
      exact hle
  | proper ctx hhead source nextSource nextMajorant
      nextPrefixOrder terminalOrder next hle hmajorant ih =>
      have hnext :=
        ctx.step.ae_post_comp_le ih
      filter_upwards [hle, hnext] with v hv hnextv
      exact hv.trans
        (mul_le_mul_of_nonneg_left hnextv
          (mul_nonneg
            (ctx.step.normalizedHeadDensity_nonneg
              ρ lam ε _)
            (ctx.connector_nonneg _ _)))

/-- Integrability is retained at every suffix, not merely at the initial
carrier.  This is the recursive datum required by the proper-head
Bochner/Fubini iteration. -/
theorem majorant_integrable
    (factorization :
      R324NestedCrossContextFactorization
        ρ lam ε stopCarrier x y z w
        res source majorant prefixOrder terminalOrder) :
    Integrable majorant
      (Measure.pi fun _ :
        {i : Fin (2 * m) // i ∈ res.activeCarrier} =>
          paperMeasure) := by
  cases factorization with
  | stop step hstop context source hcontext hmajorant hle =>
      exact hmajorant
  | proper ctx hhead source nextSource nextMajorant
      nextPrefixOrder terminalOrder next hle hmajorant =>
      exact hmajorant

/-- Every canonical majorant produced by the certificate is pointwise
nonnegative. -/
theorem majorant_nonneg
    (factorization :
      R324NestedCrossContextFactorization
        ρ lam ε stopCarrier x y z w
        res source majorant prefixOrder terminalOrder) :
    ∀ v, 0 ≤ majorant v := by
  induction factorization with
  | stop step hstop context source hcontext hmajorant hle =>
      intro v
      unfold R324NestedCrossTerminalPayload.density
      exact mul_nonneg
        ((even_two_mul
          step.residual.remainingOrder).pow_nonneg _)
        (hcontext v)
  | proper ctx hhead source nextSource nextMajorant
      nextPrefixOrder terminalOrder next hle hmajorant ih =>
      intro v
      exact mul_nonneg
        (mul_nonneg
          (ctx.step.normalizedHeadDensity_nonneg ρ lam ε _)
          (ctx.connector_nonneg _ _))
        (ih _)

end R324NestedCrossContextFactorization

/-! ## The initial package and its integral-level consumer -/

/-- Complete factorization datum at the output of the exact two-half
bridge, including the local certificate and its suffix-by-suffix
integrability data. -/
structure R324InitialNestedContextFactorization
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (terminal :
      R324TwoHalfTerminalData ρ lam ε κp κm)
    (L : ℝ) (x y z w : T4) where
  majorant :
    (terminal.NestedCoordinate π → T4) → ℝ
  prefixOrder : ℕ
  terminalOrder : ℕ
  factorization :
    R324NestedCrossContextFactorization
      ρ lam ε
      (r324MarkedResidualBlock κp κm π selected)
      x y z w
      (R324NestedCrossResidualPrefix.initial κp κm π)
      (terminal.initialNestedWeightedNormDensity
        π selected L x y z w)
      majorant prefixOrder terminalOrder

namespace R324InitialNestedContextFactorization

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {selected : R324ResidualCovarianceSlot κp}
    {terminal :
      R324TwoHalfTerminalData ρ lam ε κp κm}
    {L : ℝ} {x y z w : T4}

/-- The packaged majorant carries the canonical stop-at-marked run. -/
theorem toProperPrefixRun
    (factorization :
      R324InitialNestedContextFactorization
        ρ lam ε κp κm π selected terminal L x y z w) :
    R324NestedCrossProperPrefixRun
      ρ lam ε
      (r324MarkedResidualBlock κp κm π selected)
      (R324NestedCrossResidualPrefix.initial κp κm π)
      factorization.majorant
      factorization.prefixOrder factorization.terminalOrder :=
  factorization.factorization.toProperPrefixRun

/-- Initial-carrier integrability, projected from the recursive
suffix-by-suffix certificate. -/
theorem majorant_integrable
    (factorization :
      R324InitialNestedContextFactorization
        ρ lam ε κp κm π selected terminal L x y z w) :
    Integrable factorization.majorant
      (Measure.pi fun _ :
        terminal.NestedCoordinate π => paperMeasure) :=
  factorization.factorization.majorant_integrable

/-- Initial canonical majorant is pointwise nonnegative. -/
theorem majorant_nonneg
    (factorization :
      R324InitialNestedContextFactorization
        ρ lam ε κp κm π selected terminal L x y z w) :
    ∀ v, 0 ≤ factorization.majorant v :=
  factorization.factorization.majorant_nonneg

/-- The exact perturbative weight splits into the proper-prefix order and
the terminal marked/suffix order recorded by the canonical run. -/
theorem prefixOrder_add_terminalOrder
    (factorization :
      R324InitialNestedContextFactorization
        ρ lam ε κp κm π selected terminal L x y z w) :
    factorization.prefixOrder + factorization.terminalOrder =
      (R324NestedCrossResidualPrefix.initial
        κp κm π).remainingOrder :=
  factorization.toProperPrefixRun.remainingOrder_eq.symm

/-- Main integral-level handoff.  It keeps the four external endpoints in
the terminal payload while allowing every earlier proper block to be
consumed by the canonical cross iteration. -/
theorem initialWeight_mul_norm_integral_le_majorant
    (factorization :
      R324InitialNestedContextFactorization
        ρ lam ε κp κm π selected terminal L x y z w)
    (hphysical :
      Integrable
        (terminal.initialNestedMarkedPhysicalCore
          π selected L x y z w)
        (Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure)) :
    lamEps lam ε ^
          (2 *
            (R324NestedCrossResidualPrefix.initial
              κp κm π).remainingOrder) *
        ‖∫ v,
            terminal.initialNestedMarkedPhysicalCore
              π selected L x y z w v
            ∂Measure.pi fun _ :
              terminal.NestedCoordinate π => paperMeasure‖ ≤
      ∫ v, factorization.majorant v
        ∂Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure := by
  have hsource :
      Integrable
        (terminal.initialNestedWeightedNormDensity
          π selected L x y z w)
        (Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure) :=
    terminal.integrable_initialNestedWeightedNormDensity
      π selected L x y z w hphysical
  exact
    (terminal.initialWeight_mul_norm_integral_le_integral_weightedNorm
      π selected L x y z w).trans
      (integral_mono_ae
        hsource factorization.majorant_integrable
        factorization.factorization.ae_le)

/-- Consumer-facing complex form of the same endpoint-preserving handoff. -/
theorem norm_complexInitialWeight_mul_integral_le_majorant
    (factorization :
      R324InitialNestedContextFactorization
        ρ lam ε κp κm π selected terminal L x y z w)
    (hphysical :
      Integrable
        (terminal.initialNestedMarkedPhysicalCore
          π selected L x y z w)
        (Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure)) :
    ‖(lamEps lam ε : ℂ) ^
          (2 *
            (R324NestedCrossResidualPrefix.initial
              κp κm π).remainingOrder) *
        (∫ v,
          terminal.initialNestedMarkedPhysicalCore
            π selected L x y z w v
          ∂Measure.pi fun _ :
            terminal.NestedCoordinate π => paperMeasure)‖ ≤
      ∫ v, factorization.majorant v
        ∂Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure := by
  rw [terminal.norm_complexInitialWeight_mul_integral_eq
    π selected L x y z w]
  exact
    factorization.initialWeight_mul_norm_integral_le_majorant hphysical

end R324InitialNestedContextFactorization

end

end Anderson4D
