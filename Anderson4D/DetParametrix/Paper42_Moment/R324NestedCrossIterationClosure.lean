import Anderson4D.DetParametrix.Paper42_Moment.R324NestedCrossQuantitativeStep
import Anderson4D.DetParametrix.Paper42_Moment.R324SignedPhaseAOneBlockUpdate
import Anderson4D.DetParametrix.Paper42_Moment.R324PrimitiveIterationClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324MarkerPreservingResidualCollapse
import Anderson4D.DetParametrix.Paper42_Moment.R324TwoHalfToNestedCrossBridge

/-!
# Exact suffix iteration for the nested cross blocks in R-324

Paper §4.2 Step 3 successively removes the proper cross-cut primitive
blocks from inside to outside until it reaches the block carrying the
selected projected covariance.  This file keeps the two logically
different inputs separate:

* an upstream bridge first takes the honest norm/edge majorants of the
  post-two-half physical fibre and exposes the resulting proper prefix
  together with an explicit four-endpoint context;
* the iteration below performs the exact coordinate/Fubini transitions,
  applies Proposition 4.1 only to unmarked proper heads, and returns the
  complete marked/endpoint payload to the Step 4 routing machinery.

The elementary critical convolution between two inverse-square connector
edges and the inserted majorant is exposed as a local analytic provider.
It is not a final R-324 estimate and its constant may depend on the fixed
support constant, but is uniform in the schedule, order, scale and
endpoints.
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

/-! ## Translation of the genuine cross-gap term -/

/-- Translation of every standard block coordinate by the same torus
point. -/
def blockTranslation
    (ctx : R324NestedCrossStepContext κp κm π)
    (a : T4) :
    (Fin (2 * ctx.order) → T4) ≃ᵐ
      (Fin (2 * ctx.order) → T4) :=
  MeasurableEquiv.piCongrRight fun _ =>
    MeasurableEquiv.addRight a

@[simp]
theorem blockTranslation_apply
    (ctx : R324NestedCrossStepContext κp κm π)
    (a : T4) (x : Fin (2 * ctx.order) → T4) :
    ctx.blockTranslation a x = fun i => x i + a := by
  rfl

theorem measurePreserving_blockTranslation
    (ctx : R324NestedCrossStepContext κp κm π)
    (a : T4) :
    MeasurePreserving
      (ctx.blockTranslation a)
      (Measure.pi fun _ : Fin (2 * ctx.order) =>
        paperMeasure)
      (Measure.pi fun _ : Fin (2 * ctx.order) =>
        paperMeasure) := by
  change
    MeasurePreserving
      (fun x i => x i + a)
      (Measure.pi fun _ : Fin (2 * ctx.order) =>
        paperMeasure)
      (Measure.pi fun _ : Fin (2 * ctx.order) =>
        paperMeasure)
  exact
    measurePreserving_pi
      (fun _ : Fin (2 * ctx.order) => paperMeasure)
      (fun _ : Fin (2 * ctx.order) => paperMeasure)
      (f := fun _ x => x + a) fun _ => by
        rw [paperMeasure_eq_volume]
        exact
          measurePreserving_add_right
            (volume : Measure T4) a

theorem primitiveChainProduct_add_const
    (ctx : R324NestedCrossStepContext κp κm π)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (x : Fin (2 * ctx.order) → T4) (a : T4) :
    primitiveChainProduct ctx.order ctx.one_le_order G
        (fun i => x i + a) =
      primitiveChainProduct ctx.order ctx.one_le_order G x := by
  unfold primitiveChainProduct
  apply Finset.prod_congr rfl
  intro j _hj
  rw [add_sub_add_right_eq_sub]

theorem primitiveCovarianceProduct_add_const
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (x : Fin (2 * ctx.order) → T4) (a : T4) :
    primitiveCovarianceProduct ρ ε ctx.order
        ctx.blockPairing (fun i => x i + a) =
      primitiveCovarianceProduct ρ ε ctx.order
        ctx.blockPairing x := by
  unfold primitiveCovarianceProduct
  apply Finset.prod_congr rfl
  intro i _hi
  rw [add_sub_add_right_eq_sub]

theorem primitiveIntegrand_add_const
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (x : Fin (2 * ctx.order) → T4) (a : T4) :
    primitiveIntegrand ρ ε ctx.order ctx.one_le_order
        G ctx.blockPairing (fun i => x i + a) =
      primitiveIntegrand ρ ε ctx.order ctx.one_le_order
        G ctx.blockPairing x := by
  unfold primitiveIntegrand
  rw [ctx.primitiveChainProduct_add_const,
    ctx.primitiveCovarianceProduct_add_const]

theorem crossGapPrimitiveIntegrand_add_const
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (x : Fin (2 * ctx.order) → T4) (a : T4) :
    ctx.crossGapPrimitiveIntegrand ρ ε G
        (fun i => x i + a) =
      ctx.crossGapPrimitiveIntegrand ρ ε G x := by
  unfold crossGapPrimitiveIntegrand
  rw [add_sub_add_right_eq_sub,
    ctx.primitiveIntegrand_add_const]

/-- Internal coordinates of a primitive block translated simultaneously. -/
def internalTranslation
    (ctx : R324NestedCrossStepContext κp κm π)
    (a : T4) :
    (Fin (2 * ctx.order - 2) → T4) ≃ᵐ
      (Fin (2 * ctx.order - 2) → T4) :=
  MeasurableEquiv.piCongrRight fun _ =>
    MeasurableEquiv.addRight a

theorem measurePreserving_internalTranslation
    (ctx : R324NestedCrossStepContext κp κm π)
    (a : T4) :
    MeasurePreserving
      (ctx.internalTranslation a)
      (Measure.pi fun _ : Fin (2 * ctx.order - 2) =>
        paperMeasure)
      (Measure.pi fun _ : Fin (2 * ctx.order - 2) =>
        paperMeasure) := by
  change
    MeasurePreserving
      (fun x i => x i + a)
      (Measure.pi fun _ : Fin (2 * ctx.order - 2) =>
        paperMeasure)
      (Measure.pi fun _ : Fin (2 * ctx.order - 2) =>
        paperMeasure)
  exact
    measurePreserving_pi
      (fun _ : Fin (2 * ctx.order - 2) => paperMeasure)
      (fun _ : Fin (2 * ctx.order - 2) => paperMeasure)
      (f := fun _ x => x + a) fun _ => by
        rw [paperMeasure_eq_volume]
        exact
          measurePreserving_add_right
            (volume : Measure T4) a

/-- The genuine central-gap primitive term depends only on the endpoint
difference.  This is an exact Haar change of variables, not a law-level or
pointwise-majorant replacement. -/
theorem crossGapPrimitiveTerm_eq_diff
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (z w : T4) :
    ctx.crossGapPrimitiveTerm ρ lam ε G z w =
      ctx.crossGapPrimitiveTerm ρ lam ε G (z - w) 0 := by
  unfold crossGapPrimitiveTerm
  congr 1
  let f :
      (Fin (2 * ctx.order - 2) → T4) → ℝ :=
    fun u =>
      ctx.crossGapPrimitiveIntegrand ρ ε G
        (primitiveAssemble
          ctx.order ctx.one_le_order z w u)
  have hp :=
    ctx.measurePreserving_internalTranslation w
  calc
    (∫ u, f u
        ∂Measure.pi fun _ : Fin (2 * ctx.order - 2) =>
          paperMeasure) =
      ∫ u, f (ctx.internalTranslation w u)
        ∂Measure.pi fun _ : Fin (2 * ctx.order - 2) =>
          paperMeasure := by
      exact (hp.integral_comp' f).symm
    _ =
      ∫ u,
        ctx.crossGapPrimitiveIntegrand ρ ε G
          (primitiveAssemble
            ctx.order ctx.one_le_order (z - w) 0 u)
        ∂Measure.pi fun _ : Fin (2 * ctx.order - 2) =>
          paperMeasure := by
      apply integral_congr_ae
      filter_upwards with u
      dsimp only [f, internalTranslation]
      have hassemble :=
        primitiveAssemble_add_const
          ctx.order ctx.one_le_order
          (z - w) 0 w
          u
      have hend :
          z - w + w = z := by simp
      rw [hend, zero_add] at hassemble
      change
        ctx.crossGapPrimitiveIntegrand ρ ε G
            (primitiveAssemble ctx.order ctx.one_le_order
              z w (fun i => u i + w)) =
          ctx.crossGapPrimitiveIntegrand ρ ε G
            (primitiveAssemble ctx.order ctx.one_le_order
              (z - w) 0 u)
      rw [hassemble]
      exact
        ctx.crossGapPrimitiveIntegrand_add_const
          ρ ε G
          (primitiveAssemble
            ctx.order ctx.one_le_order
            (z - w) 0 u)
          w

/-! ## Canonical normalized density for a literal cross block -/

/-- The normalized inverse-square input on every internal edge of a
literal cross block.  Heterogeneous physical edge scales are extracted
outside this normalized density and propagated separately below. -/
def normalizedInput
    (ctx : R324NestedCrossStepContext κp κm π) :
    Fin (2 * ctx.order - 1) → T4 → ℝ :=
  fun _ => invSqKer

/-- The exact coupled central-gap density on all standard coordinates of
one literal block. -/
def normalizedHeadDensity
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (t : Fin (2 * ctx.order) → T4) : ℝ :=
  lamEps lam ε ^ (2 * ctx.order) *
    ctx.crossGapPrimitiveIntegrand
      ρ ε ctx.normalizedInput t

end R324NestedCrossStepContext

/-! ## Honest norm boundary from the physical two-half bridge -/

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal :
      R324TwoHalfTerminalData ρ lam ε κp κm)

/-- The first real nonnegative density after the endpoint-explicit complex
physical bridge.  No Green edge or covariance has yet been replaced. -/
def initialNestedMarkedNormDensity
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4)
    (v : terminal.NestedCoordinate π → T4) : ℝ :=
  ‖terminal.initialNestedMarkedPhysicalCore
      π selected L x y z w v‖

theorem initialNestedMarkedNormDensity_nonneg
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4)
    (v : terminal.NestedCoordinate π → T4) :
    0 ≤ terminal.initialNestedMarkedNormDensity
      π selected L x y z w v :=
  norm_nonneg _

theorem integrable_initialNestedMarkedNormDensity
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
      (terminal.initialNestedMarkedNormDensity
        π selected L x y z w)
      (Measure.pi fun _ :
        terminal.NestedCoordinate π => paperMeasure) := by
  exact hphysical.norm

/-- Taking the norm occurs only after the complete endpoint-explicit
physical integral. -/
theorem norm_integral_initialNestedMarkedPhysicalCore_le
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4) :
    ‖∫ v,
        terminal.initialNestedMarkedPhysicalCore
          π selected L x y z w v
        ∂Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure‖ ≤
      ∫ v,
        terminal.initialNestedMarkedNormDensity
          π selected L x y z w v
        ∂Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure := by
  exact
    norm_integral_le_integral_norm
      (fun v =>
        terminal.initialNestedMarkedPhysicalCore
          π selected L x y z w v)

/-- Honest consumer for a later a.e. edgewise majorization.  The
majorization is intentionally a.e. because the inserted
`distance² × invSqKer` factors are totalized to zero on the diagonal. -/
theorem norm_integral_initialNestedMarkedPhysicalCore_le_of_ae_majorant
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4)
    (majorant :
      (terminal.NestedCoordinate π → T4) → ℝ)
    (hphysical :
      Integrable
        (terminal.initialNestedMarkedPhysicalCore
          π selected L x y z w)
        (Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure))
    (hmajorant :
      Integrable majorant
        (Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure))
    (hle :
      terminal.initialNestedMarkedNormDensity
          π selected L x y z w ≤ᵐ[
        Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure]
        majorant) :
    ‖∫ v,
        terminal.initialNestedMarkedPhysicalCore
          π selected L x y z w v
        ∂Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure‖ ≤
      ∫ v, majorant v
        ∂Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure := by
  exact
    (terminal.norm_integral_initialNestedMarkedPhysicalCore_le
      π selected L x y z w).trans
      (integral_mono_ae hphysical.norm hmajorant hle)

/-- Exact norm ledger before any canonical inverse-square majorization.
The four external endpoints remain inside the two terminal chain factors,
and the selected projected covariance remains inside the marked physical
product. -/
theorem initialNestedMarkedNormDensity_eq_terminalFactors
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4)
    (v : terminal.NestedCoordinate π → T4) :
    terminal.initialNestedMarkedNormDensity
        π selected L x y z w v =
      |terminal.left.residualIntegrand ρ ε x y
          (terminal.left.reconstruct
            ((terminal.terminalProductPiMeasurableEquivNested π).symm
              v).1)| *
        |terminal.right.residualIntegrand ρ ε z w
          (terminal.right.reconstruct
            ((terminal.terminalProductPiMeasurableEquivNested π).symm
              v).2)| *
        ‖ρ.r324MarkedPairingCovarianceProductOn ε L
          (momentCombinedPairing κp κm π)
          (r324ResidualMarkedLowerEndpoint selected)
          (momentResidualActive κp κm)
          (terminal.terminalDoubledReconstruct
            ((terminal.terminalProductPiMeasurableEquivNested π).symm
              v))‖ := by
  unfold initialNestedMarkedNormDensity
    initialNestedMarkedPhysicalCore
    terminalMarkedPhysicalCore
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]

end R324TwoHalfTerminalData

/-! ## The canonical nonnegative residual density -/

namespace R324NestedCrossResidualPrefix

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- The proof-relevant head context attached to a literal nonempty suffix. -/
def headContext
    (res : R324NestedCrossResidualPrefix κp κm π)
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining : res.remaining = head :: tail) :
    R324NestedCrossStepContext κp κm π where
  residual := res
  head := head
  tail := tail
  remaining_eq := hremaining

end R324NestedCrossResidualPrefix

/-- A nonterminal literal head together with the next outer cross block.
The two connector edges of paper Step 3 run from the endpoints of `head`
to the central-gap coordinates of `nextHead`. -/
structure R324NestedCrossProperStepContext
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) where
  step : R324NestedCrossStepContext κp κm π
  nextHead : R324NestedCrossBlock κp κm π
  rest : List (R324NestedCrossBlock κp κm π)
  tail_eq : step.tail = nextHead :: rest

namespace R324NestedCrossProperStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- The next literal head context after deleting the current head. -/
def nextContext
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    R324NestedCrossStepContext κp κm π where
  residual := ctx.step.next
  head := ctx.nextHead
  tail := ctx.rest
  remaining_eq := by
    simpa only [
      R324NestedCrossStepContext.next,
      R324NestedCrossResidualPrefix.afterHead_remaining] using
      ctx.tail_eq

/-- The inner-left coordinate of the next outer shell, viewed in the
post-head carrier. -/
def nextLeftPostCoordinate
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    ctx.step.PostCoordinate :=
  ⟨ctx.nextHead.leftGap,
    ctx.nextContext.head_subset_activeCarrier
      ctx.nextHead.leftGap_mem⟩

/-- The inner-right coordinate of the next outer shell, viewed in the
post-head carrier. -/
def nextRightPostCoordinate
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    ctx.step.PostCoordinate :=
  ⟨ctx.nextHead.rightGap,
    ctx.nextContext.head_subset_activeCarrier
      ctx.nextHead.rightGap_mem⟩

/-- The two genuine chain edges connecting the current block to the next
outer shell. -/
def connector
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (t : Fin (2 * ctx.step.order) → T4)
    (v : ctx.step.PostCoordinate → T4) : ℝ :=
  invSqKer
      (v ctx.nextLeftPostCoordinate -
        t ⟨0, by
          have horder := ctx.step.one_le_order
          omega⟩) *
    invSqKer
      (t (primitiveLast
        ctx.step.order ctx.step.one_le_order) -
        v ctx.nextRightPostCoordinate)

theorem connector_nonneg
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (t : Fin (2 * ctx.step.order) → T4)
    (v : ctx.step.PostCoordinate → T4) :
    0 ≤ ctx.connector t v :=
  mul_nonneg (invSqKer_nonneg _) (invSqKer_nonneg _)

theorem connector_measurable
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (post : ctx.step.PostCoordinate → T4) :
    Measurable
      (fun t : Fin (2 * ctx.step.order) → T4 =>
        ctx.connector t post) := by
  unfold connector
  apply Measurable.mul
  · exact
      measurable_invSqKer.comp
        (measurable_const.sub
          (measurable_pi_apply
            (⟨0, by
              have horder := ctx.step.one_le_order
              omega⟩ : Fin (2 * ctx.step.order))))
  · exact
      measurable_invSqKer.comp
        ((measurable_pi_apply
          (primitiveLast
            ctx.step.order ctx.step.one_le_order)).sub
          measurable_const)

/-- Joint measurability of the two connector edges in head/post
coordinates. -/
theorem connector_joint_measurable
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    Measurable
      (fun p :
          (Fin (2 * ctx.step.order) → T4) ×
            (ctx.step.PostCoordinate → T4) =>
        ctx.connector p.1 p.2) := by
  unfold connector
  apply Measurable.mul
  · exact
      measurable_invSqKer.comp
        (((measurable_pi_apply
            ctx.nextLeftPostCoordinate).comp
          measurable_snd).sub
        ((measurable_pi_apply
            (⟨0, by
              have horder := ctx.step.one_le_order
              omega⟩ : Fin (2 * ctx.step.order))).comp
          measurable_fst))
  · exact
      measurable_invSqKer.comp
        (((measurable_pi_apply
            (primitiveLast
              ctx.step.order ctx.step.one_le_order)).comp
          measurable_fst).sub
        ((measurable_pi_apply
            ctx.nextRightPostCoordinate).comp
          measurable_snd))

/-- The exact endpoint integral produced after the internal coordinates of
one proper cross block have been integrated. -/
def properHeadIntegral
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (left right : T4) : ℝ :=
  ∫ p : T4 × T4,
    invSqKer (left - p.1) *
      ctx.step.crossGapPrimitiveTerm
        ρ lam ε ctx.step.normalizedInput
        (p.1 - p.2) 0 *
      invSqKer (p.2 - right)
    ∂(paperMeasure.prod paperMeasure)

theorem properHeadIntegral_nonneg
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (left right : T4) :
    0 ≤ ctx.properHeadIntegral ρ lam ε left right := by
  exact integral_nonneg fun p =>
    mul_nonneg
      (mul_nonneg
        (invSqKer_nonneg _)
        (ctx.step.crossGapPrimitiveTerm_nonneg
          ρ lam ε ctx.step.normalizedInput
          (fun _ z => invSqKer_nonneg z)
          (p.1 - p.2) 0))
      (invSqKer_nonneg _)

/-- Exact endpoint/internal Fubini identity for one proper block.  The
right side contains the genuine `crossGapPrimitiveTerm`; Proposition 4.1
has not yet been applied. -/
theorem integral_normalizedHeadDensity_mul_connector
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (post : ctx.step.PostCoordinate → T4)
    (hint :
      Integrable
        (fun t : Fin (2 * ctx.step.order) → T4 =>
          ctx.step.normalizedHeadDensity ρ lam ε t *
            ctx.connector t post)
        (Measure.pi fun _ => paperMeasure)) :
    (∫ t : Fin (2 * ctx.step.order) → T4,
        ctx.step.normalizedHeadDensity ρ lam ε t *
          ctx.connector t post
        ∂Measure.pi fun _ => paperMeasure) =
      ctx.properHeadIntegral ρ lam ε
        (post ctx.nextLeftPostCoordinate)
        (post ctx.nextRightPostCoordinate) := by
  rw [integral_standardBlock_eq_integral_endpoints_internal
    ctx.step.order ctx.step.one_le_order _ hint]
  unfold properHeadIntegral
  apply integral_congr_ae
  filter_upwards with p
  change
    (∫ u : Fin (2 * ctx.step.order - 2) → T4,
      ctx.step.normalizedHeadDensity ρ lam ε
          (primitiveAssemble
            ctx.step.order ctx.step.one_le_order
            p.1 p.2 u) *
        ctx.connector
          (primitiveAssemble
            ctx.step.order ctx.step.one_le_order
            p.1 p.2 u)
          post
      ∂Measure.pi fun _ => paperMeasure) =
    invSqKer
        (post ctx.nextLeftPostCoordinate - p.1) *
      ctx.step.crossGapPrimitiveTerm
        ρ lam ε ctx.step.normalizedInput
        (p.1 - p.2) 0 *
      invSqKer
        (p.2 - post ctx.nextRightPostCoordinate)
  have hconnector :
      ∀ u : Fin (2 * ctx.step.order - 2) → T4,
        ctx.connector
            (primitiveAssemble
              ctx.step.order ctx.step.one_le_order
              p.1 p.2 u)
            post =
          invSqKer
              (post ctx.nextLeftPostCoordinate - p.1) *
            invSqKer
              (p.2 -
                post ctx.nextRightPostCoordinate) := by
    intro u
    unfold connector
    rw [primitiveAssemble_zero,
      primitiveAssemble_last]
  simp_rw [hconnector]
  rw [integral_mul_const]
  unfold R324NestedCrossStepContext.normalizedHeadDensity
  rw [integral_const_mul]
  rw [← ctx.step.crossGapPrimitiveTerm_eq_diff
    ρ lam ε ctx.step.normalizedInput p.1 p.2]
  unfold R324NestedCrossStepContext.crossGapPrimitiveTerm
  ring

end R324NestedCrossProperStepContext

namespace R324NestedCrossStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- The normalized inverse-square edge belongs to the paper's symmetry
class. -/
theorem invSqKer_memE : MemEClassT4 invSqKer where
  perm_invariant := by
    intro σ z
    unfold invSqKer
    rw [torusDistSq_memE.perm_invariant σ z]
  even_coord := by
    intro i z
    unfold invSqKer
    rw [torusDistSq_memE.even_coord i z]

theorem normalizedInput_measurable
    (ctx : R324NestedCrossStepContext κp κm π) :
    ∀ j, Measurable (ctx.normalizedInput j) := by
  intro _j
  exact measurable_invSqKer

theorem normalizedInput_nonneg
    (ctx : R324NestedCrossStepContext κp κm π) :
    ∀ j z, 0 ≤ ctx.normalizedInput j z := by
  intro _j z
  exact invSqKer_nonneg z

theorem normalizedInput_admissible
    (ctx : R324NestedCrossStepContext κp κm π) :
    IsAdmissiblePrimitiveInput ctx.order
      ctx.normalizedInput := by
  constructor
  · intro _j
    exact invSqKer_memE
  · intro _j z
    change |invSqKer z| ≤ invSqKer z
    rw [abs_of_nonneg (invSqKer_nonneg z)]

/-- Every literal block order is bounded by the ambient perturbative
order. -/
theorem order_le_ambient
    (ctx : R324NestedCrossStepContext κp κm π) :
    ctx.order ≤ m := by
  have hcard :
      2 * ctx.order = ctx.head.carrier.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_congr ctx.blockOrderIso.toEquiv
  have hsubset :
      ctx.head.carrier.card ≤ 2 * m :=
    by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card
          (show ctx.head.carrier ⊆
              (Finset.univ : Finset (Fin (2 * m))) from
            Finset.subset_univ _)
  rw [← hcard] at hsubset
  omega

/-- On the genuine current surviving carrier, inserting the moving
central-gap numerator times its inverse-square bridge is exactly one
almost everywhere.  This is the lossless insertion used before any Green
edge is replaced by its inverse-square majorant. -/
theorem ae_centralGapCancellation_reconstruct_eq_one
    (ctx : R324NestedCrossStepContext κp κm π) :
    ∀ᵐ v : ctx.SurvivingCoordinate → T4
        ∂(Measure.pi fun _ => paperMeasure),
      ctx.head.centralGapNumerator (ctx.reconstruct v) *
          invSqKer
            (ctx.reconstruct v ctx.head.leftGap -
              ctx.reconstruct v ctx.head.rightGap) =
        1 := by
  have hcard : 0 < 2 * ctx.order := by
    have horder := ctx.one_le_order
    omega
  have hhead :
      ∀ᵐ t : Fin (2 * ctx.order) → T4
          ∂(Measure.pi fun _ => paperMeasure),
        t ctx.leftGapIndex ≠
          t ctx.rightGapIndex :=
    ae_pi_eval_ne_eval_of_pos
      hcard ctx.leftGapIndex ctx.rightGapIndex
      ctx.leftGapIndex_ne_rightGapIndex
  have hprod :
      ∀ᵐ p :
          (Fin (2 * ctx.order) → T4) ×
            (ctx.PostCoordinate → T4)
          ∂((Measure.pi fun _ : Fin (2 * ctx.order) =>
              paperMeasure).prod
            (Measure.pi fun _ : ctx.PostCoordinate =>
              paperMeasure)),
        p.1 ctx.leftGapIndex ≠
          p.1 ctx.rightGapIndex :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae hhead
  have hpull :
      ∀ᵐ v : ctx.SurvivingCoordinate → T4
          ∂(Measure.pi fun _ => paperMeasure),
        (ctx.splitSurvivingPiMeasurableEquiv v).1
              ctx.leftGapIndex ≠
          (ctx.splitSurvivingPiMeasurableEquiv v).1
              ctx.rightGapIndex :=
    ctx.measurePreserving_splitSurvivingPiMeasurableEquiv
      |>.quasiMeasurePreserving.tendsto_ae hprod
  filter_upwards [hpull] with v hv
  apply
    ctx.head.centralGapCancellation_eq_one_of_ne
      (ctx.reconstruct v)
  have hv' :
      v (ctx.headSurvivingCoordinate
            ctx.leftGapIndex) ≠
        v (ctx.headSurvivingCoordinate
            ctx.rightGapIndex) := by
    simpa only [
      splitSurvivingPiMeasurableEquiv_apply_fst] using hv
  have hleft :
      ctx.reconstruct v ctx.head.leftGap =
        v (ctx.headSurvivingCoordinate
          ctx.leftGapIndex) := by
    have hval :
        (ctx.headSurvivingCoordinate
          ctx.leftGapIndex).1 =
            ctx.head.leftGap := by
      exact congrArg Subtype.val
        ctx.blockOrderIso_leftGapIndex
    rw [← hval, ctx.reconstruct_surviving]
  have hright :
      ctx.reconstruct v ctx.head.rightGap =
        v (ctx.headSurvivingCoordinate
          ctx.rightGapIndex) := by
    have hval :
        (ctx.headSurvivingCoordinate
          ctx.rightGapIndex).1 =
            ctx.head.rightGap := by
      exact congrArg Subtype.val
        ctx.blockOrderIso_rightGapIndex
    rw [← hval, ctx.reconstruct_surviving]
  simpa only [hleft, hright] using hv'

theorem normalizedHeadDensity_nonneg
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (t : Fin (2 * ctx.order) → T4) :
    0 ≤ ctx.normalizedHeadDensity ρ lam ε t := by
  unfold normalizedHeadDensity
  exact mul_nonneg
    ((even_two_mul ctx.order).pow_nonneg _)
    (ctx.crossGapPrimitiveIntegrand_nonneg
      ρ ε ctx.normalizedInput
      (fun _ z => invSqKer_nonneg z) t)

theorem normalizedHeadDensity_measurable
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ) :
    Measurable (ctx.normalizedHeadDensity ρ lam ε) := by
  unfold normalizedHeadDensity crossGapPrimitiveIntegrand
  apply Measurable.const_mul
  apply Measurable.mul
  · exact
      measurable_torusDistSq.comp
        ((measurable_pi_apply ctx.leftGapIndex).sub
          (measurable_pi_apply ctx.rightGapIndex))
  · exact
      measurable_primitiveIntegrand
        ρ ε ctx.order ctx.one_le_order
        ctx.normalizedInput
        ctx.normalizedInput_measurable
        ctx.blockPairing

/-- Truncation-range form of Proposition 4.1 for every normalized literal
cross head.  The constants are selected once, before the ambient order and
the residual schedule. -/
theorem exists_normalizedCrossGapTerm_le_majorant_at_truncation
    (ρ : SmoothCutoff) :
    ∃ supportConstant C : ℝ,
      0 < supportConstant ∧
      0 < C ∧
      ∀ {m : ℕ} (κp κm : PartialPairing (Fin m))
        (π : κp.singles ≃ κm.singles)
        (ctx : R324NestedCrossStepContext κp κm π)
        (lam ε : ℝ),
        0 < lam →
        0 < ε →
        ε ≤ 1 →
        m ≤ truncOrder ε →
        ∀ z : T4,
          0 ≤ ctx.crossGapPrimitiveTerm
              ρ lam ε ctx.normalizedInput z 0 ∧
          ctx.crossGapPrimitiveTerm
              ρ lam ε ctx.normalizedInput z 0 ≤
            primitiveInsertedMajorant
              C lam ε supportConstant ctx.order z := by
  obtain ⟨supportConstant, C, hsupport, hC, hprop⟩ :=
    proposition41_at_truncation ρ
  refine
    ⟨supportConstant, C, hsupport, hC, ?_⟩
  intro m κp κm π ctx lam ε
    hlam hε hε1 hmtrunc z
  have horderTrunc :
      ctx.order ≤ truncOrder ε :=
    ctx.order_le_ambient.trans hmtrunc
  have hbounds :=
    hprop lam ε ctx.order ctx.one_le_order
      ctx.normalizedInput
      hlam hε hε1 horderTrunc
      ctx.normalizedInput_admissible
  constructor
  · exact
      ctx.crossGapPrimitiveTerm_nonneg
        ρ lam ε ctx.normalizedInput
        ctx.normalizedInput_nonneg z 0
  · calc
      ctx.crossGapPrimitiveTerm
          ρ lam ε ctx.normalizedInput z 0 ≤
          primitivePairingKernelInsertedTerm
            ρ lam ε ctx.order ctx.one_le_order
            ctx.normalizedInput ctx.blockPairing z 0 :=
        ctx.crossGapPrimitiveTerm_le_insertedTerm
          ρ lam hε hε1 ctx.normalizedInput
          ctx.normalizedInput_measurable
          ctx.normalizedInput_admissible
          ctx.normalizedInput_nonneg z 0
      _ ≤
          primitiveKernelInserted
            ρ lam ε ctx.order ctx.one_le_order
            ctx.normalizedInput z 0 :=
        primitivePairingKernelInsertedTerm_le_kernel
          ρ lam ε ctx.order ctx.one_le_order
          ctx.normalizedInput ctx.normalizedInput_nonneg
          ctx.blockPairing ctx.blockPairing_mem z 0
      _ ≤
          |primitiveKernelInsertedDiff
            ρ lam ε ctx.order ctx.one_le_order
            ctx.normalizedInput z| := by
        exact le_abs_self _
      _ ≤
          primitiveInsertedMajorant
            C lam ε supportConstant ctx.order z :=
        (hbounds.2.2 z).2

/-- Standalone endpoint/internal Fubini identity for one *bare normalized*
block.  This is useful inside a proper-head calculation; it is not a
claim that the physical Step 4 terminal context can be discarded. -/
theorem integral_normalizedHeadDensity_eq_endpointTerms
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (hint :
      Integrable
        (ctx.normalizedHeadDensity ρ lam ε)
        (Measure.pi fun _ : Fin (2 * ctx.order) =>
          paperMeasure)) :
    (∫ t : Fin (2 * ctx.order) → T4,
        ctx.normalizedHeadDensity ρ lam ε t
        ∂Measure.pi fun _ => paperMeasure) =
      ∫ p : T4 × T4,
        ctx.crossGapPrimitiveTerm
          ρ lam ε ctx.normalizedInput p.1 p.2
        ∂(paperMeasure.prod paperMeasure) := by
  rw [integral_standardBlock_eq_integral_endpoints_internal
    ctx.order ctx.one_le_order _ hint]
  apply integral_congr_ae
  filter_upwards with p
  unfold normalizedHeadDensity crossGapPrimitiveTerm
  rw [integral_const_mul]

end R324NestedCrossStepContext

/-! ## Proper-prefix runs and the explicit Step 4 payload

Paper Step 3 does **not** collapse the last physical block to a bare radial
primitive term.  The four external Green edges are still attached to the
first, left-gap, right-gap and last coordinates of the remaining block.
Moreover, the block containing the selected projected covariance need not
be the last element of the unmarked schedule.

Consequently this run removes only literal proper heads which precede a
chosen stop carrier.  At that carrier it returns the complete four-endpoint
context unchanged.  The routed endpoint machinery of Step 4, rather than
this file, consumes that payload. -/

/-- A concrete four-endpoint context at the point where the proper-prefix
iteration stops.  No factorization or estimate is hidden in this record:
the eventual physical adapter must supply the actual context. -/
structure R324NestedCrossTerminalPayload
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (lam ε : ℝ)
    (step : R324NestedCrossStepContext κp κm π) where
  context :
    T4 → T4 → T4 → T4 →
      (step.SurvivingCoordinate → T4) → ℝ
  x : T4
  y : T4
  z : T4
  w : T4

namespace R324NestedCrossTerminalPayload

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {lam ε : ℝ}
    {step : R324NestedCrossStepContext κp κm π}

/-- Named constructor for a concrete terminal context and its four
external endpoints. -/
def ofContext
    (lam ε : ℝ)
    (step : R324NestedCrossStepContext κp κm π)
    (context :
      T4 → T4 → T4 → T4 →
        (step.SurvivingCoordinate → T4) → ℝ)
    (x y z w : T4) :
    R324NestedCrossTerminalPayload lam ε step where
  context := context
  x := x
  y := y
  z := z
  w := w

/-- The unscaled four-endpoint context at the stop carrier. -/
def unscaledDensity
    (payload : R324NestedCrossTerminalPayload lam ε step) :
    (step.SurvivingCoordinate → T4) → ℝ :=
  payload.context payload.x payload.y payload.z payload.w

/-- The terminal payload retains the exact perturbative weight of the
marked head and every outer suffix block.  Only the prefix before this
carrier may be charged by the proper-run constructors. -/
def density
    (payload : R324NestedCrossTerminalPayload lam ε step) :
    (step.SurvivingCoordinate → T4) → ℝ :=
  fun v =>
    lamEps lam ε ^ (2 * step.residual.remainingOrder) *
      payload.unscaledDensity v

end R324NestedCrossTerminalPayload

/-- Proof-relevant exact factorization of the *canonical majorant* on the
unmarked proper prefix before a chosen stop carrier.

The `stop` constructor deliberately leaves its four-endpoint density
opaque.  A `proper` constructor is allowed only when the current head is
not the stop carrier and records exactly
`head × two connectors × next payload`.  Thus the relation cannot
silently apply the proper convolution to the marked/terminal block.  The
separate physical adapter must justify the preceding norm and edgewise
majorization; this relation does not pretend those are equalities. -/
inductive R324NestedCrossProperPrefixRun
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (stopCarrier : Finset (Fin (2 * m))) :
    (res : R324NestedCrossResidualPrefix κp κm π) →
    (({i : Fin (2 * m) // i ∈ res.activeCarrier} → T4) → ℝ) →
    ℕ → ℕ → Prop
  | stop
      (step : R324NestedCrossStepContext κp κm π)
      (hstop : step.head.carrier = stopCarrier)
      (payload : R324NestedCrossTerminalPayload lam ε step) :
      R324NestedCrossProperPrefixRun
        ρ lam ε stopCarrier step.residual payload.density
        0 step.residual.remainingOrder
  | proper
      (ctx : R324NestedCrossProperStepContext κp κm π)
      (hhead : ctx.step.head.carrier ≠ stopCarrier)
      (nextDensity :
        (ctx.step.PostCoordinate → T4) → ℝ)
      (nextPrefixOrder terminalOrder : ℕ)
      (next :
        R324NestedCrossProperPrefixRun
          ρ lam ε stopCarrier ctx.step.next nextDensity
          nextPrefixOrder terminalOrder) :
      R324NestedCrossProperPrefixRun
        ρ lam ε stopCarrier ctx.step.residual
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
        (ctx.step.order + nextPrefixOrder) terminalOrder

namespace R324NestedCrossProperPrefixRun

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {stopCarrier : Finset (Fin (2 * m))}
    {res : R324NestedCrossResidualPrefix κp κm π}
    {density :
      ({i : Fin (2 * m) // i ∈ res.activeCarrier} → T4) → ℝ}
    {prefixOrder terminalOrder : ℕ}

/-- A proper-prefix run partitions the exact remaining cross order into
the order charged by the literal proper heads and the order retained in
the terminal four-endpoint payload. -/
theorem remainingOrder_eq
    (run :
      R324NestedCrossProperPrefixRun
        ρ lam ε stopCarrier res density prefixOrder terminalOrder) :
    res.remainingOrder = prefixOrder + terminalOrder := by
  induction run with
  | stop step _hstop payload =>
      simp only [Nat.zero_add]
  | proper ctx _hhead nextDensity nextPrefixOrder terminalOrder next ih =>
      rw [ctx.step.remainingOrder_eq_order_add_next, ih]
      omega

/-- Additive orientation of `remainingOrder_eq`, convenient for consumers
which accumulate the proper prefix from inside to outside. -/
theorem prefixOrder_add_terminalOrder
    (run :
      R324NestedCrossProperPrefixRun
        ρ lam ε stopCarrier res density prefixOrder terminalOrder) :
    prefixOrder + terminalOrder = res.remainingOrder :=
  run.remainingOrder_eq.symm

/-- Exact multiplication ledger for the perturbative weight along a
proper-prefix run. -/
theorem lamEps_pow_remainingOrder_eq
    (run :
      R324NestedCrossProperPrefixRun
        ρ lam ε stopCarrier res density prefixOrder terminalOrder) :
    lamEps lam ε ^ (2 * res.remainingOrder) =
      lamEps lam ε ^ (2 * prefixOrder) *
        lamEps lam ε ^ (2 * terminalOrder) := by
  rw [run.remainingOrder_eq]
  rw [show 2 * (prefixOrder + terminalOrder) =
      2 * prefixOrder + 2 * terminalOrder by omega]
  exact pow_add _ _ _

/-- Absolute-value form of the exact multiplication ledger, used at the
physical norm boundary. -/
theorem abs_lamEps_pow_remainingOrder_eq
    (run :
      R324NestedCrossProperPrefixRun
        ρ lam ε stopCarrier res density prefixOrder terminalOrder) :
    |lamEps lam ε| ^ (2 * res.remainingOrder) =
      |lamEps lam ε| ^ (2 * prefixOrder) *
        |lamEps lam ε| ^ (2 * terminalOrder) := by
  rw [run.remainingOrder_eq]
  rw [show 2 * (prefixOrder + terminalOrder) =
      2 * prefixOrder + 2 * terminalOrder by omega]
  exact pow_add _ _ _

end R324NestedCrossProperPrefixRun

/-- A residual suffix still contains the chosen stop carrier. -/
def R324NestedCrossResidualPrefix.ContainsCarrier
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (res : R324NestedCrossResidualPrefix κp κm π)
    (stopCarrier : Finset (Fin (2 * m))) : Prop :=
  ∃ block ∈ res.remaining,
    block.carrier = stopCarrier

/-- The initial literal nested schedule contains the unique block carrying
the selected projected covariance. -/
theorem
    R324NestedCrossResidualPrefix.initial_contains_markedCarrier
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    (R324NestedCrossResidualPrefix.initial κp κm π).ContainsCarrier
      (r324MarkedResidualBlock κp κm π selected) := by
  have hcarrier :
      r324MarkedResidualBlock κp κm π selected ∈
        (r324NestedCrossSchedule κp κm π).map
          R324NestedCrossBlock.carrier := by
    rw [r324NestedCrossSchedule_carriers]
    exact
      r324MarkedResidualBlock_mem
        κp κm π selected
  obtain ⟨block, hblock, hblockCarrier⟩ :=
    List.mem_map.mp hcarrier
  exact ⟨block, hblock, hblockCarrier⟩

/-- Structural construction of the proper-prefix trace up to a carrier
known to occur in the literal suffix.

The only supplied datum is the actual four-endpoint payload to use when
that carrier becomes the head.  No terminal majorant, scalar bound, or
radial replacement is assumed. -/
theorem exists_r324NestedCrossProperPrefixRun_of_containsCarrier
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (stopCarrier : Finset (Fin (2 * m)))
    (terminalPayload :
      ∀ (step : R324NestedCrossStepContext κp κm π),
        step.head.carrier = stopCarrier →
          R324NestedCrossTerminalPayload lam ε step)
    (res : R324NestedCrossResidualPrefix κp κm π)
    (hcontains : res.ContainsCarrier stopCarrier) :
    ∃ density :
        ({i : Fin (2 * m) // i ∈ res.activeCarrier} → T4) → ℝ,
      ∃ prefixOrder terminalOrder : ℕ,
      R324NestedCrossProperPrefixRun
        ρ lam ε stopCarrier res density prefixOrder terminalOrder := by
  cases hremaining : res.remaining with
  | nil =>
      obtain ⟨block, hblock, _hcarrier⟩ := hcontains
      simp only [hremaining, List.not_mem_nil] at hblock
  | cons head tail =>
      let step :=
        res.headContext head tail hremaining
      by_cases hhead : head.carrier = stopCarrier
      · let payload := terminalPayload step hhead
        exact
          ⟨payload.density, 0, step.residual.remainingOrder,
            R324NestedCrossProperPrefixRun.stop
              step hhead payload⟩
      · have htailContains :
            ∃ block ∈ tail,
              block.carrier = stopCarrier := by
          obtain ⟨block, hblock, hcarrier⟩ := hcontains
          rw [hremaining] at hblock
          rcases List.mem_cons.mp hblock with hblockHead | hblockTail
          · subst block
            exact False.elim (hhead hcarrier)
          · exact ⟨block, hblockTail, hcarrier⟩
        cases htail : tail with
        | nil =>
            obtain ⟨block, hblock, _hcarrier⟩ :=
              htailContains
            simp only [htail, List.not_mem_nil] at hblock
        | cons nextHead rest =>
            let proper :
                R324NestedCrossProperStepContext κp κm π :=
              { step := step
                nextHead := nextHead
                rest := rest
                tail_eq := htail }
            have hnextContains :
                step.next.ContainsCarrier stopCarrier := by
              change ∃ block ∈ tail,
                block.carrier = stopCarrier
              exact htailContains
            obtain ⟨nextDensity, nextPrefixOrder, terminalOrder, hnext⟩ :=
              exists_r324NestedCrossProperPrefixRun_of_containsCarrier
                ρ lam ε stopCarrier terminalPayload
                step.next hnextContains
            refine
              ⟨fun v =>
                  step.normalizedHeadDensity ρ lam ε
                      (fun j =>
                        v (step.headSurvivingCoordinate j)) *
                    proper.connector
                      (fun j =>
                        v (step.headSurvivingCoordinate j))
                      (fun i =>
                        v (step.postSurvivingCoordinate i)) *
                    nextDensity
                      (fun i =>
                        v (step.postSurvivingCoordinate i)),
                step.order + nextPrefixOrder,
                terminalOrder,
                ?_⟩
            exact
              R324NestedCrossProperPrefixRun.proper
                proper (by
                  change head.carrier ≠ stopCarrier
                  exact hhead)
                nextDensity nextPrefixOrder terminalOrder hnext
termination_by res.remaining.length
decreasing_by
  simp [
    R324NestedCrossResidualPrefix.headContext,
    R324NestedCrossStepContext.next,
    R324NestedCrossResidualPrefix.afterHead,
    hremaining, htail]

/-- Specialization of the structural run to the genuine block carrying
the selected projected covariance. -/
theorem exists_r324NestedCrossProperPrefixRun_to_markedCarrier
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (terminalPayload :
      ∀ (step : R324NestedCrossStepContext κp κm π),
        step.head.carrier =
            r324MarkedResidualBlock κp κm π selected →
          R324NestedCrossTerminalPayload lam ε step) :
    ∃ density :
        ({i : Fin (2 * m) //
          i ∈
            (R324NestedCrossResidualPrefix.initial
              κp κm π).activeCarrier} → T4) → ℝ,
      ∃ prefixOrder terminalOrder : ℕ,
      R324NestedCrossProperPrefixRun
        ρ lam ε
        (r324MarkedResidualBlock κp κm π selected)
        (R324NestedCrossResidualPrefix.initial κp κm π)
        density prefixOrder terminalOrder := by
  exact
    exists_r324NestedCrossProperPrefixRun_of_containsCarrier
      ρ lam ε
      (r324MarkedResidualBlock κp κm π selected)
      terminalPayload
      (R324NestedCrossResidualPrefix.initial κp κm π)
      (R324NestedCrossResidualPrefix.initial_contains_markedCarrier
        κp κm π selected)

/-! ## Exact integral transition for one proper constructor

This identity is deliberately stated before Proposition 4.1 and retains
the genuine cross-gap primitive term.  There is no terminal analogue in
this file: Step 4 must consume the explicit four-endpoint payload. -/

namespace R324NestedCrossProperStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- Integrating a proper exact-run constructor first over its current
head gives the genuine endpoint cross term times the untouched suffix
density. -/
theorem integral_exactProperDensity
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (nextDensity : (ctx.step.PostCoordinate → T4) → ℝ)
    (hcurrent :
      Integrable
        (fun w : ctx.step.SurvivingCoordinate → T4 =>
          ctx.step.normalizedHeadDensity ρ lam ε
              (fun j =>
                w (ctx.step.headSurvivingCoordinate j)) *
            ctx.connector
              (fun j =>
                w (ctx.step.headSurvivingCoordinate j))
              (fun i =>
                w (ctx.step.postSurvivingCoordinate i)) *
            nextDensity
              (fun i =>
                w (ctx.step.postSurvivingCoordinate i)))
        (Measure.pi fun _ => paperMeasure))
    (hhead :
      ∀ post : ctx.step.PostCoordinate → T4,
        Integrable
          (fun t : Fin (2 * ctx.step.order) → T4 =>
            ctx.step.normalizedHeadDensity ρ lam ε t *
              ctx.connector t post)
          (Measure.pi fun _ => paperMeasure)) :
    (∫ w : ctx.step.SurvivingCoordinate → T4,
        ctx.step.normalizedHeadDensity ρ lam ε
            (fun j =>
              w (ctx.step.headSurvivingCoordinate j)) *
          ctx.connector
            (fun j =>
              w (ctx.step.headSurvivingCoordinate j))
            (fun i =>
              w (ctx.step.postSurvivingCoordinate i)) *
          nextDensity
            (fun i =>
              w (ctx.step.postSurvivingCoordinate i))
        ∂Measure.pi fun _ => paperMeasure) =
      ∫ post : ctx.step.PostCoordinate → T4,
        ctx.properHeadIntegral ρ lam ε
            (post ctx.nextLeftPostCoordinate)
            (post ctx.nextRightPostCoordinate) *
          nextDensity post
        ∂Measure.pi fun _ => paperMeasure := by
  rw [ctx.step.integral_splitSurviving_post_first _ hcurrent]
  apply integral_congr_ae
  filter_upwards with post
  simp only [
    R324NestedCrossStepContext.splitSurvivingPiMeasurableEquiv_symm_head,
    R324NestedCrossStepContext.splitSurvivingPiMeasurableEquiv_symm_post]
  rw [integral_mul_const,
    ctx.integral_normalizedHeadDensity_mul_connector
      ρ lam ε post (hhead post)]

end R324NestedCrossProperStepContext

end

end Anderson4D
