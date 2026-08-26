import Anderson4D.DetParametrix.Paper42_Moment.R324ConcreteRefinedExpansionInstance

/-!
# Cancellation-preserving grouped route weights for R-324

The exact refined Fourier expansion groups a complete compatible primitive
fibre before taking a norm.  This module attaches the reciprocal
eighth-order cost to that grouped object, after the four endpoint
integrations and before the final countable central-frequency routing.

The endpoint-free budget below contains only integrability and summability
of the grouped internal core masses.  In particular, it does not assume the
final moment estimate.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## Reciprocal decay cost of one common-increment group -/

/-- Reciprocal eighth-order cost of one concrete grouped increment.

Unlike `r324PairDecayCost`, this cost is attached directly to the common
increment key of the whole refined group; there is no remaining raw
full-pairing index. -/
def r324GroupedIncrementCost
    {m : ℕ} (hm : 0 < m) (b : ℕ) (i : Fin m) : ℝ :=
  (1 +
    ‖z4EuclideanFrequency
      (r324NatEquivStandardConfigurations hm b i)‖ ^ 2) ^ 4

theorem r324GroupedIncrementCost_pos
    {m : ℕ} (hm : 0 < m) (b : ℕ) (i : Fin m) :
    0 < r324GroupedIncrementCost hm b i := by
  unfold r324GroupedIncrementCost
  positivity

/-- The grouped cost is exactly the reciprocal of the routed decay. -/
theorem r324GroupedIncrementCost_mul_decay
    {m : ℕ} (hm : 0 < m) (b : ℕ) (i : Fin m) :
    r324GroupedIncrementCost hm b i *
        eighthOrderFrequencyDecay
          ‖z4EuclideanFrequency
            (r324NatEquivStandardConfigurations hm b i)‖ =
      1 := by
  unfold r324GroupedIncrementCost eighthOrderFrequencyDecay
  have h :
      (1 +
        ‖z4EuclideanFrequency
          (r324NatEquivStandardConfigurations hm b i)‖ ^ 2) ^ 4 ≠
        0 := by
    positivity
  exact mul_inv_cancel₀ h

/-! ## Endpoint-free grouped base weights -/

/-- Internal `L¹` mass of one common-increment refined group.

The complete compatible primitive fibre has already been summed in
`r324KeyGroupedRefinedEndpointCore`; only then is the norm taken and
integrated over the doubled internal tuple. -/
def r324GroupedRefinedCoreL1
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m × ℕ) : ℝ :=
  ∫ v : Fin (2 * m) → T4,
    ‖ρ.r324KeyGroupedRefinedEndpointCore
      hm ε p.1 p.2 v‖
    ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)

theorem r324GroupedRefinedCoreL1_nonneg
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m × ℕ) :
    0 ≤ ρ.r324GroupedRefinedCoreL1 hm ε p := by
  unfold r324GroupedRefinedCoreL1
  exact integral_nonneg fun _ => norm_nonneg _

/-- Endpoint-free route weight of one grouped configuration.

It consists of the common coupling factor, the integrated norm of the
already-grouped primitive fibre, and one sum of reciprocal routed costs.
No external Fourier mode or endpoint loss occurs in this definition. -/
def r324GroupedRouteBaseWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m × ℕ) : ℝ :=
  |lamEps lam ε| ^ (2 * m) *
    ρ.r324GroupedRefinedCoreL1 hm ε p *
    ∑ i : Fin m, r324GroupedIncrementCost hm p.2 i

theorem r324GroupedRouteBaseWeight_nonneg
    (lam : ℝ) {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m × ℕ) :
    0 ≤ ρ.r324GroupedRouteBaseWeight lam hm ε p := by
  unfold r324GroupedRouteBaseWeight
  exact mul_nonneg
    (mul_nonneg
      (pow_nonneg (abs_nonneg _) _)
      (ρ.r324GroupedRefinedCoreL1_nonneg hm ε p))
    (Finset.sum_nonneg fun i _ =>
      (r324GroupedIncrementCost_pos hm p.2 i).le)

/-! ## Removing the apparent second endpoint sacrifice -/

/-- The sacrificed endpoint estimate implies the same bound without an
extra `ε⁻⁸` on the left when `0 < ε ≤ 1`.

Thus the single `r324EndpointLoss` on the right is the only endpoint
scale loss passed to the routing layer. -/
theorem norm_integral_r324EndpointSeparatedIntegrand_le_endpointLoss
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (α β : Z4)
    (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags) (core : ℂ) :
    ‖∫ x, ∫ y, ∫ z, ∫ w,
        r324EndpointSeparatedIntegrand
          α β anchors flags core x y z w
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure‖ ≤
      (16 * r324EndpointLoss ε α β) * ‖core‖ := by
  have hinv : 1 ≤ ε⁻¹ :=
    (one_le_inv₀ hε).2 hε1
  have hpow : 1 ≤ ε⁻¹ ^ (8 : ℕ) :=
    one_le_pow₀ hinv
  have hnorm :
      0 ≤
        ‖∫ x, ∫ y, ∫ z, ∫ w,
          r324EndpointSeparatedIntegrand
            α β anchors flags core x y z w
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure ∂paperMeasure‖ :=
    norm_nonneg _
  calc
    ‖∫ x, ∫ y, ∫ z, ∫ w,
        r324EndpointSeparatedIntegrand
          α β anchors flags core x y z w
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure‖ =
        1 *
          ‖∫ x, ∫ y, ∫ z, ∫ w,
            r324EndpointSeparatedIntegrand
              α β anchors flags core x y z w
            ∂paperMeasure ∂paperMeasure
            ∂paperMeasure ∂paperMeasure‖ := by
      ring
    _ ≤ ε⁻¹ ^ (8 : ℕ) *
          ‖∫ x, ∫ y, ∫ z, ∫ w,
            r324EndpointSeparatedIntegrand
              α β anchors flags core x y z w
            ∂paperMeasure ∂paperMeasure
            ∂paperMeasure ∂paperMeasure‖ :=
      mul_le_mul_of_nonneg_right hpow hnorm
    _ ≤ (16 * r324EndpointLoss ε α β) * ‖core‖ :=
      sacrificed_norm_integral_r324EndpointSeparatedIntegrand_le
        ε α β anchors flags core

/-! ## Local grouped routed estimate -/

/-- A complete grouped core with integrable internal norm obeys the local
eighth-order routed estimate required by the countable central-frequency
constructor.

The zero-term branch is discharged before inspecting the artificial
frequency-conserving delta route. -/
theorem
    norm_r324GroupedEndpointConfigurationTerm_le_groupedRouteBaseWeight_mul_decay
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m × ℕ)
    (hcore :
      Integrable
        (fun v : Fin (2 * m) → T4 =>
          ‖ρ.r324KeyGroupedRefinedEndpointCore
            hm ε p.1 p.2 v‖)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure))
    (i : Fin m) :
    ‖r324GroupedEndpointConfigurationTerm
        hm ρ lam ε α β
        (r324RefinedScheduleRepresentative p.1)
        (ρ.r324KeyGroupedRefinedEndpointCore
          hm ε p.1 p.2)‖ ≤
      ((16 * r324EndpointLoss ε α β) *
          ρ.r324GroupedRouteBaseWeight lam hm ε p) *
        eighthOrderFrequencyDecay
          ‖ρ.r324ConcreteRefinedIncrement
            lam hm ε α β p i‖ := by
  by_cases hzero :
      r324GroupedEndpointConfigurationTerm
          hm ρ lam ε α β
          (r324RefinedScheduleRepresentative p.1)
          (ρ.r324KeyGroupedRefinedEndpointCore
            hm ε p.1 p.2) =
        0
  · rw [hzero, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (r324EndpointLoss_nonneg ε α β))
        (ρ.r324GroupedRouteBaseWeight_nonneg
          lam hm ε p))
      (eighthOrderFrequencyDecay_nonneg _)
  · have hincrement :
        ρ.r324ConcreteRefinedIncrement
            lam hm ε α β p i =
          z4EuclideanFrequency
            (r324NatEquivStandardConfigurations
              hm p.2 i) := by
      simp [r324ConcreteRefinedIncrement, hzero]
    rw [hincrement]
    let scale : ℝ :=
      16 * r324EndpointLoss ε α β
    let scalar : ℝ :=
      |lamEps lam ε| ^ (2 * m)
    let core :
        (Fin (2 * m) → T4) → ℂ :=
      ρ.r324KeyGroupedRefinedEndpointCore
        hm ε p.1 p.2
    let endpointIntegral :
        (Fin (2 * m) → T4) → ℂ := fun v =>
      ∫ x, ∫ y, ∫ z, ∫ w,
        r324EndpointSeparatedIntegrand α β
          (r324ContractionEndpointAnchors hm
            (r324RefinedScheduleRepresentative p.1) v)
          (r324ContractionEndpointFlags
            (r324RefinedScheduleRepresentative p.1))
          (core v) x y z w
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure
    have hscale : 0 ≤ scale := by
      dsimp only [scale]
      exact mul_nonneg (by norm_num)
        (r324EndpointLoss_nonneg ε α β)
    have hscalar : 0 ≤ scalar := by
      dsimp only [scalar]
      positivity
    have hcore' :
        Integrable (fun v => ‖core v‖)
          (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
      exact hcore
    have hmajor :
        Integrable (fun v => scale * ‖core v‖)
          (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
      simpa only [smul_eq_mul] using
        hcore'.const_mul scale
    have hpoint :
        ∀ v, ‖endpointIntegral v‖ ≤
          scale * ‖core v‖ := by
      intro v
      exact
        norm_integral_r324EndpointSeparatedIntegrand_le_endpointLoss
          hε hε1 α β
          (r324ContractionEndpointAnchors hm
            (r324RefinedScheduleRepresentative p.1) v)
          (r324ContractionEndpointFlags
            (r324RefinedScheduleRepresentative p.1))
          (core v)
    have hintegral :
        ‖∫ v, endpointIntegral v
            ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)‖ ≤
          ∫ v, scale * ‖core v‖
            ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
      norm_integral_le_of_norm_le hmajor
        (Filter.Eventually.of_forall hpoint)
    have hmass :
        0 ≤ ρ.r324GroupedRefinedCoreL1 hm ε p :=
      ρ.r324GroupedRefinedCoreL1_nonneg hm ε p
    have htermCore :
        ‖r324GroupedEndpointConfigurationTerm
            hm ρ lam ε α β
            (r324RefinedScheduleRepresentative p.1)
            (ρ.r324KeyGroupedRefinedEndpointCore
              hm ε p.1 p.2)‖ ≤
          scale *
            (scalar *
              ρ.r324GroupedRefinedCoreL1 hm ε p) := by
      unfold r324GroupedEndpointConfigurationTerm
      change
        ‖(lamEps lam ε ^ (2 * m) : ℂ) *
            ∫ v, endpointIntegral v
              ∂(Measure.pi fun _ : Fin (2 * m) =>
                paperMeasure)‖ ≤
          scale *
            (scalar *
              ρ.r324GroupedRefinedCoreL1 hm ε p)
      rw [norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs]
      calc
        |lamEps lam ε| ^ (2 * m) *
              ‖∫ v, endpointIntegral v
                ∂(Measure.pi fun _ : Fin (2 * m) =>
                  paperMeasure)‖ ≤
            scalar *
              ∫ v, scale * ‖core v‖
                ∂(Measure.pi fun _ : Fin (2 * m) =>
                  paperMeasure) :=
          mul_le_mul_of_nonneg_left hintegral hscalar
        _ = scale *
              (scalar *
                ρ.r324GroupedRefinedCoreL1 hm ε p) := by
          rw [integral_const_mul]
          unfold r324GroupedRefinedCoreL1
          dsimp only [scalar]
          ring
    have hcost :
        r324GroupedIncrementCost hm p.2 i ≤
          ∑ j : Fin m,
            r324GroupedIncrementCost hm p.2 j :=
      Finset.single_le_sum
        (fun j _ =>
          (r324GroupedIncrementCost_pos hm p.2 j).le)
        (Finset.mem_univ i)
    have hdecay :
        0 ≤
          eighthOrderFrequencyDecay
            ‖z4EuclideanFrequency
              (r324NatEquivStandardConfigurations
                hm p.2 i)‖ :=
      eighthOrderFrequencyDecay_nonneg _
    have hbaseCore :
        0 ≤
          scale *
            (scalar *
              ρ.r324GroupedRefinedCoreL1 hm ε p) :=
      mul_nonneg hscale (mul_nonneg hscalar hmass)
    calc
      ‖r324GroupedEndpointConfigurationTerm
          hm ρ lam ε α β
          (r324RefinedScheduleRepresentative p.1)
          (ρ.r324KeyGroupedRefinedEndpointCore
            hm ε p.1 p.2)‖ ≤
          scale *
            (scalar *
              ρ.r324GroupedRefinedCoreL1 hm ε p) :=
        htermCore
      _ =
          (scale *
            (scalar *
              ρ.r324GroupedRefinedCoreL1 hm ε p)) *
            (r324GroupedIncrementCost hm p.2 i *
              eighthOrderFrequencyDecay
                ‖z4EuclideanFrequency
                  (r324NatEquivStandardConfigurations
                    hm p.2 i)‖) := by
        rw [r324GroupedIncrementCost_mul_decay]
        ring
      _ ≤
          (scale *
            (scalar *
              ρ.r324GroupedRefinedCoreL1 hm ε p)) *
            ((∑ j : Fin m,
                r324GroupedIncrementCost hm p.2 j) *
              eighthOrderFrequencyDecay
                ‖z4EuclideanFrequency
                  (r324NatEquivStandardConfigurations
                    hm p.2 i)‖) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcost hdecay)
            hbaseCore
      _ =
          (scale *
            ρ.r324GroupedRouteBaseWeight
              lam hm ε p) *
            eighthOrderFrequencyDecay
              ‖z4EuclideanFrequency
                (r324NatEquivStandardConfigurations
                  hm p.2 i)‖ := by
        unfold r324GroupedRouteBaseWeight
        dsimp only [scalar]
        ring

/-! ## Endpoint-free integrated primitive-collapse budget -/

/-- Output expected from the integrated primitive-collapse phase.

It certifies integrability and a summable total budget for the norms of
the already-grouped internal cores.  The endpoint loss, the external modes,
and the final moment estimate are absent from this interface. -/
structure IntegratedPrimitiveCollapseBudget
    (lam ε : ℝ) (m : ℕ) (hm : 0 < m)
    (amplitude : ℝ) : Prop where
  integrable_groupedCore :
    ∀ p : R324RefinedScheduleIndex m × ℕ,
      Integrable
        (fun v : Fin (2 * m) → T4 =>
          ‖ρ.r324KeyGroupedRefinedEndpointCore
            hm ε p.1 p.2 v‖)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure)
  summable_baseWeight :
    Summable (ρ.r324GroupedRouteBaseWeight lam hm ε)
  tsum_baseWeight_le :
    (∑' p, ρ.r324GroupedRouteBaseWeight lam hm ε p) ≤
      amplitude

/-- The concrete exact expansion and an endpoint-free integrated
primitive-collapse budget produce the routed output used by the final
central-frequency estimate. -/
theorem
    countableCentralRoutedMomentReductionOutput_of_integratedPrimitiveCollapseBudget
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (α β : Z4) (amplitude : ℝ)
    (budget :
      ρ.IntegratedPrimitiveCollapseBudget
        lam ε m hm amplitude) :
    CountableCentralRoutedMomentReductionOutput
      ρ lam ε m α β
        ((16 * amplitude) *
          r324EndpointLoss ε α β) := by
  let concrete :=
    ρ.r324ConcreteRefinedCoreExpansion
      lam hm hε hmtrunc α β
  let routed :=
    concrete.toRefinedFourierRoutingData hε hε1
  apply
    routed.toCountableCentralRoutedMomentReductionOutput
      (ρ.r324GroupedRouteBaseWeight lam hm ε)
      amplitude
      budget.summable_baseWeight
      (ρ.r324GroupedRouteBaseWeight_nonneg lam hm ε)
      budget.tsum_baseWeight_le
  intro p i
  change
    ‖r324GroupedEndpointConfigurationTerm
        hm ρ lam ε α β
        (r324RefinedScheduleRepresentative p.1)
        (ρ.r324KeyGroupedRefinedEndpointCore
          hm ε p.1 p.2)‖ ≤
      ((16 * r324EndpointLoss ε α β) *
          ρ.r324GroupedRouteBaseWeight lam hm ε p) *
        eighthOrderFrequencyDecay
          ‖ρ.r324ConcreteRefinedIncrement
            lam hm ε α β p i‖
  exact
    ρ.norm_r324GroupedEndpointConfigurationTerm_le_groupedRouteBaseWeight_mul_decay
      lam hm hε hε1 α β p
      (budget.integrable_groupedCore p) i

end SmoothCutoff

end

end Anderson4D
