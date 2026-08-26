import Anderson4D.DetParametrix.Paper42_Moment.R324GroupedRouteWeightClosure

/-!
# Summable grouped covariance budgets for R-324

The cancellation-preserving refined expansion is grouped by the common
signed increment vector before a norm is taken.  This file proves that the
scalar covariance weights of those groups remain summable after inserting
the reciprocal eighth-order routing cost.  The proof first establishes the
corresponding statement for raw refined configurations and then uses the
exact `tsumByKey` fibre decomposition.

No primitive-collapse estimate is assumed here.  This is a qualitative
Fubini/summability layer only: separating the scalar covariance weights from
the physical Green skeleton is too coarse to recover the paper-scale
`P-3.5b-det` amplitude.  The quantitative critical path must keep the
unexpanded covariances inside the primitive physical collapse and expand only
the final marked surviving edge.
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

/-- Reciprocal routing cost carried by one arbitrary increment key. -/
def r324IncrementKeyCost
    {m : ℕ} (key : Fin m → Z4) : ℝ :=
  ∑ i : Fin m,
    (1 + ‖z4EuclideanFrequency (key i)‖ ^ 2) ^ 4

theorem r324IncrementKeyCost_nonneg
    {m : ℕ} (key : Fin m → Z4) :
    0 ≤ r324IncrementKeyCost key := by
  unfold r324IncrementKeyCost
  exact Finset.sum_nonneg fun _ _ => by positivity

theorem r324IncrementKeyCost_natConfiguration
    {m : ℕ} (hm : 0 < m) (b : ℕ) :
    r324IncrementKeyCost
        (r324NatEquivStandardConfigurations hm b) =
      ∑ i : Fin m, r324GroupedIncrementCost hm b i := by
  rfl

/-- Raw refined covariance weight with one reciprocal routing cost. -/
def r324RefinedRawCovarianceRouteWeight
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m) (a : ℕ) : ℝ :=
  ρ.r324RefinedRawCovarianceWeight hm ε p a *
    r324IncrementKeyCost
      (r324RefinedRawIncrementKey hm p a)

theorem r324RefinedRawCovarianceRouteWeight_nonneg
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m) (a : ℕ) :
    0 ≤ ρ.r324RefinedRawCovarianceRouteWeight
      hm ε p a := by
  unfold r324RefinedRawCovarianceRouteWeight
  exact mul_nonneg
    (ρ.r324RefinedRawCovarianceWeight_nonneg hm ε p a)
    (r324IncrementKeyCost_nonneg _)

/-- Raw refined covariance route weights are summable.  Only one
degree-eight cost is inserted at a time. -/
theorem summable_r324RefinedRawCovarianceRouteWeight
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m) :
    Summable
      (ρ.r324RefinedRawCovarianceRouteWeight
        hm ε p) := by
  let F :
      R324RefinedContractionIndex p × ℕ → ℝ := fun u =>
    let κ := momentContractionEquivFullPairing m u.1.1
    ρ.r324NatCovarianceConfigurationWeight hm ε κ u.2 *
      ∑ i : Fin m,
        r324PairDecayCost κ
          (r324NatEquivStandardConfigurations hm u.2) i
  have hFnonneg : ∀ u, 0 ≤ F u := by
    intro u
    dsimp only [F]
    exact mul_nonneg
      (ρ.r324CovarianceConfigurationWeight_nonneg ε _ _)
      (Finset.sum_nonneg fun i _ =>
        (r324PairDecayCost_pos _ _ i).le)
  have hF : Summable F := by
    rw [summable_prod_of_nonneg hFnonneg]
    constructor
    · intro e
      let κ := momentContractionEquivFullPairing m e.1
      have hslots :
          Summable fun q : Fin m → Z4 =>
            ∑ i : Fin m,
              ρ.r324CovarianceConfigurationWeight ε κ.1
                  (r324FullConfigurationOfStandard κ q) *
                r324PairDecayCost κ q i := by
        classical
        induction (Finset.univ : Finset (Fin m)) using
          Finset.induction_on with
        | empty =>
            simp
        | @insert i s hi ih =>
            simp_rw [Finset.sum_insert hi]
            exact
              (ρ.summable_standardConfigurationWeight_mul_pairDecayCost
                hε κ i).add ih
      have hnat :=
        hslots.comp_injective
          (r324NatEquivStandardConfigurations hm).injective
      exact hnat.congr fun a => by
        dsimp only [F, κ,
          r324NatCovarianceConfigurationWeight]
        rw [Finset.mul_sum]
        rfl
    · exact Summable.of_finite
  have hpre :=
    hF.comp_injective
      (r324NatEquivRefinedContractionConfigurations p).injective
  exact hpre.congr fun a => by
    unfold r324RefinedRawCovarianceRouteWeight
      r324IncrementKeyCost
      r324RefinedRawCovarianceWeight
      r324RefinedRawIncrementKey
    dsimp only [F]
    apply congrArg₂ (· * ·) rfl
    apply Finset.sum_congr rfl
    intro i _hi
    unfold r324PairDecayCost
    rw [z4EuclideanFrequency_r324NatCovarianceIncrementKey]
    rfl

/-- Grouped scalar covariance route weight. -/
def r324GroupedCovarianceRouteWeight
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m × ℕ) : ℝ :=
  ρ.r324KeyGroupedRefinedCovarianceWeight
      hm ε p.1 p.2 *
    ∑ i : Fin m, r324GroupedIncrementCost hm p.2 i

theorem r324GroupedCovarianceRouteWeight_nonneg
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m × ℕ) :
    0 ≤ ρ.r324GroupedCovarianceRouteWeight hm ε p := by
  unfold r324GroupedCovarianceRouteWeight
  exact mul_nonneg
    (ρ.r324KeyGroupedRefinedCovarianceWeight_nonneg
      hm ε p.1 p.2)
    (Finset.sum_nonneg fun i _ =>
      (r324GroupedIncrementCost_pos hm p.2 i).le)

/-- One grouped route weight is exactly the fibrewise sum of the raw
route weights carrying that increment key. -/
theorem r324GroupedCovarianceRouteWeight_eq_tsumByKey
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m) (b : ℕ) :
    ρ.r324GroupedCovarianceRouteWeight
        hm ε (p, b) =
      tsumByKey
        (ρ.r324RefinedRawCovarianceRouteWeight hm ε p)
        (r324RefinedRawIncrementKey hm p)
        (r324NatEquivStandardConfigurations hm b) := by
  unfold r324GroupedCovarianceRouteWeight
    r324KeyGroupedRefinedCovarianceWeight
    r324RefinedRawCovarianceRouteWeight
    tsumByKey
  rw [← tsum_mul_right]
  apply tsum_congr
  intro a
  apply congrArg₂ (· * ·) rfl
  unfold r324IncrementKeyCost
  apply Finset.sum_congr rfl
  intro i _hi
  rw [a.2]
  rfl

/-- For one refined schedule, all common-increment grouped covariance
route weights are summable. -/
theorem summable_r324GroupedCovarianceRouteWeight_fiber
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m) :
    Summable fun b =>
      ρ.r324GroupedCovarianceRouteWeight
        hm ε (p, b) := by
  have hkey :
      Summable fun k : Fin m → Z4 =>
        tsumByKey
          (ρ.r324RefinedRawCovarianceRouteWeight hm ε p)
          (r324RefinedRawIncrementKey hm p) k :=
    summable_tsumByKey _ _
      (ρ.summable_r324RefinedRawCovarianceRouteWeight
        hm hε p)
  have hnat :=
    hkey.comp_injective
      (r324NatEquivStandardConfigurations hm).injective
  exact hnat.congr fun b =>
    (ρ.r324GroupedCovarianceRouteWeight_eq_tsumByKey
      hm ε p b).symm

/-- The complete schedule-by-key grouped covariance route budget is
summable. -/
theorem summable_r324GroupedCovarianceRouteWeight
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    Summable
      (ρ.r324GroupedCovarianceRouteWeight hm ε) := by
  rw [summable_prod_of_nonneg
    (ρ.r324GroupedCovarianceRouteWeight_nonneg hm ε)]
  constructor
  · intro p
    exact
      ρ.summable_r324GroupedCovarianceRouteWeight_fiber
        hm hε p
  · exact Summable.of_finite

/-- Exact removal of the common-increment grouping from the scalar
route budget of one refined schedule. -/
theorem tsum_r324GroupedCovarianceRouteWeight_fiber
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m) :
    (∑' b,
      ρ.r324GroupedCovarianceRouteWeight
        hm ε (p, b)) =
      ∑' a,
        ρ.r324RefinedRawCovarianceRouteWeight
          hm ε p a := by
  calc
    (∑' b,
      ρ.r324GroupedCovarianceRouteWeight
        hm ε (p, b)) =
        ∑' b : ℕ,
          tsumByKey
            (ρ.r324RefinedRawCovarianceRouteWeight hm ε p)
            (r324RefinedRawIncrementKey hm p)
            (r324NatEquivStandardConfigurations hm b) := by
      apply tsum_congr
      intro b
      exact
        ρ.r324GroupedCovarianceRouteWeight_eq_tsumByKey
          hm ε p b
    _ =
        ∑' k : Fin m → Z4,
          tsumByKey
            (ρ.r324RefinedRawCovarianceRouteWeight hm ε p)
            (r324RefinedRawIncrementKey hm p) k := by
      exact
        (r324NatEquivStandardConfigurations hm).tsum_eq
          (fun k : Fin m → Z4 =>
            tsumByKey
              (ρ.r324RefinedRawCovarianceRouteWeight hm ε p)
              (r324RefinedRawIncrementKey hm p) k)
    _ = ∑' a,
          ρ.r324RefinedRawCovarianceRouteWeight
            hm ε p a :=
      tsum_tsumByKey _ _
        (ρ.summable_r324RefinedRawCovarianceRouteWeight
          hm hε p)

/-! ## Passage from a physical core majorant to the routed budget -/

/-- A uniform physical `L¹` bound by the grouped scalar covariance weight
dominates the concrete grouped route base weight. -/
theorem r324GroupedRouteBaseWeight_le_groupedCovarianceRouteWeight
    (lam C : ℝ)
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (hcore :
      ∀ p : R324RefinedScheduleIndex m × ℕ,
        ρ.r324GroupedRefinedCoreL1 hm ε p ≤
          C *
            ρ.r324KeyGroupedRefinedCovarianceWeight
              hm ε p.1 p.2)
    (p : R324RefinedScheduleIndex m × ℕ) :
    ρ.r324GroupedRouteBaseWeight lam hm ε p ≤
      (|lamEps lam ε| ^ (2 * m) * C) *
        ρ.r324GroupedCovarianceRouteWeight hm ε p := by
  have hscalar :
      0 ≤ |lamEps lam ε| ^ (2 * m) :=
    pow_nonneg (abs_nonneg _) _
  have hcost :
      0 ≤
        ∑ i : Fin m,
          r324GroupedIncrementCost hm p.2 i :=
    Finset.sum_nonneg fun i _ =>
      (r324GroupedIncrementCost_pos hm p.2 i).le
  unfold r324GroupedRouteBaseWeight
    r324GroupedCovarianceRouteWeight
  calc
    |lamEps lam ε| ^ (2 * m) *
          ρ.r324GroupedRefinedCoreL1 hm ε p *
          ∑ i : Fin m,
            r324GroupedIncrementCost hm p.2 i ≤
        |lamEps lam ε| ^ (2 * m) *
          (C *
            ρ.r324KeyGroupedRefinedCovarianceWeight
              hm ε p.1 p.2) *
          ∑ i : Fin m,
            r324GroupedIncrementCost hm p.2 i := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcore p) hscalar)
        hcost
    _ =
        (|lamEps lam ε| ^ (2 * m) * C) *
          (ρ.r324KeyGroupedRefinedCovarianceWeight
              hm ε p.1 p.2 *
            ∑ i : Fin m,
              r324GroupedIncrementCost hm p.2 i) := by
      ring

/-- A uniform grouped-core majorant transfers the already-proved scalar
covariance summability to the concrete grouped route weights. -/
theorem summable_r324GroupedRouteBaseWeight_of_coreCovarianceMajorant
    (lam C : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (hcore :
      ∀ p : R324RefinedScheduleIndex m × ℕ,
        ρ.r324GroupedRefinedCoreL1 hm ε p ≤
          C *
            ρ.r324KeyGroupedRefinedCovarianceWeight
              hm ε p.1 p.2) :
    Summable
      (ρ.r324GroupedRouteBaseWeight lam hm ε) := by
  let scalar : ℝ :=
    |lamEps lam ε| ^ (2 * m) * C
  have hmajor :
      Summable fun p =>
        scalar *
          ρ.r324GroupedCovarianceRouteWeight hm ε p :=
    (ρ.summable_r324GroupedCovarianceRouteWeight
      hm hε).mul_left scalar
  exact hmajor.of_nonneg_of_le
    (ρ.r324GroupedRouteBaseWeight_nonneg lam hm ε)
    (ρ.r324GroupedRouteBaseWeight_le_groupedCovarianceRouteWeight
      lam C hm ε hcore)

/-- A logically exact, but generally coarse, constructor for the downstream
integrated primitive-collapse budget.

It applies when a sharp core/covariance separation is independently available.
Naive instances of `hcore` and `hcovariance` lose unacceptable powers of `ε`
and the primitive-fibre cancellation. -/
theorem integratedPrimitiveCollapseBudget_of_coreCovarianceMajorant
    (lam C covarianceAmplitude : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (hC : 0 ≤ C)
    (hintegrable :
      ∀ p : R324RefinedScheduleIndex m × ℕ,
        Integrable
          (fun v : Fin (2 * m) → T4 =>
            ‖ρ.r324KeyGroupedRefinedEndpointCore
              hm ε p.1 p.2 v‖)
          (Measure.pi fun _ : Fin (2 * m) =>
            paperMeasure))
    (hcore :
      ∀ p : R324RefinedScheduleIndex m × ℕ,
        ρ.r324GroupedRefinedCoreL1 hm ε p ≤
          C *
            ρ.r324KeyGroupedRefinedCovarianceWeight
              hm ε p.1 p.2)
    (hcovariance :
      (∑' p,
        ρ.r324GroupedCovarianceRouteWeight hm ε p) ≤
          covarianceAmplitude) :
    ρ.IntegratedPrimitiveCollapseBudget
      lam ε m hm
        ((|lamEps lam ε| ^ (2 * m) * C) *
          covarianceAmplitude) := by
  let scalar : ℝ :=
    |lamEps lam ε| ^ (2 * m) * C
  have hscalar : 0 ≤ scalar :=
    mul_nonneg (pow_nonneg (abs_nonneg _) _) hC
  have hbase :=
    ρ.summable_r324GroupedRouteBaseWeight_of_coreCovarianceMajorant
      lam C hm hε hcore
  have hmajor :
      Summable fun p =>
        scalar *
          ρ.r324GroupedCovarianceRouteWeight hm ε p :=
    (ρ.summable_r324GroupedCovarianceRouteWeight
      hm hε).mul_left scalar
  refine
    { integrable_groupedCore := hintegrable
      summable_baseWeight := hbase
      tsum_baseWeight_le := ?_ }
  calc
    (∑' p,
      ρ.r324GroupedRouteBaseWeight lam hm ε p) ≤
        ∑' p,
          scalar *
            ρ.r324GroupedCovarianceRouteWeight hm ε p :=
      hbase.tsum_le_tsum
        (ρ.r324GroupedRouteBaseWeight_le_groupedCovarianceRouteWeight
          lam C hm ε hcore)
        hmajor
    _ =
        scalar *
          ∑' p,
            ρ.r324GroupedCovarianceRouteWeight hm ε p := by
      rw [tsum_mul_left]
    _ ≤ scalar * covarianceAmplitude :=
      mul_le_mul_of_nonneg_left hcovariance hscalar
    _ =
        (|lamEps lam ε| ^ (2 * m) * C) *
          covarianceAmplitude := by
      rfl

end SmoothCutoff

end

end Anderson4D
