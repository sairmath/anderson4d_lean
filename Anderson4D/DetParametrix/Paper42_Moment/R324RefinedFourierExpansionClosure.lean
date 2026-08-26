import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedFourierTermClosure

/-!
# Exact integrated expansion of residual-refined Fourier groups

The preceding module constructs the pointwise common-increment groups
and proves their joint integrability.  Here the summable physical `L¹`
ledger licenses the exact exchange of the five-group physical integral
with each increment fibre.  No decay estimate or target budget enters
this module.
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

/-- Product-space integral of one raw refined Fourier configuration. -/
def r324RefinedRawFourierIntegral
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) (a : ℕ) : ℂ :=
  ∫ q,
    r324Flatten
      (ρ.r324RefinedRawEndpointIntegrand
        hm ε α β p a) q
    ∂(r324PhysicalMeasure m)

/-- The raw refined Fourier integrals are summable. -/
theorem summable_r324RefinedRawFourierIntegral
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) :
    Summable
      (ρ.r324RefinedRawFourierIntegral
        hm ε α β p) := by
  apply Summable.of_norm
  exact
    (ρ.summable_r324RefinedRawEndpointL1
      hm hε α β p).of_nonneg_of_le
      (fun a => norm_nonneg _)
      (fun a => norm_integral_le_integral_norm _)

/-- Exact Fubini exchange for one common-increment group on the genuine
five-group product measure. -/
theorem integral_keyGroupedRefinedEndpointIntegrand_eq_tsumByKey
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) (b : ℕ) :
    (∫ q,
      r324Flatten
        (ρ.r324KeyGroupedRefinedEndpointIntegrand
          hm ε α β p b) q
      ∂(r324PhysicalMeasure m)) =
      tsumByKey
        (ρ.r324RefinedRawFourierIntegral
          hm ε α β p)
        (r324RefinedRawIncrementKey hm p)
        (r324NatEquivStandardConfigurations hm b) := by
  let key : Fin m → Z4 :=
    r324NatEquivStandardConfigurations hm b
  let S :=
    {a : ℕ //
      r324RefinedRawIncrementKey hm p a = key}
  have hFint :
      ∀ a : S,
        Integrable
          (r324Flatten
            (ρ.r324RefinedRawEndpointIntegrand
              hm ε α β p a.1))
          (r324PhysicalMeasure m) := fun a =>
    ρ.integrable_r324Flatten_refinedRawEndpointIntegrand
      hm ε α β p a.1
  have hFnorm :
      Summable fun a : S =>
        ∫ q,
          ‖r324Flatten
            (ρ.r324RefinedRawEndpointIntegrand
              hm ε α β p a.1) q‖
          ∂(r324PhysicalMeasure m) := by
    exact
      (ρ.summable_r324RefinedRawEndpointL1
        hm hε α β p).subtype _
  calc
    (∫ q,
      r324Flatten
        (ρ.r324KeyGroupedRefinedEndpointIntegrand
          hm ε α β p b) q
      ∂(r324PhysicalMeasure m)) =
        ∫ q,
          ∑' a : S,
            r324Flatten
              (ρ.r324RefinedRawEndpointIntegrand
                hm ε α β p a.1) q
          ∂(r324PhysicalMeasure m) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q =>
        ρ.r324KeyGroupedRefinedEndpointIntegrand_eq_tsumByKey
          hm ε α β p b
          q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
    _ = ∑' a : S,
          ∫ q,
            r324Flatten
              (ρ.r324RefinedRawEndpointIntegrand
                hm ε α β p a.1) q
            ∂(r324PhysicalMeasure m) :=
      (integral_tsum_of_summable_integral_norm
        hFint hFnorm).symm
    _ = tsumByKey
          (ρ.r324RefinedRawFourierIntegral
            hm ε α β p)
          (r324RefinedRawIncrementKey hm p)
          (r324NatEquivStandardConfigurations hm b) := by
      rfl

/-- A concrete grouped endpoint configuration term is the common
coupling factor times the exact raw-integral sum over its shared
increment fibre. -/
theorem r324GroupedEndpointConfigurationTerm_keyGrouped_eq_tsumByKey
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) (b : ℕ) :
    r324GroupedEndpointConfigurationTerm
        hm ρ lam ε α β
        (r324RefinedScheduleRepresentative p)
        (ρ.r324KeyGroupedRefinedEndpointCore
          hm ε p b) =
      (lamEps lam ε ^ (2 * m) : ℂ) *
        tsumByKey
          (ρ.r324RefinedRawFourierIntegral
            hm ε α β p)
          (r324RefinedRawIncrementKey hm p)
          (r324NatEquivStandardConfigurations hm b) := by
  have hint :=
    ρ.integrable_r324Flatten_keyGroupedRefinedEndpointIntegrand
      hm hε α β p b
  unfold r324GroupedEndpointConfigurationTerm
  change
    (lamEps lam ε ^ (2 * m) : ℂ) *
        (∫ v, ∫ x, ∫ y, ∫ z, ∫ w,
          ρ.r324KeyGroupedRefinedEndpointIntegrand
            hm ε α β p b x y z w v
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure ∂paperMeasure
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) =
      _
  rw [← r324_integral_product_eq_internal_first
    (ρ.r324KeyGroupedRefinedEndpointIntegrand
      hm ε α β p b) hint]
  rw [ρ.integral_keyGroupedRefinedEndpointIntegrand_eq_tsumByKey
    hm hε α β p b]

end SmoothCutoff

end

end Anderson4D
