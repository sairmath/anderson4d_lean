import Anderson4D.DetParametrix.Paper42_Moment.R324SignedRoutedEndpointBudget
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Exact endpoint-case grouping of the raw signed R-324 slot series

The raw marked-slot series lives on the full doubled internal
configuration space.  This file groups that series by the actual
four-endpoint reduction pattern before any phase-A physical-space
estimate is applied.

The later phase-A bridge is represented separately: it pushes each raw
case density to a density in one surviving relative endpoint variable.
Thus the target primitive majorant does not occur in the definition of
the raw density.
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

/-! ## A reusable `L¹` summation lemma -/

/-- A countable family whose integral norms form a summable series has an
integrable pointwise sum.  This is the `L¹` completeness step needed
below; it is deliberately stated locally so the raw density can remain a
literal pointwise `tsum`. -/
private theorem integrable_tsum_of_summable_integral_norm
    {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {μ : Measure α} (F : ι → α → ℝ)
    (hF_int : ∀ i, Integrable (F i) μ)
    (hF_sum : Summable fun i => ∫ x, ‖F i x‖ ∂μ) :
    Integrable (fun x => ∑' i, F i x) μ := by
  let F₁ : ι → (α →₁[μ] ℝ) := fun i =>
    (hF_int i).toL1 (F i)
  have hnorm (i : ι) :
      ‖F₁ i‖ = ∫ x, ‖F i x‖ ∂μ := by
    dsimp only [F₁]
    rw [Integrable.norm_toL1]
    rw [integral_norm_eq_lintegral_enorm
      (hF_int i).aestronglyMeasurable]
    simp only [edist_zero_right]
  have hF₁_norm : Summable fun i => ‖F₁ i‖ := by
    exact hF_sum.congr fun i => (hnorm i).symm
  have hF₁_enorm :
      (∑' i, ‖F₁ i‖ₑ) ≠ ⊤ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hF₁_norm
  have hcoe :
      (⇑(∑' i, F₁ i) : α → ℝ) =ᵐ[μ]
        fun x => ∑' i, F₁ i x :=
    Lp.coeFn_tsum hF₁_enorm
  have hterm :
      ∀ᵐ x ∂μ, ∀ i, F₁ i x = F i x :=
    eventually_countable_forall.2 fun i =>
      (hF_int i).coeFn_toL1
  have heq :
      (⇑(∑' i, F₁ i) : α → ℝ) =ᵐ[μ]
        fun x => ∑' i, F i x := by
    filter_upwards [hcoe, hterm] with x hx hxi
    calc
      (∑' i, F₁ i) x = ∑' i, F₁ i x := hx
      _ = ∑' i, F i x := tsum_congr hxi
  exact (L1.integrable_coeFn (∑' i, F₁ i)).congr heq

/-! ## Raw case densities on the full internal configuration space -/

/-- One raw grouped schedule term, retained exactly when its actual four
endpoint cases agree with `cases`. -/
def r324RawCaseDensityTerm
    (lam : ℝ) {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (i : Fin m) (cases : R324EndpointReductionPattern)
    (p : R324RefinedScheduleIndex m × ℕ)
    (v : Fin (2 * m) → T4) : ℝ :=
  if r324RefinedEndpointReductionCase p.1 = cases then
    |lamEps lam ε| ^ (2 * m) *
      ‖ρ.r324KeyGroupedRefinedEndpointCore
        hm ε p.1 p.2 v‖ *
      r324GroupedIncrementCost hm p.2 i
  else
    0

/-- The exact raw density of one endpoint-case fibre.  Its domain is the
full doubled internal configuration space, not the final relative
endpoint torus. -/
def r324RawCaseDensity
    (lam : ℝ) {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (i : Fin m) (cases : R324EndpointReductionPattern)
    (v : Fin (2 * m) → T4) : ℝ :=
  ∑' p : R324RefinedScheduleIndex m × ℕ,
    ρ.r324RawCaseDensityTerm lam hm ε i cases p v

theorem r324RawCaseDensityTerm_nonneg
    (lam : ℝ) {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (i : Fin m) (cases : R324EndpointReductionPattern)
    (p : R324RefinedScheduleIndex m × ℕ)
    (v : Fin (2 * m) → T4) :
    0 ≤ ρ.r324RawCaseDensityTerm
      lam hm ε i cases p v := by
  unfold r324RawCaseDensityTerm
  split_ifs
  · exact mul_nonneg
      (mul_nonneg
        (pow_nonneg (abs_nonneg _) _)
        (norm_nonneg _))
      (r324GroupedIncrementCost_pos hm p.2 i).le
  · exact le_rfl

theorem integrable_r324RawCaseDensityTerm
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (i : Fin m) (cases : R324EndpointReductionPattern)
    (p : R324RefinedScheduleIndex m × ℕ) :
    Integrable
      (ρ.r324RawCaseDensityTerm lam hm ε i cases p)
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  by_cases hcase :
      r324RefinedEndpointReductionCase p.1 = cases
  · have hcore :=
      ρ.integrable_norm_r324KeyGroupedRefinedEndpointCore
        hm hε p.1 p.2
    unfold r324RawCaseDensityTerm
    simp only [hcase, if_pos]
    simpa only [smul_eq_mul] using
      (hcore.const_mul
        (|lamEps lam ε| ^ (2 * m))).mul_const
          (r324GroupedIncrementCost hm p.2 i)
  · unfold r324RawCaseDensityTerm
    simp only [hcase, if_false]
    exact integrable_zero _ _ _

theorem integral_r324RawCaseDensityTerm
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (i : Fin m)
    (cases : R324EndpointReductionPattern)
    (p : R324RefinedScheduleIndex m × ℕ) :
    (∫ v,
      ρ.r324RawCaseDensityTerm lam hm ε i cases p v
      ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) =
      if r324RefinedEndpointReductionCase p.1 = cases then
        ρ.r324SignedRouteSlotWeight lam hm ε i p
      else
        0 := by
  by_cases hcase :
      r324RefinedEndpointReductionCase p.1 = cases
  · simp only [r324RawCaseDensityTerm, hcase, if_pos]
    rw [integral_mul_const, integral_const_mul]
    rfl
  · simp only [r324RawCaseDensityTerm, hcase, if_false,
      integral_zero]

theorem integral_norm_r324RawCaseDensityTerm
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (i : Fin m)
    (cases : R324EndpointReductionPattern)
    (p : R324RefinedScheduleIndex m × ℕ) :
    (∫ v,
      ‖ρ.r324RawCaseDensityTerm lam hm ε i cases p v‖
      ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) =
      if r324RefinedEndpointReductionCase p.1 = cases then
        ρ.r324SignedRouteSlotWeight lam hm ε i p
      else
        0 := by
  calc
    (∫ v,
        ‖ρ.r324RawCaseDensityTerm lam hm ε i cases p v‖
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) =
        ∫ v,
          ρ.r324RawCaseDensityTerm lam hm ε i cases p v
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by
        change
          ‖ρ.r324RawCaseDensityTerm
              lam hm ε i cases p v‖ =
            ρ.r324RawCaseDensityTerm
              lam hm ε i cases p v
        rw [Real.norm_eq_abs,
          abs_of_nonneg
            (ρ.r324RawCaseDensityTerm_nonneg
              lam hm ε i cases p v)]
    _ =
        if r324RefinedEndpointReductionCase p.1 = cases then
          ρ.r324SignedRouteSlotWeight lam hm ε i p
        else
          0 :=
      ρ.integral_r324RawCaseDensityTerm
        lam hm ε i cases p

/-- The subseries selected by one endpoint pattern is summable. -/
theorem summable_r324RawCaseSelectedSlotWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (i : Fin m) (cases : R324EndpointReductionPattern) :
    Summable fun p : R324RefinedScheduleIndex m × ℕ =>
      if r324RefinedEndpointReductionCase p.1 = cases then
        ρ.r324SignedRouteSlotWeight lam hm ε i p
      else
        0 := by
  exact
    (ρ.summable_r324SignedRouteSlotWeight
      lam hm hε i).of_nonneg_of_le
      (fun p => by
        split_ifs
        · exact ρ.r324SignedRouteSlotWeight_nonneg
            lam hm ε i p
        · exact le_rfl)
      (fun p => by
        split_ifs
        · exact le_rfl
        · exact ρ.r324SignedRouteSlotWeight_nonneg
            lam hm ε i p)

theorem summable_integral_norm_r324RawCaseDensityTerm
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (i : Fin m) (cases : R324EndpointReductionPattern) :
    Summable fun p : R324RefinedScheduleIndex m × ℕ =>
      ∫ v,
        ‖ρ.r324RawCaseDensityTerm
          lam hm ε i cases p v‖
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  exact
    (ρ.summable_r324RawCaseSelectedSlotWeight
      lam hm hε i cases).congr fun p =>
        (ρ.integral_norm_r324RawCaseDensityTerm
          lam hm ε i cases p).symm

/-- Every exact case density is integrable. -/
theorem integrable_r324RawCaseDensity
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (i : Fin m) (cases : R324EndpointReductionPattern) :
    Integrable
      (ρ.r324RawCaseDensity lam hm ε i cases)
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  unfold r324RawCaseDensity
  exact integrable_tsum_of_summable_integral_norm
    (ρ.r324RawCaseDensityTerm lam hm ε i cases)
    (ρ.integrable_r324RawCaseDensityTerm
      lam hm hε i cases)
    (ρ.summable_integral_norm_r324RawCaseDensityTerm
      lam hm hε i cases)

/-- Integrating one raw case density gives exactly the corresponding
subseries of marked-slot weights. -/
theorem integral_r324RawCaseDensity
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (i : Fin m) (cases : R324EndpointReductionPattern) :
    (∫ v,
      ρ.r324RawCaseDensity lam hm ε i cases v
      ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) =
      ∑' p : R324RefinedScheduleIndex m × ℕ,
        if r324RefinedEndpointReductionCase p.1 = cases then
          ρ.r324SignedRouteSlotWeight lam hm ε i p
        else
          0 := by
  calc
    (∫ v,
        ρ.r324RawCaseDensity lam hm ε i cases v
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) =
        ∑' p : R324RefinedScheduleIndex m × ℕ,
          ∫ v,
            ρ.r324RawCaseDensityTerm
              lam hm ε i cases p v
            ∂(Measure.pi fun _ : Fin (2 * m) =>
              paperMeasure) := by
      symm
      exact integral_tsum_of_summable_integral_norm
        (ρ.integrable_r324RawCaseDensityTerm
          lam hm hε i cases)
        (ρ.summable_integral_norm_r324RawCaseDensityTerm
          lam hm hε i cases)
    _ =
        ∑' p : R324RefinedScheduleIndex m × ℕ,
          if r324RefinedEndpointReductionCase p.1 = cases then
            ρ.r324SignedRouteSlotWeight lam hm ε i p
          else
            0 := by
      apply tsum_congr
      intro p
      exact ρ.integral_r324RawCaseDensityTerm
        lam hm ε i cases p

/-- Exact regrouping of the complete raw marked-slot series by the
actual four-endpoint reduction pattern. -/
theorem tsum_r324SignedRouteSlotWeight_eq_sum_integral_rawCaseDensity
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (i : Fin m) :
    (∑' p : R324RefinedScheduleIndex m × ℕ,
      ρ.r324SignedRouteSlotWeight lam hm ε i p) =
      ∑ cases : R324EndpointReductionPattern,
        ∫ v,
          ρ.r324RawCaseDensity lam hm ε i cases v
          ∂(Measure.pi fun _ : Fin (2 * m) =>
            paperMeasure) := by
  calc
    (∑' p : R324RefinedScheduleIndex m × ℕ,
        ρ.r324SignedRouteSlotWeight lam hm ε i p) =
        ∑' p : R324RefinedScheduleIndex m × ℕ,
          ∑ cases : R324EndpointReductionPattern,
            if r324RefinedEndpointReductionCase p.1 = cases then
              ρ.r324SignedRouteSlotWeight lam hm ε i p
            else
              0 := by
      apply tsum_congr
      intro p
      simp
    _ =
        ∑ cases : R324EndpointReductionPattern,
          ∑' p : R324RefinedScheduleIndex m × ℕ,
            if r324RefinedEndpointReductionCase p.1 = cases then
              ρ.r324SignedRouteSlotWeight lam hm ε i p
            else
              0 := by
      rw [Summable.tsum_finsetSum
        (s := (Finset.univ :
          Finset R324EndpointReductionPattern))
        (fun cases _hcases =>
          ρ.summable_r324RawCaseSelectedSlotWeight
            lam hm hε i cases)]
    _ =
        ∑ cases : R324EndpointReductionPattern,
          ∫ v,
            ρ.r324RawCaseDensity lam hm ε i cases v
            ∂(Measure.pi fun _ : Fin (2 * m) =>
              paperMeasure) := by
      apply Finset.sum_congr rfl
      intro cases _hcases
      exact
        (ρ.integral_r324RawCaseDensity
          lam hm hε i cases).symm

/-! ## Non-circular interface to the physical phase-A collapse -/

/-- Output required from the genuine phase-A physical-space reduction.

For each marked slot and actual endpoint pattern, the bridge pushes the
full doubled-configuration density above to a density in one surviving
relative endpoint variable.  Its integral comparison is stated
case-by-case; no total routed budget or downstream slot `tsum` estimate is
a field of this structure. -/
structure R324RawCaseDensityPhaseAOutput
    (lam ε : ℝ) (m : ℕ) (hm : 0 < m)
    (primitiveConstant supportConstant : ℝ) : Type where
  reducedDensity :
    Fin m → R324EndpointReductionPattern → T4 → ℝ
  reducedDensity_integrable :
    ∀ (i : Fin m) (cases : R324EndpointReductionPattern),
      Integrable (reducedDensity i cases) paperMeasure
  raw_case_integral_le_reduced_integral :
    ∀ (i : Fin m) (cases : R324EndpointReductionPattern),
      (∫ v,
        ρ.r324RawCaseDensity lam hm ε i cases v
        ∂(Measure.pi fun _ : Fin (2 * m) =>
          paperMeasure)) ≤
        ∫ z, reducedDensity i cases z ∂paperMeasure
  pointwise_reduced_le_caseAdjustedMajorant :
    ∀ (i : Fin m) (cases : R324EndpointReductionPattern)
      (z : T4),
      reducedDensity i cases z ≤
        r324EndpointPatternAdjustedPrimitiveMajorant
          ε cases primitiveConstant lam supportConstant m z

/-- Exact case regrouping plus a genuine phase-A output produces the
normalized collapse datum consumed by the routed endpoint budget.

The only inequality before the proved constructor is the
case-by-case full-configuration-to-relative-endpoint comparison stored in
`phaseA`; countable regrouping itself remains an equality. -/
def signedRoutedPrimitiveSlotCollapseData_of_rawCaseDensityPhaseAOutput
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (primitiveConstant supportConstant : ℝ)
    (phaseA :
      ρ.R324RawCaseDensityPhaseAOutput
        lam ε m hm primitiveConstant supportConstant) :
    ρ.SignedRoutedPrimitiveSlotCollapseData
      lam ε m hm primitiveConstant supportConstant :=
  ρ.signedRoutedPrimitiveSlotCollapseData_of_rawCaseDensities
    lam ε hm primitiveConstant supportConstant
    phaseA.reducedDensity
    phaseA.reducedDensity_integrable
    (fun i => by
      calc
        (∑' p : R324RefinedScheduleIndex m × ℕ,
            ρ.r324SignedRouteSlotWeight lam hm ε i p) =
            ∑ cases : R324EndpointReductionPattern,
              ∫ v,
                ρ.r324RawCaseDensity
                  lam hm ε i cases v
                ∂(Measure.pi fun _ : Fin (2 * m) =>
                  paperMeasure) :=
          ρ.tsum_r324SignedRouteSlotWeight_eq_sum_integral_rawCaseDensity
            lam hm hε i
        _ ≤
            ∑ cases : R324EndpointReductionPattern,
              ∫ z, phaseA.reducedDensity i cases z
                ∂paperMeasure := by
          exact Finset.sum_le_sum fun cases _hcases =>
            phaseA.raw_case_integral_le_reduced_integral
              i cases)
    phaseA.pointwise_reduced_le_caseAdjustedMajorant

end SmoothCutoff

end

end Anderson4D
