import Anderson4D.DetParametrix.Paper42_Moment.R324RawCaseDensityGrouping

/-!
# Producer for the signed routed primitive slot collapse datum

`SignedRoutedPrimitiveSlotCollapseData` is the single routing input of
the final R-324 assembly.  Its proved constructors consume a family
of per-pattern densities.  This file eliminates the density data
entirely: the datum follows from one scalar inequality per marked slot
— the countable signed route weight against the integrated inserted
majorant.  The density is chosen as the inserted majorant itself,
concentrated on the all-`directFourier` pattern, whose sacrifice
product is `1`; every pattern-adjusted domination then holds pointwise
with no analytic content.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- **The signed collapse datum from a single scalar budget per slot.**
The only remaining content of the routing input is the inequality
`budget`: the total signed route weight of each marked slot is at most
the integrated inserted majorant. -/
def signedRoutedPrimitiveSlotCollapseData_of_slotInsertedBudget
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (primitiveConstant supportConstant : ℝ)
    (hC : 0 ≤ primitiveConstant) (hlam : 0 ≤ lam)
    (budget :
      ∀ i : Fin m,
        (∑' p : R324RefinedScheduleIndex m × ℕ,
          ρ.r324SignedRouteSlotWeight lam hm ε i p) ≤
          ∫ z,
            primitiveInsertedMajorant
              primitiveConstant lam ε supportConstant m z
            ∂paperMeasure) :
    ρ.SignedRoutedPrimitiveSlotCollapseData
      lam ε m hm primitiveConstant supportConstant := by
  refine
    ρ.signedRoutedPrimitiveSlotCollapseData_of_rawCaseDensities
      lam ε hm primitiveConstant supportConstant
      (fun _i cases z =>
        if cases =
            (fun _ => R324EndpointReductionCase.directFourier) then
          primitiveInsertedMajorant
            primitiveConstant lam ε supportConstant m z
        else 0)
      ?_ ?_ ?_
  · intro i cases
    by_cases h :
        cases =
          (fun _ => R324EndpointReductionCase.directFourier)
    · simpa [h] using
        integrable_primitiveInsertedMajorant
          primitiveConstant lam ε supportConstant m hε
    · simp [h]
  · intro i
    have hsum :
        (∑ cases : R324EndpointReductionPattern,
          ∫ z,
            (if cases =
                (fun _ =>
                  R324EndpointReductionCase.directFourier) then
              primitiveInsertedMajorant
                primitiveConstant lam ε supportConstant m z
            else 0)
            ∂paperMeasure) =
          ∫ z,
            primitiveInsertedMajorant
              primitiveConstant lam ε supportConstant m z
            ∂paperMeasure := by
      rw [Finset.sum_eq_single
        (fun _ => R324EndpointReductionCase.directFourier)]
      · simp
      · intro b _hb hbne
        simp [hbne]
      · intro habs
        exact absurd (Finset.mem_univ _) habs
    rw [hsum]
    exact budget i
  · intro i cases z
    unfold r324EndpointPatternAdjustedPrimitiveMajorant
    by_cases h :
        cases =
          (fun _ => R324EndpointReductionCase.directFourier)
    · rw [if_pos h]
      exact le_mul_of_one_le_left
        (primitiveInsertedMajorant_nonneg hC hlam)
        (one_le_r324EndpointPrimitiveSacrificeProduct hε hε1 cases)
    · rw [if_neg h]
      exact mul_nonneg
        (r324EndpointPrimitiveSacrificeProduct_nonneg ε cases)
        (primitiveInsertedMajorant_nonneg hC hlam)

/-- Physical-space form of the same producer: it suffices to bound the
sixteen pattern-grouped raw case-density integrals — the genuine
doubled-configuration integrals of the marked-slot series — by the
integrated inserted majorant.  The countable regrouping itself is the
proved exact equality. -/
def signedRoutedPrimitiveSlotCollapseData_of_rawCaseIntegralBudget
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (primitiveConstant supportConstant : ℝ)
    (hC : 0 ≤ primitiveConstant) (hlam : 0 ≤ lam)
    (budget :
      ∀ i : Fin m,
        (∑ cases : R324EndpointReductionPattern,
          ∫ v,
            ρ.r324RawCaseDensity lam hm ε i cases v
            ∂(Measure.pi fun _ : Fin (2 * m) =>
              paperMeasure)) ≤
          ∫ z,
            primitiveInsertedMajorant
              primitiveConstant lam ε supportConstant m z
            ∂paperMeasure) :
    ρ.SignedRoutedPrimitiveSlotCollapseData
      lam ε m hm primitiveConstant supportConstant :=
  ρ.signedRoutedPrimitiveSlotCollapseData_of_slotInsertedBudget
    lam hm hε hε1 primitiveConstant supportConstant hC hlam
    (fun i => by
      rw [ρ.tsum_r324SignedRouteSlotWeight_eq_sum_integral_rawCaseDensity
        lam hm hε i]
      exact budget i)

end SmoothCutoff

end

end Anderson4D
