import Anderson4D.DetParametrix.Paper42_Moment.R324GroupedRouteWeightClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324SignedRoutedEndpointBudget

/-!
# Step 4(B)'s collapse budget, narrowed to its quantitative field

Paper: R-324 — §4.2 Step 4(B) — the collapse budget, quantitative field only

`IntegratedPrimitiveCollapseBudget` is the datum
`countableCentralRoutedMomentReductionOutput_of_integratedPrimitiveCollapseBudget`
consumes to produce the routed output carrying the central
`⟨ε²(α+β)⟩⁻⁸` factor of paper §4.2 Step 4(B).  It has three fields, of
which the first is purely qualitative and already proved:

* `integrable_groupedCore` — closed by
  `integrable_norm_r324KeyGroupedRefinedEndpointCore` (each signed
  common-increment internal core has finite `L¹` mass, no analytic
  hypothesis);
* `summable_baseWeight`, `tsum_baseWeight_le` — the genuine budget.

This module removes the first field from the interface, reducing Step 4(B)
to one summable series with one bound.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- **Step 4(B)'s budget, from its quantitative field alone.**

The qualitative field of `IntegratedPrimitiveCollapseBudget` is
unconditional, so the whole datum follows from the summability of the base
weight and its total bound. -/
theorem integratedPrimitiveCollapseBudget_of_tsum_le
    (lam : ℝ) {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε)
    {amplitude : ℝ}
    (hsummable : Summable (ρ.r324GroupedRouteBaseWeight lam hm ε))
    (hle :
      (∑' p, ρ.r324GroupedRouteBaseWeight lam hm ε p) ≤ amplitude) :
    ρ.IntegratedPrimitiveCollapseBudget lam ε m hm amplitude where
  integrable_groupedCore p :=
    ρ.integrable_norm_r324KeyGroupedRefinedEndpointCore hm hε p.1 p.2
  summable_baseWeight := hsummable
  tsum_baseWeight_le := hle

/-- **Step 4(B), reduced to one summable series.**

Composing the previous narrowing with
`countableCentralRoutedMomentReductionOutput_of_integratedPrimitiveCollapseBudget`:
the countable routed decomposition — the object that carries the central
eighth-order bracket through `r324Step4_centralDecay_of_composition` — now
rests on nothing but the summability of `r324GroupedRouteBaseWeight` and
its total mass. -/
theorem countableCentralRoutedMomentReductionOutput_of_tsum_le
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (α β : Z4) {amplitude : ℝ}
    (hsummable : Summable (ρ.r324GroupedRouteBaseWeight lam hm ε))
    (hle :
      (∑' p, ρ.r324GroupedRouteBaseWeight lam hm ε p) ≤ amplitude) :
    CountableCentralRoutedMomentReductionOutput ρ lam ε m α β
      ((16 * amplitude) * r324EndpointLoss ε α β) :=
  ρ.countableCentralRoutedMomentReductionOutput_of_integratedPrimitiveCollapseBudget
    lam hm hε hε1 hmtrunc α β amplitude
    (ρ.integratedPrimitiveCollapseBudget_of_tsum_le lam hm hε hsummable hle)

end SmoothCutoff

end

end Anderson4D
