import Anderson4D.DetParametrix.Paper42_Moment.R324ConcreteRoutingClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointBudgetClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedFourierTermClosure

/-!
# Endpoint-first physical-integral bridge for R-324

This file records an exact Fubini-reordered normal form in which the four
raw external Green legs are integrated before the internal variables.  It
is not the literal proof order of paper Section 4.2: Step 2 first performs
the signed within-half primitive-interval collapses, and Step 4 integrates
the endpoint variables after those collapses and before taking absolute
values.  The equalities here are useful audit identities, but do not by
themselves supply a Phase-A iterator.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- Fubini moves the internal variables in front of the four endpoint
integrals.  No norm or triangle inequality has yet been used. -/
theorem r324RefinedPhysicalIntegral_eq_integral_refinedEndpointCoefficient
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (α β : Z4)
    (p : R324RefinedScheduleIndex m) :
    r324RefinedPhysicalIntegral ρ ε m α β p =
      ∫ v,
        r324RefinedEndpointCoefficient
          ρ ε m α β p.1.1 p.2.1 v
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  unfold r324RefinedPhysicalIntegral
    r324RefinedEndpointCoefficient
  exact
    r324_integral_product_eq_internal_first
      (momentRefinedPhysicalIntegrand
        ρ ε m α β p.1.1 p.2.1)
      (integrable_r324RefinedPhysicalIntegrand
        ρ hε hε1 α β p)

/-- The exact endpoint-first integrand associated with a realized refined
schedule.  Its final factor is still the signed sum over all primitive
pairings in that refined fibre. -/
def r324EndpointFirstRefinedCoreIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (hm : 0 < m)
    (α β : Z4) (p : R324RefinedScheduleIndex m)
    (v : Fin (2 * m) → T4) : ℂ :=
  let e₀ := r324RefinedScheduleRepresentative p
  r324EndpointCoefficient α
      ((r324ContractionEndpointAnchors hm e₀ v) 0).1
      ((r324ContractionEndpointAnchors hm e₀ v) 0).2
      ((r324ContractionEndpointFlags e₀) 0) *
    (r324EndpointCoefficient β
      ((r324ContractionEndpointAnchors hm e₀ v) 1).1
      ((r324ContractionEndpointAnchors hm e₀ v) 1).2
      ((r324ContractionEndpointFlags e₀) 1) *
    (r324EndpointCoefficient (-α)
      ((r324ContractionEndpointAnchors hm e₀ v) 2).1
      ((r324ContractionEndpointAnchors hm e₀ v) 2).2
      ((r324ContractionEndpointFlags e₀) 2) *
    (r324EndpointCoefficient (-β)
      ((r324ContractionEndpointAnchors hm e₀ v) 3).1
      ((r324ContractionEndpointAnchors hm e₀ v) 3).2
      ((r324ContractionEndpointFlags e₀) 3) *
      r324RefinedEndpointCore
        ρ ε m p.1.1 p.2.1 e₀ v)))

/-- Pointwise endpoint separation after the four endpoint integrations. -/
theorem r324RefinedEndpointCoefficient_eq_endpointFirstRefinedCoreIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (hm : 0 < m)
    (α β : Z4) (p : R324RefinedScheduleIndex m)
    (v : Fin (2 * m) → T4) :
    r324RefinedEndpointCoefficient
        ρ ε m α β p.1.1 p.2.1 v =
      r324EndpointFirstRefinedCoreIntegrand
        ρ ε m hm α β p v := by
  unfold r324EndpointFirstRefinedCoreIntegrand
  exact
    r324RefinedEndpointCoefficient_eq
      ρ ε m hm α β p.1.1 p.2.1
      (r324RefinedScheduleRepresentative p)
      (r324RefinedScheduleRepresentative_mem p) v

/-- Exact endpoint-first normal form of a realized refined physical fibre.
This is an auxiliary Fubini normal form; the main signed Phase-A route acts
on the original full physical integral. -/
theorem r324RefinedPhysicalIntegral_eq_integral_endpointFirstRefinedCore
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (hm : 0 < m) (α β : Z4)
    (p : R324RefinedScheduleIndex m) :
    r324RefinedPhysicalIntegral ρ ε m α β p =
      ∫ v,
        r324EndpointFirstRefinedCoreIntegrand
          ρ ε m hm α β p v
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  rw [
    r324RefinedPhysicalIntegral_eq_integral_refinedEndpointCoefficient
      ρ hε hε1 α β p]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v =>
    r324RefinedEndpointCoefficient_eq_endpointFirstRefinedCoreIntegrand
      ρ ε m hm α β p v

end

end Anderson4D
