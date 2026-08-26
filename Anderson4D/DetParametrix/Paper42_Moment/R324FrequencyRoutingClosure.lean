import Anderson4D.DetParametrix.Core.MomentReduction

/-!
# Frequency-routing closure for R-324

This file contains the final assembly tools for paper §4.2 Step 4.  The
projected-noise construction and its covariance expansion are developed
separately from the primitive-block iteration; this module joins their
outputs at the `RoutedMomentReductionOutput` boundary.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- Paper-faithful countable version of the central-frequency part of
the Step 4 decomposition.

The Fourier expansion of a projected mollified noise is a `tsum`, not a
finite sum.  Indexing by `ℕ` allows any countable frequency
configuration to be enumerated (with zero padding).

This structure deliberately carries only the `α+β` decay.  The
`α`/`β` endpoint factors use the class-`E` cancellation after summing a
whole primitive fiber, so imposing them term-by-term on Fourier
configurations would be stronger than the paper. -/
structure CountableCentralRoutedMomentDecomposition
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (weightBudget : ℝ) where
  term : ℕ → ℂ
  weight : ℕ → ℝ
  incrementCount : ℕ → ℕ
  increment :
    ∀ a : ℕ,
      Fin (incrementCount a) → EuclideanSpace ℝ (Fin dim)
  sum_eq :
    deterministicMomentPairingSum ρ lam ε m α β =
      ∑' a, term a
  summable_term : Summable term
  summable_weight : Summable weight
  weight_nonneg : ∀ a, 0 ≤ weight a
  incrementCount_pos : ∀ a, 0 < incrementCount a
  incrementCount_le_trunc :
    ∀ a, incrementCount a ≤ truncOrder ε
  increment_sum :
    ∀ a, (∑ i, increment a i) =
      z4EuclideanFrequency (α + β)
  term_le_increment_decay :
    ∀ (a : ℕ) (i : Fin (incrementCount a)),
      ‖term a‖ ≤
        weight a *
          eighthOrderFrequencyDecay ‖increment a i‖
  tsum_weight_le : (∑' a, weight a) ≤ weightBudget

/-- Existence wrapper for the countable Fourier-configuration
decomposition. -/
def CountableCentralRoutedMomentReductionOutput
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (weightBudget : ℝ) : Prop :=
  Nonempty
    (CountableCentralRoutedMomentDecomposition
      ρ lam ε m α β weightBudget)

/-- Countable routed decompositions are monotone in their total weight
budget. -/
theorem CountableCentralRoutedMomentReductionOutput.mono
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {α β : Z4}
    {weightBudget weightBudget' : ℝ}
    (h : CountableCentralRoutedMomentReductionOutput
      ρ lam ε m α β weightBudget)
    (hbudget : weightBudget ≤ weightBudget') :
    CountableCentralRoutedMomentReductionOutput
      ρ lam ε m α β weightBudget' := by
  obtain ⟨d⟩ := h
  exact
    ⟨{ term := d.term
       weight := d.weight
       incrementCount := d.incrementCount
       increment := d.increment
       sum_eq := d.sum_eq
       summable_term := d.summable_term
       summable_weight := d.summable_weight
       weight_nonneg := d.weight_nonneg
       incrementCount_pos := d.incrementCount_pos
       incrementCount_le_trunc := d.incrementCount_le_trunc
       increment_sum := d.increment_sum
       term_le_increment_decay :=
         d.term_le_increment_decay
       tsum_weight_le := d.tsum_weight_le.trans hbudget }⟩

/-- The countable Fourier decomposition and truncation-length routing
give the central `⟨ε²(α+β)⟩⁻⁸` factor. -/
theorem
    deterministicMomentPairingSum_centralDecay_bound_of_countableRoutedReduction
    {ρ : SmoothCutoff} {lam ε weightBudget : ℝ} {m : ℕ}
    {α β : Z4}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hred : CountableCentralRoutedMomentReductionOutput
      ρ lam ε m α β weightBudget) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      weightBudget *
        eighthOrderFrequencyDecay
          (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) := by
  obtain ⟨d⟩ := hred
  have hterm :
      ∀ a : ℕ,
        ‖d.term a‖ ≤
          d.weight a *
            eighthOrderFrequencyDecay
              (ε ^ 2 *
                ‖z4EuclideanFrequency (α + β)‖) := by
    intro a
    obtain ⟨i, hi⟩ :=
      exists_increment_with_eighth_order_payoff
        (d.incrementCount a) (d.incrementCount_pos a)
        (d.increment a) ε hε hεsmall
        (d.incrementCount_le_trunc a)
    have hselected :
        eighthOrderFrequencyDecay ‖d.increment a i‖ ≤
          eighthOrderFrequencyDecay
            (ε ^ 2 *
              ‖z4EuclideanFrequency (α + β)‖) := by
      simpa only [d.increment_sum a] using hi
    exact (d.term_le_increment_decay a i).trans
      (mul_le_mul_of_nonneg_left hselected
        (d.weight_nonneg a))
  have hscaledSummable :
      Summable fun a : ℕ =>
        d.weight a *
          eighthOrderFrequencyDecay
            (ε ^ 2 *
              ‖z4EuclideanFrequency (α + β)‖) :=
    d.summable_weight.mul_right _
  calc
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ =
        ‖∑' a, d.term a‖ := by rw [d.sum_eq]
    _ ≤ ∑' a, ‖d.term a‖ :=
      norm_tsum_le_tsum_norm d.summable_term.norm
    _ ≤ ∑' a,
          d.weight a *
            eighthOrderFrequencyDecay
              (ε ^ 2 *
                ‖z4EuclideanFrequency (α + β)‖) :=
      d.summable_term.norm.tsum_le_tsum hterm
        hscaledSummable
    _ = (∑' a, d.weight a) *
          eighthOrderFrequencyDecay
            (ε ^ 2 *
              ‖z4EuclideanFrequency (α + β)‖) := by
      rw [tsum_mul_right]
    _ ≤ weightBudget *
          eighthOrderFrequencyDecay
            (ε ^ 2 *
              ‖z4EuclideanFrequency (α + β)‖) :=
      mul_le_mul_of_nonneg_right d.tsum_weight_le
        (eighthOrderFrequencyDecay_nonneg _)

/-- The endpoint part of paper Step 4: four external Green integrations
give the two fourth-order mode decays at the cost `ε⁻⁸`. -/
def r324EndpointLoss (ε : ℝ) (α β : Z4) : ℝ :=
  ε⁻¹ ^ (8 : ℕ) *
    paperFourthOrderModeDecay α *
    paperFourthOrderModeDecay β

theorem r324EndpointLoss_nonneg
    (ε : ℝ) (α β : Z4) :
    0 ≤ r324EndpointLoss ε α β := by
  unfold r324EndpointLoss
  exact mul_nonneg
    (mul_nonneg (by positivity)
      (paperFourthOrderModeDecay_nonneg α))
    (paperFourthOrderModeDecay_nonneg β)

theorem paperDeterministicMomentDecay_eq_endpoint_mul_central
    (ε : ℝ) (α β : Z4) :
    paperDeterministicMomentDecay ε α β =
      r324EndpointLoss ε α β *
        eighthOrderFrequencyDecay
          (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) := by
  rfl

/-- Combine a central countable routing output with the separate
fiber-level endpoint-oscillation budget.  The endpoint inequality is
aggregate, so the class-`E` cancellation is not incorrectly imposed on
individual Fourier configurations. -/
theorem
    deterministicMomentPairingSum_paperDecay_bound_of_countableCentralRouting
    {ρ : SmoothCutoff} {lam ε weightBudget amplitude : ℝ}
    {m : ℕ} {α β : Z4}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hred : CountableCentralRoutedMomentReductionOutput
      ρ lam ε m α β weightBudget)
    (hendpoint :
      weightBudget ≤
        amplitude * r324EndpointLoss ε α β) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      amplitude * paperDeterministicMomentDecay ε α β := by
  have hcentral :=
    deterministicMomentPairingSum_centralDecay_bound_of_countableRoutedReduction
      hε hεsmall hred
  rw [paperDeterministicMomentDecay_eq_endpoint_mul_central]
  exact hcentral.trans
    (by
      calc
        weightBudget *
              eighthOrderFrequencyDecay
                (ε ^ 2 *
                  ‖z4EuclideanFrequency (α + β)‖)
            ≤ (amplitude * r324EndpointLoss ε α β) *
                eighthOrderFrequencyDecay
                  (ε ^ 2 *
                    ‖z4EuclideanFrequency (α + β)‖) :=
          mul_le_mul_of_nonneg_right hendpoint
            (eighthOrderFrequencyDecay_nonneg _)
        _ = amplitude *
              (r324EndpointLoss ε α β *
                eighthOrderFrequencyDecay
                  (ε ^ 2 *
                    ‖z4EuclideanFrequency (α + β)‖)) := by
          ring)

/-- A routed decomposition is monotone in its total weight budget.  This
is the bookkeeping needed to replace the independently selected uniform
and routing constants by their maximum. -/
theorem RoutedMomentReductionOutput.mono
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {α β : Z4}
    {amplitude amplitude' : ℝ}
    (h : RoutedMomentReductionOutput
      ρ lam ε m α β amplitude)
    (hamp : amplitude ≤ amplitude') :
    RoutedMomentReductionOutput
      ρ lam ε m α β amplitude' := by
  obtain ⟨d⟩ := h
  exact
    ⟨{ termCount := d.termCount
       term := d.term
       weight := d.weight
       incrementCount := d.incrementCount
       increment := d.increment
       sum_eq := d.sum_eq
       weight_nonneg := d.weight_nonneg
       incrementCount_pos := d.incrementCount_pos
       incrementCount_le_trunc := d.incrementCount_le_trunc
       increment_sum := d.increment_sum
       term_le_increment_decay :=
         d.term_le_increment_decay
       sum_weight_le := d.sum_weight_le.trans hamp }⟩

/-- In particular, a routing constant can always be enlarged to the
maximum of itself and an independently chosen uniform constant. -/
theorem RoutedMomentReductionOutput.mono_max_left
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {α β : Z4}
    {amplitude extra : ℝ}
    (h : RoutedMomentReductionOutput
      ρ lam ε m α β amplitude) :
    RoutedMomentReductionOutput
      ρ lam ε m α β (max amplitude extra) :=
  h.mono (le_max_left _ _)

end

end Anderson4D
