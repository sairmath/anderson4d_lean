import Anderson4D.DetParametrix.Paper42_Moment.R324FrequencyRoutingClosure

/-!
# Final deterministic closure from countable R-324 routing

The Fourier expansion used by R-324 is a genuine countable series.  This
module combines that countable central-frequency output with the uniform
primitive-block branch, without converting the series to a finite routing interface.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- A uniform estimate and a countable central-frequency decomposition with
the aggregate endpoint budget give the exact paper-bracket `min` estimate. -/
theorem deterministicMomentPairingSum_paper_bound_of_uniform_and_countable
    {ρ : SmoothCutoff} {lam ε amplitude weightBudget : ℝ}
    {m : ℕ} {α β : Z4}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (huniform :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        amplitude)
    (hroute :
      CountableCentralRoutedMomentReductionOutput
        ρ lam ε m α β weightBudget)
    (hendpoint :
      weightBudget ≤
        amplitude * r324EndpointLoss ε α β) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      amplitude * min 1
        (paperDeterministicMomentDecay ε α β) := by
  have hdecay :=
    deterministicMomentPairingSum_paperDecay_bound_of_countableCentralRouting
      hε hεsmall hroute hendpoint
  exact le_mul_min_of_le_of_le_mul huniform hdecay

/-- Countable-series counterpart of
`exists_deterministicMoment_paper_bound_of_reductions`.

The routing input is stated with exactly the endpoint-weighted budget needed
by the preceding theorem.  It contains no target moment inequality. -/
theorem
    exists_deterministicMoment_paper_bound_of_uniform_and_countable
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4),
        0 < ε → ε ≤ 1 / 4 → 1 ≤ |Real.log ε| → 1 ≤ m →
        MomentUniformReductionOutputAt ρ lam ε m α β
          primitiveConstant supportConstant →
        CountableCentralRoutedMomentReductionOutput
          ρ lam ε m α β
          ((lamEps lam ε ^ 2 * outerConstant *
              (primitiveConstant * lam) ^ (2 * m - 2)) *
            r324EndpointLoss ε α β) →
          ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
            paperDeterministicMomentRHS outerConstant primitiveConstant
              lam ε m α β := by
  obtain ⟨outerConstant, houter, huniform⟩ :=
    exists_deterministicMoment_uniform_bound_of_reduction
      hprimitive hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m α β hε hεsmall hlog hm
    huniformRed hroute
  let amplitude : ℝ :=
    lamEps lam ε ^ 2 * outerConstant *
      (primitiveConstant * lam) ^ (2 * m - 2)
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hu :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        amplitude := by
    exact
      huniform ρ lam ε m α β hε hε1 hlog hm
        huniformRed
  have hcombined :=
    deterministicMomentPairingSum_paper_bound_of_uniform_and_countable
      hε hεsmall hu hroute (le_refl _)
  simpa only [paperDeterministicMomentRHS, amplitude] using hcombined

end

end Anderson4D
