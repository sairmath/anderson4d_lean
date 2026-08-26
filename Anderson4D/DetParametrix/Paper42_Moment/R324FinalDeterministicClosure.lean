import Anderson4D.DetParametrix.Paper42_Moment.R324PrimitiveIterationClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324FrequencyRoutingClosure

/-!
# Final deterministic closure for R-324

This module combines the two paper-faithful outputs of Section 4.2:

* the integrated residual-refined primitive-collapse output from Steps 1--3;
* the countable central-frequency routing output from Step 4.

In particular, the uniform branch is derived from the integrated scalar
majorant.  The stronger pointwise-density interface
`MomentUniformReductionOutputAt` is not used.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-! ## Uniform branch from the integrated refined collapse -/

/-- The integrated residual-refined collapse implies the uniform branch of
paper (3.24).  Both finite schedule counts have already been absorbed by
`C ↦ 16 C` in
`deterministicMomentPairingSum_le_integral_insertedMajorant_of_refined`.
The radial constants are selected before any cutoff, scale, order, or
Fourier mode. -/
theorem
    exists_deterministicMoment_uniform_bound_of_refinedIntegratedReduction
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4),
        0 ≤ lam →
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 1 ≤ m →
        MomentRefinedIntegratedReductionOutputAt
          ρ lam ε m α β primitiveConstant supportConstant →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          lamEps lam ε ^ 2 * outerConstant *
            ((16 * primitiveConstant) * lam) ^ (2 * m - 2) := by
  obtain ⟨Cball, Creg, hCball, hCreg, hmajorant⟩ :=
    exists_integral_primitiveInsertedMajorant_le
  let powerConstant : ℝ := 16 * primitiveConstant
  let K : ℝ :=
    Cball * supportConstant ^ 2 + 2 * Creg
  let outerConstant : ℝ :=
    K * powerConstant ^ 2
  have hpower : 0 < powerConstant := by
    dsimp only [powerConstant]
    positivity
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have houter : 0 < outerConstant := by
    dsimp only [outerConstant]
    positivity
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m α β hlam hε hε1 hlog hm hred
  have hlogPos : 0 < |Real.log ε| :=
    zero_lt_one.trans_le hlog
  have hraw :=
    (deterministicMomentPairingSum_le_integral_insertedMajorant_of_refined
      hprimitive.le hlam hred).trans
      (hmajorant powerConstant lam ε supportConstant m
        hε hε1 hsupport hlog)
  calc
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        (powerConstant * lam) ^ (2 * m) *
          (K / |Real.log ε|) := by
      simpa only [powerConstant, K] using hraw
    _ = lamEps lam ε ^ 2 * outerConstant *
          (powerConstant * lam) ^ (2 * m - 2) := by
      have hexp : 2 * m = (2 * m - 2) + 2 := by
        omega
      have hpow :
          (powerConstant * lam) ^ (2 * m) =
            (powerConstant * lam) ^ (2 * m - 2) *
              (powerConstant * lam) ^ 2 := by
        calc
          (powerConstant * lam) ^ (2 * m) =
              (powerConstant * lam) ^ ((2 * m - 2) + 2) :=
            congrArg
              (fun e : ℕ => (powerConstant * lam) ^ e) hexp
          _ = (powerConstant * lam) ^ (2 * m - 2) *
              (powerConstant * lam) ^ 2 :=
            pow_add _ _ _
      rw [hpow, lamEps_sq hlogPos]
      dsimp only [outerConstant]
      ring
    _ = lamEps lam ε ^ 2 * outerConstant *
          ((16 * primitiveConstant) * lam) ^ (2 * m - 2) := by
      rfl

/-! ## Exact paper-bracket closure -/

/-- Countable-series closure of deterministic R-324.

The first input is the integrated residual-refined collapse.  The second input is the countable
central-frequency decomposition with its aggregate endpoint budget.
Together they give the exact paper bracket
`min (1, ⟨α⟩⁻⁴ ⟨β⟩⁻⁴
⟨ε²(α+β)⟩⁻⁸)`, with the coupling and order dependence
`λ_ε² C ((16 C₀) λ)^(2m-2)`. -/
theorem
    exists_deterministicMoment_paper_bound_of_refinedIntegrated_and_countable
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4),
        0 ≤ lam →
        0 < ε → ε ≤ 1 / 4 → 1 ≤ |Real.log ε| → 1 ≤ m →
        MomentRefinedIntegratedReductionOutputAt
          ρ lam ε m α β primitiveConstant supportConstant →
        CountableCentralRoutedMomentReductionOutput
          ρ lam ε m α β
          ((lamEps lam ε ^ 2 * outerConstant *
              ((16 * primitiveConstant) * lam) ^ (2 * m - 2)) *
            r324EndpointLoss ε α β) →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (16 * primitiveConstant) lam ε m α β := by
  obtain ⟨outerConstant, houter, huniform⟩ :=
    exists_deterministicMoment_uniform_bound_of_refinedIntegratedReduction
      hprimitive hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m α β hlam hε hεsmall hlog hm
    hrefined hroute
  let amplitude : ℝ :=
    lamEps lam ε ^ 2 * outerConstant *
      ((16 * primitiveConstant) * lam) ^ (2 * m - 2)
  have hε1 : ε ≤ 1 :=
    hεsmall.trans (by norm_num)
  have hu :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        amplitude := by
    exact
      huniform ρ lam ε m α β
        hlam hε hε1 hlog hm hrefined
  have hd :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        amplitude * paperDeterministicMomentDecay ε α β := by
    exact
      deterministicMomentPairingSum_paperDecay_bound_of_countableCentralRouting
        hε hεsmall hroute (le_refl _)
  have hcombined :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        amplitude *
          min 1 (paperDeterministicMomentDecay ε α β) :=
    le_mul_min_of_le_of_le_mul hu hd
  simpa only [paperDeterministicMomentRHS, amplitude] using hcombined

end

end Anderson4D
