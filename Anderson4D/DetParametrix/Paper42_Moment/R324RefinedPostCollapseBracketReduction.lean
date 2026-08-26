import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedPostCollapseBracket
import Anderson4D.DetParametrix.Paper42_Moment.R324ScaledBracketClosure

/-!
# The minimal signed-harvest input for the refined R-324 bracket

The four external integrations are already exact identities in
`r324Beta_sum_eq_endpointDecays_mul_quadHarvest`.  Consequently the refined
post-collapse bracket reduces directly to a bound on
`r324BetaQuadHarvest` for the realized refined fibre.

This is the last cancellation-preserving carrier before an analytic
estimate: the entity sum remains inside `r324BetaQuadCore`, the two
transported character differences remain inside the physical integral, and
the norm is taken only after that complete signed integral.  In particular,
the interface below contains neither a raw-route positive mass nor a norm
inside a covariance-key sum.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

/-- **Minimal refined signed-harvest bracket input.**  On each realized
residual-refined fibre, the complete quadruple harvest carries the natural
`ε`-scaled central bracket.  The factor `ε⁻⁸` is not an estimate here: the
exact external endpoint factorization later combines it with
`⟨α⟩⁻⁴⟨β⟩⁻⁴` to give `r324EndpointLoss`.

The order cap is part of the statement, and the norm is outside the full
physical integral defining `r324BetaQuadHarvest`. -/
def R324RefinedPostCollapseQuadHarvestBound
    (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        ∀ (hm : 0 < m) (p : R324RefinedScheduleIndex m),
          ‖r324BetaQuadHarvest ρ ε m α β hm
              (momentRefinedContractionFiber m p.1.1 p.2.1)‖ ≤
            (m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
              (ε⁻¹ ^ (8 : ℕ) *
                eighthOrderFrequencyDecay
                  (ε * ‖z4EuclideanFrequency (α + β)‖))

/-- The signed quadruple-harvest input implies the physical refined-fibre
bracket.  Both transitions used here are exact:

* `r324RefinedPhysicalIntegral_eq_sum_contractionTerms` identifies the
  refined physical integral with its finite contraction fibre;
* `r324Beta_sum_eq_endpointDecays_mul_quadHarvest` performs all four
  external integrations before any norm is taken.

Thus the proof loses no cancellation and merely regroups the endpoint
factors into `r324EndpointLoss`. -/
theorem R324RefinedPostCollapseQuadHarvestBound.toPostCollapseBracket
    {ρ : SmoothCutoff} {K : ℝ}
    (h : R324RefinedPostCollapseQuadHarvestBound ρ K) :
    R324RefinedPostCollapseBracketBound ρ K := by
  intro ε m α β hε hε1 hlog hm2 hcap p
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) hm2
  have hendpoint :
      0 ≤ paperFourthOrderModeDecay α * paperFourthOrderModeDecay β :=
    mul_nonneg (paperFourthOrderModeDecay_nonneg α)
      (paperFourthOrderModeDecay_nonneg β)
  rw [r324RefinedPhysicalIntegral_eq_sum_contractionTerms
    ρ hε hε1 α β p,
    r324Beta_sum_eq_endpointDecays_mul_quadHarvest
      ρ hε hε1 hm α β
        (momentRefinedContractionFiber m p.1.1 p.2.1),
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hendpoint]
  calc
    paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
        ‖r324BetaQuadHarvest ρ ε m α β hm
            (momentRefinedContractionFiber m p.1.1 p.2.1)‖ ≤
      paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
        ((m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
          (ε⁻¹ ^ (8 : ℕ) *
            eighthOrderFrequencyDecay
              (ε * ‖z4EuclideanFrequency (α + β)‖))) :=
      mul_le_mul_of_nonneg_left
        (h m α β hε hε1 hlog hm2 hcap hm p) hendpoint
    _ = (m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
          (r324EndpointLoss ε α β *
            eighthOrderFrequencyDecay
              (ε * ‖z4EuclideanFrequency (α + β)‖)) := by
      unfold r324EndpointLoss
      ring

/-- Direct capstone adapter from the minimal signed harvest to the Hdet
ledger. -/
theorem R324RefinedPostCollapseQuadHarvestBound.toHdetBracketLedger
    {ρ : SmoothCutoff} {K : ℝ}
    (h : R324RefinedPostCollapseQuadHarvestBound ρ K) :
    R324HdetBracketLedgerBound ρ K :=
  R324RefinedPostCollapseBracketBound.toHdetBracketLedger
    (R324RefinedPostCollapseQuadHarvestBound.toPostCollapseBracket h)

/-- The existing arbitrary-finite-set scaled quadruple ledger specializes to
the minimal refined signed-harvest input.  The Hdet allowance `m⁸` is free on
the range `m ≥ 2`; no phase-free density clause is introduced. -/
theorem R324ScaledQuadBracketLedger.toRefinedPostCollapseQuadHarvest
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (h : R324ScaledQuadBracketLedger ρ K) :
    R324RefinedPostCollapseQuadHarvestBound ρ K := by
  intro ε m α β hε hε1 hlog hm2 hcap hm p
  have hbase :
      0 ≤ K ^ m * |Real.log ε| ^ (m - 1) *
        (ε⁻¹ ^ (8 : ℕ) *
          eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖)) := by
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hK m) (pow_nonneg (abs_nonneg _) _))
      (mul_nonneg (by positivity) (eighthOrderFrequencyDecay_nonneg _))
  have hm8 : (1 : ℝ) ≤ (m : ℝ) ^ 8 := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
    exact one_le_pow₀ h1
  refine (h m α β hε hε1 hlog hm2 hcap _ hm).trans ?_
  nlinarith [hbase, hm8]

end

end Anderson4D
