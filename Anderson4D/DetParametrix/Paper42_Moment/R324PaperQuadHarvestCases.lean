import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedQuadCompositionBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedQuadCovarianceReassembly

/-!
# The two external-frequency cases in paper Step 4(B)

The first-large-factor selector is needed only when the conserved external
shift `α + β` is nonzero.  At zero shift the central paper bracket is exactly
one, so the phase-free Steps 2--3 estimate is already the required bound.

This file contains only that case split.  In particular, it introduces no
routewise norm and no positive route-mass estimate.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

/-! ## The phase-free zero-shift boundary -/

/-- The zero-shift instance of the paper quadruple-harvest estimate.  Its
right-hand side is exactly the paper-scale target with
`eighthOrderFrequencyDecay 0 = 1`. -/
def R324RefinedQuadZeroShiftBound
    (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 / 4 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε → α + β = 0 →
        ∀ (hm : 0 < m) (p : R324RefinedScheduleIndex m),
          ‖r324BetaQuadHarvest ρ ε m α β hm
              (momentRefinedContractionFiber m p.1.1 p.2.1)‖ ≤
            (m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
              ε⁻¹ ^ (8 : ℕ)

/-- The paper-scale quadruple ledger follows by the literal two cases:
nonzero conserved shift uses the first-large open covariance series, while
zero shift uses the phase-free Steps 2--3 estimate. -/
theorem r324RefinedPostCollapsePaperQuadHarvestBound_of_open_and_zero
    {ρ : SmoothCutoff} {K : ℝ}
    (hopen : SmoothCutoff.R324RefinedQuadOpenCovarianceSeriesBound ρ K)
    (hzero : R324RefinedQuadZeroShiftBound ρ K) :
    R324RefinedPostCollapsePaperQuadHarvestBound ρ K := by
  intro ε m α β hε hεsmall hlog hm2 hmtrunc hm p
  by_cases hexternal : α + β = 0
  · have hz :=
      hzero m α β hε hεsmall hlog hm2 hmtrunc
        hexternal hm p
    have hfreq : z4EuclideanFrequency (α + β) = 0 := by
      rw [hexternal]
      exact SmoothCutoff.z4EuclideanFrequencyAddHom.map_zero
    have hdecay : eighthOrderFrequencyDecay 0 = 1 := by
      norm_num [eighthOrderFrequencyDecay]
    simpa only [hfreq, norm_zero, mul_zero, hdecay, mul_one] using hz
  · exact
      SmoothCutoff.norm_r324BetaQuadHarvest_le_of_openCovarianceSeriesBound
        ρ hm ε α β hexternal hε hεsmall hlog hm2 hmtrunc p hopen

end

end Anderson4D
