import Anderson4D.DetParametrix.Paper42_Moment.R324PhaseAOrderLedgerBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324CappedMixedReduction

/-!
# Post-collapse bracket interface for R-324

This module isolates the smallest bracket-retaining analytic input on the
actual residual-refined physical carrier.  The input is deliberately
unweighted: `r324RefinedPhysicalIntegral` is exactly the unweighted finite
contraction sum `momentRefinedDeterministicTermSum`.  The factor
`|lamEps lam ε|^(2*m)` is introduced only later, when the refined fibres are
reassembled into `deterministicMomentPairingSum`.

It also records the direct reduction from the arbitrary-finite-set capped
bracket ledger to the refined-fibre Hdet ledger, without adding the unrelated
phase-free density clause of `R324CappedCrossLedgerStrong`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- **The post-collapse bracket bound on one realized refined schedule.**

The norm is outside the complete signed physical integral of the refined
fibre.  In particular, no norm is taken inside a covariance-key sum.  The
statement carries no `lamEps` factor because its exact downstream target,
`R324HdetBracketLedgerBound`, bounds the unweighted deterministic fibre sum.
-/
def R324RefinedPostCollapseBracketBound
    (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        ∀ p : R324RefinedScheduleIndex m,
          ‖r324RefinedPhysicalIntegral ρ ε m α β p‖ ≤
            (m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
              (r324EndpointLoss ε α β *
                eighthOrderFrequencyDecay
                  (ε * ‖z4EuclideanFrequency (α + β)‖))

/-- The physical refined-schedule bound is exactly the Hdet bracket ledger.
The bridge is an equality of the two unweighted signed fibre expressions, so
no coupling or logarithmic normalization is introduced here. -/
theorem R324RefinedPostCollapseBracketBound.toHdetBracketLedger
    {ρ : SmoothCutoff} {K : ℝ}
    (h : R324RefinedPostCollapseBracketBound ρ K) :
    R324HdetBracketLedgerBound ρ K := by
  intro ε m α β hε hε1 hlog hm2 hcap s hs r hr
  rw [momentRefinedDeterministicTermSum_eq_r324RefinedPhysicalIntegral
    ρ hε hε1 α β s hs r hr]
  exact h m α β hε hε1 hlog hm2 hcap
    (⟨⟨s, hs⟩, ⟨r, hr⟩⟩ : R324RefinedScheduleIndex m)

/-- The capped arbitrary-finite-set bracket ledger implies the Hdet
refined-fibre ledger directly.  This is the bracket half of
`R324CappedCrossLedgerStrong.toBracket`, with no phase-free density
hypothesis. -/
theorem R324CappedBracketDensityLedger.toHdetBracketLedger
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (h : R324CappedBracketDensityLedger ρ K) :
    R324HdetBracketLedgerBound ρ K := by
  intro ε m α β hε hε1 hlog hm2 hcap s _hs r _hr
  have hW0 : 0 ≤ r324CMBracketWeight ε α β :=
    r324CMBracketWeight_nonneg ε α β
  have hKL : (0 : ℝ) ≤ K ^ m * |Real.log ε| ^ (m - 1) :=
    mul_nonneg (pow_nonneg hK m) (pow_nonneg (abs_nonneg _) _)
  have hm8 : (1 : ℝ) ≤ (m : ℝ) ^ 8 := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.one_le_of_lt hm2
    exact one_le_pow₀ h1
  calc
    ‖momentRefinedDeterministicTermSum ρ ε m α β s r‖ ≤
        K ^ m * |Real.log ε| ^ (m - 1) *
          r324CMBracketWeight ε α β :=
      h m α β hε hε1 hlog hm2 hcap _
    _ ≤ (m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
          r324CMBracketWeight ε α β := by
      have hXB : (0 : ℝ) ≤
          K ^ m * |Real.log ε| ^ (m - 1) *
            r324CMBracketWeight ε α β :=
        mul_nonneg hKL hW0
      nlinarith [hXB, hm8]

end

end Anderson4D
