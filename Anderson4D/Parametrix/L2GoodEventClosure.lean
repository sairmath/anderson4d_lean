import Anderson4D.Parametrix.IdentityAECoefficientClosure
import Anderson4D.Parametrix.L2NumericalBudget

/-!
# Closed one-sided good-event estimate

This module removes the final Proposition 3.4 interface from the
one-sided numerical good-event theorem.  The pairing/graded coefficient
agreement is automatic on every positive-scale continuous-noise event.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open Set

namespace PartialPairing

/-- The exact `2 ε²` exceptional-set bound with all Proposition 3.4
inputs discharged.  Only the deterministic P-3.5b estimate and the
renormalization-constant estimate remain as quantitative inputs. -/
theorem
    eventually_measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_two_mul_sq_closed
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant Crenorm lam : ℝ}
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hCrenorm : 0 ≤ Crenorm)
    (hlam : 0 ≤ lam) (hlamle : lam ≤ 1)
    (hpowerRatio :
      powerConstant * lam ≤ boundaryGeometricRatio)
    (hrenormRatio :
      Crenorm * lam ≤ boundaryGeometricRatio)
    (hdet :
      ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
        ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
          ‖deterministicMomentPairingSum
              ρ lam ε m α β‖ ≤
            deterministicMomentRHS
              outerConstant powerConstant lam ε m α β)
    (hcounter :
      ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
        ∀ q ∈ Finset.Icc 1 (truncOrder ε),
          |renormC2q ρ lam ε q| ≤
            ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
              (Crenorm * lam) ^ (2 * q)) :
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
      (volume : Measure M.Ω).real
          (canonicalOneSidedL2ParametrixGoodEvent
            M ρ lam ε (truncOrder ε)
            (canonicalGradedTruncatedParametrixL2Factor
              M ρ lam ε (truncOrder ε))
            (canonicalPerrLeftRemainder
              M ρ lam ε (truncOrder ε)))ᶜ ≤
        2 * ε ^ 2 := by
  have hagree :
      ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
        ∀ᵐ ω ∂(volume : Measure M.Ω),
          ParametrixGradedCoefficientAgreement
            M ρ lam ε (truncOrder ε) ω := by
    filter_upwards
      [self_mem_nhdsWithin,
        eventually_smallScale_le zero_lt_one] with
      ε hε hεle
    exact
      ae_parametrixGradedCoefficientAgreement
        M ρ lam hε hεle (truncOrder ε)
  exact
    eventually_measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_two_mul_sq
      houter hpower hCrenorm hlam hlamle
      hpowerRatio hrenormRatio hdet hagree hcounter

end PartialPairing

end

end Anderson4D
