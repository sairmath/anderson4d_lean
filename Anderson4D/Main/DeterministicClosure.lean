import Anderson4D.Main.DeterministicAssembly
import Anderson4D.Parametrix.P35bClosure
import Anderson4D.Continuum.LogAsymptotics

/-!
# Direct deterministic closure of the conditional main theorem

This file uses the paper's quantifier order: the uniform and routed
branches produce one fixed absolute constant, which may subsequently
be enlarged.  A single deterministic
(3.24) bound produces `MainSecondMomentInput` through the concrete
Fubini and Wick laws, and the same bound is then reused by the
measurable good-event construction.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter Set
open scoped Topology

/-- A deterministic (3.24) bound gives the exact squared geometric
second-moment input used by the Cramér--Wold argument.  All probabilistic
qualitative premises are discharged by the concrete mollified-noise
construction. -/
theorem mainSecondMomentInput_of_deterministicMomentBound
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant : ℝ}
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hdet :
      ∀ lam : ℝ, 0 < lam →
        ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
          ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
            ‖deterministicMomentPairingSum
                ρ lam ε m α β‖ ≤
              deterministicMomentRHS
                outerConstant powerConstant lam ε m α β) :
    MainSecondMomentInput
      M ρ (Real.sqrt outerConstant) powerConstant := by
  intro lam hlam s modes
  filter_upwards
      [self_mem_nhdsWithin,
        eventually_smallScale_le (by norm_num : (0 : ℝ) < 1),
        hdet lam hlam] with
      ε hεmem hεsmall hdetε
  have hε : 0 < ε := hεmem
  intro j n hn hntrunc
  exact
    parametrix_coeff_geometric_second_moment_bound
      (pmCoeffMomentFubiniOutput_of_r324
        M ρ lam hε hεsmall n (modes j).1 (modes j).2)
      (M.wickAtSecondMomentLaw ρ hε n)
      (hdetε n hn hntrunc (modes j).1 (modes j).2)
      houter hpower hlam.le hn

/-- Final conditional theorem from the R-322 and R-324 quantitative
estimates. -/
theorem mainConditional_of_deterministic_bounds
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant Crenorm : ℝ}
    (houter : 0 < outerConstant)
    (hpower : 0 < powerConstant)
    (hCrenorm : 0 < Crenorm)
    (hdet :
      ∀ lam : ℝ, 0 < lam →
        ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
          ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
            ‖deterministicMomentPairingSum
                ρ lam ε m α β‖ ≤
              deterministicMomentRHS
                outerConstant powerConstant lam ε m α β)
    (hcounter :
      ∀ lam : ℝ, 0 < lam →
        ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
          ∀ q ∈ Finset.Icc 1 (truncOrder ε),
            |renormC2q ρ lam ε q| ≤
              ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
                (Crenorm * lam) ^ (2 * q)) :
    MainConditional M ρ := by
  exact
    mainConditional_of_secondMoment_and_deterministic_bounds
      (Real.sqrt_nonneg outerConstant)
      hpower houter.le hpower hCrenorm
      (mainSecondMomentInput_of_deterministicMomentBound
        houter.le hpower.le hdet)
      hdet hcounter

end

end Anderson4D
