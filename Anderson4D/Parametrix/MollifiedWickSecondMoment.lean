import Anderson4D.Parametrix.MomentBounds
import Anderson4D.Probability.MollifiedWickLaw
import Anderson4D.Parametrix.WickAtCrossContractions

/-!
# Wick second moments for the random parametrix

This is the parameterized `xiEps` instance of the abstract
`WickAtSecondMomentLaw` consumed by the parametrix moment reduction.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace NoiseModel

variable (M : NoiseModel)

/-- The two `wickAt` factors appearing in the doubled parametrix kernel obey
the exact cross-single contraction formula. -/
theorem wickAtSecondMomentLaw
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    WickAtSecondMomentLaw M ρ ε m where
  integrable κp κm x y z w v := by
    unfold pairedWickProduct
    simp_rw [wickAt_eq_wickPolynomial]
    exact M.integrable_wickPolynomial_xiEps_mul ρ hε
      (wickAtSingleLabels κp
        (assemble x y fun i => v (leftMomentIndex i)))
      (wickAtSingleLabels κm
        (assemble z w fun i => v (rightMomentIndex i)))
  expectation κp κm x y z w v := by
    unfold pairedWickProduct
    simp_rw [wickAt_eq_wickPolynomial]
    rw [M.integral_wickPolynomial_xiEps_mul ρ hε]
    rw [crossWickList_wickAtSingleLabels_eq_crossSingles]
    simp only [assemble_varIdx]

end NoiseModel

end

end Anderson4D
