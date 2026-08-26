import Anderson4D.DetParametrix.Paper42_Moment.R324PaperQuadHarvestCases

/-!
# Paper Step 4(A) consumer at zero conserved shift

The four external variables in (4.18) are integrated before the first norm.
This file records only the final cancellation of their strictly positive
Fourier multipliers.  The analytic producer belongs to the endpoint-collapse
modules: it must first finish every primitive-interval removal and may then
pay at most one ordinary-`J` sacrifice at each external endpoint.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

/-- The paper Step 4(A) output on one complete residual-refined fibre.
The norm is outside the full physical integral, and the four endpoint
multipliers have already been evaluated. -/
def R324PaperEndpointPhysicalBound
    (rho : SmoothCutoff) (K : Real) : Prop :=
  forall {epsilon : Real} (m : Nat) (alpha beta : Z4),
    0 < epsilon -> epsilon <= 1 / 4 -> 1 <= abs (Real.log epsilon) ->
      2 <= m -> m <= truncOrder epsilon ->
        alpha + beta = 0 -> forall p : R324RefinedScheduleIndex m,
          norm (r324RefinedPhysicalIntegral rho epsilon m alpha beta p) <=
            (paperFourthOrderModeDecay alpha *
                paperFourthOrderModeDecay beta) *
              ((m : Real) ^ 8 * K ^ m *
                abs (Real.log epsilon) ^ (m - 1) *
                  epsilon⁻¹ ^ (8 : Nat))

/-- Exact endpoint-factor cancellation turns Step 4(A) into the zero-shift
quadruple-harvest input.  No estimate is changed here; positivity of the two
Green Fourier multipliers is the only ingredient. -/
theorem R324PaperEndpointPhysicalBound.toQuadZeroShift
    {rho : SmoothCutoff} {K : Real}
    (h : R324PaperEndpointPhysicalBound rho K) :
    R324RefinedQuadZeroShiftBound rho K := by
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    _hexternal hm p
  have hepsilonOne : epsilon <= 1 :=
    hepsilonSmall.trans (by norm_num)
  have hendpoint :
      0 < paperFourthOrderModeDecay alpha *
        paperFourthOrderModeDecay beta :=
    mul_pos (paperFourthOrderModeDecay_pos alpha)
      (paperFourthOrderModeDecay_pos beta)
  have hphysical :=
    h m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
      _hexternal p
  rw [r324RefinedPhysicalIntegral_eq_sum_contractionTerms
      rho hepsilon hepsilonOne alpha beta p,
    r324Beta_sum_eq_endpointDecays_mul_quadHarvest
      rho hepsilon hepsilonOne hm alpha beta
        (momentRefinedContractionFiber m p.1.1 p.2.1),
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hendpoint] at hphysical
  exact le_of_mul_le_mul_left
    (by simpa only [mul_assoc] using hphysical) hendpoint

end

end Anderson4D
