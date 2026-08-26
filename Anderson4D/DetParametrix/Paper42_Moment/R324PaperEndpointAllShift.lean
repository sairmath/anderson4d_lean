import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointNumerics

/-!
# Paper Step 4(A) before the central-frequency case split

The four endpoint integrations in paper Section 4.2, Step 4 do not assume
that the conserved shift `alpha + beta` vanishes.  The old zero-shift
interface is only the branch in which the central-frequency argument is
unnecessary.  This file records the stronger, literal endpoint statement.

Keeping this distinction is useful in the complementary branch
`epsilon^2 * |alpha + beta| < 1`: there the eighth-order central bracket is
bounded below by an absolute constant, so Step 4(A) already gives the full
paper bound and no first-high selector is needed.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- The exact endpoint-to-majorant producer, for arbitrary external modes.
All primitive removals precede the norm, exactly as in paper Step 2(f). -/
def R324PaperEndpointAllShiftWeightedMajorantBound
    (rho : SmoothCutoff) (primitiveConstant supportConstant : Real) : Prop :=
  forall {epsilon : Real} (m : Nat) (alpha beta : Z4),
    0 < epsilon -> epsilon <= 1 / 4 ->
      1 <= abs (Real.log epsilon) -> 2 <= m ->
        m <= truncOrder epsilon ->
          forall p : R324RefinedScheduleIndex m,
            abs (lamEps 1 epsilon) ^ (2 * m) *
                  norm (r324RefinedPhysicalIntegral
                    rho epsilon m alpha beta p) <=
                (paperFourthOrderModeDecay alpha *
                    paperFourthOrderModeDecay beta) *
                  (epsilon⁻¹ ^ (8 : Nat) *
                    ∫ z, primitiveInsertedMajorant
                      primitiveConstant 1 epsilon supportConstant m z
                      ∂paperMeasure)

/-- The arbitrary-shift endpoint estimate after the common numerical
conversion of the final inserted primitive majorant. -/
def R324PaperEndpointAllShiftPhysicalBound
    (rho : SmoothCutoff) (K : Real) : Prop :=
  forall {epsilon : Real} (m : Nat) (alpha beta : Z4),
    0 < epsilon -> epsilon <= 1 / 4 ->
      1 <= abs (Real.log epsilon) -> 2 <= m ->
        m <= truncOrder epsilon ->
          forall p : R324RefinedScheduleIndex m,
            norm (r324RefinedPhysicalIntegral
                rho epsilon m alpha beta p) <=
              (paperFourthOrderModeDecay alpha *
                  paperFourthOrderModeDecay beta) *
                ((m : Real) ^ 8 * K ^ m *
                  abs (Real.log epsilon) ^ (m - 1) *
                    epsilon⁻¹ ^ (8 : Nat))

/-- The scalar endpoint-majorant calculation is independent of the
conserved shift, so it packages the stronger producer without change. -/
theorem R324PaperEndpointAllShiftWeightedMajorantBound.toPhysicalBound
    {rho : SmoothCutoff} {primitiveConstant supportConstant : Real}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant)
    (h : R324PaperEndpointAllShiftWeightedMajorantBound
      rho primitiveConstant supportConstant) :
    exists K : Real, 0 < K ∧
      R324PaperEndpointAllShiftPhysicalBound rho K := by
  obtain ⟨K, hK, hnumeric⟩ :=
    exists_r324PaperEndpointBase_of_weightedMajorant
      rho hprimitive hsupport
  refine ⟨K, hK, ?_⟩
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc p
  exact hnumeric m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc p
    (h m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc p)

/-- The old zero-shift endpoint interface is a direct specialization. -/
theorem R324PaperEndpointAllShiftPhysicalBound.toZeroShift
    {rho : SmoothCutoff} {K : Real}
    (h : R324PaperEndpointAllShiftPhysicalBound rho K) :
    R324PaperEndpointPhysicalBound rho K := by
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    _hshift p
  exact h m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc p

end

end Anderson4D
