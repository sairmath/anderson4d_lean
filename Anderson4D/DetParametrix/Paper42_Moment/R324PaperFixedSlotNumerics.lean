import Anderson4D.DetParametrix.Paper42_Moment.R324PaperWeightedMajorantNumerics
import Anderson4D.DetParametrix.Paper42_Moment.R324SelectorRetainingSlotRegroup

/-!
# Numerical closure of paper Step 4(B) at one fixed operator slot

The physical proof of Step 4(B) keeps the complete fixed-slot source signed,
extracts the one high projected covariance, and repeats Steps 2--3.  Its
natural endpoint is therefore one inserted primitive majorant multiplied by
the endpoint and central-frequency decays.  This file names that endpoint
and performs only the common scalar conversion.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace SmoothCutoff

/-- Paper Step 4(B)'s physical producer boundary for a single fixed
operator slot.  The norm is outside the complete signed slot series; no
contraction, pairing, route, or Fourier-configuration norm occurs here. -/
def R324PaperFixedSlotWeightedMajorantBound
    (rho : SmoothCutoff) (primitiveConstant supportConstant : Real) : Prop :=
  forall {epsilon : Real} (m : Nat) (alpha beta : Z4),
    forall (hepsilon : 0 < epsilon)
      (hepsilonSmall : epsilon <= 1 / 4)
      (_hlog : 1 <= abs (Real.log epsilon))
      (_hm2 : 2 <= m)
      (hmtrunc : m <= truncOrder epsilon),
    forall (hexternal : alpha + beta ≠ 0) (hm : 0 < m)
      (p : R324RefinedScheduleIndex m) (i : Fin m),
      abs (lamEps 1 epsilon) ^ (2 * m) *
          norm (rho.r324RefinedQuadOpenCovarianceSlotSeries
            hm epsilon alpha beta hexternal hepsilon
              (hepsilonSmall.trans (by norm_num)) hmtrunc p i) <=
        ((paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          eighthOrderFrequencyDecay
            (epsilon ^ 2 *
              norm (z4EuclideanFrequency (alpha + beta)))) *
          (epsilon⁻¹ ^ (8 : Nat) *
            ∫ z, primitiveInsertedMajorant
              primitiveConstant 1 epsilon supportConstant m z
              ∂paperMeasure)

/-- The complete weighted-majorant producer at one fixed slot implies the
literal operator-slot collapse bound used by the Step 4 capstone. -/
theorem R324PaperFixedSlotWeightedMajorantBound.toOperatorSlotCollapseBound
    {rho : SmoothCutoff} {primitiveConstant supportConstant : Real}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant)
    (h : R324PaperFixedSlotWeightedMajorantBound
      rho primitiveConstant supportConstant) :
    exists K : Real, 0 < K ∧
      R324RefinedQuadOperatorSlotCollapseBound rho K := by
  obtain ⟨K, hK, hnumeric⟩ :=
    exists_r324PaperWeightedMajorantBase hprimitive hsupport
  refine ⟨K, hK, ?_⟩
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    hexternal hm p i
  let decay : Real :=
    (paperFourthOrderModeDecay alpha *
        paperFourthOrderModeDecay beta) *
      eighthOrderFrequencyDecay
        (epsilon ^ 2 * norm (z4EuclideanFrequency (alpha + beta)))
  have hdecay : 0 <= decay := by
    dsimp only [decay]
    exact mul_nonneg
      (mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
        (paperFourthOrderModeDecay_nonneg beta))
      (eighthOrderFrequencyDecay_nonneg _)
  have hbound :=
    hnumeric m decay
      (norm (rho.r324RefinedQuadOpenCovarianceSlotSeries
        hm epsilon alpha beta hexternal hepsilon
          (hepsilonSmall.trans (by norm_num)) hmtrunc p i))
      hepsilon hepsilonSmall hlog hm2 hdecay
      (h m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
        hexternal hm p i)
  dsimp only [decay] at hbound
  calc
    norm (rho.r324RefinedQuadOpenCovarianceSlotSeries
        hm epsilon alpha beta hexternal hepsilon
          (hepsilonSmall.trans (by norm_num)) hmtrunc p i) <=
      (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        eighthOrderFrequencyDecay
          (epsilon ^ 2 * norm (z4EuclideanFrequency (alpha + beta))) *
        ((m : Real) ^ 8 * K ^ m *
          abs (Real.log epsilon) ^ (m - 1) *
            epsilon⁻¹ ^ (8 : Nat)) := hbound
    _ = (paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          ((m : Real) ^ 8 * K ^ m *
            abs (Real.log epsilon) ^ (m - 1) *
              epsilon⁻¹ ^ (8 : Nat) *
                eighthOrderFrequencyDecay
                  (epsilon ^ 2 *
                    norm (z4EuclideanFrequency (alpha + beta)))) := by
      ring

end SmoothCutoff

end

end Anderson4D
