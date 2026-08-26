import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointZeroShift
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRefinedStep23Closure
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperScaleMainConditional
import Anderson4D.DetParametrix.Paper42_Moment.R324SelectorRetainingSlotRegroup

/-!
# Paper Step 4 capstone

The zero conserved shift is supplied by the four-endpoint collapse of
Step 4(A).  A nonzero shift is supplied by the first-large-factor fixed-slot
collapse of Step 4(B).  This file only enlarges their geometric constants,
performs the literal two-case split already recorded by the paper-scale
quadruple-harvest API, and connects the result to the unconditional
Steps 2--3 closure.

No physical integral is split and no modulus is moved in this file.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

/-- A zero-shift bound is monotone in its nonnegative geometric base. -/
theorem R324RefinedQuadZeroShiftBound.mono
    {rho : SmoothCutoff} {K0 K : Real}
    (hK0 : 0 <= K0) (hK : K0 <= K)
    (h : R324RefinedQuadZeroShiftBound rho K0) :
    R324RefinedQuadZeroShiftBound rho K := by
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    hexternal hm p
  exact (h m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    hexternal hm p).trans (by
      gcongr)

namespace SmoothCutoff

/-- The complete open covariance-series bound is monotone in its
nonnegative geometric base. -/
theorem R324RefinedQuadOpenCovarianceSeriesBound.mono
    {rho : SmoothCutoff} {K0 K : Real}
    (hK0 : 0 <= K0) (hK : K0 <= K)
    (h : R324RefinedQuadOpenCovarianceSeriesBound rho K0) :
    R324RefinedQuadOpenCovarianceSeriesBound rho K := by
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    hexternal hm p
  have hEndpoint :
      0 <= paperFourthOrderModeDecay alpha *
        paperFourthOrderModeDecay beta :=
    mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
      (paperFourthOrderModeDecay_nonneg beta)
  have hDecay :
      0 <= eighthOrderFrequencyDecay
        (epsilon ^ 2 * norm (z4EuclideanFrequency (alpha + beta))) :=
    eighthOrderFrequencyDecay_nonneg _
  exact (h m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    hexternal hm p).trans (by
      gcongr)

end SmoothCutoff

/-- Once the two paper Step 4 producers exist, the conditional main theorem
follows with no further analytic hypothesis.  Steps 2--3 are supplied by
`exists_r324PaperRefinedStep23Input`; the Gabriel--Rosati input remains
explicit inside `MainConditional`. -/
theorem mainConditional_of_paperEndpoint_and_fixedSlot
    {M : NoiseModel} {rho : SmoothCutoff}
    (hEndpoint : exists K0 : Real,
      0 <= K0 ∧ R324PaperEndpointPhysicalBound rho K0)
    (hFixedSlot : exists K1 : Real,
      0 <= K1 ∧
        SmoothCutoff.R324RefinedQuadOperatorSlotCollapseBound rho K1) :
    MainConditional M rho := by
  obtain ⟨K0, hK0, hEndpoint0⟩ := hEndpoint
  obtain ⟨K1, hK1, hFixedSlot1⟩ := hFixedSlot
  let K : Real := max K0 (2 * K1)
  have hK : 0 <= K :=
    hK0.trans (by
      dsimp only [K]
      exact le_max_left _ _)
  have hK0K : K0 <= K := by
    dsimp only [K]
    exact le_max_left _ _
  have hK1K : 2 * K1 <= K := by
    dsimp only [K]
    exact le_max_right _ _
  have h2K1 : 0 <= 2 * K1 := mul_nonneg (by norm_num) hK1
  have hZero : R324RefinedQuadZeroShiftBound rho K :=
    R324RefinedQuadZeroShiftBound.mono hK0 hK0K
      (R324PaperEndpointPhysicalBound.toQuadZeroShift hEndpoint0)
  have hOpen0 :
      SmoothCutoff.R324RefinedQuadOpenCovarianceSeriesBound rho (2 * K1) :=
    hFixedSlot1.toOpenCovarianceSeriesBound hK1
  have hOpen :
      SmoothCutoff.R324RefinedQuadOpenCovarianceSeriesBound rho K :=
    SmoothCutoff.R324RefinedQuadOpenCovarianceSeriesBound.mono
      h2K1 hK1K hOpen0
  have hQuad : R324RefinedPostCollapsePaperQuadHarvestBound rho K :=
    r324RefinedPostCollapsePaperQuadHarvestBound_of_open_and_zero
      hOpen hZero
  have hBracket : R324RefinedPostCollapsePaperBracketBound rho K :=
    hQuad.toPaperBracket
  obtain ⟨primitiveConstant, supportConstant,
      hPrimitive, hSupport, hStep23⟩ :=
    exists_r324PaperRefinedStep23Input rho
  exact mainConditional_of_paperRefinedStep23_and_paperBracket
    hPrimitive hSupport hStep23 ⟨K, hK, hBracket⟩

end

end Anderson4D
