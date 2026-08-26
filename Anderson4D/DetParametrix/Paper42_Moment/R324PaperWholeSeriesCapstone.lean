import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHighSlotCapstone

/-!
# Paper Step 4(B) at the complete signed-series boundary

Paper: R-324 — §4.2 Step 4(B), complete signed-series boundary

The paper obtains the central-frequency gain before splitting the complete
operator expansion into selected slots.  This module records the corresponding
consumer interface: one norm is taken only after the complete signed open
covariance series has been reassembled.  It deliberately does not pass through
the per-slot interface, whose triangle inequality is too early for the
common-translation proof.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace SmoothCutoff

/-- The paper Step 4(B) producer at the complete signed-series boundary. -/
def R324PaperHighWholeSeriesWeightedMajorantBound
    (rho : SmoothCutoff) (primitiveConstant supportConstant : Real) : Prop :=
  forall {epsilon : Real} (m : Nat) (alpha beta : Z4),
    forall (hepsilon : 0 < epsilon)
      (hepsilonSmall : epsilon <= 1 / 4)
      (_hlog : 1 <= abs (Real.log epsilon))
      (_hm2 : 2 <= m)
      (hmtrunc : m <= truncOrder epsilon),
    forall (hexternal : alpha + beta ≠ 0) (hm : 0 < m)
      (p : R324RefinedScheduleIndex m),
      1 <= epsilon ^ 2 * norm (z4EuclideanFrequency (alpha + beta)) ->
      abs (lamEps 1 epsilon) ^ (2 * m) *
          norm (rho.r324RefinedQuadOpenCovarianceSeries
            hm epsilon alpha beta hexternal hepsilon
              (hepsilonSmall.trans (by norm_num)) hmtrunc p) <=
        ((paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          eighthOrderFrequencyDecay
            (epsilon ^ 2 *
              norm (z4EuclideanFrequency (alpha + beta)))) *
          (epsilon⁻¹ ^ (8 : Nat) *
            ∫ z, primitiveInsertedMajorant
              primitiveConstant 1 epsilon supportConstant m z
              ∂paperMeasure)

/-- Numerical high-branch estimate for the complete signed series. -/
def R324RefinedQuadHighWholeSeriesCollapseBound
    (rho : SmoothCutoff) (K : Real) : Prop :=
  forall {epsilon : Real} (m : Nat) (alpha beta : Z4)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 4)
    (hlog : 1 <= abs (Real.log epsilon)) (hm2 : 2 <= m)
    (hmtrunc : m <= truncOrder epsilon) (hexternal : alpha + beta ≠ 0)
    (hm : 0 < m) (p : R324RefinedScheduleIndex m),
      1 <= epsilon ^ 2 * norm (z4EuclideanFrequency (alpha + beta)) ->
      norm (rho.r324RefinedQuadOpenCovarianceSeries
          hm epsilon alpha beta hexternal hepsilon
            (hepsilonSmall.trans (by norm_num)) hmtrunc p) <=
        (paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          ((m : Real) ^ 8 * K ^ m * abs (Real.log epsilon) ^ (m - 1) *
            epsilon⁻¹ ^ (8 : Nat) *
              eighthOrderFrequencyDecay
                (epsilon ^ 2 *
                  norm (z4EuclideanFrequency (alpha + beta))))

/-- The common inserted-majorant calculation closes the whole-series scalar
ledger without an additional slot-count triangle inequality. -/
theorem R324PaperHighWholeSeriesWeightedMajorantBound.toHighWholeSeriesCollapseBound
    {rho : SmoothCutoff} {primitiveConstant supportConstant : Real}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant)
    (h : R324PaperHighWholeSeriesWeightedMajorantBound
      rho primitiveConstant supportConstant) :
    exists K : Real, 0 < K ∧
      R324RefinedQuadHighWholeSeriesCollapseBound rho K := by
  obtain ⟨K, hK, hnumeric⟩ :=
    exists_r324PaperWeightedMajorantBase hprimitive hsupport
  refine ⟨K, hK, ?_⟩
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    hexternal hm p hlarge
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
      (norm (rho.r324RefinedQuadOpenCovarianceSeries
        hm epsilon alpha beta hexternal hepsilon
          (hepsilonSmall.trans (by norm_num)) hmtrunc p))
      hepsilon hepsilonSmall hlog hm2 hdecay
      (h m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
        hexternal hm p hlarge)
  dsimp only [decay] at hbound
  calc
    norm (rho.r324RefinedQuadOpenCovarianceSeries
        hm epsilon alpha beta hexternal hepsilon
          (hepsilonSmall.trans (by norm_num)) hmtrunc p) <=
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

/-- Literal low/high central-frequency split using a whole-series high
estimate.  The low branch is unchanged from Step 4(A). -/
theorem R324PaperEndpointAllShiftPhysicalBound.openSeries_of_highWholeSeries
    {rho : SmoothCutoff} {K0 K1 : Real}
    (hK0 : 0 <= K0) (hK1 : 0 <= K1)
    (hEndpoint : R324PaperEndpointAllShiftPhysicalBound rho K0)
    (hHigh : R324RefinedQuadHighWholeSeriesCollapseBound rho K1) :
    R324RefinedQuadOpenCovarianceSeriesBound rho
      (max (16 * max 1 K0) K1) := by
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    hexternal hm p
  have hepsilonOne : epsilon <= 1 :=
    hepsilonSmall.trans (by norm_num)
  let x : Real :=
    epsilon ^ 2 * norm (z4EuclideanFrequency (alpha + beta))
  have hx : 0 <= x := by
    dsimp only [x]
    positivity
  have hK0B : K0 <= max 1 K0 := le_max_right _ _
  have hB : 0 <= max 1 K0 :=
    (by norm_num : (0 : Real) <= 1).trans (le_max_left _ _)
  have hLowBase : 0 <= 16 * max 1 K0 :=
    mul_nonneg (by norm_num) hB
  have hFinalBase : 0 <= max (16 * max 1 K0) K1 :=
    hLowBase.trans (le_max_left _ _)
  by_cases hlarge : 1 <= x
  · have hbound :=
      hHigh m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
        hexternal hm p hlarge
    exact hbound.trans (by
      have hbase :
          K1 <= max (16 * max 1 K0) K1 :=
        le_max_right _ _
      have hpow :
          K1 ^ m <= (max (16 * max 1 K0) K1) ^ m :=
        pow_le_pow_left₀ hK1 hbase m
      gcongr
      · exact mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
          (paperFourthOrderModeDecay_nonneg beta)
      · exact eighthOrderFrequencyDecay_nonneg _)
  · have hsmall : x < 1 := lt_of_not_ge hlarge
    have hdecay :
        (1 / 16 : Real) <= eighthOrderFrequencyDecay x :=
      one_div_sixteen_le_eighthOrderFrequencyDecay hx hsmall
    have hdecayNonneg :
        0 <= eighthOrderFrequencyDecay x :=
      eighthOrderFrequencyDecay_nonneg _
    have hdecayScaled :
        1 <= 16 * eighthOrderFrequencyDecay x := by
      nlinarith
    have hK0pow : K0 ^ m <= (max 1 K0) ^ m :=
      pow_le_pow_left₀ hK0 hK0B m
    have hSixteenPow : (16 : Real) <= 16 ^ m := by
      calc
        (16 : Real) = 16 ^ 1 := (pow_one _).symm
        _ <= 16 ^ m := pow_le_pow_right₀ (by norm_num) hm
    have hAbsorbSixteen :
        16 * (max 1 K0) ^ m <=
          (16 * max 1 K0) ^ m := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hSixteenPow
        (pow_nonneg hB m)
    have hLowToFinal :
        (16 * max 1 K0) ^ m <=
          (max (16 * max 1 K0) K1) ^ m :=
      pow_le_pow_left₀ hLowBase (le_max_left _ _) m
    have hSixteenK0 :
        16 * K0 ^ m <=
          (max (16 * max 1 K0) K1) ^ m := by
      calc
        16 * K0 ^ m <= 16 * (max 1 K0) ^ m :=
          mul_le_mul_of_nonneg_left hK0pow (by norm_num)
        _ <= (16 * max 1 K0) ^ m := hAbsorbSixteen
        _ <= (max (16 * max 1 K0) K1) ^ m := hLowToFinal
    have hKpowDecay :
        K0 ^ m <=
          (max (16 * max 1 K0) K1) ^ m *
            eighthOrderFrequencyDecay x := by
      calc
        K0 ^ m = K0 ^ m * 1 := by ring
        _ <= K0 ^ m * (16 * eighthOrderFrequencyDecay x) :=
          mul_le_mul_of_nonneg_left hdecayScaled (pow_nonneg hK0 m)
        _ = (16 * K0 ^ m) * eighthOrderFrequencyDecay x := by ring
        _ <= (max (16 * max 1 K0) K1) ^ m *
              eighthOrderFrequencyDecay x :=
          mul_le_mul_of_nonneg_right hSixteenK0 hdecayNonneg
    have hopenPhysical :=
      rho.r324RefinedPhysicalIntegral_eq_openCovarianceSeries
        m alpha beta hepsilon hepsilonOne hexternal hm hmtrunc p
    calc
      norm (rho.r324RefinedQuadOpenCovarianceSeries
          hm epsilon alpha beta hexternal hepsilon hepsilonOne hmtrunc p) =
        norm (r324RefinedPhysicalIntegral
          rho epsilon m alpha beta p) :=
        congrArg norm hopenPhysical.symm
      _ <= (paperFourthOrderModeDecay alpha *
              paperFourthOrderModeDecay beta) *
            ((m : Real) ^ 8 * K0 ^ m *
              abs (Real.log epsilon) ^ (m - 1) *
                epsilon⁻¹ ^ (8 : Nat)) :=
        hEndpoint m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc p
      _ <= (paperFourthOrderModeDecay alpha *
              paperFourthOrderModeDecay beta) *
            ((m : Real) ^ 8 *
              ((max (16 * max 1 K0) K1) ^ m *
                eighthOrderFrequencyDecay x) *
              abs (Real.log epsilon) ^ (m - 1) *
                epsilon⁻¹ ^ (8 : Nat)) := by
        gcongr
        exact mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
          (paperFourthOrderModeDecay_nonneg beta)
      _ = (paperFourthOrderModeDecay alpha *
              paperFourthOrderModeDecay beta) *
            ((m : Real) ^ 8 *
              (max (16 * max 1 K0) K1) ^ m *
                abs (Real.log epsilon) ^ (m - 1) *
                  epsilon⁻¹ ^ (8 : Nat) *
                    eighthOrderFrequencyDecay
                      (epsilon ^ 2 *
                        norm (z4EuclideanFrequency (alpha + beta)))) := by
        dsimp only [x]
        ring

end SmoothCutoff

/-! ## Conditional main-theorem capstone with the whole-series producer -/

theorem exists_r324PaperPostCollapseBracket_of_endpoint_and_highWholeSeries
    {rho : SmoothCutoff}
    {endpointPrimitive endpointSupport : Real}
    {highPrimitive highSupport : Real}
    (hEndpointPrimitive : 0 < endpointPrimitive)
    (hEndpointSupport : 0 < endpointSupport)
    (hHighPrimitive : 0 < highPrimitive)
    (hHighSupport : 0 < highSupport)
    (hEndpoint : R324PaperEndpointAllShiftWeightedMajorantBound
      rho endpointPrimitive endpointSupport)
    (hHigh : SmoothCutoff.R324PaperHighWholeSeriesWeightedMajorantBound
      rho highPrimitive highSupport) :
    exists K : Real, 0 <= K /\
      R324RefinedPostCollapsePaperBracketBound rho K := by
  obtain ⟨K0, hK0, hEndpoint0⟩ :=
    hEndpoint.toPhysicalBound hEndpointPrimitive hEndpointSupport
  obtain ⟨K1, hK1, hHigh1⟩ :=
    hHigh.toHighWholeSeriesCollapseBound hHighPrimitive hHighSupport
  let K : Real := max (16 * max 1 K0) K1
  have hB : 0 <= max 1 K0 :=
    (by norm_num : (0 : Real) <= 1).trans (le_max_left _ _)
  have hK : 0 <= K := by
    dsimp only [K]
    exact (mul_nonneg (by norm_num) hB).trans (le_max_left _ _)
  have hK0K : K0 <= K := by
    have hK0B : K0 <= max 1 K0 := le_max_right _ _
    have hB16 : max 1 K0 <= 16 * max 1 K0 := by
      nlinarith
    exact hK0B.trans (hB16.trans (by
      dsimp only [K]
      exact le_max_left _ _))
  have hOpen :
      SmoothCutoff.R324RefinedQuadOpenCovarianceSeriesBound rho K := by
    dsimp only [K]
    exact
      SmoothCutoff.R324PaperEndpointAllShiftPhysicalBound.openSeries_of_highWholeSeries
        hK0.le hK1.le hEndpoint0 hHigh1
  have hZero0 : R324RefinedQuadZeroShiftBound rho K0 :=
    R324PaperEndpointPhysicalBound.toQuadZeroShift
      hEndpoint0.toZeroShift
  have hZero : R324RefinedQuadZeroShiftBound rho K :=
    R324RefinedQuadZeroShiftBound.mono hK0.le hK0K hZero0
  have hQuad : R324RefinedPostCollapsePaperQuadHarvestBound rho K :=
    r324RefinedPostCollapsePaperQuadHarvestBound_of_open_and_zero
      hOpen hZero
  exact ⟨K, hK, hQuad.toPaperBracket⟩

/-- Existential P-3.5b-det interface using the complete-series high producer. -/
theorem r324PaperScale_hdet_of_exists_paperEndpointCases_and_highWholeSeries
    (rho : SmoothCutoff)
    (hResidual :
      exists residualConstant supportConstant : Real,
        0 < residualConstant /\ 0 < supportConstant /\
          R324PaperResidualEndpointWeightedMajorantBound
            rho residualConstant supportConstant)
    (hFull :
      forall {supportConstant : Real}, 0 < supportConstant ->
        exists fullConstant : Real, 0 < fullConstant /\
          R324PaperFullEndpointZeroShiftWeightedMajorantBound
            rho fullConstant supportConstant)
    (hHigh :
      exists highConstant highSupport : Real,
        0 < highConstant /\ 0 < highSupport /\
          SmoothCutoff.R324PaperHighWholeSeriesWeightedMajorantBound
            rho highConstant highSupport) :
    exists outerC powerC : Real, 0 < outerC /\ 0 < powerC /\
      forall lam : Real, 0 < lam ->
        ∀ᶠ epsilon : Real in nhdsWithin 0 (Set.Ioi 0),
          forall m, 1 <= m -> m <= truncOrder epsilon ->
            forall alpha beta : Z4,
              norm (deterministicMomentPairingSum
                rho lam epsilon m alpha beta) <=
                paperDeterministicMomentRHS
                  outerC powerC lam epsilon m alpha beta := by
  obtain ⟨residualConstant, endpointSupport,
      hResidualConstant, hEndpointSupport, hResidualBound⟩ := hResidual
  obtain ⟨fullConstant, hFullConstant, hFullBound⟩ :=
    hFull hEndpointSupport
  obtain ⟨highConstant, highSupport,
      hHighConstant, hHighSupport, hHighBound⟩ := hHigh
  have hEndpointConstant :
      0 < max residualConstant fullConstant :=
    lt_max_of_lt_left hResidualConstant
  obtain ⟨K, hK, hBracket⟩ :=
    exists_r324PaperPostCollapseBracket_of_endpoint_and_highWholeSeries
      hEndpointConstant hEndpointSupport hHighConstant hHighSupport
      (R324PaperEndpointAllShiftWeightedMajorantBound.of_residual_and_zeroShift
        hResidualConstant.le hFullConstant.le hResidualBound hFullBound)
      hHighBound
  obtain ⟨step23Primitive, step23Support,
      hStep23Primitive, hStep23Support, hStep23⟩ :=
    exists_r324PaperRefinedStep23Input rho
  exact r324PaperScale_hdet_paper rho
    hStep23Primitive hStep23Support hStep23 ⟨K, hK, hBracket⟩

/-- Final conditional-main interface using the complete-series high producer. -/
theorem mainConditional_of_exists_paperEndpointCases_and_highWholeSeries
    {M : NoiseModel} {rho : SmoothCutoff}
    (hResidual :
      exists residualConstant supportConstant : Real,
        0 < residualConstant ∧ 0 < supportConstant ∧
          R324PaperResidualEndpointWeightedMajorantBound
            rho residualConstant supportConstant)
    (hFull :
      forall {supportConstant : Real}, 0 < supportConstant ->
        exists fullConstant : Real, 0 < fullConstant ∧
          R324PaperFullEndpointZeroShiftWeightedMajorantBound
            rho fullConstant supportConstant)
    (hHigh :
      exists highConstant highSupport : Real,
        0 < highConstant ∧ 0 < highSupport ∧
          SmoothCutoff.R324PaperHighWholeSeriesWeightedMajorantBound
            rho highConstant highSupport) :
    MainConditional M rho := by
  obtain ⟨residualConstant, endpointSupport,
      hResidualConstant, hEndpointSupport, hResidualBound⟩ := hResidual
  obtain ⟨fullConstant, hFullConstant, hFullBound⟩ :=
    hFull hEndpointSupport
  obtain ⟨highConstant, highSupport,
      hHighConstant, hHighSupport, hHighBound⟩ := hHigh
  have hEndpointConstant :
      0 < max residualConstant fullConstant :=
    lt_max_of_lt_left hResidualConstant
  obtain ⟨K, hK, hBracket⟩ :=
    exists_r324PaperPostCollapseBracket_of_endpoint_and_highWholeSeries
      hEndpointConstant hEndpointSupport hHighConstant hHighSupport
      (R324PaperEndpointAllShiftWeightedMajorantBound.of_residual_and_zeroShift
        hResidualConstant.le hFullConstant.le hResidualBound hFullBound)
      hHighBound
  obtain ⟨step23Primitive, step23Support,
      hStep23Primitive, hStep23Support, hStep23⟩ :=
    exists_r324PaperRefinedStep23Input rho
  exact mainConditional_of_paperRefinedStep23_and_paperBracket
    hStep23Primitive hStep23Support hStep23 ⟨K, hK, hBracket⟩

end

end Anderson4D
