import Anderson4D.DetParametrix.Paper42_Moment.R324LowFrequencySlack
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointCaseAssembly
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperFixedSlotNumerics
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperStep4Capstone

/-!
# Paper Step 4(B) only on the genuinely high central-frequency branch

Paper Section 4.2 invokes the projected-noise factor only when
`epsilon^2 * |alpha + beta| >= 1`.  On the complementary branch the
central bracket is bounded below by `1 / 16`, and the arbitrary-shift
four-endpoint estimate already gives the desired bound.  This file keeps
that case split explicit, so the first-high physical producer is not asked
to prove a statement outside the branch where the paper uses it.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace SmoothCutoff

/-! ## Exact reassembly and the genuinely high branch -/

/-- Away from zero conserved shift, the open-covariance series is exactly
the original refined physical integral.  This is only a rebracketing of
the two exact identities already used in the covariance reassembly; in
particular, no modulus enters here. -/
theorem r324RefinedPhysicalIntegral_eq_openCovarianceSeries
    (rho : SmoothCutoff)
    {epsilon : Real} (m : Nat) (alpha beta : Z4)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon <= 1)
    (hexternal : alpha + beta ≠ 0) (hm : 0 < m)
    (hmtrunc : m <= truncOrder epsilon)
    (p : R324RefinedScheduleIndex m) :
    r324RefinedPhysicalIntegral rho epsilon m alpha beta p =
      rho.r324RefinedQuadOpenCovarianceSeries
        hm epsilon alpha beta hexternal hepsilon hepsilonOne hmtrunc p := by
  rw [r324RefinedPhysicalIntegral_eq_sum_contractionTerms
      rho hepsilon hepsilonOne alpha beta p,
    r324Beta_sum_eq_endpointDecays_mul_quadHarvest
      rho hepsilon hepsilonOne hm alpha beta
        (momentRefinedContractionFiber m p.1.1 p.2.1)]
  exact rho.endpointDecay_mul_r324BetaQuadHarvest_eq_openCovarianceSeries
    hm epsilon alpha beta hexternal hepsilon hepsilonOne hmtrunc p

/-- The fixed-slot physical producer on the large-central-frequency
branch.  The complete slot source remains signed until the displayed norm. -/
def R324PaperHighSlotWeightedMajorantBound
    (rho : SmoothCutoff) (primitiveConstant supportConstant : Real) : Prop :=
  forall {epsilon : Real} (m : Nat) (alpha beta : Z4),
    forall (hepsilon : 0 < epsilon)
      (hepsilonSmall : epsilon <= 1 / 4)
      (_hlog : 1 <= abs (Real.log epsilon))
      (_hm2 : 2 <= m)
      (hmtrunc : m <= truncOrder epsilon),
    forall (hexternal : alpha + beta ≠ 0) (hm : 0 < m)
      (p : R324RefinedScheduleIndex m) (i : Fin m),
      1 <= epsilon ^ 2 * norm (z4EuclideanFrequency (alpha + beta)) ->
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

/-- Numerical form of the high-branch fixed-slot estimate. -/
def R324RefinedQuadHighOperatorSlotCollapseBound
    (rho : SmoothCutoff) (K : Real) : Prop :=
  forall {epsilon : Real} (m : Nat) (alpha beta : Z4)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 4)
    (hlog : 1 <= abs (Real.log epsilon)) (hm2 : 2 <= m)
    (hmtrunc : m <= truncOrder epsilon) (hexternal : alpha + beta ≠ 0)
    (hm : 0 < m) (p : R324RefinedScheduleIndex m) (i : Fin m),
      1 <= epsilon ^ 2 * norm (z4EuclideanFrequency (alpha + beta)) ->
      norm (rho.r324RefinedQuadOpenCovarianceSlotSeries
          hm epsilon alpha beta hexternal hepsilon
            (hepsilonSmall.trans (by norm_num)) hmtrunc p i) <=
        (paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          ((m : Real) ^ 8 * K ^ m * abs (Real.log epsilon) ^ (m - 1) *
            epsilon⁻¹ ^ (8 : Nat) *
              eighthOrderFrequencyDecay
                (epsilon ^ 2 *
                  norm (z4EuclideanFrequency (alpha + beta))))

/-- The common inserted-majorant calculation closes the high-slot scalar
ledger; the extra high-branch premise is simply passed to the producer. -/
theorem R324PaperHighSlotWeightedMajorantBound.toHighSlotCollapseBound
    {rho : SmoothCutoff} {primitiveConstant supportConstant : Real}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant)
    (h : R324PaperHighSlotWeightedMajorantBound
      rho primitiveConstant supportConstant) :
    exists K : Real, 0 < K ∧
      R324RefinedQuadHighOperatorSlotCollapseBound rho K := by
  obtain ⟨K, hK, hnumeric⟩ :=
    exists_r324PaperWeightedMajorantBase hprimitive hsupport
  refine ⟨K, hK, ?_⟩
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    hexternal hm p i hlarge
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
        hexternal hm p i hlarge)
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

/-- On the branch on which the paper invokes the first-high selector, the
single-slot estimate closes the complete signed open series.  The only
triangle inequality is the finite sum over at most `m` possible slots;
`m <= 2^m` is absorbed into the geometric base. -/
theorem R324RefinedQuadHighOperatorSlotCollapseBound.openSeries_of_high
    {rho : SmoothCutoff} {K : Real} (hK : 0 <= K)
    (h : R324RefinedQuadHighOperatorSlotCollapseBound rho K) :
    forall {epsilon : Real} (m : Nat) (alpha beta : Z4)
      (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 4)
      (hlog : 1 <= abs (Real.log epsilon)) (hm2 : 2 <= m)
      (hmtrunc : m <= truncOrder epsilon)
      (hexternal : alpha + beta ≠ 0) (hm : 0 < m)
      (p : R324RefinedScheduleIndex m),
        1 <= epsilon ^ 2 * norm (z4EuclideanFrequency (alpha + beta)) ->
        norm (rho.r324RefinedQuadOpenCovarianceSeries
          hm epsilon alpha beta hexternal hepsilon
            (hepsilonSmall.trans (by norm_num)) hmtrunc p) <=
          (paperFourthOrderModeDecay alpha *
              paperFourthOrderModeDecay beta) *
            ((m : Real) ^ 8 * (2 * K) ^ m *
              abs (Real.log epsilon) ^ (m - 1) *
                epsilon⁻¹ ^ (8 : Nat) *
                  eighthOrderFrequencyDecay
                    (epsilon ^ 2 *
                      norm (z4EuclideanFrequency (alpha + beta)))) := by
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    hexternal hm p hlarge
  have hepsilonOne : epsilon <= 1 :=
    hepsilonSmall.trans (by norm_num)
  let D : Real :=
    paperFourthOrderModeDecay alpha *
      paperFourthOrderModeDecay beta
  let A : Real :=
    (m : Real) ^ 8 * K ^ m *
      abs (Real.log epsilon) ^ (m - 1) *
        epsilon⁻¹ ^ (8 : Nat) *
          eighthOrderFrequencyDecay
            (epsilon ^ 2 *
              norm (z4EuclideanFrequency (alpha + beta)))
  have hD : 0 <= D := by
    exact mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
      (paperFourthOrderModeDecay_nonneg beta)
  have hA : 0 <= A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) (pow_nonneg hK m))
          (pow_nonneg (abs_nonneg _) _))
        (by positivity))
      (eighthOrderFrequencyDecay_nonneg _)
  have hmcast : (m : Real) <= (2 : Real) ^ m := by
    exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
  calc
    norm (rho.r324RefinedQuadOpenCovarianceSeries
        hm epsilon alpha beta hexternal hepsilon hepsilonOne hmtrunc p) <=
      ∑ i : Fin m,
        norm (rho.r324RefinedQuadOpenCovarianceSlotSeries
          hm epsilon alpha beta hexternal hepsilon hepsilonOne hmtrunc p i) :=
      rho.norm_r324RefinedQuadOpenCovarianceSeries_le_sum_slotSeries
        hm epsilon alpha beta hexternal hepsilon hepsilonOne hmtrunc p
    _ <= ∑ _i : Fin m, D * A := by
      apply Finset.sum_le_sum
      intro i _hi
      dsimp only [D, A]
      exact h m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
        hexternal hm p i hlarge
    _ = (m : Real) * (D * A) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [Finset.card_univ, Fintype.card_fin]
    _ <= (2 : Real) ^ m * (D * A) :=
      mul_le_mul_of_nonneg_right hmcast (mul_nonneg hD hA)
    _ = (paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          ((m : Real) ^ 8 * (2 * K) ^ m *
            abs (Real.log epsilon) ^ (m - 1) *
              epsilon⁻¹ ^ (8 : Nat) *
                eighthOrderFrequencyDecay
                  (epsilon ^ 2 *
                    norm (z4EuclideanFrequency (alpha + beta)))) := by
      dsimp only [D, A]
      rw [mul_pow]
      ring

/-! ## Literal Step 4(A)/Step 4(B) case split -/

/-- Paper Step 4 closes the open covariance series by the literal central
frequency split.  If `epsilon^2 * |alpha + beta| < 1`, the arbitrary-shift
four-endpoint estimate supplies the whole series and the target central
decay costs only the absolute factor `16`.  Otherwise the first-high slot
estimate applies and the finite slot count costs `2^m`. -/
theorem R324PaperEndpointAllShiftPhysicalBound.openSeries_of_highSlot
    {rho : SmoothCutoff} {K0 K1 : Real}
    (hK0 : 0 <= K0) (hK1 : 0 <= K1)
    (hEndpoint : R324PaperEndpointAllShiftPhysicalBound rho K0)
    (hHigh : R324RefinedQuadHighOperatorSlotCollapseBound rho K1) :
    R324RefinedQuadOpenCovarianceSeriesBound rho
      (max (16 * max 1 K0) (2 * K1)) := by
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
  have hHighBase : 0 <= 2 * K1 :=
    mul_nonneg (by norm_num) hK1
  have hFinalBase :
      0 <= max (16 * max 1 K0) (2 * K1) :=
    hLowBase.trans (le_max_left _ _)
  by_cases hlarge : 1 <= x
  · have hbound :=
      hHigh.openSeries_of_high hK1 m alpha beta hepsilon
        hepsilonSmall hlog hm2 hmtrunc hexternal hm p hlarge
    exact hbound.trans (by
      have hbase :
          2 * K1 <= max (16 * max 1 K0) (2 * K1) :=
        le_max_right _ _
      have hpow :
          (2 * K1) ^ m <=
            (max (16 * max 1 K0) (2 * K1)) ^ m :=
        pow_le_pow_left₀ hHighBase hbase m
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
          (max (16 * max 1 K0) (2 * K1)) ^ m :=
      pow_le_pow_left₀ hLowBase (le_max_left _ _) m
    have hSixteenK0 :
        16 * K0 ^ m <=
          (max (16 * max 1 K0) (2 * K1)) ^ m := by
      calc
        16 * K0 ^ m <= 16 * (max 1 K0) ^ m :=
          mul_le_mul_of_nonneg_left hK0pow (by norm_num)
        _ <= (16 * max 1 K0) ^ m := hAbsorbSixteen
        _ <= (max (16 * max 1 K0) (2 * K1)) ^ m :=
          hLowToFinal
    have hKpowDecay :
        K0 ^ m <=
          (max (16 * max 1 K0) (2 * K1)) ^ m *
            eighthOrderFrequencyDecay x := by
      calc
        K0 ^ m = K0 ^ m * 1 := by ring
        _ <= K0 ^ m * (16 * eighthOrderFrequencyDecay x) :=
          mul_le_mul_of_nonneg_left hdecayScaled (pow_nonneg hK0 m)
        _ = (16 * K0 ^ m) * eighthOrderFrequencyDecay x := by ring
        _ <= (max (16 * max 1 K0) (2 * K1)) ^ m *
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
              ((max (16 * max 1 K0) (2 * K1)) ^ m *
                eighthOrderFrequencyDecay x) *
              abs (Real.log epsilon) ^ (m - 1) *
                epsilon⁻¹ ^ (8 : Nat)) := by
        gcongr
        exact mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
          (paperFourthOrderModeDecay_nonneg beta)
      _ = (paperFourthOrderModeDecay alpha *
              paperFourthOrderModeDecay beta) *
            ((m : Real) ^ 8 *
              (max (16 * max 1 K0) (2 * K1)) ^ m *
                abs (Real.log epsilon) ^ (m - 1) *
                  epsilon⁻¹ ^ (8 : Nat) *
                    eighthOrderFrequencyDecay
                      (epsilon ^ 2 *
                        norm (z4EuclideanFrequency (alpha + beta)))) := by
        dsimp only [x]
        ring

end SmoothCutoff

/-! ## Step 4 capstone -/

/-- The two literal Step 4 outputs, assembled only as far as the
post-collapse paper bracket.  This is the deterministic seam shared by
P-3.5b-det and the later conditional-main assembly. -/
theorem exists_r324PaperPostCollapseBracket_of_endpoint_and_highSlot
    {rho : SmoothCutoff}
    {endpointPrimitive endpointSupport : Real}
    {highPrimitive highSupport : Real}
    (hEndpointPrimitive : 0 < endpointPrimitive)
    (hEndpointSupport : 0 < endpointSupport)
    (hHighPrimitive : 0 < highPrimitive)
    (hHighSupport : 0 < highSupport)
    (hEndpoint : R324PaperEndpointAllShiftWeightedMajorantBound
      rho endpointPrimitive endpointSupport)
    (hHigh : SmoothCutoff.R324PaperHighSlotWeightedMajorantBound
      rho highPrimitive highSupport) :
    exists K : Real, 0 <= K /\
      R324RefinedPostCollapsePaperBracketBound rho K := by
  obtain ⟨K0, hK0, hEndpoint0⟩ :=
    hEndpoint.toPhysicalBound hEndpointPrimitive hEndpointSupport
  obtain ⟨K1, hK1, hHigh1⟩ :=
    hHigh.toHighSlotCollapseBound hHighPrimitive hHighSupport
  let K : Real := max (16 * max 1 K0) (2 * K1)
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
      SmoothCutoff.R324PaperEndpointAllShiftPhysicalBound.openSeries_of_highSlot
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

/-- **P-3.5b-det from the two paper Step 4 outputs.**  The signed
Steps 2--3 reduction is supplied by its unconditional producer, and the
conclusion is the eventually-small-scale deterministic pairing-sum bound
with the exact paper central-frequency decay. -/
theorem r324PaperScale_hdet_of_endpoint_and_highSlot
    (rho : SmoothCutoff)
    {endpointPrimitive endpointSupport : Real}
    {highPrimitive highSupport : Real}
    (hEndpointPrimitive : 0 < endpointPrimitive)
    (hEndpointSupport : 0 < endpointSupport)
    (hHighPrimitive : 0 < highPrimitive)
    (hHighSupport : 0 < highSupport)
    (hEndpoint : R324PaperEndpointAllShiftWeightedMajorantBound
      rho endpointPrimitive endpointSupport)
    (hHigh : SmoothCutoff.R324PaperHighSlotWeightedMajorantBound
      rho highPrimitive highSupport) :
    exists outerC powerC : Real, 0 < outerC /\ 0 < powerC /\
      forall lam : Real, 0 < lam ->
        ∀ᶠ epsilon : Real in nhdsWithin 0 (Set.Ioi 0),
          forall m, 1 <= m -> m <= truncOrder epsilon ->
            forall alpha beta : Z4,
              norm (deterministicMomentPairingSum
                rho lam epsilon m alpha beta) <=
                paperDeterministicMomentRHS
                  outerC powerC lam epsilon m alpha beta := by
  obtain ⟨K, hK, hBracket⟩ :=
    exists_r324PaperPostCollapseBracket_of_endpoint_and_highSlot
      hEndpointPrimitive hEndpointSupport hHighPrimitive hHighSupport
      hEndpoint hHigh
  obtain ⟨step23Primitive, step23Support,
      hStep23Primitive, hStep23Support, hStep23⟩ :=
    exists_r324PaperRefinedStep23Input rho
  exact r324PaperScale_hdet_paper rho
    hStep23Primitive hStep23Support hStep23 ⟨K, hK, hBracket⟩

/-- The two literal paper Step 4 producers close the conditional main
theorem.  The endpoint producer also supplies the zero conserved-shift
branch; on the nonzero branch the preceding low/high split supplies the
complete open covariance-series estimate. -/
theorem mainConditional_of_paperAllShiftEndpoint_and_highSlot
    {M : NoiseModel} {rho : SmoothCutoff}
    {endpointPrimitive endpointSupport : Real}
    {highPrimitive highSupport : Real}
    (hEndpointPrimitive : 0 < endpointPrimitive)
    (hEndpointSupport : 0 < endpointSupport)
    (hHighPrimitive : 0 < highPrimitive)
    (hHighSupport : 0 < highSupport)
    (hEndpoint : R324PaperEndpointAllShiftWeightedMajorantBound
      rho endpointPrimitive endpointSupport)
    (hHigh : SmoothCutoff.R324PaperHighSlotWeightedMajorantBound
      rho highPrimitive highSupport) :
    MainConditional M rho := by
  obtain ⟨K, hK, hBracket⟩ :=
    exists_r324PaperPostCollapseBracket_of_endpoint_and_highSlot
      hEndpointPrimitive hEndpointSupport hHighPrimitive hHighSupport
      hEndpoint hHigh
  obtain ⟨step23Primitive, step23Support,
      hStep23Primitive, hStep23Support, hStep23⟩ :=
    exists_r324PaperRefinedStep23Input rho
  exact mainConditional_of_paperRefinedStep23_and_paperBracket
    hStep23Primitive hStep23Support hStep23 ⟨K, hK, hBracket⟩

/-- Final producer-facing form: the residual endpoint carrier, the
full/full endpoint carrier, and the genuinely-high selected-slot carrier
are the only remaining physical inputs. -/
theorem mainConditional_of_paperEndpointCases_and_highSlot
    {M : NoiseModel} {rho : SmoothCutoff}
    {endpointPrimitive endpointSupport : Real}
    {highPrimitive highSupport : Real}
    (hEndpointPrimitive : 0 < endpointPrimitive)
    (hEndpointSupport : 0 < endpointSupport)
    (hHighPrimitive : 0 < highPrimitive)
    (hHighSupport : 0 < highSupport)
    (hResidual : R324PaperResidualEndpointWeightedMajorantBound
      rho endpointPrimitive endpointSupport)
    (hFull : R324PaperFullEndpointWeightedMajorantBound
      rho endpointPrimitive endpointSupport)
    (hHigh : SmoothCutoff.R324PaperHighSlotWeightedMajorantBound
      rho highPrimitive highSupport) :
    MainConditional M rho :=
  mainConditional_of_paperAllShiftEndpoint_and_highSlot
    hEndpointPrimitive hEndpointSupport hHighPrimitive hHighSupport
      (R324PaperEndpointAllShiftWeightedMajorantBound.of_scheduleCases
        hResidual hFull)
      hHigh

/-- Existential producer-facing P-3.5b-det.  The two endpoint branches may
choose independent primitive constants, exactly as in the final
conditional-main wrapper below. -/
theorem r324PaperScale_hdet_of_exists_paperEndpointCases_and_highSlot
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
          SmoothCutoff.R324PaperHighSlotWeightedMajorantBound
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
  exact r324PaperScale_hdet_of_endpoint_and_highSlot rho
    hEndpointConstant hEndpointSupport hHighConstant hHighSupport
    (R324PaperEndpointAllShiftWeightedMajorantBound.of_residual_and_zeroShift
      hResidualConstant.le hFullConstant.le hResidualBound hFullBound)
    hHighBound

/-- Final existential producer interface.  The residual and full/full
endpoint proofs may choose independent primitive constants; the full/full
producer only has to work at the support radius selected by the residual
proof.  The high-slot proof remains completely independent. -/
theorem mainConditional_of_exists_paperEndpointCases_and_highSlot
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
          SmoothCutoff.R324PaperHighSlotWeightedMajorantBound
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
  exact mainConditional_of_paperAllShiftEndpoint_and_highSlot
    hEndpointConstant hEndpointSupport hHighConstant hHighSupport
    (R324PaperEndpointAllShiftWeightedMajorantBound.of_residual_and_zeroShift
      hResidualConstant.le hFullConstant.le hResidualBound hFullBound)
    hHighBound

end

end Anderson4D
