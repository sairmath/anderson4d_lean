import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedQuadProjectedCompositionProducer
import Anderson4D.DetParametrix.Paper42_Moment.R324NonzeroRoutedDensity

/-!
# Exact covariance-factor reassembly of one refined quad harvest

The canonical high-frequency covariance mode is selected separately on
each endpoint-nonzero Fourier configuration.  Consequently its lattice
mode is not constant on the complete refined fibre.  The exact object
which can be reassembled is therefore a signed double series, first over
the genuine corrected route fibres and then over the members of each
fibre.  This file keeps both sums intact.

For every member we remove exactly one covariance coefficient before the
physical integral.  We then reassemble the endpoint phases, the signed
route fibres, and the complete refined fibre.  No norm is taken on an
entity, configuration, or route.

The final analytic boundary is a single norm of the already reassembled
signed series.  In particular, this file does not replace that norm by a
sum of route norms.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace SmoothCutoff

variable (rho : SmoothCutoff)

/-! ## Removing the selected coefficient on one genuine raw member -/

/-- The actual lattice mode on the canonical selected cross-pair of one
endpoint-nonzero raw refined Fourier member. -/
def r324RefinedRawSelectedCovarianceMode
    {m : Nat} (hm : 0 < m)
    (eps : Real) (alpha beta : Z4)
    (hexternal : alpha + beta ≠ 0)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hmtrunc : m <= truncOrder eps)
    (p : R324RefinedScheduleIndex m) (a : Nat)
    (hne :
      rho.r324RefinedRawFullPairingIntegral
        hm eps alpha beta p a ≠ 0) : Z4 :=
  let e := r324RefinedRawMomentContraction p a
  let omega :=
    rho.r324RefinedRawSelectedConfigurationFiber
      hm eps alpha beta hexternal heps heps1 hmtrunc p a hne
  let selected :=
    rho.r324FirstLargeCrossSlotForNonzeroConfiguration
      eps alpha beta e.1 e.2.1 e.2.2
      hexternal heps heps1 hmtrunc omega.1
  omega.1.1 (r324CrossSlotPairIndex e.1 e.2.1 e.2.2 selected)

/-- The signed internal term after deleting only the selected covariance
coefficient.  Its character, both Green cores, and every unselected fixed
Fourier mode remain in the amplitude. -/
def r324RefinedRawOpenCovarianceCore
    {m : Nat} (hm : 0 < m)
    (eps : Real) (alpha beta : Z4)
    (hexternal : alpha + beta ≠ 0)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hmtrunc : m <= truncOrder eps)
    (p : R324RefinedScheduleIndex m) (a : Nat)
    (hne :
      rho.r324RefinedRawFullPairingIntegral
        hm eps alpha beta p a ≠ 0)
    (v : Fin (2 * m) -> T4) : Complex :=
  let e := r324RefinedRawMomentContraction p a
  let omega :=
    rho.r324RefinedRawSelectedConfigurationFiber
      hm eps alpha beta hexternal heps heps1 hmtrunc p a hne
  let selected :=
    rho.r324FirstLargeCrossSlotForNonzeroConfiguration
      eps alpha beta e.1 e.2.1 e.2.2
      hexternal heps heps1 hmtrunc omega.1
  r324RenormalizedInteriorCore e.1
      (fun i => v (leftMomentIndex i)) *
    r324RenormalizedInteriorCore e.2.1
      (fun i => v (rightMomentIndex i)) *
    charT4
      (rho.r324RefinedRawSelectedCovarianceMode
        hm eps alpha beta hexternal heps heps1 hmtrunc p a hne)
      (v (r324ResidualMarkedLowerEndpoint selected) -
        v (r324ResidualMarkedUpperEndpoint e.2.2 selected)) *
    rho.r324SelectedHighUnselectedPairModeProduct
      eps (norm (z4EuclideanFrequency (alpha + beta)))
      e.1 e.2.1 e.2.2 omega.1.1 selected v

/-- Exact pointwise removal of the selected covariance coefficient from
one selector-restricted signed internal term. -/
theorem r324RefinedRawSelectorRestrictedSignedCore_eq_coeff_mul_open
    {m : Nat} (hm : 0 < m)
    (eps : Real) (alpha beta : Z4)
    (hexternal : alpha + beta ≠ 0)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hmtrunc : m <= truncOrder eps)
    (p : R324RefinedScheduleIndex m) (a : Nat)
    (hne :
      rho.r324RefinedRawFullPairingIntegral
        hm eps alpha beta p a ≠ 0)
    (v : Fin (2 * m) -> T4) :
    rho.r324RefinedRawSelectorRestrictedSignedCore
        hm eps alpha beta hexternal heps heps1 hmtrunc
        p a hne v =
      rho.covarianceModeCoeff eps
          (rho.r324RefinedRawSelectedCovarianceMode
            hm eps alpha beta hexternal heps heps1 hmtrunc p a hne) *
        rho.r324RefinedRawOpenCovarianceCore
          hm eps alpha beta hexternal heps heps1 hmtrunc p a hne v := by
  let e := r324RefinedRawMomentContraction p a
  let omega :=
    rho.r324RefinedRawSelectedConfigurationFiber
      hm eps alpha beta hexternal heps heps1 hmtrunc p a hne
  let selected :=
    rho.r324FirstLargeCrossSlotForNonzeroConfiguration
      eps alpha beta e.1 e.2.1 e.2.2
      hexternal heps heps1 hmtrunc omega.1
  have hmode :
      omega.1.1
          (r324CrossSlotPairIndex e.1 e.2.1 e.2.2 selected) ∈
        r324HighModeSet eps
          (norm (z4EuclideanFrequency (alpha + beta))) := by
    change omega.1.1
        (rho.r324FirstLargeCrossPairIndexForNonzeroConfiguration
          eps alpha beta e.1 e.2.1 e.2.2
          hexternal heps heps1 hmtrunc omega.1) ∈
      r324HighModeSet eps
        (norm (z4EuclideanFrequency (alpha + beta)))
    exact
      rho.firstLargeCrossPairModeForNonzeroConfiguration_mem_highModeSet
        eps alpha beta e.1 e.2.1 e.2.2
        hexternal heps heps1 hmtrunc omega.1
  unfold r324RefinedRawSelectorRestrictedSignedCore
    r324SelectorRestrictedSignedInteriorMode
    r324RefinedRawOpenCovarianceCore
    r324RefinedRawSelectedCovarianceMode
  dsimp only
  unfold r324HighCovarianceModeTerm
  rw [Set.indicator_of_mem hmode]
  unfold r324CovarianceModeTerm
  ring

/-! ## Endpoint phases and the physical integral -/

/-- The complete five-group physical integrand after removal of the one
selected covariance coefficient. -/
def r324RefinedRawOpenCovarianceIntegrand
    {m : Nat} (hm : 0 < m)
    (eps : Real) (alpha beta : Z4)
    (hexternal : alpha + beta ≠ 0)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hmtrunc : m <= truncOrder eps)
    (p : R324RefinedScheduleIndex m) (a : Nat)
    (hne :
      rho.r324RefinedRawFullPairingIntegral
        hm eps alpha beta p a ≠ 0)
    (x y z w : T4) (v : Fin (2 * m) -> T4) : Complex :=
  let e := r324RefinedRawMomentContraction p a
  r324EndpointSeparatedIntegrand alpha beta
    (r324ContractionEndpointAnchors hm e v)
    (r324ContractionEndpointFlags e)
    (rho.r324RefinedRawOpenCovarianceCore
      hm eps alpha beta hexternal heps heps1 hmtrunc p a hne v)
    x y z w

/-- Exact coefficient removal survives all four endpoint phases
pointwise. -/
theorem r324RefinedRawEndpointIntegrand_eq_coeff_mul_open
    {m : Nat} (hm : 0 < m)
    (eps : Real) (alpha beta : Z4)
    (hexternal : alpha + beta ≠ 0)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hmtrunc : m <= truncOrder eps)
    (p : R324RefinedScheduleIndex m) (a : Nat)
    (hne :
      rho.r324RefinedRawFullPairingIntegral
        hm eps alpha beta p a ≠ 0)
    (x y z w : T4) (v : Fin (2 * m) -> T4) :
    rho.r324RefinedRawEndpointIntegrand
        hm eps alpha beta p a x y z w v =
      rho.covarianceModeCoeff eps
          (rho.r324RefinedRawSelectedCovarianceMode
            hm eps alpha beta hexternal heps heps1 hmtrunc p a hne) *
        rho.r324RefinedRawOpenCovarianceIntegrand
          hm eps alpha beta hexternal heps heps1 hmtrunc
          p a hne x y z w v := by
  rw [rho.r324RefinedRawEndpointIntegrand_eq_selectorRestrictedSigned
    hm eps alpha beta hexternal heps heps1 hmtrunc
    p a hne x y z w v]
  rw [rho.r324RefinedRawSelectorRestrictedSignedCore_eq_coeff_mul_open
    hm eps alpha beta hexternal heps heps1 hmtrunc p a hne v]
  unfold r324RefinedRawOpenCovarianceIntegrand
    r324EndpointSeparatedIntegrand
  dsimp only
  ring

/-- The complete physical coefficient of one raw member is its selected
covariance coefficient times the signed open physical integral. -/
theorem r324RefinedRawFullPairingIntegral_eq_coeff_mul_openIntegral
    {m : Nat} (hm : 0 < m)
    (eps : Real) (alpha beta : Z4)
    (hexternal : alpha + beta ≠ 0)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hmtrunc : m <= truncOrder eps)
    (p : R324RefinedScheduleIndex m) (a : Nat)
    (hne :
      rho.r324RefinedRawFullPairingIntegral
        hm eps alpha beta p a ≠ 0) :
    rho.r324RefinedRawFullPairingIntegral
        hm eps alpha beta p a =
      rho.covarianceModeCoeff eps
          (rho.r324RefinedRawSelectedCovarianceMode
            hm eps alpha beta hexternal heps heps1 hmtrunc p a hne) *
        (∫ q,
          r324Flatten
            (rho.r324RefinedRawOpenCovarianceIntegrand
              hm eps alpha beta hexternal heps heps1 hmtrunc
              p a hne) q
          ∂(r324PhysicalMeasure m)) := by
  let c : Complex :=
    rho.covarianceModeCoeff eps
      (rho.r324RefinedRawSelectedCovarianceMode
        hm eps alpha beta hexternal heps heps1 hmtrunc p a hne)
  let f : R324PhysicalPoint m -> Complex :=
    r324Flatten (rho.r324RefinedRawEndpointIntegrand
      hm eps alpha beta p a)
  let g : R324PhysicalPoint m -> Complex :=
    r324Flatten (rho.r324RefinedRawOpenCovarianceIntegrand
      hm eps alpha beta hexternal heps heps1 hmtrunc p a hne)
  have hpoint : forall q, f q = c * g q := by
    intro q
    exact rho.r324RefinedRawEndpointIntegrand_eq_coeff_mul_open
      hm eps alpha beta hexternal heps heps1 hmtrunc p a hne
      q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
  calc
    rho.r324RefinedRawFullPairingIntegral
        hm eps alpha beta p a =
        (∫ q, f q ∂(r324PhysicalMeasure m)) :=
      (rho.integral_r324Flatten_refinedRawEndpointIntegrand_eq_rawFullPairingIntegral
        hm eps alpha beta p a).symm
    _ = (∫ q, c * g q ∂(r324PhysicalMeasure m)) :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = c * (∫ q, g q ∂(r324PhysicalMeasure m)) :=
      integral_const_mul c g

/-! ## Complete signed refined-fibre reassembly -/

/-- The signed series which remains after one covariance coefficient has
been removed separately on every endpoint-nonzero Fourier member.  The
outer route partition and each inner fibre sum are both retained exactly. -/
def r324RefinedQuadOpenCovarianceSeries
    {m : Nat} (hm : 0 < m)
    (eps : Real) (alpha beta : Z4)
    (hexternal : alpha + beta ≠ 0)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hmtrunc : m <= truncOrder eps)
    (p : R324RefinedScheduleIndex m) : Complex :=
  tsum fun route : R324NonzeroRouteLabel m =>
    tsum fun a :
        rho.R324RefinedEndpointNonzeroRouteFiber
          hm eps alpha beta hexternal heps heps1 hmtrunc p route =>
      rho.covarianceModeCoeff eps
          (rho.r324RefinedRawSelectedCovarianceMode
            hm eps alpha beta hexternal heps heps1 hmtrunc
            p a.1.1 a.1.2) *
        (∫ q,
          r324Flatten
            (rho.r324RefinedRawOpenCovarianceIntegrand
              hm eps alpha beta hexternal heps heps1 hmtrunc
              p a.1.1 a.1.2) q
          ∂(r324PhysicalMeasure m))

/-- **Exact full-fibre covariance reassembly.**  The endpoint-decay
multiple of the complete quad harvest is precisely the signed open series.
No triangle inequality occurs in this identity. -/
theorem endpointDecay_mul_r324BetaQuadHarvest_eq_openCovarianceSeries
    {m : Nat} (hm : 0 < m)
    (eps : Real) (alpha beta : Z4)
    (hexternal : alpha + beta ≠ 0)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hmtrunc : m <= truncOrder eps)
    (p : R324RefinedScheduleIndex m) :
    (((paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta : Real) : Complex) *
        r324BetaQuadHarvest rho eps m alpha beta hm
          (momentRefinedContractionFiber m p.1.1 p.2.1)) =
      rho.r324RefinedQuadOpenCovarianceSeries
        hm eps alpha beta hexternal heps heps1 hmtrunc p := by
  calc
    (((paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta : Real) : Complex) *
        r324BetaQuadHarvest rho eps m alpha beta hm
          (momentRefinedContractionFiber m p.1.1 p.2.1)) =
        ∑ e ∈ momentRefinedContractionFiber m p.1.1 p.2.1,
          deterministicMomentContractionTerm rho eps m alpha beta e :=
      (r324Beta_sum_eq_endpointDecays_mul_quadHarvest
        rho heps heps1 hm alpha beta
        (momentRefinedContractionFiber m p.1.1 p.2.1)).symm
    _ = r324RefinedPhysicalIntegral rho eps m alpha beta p :=
      (r324RefinedPhysicalIntegral_eq_sum_contractionTerms
        rho heps heps1 alpha beta p).symm
    _ = tsum fun route : R324NonzeroRouteLabel m =>
          ∫ q,
            rho.r324RefinedEndpointNonzeroRoutePhysicalCore
              hm eps alpha beta hexternal heps heps1 hmtrunc
              p route q
            ∂(r324PhysicalMeasure m) :=
      rho.r324RefinedPhysicalIntegral_eq_nonzeroRoutePhysicalCore
        hm heps alpha beta hexternal heps1 hmtrunc p
    _ = tsum fun route : R324NonzeroRouteLabel m =>
          tsum fun a :
              rho.R324RefinedEndpointNonzeroRouteFiber
                hm eps alpha beta hexternal heps heps1 hmtrunc p route =>
            rho.r324RefinedRawFullPairingIntegral
              hm eps alpha beta p a.1.1 := by
      apply tsum_congr
      intro route
      exact rho.integral_r324RefinedEndpointNonzeroRoutePhysicalCore
        hm heps alpha beta hexternal heps1 hmtrunc p route
    _ = rho.r324RefinedQuadOpenCovarianceSeries
          hm eps alpha beta hexternal heps heps1 hmtrunc p := by
      unfold r324RefinedQuadOpenCovarianceSeries
      apply tsum_congr
      intro route
      apply tsum_congr
      intro a
      exact
        rho.r324RefinedRawFullPairingIntegral_eq_coeff_mul_openIntegral
          hm eps alpha beta hexternal heps heps1 hmtrunc
          p a.1.1 a.1.2

/-! ## Signed open-series bound -/

/-- A cancellation-preserving bound on the already reassembled signed
open series.  This is intentionally one norm of the complete series, not
a `tsum` of route or entity norms. -/
def R324RefinedQuadOpenCovarianceSeriesBound
    (rho : SmoothCutoff) (K : Real) : Prop :=
  ∀ {eps : Real} (m : Nat) (alpha beta : Z4)
    (heps : 0 < eps) (hepssmall : eps <= 1 / 4)
    (hlog : 1 <= abs (Real.log eps)) (hm2 : 2 <= m)
    (hmtrunc : m <= truncOrder eps) (hexternal : alpha + beta ≠ 0)
    (hm : 0 < m) (p : R324RefinedScheduleIndex m),
          norm (rho.r324RefinedQuadOpenCovarianceSeries
            hm eps alpha beta hexternal heps
              (hepssmall.trans (by norm_num)) hmtrunc p) <=
            (paperFourthOrderModeDecay alpha *
                paperFourthOrderModeDecay beta) *
              ((m : Real) ^ 8 * K ^ m * abs (Real.log eps) ^ (m - 1) *
                eps⁻¹ ^ (8 : Nat) *
                  eighthOrderFrequencyDecay
                    (eps ^ 2 * norm (z4EuclideanFrequency (alpha + beta))))

/-- The preceding whole-series estimate gives the desired paper-scale
quad-harvest estimate by cancelling the strictly positive endpoint
decays. -/
theorem norm_r324BetaQuadHarvest_le_of_openCovarianceSeriesBound
    {m : Nat} (hm : 0 < m)
    (eps : Real) (alpha beta : Z4)
    (hexternal : alpha + beta ≠ 0)
    (heps : 0 < eps) (hepssmall : eps <= 1 / 4)
    (hlog : 1 <= abs (Real.log eps))
    (hm2 : 2 <= m) (hmtrunc : m <= truncOrder eps)
    (p : R324RefinedScheduleIndex m)
    {K : Real}
    (hbound : R324RefinedQuadOpenCovarianceSeriesBound rho K) :
    norm (r324BetaQuadHarvest rho eps m alpha beta hm
        (momentRefinedContractionFiber m p.1.1 p.2.1)) <=
      (m : Real) ^ 8 * K ^ m * abs (Real.log eps) ^ (m - 1) *
        (eps⁻¹ ^ (8 : Nat) *
          eighthOrderFrequencyDecay
            (eps ^ 2 * norm (z4EuclideanFrequency (alpha + beta)))) := by
  have heps1 : eps <= 1 := hepssmall.trans (by norm_num)
  have hseries :=
    hbound m alpha beta heps hepssmall hlog hm2 hmtrunc
      hexternal hm p
  have hendpoint :
      0 < paperFourthOrderModeDecay alpha *
        paperFourthOrderModeDecay beta :=
    mul_pos (paperFourthOrderModeDecay_pos alpha)
      (paperFourthOrderModeDecay_pos beta)
  rw [← rho.endpointDecay_mul_r324BetaQuadHarvest_eq_openCovarianceSeries
    hm eps alpha beta hexternal heps heps1 hmtrunc p,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hendpoint] at hseries
  simpa only [mul_assoc] using
    (le_of_mul_le_mul_left hseries hendpoint)

end SmoothCutoff

end

end Anderson4D
