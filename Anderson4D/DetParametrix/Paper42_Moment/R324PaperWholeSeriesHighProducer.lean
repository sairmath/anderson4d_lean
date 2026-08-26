import Anderson4D.DetParametrix.Paper42_Moment.R324PaperWholeSeriesCapstone
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperFullFullFrequency
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointCommonLeftCanonical
import Anderson4D.DetParametrix.Paper42_Moment.R324ResidualCommonLeftFourier
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperMixedCutoffCompleteRun
import Anderson4D.DetParametrix.Paper42_Moment.R324DerivativeLossAbsorption
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTwoHalfRouteAssembly

/-!
# Paper Step 4(B): whole-series high-frequency producer

Paper: R-324 — §4.2 Step 4(B), whole-series high-frequency producer

The common-left Fourier argument is needed only when the canonical refined
representative has a residual single.  If both halves are full, the whole
physical integral vanishes at a non-zero conserved external mode.  This file
records that dichotomy at the exact boundary required by the final capstone.

Keeping the residual input at the complete signed-series boundary is
intentional: no selected-slot, first-high, cell, or contraction-wise triangle
inequality occurs here.  The analytic residual producer is supplied by the
endpoint common-left Fourier identity, the grouped residual Fourier estimate,
and the mixed-cutoff complete nested run imported above.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace SmoothCutoff

/-! ## Absorbing the common-left Haar average -/

/-- Normalized common-left Haar average of a nonnegative auxiliary
coefficient.  The normalization is the paper's (non-probability) torus
mass. -/
def r324CommonLeftHaarAverage
    {I J : Type*}
    (auxiliary : (I -> T4) -> (J -> T4) -> Real)
    (left : I -> T4) (right : J -> T4) : Real :=
  r324PaperTorusMass⁻¹ *
    ∫ a : T4,
      auxiliary (R324WithinHalfResidualPrefix.r324CommonTranslate a left)
      right
      ∂paperMeasure

theorem r324CommonLeftHaarAverage_nonneg
    {I J : Type*}
    (auxiliary : (I -> T4) -> (J -> T4) -> Real)
    (hauxiliary : forall (left : I -> T4) (right : J -> T4),
      0 <= auxiliary left right)
    (left : I -> T4) (right : J -> T4) :
    0 <= r324CommonLeftHaarAverage auxiliary left right := by
  unfold r324CommonLeftHaarAverage
  exact mul_nonneg (inv_nonneg.mpr r324PaperTorusMass_pos.le)
    (integral_nonneg fun a => hauxiliary _ _)

/-- One coordinate of a four-dimensional lattice mode carries at least half
of its Euclidean size.  The factor two is exactly `sqrt 4`; the selected
coordinate itself is an honest maximum for the auxiliary sup norm. -/
theorem exists_frequencyCoordinate_two_mul_abs_ge_euclidean
    (mode : Z4) :
    exists coord : Fin dim,
      norm (z4EuclideanFrequency mode) <= 2 * abs (mode coord : Real) := by
  let f : Fin dim -> Real := fun i => (mode i : Real)
  obtain ⟨coord, hcoord⟩ := (IsGreatest.pi_norm f).1
  refine ⟨coord, (norm_z4EuclideanFrequency_le_two_mul_frequencyNorm mode).trans_eq ?_⟩
  unfold z4FrequencyNorm
  change 2 * norm f = 2 * abs (mode coord : Real)
  rw [← hcoord]
  simp only [f, Real.norm_eq_abs]

/-- At the high-frequency threshold, the inverse eighth power of a coordinate
carrying half the Euclidean norm is absorbed by the paper's central bracket.
The explicit constant is `2^8 * 2^4 = 4096`. -/
theorem eps_inv_pow_eight_mul_inv_frequencyCoordinate_pow_eight_le_centralDecay
    {eps L a : Real} (heps : 0 < eps) (heps1 : eps <= 1)
    (hL : 0 <= L) (hcoord : L <= 2 * a)
    (hlarge : 1 <= eps ^ 2 * L) :
    eps⁻¹ ^ 8 * a⁻¹ ^ 8 <=
      4096 * eighthOrderFrequencyDecay (eps ^ 2 * L) := by
  let x := eps ^ 2 * L
  have hx : 1 <= x := hlarge
  have hx0 : 0 <= x := zero_le_one.trans hx
  have hLpos : 0 < L := by
    by_contra h
    have hL0 : L = 0 := le_antisymm (le_of_not_gt h) hL
    simp only [hL0, mul_zero] at hlarge
    norm_num at hlarge
  have ha : 0 < a := by nlinarith
  have hbracket : 1 + x ^ 2 <= 2 * x ^ 2 := by
    nlinarith [sq_nonneg (x - 1)]
  have hbracketPow : (1 + x ^ 2) ^ 4 <= 16 * x ^ 8 := by
    calc
      (1 + x ^ 2) ^ 4 <= (2 * x ^ 2) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hbracket 4
      _ = 16 * x ^ 8 := by ring
  have hepsPowEight : eps ^ 8 <= 1 :=
    pow_le_one₀ heps.le heps1
  have hLPow : L ^ 8 <= 256 * a ^ 8 := by
    calc
      L ^ 8 <= (2 * a) ^ 8 :=
        pow_le_pow_left₀ hL hcoord 8
      _ = 256 * a ^ 8 := by ring
  have hxPow : x ^ 8 <= eps ^ 16 * (256 * a ^ 8) := by
    calc
      x ^ 8 = eps ^ 16 * L ^ 8 := by
        dsimp only [x]
        ring
      _ <= eps ^ 16 * (256 * a ^ 8) :=
        mul_le_mul_of_nonneg_left hLPow (by positivity)
  have hdenom :
      (1 + x ^ 2) ^ 4 <= 4096 * eps ^ 16 * a ^ 8 := by
    calc
      (1 + x ^ 2) ^ 4 <= 16 * x ^ 8 := hbracketPow
      _ <= 16 * (eps ^ 16 * (256 * a ^ 8)) :=
        mul_le_mul_of_nonneg_left hxPow (by norm_num)
      _ = 4096 * eps ^ 16 * a ^ 8 := by ring
  unfold eighthOrderFrequencyDecay
  rw [le_mul_inv_iff₀ (by positivity)]
  calc
    (eps⁻¹ ^ 8 * a⁻¹ ^ 8) *
        (1 + (eps ^ 2 * L) ^ 2) ^ 4 =
      (eps⁻¹ ^ 8 * a⁻¹ ^ 8) * (1 + x ^ 2) ^ 4 := by rfl
    _ <= (eps⁻¹ ^ 8 * a⁻¹ ^ 8) *
        (4096 * eps ^ 16 * a ^ 8) :=
      mul_le_mul_of_nonneg_left hdenom (by positivity)
    _ = 4096 * eps ^ 8 := by
      field_simp [heps.ne', ha.ne']
    _ <= 4096 := by
      calc
        4096 * eps ^ 8 <= 4096 * 1 :=
          mul_le_mul_of_nonneg_left hepsPowEight (by norm_num)
        _ = 4096 := by ring

/-- The coordinate subgroup used by the one-dimensional Fourier estimate is
literally the restriction of the canonical left-copy torus translation. -/
theorem r324LeftInternalTranslate_coordinateDisplacement_eq_commonLeftMomentTranslation
    {m : Nat} (v : Fin (2 * m) -> T4) (coord : Fin dim) (t : Real) :
    r324LeftInternalTranslateMeasurableEquiv m
        (r324CoordinateDisplacementT4 coord t) v =
      r324CommonLeftMomentTranslation v coord t := by
  funext i
  rw [r324LeftInternalTranslateMeasurableEquiv_apply]
  rfl

theorem r324LeftInternalTranslate_add
    {m : Nat} (v : Fin (2 * m) -> T4) (a b : T4) :
    r324LeftInternalTranslateMeasurableEquiv m b
        (r324LeftInternalTranslateMeasurableEquiv m a v) =
      r324LeftInternalTranslateMeasurableEquiv m (a + b) v := by
  funext i
  simp only [r324LeftInternalTranslateMeasurableEquiv_apply]
  by_cases hi : i.val < m
  · simp only [hi, if_pos]
    abel
  · simp only [hi, if_false]

/-- The complete grouped residual coefficient, translated as one signed
family, is integrable against a torus character.  This uses the repository's
existing measurable and uniform-bound theorems for the *whole* residual sum;
no primitive-coordinate triangle inequality is introduced here. -/
theorem integrable_char_mul_r324ResidualPrimitiveSumProduct_leftTranslate
    (rho : SmoothCutoff) {eps : Real} (heps : 0 < eps) (heps1 : eps <= 1)
    {m : Nat} (kappaPlus kappaMinus : PartialPairing (Fin m))
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (mode : Z4) (v : Fin (2 * m) -> T4) :
    Integrable
      (fun a : T4 =>
        charT4 mode a *
          (r324ResidualPrimitiveSumProduct rho eps
            kappaPlus kappaMinus pi
              (r324LeftInternalTranslateMeasurableEquiv m a v) : Complex))
      paperMeasure := by
  have htranslate : Measurable
      (fun a : T4 => r324LeftInternalTranslateMeasurableEquiv m a v) := by
    apply measurable_pi_lambda
    intro i
    simp only [r324LeftInternalTranslateMeasurableEquiv_apply]
    by_cases hi : i.val < m
    · simp only [hi, if_pos]
      exact measurable_const.add measurable_id
    · simp only [hi]
      exact measurable_const
  have hresidual : Measurable
      (fun a : T4 =>
        (r324ResidualPrimitiveSumProduct rho eps
          kappaPlus kappaMinus pi
            (r324LeftInternalTranslateMeasurableEquiv m a v) : Complex)) :=
    (rho.measurable_r324ResidualPrimitiveSumProduct
      eps kappaPlus kappaMinus pi).complex_ofReal.comp htranslate
  obtain ⟨bound, _hboundNonneg, hbound⟩ :=
    rho.exists_norm_r324ResidualPrimitiveSumProduct_le
      heps heps1 kappaPlus kappaMinus pi
  apply Integrable.of_bound
    ((continuous_charT4 mode).measurable.mul hresidual).aestronglyMeasurable
    bound
  filter_upwards with a
  change norm (charT4 mode a *
      (r324ResidualPrimitiveSumProduct rho eps
        kappaPlus kappaMinus pi
          (r324LeftInternalTranslateMeasurableEquiv m a v) : Complex)) <= bound
  rw [norm_mul, norm_charT4, one_mul, Complex.norm_real]
  exact hbound _

/-- The full four-dimensional common-left Fourier coefficient of one grouped
residual primitive sum. -/
def r324ResidualCommonLeftTorusCoefficient
    (rho : SmoothCutoff) (eps : Real) {m : Nat}
    (kappaPlus kappaMinus : PartialPairing (Fin m))
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (mode : Z4) (v : Fin (2 * m) -> T4) : Complex :=
  (r324PaperTorusMass : Complex)⁻¹ *
    ∫ a : T4,
      charT4 mode a *
        (r324ResidualPrimitiveSumProduct rho eps
          kappaPlus kappaMinus pi
            (r324LeftInternalTranslateMeasurableEquiv m a v) : Complex)
      ∂paperMeasure

/-- Averaging a function over one coordinate subgroup and over full torus
Haar gives exactly `2π` times its original integral.  This is the Fubini
normalization seam used twice below: once for the signed coefficient and once
for its nonnegative auxiliary majorant. -/
theorem integral_commonLeftCoordinateShift_eq_two_pi_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [CompleteSpace E]
    (coord : Fin dim) (f : T4 -> E)
    (hjoint : Integrable
      (Function.uncurry fun t : Real => fun a : T4 =>
        f (a + r324CoordinateDisplacementT4 coord t))
      ((volume.restrict (Set.uIoc (-Real.pi) Real.pi)).prod paperMeasure)) :
    (∫ a : T4,
        (∫ t in -Real.pi..Real.pi,
          f (a + r324CoordinateDisplacementT4 coord t))
        ∂paperMeasure) =
      (2 * Real.pi) • ∫ a : T4, f a ∂paperMeasure := by
  have hshift (t : Real) :
      (∫ a : T4, f (a + r324CoordinateDisplacementT4 coord t)
          ∂paperMeasure) =
        ∫ a : T4, f a ∂paperMeasure := by
    rw [paperMeasure_eq_volume]
    let e : T4 ≃ᵐ T4 :=
      MeasurableEquiv.addRight (r324CoordinateDisplacementT4 coord t)
    have hp : MeasurePreserving e (volume : Measure T4) volume := by
      change MeasurePreserving
        (fun x : T4 => x + r324CoordinateDisplacementT4 coord t)
        volume volume
      exact
        measurePreserving_add_right (volume : Measure T4)
          (r324CoordinateDisplacementT4 coord t)
    exact hp.integral_comp' f
  calc
    (∫ a : T4,
        (∫ t in -Real.pi..Real.pi,
          f (a + r324CoordinateDisplacementT4 coord t))
        ∂paperMeasure) =
      ∫ t in -Real.pi..Real.pi,
        ∫ a : T4, f (a + r324CoordinateDisplacementT4 coord t)
          ∂paperMeasure :=
      (MeasureTheory.intervalIntegral_integral_swap hjoint).symm
    _ = ∫ _t in -Real.pi..Real.pi,
        ∫ a : T4, f a ∂paperMeasure := by
      apply intervalIntegral.integral_congr
      intro t _ht
      exact hshift t
    _ = (2 * Real.pi) • ∫ a : T4, f a ∂paperMeasure := by
      rw [intervalIntegral.integral_const]
      congr 1
      ring

/-- The interval-parameterized coordinate shift projects quasi-preservingly
to full torus Haar. -/
theorem quasiMeasurePreserving_commonLeftCoordinateShift
    (coord : Fin dim) :
    Measure.QuasiMeasurePreserving
      (fun q : Real × T4 =>
        q.2 + r324CoordinateDisplacementT4 coord q.1)
      ((volume.restrict (Set.uIoc (-Real.pi) Real.pi)).prod paperMeasure)
      paperMeasure := by
  have hdisplacement : Measurable
      (r324CoordinateDisplacementT4 coord) := by
    apply measurable_pi_lambda
    intro i
    unfold r324CoordinateDisplacementT4 periodizeR4
      r324CoordinateDisplacementR4
    by_cases h : i = coord
    · subst i
      simp only [Function.update_self]
      fun_prop
    · simp only [Function.update_of_ne h]
      fun_prop
  apply QuasiMeasurePreserving.prod_of_right
  · exact measurable_snd.add (hdisplacement.comp measurable_fst)
  · filter_upwards with t
    rw [paperMeasure_eq_volume]
    exact (measurePreserving_add_right (volume : Measure T4)
      (r324CoordinateDisplacementT4 coord t)).quasiMeasurePreserving

theorem integrable_commonLeftCoordinateShift_char_mul_residual
    (rho : SmoothCutoff) {eps : Real} (heps : 0 < eps) (heps1 : eps <= 1)
    {m : Nat} (kappaPlus kappaMinus : PartialPairing (Fin m))
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (mode : Z4) (v : Fin (2 * m) -> T4) (coord : Fin dim) :
    Integrable
      (Function.uncurry fun t : Real => fun a : T4 =>
        charT4 mode (a + r324CoordinateDisplacementT4 coord t) *
          (r324ResidualPrimitiveSumProduct rho eps
            kappaPlus kappaMinus pi
              (r324LeftInternalTranslateMeasurableEquiv m
                (a + r324CoordinateDisplacementT4 coord t) v) : Complex))
      ((volume.restrict (Set.uIoc (-Real.pi) Real.pi)).prod paperMeasure) := by
  letI : IsFiniteMeasure
      (volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := by
    rw [Set.uIoc_of_le (neg_le_self Real.pi_pos.le)]
    infer_instance
  have hbase :=
    integrable_char_mul_r324ResidualPrimitiveSumProduct_leftTranslate
      rho heps heps1 kappaPlus kappaMinus pi mode v
  have hmeas := hbase.aestronglyMeasurable.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_commonLeftCoordinateShift coord)
  obtain ⟨bound, _hboundNonneg, hbound⟩ :=
    rho.exists_norm_r324ResidualPrimitiveSumProduct_le
      heps heps1 kappaPlus kappaMinus pi
  have hmeas' : AEStronglyMeasurable
      (Function.uncurry fun t : Real => fun a : T4 =>
        charT4 mode (a + r324CoordinateDisplacementT4 coord t) *
          (r324ResidualPrimitiveSumProduct rho eps
            kappaPlus kappaMinus pi
              (r324LeftInternalTranslateMeasurableEquiv m
                (a + r324CoordinateDisplacementT4 coord t) v) : Complex))
      ((volume.restrict (Set.uIoc (-Real.pi) Real.pi)).prod paperMeasure) := by
    apply hmeas.congr
    filter_upwards with q
    rfl
  apply Integrable.of_bound hmeas' bound
  filter_upwards with q
  change norm (charT4 mode
      (q.2 + r324CoordinateDisplacementT4 coord q.1) *
        (r324ResidualPrimitiveSumProduct rho eps
          kappaPlus kappaMinus pi
            (r324LeftInternalTranslateMeasurableEquiv m
              (q.2 + r324CoordinateDisplacementT4 coord q.1) v) : Complex)) <= bound
  rw [norm_mul, norm_charT4, one_mul, Complex.norm_real]
  exact hbound _

theorem integrable_r324ResidualPrimitiveSumProduct_leftTranslate
    (rho : SmoothCutoff) {eps : Real} (heps : 0 < eps) (heps1 : eps <= 1)
    {m : Nat} (kappaPlus kappaMinus : PartialPairing (Fin m))
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (v : Fin (2 * m) -> T4) :
    Integrable
      (fun a : T4 =>
        r324ResidualPrimitiveSumProduct rho eps
          kappaPlus kappaMinus pi
            (r324LeftInternalTranslateMeasurableEquiv m a v))
      paperMeasure := by
  have h :=
    integrable_char_mul_r324ResidualPrimitiveSumProduct_leftTranslate
      rho heps heps1 kappaPlus kappaMinus pi 0 v
  apply h.norm.congr
  filter_upwards with a
  rw [charT4_zero, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  exact r324ResidualPrimitiveSumProduct_nonneg rho eps
    kappaPlus kappaMinus pi _

theorem integrable_commonLeftCoordinateShift_residual
    (rho : SmoothCutoff) {eps : Real} (heps : 0 < eps) (heps1 : eps <= 1)
    {m : Nat} (kappaPlus kappaMinus : PartialPairing (Fin m))
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (v : Fin (2 * m) -> T4) (coord : Fin dim) :
    Integrable
      (Function.uncurry fun t : Real => fun a : T4 =>
        r324ResidualPrimitiveSumProduct rho eps
          kappaPlus kappaMinus pi
            (r324LeftInternalTranslateMeasurableEquiv m
              (a + r324CoordinateDisplacementT4 coord t) v))
      ((volume.restrict (Set.uIoc (-Real.pi) Real.pi)).prod paperMeasure) := by
  have h :=
    integrable_commonLeftCoordinateShift_char_mul_residual
      rho heps heps1 kappaPlus kappaMinus pi 0 v coord
  apply h.norm.congr
  filter_upwards with q
  change norm (charT4 0
      (q.2 + r324CoordinateDisplacementT4 coord q.1) *
        (r324ResidualPrimitiveSumProduct rho eps
          kappaPlus kappaMinus pi
            (r324LeftInternalTranslateMeasurableEquiv m
              (q.2 + r324CoordinateDisplacementT4 coord q.1) v) : Complex)) =
    r324ResidualPrimitiveSumProduct rho eps kappaPlus kappaMinus pi
      (r324LeftInternalTranslateMeasurableEquiv m
        (q.2 + r324CoordinateDisplacementT4 coord q.1) v)
  rw [charT4_zero, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  exact r324ResidualPrimitiveSumProduct_nonneg rho eps
    kappaPlus kappaMinus pi _

/-- Exact partial-Fourier decomposition of the normalized full-torus
coefficient.  The common coordinate is averaged only after the complete
signed source has been formed. -/
theorem normalized_torusCoefficient_eq_integral_coordinateFourierCoeffOn
    (mode : Z4) (coord : Fin dim) (source : T4 -> Complex)
    (hjoint : Integrable
      (Function.uncurry fun t : Real => fun a : T4 =>
        charT4 mode (a + r324CoordinateDisplacementT4 coord t) *
          source (a + r324CoordinateDisplacementT4 coord t))
      ((volume.restrict (Set.uIoc (-Real.pi) Real.pi)).prod paperMeasure)) :
    (r324PaperTorusMass : Complex)⁻¹ *
        ∫ a : T4, charT4 mode a * source a ∂paperMeasure =
      (r324PaperTorusMass : Complex)⁻¹ *
        ∫ a : T4,
          charT4 mode a *
            fourierCoeffOn (neg_lt_self Real.pi_pos)
              (fun t : Real =>
                source (a + r324CoordinateDisplacementT4 coord t))
              (-(mode coord))
          ∂paperMeasure := by
  let F : T4 -> Complex := fun a => charT4 mode a * source a
  have havg :=
    integral_commonLeftCoordinateShift_eq_two_pi_smul coord F hjoint
  have hinner (a : T4) :
      charT4 mode a *
          fourierCoeffOn (neg_lt_self Real.pi_pos)
            (fun t : Real =>
              source (a + r324CoordinateDisplacementT4 coord t))
            (-(mode coord)) =
        ((2 * Real.pi : Real) : Complex)⁻¹ *
          ∫ t in -Real.pi..Real.pi,
            F (a + r324CoordinateDisplacementT4 coord t) := by
    rw [fourierCoeffOn_eq_integral]
    simp only [neg_neg, smul_eq_mul]
    rw [show Real.pi - -Real.pi = 2 * Real.pi by ring]
    rw [Complex.real_smul, ← mul_assoc]
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    unfold F
    dsimp only
    rw [charT4_add_argument, charT4_coordinateDisplacementT4]
    push_cast
    ring
  have htwoPi : ((2 * Real.pi : Real) : Complex) ≠ 0 := by
    exact_mod_cast (mul_pos (by norm_num : (0 : Real) < 2) Real.pi_pos).ne'
  congr 1
  calc
    (∫ a : T4, charT4 mode a * source a ∂paperMeasure) =
        ((2 * Real.pi : Real) : Complex)⁻¹ *
          ∫ a : T4,
            (∫ t in -Real.pi..Real.pi,
              F (a + r324CoordinateDisplacementT4 coord t))
            ∂paperMeasure := by
      change (∫ a : T4, F a ∂paperMeasure) = _
      rw [havg]
      change _ = ((2 * Real.pi : Real) : Complex)⁻¹ *
        (((2 * Real.pi : Real) : Complex) * _)
      field_simp [htwoPi]
    _ = ∫ a : T4,
          charT4 mode a *
            fourierCoeffOn (neg_lt_self Real.pi_pos)
              (fun t : Real =>
                source (a + r324CoordinateDisplacementT4 coord t))
              (-(mode coord))
          ∂paperMeasure := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with a
      exact (hinner a).symm

/-- Concrete exact decomposition of the grouped residual torus coefficient
into one-dimensional coordinate Fourier coefficients. -/
theorem r324ResidualCommonLeftTorusCoefficient_eq_integral_fourierCoeffOn
    (rho : SmoothCutoff) {eps : Real} (heps : 0 < eps) (heps1 : eps <= 1)
    {m : Nat} (e0 : MomentContraction m)
    (mode : Z4) (v : Fin (2 * m) -> T4) (coord : Fin dim) :
    r324ResidualCommonLeftTorusCoefficient rho eps
        e0.1 e0.2.1 e0.2.2 mode v =
      (r324PaperTorusMass : Complex)⁻¹ *
        ∫ a : T4,
          charT4 mode a *
            fourierCoeffOn (neg_lt_self Real.pi_pos)
              (r324ResidualPrimitiveSumCommonLeftCoordLineC rho eps e0
                (r324LeftInternalTranslateMeasurableEquiv m a v) coord)
              (-(mode coord))
          ∂paperMeasure := by
  unfold r324ResidualCommonLeftTorusCoefficient
  rw [normalized_torusCoefficient_eq_integral_coordinateFourierCoeffOn
    mode coord
    (fun a : T4 =>
      (r324ResidualPrimitiveSumProduct rho eps
        e0.1 e0.2.1 e0.2.2
          (r324LeftInternalTranslateMeasurableEquiv m a v) : Complex))
    (integrable_commonLeftCoordinateShift_char_mul_residual
      rho heps heps1 e0.1 e0.2.1 e0.2.2 mode v coord)]
  apply congrArg (fun z : Complex =>
    (r324PaperTorusMass : Complex)⁻¹ * z)
  apply integral_congr_ae
  filter_upwards with a
  apply congrArg (fun z : Complex => charT4 mode a * z)
  symm
  apply congrFun
  apply fourierCoeffOn_congr_ae (neg_lt_self Real.pi_pos)
  filter_upwards with t
  unfold r324ResidualPrimitiveSumCommonLeftCoordLineC
  rw [← r324LeftInternalTranslate_coordinateDisplacement_eq_commonLeftMomentTranslation]
  rw [r324LeftInternalTranslate_add]

/-- Global grouped Step 4(B) Fourier estimate at one nonzero coordinate.
The `2π` in the one-dimensional Fourier coefficient cancels exactly against
the coordinate-subgroup Haar average. -/
theorem norm_r324ResidualCommonLeftTorusCoefficient_le_auxiliaryHaarAverage
    (rho : SmoothCutoff) {eps : Real} (heps : 0 < eps) (heps1 : eps <= 1)
    {m : Nat} (e0 : MomentContraction m)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (mode : Z4) (v : Fin (2 * m) -> T4) (coord : Fin dim)
    (hcoord : mode coord ≠ 0) :
    norm (r324ResidualCommonLeftTorusCoefficient rho eps
        e0.1 e0.2.1 e0.2.2 mode v) <=
      (abs (mode coord : Real)⁻¹ ^ 8 *
        ((m : Real) ^ 8 *
          r324ResidualFourierMajorantBase rho ^ (3 * m) * eps⁻¹ ^ 8)) *
        (r324PaperTorusMass⁻¹ *
          ∫ a : T4,
            r324ResidualPrimitiveSumProduct rho.auxiliaryCutoff eps
              e0.1 e0.2.1 e0.2.2
                (r324LeftInternalTranslateMeasurableEquiv m a v)
            ∂paperMeasure) := by
  let rawConstant : Real :=
    abs (mode coord : Real)⁻¹ ^ 8 * (2 * Real.pi)⁻¹ *
      ((m : Real) ^ 8 *
        r324ResidualFourierMajorantBase rho ^ (3 * m) * eps⁻¹ ^ 8)
  let auxiliary : T4 -> Real := fun a =>
    r324ResidualPrimitiveSumProduct rho.auxiliaryCutoff eps
      e0.1 e0.2.1 e0.2.2
        (r324LeftInternalTranslateMeasurableEquiv m a v)
  have hauxJoint : Integrable
      (Function.uncurry fun t : Real => fun a : T4 =>
        auxiliary (a + r324CoordinateDisplacementT4 coord t))
      ((volume.restrict (Set.uIoc (-Real.pi) Real.pi)).prod paperMeasure) := by
    exact integrable_commonLeftCoordinateShift_residual
      rho.auxiliaryCutoff heps heps1 e0.1 e0.2.1 e0.2.2 v coord
  have hinnerIntegrable : Integrable
      (fun a : T4 =>
        ∫ t in -Real.pi..Real.pi,
          auxiliary (a + r324CoordinateDisplacementT4 coord t))
      paperMeasure := by
    have h := hauxJoint.integral_prod_right
    simpa only [Set.uIoc_of_le (neg_le_self Real.pi_pos.le),
      intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
      Function.uncurry] using h
  have hrawNonneg : 0 <= rawConstant := by
    have hbase : 0 <= r324ResidualFourierMajorantBase rho :=
      le_trans zero_le_one (one_le_r324ResidualFourierMajorantBase rho)
    unfold rawConstant
    positivity
  have hmajorant : Integrable
      (fun a : T4 => rawConstant *
        ∫ t in -Real.pi..Real.pi,
          auxiliary (a + r324CoordinateDisplacementT4 coord t))
      paperMeasure :=
    hinnerIntegrable.const_mul rawConstant
  have hpointwise : ∀ a : T4,
      norm (charT4 mode a *
          fourierCoeffOn (neg_lt_self Real.pi_pos)
            (r324ResidualPrimitiveSumCommonLeftCoordLineC rho eps e0
              (r324LeftInternalTranslateMeasurableEquiv m a v) coord)
            (-(mode coord))) <=
        rawConstant *
          ∫ t in -Real.pi..Real.pi,
            auxiliary (a + r324CoordinateDisplacementT4 coord t) := by
    intro a
    rw [norm_mul, norm_charT4, one_mul]
    have hline :=
      norm_fourierCoeffOn_r324ResidualPrimitiveSumCommonLeftCoordLineC_le_auxiliary
        rho heps e0 he0
          (r324LeftInternalTranslateMeasurableEquiv m a v) coord
          (n := -(mode coord)) (neg_ne_zero.mpr hcoord)
    have hlineFunction :
        (fun t : Real =>
          r324ResidualPrimitiveSumProduct rho.auxiliaryCutoff eps
            e0.1 e0.2.1 e0.2.2
              (r324CommonLeftMomentTranslation
                (r324LeftInternalTranslateMeasurableEquiv m a v)
                coord t)) =
          fun t : Real =>
            auxiliary (a + r324CoordinateDisplacementT4 coord t) := by
      funext t
      unfold auxiliary
      rw [← r324LeftInternalTranslate_coordinateDisplacement_eq_commonLeftMomentTranslation]
      rw [r324LeftInternalTranslate_add]
    simpa only [Int.cast_neg, abs_neg, abs_inv, hlineFunction, rawConstant]
      using hline
  have hdecomposition :=
    r324ResidualCommonLeftTorusCoefficient_eq_integral_fourierCoeffOn
      rho heps heps1 e0 mode v coord
  have hmassNorm :
      norm ((r324PaperTorusMass : Complex)⁻¹) =
        r324PaperTorusMass⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos r324PaperTorusMass_pos]
  have hnormIntegral :
      norm (∫ a : T4,
          charT4 mode a *
            fourierCoeffOn (neg_lt_self Real.pi_pos)
              (r324ResidualPrimitiveSumCommonLeftCoordLineC rho eps e0
                (r324LeftInternalTranslateMeasurableEquiv m a v) coord)
              (-(mode coord))
          ∂paperMeasure) <=
        ∫ a : T4, rawConstant *
          (∫ t in -Real.pi..Real.pi,
            auxiliary (a + r324CoordinateDisplacementT4 coord t))
          ∂paperMeasure := by
    exact norm_integral_le_of_norm_le hmajorant
      (Filter.Eventually.of_forall hpointwise)
  have hauxAverage :=
    integral_commonLeftCoordinateShift_eq_two_pi_smul
      coord auxiliary hauxJoint
  have htwoPi : 2 * Real.pi ≠ 0 :=
    (mul_pos (by norm_num : (0 : Real) < 2) Real.pi_pos).ne'
  rw [hdecomposition, norm_mul, hmassNorm]
  calc
    r324PaperTorusMass⁻¹ *
        norm (∫ a : T4,
          charT4 mode a *
            fourierCoeffOn (neg_lt_self Real.pi_pos)
              (r324ResidualPrimitiveSumCommonLeftCoordLineC rho eps e0
                (r324LeftInternalTranslateMeasurableEquiv m a v) coord)
              (-(mode coord))
          ∂paperMeasure) <=
      r324PaperTorusMass⁻¹ *
        ∫ a : T4, rawConstant *
          (∫ t in -Real.pi..Real.pi,
            auxiliary (a + r324CoordinateDisplacementT4 coord t))
          ∂paperMeasure :=
      mul_le_mul_of_nonneg_left hnormIntegral
        (inv_nonneg.mpr r324PaperTorusMass_pos.le)
    _ = r324PaperTorusMass⁻¹ * rawConstant *
        (∫ a : T4,
          (∫ t in -Real.pi..Real.pi,
            auxiliary (a + r324CoordinateDisplacementT4 coord t))
          ∂paperMeasure) := by
      rw [integral_const_mul]
      ring
    _ = (abs (mode coord : Real)⁻¹ ^ 8 *
          ((m : Real) ^ 8 *
            r324ResidualFourierMajorantBase rho ^ (3 * m) * eps⁻¹ ^ 8)) *
        (r324PaperTorusMass⁻¹ * ∫ a : T4, auxiliary a ∂paperMeasure) := by
      rw [hauxAverage]
      unfold rawConstant
      field_simp [htwoPi]
      ring
    _ = _ := by rfl

private theorem frequencyCoordinate_ne_zero_of_large
    {eps : Real} (mode : Z4) (coord : Fin dim)
    (hcoord : norm (z4EuclideanFrequency mode) <=
      2 * abs (mode coord : Real))
    (hlarge : 1 <= eps ^ 2 * norm (z4EuclideanFrequency mode)) :
    mode coord ≠ 0 := by
  intro hcoordZero
  have hcoordZeroReal : (mode coord : Real) = 0 := by
    rw [hcoordZero]
    norm_num
  have habsZero : abs (mode coord : Real) = 0 := by
    rw [hcoordZeroReal, abs_zero]
  have hnormZero : norm (z4EuclideanFrequency mode) = 0 := by
    apply le_antisymm
    · calc
        norm (z4EuclideanFrequency mode) <=
            2 * abs (mode coord : Real) := hcoord
        _ = 0 := by rw [habsZero, mul_zero]
    · exact norm_nonneg _
  rw [hnormZero, mul_zero] at hlarge
  norm_num at hlarge

private theorem exists_nonzero_frequencyCoordinate_with_decay
    {eps : Real} (heps : 0 < eps) (heps1 : eps <= 1)
    (mode : Z4)
    (hlarge : 1 <= eps ^ 2 * norm (z4EuclideanFrequency mode)) :
    exists coord : Fin dim,
      mode coord ≠ 0 /\
        eps⁻¹ ^ 8 * (abs (mode coord : Real))⁻¹ ^ 8 <=
          4096 * eighthOrderFrequencyDecay
            (eps ^ 2 * norm (z4EuclideanFrequency mode)) := by
  obtain ⟨coord, hcoord⟩ :=
    exists_frequencyCoordinate_two_mul_abs_ge_euclidean mode
  have hcoordNe : mode coord ≠ 0 :=
    frequencyCoordinate_ne_zero_of_large mode coord hcoord hlarge
  refine ⟨coord, hcoordNe, ?_⟩
  exact
    eps_inv_pow_eight_mul_inv_frequencyCoordinate_pow_eight_le_centralDecay
      (eps := eps) (L := norm (z4EuclideanFrequency mode))
      (a := abs (mode coord : Real))
      heps heps1 (norm_nonneg _) hcoord hlarge

private theorem coordinateDecay_mul_nonneg_tail
    {eps a decay baseLoss average : Real}
    (hdecay : eps⁻¹ ^ 8 * a⁻¹ ^ 8 <= 4096 * decay)
    (htail : 0 <= baseLoss * average) :
    (a⁻¹ ^ 8 * (baseLoss * eps⁻¹ ^ 8)) * average <=
      (4096 * baseLoss) * decay * average := by
  calc
    (a⁻¹ ^ 8 * (baseLoss * eps⁻¹ ^ 8)) * average =
        (eps⁻¹ ^ 8 * a⁻¹ ^ 8) * (baseLoss * average) := by ac_rfl
    _ <= (4096 * decay) * (baseLoss * average) :=
      mul_le_mul_of_nonneg_right hdecay htail
    _ = (4096 * baseLoss) * decay * average := by ac_rfl

/-- Coordinate-free form of the grouped Step 4(B) estimate, with the explicit
finite-dimensional loss absorbed into a fixed scalar. -/
theorem norm_r324ResidualCommonLeftTorusCoefficient_le_centralDecay_auxiliaryHaarAverage
    (rho : SmoothCutoff) {eps : Real} (heps : 0 < eps) (heps1 : eps <= 1)
    {m : Nat} (e0 : MomentContraction m)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (mode : Z4) (v : Fin (2 * m) -> T4)
    (hlarge : 1 <= eps ^ 2 * norm (z4EuclideanFrequency mode)) :
    norm (r324ResidualCommonLeftTorusCoefficient rho eps
        e0.1 e0.2.1 e0.2.2 mode v) <=
      (4096 * ((m : Real) ^ 8 *
        r324ResidualFourierMajorantBase rho ^ (3 * m))) *
        eighthOrderFrequencyDecay
          (eps ^ 2 * norm (z4EuclideanFrequency mode)) *
        (r324PaperTorusMass⁻¹ *
          ∫ a : T4,
            r324ResidualPrimitiveSumProduct rho.auxiliaryCutoff eps
              e0.1 e0.2.1 e0.2.2
                (r324LeftInternalTranslateMeasurableEquiv m a v)
            ∂paperMeasure) := by
  obtain ⟨coord, hcoordNe, hcoordinateDecay⟩ :=
    exists_nonzero_frequencyCoordinate_with_decay
      heps heps1 mode hlarge
  have haverage : 0 <=
      r324PaperTorusMass⁻¹ *
        ∫ a : T4,
          r324ResidualPrimitiveSumProduct rho.auxiliaryCutoff eps
            e0.1 e0.2.1 e0.2.2
              (r324LeftInternalTranslateMeasurableEquiv m a v)
          ∂paperMeasure := by
    exact mul_nonneg (inv_nonneg.mpr r324PaperTorusMass_pos.le)
      (integral_nonneg fun a =>
        r324ResidualPrimitiveSumProduct_nonneg rho.auxiliaryCutoff eps
          e0.1 e0.2.1 e0.2.2 _)
  have hbaseLoss : 0 <=
      (m : Real) ^ 8 * r324ResidualFourierMajorantBase rho ^ (3 * m) := by
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg m) _)
      (pow_nonneg
        (le_trans zero_le_one (one_le_r324ResidualFourierMajorantBase rho)) _)
  have hraw :=
    norm_r324ResidualCommonLeftTorusCoefficient_le_auxiliaryHaarAverage
      rho heps heps1 e0 he0 mode v coord hcoordNe
  simp only [abs_inv] at hraw
  exact hraw.trans
    (coordinateDecay_mul_nonneg_tail
      (eps := eps) (a := abs (mode coord : Real))
      (decay := eighthOrderFrequencyDecay
        (eps ^ 2 * norm (z4EuclideanFrequency mode)))
      (baseLoss := (m : Real) ^ 8 *
        r324ResidualFourierMajorantBase rho ^ (3 * m))
      (average := r324PaperTorusMass⁻¹ *
        ∫ a : T4,
          r324ResidualPrimitiveSumProduct rho.auxiliaryCutoff eps
            e0.1 e0.2.1 e0.2.2
              (r324LeftInternalTranslateMeasurableEquiv m a v)
          ∂paperMeasure)
      hcoordinateDecay (mul_nonneg hbaseLoss haverage))

end SmoothCutoff

open SmoothCutoff

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {alpha beta : Z4}
    {p : R324RefinedScheduleIndex m}
    {e0 : MomentContraction m}
    {leftProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) e0.1 alpha}
    {rightProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) e0.2.1 (-alpha)}
    {leftRoute : R324PaperHalfEndpointRoute leftProviders}
    {rightRoute : R324PaperHalfEndpointRoute rightProviders}

/-- The canonical route coefficient is exactly the grouped residual torus
coefficient at the doubled terminal root. -/
theorem R324PaperLeftRouteExactPackage.commonLeftFourierCoefficient_eq_residualTorusCoefficient
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta)
    (right : R324PaperRightRouteExactLinearPackage left rightRoute)
    (leftPost : left.bound.carrier.SurvivingCoordinate -> T4)
    (rightPost : right.package.bound.carrier.SurvivingCoordinate -> T4) :
    r324CommonLeftFourierCoefficient (alpha + beta)
        (left.bound.crossCoefficient right.package.bound e0.2.2)
        leftPost rightPost =
      r324ResidualCommonLeftTorusCoefficient rho eps
        e0.1 e0.2.1 e0.2.2 (alpha + beta)
        (r324TwoHalfRootDoubledReconstruct
          left.bound.carrier right.package.bound.carrier
          (leftPost, rightPost)) := by
  unfold r324CommonLeftFourierCoefficient
    r324ResidualCommonLeftTorusCoefficient
  congr 1
  apply integral_congr_ae
  filter_upwards with a
  rw [left.crossCoefficient_commonTranslate_eq_leftInternalTranslate right]

end R324WithinHalfResidualPrefix

namespace SmoothCutoff

/-- Joint integrability required by common-left Fubini follows from
integrability on the terminal product carrier and quasi-measure-preservation
of the common-translation projection. -/
theorem integrable_geometry_mul_commonLeft_of_projection
    {I J : Type*} [Fintype I] [Fintype J]
    (geometry auxiliary : (I -> T4) -> (J -> T4) -> Real)
    (hgeometry : forall (a : T4) (left : I -> T4) (right : J -> T4),
      geometry
          (R324WithinHalfResidualPrefix.r324CommonTranslate a left) right =
        geometry left right)
    (hprojection : Measure.QuasiMeasurePreserving
      (fun q : T4 × ((I -> T4) × (J -> T4)) =>
        (R324WithinHalfResidualPrefix.r324CommonTranslate q.1 q.2.1,
          q.2.2))
      (paperMeasure.prod
        ((Measure.pi fun _ : I => paperMeasure).prod
          (Measure.pi fun _ : J => paperMeasure)))
      ((Measure.pi fun _ : I => paperMeasure).prod
        (Measure.pi fun _ : J => paperMeasure)))
    (hbase : Integrable
      (fun p : (I -> T4) × (J -> T4) =>
        geometry p.1 p.2 * auxiliary p.1 p.2)
      ((Measure.pi fun _ : I => paperMeasure).prod
        (Measure.pi fun _ : J => paperMeasure))) :
    Integrable
      (fun q : T4 × ((I -> T4) × (J -> T4)) =>
        geometry q.2.1 q.2.2 *
          auxiliary
            (R324WithinHalfResidualPrefix.r324CommonTranslate q.1 q.2.1)
            q.2.2)
      (paperMeasure.prod
        ((Measure.pi fun _ : I => paperMeasure).prod
          (Measure.pi fun _ : J => paperMeasure))) := by
  let terminalMeasure : Measure ((I -> T4) × (J -> T4)) :=
    (Measure.pi fun _ : I => paperMeasure).prod
      (Measure.pi fun _ : J => paperMeasure)
  let projection :
      T4 × ((I -> T4) × (J -> T4)) ->
        ((I -> T4) × (J -> T4)) := fun q =>
    (R324WithinHalfResidualPrefix.r324CommonTranslate q.1 q.2.1, q.2.2)
  let base : ((I -> T4) × (J -> T4)) -> Real := fun p =>
    geometry p.1 p.2 * auxiliary p.1 p.2
  have hbase' : Integrable base terminalMeasure := by
    simpa only [base, terminalMeasure] using hbase
  have hprojection' : Measure.QuasiMeasurePreserving projection
      (paperMeasure.prod terminalMeasure) terminalMeasure := by
    simpa only [projection, terminalMeasure] using hprojection
  have hmeas : AEStronglyMeasurable
      (fun q : T4 × ((I -> T4) × (J -> T4)) => base (projection q))
      (paperMeasure.prod terminalMeasure) :=
    hbase'.aestronglyMeasurable.comp_quasiMeasurePreserving hprojection'
  have hcomposed : Integrable
      (fun q : T4 × ((I -> T4) × (J -> T4)) => base (projection q))
      (paperMeasure.prod terminalMeasure) := by
    rw [integrable_prod_iff hmeas]
    constructor
    · filter_upwards with a
      change Integrable
        (base ∘
          R324WithinHalfResidualPrefix.r324CommonLeftProjectionSectionMeasurableEquiv
            I J a) terminalMeasure
      exact
        (R324WithinHalfResidualPrefix.measurePreserving_r324CommonLeftProjectionSection
          I J a).integrable_comp_of_integrable hbase'
    · have hnorm : forall a : T4,
          (∫ p, norm (base (projection (a, p))) ∂terminalMeasure) =
            ∫ p, norm (base p) ∂terminalMeasure := by
        intro a
        simpa only [projection, Function.comp_apply,
          R324WithinHalfResidualPrefix.r324CommonLeftProjectionSectionMeasurableEquiv_apply] using
          (R324WithinHalfResidualPrefix.measurePreserving_r324CommonLeftProjectionSection
            I J a).integral_comp' (fun p => norm (base p))
      simp_rw [hnorm]
      exact integrable_const _
  apply hcomposed.congr
  filter_upwards with q
  dsimp only [base, projection]
  rw [hgeometry]

/-- Product Haar absorbs a normalized common-left average whenever the
remaining endpoint geometry is invariant under the same translation.  This
is the positive Fubini seam between the global Fourier coefficient estimate
and `completeNestedRunDensityWithCrossCutoff`.

No norm or triangle inequality occurs here.  The only analytic premise is
joint integrability before exchanging the common translation with the two
terminal configuration integrals. -/
theorem integral_geometry_mul_commonLeftHaarAverage_eq
    {I J : Type*} [Fintype I] [Fintype J]
    (geometry auxiliary : (I -> T4) -> (J -> T4) -> Real)
    (hgeometry : forall (a : T4) (left : I -> T4) (right : J -> T4),
      geometry
          (R324WithinHalfResidualPrefix.r324CommonTranslate a left) right =
        geometry left right)
    (hjoint : Integrable
      (fun q : T4 × ((I -> T4) × (J -> T4)) =>
        geometry q.2.1 q.2.2 *
          auxiliary
            (R324WithinHalfResidualPrefix.r324CommonTranslate q.1 q.2.1)
            q.2.2)
      (paperMeasure.prod
        ((Measure.pi fun _ : I => paperMeasure).prod
          (Measure.pi fun _ : J => paperMeasure)))) :
    (∫ p : (I -> T4) × (J -> T4),
        geometry p.1 p.2 *
          r324CommonLeftHaarAverage auxiliary p.1 p.2
      ∂((Measure.pi fun _ : I => paperMeasure).prod
        (Measure.pi fun _ : J => paperMeasure))) =
      ∫ p : (I -> T4) × (J -> T4),
        geometry p.1 p.2 * auxiliary p.1 p.2
      ∂((Measure.pi fun _ : I => paperMeasure).prod
        (Measure.pi fun _ : J => paperMeasure)) := by
  let muLeft := Measure.pi fun _ : I => paperMeasure
  let muRight := Measure.pi fun _ : J => paperMeasure
  let muProduct := muLeft.prod muRight
  let base : ((I -> T4) × (J -> T4)) -> Real := fun p =>
    geometry p.1 p.2 * auxiliary p.1 p.2
  let shifted : T4 -> ((I -> T4) × (J -> T4)) -> Real := fun a p =>
    r324PaperTorusMass⁻¹ *
      (geometry p.1 p.2 *
        auxiliary
          (R324WithinHalfResidualPrefix.r324CommonTranslate a p.1) p.2)
  have hshift (a : T4) :
      (∫ p, shifted a p ∂muProduct) =
        r324PaperTorusMass⁻¹ * ∫ p, base p ∂muProduct := by
    have hpLeft :=
      R324WithinHalfResidualPrefix.measurePreserving_r324CommonTranslate I a
    let shiftProduct :
        ((I -> T4) × (J -> T4)) ≃ᵐ ((I -> T4) × (J -> T4)) :=
      MeasurableEquiv.prodCongr
        (R324WithinHalfResidualPrefix.r324CommonTranslateMeasurableEquiv I a)
        (MeasurableEquiv.refl (J -> T4))
    have hp : MeasurePreserving shiftProduct muProduct muProduct := by
      change MeasurePreserving
        (fun p : (I -> T4) × (J -> T4) =>
          (R324WithinHalfResidualPrefix.r324CommonTranslate a p.1, p.2))
        muProduct muProduct
      exact hpLeft.prod (MeasurePreserving.id muRight)
    calc
      (∫ p, shifted a p ∂muProduct) =
          r324PaperTorusMass⁻¹ *
            ∫ p, base (shiftProduct p) ∂muProduct := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with p
        have hshiftProduct :
            shiftProduct p =
              (R324WithinHalfResidualPrefix.r324CommonTranslate a p.1,
                p.2) := by
          rfl
        rw [hshiftProduct]
        unfold shifted base
        rw [hgeometry]
      _ = r324PaperTorusMass⁻¹ *
          ∫ p, base p ∂muProduct := by
        rw [hp.integral_comp' base]
  have hvolume :
      (ENNReal.ofReal ((2 * Real.pi) ^ (dim : Nat))).toReal =
        r324PaperTorusMass := by
    rw [ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hvolumeNe : r324PaperTorusMass ≠ 0 :=
    r324PaperTorusMass_pos.ne'
  have hjointShifted : Integrable
      (fun q : T4 × ((I -> T4) × (J -> T4)) => shifted q.1 q.2)
      (paperMeasure.prod muProduct) := by
    simpa only [shifted, muProduct, muLeft, muRight] using
      hjoint.const_mul r324PaperTorusMass⁻¹
  have hconstant :
      (∫ _a : T4,
          r324PaperTorusMass⁻¹ * ∫ p, base p ∂muProduct
          ∂paperMeasure) =
        ∫ p, base p ∂muProduct := by
    rw [integral_const, measureReal_def, paperMeasure_univ, hvolume]
    change r324PaperTorusMass *
        (r324PaperTorusMass⁻¹ * ∫ p, base p ∂muProduct) =
      ∫ p, base p ∂muProduct
    field_simp [hvolumeNe]
  calc
    (∫ p : (I -> T4) × (J -> T4),
        geometry p.1 p.2 *
          r324CommonLeftHaarAverage auxiliary p.1 p.2 ∂muProduct) =
        ∫ p, (∫ a : T4, shifted a p ∂paperMeasure)
          ∂muProduct := by
      apply integral_congr_ae
      filter_upwards with p
      unfold r324CommonLeftHaarAverage shifted
      rw [integral_const_mul, integral_const_mul]
      ring
    _ = ∫ a : T4, (∫ p, shifted a p ∂muProduct)
          ∂paperMeasure := by
      exact ((integral_prod _ hjointShifted).symm.trans
        (integral_prod_symm _ hjointShifted)).symm
    _ = ∫ _a : T4,
          r324PaperTorusMass⁻¹ * ∫ p, base p ∂muProduct
          ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with a
      exact hshift a
    _ = ∫ p, base p ∂muProduct := hconstant
    _ = ∫ p : (I -> T4) × (J -> T4),
          geometry p.1 p.2 * auxiliary p.1 p.2 ∂muProduct := rfl

private theorem r324Reconstruct_commonTranslate_of_active
    {rho : SmoothCutoff} {lam epsilon : Real} {m : Nat}
    {pairing : PartialPairing (Fin m)}
    (res : R324WithinHalfResidualPrefix rho lam epsilon pairing)
    (v : res.SurvivingCoordinate -> T4) (a : T4)
    (i : Fin m) (hi : i ∈ res.state.active) :
    res.reconstruct
        (R324WithinHalfResidualPrefix.r324CommonTranslate a v) i =
      res.reconstruct v i + a := by
  simp only [R324WithinHalfResidualPrefix.reconstruct, hi, dite_true,
    R324WithinHalfResidualPrefix.r324CommonTranslate_apply]

private theorem r324EndpointErased_edgeDisplacement_commonTranslate
    {rho : SmoothCutoff} {lam epsilon : Real} {m : Nat}
    {pairing : PartialPairing (Fin m)}
    (res : R324WithinHalfResidualPrefix rho lam epsilon pairing)
    (hactive : res.state.active.Nonempty)
    (v : res.SurvivingCoordinate -> T4) (a : T4)
    {edge : Fin (m + 1)}
    (hedge : edge ∈ res.endpointErasedActiveEdgeSlots hactive) :
    res.edgeDisplacement 0 0
        (res.reconstruct
          (R324WithinHalfResidualPrefix.r324CommonTranslate a v)) edge =
      res.edgeDisplacement 0 0 (res.reconstruct v) edge := by
  have hedgeActive :=
    res.mem_activeEdgeSlots_of_mem_endpointErased hactive hedge
  have hedgeZero := res.ne_zero_of_mem_endpointErased hactive hedge
  rw [R324WithinHalfResidualPrefix.activeEdgeSlots] at hedgeActive
  rcases Finset.mem_union.mp hedgeActive with hzero | hsource
  · exact (hedgeZero (by simpa using hzero)).elim
  · obtain ⟨source, hsourceActive, hsourceEdge⟩ :=
      Finset.mem_image.mp hsource
    obtain ⟨target, htargetEdge⟩ :=
      res.exists_targetInternalIndex_of_mem_endpointErased hactive hedge
    have htargetCandidate := res.edgeSuccessor_mem_candidates edge
    rw [R324WithinHalfResidualPrefix.edgeSuccessorCandidates]
      at htargetCandidate
    rcases Finset.mem_union.mp htargetCandidate with
      htargetLast | htargetInternal
    · have hvarLast : varIdx target = Fin.last (m + 1) := by
        rw [← htargetEdge]
        simpa using htargetLast
      have hval := congrArg Fin.val hvarLast
      simp only [varIdx_val, Fin.val_last] at hval
      omega
    · obtain ⟨target', htargetActive, htargetEq⟩ :=
        Finset.mem_image.mp htargetInternal
      have hsourceCast : edge.castSucc = varIdx source := by
        rw [← hsourceEdge]
        rfl
      have htarget' : res.edgeSuccessor edge = varIdx target' :=
        htargetEq.symm
      unfold R324WithinHalfResidualPrefix.edgeDisplacement
      rw [hsourceCast, htarget', assemble_varIdx, assemble_varIdx,
        assemble_varIdx, assemble_varIdx,
        r324Reconstruct_commonTranslate_of_active
          res v a source hsourceActive,
        r324Reconstruct_commonTranslate_of_active
          res v a target' (Finset.mem_filter.mp htargetActive).1,
        add_sub_add_right_eq_sub]

/-- The endpoint-erased inverse-square geometry is invariant under a common
translation of every surviving coordinate in one completed half. -/
theorem r324EndpointErasedInvSqChainProduct_commonTranslate
    {rho : SmoothCutoff} {lam epsilon : Real} {m : Nat}
    {pairing : PartialPairing (Fin m)}
    (res : R324WithinHalfResidualPrefix rho lam epsilon pairing)
    (hactive : res.state.active.Nonempty)
    (v : res.SurvivingCoordinate -> T4) (a : T4) :
    res.endpointErasedInvSqChainProduct hactive
        (R324WithinHalfResidualPrefix.r324CommonTranslate a v) =
      res.endpointErasedInvSqChainProduct hactive v := by
  unfold R324WithinHalfResidualPrefix.endpointErasedInvSqChainProduct
  apply Finset.prod_congr rfl
  intro edge hedge
  rw [r324EndpointErased_edgeDisplacement_commonTranslate
    res hactive v a hedge]

/-! ## Exact mixed-cutoff transport to the initial nested run -/

end SmoothCutoff

namespace R324PaperMixedEndpoint

open R324WithinHalfResidualPrefix
open scoped BigOperators

variable {rho sigma : SmoothCutoff} {lam epsilon : Real}
    {m : Nat} {kappaPlus kappaMinus : PartialPairing (Fin m)}

/-- The terminal endpoint geometry with only the complete residual covariance
factor replaced by `sigma`.  The two certified half traces, their scale
products, and both endpoint-erased inverse-square chains remain those of
`rho`, exactly as in paper Step 4(B). -/
def endpointIntegratedGroupedMajorantWithCrossCutoff
    (terminal : R324TwoHalfTerminalData
      rho lam epsilon kappaPlus kappaMinus)
    (sigma : SmoothCutoff)
    (leftScale rightScale : Fin (m + 1) -> Real)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (p :
      (terminal.left.SurvivingCoordinate -> T4) ×
        (terminal.right.SurvivingCoordinate -> T4)) : Real :=
  ((∏ edge ∈ terminal.left.activeEdgeSlots, leftScale edge) *
      (∏ edge ∈ terminal.right.activeEdgeSlots, rightScale edge)) *
    invSqKerMass ^ (4 : Nat) *
    terminal.left.endpointErasedInvSqChainProduct hleft p.1 *
    terminal.right.endpointErasedInvSqChainProduct hright p.2 *
    r324ResidualPrimitiveSumProduct sigma epsilon
      kappaPlus kappaMinus pi (terminal.terminalDoubledReconstruct p)

/-- Pullback of the mixed-cutoff endpoint geometry to the literal initial
nested-cross carrier. -/
def initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff
    (terminal : R324TwoHalfTerminalData
      rho lam epsilon kappaPlus kappaMinus)
    (sigma : SmoothCutoff)
    (leftScale rightScale : Fin (m + 1) -> Real)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (v : terminal.NestedCoordinate pi -> T4) : Real :=
  endpointIntegratedGroupedMajorantWithCrossCutoff terminal sigma
    leftScale rightScale hleft hright pi
    ((terminal.terminalProductPiMeasurableEquivNested pi).symm v)

/-- Exact mixed-cutoff counterpart of
`initialNestedEndpointIntegratedGroupedMajorant_mul_coupling_eq`.

No estimate occurs here.  The equality only reindexes the completed terminal
pair, identifies its reconstruction with the initial nested reconstruction,
and unfolds the grouped residual product with cutoff `sigma`. -/
theorem initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff_mul_coupling_eq
    (terminal : R324TwoHalfTerminalData
      rho lam epsilon kappaPlus kappaMinus)
    (sigma : SmoothCutoff)
    (leftScale rightScale : Fin (m + 1) -> Real)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (head : R324NestedCrossBlock kappaPlus kappaMinus pi)
    (tail : List (R324NestedCrossBlock kappaPlus kappaMinus pi))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial
        kappaPlus kappaMinus pi).remaining = head :: tail)
    (v : terminal.NestedCoordinate pi -> T4) :
    let step :=
      r324InitialNestedCrossStepContext
        kappaPlus kappaMinus pi head tail hremaining
    let hleftInitial :
        (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
      change (r324LeftHalfPullback
        (R324NestedCrossResidualPrefix.initial
          kappaPlus kappaMinus pi).activeCarrier).Nonempty
      rw [R324TwoHalfTerminalData.initial_leftHalfPullback_eq_terminalActive
        terminal pi]
      exact hleft
    let hrightInitial :
        (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
      change (r324RightHalfPullback
        (R324NestedCrossResidualPrefix.initial
          kappaPlus kappaMinus pi).activeCarrier).Nonempty
      rw [R324TwoHalfTerminalData.initial_rightHalfPullback_eq_terminalActive
        terminal pi]
      exact hright
    lamEps lam epsilon ^ (2 * step.residual.remainingOrder) *
        initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff
          terminal sigma leftScale rightScale hleft hright pi v =
      (((∏ edge ∈ terminal.left.activeEdgeSlots, leftScale edge) *
          (∏ edge ∈ terminal.right.activeEdgeSlots, rightScale edge)) *
        invSqKerMass ^ (4 : Nat)) *
        terminal.completeNestedRunDensityWithCrossCutoff
          sigma step hleftInitial hrightInitial v := by
  dsimp only
  let step :=
    r324InitialNestedCrossStepContext
      kappaPlus kappaMinus pi head tail hremaining
  change step.SurvivingCoordinate -> T4 at v
  have hleftCarrier :=
    R324TwoHalfTerminalData.initial_leftHalfPullback_eq_terminalActive
      terminal pi
  have hrightCarrier :=
    R324TwoHalfTerminalData.initial_rightHalfPullback_eq_terminalActive
      terminal pi
  have hleftInitial :
      (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
    change (r324LeftHalfPullback
      (R324NestedCrossResidualPrefix.initial
        kappaPlus kappaMinus pi).activeCarrier).Nonempty
    rw [hleftCarrier]
    exact hleft
  have hrightInitial :
      (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
    change (r324RightHalfPullback
      (R324NestedCrossResidualPrefix.initial
        kappaPlus kappaMinus pi).activeCarrier).Nonempty
    rw [hrightCarrier]
    exact hright
  have hleftTuple :=
    R324TwoHalfTerminalData.initialTerminalProduct_left_eq_initialLeftTuple
      terminal pi head tail hremaining v
  have hrightTuple :=
    R324TwoHalfTerminalData.initialTerminalProduct_right_eq_initialRightTuple
      terminal pi head tail hremaining v
  have hreconstruct :=
    R324TwoHalfTerminalData.initialTerminalDoubledReconstruct_symm_eq_stepReconstruct
      terminal pi head tail hremaining v
  have hleftPath :
      terminal.left.endpointErasedInvSqChainProduct hleft
          ((terminal.terminalProductPiMeasurableEquivNested pi).symm v).1 =
        terminal.nestedLeftHalfInvSqProduct step
          step.residual.activeCarrier hleftInitial v := by
    rw [terminal.left.endpointErasedInvSqChainProduct_eq_halfInvSqChainProduct,
      hleftTuple]
    unfold R324TwoHalfTerminalData.nestedLeftHalfInvSqProduct
    dsimp only [step, r324InitialNestedCrossStepContext]
    simp only [hleftCarrier]
  have hrightPath :
      terminal.right.endpointErasedInvSqChainProduct hright
          ((terminal.terminalProductPiMeasurableEquivNested pi).symm v).2 =
        terminal.nestedRightHalfInvSqProduct step
          step.residual.activeCarrier hrightInitial v := by
    rw [terminal.right.endpointErasedInvSqChainProduct_eq_halfInvSqChainProduct,
      hrightTuple]
    unfold R324TwoHalfTerminalData.nestedRightHalfInvSqProduct
    dsimp only [step, r324InitialNestedCrossStepContext]
    simp only [hrightCarrier]
  have hresidual :
      r324ResidualPrimitiveSumProduct sigma epsilon
          kappaPlus kappaMinus pi
          (terminal.terminalDoubledReconstruct
            ((terminal.terminalProductPiMeasurableEquivNested pi).symm v)) =
        r324NestedResidualPrimitiveSumProduct sigma epsilon
          kappaPlus kappaMinus pi step.residual (step.reconstruct v) := by
    rw [hreconstruct]
    dsimp only [step, r324InitialNestedCrossStepContext]
    rw [r324NestedResidualPrimitiveSumProduct_initial]
  unfold initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff
    endpointIntegratedGroupedMajorantWithCrossCutoff
    R324TwoHalfTerminalData.completeNestedRunDensityWithCrossCutoff
  rw [hleftPath, hrightPath, hresidual]
  ring

/-- Integrated form of the exact mixed-cutoff transport.  This is the form
consumed by the scalar complete-run estimate after the endpoint norm has been
taken once. -/
theorem integral_lamEps_pow_initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff_eq
    (terminal : R324TwoHalfTerminalData
      rho lam epsilon kappaPlus kappaMinus)
    (sigma : SmoothCutoff)
    (leftScale rightScale : Fin (m + 1) -> Real)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (head : R324NestedCrossBlock kappaPlus kappaMinus pi)
    (tail : List (R324NestedCrossBlock kappaPlus kappaMinus pi))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial
        kappaPlus kappaMinus pi).remaining = head :: tail) :
    let step :=
      r324InitialNestedCrossStepContext
        kappaPlus kappaMinus pi head tail hremaining
    let hleftInitial :
        (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
      change (r324LeftHalfPullback
        (R324NestedCrossResidualPrefix.initial
          kappaPlus kappaMinus pi).activeCarrier).Nonempty
      rw [R324TwoHalfTerminalData.initial_leftHalfPullback_eq_terminalActive
        terminal pi]
      exact hleft
    let hrightInitial :
        (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
      change (r324RightHalfPullback
        (R324NestedCrossResidualPrefix.initial
          kappaPlus kappaMinus pi).activeCarrier).Nonempty
      rw [R324TwoHalfTerminalData.initial_rightHalfPullback_eq_terminalActive
        terminal pi]
      exact hright
    (∫ v,
        lamEps lam epsilon ^ (2 * step.residual.remainingOrder) *
          initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff
            terminal sigma leftScale rightScale hleft hright pi v
      ∂Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure) =
      (((∏ edge ∈ terminal.left.activeEdgeSlots, leftScale edge) *
          (∏ edge ∈ terminal.right.activeEdgeSlots, rightScale edge)) *
        invSqKerMass ^ (4 : Nat)) *
        ∫ v,
          terminal.completeNestedRunDensityWithCrossCutoff
            sigma step hleftInitial hrightInitial v
        ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure := by
  dsimp only
  let step :=
    r324InitialNestedCrossStepContext
      kappaPlus kappaMinus pi head tail hremaining
  have hpointwise (v : terminal.NestedCoordinate pi -> T4) :=
    initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff_mul_coupling_eq
      terminal sigma leftScale rightScale hleft hright pi
        head tail hremaining v
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  exact hpointwise v

/-- Integrability of the initial mixed grouped majorant.  The only division
is by the strictly positive even power of `lamEps`; all scale products remain
as harmless finite constants. -/
theorem integrable_initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff_at_truncation
    (terminal : R324TwoHalfTerminalData
      rho lam epsilon kappaPlus kappaMinus)
    (sigma : SmoothCutoff)
    (leftScale rightScale : Fin (m + 1) -> Real)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (head : R324NestedCrossBlock kappaPlus kappaMinus pi)
    (tail : List (R324NestedCrossBlock kappaPlus kappaMinus pi))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial
        kappaPlus kappaMinus pi).remaining = head :: tail)
    (hlam : 0 < lam) (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon <= 1)
    (hlog : 1 <= abs (Real.log epsilon))
    (hmtrunc : m <= truncOrder epsilon) :
    Integrable
      (initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff
        terminal sigma leftScale rightScale hleft hright pi)
      (Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure) := by
  let step :=
    r324InitialNestedCrossStepContext
      kappaPlus kappaMinus pi head tail hremaining
  have hleftInitial :
      (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
    change (r324LeftHalfPullback
      (R324NestedCrossResidualPrefix.initial
        kappaPlus kappaMinus pi).activeCarrier).Nonempty
    rw [R324TwoHalfTerminalData.initial_leftHalfPullback_eq_terminalActive
      terminal pi]
    exact hleft
  have hrightInitial :
      (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
    change (r324RightHalfPullback
      (R324NestedCrossResidualPrefix.initial
        kappaPlus kappaMinus pi).activeCarrier).Nonempty
    rw [R324TwoHalfTerminalData.initial_rightHalfPullback_eq_terminalActive
      terminal pi]
    exact hright
  have hrun :=
    terminal.integrable_completeNestedRunDensityWithCrossCutoff_at_truncation
      sigma hlam hepsilon hepsilonOne hlog hmtrunc
        step hleftInitial hrightInitial
  let weight : Real :=
    lamEps lam epsilon ^ (2 * step.residual.remainingOrder)
  let scale : Real :=
    ((∏ edge ∈ terminal.left.activeEdgeSlots, leftScale edge) *
        (∏ edge ∈ terminal.right.activeEdgeSlots, rightScale edge)) *
      invSqKerMass ^ (4 : Nat)
  have hlogPos : 0 < abs (Real.log epsilon) :=
    lt_of_lt_of_le zero_lt_one hlog
  have hlamEps : 0 < lamEps lam epsilon := by
    unfold lamEps
    exact div_pos hlam (Real.sqrt_pos.2 hlogPos)
  have hweight : weight ≠ 0 := by
    exact pow_ne_zero _ hlamEps.ne'
  have hscaled : Integrable
      (fun v : step.SurvivingCoordinate -> T4 =>
        weight⁻¹ * scale *
          terminal.completeNestedRunDensityWithCrossCutoff
            sigma step hleftInitial hrightInitial v)
      (Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) := by
    exact hrun.const_mul (weight⁻¹ * scale)
  apply hscaled.congr
  filter_upwards with v
  have hpoint :=
    initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff_mul_coupling_eq
      terminal sigma leftScale rightScale hleft hright pi
        head tail hremaining v
  change weight *
      initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff
        terminal sigma leftScale rightScale hleft hright pi v =
    scale * terminal.completeNestedRunDensityWithCrossCutoff
      sigma step hleftInitial hrightInitial v at hpoint
  symm
  calc
    initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff
        terminal sigma leftScale rightScale hleft hright pi v =
      weight⁻¹ *
        (weight *
          initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff
            terminal sigma leftScale rightScale hleft hright pi v) := by
      field_simp [hweight]
    _ = weight⁻¹ * scale *
        terminal.completeNestedRunDensityWithCrossCutoff
          sigma step hleftInitial hrightInitial v := by
      rw [hpoint]
      ring

/-- The preceding integrability statement transported back to the completed
two-half terminal carrier. -/
theorem integrable_endpointIntegratedGroupedMajorantWithCrossCutoff_at_truncation
    (terminal : R324TwoHalfTerminalData
      rho lam epsilon kappaPlus kappaMinus)
    (sigma : SmoothCutoff)
    (leftScale rightScale : Fin (m + 1) -> Real)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (head : R324NestedCrossBlock kappaPlus kappaMinus pi)
    (tail : List (R324NestedCrossBlock kappaPlus kappaMinus pi))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial
        kappaPlus kappaMinus pi).remaining = head :: tail)
    (hlam : 0 < lam) (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon <= 1)
    (hlog : 1 <= abs (Real.log epsilon))
    (hmtrunc : m <= truncOrder epsilon) :
    Integrable
      (endpointIntegratedGroupedMajorantWithCrossCutoff terminal sigma
        leftScale rightScale hleft hright pi)
      ((Measure.pi fun _ : terminal.left.SurvivingCoordinate =>
          paperMeasure).prod
        (Measure.pi fun _ : terminal.right.SurvivingCoordinate =>
          paperMeasure)) := by
  let e := terminal.terminalProductPiMeasurableEquivNested pi
  have hp := terminal.measurePreserving_terminalProductPiMeasurableEquivNested pi
  have hnested :=
    integrable_initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff_at_truncation
      terminal sigma leftScale rightScale hleft hright pi
        head tail hremaining hlam hepsilon hepsilonOne hlog hmtrunc
  have hcomp := hp.integrable_comp_of_integrable hnested
  apply hcomp.congr
  filter_upwards with p
  change endpointIntegratedGroupedMajorantWithCrossCutoff terminal sigma
      leftScale rightScale hleft hright pi (e.symm (e p)) =
    endpointIntegratedGroupedMajorantWithCrossCutoff terminal sigma
      leftScale rightScale hleft hright pi p
  rw [MeasurableEquiv.symm_apply_apply]

end R324PaperMixedEndpoint

namespace R324PaperCommonLeftAverage

open R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam epsilon K A : Real}
    {m : Nat} {kappaPlus kappaMinus : PartialPairing (Fin m)}
    {alpha : Z4}
    {leftProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := epsilon)
      (K := K) (A := A) kappaPlus alpha}
    {rightProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := epsilon)
      (K := K) (A := A) kappaMinus (-alpha)}
    {routes : R324PaperTwoHalfEndpointRoutes leftProviders rightProviders}

/-- The coefficient-free spatial geometry in the parametric two-half
endpoint majorant. -/
def coefficientEndpointGeometry
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (p :
      (left.carrier.SurvivingCoordinate -> T4) ×
        (right.carrier.SurvivingCoordinate -> T4)) : Real :=
  ((∏ edge ∈ left.carrier.activeEdgeSlots,
        routes.left.completedRoute.terminalScale edge) *
      (∏ edge ∈ right.carrier.activeEdgeSlots,
        routes.right.completedRoute.terminalScale edge)) *
    invSqKerMass ^ (4 : Nat) *
    left.carrier.endpointErasedInvSqChainProduct left.active p.1 *
    right.carrier.endpointErasedInvSqChainProduct right.active p.2

theorem coefficientEndpointGroupedMajorant_eq_geometry_mul_norm
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (coefficient :
      (left.carrier.SurvivingCoordinate -> T4) ->
        (right.carrier.SurvivingCoordinate -> T4) -> Complex)
    (p :
      (left.carrier.SurvivingCoordinate -> T4) ×
        (right.carrier.SurvivingCoordinate -> T4)) :
    left.coefficientEndpointGroupedMajorant right coefficient p =
      coefficientEndpointGeometry left right p *
        norm (coefficient p.1 p.2) := by
  unfold R324PaperHalfEndpointUniformBound.coefficientEndpointGroupedMajorant
    coefficientEndpointGeometry
  ring

theorem coefficientEndpointGeometry_nonneg
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (p :
      (left.carrier.SurvivingCoordinate -> T4) ×
        (right.carrier.SurvivingCoordinate -> T4)) :
    0 <= coefficientEndpointGeometry left right p := by
  unfold coefficientEndpointGeometry
  have hleftScale : 0 <=
      ∏ edge ∈ left.carrier.activeEdgeSlots,
        routes.left.completedRoute.terminalScale edge :=
    Finset.prod_nonneg fun edge _ =>
      (routes.left.completedRoute.terminalCertificate.scale_pos edge).le
  have hrightScale : 0 <=
      ∏ edge ∈ right.carrier.activeEdgeSlots,
        routes.right.completedRoute.terminalScale edge :=
    Finset.prod_nonneg fun edge _ =>
      (routes.right.completedRoute.terminalCertificate.scale_pos edge).le
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (mul_nonneg hleftScale hrightScale)
        (pow_nonneg r324_invSqKerMass_pos.le _))
      (left.carrier.endpointErasedInvSqChainProduct_nonneg left.active p.1))
    (right.carrier.endpointErasedInvSqChainProduct_nonneg right.active p.2)

theorem coefficientEndpointGeometry_commonTranslate_left
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (a : T4) (leftPost : left.carrier.SurvivingCoordinate -> T4)
    (rightPost : right.carrier.SurvivingCoordinate -> T4) :
    coefficientEndpointGeometry left right
        (r324CommonTranslate a leftPost, rightPost) =
      coefficientEndpointGeometry left right (leftPost, rightPost) := by
  unfold coefficientEndpointGeometry
  rw [r324EndpointErasedInvSqChainProduct_commonTranslate]

/-- Specialization of the generic Haar-absorption identity to the exact
coefficient-free geometry emitted by the parametric endpoint majorant. -/
theorem integral_coefficientEndpointGeometry_mul_commonLeftHaarAverage_eq
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (auxiliary :
      (left.carrier.SurvivingCoordinate -> T4) ->
        (right.carrier.SurvivingCoordinate -> T4) -> Real)
    (hjoint : Integrable
      (fun q : T4 ×
          ((left.carrier.SurvivingCoordinate -> T4) ×
            (right.carrier.SurvivingCoordinate -> T4)) =>
        coefficientEndpointGeometry left right q.2 *
          auxiliary (r324CommonTranslate q.1 q.2.1) q.2.2)
      (paperMeasure.prod
        ((Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
            paperMeasure).prod
          (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
            paperMeasure)))) :
    (∫ p,
        coefficientEndpointGeometry left right p *
          r324CommonLeftHaarAverage auxiliary p.1 p.2
      ∂((Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
          paperMeasure).prod
        (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
          paperMeasure))) =
      ∫ p,
        coefficientEndpointGeometry left right p * auxiliary p.1 p.2
      ∂((Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
          paperMeasure).prod
        (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
          paperMeasure)) := by
  exact integral_geometry_mul_commonLeftHaarAverage_eq
    (fun leftPost rightPost =>
      coefficientEndpointGeometry left right (leftPost, rightPost))
    auxiliary
    (fun a leftPost rightPost =>
      coefficientEndpointGeometry_commonTranslate_left
        left right a leftPost rightPost)
    hjoint

/-- Integrability companion to the preceding Haar-absorption identity.
The joint `T4 × terminal` function is integrated first in the common-left
Haar parameter; normalization by the fixed torus mass is then harmless. -/
theorem integrable_coefficientEndpointGeometry_mul_commonLeftHaarAverage
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (auxiliary :
      (left.carrier.SurvivingCoordinate -> T4) ->
        (right.carrier.SurvivingCoordinate -> T4) -> Real)
    (hjoint : Integrable
      (fun q : T4 ×
          ((left.carrier.SurvivingCoordinate -> T4) ×
            (right.carrier.SurvivingCoordinate -> T4)) =>
        coefficientEndpointGeometry left right q.2 *
          auxiliary (r324CommonTranslate q.1 q.2.1) q.2.2)
      (paperMeasure.prod
        ((Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
            paperMeasure).prod
          (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
            paperMeasure)))) :
    Integrable
      (fun p :
          (left.carrier.SurvivingCoordinate -> T4) ×
            (right.carrier.SurvivingCoordinate -> T4) =>
        coefficientEndpointGeometry left right p *
          r324CommonLeftHaarAverage auxiliary p.1 p.2)
      ((Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
          paperMeasure).prod
        (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
          paperMeasure)) := by
  have hmarginal := hjoint.integral_prod_right
  have hscaled := hmarginal.const_mul r324PaperTorusMass⁻¹
  apply hscaled.congr
  filter_upwards with p
  unfold r324CommonLeftHaarAverage
  rw [integral_const_mul]
  ring

/-- The same absorption identity on the literal initial nested carrier used
by the exact four-endpoint collapse and by the mixed-cutoff run. -/
theorem integral_initialNested_coefficientEndpointGeometry_mul_commonLeftHaarAverage_eq
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (auxiliary :
      (left.carrier.SurvivingCoordinate -> T4) ->
        (right.carrier.SurvivingCoordinate -> T4) -> Real)
    (hjoint : Integrable
      (fun q : T4 ×
          ((left.carrier.SurvivingCoordinate -> T4) ×
            (right.carrier.SurvivingCoordinate -> T4)) =>
        coefficientEndpointGeometry left right q.2 *
          auxiliary (r324CommonTranslate q.1 q.2.1) q.2.2)
      (paperMeasure.prod
        ((Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
            paperMeasure).prod
          (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
            paperMeasure)))) :
    (∫ v,
        (left.twoHalfTerminal right).initialNestedPullback pi
          (fun p => coefficientEndpointGeometry left right p *
            r324CommonLeftHaarAverage auxiliary p.1 p.2) v
      ∂Measure.pi fun _ :
        (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure) =
      ∫ v,
        (left.twoHalfTerminal right).initialNestedPullback pi
          (fun p => coefficientEndpointGeometry left right p *
            auxiliary p.1 p.2) v
      ∂Measure.pi fun _ :
        (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure := by
  rw [← (left.twoHalfTerminal right)
      |>.integral_terminalProduct_eq_integral_initialNestedPullback
        pi (fun p => coefficientEndpointGeometry left right p *
          r324CommonLeftHaarAverage auxiliary p.1 p.2),
    ← (left.twoHalfTerminal right)
      |>.integral_terminalProduct_eq_integral_initialNestedPullback
        pi (fun p => coefficientEndpointGeometry left right p *
          auxiliary p.1 p.2)]
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal, integral_complex_ofReal]
  congr 1
  exact integral_coefficientEndpointGeometry_mul_commonLeftHaarAverage_eq
    left right auxiliary hjoint

/-- The Haar-averaged endpoint geometry is integrable on the literal initial
nested carrier.  This is the missing `Integrable` premise for the first legal
post-collapse norm comparison. -/
theorem integrable_initialNested_coefficientEndpointGeometry_mul_commonLeftHaarAverage
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (auxiliary :
      (left.carrier.SurvivingCoordinate -> T4) ->
        (right.carrier.SurvivingCoordinate -> T4) -> Real)
    (hjoint : Integrable
      (fun q : T4 ×
          ((left.carrier.SurvivingCoordinate -> T4) ×
            (right.carrier.SurvivingCoordinate -> T4)) =>
        coefficientEndpointGeometry left right q.2 *
          auxiliary (r324CommonTranslate q.1 q.2.1) q.2.2)
      (paperMeasure.prod
        ((Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
            paperMeasure).prod
          (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
            paperMeasure)))) :
    Integrable
      ((left.twoHalfTerminal right).initialNestedPullback pi
        (fun p => coefficientEndpointGeometry left right p *
          r324CommonLeftHaarAverage auxiliary p.1 p.2))
      (Measure.pi fun _ :
        (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure) := by
  have hterminal : Integrable
      (fun p :
          (left.carrier.SurvivingCoordinate -> T4) ×
            (right.carrier.SurvivingCoordinate -> T4) =>
        coefficientEndpointGeometry left right p *
          r324CommonLeftHaarAverage auxiliary p.1 p.2)
      ((Measure.pi fun _ : left.carrier.SurvivingCoordinate => paperMeasure).prod
        (Measure.pi fun _ : right.carrier.SurvivingCoordinate => paperMeasure)) :=
    integrable_coefficientEndpointGeometry_mul_commonLeftHaarAverage
      left right auxiliary hjoint
  have hp := (left.twoHalfTerminal right)
    |>.measurePreserving_terminalProductPiMeasurableEquivNested pi
  have hterminalComplex : Integrable
      (fun p :
          (left.carrier.SurvivingCoordinate -> T4) ×
            (right.carrier.SurvivingCoordinate -> T4) =>
        (coefficientEndpointGeometry left right p : Complex) *
          (r324CommonLeftHaarAverage auxiliary p.1 p.2 : Complex))
      ((Measure.pi fun _ : left.carrier.SurvivingCoordinate => paperMeasure).prod
        (Measure.pi fun _ : right.carrier.SurvivingCoordinate => paperMeasure)) := by
    apply (hterminal.ofReal (𝕜 := Complex)).congr
    filter_upwards with p
    exact Complex.ofReal_mul _ _
  have hcomp := hp.symm.integrable_comp_of_integrable hterminalComplex
  apply hcomp.congr
  filter_upwards with v
  rfl

/-- Real-valued form of the preceding integrability statement.  The
complex-valued `initialNestedPullback` is only an implementation detail of
the exact endpoint-density API. -/
theorem integrable_initialNested_coefficientEndpointGeometry_mul_commonLeftHaarAverage_real
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (auxiliary :
      (left.carrier.SurvivingCoordinate -> T4) ->
        (right.carrier.SurvivingCoordinate -> T4) -> Real)
    (hjoint : Integrable
      (fun q : T4 ×
          ((left.carrier.SurvivingCoordinate -> T4) ×
            (right.carrier.SurvivingCoordinate -> T4)) =>
        coefficientEndpointGeometry left right q.2 *
          auxiliary (r324CommonTranslate q.1 q.2.1) q.2.2)
      (paperMeasure.prod
        ((Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
            paperMeasure).prod
          (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
            paperMeasure)))) :
    Integrable
      (fun v =>
        let p := ((left.twoHalfTerminal right
          |>.terminalProductPiMeasurableEquivNested pi).symm v)
        coefficientEndpointGeometry left right p *
          r324CommonLeftHaarAverage auxiliary p.1 p.2)
      (Measure.pi fun _ :
        (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure) := by
  have hcomplex :=
    integrable_initialNested_coefficientEndpointGeometry_mul_commonLeftHaarAverage
      left right pi auxiliary hjoint
  apply hcomplex.re.congr
  filter_upwards with v
  let p0 :=
    ((left.twoHalfTerminal right
      |>.terminalProductPiMeasurableEquivNested pi).symm v)
  change Complex.re
      ((coefficientEndpointGeometry left right p0 : Complex) *
        (r324CommonLeftHaarAverage auxiliary p0.1 p0.2 : Complex)) = _
  norm_num
  rfl

/-- The complete positive auxiliary residual sum evaluated on the reconstructed
terminal pair.  This is the sole coefficient that changes from `rho` to the
analytic cross cutoff `sigma`; the endpoint geometry is untouched. -/
def mixedResidualAuxiliary
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (sigma : SmoothCutoff)
    (leftPost : left.carrier.SurvivingCoordinate -> T4)
    (rightPost : right.carrier.SurvivingCoordinate -> T4) : Real :=
  r324ResidualPrimitiveSumProduct sigma epsilon
    kappaPlus kappaMinus pi
    ((left.twoHalfTerminal right).terminalDoubledReconstruct
      (leftPost, rightPost))

theorem mixedResidualAuxiliary_nonneg
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (sigma : SmoothCutoff)
    (leftPost : left.carrier.SurvivingCoordinate -> T4)
    (rightPost : right.carrier.SurvivingCoordinate -> T4) :
    0 <= mixedResidualAuxiliary left right pi sigma leftPost rightPost := by
  exact r324ResidualPrimitiveSumProduct_nonneg sigma epsilon
    kappaPlus kappaMinus pi _

/-- Translating the completed left terminal tuple is exactly the canonical
left-copy translation of the doubled root, on the genuine support of the
grouped residual sum. -/
theorem mixedResidualAuxiliary_commonTranslate_left
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (sigma : SmoothCutoff)
    (leftPost : left.carrier.SurvivingCoordinate -> T4)
    (rightPost : right.carrier.SurvivingCoordinate -> T4)
    (a : T4) :
    mixedResidualAuxiliary left right pi sigma
        (r324CommonTranslate a leftPost) rightPost =
      r324ResidualPrimitiveSumProduct sigma epsilon
        kappaPlus kappaMinus pi
        (r324LeftInternalTranslateMeasurableEquiv m a
          (r324TwoHalfRootDoubledReconstruct
            left.carrier right.carrier (leftPost, rightPost))) := by
  unfold mixedResidualAuxiliary
  apply r324ResidualPrimitiveSumProduct_congr_on_active
  intro q hq
  by_cases hleft : q.val < m
  · obtain ⟨i, hi, rfl⟩ :=
      exists_leftMomentIndex_of_mem_momentResidualActive hq hleft
    have hiCarrier : i ∈ left.carrier.state.active := by
      rw [left.carrier.active_eq_finalActive_of_processed_eq_schedule
        left.carrier_processed]
      exact hi
    have hiLeft : (leftMomentIndex i).val < m := by
      simp only [leftMomentIndex]
      exact i.isLt
    unfold R324TwoHalfTerminalData.terminalDoubledReconstruct
      r324TwoHalfRootDoubledReconstruct
    simp only [
      momentDoubleFinEquiv_symm_leftMomentIndex,
      r324LeftInternalTranslateMeasurableEquiv_apply,
      if_pos hiLeft]
    exact left.carrier.reconstruct_commonTranslate_of_active
      leftPost a i hiCarrier
  · obtain ⟨i, hi, rfl⟩ :=
      exists_rightMomentIndex_of_mem_momentResidualActive hq (by omega)
    have hiRight : ¬ (rightMomentIndex i).val < m := by
      simp only [rightMomentIndex]
      omega
    unfold R324TwoHalfTerminalData.terminalDoubledReconstruct
      r324TwoHalfRootDoubledReconstruct
    simp only [
      momentDoubleFinEquiv_symm_rightMomentIndex,
      r324LeftInternalTranslateMeasurableEquiv_apply,
      if_neg hiRight]
    change right.carrier.reconstruct rightPost i =
      right.carrier.reconstruct rightPost i
    rfl

theorem commonLeftHaarAverage_mixedResidualAuxiliary_eq_rootAverage
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (sigma : SmoothCutoff)
    (leftPost : left.carrier.SurvivingCoordinate -> T4)
    (rightPost : right.carrier.SurvivingCoordinate -> T4) :
    r324CommonLeftHaarAverage
        (mixedResidualAuxiliary left right pi sigma)
        leftPost rightPost =
      r324PaperTorusMass⁻¹ *
        ∫ a : T4,
          r324ResidualPrimitiveSumProduct sigma epsilon
            kappaPlus kappaMinus pi
            (r324LeftInternalTranslateMeasurableEquiv m a
              (r324TwoHalfRootDoubledReconstruct
                left.carrier right.carrier (leftPost, rightPost)))
          ∂paperMeasure := by
  unfold r324CommonLeftHaarAverage
  congr 1
  apply integral_congr_ae
  filter_upwards with a
  exact mixedResidualAuxiliary_commonTranslate_left
    left right pi sigma leftPost rightPost a

/-- On the terminal product carrier, coefficient-free endpoint geometry
times the complete auxiliary residual sum is definitionally the mixed-cutoff
grouped endpoint majorant (up to reassociation of scalar products). -/
theorem coefficientEndpointGeometry_mul_mixedResidualAuxiliary_eq
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (sigma : SmoothCutoff)
    (p :
      (left.carrier.SurvivingCoordinate -> T4) ×
        (right.carrier.SurvivingCoordinate -> T4)) :
    coefficientEndpointGeometry left right p *
        mixedResidualAuxiliary left right pi sigma p.1 p.2 =
      R324PaperMixedEndpoint.endpointIntegratedGroupedMajorantWithCrossCutoff
        (left.twoHalfTerminal right) sigma
        routes.left.completedRoute.terminalScale
        routes.right.completedRoute.terminalScale
        left.active right.active pi p := by
  unfold coefficientEndpointGeometry mixedResidualAuxiliary
    R324PaperMixedEndpoint.endpointIntegratedGroupedMajorantWithCrossCutoff
  rfl

/-- The mixed endpoint geometry supplies the joint integrability needed for
the common-left Haar/Fubini step. -/
theorem integrable_coefficientEndpointGeometry_mul_mixedResidual_commonLeft
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (sigma : SmoothCutoff)
    (head : R324NestedCrossBlock kappaPlus kappaMinus pi)
    (tail : List (R324NestedCrossBlock kappaPlus kappaMinus pi))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial
        kappaPlus kappaMinus pi).remaining = head :: tail)
    (hlam : 0 < lam) (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon <= 1)
    (hlog : 1 <= abs (Real.log epsilon))
    (hmtrunc : m <= truncOrder epsilon) :
    Integrable
      (fun q : T4 ×
          ((left.carrier.SurvivingCoordinate -> T4) ×
            (right.carrier.SurvivingCoordinate -> T4)) =>
        coefficientEndpointGeometry left right q.2 *
          mixedResidualAuxiliary left right pi sigma
            (r324CommonTranslate q.1 q.2.1) q.2.2)
      (paperMeasure.prod
        ((Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
            paperMeasure).prod
          (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
            paperMeasure))) := by
  have hmixed :=
    R324PaperMixedEndpoint.integrable_endpointIntegratedGroupedMajorantWithCrossCutoff_at_truncation
        (left.twoHalfTerminal right) sigma
        routes.left.completedRoute.terminalScale
        routes.right.completedRoute.terminalScale
        left.active right.active pi head tail hremaining
        hlam hepsilon hepsilonOne hlog hmtrunc
  have hbase : Integrable
      (fun p :
          (left.carrier.SurvivingCoordinate -> T4) ×
            (right.carrier.SurvivingCoordinate -> T4) =>
        coefficientEndpointGeometry left right p *
          mixedResidualAuxiliary left right pi sigma p.1 p.2)
      ((Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
          paperMeasure).prod
        (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
          paperMeasure)) := by
    apply hmixed.congr
    filter_upwards with p
    exact (coefficientEndpointGeometry_mul_mixedResidualAuxiliary_eq
      left right pi sigma p).symm
  exact integrable_geometry_mul_commonLeft_of_projection
    (fun leftPost rightPost =>
      coefficientEndpointGeometry left right (leftPost, rightPost))
    (mixedResidualAuxiliary left right pi sigma)
    (fun a leftPost rightPost =>
      coefficientEndpointGeometry_commonTranslate_left
        left right a leftPost rightPost)
    (R324WithinHalfResidualPrefix.quasiMeasurePreserving_r324CommonLeftProjection
        left.carrier.SurvivingCoordinate
        right.carrier.SurvivingCoordinate)
    hbase

/-- Common-left Haar absorption followed by the exact terminal-to-nested
reindexing.  The result is precisely the mixed-cutoff grouped majorant read by
the Steps 2--3 complete-run identity; no pointwise comparison between the
original and auxiliary cutoff is used. -/
theorem integral_initialNested_geometry_mul_commonLeftAverage_eq_mixedMajorant
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (sigma : SmoothCutoff)
    (hjoint : Integrable
      (fun q : T4 ×
          ((left.carrier.SurvivingCoordinate -> T4) ×
            (right.carrier.SurvivingCoordinate -> T4)) =>
        coefficientEndpointGeometry left right q.2 *
          mixedResidualAuxiliary left right pi sigma
            (r324CommonTranslate q.1 q.2.1) q.2.2)
      (paperMeasure.prod
        ((Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
            paperMeasure).prod
          (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
            paperMeasure)))) :
    (∫ v,
        (left.twoHalfTerminal right).initialNestedPullback pi
          (fun p => coefficientEndpointGeometry left right p *
            r324CommonLeftHaarAverage
              (mixedResidualAuxiliary left right pi sigma) p.1 p.2) v
      ∂Measure.pi fun _ :
        (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure) =
      ∫ v,
        R324PaperMixedEndpoint.initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff
          (left.twoHalfTerminal right) sigma
          routes.left.completedRoute.terminalScale
          routes.right.completedRoute.terminalScale
          left.active right.active pi v
      ∂Measure.pi fun _ :
        (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure := by
  calc
    (∫ v,
        (left.twoHalfTerminal right).initialNestedPullback pi
          (fun p => coefficientEndpointGeometry left right p *
            r324CommonLeftHaarAverage
              (mixedResidualAuxiliary left right pi sigma) p.1 p.2) v
      ∂Measure.pi fun _ :
        (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure) =
      ∫ v,
        (left.twoHalfTerminal right).initialNestedPullback pi
          (fun p => coefficientEndpointGeometry left right p *
            mixedResidualAuxiliary left right pi sigma p.1 p.2) v
      ∂Measure.pi fun _ :
        (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure :=
      integral_initialNested_coefficientEndpointGeometry_mul_commonLeftHaarAverage_eq
        left right pi (mixedResidualAuxiliary left right pi sigma) hjoint
    _ = _ := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards with v
      unfold R324TwoHalfTerminalData.initialNestedPullback
        R324PaperMixedEndpoint.initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff
      let p := ((left.twoHalfTerminal right
        |>.terminalProductPiMeasurableEquivNested pi).symm v)
      calc
        (coefficientEndpointGeometry left right p : Complex) *
            (mixedResidualAuxiliary left right pi sigma p.1 p.2 : Complex) =
          ((coefficientEndpointGeometry left right p *
            mixedResidualAuxiliary left right pi sigma p.1 p.2 : Real) : Complex) :=
              (Complex.ofReal_mul _ _).symm
        _ = _ := congrArg Complex.ofReal
          (coefficientEndpointGeometry_mul_mixedResidualAuxiliary_eq
            left right pi sigma p)

/-- Real-valued common-left Haar absorption on the literal nested carrier.
This is the scalar identity used after the first legal endpoint norm. -/
theorem integral_initialNested_coefficientEndpointGeometry_mul_commonLeftHaarAverage_eq_real
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (sigma : SmoothCutoff)
    (hjoint : Integrable
      (fun q : T4 ×
          ((left.carrier.SurvivingCoordinate -> T4) ×
            (right.carrier.SurvivingCoordinate -> T4)) =>
        coefficientEndpointGeometry left right q.2 *
          mixedResidualAuxiliary left right pi sigma
            (r324CommonTranslate q.1 q.2.1) q.2.2)
      (paperMeasure.prod
        ((Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
            paperMeasure).prod
          (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
            paperMeasure)))) :
    (∫ v,
        (let p := ((left.twoHalfTerminal right
          |>.terminalProductPiMeasurableEquivNested pi).symm v);
          coefficientEndpointGeometry left right p *
            r324CommonLeftHaarAverage
              (mixedResidualAuxiliary left right pi sigma) p.1 p.2)
      ∂Measure.pi fun _ :
        (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure) =
      ∫ v,
        R324PaperMixedEndpoint.initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff
          (left.twoHalfTerminal right) sigma
          routes.left.completedRoute.terminalScale
          routes.right.completedRoute.terminalScale
          left.active right.active pi v
      ∂Measure.pi fun _ :
        (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure := by
  have hcomplexIntegrable :=
    integrable_initialNested_coefficientEndpointGeometry_mul_commonLeftHaarAverage
      left right pi (mixedResidualAuxiliary left right pi sigma) hjoint
  have hcomplexEq :=
    integral_initialNested_geometry_mul_commonLeftAverage_eq_mixedMajorant
      left right pi sigma hjoint
  calc
    (∫ v,
        (let p := ((left.twoHalfTerminal right
          |>.terminalProductPiMeasurableEquivNested pi).symm v);
          coefficientEndpointGeometry left right p *
            r324CommonLeftHaarAverage
              (mixedResidualAuxiliary left right pi sigma) p.1 p.2)
      ∂Measure.pi fun _ :
        (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure) =
        ∫ v,
          ((left.twoHalfTerminal right).initialNestedPullback pi
            (fun p => coefficientEndpointGeometry left right p *
              r324CommonLeftHaarAverage
                (mixedResidualAuxiliary left right pi sigma) p.1 p.2) v).re
        ∂Measure.pi fun _ :
          (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure := by
      apply integral_congr_ae
      filter_upwards with v
      let p0 :=
        ((left.twoHalfTerminal right
          |>.terminalProductPiMeasurableEquivNested pi).symm v)
      change _ = Complex.re
          ((coefficientEndpointGeometry left right p0 : Complex) *
            (r324CommonLeftHaarAverage
              (mixedResidualAuxiliary left right pi sigma)
              p0.1 p0.2 : Complex))
      norm_num
      rfl
    _ = (∫ v,
          (left.twoHalfTerminal right).initialNestedPullback pi
            (fun p => coefficientEndpointGeometry left right p *
              r324CommonLeftHaarAverage
                (mixedResidualAuxiliary left right pi sigma) p.1 p.2) v
        ∂Measure.pi fun _ :
          (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure).re :=
      integral_re hcomplexIntegrable
    _ = _ := by
      rw [hcomplexEq]
      simp only [Complex.ofReal_re]

end R324PaperCommonLeftAverage

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {alpha beta : Z4}
    {p : R324RefinedScheduleIndex m}
    {e0 : MomentContraction m}
    {leftProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) e0.1 alpha}
    {rightProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) e0.2.1 (-alpha)}
    {leftRoute : R324PaperHalfEndpointRoute leftProviders}
    {rightRoute : R324PaperHalfEndpointRoute rightProviders}

/-- Pointwise coefficient estimate on the actual completed route packages.
This is the exact input expected by the coefficient-parametric endpoint
majorant. -/
theorem R324PaperLeftRouteExactPackage.norm_commonLeftFourierCoefficient_le_auxiliaryAverage
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta)
    (right : R324PaperRightRouteExactLinearPackage left rightRoute)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hlarge : 1 <= eps ^ 2 *
      norm (z4EuclideanFrequency (alpha + beta)))
    (leftPost : left.bound.carrier.SurvivingCoordinate -> T4)
    (rightPost : right.package.bound.carrier.SurvivingCoordinate -> T4) :
    norm (r324CommonLeftFourierCoefficient (alpha + beta)
        (left.bound.crossCoefficient right.package.bound e0.2.2)
        leftPost rightPost) <=
      (4096 * ((m : Real) ^ 8 *
        r324ResidualFourierMajorantBase rho ^ (3 * m))) *
        eighthOrderFrequencyDecay
          (eps ^ 2 * norm (z4EuclideanFrequency (alpha + beta))) *
        r324CommonLeftHaarAverage
          (R324PaperCommonLeftAverage.mixedResidualAuxiliary
            (routes := {
              left := leftRoute
              right := rightRoute })
            left.bound right.package.bound e0.2.2 rho.auxiliaryCutoff)
          leftPost rightPost := by
  let routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders := {
    left := leftRoute
    right := rightRoute }
  rw [left.commonLeftFourierCoefficient_eq_residualTorusCoefficient right]
  have hbound :=
    norm_r324ResidualCommonLeftTorusCoefficient_le_centralDecay_auxiliaryHaarAverage
      rho heps heps1 e0 he0 (alpha + beta)
        (r324TwoHalfRootDoubledReconstruct
          left.bound.carrier right.package.bound.carrier
          (leftPost, rightPost)) hlarge
  rw [R324PaperCommonLeftAverage.commonLeftHaarAverage_mixedResidualAuxiliary_eq_rootAverage
    (routes := routes) left.bound right.package.bound e0.2.2
      rho.auxiliaryCutoff leftPost rightPost]
  simpa only [routes] using hbound

end R324WithinHalfResidualPrefix

namespace SmoothCutoff

open R324WithinHalfResidualPrefix

/-! ## Minimal signed endpoint/Fourier certificate -/

/-! ### Uniform absorption of the grouped Fourier loss -/

/-- Fixed base which absorbs the endpoint mass normalization, the explicit
`4096`, the eighth-degree order loss, and the three copies per order of the
cutoff derivative majorant. -/
def r324CommonLeftFourierAbsorptionBase (rho : SmoothCutoff) : Real :=
  (4096 *
      R324WithinHalfResidualPrefix.R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation) *
    r324DerivativeAbsorptionBase
      (r324ResidualFourierMajorantBase rho ^ 3)

theorem one_le_r324CommonLeftFourierAbsorptionBase (rho : SmoothCutoff) :
    1 <= r324CommonLeftFourierAbsorptionBase rho := by
  unfold r324CommonLeftFourierAbsorptionBase
  have hq : 1 <= (4096 : Real) *
      R324WithinHalfResidualPrefix.R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation := by
    calc
      (1 : Real) <= 4096 := by norm_num
      _ = 4096 * 1 := by ring
      _ <= 4096 *
          R324WithinHalfResidualPrefix.R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation :=
        mul_le_mul_of_nonneg_left
          R324WithinHalfResidualPrefix.R324PaperHalfEndpointUniformBound.one_le_twoHalfEndpointMassCompensation
          (by norm_num)
  have hd := one_le_r324DerivativeAbsorptionBase
    (r324ResidualFourierMajorantBase rho ^ 3)
  calc
    (1 : Real) = 1 * 1 := by ring
    _ <= (4096 *
        R324WithinHalfResidualPrefix.R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation) *
      r324DerivativeAbsorptionBase
        (r324ResidualFourierMajorantBase rho ^ 3) :=
      mul_le_mul hq hd zero_le_one (zero_le_one.trans hq)

/-- The whole grouped Fourier loss is exponential in the ambient order and
therefore fits into the `2m` power already present in the inserted primitive
majorant. -/
theorem r324CommonLeftFourierLoss_le_absorptionBase_pow
    (rho : SmoothCutoff) {m : Nat} (hm : 1 <= m) :
    (4096 *
        R324WithinHalfResidualPrefix.R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation) *
      ((m : Real) ^ 8 *
        r324ResidualFourierMajorantBase rho ^ (3 * m)) <=
      r324CommonLeftFourierAbsorptionBase rho ^ (2 * m) := by
  let q : Real := 4096 *
    R324WithinHalfResidualPrefix.R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation
  let d : Real := r324DerivativeAbsorptionBase
    (r324ResidualFourierMajorantBase rho ^ 3)
  let s : Real := q * d
  have hq : 1 <= q := by
    dsimp only [q]
    calc
      (1 : Real) <= 4096 := by norm_num
      _ = 4096 * 1 := by ring
      _ <= 4096 *
          R324WithinHalfResidualPrefix.R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation :=
        mul_le_mul_of_nonneg_left
          R324WithinHalfResidualPrefix.R324PaperHalfEndpointUniformBound.one_le_twoHalfEndpointMassCompensation
          (by norm_num)
  have hd : 1 <= d := by
    exact one_le_r324DerivativeAbsorptionBase _
  have hs : 1 <= s := by
    dsimp only [s]
    calc
      (1 : Real) = 1 * 1 := by ring
      _ <= q * d := mul_le_mul hq hd zero_le_one (zero_le_one.trans hq)
  have hbase : 0 <= r324ResidualFourierMajorantBase rho ^ 3 :=
    pow_nonneg
      (zero_le_one.trans (one_le_r324ResidualFourierMajorantBase rho)) _
  have hderiv :
      (m : Real) ^ 8 *
          r324ResidualFourierMajorantBase rho ^ (3 * m) <=
        d * d ^ (2 * m - 2) := by
    have h := r324_derivative_order_loss_le_absorptionBase_mul_power
      hbase hm
    rw [show r324ResidualFourierMajorantBase rho ^ (3 * m) =
        (r324ResidualFourierMajorantBase rho ^ 3) ^ m by
      rw [pow_mul]]
    exact h
  have hdle : d <= s := by
    calc
      d = 1 * d := by ring
      _ <= q * d :=
        mul_le_mul_of_nonneg_right hq (zero_le_one.trans hd)
  have hdpow : d ^ (2 * m - 2) <= s ^ (2 * m - 2) :=
    pow_le_pow_left₀ (zero_le_one.trans hd) hdle _
  have hqderiv : q *
      ((m : Real) ^ 8 * r324ResidualFourierMajorantBase rho ^ (3 * m)) <=
      s * s ^ (2 * m - 2) := by
    calc
      q * ((m : Real) ^ 8 *
          r324ResidualFourierMajorantBase rho ^ (3 * m)) <=
          q * (d * d ^ (2 * m - 2)) :=
        mul_le_mul_of_nonneg_left hderiv (zero_le_one.trans hq)
      _ = s * d ^ (2 * m - 2) := by
        dsimp only [s]
        ring
      _ <= s * s ^ (2 * m - 2) :=
        mul_le_mul_of_nonneg_left hdpow (zero_le_one.trans hs)
  have hpow : s * s ^ (2 * m - 2) <= s ^ (2 * m) := by
    rw [show s * s ^ (2 * m - 2) = s ^ (1 + (2 * m - 2)) by
      rw [pow_add, pow_one]]
    exact pow_le_pow_right₀ hs (by omega)
  simpa only [q, d, s, r324CommonLeftFourierAbsorptionBase] using
    hqderiv.trans hpow

private theorem r324CommonLeftFourierLoss_mul_integral_le_absorbed
    (rho : SmoothCutoff) {P epsilon supportConstant : Real} {m : Nat}
    (hP : 0 <= P) (hm : 1 <= m) :
    ((4096 *
        R324WithinHalfResidualPrefix.R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation) *
      ((m : Real) ^ 8 *
        r324ResidualFourierMajorantBase rho ^ (3 * m))) *
        (∫ z, primitiveInsertedMajorant
          P 1 epsilon supportConstant m z ∂paperMeasure) <=
      ∫ z, primitiveInsertedMajorant
        (r324CommonLeftFourierAbsorptionBase rho * P)
          1 epsilon supportConstant m z ∂paperMeasure := by
  have hmajorantNonneg : 0 <=
      ∫ z, primitiveInsertedMajorant
        P 1 epsilon supportConstant m z ∂paperMeasure :=
    integral_nonneg fun z =>
      primitiveInsertedMajorant_nonneg hP zero_le_one
  calc
    _ <= r324CommonLeftFourierAbsorptionBase rho ^ (2 * m) *
        (∫ z, primitiveInsertedMajorant
          P 1 epsilon supportConstant m z ∂paperMeasure) :=
      mul_le_mul_of_nonneg_right
        (r324CommonLeftFourierLoss_le_absorptionBase_pow rho hm)
        hmajorantNonneg
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      exact (primitiveInsertedMajorant_mul_constant
        (r324CommonLeftFourierAbsorptionBase rho) P 1 epsilon
          supportConstant m z).symm

private theorem commonLeftEndpointScalarAssembly
    {q modeWeight sacrifice fourierLoss centralDecay scaleRun
      baseIntegral finalIntegral epsilon : Real}
    (hq : 0 <= q) (hmode : 0 <= modeWeight)
    (hsacrifice : 0 <= sacrifice) (hfourier : 0 <= fourierLoss)
    (hcentral : 0 <= centralDecay) (_hscaleRun : 0 <= scaleRun)
    (hbaseIntegral : 0 <= baseIntegral)
    (hscale : scaleRun <= baseIntegral)
    (habsorb : (q * fourierLoss) * baseIntegral <= finalIntegral)
    (hsacrificeLe : sacrifice <= epsilon⁻¹ ^ (8 : Nat)) :
    (q * (modeWeight * sacrifice) *
        (fourierLoss * centralDecay)) * scaleRun <=
      (modeWeight * centralDecay) *
        (epsilon⁻¹ ^ (8 : Nat) * finalIntegral) := by
  have hpaper : 0 <= modeWeight * centralDecay * sacrifice :=
    mul_nonneg (mul_nonneg hmode hcentral) hsacrifice
  have hqFourier : 0 <= q * fourierLoss := mul_nonneg hq hfourier
  have hfinal : 0 <= finalIntegral := by
    exact le_trans
      (mul_nonneg hqFourier hbaseIntegral)
      habsorb
  calc
    (q * (modeWeight * sacrifice) *
        (fourierLoss * centralDecay)) * scaleRun =
        (modeWeight * centralDecay * sacrifice) *
          ((q * fourierLoss) * scaleRun) := by ring
    _ <= (modeWeight * centralDecay * sacrifice) *
        ((q * fourierLoss) * baseIntegral) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hscale hqFourier) hpaper
    _ <= (modeWeight * centralDecay * sacrifice) * finalIntegral :=
      mul_le_mul_of_nonneg_left habsorb hpaper
    _ = (modeWeight * centralDecay) *
        (sacrifice * finalIntegral) := by ring
    _ <= (modeWeight * centralDecay) *
        (epsilon⁻¹ ^ (8 : Nat) * finalIntegral) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hsacrificeLe hfinal)
        (mul_nonneg hmode hcentral)

/-- Optional abstract certificate for the exact downstream information
produced by the common-left endpoint calculation for one residual schedule.

This interface is useful for independent consumers, but it is not an
assumption of the final proof chain: the unconditional producer below
constructs the physical estimate directly.

`canonicalCommonLeftIdentity` is the signed Haar/Fubini identity and occurs
before any norm.  `commonLeftCoefficient_le_auxiliary` is the grouped
Fourier-to-auxiliary estimate.  The coefficient-parametric endpoint theorem
then gives the first legal endpoint-density norm, and its weighted integral
is discharged by the mixed-cutoff complete nested run. -/
structure R324PaperResidualCommonLeftEndpointCertificate
    (X : Type*) [MeasurableSpace X]
    (rho : SmoothCutoff) (primitiveConstant supportConstant : Real)
    (epsilon : Real) (m : Nat) (alpha beta : Z4)
    (p : R324RefinedScheduleIndex m) where
  leftOrder : Nat
  rightOrder : Nat
  crossOrder : Nat
  order_eq : leftOrder + rightOrder + crossOrder = m
  measure : Measure X
  endpointDensityWithCoefficient : (X -> Complex) -> X -> Complex
  originalCoefficient : X -> Complex
  commonLeftCoefficient : X -> Complex
  auxiliaryCoefficientMajorant : X -> Real
  mixedCutoffMajorant : X -> Real
  exactEndpointCollapse :
    (lamEps 1 epsilon : Complex) ^ (2 * (leftOrder + rightOrder)) *
        r324RefinedPhysicalIntegral rho epsilon m alpha beta p =
      ∫ x, endpointDensityWithCoefficient originalCoefficient x ∂measure
  canonicalCommonLeftIdentity :
    (∫ x, endpointDensityWithCoefficient originalCoefficient x ∂measure) =
      ∫ x, endpointDensityWithCoefficient commonLeftCoefficient x ∂measure
  commonLeftCoefficient_le_auxiliary :
    (fun x => norm (commonLeftCoefficient x)) ≤ᵐ[measure]
      auxiliaryCoefficientMajorant
  coefficientParametricEndpointDensity_le_mixedCutoffMajorant :
    ((fun x => norm (commonLeftCoefficient x)) ≤ᵐ[measure]
        auxiliaryCoefficientMajorant) ->
      (fun x => norm (endpointDensityWithCoefficient
        commonLeftCoefficient x)) ≤ᵐ[measure]
        mixedCutoffMajorant
  weightedMixedCutoffMajorant_integrable :
    Integrable
      (fun x => lamEps 1 epsilon ^ (2 * crossOrder) *
        mixedCutoffMajorant x) measure
  weightedMixedCutoffMajorant_integral_le :
    (∫ x, lamEps 1 epsilon ^ (2 * crossOrder) *
        mixedCutoffMajorant x ∂measure) <=
      ((paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        eighthOrderFrequencyDecay
          (epsilon ^ 2 *
            norm (z4EuclideanFrequency (alpha + beta)))) *
        (epsilon⁻¹ ^ (8 : Nat) *
          ∫ z, primitiveInsertedMajorant
            primitiveConstant 1 epsilon supportConstant m z
            ∂paperMeasure)

/-- Optional schedule-uniform certificate interface.  A concrete instance
would combine canonical endpoint averaging, the grouped residual
Fourier-to-auxiliary estimate, and the mixed-cutoff run.  The final
unconditional route does not consume this interface as a hypothesis. -/
def R324PaperResidualCommonLeftEndpointInput
    (rho : SmoothCutoff) (primitiveConstant supportConstant : Real) : Prop :=
  forall {epsilon : Real} (m : Nat) (alpha beta : Z4),
    forall (_hepsilon : 0 < epsilon)
      (_hepsilonSmall : epsilon <= 1 / 4)
      (_hlog : 1 <= abs (Real.log epsilon))
      (_hm2 : 2 <= m)
      (_hmtrunc : m <= truncOrder epsilon),
    forall (_hexternal : alpha + beta ≠ 0) (_hm : 0 < m)
      (p : R324RefinedScheduleIndex m),
      (r324RefinedScheduleRepresentative p).1.singles.Nonempty ->
      1 <= epsilon ^ 2 * norm (z4EuclideanFrequency (alpha + beta)) ->
      exists (X : Type) (inst : MeasurableSpace X),
        Nonempty (@R324PaperResidualCommonLeftEndpointCertificate X inst
          rho primitiveConstant supportConstant epsilon m alpha beta p)

/-!
The concrete certificate is assembled after choosing the canonical routes as
follows.

* `X` is the literal initial nested-coordinate function space of
  `left.bound.twoHalfTerminal right.bound`, with product paper measure.
* `endpointDensityWithCoefficient` is
  `nestedEndpointProductDensityWithCoefficient` after pulling a two-terminal
  coefficient back along `terminalProductPiMeasurableEquivNested`.
* `originalCoefficient` is `left.bound.crossCoefficient right.bound pi`;
  `commonLeftCoefficient` is its `r324CommonLeftFourierCoefficient` at
  `alpha + beta`.  The canonical route package supplies the signed integral
  identity before the first norm.
* `auxiliaryCoefficientMajorant` is the common-left Haar average of
  `r324ResidualPrimitiveSumProduct rho.auxiliaryCutoff`.  The grouped global
  Fourier theorem supplies its pointwise coefficient bound, including the
  eighth-order central decay and the absorbable `m^8 C^(3m)` loss.
* `mixedCutoffMajorant` is the coefficient-parametric endpoint majorant with
  that auxiliary coefficient.  Common-translation invariance of product Haar
  turns its integral into `completeNestedRunDensityWithCrossCutoff`; the mixed
  complete-run theorem and the existing reachable-scale ledger then supply
  the final weighted integral field.

Thus the certificate has no selected-slot, cell, word, or contraction-local
norm, and its fields correspond one-for-one to the paper's endpoint collapse,
common translation, derivative estimate, and Steps 2--3 nested run.
-/

/-- The analytic residual target in the physical-integral normalization used
by the exact two-half endpoint packages.  This is the convenient output of
the common-left Fourier / mixed-cutoff nested-run proof. -/
def R324PaperResidualHighPhysicalWeightedMajorantBound
    (rho : SmoothCutoff) (primitiveConstant supportConstant : Real) : Prop :=
  forall {epsilon : Real} (m : Nat) (alpha beta : Z4),
    forall (_hepsilon : 0 < epsilon)
      (_hepsilonSmall : epsilon <= 1 / 4)
      (_hlog : 1 <= abs (Real.log epsilon))
      (_hm2 : 2 <= m)
      (_hmtrunc : m <= truncOrder epsilon),
    forall (_hexternal : alpha + beta ≠ 0) (_hm : 0 < m)
      (p : R324RefinedScheduleIndex m),
      (r324RefinedScheduleRepresentative p).1.singles.Nonempty ->
      1 <= epsilon ^ 2 * norm (z4EuclideanFrequency (alpha + beta)) ->
      abs (lamEps 1 epsilon) ^ (2 * m) *
          norm (r324RefinedPhysicalIntegral rho epsilon m alpha beta p) <=
        ((paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          eighthOrderFrequencyDecay
            (epsilon ^ 2 *
              norm (z4EuclideanFrequency (alpha + beta)))) *
          (epsilon⁻¹ ^ (8 : Nat) *
            ∫ z, primitiveInsertedMajorant
              primitiveConstant 1 epsilon supportConstant m z
              ∂paperMeasure)

/-- Unconditional Step 4(B) producer in the physical normalization.
This is a whole-series implementation of the paper's high-frequency gain:
complete both signed endpoint routes, apply the common-left Fourier identity
before taking a norm, use the coefficient-parametric endpoint majorant once,
Haar-average the complete residual family, and finally run the already closed
Steps 2--3 majorant.  It is mathematically equivalent at the public estimate
boundary, but is not the paper's literal single-high-slot presentation. -/
theorem exists_r324PaperResidualHighPhysicalWeightedMajorantBound
    (rho : SmoothCutoff) :
    exists primitiveConstant supportConstant : Real,
      0 < primitiveConstant /\ 0 < supportConstant /\
        R324PaperResidualHighPhysicalWeightedMajorantBound
          rho primitiveConstant supportConstant := by
  obtain ⟨_routeSupport, C, K, A,
      _hrouteSupport, hC, hK, hA, hroutes⟩ :=
    R324WithinHalfResidualPrefix.exists_r324PaperTwoHalfEndpointRoutes_at_truncation
      rho
  obtain ⟨runSupport, B, hrunSupport, hB, hrun⟩ :=
    R324TwoHalfTerminalData.exists_integral_completeNestedRunDensityWithCrossCutoff_le_primitiveInsertedMajorant
      rho.auxiliaryCutoff
  let routeBase : Real := r324TwoHalfCompleteAbsorbedBase A C K B
  let finalConstant : Real :=
    r324CommonLeftFourierAbsorptionBase rho * routeBase
  have hrouteBase : 0 < routeBase := by
    exact r324TwoHalfCompleteAbsorbedBase_pos A C K B
  have hfinal : 0 < finalConstant := by
    exact mul_pos
      (lt_of_lt_of_le zero_lt_one
        (one_le_r324CommonLeftFourierAbsorptionBase rho))
      hrouteBase
  refine ⟨finalConstant, runSupport, hfinal, hrunSupport, ?_⟩
  intro epsilon m alpha beta heps hepsSmall hlog hm2 hmtrunc
    hexternal hm0 p hsingles hlarge
  have heps1 : epsilon <= 1 := hepsSmall.trans (by norm_num)
  have hm1 : 1 <= m := by omega
  let e0 := r324RefinedContractionRepresentative m p.1.1 p.2.1
  have he0 : e0 ∈ momentRefinedContractionFiber m p.1.1 p.2.1 := by
    exact r324RefinedContractionRepresentative_mem p.2.2
  have hleftSingles : e0.1.singles.Nonempty := by
    exact r324RefinedContractionRepresentative_singles_nonempty p hsingles
  have hrightSingles : e0.2.1.singles.Nonempty := by
    obtain ⟨i, hi⟩ := hleftSingles
    let j : e0.2.1.singles := e0.2.2 ⟨i, hi⟩
    exact ⟨j.1, j.2⟩
  obtain ⟨head, tail, hremaining⟩ :=
    exists_r324InitialNestedCross_head_of_singles_nonempty
      e0.1 e0.2.1 e0.2.2 hleftSingles
  obtain ⟨leftProviders, rightProviders, routes,
      _leftTrace, _rightTrace, _hterminalTrace⟩ :=
    hroutes 1 epsilon m e0.1 e0.2.1 alpha (-alpha)
      one_pos heps heps1 hlog hmtrunc hm0 hleftSingles hrightSingles
  obtain ⟨left⟩ :=
    R324WithinHalfResidualPrefix.R324PaperLeftRouteExactPackage.exists_of_route
      he0 hleftSingles routes.left beta
  obtain ⟨right⟩ :=
    R324WithinHalfResidualPrefix.R324PaperRightRouteExactPackage.exists_linear_of_route
      left hrightSingles routes.right
  let terminal := left.bound.twoHalfTerminal right.package.bound
  have hterminal : terminal = routes.terminal :=
    R324WithinHalfResidualPrefix.R324PaperHalfEndpointUniformBound.twoHalfTerminal_eq_routes
      routes left.bound right.package.bound
  let step :=
    r324InitialNestedCrossStepContext
      e0.1 e0.2.1 e0.2.2 head tail hremaining
  have hleftInitial :
      (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
    change (r324LeftHalfPullback
      (R324NestedCrossResidualPrefix.initial
        e0.1 e0.2.1 e0.2.2).activeCarrier).Nonempty
    rw [R324TwoHalfTerminalData.initial_leftHalfPullback_eq_terminalActive
      terminal e0.2.2]
    exact left.bound.active
  have hrightInitial :
      (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
    change (r324RightHalfPullback
      (R324NestedCrossResidualPrefix.initial
        e0.1 e0.2.1 e0.2.2).activeCarrier).Nonempty
    rw [R324TwoHalfTerminalData.initial_rightHalfPullback_eq_terminalActive
      terminal e0.2.2]
    exact right.package.bound.active
  let auxiliary :=
    R324PaperCommonLeftAverage.mixedResidualAuxiliary
      (routes := routes) left.bound right.package.bound e0.2.2
        rho.auxiliaryCutoff
  let commonCoefficient :=
    R324WithinHalfResidualPrefix.r324CommonLeftFourierCoefficient (alpha + beta)
      (left.bound.crossCoefficient right.package.bound e0.2.2)
  let endpointDensity :=
    left.bound.nestedEndpointProductDensityWithCoefficient
      (routes := routes) right.package.bound beta e0.2.2 commonCoefficient
  let geometryAverage :
      (terminal.NestedCoordinate e0.2.2 -> T4) -> Real := fun v =>
    let q := (terminal.terminalProductPiMeasurableEquivNested e0.2.2).symm v
    R324PaperCommonLeftAverage.coefficientEndpointGeometry
        left.bound right.package.bound q *
      r324CommonLeftHaarAverage auxiliary q.1 q.2
  let q : Real :=
    R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation
  let modeWeight : Real :=
    paperFourthOrderModeDecay alpha * paperFourthOrderModeDecay beta
  let sacrifice : Real :=
    r324EndpointPrimitiveSacrificeProduct epsilon routes.cases
  let fourierLoss : Real :=
    4096 * ((m : Real) ^ 8 *
      r324ResidualFourierMajorantBase rho ^ (3 * m))
  let centralDecay : Real :=
    eighthOrderFrequencyDecay
      (epsilon ^ 2 * norm (z4EuclideanFrequency (alpha + beta)))
  let crossOrder : Nat :=
    step.residual.remainingOrder
  let couplingPow : Real := lamEps 1 epsilon ^ (2 * crossOrder)
  let outerWeight : Real :=
    q * (modeWeight * sacrifice) * (fourierLoss * centralDecay)
  let weightedMajorant :
      (terminal.NestedCoordinate e0.2.2 -> T4) -> Real :=
    fun v => outerWeight * (couplingPow * geometryAverage v)
  have hcollapse :
      (lamEps 1 epsilon : Complex) ^
            (2 *
              ((R324WithinHalfResidualPrefix.initial
                  rho 1 epsilon e0.1).remainingOrder +
                (R324WithinHalfResidualPrefix.initial
                  rho 1 epsilon e0.2.1).remainingOrder)) *
          r324RefinedPhysicalIntegral rho epsilon m alpha beta p =
        ∫ v, endpointDensity v
          ∂Measure.pi fun _ : terminal.NestedCoordinate e0.2.2 =>
            paperMeasure := by
    exact
      (R324WithinHalfResidualPrefix.R324PaperRightRouteExactLinearPackage.exactCollapse_to_nested
        left right).trans
        (left.integral_nestedEndpointProductDensity_eq_commonLeftFourier right)
  have hnative :=
    R324PaperHalfEndpointUniformBound.ae_norm_nestedEndpointProductDensityWithCoefficient_le_compensatedGrouped
      (beta := beta) routes left.bound right.package.bound e0.2.2
        commonCoefficient
  have hcoefficient : forall
      (leftPost : left.bound.carrier.SurvivingCoordinate -> T4)
      (rightPost : right.package.bound.carrier.SurvivingCoordinate -> T4),
      norm (commonCoefficient leftPost rightPost) <=
        fourierLoss * centralDecay *
          r324CommonLeftHaarAverage auxiliary leftPost rightPost := by
    intro leftPost rightPost
    simpa only [commonCoefficient, fourierLoss, centralDecay, auxiliary] using
      left.norm_commonLeftFourierCoefficient_le_auxiliaryAverage
        right he0 heps heps1 hlarge leftPost rightPost
  have hgeometryNonneg : forall
      (v : terminal.NestedCoordinate e0.2.2 -> T4),
      0 <= geometryAverage v := by
    intro v
    let p0 :=
      (terminal.terminalProductPiMeasurableEquivNested e0.2.2).symm v
    dsimp only [geometryAverage, p0]
    exact mul_nonneg
      (R324PaperCommonLeftAverage.coefficientEndpointGeometry_nonneg
        left.bound right.package.bound _)
      (r324CommonLeftHaarAverage_nonneg auxiliary
        (fun leftPost rightPost =>
          R324PaperCommonLeftAverage.mixedResidualAuxiliary_nonneg
            left.bound right.package.bound e0.2.2 rho.auxiliaryCutoff
              leftPost rightPost) _ _)
  have hendpointPointwise :
      (fun v => couplingPow * norm (endpointDensity v)) ≤ᵐ[
        Measure.pi fun _ : terminal.NestedCoordinate e0.2.2 => paperMeasure]
        weightedMajorant := by
    filter_upwards [hnative] with v hv
    let p0 :=
      (terminal.terminalProductPiMeasurableEquivNested e0.2.2).symm v
    have hgroup :
        R324PaperHalfEndpointUniformBound.initialNestedCoefficientEndpointGroupedMajorant
            left.bound right.package.bound e0.2.2 commonCoefficient v <=
          (fourierLoss * centralDecay) * geometryAverage v := by
      rw [R324PaperHalfEndpointUniformBound.initialNestedCoefficientEndpointGroupedMajorant,
        R324PaperCommonLeftAverage.coefficientEndpointGroupedMajorant_eq_geometry_mul_norm]
      change
        R324PaperCommonLeftAverage.coefficientEndpointGeometry
            left.bound right.package.bound p0 *
            norm (commonCoefficient p0.1 p0.2) <=
          (fourierLoss * centralDecay) * geometryAverage v
      calc
        _ <= R324PaperCommonLeftAverage.coefficientEndpointGeometry
              left.bound right.package.bound p0 *
            (fourierLoss * centralDecay *
              r324CommonLeftHaarAverage auxiliary p0.1 p0.2) :=
          mul_le_mul_of_nonneg_left (hcoefficient p0.1 p0.2)
            (R324PaperCommonLeftAverage.coefficientEndpointGeometry_nonneg
              left.bound right.package.bound p0)
        _ = _ := by
          dsimp only [geometryAverage, p0]
          ring
    have hendpointWeight : 0 <= q * (modeWeight * sacrifice) := by
      exact mul_nonneg
        (zero_le_one.trans
          R324PaperHalfEndpointUniformBound.one_le_twoHalfEndpointMassCompensation)
        (mul_nonneg
          (mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
            (paperFourthOrderModeDecay_nonneg beta))
          (r324EndpointPrimitiveSacrificeProduct_nonneg epsilon routes.cases))
    have hcoupling : 0 <= couplingPow := by
      exact (even_two_mul crossOrder).pow_nonneg _
    calc
      couplingPow * norm (endpointDensity v) <=
          couplingPow *
            (q * (modeWeight * sacrifice) *
              R324PaperHalfEndpointUniformBound.initialNestedCoefficientEndpointGroupedMajorant
                left.bound right.package.bound e0.2.2 commonCoefficient v) :=
        mul_le_mul_of_nonneg_left hv hcoupling
      _ <= couplingPow *
          (q * (modeWeight * sacrifice) *
            ((fourierLoss * centralDecay) * geometryAverage v)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hgroup hendpointWeight) hcoupling
      _ = weightedMajorant v := by
        dsimp only [weightedMajorant, outerWeight]
        ring
  have hjoint :=
    R324PaperCommonLeftAverage.integrable_coefficientEndpointGeometry_mul_mixedResidual_commonLeft
      (routes := routes) left.bound right.package.bound e0.2.2
        rho.auxiliaryCutoff head tail hremaining one_pos heps heps1 hlog hmtrunc
  have hgeometryIntegrable : Integrable geometryAverage
      (Measure.pi fun _ : terminal.NestedCoordinate e0.2.2 => paperMeasure) := by
    simpa only [geometryAverage, terminal, auxiliary] using
      R324PaperCommonLeftAverage.integrable_initialNested_coefficientEndpointGeometry_mul_commonLeftHaarAverage_real
        (routes := routes) left.bound right.package.bound e0.2.2 auxiliary hjoint
  have hweightedIntegrable : Integrable weightedMajorant
      (Measure.pi fun _ : terminal.NestedCoordinate e0.2.2 => paperMeasure) := by
    have h := (hgeometryIntegrable.const_mul couplingPow).const_mul outerWeight
    apply h.congr
    filter_upwards with v
    dsimp only [weightedMajorant]
  have hhaarReal :
      (∫ v, geometryAverage v
        ∂Measure.pi fun _ : terminal.NestedCoordinate e0.2.2 => paperMeasure) =
      ∫ v,
        R324PaperMixedEndpoint.initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff
          terminal rho.auxiliaryCutoff
          routes.left.completedRoute.terminalScale
          routes.right.completedRoute.terminalScale
          left.bound.active right.package.bound.active e0.2.2 v
        ∂Measure.pi fun _ : terminal.NestedCoordinate e0.2.2 => paperMeasure := by
    simpa only [geometryAverage, terminal, auxiliary] using
      R324PaperCommonLeftAverage.integral_initialNested_coefficientEndpointGeometry_mul_commonLeftHaarAverage_eq_real
        (routes := routes) left.bound right.package.bound e0.2.2
          rho.auxiliaryCutoff hjoint
  let scaleFactor : Real :=
    (((∏ edge ∈ terminal.left.activeEdgeSlots,
          routes.left.completedRoute.terminalScale edge) *
        (∏ edge ∈ terminal.right.activeEdgeSlots,
          routes.right.completedRoute.terminalScale edge)) *
      invSqKerMass ^ (4 : Nat))
  let runIntegral : Real :=
    ∫ v, terminal.completeNestedRunDensityWithCrossCutoff
      rho.auxiliaryCutoff step hleftInitial hrightInitial v
      ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure
  let scaleRun : Real := scaleFactor * runIntegral
  have hmixedExact :
      (∫ v, couplingPow *
          R324PaperMixedEndpoint.initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff
            terminal rho.auxiliaryCutoff
            routes.left.completedRoute.terminalScale
            routes.right.completedRoute.terminalScale
            left.bound.active right.package.bound.active e0.2.2 v
        ∂Measure.pi fun _ : terminal.NestedCoordinate e0.2.2 => paperMeasure) =
        scaleRun := by
    simpa only [couplingPow, crossOrder, scaleRun, scaleFactor, runIntegral,
      step] using
      R324PaperMixedEndpoint.integral_lamEps_pow_initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff_eq
        terminal rho.auxiliaryCutoff
          routes.left.completedRoute.terminalScale
          routes.right.completedRoute.terminalScale
          left.bound.active right.package.bound.active e0.2.2
          head tail hremaining
  have hgeometryScaledIntegral :
      (∫ v, couplingPow * geometryAverage v
        ∂Measure.pi fun _ : terminal.NestedCoordinate e0.2.2 => paperMeasure) =
        scaleRun := by
    calc
      _ = couplingPow *
          (∫ v, geometryAverage v
            ∂Measure.pi fun _ : terminal.NestedCoordinate e0.2.2 =>
              paperMeasure) := by
        rw [integral_const_mul]
      _ = couplingPow *
          (∫ v,
            R324PaperMixedEndpoint.initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff
              terminal rho.auxiliaryCutoff
              routes.left.completedRoute.terminalScale
              routes.right.completedRoute.terminalScale
              left.bound.active right.package.bound.active e0.2.2 v
            ∂Measure.pi fun _ : terminal.NestedCoordinate e0.2.2 =>
              paperMeasure) := congrArg (fun x => couplingPow * x) hhaarReal
      _ = ∫ v, couplingPow *
            R324PaperMixedEndpoint.initialNestedEndpointIntegratedGroupedMajorantWithCrossCutoff
              terminal rho.auxiliaryCutoff
              routes.left.completedRoute.terminalScale
              routes.right.completedRoute.terminalScale
              left.bound.active right.package.bound.active e0.2.2 v
          ∂Measure.pi fun _ : terminal.NestedCoordinate e0.2.2 =>
            paperMeasure := by
        rw [integral_const_mul]
      _ = scaleRun := hmixedExact
  have hrunBound : runIntegral <=
      ∫ z, primitiveInsertedMajorant
        B 1 epsilon runSupport crossOrder z ∂paperMeasure := by
    simpa only [runIntegral, crossOrder, step] using
      hrun terminal one_pos heps heps1 hlog hmtrunc
        step hleftInitial hrightInitial
  have hscaleFactor : 0 <= scaleFactor := by
    dsimp only [scaleFactor]
    exact mul_nonneg
      (mul_nonneg
        (Finset.prod_nonneg fun edge _ =>
          (routes.left.completedRoute.terminalCertificate.scale_pos edge).le)
        (Finset.prod_nonneg fun edge _ =>
          (routes.right.completedRoute.terminalCertificate.scale_pos edge).le))
      (pow_nonneg invSqKerMass_nonneg _)
  have hleftReachable :
      R324WithinHalfBudgetScaleReachable
        e0.1 rho C 1 epsilon K A terminal.left.state
          routes.left.completedRoute.terminalScale := by
    rw [hterminal]
    exact routes.left.completedRoute.terminalReachable
  have hrightReachable :
      R324WithinHalfBudgetScaleReachable
        e0.2.1 rho C 1 epsilon K A terminal.right.state
          routes.right.completedRoute.terminalScale := by
    rw [hterminal]
    exact routes.right.completedRoute.terminalReachable
  have hrouteAbsorb :
      scaleFactor *
          (∫ z, primitiveInsertedMajorant
            B 1 epsilon runSupport crossOrder z ∂paperMeasure) <=
        ∫ z, primitiveInsertedMajorant
          routeBase 1 epsilon runSupport m z ∂paperMeasure := by
    simpa only [scaleFactor, crossOrder, step,
      r324InitialNestedCrossStepContext, routeBase] using
      r324_twoHalf_reachable_terminalScale_mul_integral_majorant_le
        (zero_le_one.trans hA) hC.le (zero_le_one.trans hK) hB.le
        zero_le_one heps
        terminal routes.left.completedRoute.terminalScale
          routes.right.completedRoute.terminalScale
          hleftReachable hrightReachable e0.2.2 hm1
  have hscaleRun : scaleRun <=
      ∫ z, primitiveInsertedMajorant
        routeBase 1 epsilon runSupport m z ∂paperMeasure := by
    calc
      scaleRun = scaleFactor * runIntegral := rfl
      _ <= scaleFactor *
          (∫ z, primitiveInsertedMajorant
            B 1 epsilon runSupport crossOrder z ∂paperMeasure) :=
        mul_le_mul_of_nonneg_left hrunBound hscaleFactor
      _ <= _ := hrouteAbsorb
  have hrouteBaseNonneg : 0 <= routeBase := hrouteBase.le
  have habsorb :
      (q * fourierLoss) *
          (∫ z, primitiveInsertedMajorant
            routeBase 1 epsilon runSupport m z ∂paperMeasure) <=
        ∫ z, primitiveInsertedMajorant
          finalConstant 1 epsilon runSupport m z ∂paperMeasure := by
    simpa only [q, fourierLoss, finalConstant, mul_assoc, mul_left_comm,
      mul_comm] using
      r324CommonLeftFourierLoss_mul_integral_le_absorbed
        (P := routeBase) (epsilon := epsilon) (supportConstant := runSupport)
        rho hrouteBaseNonneg hm1
  have hsacrificeLe :
      sacrifice <= epsilon⁻¹ ^ (8 : Nat) := by
    exact r324EndpointPrimitiveSacrificeProduct_le
      heps heps1 routes.cases
  have hbaseIntegral : 0 <=
      ∫ z, primitiveInsertedMajorant
        routeBase 1 epsilon runSupport m z ∂paperMeasure :=
    integral_nonneg fun z =>
      primitiveInsertedMajorant_nonneg hrouteBaseNonneg zero_le_one
  have hendpointIntegral :
      (∫ v, couplingPow * norm (endpointDensity v)
        ∂Measure.pi fun _ : terminal.NestedCoordinate e0.2.2 => paperMeasure) <=
      (modeWeight * centralDecay) *
        (epsilon⁻¹ ^ (8 : Nat) *
          ∫ z, primitiveInsertedMajorant
            finalConstant 1 epsilon runSupport m z ∂paperMeasure) := by
    have hsourceNonneg :
        0 ≤ᵐ[Measure.pi fun _ : terminal.NestedCoordinate e0.2.2 =>
          paperMeasure] fun v => couplingPow * norm (endpointDensity v) :=
      Filter.Eventually.of_forall fun v =>
        mul_nonneg ((even_two_mul crossOrder).pow_nonneg _) (norm_nonneg _)
    calc
      _ <= ∫ v, weightedMajorant v
          ∂Measure.pi fun _ : terminal.NestedCoordinate e0.2.2 =>
            paperMeasure :=
        integral_mono_of_nonneg hsourceNonneg hweightedIntegrable
          hendpointPointwise
      _ = outerWeight *
          (∫ v, couplingPow * geometryAverage v
            ∂Measure.pi fun _ : terminal.NestedCoordinate e0.2.2 =>
              paperMeasure) := by
        rw [integral_const_mul]
      _ = outerWeight * scaleRun := by rw [hgeometryScaledIntegral]
      _ <= _ := by
        dsimp only [outerWeight]
        exact commonLeftEndpointScalarAssembly
          (zero_le_one.trans
            R324PaperHalfEndpointUniformBound.one_le_twoHalfEndpointMassCompensation)
          (mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
            (paperFourthOrderModeDecay_nonneg beta))
          (r324EndpointPrimitiveSacrificeProduct_nonneg epsilon routes.cases)
          (mul_nonneg (by norm_num)
            (mul_nonneg (pow_nonneg (Nat.cast_nonneg m) _)
              (pow_nonneg
                (zero_le_one.trans
                  (one_le_r324ResidualFourierMajorantBase rho)) _)))
          (eighthOrderFrequencyDecay_nonneg _)
          (mul_nonneg hscaleFactor
            (integral_nonneg fun v =>
              terminal.completeNestedRunDensityWithCrossCutoff_nonneg
                rho.auxiliaryCutoff step hleftInitial hrightInitial v))
          hbaseIntegral hscaleRun habsorb hsacrificeLe
  have horder :=
    r324InitialSchedules_remainingOrders_eq_ambient
      rho 1 epsilon e0.1 e0.2.1 e0.2.2
  have horder' :
      (R324WithinHalfResidualPrefix.initial
          rho 1 epsilon e0.1).remainingOrder +
        (R324WithinHalfResidualPrefix.initial
          rho 1 epsilon e0.2.1).remainingOrder + crossOrder = m := by
    simpa only [crossOrder, step, r324InitialNestedCrossStepContext] using horder
  simpa only [modeWeight, centralDecay, finalConstant] using
    weighted_norm_le_of_collapsed_endpointIntegral
      (lam := 1) (ε := epsilon) (m := m)
      (leftOrder :=
        (R324WithinHalfResidualPrefix.initial
          rho 1 epsilon e0.1).remainingOrder)
      (rightOrder :=
        (R324WithinHalfResidualPrefix.initial
          rho 1 epsilon e0.2.1).remainingOrder)
      (crossOrder := crossOrder)
      horder' (r324RefinedPhysicalIntegral rho epsilon m alpha beta p)
        endpointDensity hcollapse hendpointIntegral

/-- The optional abstract signed endpoint/Fourier certificate suffices to
close the residual physical estimate.  This adapter is not on the final
unconditional proof path. -/
theorem R324PaperResidualCommonLeftEndpointInput.toPhysical
    {rho : SmoothCutoff} {primitiveConstant supportConstant : Real}
    (hinput : R324PaperResidualCommonLeftEndpointInput
      rho primitiveConstant supportConstant) :
    R324PaperResidualHighPhysicalWeightedMajorantBound
      rho primitiveConstant supportConstant := by
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    hexternal hm p hsingles hlarge
  obtain ⟨X, inst, ⟨certificate⟩⟩ :=
    hinput m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
      hexternal hm p hsingles hlarge
  letI : MeasurableSpace X := inst
  refine weighted_norm_le_of_collapsed_endpointIntegral
    (μ := certificate.measure) (lam := 1) (ε := epsilon)
    (m := m) (leftOrder := certificate.leftOrder)
    (rightOrder := certificate.rightOrder)
    (crossOrder := certificate.crossOrder)
    certificate.order_eq
    (r324RefinedPhysicalIntegral rho epsilon m alpha beta p)
    (certificate.endpointDensityWithCoefficient
      certificate.commonLeftCoefficient) ?_ ?_
  · exact certificate.exactEndpointCollapse.trans
      certificate.canonicalCommonLeftIdentity
  · have hsourceNonneg :
        0 ≤ᵐ[certificate.measure]
          fun x => lamEps 1 epsilon ^ (2 * certificate.crossOrder) *
            norm (certificate.endpointDensityWithCoefficient
              certificate.commonLeftCoefficient x) :=
      Filter.Eventually.of_forall fun x =>
        mul_nonneg ((even_two_mul certificate.crossOrder).pow_nonneg _)
          (norm_nonneg _)
    have hpointwise :
        (fun x => lamEps 1 epsilon ^ (2 * certificate.crossOrder) *
            norm (certificate.endpointDensityWithCoefficient
              certificate.commonLeftCoefficient x)) ≤ᵐ[
              certificate.measure]
          fun x => lamEps 1 epsilon ^ (2 * certificate.crossOrder) *
            certificate.mixedCutoffMajorant x := by
      filter_upwards [
          certificate.coefficientParametricEndpointDensity_le_mixedCutoffMajorant
            certificate.commonLeftCoefficient_le_auxiliary]
        with x hx
      exact mul_le_mul_of_nonneg_left hx
        ((even_two_mul certificate.crossOrder).pow_nonneg _)
    exact (integral_mono_of_nonneg hsourceNonneg
      certificate.weightedMixedCutoffMajorant_integrable hpointwise).trans
        certificate.weightedMixedCutoffMajorant_integral_le

/-- The genuinely residual part of paper Step 4(B), still at the complete
signed open-series boundary.  This is the precise target of the common-left
Fourier calculation; the full/full branch is discharged structurally below. -/
def R324PaperResidualHighWholeSeriesWeightedMajorantBound
    (rho : SmoothCutoff) (primitiveConstant supportConstant : Real) : Prop :=
  forall {epsilon : Real} (m : Nat) (alpha beta : Z4),
    forall (hepsilon : 0 < epsilon)
      (hepsilonSmall : epsilon <= 1 / 4)
      (_hlog : 1 <= abs (Real.log epsilon))
      (_hm2 : 2 <= m)
      (hmtrunc : m <= truncOrder epsilon),
    forall (hexternal : alpha + beta ≠ 0) (hm : 0 < m)
      (p : R324RefinedScheduleIndex m),
      (r324RefinedScheduleRepresentative p).1.singles.Nonempty ->
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

/-- Exact covariance reassembly transports a physical-integral estimate to
the complete signed open series without any triangle inequality. -/
theorem R324PaperResidualHighPhysicalWeightedMajorantBound.toOpenSeries
    {rho : SmoothCutoff} {primitiveConstant supportConstant : Real}
    (hphysical : R324PaperResidualHighPhysicalWeightedMajorantBound
      rho primitiveConstant supportConstant) :
    R324PaperResidualHighWholeSeriesWeightedMajorantBound
      rho primitiveConstant supportConstant := by
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    hexternal hm p hsingles hlarge
  have hepsilonOne : epsilon <= 1 :=
    hepsilonSmall.trans (by norm_num)
  have hopen :=
    rho.r324RefinedPhysicalIntegral_eq_openCovarianceSeries
      m alpha beta hepsilon hepsilonOne hexternal hm hmtrunc p
  rw [← hopen]
  exact hphysical m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    hexternal hm p hsingles hlarge

/-- Adding the structurally vanishing full/full branch turns the residual
common-left estimate into the public complete-series Step 4(B) producer. -/
theorem R324PaperResidualHighWholeSeriesWeightedMajorantBound.toHighWholeSeries
    {rho : SmoothCutoff} {primitiveConstant supportConstant : Real}
    (hprimitive : 0 <= primitiveConstant)
    (hresidual : R324PaperResidualHighWholeSeriesWeightedMajorantBound
      rho primitiveConstant supportConstant) :
    R324PaperHighWholeSeriesWeightedMajorantBound
      rho primitiveConstant supportConstant := by
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    hexternal hm p hlarge
  rcases r324RefinedScheduleRepresentative_singles_nonempty_or_isFull p with
    hsingles | hfull
  · exact hresidual m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
      hexternal hm p hsingles hlarge
  · have hepsilonOne : epsilon <= 1 :=
      hepsilonSmall.trans (by norm_num)
    have hopen :=
      rho.r324RefinedPhysicalIntegral_eq_openCovarianceSeries
        m alpha beta hepsilon hepsilonOne hexternal hm hmtrunc p
    have hzero :=
      rho.r324RefinedPhysicalIntegral_eq_zero_of_representative_isFull
        hepsilon hepsilonOne alpha beta p hexternal hfull
    have hseries :
        rho.r324RefinedQuadOpenCovarianceSeries
            hm epsilon alpha beta hexternal hepsilon hepsilonOne hmtrunc p = 0 :=
      hopen.symm.trans hzero
    rw [hseries, norm_zero, mul_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
          (paperFourthOrderModeDecay_nonneg beta))
        (eighthOrderFrequencyDecay_nonneg _))
      (mul_nonneg (by positivity)
        (integral_nonneg fun z =>
          primitiveInsertedMajorant_nonneg hprimitive (by norm_num)))

/-- Existential adapter from the residual common-left Fourier estimate to the
final assembly. -/
theorem exists_r324PaperHighWholeSeriesWeightedMajorantBound_of_residual
    (rho : SmoothCutoff)
    (hresidual :
      exists primitiveConstant supportConstant : Real,
        0 < primitiveConstant /\ 0 < supportConstant /\
          R324PaperResidualHighWholeSeriesWeightedMajorantBound
            rho primitiveConstant supportConstant) :
    exists primitiveConstant supportConstant : Real,
      0 < primitiveConstant /\ 0 < supportConstant /\
        R324PaperHighWholeSeriesWeightedMajorantBound
          rho primitiveConstant supportConstant := by
  obtain ⟨primitiveConstant, supportConstant,
      hprimitive, hsupport, hbound⟩ := hresidual
  exact ⟨primitiveConstant, supportConstant, hprimitive, hsupport,
    hbound.toHighWholeSeries hprimitive.le⟩

/-- One-step adapter from the exact endpoint/Fourier proof's physical
normalization to the public complete signed-series producer. -/
theorem exists_r324PaperHighWholeSeriesWeightedMajorantBound_of_physical
    (rho : SmoothCutoff)
    (hphysical :
      exists primitiveConstant supportConstant : Real,
        0 < primitiveConstant /\ 0 < supportConstant /\
          R324PaperResidualHighPhysicalWeightedMajorantBound
            rho primitiveConstant supportConstant) :
    exists primitiveConstant supportConstant : Real,
      0 < primitiveConstant /\ 0 < supportConstant /\
        R324PaperHighWholeSeriesWeightedMajorantBound
          rho primitiveConstant supportConstant := by
  obtain ⟨primitiveConstant, supportConstant,
      hprimitive, hsupport, hbound⟩ := hphysical
  have hopen : R324PaperResidualHighWholeSeriesWeightedMajorantBound
      rho primitiveConstant supportConstant :=
    R324PaperResidualHighPhysicalWeightedMajorantBound.toOpenSeries hbound
  exact ⟨primitiveConstant, supportConstant, hprimitive, hsupport,
    R324PaperResidualHighWholeSeriesWeightedMajorantBound.toHighWholeSeries
      hprimitive.le hopen⟩

/-- Unconditional paper Step 4(B) producer consumed by the final assembly. -/
theorem exists_r324PaperHighWholeSeriesWeightedMajorantBound
    (rho : SmoothCutoff) :
    exists primitiveConstant supportConstant : Real,
      0 < primitiveConstant /\ 0 < supportConstant /\
        R324PaperHighWholeSeriesWeightedMajorantBound
          rho primitiveConstant supportConstant := by
  exact exists_r324PaperHighWholeSeriesWeightedMajorantBound_of_physical rho
    (exists_r324PaperResidualHighPhysicalWeightedMajorantBound rho)

/-- Optional abstract assembly: a uniform common-left endpoint certificate
also implies the public Step 4(B) producer.  The stable final theorem above
instead uses the unconditional physical producer directly. -/
theorem exists_r324PaperHighWholeSeriesWeightedMajorantBound_of_commonLeftInput
    (rho : SmoothCutoff)
    (hinput :
      exists primitiveConstant supportConstant : Real,
        0 < primitiveConstant /\ 0 < supportConstant /\
          R324PaperResidualCommonLeftEndpointInput
            rho primitiveConstant supportConstant) :
    exists primitiveConstant supportConstant : Real,
      0 < primitiveConstant /\ 0 < supportConstant /\
        R324PaperHighWholeSeriesWeightedMajorantBound
          rho primitiveConstant supportConstant := by
  obtain ⟨primitiveConstant, supportConstant,
      hprimitive, hsupport, hcertificate⟩ := hinput
  exact exists_r324PaperHighWholeSeriesWeightedMajorantBound_of_physical rho
    ⟨primitiveConstant, supportConstant, hprimitive, hsupport,
      hcertificate.toPhysical⟩

end SmoothCutoff

end

end Anderson4D
