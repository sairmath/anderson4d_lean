import Anderson4D.Probability.NoiseConstruction
import Anderson4D.Probability.MollifiedNoise
import Anderson4D.Continuum.PeriodizedCovariance
import Anderson4D.Continuum.FourierCovariance
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Infinite Fourier series for the mollified noise

This file supplies the analytic infinite-series layer of blueprint node
`I-noise`.  The cutoff is first transported from the project's sup-norm
model of `ℝ⁴` to Euclidean space.  Compact support and smoothness make it
a Schwartz function, so its Fourier multiplier has rapid decay.  The
probabilistic statements below then isolate the exact summability input
needed to pass from finite Fourier sums to the totalized `tsum`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory ComplexConjugate
open scoped BigOperators ENNReal FourierTransform

/-- Spatial subtraction law for a torus Fourier character. -/
theorem charT4_sub_point (k : Z4) (x y : T4) :
    charT4 k (x - y) = charT4 k x * charT4 (-k) y := by
  simp only [charT4, Pi.sub_apply, Pi.neg_apply]
  calc
    (∏ i, fourier (k i) (x i - y i)) =
        ∏ i, fourier (k i) (x i) * fourier (-(k i)) (y i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [fourier_neg]
      simp only [fourier_apply]
      rw [show (k i) • (x i - y i) =
          (k i) • x i + -((k i) • y i) by module]
      rw [AddCircle.toCircle_add, AddCircle.toCircle_neg, Circle.coe_mul,
        Circle.coe_inv_eq_conj]
    _ = (∏ i, fourier (k i) (x i)) *
        ∏ i, fourier (-(k i)) (y i) := by
      rw [Finset.prod_mul_distrib]

/-! ## Absolute convergence of the random Fourier series -/

namespace NoiseModel

variable (M : NoiseModel)

/-- Joint measurability of the totalized mollified Fourier series in
the noise sample and the torus point. -/
theorem measurable_xiEps_joint
    (ρ : SmoothCutoff) (ε : ℝ) :
    Measurable (fun p : M.Ω × T4 =>
      M.xiEps ρ ε p.1 p.2) := by
  unfold xiEps
  apply measurable_const.mul
  apply Complex.measurable_re.comp
  apply Measurable.tsum
  intro k
  exact
    (measurable_const.mul
      ((M.measurable_g k).comp measurable_fst)).mul
      ((continuous_charT4 k).measurable.comp measurable_snd)

/-- The totalized infinite mollified Fourier series is measurable in
the noise sample for every fixed spatial point.  No summability
hypothesis is needed: measurability of `tsum` includes its junk value
off the summable branch. -/
theorem measurable_xiEps
    (ρ : SmoothCutoff) (ε : ℝ) (x : T4) :
    Measurable (fun ω => M.xiEps ρ ε ω x) := by
  unfold xiEps
  apply measurable_const.mul
  apply Complex.measurable_re.comp
  apply Measurable.tsum
  intro k
  exact (measurable_const.mul (M.measurable_g k)).mul
    measurable_const

/-- The covariance normalization gives unit `L²` norm for every complex
Fourier coefficient. -/
theorem integral_norm_g_sq (k : Z4) :
    ∫ ω, ‖M.g k ω‖ ^ 2 = 1 := by
  calc
    ∫ ω, ‖M.g k ω‖ ^ 2 =
        ∫ ω, (M.g k ω * conj (M.g k ω)).re := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
    _ = (∫ ω, M.g k ω * conj (M.g k ω)).re :=
      integral_re (M.integrable_g_mul_conj_g k k)
    _ = 1 := by rw [M.cov_conj]; simp

/-- Every normalized Fourier coefficient has first absolute moment at
most one. -/
theorem integral_norm_g_le_one (k : Z4) :
    ∫ ω, ‖M.g k ω‖ ≤ 1 := by
  have hg :
      MemLp (fun ω => ‖M.g k ω‖) (ENNReal.ofReal 2)
        (volume : Measure M.Ω) := by
    norm_num
    exact (M.memLp_g k 2 (by norm_num)).norm
  have hone :
      MemLp (fun _ω : M.Ω => (1 : ℝ)) (ENNReal.ofReal 2)
        (volume : Measure M.Ω) := by
    exact memLp_const 1
  have h :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := (volume : Measure M.Ω))
      Real.HolderConjugate.two_two
      (f := fun ω => ‖M.g k ω‖) (g := fun _ω => (1 : ℝ))
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall fun _ => zero_le_one)
      hg hone
  simpa [M.integral_norm_g_sq k, Real.rpow_two] using h

/-- Cauchy--Schwarz and the unit second moments bound the first
absolute moment of any coefficient product. -/
theorem integral_norm_g_mul_g_le_one (k l : Z4) :
    ∫ ω, ‖M.g k ω * M.g l ω‖ ≤ 1 := by
  have hgk :
      MemLp (fun ω => ‖M.g k ω‖) (ENNReal.ofReal 2)
        (volume : Measure M.Ω) := by
    norm_num
    exact (M.memLp_g k 2 (by norm_num)).norm
  have hgl :
      MemLp (fun ω => ‖M.g l ω‖) (ENNReal.ofReal 2)
        (volume : Measure M.Ω) := by
    norm_num
    exact (M.memLp_g l 2 (by norm_num)).norm
  have h :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := (volume : Measure M.Ω))
      Real.HolderConjugate.two_two
      (f := fun ω => ‖M.g k ω‖) (g := fun ω => ‖M.g l ω‖)
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hgk hgl
  simpa [norm_mul, M.integral_norm_g_sq k,
    M.integral_norm_g_sq l, Real.rpow_two] using h

/-- The random coefficient of the mollified Fourier series before
evaluation at a torus character. -/
def mollifiedRandomCoeff
    (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) (ω : M.Ω) : ℂ :=
  ρ.symbol ε k * M.g k ω

theorem measurable_mollifiedRandomCoeff
    (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    Measurable (M.mollifiedRandomCoeff ρ ε k) :=
  measurable_const.mul (M.measurable_g k)

theorem integrable_mollifiedRandomCoeff
    (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    Integrable (M.mollifiedRandomCoeff ρ ε k)
      (volume : Measure M.Ω) := by
  exact ((M.memLp_g k 1 (by norm_num)).integrable le_rfl).const_mul
    (ρ.symbol ε k)

/-- The `L¹` norm of one random coefficient is bounded by the
deterministic symbol norm. -/
theorem integral_norm_mollifiedRandomCoeff_le
    (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    ∫ ω, ‖M.mollifiedRandomCoeff ρ ε k ω‖ ≤ ‖ρ.symbol ε k‖ := by
  unfold mollifiedRandomCoeff
  simp_rw [norm_mul]
  rw [integral_const_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (M.integral_norm_g_le_one k)

/-- The `L¹` seminorm of one random coefficient is bounded by the
deterministic symbol norm, in `ℝ≥0∞` form. -/
theorem eLpNorm_one_mollifiedRandomCoeff_le
    (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    eLpNorm (M.mollifiedRandomCoeff ρ ε k) 1
        (volume : Measure M.Ω) ≤
      ENNReal.ofReal ‖ρ.symbol ε k‖ := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  calc
    ∫⁻ ω, ‖M.mollifiedRandomCoeff ρ ε k ω‖ₑ =
        ∫⁻ ω, ENNReal.ofReal ‖M.mollifiedRandomCoeff ρ ε k ω‖ := by
      apply lintegral_congr
      intro ω
      exact (ofReal_norm _).symm
    _ = ENNReal.ofReal
          (∫ ω, ‖M.mollifiedRandomCoeff ρ ε k ω‖) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal
        (M.integrable_mollifiedRandomCoeff ρ ε k).norm
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ ENNReal.ofReal ‖ρ.symbol ε k‖ :=
      ENNReal.ofReal_le_ofReal
        (M.integral_norm_mollifiedRandomCoeff_le ρ ε k)

/-- At positive scale, the random mollified coefficients are absolutely
summable almost surely. -/
theorem ae_summable_norm_mollifiedRandomCoeff
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂(volume : Measure M.Ω),
      Summable fun k : Z4 => ‖M.mollifiedRandomCoeff ρ ε k ω‖ := by
  let a : Z4 → NNReal := fun k => ⟨‖ρ.symbol ε k‖, norm_nonneg _⟩
  have ha_real : Summable fun k => (a k : ℝ) := by
    change Summable fun k => ‖ρ.symbol ε k‖
    exact ρ.summable_norm_symbol hε
  have ha : Summable a := NNReal.summable_coe.mp ha_real
  have htop : ∑' k : Z4, (a k : ℝ≥0∞) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr ha
  have hcoeff :
      ∑' k : Z4,
          eLpNorm (M.mollifiedRandomCoeff ρ ε k) 1
            (volume : Measure M.Ω) ≠ ∞ := by
    have hle :
        ∑' k : Z4,
            eLpNorm (M.mollifiedRandomCoeff ρ ε k) 1
              (volume : Measure M.Ω) ≤
          ∑' k : Z4, (a k : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro k
      rw [ENNReal.coe_nnreal_eq]
      change
        eLpNorm (M.mollifiedRandomCoeff ρ ε k) 1
            (volume : Measure M.Ω) ≤
          ENNReal.ofReal ‖ρ.symbol ε k‖
      exact M.eLpNorm_one_mollifiedRandomCoeff_le ρ ε k
    exact ne_top_of_le_ne_top htop hle
  exact summable_norm_of_tsum_eLpNorm_ne_top
    (p := (1 : ℝ≥0∞)) le_rfl
    (fun k => (M.measurable_mollifiedRandomCoeff ρ ε k).aestronglyMeasurable)
    hcoeff

/-- Polynomially weighted random mollified coefficient. -/
def weightedMollifiedRandomCoeff
    (r : ℕ) (ρ : SmoothCutoff) (ε : ℝ)
    (k : Z4) (ω : M.Ω) : ℂ :=
  (latticePolynomialWeight r k : ℂ) *
    M.mollifiedRandomCoeff ρ ε k ω

theorem measurable_weightedMollifiedRandomCoeff
    (r : ℕ) (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    Measurable (M.weightedMollifiedRandomCoeff r ρ ε k) :=
  measurable_const.mul (M.measurable_mollifiedRandomCoeff ρ ε k)

theorem integrable_weightedMollifiedRandomCoeff
    (r : ℕ) (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    Integrable (M.weightedMollifiedRandomCoeff r ρ ε k)
      (volume : Measure M.Ω) :=
  (M.integrable_mollifiedRandomCoeff ρ ε k).const_mul
    (latticePolynomialWeight r k : ℂ)

theorem integral_norm_weightedMollifiedRandomCoeff_le
    (r : ℕ) (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    ∫ ω, ‖M.weightedMollifiedRandomCoeff r ρ ε k ω‖ ≤
      latticePolynomialWeight r k * ‖ρ.symbol ε k‖ := by
  unfold weightedMollifiedRandomCoeff
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (latticePolynomialWeight_nonneg r k)]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (M.integral_norm_mollifiedRandomCoeff_le ρ ε k)
    (latticePolynomialWeight_nonneg r k)

theorem eLpNorm_one_weightedMollifiedRandomCoeff_le
    (r : ℕ) (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    eLpNorm (M.weightedMollifiedRandomCoeff r ρ ε k) 1
        (volume : Measure M.Ω) ≤
      ENNReal.ofReal
        (latticePolynomialWeight r k * ‖ρ.symbol ε k‖) := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  calc
    ∫⁻ ω, ‖M.weightedMollifiedRandomCoeff r ρ ε k ω‖ₑ =
        ∫⁻ ω, ENNReal.ofReal
          ‖M.weightedMollifiedRandomCoeff r ρ ε k ω‖ := by
      apply lintegral_congr
      intro ω
      exact (ofReal_norm _).symm
    _ = ENNReal.ofReal
          (∫ ω, ‖M.weightedMollifiedRandomCoeff r ρ ε k ω‖) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal
        (M.integrable_weightedMollifiedRandomCoeff r ρ ε k).norm
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (M.integral_norm_weightedMollifiedRandomCoeff_le r ρ ε k)

/-- Every polynomial weight is almost surely summable at positive
scale. -/
theorem ae_summable_norm_weightedMollifiedRandomCoeff
    (r : ℕ) (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂(volume : Measure M.Ω),
      Summable fun k : Z4 =>
        ‖M.weightedMollifiedRandomCoeff r ρ ε k ω‖ := by
  let a : Z4 → NNReal := fun k =>
    ⟨latticePolynomialWeight r k * ‖ρ.symbol ε k‖,
      mul_nonneg
        (latticePolynomialWeight_nonneg r k)
        (norm_nonneg _)⟩
  have ha_real : Summable fun k => (a k : ℝ) := by
    change Summable fun k =>
      latticePolynomialWeight r k * ‖ρ.symbol ε k‖
    exact ρ.summable_latticePolynomialWeight_mul_norm_symbol r hε
  have ha : Summable a := NNReal.summable_coe.mp ha_real
  have htop : ∑' k : Z4, (a k : ℝ≥0∞) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr ha
  have hcoeff :
      ∑' k : Z4,
          eLpNorm (M.weightedMollifiedRandomCoeff r ρ ε k) 1
            (volume : Measure M.Ω) ≠ ∞ := by
    have hle :
        ∑' k : Z4,
            eLpNorm (M.weightedMollifiedRandomCoeff r ρ ε k) 1
              (volume : Measure M.Ω) ≤
          ∑' k : Z4, (a k : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro k
      rw [ENNReal.coe_nnreal_eq]
      change
        eLpNorm (M.weightedMollifiedRandomCoeff r ρ ε k) 1
            (volume : Measure M.Ω) ≤
          ENNReal.ofReal
            (latticePolynomialWeight r k * ‖ρ.symbol ε k‖)
      exact M.eLpNorm_one_weightedMollifiedRandomCoeff_le r ρ ε k
    exact ne_top_of_le_ne_top htop hle
  exact summable_norm_of_tsum_eLpNorm_ne_top
    (p := (1 : ℝ≥0∞)) le_rfl
    (fun k =>
      (M.measurable_weightedMollifiedRandomCoeff r ρ ε k).aestronglyMeasurable)
    hcoeff

/-- One event of probability one works simultaneously for every
polynomial degree. -/
theorem ae_forall_nat_summable_norm_weightedMollifiedRandomCoeff
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂(volume : Measure M.Ω), ∀ r : ℕ,
      Summable fun k : Z4 =>
        ‖M.weightedMollifiedRandomCoeff r ρ ε k ω‖ := by
  rw [ae_all_iff]
  intro r
  exact M.ae_summable_norm_weightedMollifiedRandomCoeff r ρ hε

/-- A single probability-one event works for every polynomial degree
and every member of an arbitrary countable family of positive scales
(in particular for any prescribed sequence `εₙ ↓ 0`). -/
theorem ae_forall_nat_scale_forall_nat_weight
    (ρ : SmoothCutoff) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∀ᵐ ω ∂(volume : Measure M.Ω), ∀ n r : ℕ,
      Summable fun k : Z4 =>
        ‖M.weightedMollifiedRandomCoeff r ρ (ε n) k ω‖ := by
  rw [ae_all_iff]
  intro n
  exact M.ae_forall_nat_summable_norm_weightedMollifiedRandomCoeff
    ρ (hε n)

/-- A single probability-one event gives absolute convergence at every
spatial point, since torus characters have norm one. -/
theorem ae_forall_summable_norm_mollified_fourier
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂(volume : Measure M.Ω), ∀ x : T4,
      Summable fun k : Z4 =>
        ‖ρ.symbol ε k * M.g k ω * charT4 k x‖ := by
  filter_upwards [M.ae_summable_norm_mollifiedRandomCoeff ρ hε] with ω hω
  intro x
  refine hω.congr fun k => ?_
  simp [mollifiedRandomCoeff, norm_charT4]

/-- Hence the complex random Fourier series converges at every spatial
point on the same probability-one event. -/
theorem ae_forall_summable_mollified_fourier
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂(volume : Measure M.Ω), ∀ x : T4,
      Summable fun k : Z4 =>
        ρ.symbol ε k * M.g k ω * charT4 k x := by
  filter_upwards [M.ae_forall_summable_norm_mollified_fourier ρ hε] with ω hω
  intro x
  exact summable_norm_iff.mp (hω x)

/-- The infinite complex Fourier sum is pointwise real.  This identity
uses the exact `k ↦ -k` reality constraints and is valid independently
of summability because both conjugation and reindexing preserve the
junk-totalized `tsum`. -/
theorem conj_tsum_mollified_fourier_eq
    (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω) (x : T4) :
    conj (∑' k : Z4,
        ρ.symbol ε k * M.g k ω * charT4 k x) =
      ∑' k : Z4,
        ρ.symbol ε k * M.g k ω * charT4 k x := by
  rw [Complex.conj_tsum]
  calc
    (∑' k : Z4,
        conj (ρ.symbol ε k * M.g k ω * charT4 k x)) =
        ∑' k : Z4,
          ρ.symbol ε (-k) * M.g (-k) ω * charT4 (-k) x := by
      apply tsum_congr
      intro k
      rw [map_mul, map_mul, ← ρ.symbol_neg, ← M.reality,
        ← charT4_neg]
    _ = ∑' k : Z4,
          ρ.symbol ε k * M.g k ω * charT4 k x := by
      exact (Equiv.neg Z4).tsum_eq
        (fun k : Z4 =>
          ρ.symbol ε k * M.g k ω * charT4 k x)

/-- The imaginary part of the infinite Fourier series vanishes. -/
theorem tsum_mollified_fourier_im_eq_zero
    (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω) (x : T4) :
    (∑' k : Z4,
      ρ.symbol ε k * M.g k ω * charT4 k x).im = 0 := by
  have h := congrArg Complex.im
    (M.conj_tsum_mollified_fourier_eq ρ ε ω x)
  simp only [Complex.conj_im] at h
  linarith

/-- Absolute summability of the random coefficients gives uniform
convergence and hence continuity of the mollified field. -/
theorem continuous_xiEps_of_summable
    (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖) :
    Continuous (M.xiEps ρ ε ω) := by
  have hcomplex :
      Continuous fun x : T4 =>
        ∑' k : Z4,
          ρ.symbol ε k * M.g k ω * charT4 k x := by
    apply continuous_tsum
    · intro k
      exact continuous_const.mul (continuous_charT4 k)
    · exact hω
    · intro k x
      simp [mollifiedRandomCoeff, norm_charT4]
  unfold xiEps
  fun_prop

/-- For every positive scale, the totalized mollified field is
continuous almost surely. -/
theorem ae_continuous_xiEps
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂(volume : Measure M.Ω),
      Continuous (M.xiEps ρ ε ω) := by
  filter_upwards [M.ae_summable_norm_mollifiedRandomCoeff ρ hε] with ω hω
  exact M.continuous_xiEps_of_summable ρ ε ω hω

/-! ## Infinite covariance before the Poisson identification -/

/-- Complex version of the mollified field.  Its imaginary part is zero
by `tsum_mollified_fourier_im_eq_zero`. -/
def xiEpsC (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω) (x : T4) : ℂ :=
  ∑' k : Z4, mollifiedModeCoeff ρ ε x k * M.g k ω

/-- The complex field is the raw Fourier series multiplied by the
Lebesgue white-noise half-density `(2π)⁻²`. -/
theorem xiEpsC_eq_scale_mul_tsum
    (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω) (x : T4) :
    M.xiEpsC ρ ε ω x =
      (whiteNoiseFourierScale : ℂ) *
        ∑' k : Z4, ρ.symbol ε k * M.g k ω * charT4 k x := by
  unfold xiEpsC mollifiedModeCoeff
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  ring

@[simp]
theorem xiEpsC_re (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω) (x : T4) :
    (M.xiEpsC ρ ε ω x).re = M.xiEps ρ ε ω x := by
  rw [M.xiEpsC_eq_scale_mul_tsum]
  simp [xiEps]

@[simp]
theorem xiEpsC_im (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω) (x : T4) :
    (M.xiEpsC ρ ε ω x).im = 0 := by
  rw [M.xiEpsC_eq_scale_mul_tsum]
  simp [M.tsum_mollified_fourier_im_eq_zero ρ ε ω x]

/-- One term in the double Fourier expansion of the two-field
covariance. -/
def mollifiedPairTerm
    (ρ : SmoothCutoff) (ε : ℝ) (x y : T4)
    (p : Z4 × Z4) (ω : M.Ω) : ℂ :=
  (mollifiedModeCoeff ρ ε x p.1 * M.g p.1 ω) *
    (mollifiedModeCoeff ρ ε y p.2 * M.g p.2 ω)

theorem integrable_mollifiedPairTerm
    (ρ : SmoothCutoff) (ε : ℝ) (x y : T4) (p : Z4 × Z4) :
    Integrable (M.mollifiedPairTerm ρ ε x y p)
      (volume : Measure M.Ω) := by
  have hbase := (M.integrable_g_mul_g p.1 p.2).const_mul
    (mollifiedModeCoeff ρ ε x p.1 *
      mollifiedModeCoeff ρ ε y p.2)
  refine hbase.congr ?_
  filter_upwards with ω
  unfold mollifiedPairTerm
  ring

theorem integral_mollifiedPairTerm
    (ρ : SmoothCutoff) (ε : ℝ) (x y : T4) (p : Z4 × Z4) :
    ∫ ω, M.mollifiedPairTerm ρ ε x y p ω =
      mollifiedModeCoeff ρ ε x p.1 *
        mollifiedModeCoeff ρ ε y p.2 *
          (if p.1 = -p.2 then 1 else 0) := by
  have hfun :
      M.mollifiedPairTerm ρ ε x y p =
        fun ω =>
          (mollifiedModeCoeff ρ ε x p.1 *
            mollifiedModeCoeff ρ ε y p.2) *
              (M.g p.1 ω * M.g p.2 ω) := by
    funext ω
    unfold mollifiedPairTerm
    ring
  rw [hfun, integral_const_mul, M.cov_pair]

theorem integral_norm_mollifiedPairTerm_le
    (ρ : SmoothCutoff) (ε : ℝ) (x y : T4) (p : Z4 × Z4) :
    ∫ ω, ‖M.mollifiedPairTerm ρ ε x y p ω‖ ≤
      ‖mollifiedModeCoeff ρ ε x p.1‖ *
        ‖mollifiedModeCoeff ρ ε y p.2‖ := by
  have hfun :
      (fun ω => ‖M.mollifiedPairTerm ρ ε x y p ω‖) =
        fun ω =>
          (‖mollifiedModeCoeff ρ ε x p.1‖ *
            ‖mollifiedModeCoeff ρ ε y p.2‖) *
            ‖M.g p.1 ω * M.g p.2 ω‖ := by
    funext ω
    unfold mollifiedPairTerm
    simp
    ring
  rw [hfun, integral_const_mul]
  exact mul_le_of_le_one_right
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (M.integral_norm_g_mul_g_le_one p.1 p.2)

set_option maxHeartbeats 800000 in
/-- The product of the two infinite Fourier sums is the double `tsum`
almost surely. -/
theorem ae_xiEpsC_mul_eq_tsum_pair
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (x y : T4) :
    (fun ω => M.xiEpsC ρ ε ω x * M.xiEpsC ρ ε ω y) =ᵐ[
      (volume : Measure M.Ω)]
      fun ω => ∑' p : Z4 × Z4,
        M.mollifiedPairTerm ρ ε x y p ω := by
  filter_upwards [M.ae_forall_summable_mollified_fourier ρ hε] with ω hω
  let fx : Z4 → ℂ := fun k =>
    mollifiedModeCoeff ρ ε x k * M.g k ω
  let fy : Z4 → ℂ := fun k =>
    mollifiedModeCoeff ρ ε y k * M.g k ω
  have hx : Summable fx := by
    refine ((hω x).mul_left (whiteNoiseFourierScale : ℂ)).congr ?_
    intro k
    unfold fx mollifiedModeCoeff
    ring
  have hy : Summable fy := by
    refine ((hω y).mul_left (whiteNoiseFourierScale : ℂ)).congr ?_
    intro k
    unfold fy mollifiedModeCoeff
    ring
  have hxy_norm :
      Summable fun p : Z4 × Z4 => ‖fx p.1‖ * ‖fy p.2‖ :=
    Summable.mul_of_nonneg hx.norm hy.norm
      (fun k => norm_nonneg _) (fun k => norm_nonneg _)
  have hxy :
      Summable fun p : Z4 × Z4 => fx p.1 * fy p.2 := by
    rw [← summable_norm_iff]
    exact hxy_norm.congr fun p => (norm_mul _ _).symm
  exact hx.tsum_mul_tsum hy hxy

/-- Exact covariance of the two infinite complex Fourier sums, before
collapsing the Kronecker factor. -/
theorem integral_xiEpsC_mul_eq_tsum_pair
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (x y : T4) :
    ∫ ω, M.xiEpsC ρ ε ω x * M.xiEpsC ρ ε ω y =
      ∑' p : Z4 × Z4,
        mollifiedModeCoeff ρ ε x p.1 *
          mollifiedModeCoeff ρ ε y p.2 *
            (if p.1 = -p.2 then 1 else 0) := by
  have hint : ∀ p : Z4 × Z4,
      Integrable (M.mollifiedPairTerm ρ ε x y p)
        (volume : Measure M.Ω) :=
    fun p => M.integrable_mollifiedPairTerm ρ ε x y p
  have hxcoeff :
      Summable fun k : Z4 =>
        ‖mollifiedModeCoeff ρ ε x k‖ := by
    simpa [mollifiedModeCoeff, norm_mul, norm_charT4] using
      (ρ.summable_norm_symbol hε).mul_left
        ‖(whiteNoiseFourierScale : ℂ)‖
  have hycoeff :
      Summable fun k : Z4 =>
        ‖mollifiedModeCoeff ρ ε y k‖ := by
    simpa [mollifiedModeCoeff, norm_mul, norm_charT4] using
      (ρ.summable_norm_symbol hε).mul_left
        ‖(whiteNoiseFourierScale : ℂ)‖
  have hsymbols :
      Summable fun p : Z4 × Z4 =>
        ‖mollifiedModeCoeff ρ ε x p.1‖ *
          ‖mollifiedModeCoeff ρ ε y p.2‖ :=
    Summable.mul_of_nonneg
      hxcoeff hycoeff
      (fun k => norm_nonneg _) (fun k => norm_nonneg _)
  have hintegrals :
      Summable fun p : Z4 × Z4 =>
        ∫ ω, ‖M.mollifiedPairTerm ρ ε x y p ω‖ := by
    exact hsymbols.of_nonneg_of_le
      (fun p => integral_nonneg fun _ => norm_nonneg _)
      (fun p => M.integral_norm_mollifiedPairTerm_le ρ ε x y p)
  rw [integral_congr_ae (M.ae_xiEpsC_mul_eq_tsum_pair ρ hε x y)]
  rw [← integral_tsum_of_summable_integral_norm hint hintegrals]
  apply tsum_congr
  intro p
  exact M.integral_mollifiedPairTerm ρ ε x y p

/-- The Kronecker covariance collapses the double Fourier sum to the
paired single sum. -/
theorem tsum_pair_covariance_collapse
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (x y : T4) :
    (∑' p : Z4 × Z4,
        mollifiedModeCoeff ρ ε x p.1 *
          mollifiedModeCoeff ρ ε y p.2 *
            (if p.1 = -p.2 then 1 else 0)) =
      ∑' k : Z4,
        mollifiedModeCoeff ρ ε x k *
          mollifiedModeCoeff ρ ε y (-k) := by
  let F : Z4 × Z4 → ℂ := fun p =>
    mollifiedModeCoeff ρ ε x p.1 *
      mollifiedModeCoeff ρ ε y p.2 *
        (if p.1 = -p.2 then 1 else 0)
  have hxcoeff :
      Summable fun k : Z4 =>
        ‖mollifiedModeCoeff ρ ε x k‖ := by
    simpa [mollifiedModeCoeff, norm_mul, norm_charT4] using
      (ρ.summable_norm_symbol hε).mul_left
        ‖(whiteNoiseFourierScale : ℂ)‖
  have hycoeff :
      Summable fun k : Z4 =>
        ‖mollifiedModeCoeff ρ ε y k‖ := by
    simpa [mollifiedModeCoeff, norm_mul, norm_charT4] using
      (ρ.summable_norm_symbol hε).mul_left
        ‖(whiteNoiseFourierScale : ℂ)‖
  have hsymbols :
      Summable fun p : Z4 × Z4 =>
        ‖mollifiedModeCoeff ρ ε x p.1‖ *
          ‖mollifiedModeCoeff ρ ε y p.2‖ :=
    Summable.mul_of_nonneg
      hxcoeff hycoeff
      (fun k => norm_nonneg _) (fun k => norm_nonneg _)
  have hF : Summable F := by
    apply Summable.of_norm_bounded hsymbols
    intro p
    unfold F
    split_ifs with hp
    · simp only [mul_one, norm_mul]
      exact le_rfl
    · simp only [mul_zero, norm_zero]
      positivity
  change (∑' p : Z4 × Z4, F p) = _
  rw [hF.tsum_prod]
  apply tsum_congr
  intro k
  rw [tsum_eq_single (-k)]
  · change
      mollifiedModeCoeff ρ ε x k *
          mollifiedModeCoeff ρ ε y (-k) *
            (if k = -(-k) then 1 else 0) =
        mollifiedModeCoeff ρ ε x k *
          mollifiedModeCoeff ρ ε y (-k)
    rw [if_pos (by simp), mul_one]
  · intro l hl
    have hne : k ≠ -l := by
      intro h
      apply hl
      have hn := congrArg Neg.neg h
      simpa using hn.symm
    change
      mollifiedModeCoeff ρ ε x k *
          mollifiedModeCoeff ρ ε y l *
            (if k = -l then 1 else 0) = 0
    rw [if_neg hne, mul_zero]

/-- Exact covariance of the actual real-valued totalized field, in
single Fourier-series form. -/
theorem integral_xiEps_mul_eq_re_tsum
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (x y : T4) :
    ∫ ω, M.xiEps ρ ε ω x * M.xiEps ρ ε ω y =
      (∑' k : Z4,
        mollifiedModeCoeff ρ ε x k *
          mollifiedModeCoeff ρ ε y (-k)).re := by
  have hreal (ω : M.Ω) (z : T4) :
      M.xiEpsC ρ ε ω z = (M.xiEps ρ ε ω z : ℂ) := by
    apply Complex.ext
    · simp
    · simp
  have hcomplex := M.integral_xiEpsC_mul_eq_tsum_pair ρ hε x y
  rw [tsum_pair_covariance_collapse ρ hε x y] at hcomplex
  have hleft :
      (∫ ω, M.xiEpsC ρ ε ω x * M.xiEpsC ρ ε ω y) =
        ((∫ ω, M.xiEps ρ ε ω x * M.xiEps ρ ε ω y : ℝ) : ℂ) := by
    simp_rw [hreal]
    rw [show
      (fun ω =>
        (M.xiEps ρ ε ω x : ℂ) * (M.xiEps ρ ε ω y : ℂ)) =
        (fun ω =>
          ((M.xiEps ρ ε ω x * M.xiEps ρ ε ω y : ℝ) : ℂ)) by
      funext ω
      exact (Complex.ofReal_mul _ _).symm]
    rw [integral_complex_ofReal]
  rw [hleft] at hcomplex
  exact congrArg Complex.re hcomplex

/-- Algebraic normalization of one paired covariance mode. -/
theorem paired_mollified_mode_eq_norm_sq
    (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) (x y : T4) :
    mollifiedModeCoeff ρ ε x k *
        mollifiedModeCoeff ρ ε y (-k) =
      (whiteNoiseFourierScale : ℂ) ^ 2 *
        ((‖ρ.symbol ε k‖ ^ 2 : ℝ) : ℂ) *
          charT4 k (x - y) := by
  unfold mollifiedModeCoeff
  rw [ρ.symbol_neg, charT4_sub_point]
  calc
    ((whiteNoiseFourierScale : ℂ) * ρ.symbol ε k * charT4 k x) *
        ((whiteNoiseFourierScale : ℂ) * conj (ρ.symbol ε k) *
          charT4 (-k) y) =
      (whiteNoiseFourierScale : ℂ) ^ 2 *
        (ρ.symbol ε k * conj (ρ.symbol ε k)) *
          (charT4 k x * charT4 (-k) y) := by ring
    _ = (whiteNoiseFourierScale : ℂ) ^ 2 *
        ((‖ρ.symbol ε k‖ ^ 2 : ℝ) : ℂ) *
          (charT4 k x * charT4 (-k) y) := by
      rw [Complex.mul_conj, Complex.sq_norm]

/-- Exact covariance of the mollified field in probability-Haar Fourier
form.  The remaining spatial-side identification is a separate
multidimensional Poisson-summation theorem.  The coefficient
`whiteNoiseFourierScale ^ 2 = (2π)⁻⁴` is exactly the reciprocal-volume
factor needed for the intended identity
`fourierCovarianceT4 ρ ε = ρ.etaEpsT4 ε`. -/
theorem integral_xiEps_mul_eq_fourierCovarianceT4
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (x y : T4) :
    ∫ ω, M.xiEps ρ ε ω x * M.xiEps ρ ε ω y =
      fourierCovarianceT4 ρ ε (x - y) := by
  rw [M.integral_xiEps_mul_eq_re_tsum ρ hε x y]
  unfold fourierCovarianceT4
  congr 1
  apply tsum_congr
  intro k
  exact paired_mollified_mode_eq_norm_sq ρ ε k x y

end NoiseModel

end

end Anderson4D
