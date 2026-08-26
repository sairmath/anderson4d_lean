import Anderson4D.DetParametrix.Paper42_Moment.R324InteriorLogBudgetProof
import Anderson4D.DetParametrix.Core.ReductionBase

/-!
# The interior transport at order two: the exact mass and its `ε`-divergence

This file shows that, beyond the base order, the `ε`-uniform interior-core budget
`R324InteriorCoreLogBudget ρ ε m C` is **false** at `m = 2` for every
cutoff and every constant, and so is the corresponding Statement 1
interface `R324InteriorCoreMajorantBound`.  Thus the endpoint difference
factor must be retained at `m ≥ 2` to obtain the paper (3.24) scale.

**The mechanism.**  For the two-block schedule (both within-half
pairings the full swap) the extraction of each swap block removes the
*last* chain edge and installs the compensating difference factor
`G(v₁-y) - G(v₀-y)` there — but the interior core erases the first and
last chain edges into the endpoint legs, which the proved chain then
bounds in sup by `16·⟨α⟩⁻⁴⟨β⟩⁻⁴`.  What stays inside the interior core
is the *raw* middle chain edge `G(v₀-v₁)` against its own covariance
factor `η_ε(v₀-v₁)` on the same relative coordinate, per half.  The
parity/Taylor cancellation that renormalizes this block in the true
physical integral lives entirely in the discarded endpoint difference
factor, so the interior mass is the square of the raw one-block mass:

* `integral_greenFn_mul_etaEpsT4_eq` — the Green-weighted covariance
  mass, exactly: `∫ G η_ε = ⟨2π⟩⁻⁴ Σ_k ‖ρ̂(εk)‖² ⟨k⟩⁻²`;
* `exists_le_integral_greenFn_mul_etaEpsT4` — that mass is `≥ c ε⁻²`:
  all `≈ ε⁻⁴` low modes carry symbol weight `≥ 1/4`;
* `r324RefinedInteriorCoreIntegral_twoBlock` — the two-block interior
  core equals `((2π)⁴ ∫ G η_ε)²` (so it is `≳ ε⁻⁴`, against the
  budget's `C^4·|log ε|` allowance);
* `not_r324InteriorCoreLogBudget_two`,
  `not_r324InteriorCoreMajorantBound_two`,
  `r324InteriorCoreLogBudget_two_unsatisfiable` — the nonexistence theorems.

**Difference-retaining formulation.**  Any true `m ≥ 2` interior transport must keep,
for every within-half pair `(l, m-1)` extracted onto the terminal chain
edge, that edge's difference factor (or an equivalent `ε`-gain) inside
the interior object; equivalently, the endpoint legs may only be
sup-normalized after the terminal blocks are integrated jointly with
their difference factors.  The base order `m = 1` is unaffected: there
the interior skeleton is empty
(`r324InteriorCoreLogBudget_base`), and the divergence mechanism needs
an adjacent extracted pair, which first exists at `m = 2`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## The mollifier symbol near frequency zero -/

/-- The mollifier is integrable: its integral is one, not junk. -/
theorem SmoothCutoff.integrable_toFun (ρ : SmoothCutoff) :
    Integrable ρ.toFun :=
  Integrable.of_integral_ne_zero (by rw [ρ.integral_one]; norm_num)

/-- The unit character bound `‖e^{-i θ} - 1‖ ≤ |θ|` in the form used
below. -/
theorem norm_exp_neg_I_mul_ofReal_sub_one_le (θ : ℝ) :
    ‖Complex.exp (-Complex.I * (θ : ℝ)) - 1‖ ≤ |θ| := by
  have h : (-Complex.I * (θ : ℝ)) = Complex.I * ((-θ : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h]
  simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := -θ)

/-- Quantitative continuity of the mollifier symbol at frequency zero:
`‖ρ̂(ξ) - 1‖ ≤ radius · Σᵢ |ξᵢ|`. -/
theorem SmoothCutoff.norm_fourierR4_sub_one_le (ρ : SmoothCutoff)
    (ξ : R4) :
    ‖fourierR4 ρ ξ - 1‖ ≤ ρ.radius * ∑ i, |ξ i| := by
  have hone : (∫ x : R4, ((ρ x : ℝ) : ℂ)) = 1 := by
    rw [integral_complex_ofReal, ρ.integral_one, Complex.ofReal_one]
  have hker : Integrable
      (fun x : R4 =>
        Complex.exp (-Complex.I * (∑ i, x i * ξ i : ℝ)) *
          ((ρ x : ℝ) : ℂ)) := by
    have h1 : Measurable fun x : R4 => (∑ i, x i * ξ i : ℝ) := by
      apply Finset.measurable_sum
      intro i _
      exact (measurable_pi_apply i :
        Measurable fun x : R4 => x i).mul_const (ξ i)
    have h2 : Measurable fun x : R4 =>
        Complex.exp (-Complex.I * (∑ i, x i * ξ i : ℝ)) :=
      Complex.measurable_exp.comp
        ((Complex.measurable_ofReal.comp h1).const_mul (-Complex.I))
    have h3 : Measurable fun x : R4 => ((ρ x : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp
        (ρ.smooth 0).continuous.measurable
    refine ρ.integrable_toFun.mono' ?_ ?_
    · exact (h2.mul h3).aestronglyMeasurable
    · filter_upwards with x
      have h : (-Complex.I * (∑ i, x i * ξ i : ℝ)) =
          Complex.I * ((-(∑ i, x i * ξ i) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [norm_mul, h, Complex.norm_exp, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg x)]
      simp
  have hsub :
      (∫ x : R4,
        (Complex.exp (-Complex.I * (∑ i, x i * ξ i : ℝ)) - 1) *
          ((ρ x : ℝ) : ℂ)) =
        (∫ x : R4,
          Complex.exp (-Complex.I * (∑ i, x i * ξ i : ℝ)) *
            ((ρ x : ℝ) : ℂ)) -
          ∫ x : R4, ((ρ x : ℝ) : ℂ) := by
    calc
      (∫ x : R4,
          (Complex.exp (-Complex.I * (∑ i, x i * ξ i : ℝ)) - 1) *
            ((ρ x : ℝ) : ℂ)) =
          ∫ x : R4,
            (Complex.exp (-Complex.I * (∑ i, x i * ξ i : ℝ)) *
                ((ρ x : ℝ) : ℂ) -
              ((ρ x : ℝ) : ℂ)) := by
        congr 1
        funext x
        ring
      _ = (∫ x : R4,
            Complex.exp (-Complex.I * (∑ i, x i * ξ i : ℝ)) *
              ((ρ x : ℝ) : ℂ)) -
            ∫ x : R4, ((ρ x : ℝ) : ℂ) :=
        integral_sub hker ρ.integrable_toFun.ofReal
  have hdiff :
      fourierR4 ρ ξ - 1 =
        ∫ x : R4,
          (Complex.exp (-Complex.I * (∑ i, x i * ξ i : ℝ)) - 1) *
            ((ρ x : ℝ) : ℂ) := by
    rw [hsub, hone]
    rfl
  rw [hdiff]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hpoint : ∀ x : R4,
      ‖(Complex.exp (-Complex.I * (∑ i, x i * ξ i : ℝ)) - 1) *
          ((ρ x : ℝ) : ℂ)‖ ≤
        ρ x * (ρ.radius * ∑ i, |ξ i|) := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (ρ.nonneg x), mul_comm]
    by_cases hx : ρ x = 0
    · rw [hx, zero_mul, zero_mul]
    · have hmem : x ∈ Metric.ball (0 : R4) ρ.radius :=
        ρ.support_subset (Function.mem_support.mpr hx)
      have hxnorm : ‖x‖ < ρ.radius := by
        rwa [Metric.mem_ball, dist_zero_right] at hmem
      refine mul_le_mul_of_nonneg_left ?_ (ρ.nonneg x)
      refine (norm_exp_neg_I_mul_ofReal_sub_one_le _).trans ?_
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      exact ((norm_le_pi_norm x i).trans hxnorm.le).trans le_rfl
  calc
    (∫ x : R4,
        ‖(Complex.exp (-Complex.I * (∑ i, x i * ξ i : ℝ)) - 1) *
          ((ρ x : ℝ) : ℂ)‖) ≤
        ∫ x : R4, ρ x * (ρ.radius * ∑ i, |ξ i|) := by
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun x => norm_nonneg _)
        (ρ.integrable_toFun.mul_const _)
        (Filter.Eventually.of_forall hpoint)
    _ = ρ.radius * ∑ i, |ξ i| := by
      rw [integral_mul_const, ρ.integral_one, one_mul]

/-- The scaled-frequency symbol form of the zero-frequency continuity
bound. -/
theorem SmoothCutoff.norm_symbol_sub_one_le (ρ : SmoothCutoff)
    (ε : ℝ) (k : Z4) :
    ‖ρ.symbol ε k - 1‖ ≤ ρ.radius * ∑ i, |ε * ((k i : ℤ) : ℝ)| :=
  ρ.norm_fourierR4_sub_one_le fun i => ε * ((k i : ℤ) : ℝ)

/-- The Green-weighted covariance density is integrable. -/
theorem integrable_greenFn_mul_etaEpsT4 (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (fun z : T4 => greenFn z * ρ.etaEpsT4 ε z)
      paperMeasure := by
  obtain ⟨Cη, hCη, hbound⟩ := ρ.exists_pos_etaEpsT4_uniform_bound
  refine (integrable_greenFn_paper.const_mul
      (ε⁻¹ ^ (dim : ℕ) * Cη)).mono'
    ((measurable_greenFn.mul
      (ρ.measurable_etaEpsT4 ε)).aestronglyMeasurable) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (greenFn_nonneg z),
    abs_of_nonneg (ρ.etaEpsT4_nonneg ε z)]
  calc
    greenFn z * ρ.etaEpsT4 ε z ≤
        greenFn z * (ε⁻¹ ^ (dim : ℕ) * Cη) :=
      mul_le_mul_of_nonneg_left (hbound hε hε1 z) (greenFn_nonneg z)
    _ = ε⁻¹ ^ (dim : ℕ) * Cη * greenFn z := by ring

/-- The Lebesgue normalization constant is the explicit inverse square,
hence positive. -/
theorem whiteNoiseFourierScale_eq :
    NoiseModel.whiteNoiseFourierScale = ((2 * Real.pi) ^ (2 : ℕ))⁻¹ := by
  unfold NoiseModel.whiteNoiseFourierScale
  rw [zpow_neg]
  norm_cast

theorem whiteNoiseFourierScale_pos :
    0 < NoiseModel.whiteNoiseFourierScale := by
  rw [whiteNoiseFourierScale_eq]
  positivity

/-- Norm of one covariance mode coefficient. -/
theorem SmoothCutoff.norm_covarianceModeCoeff (ρ : SmoothCutoff)
    (ε : ℝ) (k : Z4) :
    ‖ρ.covarianceModeCoeff ε k‖ =
      NoiseModel.whiteNoiseFourierScale ^ 2 * ‖ρ.symbol ε k‖ ^ 2 := by
  unfold SmoothCutoff.covarianceModeCoeff
  rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg whiteNoiseFourierScale_pos.le,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖ρ.symbol ε k‖ ^ 2)]

/-- Summability of the Green-weighted symbol series. -/
theorem SmoothCutoff.summable_symbol_sq_mul_invBracket
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) :
    Summable fun k : Z4 =>
      ‖ρ.symbol ε k‖ ^ 2 *
        (1 + ∑ i, ((k i : ℤ) : ℝ) ^ 2)⁻¹ := by
  have hsq : Summable fun k : Z4 => ‖ρ.symbol ε k‖ ^ 2 := by
    have h := (ρ.summable_norm_covarianceModeCoeff hε).mul_left
      ((NoiseModel.whiteNoiseFourierScale ^ 2)⁻¹)
    refine h.congr fun k => ?_
    rw [ρ.norm_covarianceModeCoeff, ← mul_assoc,
      inv_mul_cancel₀ (pow_pos whiteNoiseFourierScale_pos 2).ne',
      one_mul]
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hsq
  · have hS : (0:ℝ) ≤ ∑ i, ((k i : ℤ) : ℝ) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    positivity
  · have hS : (0:ℝ) ≤ ∑ i, ((k i : ℤ) : ℝ) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hinv : (1 + ∑ i, ((k i : ℤ) : ℝ) ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      linarith
    calc
      ‖ρ.symbol ε k‖ ^ 2 * (1 + ∑ i, ((k i : ℤ) : ℝ) ^ 2)⁻¹ ≤
          ‖ρ.symbol ε k‖ ^ 2 * 1 := by
        gcongr
      _ = ‖ρ.symbol ε k‖ ^ 2 := mul_one _

/-- **The Green-weighted covariance mass, exactly.**  In the absolutely
convergent covariance Fourier series each mode is weighted by the Green
coefficient `⟨k⟩⁻²`; this is the two-block analogue of the base-order
zero-mode extraction `∫ η_ε = ⟨2π⟩⁻⁴ ‖ρ̂(0)‖² (2π)⁴`. -/
theorem integral_greenFn_mul_etaEpsT4_eq (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ z, greenFn z * ρ.etaEpsT4 ε z ∂paperMeasure =
      NoiseModel.whiteNoiseFourierScale ^ 2 *
        ∑' k : Z4,
          ‖ρ.symbol ε k‖ ^ 2 *
            (1 + ∑ i, ((k i : ℤ) : ℝ) ^ 2)⁻¹ := by
  have hcharG : ∀ k : Z4,
      Integrable (fun z : T4 => charT4 k z * (greenFn z : ℂ))
        paperMeasure :=
    fun k =>
      integrable_greenFn_paper.ofReal.bdd_mul
        (continuous_charT4 k).measurable.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z =>
          le_of_eq (norm_charT4 k z))
  have hint : ∀ k : Z4,
      Integrable
        (fun z : T4 =>
          ρ.covarianceModeCoeff ε k *
            (charT4 k z * (greenFn z : ℂ)))
        paperMeasure :=
    fun k => (hcharG k).const_mul _
  have hnormint : ∀ k : Z4,
      (∫ z, ‖ρ.covarianceModeCoeff ε k *
          (charT4 k z * (greenFn z : ℂ))‖ ∂paperMeasure) =
        ‖ρ.covarianceModeCoeff ε k‖ := by
    intro k
    have hfun :
        (fun z : T4 =>
          ‖ρ.covarianceModeCoeff ε k *
            (charT4 k z * (greenFn z : ℂ))‖) =
        fun z : T4 =>
          ‖ρ.covarianceModeCoeff ε k‖ * greenFn z := by
      funext z
      rw [norm_mul, norm_mul, norm_charT4, one_mul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (greenFn_nonneg z)]
    rw [hfun, integral_const_mul, integral_greenFn_paper, mul_one]
  have hsummable :
      Summable fun k : Z4 =>
        ∫ z, ‖ρ.covarianceModeCoeff ε k *
          (charT4 k z * (greenFn z : ℂ))‖ ∂paperMeasure :=
    (ρ.summable_norm_covarianceModeCoeff hε).congr fun k =>
      (hnormint k).symm
  have hswap :=
    integral_tsum_of_summable_integral_norm hint hsummable
  have hseries :
      (∫ z : T4,
        ∑' k : Z4,
          ρ.covarianceModeCoeff ε k *
            (charT4 k z * (greenFn z : ℂ)) ∂paperMeasure) =
      ((∫ z, greenFn z * ρ.etaEpsT4 ε z ∂paperMeasure : ℝ) : ℂ) := by
    have hfun :
        (fun z : T4 =>
          ∑' k : Z4,
            ρ.covarianceModeCoeff ε k *
              (charT4 k z * (greenFn z : ℂ))) =
        fun z : T4 => ((greenFn z * ρ.etaEpsT4 ε z : ℝ) : ℂ) := by
      funext z
      calc
        (∑' k : Z4,
            ρ.covarianceModeCoeff ε k *
              (charT4 k z * (greenFn z : ℂ))) =
            (∑' k : Z4,
              ρ.covarianceModeCoeff ε k * charT4 k z) *
              (greenFn z : ℂ) := by
          rw [← tsum_mul_right]
          exact tsum_congr fun k => by ring
        _ = ((ρ.etaEpsT4 ε z : ℝ) : ℂ) * (greenFn z : ℂ) := by
          have h := ρ.complexFourierCovarianceT4_eq_etaEpsT4 hε z
          unfold SmoothCutoff.complexFourierCovarianceT4 at h
          rw [h]
        _ = ((greenFn z * ρ.etaEpsT4 ε z : ℝ) : ℂ) := by
          push_cast
          ring
    rw [hfun]
    exact integral_ofReal
  have hterm : ∀ k : Z4,
      (∫ z, ρ.covarianceModeCoeff ε k *
          (charT4 k z * (greenFn z : ℂ)) ∂paperMeasure) =
        ((NoiseModel.whiteNoiseFourierScale ^ 2 *
          (‖ρ.symbol ε k‖ ^ 2 *
            (1 + ∑ i, ((k i : ℤ) : ℝ) ^ 2)⁻¹) : ℝ) : ℂ) := by
    intro k
    rw [integral_const_mul, paperFourierCoeff_greenFn k]
    unfold SmoothCutoff.covarianceModeCoeff
    push_cast
    ring
  have hfinal :
      ((∫ z, greenFn z * ρ.etaEpsT4 ε z ∂paperMeasure : ℝ) : ℂ) =
        ((NoiseModel.whiteNoiseFourierScale ^ 2 *
          ∑' k : Z4,
            ‖ρ.symbol ε k‖ ^ 2 *
              (1 + ∑ i, ((k i : ℤ) : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [← hseries, ← hswap, tsum_congr hterm]
    rw [Complex.ofReal_mul, Complex.ofReal_tsum, ← tsum_mul_left]
    exact tsum_congr fun k => by
      push_cast
      ring
  exact Complex.ofReal_injective hfinal

/-- **`ε⁻²`-divergence of the Green-weighted covariance mass.**  All
`≈ ε⁻⁴` low modes carry symbol weight `≥ 1/4`, and the Green weight
`⟨k⟩⁻²` sums to `≳ ε⁻²` over them.  The constant depends only on the
mollifier radius. -/
theorem exists_le_integral_greenFn_mul_etaEpsT4 (ρ : SmoothCutoff) :
    ∃ c εmax : ℝ, 0 < c ∧ 0 < εmax ∧ εmax ≤ 1 / 4 ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ εmax →
        c / ε ^ 2 ≤ ∫ z, greenFn z * ρ.etaEpsT4 ε z ∂paperMeasure := by
  set R : ℝ := max ρ.radius 1 with hRdef
  have hR1 : (1 : ℝ) ≤ R := le_max_right _ _
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hρR : ρ.radius ≤ R := le_max_left _ _
  refine ⟨NoiseModel.whiteNoiseFourierScale ^ 2 / (1024 * R ^ 2),
    1 / (32 * R),
    div_pos (pow_pos whiteNoiseFourierScale_pos 2) (by positivity),
    by positivity, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  intro ε hε hεmax
  set N : ℕ := ⌊1 / (8 * R * ε)⌋₊ with hNdef
  have hx0 : (0 : ℝ) ≤ 1 / (8 * R * ε) := by positivity
  have hNle : (N : ℝ) ≤ 1 / (8 * R * ε) := Nat.floor_le hx0
  have hNgt : 1 / (8 * R * ε) < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  set B : Finset Z4 :=
    Fintype.piFinset fun _ : Fin dim => Finset.Icc (0 : ℤ) (N : ℤ)
    with hBdef
  have hmem : ∀ k : Z4, k ∈ B → ∀ i, 0 ≤ k i ∧ k i ≤ (N : ℤ) := by
    intro k hk i
    rw [hBdef, Fintype.mem_piFinset] at hk
    exact Finset.mem_Icc.mp (hk i)
  have hterm : ∀ k : Z4, k ∈ B →
      (1 / 4 : ℝ) * (4 * ((N : ℝ) + 1) ^ 2)⁻¹ ≤
        ‖ρ.symbol ε k‖ ^ 2 *
          (1 + ∑ i, ((k i : ℤ) : ℝ) ^ 2)⁻¹ := by
    intro k hk
    have hki : ∀ i, 0 ≤ ((k i : ℤ) : ℝ) ∧ ((k i : ℤ) : ℝ) ≤ (N : ℝ) := by
      intro i
      constructor
      · exact_mod_cast (hmem k hk i).1
      · exact_mod_cast (hmem k hk i).2
    have hsum4 : (∑ i, |ε * ((k i : ℤ) : ℝ)|) ≤ ε * (4 * (N : ℝ)) := by
      have : ∀ i : Fin dim, |ε * ((k i : ℤ) : ℝ)| ≤ ε * (N : ℝ) := by
        intro i
        rw [abs_mul, abs_of_nonneg hε.le, abs_of_nonneg (hki i).1]
        exact mul_le_mul_of_nonneg_left (hki i).2 hε.le
      calc
        (∑ i, |ε * ((k i : ℤ) : ℝ)|) ≤ ∑ _i : Fin dim, ε * (N : ℝ) :=
          Finset.sum_le_sum fun i _ => this i
        _ = ε * (4 * (N : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          norm_num [dim]
          ring
    have hsymbol_half : (1 / 2 : ℝ) ≤ ‖ρ.symbol ε k‖ := by
      have hclose : ‖ρ.symbol ε k - 1‖ ≤ 1 / 2 := by
        refine (ρ.norm_symbol_sub_one_le ε k).trans ?_
        have h1 : ρ.radius * ∑ i, |ε * ((k i : ℤ) : ℝ)| ≤
            R * (ε * (4 * (N : ℝ))) := by
          have hsum0 : (0 : ℝ) ≤ ∑ i, |ε * ((k i : ℤ) : ℝ)| :=
            Finset.sum_nonneg fun i _ => abs_nonneg _
          calc
            ρ.radius * ∑ i, |ε * ((k i : ℤ) : ℝ)| ≤
                R * ∑ i, |ε * ((k i : ℤ) : ℝ)| :=
              mul_le_mul_of_nonneg_right hρR hsum0
            _ ≤ R * (ε * (4 * (N : ℝ))) :=
              mul_le_mul_of_nonneg_left hsum4 hR0.le
        refine h1.trans ?_
        have hN8 : (N : ℝ) * (8 * R * ε) ≤ 1 := by
          rw [← le_div_iff₀ (by positivity)]
          exact hNle
        nlinarith
      have := norm_sub_norm_le (1 : ℂ) (ρ.symbol ε k)
      rw [norm_one, norm_sub_rev] at this
      linarith
    have hbracket : (1 + ∑ i, ((k i : ℤ) : ℝ) ^ 2) ≤
        4 * ((N : ℝ) + 1) ^ 2 := by
      have hsq : ∀ i : Fin dim, ((k i : ℤ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
        intro i
        exact pow_le_pow_left₀ (hki i).1 (hki i).2 2
      have : (∑ i, ((k i : ℤ) : ℝ) ^ 2) ≤ 4 * (N : ℝ) ^ 2 := by
        calc
          (∑ i, ((k i : ℤ) : ℝ) ^ 2) ≤ ∑ _i : Fin dim, (N : ℝ) ^ 2 :=
            Finset.sum_le_sum fun i _ => hsq i
          _ = 4 * (N : ℝ) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            norm_num [dim]
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    have hS0 : (0 : ℝ) ≤ ∑ i, ((k i : ℤ) : ℝ) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hinv : (4 * ((N : ℝ) + 1) ^ 2)⁻¹ ≤
        (1 + ∑ i, ((k i : ℤ) : ℝ) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) hbracket
    have hsymbolsq : (1 / 4 : ℝ) ≤ ‖ρ.symbol ε k‖ ^ 2 := by
      nlinarith
    exact mul_le_mul hsymbolsq hinv (by positivity) (by positivity)
  have hcard : (B.card : ℝ) = ((N : ℝ) + 1) ^ 4 := by
    rw [hBdef, Fintype.card_piFinset]
    have h1 : (Finset.Icc (0 : ℤ) (N : ℤ)).card = N + 1 := by
      rw [Int.card_Icc]
      simp
    rw [Finset.prod_const, h1, Finset.card_univ, Fintype.card_fin]
    push_cast
    norm_num [dim]
  have hsumB :
      (B.card : ℝ) * ((1 / 4 : ℝ) * (4 * ((N : ℝ) + 1) ^ 2)⁻¹) ≤
        ∑ k ∈ B,
          ‖ρ.symbol ε k‖ ^ 2 *
            (1 + ∑ i, ((k i : ℤ) : ℝ) ^ 2)⁻¹ := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum B _ _ hterm
  have htsum :
      (∑ k ∈ B,
        ‖ρ.symbol ε k‖ ^ 2 *
          (1 + ∑ i, ((k i : ℤ) : ℝ) ^ 2)⁻¹) ≤
        ∑' k : Z4,
          ‖ρ.symbol ε k‖ ^ 2 *
            (1 + ∑ i, ((k i : ℤ) : ℝ) ^ 2)⁻¹ := by
    refine Summable.sum_le_tsum B (fun k _ => ?_)
      (ρ.summable_symbol_sq_mul_invBracket hε)
    have hS0 : (0 : ℝ) ≤ ∑ i, ((k i : ℤ) : ℝ) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    positivity
  have hNsq : (1 / (8 * R * ε)) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := by
    exact pow_le_pow_left₀ hx0 hNgt.le 2
  have hkey :
      NoiseModel.whiteNoiseFourierScale ^ 2 / (1024 * R ^ 2) / ε ^ 2 ≤
        NoiseModel.whiteNoiseFourierScale ^ 2 *
          ((B.card : ℝ) * ((1 / 4 : ℝ) * (4 * ((N : ℝ) + 1) ^ 2)⁻¹)) := by
    rw [hcard]
    have hexp :
        (((N : ℝ) + 1) ^ 4 * ((1 / 4 : ℝ) * (4 * ((N : ℝ) + 1) ^ 2)⁻¹)) =
          ((N : ℝ) + 1) ^ 2 / 16 := by
      have hne : ((N : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [hexp]
    have h16 : (1 / (8 * R * ε)) ^ 2 / 16 ≤ ((N : ℝ) + 1) ^ 2 / 16 := by
      linarith
    have hval : (1 / (8 * R * ε)) ^ 2 / 16 =
        (1 / (1024 * R ^ 2)) / ε ^ 2 := by
      field_simp
      ring
    calc
      NoiseModel.whiteNoiseFourierScale ^ 2 / (1024 * R ^ 2) / ε ^ 2 =
          NoiseModel.whiteNoiseFourierScale ^ 2 *
            ((1 / (1024 * R ^ 2)) / ε ^ 2) := by
        field_simp
      _ ≤ NoiseModel.whiteNoiseFourierScale ^ 2 *
            (((N : ℝ) + 1) ^ 2 / 16) := by
        rw [← hval]
        exact mul_le_mul_of_nonneg_left h16 (by positivity)
  calc
    NoiseModel.whiteNoiseFourierScale ^ 2 / (1024 * R ^ 2) / ε ^ 2 ≤
        NoiseModel.whiteNoiseFourierScale ^ 2 *
          ((B.card : ℝ) * ((1 / 4 : ℝ) * (4 * ((N : ℝ) + 1) ^ 2)⁻¹)) :=
      hkey
    _ ≤ NoiseModel.whiteNoiseFourierScale ^ 2 *
          ∑' k : Z4,
            ‖ρ.symbol ε k‖ ^ 2 *
              (1 + ∑ i, ((k i : ℤ) : ℝ) ^ 2)⁻¹ := by
      exact mul_le_mul_of_nonneg_left (hsumB.trans htsum) (by positivity)
    _ = ∫ z, greenFn z * ρ.etaEpsT4 ε z ∂paperMeasure :=
      (integral_greenFn_mul_etaEpsT4_eq ρ hε).symm

/-! ## The two-block schedule of order two -/

/-- The all-singles pairing of a two-point half. -/
def idPairingFinTwo : PartialPairing (Fin 2) :=
  ⟨id, fun _ => rfl⟩

/-- A pairing of the two-point half is the full swap or all singles. -/
theorem partialPairing_finTwo_classify (κ : PartialPairing (Fin 2)) :
    κ = pairingFinTwo ∨ κ = idPairingFinTwo := by
  rcases Finset.eq_empty_or_nonempty κ.pairSupport with h | h
  · right
    refine PartialPairing.ext fun i => ?_
    show κ i = i
    by_contra hi
    exact absurd (κ.pairSupport.eq_empty_iff_forall_notMem.mp h i)
      (by simp [PartialPairing.pairSupport, hi])
  · left
    obtain ⟨i, hi⟩ := h
    have hκi : κ i ≠ i := by
      simpa [PartialPairing.pairSupport] using hi
    have h01 : κ 0 = 1 := by
      fin_cases i
      · have hv := (κ 0).isLt
        have hne : (κ 0).val ≠ 0 := fun h => hκi (Fin.ext h)
        exact Fin.ext (by omega)
      · have hv := (κ 1).isLt
        have hne : (κ 1).val ≠ 1 := fun h => hκi (Fin.ext h)
        have h10 : κ 1 = 0 := Fin.ext (by omega)
        have happ := κ.apply_apply 1
        rw [h10] at happ
        rw [happ]
    have h10 : κ 1 = 0 := by
      have happ := κ.apply_apply 0
      rw [h01] at happ
      exact happ
    refine PartialPairing.ext fun j => ?_
    have hj : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    rcases hj j with rfl | rfl
    · rw [h01]; rfl
    · rw [h10]; rfl

/-- The two-block contraction: both within-half pairings are the full
swap, and there are no singles to cross-match. -/
def twoBlockContraction : MomentContraction 2 :=
  ⟨pairingFinTwo, pairingFinTwo, Equiv.refl _⟩

instance : IsEmpty { x : Fin 2 // x ∈ pairingFinTwo.singles } := by
  constructor
  intro x
  obtain ⟨i, hi⟩ := x
  rw [PartialPairing.mem_singles] at hi
  fin_cases i <;> exact absurd hi (by decide)

/-- The two-block signature fibre is a singleton: the endpoint
signature already determines both within-half pairings, and the swap
has no singles. -/
theorem momentContractionFiber_twoBlock :
    momentContractionFiber 2
        (momentContractionSignature twoBlockContraction) =
      {twoBlockContraction} := by
  ext e
  rw [Finset.mem_singleton]
  constructor
  · intro he
    have hsig := mem_momentContractionFiber.mp he
    obtain ⟨κp, κm, π⟩ := e
    rcases partialPairing_finTwo_classify κp with rfl | rfl <;>
      rcases partialPairing_finTwo_classify κm with rfl | rfl
    · have hπ : π = Equiv.refl _ := Subsingleton.elim _ _
      rw [hπ]
      rfl
    · have hsig' :
          momentWithinHalfEndpointSignature pairingFinTwo idPairingFinTwo =
            momentWithinHalfEndpointSignature pairingFinTwo pairingFinTwo :=
        hsig
      exact absurd hsig' (by decide)
    · have hsig' :
          momentWithinHalfEndpointSignature idPairingFinTwo pairingFinTwo =
            momentWithinHalfEndpointSignature pairingFinTwo pairingFinTwo :=
        hsig
      exact absurd hsig' (by decide)
    · have hsig' :
          momentWithinHalfEndpointSignature idPairingFinTwo idPairingFinTwo =
            momentWithinHalfEndpointSignature pairingFinTwo pairingFinTwo :=
        hsig
      exact absurd hsig' (by decide)
  · rintro rfl
    exact mem_momentContractionFiber.mpr rfl

/-- The two-block refined schedule index. -/
def twoBlockScheduleIndex : R324RefinedScheduleIndex 2 :=
  ⟨⟨momentContractionSignature twoBlockContraction,
      Finset.mem_image.mpr
        ⟨twoBlockContraction, Finset.mem_univ _, rfl⟩⟩,
    ⟨momentResidualChainSignature twoBlockContraction.1
        twoBlockContraction.2.1 twoBlockContraction.2.2,
      Finset.mem_image.mpr
        ⟨twoBlockContraction,
          mem_momentContractionFiber.mpr rfl, rfl⟩⟩⟩

/-- The canonical representative of the two-block schedule is the
two-block contraction itself: its signature fibre is a singleton. -/
theorem r324RefinedScheduleRepresentative_twoBlock :
    r324RefinedScheduleRepresentative twoBlockScheduleIndex =
      twoBlockContraction := by
  have h :=
    r324RefinedScheduleRepresentative_mem twoBlockScheduleIndex
  have h' :
      r324RefinedScheduleRepresentative twoBlockScheduleIndex ∈
        momentContractionFiber 2
          (momentContractionSignature twoBlockContraction) := h
  rw [momentContractionFiber_twoBlock] at h'
  exact Finset.mem_singleton.mp h'

/-- The refined fibre of the two-block schedule is the singleton. -/
theorem momentRefinedContractionFiber_twoBlock :
    momentRefinedContractionFiber 2
        (momentContractionSignature twoBlockContraction)
        (momentResidualChainSignature twoBlockContraction.1
          twoBlockContraction.2.1 twoBlockContraction.2.2) =
      {twoBlockContraction} := by
  unfold momentRefinedContractionFiber
  rw [momentContractionFiber_twoBlock, Finset.filter_singleton,
    if_pos rfl]

/-- The swap skeleton keeps exactly the raw middle chain edge: the
extracted difference factor sits on the erased last edge. -/
theorem r324RenormalizedInteriorCore_pairingFinTwo
    (w : Fin 2 → T4) :
    r324RenormalizedInteriorCore pairingFinTwo w =
      (greenFn (w 0 - w 1) : ℂ) := by
  unfold r324RenormalizedInteriorCore
  have hset :
      (((Finset.univ : Finset (Fin (2 + 1))).erase 0).erase
        (Fin.last 2)) = {1} := by decide
  rw [hset, Finset.prod_singleton]
  have hshort :
      extractedShortcutGreenEdge pairingFinTwo (assemble 0 0 w) 1 =
        0 := by
    unfold extractedShortcutGreenEdge
    rw [dif_neg (by decide)]
  rw [hshort, sub_zero]
  unfold originalGreenEdge
  have h1 : ((1 : Fin (2 + 1)).castSucc) = varIdx (0 : Fin 2) := rfl
  have h2 : ((1 : Fin (2 + 1)).succ) = varIdx (1 : Fin 2) := rfl
  rw [h1, h2, assemble_varIdx, assemble_varIdx]

/-- The two-block covariance product is the product of the two
within-half covariance factors. -/
theorem primitiveCovarianceProduct_twoBlock
    (ρ : SmoothCutoff) (ε : ℝ) (v : Fin (2 * 2) → T4) :
    primitiveCovarianceProduct ρ ε 2
        (momentCombinedPairing twoBlockContraction.1
          twoBlockContraction.2.1 twoBlockContraction.2.2) v =
      ρ.etaEpsT4 ε (v ⟨0, by omega⟩ - v ⟨1, by omega⟩) *
        ρ.etaEpsT4 ε (v ⟨2, by omega⟩ - v ⟨3, by omega⟩) := by
  unfold primitiveCovarianceProduct
  have hset :
      ((momentCombinedPairing twoBlockContraction.1
          twoBlockContraction.2.1
          twoBlockContraction.2.2).pairSupport.filter
        (fun i => i < (momentCombinedPairing twoBlockContraction.1
          twoBlockContraction.2.1 twoBlockContraction.2.2) i)) =
      ({⟨0, by omega⟩, ⟨2, by omega⟩} : Finset (Fin (2 * 2))) := by
    decide
  rw [hset]
  have hne : (⟨0, by omega⟩ : Fin (2 * 2)) ∉
      ({⟨2, by omega⟩} : Finset (Fin (2 * 2))) := by decide
  rw [Finset.prod_insert hne, Finset.prod_singleton]
  have h01 : (momentCombinedPairing twoBlockContraction.1
      twoBlockContraction.2.1 twoBlockContraction.2.2)
        (⟨0, by omega⟩ : Fin (2 * 2)) = ⟨1, by omega⟩ := by decide
  have h23 : (momentCombinedPairing twoBlockContraction.1
      twoBlockContraction.2.1 twoBlockContraction.2.2)
        (⟨2, by omega⟩ : Fin (2 * 2)) = ⟨3, by omega⟩ := by decide
  rw [h01, h23]

/-- Pointwise norm of the two-block interior core: the raw Green edge
of each half multiplies its own covariance factor on the *same*
relative coordinate. -/
theorem norm_r324RefinedEndpointCore_twoBlock
    (ρ : SmoothCutoff) (ε : ℝ) (v : Fin (2 * 2) → T4) :
    ‖r324RefinedEndpointCore ρ ε 2
        twoBlockScheduleIndex.1.1 twoBlockScheduleIndex.2.1
        (r324RefinedScheduleRepresentative twoBlockScheduleIndex) v‖ =
      (greenFn (v ⟨0, by omega⟩ - v ⟨1, by omega⟩) *
          ρ.etaEpsT4 ε (v ⟨0, by omega⟩ - v ⟨1, by omega⟩)) *
        (greenFn (v ⟨2, by omega⟩ - v ⟨3, by omega⟩) *
          ρ.etaEpsT4 ε (v ⟨2, by omega⟩ - v ⟨3, by omega⟩)) := by
  rw [r324RefinedScheduleRepresentative_twoBlock]
  unfold r324RefinedEndpointCore
  have hfiber :
      momentRefinedContractionFiber 2
          twoBlockScheduleIndex.1.1 twoBlockScheduleIndex.2.1 =
        {twoBlockContraction} :=
    momentRefinedContractionFiber_twoBlock
  rw [hfiber, Finset.sum_singleton]
  have hL :
      r324RenormalizedInteriorCore twoBlockContraction.1
          (fun i => v (leftMomentIndex i)) =
        (greenFn (v ⟨0, by omega⟩ - v ⟨1, by omega⟩) : ℂ) :=
    r324RenormalizedInteriorCore_pairingFinTwo _
  have hR :
      r324RenormalizedInteriorCore twoBlockContraction.2.1
          (fun i => v (rightMomentIndex i)) =
        (greenFn (v ⟨2, by omega⟩ - v ⟨3, by omega⟩) : ℂ) :=
    r324RenormalizedInteriorCore_pairingFinTwo _
  rw [hL, hR, primitiveCovarianceProduct_twoBlock ρ ε v]
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (greenFn_nonneg _),
    abs_of_nonneg (greenFn_nonneg _),
    abs_of_nonneg
      (mul_nonneg (ρ.etaEpsT4_nonneg ε _) (ρ.etaEpsT4_nonneg ε _))]
  ring

/-- One half of the two-block interior mass: the raw Green edge against
its own covariance factor, `(2π)⁴ ∫ G η_ε`. -/
theorem integral_twoBlock_half (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ w : Fin 2 → T4,
        greenFn (w 0 - w 1) * ρ.etaEpsT4 ε (w 0 - w 1)
        ∂(Measure.pi fun _ : Fin 2 => paperMeasure) =
      (2 * Real.pi) ^ (dim : ℕ) *
        ∫ z, greenFn z * ρ.etaEpsT4 ε z ∂paperMeasure := by
  have hint := integrable_greenFn_mul_etaEpsT4 ρ hε hε1
  have hmeas : Measurable
      (fun z : T4 => greenFn z * ρ.etaEpsT4 ε z) :=
    measurable_greenFn.mul (ρ.measurable_etaEpsT4 ε)
  have hsection : ∀ y : T4,
      Integrable
        (fun x : T4 =>
          greenFn (x - y) * ρ.etaEpsT4 ε (x - y)) paperMeasure := by
    intro y
    exact ((measurePreserving_sub_paper y).integrable_comp_emb
      (MeasurableEquiv.subRight y).measurableEmbedding).mpr hint
  have hinner : ∀ y : T4,
      (∫ x, greenFn (x - y) * ρ.etaEpsT4 ε (x - y) ∂paperMeasure) =
        ∫ z, greenFn z * ρ.etaEpsT4 ε z ∂paperMeasure := by
    intro y
    exact (measurePreserving_sub_paper y).integral_comp
      (MeasurableEquiv.subRight y).measurableEmbedding
      (fun z => greenFn z * ρ.etaEpsT4 ε z)
  have hprodInt :
      Integrable
        (fun p : T4 × T4 =>
          greenFn (p.1 - p.2) * ρ.etaEpsT4 ε (p.1 - p.2))
        (paperMeasure.prod paperMeasure) := by
    have hpm : AEStronglyMeasurable
        (fun p : T4 × T4 =>
          greenFn (p.1 - p.2) * ρ.etaEpsT4 ε (p.1 - p.2))
        (paperMeasure.prod paperMeasure) :=
      (hmeas.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
    refine (integrable_prod_iff' hpm).mpr ⟨?_, ?_⟩
    · filter_upwards with y
      exact hsection y
    · have hfun :
          (fun y : T4 =>
            ∫ x, ‖greenFn (x - y) * ρ.etaEpsT4 ε (x - y)‖
              ∂paperMeasure) =
          fun _ : T4 =>
            ∫ z, ‖greenFn z * ρ.etaEpsT4 ε z‖ ∂paperMeasure := by
        funext y
        exact (measurePreserving_sub_paper y).integral_comp
          (MeasurableEquiv.subRight y).measurableEmbedding
          (fun z => ‖greenFn z * ρ.etaEpsT4 ε z‖)
      rw [hfun]
      exact integrable_const _
  have hpi :
      (∫ w : Fin 2 → T4,
          greenFn (w 0 - w 1) * ρ.etaEpsT4 ε (w 0 - w 1)
          ∂(Measure.pi fun _ : Fin 2 => paperMeasure)) =
        ∫ p : T4 × T4,
          greenFn (p.1 - p.2) * ρ.etaEpsT4 ε (p.1 - p.2)
          ∂(paperMeasure.prod paperMeasure) :=
    (measurePreserving_piFinTwo
      (fun _ : Fin 2 => paperMeasure)).integral_comp'
      (fun p : T4 × T4 =>
        greenFn (p.1 - p.2) * ρ.etaEpsT4 ε (p.1 - p.2))
  rw [hpi, integral_prod_symm _ hprodInt]
  calc
    (∫ y, ∫ x,
        greenFn (x - y) * ρ.etaEpsT4 ε (x - y)
        ∂paperMeasure ∂paperMeasure) =
        ∫ _y : T4,
          (∫ z, greenFn z * ρ.etaEpsT4 ε z ∂paperMeasure)
          ∂paperMeasure :=
      integral_congr_ae
        (Filter.Eventually.of_forall fun y => hinner y)
    _ = (2 * Real.pi) ^ (dim : ℕ) *
          ∫ z, greenFn z * ρ.etaEpsT4 ε z ∂paperMeasure := by
      rw [integral_const, measureReal_def, paperMeasure_univ,
        ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-- **The two-block interior core, exactly.**  The mode-free interior
`L¹` mass of the two-block schedule is the square of the *raw*
one-block mass `(2π)⁴ ∫ G η_ε`: no difference factor survives inside
the interior core, because the extraction of each swap block sits on
the erased terminal chain edge. -/
theorem r324RefinedInteriorCoreIntegral_twoBlock (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    r324RefinedInteriorCoreIntegral ρ ε 2 twoBlockScheduleIndex =
      ((2 * Real.pi) ^ (dim : ℕ) *
        ∫ z, greenFn z * ρ.etaEpsT4 ε z ∂paperMeasure) ^ 2 := by
  unfold r324RefinedInteriorCoreIntegral
  have hpt :
      (fun v : Fin (2 * 2) → T4 =>
        ‖r324RefinedEndpointCore ρ ε 2
          twoBlockScheduleIndex.1.1 twoBlockScheduleIndex.2.1
          (r324RefinedScheduleRepresentative twoBlockScheduleIndex)
          v‖) =
      fun v : Fin (2 * 2) → T4 =>
        (fun p : (Fin 2 → T4) × (Fin 2 → T4) =>
          (greenFn (p.1 0 - p.1 1) *
              ρ.etaEpsT4 ε (p.1 0 - p.1 1)) *
            (greenFn (p.2 0 - p.2 1) *
              ρ.etaEpsT4 ε (p.2 0 - p.2 1)))
          (r324DoublePiMeasurableEquiv 2 v) := by
    funext v
    rw [norm_r324RefinedEndpointCore_twoBlock ρ ε v]
    rfl
  rw [hpt]
  rw [(measurePreserving_r324DoublePiMeasurableEquiv 2).integral_comp'
    (fun p : (Fin 2 → T4) × (Fin 2 → T4) =>
      (greenFn (p.1 0 - p.1 1) *
          ρ.etaEpsT4 ε (p.1 0 - p.1 1)) *
        (greenFn (p.2 0 - p.2 1) *
          ρ.etaEpsT4 ε (p.2 0 - p.2 1)))]
  rw [integral_prod_mul
    (f := fun w : Fin 2 → T4 =>
      greenFn (w 0 - w 1) * ρ.etaEpsT4 ε (w 0 - w 1))
    (g := fun w : Fin 2 → T4 =>
      greenFn (w 0 - w 1) * ρ.etaEpsT4 ε (w 0 - w 1))]
  rw [integral_twoBlock_half ρ hε hε1]
  ring

/-- **The `ε`-uniform interior-core budget is false at order two.**
For every cutoff and every constant, the two-block schedule violates
the budget at all sufficiently small scales: its interior mass is
`((2π)⁴ ∫ G η_ε)² ≳ ε⁻⁴`, while the budget allows only `|log ε|`. -/
theorem not_r324InteriorCoreLogBudget_two (ρ : SmoothCutoff) (C : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ 1 ≤ |Real.log ε| ∧
      ¬ R324InteriorCoreLogBudget ρ ε 2 C := by
  obtain ⟨c, εmax, hc, hεmax0, hεmax14, hlow⟩ :=
    exists_le_integral_greenFn_mul_etaEpsT4 ρ
  set B : ℝ := (2 * Real.pi) ^ (dim : ℕ) with hBdef
  have hB0 : 0 < B := by rw [hBdef]; positivity
  set D : ℝ := 16 * B ^ 2 * c ^ 2 with hDdef
  have hD0 : 0 < D := by rw [hDdef]; positivity
  set Cp : ℝ := C ^ (2 * 2) with hCpdef
  have hCp0 : 0 ≤ Cp := (even_two_mul 2).pow_nonneg C
  set n : ℕ :=
    max 4 (max (⌈εmax⁻¹⌉₊ + 1) (⌈Cp / D⌉₊ + 1)) with hndef
  have hn4 : (4 : ℕ) ≤ n := le_max_left _ _
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (4 : ℕ) ≤ n := hn4
    exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) this
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (4 : ℕ) ≤ n := hn4
    exact_mod_cast Nat.le_of_lt (Nat.lt_of_lt_of_le (by norm_num) this)
  refine ⟨(n : ℝ)⁻¹, by positivity, ?_, ?_, ?_⟩
  · have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    rw [one_div]
    exact inv_anti₀ (by norm_num) h4
  · rw [Real.log_inv, abs_neg,
      abs_of_nonneg (Real.log_nonneg hn1)]
    rw [Real.le_log_iff_exp_le hn0]
    calc
      Real.exp 1 ≤ 4 := by
        have h := Real.exp_one_lt_d9
        linarith
      _ ≤ (n : ℝ) := by exact_mod_cast hn4
  · intro hbudget
    have hε : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
    have hεεmax : (n : ℝ)⁻¹ ≤ εmax := by
      have hceil : εmax⁻¹ < (n : ℝ) := by
        have h1 : ⌈εmax⁻¹⌉₊ + 1 ≤ n :=
          le_trans (le_max_left _ _) (le_max_right _ _)
        have h2 : εmax⁻¹ ≤ (⌈εmax⁻¹⌉₊ : ℝ) := Nat.le_ceil _
        have h3 : ((⌈εmax⁻¹⌉₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
          exact_mod_cast h1
        linarith
      calc
        (n : ℝ)⁻¹ ≤ (εmax⁻¹)⁻¹ := inv_anti₀ (by positivity) hceil.le
        _ = εmax := inv_inv εmax
    have hε1 : (n : ℝ)⁻¹ ≤ 1 := le_trans hεεmax
      (hεmax14.trans (by norm_num))
    have hI := hlow hε hεεmax
    have hIn : c * (n : ℝ) ^ 2 ≤
        ∫ z, greenFn z * ρ.etaEpsT4 ((n : ℝ)⁻¹) z ∂paperMeasure := by
      refine le_trans (le_of_eq ?_) hI
      field_simp
    have hbud := hbudget twoBlockScheduleIndex
    rw [r324RefinedInteriorCoreIntegral_twoBlock ρ hε hε1] at hbud
    set L : ℝ := |Real.log ((n : ℝ)⁻¹)| with hLdef
    have hLeq : L = Real.log (n : ℝ) := by
      rw [hLdef, Real.log_inv, abs_neg,
        abs_of_nonneg (Real.log_nonneg hn1)]
    have hL1 : 1 ≤ L := by
      rw [hLeq, Real.le_log_iff_exp_le hn0]
      calc
        Real.exp 1 ≤ 4 := by
          have h := Real.exp_one_lt_d9
          linarith
        _ ≤ (n : ℝ) := by exact_mod_cast hn4
    have hL0 : 0 < L := lt_of_lt_of_le one_pos hL1
    have hLn : L ≤ (n : ℝ) := by
      rw [hLeq]
      have := Real.log_le_sub_one_of_pos hn0
      linarith
    have hCoreLB : (B * (c * (n : ℝ) ^ 2)) ^ 2 ≤
        (B * ∫ z, greenFn z * ρ.etaEpsT4 ((n : ℝ)⁻¹) z
          ∂paperMeasure) ^ 2 := by
      have h1 : 0 ≤ B * (c * (n : ℝ) ^ 2) := by positivity
      have h2 : B * (c * (n : ℝ) ^ 2) ≤
          B * ∫ z, greenFn z * ρ.etaEpsT4 ((n : ℝ)⁻¹) z
            ∂paperMeasure :=
        mul_le_mul_of_nonneg_left hIn hB0.le
      exact pow_le_pow_left₀ h1 h2 2
    have hCpD : Cp < D * (n : ℝ) ^ 3 := by
      have h1 : ⌈Cp / D⌉₊ + 1 ≤ n :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      have h2 : Cp / D ≤ (⌈Cp / D⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : ((⌈Cp / D⌉₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast h1
      have h4 : Cp / D < (n : ℝ) := by linarith
      have h5 : Cp < D * (n : ℝ) := by
        rw [div_lt_iff₀ hD0] at h4
        linarith
      have h6 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by nlinarith
      nlinarith
    have hfinal : Cp * L ^ 2 <
        16 * (L * (B * ∫ z, greenFn z *
          ρ.etaEpsT4 ((n : ℝ)⁻¹) z ∂paperMeasure) ^ 2) := by
      calc
        Cp * L ^ 2 ≤ Cp * (L * (n : ℝ)) := by
          have : L ^ 2 ≤ L * (n : ℝ) := by nlinarith
          exact mul_le_mul_of_nonneg_left this hCp0
        _ < D * (n : ℝ) ^ 3 * (L * (n : ℝ)) := by
          have hpos : 0 < L * (n : ℝ) := by positivity
          exact mul_lt_mul_of_pos_right hCpD hpos
        _ = 16 * (L * (B * (c * (n : ℝ) ^ 2)) ^ 2) := by
          rw [hDdef]
          ring
        _ ≤ 16 * (L * (B * ∫ z, greenFn z *
              ρ.etaEpsT4 ((n : ℝ)⁻¹) z ∂paperMeasure) ^ 2) := by
          have := mul_le_mul_of_nonneg_left hCoreLB hL0.le
          linarith
    exact absurd hbud (not_le.mpr hfinal)

/-- **Statement 1 itself is false at order two.**  The mode-free
interior inserted-majorant estimate `R324InteriorCoreMajorantBound`
fails for every positive coupling and every choice of constants at all
sufficiently small scales: the two-block interior mass `≳ ε⁻⁴/|log ε|²`
exceeds the integrated majorant `≲ 1/|log ε|`. -/
theorem not_r324InteriorCoreMajorantBound_two (ρ : SmoothCutoff)
    {lam : ℝ} (hlam : 0 < lam)
    (primitiveConstant supportConstant : ℝ)
    (hsupport : 0 < supportConstant) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ 1 ≤ |Real.log ε| ∧
      ¬ R324InteriorCoreMajorantBound ρ lam ε 2
          primitiveConstant supportConstant := by
  obtain ⟨c, εmax, hc, hεmax0, hεmax14, hlow⟩ :=
    exists_le_integral_greenFn_mul_etaEpsT4 ρ
  obtain ⟨Cball, Creg, hCball, hCreg, hmajUB⟩ :=
    exists_integral_primitiveInsertedMajorant_le
  set B : ℝ := (2 * Real.pi) ^ (dim : ℕ) with hBdef
  have hB0 : 0 < B := by rw [hBdef]; positivity
  set lam4 : ℝ := lam ^ (2 * 2) with hlam4def
  have hlam40 : 0 < lam4 := by rw [hlam4def]; positivity
  set K : ℝ := Cball * supportConstant ^ 2 + 2 * Creg with hKdef
  have hK0 : 0 < K := by rw [hKdef]; positivity
  set Q : ℝ := (primitiveConstant * lam) ^ (2 * 2) with hQdef
  have hQ0 : 0 ≤ Q := (even_two_mul 2).pow_nonneg _
  set D : ℝ := 16 * lam4 * B ^ 2 * c ^ 2 with hDdef
  have hD0 : 0 < D := by rw [hDdef]; positivity
  set n : ℕ :=
    max 4 (max (⌈εmax⁻¹⌉₊ + 1) (⌈Q * K / D⌉₊ + 1)) with hndef
  have hn4 : (4 : ℕ) ≤ n := le_max_left _ _
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hn4
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.le_of_lt (Nat.lt_of_lt_of_le (by norm_num) hn4)
  have hexpn : Real.exp 1 ≤ (n : ℝ) := by
    have h := Real.exp_one_lt_d9
    have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    linarith
  refine ⟨(n : ℝ)⁻¹, by positivity, ?_, ?_, ?_⟩
  · have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    rw [one_div]
    exact inv_anti₀ (by norm_num) h4
  · rw [Real.log_inv, abs_neg,
      abs_of_nonneg (Real.log_nonneg hn1)]
    rwa [Real.le_log_iff_exp_le hn0]
  · intro hbound
    have hε : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
    have hεεmax : (n : ℝ)⁻¹ ≤ εmax := by
      have h1 : ⌈εmax⁻¹⌉₊ + 1 ≤ n :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      have h2 : εmax⁻¹ ≤ (⌈εmax⁻¹⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : ((⌈εmax⁻¹⌉₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast h1
      calc
        (n : ℝ)⁻¹ ≤ (εmax⁻¹)⁻¹ :=
          inv_anti₀ (by positivity) (by linarith)
        _ = εmax := inv_inv εmax
    have hε1 : (n : ℝ)⁻¹ ≤ 1 :=
      le_trans hεεmax (hεmax14.trans (by norm_num))
    set L : ℝ := |Real.log ((n : ℝ)⁻¹)| with hLdef
    have hLeq : L = Real.log (n : ℝ) := by
      rw [hLdef, Real.log_inv, abs_neg,
        abs_of_nonneg (Real.log_nonneg hn1)]
    have hL1 : 1 ≤ L := by
      rw [hLeq]
      rwa [Real.le_log_iff_exp_le hn0]
    have hL0 : 0 < L := lt_of_lt_of_le one_pos hL1
    have hLn : L ≤ (n : ℝ) := by
      rw [hLeq]
      have := Real.log_le_sub_one_of_pos hn0
      linarith
    have hI := hlow hε hεεmax
    have hIn : c * (n : ℝ) ^ 2 ≤
        ∫ z, greenFn z * ρ.etaEpsT4 ((n : ℝ)⁻¹) z ∂paperMeasure := by
      refine le_trans (le_of_eq ?_) hI
      field_simp
    set I : ℝ :=
      ∫ z, greenFn z * ρ.etaEpsT4 ((n : ℝ)⁻¹) z ∂paperMeasure
      with hIdef
    have hbud := hbound twoBlockScheduleIndex
    rw [r324RefinedInteriorCoreIntegral_twoBlock ρ hε hε1,
      abs_lamEps_pow_two_mul hlam.le] at hbud
    have hmaj := hmajUB primitiveConstant lam ((n : ℝ)⁻¹)
      supportConstant 2 hε hε1 hsupport
      (by rw [← hLdef]; exact hL1)
    rw [← hLdef, ← hlam4def, ← hBdef] at hbud
    rw [← hLdef, ← hKdef, ← hQdef] at hmaj
    have hcomb : 16 * (lam4 / L ^ 2 * (B * I) ^ 2) ≤ Q * (K / L) :=
      hbud.trans hmaj
    have hIB : (B * (c * (n : ℝ) ^ 2)) ^ 2 ≤ (B * I) ^ 2 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      exact mul_le_mul_of_nonneg_left hIn hB0.le
    have hcomb2 :
        16 * (lam4 / L ^ 2 * (B * (c * (n : ℝ) ^ 2)) ^ 2) ≤
          Q * (K / L) := by
      refine le_trans ?_ hcomb
      have hfac : (0 : ℝ) ≤ lam4 / L ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hIB hfac
      linarith
    have hL2 : (0 : ℝ) < L ^ 2 := by positivity
    have hstep :
        16 * lam4 * (B * (c * (n : ℝ) ^ 2)) ^ 2 ≤ Q * K * L := by
      have h := mul_le_mul_of_nonneg_right hcomb2 hL2.le
      have heqL :
          16 * (lam4 / L ^ 2 * (B * (c * (n : ℝ) ^ 2)) ^ 2) * L ^ 2 =
            16 * lam4 * (B * (c * (n : ℝ) ^ 2)) ^ 2 := by
        field_simp
      have heqR : Q * (K / L) * L ^ 2 = Q * K * L := by
        field_simp
      rw [heqL, heqR] at h
      exact h
    have hQK : Q * K < D * (n : ℝ) ^ 3 := by
      have h1 : ⌈Q * K / D⌉₊ + 1 ≤ n :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      have h2 : Q * K / D ≤ (⌈Q * K / D⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : ((⌈Q * K / D⌉₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast h1
      have h4 : Q * K / D < (n : ℝ) := by linarith
      have h5 : Q * K < D * (n : ℝ) := by
        rw [div_lt_iff₀ hD0] at h4
        linarith
      have h6 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by nlinarith
      nlinarith
    have hDn4 : D * (n : ℝ) ^ 4 =
        16 * lam4 * (B * (c * (n : ℝ) ^ 2)) ^ 2 := by
      rw [hDdef]
      ring
    have hQKn : Q * K * L ≤ Q * K * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hLn (mul_nonneg hQ0 hK0.le)
    have hlast : Q * K * (n : ℝ) < D * (n : ℝ) ^ 3 * (n : ℝ) :=
      mul_lt_mul_of_pos_right hQK hn0
    have hfin : D * (n : ℝ) ^ 3 * (n : ℝ) = D * (n : ℝ) ^ 4 := by
      ring
    linarith

/-- The interior-core budget hypothesis is unsatisfiable at order two:
no `ε`-uniform constant
discharges it on the admissible scale range, so
`exists_deterministicMoment_paper_bound_of_logBudget_and_veryHighFrequency`
and `exists_deterministicMoment_paper_bound_of_logBudget_and_highFrequency`
are vacuous at `m = 2`. -/
theorem r324InteriorCoreLogBudget_two_unsatisfiable
    (ρ : SmoothCutoff) (C : ℝ) :
    ¬ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → 1 ≤ |Real.log ε| →
        R324InteriorCoreLogBudget ρ ε 2 C := by
  intro h
  obtain ⟨ε, hε, hε14, hlog, hnot⟩ :=
    not_r324InteriorCoreLogBudget_two ρ C
  exact hnot (h ε hε hε14 hlog)

end

end Anderson4D
