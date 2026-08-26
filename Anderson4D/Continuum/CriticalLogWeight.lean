import Anderson4D.Continuum.CellChainComplete
import Anderson4D.Continuum.SingularConv

/-!
# Critical logarithmic weight on the four-torus

The binary convolution of two inverse-square kernels has a logarithmic
singularity.  This file packages the elementary pointwise inequalities
needed to average that logarithm at a moving mollifier scale.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set

/-- The nonnegative critical weight produced by the sharp binary
inverse-square convolution.  Mathlib uses `Real.log 0 = 0`; this harmless
value agrees with all a.e. applications below. -/
def criticalLogWeight (z : T4) : ℝ :=
  1 + |Real.log ‖z‖|

theorem criticalLogWeight_nonneg (z : T4) :
    0 ≤ criticalLogWeight z := by
  unfold criticalLogWeight
  positivity

theorem measurable_criticalLogWeight :
    Measurable criticalLogWeight := by
  unfold criticalLogWeight
  fun_prop

/-- The half-power kernel `|z|⁻¹`, expressed intrinsically through the
paper's inverse-square model. -/
def invSqKerHalf (z : T4) : ℝ :=
  (invSqKer z) ^ (1 / 2 : ℝ)

theorem invSqKerHalf_nonneg (z : T4) :
    0 ≤ invSqKerHalf z :=
  Real.rpow_nonneg (invSqKer_nonneg z) _

theorem measurable_invSqKerHalf :
    Measurable invSqKerHalf :=
  measurable_invSqKer.pow_const _

private theorem abs_log_le_self_add_inv
    {t : ℝ} (ht : 0 < t) :
    |Real.log t| ≤ t + t⁻¹ := by
  have hupper₀ :=
    Real.log_le_sub_one_of_pos ht
  have hupper : Real.log t ≤ t + t⁻¹ := by
    nlinarith [inv_nonneg.mpr ht.le]
  have hinvPos : 0 < t⁻¹ := inv_pos.mpr ht
  have hlower₀ :=
    Real.log_le_sub_one_of_pos hinvPos
  rw [Real.log_inv] at hlower₀
  have hlower : -(t + t⁻¹) ≤ Real.log t := by
    nlinarith [ht.le]
  exact (abs_le).2 ⟨hlower, hupper⟩

/-- Scale-relative logarithmic inequality.  The only singular term is
`r / t`; all remaining losses are an absolute constant, the fixed
aperture `A`, and `|log r|`. -/
theorem one_add_abs_log_le_scaled_inv
    {r t A : ℝ} (hr : 0 < r) (ht : 0 < t)
    (htA : t ≤ A * r) :
    1 + |Real.log t| ≤
      1 + |Real.log r| + A + r / t := by
  let q : ℝ := t / r
  have hq : 0 < q := div_pos ht hr
  have hqA : q ≤ A := by
    dsimp only [q]
    exact (div_le_iff₀ hr).2 htA
  have hsplit :
      Real.log t = Real.log r + Real.log q := by
    dsimp only [q]
    rw [Real.log_div ht.ne' hr.ne']
    ring
  have hqlog := abs_log_le_self_add_inv hq
  have hqinv : q⁻¹ = r / t := by
    dsimp only [q]
    field_simp [hr.ne', ht.ne']
  rw [hsplit]
  calc
    1 + |Real.log r + Real.log q| ≤
        1 + (|Real.log r| + |Real.log q|) := by
      linarith [abs_add_le (Real.log r) (Real.log q)]
    _ ≤ 1 + |Real.log r| + (q + q⁻¹) := by
      linarith
    _ ≤ 1 + |Real.log r| + A + r / t := by
      rw [hqinv]
      linarith

/-- The inverse norm is controlled by twice the intrinsic half-power
kernel.  The factor two is exactly the comparison
`torusDistSq z ≤ 4 ‖z‖²`. -/
theorem inv_norm_le_two_mul_invSqKerHalf
    {z : T4} (hz : z ≠ 0) :
    ‖z‖⁻¹ ≤ 2 * invSqKerHalf z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hd : 0 < torusDistSq z := by
    have hne : torusDistSq z ≠ 0 := by
      intro hzero
      exact hz ((torusDistSq_eq_zero_iff z).mp hzero)
    exact lt_of_le_of_ne (torusDistSq_nonneg z) hne.symm
  apply (sq_le_sq₀ (inv_nonneg.mpr hn.le)
    (mul_nonneg (by norm_num) (invSqKerHalf_nonneg z))).mp
  have hfrac :
      1 / ‖z‖ ^ 2 ≤ 4 / torusDistSq z := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hn) hd]
    simpa only [one_mul] using
      torusDistSq_le_four_mul_sq_norm z
  rw [mul_pow]
  have hhalfSq :
      invSqKerHalf z ^ 2 = invSqKer z := by
    unfold invSqKerHalf
    rw [← Real.rpow_natCast, ← Real.rpow_mul
      (invSqKer_nonneg z)]
    norm_num
  rw [hhalfSq]
  unfold invSqKer
  norm_num
  simpa only [one_div, inv_pow, div_eq_mul_inv, one_mul] using hfrac

/-- Weighted Young inequality at the exponents used in the local
logarithmic convolution. -/
theorem invSqKer_mul_half_le_threeHalf_add
    (u v : T4) :
    invSqKer u * invSqKerHalf v ≤
      invSqKerThreeHalf u + invSqKerThreeHalf v := by
  let a := invSqKer u
  let b := invSqKer v
  have ha : 0 ≤ a := invSqKer_nonneg u
  have hb : 0 ≤ b := invSqKer_nonneg v
  have hyoung :=
    Real.geom_mean_le_arith_mean2_weighted
      (w₁ := (2 / 3 : ℝ)) (w₂ := (1 / 3 : ℝ))
      (p₁ := a ^ (3 / 2 : ℝ))
      (p₂ := b ^ (3 / 2 : ℝ))
      (by norm_num) (by norm_num)
      (Real.rpow_nonneg ha _)
      (Real.rpow_nonneg hb _)
      (by norm_num)
  have hleft :
      (a ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
          (b ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) =
        a * b ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul ha, ← Real.rpow_mul hb]
    norm_num
  rw [hleft] at hyoung
  unfold invSqKerHalf invSqKerThreeHalf
  dsimp only [a, b] at hyoung ⊢
  have h₁ : 0 ≤ invSqKer u ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (invSqKer_nonneg u) _
  have h₂ : 0 ≤ invSqKer v ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (invSqKer_nonneg v) _
  nlinarith

/-- Near one fixed scale, the critical logarithm is a constant scale-log
plus a single half-power singularity. -/
theorem criticalLogWeight_le_scaled_half
    {r A : ℝ} (hr : 0 < r) (hA : 0 ≤ A)
    (z : T4) (hz : ‖z‖ ≤ A * r) :
    criticalLogWeight z ≤
      1 + |Real.log r| + A +
        2 * r * invSqKerHalf z := by
  by_cases hzero : z = 0
  · subst z
    have hdist :
        torusDistSq (0 : T4) = 0 :=
      (torusDistSq_eq_zero_iff 0).2 rfl
    have hhalf : invSqKerHalf (0 : T4) = 0 := by
      unfold invSqKerHalf invSqKer
      rw [hdist]
      norm_num
    rw [criticalLogWeight, norm_zero, Real.log_zero,
      abs_zero, hhalf, mul_zero]
    linarith [abs_nonneg (Real.log r)]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hzero
    have hbase :=
      one_add_abs_log_le_scaled_inv hr hn hz
    have hinv :=
      inv_norm_le_two_mul_invSqKerHalf hzero
    unfold criticalLogWeight
    calc
      1 + |Real.log ‖z‖| ≤
          1 + |Real.log r| + A + r / ‖z‖ :=
        hbase
      _ ≤ 1 + |Real.log r| + A +
          2 * r * invSqKerHalf z := by
        rw [div_eq_mul_inv]
        have :=
          mul_le_mul_of_nonneg_left hinv hr.le
        linarith

/-- Squared inverse-norm comparison, used when a bounded density rather
than an inverse-square factor is averaged against the logarithm. -/
theorem inv_norm_sq_le_four_mul_invSqKer
    {z : T4} (hz : z ≠ 0) :
    ‖z‖⁻¹ ^ (2 : ℕ) ≤ 4 * invSqKer z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hd : 0 < torusDistSq z := by
    have hne : torusDistSq z ≠ 0 := by
      intro hzero
      exact hz ((torusDistSq_eq_zero_iff z).mp hzero)
    exact lt_of_le_of_ne (torusDistSq_nonneg z) hne.symm
  have hfrac :
      1 / ‖z‖ ^ 2 ≤ 4 / torusDistSq z := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hn) hd]
    simpa only [one_mul] using
      torusDistSq_le_four_mul_sq_norm z
  unfold invSqKer
  simpa only [one_div, inv_pow, div_eq_mul_inv, one_mul] using hfrac

/-- A less singular scale-relative logarithmic inequality, suited to a
bounded density on a scale ball. -/
theorem criticalLogWeight_le_scaled_invSq
    {r A : ℝ} (hr : 0 < r) (hA : 0 ≤ A)
    (z : T4) (hz : ‖z‖ ≤ A * r) :
    criticalLogWeight z ≤
      2 + |Real.log r| + A +
        4 * r ^ 2 * invSqKer z := by
  by_cases hzero : z = 0
  · subst z
    have hdist :
        torusDistSq (0 : T4) = 0 :=
      (torusDistSq_eq_zero_iff 0).2 rfl
    have hker : invSqKer (0 : T4) = 0 := by
      unfold invSqKer
      rw [hdist]
      norm_num
    rw [criticalLogWeight, norm_zero, Real.log_zero,
      abs_zero, hker, mul_zero]
    linarith [abs_nonneg (Real.log r)]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hzero
    have hbase :=
      one_add_abs_log_le_scaled_inv hr hn hz
    let q : ℝ := r * ‖z‖⁻¹
    have hq : 0 ≤ q :=
      mul_nonneg hr.le (inv_nonneg.mpr hn.le)
    have hqSelf : q ≤ 1 + q ^ 2 := by
      nlinarith [sq_nonneg (q - 1 / 2)]
    have hnormSq :=
      inv_norm_sq_le_four_mul_invSqKer hzero
    have hqSq :
        q ^ 2 ≤ 4 * r ^ 2 * invSqKer z := by
      dsimp only [q]
      rw [mul_pow]
      have :=
        mul_le_mul_of_nonneg_left hnormSq
          (sq_nonneg r)
      nlinarith
    unfold criticalLogWeight
    rw [div_eq_mul_inv] at hbase
    calc
      1 + |Real.log ‖z‖| ≤
          1 + |Real.log r| + A + q := hbase
      _ ≤ 2 + |Real.log r| + A + q ^ 2 := by
        linarith
      _ ≤ 2 + |Real.log r| + A +
          4 * r ^ 2 * invSqKer z := by
        linarith

/-- The product torus has diameter at most `π` in its sup norm. -/
theorem norm_t4_le_pi (z : T4) :
    ‖z‖ ≤ Real.pi := by
  rw [pi_norm_le_iff_of_nonneg Real.pi_pos.le]
  intro i
  have h :=
    AddCircle.norm_le_half_period
      (x := z i)
      (p := 2 * Real.pi)
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  rw [abs_of_pos (mul_pos (by norm_num) Real.pi_pos)] at h
  nlinarith

/-- If a torus point stays at least a fixed multiple of `ε` away from
the logarithmic singularity, its critical weight costs only one copy of
`|log ε|`.  The constant depends explicitly on that fixed multiple. -/
theorem criticalLogWeight_le_of_fixedScale
    {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hlog : 1 ≤ |Real.log ε|)
    (z : T4) (hz : a * ε ≤ ‖z‖) :
    criticalLogWeight z ≤
      (5 + |Real.log a|) * |Real.log ε| := by
  have hzpos : 0 < ‖z‖ :=
    (mul_pos ha hε).trans_le hz
  have hlogε :
      |Real.log ε| = -Real.log ε :=
    abs_of_nonpos (Real.log_nonpos hε.le hε1)
  have hlogLower :
      Real.log a + Real.log ε ≤ Real.log ‖z‖ := by
    rw [← Real.log_mul ha.ne' hε.ne']
    exact Real.log_le_log (mul_pos ha hε) hz
  by_cases hz1 : ‖z‖ ≤ 1
  · have hlogz :
        |Real.log ‖z‖| = -Real.log ‖z‖ :=
      abs_of_nonpos
        (Real.log_nonpos hzpos.le hz1)
    unfold criticalLogWeight
    rw [hlogz, hlogε]
    have habsa := neg_le_abs (Real.log a)
    nlinarith [abs_nonneg (Real.log a)]
  · have hzOne : 1 ≤ ‖z‖ := le_of_not_ge hz1
    have hlogzNonneg :
        0 ≤ Real.log ‖z‖ :=
      Real.log_nonneg hzOne
    have hlogzUpper :
        Real.log ‖z‖ ≤ 4 := by
      have hbasic :=
        Real.log_le_sub_one_of_pos hzpos
      have hpi := norm_t4_le_pi z
      linarith [Real.pi_le_four]
    unfold criticalLogWeight
    rw [abs_of_nonneg hlogzNonneg]
    nlinarith [abs_nonneg (Real.log a)]

/-- The critical logarithm has the expected `r⁴(1+|log r|)` mass on
a four-dimensional torus ball, uniformly in its centre. -/
theorem exists_setIntegral_criticalLogWeight_ball_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ (x : T4) (r : ℝ), 0 < r →
        (∫ z in Metric.ball x r,
          criticalLogWeight (x - z) ∂paperMeasure) ≤
            K * r ^ 4 * (3 + |Real.log r|) := by
  obtain ⟨Cvol, hCvol, hvol⟩ :=
    paperMeasure_ball_toReal_le
  obtain ⟨Cker, hCker, hker⟩ :=
    invSqKerBallIntegral_le
  let K : ℝ := Cvol + 4 * Cker + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro x r hr
  let A : ℝ := 3 + |Real.log r|
  let f : T4 → ℝ := fun z =>
    criticalLogWeight (x - z)
  let g : T4 → ℝ := fun z =>
    A + 4 * r ^ 2 * invSqKer (x - z)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hball : MeasurableSet (Metric.ball x r) :=
    measurableSet_ball
  have hg :
      Integrable g paperMeasure := by
    dsimp only [g]
    exact
      (integrable_const A).add
        ((integrable_invSqKer_sub_left x).const_mul
          (4 * r ^ 2))
  have hfMeas :
      AEStronglyMeasurable f
        (paperMeasure.restrict (Metric.ball x r)) :=
    ((measurable_criticalLogWeight.comp
      (measurable_const.sub measurable_id))
      |>.aestronglyMeasurable.restrict)
  have hpoint :
      ∀ z ∈ Metric.ball x r, f z ≤ g z := by
    intro z hz
    have hnorm : ‖x - z‖ ≤ 1 * r := by
      rw [one_mul]
      rw [Metric.mem_ball, dist_eq_norm] at hz
      rw [norm_sub_rev]
      exact hz.le
    have hbound :=
      criticalLogWeight_le_scaled_invSq
        hr zero_le_one (x - z) hnorm
    dsimp only [f, g, A]
    linarith
  have hf :
      IntegrableOn f (Metric.ball x r) paperMeasure := by
    refine Integrable.mono' hg.integrableOn hfMeas ?_
    filter_upwards [ae_restrict_mem hball] with z hz
    rw [Real.norm_eq_abs,
      abs_of_nonneg (criticalLogWeight_nonneg (x - z))]
    exact hpoint z hz
  have hmono :
      (∫ z in Metric.ball x r, f z ∂paperMeasure) ≤
        ∫ z in Metric.ball x r, g z ∂paperMeasure :=
    setIntegral_mono_on hf hg.integrableOn hball hpoint
  have hsplit :
      (∫ z in Metric.ball x r, g z ∂paperMeasure) =
        A * (paperMeasure (Metric.ball x r)).toReal +
          4 * r ^ 2 * invSqKerBallIntegral x r := by
    dsimp only [g]
    rw [integral_add
      (integrableOn_const :
        IntegrableOn (fun _ : T4 => A)
          (Metric.ball x r) paperMeasure)
      ((integrable_invSqKer_sub_left x).const_mul
        (4 * r ^ 2) |>.integrableOn),
      setIntegral_const, integral_const_mul]
    simp only [smul_eq_mul, measureReal_def,
      invSqKerBallIntegral]
    ring
  have hvolBound :
      (paperMeasure (Metric.ball x r)).toReal ≤
        Cvol * r ^ 4 :=
    hvol x r hr
  have hkerBound :
      invSqKerBallIntegral x r ≤ Cker * r ^ 2 :=
    hker x r hr
  rw [hsplit] at hmono
  calc
    (∫ z in Metric.ball x r,
        criticalLogWeight (x - z) ∂paperMeasure) =
        ∫ z in Metric.ball x r, f z ∂paperMeasure := rfl
    _ ≤ A * (paperMeasure (Metric.ball x r)).toReal +
          4 * r ^ 2 * invSqKerBallIntegral x r :=
      hmono
    _ ≤ A * (Cvol * r ^ 4) +
          4 * r ^ 2 * (Cker * r ^ 2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hvolBound hA)
        (mul_le_mul_of_nonneg_left hkerBound
          (by positivity))
    _ ≤ K * r ^ 4 * A := by
      have hAone : 1 ≤ A := by
        dsimp only [A]
        linarith [abs_nonneg (Real.log r)]
      have hr4 : 0 ≤ r ^ 4 := by positivity
      have hsecond :
          4 * r ^ 2 * (Cker * r ^ 2) ≤
            4 * Cker * r ^ 4 * A := by
        rw [show
          4 * r ^ 2 * (Cker * r ^ 2) =
            4 * Cker * r ^ 4 by ring]
        exact le_mul_of_one_le_right
          (mul_nonneg
            (mul_nonneg (by norm_num) hCker.le) hr4)
          hAone
      calc
        A * (Cvol * r ^ 4) +
              4 * r ^ 2 * (Cker * r ^ 2) ≤
            A * (Cvol * r ^ 4) +
              4 * Cker * r ^ 4 * A :=
          by
            linarith
        _ ≤ K * r ^ 4 * A := by
          dsimp only [K]
          nlinarith [mul_nonneg hr4 hA]
    _ = K * r ^ 4 * (3 + |Real.log r|) := by
      rfl


end

end Anderson4D
