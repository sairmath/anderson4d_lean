import Anderson4D.DetParametrix.Paper41_Renorm.R322ApproxIdentity

/-!
# The truncated Taylor profile in the R-322 collapse

After the class-`E` cancellation in region (4.10), the primitive block is
weighted by the squared increment and integrated only over
`2‖u‖ ≤ ‖q‖`.  This file proves the two pointwise profiles used by the
outer integral:

* on `torusDistSq q ≤ ε²`, a flat `ε⁻⁴ / |log ε|` bound;
* on `ε² ≤ torusDistSq q`, a critical
  `invSqKer q ^ 2 / |log ε|` bound.

Both are consequences of the explicit Proposition 4.1 majorant, not
additional reduction hypotheses.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set

/-- The radial moment remaining after Taylor cancellation in (4.10). -/
def r322TaylorMoment
    (C lam ε supportConstant : ℝ) (n : ℕ) (q : T4) : ℝ :=
  ∫ u,
    reductionRegionOneKernel q
      (primitiveKernelMajorant C lam ε supportConstant n) u *
      torusDistSq u
    ∂paperMeasure

/-- The outer density after inserting the Hessian singularity. -/
def r322TaylorDensity
    (C lam ε supportConstant : ℝ) (n : ℕ) (q : T4) : ℝ :=
  invSqKer q ^ 2 *
    r322TaylorMoment C lam ε supportConstant n q

theorem measurable_primitiveKernelMajorant
    (C lam ε supportConstant : ℝ) (n : ℕ) :
    Measurable
      (primitiveKernelMajorant C lam ε supportConstant n) := by
  unfold primitiveKernelMajorant primitiveSupportIndicator
  exact measurable_const.mul
    (((measurable_const.mul measurable_invSqKer).mul
        (Measurable.ite
          (measurableSet_le measurable_torusDistSq measurable_const)
          measurable_const measurable_const)).add
      (measurable_const.mul
        ((measurable_torusDistSq.add measurable_const).inv.pow_const 3)))

theorem measurable_r322TaylorMoment
    (C lam ε supportConstant : ℝ) (n : ℕ) :
    Measurable
      (r322TaylorMoment C lam ε supportConstant n) := by
  unfold r322TaylorMoment
  rw [paperMeasure_eq_volume]
  have hjoint :
      Measurable fun p : T4 × T4 =>
        reductionRegionOneKernel p.1
          (primitiveKernelMajorant C lam ε supportConstant n) p.2 *
          torusDistSq p.2 := by
    unfold reductionRegionOneKernel
    exact
      (Measurable.ite
        (measurableSet_le
          (measurable_const.mul measurable_snd.norm)
          measurable_fst.norm)
        ((measurable_primitiveKernelMajorant
          C lam ε supportConstant n).comp measurable_snd)
        measurable_const).mul
      (measurable_torusDistSq.comp measurable_snd)
  exact hjoint.stronglyMeasurable.integral_prod_right.measurable

theorem measurable_r322TaylorDensity
    (C lam ε supportConstant : ℝ) (n : ℕ) :
    Measurable
      (r322TaylorDensity C lam ε supportConstant n) := by
  unfold r322TaylorDensity
  exact (measurable_invSqKer.pow_const 2).mul
    (measurable_r322TaylorMoment C lam ε supportConstant n)

theorem r322TaylorMoment_nonneg
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (ε supportConstant : ℝ) (n : ℕ) (q : T4) :
    0 ≤ r322TaylorMoment C lam ε supportConstant n q := by
  unfold r322TaylorMoment
  exact integral_nonneg fun u =>
    mul_nonneg
      (by
        unfold reductionRegionOneKernel
        split_ifs
        · exact primitiveKernelMajorant_nonneg hC hlam
        · exact le_rfl)
      (torusDistSq_nonneg u)

theorem r322TaylorDensity_nonneg
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (ε supportConstant : ℝ) (n : ℕ) (q : T4) :
    0 ≤ r322TaylorDensity C lam ε supportConstant n q :=
  mul_nonneg (sq_nonneg (invSqKer q))
    (r322TaylorMoment_nonneg hC hlam ε supportConstant n q)

theorem torusDistSq_mul_invSqKer_le_one (z : T4) :
    torusDistSq z * invSqKer z ≤ 1 := by
  unfold invSqKer
  rcases (torusDistSq_nonneg z).eq_or_lt with hz | hz
  · rw [← hz]
    simp
  · field_simp [hz.ne']
    norm_num

@[simp]
theorem invSqKer_zero_r322 :
    invSqKer (0 : T4) = 0 := by
  unfold invSqKer
  rw [(torusDistSq_eq_zero_iff (0 : T4)).mpr rfl]
  simp

theorem invSqKer_sq_mul_norm_four_le_one (z : T4) :
    invSqKer z ^ 2 * ‖z‖ ^ 4 ≤ 1 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · have hd : 0 < torusDistSq z := by
      have hne : torusDistSq z ≠ 0 := by
        intro hzero
        exact hz ((torusDistSq_eq_zero_iff z).mp hzero)
      exact lt_of_le_of_ne (torusDistSq_nonneg z) hne.symm
    have hnorm :
        ‖z‖ ^ 4 ≤ torusDistSq z ^ 2 := by
      nlinarith [sq_norm_le_torusDistSq z,
        norm_nonneg z, torusDistSq_nonneg z]
    unfold invSqKer
    rw [show (torusDistSq z)⁻¹ ^ 2 =
        1 / torusDistSq z ^ 2 by
          rw [one_div, inv_pow]]
    rw [div_mul_eq_mul_div, div_le_one (sq_pos_of_pos hd)]
    simpa only [one_mul] using hnorm

theorem torusDistSq_le_of_reductionRegion_one
    {q u : T4} (hregion : 2 * ‖u‖ ≤ ‖q‖) :
    torusDistSq u ≤ torusDistSq q := by
  calc
    torusDistSq u ≤ 4 * ‖u‖ ^ 2 :=
      torusDistSq_le_four_mul_sq_norm u
    _ ≤ ‖q‖ ^ 2 := by
      nlinarith [norm_nonneg u, norm_nonneg q]
    _ ≤ torusDistSq q := sq_norm_le_torusDistSq q

theorem primitiveKernelMajorant_nonneg_even
    (C lam ε supportConstant : ℝ) (n : ℕ) (z : T4) :
    0 ≤ primitiveKernelMajorant C lam ε supportConstant n z := by
  unfold primitiveKernelMajorant
  exact mul_nonneg ((even_two_mul n).pow_nonneg (C * lam))
    (add_nonneg
      (mul_nonneg
        (mul_nonneg
          (div_nonneg
            ((show Even (4 : ℕ) by norm_num).pow_nonneg ε⁻¹)
            (abs_nonneg _))
          (invSqKer_nonneg z))
        (primitiveSupportIndicator_nonneg supportConstant ε z))
      (mul_nonneg
        (div_nonneg zero_le_one (sq_nonneg _))
        (pow_nonneg
          (inv_nonneg.mpr
            (add_nonneg (torusDistSq_nonneg z) (sq_nonneg ε))) 3)))

theorem integrable_weighted_primitiveKernelMajorant
    {C lam ε supportConstant : ℝ} {n : ℕ}
    (hsupport : 0 < supportConstant) (hε : 0 < ε) :
    Integrable
      (fun u : T4 =>
        primitiveKernelMajorant C lam ε supportConstant n u *
          torusDistSq u)
      paperMeasure := by
  let L : ℝ := |Real.log ε|
  let A : ℝ := (C * lam) ^ (2 * n)
  let a : ℝ := ε⁻¹ ^ 4 / L
  let b : ℝ := 1 / L ^ 2
  have hlocal :=
    integrable_r322LocalMoment hsupport hε
  have hreg := integrable_r322RegularizedMoment hε
  have heq :
      (fun u : T4 =>
        primitiveKernelMajorant C lam ε supportConstant n u *
          torusDistSq u) =
        fun u =>
          A * (a * r322LocalMoment supportConstant ε u +
            b * r322RegularizedMoment ε u) := by
    funext u
    unfold primitiveKernelMajorant r322LocalMoment
      r322RegularizedMoment
    dsimp only [A, a, b, L]
    ring
  rw [heq]
  exact
    ((hlocal.const_mul a).add (hreg.const_mul b)).const_mul A

theorem integrable_r322TaylorMoment_integrand
    {C lam ε supportConstant : ℝ} {n : ℕ}
    {q : T4} (hsupport : 0 < supportConstant)
    (hε : 0 < ε) :
    Integrable
      (fun u =>
        reductionRegionOneKernel q
          (primitiveKernelMajorant C lam ε supportConstant n) u *
          torusDistSq u)
      paperMeasure := by
  let R : Set T4 := {u | 2 * ‖u‖ ≤ ‖q‖}
  have hR : MeasurableSet R :=
    measurableSet_le
      (measurable_const.mul measurable_norm) measurable_const
  have heq :
      (fun u =>
        reductionRegionOneKernel q
          (primitiveKernelMajorant C lam ε supportConstant n) u *
          torusDistSq u) =
        R.indicator
          (fun u =>
            primitiveKernelMajorant C lam ε supportConstant n u *
              torusDistSq u) := by
    funext u
    unfold reductionRegionOneKernel
    by_cases hu : 2 * ‖u‖ ≤ ‖q‖ <;>
      simp [R, hu]
  rw [heq]
  exact
    (integrable_weighted_primitiveKernelMajorant hsupport hε).indicator hR

theorem r322TaylorRegion_subset_ball
    {q : T4} (hq : q ≠ 0) :
    {u : T4 | 2 * ‖u‖ ≤ ‖q‖} ⊆
      Metric.ball (0 : T4) ‖q‖ := by
  intro u hu
  rw [Metric.mem_ball, dist_zero_right]
  change 2 * ‖u‖ ≤ ‖q‖ at hu
  have hqnorm : 0 < ‖q‖ := norm_pos_iff.mpr hq
  nlinarith [norm_nonneg u]

/-- Inner-scale part of the Taylor density. -/
theorem exists_r322TaylorDensity_inner_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C lam ε supportConstant : ℝ) (n : ℕ) (q : T4),
        0 ≤ C → 0 ≤ lam → 0 < ε → 0 < supportConstant →
        1 ≤ |Real.log ε| → q ≠ 0 →
        torusDistSq q ≤ ε ^ 2 →
        r322TaylorDensity C lam ε supportConstant n q ≤
          (C * lam) ^ (2 * n) * K *
            (ε⁻¹ ^ (4 : ℕ) / |Real.log ε|) := by
  obtain ⟨Cvol, hCvol, hvol⟩ :=
    paperMeasure_ball_toReal_le
  let K : ℝ := 2 * Cvol + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro C lam ε supportConstant n q hC hlam hε hsupport hlog hq hqε
  let L : ℝ := |Real.log ε|
  let A : ℝ := (C * lam) ^ (2 * n)
  let R : Set T4 := {u | 2 * ‖u‖ ≤ ‖q‖}
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hlog
  have hA : 0 ≤ A := pow_nonneg (mul_nonneg hC hlam) _
  have hR : MeasurableSet R := by
    exact measurableSet_le
      (measurable_const.mul measurable_norm) measurable_const
  have hpoint :
      ∀ u ∈ R,
        primitiveKernelMajorant C lam ε supportConstant n u *
            torusDistSq u ≤
          A * (2 * (ε⁻¹ ^ (4 : ℕ) / L)) := by
    intro u hu
    have huDist :
        torusDistSq u ≤ torusDistSq q :=
      torusDistSq_le_of_reductionRegion_one hu
    have hlocal :
        r322LocalMoment supportConstant ε u ≤ 1 := by
      unfold r322LocalMoment
      calc
        torusDistSq u * invSqKer u *
              primitiveSupportIndicator supportConstant ε u ≤
            1 * primitiveSupportIndicator supportConstant ε u := by
          exact mul_le_mul_of_nonneg_right
            (torusDistSq_mul_invSqKer_le_one u)
            (primitiveSupportIndicator_nonneg
              supportConstant ε u)
        _ ≤ 1 := by
          unfold primitiveSupportIndicator
          split_ifs <;> norm_num
    have hreg :
        r322RegularizedMoment ε u ≤
          torusDistSq q * ε⁻¹ ^ (6 : ℕ) := by
      unfold r322RegularizedMoment
      have hinv :
          (torusDistSq u + ε ^ 2)⁻¹ ≤
            (ε ^ 2)⁻¹ :=
        inv_anti₀ (sq_pos_of_pos hε)
          (le_add_of_nonneg_left (torusDistSq_nonneg u))
      calc
        torusDistSq u *
              (torusDistSq u + ε ^ 2)⁻¹ ^ 3 ≤
            torusDistSq u * (ε ^ 2)⁻¹ ^ 3 := by
          apply mul_le_mul_of_nonneg_left _ (torusDistSq_nonneg u)
          exact pow_le_pow_left₀
            (inv_nonneg.mpr
              (add_nonneg (torusDistSq_nonneg u)
                (sq_nonneg ε)))
            hinv 3
        _ ≤ torusDistSq q * (ε ^ 2)⁻¹ ^ 3 :=
          mul_le_mul_of_nonneg_right huDist
            (pow_nonneg (inv_nonneg.mpr (sq_nonneg ε)) 3)
        _ = torusDistSq q * ε⁻¹ ^ (6 : ℕ) := by
          rw [inv_pow, ← pow_mul]
          norm_num
    have hregScale :
        (1 / L ^ 2) *
            (torusDistSq q * ε⁻¹ ^ (6 : ℕ)) ≤
          ε⁻¹ ^ (4 : ℕ) / L := by
      rw [div_eq_mul_inv]
      field_simp [hε.ne', hL.ne']
      nlinarith
    rw [show
      primitiveKernelMajorant C lam ε supportConstant n u *
            torusDistSq u =
        A * ((ε⁻¹ ^ 4 / L) *
              r322LocalMoment supportConstant ε u +
            (1 / L ^ 2) * r322RegularizedMoment ε u) by
      unfold primitiveKernelMajorant r322LocalMoment
        r322RegularizedMoment
      dsimp only [A, L]
      ring]
    change A * _ ≤ A * _
    apply mul_le_mul_of_nonneg_left _ hA
    calc
      (ε⁻¹ ^ 4 / L) *
            r322LocalMoment supportConstant ε u +
          (1 / L ^ 2) * r322RegularizedMoment ε u ≤
          (ε⁻¹ ^ 4 / L) * 1 +
            (1 / L ^ 2) *
              (torusDistSq q * ε⁻¹ ^ 6) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hlocal (by positivity))
          (mul_le_mul_of_nonneg_left hreg (by positivity))
      _ ≤ ε⁻¹ ^ 4 / L + ε⁻¹ ^ 4 / L := by
        simpa only [mul_one] using
          (add_le_add (le_refl (ε⁻¹ ^ 4 / L)) hregScale)
      _ = 2 * (ε⁻¹ ^ 4 / L) := by ring
  have hmoment :
      r322TaylorMoment C lam ε supportConstant n q ≤
        A * (2 * (ε⁻¹ ^ (4 : ℕ) / L)) *
          (paperMeasure (Metric.ball (0 : T4) ‖q‖)).toReal := by
    let B : Set T4 := Metric.ball (0 : T4) ‖q‖
    have hB : MeasurableSet B := measurableSet_ball
    have hconst :
        IntegrableOn
          (fun _u : T4 =>
            A * (2 * (ε⁻¹ ^ (4 : ℕ) / L)))
          R paperMeasure :=
      integrableOn_const
    have hrestricted :
        IntegrableOn
          (fun u : T4 =>
            primitiveKernelMajorant C lam ε supportConstant n u *
              torusDistSq u)
          R paperMeasure := by
      exact
        (integrable_weighted_primitiveKernelMajorant
          hsupport hε).integrableOn
    unfold r322TaylorMoment reductionRegionOneKernel
    rw [show
      (fun u : T4 =>
        (if 2 * ‖u‖ ≤ ‖q‖ then
          primitiveKernelMajorant C lam ε supportConstant n u else 0) *
            torusDistSq u) =
        R.indicator
          (fun u =>
            primitiveKernelMajorant C lam ε supportConstant n u *
              torusDistSq u) by
      funext u
      by_cases hu : 2 * ‖u‖ ≤ ‖q‖ <;>
        simp [R, hu]]
    rw [integral_indicator hR]
    calc
      (∫ u in R,
          primitiveKernelMajorant C lam ε supportConstant n u *
            torusDistSq u ∂paperMeasure) ≤
          ∫ _u in R,
            A * (2 * (ε⁻¹ ^ (4 : ℕ) / L))
              ∂paperMeasure :=
        setIntegral_mono_on hrestricted hconst hR hpoint
      _ = A * (2 * (ε⁻¹ ^ (4 : ℕ) / L)) *
          (paperMeasure R).toReal := by
        rw [setIntegral_const]
        simp only [smul_eq_mul, measureReal_def]
        ring
      _ ≤ A * (2 * (ε⁻¹ ^ (4 : ℕ) / L)) *
          (paperMeasure B).toReal := by
        apply mul_le_mul_of_nonneg_left
          (measureReal_mono (r322TaylorRegion_subset_ball hq))
        positivity
  have hvolume :
      (paperMeasure (Metric.ball (0 : T4) ‖q‖)).toReal ≤
        Cvol * ‖q‖ ^ 4 :=
    hvol 0 ‖q‖ (norm_pos_iff.mpr hq)
  unfold r322TaylorDensity
  have hcancel :
      invSqKer q ^ 2 *
          (A * (2 * (ε⁻¹ ^ (4 : ℕ) / L)) *
            (Cvol * ‖q‖ ^ 4)) ≤
        A * (2 * Cvol) *
          (ε⁻¹ ^ (4 : ℕ) / L) := by
    calc
      invSqKer q ^ 2 *
            (A * (2 * (ε⁻¹ ^ (4 : ℕ) / L)) *
              (Cvol * ‖q‖ ^ 4)) =
          (A * (2 * Cvol) *
            (ε⁻¹ ^ (4 : ℕ) / L)) *
              (invSqKer q ^ 2 * ‖q‖ ^ 4) := by ring
      _ ≤ (A * (2 * Cvol) *
            (ε⁻¹ ^ (4 : ℕ) / L)) * 1 := by
        apply mul_le_mul_of_nonneg_left
          (invSqKer_sq_mul_norm_four_le_one q)
        positivity
      _ = A * (2 * Cvol) *
            (ε⁻¹ ^ (4 : ℕ) / L) := by ring
  calc
    invSqKer q ^ 2 *
        r322TaylorMoment C lam ε supportConstant n q ≤
        invSqKer q ^ 2 *
          (A * (2 * (ε⁻¹ ^ (4 : ℕ) / L)) *
            (paperMeasure
              (Metric.ball (0 : T4) ‖q‖)).toReal) :=
      mul_le_mul_of_nonneg_left hmoment (sq_nonneg _)
    _ ≤ invSqKer q ^ 2 *
          (A * (2 * (ε⁻¹ ^ (4 : ℕ) / L)) *
            (Cvol * ‖q‖ ^ 4)) := by
      gcongr
    _ ≤ A * (2 * Cvol) *
          (ε⁻¹ ^ (4 : ℕ) / L) := hcancel
    _ ≤ (C * lam) ^ (2 * n) * K *
          (ε⁻¹ ^ (4 : ℕ) / |Real.log ε|) := by
      dsimp only [A, K, L]
      gcongr
      linarith

/-- Outer-scale part of the Taylor density, retaining the critical inverse
logarithm. -/
theorem exists_r322TaylorDensity_outer_le
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C lam ε : ℝ) (n : ℕ) (q : T4),
        0 ≤ C → 0 ≤ lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| →
        r322TaylorDensity C lam ε supportConstant n q ≤
          (C * lam) ^ (2 * n) * K *
            ((1 / |Real.log ε|) * invSqKer q ^ 2) := by
  obtain ⟨K, hK, hmoment⟩ :=
    exists_primitiveKernelMajorant_moment_bound_div_log hsupport
  refine ⟨K, hK, ?_⟩
  intro C lam ε n q hC hlam hε hε1 hlog
  obtain ⟨hfullInt, hfull⟩ :=
    hmoment C lam ε n hC hlam hε hε1 hlog
  have htrunc :
      r322TaylorMoment C lam ε supportConstant n q ≤
        ∫ u, torusDistSq u *
          primitiveKernelMajorant C lam ε supportConstant n u
            ∂paperMeasure := by
    unfold r322TaylorMoment
    have htruncInt :=
      integrable_r322TaylorMoment_integrand
        (C := C) (lam := lam) (n := n)
        (q := q) hsupport hε
    exact integral_mono htruncInt hfullInt fun u => by
      unfold reductionRegionOneKernel
      split_ifs
      · rw [mul_comm]
      · simp only [zero_mul]
        exact mul_nonneg (torusDistSq_nonneg u)
          (primitiveKernelMajorant_nonneg_even
            C lam ε supportConstant n u)
  unfold r322TaylorDensity
  calc
    invSqKer q ^ 2 *
        r322TaylorMoment C lam ε supportConstant n q ≤
        invSqKer q ^ 2 *
          (∫ u, torusDistSq u *
            primitiveKernelMajorant C lam ε supportConstant n u
              ∂paperMeasure) :=
      mul_le_mul_of_nonneg_left htrunc (sq_nonneg _)
    _ ≤ invSqKer q ^ 2 *
          ((C * lam) ^ (2 * n) *
            (K / |Real.log ε|)) :=
      mul_le_mul_of_nonneg_left hfull (sq_nonneg _)
    _ = (C * lam) ^ (2 * n) * K *
          ((1 / |Real.log ε|) * invSqKer q ^ 2) := by
      ring

/-- The complete Taylor-region outer integral preserves the inverse-square
majorant.  This is the analytic content of paper (4.10) after class-`E`
cancellation: neither a cutoff power nor an extra logarithm is lost. -/
theorem exists_r322TaylorDensity_convolution_le
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C lam ε : ℝ) (n : ℕ) (x : T4),
        0 ≤ C → 0 ≤ lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| → x ≠ 0 →
        (∫ q,
          invSqKer (x - q) *
            r322TaylorDensity C lam ε supportConstant n q
          ∂paperMeasure) ≤
          (C * lam) ^ (2 * n) * K * invSqKer x := by
  obtain ⟨Kinner, hKinner, hinner⟩ :=
    exists_r322TaylorDensity_inner_le
  obtain ⟨Kouter, hKouter, houter⟩ :=
    exists_r322TaylorDensity_outer_le hsupport
  obtain ⟨Kscale, hKscale, hscale⟩ :=
    exists_r322ScaleBall_convolution_le
      (supportConstant := 1) zero_lt_one
  obtain ⟨Kcritical, hKcritical, hcritical⟩ :=
    exists_r322CriticalAnnulus_convolution_le
  let K : ℝ :=
    Kinner * Kscale + Kouter * Kcritical
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro C lam ε n x hC hlam hε hε1 hlog hx
  let L : ℝ := |Real.log ε|
  let A : ℝ := (C * lam) ^ (2 * n)
  let Sin : Set T4 := r322ScaleBall 1 ε
  let Sout : Set T4 := r322CriticalAnnulus ε
  let f : T4 → ℝ := fun q =>
    invSqKer (x - q) *
      r322TaylorDensity C lam ε supportConstant n q
  let g₁ : T4 → ℝ := fun q =>
    Sin.indicator
      (fun z =>
        (A * Kinner * (ε⁻¹ ^ (4 : ℕ) / L)) *
          invSqKer (x - z)) q
  let g₂ : T4 → ℝ := fun q =>
    Sout.indicator
      (fun z =>
        (A * Kouter) *
          ((1 / L) *
            (invSqKer (x - z) * invSqKer z ^ 2))) q
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hlog
  have hA : 0 ≤ A := pow_nonneg (mul_nonneg hC hlam) _
  have hSin : MeasurableSet Sin :=
    measurableSet_r322ScaleBall 1 ε
  have hSout : MeasurableSet Sout :=
    measurableSet_r322CriticalAnnulus ε
  have hg₁ : Integrable g₁ paperMeasure := by
    dsimp only [g₁]
    exact
      ((integrable_invSqKer_sub_left x).const_mul
        (A * Kinner * (ε⁻¹ ^ (4 : ℕ) / L))).indicator hSin
  have hg₂ : Integrable g₂ paperMeasure := by
    dsimp only [g₂]
    have hg₂On :
        IntegrableOn
          (fun z : T4 =>
            (A * Kouter) *
              ((1 / L) *
                (invSqKer (x - z) * invSqKer z ^ 2)))
          Sout paperMeasure :=
      ((integrableOn_r322Critical_product hε x).const_mul
        (1 / L)).const_mul (A * Kouter)
    exact hg₂On.integrable_indicator hSout
  have hpoint : ∀ q, f q ≤ g₁ q + g₂ q := by
    intro q
    by_cases hqin : torusDistSq q ≤ ε ^ 2
    · have hmem : q ∈ Sin := by
        change torusDistSq q ≤ (1 * ε) ^ 2
        simpa only [one_mul] using hqin
      rw [show g₁ q =
          (A * Kinner * (ε⁻¹ ^ (4 : ℕ) / L)) *
            invSqKer (x - q) by
        simp [g₁, hmem]]
      by_cases hq : q = 0
      · subst q
        unfold f r322TaylorDensity
        rw [invSqKer_zero_r322,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0),
          zero_mul, mul_zero]
        have hg₂0 : 0 ≤ g₂ 0 := by
          dsimp only [g₂]
          apply Set.indicator_nonneg
          intro z _
          exact mul_nonneg
            (mul_nonneg hA hKouter.le)
            (mul_nonneg (by positivity)
              (mul_nonneg
                (invSqKer_nonneg _)
                (sq_nonneg _)))
        exact add_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg hA hKinner.le)
              (by positivity))
            (by simpa only [sub_zero] using invSqKer_nonneg x))
          hg₂0
      · have hdensity :=
          hinner C lam ε supportConstant n q
            hC hlam hε hsupport hlog hq hqin
        unfold f
        have hmul :
            invSqKer (x - q) *
                r322TaylorDensity C lam ε supportConstant n q ≤
              invSqKer (x - q) *
                (A * Kinner *
                  (ε⁻¹ ^ (4 : ℕ) / L)) :=
          mul_le_mul_of_nonneg_left hdensity
            (invSqKer_nonneg (x - q))
        exact le_add_of_le_of_nonneg
          (by
            calc
              invSqKer (x - q) *
                    r322TaylorDensity C lam ε
                      supportConstant n q ≤
                  invSqKer (x - q) *
                    (A * Kinner *
                      (ε⁻¹ ^ (4 : ℕ) / L)) := hmul
              _ = (A * Kinner *
                    (ε⁻¹ ^ (4 : ℕ) / L)) *
                  invSqKer (x - q) := by ring)
          (Set.indicator_nonneg
            (fun _ _ =>
              mul_nonneg
                (mul_nonneg hA hKouter.le)
                (mul_nonneg (by positivity)
                  (mul_nonneg
                    (invSqKer_nonneg _)
                    (sq_nonneg _)))) q)
    · have hqout : ε ^ 2 ≤ torusDistSq q :=
        le_of_not_ge hqin
      have hmem : q ∈ Sout := hqout
      rw [show g₂ q =
          (A * Kouter) *
            ((1 / L) *
              (invSqKer (x - q) * invSqKer q ^ 2)) by
        simp [g₂, hmem]]
      have hdensity :=
        houter C lam ε n q hC hlam hε hε1 hlog
      unfold f
      have hmul :
          invSqKer (x - q) *
              r322TaylorDensity C lam ε supportConstant n q ≤
            invSqKer (x - q) *
              (A * Kouter *
                ((1 / L) * invSqKer q ^ 2)) :=
        mul_le_mul_of_nonneg_left hdensity
          (invSqKer_nonneg (x - q))
      exact le_add_of_nonneg_of_le
        (Set.indicator_nonneg
          (fun _ _ =>
            mul_nonneg
              (mul_nonneg
                (mul_nonneg hA hKinner.le)
                (by positivity))
              (invSqKer_nonneg _)) q)
        (hmul.trans_eq (by ring))
  have hf : Integrable f paperMeasure := by
    apply (hg₁.add hg₂).mono'
      (((measurable_invSqKer.comp
          (measurable_const.sub measurable_id)).mul
        (measurable_r322TaylorDensity
          C lam ε supportConstant n)).aestronglyMeasurable)
    filter_upwards with q
    change
      |invSqKer (x - q) *
          r322TaylorDensity C lam ε supportConstant n q| ≤
        g₁ q + g₂ q
    rw [abs_of_nonneg
        (mul_nonneg (invSqKer_nonneg (x - q))
          (r322TaylorDensity_nonneg hC hlam
            ε supportConstant n q))]
    exact hpoint q
  have hg₁Int :
      (∫ q, g₁ q ∂paperMeasure) ≤
        A * Kinner * Kscale * invSqKer x := by
    have hs :=
      hscale ε x hε hx
    dsimp only [g₁]
    rw [integral_indicator hSin, integral_const_mul]
    calc
      (A * Kinner * (ε⁻¹ ^ (4 : ℕ) / L)) *
            ∫ q in Sin, invSqKer (x - q) ∂paperMeasure =
          (A * Kinner / L) *
            (ε⁻¹ ^ (4 : ℕ) *
              ∫ q in Sin, invSqKer (x - q) ∂paperMeasure) := by
        ring
      _ ≤ (A * Kinner / L) *
            (Kscale * invSqKer x) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [Sin] using hs)
          (by positivity)
      _ ≤ (A * Kinner) *
            (Kscale * invSqKer x) := by
        apply mul_le_mul_of_nonneg_right _
          (mul_nonneg hKscale.le (invSqKer_nonneg x))
        simpa only [L] using
          (div_le_self
            (mul_nonneg hA hKinner.le) hlog)
      _ = A * Kinner * Kscale * invSqKer x := by ring
  have hg₂Int :
      (∫ q, g₂ q ∂paperMeasure) ≤
        A * Kouter * Kcritical * invSqKer x := by
    have hc :=
      hcritical ε x hε hε1 hlog hx
    dsimp only [g₂]
    rw [integral_indicator hSout, integral_const_mul,
      integral_const_mul]
    calc
      A * Kouter *
            ((1 / L) *
              ∫ q in Sout,
                invSqKer (x - q) * invSqKer q ^ 2
                  ∂paperMeasure) ≤
          A * Kouter * (Kcritical * invSqKer x) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [L, Sout] using hc)
          (mul_nonneg hA hKouter.le)
      _ = A * Kouter * Kcritical * invSqKer x := by ring
  calc
    (∫ q, f q ∂paperMeasure) ≤
        ∫ q, g₁ q + g₂ q ∂paperMeasure :=
      integral_mono hf (hg₁.add hg₂) hpoint
    _ = (∫ q, g₁ q ∂paperMeasure) +
          ∫ q, g₂ q ∂paperMeasure :=
      integral_add hg₁ hg₂
    _ ≤ A * Kinner * Kscale * invSqKer x +
        A * Kouter * Kcritical * invSqKer x :=
      add_le_add hg₁Int hg₂Int
    _ = (C * lam) ^ (2 * n) * K * invSqKer x := by
      dsimp only [A, K]
      ring

end

end Anderson4D
