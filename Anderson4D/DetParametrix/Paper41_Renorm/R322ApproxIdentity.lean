import Anderson4D.DetParametrix.Paper41_Renorm.R322MajorantMoment
import Anderson4D.Continuum.CellSingular

/-!
# Approximate-identity estimates for the R-322 collapse

The Taylor region in paper (4.10) leaves two radial kernels in the outer
variable.  The first is the normalized indicator of a ball of radius
`O(ε)`.  This file proves directly that convolution with this kernel
preserves the inverse-square Green majorant.  The critical annular kernel
is treated below by the same near/far decomposition.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set

/-- The closed torus ball at the primitive support scale. -/
def r322ScaleBall (supportConstant ε : ℝ) : Set T4 :=
  {z | torusDistSq z ≤ (supportConstant * ε) ^ 2}

theorem measurableSet_r322ScaleBall
    (supportConstant ε : ℝ) :
    MeasurableSet (r322ScaleBall supportConstant ε) :=
  measurable_torusDistSq measurableSet_Iic

theorem r322ScaleBall_subset_metricBall
    {supportConstant ε : ℝ}
    (hsupport : 0 < supportConstant) (hε : 0 < ε) :
    r322ScaleBall supportConstant ε ⊆
      Metric.ball (0 : T4) (2 * (supportConstant * ε)) := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right]
  have hr : 0 < supportConstant * ε :=
    mul_pos hsupport hε
  have hsq :
      ‖z‖ ^ 2 ≤ (supportConstant * ε) ^ 2 :=
    (sq_norm_le_torusDistSq z).trans hz
  have hnorm : ‖z‖ ≤ supportConstant * ε := by
    nlinarith [norm_nonneg z]
  linarith

/-- The normalized `ε`-ball is an approximate identity for the
inverse-square kernel.  The constant is chosen before `ε` and the external
point; dependence on the fixed primitive support radius is explicit in
the choice of `K`. -/
theorem exists_r322ScaleBall_convolution_le
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ε : ℝ) (x : T4),
        0 < ε → x ≠ 0 →
        ε⁻¹ ^ (4 : ℕ) *
            (∫ z in r322ScaleBall supportConstant ε,
              invSqKer (x - z) ∂paperMeasure) ≤
          K * invSqKer x := by
  obtain ⟨Cker, hCker, hker⟩ := invSqKerBallIntegral_le
  obtain ⟨Cvol, hCvol, hvol⟩ := paperMeasure_ball_toReal_le
  let K : ℝ :=
    (2304 * Cker + 128 * Cvol) * supportConstant ^ 4 + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro ε x hε hx
  let r : ℝ := supportConstant * ε
  let S : Set T4 := r322ScaleBall supportConstant ε
  have hr : 0 < r := mul_pos hsupport hε
  have hS : MeasurableSet S :=
    measurableSet_r322ScaleBall supportConstant ε
  have hxDist : 0 < torusDistSq x := by
    have hne : torusDistSq x ≠ 0 := by
      intro hzero
      exact hx ((torusDistSq_eq_zero_iff x).mp hzero)
    exact lt_of_le_of_ne (torusDistSq_nonneg x) hne.symm
  by_cases hnear : ‖x‖ ≤ 4 * r
  · have hsubset :
        S ⊆ Metric.ball x (6 * r) := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm]
      have hzsq : ‖z‖ ^ 2 ≤ r ^ 2 :=
        (sq_norm_le_torusDistSq z).trans hz
      have hznorm : ‖z‖ ≤ r := by
        nlinarith [norm_nonneg z]
      calc
        ‖z - x‖ ≤ ‖z‖ + ‖x‖ := norm_sub_le _ _
        _ ≤ r + 4 * r := by linarith
        _ < 6 * r := by linarith
    have hint :
        IntegrableOn (fun z : T4 => invSqKer (x - z))
          S paperMeasure :=
      (integrable_invSqKer_sub_left x).integrableOn
    have hlocal :
        (∫ z in S, invSqKer (x - z) ∂paperMeasure) ≤
          Cker * (6 * r) ^ 2 := by
      calc
        (∫ z in S, invSqKer (x - z) ∂paperMeasure) ≤
            ∫ z in Metric.ball x (6 * r),
              invSqKer (x - z) ∂paperMeasure := by
          exact setIntegral_mono_set
            (integrable_invSqKer_sub_left x).integrableOn
            (.of_forall fun z => invSqKer_nonneg (x - z))
            (.of_forall hsubset)
        _ = invSqKerBallIntegral x (6 * r) := rfl
        _ ≤ Cker * (6 * r) ^ 2 := hker x (6 * r) (by positivity)
    have hxUpper : torusDistSq x ≤ 64 * r ^ 2 := by
      calc
        torusDistSq x ≤ 4 * ‖x‖ ^ 2 :=
          torusDistSq_le_four_mul_sq_norm x
        _ ≤ 4 * (4 * r) ^ 2 := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg x) hnear 2)
            (by norm_num)
        _ = 64 * r ^ 2 := by ring
    have hscale :
        ε⁻¹ ^ (4 : ℕ) * (Cker * (6 * r) ^ 2) ≤
          (2304 * Cker * supportConstant ^ 4) *
            invSqKer x := by
      unfold invSqKer
      rw [le_mul_inv_iff₀ hxDist]
      dsimp only [r]
      field_simp [hε.ne']
      nlinarith [hCker.le, sq_nonneg supportConstant,
        sq_nonneg (supportConstant ^ 2)]
    calc
      ε⁻¹ ^ (4 : ℕ) *
          (∫ z in S, invSqKer (x - z) ∂paperMeasure) ≤
          ε⁻¹ ^ (4 : ℕ) * (Cker * (6 * r) ^ 2) :=
        mul_le_mul_of_nonneg_left hlocal
          (pow_nonneg (inv_nonneg.mpr hε.le) 4)
      _ ≤ (2304 * Cker * supportConstant ^ 4) *
          invSqKer x := hscale
      _ ≤ K * invSqKer x := by
        apply mul_le_mul_of_nonneg_right _ (invSqKer_nonneg x)
        dsimp only [K]
        nlinarith [hCvol.le, pow_nonneg hsupport.le 4]
  · have hfar : 4 * r < ‖x‖ := lt_of_not_ge hnear
    have hpoint :
        ∀ z ∈ S,
          invSqKer (x - z) ≤ 8 * invSqKer x := by
      intro z hz
      have hzsq : ‖z‖ ^ 2 ≤ r ^ 2 :=
        (sq_norm_le_torusDistSq z).trans hz
      have hznorm : ‖z‖ ≤ r := by
        nlinarith [norm_nonneg z]
      have hquarter : 4 * ‖z‖ < ‖x‖ := by
        linarith
      have hsep : 3 * ‖x‖ / 4 < ‖x - z‖ := by
        have hreverse := norm_sub_norm_le x z
        linarith
      have hsepSq :
          9 * ‖x‖ ^ 2 < 16 * ‖x - z‖ ^ 2 := by
        nlinarith [norm_nonneg x, norm_nonneg (x - z)]
      rcases eq_or_ne (x - z) 0 with hzero | hne
      · exfalso
        rw [hzero, norm_zero] at hsep
        linarith [norm_nonneg x]
      · have hxd :
            torusDistSq x ≤ 4 * ‖x‖ ^ 2 :=
          torusDistSq_le_four_mul_sq_norm x
        have hsepDist :
            torusDistSq x < 8 * torusDistSq (x - z) := by
          have hlower :
              ‖x - z‖ ^ 2 ≤ torusDistSq (x - z) :=
            sq_norm_le_torusDistSq (x - z)
          nlinarith
        unfold invSqKer
        have hdiffDist : 0 < torusDistSq (x - z) := by
          have hdistNe : torusDistSq (x - z) ≠ 0 := by
            intro hd0
            exact hne ((torusDistSq_eq_zero_iff (x - z)).mp hd0)
          exact lt_of_le_of_ne
            (torusDistSq_nonneg (x - z)) hdistNe.symm
        rw [le_mul_inv_iff₀ hxDist, inv_mul_eq_div,
          div_le_iff₀ hdiffDist]
        exact hsepDist.le
    have hmeasure :
        (paperMeasure S).toReal ≤
          Cvol * (2 * r) ^ 4 := by
      calc
        (paperMeasure S).toReal ≤
            (paperMeasure
              (Metric.ball (0 : T4) (2 * r))).toReal :=
          measureReal_mono
            (r322ScaleBall_subset_metricBall hsupport hε)
        _ ≤ Cvol * (2 * r) ^ 4 :=
          hvol 0 (2 * r) (by positivity)
    have hconstInt :
        IntegrableOn (fun _z : T4 => 8 * invSqKer x)
          S paperMeasure :=
      integrableOn_const
    have hintegral :
        (∫ z in S, invSqKer (x - z) ∂paperMeasure) ≤
          (8 * invSqKer x) * (paperMeasure S).toReal := by
      calc
        (∫ z in S, invSqKer (x - z) ∂paperMeasure) ≤
            ∫ _z in S, 8 * invSqKer x ∂paperMeasure := by
          exact setIntegral_mono_on
            (integrable_invSqKer_sub_left x).integrableOn
            hconstInt hS hpoint
        _ = (8 * invSqKer x) *
            (paperMeasure S).toReal := by
          rw [setIntegral_const]
          simp only [smul_eq_mul, measureReal_def]
          ring
    have hscaled :
        ε⁻¹ ^ (4 : ℕ) *
            ((8 * invSqKer x) * (paperMeasure S).toReal) ≤
          (128 * Cvol * supportConstant ^ 4) *
            invSqKer x := by
      calc
        ε⁻¹ ^ (4 : ℕ) *
              ((8 * invSqKer x) * (paperMeasure S).toReal) ≤
            ε⁻¹ ^ (4 : ℕ) *
              ((8 * invSqKer x) * (Cvol * (2 * r) ^ 4)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmeasure
              (mul_nonneg (by norm_num) (invSqKer_nonneg x)))
            (pow_nonneg (inv_nonneg.mpr hε.le) 4)
        _ = (128 * Cvol * supportConstant ^ 4) *
              invSqKer x := by
          dsimp only [r]
          field_simp [hε.ne']
          ring
    calc
      ε⁻¹ ^ (4 : ℕ) *
          (∫ z in S, invSqKer (x - z) ∂paperMeasure) ≤
          ε⁻¹ ^ (4 : ℕ) *
            ((8 * invSqKer x) * (paperMeasure S).toReal) :=
        mul_le_mul_of_nonneg_left hintegral
          (pow_nonneg (inv_nonneg.mpr hε.le) 4)
      _ ≤ (128 * Cvol * supportConstant ^ 4) *
          invSqKer x := hscaled
      _ ≤ K * invSqKer x := by
        apply mul_le_mul_of_nonneg_right _ (invSqKer_nonneg x)
        dsimp only [K]
        nlinarith [hCker.le, pow_nonneg hsupport.le 4]

/-- The critical annulus outside the cutoff scale. -/
def r322CriticalAnnulus (ε : ℝ) : Set T4 :=
  {z | ε ^ 2 ≤ torusDistSq z}

theorem measurableSet_r322CriticalAnnulus (ε : ℝ) :
    MeasurableSet (r322CriticalAnnulus ε) :=
  measurable_torusDistSq measurableSet_Ici

/-- If `w` is at least half as far from zero as `x`, its inverse-square
kernel is controlled by the kernel at `x`. -/
theorem invSqKer_le_sixteen_mul_of_half_norm
    {x w : T4} (hx : x ≠ 0)
    (hfar : ‖x‖ / 2 ≤ ‖w‖) :
    invSqKer w ≤ 16 * invSqKer x := by
  have hxDist : 0 < torusDistSq x := by
    have hne : torusDistSq x ≠ 0 := by
      intro hzero
      exact hx ((torusDistSq_eq_zero_iff x).mp hzero)
    exact lt_of_le_of_ne (torusDistSq_nonneg x) hne.symm
  have hxNorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hwNorm : 0 < ‖w‖ := lt_of_lt_of_le (by positivity) hfar
  have hw : w ≠ 0 := norm_ne_zero_iff.mp hwNorm.ne'
  have hwDist : 0 < torusDistSq w := by
    have hne : torusDistSq w ≠ 0 := by
      intro hzero
      exact hw ((torusDistSq_eq_zero_iff w).mp hzero)
    exact lt_of_le_of_ne (torusDistSq_nonneg w) hne.symm
  have hcompare :
      torusDistSq x ≤ 16 * torusDistSq w := by
    calc
      torusDistSq x ≤ 4 * ‖x‖ ^ 2 :=
        torusDistSq_le_four_mul_sq_norm x
      _ ≤ 16 * ‖w‖ ^ 2 := by
        nlinarith [norm_nonneg x, norm_nonneg w]
      _ ≤ 16 * torusDistSq w :=
        mul_le_mul_of_nonneg_left
          (sq_norm_le_torusDistSq w) (by norm_num)
  unfold invSqKer
  rw [le_mul_inv_iff₀ hxDist, inv_mul_eq_div,
    div_le_iff₀ hwDist]
  exact hcompare

theorem integrableOn_invSqKer_sq_r322CriticalAnnulus
    {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun z : T4 => invSqKer z ^ 2)
      (r322CriticalAnnulus ε) paperMeasure := by
  let B : ℝ := ε⁻¹ ^ (4 : ℕ)
  have hconst :
      Integrable (fun _ : T4 => B)
        (paperMeasure.restrict (r322CriticalAnnulus ε)) :=
    integrable_const B
  apply hconst.mono'
    ((measurable_invSqKer.pow_const 2)
      |>.aestronglyMeasurable.restrict)
  filter_upwards
      [ae_restrict_mem (measurableSet_r322CriticalAnnulus ε)]
      with z hz
  unfold invSqKer B
  change
    |(torusDistSq z)⁻¹ ^ 2| ≤ ε⁻¹ ^ (4 : ℕ)
  rw [abs_of_nonneg
      (pow_nonneg (inv_nonneg.mpr (torusDistSq_nonneg z)) 2)]
  have hzDist : 0 < torusDistSq z :=
    lt_of_lt_of_le (sq_pos_of_pos hε) hz
  have hinv :
      (torusDistSq z)⁻¹ ≤ (ε ^ 2)⁻¹ :=
    (inv_le_inv₀ hzDist (sq_pos_of_pos hε)).2 hz
  calc
    (torusDistSq z)⁻¹ ^ 2 ≤ (ε ^ 2)⁻¹ ^ 2 :=
      pow_le_pow_left₀
        (inv_nonneg.mpr (torusDistSq_nonneg z)) hinv 2
    _ = ε⁻¹ ^ (4 : ℕ) := by
      field_simp [hε.ne']

/-- On the critical annulus the squared kernel is bounded, which supplies
the joint integrability needed before splitting at the second
singularity. -/
theorem integrableOn_r322Critical_product
    {ε : ℝ} (hε : 0 < ε) (x : T4) :
    IntegrableOn
      (fun z : T4 =>
        invSqKer (x - z) * invSqKer z ^ 2)
      (r322CriticalAnnulus ε) paperMeasure := by
  have hmajorant :
      IntegrableOn
        (fun z : T4 =>
          invSqKer (x - z) * ε⁻¹ ^ (4 : ℕ))
        (r322CriticalAnnulus ε) paperMeasure :=
    ((integrable_invSqKer_sub_left x).mul_const
      (ε⁻¹ ^ (4 : ℕ))).integrableOn
  apply hmajorant.mono'
    (((measurable_invSqKer.comp
        (measurable_const.sub measurable_id)).mul
      (measurable_invSqKer.pow_const 2))
      |>.aestronglyMeasurable.restrict)
  filter_upwards
      [ae_restrict_mem (measurableSet_r322CriticalAnnulus ε)]
      with z hz
  change
    |invSqKer (x - z) * invSqKer z ^ 2| ≤
      invSqKer (x - z) * ε⁻¹ ^ 4
  rw [abs_of_nonneg
    (mul_nonneg (invSqKer_nonneg (x - z))
      (sq_nonneg (invSqKer z)))]
  apply mul_le_mul_of_nonneg_left _ (invSqKer_nonneg (x - z))
  unfold invSqKer
  have hzDist : 0 < torusDistSq z :=
    lt_of_lt_of_le (sq_pos_of_pos hε) hz
  have hinv :
      (torusDistSq z)⁻¹ ≤ (ε ^ 2)⁻¹ :=
    (inv_le_inv₀ hzDist (sq_pos_of_pos hε)).2 hz
  calc
    (torusDistSq z)⁻¹ ^ 2 ≤ (ε ^ 2)⁻¹ ^ 2 :=
      pow_le_pow_left₀
        (inv_nonneg.mpr (torusDistSq_nonneg z)) hinv 2
    _ = ε⁻¹ ^ (4 : ℕ) := by
      field_simp [hε.ne']

/-- The logarithmically normalized critical annulus is also an
approximate identity for the inverse-square kernel.  The proof splits at
a ball around the moving singularity `x`; this avoids any hidden use of a
non-integrable product. -/
theorem exists_r322CriticalAnnulus_convolution_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ε : ℝ) (x : T4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → x ≠ 0 →
        (1 / |Real.log ε|) *
            (∫ z in r322CriticalAnnulus ε,
              invSqKer (x - z) * invSqKer z ^ 2
                ∂paperMeasure) ≤
          K * invSqKer x := by
  obtain ⟨Cker, hCker, hker⟩ := invSqKerBallIntegral_le
  obtain ⟨Cann, hCann, hann⟩ :=
    setIntegral_invSqKer_sq_annulus_le
  let K : ℝ := 256 * Cker + 64 * Cann + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro ε x hε hε1 hlog hx
  let L : ℝ := |Real.log ε|
  let S : Set T4 := r322CriticalAnnulus ε
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hlog
  have hS : MeasurableSet S :=
    measurableSet_r322CriticalAnnulus ε
  have hint :=
    integrableOn_r322Critical_product hε x
  have hAnnInt :
      IntegrableOn (fun z : T4 => invSqKer z ^ 2)
        S paperMeasure :=
    integrableOn_invSqKer_sq_r322CriticalAnnulus hε
  have hAnn :
      (∫ z in S, invSqKer z ^ 2 ∂paperMeasure) ≤
        Cann * (1 + L) := by
    exact hann ε hε hε1
  have hratio : (1 + L) / L ≤ 2 := by
    rw [div_le_iff₀ hL]
    linarith
  have hxDist : 0 < torusDistSq x := by
    have hne : torusDistSq x ≠ 0 := by
      intro hzero
      exact hx ((torusDistSq_eq_zero_iff x).mp hzero)
    exact lt_of_le_of_ne (torusDistSq_nonneg x) hne.symm
  by_cases hnear : ‖x‖ ≤ 4 * ε
  · let B : Set T4 := Metric.ball x (2 * ε)
    have hB : MeasurableSet B := measurableSet_ball
    let f : T4 → ℝ := fun z =>
      S.indicator
        (fun w => invSqKer (x - w) * invSqKer w ^ 2) z
    let g₁ : T4 → ℝ := fun z =>
      B.indicator
        (fun w => ε⁻¹ ^ (4 : ℕ) * invSqKer (x - w)) z
    let g₂ : T4 → ℝ := fun z =>
      Bᶜ.indicator
        (fun w => (2 * ε)⁻¹ ^ (2 : ℕ) *
          S.indicator (fun v => invSqKer v ^ 2) w) z
    have hf : Integrable f paperMeasure := by
      dsimp only [f]
      exact hint.integrable_indicator hS
    have hg₁ : Integrable g₁ paperMeasure := by
      dsimp only [g₁]
      exact
        ((integrable_invSqKer_sub_left x).const_mul
          (ε⁻¹ ^ (4 : ℕ))).indicator hB
    have hg₂ : Integrable g₂ paperMeasure := by
      dsimp only [g₂]
      exact
        ((hAnnInt.integrable_indicator hS).const_mul
          ((2 * ε)⁻¹ ^ (2 : ℕ))).indicator hB.compl
    have hpoint : ∀ z, f z ≤ g₁ z + g₂ z := by
      intro z
      by_cases hzS : z ∈ S
      · rw [show f z =
            invSqKer (x - z) * invSqKer z ^ 2 by
          simp [f, hzS]]
        by_cases hzB : z ∈ B
        · rw [show g₁ z =
              ε⁻¹ ^ (4 : ℕ) * invSqKer (x - z) by
            simp [g₁, hzB]]
          have hsq :
              invSqKer z ^ 2 ≤ ε⁻¹ ^ (4 : ℕ) := by
            unfold invSqKer
            have hzDist : 0 < torusDistSq z :=
              lt_of_lt_of_le (sq_pos_of_pos hε) hzS
            have hinv :
                (torusDistSq z)⁻¹ ≤ (ε ^ 2)⁻¹ :=
              (inv_le_inv₀ hzDist (sq_pos_of_pos hε)).2 hzS
            calc
              (torusDistSq z)⁻¹ ^ 2 ≤
                  (ε ^ 2)⁻¹ ^ 2 :=
                pow_le_pow_left₀
                  (inv_nonneg.mpr (torusDistSq_nonneg z))
                  hinv 2
              _ = ε⁻¹ ^ (4 : ℕ) := by
                field_simp [hε.ne']
          exact le_add_of_le_of_nonneg
            (by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_right hsq
                (invSqKer_nonneg (x - z)))
            (Set.indicator_nonneg
              (fun _ _ =>
                mul_nonneg
                  (pow_nonneg
                    (inv_nonneg.mpr (by positivity : 0 ≤ 2 * ε)) 2)
                  (Set.indicator_nonneg
                    (fun _ _ => sq_nonneg _) z)) z)
        · rw [show g₂ z =
              (2 * ε)⁻¹ ^ (2 : ℕ) * invSqKer z ^ 2 by
            simp [g₂, hzB, hzS]]
          have hnorm :
              2 * ε ≤ ‖x - z‖ := by
            change z ∉ Metric.ball x (2 * ε) at hzB
            rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hzB
            exact le_of_not_gt hzB
          have hker :
              invSqKer (x - z) ≤
                (2 * ε)⁻¹ ^ (2 : ℕ) := by
            calc
              invSqKer (x - z) ≤ (‖x - z‖ ^ 2)⁻¹ :=
                invSqKer_le_inv_sq_norm_cell (x - z)
              _ ≤ ((2 * ε) ^ 2)⁻¹ :=
                inv_anti₀ (sq_pos_of_pos (by positivity))
                  (pow_le_pow_left₀ (by positivity) hnorm 2)
              _ = (2 * ε)⁻¹ ^ (2 : ℕ) := by
                rw [inv_pow]
          exact le_add_of_nonneg_of_le
            (Set.indicator_nonneg
              (fun _ _ =>
                mul_nonneg
                  (pow_nonneg (inv_nonneg.mpr hε.le) 4)
                  (invSqKer_nonneg _)) z)
            (mul_le_mul_of_nonneg_right hker
              (sq_nonneg (invSqKer z)))
      · rw [show f z = 0 by simp [f, hzS]]
        exact add_nonneg
          (Set.indicator_nonneg
            (fun _ _ =>
              mul_nonneg
                (pow_nonneg (inv_nonneg.mpr hε.le) 4)
                (invSqKer_nonneg _)) z)
          (Set.indicator_nonneg
            (fun _ _ =>
              mul_nonneg
                (pow_nonneg
                  (inv_nonneg.mpr (by positivity : 0 ≤ 2 * ε)) 2)
                (Set.indicator_nonneg
                  (fun _ _ => sq_nonneg _) z)) z)
    have hraw :
        (∫ z in S,
            invSqKer (x - z) * invSqKer z ^ 2
              ∂paperMeasure) ≤
          ε⁻¹ ^ (4 : ℕ) *
              (Cker * (2 * ε) ^ 2) +
            (2 * ε)⁻¹ ^ (2 : ℕ) *
              (Cann * (1 + L)) := by
      calc
        (∫ z in S,
            invSqKer (x - z) * invSqKer z ^ 2
              ∂paperMeasure) =
            ∫ z, f z ∂paperMeasure := by
          dsimp only [f]
          exact (integral_indicator hS).symm
        _ ≤ ∫ z, g₁ z + g₂ z ∂paperMeasure :=
          integral_mono hf (hg₁.add hg₂) hpoint
        _ = (∫ z, g₁ z ∂paperMeasure) +
              ∫ z, g₂ z ∂paperMeasure :=
          integral_add hg₁ hg₂
        _ ≤ ε⁻¹ ^ (4 : ℕ) *
              (Cker * (2 * ε) ^ 2) +
            (2 * ε)⁻¹ ^ (2 : ℕ) *
              (Cann * (1 + L)) := by
          apply add_le_add
          · dsimp only [g₁]
            rw [integral_indicator hB, integral_const_mul]
            exact mul_le_mul_of_nonneg_left
              (hker x (2 * ε) (by positivity))
              (pow_nonneg (inv_nonneg.mpr hε.le) 4)
          · dsimp only [g₂]
            rw [integral_indicator hB.compl, integral_const_mul]
            calc
              (2 * ε)⁻¹ ^ (2 : ℕ) *
                    ∫ z in Bᶜ,
                      S.indicator (fun v => invSqKer v ^ 2) z
                        ∂paperMeasure ≤
                  (2 * ε)⁻¹ ^ (2 : ℕ) *
                    ∫ z, S.indicator
                      (fun v => invSqKer v ^ 2) z
                        ∂paperMeasure := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact setIntegral_le_integral
                  (hAnnInt.integrable_indicator hS)
                  (.of_forall fun z =>
                    Set.indicator_nonneg
                      (fun _ _ => sq_nonneg _) z)
              _ = (2 * ε)⁻¹ ^ (2 : ℕ) *
                    ∫ z in S, invSqKer z ^ 2
                      ∂paperMeasure := by
                rw [integral_indicator hS]
              _ ≤ (2 * ε)⁻¹ ^ (2 : ℕ) *
                    (Cann * (1 + L)) :=
                mul_le_mul_of_nonneg_left hAnn (by positivity)
    have hxUpper : torusDistSq x ≤ 64 * ε ^ 2 := by
      calc
        torusDistSq x ≤ 4 * ‖x‖ ^ 2 :=
          torusDistSq_le_four_mul_sq_norm x
        _ ≤ 4 * (4 * ε) ^ 2 := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg x) hnear 2)
            (by norm_num)
        _ = 64 * ε ^ 2 := by ring
    have hscaled :
        (1 / L) *
            (ε⁻¹ ^ (4 : ℕ) *
                (Cker * (2 * ε) ^ 2) +
              (2 * ε)⁻¹ ^ (2 : ℕ) *
                (Cann * (1 + L))) ≤
          (256 * Cker + 32 * Cann) * invSqKer x := by
      have hsimplify :
          (1 / L) *
              (ε⁻¹ ^ (4 : ℕ) *
                  (Cker * (2 * ε) ^ 2) +
                (2 * ε)⁻¹ ^ (2 : ℕ) *
                  (Cann * (1 + L))) =
            ε⁻¹ ^ (2 : ℕ) *
              (4 * Cker / L +
                (Cann / 4) * ((1 + L) / L)) := by
        field_simp [hε.ne', hL.ne']
        ring
      rw [hsimplify]
      have hcoeff :
          4 * Cker / L +
              (Cann / 4) * ((1 + L) / L) ≤
            4 * Cker + Cann / 2 := by
        apply add_le_add
        · exact div_le_self
            (mul_nonneg (by norm_num) hCker.le) hlog
        · calc
            (Cann / 4) * ((1 + L) / L) ≤
                (Cann / 4) * 2 :=
              mul_le_mul_of_nonneg_left hratio
                (div_nonneg hCann.le (by norm_num))
            _ = Cann / 2 := by ring
      calc
        ε⁻¹ ^ (2 : ℕ) *
              (4 * Cker / L +
                (Cann / 4) * ((1 + L) / L)) ≤
            ε⁻¹ ^ (2 : ℕ) *
              (4 * Cker + Cann / 2) :=
          mul_le_mul_of_nonneg_left hcoeff
            (pow_nonneg (inv_nonneg.mpr hε.le) 2)
        _ ≤ (256 * Cker + 32 * Cann) * invSqKer x := by
          unfold invSqKer
          rw [le_mul_inv_iff₀ hxDist]
          field_simp [hε.ne']
          nlinarith [hxUpper, hCker.le, hCann.le]
    calc
      (1 / L) *
          (∫ z in S,
            invSqKer (x - z) * invSqKer z ^ 2
              ∂paperMeasure) ≤
          (1 / L) *
            (ε⁻¹ ^ (4 : ℕ) *
                (Cker * (2 * ε) ^ 2) +
              (2 * ε)⁻¹ ^ (2 : ℕ) *
                (Cann * (1 + L))) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
      _ ≤ (256 * Cker + 32 * Cann) * invSqKer x :=
        hscaled
      _ ≤ K * invSqKer x := by
        apply mul_le_mul_of_nonneg_right _ (invSqKer_nonneg x)
        dsimp only [K]
        linarith [hCann.le]
  · have hfar : 4 * ε < ‖x‖ := lt_of_not_ge hnear
    let B : Set T4 := Metric.ball x (‖x‖ / 2)
    have hB : MeasurableSet B := measurableSet_ball
    let f : T4 → ℝ := fun z =>
      S.indicator
        (fun w => invSqKer (x - w) * invSqKer w ^ 2) z
    let g₁ : T4 → ℝ := fun z =>
      B.indicator
        (fun w => 256 * invSqKer x ^ 2 *
          invSqKer (x - w)) z
    let g₂ : T4 → ℝ := fun z =>
      Bᶜ.indicator
        (fun w => 16 * invSqKer x *
          S.indicator (fun v => invSqKer v ^ 2) w) z
    have hf : Integrable f paperMeasure := by
      dsimp only [f]
      exact hint.integrable_indicator hS
    have hg₁ : Integrable g₁ paperMeasure := by
      dsimp only [g₁]
      exact
        ((integrable_invSqKer_sub_left x).const_mul
          (256 * invSqKer x ^ 2)).indicator hB
    have hg₂ : Integrable g₂ paperMeasure := by
      dsimp only [g₂]
      exact
        ((hAnnInt.integrable_indicator hS).const_mul
          (16 * invSqKer x)).indicator hB.compl
    have hpoint : ∀ z, f z ≤ g₁ z + g₂ z := by
      intro z
      by_cases hzS : z ∈ S
      · rw [show f z =
            invSqKer (x - z) * invSqKer z ^ 2 by
          simp [f, hzS]]
        by_cases hzB : z ∈ B
        · rw [show g₁ z =
              256 * invSqKer x ^ 2 * invSqKer (x - z) by
            simp [g₁, hzB]]
          have hzHalf : ‖x‖ / 2 ≤ ‖z‖ := by
            have hzNear : ‖z - x‖ < ‖x‖ / 2 := by
              simpa only [B, Metric.mem_ball, dist_eq_norm] using hzB
            have hreverse := norm_sub_norm_le x z
            rw [norm_sub_rev] at hreverse
            linarith
          have hzKer :=
            invSqKer_le_sixteen_mul_of_half_norm hx hzHalf
          have hzSq :
              invSqKer z ^ 2 ≤
                256 * invSqKer x ^ 2 := by
            nlinarith [invSqKer_nonneg z, invSqKer_nonneg x]
          exact le_add_of_le_of_nonneg
            (by
              rw [mul_assoc, mul_comm (invSqKer (x - z))]
              simpa only [mul_assoc] using
                (mul_le_mul_of_nonneg_right hzSq
                  (invSqKer_nonneg (x - z))))
            (Set.indicator_nonneg
              (fun _ _ =>
                mul_nonneg
                  (mul_nonneg (by norm_num) (invSqKer_nonneg x))
                  (Set.indicator_nonneg
                    (fun _ _ => sq_nonneg _) z)) z)
        · rw [show g₂ z =
              16 * invSqKer x * invSqKer z ^ 2 by
            simp [g₂, hzB, hzS]]
          have hzHalf : ‖x‖ / 2 ≤ ‖x - z‖ := by
            change z ∉ Metric.ball x (‖x‖ / 2) at hzB
            rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hzB
            exact le_of_not_gt hzB
          have hkernel :=
            invSqKer_le_sixteen_mul_of_half_norm
              hx hzHalf
          exact le_add_of_nonneg_of_le
            (Set.indicator_nonneg
              (fun _ _ =>
                mul_nonneg
                  (mul_nonneg (by norm_num)
                    (sq_nonneg (invSqKer x)))
                  (invSqKer_nonneg _)) z)
            (mul_le_mul_of_nonneg_right hkernel
              (sq_nonneg (invSqKer z)))
      · rw [show f z = 0 by simp [f, hzS]]
        exact add_nonneg
          (Set.indicator_nonneg
            (fun _ _ =>
              mul_nonneg
                (mul_nonneg (by norm_num)
                  (sq_nonneg (invSqKer x)))
                (invSqKer_nonneg _)) z)
          (Set.indicator_nonneg
            (fun _ _ =>
              mul_nonneg
                (mul_nonneg (by norm_num) (invSqKer_nonneg x))
                (Set.indicator_nonneg
                  (fun _ _ => sq_nonneg _) z)) z)
    have hraw :
        (∫ z in S,
            invSqKer (x - z) * invSqKer z ^ 2
              ∂paperMeasure) ≤
          (256 * invSqKer x ^ 2) *
              (Cker * (‖x‖ / 2) ^ 2) +
            (16 * invSqKer x) *
              (Cann * (1 + L)) := by
      calc
        (∫ z in S,
            invSqKer (x - z) * invSqKer z ^ 2
              ∂paperMeasure) =
            ∫ z, f z ∂paperMeasure := by
          dsimp only [f]
          exact (integral_indicator hS).symm
        _ ≤ ∫ z, g₁ z + g₂ z ∂paperMeasure :=
          integral_mono hf (hg₁.add hg₂) hpoint
        _ = (∫ z, g₁ z ∂paperMeasure) +
              ∫ z, g₂ z ∂paperMeasure :=
          integral_add hg₁ hg₂
        _ ≤ (256 * invSqKer x ^ 2) *
              (Cker * (‖x‖ / 2) ^ 2) +
            (16 * invSqKer x) *
              (Cann * (1 + L)) := by
          apply add_le_add
          · dsimp only [g₁]
            rw [integral_indicator hB, integral_const_mul]
            exact mul_le_mul_of_nonneg_left
              (hker x (‖x‖ / 2) (by positivity))
              (mul_nonneg (by norm_num) (sq_nonneg (invSqKer x)))
          · dsimp only [g₂]
            rw [integral_indicator hB.compl, integral_const_mul]
            calc
              (16 * invSqKer x) *
                    ∫ z in Bᶜ,
                      S.indicator (fun v => invSqKer v ^ 2) z
                        ∂paperMeasure ≤
                  (16 * invSqKer x) *
                    ∫ z, S.indicator
                      (fun v => invSqKer v ^ 2) z
                        ∂paperMeasure := by
                apply mul_le_mul_of_nonneg_left _
                  (mul_nonneg (by norm_num) (invSqKer_nonneg x))
                exact setIntegral_le_integral
                  (hAnnInt.integrable_indicator hS)
                  (.of_forall fun z =>
                    Set.indicator_nonneg
                      (fun _ _ => sq_nonneg _) z)
              _ = (16 * invSqKer x) *
                    ∫ z in S, invSqKer z ^ 2
                      ∂paperMeasure := by
                rw [integral_indicator hS]
              _ ≤ (16 * invSqKer x) *
                    (Cann * (1 + L)) :=
                mul_le_mul_of_nonneg_left hAnn
                  (mul_nonneg (by norm_num) (invSqKer_nonneg x))
    have hfirst :
        (1 / L) *
            ((256 * invSqKer x ^ 2) *
              (Cker * (‖x‖ / 2) ^ 2)) ≤
          64 * Cker * invSqKer x := by
      have hnormDist :
          ‖x‖ ^ 2 ≤ torusDistSq x :=
        sq_norm_le_torusDistSq x
      unfold invSqKer
      rw [show (torusDistSq x)⁻¹ ^ 2 =
          1 / (torusDistSq x) ^ 2 by
        simp only [one_div, inv_pow]]
      rw [le_mul_inv_iff₀ hxDist]
      field_simp [hL.ne', hxDist.ne']
      nlinarith [hCker.le, hlog, hnormDist]
    have hsecond :
        (1 / L) *
            ((16 * invSqKer x) * (Cann * (1 + L))) ≤
          32 * Cann * invSqKer x := by
      have hnonneg : 0 ≤ 16 * invSqKer x * Cann := by
        exact mul_nonneg
          (mul_nonneg (by norm_num) (invSqKer_nonneg x))
          hCann.le
      calc
        (1 / L) *
              ((16 * invSqKer x) * (Cann * (1 + L))) =
            (16 * invSqKer x * Cann) * ((1 + L) / L) := by
          field_simp [hL.ne']
        _ ≤ (16 * invSqKer x * Cann) * 2 :=
          mul_le_mul_of_nonneg_left hratio hnonneg
        _ = 32 * Cann * invSqKer x := by ring
    calc
      (1 / L) *
          (∫ z in S,
            invSqKer (x - z) * invSqKer z ^ 2
              ∂paperMeasure) ≤
          (1 / L) *
            ((256 * invSqKer x ^ 2) *
                (Cker * (‖x‖ / 2) ^ 2) +
              (16 * invSqKer x) *
                (Cann * (1 + L))) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
      _ = (1 / L) *
            ((256 * invSqKer x ^ 2) *
              (Cker * (‖x‖ / 2) ^ 2)) +
          (1 / L) *
            ((16 * invSqKer x) *
              (Cann * (1 + L))) := by ring
      _ ≤ 64 * Cker * invSqKer x +
          32 * Cann * invSqKer x :=
        add_le_add hfirst hsecond
      _ ≤ K * invSqKer x := by
        calc
          64 * Cker * invSqKer x +
                32 * Cann * invSqKer x =
              (64 * Cker + 32 * Cann) * invSqKer x := by ring
          _ ≤ K * invSqKer x := by
            apply mul_le_mul_of_nonneg_right _ (invSqKer_nonneg x)
            dsimp only [K]
            nlinarith [hCker.le, hCann.le]

end

end Anderson4D
