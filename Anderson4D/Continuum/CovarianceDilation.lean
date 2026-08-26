import Anderson4D.Continuum.Covariance

/-!
# Dilation and local positivity of cutoff covariances

This file supplies the cutoff-dependent auxiliary covariance used by the
relative-translation derivative route in paper §4.2.  Dilating a cutoff
preserves the frozen `SmoothCutoff` contract and gives an exact scaling law
for `η = ρ * ρ`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set
open scoped Convolution

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- Dilation by a positive scale, with the same normalization as `rescale`. -/
noncomputable def dilate (a : ℝ) (ha : 0 < a) : SmoothCutoff where
  toFun := ρ.rescale a
  radius := a * ρ.radius
  radius_pos := mul_pos ha ρ.radius_pos
  smooth := by
    intro n
    unfold rescale
    simpa only [smul_eq_mul, Function.comp_apply] using
      ((ρ.smooth n).comp (contDiff_const_smul a⁻¹)).const_smul
        (a⁻¹ ^ (dim : ℕ))
  nonneg := by
    intro x
    exact mul_nonneg (pow_nonneg (inv_nonneg.mpr ha.le) _) (ρ.nonneg _)
  support_subset := by
    intro x hx
    have hρ : ρ (a⁻¹ • x) ≠ 0 := by
      intro hzero
      apply hx
      simp [rescale, hzero]
    have hsupport := ρ.support_subset hρ
    have hscaled : a⁻¹ * ‖x‖ < ρ.radius := by
      simpa [Metric.mem_ball, dist_zero_right, norm_smul,
        abs_of_pos ha, abs_inv] using hsupport
    rw [Metric.mem_ball, dist_zero_right]
    calc
      ‖x‖ = a * (a⁻¹ * ‖x‖) := by field_simp [ha.ne']
      _ < a * ρ.radius := mul_lt_mul_of_pos_left hscaled ha
  memE := by
    constructor
    · intro σ x
      unfold rescale
      have harg : a⁻¹ • (x ∘ σ) = (a⁻¹ • x) ∘ σ := rfl
      rw [harg, ρ.memE.perm_invariant σ (a⁻¹ • x)]
    · intro i x
      unfold rescale
      have harg :
          a⁻¹ • Function.update x i (-(x i)) =
            Function.update (a⁻¹ • x) i (-((a⁻¹ • x) i)) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp
        · simp [Function.update_of_ne hji]
      rw [harg, ρ.memE.even_coord i (a⁻¹ • x)]
  integral_one := by
    unfold rescale
    rw [integral_const_mul]
    rw [(volume : Measure R4).integral_comp_inv_smul_of_nonneg
      (ρ : R4 → ℝ) ha.le]
    simp only [Module.finrank_pi, Fintype.card_fin, dim,
      ρ.integral_one, smul_eq_mul, mul_one]
    field_simp [ha.ne']

@[simp]
theorem dilate_apply (a : ℝ) (ha : 0 < a) (x : R4) :
    ρ.dilate a ha x = a⁻¹ ^ (dim : ℕ) * ρ (a⁻¹ • x) :=
  rfl

@[simp]
theorem dilate_radius (a : ℝ) (ha : 0 < a) :
    (ρ.dilate a ha).radius = a * ρ.radius :=
  rfl

theorem dilate_toFun_eq_rescale (a : ℝ) (ha : 0 < a) :
    (ρ.dilate a ha : R4 → ℝ) = ρ.rescale a :=
  rfl

/-- The covariance of a dilated cutoff has the exact four-dimensional
scaling dictated by convolution. -/
theorem eta_dilate (a : ℝ) (ha : 0 < a) (x : R4) :
    (ρ.dilate a ha).eta x =
      a⁻¹ ^ (dim : ℕ) * ρ.eta (a⁻¹ • x) := by
  let c : ℝ := a⁻¹ ^ (dim : ℕ)
  let g : R4 → ℝ :=
    fun u => c ^ 2 * (ρ u * ρ (a⁻¹ • x - u))
  have hpoint (y : R4) :
      ρ.dilate a ha y * ρ.dilate a ha (x - y) =
        g (a⁻¹ • y) := by
    simp only [dilate_apply]
    dsimp [g, c]
    rw [smul_sub]
    ring
  have hg :
      (∫ u : R4, g u) = c ^ 2 * ρ.eta (a⁻¹ • x) := by
    dsimp [g]
    rw [integral_const_mul]
    rfl
  change
    (∫ y : R4, ρ.dilate a ha y * ρ.dilate a ha (x - y)) =
      a⁻¹ ^ (dim : ℕ) * ρ.eta (a⁻¹ • x)
  calc
    (∫ y : R4, ρ.dilate a ha y * ρ.dilate a ha (x - y)) =
        ∫ y : R4, g (a⁻¹ • y) :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = a ^ Module.finrank ℝ R4 • ∫ u : R4, g u :=
      (volume : Measure R4).integral_comp_inv_smul_of_nonneg g ha.le
    _ = a⁻¹ ^ (dim : ℕ) * ρ.eta (a⁻¹ • x) := by
      rw [hg]
      dsimp [c]
      simp only [Module.finrank_pi, Fintype.card_fin, dim]
      field_simp [ha.ne']

/-- The cutoff covariance is smooth to every requested finite order. -/
theorem contDiff_eta (n : ℕ) :
    ContDiff ℝ n ρ.eta := by
  change ContDiff ℝ n
    ((ρ : R4 → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ]
      (ρ : R4 → ℝ))
  exact ρ.hasCompactSupport.contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ)
    ρ.integrable.locallyIntegrable (ρ.smooth n)

/-- In particular, the cutoff covariance is continuous. -/
theorem continuous_eta :
    Continuous ρ.eta :=
  (ρ.contDiff_eta 0).continuous

/-- Convolution preserves compact support for the cutoff covariance. -/
theorem hasCompactSupport_eta :
    HasCompactSupport ρ.eta := by
  change HasCompactSupport
    ((ρ : R4 → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ]
      (ρ : R4 → ℝ))
  exact ρ.hasCompactSupport.convolution
    (ContinuousLinearMap.mul ℝ ℝ) ρ.hasCompactSupport

end SmoothCutoff

end

end Anderson4D
