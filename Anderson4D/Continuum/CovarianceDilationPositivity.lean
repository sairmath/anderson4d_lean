import Anderson4D.Continuum.CovarianceDilation

/-!
# Positive auxiliary cutoff covariance

The relative-translation derivative route needs a positive covariance
majorant on the support of every derivative of the original covariance.
This file constructs that majorant from a named, cutoff-dependent dilation.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set

/-! ## Simultaneous Euclidean sign flips -/

/-- Negate precisely the Euclidean coordinates in `s`. -/
def flipR4Coords (s : Finset (Fin dim)) (x : R4) : R4 :=
  fun i => if i ∈ s then -(x i) else x i

theorem flipR4Coords_insert
    (s : Finset (Fin dim)) (i : Fin dim) (hi : i ∉ s)
    (x : R4) :
    flipR4Coords (insert i s) x =
      Function.update (flipR4Coords s x) i
        (-(flipR4Coords s x i)) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [flipR4Coords, hi]
  · simp [flipR4Coords, hji]

/-- Membership in `𝓔` gives invariance under any set of Euclidean
coordinate sign flips. -/
theorem MemEClassR4.flipR4Coords_invariant
    {f : R4 → ℝ} (hf : MemEClassR4 f)
    (s : Finset (Fin dim)) (x : R4) :
    f (flipR4Coords s x) = f x := by
  induction s using Finset.induction with
  | empty =>
      have harg : flipR4Coords ∅ x = x := by
        funext i
        simp [flipR4Coords]
      rw [harg]
  | @insert i s hi ih =>
      rw [flipR4Coords_insert s i hi]
      exact (hf.even_coord i (flipR4Coords s x)).trans ih

/-- In particular, a cutoff in `𝓔` is invariant under total negation. -/
theorem MemEClassR4.neg_invariant
    {f : R4 → ℝ} (hf : MemEClassR4 f) (x : R4) :
    f (-x) = f x := by
  have h := hf.flipR4Coords_invariant Finset.univ x
  have harg : flipR4Coords Finset.univ x = -x := by
    funext i
    simp [flipR4Coords]
  rw [harg] at h
  exact h

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## Strict positivity near the origin -/

/-- A normalized nonnegative cutoff is nonzero somewhere. -/
theorem exists_cutoff_ne_zero :
    ∃ x : R4, ρ x ≠ 0 := by
  by_contra h
  push Not at h
  have hzero : (∫ x : R4, ρ x) = 0 := by
    simp_rw [h]
    simp
  linarith [ρ.integral_one]

/-- The autocorrelation covariance is strictly positive at the origin. -/
theorem eta_zero_pos :
    0 < ρ.eta 0 := by
  obtain ⟨x, hx⟩ := ρ.exists_cutoff_ne_zero
  have hcontinuous :
      Continuous fun y : R4 => ρ y * ρ (0 - y) :=
    ρ.continuous.mul
      (ρ.continuous.comp (continuous_const.sub continuous_id))
  have hnonneg :
      ∀ y : R4, 0 ≤ ρ y * ρ (0 - y) :=
    fun y => mul_nonneg (ρ.nonneg y) (ρ.nonneg (0 - y))
  have hnonzero : ρ x * ρ (0 - x) ≠ 0 := by
    have hneg := ρ.memE.neg_invariant x
    simpa [hneg] using mul_ne_zero hx hx
  change 0 < ∫ y : R4, ρ y * ρ (0 - y)
  exact integral_pos_of_integrable_nonneg_nonzero
    hcontinuous (ρ.integrable_eta_integrand 0) hnonneg hnonzero

/-- The cutoff covariance is strictly positive on a ball about zero. -/
theorem exists_eta_pos_ball :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : R4, ‖x‖ < δ → 0 < ρ.eta x := by
  have hzero := ρ.eta_zero_pos
  have hcontinuousAt : ContinuousAt ρ.eta 0 :=
    ρ.continuous_eta.continuousAt
  obtain ⟨δ, hδ, hclose⟩ :=
    Metric.continuousAt_iff.mp hcontinuousAt
      (ρ.eta 0 / 2) (half_pos hzero)
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have hdist := hclose (by simpa [dist_zero_right] using hx)
  rw [Real.dist_eq] at hdist
  have hlower := (abs_lt.mp hdist).1
  linarith

/-! ## Explicit support geometry -/

/-- Every nonzero covariance point lies in the open radius-`2R` ball. -/
theorem support_eta_subset_ball_two_radius :
    Function.support ρ.eta ⊆ Metric.ball 0 (2 * ρ.radius) := by
  intro x hx
  have hex : ∃ y : R4, ρ y * ρ (x - y) ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    unfold eta
    simp only [h, integral_zero]
  obtain ⟨y, hy⟩ := hex
  have hy₁ := (mul_ne_zero_iff.mp hy).1
  have hy₂ := (mul_ne_zero_iff.mp hy).2
  have hyr : ‖y‖ < ρ.radius := by
    simpa [Metric.mem_ball, dist_zero_right] using ρ.support_subset hy₁
  have hxyr : ‖x - y‖ < ρ.radius := by
    simpa [Metric.mem_ball, dist_zero_right] using ρ.support_subset hy₂
  rw [Metric.mem_ball, dist_zero_right]
  calc
    ‖x‖ = ‖y + (x - y)‖ := by
      congr 1
      abel
    _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
    _ < 2 * ρ.radius := by linarith

/-- The topological support of `η` lies in the corresponding closed ball. -/
theorem tsupport_eta_subset_closedBall_two_radius :
    tsupport ρ.eta ⊆ Metric.closedBall 0 (2 * ρ.radius) :=
  closure_minimal
    (ρ.support_eta_subset_ball_two_radius.trans
      Metric.ball_subset_closedBall)
    Metric.isClosed_closedBall

/-! ## A named cutoff-dependent positive majorant -/

/-- A chosen radius on which the original covariance is positive.  This
constant intentionally depends on `ρ`. -/
noncomputable def etaPosRadius : ℝ :=
  Classical.choose ρ.exists_eta_pos_ball

theorem etaPosRadius_pos :
    0 < ρ.etaPosRadius :=
  (Classical.choose_spec ρ.exists_eta_pos_ball).1

theorem eta_pos_of_norm_lt_etaPosRadius
    {x : R4} (hx : ‖x‖ < ρ.etaPosRadius) :
    0 < ρ.eta x :=
  (Classical.choose_spec ρ.exists_eta_pos_ball).2 x hx

/-- A dilation large enough to make its covariance positive throughout
the full topological support of the original covariance. -/
noncomputable def auxiliaryScale : ℝ :=
  4 * ρ.radius / ρ.etaPosRadius

theorem auxiliaryScale_pos :
    0 < ρ.auxiliaryScale := by
  unfold auxiliaryScale
  exact div_pos (mul_pos (by norm_num) ρ.radius_pos)
    ρ.etaPosRadius_pos

/-- The named auxiliary cutoff used in derivative majorants. -/
noncomputable def auxiliaryCutoff : SmoothCutoff :=
  ρ.dilate ρ.auxiliaryScale ρ.auxiliaryScale_pos

theorem auxiliaryScale_mul_etaPosRadius :
    ρ.auxiliaryScale * ρ.etaPosRadius =
      4 * ρ.radius := by
  unfold auxiliaryScale
  field_simp [ρ.etaPosRadius_pos.ne']

/-- Points in `tsupport η` enter the positivity ball after the named
auxiliary dilation. -/
theorem norm_inv_auxiliaryScale_smul_lt_etaPosRadius_of_mem_tsupport
    {x : R4} (hx : x ∈ tsupport ρ.eta) :
    ‖ρ.auxiliaryScale⁻¹ • x‖ < ρ.etaPosRadius := by
  have hnorm : ‖x‖ ≤ 2 * ρ.radius := by
    have hclosed :=
      ρ.tsupport_eta_subset_closedBall_two_radius hx
    simpa [Metric.mem_closedBall, dist_zero_right] using hclosed
  have hxlt :
      ‖x‖ < ρ.auxiliaryScale * ρ.etaPosRadius := by
    rw [ρ.auxiliaryScale_mul_etaPosRadius]
    linarith [ρ.radius_pos]
  have hscaled :=
    mul_lt_mul_of_pos_left hxlt
      (inv_pos.mpr ρ.auxiliaryScale_pos)
  calc
    ‖ρ.auxiliaryScale⁻¹ • x‖ =
        ρ.auxiliaryScale⁻¹ * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos ρ.auxiliaryScale_pos]
    _ < ρ.auxiliaryScale⁻¹ *
        (ρ.auxiliaryScale * ρ.etaPosRadius) :=
      hscaled
    _ = ρ.etaPosRadius := by
      field_simp [ρ.auxiliaryScale_pos.ne']

/-- The auxiliary covariance is strictly positive wherever any derivative
of the original compactly supported covariance can be nonzero. -/
theorem auxiliaryCutoff_eta_pos_on_tsupport
    {x : R4} (hx : x ∈ tsupport ρ.eta) :
    0 < ρ.auxiliaryCutoff.eta x := by
  change
    0 <
      (ρ.dilate ρ.auxiliaryScale
        ρ.auxiliaryScale_pos).eta x
  rw [ρ.eta_dilate]
  exact mul_pos
    (pow_pos (inv_pos.mpr ρ.auxiliaryScale_pos) _)
    (ρ.eta_pos_of_norm_lt_etaPosRadius
      (ρ.norm_inv_auxiliaryScale_smul_lt_etaPosRadius_of_mem_tsupport hx))

end SmoothCutoff

end

end Anderson4D
