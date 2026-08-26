import Anderson4D.Continuum.Basic

/-!
# Analytic facts about the cutoff covariance

This file derives the elementary analytic input about the cutoff
`ρ` and its Euclidean covariance `η = ρ * ρ` directly from
`SmoothCutoff`.  In particular, compact support is not carried as an
extra hypothesis: it follows from the explicit support-radius field.

These lemmas are the analytic base used by the `n = 1` case and by the
cellwise estimates in paper §5.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- A smooth cutoff is continuous. -/
theorem continuous : Continuous (ρ : R4 → ℝ) :=
  (ρ.smooth 0).continuous

/-- The explicit support-radius field implies compact support. -/
theorem hasCompactSupport : HasCompactSupport (ρ : R4 → ℝ) := by
  show IsCompact (tsupport (ρ : R4 → ℝ))
  refine (isCompact_closedBall (0 : R4) ρ.radius).of_isClosed_subset
    isClosed_closure ?_
  exact closure_minimal
    (ρ.support_subset.trans Metric.ball_subset_closedBall)
    Metric.isClosed_closedBall

/-- Every smooth cutoff is Lebesgue-integrable. -/
theorem integrable : Integrable (ρ : R4 → ℝ) :=
  ρ.continuous.integrable_of_hasCompactSupport ρ.hasCompactSupport

/-- A named positive pointwise bound for the cutoff. -/
theorem exists_pos_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : R4, ρ x ≤ C := by
  obtain ⟨B, hB⟩ :=
    ρ.continuous.bounded_above_of_compact_support ρ.hasCompactSupport
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x => ?_⟩
  calc
    ρ x ≤ |ρ x| := le_abs_self _
    _ = ‖ρ x‖ := rfl
    _ ≤ B := hB x
    _ ≤ max B 1 := le_max_left _ _

/-- The convolution integrand defining `η` is integrable. -/
theorem integrable_eta_integrand (x : R4) :
    Integrable fun y : R4 => ρ y * ρ (x - y) := by
  have hcontinuous :
      Continuous fun y : R4 => ρ y * ρ (x - y) :=
    ρ.continuous.mul
      (ρ.continuous.comp (continuous_const.sub continuous_id))
  exact hcontinuous.integrable_of_hasCompactSupport
    ρ.hasCompactSupport.mul_right

/-- The Euclidean covariance is nonnegative. -/
theorem eta_nonneg (x : R4) : 0 ≤ ρ.eta x := by
  unfold eta
  exact integral_nonneg fun y => mul_nonneg (ρ.nonneg y) (ρ.nonneg (x - y))

/-- The covariance is bounded uniformly by any pointwise cutoff bound. -/
theorem eta_le_of_bound {C : ℝ} (hC : ∀ x : R4, ρ x ≤ C) (x : R4) :
    ρ.eta x ≤ C := by
  unfold eta
  calc
    (∫ y : R4, ρ y * ρ (x - y))
        ≤ ∫ y : R4, ρ y * C := by
          exact integral_mono (ρ.integrable_eta_integrand x)
            (ρ.integrable.mul_const C) fun y =>
              mul_le_mul_of_nonneg_left (hC (x - y)) (ρ.nonneg y)
    _ = C := by rw [integral_mul_const, ρ.integral_one, one_mul]

/-- Consequently `η` admits a positive global upper bound depending only
on the named cutoff. -/
theorem exists_pos_eta_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : R4, ρ.eta x ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := ρ.exists_pos_uniform_bound
  exact ⟨C, hCpos, ρ.eta_le_of_bound hC⟩

end SmoothCutoff

end

end Anderson4D
