import Anderson4D.Continuum.CutoffFourier
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Rapid Fourier decay of the deterministic cutoff

This module is the deterministic, layer-L2 home of the Schwartz decay
used both by the mollified-noise construction and by the R-324
frequency-routing argument.  Keeping it above the probability layer
prevents the deterministic parametrix from depending on random-noise
infrastructure.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

/-- The Euclidean-norm copy of the four-dimensional frequency space. -/
abbrev EuclideanR4 := EuclideanSpace ℝ (Fin dim)

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- A smooth compactly supported cutoff, transported to Euclidean space
and complexified, is a Schwartz function. -/
def euclideanSchwartz : SchwartzMap EuclideanR4 ℂ := by
  let e : EuclideanR4 ≃L[ℝ] R4 :=
    EuclideanSpace.equiv (Fin dim) ℝ
  let f : EuclideanR4 → ℝ := fun x => ρ (e x)
  have hf_compact : HasCompactSupport f := by
    exact ρ.hasCompactSupport.comp_homeomorph e.toHomeomorph
  have hf_smooth :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
    exact (contDiff_infty.mpr ρ.smooth).comp e.contDiff
  exact
    (hf_compact.comp_left
      (by simp : Complex.ofReal (0 : ℝ) = 0)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hf_smooth)

@[simp]
theorem euclideanSchwartz_apply (x : EuclideanR4) :
    ρ.euclideanSchwartz x =
      (ρ ((EuclideanSpace.equiv (Fin dim) ℝ) x) : ℂ) :=
  rfl

/-- Frequency conversion accounting for mathlib's `2π` Fourier
normalization. -/
def euclideanFrequency (ξ : R4) : EuclideanR4 :=
  WithLp.toLp 2 fun i => ξ i / (2 * Real.pi)

@[simp]
theorem euclideanFrequency_apply (ξ : R4) (i : Fin dim) :
    euclideanFrequency ξ i = ξ i / (2 * Real.pi) :=
  rfl

/-- The project's unnormalized Fourier transform is exactly mathlib's
Schwartz Fourier transform sampled at frequency `ξ/(2π)`. -/
theorem fourierR4_eq_euclideanSchwartz_fourier (ξ : R4) :
    fourierR4 ρ ξ =
      𝓕 ρ.euclideanSchwartz (euclideanFrequency ξ) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  rw [← (PiLp.volume_preserving_toLp (Fin dim)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  unfold fourierR4
  apply integral_congr_ae
  filter_upwards with x
  simp only [Real.fourierChar_apply, Circle.smul_def]
  simp only [euclideanFrequency, euclideanSchwartz_apply,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  congr 1
  congr 1
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsum :
      (∑ i,
          (ξ i : ℂ) / (2 * (Real.pi : ℂ)) *
            (x i : ℂ)) =
        (∑ i, (x i : ℂ) * (ξ i : ℂ)) *
          (Real.pi : ℂ)⁻¹ * (1 / 2) := by
    calc
      _ = ∑ i, (x i : ℂ) * (ξ i : ℂ) *
          (Real.pi : ℂ)⁻¹ * (1 / 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        field_simp [hpi]
      _ = _ := by
        rw [Finset.sum_mul, Finset.sum_mul]
  rw [hsum]
  field_simp [hpi]

/-- Arbitrary-order rapid Fourier decay in the project's normalization. -/
theorem exists_fourierR4_one_add_norm_bound_nat (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : R4,
      (1 + ‖euclideanFrequency ξ‖) ^ N *
          ‖fourierR4 ρ ξ‖ ≤ C := by
  let f := 𝓕 ρ.euclideanSchwartz
  let C0 : ℝ := (SchwartzMap.seminorm ℂ 0 0) f
  let CN : ℝ := (SchwartzMap.seminorm ℂ N 0) f
  let C : ℝ := max (2 ^ (N - 1) * (C0 + CN)) 1
  refine
    ⟨C, lt_of_lt_of_le zero_lt_one
      (le_max_right _ _), fun ξ => ?_⟩
  have h0 :
      ‖f (euclideanFrequency ξ)‖ ≤ C0 := by
    simpa [f, C0] using
      SchwartzMap.norm_pow_mul_le_seminorm
        ℂ f 0 (euclideanFrequency ξ)
  have hN :
      ‖euclideanFrequency ξ‖ ^ N *
          ‖f (euclideanFrequency ξ)‖ ≤ CN := by
    simpa [CN] using
      SchwartzMap.norm_pow_mul_le_seminorm
        ℂ f N (euclideanFrequency ξ)
  rw [fourierR4_eq_euclideanSchwartz_fourier]
  change
    (1 + ‖euclideanFrequency ξ‖) ^ N *
        ‖f (euclideanFrequency ξ)‖ ≤ C
  calc
    _ ≤ (2 : ℝ) ^ (N - 1) *
        (1 ^ N + ‖euclideanFrequency ξ‖ ^ N) *
          ‖f (euclideanFrequency ξ)‖ := by
      gcongr
      exact add_pow_le (by positivity)
        (norm_nonneg _) N
    _ = 2 ^ (N - 1) *
        (‖f (euclideanFrequency ξ)‖ +
          ‖euclideanFrequency ξ‖ ^ N *
            ‖f (euclideanFrequency ξ)‖) := by
      ring
    _ ≤ 2 ^ (N - 1) * (C0 + CN) := by
      gcongr
    _ ≤ C := le_max_left _ _

/-- The eighth-order specialization used throughout the project. -/
theorem exists_fourierR4_one_add_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : R4,
      (1 + ‖euclideanFrequency ξ‖) ^ 8 *
          ‖fourierR4 ρ ξ‖ ≤ C :=
  ρ.exists_fourierR4_one_add_norm_bound_nat 8

end SmoothCutoff

end

end Anderson4D
