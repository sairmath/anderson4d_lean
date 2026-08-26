import Anderson4D.Continuum.Covariance

/-!
# Fourier facts for the smooth cutoff

These are the normalization and reality identities needed by the
white-noise Fourier series.  They are proved directly from the project's
unnormalized Euclidean Fourier convention.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ComplexConjugate

/-- The Fourier transform of a real-valued function has the usual
conjugate symmetry. -/
theorem fourierR4_neg_eq_conj (f : R4 → ℝ) (ξ : R4) :
    fourierR4 f (-ξ) = conj (fourierR4 f ξ) := by
  unfold fourierR4
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  rw [map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
  congr 1
  have hsum :
      (∑ i, x i * ((-ξ) i)) = -(∑ i, x i * ξ i) := by
    simp
  rw [hsum]
  push_cast
  simp only [map_neg, map_mul, map_sum, Complex.conj_I,
    Complex.conj_ofReal]
  ring_nf

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- The mollifier multiplier obeys the reality constraint needed to pair
the modes `k` and `-k`. -/
@[simp] theorem symbol_neg (ε : ℝ) (k : Z4) :
    ρ.symbol ε (-k) = conj (ρ.symbol ε k) := by
  unfold symbol
  rw [← fourierR4_neg_eq_conj]
  congr 1
  funext i
  simp

/-- The zero Fourier mode is one, with the exact normalization inherited
from `∫ρ = 1`. -/
@[simp] theorem symbol_zero (ε : ℝ) :
  ρ.symbol ε 0 = 1 := by
  unfold symbol fourierR4
  simp [integral_complex_ofReal, ρ.integral_one]

/-- Every cutoff multiplier lies in the closed unit disk. -/
theorem norm_symbol_le_one (ε : ℝ) (k : Z4) :
    ‖ρ.symbol ε k‖ ≤ 1 := by
  unfold symbol fourierR4
  calc
    ‖∫ x : R4,
        Complex.exp
            (-Complex.I * (∑ i, x i * (ε * (k i : ℝ)))) *
          (ρ x : ℂ)‖
        ≤ ∫ x : R4,
            ‖Complex.exp
                (-Complex.I * (∑ i, x i * (ε * (k i : ℝ)))) *
              (ρ x : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : R4, ρ x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [norm_mul, Complex.norm_exp]
      have him :
          (-Complex.I *
            (∑ i, x i * (ε * (k i : ℝ))) : ℂ).re = 0 := by
        simp
      rw [him, Real.exp_zero, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg x)]
    _ = 1 := ρ.integral_one

end SmoothCutoff

end

end Anderson4D
