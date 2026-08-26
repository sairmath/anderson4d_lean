import Mathlib.Analysis.Fourier.AddCircle

/-!
# Periodic one-dimensional Fourier integration by parts

This module isolates the boundary cancellation used by the eighth-order
relative-translation argument.  It works on the paper interval
`[-π, π]`, whose length is the torus period `2π`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- One integration by parts on `[-π, π]` for a periodic function.

Because the interval length is exactly `2π`, the normalized Fourier
coefficient gains the scalar `(I n)⁻¹` with no additional normalization
factor. -/
theorem fourierCoeffOn_negPi_pi_eq_inv_I_mul_deriv
    {f f' : ℝ → ℂ} {n : ℤ}
    (hn : n ≠ 0)
    (hf :
      ∀ x, x ∈ Set.uIcc (-Real.pi) Real.pi →
        HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume (-Real.pi) Real.pi)
    (hperiod : f Real.pi = f (-Real.pi)) :
    fourierCoeffOn
        (neg_lt_self Real.pi_pos) f n =
      (Complex.I * (n : ℂ))⁻¹ *
        fourierCoeffOn
          (neg_lt_self Real.pi_pos) f' n := by
  rw [
    fourierCoeffOn_of_hasDerivAt
      (neg_lt_self Real.pi_pos)
      hn hf hf',
    hperiod, sub_self, mul_zero, zero_sub]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn
  push_cast
  field_simp
  ring

/-- Norm form of one periodic integration by parts. -/
theorem norm_fourierCoeffOn_negPi_pi_le_inv_abs_mul_deriv
    {f f' : ℝ → ℂ} {n : ℤ}
    (hn : n ≠ 0)
    (hf :
      ∀ x, x ∈ Set.uIcc (-Real.pi) Real.pi →
        HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume (-Real.pi) Real.pi)
    (hperiod : f Real.pi = f (-Real.pi)) :
    ‖fourierCoeffOn
        (neg_lt_self Real.pi_pos) f n‖ ≤
      |(n : ℝ)|⁻¹ *
        ‖fourierCoeffOn
          (neg_lt_self Real.pi_pos) f' n‖ := by
  rw [
    fourierCoeffOn_negPi_pi_eq_inv_I_mul_deriv
      hn hf hf' hperiod,
    norm_mul, norm_inv, norm_mul, Complex.norm_I,
    one_mul, Complex.norm_intCast]

end

end Anderson4D
