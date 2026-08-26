import Anderson4D.Continuum.CutoffFourierSummability

/-!
# Deterministic Fourier covariance of the mollified noise

This module records the normalization and absolutely convergent Fourier
series underlying the cutoff covariance.  Although the normalization is
used to construct white noise, every declaration here is deterministic
and belongs below the probability layer.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace NoiseModel

/-- Fourier half-density converting the probability-Haar character basis
to Lebesgue-normalized white noise on `[−π,π]⁴`. -/
def whiteNoiseFourierScale : ℝ :=
  (2 * Real.pi) ^ (-2 : ℤ)

theorem whiteNoiseFourierScale_pos : 0 < whiteNoiseFourierScale := by
  unfold whiteNoiseFourierScale
  positivity

/-- The deterministic Fourier-series covariance associated with the
cutoff multiplier, including the Lebesgue white-noise half-density
squared. -/
def fourierCovarianceT4
    (ρ : SmoothCutoff) (ε : ℝ) (z : T4) : ℝ :=
  (∑' k : Z4,
    (whiteNoiseFourierScale : ℂ) ^ 2 *
      ((‖ρ.symbol ε k‖ ^ 2 : ℝ) : ℂ) *
        charT4 k z).re

end NoiseModel

end

end Anderson4D
