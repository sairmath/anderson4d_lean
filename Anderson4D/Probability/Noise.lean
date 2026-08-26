import Anderson4D.Continuum.FourierCovariance

/-!
# The white-noise model (blueprint node I-noise, interface part)

Statements downstream are parameterized by a `NoiseModel`: a probability
space carrying the complex Fourier coefficients `g k` of white noise on
`𝕋⁴`, subject to (i) the reality constraint across `±k`, (ii) the
covariance identities of DESIGN §5.1, and (iii) joint
Gaussianity, characterized Cramér–Wold-style through one-dimensional
real linear combinations (API-light and equivalent to the usual joint
definition). A canonical `NoiseModel`, using two independent real Gaussians
per `{±k}`-orbit and one for the zero mode, is given in
`NoiseConstruction`.

The mollified noise `xiEps` is the only analytically used object
(DESIGN §5.1): a junk-totalized random Fourier series. Its almost-sure
smoothness and covariance `E[ξ_ε(x)ξ_ε(y)] = η_ε(x-y)` are proved in
the corresponding noise and Fourier-covariance modules.

The project characters are orthonormal for probability Haar, whereas
the paper's white noise is normalized against Lebesgue measure of mass
`(2π)⁴`.  Its Fourier series therefore carries the half-density factor
`(2π)⁻²`; the Gaussian coefficients themselves retain variance one.
-/

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory ComplexConjugate

/-- A model of the white-noise Fourier coefficients. The probability space is packaged via
`MeasureSpace` + `IsProbabilityMeasure`. -/
structure NoiseModel where
  /-- Sample space. -/
  Ω : Type
  /-- Measure structure (volume = the probability measure `ℙ`). -/
  [measureSpace : MeasureSpace Ω]
  /-- `ℙ` is a probability measure. -/
  [isProb : IsProbabilityMeasure (volume : Measure Ω)]
  /-- Complex Fourier coefficients of the noise. -/
  g : Z4 → Ω → ℂ
  measurable_g : ∀ k, Measurable (g k)
  /-- Reality of the noise: `g_{-k} = conj (g k)` pointwise. -/
  reality : ∀ k ω, g (-k) ω = conj (g k ω)
  /-- Covariance identity `E[g_k g_l] = 1_{k = -l}` (DESIGN §5.1). -/
  cov_pair : ∀ k l : Z4, ∫ ω, g k ω * g l ω = if k = -l then 1 else 0
  /-- Covariance identity `E[g_k conj (g_l)] = 1_{k = l}`. -/
  cov_conj : ∀ k l : Z4, ∫ ω, g k ω * conj (g l ω) = if k = l then 1 else 0
  /-- Joint (centered) Gaussianity, via real one-dimensional linear
  combinations: every finite real linear combination of real and
  imaginary parts is a centered real Gaussian. -/
  gaussian_lincomb : ∀ (s : Finset Z4) (a b : Z4 → ℝ), ∃ v : NNReal,
    Measure.map (fun ω => ∑ k ∈ s, (a k * (g k ω).re + b k * (g k ω).im))
      (volume : Measure Ω) = gaussianReal 0 v

attribute [instance] NoiseModel.measureSpace NoiseModel.isProb

namespace NoiseModel

variable (M : NoiseModel)

/-- The mollified noise
`ξ_ε(x) = (2π)⁻² ∑_k ρ̂(εk) g_k e_k(x)` as a
junk-totalized random Fourier series (real part taken; the sum is a.s.
real by the reality constraint). -/
def xiEps (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω) (x : T4) : ℝ :=
  whiteNoiseFourierScale *
    (∑' k : Z4, ρ.symbol ε k * M.g k ω * charT4 k x).re

end NoiseModel

end

end Anderson4D
