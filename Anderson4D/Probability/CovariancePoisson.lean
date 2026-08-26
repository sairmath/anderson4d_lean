import Anderson4D.Continuum.CovariancePoissonDeterministic
import Anderson4D.Probability.NoiseRegularity

/-!
# Covariance identity for the random Fourier series

The multidimensional Poisson-summation proof is deterministic and lives
in `CovariancePoissonDeterministic`.  This compatibility module adds only
the final probability-facing covariance corollary, preserving the
original import path and public API.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace NoiseModel

/-- **Headline covariance identity (paper (2.3)).**

The Lebesgue-normalized random Fourier series, including its
half-density `(2π)⁻²`, has exactly the periodized cutoff covariance
used by `detIntegrand` and the Wick-expansion layer. -/
theorem integral_xiEps_mul_eq_etaEpsT4
    (M : NoiseModel) (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) (x y : T4) :
    ∫ ω, M.xiEps ρ ε ω x * M.xiEps ρ ε ω y
        ∂(volume : Measure M.Ω) =
      ρ.etaEpsT4 ε (x - y) := by
  rw [
    M.integral_xiEps_mul_eq_fourierCovarianceT4
      ρ hε x y,
    fourierCovarianceT4_eq_etaEpsT4
      ρ hε (x - y)]

end NoiseModel

end

end Anderson4D
