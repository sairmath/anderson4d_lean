import Anderson4D.ForMathlib.WickRecursion
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Isserlis' theorem: analytic reduction

Mathlib already identifies mixed moments with iterated Fréchet derivatives
of a characteristic function.  For a centered Gaussian measure its
characteristic function is the exponential of the negative covariance
quadratic form.  This file packages those two facts in the exact form needed
for the finite-dimensional Isserlis induction.

The remaining algebraic step is to differentiate that quadratic exponential
and identify the result with `wickPairingSum`; keeping it separate makes the
probabilistic transport and the finite pairing induction independently
auditable.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory Complex
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- A Gaussian measure has moments of every finite order, in the precise
form expected by the characteristic-function differentiation theorem. -/
theorem gaussian_memLp_id (μ : Measure E) [IsGaussian μ] (n : ℕ) :
    MemLp id n μ :=
  IsGaussian.memLp_id μ n (by simp)

/-- Mixed inner-product moments are the iterated Fréchet derivatives of the
Gaussian characteristic function at the origin. -/
theorem iteratedFDeriv_charFun_gaussian_zero
    (μ : Measure E) [IsGaussian μ] (n : ℕ) (x : Fin n → E) :
    iteratedFDeriv ℝ n (charFun μ) 0 x =
      I ^ n * ((∫ y, ∏ i, ⟪y, x i⟫ ∂μ : ℝ) : ℂ) := by
  calc
    iteratedFDeriv ℝ n (charFun μ) 0 x =
        I ^ n *
          ∫ y, (∏ i, ⟪y, x i⟫) *
            Complex.exp (⟪y, (0 : E)⟫ * I) ∂μ :=
      MeasureTheory.iteratedFDeriv_charFun
        (gaussian_memLp_id μ n) x
    _ = I ^ n * ∫ y, ((∏ i, ⟪y, x i⟫ : ℝ) : ℂ) ∂μ := by
      simp
    _ = I ^ n * ((∫ y, ∏ i, ⟪y, x i⟫ ∂μ : ℝ) : ℂ) := by
      congr 1
      exact integral_complex_ofReal

/-- Characteristic function of a centered Gaussian measure, written only in
terms of its covariance bilinear form. -/
theorem charFun_centeredGaussian
    (μ : Measure E) [IsGaussian μ] (hμ : ∫ y, y ∂μ = 0) (t : E) :
    charFun μ t =
      Complex.exp (-((covarianceBilin μ t t : ℝ) : ℂ) / 2) := by
  calc
    charFun μ t =
        Complex.exp
          (⟪t, (∫ y, y ∂μ)⟫ * I -
            ((covarianceBilin μ t t : ℝ) : ℂ) / 2) :=
      IsGaussian.charFun_eq' t
    _ = Complex.exp (-((covarianceBilin μ t t : ℝ) : ℂ) / 2) := by
      rw [hμ]
      simp
      congr 1
      ring

/-- Exact analytic reduction of Isserlis: the mixed moment is obtained by
differentiating the exponential covariance quadratic form.  No moment or
measurability hypothesis remains beyond Gaussianity. -/
theorem iteratedFDeriv_covarianceExp_zero
    (μ : Measure E) [IsGaussian μ] (hμ : ∫ y, y ∂μ = 0)
    (n : ℕ) (x : Fin n → E) :
    iteratedFDeriv ℝ n
        (fun t : E =>
          Complex.exp (-((covarianceBilin μ t t : ℝ) : ℂ) / 2))
        0 x =
      I ^ n * ((∫ y, ∏ i, ⟪y, x i⟫ ∂μ : ℝ) : ℂ) := by
  have hfun :
      (fun t : E =>
        Complex.exp (-((covarianceBilin μ t t : ℝ) : ℂ) / 2)) =
        charFun μ := by
    funext t
    exact (charFun_centeredGaussian μ hμ t).symm
  rw [hfun, iteratedFDeriv_charFun_gaussian_zero]

end

end Anderson4D
