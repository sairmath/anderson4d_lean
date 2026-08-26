import Anderson4D.Main.GaussianLimit

/-!
# The realified Gaussian quadratic form

This file identifies the matrix quadratic form of `limitCovMatrix` with
the scalar variance `limitVar` used in the characteristic-function
statement of the main theorem.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

/-- The real covariance matrix has exactly the scalar quadratic form
specified by `limitVar`. -/
theorem realifiedLinearCoeff_quadratic
    (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) :
    realifiedLinearCoeff c ⬝ᵥ
        (limitCovMatrix lam modes).mulVec (realifiedLinearCoeff c) =
      limitVar lam modes c := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp only [realifiedLinearCoeff, limitCovMatrix, limitVar,
    limitPseudoCov, limitConjCov, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_sum,
    Complex.conj_re, Complex.conj_im, neg_mul, mul_neg]
  simp_rw [← Finset.sum_add_distrib]
  simp only [Finset.mul_sum]
  simp only [← Finset.sum_neg_distrib]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Positive semidefiniteness of the real covariance matrix implies the
nonnegativity of every scalar variance used by the main theorem. -/
theorem limitVar_nonneg_of_posSemidef
    (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4)
    (hPSD : (limitCovMatrix lam modes).PosSemidef)
    (c : Fin s → ℂ) :
    0 ≤ limitVar lam modes c := by
  rw [← realifiedLinearCoeff_quadratic lam modes c]
  simpa using
    hPSD.dotProduct_mulVec_nonneg (realifiedLinearCoeff c)

/-- Characteristic function of the explicit limit evaluated at the
real-linear coefficient vector corresponding to `Re ∑ⱼ cⱼ Zⱼ`. -/
theorem charFun_gaussianLimitLaw_realifiedLinearCoeff
    (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4)
    (hlam : lam ^ 2 < 2 * Real.pi ^ 2)
    (hPSD : (limitCovMatrix lam modes).PosSemidef)
    (c : Fin s → ℂ) :
    charFun (gaussianLimitLaw lam modes :
        MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin s × Bool)))
        (WithLp.toLp 2 (realifiedLinearCoeff c)) =
      Complex.exp (-((limitVar lam modes c : ℂ) / 2)) := by
  rw [charFun_gaussianLimitLaw lam modes hlam hPSD]
  rw [realifiedLinearCoeff_quadratic]
  congr 1
  ring

end

end Anderson4D
