import Anderson4D.Main.External
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The finite-dimensional Gaussian limit law

This file implements node D-limit at the statement/construction level.
A complex family of `s` Fourier modes is realified as the Euclidean
space indexed by `Fin s × Bool`, with `false` denoting the real
coordinate and `true` the imaginary coordinate.  The covariance and
pseudo-covariance prescribed by paper (1.3), (3.25), and (3.28) are
expanded into the four real covariance blocks.

`gaussianLimitLaw` is total: outside `λ² < 2π²` it is the Dirac mass at
zero.  Inside that range it is mathlib's multivariate Gaussian for the
explicit matrix below.  Positive semidefiniteness follows from the Gram
form of the four-point kernel.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

/-- The scalar multiplying the four-point covariance in paper (1.3). -/
def limitPrefactor (lam : ℝ) : ℝ :=
  2 * Real.pi ^ 2 / (2 * Real.pi ^ 2 - lam ^ 2)

/-- Complex pseudo-covariance `E[Zᵢ Zⱼ]` of the proposed limit. -/
def limitPseudoCov (lam : ℝ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (i j : Fin s) : ℂ :=
  (limitPrefactor lam : ℂ) *
    fourPointHCoeff
      (modes i).1 (modes i).2 (modes j).1 (modes j).2

/-- Complex covariance `E[Zᵢ conj Zⱼ]`, obtained by adjoining the
conjugate (negated) mode. -/
def limitConjCov (lam : ℝ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (i j : Fin s) : ℂ :=
  (limitPrefactor lam : ℂ) *
    fourPointHCoeff
      (modes i).1 (modes i).2 (-(modes j).1) (-(modes j).2)

/-- Real covariance matrix of the realification `(Re Zᵢ, Im Zᵢ)`.
For `Pᵢⱼ = E[ZᵢZⱼ]` and `Qᵢⱼ = E[Zᵢ conj Zⱼ]`, the four blocks are

* `E[Re Zᵢ Re Zⱼ] = Re(Pᵢⱼ + Qᵢⱼ)/2`,
* `E[Re Zᵢ Im Zⱼ] = Im(Pᵢⱼ - Qᵢⱼ)/2`,
* `E[Im Zᵢ Re Zⱼ] = Im(Pᵢⱼ + Qᵢⱼ)/2`,
* `E[Im Zᵢ Im Zⱼ] = Re(Qᵢⱼ - Pᵢⱼ)/2`.
-/
def limitCovMatrix (lam : ℝ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) :
    Matrix (Fin s × Bool) (Fin s × Bool) ℝ :=
  fun p q =>
    let P := limitPseudoCov lam modes p.1 q.1
    let Q := limitConjCov lam modes p.1 q.1
    match p.2, q.2 with
    | false, false => (P + Q).re / 2
    | false, true => (P - Q).im / 2
    | true, false => (P + Q).im / 2
    | true, true => (Q - P).re / 2

/-- **Limit variance quadratic form** (node D-limit): the variance of
`Re ∑ⱼ cⱼ Zⱼ`, expressed directly through covariance and
pseudo-covariance. -/
def limitVar (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) : ℝ :=
  (limitPrefactor lam / 2) *
    ((∑ j, ∑ k, c j * c k *
        fourPointHCoeff
          (modes j).1 (modes j).2 (modes k).1 (modes k).2).re +
      (∑ j, ∑ k, c j * (starRingEnd ℂ) (c k) *
        fourPointHCoeff
          (modes j).1 (modes j).2
          (-(modes k).1) (-(modes k).2)).re)

/-- Coefficients of the real linear functional
`z ↦ Re ∑ⱼ cⱼ zⱼ` on the realified mode space. -/
def realifiedLinearCoeff {s : ℕ} (c : Fin s → ℂ) :
    Fin s × Bool → ℝ
  | (j, false) => (c j).re
  | (j, true) => -(c j).im

/-- The explicit centered Gaussian law on the realified mode space.
Outside the subcritical denominator range it is junk-totalized to
`δ₀`, as fixed in DESIGN §2.2 and §5.7. -/
def gaussianLimitLaw (lam : ℝ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin s × Bool)) :=
  if _h : lam ^ 2 < 2 * Real.pi ^ 2 then
    ⟨multivariateGaussian 0 (limitCovMatrix lam modes),
      inferInstance⟩
  else
    ⟨Measure.dirac 0, Measure.dirac.isProbabilityMeasure⟩

theorem gaussianLimitLaw_of_sq_lt (lam : ℝ) {s : ℕ}
    (modes : Fin s → Z4 × Z4)
    (hlam : lam ^ 2 < 2 * Real.pi ^ 2) :
    (gaussianLimitLaw lam modes : Measure
      (EuclideanSpace ℝ (Fin s × Bool))) =
      multivariateGaussian 0 (limitCovMatrix lam modes) := by
  simp [gaussianLimitLaw, hlam]

theorem gaussianLimitLaw_of_sq_not_lt (lam : ℝ) {s : ℕ}
    (modes : Fin s → Z4 × Z4)
    (hlam : ¬lam ^ 2 < 2 * Real.pi ^ 2) :
    (gaussianLimitLaw lam modes : Measure
      (EuclideanSpace ℝ (Fin s × Bool))) =
      Measure.dirac 0 := by
  simp [gaussianLimitLaw, hlam]

/-- Characteristic function of the explicit limit law, conditional only
on the analytic PSD obligation for its covariance matrix. -/
theorem charFun_gaussianLimitLaw
    (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4)
    (hlam : lam ^ 2 < 2 * Real.pi ^ 2)
    (hPSD : (limitCovMatrix lam modes).PosSemidef)
    (t : EuclideanSpace ℝ (Fin s × Bool)) :
    charFun (gaussianLimitLaw lam modes : Measure
      (EuclideanSpace ℝ (Fin s × Bool))) t =
      Complex.exp
        (-((((t : Fin s × Bool → ℝ) ⬝ᵥ
          (limitCovMatrix lam modes).mulVec
            (t : Fin s × Bool → ℝ)) : ℝ) : ℂ) / 2) := by
  rw [gaussianLimitLaw_of_sq_lt lam modes hlam,
    charFun_multivariateGaussian hPSD]
  simp
  congr 1
  ring

/-- Coordinate covariance of the explicit limit law, again separated
cleanly from the four-point-kernel PSD proof. -/
theorem covariance_gaussianLimitLaw
    (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4)
    (hlam : lam ^ 2 < 2 * Real.pi ^ 2)
    (hPSD : (limitCovMatrix lam modes).PosSemidef)
    (p q : Fin s × Bool) :
    cov[fun x : EuclideanSpace ℝ (Fin s × Bool) ↦ x p,
        fun x : EuclideanSpace ℝ (Fin s × Bool) ↦ x q;
        (gaussianLimitLaw lam modes :
          Measure (EuclideanSpace ℝ (Fin s × Bool)))] =
      limitCovMatrix lam modes p q := by
  rw [gaussianLimitLaw_of_sq_lt lam modes hlam]
  exact covariance_eval_multivariateGaussian hPSD p q

end

end Anderson4D
