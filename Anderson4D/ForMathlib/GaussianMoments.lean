import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Exact moments of a centered real Gaussian

Mathlib records the moment-generating function of `gaussianReal`, but does
not currently expose its moments in all degrees.  This file proves the
two-step recurrence and the exact even/odd formulas.  It is the univariate
analytic input for the project's self-contained Isserlis induction.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

private lemma iteratedDeriv_linear_mul_at_zero
    (v : ℝ) (F : ℝ → ℝ) (n : ℕ)
    (hF : ContDiffAt ℝ n F 0) :
    iteratedDeriv n (fun t => (v * t) * F t) 0 =
      if n = 0 then 0 else (n : ℝ) * v * iteratedDeriv (n - 1) F 0 := by
  cases n with
  | zero => simp
  | succ n =>
      change iteratedDeriv (n + 1) ((fun t : ℝ => v * t) * F) 0 = _
      rw [iteratedDeriv_mul (n := n + 1) (by fun_prop) hF]
      rw [Finset.sum_eq_single 1]
      · simp
      · intro b hb hb1
        simp only [Finset.mem_range] at hb
        have hderiv :
            iteratedDeriv b (fun t : ℝ => v * t) 0 = 0 := by
          rw [show (fun t : ℝ => v * t) =
              fun t => v * (fun s : ℝ => s) t by rfl,
            iteratedDeriv_const_mul_field]
          simp [iteratedDeriv_fun_id_zero, hb1]
        simp [hderiv]
      · simp

private lemma deriv_centeredGaussianMGF (v : ℝ≥0) :
    deriv (fun t : ℝ => Real.exp ((v : ℝ) * t ^ 2 / 2)) =
      fun t => ((v : ℝ) * t) * Real.exp ((v : ℝ) * t ^ 2 / 2) := by
  funext t
  rw [_root_.deriv_exp (by fun_prop)]
  rw [deriv_div_const, deriv_fun_mul (by fun_prop) (by fun_prop),
    deriv_const', zero_mul, zero_add, deriv_fun_pow (by fun_prop) 2,
    deriv_id'', mul_one]
  ring

/-- The `n`-th raw moment of the centered Gaussian with variance `v`. -/
def centeredGaussianMoment (v : ℝ≥0) (n : ℕ) : ℝ :=
  ∫ x, x ^ n ∂gaussianReal 0 v

/-- Gaussian integration-by-parts recurrence in moment form:
`E[X^(n+2)] = (n+1) v E[X^n]`. -/
theorem centeredGaussianMoment_add_two (v : ℝ≥0) (n : ℕ) :
    centeredGaussianMoment v (n + 2) =
      (n + 1 : ℝ) * v * centeredGaussianMoment v n := by
  have hmgf :
      mgf (fun x : ℝ => x) (gaussianReal 0 v) =
        fun t => Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    simpa using (mgf_fun_id_gaussianReal (μ := (0 : ℝ)) (v := v))
  have hmom (k : ℕ) :
      iteratedDeriv k
          (fun t => Real.exp ((v : ℝ) * t ^ 2 / 2)) 0 =
        centeredGaussianMoment v k := by
    rw [← hmgf, iteratedDeriv_mgf_zero]
    · rfl
    · simp
  calc
    centeredGaussianMoment v (n + 2) =
        iteratedDeriv (n + 2)
          (fun t => Real.exp ((v : ℝ) * t ^ 2 / 2)) 0 :=
      (hmom (n + 2)).symm
    _ = iteratedDeriv (n + 1)
          (deriv (fun t => Real.exp ((v : ℝ) * t ^ 2 / 2))) 0 := by
      rw [show n + 2 = (n + 1) + 1 by omega, iteratedDeriv_succ']
    _ = iteratedDeriv (n + 1)
          (fun t => ((v : ℝ) * t) *
            Real.exp ((v : ℝ) * t ^ 2 / 2)) 0 := by
      rw [deriv_centeredGaussianMGF v]
    _ = (n + 1 : ℝ) * v *
          iteratedDeriv n
            (fun t => Real.exp ((v : ℝ) * t ^ 2 / 2)) 0 := by
      rw [iteratedDeriv_linear_mul_at_zero]
      · simp
      · fun_prop
    _ = (n + 1 : ℝ) * v * centeredGaussianMoment v n := by
      rw [hmom n]

/-- Number of pairings of a `2q`-element labeled set, defined by the
standard recurrence `p(q+1) = (2q+1)p(q)`. -/
def gaussianPairingCount : ℕ → ℕ
  | 0 => 1
  | q + 1 => (2 * q + 1) * gaussianPairingCount q

/-- Exact even moments of a centered Gaussian. -/
theorem centeredGaussianMoment_even (v : ℝ≥0) (q : ℕ) :
    centeredGaussianMoment v (2 * q) =
      (gaussianPairingCount q : ℝ) * (v : ℝ) ^ q := by
  induction q with
  | zero =>
      simp [centeredGaussianMoment, gaussianPairingCount]
  | succ q ih =>
      rw [show 2 * (q + 1) = 2 * q + 2 by omega,
        centeredGaussianMoment_add_two v (2 * q), ih]
      simp only [gaussianPairingCount]
      push_cast
      ring

/-- Every odd moment of a centered Gaussian vanishes. -/
theorem centeredGaussianMoment_odd (v : ℝ≥0) (q : ℕ) :
    centeredGaussianMoment v (2 * q + 1) = 0 := by
  induction q with
  | zero =>
      simp [centeredGaussianMoment]
  | succ q ih =>
      rw [show 2 * (q + 1) + 1 = (2 * q + 1) + 2 by omega,
        centeredGaussianMoment_add_two v (2 * q + 1), ih]
      ring

end

end Anderson4D
