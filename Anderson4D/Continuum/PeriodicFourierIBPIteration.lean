import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Anderson4D.Continuum.PeriodicFourierIBP

/-!
# Iterated periodic Fourier integration by parts

This file iterates the one-step boundary-free identity on `[-π, π]`.
The hypothesis records exactly the endpoint jets used in the iteration:
orders strictly below the number of integrations by parts.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- Endpoint periodicity of the jets used in `r` integrations by parts. -/
def NegPiPiPeriodicJets (f : ℝ → ℂ) (r : ℕ) : Prop :=
  ∀ j : ℕ, j < r →
    iteratedDeriv j f Real.pi =
      iteratedDeriv j f (-Real.pi)

/-- Exact `r`-fold periodic integration by parts on `[-π, π]`. -/
theorem fourierCoeffOn_negPi_pi_eq_inv_I_pow_mul_iteratedDeriv
    {f : ℝ → ℂ} {n : ℤ}
    (hn : n ≠ 0) (r : ℕ)
    (hf : ContDiff ℝ r f)
    (hperiod : NegPiPiPeriodicJets f r) :
    fourierCoeffOn (neg_lt_self Real.pi_pos) f n =
      ((Complex.I * (n : ℂ))⁻¹) ^ r *
        fourierCoeffOn
          (neg_lt_self Real.pi_pos)
          (iteratedDeriv r f) n := by
  induction r generalizing f with
  | zero =>
      simp [iteratedDeriv_zero]
  | succ r ih =>
      have hdiff : Differentiable ℝ f :=
        hf.differentiable (by simp)
      have hderiv : ContDiff ℝ r (deriv f) :=
        hf.deriv'
      have hinter :
          IntervalIntegrable (deriv f) volume
            (-Real.pi) Real.pi :=
        hderiv.continuous.intervalIntegrable _ _
      have hperiod_zero : f Real.pi = f (-Real.pi) := by
        simpa [NegPiPiPeriodicJets, iteratedDeriv_zero] using
          hperiod 0 (Nat.zero_lt_succ r)
      have hone :
          fourierCoeffOn
              (neg_lt_self Real.pi_pos) f n =
            (Complex.I * (n : ℂ))⁻¹ *
              fourierCoeffOn
                (neg_lt_self Real.pi_pos) (deriv f) n :=
        fourierCoeffOn_negPi_pi_eq_inv_I_mul_deriv
          hn
          (fun x _ => (hdiff x).hasDerivAt)
          hinter hperiod_zero
      have hperiod_deriv :
          NegPiPiPeriodicJets (deriv f) r := by
        intro j hj
        simpa only [iteratedDeriv_succ'] using
          hperiod (j + 1) (Nat.succ_lt_succ hj)
      have hih :=
        ih hderiv hperiod_deriv
      calc
        fourierCoeffOn
            (neg_lt_self Real.pi_pos) f n =
          (Complex.I * (n : ℂ))⁻¹ *
            fourierCoeffOn
              (neg_lt_self Real.pi_pos) (deriv f) n :=
          hone
        _ =
          (Complex.I * (n : ℂ))⁻¹ *
            (((Complex.I * (n : ℂ))⁻¹) ^ r *
              fourierCoeffOn
                (neg_lt_self Real.pi_pos)
                (iteratedDeriv r (deriv f)) n) := by
          rw [hih]
        _ =
          ((Complex.I * (n : ℂ))⁻¹) ^ (r + 1) *
            fourierCoeffOn
              (neg_lt_self Real.pi_pos)
              (iteratedDeriv (r + 1) f) n := by
          rw [iteratedDeriv_succ', pow_succ]
          ring

/-- Norm consequence of exact `r`-fold integration by parts. -/
theorem norm_fourierCoeffOn_negPi_pi_le_inv_abs_pow_mul_iteratedDeriv
    {f : ℝ → ℂ} {n : ℤ}
    (hn : n ≠ 0) (r : ℕ)
    (hf : ContDiff ℝ r f)
    (hperiod : NegPiPiPeriodicJets f r) :
    ‖fourierCoeffOn
        (neg_lt_self Real.pi_pos) f n‖ ≤
      |(n : ℝ)|⁻¹ ^ r *
        ‖fourierCoeffOn
          (neg_lt_self Real.pi_pos)
          (iteratedDeriv r f) n‖ := by
  rw [
    fourierCoeffOn_negPi_pi_eq_inv_I_pow_mul_iteratedDeriv
      hn r hf hperiod,
    norm_mul, norm_pow, norm_inv, norm_mul, Complex.norm_I,
    one_mul, Complex.norm_intCast]

/-- A normalized Fourier coefficient on `[-π, π]` is bounded by the
normalized `L¹` norm on that interval. -/
theorem norm_fourierCoeffOn_negPi_pi_le_average_norm
    (g : ℝ → ℂ) (n : ℤ) :
    ‖fourierCoeffOn
        (neg_lt_self Real.pi_pos) g n‖ ≤
      (2 * Real.pi)⁻¹ *
        ∫ t in -Real.pi..Real.pi, ‖g t‖ := by
  rw [fourierCoeffOn_eq_integral]
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  rw [norm_smul]
  have hint :
      ‖∫ t in -Real.pi..Real.pi,
          fourier (-n)
              (t : AddCircle (Real.pi - -Real.pi)) • g t‖ ≤
        ∫ t in -Real.pi..Real.pi,
          ‖fourier (-n)
              (t : AddCircle (Real.pi - -Real.pi)) • g t‖ :=
    intervalIntegral.norm_integral_le_integral_norm
      (le_of_lt (neg_lt_self Real.pi_pos))
  have hpoint :
      (fun t : ℝ =>
          ‖fourier (-n)
              (t : AddCircle (Real.pi - -Real.pi)) • g t‖) =
        fun t : ℝ => ‖g t‖ := by
    funext t
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
  rw [hpoint] at hint
  have hnorm :
      ‖(1 / (Real.pi - -Real.pi) : ℝ)‖ =
        (2 * Real.pi)⁻¹ := by
    rw [Real.norm_eq_abs]
    have hpos : 0 < 1 / (Real.pi - -Real.pi) := by
      exact one_div_pos.mpr (by linarith [Real.pi_pos])
    rw [abs_of_pos hpos]
    ring
  rw [hnorm]
  exact mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hpi)

/-- The final `L¹` estimate after `r` periodic integrations by parts. -/
theorem norm_fourierCoeffOn_negPi_pi_le_iteratedDeriv_integral
    {f : ℝ → ℂ} {n : ℤ}
    (hn : n ≠ 0) (r : ℕ)
    (hf : ContDiff ℝ r f)
    (hperiod : NegPiPiPeriodicJets f r) :
    ‖fourierCoeffOn
        (neg_lt_self Real.pi_pos) f n‖ ≤
      |(n : ℝ)|⁻¹ ^ r * (2 * Real.pi)⁻¹ *
        ∫ t in -Real.pi..Real.pi,
          ‖iteratedDeriv r f t‖ := by
  calc
    ‖fourierCoeffOn
        (neg_lt_self Real.pi_pos) f n‖ ≤
      |(n : ℝ)|⁻¹ ^ r *
        ‖fourierCoeffOn
          (neg_lt_self Real.pi_pos)
          (iteratedDeriv r f) n‖ :=
      norm_fourierCoeffOn_negPi_pi_le_inv_abs_pow_mul_iteratedDeriv
        hn r hf hperiod
    _ ≤
      |(n : ℝ)|⁻¹ ^ r *
        ((2 * Real.pi)⁻¹ *
          ∫ t in -Real.pi..Real.pi,
            ‖iteratedDeriv r f t‖) :=
      mul_le_mul_of_nonneg_left
        (norm_fourierCoeffOn_negPi_pi_le_average_norm
          (iteratedDeriv r f) n)
        (pow_nonneg (inv_nonneg.mpr (abs_nonneg _)) _)
    _ =
      |(n : ℝ)|⁻¹ ^ r * (2 * Real.pi)⁻¹ *
        ∫ t in -Real.pi..Real.pi,
          ‖iteratedDeriv r f t‖ := by
      ring

/-- Eight-fold periodic integration by parts in the form consumed by the
relative-translation argument. -/
theorem norm_fourierCoeffOn_negPi_pi_le_eighthDeriv_integral
    {f : ℝ → ℂ} {n : ℤ}
    (hn : n ≠ 0)
    (hf : ContDiff ℝ 8 f)
    (hperiod : NegPiPiPeriodicJets f 8) :
    ‖fourierCoeffOn
        (neg_lt_self Real.pi_pos) f n‖ ≤
      |(n : ℝ)|⁻¹ ^ 8 * (2 * Real.pi)⁻¹ *
        ∫ t in -Real.pi..Real.pi,
          ‖iteratedDeriv 8 f t‖ :=
  norm_fourierCoeffOn_negPi_pi_le_iteratedDeriv_integral
    hn 8 hf hperiod

end

end Anderson4D
