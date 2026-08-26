import Anderson4D.ForMathlib.GaussianMoments
import Anderson4D.Probability.Noise

/-!
# Scalar moments of finite white-noise Fourier combinations

This file turns the Cramér--Wold field in `NoiseModel` into a usable
one-dimensional API.  Every finite real linear combination of real and
imaginary Fourier coordinates has its exact Gaussian law, all moments, and
the usual even/odd formulas.  These are the analytic inputs for the
self-contained Isserlis polarization argument.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace NoiseModel

variable (M : NoiseModel)

/-- A finite real linear combination of the real and imaginary parts of the
Fourier coefficients. -/
def linearCombination (s : Finset Z4) (a b : Z4 → ℝ) (ω : M.Ω) : ℝ :=
  ∑ k ∈ s, (a k * (M.g k ω).re + b k * (M.g k ω).im)

theorem measurable_linearCombination (s : Finset Z4) (a b : Z4 → ℝ) :
    Measurable (M.linearCombination s a b) := by
  unfold linearCombination
  refine Finset.measurable_sum s fun k _ ↦ ?_
  have hg : Measurable (M.g k) := M.measurable_g k
  fun_prop

/-- The exact centered-Gaussian law supplied by the `NoiseModel`
Cramér--Wold field. -/
theorem exists_law_linearCombination (s : Finset Z4) (a b : Z4 → ℝ) :
    ∃ v : ℝ≥0,
      Measure.map (M.linearCombination s a b) (volume : Measure M.Ω) =
        gaussianReal 0 v := by
  change ∃ v : ℝ≥0,
    Measure.map
      (fun ω => ∑ k ∈ s,
        (a k * (M.g k ω).re + b k * (M.g k ω).im))
      (volume : Measure M.Ω) = gaussianReal 0 v
  exact M.gaussian_lincomb s a b

/-- Transport a raw moment across an exact centered-Gaussian law. -/
theorem integral_linearCombination_pow
    (s : Finset Z4) (a b : Z4 → ℝ) (v : ℝ≥0)
    (hlaw : Measure.map (M.linearCombination s a b) (volume : Measure M.Ω) =
      gaussianReal 0 v) (n : ℕ) :
    ∫ ω, (M.linearCombination s a b ω) ^ n =
      centeredGaussianMoment v n := by
  rw [centeredGaussianMoment, ← hlaw]
  symm
  exact MeasureTheory.integral_map
    (M.measurable_linearCombination s a b).aemeasurable
    (Measurable.aestronglyMeasurable (by fun_prop))

/-- All powers of a finite Fourier-coordinate combination are integrable.
This is recorded separately from the integral identity because later
finite-sum and polarization arguments need the integrability witness. -/
theorem integrable_linearCombination_pow_of_law
    (s : Finset Z4) (a b : Z4 → ℝ) (v : ℝ≥0)
    (hlaw : Measure.map (M.linearCombination s a b) (volume : Measure M.Ω) =
      gaussianReal 0 v) (n : ℕ) :
    Integrable (fun ω => (M.linearCombination s a b ω) ^ n) := by
  have hgauss :
      Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 v) := by
    apply (integrable_norm_iff (Measurable.aestronglyMeasurable (by fun_prop))).mp
    simpa [norm_pow] using
      (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := v) (n : ℝ≥0)).integrable_norm_pow'
  have hmap :
      Integrable (fun x : ℝ => x ^ n)
        (Measure.map (M.linearCombination s a b) (volume : Measure M.Ω)) := by
    rwa [hlaw]
  have hcomp := (integrable_map_measure
    (Measurable.aestronglyMeasurable (by fun_prop))
    (M.measurable_linearCombination s a b).aemeasurable).mp hmap
  simpa [Function.comp_def] using hcomp

/-- Existential-free integrability wrapper using the `NoiseModel` law. -/
theorem integrable_linearCombination_pow
    (s : Finset Z4) (a b : Z4 → ℝ) (n : ℕ) :
    Integrable (fun ω => (M.linearCombination s a b ω) ^ n) := by
  obtain ⟨v, hv⟩ := M.exists_law_linearCombination s a b
  exact M.integrable_linearCombination_pow_of_law s a b v hv n

/-- The canonical variance of a finite Fourier-coordinate combination,
defined by its second moment. -/
def linearCombinationVariance
    (s : Finset Z4) (a b : Z4 → ℝ) : ℝ≥0 :=
  ⟨∫ ω, (M.linearCombination s a b ω) ^ 2,
    integral_nonneg fun _ ↦ sq_nonneg _⟩

/-- The existential variance in the `NoiseModel` interface is uniquely the
second moment, so every combination has a canonical exact law. -/
theorem map_linearCombination_eq_gaussianReal
    (s : Finset Z4) (a b : Z4 → ℝ) :
    Measure.map (M.linearCombination s a b) (volume : Measure M.Ω) =
      gaussianReal 0 (M.linearCombinationVariance s a b) := by
  obtain ⟨v, hv⟩ := M.exists_law_linearCombination s a b
  have hsecond :
      (∫ ω, (M.linearCombination s a b ω) ^ 2) = (v : ℝ) := by
    calc
      (∫ ω, (M.linearCombination s a b ω) ^ 2) =
          centeredGaussianMoment v 2 :=
        M.integral_linearCombination_pow s a b v hv 2
      _ = (v : ℝ) := by
        simpa [gaussianPairingCount] using
          centeredGaussianMoment_even v 1
  have hvariance : M.linearCombinationVariance s a b = v := by
    apply NNReal.eq
    exact hsecond
  simpa [hvariance] using hv

/-- The second moment agrees definitionally with the canonical variance. -/
theorem integral_linearCombination_sq
    (s : Finset Z4) (a b : Z4 → ℝ) :
    (∫ ω, (M.linearCombination s a b ω) ^ 2) =
      M.linearCombinationVariance s a b := rfl

/-- Every finite Fourier-coordinate combination is centered. -/
theorem integral_linearCombination
    (s : Finset Z4) (a b : Z4 → ℝ) :
    (∫ ω, M.linearCombination s a b ω) = 0 := by
  obtain ⟨v, hv⟩ := M.exists_law_linearCombination s a b
  rw [show (fun ω => M.linearCombination s a b ω) =
      (fun ω => (M.linearCombination s a b ω) ^ 1) by
        funext ω
        simp,
    M.integral_linearCombination_pow s a b v hv 1]
  simpa using centeredGaussianMoment_odd v 0

/-- Exact even moments in terms of the canonical second-moment variance. -/
theorem integral_linearCombination_even
    (s : Finset Z4) (a b : Z4 → ℝ) (q : ℕ) :
    (∫ ω, (M.linearCombination s a b ω) ^ (2 * q)) =
      (gaussianPairingCount q : ℝ) *
        (M.linearCombinationVariance s a b : ℝ) ^ q := by
  rw [M.integral_linearCombination_pow s a b
      (M.linearCombinationVariance s a b)
      (M.map_linearCombination_eq_gaussianReal s a b),
    centeredGaussianMoment_even]

/-- Every finite Fourier-coordinate combination has the exact even Gaussian
moments for the variance appearing in its Cramér--Wold law. -/
theorem exists_integral_linearCombination_even
    (s : Finset Z4) (a b : Z4 → ℝ) (q : ℕ) :
    ∃ v : ℝ≥0,
      (∫ ω, (M.linearCombination s a b ω) ^ (2 * q)) =
        (gaussianPairingCount q : ℝ) * (v : ℝ) ^ q := by
  obtain ⟨v, hv⟩ := M.exists_law_linearCombination s a b
  refine ⟨v, ?_⟩
  rw [M.integral_linearCombination_pow s a b v hv,
    centeredGaussianMoment_even]

/-- Every odd moment of a finite Fourier-coordinate combination vanishes. -/
theorem integral_linearCombination_odd
    (s : Finset Z4) (a b : Z4 → ℝ) (q : ℕ) :
    (∫ ω, (M.linearCombination s a b ω) ^ (2 * q + 1)) = 0 := by
  obtain ⟨v, hv⟩ := M.exists_law_linearCombination s a b
  rw [M.integral_linearCombination_pow s a b v hv,
    centeredGaussianMoment_odd]

end NoiseModel

end

end Anderson4D
