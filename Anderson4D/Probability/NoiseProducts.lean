import Anderson4D.Probability.FiniteGaussian

/-!
# Integrability and finite covariance sums for Fourier noise

The covariance fields in `NoiseModel` identify the relevant integrals, but
finite-sum manipulations also need genuine integrability witnesses.  They are
not additional assumptions: joint Gaussianity gives every finite moment.
This file extracts the complex `Lᵖ` consequence and packages the finite
covariance calculation used by the random-parametrix layer.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory ComplexConjugate
open scoped ENNReal

namespace NoiseModel

variable (M : NoiseModel)

/-- Recover one complex coordinate from the real/imaginary finite-vector
representation. -/
def coordinateComplexCLM {n : ℕ} (i : Fin n) :
    (Fin n × Bool → ℝ) →L[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.proj (i, false)).prod
      (ContinuousLinearMap.proj (i, true)))

@[simp] theorem coordinateComplexCLM_apply {n : ℕ} (i : Fin n)
    (x : Fin n × Bool → ℝ) :
    coordinateComplexCLM i x =
      x (i, false) + x (i, true) * Complex.I := by
  simp [coordinateComplexCLM, Complex.equivRealProdCLM_symm_apply]

/-- Every complex Fourier coefficient has moments of every finite order.
This is derived from the finite-dimensional Gaussian law, rather than added
to `NoiseModel` as a redundant field. -/
theorem memLp_g (k : Z4) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (M.g k) p (volume : Measure M.Ω) := by
  let modes : Fin 1 → Z4 := fun _ => k
  let μv : Measure (Fin 1 × Bool → ℝ) :=
    Measure.map (M.coordinateVector modes) (volume : Measure M.Ω)
  letI : IsGaussian μv := M.isGaussian_map_coordinateVector modes
  have hid : MemLp id p μv := IsGaussian.memLp_id μv p hp
  have hcoord :
      MemLp (fun x => coordinateComplexCLM (0 : Fin 1) x) p μv :=
    hid.continuousLinearMap_comp (coordinateComplexCLM (0 : Fin 1))
  have hcomp :=
    hcoord.comp_of_map (M.measurable_coordinateVector modes).aemeasurable
  simpa [Function.comp_def, modes, coordinateVector] using hcomp

/-- Products of two Fourier coefficients are integrable. -/
theorem integrable_g_mul_g (k l : Z4) :
    Integrable (fun ω => M.g k ω * M.g l ω)
      (volume : Measure M.Ω) := by
  exact MemLp.integrable_mul (M.memLp_g k 2 (by norm_num))
    (M.memLp_g l 2 (by norm_num))

/-- Products with a conjugated Fourier coefficient are integrable. -/
theorem integrable_g_mul_conj_g (k l : Z4) :
    Integrable (fun ω => M.g k ω * conj (M.g l ω))
      (volume : Measure M.Ω) := by
  have hl : MemLp (fun ω => conj (M.g l ω)) 2
      (volume : Measure M.Ω) :=
    (M.memLp_g l 2 (by norm_num)).continuousLinearMap_comp
      Complex.conjCLE.toContinuousLinearMap
  exact MemLp.integrable_mul (M.memLp_g k 2 (by norm_num)) hl

/-- A finite complex linear combination of Fourier coefficients. -/
def finiteNoiseCombination
    (s : Finset Z4) (a : Z4 → ℂ) (ω : M.Ω) : ℂ :=
  ∑ k ∈ s, a k * M.g k ω

theorem integrable_finiteNoiseCombination
    (s : Finset Z4) (a : Z4 → ℂ) :
    Integrable (M.finiteNoiseCombination s a)
      (volume : Measure M.Ω) := by
  unfold finiteNoiseCombination
  apply integrable_finsetSum
  intro k hk
  exact (M.memLp_g k 1 (by norm_num)).integrable le_rfl |>.const_mul (a k)

/-- Exact finite covariance expansion.  Keeping the Kronecker factor
explicit avoids imposing symmetry assumptions on either finite mode set. -/
theorem integral_finiteNoiseCombination_mul
    (s t : Finset Z4) (a b : Z4 → ℂ) :
    ∫ ω, M.finiteNoiseCombination s a ω *
        M.finiteNoiseCombination t b ω =
      ∑ k ∈ s, ∑ l ∈ t,
        a k * b l * (if k = -l then 1 else 0) := by
  unfold finiteNoiseCombination
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro l hl
      have hfun :
          (fun ω => a k * M.g k ω * (b l * M.g l ω)) =
            fun ω => (a k * b l) * (M.g k ω * M.g l ω) := by
        funext ω
        ring
      rw [hfun, integral_const_mul, M.cov_pair]
    · intro l hl
      refine ((M.integrable_g_mul_g k l).const_mul (a k * b l)).congr ?_
      filter_upwards with ω
      ring
  · intro k hk
    apply integrable_finsetSum
    intro l hl
    refine ((M.integrable_g_mul_g k l).const_mul (a k * b l)).congr ?_
    filter_upwards with ω
    ring

/-- Exact finite covariance expansion with conjugation in the second
factor. -/
theorem integral_finiteNoiseCombination_mul_conj
    (s t : Finset Z4) (a b : Z4 → ℂ) :
    ∫ ω, M.finiteNoiseCombination s a ω *
        conj (M.finiteNoiseCombination t b ω) =
      ∑ k ∈ s, ∑ l ∈ t,
        a k * conj (b l) * (if k = l then 1 else 0) := by
  have hconj : ∀ ω,
      conj (M.finiteNoiseCombination t b ω) =
        ∑ l ∈ t, conj (b l) * conj (M.g l ω) := by
    intro ω
    unfold finiteNoiseCombination
    simp
  change
    (∫ ω, (∑ k ∈ s, a k * M.g k ω) *
      conj (M.finiteNoiseCombination t b ω)) = _
  simp_rw [hconj, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro l hl
      have hfun :
          (fun ω => a k * M.g k ω *
              (conj (b l) * conj (M.g l ω))) =
            fun ω => (a k * conj (b l)) *
              (M.g k ω * conj (M.g l ω)) := by
        funext ω
        ring
      rw [hfun, integral_const_mul, M.cov_conj]
    · intro l hl
      refine
        ((M.integrable_g_mul_conj_g k l).const_mul
          (a k * conj (b l))).congr ?_
      filter_upwards with ω
      ring
  · intro k hk
    apply integrable_finsetSum
    intro l hl
    refine
      ((M.integrable_g_mul_conj_g k l).const_mul
        (a k * conj (b l))).congr ?_
    filter_upwards with ω
    ring

end NoiseModel

end

end Anderson4D
