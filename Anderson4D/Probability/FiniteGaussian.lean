import Anderson4D.Probability.NoiseMoments
import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# Finite Gaussian vectors extracted from the noise model

The `NoiseModel` interface states joint Gaussianity in Cramér--Wold form.
This file packages any finite list of Fourier modes as a genuine Gaussian
vector containing both real and imaginary coordinates.  Repeated modes are
allowed; the coefficient aggregation below is therefore useful beyond a
mere reindexing lemma.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace NoiseModel

variable (M : NoiseModel)

/-- Both real coordinates (`false`) and imaginary coordinates (`true`) of a
finite list of Fourier modes. -/
def coordinateVector {n : ℕ} (k : Fin n → Z4) (ω : M.Ω) :
    Fin n × Bool → ℝ :=
  fun p => if p.2 then (M.g (k p.1) ω).im else (M.g (k p.1) ω).re

theorem measurable_coordinateVector {n : ℕ} (k : Fin n → Z4) :
    Measurable (M.coordinateVector k) := by
  apply measurable_pi_lambda
  intro p
  have hg : Measurable (M.g (k p.1)) := M.measurable_g (k p.1)
  unfold coordinateVector
  split <;> fun_prop

/-- Coefficient of a coordinate in a continuous linear functional on the
finite real coordinate space. -/
def coordinateDualCoeff {n : ℕ}
    (L : (Fin n × Bool → ℝ) →L[ℝ] ℝ) (p : Fin n × Bool) : ℝ :=
  L (fun q => if p = q then 1 else 0)

/-- Aggregate all real-part coefficients belonging to the same Fourier
mode.  This handles repeated entries in `k`. -/
def coordinateRealWeight {n : ℕ} (k : Fin n → Z4)
    (L : (Fin n × Bool → ℝ) →L[ℝ] ℝ) (z : Z4) : ℝ :=
  ∑ i : Fin n, if k i = z then coordinateDualCoeff L (i, false) else 0

/-- Aggregate all imaginary-part coefficients belonging to the same Fourier
mode. -/
def coordinateImagWeight {n : ℕ} (k : Fin n → Z4)
    (L : (Fin n × Bool → ℝ) →L[ℝ] ℝ) (z : Z4) : ℝ :=
  ∑ i : Fin n, if k i = z then coordinateDualCoeff L (i, true) else 0

private theorem sum_aggregatedWeight_mul {n : ℕ}
    (k : Fin n → Z4) (c : Fin n → ℝ) (f : Z4 → ℝ) :
    (∑ z ∈ Finset.univ.image k,
        (∑ i : Fin n, if k i = z then c i else 0) * f z) =
      ∑ i : Fin n, c i * f (k i) := by
  classical
  calc
    (∑ z ∈ Finset.univ.image k,
        (∑ i : Fin n, if k i = z then c i else 0) * f z) =
        ∑ z ∈ Finset.univ.image k,
          ∑ i ∈ Finset.univ with k i = z, c i * f z := by
      apply Finset.sum_congr rfl
      intro z _hz
      rw [Finset.sum_mul Finset.univ, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _hi
      split_ifs <;> simp
    _ = ∑ i ∈ Finset.univ, c i * f (k i) := by
      have hfiber :=
        Finset.sum_fiberwise_of_maps_to
          (s := (Finset.univ : Finset (Fin n)))
          (t := Finset.univ.image k)
          (g := k)
          (fun i _hi => Finset.mem_image.mpr
            ⟨i, Finset.mem_univ i, rfl⟩)
          (fun i => c i * f (k i))
      rw [← hfiber]
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro i hi
      have hik : k i = z := (Finset.mem_filter.mp hi).2
      rw [hik]
    _ = ∑ i : Fin n, c i * f (k i) := rfl

/-- Applying a functional to the finite vector is exactly a
`NoiseModel.linearCombination` with aggregated coefficients. -/
theorem apply_coordinateVector_eq_linearCombination {n : ℕ}
    (k : Fin n → Z4) (L : (Fin n × Bool → ℝ) →L[ℝ] ℝ) (ω : M.Ω) :
    L (M.coordinateVector k ω) =
      M.linearCombination (Finset.univ.image k)
        (coordinateRealWeight k L) (coordinateImagWeight k L) ω := by
  change L.toLinearMap (M.coordinateVector k ω) =
    M.linearCombination (Finset.univ.image k)
      (coordinateRealWeight k L) (coordinateImagWeight k L) ω
  rw [LinearMap.pi_apply_eq_sum_univ]
  unfold coordinateVector linearCombination coordinateRealWeight
    coordinateImagWeight coordinateDualCoeff
  simp only [smul_eq_mul]
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib (s := Finset.univ.image k)]
  rw [sum_aggregatedWeight_mul, sum_aggregatedWeight_mul]
  change
    ((∑ i : Fin n,
        (M.g (k i) ω).im *
          L (fun q => if (i, true) = q then 1 else 0)) +
      ∑ i : Fin n,
        (M.g (k i) ω).re *
          L (fun q => if (i, false) = q then 1 else 0)) =
      (∑ i : Fin n,
        L (fun q => if (i, false) = q then 1 else 0) *
          (M.g (k i) ω).re) +
      ∑ i : Fin n,
        L (fun q => if (i, true) = q then 1 else 0) *
          (M.g (k i) ω).im
  have hre :
      (∑ i : Fin n,
          (M.g (k i) ω).re *
            L (fun q => if (i, false) = q then 1 else 0)) =
        ∑ i : Fin n,
          L (fun q => if (i, false) = q then 1 else 0) *
            (M.g (k i) ω).re := by
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have him :
      (∑ i : Fin n,
          (M.g (k i) ω).im *
            L (fun q => if (i, true) = q then 1 else 0)) =
        ∑ i : Fin n,
          L (fun q => if (i, true) = q then 1 else 0) *
            (M.g (k i) ω).im := by
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hre, him]
  ring

/-- Every continuous linear functional of the finite coordinate vector has
an exact centered Gaussian law. -/
theorem exists_map_coordinateVector_linear_eq_gaussianReal {n : ℕ}
    (k : Fin n → Z4) (L : (Fin n × Bool → ℝ) →L[ℝ] ℝ) :
    ∃ v : ℝ≥0,
      (Measure.map (M.coordinateVector k) (volume : Measure M.Ω)).map L =
        gaussianReal 0 v := by
  let s : Finset Z4 := Finset.univ.image k
  let a : Z4 → ℝ := coordinateRealWeight k L
  let b : Z4 → ℝ := coordinateImagWeight k L
  refine ⟨M.linearCombinationVariance s a b, ?_⟩
  rw [← M.map_linearCombination_eq_gaussianReal s a b]
  rw [Measure.map_map]
  · apply Measure.map_congr
    filter_upwards with ω
    exact M.apply_coordinateVector_eq_linearCombination k L ω
  · fun_prop
  · exact M.measurable_coordinateVector k

/-- The law of the finite real/imaginary coordinate vector is Gaussian. -/
theorem isGaussian_map_coordinateVector {n : ℕ} (k : Fin n → Z4) :
    IsGaussian
      (Measure.map (M.coordinateVector k) (volume : Measure M.Ω)) := by
  apply isGaussian_of_map_eq_gaussianReal
  intro L
  obtain ⟨v, hv⟩ :=
    M.exists_map_coordinateVector_linear_eq_gaussianReal k L
  exact ⟨0, v, hv⟩

/-- The finite coordinate-vector law is centered as a vector-valued
Gaussian measure. -/
theorem integral_id_map_coordinateVector {n : ℕ} (k : Fin n → Z4) :
    ∫ x, x ∂Measure.map (M.coordinateVector k) (volume : Measure M.Ω) = 0 := by
  let μv : Measure (Fin n × Bool → ℝ) :=
    Measure.map (M.coordinateVector k) (volume : Measure M.Ω)
  letI : IsGaussian μv := M.isGaussian_map_coordinateVector k
  apply funext
  intro p
  let L : (Fin n × Bool → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj p
  obtain ⟨v, hv⟩ :=
    M.exists_map_coordinateVector_linear_eq_gaussianReal k L
  change μv.map L = gaussianReal 0 v at hv
  have hscalar : ∫ x, L x ∂μv = 0 := by
    calc
      ∫ x, L x ∂μv = ∫ r, r ∂μv.map L := by
        symm
        exact integral_map L.continuous.measurable.aemeasurable
          (Measurable.aestronglyMeasurable (by fun_prop))
      _ = ∫ r, r ∂gaussianReal 0 v := by rw [hv]
      _ = 0 := by simp
  change L (∫ x, x ∂μv) = L 0
  calc
    L (∫ x, x ∂μv) = ∫ x, L x ∂μv :=
      (L.integral_comp_comm IsGaussian.integrable_id).symm
    _ = 0 := hscalar
    _ = L 0 := L.map_zero.symm

end NoiseModel

end

end Anderson4D
