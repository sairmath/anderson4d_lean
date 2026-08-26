import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Anderson4D.Continuum.CovarianceDerivativeMajorant
import Anderson4D.Continuum.CovariancePeriodizationRepresentative

/-!
# Coordinate derivatives of one covariance-periodization term

This file differentiates one lattice summand along one scalar coordinate
line.  It deliberately stops before summing over the period lattice, so
the derivative majorant is termwise and carries no finite-box cardinality.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

namespace SmoothCutoff

/-- The continuous linear coordinate line `t ↦ (c t) eᵢ`. -/
def etaCoordLineMap (c : ℝ) (i : Fin dim) : ℝ →L[ℝ] R4 :=
  (c • (1 : ℝ →L[ℝ] ℝ)).smulRight (etaCoordDirection i)

@[simp]
theorem etaCoordLineMap_apply
    (c t : ℝ) (i : Fin dim) :
    etaCoordLineMap c i t =
      (c * t) • etaCoordDirection i := by
  simp [etaCoordLineMap, smul_eq_mul]

/-- The part of a scaled periodization argument independent of the
distinguished coordinate value. -/
def etaPeriodCoordBase
    (ε : ℝ) (x : R4) (k : Z4) (i : Fin dim) : R4 :=
  fun j =>
    ε⁻¹ *
      (Function.update x i 0 j + covariancePeriodVector k j)

/-- The scaled Euclidean argument of a periodization term, written as an
affine scalar coordinate line. -/
def etaPeriodCoordArgument
    (ε : ℝ) (x : R4) (k : Z4) (i : Fin dim) (t : ℝ) : R4 :=
  etaPeriodCoordBase ε x k i + etaCoordLineMap ε⁻¹ i t

theorem etaPeriodCoordArgument_eq
    (ε : ℝ) (x : R4) (k : Z4) (i : Fin dim) (t : ℝ) :
    etaPeriodCoordArgument ε x k i t =
      fun j =>
        ε⁻¹ *
          (Function.update x i t j + covariancePeriodVector k j) := by
  funext j
  rcases eq_or_ne j i with rfl | hji
  · simp [etaPeriodCoordArgument, etaPeriodCoordBase,
      etaCoordDirection]
    ring
  · simp [etaPeriodCoordArgument, etaPeriodCoordBase,
      etaCoordDirection, hji]

/-- One periodization summand restricted to a scalar coordinate line. -/
def etaPeriodTermCoordLine
    (ρ : SmoothCutoff) (ε : ℝ) (x : R4)
    (k : Z4) (i : Fin dim) (t : ℝ) : ℝ :=
  ε⁻¹ ^ (dim : ℕ) * ρ.eta (etaPeriodCoordArgument ε x k i t)

/-- The affine-line definition is exactly the existing periodization term
at the representative whose `i`-th coordinate is `t`. -/
theorem etaPeriodTermCoordLine_eq
    (ρ : SmoothCutoff) (ε : ℝ) (x : R4)
    (k : Z4) (i : Fin dim) (t : ℝ) :
    ρ.etaPeriodTermCoordLine ε x k i t =
      ρ.etaPeriodTermR4 ε (Function.update x i t) k := by
  unfold etaPeriodTermCoordLine etaPeriodTermR4
  rw [etaPeriodCoordArgument_eq]

/-- A scalar coordinate line in one periodization term is `C⁸`. -/
theorem contDiff_etaPeriodTermCoordLine_eight
    (ρ : SmoothCutoff) (ε : ℝ) (x : R4)
    (k : Z4) (i : Fin dim) :
    ContDiff ℝ 8 (ρ.etaPeriodTermCoordLine ε x k i) := by
  unfold etaPeriodTermCoordLine etaPeriodCoordArgument
  have harg : ContDiff ℝ 8 fun t : ℝ =>
      etaPeriodCoordBase ε x k i + etaCoordLineMap ε⁻¹ i t :=
    contDiff_const.add (etaCoordLineMap ε⁻¹ i).contDiff
  exact contDiff_const.mul ((ρ.contDiff_eta 8).comp harg)

/-- Repeated differentiation of `η` along an affine coordinate line. -/
private theorem iteratedDeriv_eta_affine_coord
    (ρ : SmoothCutoff) (r : ℕ) (b : R4)
    (c : ℝ) (i : Fin dim) (t : ℝ) :
    iteratedDeriv r
        (fun s : ℝ => ρ.eta (b + etaCoordLineMap c i s)) t =
      c ^ r *
        ρ.etaCoordDerivative r i
          (b + etaCoordLineMap c i t) := by
  have hf : ContDiff ℝ r (fun u : R4 => ρ.eta (b + u)) :=
    (ρ.contDiff_eta r).comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change
    iteratedFDeriv ℝ r
        ((fun u : R4 => ρ.eta (b + u)) ∘
          etaCoordLineMap c i) t (fun _ => 1) =
      c ^ r *
        ρ.etaCoordDerivative r i
          (b + etaCoordLineMap c i t)
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right
    (etaCoordLineMap c i) hf t le_rfl]
  simp only [
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_comp_add_left]
  simp only [etaCoordLineMap_apply, mul_one]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  change
    c ^ r *
        iteratedFDeriv ℝ r ρ.eta
          (b + (c * t) • etaCoordDirection i)
          (fun _ : Fin r => etaCoordDirection i) =
      c ^ r *
        iteratedFDeriv ℝ r ρ.eta
          (b + (c * t) • etaCoordDirection i)
          (fun _ : Fin r => etaCoordDirection i)
  rfl

/-- Exact repeated coordinate derivative of a single periodization term. -/
theorem iteratedDeriv_etaPeriodTermCoordLine
    (ρ : SmoothCutoff) {ε : ℝ} (_hε : 0 < ε)
    (r : ℕ) (x : R4) (k : Z4) (i : Fin dim) (t : ℝ) :
    iteratedDeriv r (ρ.etaPeriodTermCoordLine ε x k i) t =
      ε⁻¹ ^ (dim : ℕ) * ε⁻¹ ^ r *
        ρ.etaCoordDerivative r i
          (fun j =>
            ε⁻¹ *
              (Function.update x i t j +
                covariancePeriodVector k j)) := by
  unfold etaPeriodTermCoordLine
  rw [iteratedDeriv_const_mul_field]
  unfold etaPeriodCoordArgument
  rw [iteratedDeriv_eta_affine_coord]
  have harg :
      etaPeriodCoordBase ε x k i +
          etaCoordLineMap ε⁻¹ i t =
        fun j =>
          ε⁻¹ *
            (Function.update x i t j +
              covariancePeriodVector k j) := by
    simpa [etaPeriodCoordArgument] using
      etaPeriodCoordArgument_eq ε x k i t
  rw [harg]
  ring

/-- The derivative of one summand is bounded by the corresponding
auxiliary-cutoff summand, with exactly the expected `ε⁻ʳ` loss. -/
theorem abs_iteratedDeriv_etaPeriodTermCoordLine_le
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    {r : ℕ} (hr : r ≤ 8) (x : R4) (k : Z4)
    (i : Fin dim) (t : ℝ) :
    |iteratedDeriv r (ρ.etaPeriodTermCoordLine ε x k i) t| ≤
      (ρ.etaDerivativeMajorantConstant * ε⁻¹ ^ r) *
        ρ.auxiliaryCutoff.etaPeriodTermR4 ε
          (Function.update x i t) k := by
  rw [ρ.iteratedDeriv_etaPeriodTermCoordLine hε]
  rw [abs_mul, abs_mul]
  have hinv : 0 ≤ ε⁻¹ := (inv_pos.mpr hε).le
  rw [abs_of_nonneg (pow_nonneg hinv (dim : ℕ)),
    abs_of_nonneg (pow_nonneg hinv r)]
  let q : R4 := fun j =>
    ε⁻¹ *
      (Function.update x i t j + covariancePeriodVector k j)
  have hmajorant :
      |ρ.etaCoordDerivative r i q| ≤
        ρ.etaDerivativeMajorantConstant *
          ρ.auxiliaryCutoff.eta q :=
    ρ.abs_etaCoordDerivative_le_majorant hr i q
  calc
    ε⁻¹ ^ (dim : ℕ) * ε⁻¹ ^ r *
        |ρ.etaCoordDerivative r i q| ≤
      ε⁻¹ ^ (dim : ℕ) * ε⁻¹ ^ r *
        (ρ.etaDerivativeMajorantConstant *
          ρ.auxiliaryCutoff.eta q) :=
      mul_le_mul_of_nonneg_left hmajorant
        (mul_nonneg (pow_nonneg hinv _) (pow_nonneg hinv _))
    _ = (ρ.etaDerivativeMajorantConstant * ε⁻¹ ^ r) *
        ρ.auxiliaryCutoff.etaPeriodTermR4 ε
          (Function.update x i t) k := by
      unfold etaPeriodTermR4 q
      ring

end SmoothCutoff

end

end Anderson4D
