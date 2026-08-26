import Anderson4D.ForMathlib.QuadraticExpDeriv
import Anderson4D.Probability.NoiseProducts

/-!
# Isserlis formulas for finite Fourier-noise coordinates

This file applies the abstract centered-Gaussian Isserlis theorem to the
finite vectors supplied by `NoiseModel.coordinateVector`.  The latter use
the ordinary finite function space, whereas the analytic theorem is stated
on Hilbert spaces.  We therefore transport the vector through the canonical
finite-dimensional `ℓ²` equivalence, prove that this transported law is
Gaussian and centered, and then pull the resulting moment identities back
to the original probability space.

The final `Fin` and `List` wrappers are the application-level API: arbitrary
repetitions of modes and arbitrary choices of real or imaginary coordinate
are allowed, every displayed product is genuinely integrable, and no
moment identity is assumed.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal RealInnerProductSpace

namespace NoiseModel

variable (M : NoiseModel)

/-- The finite real/imaginary noise vector in its canonical Euclidean
realization.  This is only a change of norm on a finite-dimensional
function space; its coordinates are definitionally those of
`coordinateVector`. -/
def coordinateEuclideanVector {n : ℕ} (k : Fin n → Z4) (ω : M.Ω) :
    EuclideanSpace ℝ (Fin n × Bool) :=
  WithLp.toLp 2 (M.coordinateVector k ω)

theorem measurable_coordinateEuclideanVector {n : ℕ} (k : Fin n → Z4) :
    Measurable (M.coordinateEuclideanVector k) := by
  let L : (Fin n × Bool → ℝ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n × Bool) :=
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin n × Bool => ℝ)).symm
  exact L.continuous.measurable.comp (M.measurable_coordinateVector k)

/-- The Euclidean realization of every finite real/imaginary coordinate
vector has a genuine Gaussian law. -/
theorem isGaussian_map_coordinateEuclideanVector {n : ℕ}
    (k : Fin n → Z4) :
    IsGaussian
      (Measure.map (M.coordinateEuclideanVector k)
        (volume : Measure M.Ω)) := by
  let μv : Measure (Fin n × Bool → ℝ) :=
    Measure.map (M.coordinateVector k) (volume : Measure M.Ω)
  letI : IsGaussian μv := M.isGaussian_map_coordinateVector k
  let L : (Fin n × Bool → ℝ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n × Bool) :=
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin n × Bool => ℝ)).symm
  change IsGaussian
    (Measure.map (L ∘ M.coordinateVector k)
      (volume : Measure M.Ω))
  rw [← Measure.map_map L.continuous.measurable
    (M.measurable_coordinateVector k)]
  infer_instance

/-- The Euclidean finite-vector law is centered.  This is transported from
the exact centered law proved for `coordinateVector`; it is not an
additional hypothesis on the noise model. -/
theorem integral_id_map_coordinateEuclideanVector {n : ℕ}
    (k : Fin n → Z4) :
    ∫ x, x ∂Measure.map (M.coordinateEuclideanVector k)
      (volume : Measure M.Ω) = 0 := by
  let μv : Measure (Fin n × Bool → ℝ) :=
    Measure.map (M.coordinateVector k) (volume : Measure M.Ω)
  letI : IsGaussian μv := M.isGaussian_map_coordinateVector k
  let L : (Fin n × Bool → ℝ) →L[ℝ]
      EuclideanSpace ℝ (Fin n × Bool) :=
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin n × Bool => ℝ)).symm.toContinuousLinearMap
  change ∫ x, x ∂Measure.map (L ∘ M.coordinateVector k)
    (volume : Measure M.Ω) = 0
  rw [← Measure.map_map L.continuous.measurable
    (M.measurable_coordinateVector k)]
  calc
    (∫ x, x ∂μv.map L) = L (∫ x, x ∂μv) := by
      haveI : IsGaussian (μv.map L) := inferInstance
      calc
        _ = ∫ x, L x ∂μv :=
          integral_map (μ := μv) (φ := L) (f := id)
            L.continuous.measurable.aemeasurable
            (IsGaussian.integrable_id
              (μ := μv.map L)).aestronglyMeasurable
        _ = _ := L.integral_comp_comm
          (IsGaussian.integrable_id (μ := μv))
    _ = 0 := by
      rw [M.integral_id_map_coordinateVector k]
      exact L.map_zero

/-- A selected real or imaginary Fourier coordinate has every finite
`Lᵖ` moment. -/
theorem memLp_coordinate {n : ℕ} (k : Fin n → Z4)
    (p : Fin n × Bool) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun ω => M.coordinateVector k ω p) r
      (volume : Measure M.Ω) := by
  let μE : Measure (EuclideanSpace ℝ (Fin n × Bool)) :=
    Measure.map (M.coordinateEuclideanVector k)
      (volume : Measure M.Ω)
  letI : IsGaussian μE := M.isGaussian_map_coordinateEuclideanVector k
  have hproj :
      MemLp (fun x : EuclideanSpace ℝ (Fin n × Bool) => x p) r μE := by
    simpa [EuclideanSpace.coe_proj] using
      (IsGaussian.memLp_id μE r hr).continuousLinearMap_comp
        (EuclideanSpace.proj (𝕜 := ℝ) p)
  have hcomp :=
    hproj.comp_of_map
      (M.measurable_coordinateEuclideanVector k).aemeasurable
  simpa [Function.comp_def, coordinateEuclideanVector,
    coordinateVector] using hcomp

/-- Every selected real or imaginary coordinate is centered. -/
theorem integral_coordinate {n : ℕ} (k : Fin n → Z4)
    (p : Fin n × Bool) :
    ∫ ω, M.coordinateVector k ω p
      ∂(volume : Measure M.Ω) = 0 := by
  let μE : Measure (EuclideanSpace ℝ (Fin n × Bool)) :=
    Measure.map (M.coordinateEuclideanVector k)
      (volume : Measure M.Ω)
  letI : IsGaussian μE := M.isGaussian_map_coordinateEuclideanVector k
  let P : EuclideanSpace ℝ (Fin n × Bool) →L[ℝ] ℝ :=
    EuclideanSpace.proj p
  have hcenter := congrArg P
    (M.integral_id_map_coordinateEuclideanVector k)
  calc
    (∫ ω, M.coordinateVector k ω p
        ∂(volume : Measure M.Ω)) =
        ∫ x, P x ∂μE := by
      symm
      simpa [μE, P, Function.comp_def, coordinateEuclideanVector,
        coordinateVector, EuclideanSpace.coe_proj] using
        integral_map
          (M.measurable_coordinateEuclideanVector k).aemeasurable
          (IsGaussian.integrable_dual μE P).aestronglyMeasurable
    _ = P (∫ x, x ∂μE) :=
      P.integral_comp_comm (IsGaussian.integrable_id (μ := μE))
    _ = 0 := by simpa [μE] using hcenter

/-- Covariance kernel of the finite real-coordinate presentation. -/
def coordinateCovariance {n : ℕ} (k : Fin n → Z4)
    (p r : Fin n × Bool) : ℝ :=
  cov[(fun ω => M.coordinateVector k ω p),
    (fun ω => M.coordinateVector k ω r);
    (volume : Measure M.Ω)]

/-- Since every coordinate is centered, `coordinateCovariance` is exactly
the raw second moment. -/
theorem coordinateCovariance_eq_integral {n : ℕ}
    (k : Fin n → Z4) (p r : Fin n × Bool) :
    M.coordinateCovariance k p r =
      ∫ ω, M.coordinateVector k ω p *
        M.coordinateVector k ω r
        ∂(volume : Measure M.Ω) := by
  rw [coordinateCovariance,
    covariance_eq_sub (M.memLp_coordinate k p 2 (by simp))
      (M.memLp_coordinate k r 2 (by simp)),
    M.integral_coordinate k p, M.integral_coordinate k r]
  simp

/-- Any finite product of selected real/imaginary coordinates is genuinely
integrable.  The proof uses Gaussian `Lʳ` moments and finite Hölder with
one exponent `r` for each of the `r` factors. -/
theorem integrable_coordinateProduct {n r : ℕ} (k : Fin n → Z4)
    (p : Fin r → Fin n × Bool) :
    Integrable (fun ω => ∏ i, M.coordinateVector k ω (p i))
      (volume : Measure M.Ω) := by
  by_cases hr : r = 0
  · subst r
    simp
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hprod :=
      MemLp.prod'
        (s := (Finset.univ : Finset (Fin r)))
        (p := fun _ : Fin r => (r : ℝ≥0∞))
        (f := fun i ω => M.coordinateVector k ω (p i))
        (fun i _hi => M.memLp_coordinate k (p i) r (by simp))
    have hLp :
        MemLp (fun ω => ∏ i, M.coordinateVector k ω (p i)) 1
          (volume : Measure M.Ω) := by
      have hcast :
          (r : ℝ≥0∞) * (r : ℝ≥0∞)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (by exact_mod_cast hr) (by simp)
      have hsum :
          (∑ _ : Fin r, ((r : ℝ≥0∞)⁻¹)) = 1 := by
        simpa only [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul] using hcast
      rw [hsum] at hprod
      simpa only [inv_one] using hprod
    exact hLp.integrable le_rfl

private theorem coordinate_inner_basis {n : ℕ}
    (p : Fin n × Bool) (x : EuclideanSpace ℝ (Fin n × Bool)) :
    ⟪x, (EuclideanSpace.basisFun (Fin n × Bool) ℝ) p⟫ = x p := by
  simpa using
    (EuclideanSpace.inner_single_right p (1 : ℝ) x)

/-- Even-coordinate Isserlis formula for the actual Fourier-noise sample
space.  Repeated modes and repeated coordinates are allowed. -/
theorem integral_coordinateProduct_even_eq_wickPairingSum
    {n : ℕ} (k : Fin n → Z4) (q : ℕ)
    (p : Fin (2 * q) → Fin n × Bool) :
    (∫ ω, ∏ i, M.coordinateVector k ω (p i)
        ∂(volume : Measure M.Ω)) =
      wickPairingSum
        (fun i j => M.coordinateCovariance k (p i) (p j)) := by
  let μE : Measure (EuclideanSpace ℝ (Fin n × Bool)) :=
    Measure.map (M.coordinateEuclideanVector k)
      (volume : Measure M.Ω)
  letI : IsGaussian μE := M.isGaussian_map_coordinateEuclideanVector k
  let b : Fin (2 * q) → EuclideanSpace ℝ (Fin n × Bool) :=
    fun i => (EuclideanSpace.basisFun (Fin n × Bool) ℝ) (p i)
  have hIsserlis :=
    centeredGaussian_mixedMoment_eq_wickPairingSum μE
      (M.integral_id_map_coordinateEuclideanVector k) q b
  have hmap :
      (∫ x, ∏ i, ⟪x, b i⟫ ∂μE) =
        ∫ ω, ∏ i, M.coordinateVector k ω (p i)
          ∂(volume : Measure M.Ω) := by
    rw [integral_map
      (M.measurable_coordinateEuclideanVector k).aemeasurable
      (Measurable.aestronglyMeasurable (by fun_prop))]
    apply integral_congr_ae
    filter_upwards with ω
    apply Finset.prod_congr rfl
    intro i _hi
    exact coordinate_inner_basis (p i)
      (M.coordinateEuclideanVector k ω)
  have hcov (i j : Fin (2 * q)) :
      covarianceBilin μE (b i) (b j) =
        M.coordinateCovariance k (p i) (p j) := by
    change covarianceBilin
      (Measure.map
        (fun ω => WithLp.toLp 2
          (fun z => M.coordinateVector k ω z))
        (volume : Measure M.Ω))
      ((EuclideanSpace.basisFun (Fin n × Bool) ℝ) (p i))
      ((EuclideanSpace.basisFun (Fin n × Bool) ℝ) (p j)) =
        M.coordinateCovariance k (p i) (p j)
    exact covarianceBilin_apply_basisFun
      (fun z => M.memLp_coordinate k z 2 (by simp)) (p i) (p j)
  calc
    (∫ ω, ∏ i, M.coordinateVector k ω (p i)
        ∂(volume : Measure M.Ω)) =
        ∫ x, ∏ i, ⟪x, b i⟫ ∂μE := hmap.symm
    _ = wickPairingSum
        (fun i j => covarianceBilin μE (b i) (b j)) := hIsserlis
    _ = wickPairingSum
        (fun i j => M.coordinateCovariance k (p i) (p j)) := by
      congr 2
      funext i j
      exact hcov i j

/-- Every odd product of selected real/imaginary Fourier coordinates has
zero expectation. -/
theorem integral_coordinateProduct_odd_eq_zero
    {n : ℕ} (k : Fin n → Z4) (q : ℕ)
    (p : Fin (2 * q + 1) → Fin n × Bool) :
    (∫ ω, ∏ i, M.coordinateVector k ω (p i)
        ∂(volume : Measure M.Ω)) = 0 := by
  let μE : Measure (EuclideanSpace ℝ (Fin n × Bool)) :=
    Measure.map (M.coordinateEuclideanVector k)
      (volume : Measure M.Ω)
  letI : IsGaussian μE := M.isGaussian_map_coordinateEuclideanVector k
  let b : Fin (2 * q + 1) → EuclideanSpace ℝ (Fin n × Bool) :=
    fun i => (EuclideanSpace.basisFun (Fin n × Bool) ℝ) (p i)
  have hIsserlis :=
    centeredGaussian_mixedMoment_odd_eq_zero μE
      (M.integral_id_map_coordinateEuclideanVector k) q b
  have hmap :
      (∫ x, ∏ i, ⟪x, b i⟫ ∂μE) =
        ∫ ω, ∏ i, M.coordinateVector k ω (p i)
          ∂(volume : Measure M.Ω) := by
    rw [integral_map
      (M.measurable_coordinateEuclideanVector k).aemeasurable
      (Measurable.aestronglyMeasurable (by fun_prop))]
    apply integral_congr_ae
    filter_upwards with ω
    apply Finset.prod_congr rfl
    intro i _hi
    exact coordinate_inner_basis (p i)
      (M.coordinateEuclideanVector k ω)
  exact hmap.symm.trans hIsserlis

/-- Parity-free `Fin` wrapper.  This is the direct entry point for later
finite-index Wick products such as those occurring inside `wickAt`. -/
theorem integral_coordinateProduct_eq_wickPairingSum
    {n r : ℕ} (k : Fin n → Z4)
    (p : Fin r → Fin n × Bool) :
    (∫ ω, ∏ i, M.coordinateVector k ω (p i)
        ∂(volume : Measure M.Ω)) =
      wickPairingSum
        (fun i j => M.coordinateCovariance k (p i) (p j)) := by
  obtain ⟨q, hq | hq⟩ := r.even_or_odd'
  · subst r
    exact M.integral_coordinateProduct_even_eq_wickPairingSum k q p
  · subst r
    rw [M.integral_coordinateProduct_odd_eq_zero k q p,
      wickPairingSum_odd]

/-- List-indexed integrability wrapper. -/
theorem integrable_coordinateListProduct
    {n : ℕ} (k : Fin n → Z4)
    (ps : List (Fin n × Bool)) :
    Integrable
      (fun ω => (ps.map
        (fun p => M.coordinateVector k ω p)).prod)
      (volume : Measure M.Ω) := by
  refine (M.integrable_coordinateProduct k ps.get).congr ?_
  filter_upwards with ω
  rw [← List.prod_ofFn, List.ofFn_comp' ps.get
    (fun p => M.coordinateVector k ω p), List.ofFn_get]

/-- List-indexed form of the same identity. -/
theorem integral_coordinateListProduct_eq_wickPairingList
    {n : ℕ} (k : Fin n → Z4)
    (ps : List (Fin n × Bool)) :
    (∫ ω, (ps.map (fun p => M.coordinateVector k ω p)).prod
        ∂(volume : Measure M.Ω)) =
      wickPairingList (M.coordinateCovariance k) ps := by
  have h :=
    M.integral_coordinateProduct_eq_wickPairingSum k ps.get
  unfold wickPairingSum at h
  rw [← wickPairingList_map] at h
  have hleft (ω : M.Ω) :
      (List.ofFn
        (fun i => M.coordinateVector k ω (ps.get i))).prod =
        (ps.map (fun p => M.coordinateVector k ω p)).prod := by
    rw [List.ofFn_comp' ps.get
      (fun p => M.coordinateVector k ω p), List.ofFn_get]
  have hright :
      List.map ps.get (List.ofFn id) = ps := by
    rw [List.map_ofFn]
    simpa only [Function.comp_def, id_eq] using List.ofFn_get ps
  calc
    (∫ ω, (ps.map (fun p => M.coordinateVector k ω p)).prod
        ∂(volume : Measure M.Ω)) =
        ∫ ω, ∏ i, M.coordinateVector k ω (ps.get i)
          ∂(volume : Measure M.Ω) := by
      apply integral_congr_ae
      filter_upwards with ω
      exact (hleft ω).symm.trans List.prod_ofFn
    _ = wickPairingList (M.coordinateCovariance k)
        (List.map ps.get (List.ofFn id)) := h
    _ = wickPairingList (M.coordinateCovariance k) ps := by
      rw [hright]

end NoiseModel

end

end Anderson4D
