import Anderson4D.Probability.GaussianPolynomialMoments
import Anderson4D.Probability.MollifiedGaussian
import Anderson4D.Probability.CovariancePoisson

/-!
# Wick orthogonality for the mollified noise

This file instantiates the generic polynomial Wick theorem for `xiEps`,
then specializes it to the two `wickAt` factors in the random parametrix.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal RealInnerProductSpace

namespace NoiseModel

variable (M : NoiseModel)

theorem hasGaussianLaw_xiEps
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (z : T4) :
    HasGaussianLaw (fun ω => M.xiEps ρ ε ω z)
      (volume : Measure M.Ω) := by
  let x : Fin 1 → T4 := fun _ => z
  let a : Fin 1 → ℝ := fun _ => 1
  have h := M.hasGaussianLaw_xiEpsLinearCombination ρ hε x a
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [xiEpsLinearCombination, x, a]

theorem memLp_xiEps
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (z : T4)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun ω => M.xiEps ρ ε ω z) p
      (volume : Measure M.Ω) :=
  (M.hasGaussianLaw_xiEps ρ hε z).memLp hp

theorem integrable_xiEpsProduct {r : ℕ}
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (z : Fin r → T4) :
    Integrable (fun ω => ∏ i, M.xiEps ρ ε ω (z i))
      (volume : Measure M.Ω) := by
  by_cases hr : r = 0
  · subst r
    simp
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hprod :=
      MemLp.prod'
        (s := (Finset.univ : Finset (Fin r)))
        (p := fun _ : Fin r => (r : ℝ≥0∞))
        (f := fun i ω => M.xiEps ρ ε ω (z i))
        (fun i _hi => M.memLp_xiEps ρ hε (z i) r (by simp))
    have hLp :
        MemLp (fun ω => ∏ i, M.xiEps ρ ε ω (z i)) 1
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

theorem integrable_xiEpsListProduct
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (zs : List T4) :
    Integrable
      (gaussianListProduct
        (fun z ω => M.xiEps ρ ε ω z) zs)
      (volume : Measure M.Ω) := by
  refine (M.integrable_xiEpsProduct ρ hε zs.get).congr ?_
  filter_upwards with ω
  unfold gaussianListProduct
  rw [← List.prod_ofFn, List.ofFn_comp' zs.get
    (fun z => M.xiEps ρ ε ω z), List.ofFn_get]

private theorem xiEps_inner_basis {r : ℕ}
    (i : Fin r) (y : EuclideanSpace ℝ (Fin r)) :
    ⟪y, (EuclideanSpace.basisFun (Fin r) ℝ) i⟫ = y i := by
  simpa using EuclideanSpace.inner_single_right i (1 : ℝ) y

theorem integral_xiEpsProduct_even_eq_wickPairingSum
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (q : ℕ)
    (z : Fin (2 * q) → T4) :
    (∫ ω, ∏ i, M.xiEps ρ ε ω (z i)
        ∂(volume : Measure M.Ω)) =
      wickPairingSum
        (fun i j => ρ.etaEpsT4 ε (z i - z j)) := by
  let μE : Measure (EuclideanSpace ℝ (Fin (2 * q))) :=
    Measure.map (M.xiEpsEuclideanVector ρ ε z)
      (volume : Measure M.Ω)
  letI : IsGaussian μE :=
    M.isGaussian_map_xiEpsEuclideanVector ρ hε z
  let b : Fin (2 * q) → EuclideanSpace ℝ (Fin (2 * q)) :=
    fun i => (EuclideanSpace.basisFun (Fin (2 * q)) ℝ) i
  have hIsserlis :=
    centeredGaussian_mixedMoment_eq_wickPairingSum μE
      (M.integral_id_map_xiEpsEuclideanVector ρ hε z) q b
  have hmap :
      (∫ y, ∏ i, ⟪y, b i⟫ ∂μE) =
        ∫ ω, ∏ i, M.xiEps ρ ε ω (z i)
          ∂(volume : Measure M.Ω) := by
    rw [integral_map
      (M.measurable_xiEpsEuclideanVector ρ ε z).aemeasurable
      (Measurable.aestronglyMeasurable (by fun_prop))]
    apply integral_congr_ae
    filter_upwards with ω
    apply Finset.prod_congr rfl
    intro i _hi
    exact xiEps_inner_basis i
      (M.xiEpsEuclideanVector ρ ε z ω)
  have hcov (i j : Fin (2 * q)) :
      covarianceBilin μE (b i) (b j) =
        ρ.etaEpsT4 ε (z i - z j) := by
    change covarianceBilin
      (Measure.map
        (fun ω => WithLp.toLp 2
          (fun r => M.xiEps ρ ε ω (z r)))
        (volume : Measure M.Ω))
      ((EuclideanSpace.basisFun (Fin (2 * q)) ℝ) i)
      ((EuclideanSpace.basisFun (Fin (2 * q)) ℝ) j) =
        ρ.etaEpsT4 ε (z i - z j)
    calc
      _ = cov[(fun ω => M.xiEps ρ ε ω (z i)),
          (fun ω => M.xiEps ρ ε ω (z j));
          (volume : Measure M.Ω)] := by
        exact covarianceBilin_apply_basisFun
          (fun r => M.memLp_xiEps ρ hε (z r) 2 (by simp)) i j
      _ = ∫ ω,
          M.xiEps ρ ε ω (z i) * M.xiEps ρ ε ω (z j)
          ∂(volume : Measure M.Ω) := by
        rw [covariance_eq_sub
          (M.memLp_xiEps ρ hε (z i) 2 (by simp))
          (M.memLp_xiEps ρ hε (z j) 2 (by simp)),
          M.integral_xiEps ρ hε (z i),
          M.integral_xiEps ρ hε (z j)]
        simp
      _ = ρ.etaEpsT4 ε (z i - z j) :=
        M.integral_xiEps_mul_eq_etaEpsT4
          ρ hε (z i) (z j)
  calc
    (∫ ω, ∏ i, M.xiEps ρ ε ω (z i)
        ∂(volume : Measure M.Ω)) =
        ∫ y, ∏ i, ⟪y, b i⟫ ∂μE := hmap.symm
    _ = wickPairingSum
        (fun i j => covarianceBilin μE (b i) (b j)) := hIsserlis
    _ = wickPairingSum
        (fun i j => ρ.etaEpsT4 ε (z i - z j)) := by
      congr 2
      funext i j
      exact hcov i j

theorem integral_xiEpsProduct_odd_eq_zero
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (q : ℕ)
    (z : Fin (2 * q + 1) → T4) :
    (∫ ω, ∏ i, M.xiEps ρ ε ω (z i)
        ∂(volume : Measure M.Ω)) = 0 := by
  let μE : Measure (EuclideanSpace ℝ (Fin (2 * q + 1))) :=
    Measure.map (M.xiEpsEuclideanVector ρ ε z)
      (volume : Measure M.Ω)
  letI : IsGaussian μE :=
    M.isGaussian_map_xiEpsEuclideanVector ρ hε z
  let b : Fin (2 * q + 1) →
      EuclideanSpace ℝ (Fin (2 * q + 1)) :=
    fun i => (EuclideanSpace.basisFun (Fin (2 * q + 1)) ℝ) i
  have hIsserlis :=
    centeredGaussian_mixedMoment_odd_eq_zero μE
      (M.integral_id_map_xiEpsEuclideanVector ρ hε z) q b
  have hmap :
      (∫ y, ∏ i, ⟪y, b i⟫ ∂μE) =
        ∫ ω, ∏ i, M.xiEps ρ ε ω (z i)
          ∂(volume : Measure M.Ω) := by
    rw [integral_map
      (M.measurable_xiEpsEuclideanVector ρ ε z).aemeasurable
      (Measurable.aestronglyMeasurable (by fun_prop))]
    apply integral_congr_ae
    filter_upwards with ω
    apply Finset.prod_congr rfl
    intro i _hi
    exact xiEps_inner_basis i
      (M.xiEpsEuclideanVector ρ ε z ω)
  exact hmap.symm.trans hIsserlis

theorem integral_xiEpsProduct_eq_wickPairingSum {r : ℕ}
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (z : Fin r → T4) :
    (∫ ω, ∏ i, M.xiEps ρ ε ω (z i)
        ∂(volume : Measure M.Ω)) =
      wickPairingSum
        (fun i j => ρ.etaEpsT4 ε (z i - z j)) := by
  obtain ⟨q, hq | hq⟩ := r.even_or_odd'
  · subst r
    exact M.integral_xiEpsProduct_even_eq_wickPairingSum ρ hε q z
  · subst r
    rw [M.integral_xiEpsProduct_odd_eq_zero ρ hε q z,
      wickPairingSum_odd]

theorem integral_xiEpsListProduct_eq_wickPairingList
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (zs : List T4) :
    (∫ ω,
        gaussianListProduct
          (fun z ω => M.xiEps ρ ε ω z) zs ω
        ∂(volume : Measure M.Ω)) =
      wickPairingList
        (fun x y => ρ.etaEpsT4 ε (x - y)) zs := by
  have h :=
    M.integral_xiEpsProduct_eq_wickPairingSum ρ hε zs.get
  unfold wickPairingSum at h
  rw [← wickPairingList_map
    (fun x y => ρ.etaEpsT4 ε (x - y))
    zs.get (List.ofFn id)] at h
  have hleft (ω : M.Ω) :
      (List.ofFn
        (fun i => M.xiEps ρ ε ω (zs.get i))).prod =
        gaussianListProduct
          (fun z ω' => M.xiEps ρ ε ω' z) zs ω := by
    unfold gaussianListProduct
    rw [List.ofFn_comp' zs.get
      (fun z => M.xiEps ρ ε ω z), List.ofFn_get]
  have hright :
      List.map zs.get (List.ofFn id) = zs := by
    rw [List.map_ofFn]
    simpa only [Function.comp_def, id_eq] using List.ofFn_get zs
  calc
    (∫ ω,
        gaussianListProduct
          (fun z ω' => M.xiEps ρ ε ω' z) zs ω
        ∂(volume : Measure M.Ω)) =
        ∫ ω, ∏ i, M.xiEps ρ ε ω (zs.get i)
          ∂(volume : Measure M.Ω) := by
      apply integral_congr_ae
      filter_upwards with ω
      exact (hleft ω).symm.trans List.prod_ofFn
    _ = wickPairingList
        (fun x y => ρ.etaEpsT4 ε (x - y))
        (List.map zs.get (List.ofFn id)) := h
    _ = wickPairingList
        (fun x y => ρ.etaEpsT4 ε (x - y)) zs := by
      rw [hright]

/-- The whole spatial mollified-noise family satisfies the raw Isserlis
list-moment interface. -/
theorem gaussianListMomentLaw_xiEps
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) :
    GaussianListMomentLaw
      (volume : Measure M.Ω)
      (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
      (fun x ω => M.xiEps ρ ε ω x) where
  covariance_symm := by
    intro x y
    calc
      ρ.etaEpsT4 ε (x - y) =
          ∫ ω, M.xiEps ρ ε ω x * M.xiEps ρ ε ω y
            ∂(volume : Measure M.Ω) := by
        exact
          (M.integral_xiEps_mul_eq_etaEpsT4
            ρ hε x y).symm
      _ = ∫ ω, M.xiEps ρ ε ω y * M.xiEps ρ ε ω x
            ∂(volume : Measure M.Ω) := by
        apply integral_congr_ae
        filter_upwards with ω
        ring
      _ = ρ.etaEpsT4 ε (y - x) := by
        exact
          M.integral_xiEps_mul_eq_etaEpsT4
            ρ hε y x
  integrable_listProduct :=
    M.integrable_xiEpsListProduct ρ hε
  integral_listProduct :=
    M.integral_xiEpsListProduct_eq_wickPairingList ρ hε

/-- Polynomial Gaussian integration by parts for the mollified noise. -/
theorem gaussianPolynomialLaw_xiEps
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) :
    GaussianPolynomialLaw
      (volume : Measure M.Ω)
      (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
      (fun x ω => M.xiEps ρ ε ω x) :=
  (M.gaussianListMomentLaw_xiEps ρ hε).toGaussianPolynomialLaw

/-- Exact cross-contraction formula for two Wick polynomials of the
mollified noise. -/
theorem integral_wickPolynomial_xiEps_mul
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (xs ys : List T4) :
    (∫ ω,
        wickPolynomial
            (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
            (fun x ω' => M.xiEps ρ ε ω' x) xs ω *
          wickPolynomial
            (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
            (fun x ω' => M.xiEps ρ ε ω' x) ys ω
        ∂(volume : Measure M.Ω)) =
      crossWickList
        (fun x y : T4 => ρ.etaEpsT4 ε (x - y)) xs ys :=
  (M.gaussianPolynomialLaw_xiEps ρ hε).integral_wickPolynomial_mul xs ys

/-- Products of two mollified-noise Wick polynomials are integrable. -/
theorem integrable_wickPolynomial_xiEps_mul
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (xs ys : List T4) :
    Integrable
      (fun ω =>
        wickPolynomial
            (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
            (fun x ω' => M.xiEps ρ ε ω' x) xs ω *
          wickPolynomial
            (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
            (fun x ω' => M.xiEps ρ ε ω' x) ys ω)
      (volume : Measure M.Ω) :=
  (M.gaussianPolynomialLaw_xiEps ρ hε).integrable_wickPolynomial_mul xs ys

end NoiseModel

end

end Anderson4D
