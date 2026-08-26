import Anderson4D.Probability.NoiseIsserlis

/-!
# Complex Isserlis formulas for Fourier noise

The analytic Isserlis theorem in `NoiseIsserlis` is stated for arbitrary
real and imaginary coordinates of a finite Fourier vector.  This file
performs the finite complexification needed by the random-parametrix layer.
Every complex Fourier coefficient is expanded as `re + I * im`; the
resulting finite sum is then evaluated by the already proved real
coordinate Isserlis formula.

The definition `complexNoiseWickPairingSum` deliberately retains both
finite layers of the calculation: the outer sum chooses real or imaginary
coordinates, while the inner `wickPairingSum` sums over full pairings.
Thus it is useful without imposing circularity or independence assumptions
on the complex Gaussian vector.  For `NoiseModel.g`, its two-point
contractions reduce to the exact Fourier covariance in `NoiseModel.cov_pair`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory Complex ComplexConjugate
open scoped BigOperators ENNReal

namespace NoiseModel

variable (M : NoiseModel)

/-- Coefficient contributed by a choice of real (`false`) or imaginary
(`true`) coordinate at every position of a complex product. -/
def complexCoordinateCoefficient {n : ℕ} (σ : Fin n → Bool) : ℂ :=
  ∏ i, if σ i then I else 1

/-- The real-coordinate covariance matrix selected by `σ`. -/
def selectedCoordinateCovariance {n : ℕ} (k : Fin n → Z4)
    (σ : Fin n → Bool) (i j : Fin n) : ℝ :=
  M.coordinateCovariance k (i, σ i) (j, σ j)

/-- Complex Wick sum obtained by expanding every complex coordinate into
real and imaginary parts and applying the real Isserlis formula to each
choice.  The inner term is a genuine full-pairing sum. -/
def complexNoiseWickPairingSum {n : ℕ} (k : Fin n → Z4) : ℂ :=
  ∑ σ : Fin n → Bool,
    complexCoordinateCoefficient σ *
      (wickPairingSum (M.selectedCoordinateCovariance k σ) : ℂ)

@[simp]
theorem complexCoordinateCoefficient_zero
    (σ : Fin 0 → Bool) :
    complexCoordinateCoefficient σ = 1 := by
  simp [complexCoordinateCoefficient]

@[simp]
theorem complexNoiseWickPairingSum_zero (k : Fin 0 → Z4) :
    M.complexNoiseWickPairingSum k = 1 := by
  simp [complexNoiseWickPairingSum]

private theorem g_eq_coordinate_parts {n : ℕ}
    (k : Fin n → Z4) (i : Fin n) (ω : M.Ω) :
    M.g (k i) ω =
      (M.coordinateVector k ω (i, false) : ℂ) +
        I * M.coordinateVector k ω (i, true) := by
  simp [coordinateVector]
  apply Complex.ext <;> simp

/-- Pointwise expansion of a finite complex Fourier product into products
of selected real/imaginary coordinates. -/
theorem product_g_eq_sum_coordinateProducts {n : ℕ}
    (k : Fin n → Z4) (ω : M.Ω) :
    (∏ i, M.g (k i) ω) =
      ∑ σ : Fin n → Bool,
        complexCoordinateCoefficient σ *
          ((∏ i, M.coordinateVector k ω (i, σ i) : ℝ) : ℂ) := by
  classical
  simp_rw [M.g_eq_coordinate_parts k]
  calc
    (∏ i,
        ((M.coordinateVector k ω (i, false) : ℂ) +
          I * M.coordinateVector k ω (i, true))) =
        ∏ i, ∑ b : Bool,
          if b then
            I * M.coordinateVector k ω (i, true)
          else
            (M.coordinateVector k ω (i, false) : ℂ) := by
      apply Finset.prod_congr rfl
      intro i _hi
      simp_rw [Fintype.sum_bool]
      simp
      ring
    _ = ∑ σ : Fin n → Bool, ∏ i,
        if σ i then
          I * M.coordinateVector k ω (i, true)
        else
          (M.coordinateVector k ω (i, false) : ℂ) := by
      rw [Fintype.prod_sum]
    _ = ∑ σ : Fin n → Bool,
        complexCoordinateCoefficient σ *
          ((∏ i, M.coordinateVector k ω (i, σ i) : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro σ _hσ
      simp only [complexCoordinateCoefficient, Complex.ofReal_prod]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _hi
      cases hσi : σ i <;> simp

/-- Every finite product of complex Fourier coefficients is genuinely
integrable. -/
theorem integrable_g_product {n : ℕ} (k : Fin n → Z4) :
    Integrable (fun ω => ∏ i, M.g (k i) ω)
      (volume : Measure M.Ω) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hprod :=
      MemLp.prod'
        (s := (Finset.univ : Finset (Fin n)))
        (p := fun _ : Fin n => (n : ℝ≥0∞))
        (f := fun i ω => M.g (k i) ω)
        (fun i _hi => M.memLp_g (k i) n (by simp))
    have hLp :
        MemLp (fun ω => ∏ i, M.g (k i) ω) 1
          (volume : Measure M.Ω) := by
      have hcast :
          (n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (by exact_mod_cast hn) (by simp)
      have hsum :
          (∑ _ : Fin n, ((n : ℝ≥0∞)⁻¹)) = 1 := by
        simpa only [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul] using hcast
      rw [hsum] at hprod
      simpa only [inv_one] using hprod
    exact hLp.integrable le_rfl

/-- Complex Isserlis formula for an arbitrary finite family of Fourier
coordinates, with repetitions allowed. -/
theorem integral_g_product_eq_complexNoiseWickPairingSum
    {n : ℕ} (k : Fin n → Z4) :
    (∫ ω, ∏ i, M.g (k i) ω
        ∂(volume : Measure M.Ω)) =
      M.complexNoiseWickPairingSum k := by
  classical
  calc
    (∫ ω, ∏ i, M.g (k i) ω
        ∂(volume : Measure M.Ω)) =
        ∫ ω, ∑ σ : Fin n → Bool,
          complexCoordinateCoefficient σ *
            ((∏ i, M.coordinateVector k ω (i, σ i) : ℝ) : ℂ)
          ∂(volume : Measure M.Ω) := by
      apply integral_congr_ae
      filter_upwards with ω
      exact M.product_g_eq_sum_coordinateProducts k ω
    _ = ∑ σ : Fin n → Bool,
        ∫ ω, complexCoordinateCoefficient σ *
          ((∏ i, M.coordinateVector k ω (i, σ i) : ℝ) : ℂ)
          ∂(volume : Measure M.Ω) := by
      rw [integral_finsetSum]
      intro σ _hσ
      exact
        ((M.integrable_coordinateProduct k
          (fun i => (i, σ i))).ofReal.const_mul
            (complexCoordinateCoefficient σ))
    _ = ∑ σ : Fin n → Bool,
        complexCoordinateCoefficient σ *
          (∫ ω, ∏ i, M.coordinateVector k ω (i, σ i)
            ∂(volume : Measure M.Ω) : ℝ) := by
      apply Finset.sum_congr rfl
      intro σ _hσ
      rw [integral_const_mul, integral_complex_ofReal]
    _ = M.complexNoiseWickPairingSum k := by
      unfold complexNoiseWickPairingSum
      apply Finset.sum_congr rfl
      intro σ _hσ
      rw [M.integral_coordinateProduct_eq_wickPairingSum k
        (fun i => (i, σ i))]
      rfl

/-- Odd complex Fourier moments vanish. -/
theorem integral_g_product_odd_eq_zero
    (q : ℕ) (k : Fin (2 * q + 1) → Z4) :
    (∫ ω, ∏ i, M.g (k i) ω
        ∂(volume : Measure M.Ω)) = 0 := by
  rw [M.integral_g_product_eq_complexNoiseWickPairingSum k]
  unfold complexNoiseWickPairingSum
  apply Finset.sum_eq_zero
  intro σ _hσ
  rw [wickPairingSum_odd]
  simp

/-- The two-entry mode vector used to expose the complex contraction of
the general Wick sum. -/
def twoModes (k l : Z4) : Fin 2 → Z4 :=
  ![k, l]

@[simp]
theorem twoModes_zero (k l : Z4) :
    twoModes k l 0 = k := rfl

@[simp]
theorem twoModes_one (k l : Z4) :
    twoModes k l 1 = l := rfl

/-- At order two, the complexified Wick sum is exactly the Fourier
covariance contraction `1_{k=-l}`. -/
theorem complexNoiseWickPairingSum_two (k l : Z4) :
    M.complexNoiseWickPairingSum (twoModes k l) =
      if k = -l then 1 else 0 := by
  rw [← M.integral_g_product_eq_complexNoiseWickPairingSum
    (twoModes k l)]
  simpa [twoModes, Fin.prod_univ_succ] using M.cov_pair k l

/-- Replace a conjugated Fourier coordinate by its negative mode, using the
reality relation. -/
def orientedMode {n : ℕ} (k : Fin n → Z4)
    (conjugated : Fin n → Bool) (i : Fin n) : Z4 :=
  if conjugated i then -k i else k i

/-- A Fourier coordinate which may be conjugated independently at every
position. -/
def orientedG {n : ℕ} (k : Fin n → Z4)
    (conjugated : Fin n → Bool) (i : Fin n) (ω : M.Ω) : ℂ :=
  if conjugated i then conj (M.g (k i) ω) else M.g (k i) ω

@[simp]
theorem orientedG_eq_g_orientedMode {n : ℕ}
    (k : Fin n → Z4) (conjugated : Fin n → Bool)
    (i : Fin n) (ω : M.Ω) :
    M.orientedG k conjugated i ω =
      M.g (orientedMode k conjugated i) ω := by
  cases hconj : conjugated i <;>
    simp [orientedG, orientedMode, hconj, M.reality]

/-- Isserlis formula allowing arbitrary conjugations of the Fourier
coordinates.  Conjugation is absorbed into mode negation before applying
the complex Wick sum. -/
theorem integral_orientedG_product_eq_complexNoiseWickPairingSum
    {n : ℕ} (k : Fin n → Z4) (conjugated : Fin n → Bool) :
    (∫ ω, ∏ i, M.orientedG k conjugated i ω
        ∂(volume : Measure M.Ω)) =
      M.complexNoiseWickPairingSum
        (orientedMode k conjugated) := by
  calc
    (∫ ω, ∏ i, M.orientedG k conjugated i ω
        ∂(volume : Measure M.Ω)) =
        ∫ ω, ∏ i, M.g (orientedMode k conjugated i) ω
          ∂(volume : Measure M.Ω) := by
      apply integral_congr_ae
      filter_upwards with ω
      apply Finset.prod_congr rfl
      intro i _hi
      exact M.orientedG_eq_g_orientedMode k conjugated i ω
    _ = M.complexNoiseWickPairingSum
          (orientedMode k conjugated) :=
      M.integral_g_product_eq_complexNoiseWickPairingSum
        (orientedMode k conjugated)

/-- Every odd product of Fourier coordinates and their conjugates has zero
expectation. -/
theorem integral_orientedG_product_odd_eq_zero
    (q : ℕ) (k : Fin (2 * q + 1) → Z4)
    (conjugated : Fin (2 * q + 1) → Bool) :
    (∫ ω, ∏ i, M.orientedG k conjugated i ω
        ∂(volume : Measure M.Ω)) = 0 := by
  rw [M.integral_orientedG_product_eq_complexNoiseWickPairingSum]
  rw [← M.integral_g_product_eq_complexNoiseWickPairingSum]
  exact M.integral_g_product_odd_eq_zero q
    (orientedMode k conjugated)

/-- Every finite complex linear combination of the Fourier coordinates has
arbitrary finite `Lᵖ` moments. -/
theorem memLp_finiteNoiseCombination
    (s : Finset Z4) (a : Z4 → ℂ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (M.finiteNoiseCombination s a) p
      (volume : Measure M.Ω) := by
  unfold finiteNoiseCombination
  apply memLp_finsetSum
  intro k _hk
  exact (M.memLp_g k p hp).const_mul (a k)

/-- Wick sum for a product of possibly different finite complex linear
combinations, all written on one finite support.  The outer finite sum
chooses one Fourier mode from each factor. -/
def finiteCombinationWickPairingSum {n : ℕ}
    (s : Finset Z4) (a : Fin n → Z4 → ℂ) : ℂ :=
  ∑ modes : Fin n → ↥s,
    (∏ i, a i (modes i)) *
      M.complexNoiseWickPairingSum (fun i => (modes i : Z4))

/-- Pointwise expansion of a product of finite complex noise
combinations. -/
theorem product_finiteNoiseCombination_eq_sum {n : ℕ}
    (s : Finset Z4) (a : Fin n → Z4 → ℂ) (ω : M.Ω) :
    (∏ i, M.finiteNoiseCombination s (a i) ω) =
      ∑ modes : Fin n → ↥s,
        (∏ i, a i (modes i)) *
          ∏ i, M.g (modes i) ω := by
  classical
  unfold finiteNoiseCombination
  calc
    (∏ i, ∑ k ∈ s, a i k * M.g k ω) =
        ∏ i, ∑ k : ↥s, a i k * M.g k ω := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact
        (Finset.sum_attach s
          (fun k => a i k * M.g k ω)).symm
    _ = ∑ modes : Fin n → ↥s,
        ∏ i, a i (modes i) * M.g (modes i) ω := by
      rw [Fintype.prod_sum]
    _ = ∑ modes : Fin n → ↥s,
        (∏ i, a i (modes i)) *
          ∏ i, M.g (modes i) ω := by
      apply Finset.sum_congr rfl
      intro modes _hmodes
      rw [Finset.prod_mul_distrib]

/-- A finite product of finite complex noise combinations is integrable. -/
theorem integrable_finiteNoiseCombination_product {n : ℕ}
    (s : Finset Z4) (a : Fin n → Z4 → ℂ) :
    Integrable
      (fun ω => ∏ i, M.finiteNoiseCombination s (a i) ω)
      (volume : Measure M.Ω) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hprod :=
      MemLp.prod'
        (s := (Finset.univ : Finset (Fin n)))
        (p := fun _ : Fin n => (n : ℝ≥0∞))
        (f := fun i ω => M.finiteNoiseCombination s (a i) ω)
        (fun i _hi =>
          M.memLp_finiteNoiseCombination s (a i) n (by simp))
    have hcast :
        (n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel (by exact_mod_cast hn) (by simp)
    have hsum :
        (∑ _ : Fin n, ((n : ℝ≥0∞)⁻¹)) = 1 := by
      simpa only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] using hcast
    rw [hsum] at hprod
    have hLp :
        MemLp
          (fun ω => ∏ i, M.finiteNoiseCombination s (a i) ω)
          1 (volume : Measure M.Ω) := by
      simpa only [inv_one] using hprod
    exact hLp.integrable le_rfl

/-- High-order Isserlis formula for an arbitrary finite family of finite
complex linear combinations of Fourier noise. -/
theorem integral_finiteNoiseCombination_product_eq_wick
    {n : ℕ} (s : Finset Z4) (a : Fin n → Z4 → ℂ) :
    (∫ ω, ∏ i, M.finiteNoiseCombination s (a i) ω
        ∂(volume : Measure M.Ω)) =
      M.finiteCombinationWickPairingSum s a := by
  classical
  calc
    (∫ ω, ∏ i, M.finiteNoiseCombination s (a i) ω
        ∂(volume : Measure M.Ω)) =
        ∫ ω, ∑ modes : Fin n → ↥s,
          (∏ i, a i (modes i)) *
            ∏ i, M.g (modes i) ω
          ∂(volume : Measure M.Ω) := by
      apply integral_congr_ae
      filter_upwards with ω
      exact M.product_finiteNoiseCombination_eq_sum s a ω
    _ = ∑ modes : Fin n → ↥s,
        ∫ ω, (∏ i, a i (modes i)) *
          ∏ i, M.g (modes i) ω
          ∂(volume : Measure M.Ω) := by
      rw [integral_finsetSum]
      intro modes _hmodes
      exact
        (M.integrable_g_product
          (fun i => (modes i : Z4))).const_mul
            (∏ i, a i (modes i))
    _ = ∑ modes : Fin n → ↥s,
        (∏ i, a i (modes i)) *
          M.complexNoiseWickPairingSum
            (fun i => (modes i : Z4)) := by
      apply Finset.sum_congr rfl
      intro modes _hmodes
      rw [integral_const_mul,
        M.integral_g_product_eq_complexNoiseWickPairingSum]
    _ = M.finiteCombinationWickPairingSum s a := rfl

end NoiseModel

end

end Anderson4D
