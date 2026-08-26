import Anderson4D.ForMathlib.GaussianMoments
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# A characteristic-function moment method

The project only needs the one-dimensional Cramér--Wold form of the
Gaussian moment method.  This file derives it directly from Taylor's
theorem for characteristic functions.  An even moment controls the
Taylor remainder uniformly, so convergence of all raw moments to a
Gaussian law implies convergence of the characteristic function.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology

/-- The degree-`N-1` Taylor polynomial at frequency one, written in
terms of the first `N` raw moments. -/
def momentPolynomialOne (μ : Measure ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N,
    ((Nat.factorial k : ℂ)⁻¹ * Complex.I ^ k) *
      (∫ x, x ^ k ∂μ : ℝ)

/-- The norm of the `2q`-th derivative of a characteristic function is
bounded by the corresponding even raw moment. -/
theorem norm_iteratedDeriv_charFun_le_evenMoment
    (μ : Measure ℝ) [IsFiniteMeasure μ] (q : ℕ)
    (hmem : MemLp id (2 * q : ℕ) μ) (t : ℝ) :
    ‖iteratedDeriv (2 * q) (charFun μ) t‖ ≤
      ∫ x, x ^ (2 * q) ∂μ := by
  rw [iteratedDeriv_charFun hmem]
  calc
    ‖Complex.I ^ (2 * q) *
        ∫ x, (x ^ (2 * q) : ℂ) *
          Complex.exp (t * x * Complex.I) ∂μ‖ =
        ‖∫ x, (x ^ (2 * q) : ℂ) *
          Complex.exp (t * x * Complex.I) ∂μ‖ := by
      rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
    _ ≤ ∫ x, ‖(x ^ (2 * q) : ℂ) *
          Complex.exp (t * x * Complex.I)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = ∫ x, x ^ (2 * q) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      have htx :
          (t : ℂ) * (x : ℂ) = ((t * x : ℝ) : ℂ) := by
        norm_num
      rw [Complex.norm_mul, Complex.norm_pow, Complex.norm_real,
        htx, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs,
        (even_two_mul q).pow_abs]

/-- Taylor's theorem at frequency one, with the remainder controlled by
one even moment.  The polynomial contains all degrees below `2(q+1)`. -/
theorem norm_charFun_one_sub_momentPolynomial_le
    (μ : Measure ℝ) [IsFiniteMeasure μ] (q : ℕ)
    (hmem : MemLp id (2 * (q + 1) : ℕ) μ) :
    ‖charFun μ 1 - momentPolynomialOne μ (2 * (q + 1))‖ ≤
      (∫ x, x ^ (2 * (q + 1)) ∂μ) /
        (Nat.factorial (2 * q + 1) : ℝ) := by
  let N : ℕ := 2 * (q + 1)
  let n : ℕ := 2 * q + 1
  have hN : n + 1 = N := by
    dsimp only [N, n]
    omega
  have hdiff : ContDiff ℝ N (charFun μ) :=
    contDiff_charFun hmem
  have htaylor :
      taylorWithinEval (charFun μ) n (Set.Icc 0 1) 0 1 =
        taylorWithinEval (charFun μ) n Set.univ 0 1 := by
    rw [taylor_within_apply, taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    apply congrArg (fun z : ℂ =>
      (((Nat.factorial k : ℝ)⁻¹ * (1 - 0) ^ k) : ℝ) • z)
    have hkNnat : k ≤ N := by
      rw [Finset.mem_range] at hk
      rw [← hN]
      omega
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
      (hdiff.contDiffAt.of_le (by exact_mod_cast hkNnat))
      (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)]
    exact congrFun iteratedDerivWithin_univ 0 |>.symm
  have hnmem : MemLp id n μ := by
    have hnNnat : n ≤ N := by
      rw [← hN]
      omega
    exact hmem.mono_exponent (by exact_mod_cast hnNnat)
  have hpoly :=
    taylorWithinEval_charFun_zero (μ := μ) hnmem (1 : ℝ)
  have hpoly' :
      taylorWithinEval (charFun μ) n (Set.Icc 0 1) 0 1 =
        momentPolynomialOne μ N := by
    unfold momentPolynomialOne
    rw [htaylor, hpoly, hN]
    simp only [Complex.ofReal_one, one_mul]
  have hrem :=
    taylor_mean_remainder_bound
      (f := charFun μ) (a := (0 : ℝ)) (b := 1)
      (C := ∫ x, x ^ N ∂μ) (x := 1) (n := n)
      (by norm_num)
      (by
        simpa [← hN] using hdiff.contDiffOn)
      (by norm_num)
      (by
        intro y hy
        rw [hN]
        rw [iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
          hdiff.contDiffAt hy]
        exact norm_iteratedDeriv_charFun_le_evenMoment
          μ (q + 1) hmem y)
  rw [hpoly'] at hrem
  dsimp only [N, n] at hrem ⊢
  simpa using hrem

/-- Convergence of finitely many raw moments gives convergence of the
corresponding characteristic-function Taylor polynomials. -/
theorem tendsto_momentPolynomialOne
    {ι : Type*} {l : Filter ι}
    (μ : ι → Measure ℝ) (μ₀ : Measure ℝ) (N : ℕ)
    (hmom : ∀ n : ℕ,
      Tendsto (fun i => ∫ x, x ^ n ∂μ i) l
        (𝓝 (∫ x, x ^ n ∂μ₀))) :
    Tendsto (fun i => momentPolynomialOne (μ i) N) l
      (𝓝 (momentPolynomialOne μ₀ N)) := by
  unfold momentPolynomialOne
  apply tendsto_finsetSum
  intro k hk
  exact Tendsto.const_mul _
    ((hmom k).ofReal)

/-- **One-dimensional Gaussian moment method, characteristic-function
form.**  If all raw moments converge and the even-moment Taylor remainder
of the target tends to zero, then the characteristic functions converge
at frequency one.

The tail premise is precisely what Gaussian moment determinacy supplies;
it is separated so this theorem is reusable for any moment-determinate
target law. -/
theorem tendsto_charFun_one_of_moments
    {ι : Type*} {l : Filter ι}
    (μ : ι → Measure ℝ) (μ₀ : Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [IsFiniteMeasure μ₀]
    (hmem : ∀ (i : ι) (n : ℕ), MemLp id n (μ i))
    (hmem₀ : ∀ n : ℕ, MemLp id n μ₀)
    (hmom : ∀ n : ℕ,
      Tendsto (fun i => ∫ x, x ^ n ∂μ i) l
        (𝓝 (∫ x, x ^ n ∂μ₀)))
    (htail :
      Tendsto
        (fun q =>
          (∫ x, x ^ (2 * (q + 1)) ∂μ₀) /
            (Nat.factorial (2 * q + 1) : ℝ))
        atTop (𝓝 0)) :
    Tendsto (fun i => charFun (μ i) 1) l
      (𝓝 (charFun μ₀ 1)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε12 : 0 < ε / 12 := by positivity
  obtain ⟨q, hq⟩ :=
    (Metric.tendsto_atTop.mp htail) (ε / 12) hε12
  let N : ℕ := 2 * (q + 1)
  let denom : ℝ := Nat.factorial (2 * q + 1)
  let targetTail : ℝ :=
    (∫ x, x ^ N ∂μ₀) / denom
  have htargetTail : targetTail < ε / 12 := by
    have hq' := hq q le_rfl
    dsimp only [targetTail, N, denom]
    rw [Real.dist_eq, sub_zero] at hq'
    exact (le_abs_self _).trans_lt hq'
  have hscaled :
      Tendsto
        (fun i => (∫ x, x ^ N ∂μ i) / denom) l
        (𝓝 targetTail) := by
    dsimp only [targetTail]
    exact (hmom N).div_const denom
  have hpoly :=
    tendsto_momentPolynomialOne μ μ₀ N hmom
  have hscaled_event :
      ∀ᶠ i in l,
        (∫ x, x ^ N ∂μ i) / denom <
          targetTail + ε / 12 := by
    have h :=
      (Metric.tendsto_nhds.mp hscaled) (ε / 12) hε12
    filter_upwards [h] with i hi
    rw [Real.dist_eq] at hi
    linarith [le_abs_self
      ((∫ x, x ^ N ∂μ i) / denom - targetTail)]
  have hpoly_event :
      ∀ᶠ i in l,
        ‖momentPolynomialOne (μ i) N -
          momentPolynomialOne μ₀ N‖ < ε / 3 := by
    have h :=
      (Metric.tendsto_nhds.mp hpoly) (ε / 3) (by positivity)
    simpa only [dist_eq_norm] using h
  filter_upwards [hscaled_event, hpoly_event] with i hsourceTail hpolyClose
  have hsourceRem :
      ‖charFun (μ i) 1 - momentPolynomialOne (μ i) N‖ <
        ε / 6 := by
    have hrem :=
      norm_charFun_one_sub_momentPolynomial_le
        (μ i) q (hmem i N)
    dsimp only [N, denom] at hrem hsourceTail ⊢
    exact hrem.trans_lt (by linarith)
  have htargetRem :
      ‖momentPolynomialOne μ₀ N - charFun μ₀ 1‖ <
        ε / 12 := by
    have hrem :=
      norm_charFun_one_sub_momentPolynomial_le
        μ₀ q (hmem₀ N)
    rw [← norm_neg,
      neg_sub (momentPolynomialOne μ₀ N) (charFun μ₀ 1)]
    exact hrem.trans_lt (by
      simpa only [targetTail, N, denom] using htargetTail)
  rw [dist_eq_norm]
  calc
    ‖charFun (μ i) 1 - charFun μ₀ 1‖ =
        ‖(charFun (μ i) 1 - momentPolynomialOne (μ i) N) +
          (momentPolynomialOne (μ i) N - momentPolynomialOne μ₀ N) +
          (momentPolynomialOne μ₀ N - charFun μ₀ 1)‖ := by
      congr 1
      ring
    _ ≤ ‖charFun (μ i) 1 - momentPolynomialOne (μ i) N‖ +
          ‖momentPolynomialOne (μ i) N - momentPolynomialOne μ₀ N‖ +
          ‖momentPolynomialOne μ₀ N - charFun μ₀ 1‖ := by
      calc
        _ ≤
            ‖(charFun (μ i) 1 - momentPolynomialOne (μ i) N) +
              (momentPolynomialOne (μ i) N -
                momentPolynomialOne μ₀ N)‖ +
              ‖momentPolynomialOne μ₀ N - charFun μ₀ 1‖ :=
          norm_add_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_add_le _ _
    _ < ε := by linarith

/-- The double-factorial pairing count divided by the adjacent odd
factorial.  This is the factorial gain behind Gaussian moment
determinacy. -/
theorem gaussianPairingCount_succ_div_oddFactorial (q : ℕ) :
    (gaussianPairingCount (q + 1) : ℝ) /
        (Nat.factorial (2 * q + 1) : ℝ) =
      1 / ((2 : ℝ) ^ q * (Nat.factorial q : ℝ)) := by
  induction q with
  | zero =>
      norm_num [gaussianPairingCount]
  | succ q ih =>
      rw [gaussianPairingCount]
      have hfac :
          Nat.factorial (2 * (q + 1) + 1) =
            (2 * q + 3) * (2 * q + 2) *
              Nat.factorial (2 * q + 1) := by
        rw [show 2 * (q + 1) + 1 = (2 * q + 1) + 2 by omega,
          Nat.factorial_succ, Nat.factorial_succ]
        ring
      rw [hfac]
      push_cast
      have hq1 : (q + 1 : ℝ) ≠ 0 := by positivity
      have hodd : (2 * q + 3 : ℝ) ≠ 0 := by positivity
      have hfacq : (Nat.factorial q : ℝ) ≠ 0 := by positivity
      have hfacodd : (Nat.factorial (2 * q + 1) : ℝ) ≠ 0 := by
        positivity
      have hfacsucc :
          (Nat.factorial (q + 1) : ℝ) =
            (q + 1 : ℝ) * (Nat.factorial q : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hfacsucc, pow_succ]
      field_simp at ih ⊢
      ring_nf at ih ⊢
      nlinarith

/-- The Taylor remainders supplied by the even moments of a centered
Gaussian tend to zero. -/
theorem centeredGaussianMoment_tail_tendsto_zero (v : ℝ≥0) :
    Tendsto
      (fun q =>
        centeredGaussianMoment v (2 * (q + 1)) /
          (Nat.factorial (2 * q + 1) : ℝ))
      atTop (𝓝 0) := by
  have heq (q : ℕ) :
      centeredGaussianMoment v (2 * (q + 1)) /
          (Nat.factorial (2 * q + 1) : ℝ) =
        (v : ℝ) *
          (((v : ℝ) / 2) ^ q /
            (Nat.factorial q : ℝ)) := by
    rw [centeredGaussianMoment_even v (q + 1)]
    calc
      (gaussianPairingCount (q + 1) : ℝ) * (v : ℝ) ^ (q + 1) /
            (Nat.factorial (2 * q + 1) : ℝ) =
          ((gaussianPairingCount (q + 1) : ℝ) /
            (Nat.factorial (2 * q + 1) : ℝ)) *
              (v : ℝ) ^ (q + 1) := by ring
      _ = (1 / ((2 : ℝ) ^ q * (Nat.factorial q : ℝ))) *
            (v : ℝ) ^ (q + 1) := by
          rw [gaussianPairingCount_succ_div_oddFactorial q]
      _ = (v : ℝ) *
            (((v : ℝ) / 2) ^ q /
              (Nat.factorial q : ℝ)) := by
          have hfac : (Nat.factorial q : ℝ) ≠ 0 := by positivity
          rw [div_pow]
          field_simp
          ring
  have hzero :
      Tendsto
        (fun q => ((v : ℝ) / 2) ^ q /
          (Nat.factorial q : ℝ))
        atTop (𝓝 0) :=
    (Real.summable_pow_div_factorial ((v : ℝ) / 2)).tendsto_atTop_zero
  have hmul :
      Tendsto
        (fun q => (v : ℝ) *
          (((v : ℝ) / 2) ^ q / (Nat.factorial q : ℝ)))
        atTop (𝓝 0) := by
    simpa using Tendsto.const_mul (v : ℝ) hzero
  exact hmul.congr'
    (Filter.Eventually.of_forall fun q => (heq q).symm)

/-- Gaussian specialization of `tendsto_charFun_one_of_moments`. -/
theorem tendsto_charFun_one_of_moments_gaussian
    {ι : Type*} {l : Filter ι}
    (μ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (v : ℝ≥0)
    (hmem : ∀ (i : ι) (n : ℕ), MemLp id n (μ i))
    (hmom : ∀ n : ℕ,
      Tendsto (fun i => ∫ x, x ^ n ∂μ i) l
        (𝓝 (centeredGaussianMoment v n))) :
    Tendsto (fun i => charFun (μ i) 1) l
      (𝓝 (charFun (gaussianReal 0 v) 1)) := by
  apply tendsto_charFun_one_of_moments
    μ (gaussianReal 0 v) hmem
  · intro n
    exact memLp_id_gaussianReal' n (by simp)
  · simpa only [centeredGaussianMoment] using hmom
  · simpa only [centeredGaussianMoment] using
      centeredGaussianMoment_tail_tendsto_zero v

end

end Anderson4D
