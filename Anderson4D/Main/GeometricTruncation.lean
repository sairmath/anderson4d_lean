import Anderson4D.Main.TruncationGlue

/-!
# Geometric closure of the moving parametrix tail

This file turns the order-by-order `L¹` estimate obtained from paper
(3.24) into the uniform geometric truncation estimate (3.35).  It is
kept separate from the second-moment proof so that the latter only has
to expose its natural coefficient-level interface.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- On a probability space, Cauchy--Schwarz bounds the first absolute
moment by the square root of the second absolute moment. -/
theorem integral_norm_le_sqrt_integral_norm_sq
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → E)
    (hf : MemLp f 2 μ) :
    ∫ ω, ‖f ω‖ ∂μ ≤
      Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂μ) := by
  have hfnorm :
      MemLp (fun ω => ‖f ω‖) (ENNReal.ofReal 2) μ := by
    norm_num
    exact hf.norm
  have hone :
      MemLp (fun _ω : Ω => (1 : ℝ)) (ENNReal.ofReal 2) μ :=
    memLp_const 1
  have h :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := μ)
      Real.HolderConjugate.two_two
      (f := fun ω => ‖f ω‖) (g := fun _ω => (1 : ℝ))
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall fun _ => zero_le_one)
      hfnorm hone
  simpa [Real.sqrt_eq_rpow, Real.rpow_two] using h

/-- Convenient squared-bound form of the `L² → L¹` implication. -/
theorem integral_norm_le_of_integral_norm_sq_le_sq
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → E) (hf : MemLp f 2 μ)
    {R : ℝ} (hR : 0 ≤ R)
    (hsecond : ∫ ω, ‖f ω‖ ^ 2 ∂μ ≤ R ^ 2) :
    ∫ ω, ‖f ω‖ ∂μ ≤ R := by
  calc
    ∫ ω, ‖f ω‖ ∂μ ≤
        Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂μ) :=
      integral_norm_le_sqrt_integral_norm_sq μ f hf
    _ ≤ Real.sqrt (R ^ 2) :=
      Real.sqrt_le_sqrt hsecond
    _ = R :=
      Real.sqrt_sq hR

/-- A geometric `L¹` bound on the individual random coefficients gives
the exact finite-tail estimate needed in (3.35). -/
theorem Prop36.norm_fullParametrixChar_sub_fixed_le_geometric
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam)
    (ε : ℝ) {B A s : ℕ}
    (hA : truncOrder ε = A) (hBA : B ≤ A)
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (K q : ℝ) (hK : 0 ≤ K) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hlamEps : lamEps lam ε ≠ 0)
    (hcoeff : ∀ j : Fin s, ∀ m ∈ Finset.Ico B A,
      ∫ ω,
          ‖pmCoeff M ρ lam ε (m + 1)
            (modes j).1 (modes j).2 ω‖ ≤
        ‖(lamEps lam ε : ℂ)‖ * K * q ^ m) :
    ‖fullParametrixChar M ρ lam ε s modes c -
        charFun
          (fixedTruncationLaw M ρ lam ε B s modes c) 1‖ ≤
      (∑ j, ‖c j‖) * K * (q ^ B / (1 - q)) := by
  have htail :
      ∀ j : Fin s,
        ∑ m ∈ Finset.Ico B A,
            ∫ ω,
              ‖pmCoeff M ρ lam ε (m + 1)
                (modes j).1 (modes j).2 ω‖ ≤
          (‖(lamEps lam ε : ℂ)‖ * K) *
            (q ^ B / (1 - q)) := by
    intro j
    calc
      ∑ m ∈ Finset.Ico B A,
          ∫ ω,
            ‖pmCoeff M ρ lam ε (m + 1)
              (modes j).1 (modes j).2 ω‖ ≤
          ∑ m ∈ Finset.Ico B A,
            (‖(lamEps lam ε : ℂ)‖ * K) * q ^ m := by
        exact Finset.sum_le_sum fun m hm =>
          hcoeff j m hm
      _ = (‖(lamEps lam ε : ℂ)‖ * K) *
          ∑ m ∈ Finset.Ico B A, q ^ m := by
        rw [Finset.mul_sum]
      _ ≤ (‖(lamEps lam ε : ℂ)‖ * K) *
          (q ^ B / (1 - q)) := by
        gcongr
        exact geom_sum_Ico_le_of_lt_one hq0 hq1
  have hlamNorm :
      ‖(lamEps lam ε : ℂ)‖ ≠ 0 := by
    rw [norm_ne_zero_iff, Complex.ofReal_ne_zero]
    exact hlamEps
  have hcancel :
      ‖(lamEps lam ε : ℂ)⁻¹‖ *
          ‖(lamEps lam ε : ℂ)‖ = 1 := by
    rw [norm_inv]
    exact inv_mul_cancel₀ hlamNorm
  subst A
  calc
    ‖fullParametrixChar M ρ lam ε s modes c -
        charFun
          (fixedTruncationLaw M ρ lam ε B s modes c) 1‖ ≤
      ‖(lamEps lam ε : ℂ)⁻¹‖ *
        ∑ j, ‖c j‖ *
          ∑ m ∈ Finset.Ico B (truncOrder ε),
            ∫ ω,
              ‖pmCoeff M ρ lam ε (m + 1)
                (modes j).1 (modes j).2 ω‖ :=
      hP36.norm_fullParametrixChar_sub_fixed_le
        ε hBA modes c
    _ ≤ ‖(lamEps lam ε : ℂ)⁻¹‖ *
        ∑ j, ‖c j‖ *
          ((‖(lamEps lam ε : ℂ)‖ * K) *
            (q ^ B / (1 - q))) := by
      gcongr with j
      exact htail j
    _ = (∑ j, ‖c j‖) * K * (q ^ B / (1 - q)) := by
      rw [← Finset.sum_mul]
      calc
        ‖(lamEps lam ε : ℂ)⁻¹‖ *
            ((∑ j, ‖c j‖) *
              ((‖(lamEps lam ε : ℂ)‖ * K) *
                (q ^ B / (1 - q)))) =
            (‖(lamEps lam ε : ℂ)⁻¹‖ *
              ‖(lamEps lam ε : ℂ)‖) *
              ((∑ j, ‖c j‖) * K *
                (q ^ B / (1 - q))) := by
          ring
        _ = (∑ j, ‖c j‖) * K *
            (q ^ B / (1 - q)) := by
          rw [hcancel, one_mul]

/-- The geometric error appearing on the right of (3.35). -/
def geometricTruncationError
    {s : ℕ} (c : Fin s → ℂ) (K q : ℝ) (B : ℕ) : ℝ :=
  (∑ j, ‖c j‖) * K * (q ^ B / (1 - q))

/-- For a genuine geometric ratio, the truncation error vanishes as
`B → ∞`. -/
theorem tendsto_geometricTruncationError
    {s : ℕ} (c : Fin s → ℂ) {K q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (geometricTruncationError c K q)
      atTop (𝓝 0) := by
  have hpow :
      Tendsto (fun B : ℕ => q ^ B) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hdiv :
      Tendsto (fun B : ℕ => q ^ B / (1 - q))
        atTop (𝓝 0) := by
    simpa only [zero_div] using hpow.div_const (1 - q)
  have hmul :=
    hdiv.const_mul ((∑ j, ‖c j‖) * K)
  change
    Tendsto
      (fun B : ℕ =>
        (∑ j, ‖c j‖) * K * (q ^ B / (1 - q)))
      atTop (𝓝 0)
  simpa only [mul_zero] using hmul

/-- **Two-scale closure of paper Step 3.**

Once (3.24) has supplied a uniform geometric `L¹` bound for every
positive-order mode coefficient, the moving parametrix scalar converges
to the Gaussian characteristic function with variance `limitVar`.
This theorem performs the complete `ε → 0`, then `B → ∞` argument. -/
theorem Prop36.tendsto_fullParametrixChar_of_geometric_coeff_bound
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (hlam : 0 < lam)
    (hsmall : hP36.boundConstant * lam < 1)
    (hsub : lam ^ 2 < 2 * Real.pi ^ 2)
    {s : ℕ} (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (K q : ℝ) (hK : 0 ≤ K) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcoeff :
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        ∀ j : Fin s, ∀ n : ℕ, 1 ≤ n → n ≤ truncOrder ε →
          ∫ ω,
              ‖pmCoeff M ρ lam ε n
                (modes j).1 (modes j).2 ω‖ ≤
            ‖(lamEps lam ε : ℂ)‖ * K * q ^ (n - 1)) :
    Tendsto
      (fun ε => fullParametrixChar M ρ lam ε s modes c)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (𝓝 (Complex.exp (-((limitVar lam modes c : ℂ) / 2)))) := by
  apply hP36.tendsto_charFun_of_fixedTruncation_approximation
    hlam hsmall hsub modes c
    (fun ε => fullParametrixChar M ρ lam ε s modes c)
    (geometricTruncationError c K q)
    (tendsto_geometricTruncationError c hq0 hq1)
  intro B
  filter_upwards [
    eventually_le_truncOrder B,
    eventually_lamEps_ne_zero hlam,
    hcoeff] with ε hB hlamEps hcoeffε
  rw [dist_eq_norm]
  apply hP36.norm_fullParametrixChar_sub_fixed_le_geometric
    ε rfl hB modes c K q hK hq0 hq1 hlamEps
  intro j m hm
  have hmIco :
      B ≤ m ∧ m < truncOrder ε :=
    Finset.mem_Ico.mp hm
  have hmA : m + 1 ≤ truncOrder ε :=
    Nat.succ_le_iff.mpr hmIco.2
  simpa only [Nat.add_sub_cancel] using
    hcoeffε j (m + 1) (Nat.succ_pos m) hmA

/-- Adapter from the natural squared estimate in (3.24) to the
geometric `L¹` interface used by the two-scale closure theorem. -/
theorem Prop36.tendsto_fullParametrixChar_of_geometric_second_moment_bound
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (hlam : 0 < lam)
    (hsmall : hP36.boundConstant * lam < 1)
    (hsub : lam ^ 2 < 2 * Real.pi ^ 2)
    {s : ℕ} (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (K q : ℝ) (hK : 0 ≤ K) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hsecond :
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        ∀ j : Fin s, ∀ n : ℕ, 1 ≤ n → n ≤ truncOrder ε →
          MemLp
            (pmCoeff M ρ lam ε n
              (modes j).1 (modes j).2)
            2 (volume : Measure M.Ω) ∧
          ∫ ω,
              ‖pmCoeff M ρ lam ε n
                (modes j).1 (modes j).2 ω‖ ^ 2 ≤
            (‖(lamEps lam ε : ℂ)‖ * K * q ^ (n - 1)) ^ 2) :
    Tendsto
      (fun ε => fullParametrixChar M ρ lam ε s modes c)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (𝓝 (Complex.exp (-((limitVar lam modes c : ℂ) / 2)))) := by
  apply hP36.tendsto_fullParametrixChar_of_geometric_coeff_bound
    hlam hsmall hsub modes c K q hK hq0 hq1
  filter_upwards [hsecond] with ε hsecondε
  intro j n hn hnt
  have hR :
      0 ≤ ‖(lamEps lam ε : ℂ)‖ * K * q ^ (n - 1) :=
    mul_nonneg
      (mul_nonneg (norm_nonneg _) hK)
      (pow_nonneg hq0 _)
  exact integral_norm_le_of_integral_norm_sq_le_sq
    (volume : Measure M.Ω)
    (pmCoeff M ρ lam ε n (modes j).1 (modes j).2)
    (hsecondε j n hn hnt).1 hR
    (hsecondε j n hn hnt).2

end

end Anderson4D
