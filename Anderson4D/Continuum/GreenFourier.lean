import Anderson4D.Continuum.GreenBounds

/-!
# Fourier coefficients of the torus heat and Green kernels

This file supplies the normalization-sensitive part of blueprint node
I-green.  The intended endpoint is the paper-normalized identity
`Ĝ(k) = (1 + |k|²)⁻¹`.  The first ingredient below is a period-`p`
unfolding lemma for integrable functions on `ℝ`.
-/

namespace Anderson4D

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate

/-- Partition an integral on `ℝ` into translates of one interval of
arbitrary positive length. -/
private theorem Integrable.hasSum_intervalIntegral_comp_add_zsmul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Integrable f) {p : ℝ} (hp : 0 < p) (a : ℝ) :
    HasSum (fun n : ℤ => ∫ x in a..a + p, f (x + n • p)) (∫ x, f x) := by
  have hs :
      HasSum
        (fun n : ℤ =>
          ∫ x in Ioc (a + n • p) (a + (n + 1) • p), f x)
        (∫ x, f x) := by
    have h :=
      hasSum_integral_iUnion
        (f := f) (μ := volume)
        (fun _ : ℤ => measurableSet_Ioc)
        (pairwise_disjoint_Ioc_add_zsmul a p)
        (hf.integrableOn)
    rw [iUnion_Ioc_add_zsmul hp a, setIntegral_univ] at h
    exact h
  refine hs.congr_fun fun n => ?_
  rw [intervalIntegral.integral_comp_add_right]
  rw [intervalIntegral.integral_of_le]
  · congr 1
    simp only [add_smul, one_smul]
    abel_nf
  · linarith

/-- Pointwise periodization of a function on `ℝ` with period `p`. -/
private def periodize (p : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℤ, f (x + n • p)

/-- Pointwise periodization is periodic.  This statement is valid even on
the junk branch where the defining series is not summable. -/
private theorem periodize_periodic (p : ℝ) (f : ℝ → ℂ) :
    Function.Periodic (periodize p f) p := by
  intro x
  unfold periodize
  calc
    (∑' n : ℤ, f (x + p + n • p))
        = ∑' n : ℤ, f (x + (n + 1) • p) := by
            apply tsum_congr
            intro n
            simp only [add_smul, one_smul]
            congr 1
            abel
    _ = ∑' n : ℤ, f (x + n • p) := by
          simpa only [Equiv.coe_addRight] using
            ((Equiv.addRight (1 : ℤ)).tsum_eq fun n : ℤ => f (x + n • p))

/-- Periodization descended to the additive circle. -/
private def circlePeriodize (p : ℝ) (f : ℝ → ℂ) : AddCircle p → ℂ :=
  (periodize_periodic p f).lift

@[simp] private theorem circlePeriodize_coe (p : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    circlePeriodize p f (x : AddCircle p) = periodize p f x :=
  (periodize_periodic p f).lift_coe x

/-- Unfolding a periodized integrable function against one Fourier
character.  The circle carries its volume measure here, so there is no
normalizing factor. -/
private theorem integral_fourier_mul_circlePeriodize
    {p : ℝ} [Fact (0 < p)] (f : ℝ → ℂ) (hf : Integrable f) (m : ℤ) :
    ∫ z : AddCircle p, fourier m z * circlePeriodize p f z =
      ∫ x : ℝ, fourier m (x : AddCircle p) * f x := by
  let e : ℝ → ℂ := fun x => fourier m (x : AddCircle p)
  let F : ℤ → ℝ → ℂ := fun n x => e x * f (x + n • p)
  have he_cont : Continuous e := by
    dsimp [e]
    fun_prop
  have he_norm : ∀ x, ‖e x‖ = 1 := by
    intro x
    exact Circle.norm_coe _
  have he_periodic : Function.Periodic e p := by
    intro x
    dsimp [e]
    change fourier m ((x + p : ℝ) : AddCircle p) =
      fourier m (x : AddCircle p)
    rw [show ((x + p : ℝ) : AddCircle p) = (x : AddCircle p) by
      exact AddCircle.coe_add_period p x]
  have hf_shift : ∀ n : ℤ, Integrable (fun x => f (x + n • p)) := by
    intro n
    exact ((measurePreserving_add_right volume (n • p)).integrable_comp
      hf.aestronglyMeasurable).mpr hf
  have hF_int : ∀ n : ℤ, IntegrableOn (F n) (Ioc 0 p) := by
    intro n
    apply Integrable.integrableOn
    exact (hf_shift n).bdd_mul he_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [he_norm])
  have hF_norm : ∀ n : ℤ, ∀ x : ℝ, ‖F n x‖ = ‖f (x + n • p)‖ := by
    intro n x
    simp only [F, norm_mul, he_norm, one_mul]
  have hnormSum :
      Summable fun n : ℤ => ∫ x in Ioc 0 p, ‖F n x‖ := by
    have hs := Integrable.hasSum_intervalIntegral_comp_add_zsmul
      hf.norm (Fact.out : 0 < p) 0
    simp only [zero_add] at hs
    apply hs.summable.congr
    intro n
    rw [intervalIntegral.integral_of_le (Fact.out : 0 < p).le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    exact (hF_norm n x).symm
  have hswap :
      (∑' n : ℤ, ∫ x in Ioc 0 p, F n x) =
        ∫ x in Ioc 0 p, ∑' n : ℤ, F n x :=
    integral_tsum_of_summable_integral_norm hF_int hnormSum
  have hperiodized : ∀ x : ℝ, (∑' n : ℤ, F n x) =
      e x * periodize p f x := by
    intro x
    unfold periodize F
    exact tsum_mul_left
  have hef : Integrable (fun x => e x * f x) :=
    hf.bdd_mul he_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [he_norm])
  have hfull :
      HasSum (fun n : ℤ => ∫ x in (0 : ℝ)..p,
        (e * f) (x + n • p)) (∫ x, e x * f x) :=
    by
      simpa only [zero_add, Pi.mul_apply] using
        (Integrable.hasSum_intervalIntegral_comp_add_zsmul
          hef (Fact.out : 0 < p) 0)
  have hterms :
      HasSum (fun n : ℤ => ∫ x in Ioc 0 p, F n x)
        (∫ x, e x * f x) := by
    refine hfull.congr_fun fun n => ?_
    rw [intervalIntegral.integral_of_le (Fact.out : 0 < p).le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    simp only [Pi.mul_apply, F]
    congr 1
    simpa only [zsmul_eq_mul] using (he_periodic.int_mul n x).symm
  rw [← AddCircle.integral_preimage p 0]
  simp only [zero_add, circlePeriodize_coe]
  change (∫ x in Ioc 0 p, e x * periodize p f x) =
    ∫ x, e x * f x
  rw [← setIntegral_congr_fun measurableSet_Ioc
    (fun x _ => hperiodized x), ← hswap, hterms.tsum_eq]

/-! ## The one-dimensional Gaussian coefficient -/

private def gaussian1C (t : ℝ) (x : ℝ) : ℂ :=
  Complex.exp (-(x : ℂ) ^ 2 / (4 * t))

private def gaussian1R (t : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-x ^ 2 / (4 * t))

private theorem gaussian1C_eq_ofReal (t x : ℝ) :
    gaussian1C t x = (gaussian1R t x : ℂ) := by
  unfold gaussian1C gaussian1R
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  rfl

private theorem integrable_gaussian1C {t : ℝ} (ht : 0 < t) :
    Integrable (gaussian1C t) := by
  have hb : 0 < ((1 / (4 * t) : ℝ) : ℂ).re := by
    simp only [Complex.ofReal_re]
    positivity
  have h := integrable_cexp_quadratic hb (0 : ℂ) (0 : ℂ)
  convert h using 1
  funext x
  simp only [gaussian1C, zero_mul, add_zero]
  congr 1
  push_cast
  field_simp

/-- Raw Gaussian-transform formula for one periodized coordinate. -/
private theorem integral_fourier_mul_periodizedGaussian_raw
    {t : ℝ} (ht : 0 < t) (m : ℤ) :
    ∫ z : AddCircle (2 * Real.pi),
        fourier m z * circlePeriodize (2 * Real.pi) (gaussian1C t) z =
      (Real.pi / ((1 / (4 * t) : ℝ) : ℂ)) ^ (1 / 2 : ℂ) *
        Complex.exp (-(m : ℂ) ^ 2 / (4 * ((1 / (4 * t) : ℝ) : ℂ))) := by
  rw [integral_fourier_mul_circlePeriodize
    (gaussian1C t) (integrable_gaussian1C ht) m]
  have hb : 0 < ((1 / (4 * t) : ℝ) : ℂ).re := by
    simp only [Complex.ofReal_re]
    positivity
  have h := fourierIntegral_gaussian hb (m : ℂ)
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with x
    rw [fourier_coe_apply]
    simp only [gaussian1C]
    congr 1
    · congr 1
      push_cast
      field_simp
    · congr 1
      push_cast
      field_simp

private theorem gaussian_cpow_half {t : ℝ} (ht : 0 < t) :
    (Real.pi / ((1 / (4 * t) : ℝ) : ℂ)) ^ (1 / 2 : ℂ) =
      (Real.sqrt (4 * Real.pi * t) : ℝ) := by
  have hbase : Real.pi / ((1 / (4 * t) : ℝ) : ℂ) =
      ((4 * Real.pi * t : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [hbase]
  have hexp : (1 / 2 : ℂ) = (((1 / 2 : ℝ) : ℝ) : ℂ) := by norm_num
  rw [hexp, ← Complex.ofReal_cpow
    (by positivity : (0 : ℝ) ≤ 4 * Real.pi * t)]
  rw [← Real.sqrt_eq_rpow]

private theorem gaussian_exponent (t : ℝ) (m : ℤ) :
    -(m : ℂ) ^ 2 / (4 * ((1 / (4 * t) : ℝ) : ℂ)) =
      ((-t * (m : ℝ) ^ 2 : ℝ) : ℂ) := by
  push_cast
  field_simp

/-- Fourier coefficient of one unnormalized periodized Gaussian. -/
private theorem integral_fourier_mul_periodizedGaussian
    {t : ℝ} (ht : 0 < t) (m : ℤ) :
    ∫ z : AddCircle (2 * Real.pi),
        fourier m z * circlePeriodize (2 * Real.pi) (gaussian1C t) z =
      (Real.sqrt (4 * Real.pi * t) : ℝ) *
        Complex.exp (-t * (m : ℝ) ^ 2) := by
  rw [integral_fourier_mul_periodizedGaussian_raw ht m,
    gaussian_cpow_half ht, gaussian_exponent t m]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_intCast, Complex.ofReal_pow]

private theorem summable_exp_neg_mul_int_sq_fourier {c : ℝ} (hc : 0 < c) :
    Summable fun m : ℤ => Real.exp (-c * (m : ℝ) ^ 2) := by
  have hgeo : Summable fun n : ℕ => Real.exp (-c) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le
      (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith))
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine hgeo.of_nonneg_of_le (fun n => (Real.exp_pos _).le) fun n => ?_
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast Nat.le_self_pow two_ne_zero n
    push_cast
    nlinarith [h1, hc]
  · refine hgeo.of_nonneg_of_le (fun n => (Real.exp_pos _).le) fun n => ?_
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith [hc, sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]

private theorem summable_gaussian1C_zsmul {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable fun m : ℤ => gaussian1C t (x + m • (2 * Real.pi)) := by
  rw [← summable_norm_iff]
  have hc : 0 < Real.pi ^ 2 / (2 * t) := by positivity
  have hbase := (summable_exp_neg_mul_int_sq_fourier hc).mul_left
    (Real.exp (x ^ 2 / (4 * t)))
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hbase
  have hgauss :
      gaussian1C t (x + m • (2 * Real.pi)) =
        Complex.exp (((-(x + 2 * Real.pi * (m : ℝ)) ^ 2 / (4 * t) : ℝ) : ℂ)) := by
    unfold gaussian1C
    congr 1
    push_cast
    simp only [zsmul_eq_mul]
    field_simp
  rw [hgauss, Complex.norm_exp, Complex.ofReal_re, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs : (2 * Real.pi * (m : ℝ)) ^ 2 / 2 - x ^ 2 ≤
      (x + 2 * Real.pi * (m : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (x + Real.pi * (m : ℝ))]
  field_simp
  nlinarith

private theorem summable_gaussian1R_zsmul {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable fun m : ℤ => gaussian1R t (x + m • (2 * Real.pi)) := by
  have h := (summable_gaussian1C_zsmul ht x).norm
  exact h.congr fun m => by
    rw [gaussian1C_eq_ofReal, Complex.norm_real]
    exact Real.norm_of_nonneg (by unfold gaussian1R; positivity)

private theorem summable_pi_prod_family
    {n : ℕ} (g : Fin n → ℤ → ℝ) (h0 : ∀ i m, 0 ≤ g i m)
    (hg : ∀ i, Summable (g i)) :
    Summable fun k : Fin n → ℤ => ∏ i, g i (k i) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    have htail := ih (fun i m => g i.succ m)
      (fun i m => h0 i.succ m) (fun i => hg i.succ)
    have hgNorm : Summable fun m => ‖g 0 m‖ :=
      (hg 0).congr fun m => (Real.norm_of_nonneg (h0 0 m)).symm
    have htailNorm :
        Summable fun k : Fin n → ℤ => ‖∏ i, g i.succ (k i)‖ :=
      htail.congr fun k =>
        (Real.norm_of_nonneg
          (Finset.prod_nonneg fun i _ => h0 i.succ (k i))).symm
    let f0 : ℤ → ℝ := g 0
    let ft : (Fin n → ℤ) → ℝ := fun k => ∏ i, g i.succ (k i)
    have hstep0 := @summable_mul_of_summable_norm ℝ ℤ (Fin n → ℤ) _ _
      f0 ft (by simpa [f0] using hgNorm) (by simpa [ft] using htailNorm)
    have hstep :
        Summable fun p : ℤ × (Fin n → ℤ) =>
          g 0 p.1 * ∏ i, g i.succ (p.2 i) := by
      simpa [f0, ft] using hstep0
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).summable_iff]
    exact hstep.congr fun p => by simp [Fin.consEquiv, Fin.prod_univ_succ]

private theorem tsum_pi_prod_family
    {n : ℕ} (g : Fin n → ℤ → ℝ) (h0 : ∀ i m, 0 ≤ g i m)
    (hg : ∀ i, Summable (g i)) :
    ∑' k : Fin n → ℤ, ∏ i, g i (k i) = ∏ i, ∑' m, g i m := by
  induction n with
  | zero =>
    rw [tsum_eq_single (fun _ : Fin 0 => (0 : ℤ))
      (fun b hb => absurd (funext fun i => i.elim0) hb)]
    simp
  | succ n ih =>
    have htail := summable_pi_prod_family (fun i m => g i.succ m)
      (fun i m => h0 i.succ m) (fun i => hg i.succ)
    have hgNorm : Summable fun m => ‖g 0 m‖ :=
      (hg 0).congr fun m => (Real.norm_of_nonneg (h0 0 m)).symm
    have htailNorm :
        Summable fun k : Fin n → ℤ => ‖∏ i, g i.succ (k i)‖ :=
      htail.congr fun k =>
        (Real.norm_of_nonneg
          (Finset.prod_nonneg fun i _ => h0 i.succ (k i))).symm
    let f0 : ℤ → ℝ := g 0
    let ft : (Fin n → ℤ) → ℝ := fun k => ∏ i, g i.succ (k i)
    have hstep0 := @summable_mul_of_summable_norm ℝ ℤ (Fin n → ℤ) _ _
      f0 ft (by simpa [f0] using hgNorm) (by simpa [ft] using htailNorm)
    have hstep :
        Summable fun p : ℤ × (Fin n → ℤ) =>
          g 0 p.1 * ∏ i, g i.succ (p.2 i) := by
      simpa [f0, ft] using hstep0
    calc
      ∑' k : Fin (n + 1) → ℤ, ∏ i, g i (k i) =
          ∑' p : ℤ × (Fin n → ℤ),
            g 0 p.1 * ∏ i, g i.succ (p.2 i) := by
        rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).tsum_eq
          (fun k : Fin (n + 1) → ℤ => ∏ i, g i (k i))]
        exact tsum_congr fun p => by simp [Fin.consEquiv, Fin.prod_univ_succ]
      _ = (∑' m, g 0 m) *
          ∑' k : Fin n → ℤ, ∏ i, g i.succ (k i) :=
        ((hg 0).tsum_mul_tsum htail hstep).symm
      _ = (∑' m : ℤ, g 0 m) *
          ∏ i : Fin n, ∑' m : ℤ, g i.succ m := by
        rw [ih (fun (i : Fin n) (m : ℤ) => g i.succ m)
          (fun (i : Fin n) (m : ℤ) => h0 i.succ m)
          (fun (i : Fin n) => hg i.succ)]
      _ = ∏ i : Fin (n + 1), ∑' m : ℤ, g i m := by
        rw [Fin.prod_univ_succ (fun i : Fin (n + 1) => ∑' m, g i m)]

private theorem heat_gaussian_term_factor (t : ℝ) (z : T4) (k : Z4) :
    Real.exp (-latticeDistSq z k / (4 * t)) =
      ∏ i, gaussian1R t (torusLift z i + k i • (2 * Real.pi)) := by
  unfold latticeDistSq gaussian1R
  rw [← Real.exp_sum]
  congr 1
  simp only [zsmul_eq_mul]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  congr 1
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem heatKernelT4_eq_real_periodizedGaussian_prod
    {t : ℝ} (ht : 0 < t) (z : T4) :
    heatKernelT4 t z =
      (4 * Real.pi * t) ^ (-2 : ℤ) *
        ∏ i, ∑' m : ℤ,
          gaussian1R t (torusLift z i + m • (2 * Real.pi)) := by
  unfold heatKernelT4
  simp_rw [heat_gaussian_term_factor]
  rw [tsum_mul_left]
  congr 1
  exact tsum_pi_prod_family
    (fun i m => gaussian1R t (torusLift z i + m • (2 * Real.pi)))
    (fun _ _ => (Real.exp_pos _).le)
    (fun i => summable_gaussian1R_zsmul ht (torusLift z i))

private theorem circlePeriodize_gaussian_eq_ofReal_tsum
    {t : ℝ} (z : T4) (i : Fin dim) :
    circlePeriodize (2 * Real.pi) (gaussian1C t) (z i) =
      ((∑' m : ℤ,
        gaussian1R t (torusLift z i + m • (2 * Real.pi))) : ℝ) := by
  have hcoe :
      ((torusLift z i : ℝ) : AddCircle (2 * Real.pi)) = z i :=
    AddCircle.coe_equivIco
  rw [← hcoe, circlePeriodize_coe]
  unfold periodize
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun m => gaussian1C_eq_ofReal _ _

/-- Product factorization of the four-dimensional heat kernel into
one-dimensional periodized Gaussians. -/
theorem heatKernelT4_eq_periodizedGaussian_prod
    {t : ℝ} (ht : 0 < t) (z : T4) :
    (heatKernelT4 t z : ℂ) =
      ((4 * Real.pi * t) ^ (-2 : ℤ) : ℝ) *
        ∏ i, circlePeriodize (2 * Real.pi) (gaussian1C t) (z i) := by
  calc
    (heatKernelT4 t z : ℂ) =
        (((4 * Real.pi * t) ^ (-2 : ℤ) *
          ∏ i, ∑' m : ℤ,
            gaussian1R t (torusLift z i + m • (2 * Real.pi)) : ℝ) : ℂ) :=
      congrArg (fun r : ℝ => (r : ℂ))
        (heatKernelT4_eq_real_periodizedGaussian_prod ht z)
    _ = ((4 * Real.pi * t) ^ (-2 : ℤ) : ℝ) *
        ∏ i, (((∑' m : ℤ,
          gaussian1R t (torusLift z i + m • (2 * Real.pi))) : ℝ) : ℂ) := by
      push_cast
      rfl
    _ = ((4 * Real.pi * t) ^ (-2 : ℤ) : ℝ) *
        ∏ i, circlePeriodize (2 * Real.pi) (gaussian1C t) (z i) := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact (circlePeriodize_gaussian_eq_ofReal_tsum z i).symm

/-- Paper-normalized Fourier coefficient of the torus heat kernel. -/
theorem paperFourierCoeff_heatKernelT4
    {t : ℝ} (ht : 0 < t) (k : Z4) :
    ∫ z : T4, charT4 k z * (heatKernelT4 t z : ℂ) ∂paperMeasure =
      Complex.exp ((-t * ∑ i, (k i : ℝ) ^ 2 : ℝ) : ℂ) := by
  rw [paperMeasure_eq_volume]
  have hpoint : ∀ z : T4,
      charT4 k z * (heatKernelT4 t z : ℂ) =
        (((4 * Real.pi * t) ^ (-2 : ℤ) : ℝ) : ℂ) *
          ∏ i, (fourier (k i) (z i) *
            circlePeriodize (2 * Real.pi) (gaussian1C t) (z i)) := by
    intro z
    rw [heatKernelT4_eq_periodizedGaussian_prod ht z]
    unfold charT4
    rw [Finset.prod_mul_distrib]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    integral_const_mul]
  change (((4 * Real.pi * t) ^ (-2 : ℤ) : ℝ) : ℂ) *
      (∫ z : T4, ∏ i, (fourier (k i) (z i) *
        circlePeriodize (2 * Real.pi) (gaussian1C t) (z i))
        ∂(Measure.pi fun _ : Fin dim =>
          (volume : Measure (AddCircle (2 * Real.pi))))) =
    Complex.exp ((-t * ∑ i, (k i : ℝ) ^ 2 : ℝ) : ℂ)
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (μ := fun _ : Fin dim => (volume : Measure (AddCircle (2 * Real.pi))))
    (fun i z => fourier (k i) z *
      circlePeriodize (2 * Real.pi) (gaussian1C t) z)]
  simp_rw [integral_fourier_mul_periodizedGaussian ht]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fin, dim]
  have ha : 0 < 4 * Real.pi * t := by positivity
  have hsqrt : Real.sqrt (4 * Real.pi * t) ^ 2 = 4 * Real.pi * t :=
    Real.sq_sqrt ha.le
  have hampR :
      (4 * Real.pi * t) ^ (-2 : ℤ) *
        Real.sqrt (4 * Real.pi * t) ^ 4 = 1 := by
    rw [zpow_neg, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num,
      zpow_natCast]
    rw [show Real.sqrt (4 * Real.pi * t) ^ 4 =
      (4 * Real.pi * t) ^ 2 by
        calc
          Real.sqrt (4 * Real.pi * t) ^ 4 =
              (Real.sqrt (4 * Real.pi * t) ^ 2) ^ 2 := by ring
          _ = (4 * Real.pi * t) ^ 2 := by rw [hsqrt]]
    exact inv_mul_cancel₀ (pow_ne_zero 2 ha.ne')
  have hampC :
      (((4 * Real.pi * t) ^ (-2 : ℤ) : ℝ) : ℂ) *
        (((Real.sqrt (4 * Real.pi * t) : ℝ) : ℂ) ^ 4) = 1 := by
    exact_mod_cast hampR
  rw [← mul_assoc, hampC, one_mul, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

private theorem measurable_torusLift_coord (i : Fin dim) :
    Measurable fun z : T4 => torusLift z i := by
  unfold torusLift
  exact measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco (2 * Real.pi) (-Real.pi)).measurable.comp
      (measurable_pi_apply i))

private theorem measurable_heatKernelT4_prod :
    Measurable fun p : ℝ × T4 => heatKernelT4 p.1 p.2 := by
  unfold heatKernelT4
  apply Measurable.tsum
  intro k
  have hlattice :
      Measurable fun p : ℝ × T4 => latticeDistSq p.2 k := by
    unfold latticeDistSq
    apply Finset.measurable_sum
    intro i hi
    exact (((measurable_torusLift_coord i).comp measurable_snd).add
      measurable_const).pow_const 2
  have hcoeff : Measurable fun p : ℝ × T4 =>
      (4 * Real.pi * p.1) ^ (-2 : ℤ) :=
    ((measurable_const.mul measurable_fst).pow_const (-2 : ℤ))
  have hexp : Measurable fun p : ℝ × T4 =>
      Real.exp (-latticeDistSq p.2 k / (4 * p.1)) :=
    Real.measurable_exp.comp
      (hlattice.neg.div (measurable_const.mul measurable_fst))
  exact hcoeff.mul hexp

private theorem integral_heatKernelT4_paper
    {t : ℝ} (ht : 0 < t) :
    ∫ z : T4, heatKernelT4 t z ∂paperMeasure = 1 := by
  have h := paperFourierCoeff_heatKernelT4 ht (0 : Z4)
  simp only [charT4_zero, one_mul, Pi.zero_apply, Int.cast_zero, zero_pow
    (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero, mul_zero,
    Complex.ofReal_zero, Complex.exp_zero] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

private theorem integrable_heatKernelT4_paper
    {t : ℝ} (ht : 0 < t) :
    Integrable (heatKernelT4 t) paperMeasure :=
  Integrable.of_integral_ne_zero (by
    rw [integral_heatKernelT4_paper ht]
    norm_num)

private theorem measurable_charT4 (k : Z4) :
    Measurable (charT4 k) :=
  (by unfold charT4; fun_prop : Continuous (charT4 k)).measurable

private theorem norm_charT4_fourier (k : Z4) (z : T4) :
    ‖charT4 k z‖ = 1 := by simp [charT4]

private def greenFourierJoint (k : Z4) (p : ℝ × T4) : ℂ :=
  charT4 k p.2 *
    ((Real.exp (-p.1) * heatKernelT4 p.1 p.2 : ℝ) : ℂ)

private theorem measurable_greenFourierJoint (k : Z4) :
    Measurable (greenFourierJoint k) := by
  unfold greenFourierJoint
  exact ((measurable_charT4 k).comp measurable_snd).mul
    (Complex.measurable_ofReal.comp
      ((Real.measurable_exp.comp measurable_fst.neg).mul
        measurable_heatKernelT4_prod))

private theorem integrable_greenFourierJoint_section
    (k : Z4) {t : ℝ} (ht : 0 < t) :
    Integrable (fun z : T4 => greenFourierJoint k (t, z)) paperMeasure := by
  have hgReal :
      Integrable (fun z : T4 => Real.exp (-t) * heatKernelT4 t z)
        paperMeasure :=
    (integrable_heatKernelT4_paper ht).const_mul _
  have hgComplex :
      Integrable (fun z : T4 =>
        ((Real.exp (-t) * heatKernelT4 t z : ℝ) : ℂ)) paperMeasure :=
    hgReal.ofReal
  exact hgComplex.bdd_mul (measurable_charT4 k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      rw [norm_charT4_fourier])

private theorem integral_norm_greenFourierJoint_section
    (k : Z4) {t : ℝ} (ht : 0 < t) :
    ∫ z : T4, ‖greenFourierJoint k (t, z)‖ ∂paperMeasure =
      Real.exp (-t) := by
  calc
    ∫ z : T4, ‖greenFourierJoint k (t, z)‖ ∂paperMeasure =
        ∫ z : T4, Real.exp (-t) * heatKernelT4 t z ∂paperMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        unfold greenFourierJoint
        change ‖charT4 k z *
          ((Real.exp (-t) * heatKernelT4 t z : ℝ) : ℂ)‖ =
            Real.exp (-t) * heatKernelT4 t z
        rw [norm_mul, norm_charT4_fourier, one_mul, Complex.norm_real,
          Real.norm_of_nonneg]
        exact mul_nonneg (Real.exp_pos _).le (heatKernelT4_nonneg t z)
    _ = Real.exp (-t) * ∫ z : T4, heatKernelT4 t z ∂paperMeasure := by
      exact integral_const_mul (Real.exp (-t)) (heatKernelT4 t)
    _ = Real.exp (-t) := by rw [integral_heatKernelT4_paper ht, mul_one]

private theorem integrable_greenFourierJoint (k : Z4) :
    Integrable (greenFourierJoint k)
      ((volume.restrict (Ioi (0 : ℝ))).prod paperMeasure) := by
  rw [integrable_prod_iff (measurable_greenFourierJoint k).aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact integrable_greenFourierJoint_section k ht
  · exact (integrableOn_exp_neg_Ioi 0).congr
      ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun t ht =>
          (integral_norm_greenFourierJoint_section k ht).symm))

private theorem integral_greenFourierJoint_section
    (k : Z4) {t : ℝ} (ht : 0 < t) :
    ∫ z : T4, greenFourierJoint k (t, z) ∂paperMeasure =
      (Real.exp (-t) : ℂ) *
        Complex.exp ((-t * ∑ i, (k i : ℝ) ^ 2 : ℝ) : ℂ) := by
  calc
    ∫ z : T4, greenFourierJoint k (t, z) ∂paperMeasure =
        ∫ z : T4, (Real.exp (-t) : ℂ) *
          (charT4 k z * (heatKernelT4 t z : ℂ)) ∂paperMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        unfold greenFourierJoint
        push_cast
        ring
    _ = (Real.exp (-t) : ℂ) *
        ∫ z : T4, charT4 k z * (heatKernelT4 t z : ℂ)
          ∂paperMeasure := by
      exact integral_const_mul _ _
    _ = (Real.exp (-t) : ℂ) *
        Complex.exp ((-t * ∑ i, (k i : ℝ) ^ 2 : ℝ) : ℂ) := by
      rw [paperFourierCoeff_heatKernelT4 ht k]

private theorem integral_integral_greenFourierJoint (k : Z4) :
    ∫ t : ℝ in Ioi 0,
        ∫ z : T4, greenFourierJoint k (t, z) ∂paperMeasure =
      (((1 + ∑ i, (k i : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
  let S : ℝ := ∑ i, (k i : ℝ) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg (k i : ℝ)
  calc
    ∫ t : ℝ in Ioi 0,
        ∫ z : T4, greenFourierJoint k (t, z) ∂paperMeasure =
        ∫ t : ℝ in Ioi 0,
          ((Real.exp (-(1 + S) * t) : ℝ) : ℂ) := by
      apply integral_congr_ae
      exact (ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun t ht => by
          change (∫ z : T4, greenFourierJoint k (t, z) ∂paperMeasure) =
            ((Real.exp (-(1 + S) * t) : ℝ) : ℂ)
          rw [integral_greenFourierJoint_section k ht]
          rw [← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Real.exp_add]
          congr 2
          dsimp [S]
          ring)
    _ = ((∫ t : ℝ in Ioi 0, Real.exp (-(1 + S) * t) : ℝ) : ℂ) :=
      integral_complex_ofReal
    _ = (((1 + ∑ i, (k i : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
      rw [integral_exp_mul_Ioi (by linarith : -(1 + S) < 0) 0]
      simp only [mul_zero, Real.exp_zero, neg_div, S]
      congr 1
      field_simp

/-- Fourier coefficient of the heat-kernel definition of the Green
function, with the paper's unnormalized reference measure. -/
theorem paperFourierCoeff_greenFn (k : Z4) :
    ∫ z : T4, charT4 k z * (greenFn z : ℂ) ∂paperMeasure =
      (((1 + ∑ i, (k i : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hF :
      Integrable (Function.uncurry fun t z => greenFourierJoint k (t, z))
        ((volume.restrict (Ioi (0 : ℝ))).prod paperMeasure) := by
    change Integrable (greenFourierJoint k)
      ((volume.restrict (Ioi (0 : ℝ))).prod paperMeasure)
    exact integrable_greenFourierJoint k
  calc
    ∫ z : T4, charT4 k z * (greenFn z : ℂ) ∂paperMeasure =
        ∫ z : T4, (∫ t : ℝ in Ioi 0,
          greenFourierJoint k (t, z)) ∂paperMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        unfold greenFn greenFourierJoint
        change charT4 k z *
            ((∫ t : ℝ in Ioi 0,
              Real.exp (-t) * heatKernelT4 t z : ℝ) : ℂ) =
          ∫ t : ℝ in Ioi 0, charT4 k z *
            ((Real.exp (-t) * heatKernelT4 t z : ℝ) : ℂ)
        rw [← integral_complex_ofReal, integral_const_mul]
    _ = ∫ t : ℝ in Ioi 0,
        ∫ z : T4, greenFourierJoint k (t, z) ∂paperMeasure :=
      (integral_integral_swap hF).symm
    _ = (((1 + ∑ i, (k i : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) :=
      integral_integral_greenFourierJoint k

/-- The Green function has total mass one for the paper's Lebesgue
normalization. -/
theorem integral_greenFn_paper :
    ∫ z : T4, greenFn z ∂paperMeasure = 1 := by
  have h := paperFourierCoeff_greenFn (0 : Z4)
  simp only [charT4_zero, one_mul, Pi.zero_apply, Int.cast_zero, zero_pow
    (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero, add_zero, inv_one] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- In particular, the heat-kernel Green function is Bochner integrable
despite its diagonal singularity. -/
theorem integrable_greenFn_paper : Integrable greenFn paperMeasure :=
  Integrable.of_integral_ne_zero (by rw [integral_greenFn_paper]; norm_num)


end

end Anderson4D
