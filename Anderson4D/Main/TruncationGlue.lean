import Anderson4D.ForMathlib.TwoScaleLimit
import Anderson4D.Main.FixedTruncationTail

/-!
# Two-scale characteristic-function glue

This file isolates the analytic glue in paper (3.39).  The probabilistic
input is a uniform-in-`ε` approximation of the full scalar characteristic
function by its fixed perturbative truncations.  The fixed-truncation
moment method and the `B → ∞` covariance computation then identify the
limit.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- The unit-circle exponential is one-Lipschitz in its real phase. -/
theorem norm_exp_I_mul_sub_exp_I_mul_le (x y : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) -
        Complex.exp (Complex.I * (y : ℂ))‖ ≤
      ‖x - y‖ := by
  calc
    ‖Complex.exp (Complex.I * (x : ℂ)) -
          Complex.exp (Complex.I * (y : ℂ))‖ =
        ‖Complex.exp (Complex.I * (y : ℂ)) *
          (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1)‖ := by
      congr 1
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    _ = ‖Complex.exp (Complex.I * (y : ℂ))‖ *
        ‖Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1‖ :=
      norm_mul _ _
    _ = ‖Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1‖ := by
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      norm_num
    _ ≤ ‖x - y‖ :=
      Real.norm_exp_I_mul_ofReal_sub_one_le

/-- Difference of characteristic-function integrals is bounded by the
`L¹` distance of the two real random variables. -/
theorem norm_integral_exp_I_sub_le_integral_norm_sub
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X Y : Ω → ℝ)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXY : Integrable (fun ω => ‖X ω - Y ω‖) μ) :
    ‖(∫ ω, Complex.exp (Complex.I * (X ω : ℂ)) ∂μ) -
        ∫ ω, Complex.exp (Complex.I * (Y ω : ℂ)) ∂μ‖ ≤
      ∫ ω, ‖X ω - Y ω‖ ∂μ := by
  let f : Ω → ℂ :=
    fun ω => Complex.exp (Complex.I * (X ω : ℂ))
  let g : Ω → ℂ :=
    fun ω => Complex.exp (Complex.I * (Y ω : ℂ))
  have hfAE : AEMeasurable f μ := by
    exact Complex.measurable_exp.comp_aemeasurable
      ((Complex.measurable_ofReal.comp_aemeasurable hX).const_mul
        Complex.I)
  have hgAE : AEMeasurable g μ := by
    exact Complex.measurable_exp.comp_aemeasurable
      ((Complex.measurable_ofReal.comp_aemeasurable hY).const_mul
        Complex.I)
  have hf : Integrable f μ := by
    apply Integrable.of_bound hfAE.aestronglyMeasurable 1
    filter_upwards with ω
    dsimp only [f]
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    norm_num
  have hg : Integrable g μ := by
    apply Integrable.of_bound hgAE.aestronglyMeasurable 1
    filter_upwards with ω
    dsimp only [g]
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    norm_num
  change ‖(∫ ω, f ω ∂μ) - ∫ ω, g ω ∂μ‖ ≤ _
  rw [← integral_sub hf hg]
  refine (norm_integral_le_integral_norm
    (μ := μ) (f := fun ω => f ω - g ω)).trans ?_
  exact integral_mono_ae (hf.sub hg).norm hXY
    (ae_of_all μ fun ω =>
      norm_exp_I_mul_sub_exp_I_mul_le (X ω) (Y ω))

/-- The scalar test of the full moving parametrix cutoff
`A = ⌊|log ε|⌋`. -/
def fullParametrixReal
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (ω : M.Ω) : ℝ :=
  fixedTruncationReal M ρ lam ε (truncOrder ε) s modes c ω

/-- Characteristic-function integral of the moving parametrix cutoff. -/
def fullParametrixChar
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) : ℂ :=
  ∫ ω, Complex.exp
    (Complex.I *
      (fullParametrixReal M ρ lam ε s modes c ω : ℂ))

/-- Orders strictly above `B` and at most `A`, with the same
normalization as `fixedTruncationModeSum`. -/
def parametrixModeTail
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (B A s : ℕ) (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (ω : M.Ω) : ℂ :=
  (lamEps lam ε : ℂ)⁻¹ *
    ∑ j, c j * ∑ m ∈ Finset.Ico B A,
      pmCoeff M ρ lam ε (m + 1)
        (modes j).1 (modes j).2 ω

/-- Exact finite-sum subtraction underlying the truncation tail. -/
theorem fixedTruncationModeSum_sub_eq_parametrixModeTail
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    {B A s : ℕ} (hBA : B ≤ A)
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (ω : M.Ω) :
    fixedTruncationModeSum M ρ lam ε A s modes c ω -
        fixedTruncationModeSum M ρ lam ε B s modes c ω =
      parametrixModeTail M ρ lam ε B A s modes c ω := by
  unfold fixedTruncationModeSum parametrixModeTail
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← mul_sub]
  congr 1
  rw [
    Fin.sum_univ_eq_sum_range
      (fun m : ℕ =>
        pmCoeff M ρ lam ε (m + 1)
          (modes j).1 (modes j).2 ω),
    Fin.sum_univ_eq_sum_range
      (fun m : ℕ =>
        pmCoeff M ρ lam ε (m + 1)
          (modes j).1 (modes j).2 ω)]
  have hsum := Finset.sum_range_sub_sum_range
    (f := fun m : ℕ =>
      pmCoeff M ρ lam ε (m + 1)
        (modes j).1 (modes j).2 ω) hBA
  have hfin :
      (Finset.range A).filter (fun m => B ≤ m) =
        Finset.Ico B A := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range,
      Finset.mem_Ico]
    tauto
  rw [hfin] at hsum
  exact hsum

/-- Real-part version of the exact moving-cutoff tail identity. -/
theorem fullParametrixReal_sub_fixedTruncationReal
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    {B s : ℕ} (hB : B ≤ truncOrder ε)
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (ω : M.Ω) :
    fullParametrixReal M ρ lam ε s modes c ω -
        fixedTruncationReal M ρ lam ε B s modes c ω =
      (parametrixModeTail M ρ lam ε B (truncOrder ε)
        s modes c ω).re := by
  unfold fullParametrixReal fixedTruncationReal
  simpa only [Complex.sub_re] using congrArg Complex.re
    (fixedTruncationModeSum_sub_eq_parametrixModeTail
      M ρ lam ε hB modes c ω)

/-- Pointwise triangle bound for the perturbative tail. -/
theorem norm_parametrixModeTail_re_le
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (B A s : ℕ) (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (ω : M.Ω) :
    ‖(parametrixModeTail M ρ lam ε B A s modes c ω).re‖ ≤
      ‖(lamEps lam ε : ℂ)⁻¹‖ *
        ∑ j, ‖c j‖ * ∑ m ∈ Finset.Ico B A,
          ‖pmCoeff M ρ lam ε (m + 1)
            (modes j).1 (modes j).2 ω‖ := by
  calc
    ‖(parametrixModeTail
        M ρ lam ε B A s modes c ω).re‖ ≤
        ‖parametrixModeTail
          M ρ lam ε B A s modes c ω‖ :=
      Complex.abs_re_le_norm _
    _ = ‖(lamEps lam ε : ℂ)⁻¹‖ *
        ‖∑ j, c j * ∑ m ∈ Finset.Ico B A,
          pmCoeff M ρ lam ε (m + 1)
            (modes j).1 (modes j).2 ω‖ := by
      rw [parametrixModeTail, norm_mul]
    _ ≤ ‖(lamEps lam ε : ℂ)⁻¹‖ *
        ∑ j, ‖c j * ∑ m ∈ Finset.Ico B A,
          pmCoeff M ρ lam ε (m + 1)
            (modes j).1 (modes j).2 ω‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ ‖(lamEps lam ε : ℂ)⁻¹‖ *
        ∑ j, ‖c j‖ * ∑ m ∈ Finset.Ico B A,
          ‖pmCoeff M ρ lam ε (m + 1)
            (modes j).1 (modes j).2 ω‖ := by
      gcongr with j
      rw [norm_mul]
      gcongr
      exact norm_sum_le _ _

/-- Proposition 3.6 records measurability of every positive-order mode
coefficient. -/
theorem Prop36.measurable_pmCoeff
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam)
    {m : ℕ} (hm : 1 ≤ m) (α β : Z4) (ε : ℝ) :
    Measurable (pmCoeff M ρ lam ε m α β) := by
  let modes : Fin 1 → (Z4 × Z4) × ℕ :=
    fun _ => ((α, β), m)
  have hvalid : ∀ j, 1 ≤ (modes j).2 ∧ (modes j).2 ≤ m := by
    intro j
    exact ⟨hm, le_rfl⟩
  have hclause :=
    (hP36.fullData m 1).family_clause modes hvalid
  simpa only [modes] using hclause.1 ε (0 : Fin 1)

/-- Proposition 3.6 records integrability of every positive-order mode
coefficient (the family-size-one specialization). -/
theorem Prop36.integrable_pmCoeff
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam)
    {m : ℕ} (hm : 1 ≤ m) (α β : Z4) (ε : ℝ) :
    Integrable (pmCoeff M ρ lam ε m α β)
      (volume : Measure M.Ω) := by
  let modes : Fin 1 → (Z4 × Z4) × ℕ :=
    fun _ => ((α, β), m)
  have hvalid : ∀ j, 1 ≤ (modes j).2 ∧ (modes j).2 ≤ m := by
    intro j
    exact ⟨hm, le_rfl⟩
  have hclause :=
    (hP36.fullData m 1).family_clause modes hvalid
  simpa only [modes, Fin.prod_univ_one] using hclause.2.1 ε

/-- Integrating the pointwise tail bound commutes the two finite sums
with expectation. -/
theorem Prop36.integral_norm_parametrixModeTail_re_le
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam)
    (ε : ℝ) (B A s : ℕ)
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    (∫ ω,
      ‖(parametrixModeTail
        M ρ lam ε B A s modes c ω).re‖) ≤
      ‖(lamEps lam ε : ℂ)⁻¹‖ *
        ∑ j, ‖c j‖ * ∑ m ∈ Finset.Ico B A,
          ∫ ω,
            ‖pmCoeff M ρ lam ε (m + 1)
              (modes j).1 (modes j).2 ω‖ := by
  have hpm (j : Fin s) (m : ℕ) :
      Integrable
        (fun ω =>
          ‖pmCoeff M ρ lam ε (m + 1)
            (modes j).1 (modes j).2 ω‖)
        (volume : Measure M.Ω) := by
    exact (hP36.integrable_pmCoeff
      (m := m + 1) (by omega)
      (modes j).1 (modes j).2 ε).norm
  have hinner (j : Fin s) :
      Integrable
        (fun ω =>
          ∑ m ∈ Finset.Ico B A,
            ‖pmCoeff M ρ lam ε (m + 1)
              (modes j).1 (modes j).2 ω‖)
        (volume : Measure M.Ω) := by
    apply integrable_finsetSum
    intro m hm
    exact hpm j m
  have houter :
      Integrable
        (fun ω =>
          ∑ j, ‖c j‖ * ∑ m ∈ Finset.Ico B A,
            ‖pmCoeff M ρ lam ε (m + 1)
              (modes j).1 (modes j).2 ω‖)
        (volume : Measure M.Ω) := by
    apply integrable_finsetSum
    intro j hj
    exact (hinner j).const_mul ‖c j‖
  have hmajor :
      Integrable
        (fun ω =>
          ‖(lamEps lam ε : ℂ)⁻¹‖ *
            ∑ j, ‖c j‖ * ∑ m ∈ Finset.Ico B A,
              ‖pmCoeff M ρ lam ε (m + 1)
                (modes j).1 (modes j).2 ω‖)
        (volume : Measure M.Ω) :=
    houter.const_mul ‖(lamEps lam ε : ℂ)⁻¹‖
  calc
    (∫ ω,
      ‖(parametrixModeTail
        M ρ lam ε B A s modes c ω).re‖) ≤
        ∫ ω,
          ‖(lamEps lam ε : ℂ)⁻¹‖ *
            ∑ j, ‖c j‖ * ∑ m ∈ Finset.Ico B A,
              ‖pmCoeff M ρ lam ε (m + 1)
                (modes j).1 (modes j).2 ω‖ := by
      apply integral_mono_of_nonneg
        (ae_of_all _ fun _ => norm_nonneg _)
        hmajor
      exact ae_of_all _ fun ω =>
        norm_parametrixModeTail_re_le
          M ρ lam ε B A s modes c ω
    _ = ‖(lamEps lam ε : ℂ)⁻¹‖ *
        ∑ j, ‖c j‖ * ∑ m ∈ Finset.Ico B A,
          ∫ ω,
            ‖pmCoeff M ρ lam ε (m + 1)
              (modes j).1 (modes j).2 ω‖ := by
      rw [integral_const_mul]
      congr 1
      rw [integral_finsetSum Finset.univ
        (fun j _ => (hinner j).const_mul ‖c j‖)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul]
      congr 1
      exact integral_finsetSum (Finset.Ico B A)
        (fun m _ => hpm j m)

/-- Rewrite the fixed-truncation pushforward characteristic function as
an expectation on the original noise space. -/
theorem Prop36.charFun_fixedTruncationLaw_one_eq_integral
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam)
    (B : ℕ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (ε : ℝ) :
    charFun
        (fixedTruncationLaw M ρ lam ε B s modes c) 1 =
      ∫ ω, Complex.exp
        (Complex.I *
          (fixedTruncationReal
            M ρ lam ε B s modes c ω : ℂ)) := by
  rw [charFun_apply_real]
  unfold fixedTruncationLaw
  rw [integral_map
    (hP36.aemeasurable_fixedTruncationReal B modes c ε)
    (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with ω
  congr 1
  push_cast
  ring

/-- The characteristic-function truncation error is controlled by the
sum of the expected absolute values of the omitted mode coefficients. -/
theorem Prop36.norm_fullParametrixChar_sub_fixed_le
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam)
    (ε : ℝ) {B s : ℕ} (hB : B ≤ truncOrder ε)
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    ‖fullParametrixChar M ρ lam ε s modes c -
        charFun
          (fixedTruncationLaw M ρ lam ε B s modes c) 1‖ ≤
      ‖(lamEps lam ε : ℂ)⁻¹‖ *
        ∑ j, ‖c j‖ *
          ∑ m ∈ Finset.Ico B (truncOrder ε),
            ∫ ω,
              ‖pmCoeff M ρ lam ε (m + 1)
                (modes j).1 (modes j).2 ω‖ := by
  rw [hP36.charFun_fixedTruncationLaw_one_eq_integral
    B modes c ε]
  unfold fullParametrixChar
  have hfullAE :
      AEMeasurable
        (fullParametrixReal M ρ lam ε s modes c)
        (volume : Measure M.Ω) := by
    change
      AEMeasurable
        (fixedTruncationReal
          M ρ lam ε (truncOrder ε) s modes c)
        (volume : Measure M.Ω)
    exact hP36.aemeasurable_fixedTruncationReal
      (truncOrder ε) modes c ε
  have hfixedAE :=
    hP36.aemeasurable_fixedTruncationReal B modes c ε
  have hfullInt :
      Integrable
        (fullParametrixReal M ρ lam ε s modes c)
        (volume : Measure M.Ω) := by
    change
      Integrable
        (fixedTruncationReal
          M ρ lam ε (truncOrder ε) s modes c)
        (volume : Measure M.Ω)
    exact
      (hP36.memLp_fixedTruncationReal
        (truncOrder ε) 1 modes c ε).integrable (by norm_num)
  have hfixedInt :
      Integrable
        (fixedTruncationReal M ρ lam ε B s modes c)
        (volume : Measure M.Ω) :=
    (hP36.memLp_fixedTruncationReal
      B 1 modes c ε).integrable (by norm_num)
  calc
    ‖(∫ ω, Complex.exp
          (Complex.I *
            (fullParametrixReal
              M ρ lam ε s modes c ω : ℂ))) -
        ∫ ω, Complex.exp
          (Complex.I *
            (fixedTruncationReal
              M ρ lam ε B s modes c ω : ℂ))‖ ≤
        ∫ ω,
          ‖fullParametrixReal M ρ lam ε s modes c ω -
            fixedTruncationReal
              M ρ lam ε B s modes c ω‖ :=
      norm_integral_exp_I_sub_le_integral_norm_sub
        (volume : Measure M.Ω)
        (fullParametrixReal M ρ lam ε s modes c)
        (fixedTruncationReal M ρ lam ε B s modes c)
        hfullAE hfixedAE (hfullInt.sub hfixedInt).norm
    _ = ∫ ω,
        ‖(parametrixModeTail M ρ lam ε B (truncOrder ε)
          s modes c ω).re‖ := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω => congrArg norm
        (fullParametrixReal_sub_fixedTruncationReal
          M ρ lam ε hB modes c ω)
    _ ≤ ‖(lamEps lam ε : ℂ)⁻¹‖ *
        ∑ j, ‖c j‖ *
          ∑ m ∈ Finset.Ico B (truncOrder ε),
            ∫ ω,
              ‖pmCoeff M ρ lam ε (m + 1)
                (modes j).1 (modes j).2 ω‖ :=
      hP36.integral_norm_parametrixModeTail_re_le
        ε B (truncOrder ε) s modes c

/-- Abstract form of the final `ε → 0`, then `B → ∞` argument.

The only missing input at this boundary is the uniform characteristic-
function tail estimate supplied by (3.24). -/
theorem Prop36.tendsto_charFun_of_fixedTruncation_approximation
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (hlam : 0 < lam)
    (hsmall : hP36.boundConstant * lam < 1)
    (hsub : lam ^ 2 < 2 * Real.pi ^ 2)
    {s : ℕ} (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (fullChar : ℝ → ℂ) (error : ℕ → ℝ)
    (herror : Tendsto error atTop (𝓝 0))
    (hclose : ∀ B,
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        dist (fullChar ε)
          (charFun
            (fixedTruncationLaw
              M ρ lam ε B s modes c) 1) ≤
          error B) :
    Tendsto fullChar
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (𝓝 (Complex.exp (-((limitVar lam modes c : ℂ) / 2)))) := by
  apply tendsto_of_two_scale_approximation
    fullChar
    (fun B ε =>
      charFun
        (fixedTruncationLaw M ρ lam ε B s modes c) 1)
    (fun B =>
      charFun
        (gaussianReal 0
          (fixedTruncationGaussianVariance
            hP36 hlam B modes c)) 1)
    (Complex.exp (-((limitVar lam modes c : ℂ) / 2)))
    error
  · intro B
    exact hP36.tendsto_fixedTruncationCharFun hlam B modes c
  · exact hP36.tendsto_fixedGaussianCharFun_atTop
      hlam hsmall hsub modes c
  · exact herror
  · exact hclose

end

end Anderson4D
