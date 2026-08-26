import Anderson4D.Probability.WickOrthogonality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Closure of centered Gaussian random variables in `L²`

This file supplies the analytic closure step needed when passing from
finite Fourier sums to the mollified noise.  The proof is by characteristic
functions, with the convergence estimate

`|exp (itXₙ) - exp (itX)| ≤ |t| |Xₙ - X|`.

In particular, no independence or representation of the Gaussian variables
on a common canonical probability space is used.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal

/-- For a real `L²` function, the square of its `L²` seminorm is its
second absolute moment. -/
theorem eLpNorm_two_toReal_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 =
      ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  rw [hf.eLpNorm_eq_integral_rpow_norm
    (by norm_num) (by norm_num)]
  norm_num
  have hnonneg : 0 ≤ ∫ ω, f ω ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg (f ω)
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _)]
  rw [← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt hnonneg

/-- The variance of a centered real `L²` function is the square of its
`L²` seminorm. -/
theorem variance_eq_eLpNorm_two_toReal_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ)
    (hcenter : ∫ ω, f ω ∂μ = 0) :
    Var[f; μ] = (eLpNorm f 2 μ).toReal ^ 2 := by
  rw [variance_eq_sub hf, hcenter]
  norm_num
  rw [eLpNorm_two_toReal_sq f hf]
  apply integral_congr_ae
  filter_upwards with ω
  simp [Real.norm_eq_abs, sq_abs]

private theorem norm_cexp_mul_I_sub_le
    (t x y : ℝ) :
    ‖Complex.exp ((x * t : ℂ) * I) -
        Complex.exp ((y * t : ℂ) * I)‖ ≤
      ‖t‖ * ‖x - y‖ := by
  calc
    ‖Complex.exp ((x * t : ℂ) * I) -
        Complex.exp ((y * t : ℂ) * I)‖ =
        ‖Complex.exp ((y * t : ℂ) * I) *
          (Complex.exp (I * ((x - y) * t : ℝ)) - 1)‖ := by
      congr 1
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
    _ = ‖Complex.exp (I * ((x - y) * t : ℝ)) - 1‖ := by
      rw [norm_mul, Complex.norm_exp]
      simp
    _ ≤ ‖(x - y) * t‖ :=
      Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = ‖t‖ * ‖x - y‖ := by
      rw [norm_mul, mul_comm]

/-- Centered real Gaussian laws are closed under `L²` convergence on a
fixed probability space.

The convergence hypothesis is stated directly in `eLpNorm`; this is the
form produced by the summable Fourier-series API. -/
theorem hasGaussianLaw_of_tendsto_eLpNorm_two
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hX : ∀ n, HasGaussianLaw (X n) μ)
    (hcenter : ∀ n, ∫ ω, X n ω ∂μ = 0)
    (hmem : ∀ n, MemLp (X n) 2 μ)
    (hY : MemLp Y 2 μ)
    (hconv :
      Filter.Tendsto
        (fun n => eLpNorm (X n - Y) 2 μ)
        Filter.atTop (nhds 0)) :
    HasGaussianLaw Y μ := by
  let X₂ : ℕ → Lp ℝ 2 μ :=
    fun n => (hmem n).toLp (X n)
  let Y₂ : Lp ℝ 2 μ := hY.toLp Y
  have hconvLp :
      Filter.Tendsto X₂ Filter.atTop (nhds Y₂) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm X₂ Y hY]
    refine hconv.congr' ?_
    filter_upwards with n
    apply eLpNorm_congr_ae
    exact ((hmem n).coeFn_toLp.sub
      (Filter.EventuallyEq.rfl : Y =ᵐ[μ] Y)).symm
  have hnorm :
      Filter.Tendsto (fun n => ‖X₂ n‖) Filter.atTop (nhds ‖Y₂‖) :=
    tendsto_norm.comp hconvLp
  let v : NNReal := ⟨‖Y₂‖ ^ 2, sq_nonneg ‖Y₂‖⟩
  have hmap (n : ℕ) :
      Measure.map (X n) μ =
        gaussianReal 0
          ⟨(eLpNorm (X n) 2 μ).toReal ^ 2,
            sq_nonneg _⟩ := by
    rw [(hX n).map_eq_gaussianReal, hcenter n,
      variance_eq_eLpNorm_two_toReal_sq (X n) (hmem n)
        (hcenter n)]
    congr 1
    exact Real.toNNReal_of_nonneg (sq_nonneg _)
  have hchar :
      ∀ t : ℝ,
        charFun (Measure.map Y μ) t =
          charFun (gaussianReal 0 v) t := by
    intro t
    have hcharLimit :
        Filter.Tendsto
          (fun n => charFun (Measure.map (X n) μ) t)
          Filter.atTop
          (nhds (charFun (Measure.map Y μ) t)) := by
      have hInt (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) :
          Integrable
            (fun ω => Complex.exp ((f ω * t : ℂ) * I)) μ := by
        apply (integrable_const (1 : ℝ)).mono'
        · exact
            (by
              fun_prop :
              Continuous
                (fun r : ℝ =>
                  Complex.exp ((r * t : ℂ) * I))).comp_aestronglyMeasurable
              hf
        · filter_upwards with ω
          rw [Complex.norm_exp]
          norm_num
      have hlintegral :
          Filter.Tendsto
            (fun n =>
              ∫⁻ ω,
                ‖Complex.exp ((X n ω * t : ℂ) * I) -
                  Complex.exp ((Y ω * t : ℂ) * I)‖ₑ ∂μ)
            Filter.atTop (nhds 0) := by
        have hupper :
            Filter.Tendsto
              (fun n =>
                ‖t‖ₑ * eLpNorm (X n - Y) 2 μ)
              Filter.atTop (nhds 0) := by
          simpa using ENNReal.Tendsto.const_mul hconv
            (Or.inr enorm_ne_top)
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le
            tendsto_const_nhds hupper
        · intro n
          exact bot_le
        · intro n
          calc
            (∫⁻ ω,
                ‖Complex.exp ((X n ω * t : ℂ) * I) -
                  Complex.exp ((Y ω * t : ℂ) * I)‖ₑ ∂μ) ≤
                ∫⁻ ω, ‖t‖ₑ * ‖X n ω - Y ω‖ₑ ∂μ := by
              apply lintegral_mono
              intro ω
              have hreal :=
                norm_cexp_mul_I_sub_le t (X n ω) (Y ω)
              simpa only [ofReal_norm,
                ENNReal.ofReal_mul (norm_nonneg t)] using
                ENNReal.ofReal_le_ofReal hreal
            _ = ‖t‖ₑ * eLpNorm (X n - Y) 1 μ := by
              rw [lintegral_const_mul'']
              · simp only [eLpNorm_one_eq_lintegral_enorm,
                  Pi.sub_apply]
              · exact (hmem n).1.sub hY.1 |>.enorm
            _ ≤ ‖t‖ₑ * eLpNorm (X n - Y) 2 μ := by
              gcongr
              exact eLpNorm_le_eLpNorm_of_exponent_le
                (by norm_num) ((hmem n).1.sub hY.1)
      have htendsto :=
        tendsto_integral_of_L1
          (fun ω => Complex.exp ((Y ω * t : ℂ) * I))
          ((by
            fun_prop :
            Continuous
              (fun r : ℝ =>
                Complex.exp ((r * t : ℂ) * I))).comp_aestronglyMeasurable
            hY.1)
          (Filter.Eventually.of_forall fun n =>
            hInt (X n) (hmem n).1)
          hlintegral
      have hcharX (n : ℕ) :
          charFun (Measure.map (X n) μ) t =
            ∫ ω, Complex.exp ((X n ω * t : ℂ) * I) ∂μ := by
        rw [charFun_apply,
          integral_map (hmem n).1.aemeasurable (by fun_prop)]
        simp only [RCLike.inner_apply, conj_trivial, ofReal_mul]
        apply integral_congr_ae
        filter_upwards with ω
        congr 2
        ring
      have hcharY :
          charFun (Measure.map Y μ) t =
            ∫ ω, Complex.exp ((Y ω * t : ℂ) * I) ∂μ := by
        rw [charFun_apply,
          integral_map hY.1.aemeasurable (by fun_prop)]
        simp only [RCLike.inner_apply, conj_trivial, ofReal_mul]
        apply integral_congr_ae
        filter_upwards with ω
        congr 2
        ring
      simpa only [hcharX, hcharY] using htendsto
    have hgaussianLimit :
        Filter.Tendsto
          (fun n => charFun (Measure.map (X n) μ) t)
          Filter.atTop
          (nhds (charFun (gaussianReal 0 v) t)) := by
      simp_rw [hmap, charFun_gaussianReal]
      have hnorm' :
          Filter.Tendsto
            (fun n => (eLpNorm (X n) 2 μ).toReal)
            Filter.atTop (nhds ‖Y₂‖) := by
        simpa only [X₂, Lp.norm_toLp] using hnorm
      let F : ℝ → ℂ := fun r =>
        Complex.exp
          ((t : ℂ) * (0 : ℂ) * I -
            (((⟨r ^ 2, sq_nonneg r⟩ : NNReal) : ℝ) : ℂ) *
              (t : ℂ) ^ 2 / 2)
      have hF : Continuous F := by
        fun_prop
      change
        Filter.Tendsto
          (F ∘ fun n => (eLpNorm (X n) 2 μ).toReal)
          Filter.atTop (nhds (F ‖Y₂‖))
      exact (hF.tendsto ‖Y₂‖).comp hnorm'
    exact tendsto_nhds_unique hcharLimit hgaussianLimit
  refine ⟨?_⟩
  have hmeasure :
      Measure.map Y μ = gaussianReal 0 v := by
    apply Measure.ext_of_charFun
    funext t
    exact hchar t
  rw [hmeasure]
  infer_instance

end

end Anderson4D
