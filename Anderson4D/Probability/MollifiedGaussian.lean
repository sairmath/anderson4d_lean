import Anderson4D.Probability.GaussianClosure
import Anderson4D.Probability.NoiseRegularity

/-!
# Finite-dimensional Gaussianity of the mollified noise

The mollified field is an infinite Fourier series.  This file proves that
every finite real linear combination of its spatial values has a centered
Gaussian law.  We enumerate the lattice, use the `NoiseModel` Gaussian
interface for each finite prefix, and pass to the limit in `L²`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators ENNReal

/-- A fixed enumeration of the four-dimensional frequency lattice. -/
def z4Enumeration : ℕ ≃ Z4 :=
  Classical.choice (nonempty_equiv_of_countable (α := ℕ) (β := Z4))

/-- The first `N` modes in the fixed lattice enumeration. -/
def noiseModePrefix (N : ℕ) : Finset Z4 :=
  (Finset.range N).map z4Enumeration.toEmbedding

namespace NoiseModel

variable (M : NoiseModel)

/-- Deterministic Fourier coefficient of a finite real spatial linear
combination of the mollified field. -/
def xiEpsLinearModeCoeff {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) (a : Fin n → ℝ)
    (k : Z4) : ℂ :=
  ∑ i : Fin n, (a i : ℂ) * mollifiedModeCoeff ρ ε (x i) k

/-- The corresponding real random summand at one Fourier mode. -/
def xiEpsLinearModeTerm {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) (a : Fin n → ℝ)
    (k : Z4) (ω : M.Ω) : ℝ :=
  (xiEpsLinearModeCoeff ρ ε x a k * M.g k ω).re

/-- The actual finite real spatial linear combination. -/
def xiEpsLinearCombination {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) (a : Fin n → ℝ)
    (ω : M.Ω) : ℝ :=
  ∑ i : Fin n, a i * M.xiEps ρ ε ω (x i)

/-- The prefix approximation to `xiEpsLinearCombination`. -/
def xiEpsLinearCombinationFinite {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) (a : Fin n → ℝ)
    (N : ℕ) (ω : M.Ω) : ℝ :=
  ∑ m ∈ Finset.range N,
    M.xiEpsLinearModeTerm ρ ε x a (z4Enumeration m) ω

theorem eLpNorm_g_two (k : Z4) :
    eLpNorm (M.g k) 2 (volume : Measure M.Ω) = 1 := by
  have hmem := M.memLp_g k 2 (by norm_num)
  rw [hmem.eLpNorm_eq_integral_rpow_norm
    (by norm_num) (by norm_num)]
  norm_num [M.integral_norm_g_sq k]

theorem eLpNorm_mul_g_two (c : ℂ) (k : Z4) :
    eLpNorm (fun ω => c * M.g k ω) 2
      (volume : Measure M.Ω) = ‖c‖ₑ := by
  rw [show (fun ω => c * M.g k ω) = c • M.g k by rfl,
    eLpNorm_const_smul, M.eLpNorm_g_two k]
  simp

theorem summable_norm_xiEpsLinearModeCoeff {n : ℕ}
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → T4) (a : Fin n → ℝ) :
    Summable fun k : Z4 => ‖xiEpsLinearModeCoeff ρ ε x a k‖ := by
  have hi (i : Fin n) :
      Summable fun k : Z4 =>
        ‖(a i : ℂ) * mollifiedModeCoeff ρ ε (x i) k‖ := by
    simpa [mollifiedModeCoeff, norm_mul, norm_charT4,
      mul_assoc] using
      (ρ.summable_norm_symbol hε).mul_left
        (‖(a i : ℂ)‖ * ‖(whiteNoiseFourierScale : ℂ)‖)
  have hmajor :
      Summable fun k : Z4 =>
        ∑ i : Fin n,
          ‖(a i : ℂ) * mollifiedModeCoeff ρ ε (x i) k‖ :=
    summable_sum fun i _hi => hi i
  exact hmajor.of_nonneg_of_le
    (fun k => norm_nonneg _)
    (fun k => norm_sum_le _ _)

theorem memLp_xiEpsLinearModeTerm {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) (a : Fin n → ℝ)
    (k : Z4) :
    MemLp (M.xiEpsLinearModeTerm ρ ε x a k) 2
      (volume : Measure M.Ω) := by
  exact
    ((M.memLp_g k 2 (by norm_num)).const_mul
      (xiEpsLinearModeCoeff ρ ε x a k)).re

theorem eLpNorm_xiEpsLinearModeTerm_le {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) (a : Fin n → ℝ)
    (k : Z4) :
    eLpNorm (M.xiEpsLinearModeTerm ρ ε x a k) 2
        (volume : Measure M.Ω) ≤
      ‖xiEpsLinearModeCoeff ρ ε x a k‖ₑ := by
  let c := xiEpsLinearModeCoeff ρ ε x a k
  have hpoint :
      ∀ ω, ‖M.xiEpsLinearModeTerm ρ ε x a k ω‖ₑ ≤
        ‖c * M.g k ω‖ₑ := by
    intro ω
    change ‖(c * M.g k ω).re‖ₑ ≤ ‖c * M.g k ω‖ₑ
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe]
    exact_mod_cast (show ‖(c * M.g k ω).re‖ ≤
      ‖c * M.g k ω‖ by
        simpa only [Real.norm_eq_abs] using
          abs_re_le_norm (c * M.g k ω))
  calc
    eLpNorm (M.xiEpsLinearModeTerm ρ ε x a k) 2
        (volume : Measure M.Ω) ≤
        eLpNorm (fun ω => c * M.g k ω) 2
          (volume : Measure M.Ω) :=
      eLpNorm_mono_enorm hpoint
    _ = ‖c‖ₑ := M.eLpNorm_mul_g_two c k

/-- One Fourier summand as an element of real `L²`. -/
def xiEpsLinearModeLp {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) (a : Fin n → ℝ)
    (k : Z4) :
    Lp ℝ 2 (volume : Measure M.Ω) :=
  (M.memLp_xiEpsLinearModeTerm ρ ε x a k).toLp
    (M.xiEpsLinearModeTerm ρ ε x a k)

theorem norm_xiEpsLinearModeLp_le {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) (a : Fin n → ℝ)
    (k : Z4) :
    ‖M.xiEpsLinearModeLp ρ ε x a k‖ ≤
      ‖xiEpsLinearModeCoeff ρ ε x a k‖ := by
  rw [xiEpsLinearModeLp, Lp.norm_toLp]
  calc
    (eLpNorm (M.xiEpsLinearModeTerm ρ ε x a k) 2
      (volume : Measure M.Ω)).toReal ≤
        ‖xiEpsLinearModeCoeff ρ ε x a k‖ₑ.toReal :=
      ENNReal.toReal_mono enorm_ne_top
        (M.eLpNorm_xiEpsLinearModeTerm_le ρ ε x a k)
    _ = ‖xiEpsLinearModeCoeff ρ ε x a k‖ := by simp

theorem summable_xiEpsLinearModeLp {n : ℕ}
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → T4) (a : Fin n → ℝ) :
    Summable fun k : Z4 => M.xiEpsLinearModeLp ρ ε x a k := by
  apply Summable.of_norm
  exact
    (summable_norm_xiEpsLinearModeCoeff ρ hε x a).of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (M.norm_xiEpsLinearModeLp_le ρ ε x a)

theorem summable_norm_xiEpsLinearModeLp {n : ℕ}
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → T4) (a : Fin n → ℝ) :
    Summable fun k : Z4 => ‖M.xiEpsLinearModeLp ρ ε x a k‖ :=
  (summable_norm_xiEpsLinearModeCoeff ρ hε x a).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (M.norm_xiEpsLinearModeLp_le ρ ε x a)

theorem xiEpsLinearCombinationFinite_eq_linearCombination {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) (a : Fin n → ℝ)
    (N : ℕ) :
    M.xiEpsLinearCombinationFinite ρ ε x a N =
      M.linearCombination (noiseModePrefix N)
        (fun k => (xiEpsLinearModeCoeff ρ ε x a k).re)
        (fun k => -(xiEpsLinearModeCoeff ρ ε x a k).im) := by
  funext ω
  simp only [xiEpsLinearCombinationFinite, linearCombination,
    noiseModePrefix, Finset.sum_map, Function.Embedding.coeFn_mk]
  apply Finset.sum_congr rfl
  intro m hm
  unfold xiEpsLinearModeTerm
  rw [Complex.mul_re]
  ring

theorem hasGaussianLaw_xiEpsLinearCombinationFinite {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) (a : Fin n → ℝ)
    (N : ℕ) :
    HasGaussianLaw
      (M.xiEpsLinearCombinationFinite ρ ε x a N)
      (volume : Measure M.Ω) := by
  rw [M.xiEpsLinearCombinationFinite_eq_linearCombination]
  refine ⟨?_⟩
  rw [M.map_linearCombination_eq_gaussianReal]
  infer_instance

theorem integral_xiEpsLinearCombinationFinite {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) (a : Fin n → ℝ)
    (N : ℕ) :
    ∫ ω, M.xiEpsLinearCombinationFinite ρ ε x a N ω
        ∂(volume : Measure M.Ω) = 0 := by
  rw [M.xiEpsLinearCombinationFinite_eq_linearCombination]
  exact M.integral_linearCombination _ _ _

theorem memLp_xiEpsLinearCombinationFinite {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) (a : Fin n → ℝ)
    (N : ℕ) :
    MemLp (M.xiEpsLinearCombinationFinite ρ ε x a N) 2
      (volume : Measure M.Ω) :=
  (M.hasGaussianLaw_xiEpsLinearCombinationFinite ρ ε x a N).memLp_two

/-- On the almost-sure absolute-convergence event, summing the combined
mode terms recovers the finite spatial linear combination. -/
theorem ae_tsum_xiEpsLinearModeTerm_eq {n : ℕ}
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → T4) (a : Fin n → ℝ) :
    (fun ω => ∑' k : Z4,
      M.xiEpsLinearModeTerm ρ ε x a k ω) =ᵐ[
        (volume : Measure M.Ω)]
      M.xiEpsLinearCombination ρ ε x a := by
  filter_upwards
    [M.ae_forall_summable_mollified_fourier ρ hε] with ω hω
  have hi (i : Fin n) :
      Summable fun k : Z4 =>
        (a i : ℂ) * mollifiedModeCoeff ρ ε (x i) k * M.g k ω := by
    refine
      ((hω (x i)).mul_left
        ((a i : ℂ) * (whiteNoiseFourierScale : ℂ))).congr ?_
    intro k
    unfold mollifiedModeCoeff
    ring
  have hallComplex :
      Summable fun k : Z4 =>
        xiEpsLinearModeCoeff ρ ε x a k * M.g k ω := by
    have hsum :
        Summable fun k : Z4 =>
          ∑ i : Fin n,
            ((a i : ℂ) * mollifiedModeCoeff ρ ε (x i) k *
              M.g k ω) :=
      summable_sum fun i _hi => hi i
    refine hsum.congr fun k => ?_
    unfold xiEpsLinearModeCoeff
    rw [Finset.sum_mul]
  calc
    (∑' k : Z4, M.xiEpsLinearModeTerm ρ ε x a k ω) =
        (∑' k : Z4,
          xiEpsLinearModeCoeff ρ ε x a k * M.g k ω).re := by
      symm
      exact Complex.reCLM.map_tsum hallComplex
    _ = (∑' k : Z4,
          ∑ i : Fin n,
            ((a i : ℂ) * mollifiedModeCoeff ρ ε (x i) k *
              M.g k ω)).re := by
      congr 2
      funext k
      unfold xiEpsLinearModeCoeff
      rw [Finset.sum_mul]
    _ = (∑ i : Fin n,
          ∑' k : Z4,
            ((a i : ℂ) * mollifiedModeCoeff ρ ε (x i) k *
              M.g k ω)).re := by
      rw [Summable.tsum_finsetSum
        (s := (Finset.univ : Finset (Fin n)))
        (fun i _hi => hi i)]
    _ = (∑ i : Fin n,
          (a i : ℂ) * M.xiEpsC ρ ε ω (x i)).re := by
      congr 2
      funext i
      unfold xiEpsC
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      ring
    _ = M.xiEpsLinearCombination ρ ε x a ω := by
      unfold xiEpsLinearCombination
      change Complex.reCLM
        (∑ i : Fin n, (a i : ℂ) * M.xiEpsC ρ ε ω (x i)) =
          ∑ i : Fin n, a i * M.xiEps ρ ε ω (x i)
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      change
        ((a i : ℂ) * M.xiEpsC ρ ε ω (x i)).re =
          a i * M.xiEps ρ ε ω (x i)
      rw [Complex.mul_re]
      simp

/-- The `L²` sum of the single-mode terms represents the actual finite
spatial linear combination. -/
theorem ae_coe_tsum_xiEpsLinearModeLp_eq {n : ℕ}
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → T4) (a : Fin n → ℝ) :
    (⇑(∑' k : Z4, M.xiEpsLinearModeLp ρ ε x a k)) =ᵐ[
        (volume : Measure M.Ω)]
      M.xiEpsLinearCombination ρ ε x a := by
  have henorm :
      ∑' k : Z4, ‖M.xiEpsLinearModeLp ρ ε x a k‖ₑ ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr
      (M.summable_norm_xiEpsLinearModeLp ρ hε x a)
  have hcoeTerm :
      ∀ᵐ ω ∂(volume : Measure M.Ω), ∀ k : Z4,
        M.xiEpsLinearModeLp ρ ε x a k ω =
          M.xiEpsLinearModeTerm ρ ε x a k ω := by
    rw [ae_all_iff]
    intro k
    exact
      (M.memLp_xiEpsLinearModeTerm ρ ε x a k).coeFn_toLp
  filter_upwards
    [Lp.coeFn_tsum henorm, hcoeTerm,
      M.ae_tsum_xiEpsLinearModeTerm_eq ρ hε x a] with
      ω hsum hterm htarget
  calc
    (∑' k : Z4, M.xiEpsLinearModeLp ρ ε x a k) ω =
        ∑' k : Z4, M.xiEpsLinearModeLp ρ ε x a k ω := hsum
    _ = ∑' k : Z4, M.xiEpsLinearModeTerm ρ ε x a k ω := by
      apply tsum_congr
      exact hterm
    _ = M.xiEpsLinearCombination ρ ε x a ω := htarget

theorem memLp_xiEpsLinearCombination {n : ℕ}
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → T4) (a : Fin n → ℝ) :
    MemLp (M.xiEpsLinearCombination ρ ε x a) 2
      (volume : Measure M.Ω) := by
  exact
    (memLp_congr_ae
      (M.ae_coe_tsum_xiEpsLinearModeLp_eq ρ hε x a)).mp
      (Lp.memLp (∑' k : Z4,
        M.xiEpsLinearModeLp ρ ε x a k))

theorem tsum_xiEpsLinearModeLp_eq_toLp {n : ℕ}
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → T4) (a : Fin n → ℝ) :
    (∑' k : Z4, M.xiEpsLinearModeLp ρ ε x a k) =
      (M.memLp_xiEpsLinearCombination ρ hε x a).toLp
        (M.xiEpsLinearCombination ρ ε x a) := by
  apply Lp.ext (μ := (volume : Measure M.Ω))
  exact
    (M.ae_coe_tsum_xiEpsLinearModeLp_eq ρ hε x a).trans
      (M.memLp_xiEpsLinearCombination ρ hε x a).coeFn_toLp.symm

theorem sum_range_xiEpsLinearModeLp_eq_toLp_finite {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) (a : Fin n → ℝ)
    (N : ℕ) :
    (∑ m ∈ Finset.range N,
      M.xiEpsLinearModeLp ρ ε x a (z4Enumeration m)) =
      (M.memLp_xiEpsLinearCombinationFinite ρ ε x a N).toLp
        (M.xiEpsLinearCombinationFinite ρ ε x a N) := by
  apply Lp.ext (μ := (volume : Measure M.Ω))
  have hcoeTerm :
      ∀ᵐ ω ∂(volume : Measure M.Ω), ∀ k : Z4,
        M.xiEpsLinearModeLp ρ ε x a k ω =
          M.xiEpsLinearModeTerm ρ ε x a k ω := by
    rw [ae_all_iff]
    intro k
    exact
      (M.memLp_xiEpsLinearModeTerm ρ ε x a k).coeFn_toLp
  filter_upwards
    [Lp.coeFn_fun_finsetSum (Finset.range N)
      (fun m => M.xiEpsLinearModeLp ρ ε x a (z4Enumeration m)),
      hcoeTerm,
      (M.memLp_xiEpsLinearCombinationFinite ρ ε x a N).coeFn_toLp] with
      ω hsum hterm hfinite
  rw [hsum, hfinite]
  unfold xiEpsLinearCombinationFinite
  apply Finset.sum_congr rfl
  intro m _hm
  exact hterm (z4Enumeration m)

theorem tendsto_eLpNorm_xiEpsLinearCombinationFinite {n : ℕ}
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → T4) (a : Fin n → ℝ) :
    Filter.Tendsto
      (fun N =>
        eLpNorm
          (M.xiEpsLinearCombinationFinite ρ ε x a N -
            M.xiEpsLinearCombination ρ ε x a)
          2 (volume : Measure M.Ω))
      Filter.atTop (nhds 0) := by
  let F : ℕ → Lp ℝ 2 (volume : Measure M.Ω) :=
    fun m => M.xiEpsLinearModeLp ρ ε x a (z4Enumeration m)
  have hF : Summable F :=
    (M.summable_xiEpsLinearModeLp ρ hε x a).comp_injective
      z4Enumeration.injective
  have hlim :
      Filter.Tendsto
        (fun N => ∑ m ∈ Finset.range N, F m)
        Filter.atTop (nhds (∑' m, F m)) :=
    hF.hasSum.tendsto_sum_nat
  have hlimit :
      (∑' m, F m) =
        (M.memLp_xiEpsLinearCombination ρ hε x a).toLp
          (M.xiEpsLinearCombination ρ ε x a) := by
    rw [show (∑' m, F m) =
        ∑' k : Z4, M.xiEpsLinearModeLp ρ ε x a k by
      exact z4Enumeration.tsum_eq
        (fun k => M.xiEpsLinearModeLp ρ ε x a k)]
    exact M.tsum_xiEpsLinearModeLp_eq_toLp ρ hε x a
  have hlim' :
      Filter.Tendsto
        (fun N =>
          (M.memLp_xiEpsLinearCombinationFinite ρ ε x a N).toLp
            (M.xiEpsLinearCombinationFinite ρ ε x a N))
        Filter.atTop
        (nhds
          ((M.memLp_xiEpsLinearCombination ρ hε x a).toLp
            (M.xiEpsLinearCombination ρ ε x a))) := by
    rw [← hlimit]
    refine hlim.congr' ?_
    filter_upwards with N
    exact
      M.sum_range_xiEpsLinearModeLp_eq_toLp_finite ρ ε x a N
  have hconv :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm
      (fun N =>
        (M.memLp_xiEpsLinearCombinationFinite ρ ε x a N).toLp
          (M.xiEpsLinearCombinationFinite ρ ε x a N))
      (M.xiEpsLinearCombination ρ ε x a)
      (M.memLp_xiEpsLinearCombination ρ hε x a)).mp hlim'
  refine hconv.congr' ?_
  filter_upwards with N
  apply eLpNorm_congr_ae
  filter_upwards
    [(M.memLp_xiEpsLinearCombinationFinite ρ ε x a N).coeFn_toLp] with
      ω hω
  simp only [Pi.sub_apply, hω]

/-- Every finite real linear combination of spatial values of the
mollified field has a Gaussian law. -/
theorem hasGaussianLaw_xiEpsLinearCombination {n : ℕ}
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → T4) (a : Fin n → ℝ) :
    HasGaussianLaw (M.xiEpsLinearCombination ρ ε x a)
      (volume : Measure M.Ω) := by
  exact hasGaussianLaw_of_tendsto_eLpNorm_two
    (fun N => M.xiEpsLinearCombinationFinite ρ ε x a N)
    (M.xiEpsLinearCombination ρ ε x a)
    (M.hasGaussianLaw_xiEpsLinearCombinationFinite ρ ε x a)
    (M.integral_xiEpsLinearCombinationFinite ρ ε x a)
    (M.memLp_xiEpsLinearCombinationFinite ρ ε x a)
    (M.memLp_xiEpsLinearCombination ρ hε x a)
    (M.tendsto_eLpNorm_xiEpsLinearCombinationFinite ρ hε x a)

theorem integral_xiEpsLinearModeTerm {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) (a : Fin n → ℝ)
    (k : Z4) :
    ∫ ω, M.xiEpsLinearModeTerm ρ ε x a k ω
        ∂(volume : Measure M.Ω) = 0 := by
  let c := xiEpsLinearModeCoeff ρ ε x a k
  have hfun :
      M.xiEpsLinearModeTerm ρ ε x a k =
        M.linearCombination {k}
          (fun _ => c.re) (fun _ => -c.im) := by
    funext ω
    simp only [xiEpsLinearModeTerm, linearCombination,
      Finset.sum_singleton]
    rw [Complex.mul_re]
    ring
  rw [hfun]
  exact M.integral_linearCombination _ _ _

theorem integral_norm_xiEpsLinearModeTerm_le {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) (a : Fin n → ℝ)
    (k : Z4) :
    ∫ ω, ‖M.xiEpsLinearModeTerm ρ ε x a k ω‖
        ∂(volume : Measure M.Ω) ≤
      ‖xiEpsLinearModeCoeff ρ ε x a k‖ := by
  let c := xiEpsLinearModeCoeff ρ ε x a k
  have hterm :
      Integrable (fun ω =>
        ‖M.xiEpsLinearModeTerm ρ ε x a k ω‖)
        (volume : Measure M.Ω) :=
    (M.memLp_xiEpsLinearModeTerm ρ ε x a k).integrable
      (by norm_num) |>.norm
  have hcomplex :
      Integrable (fun ω => ‖c * M.g k ω‖)
        (volume : Measure M.Ω) :=
    (((M.memLp_g k 2 (by norm_num)).const_mul c).integrable
      (by norm_num)).norm
  calc
    (∫ ω, ‖M.xiEpsLinearModeTerm ρ ε x a k ω‖
        ∂(volume : Measure M.Ω)) ≤
        ∫ ω, ‖c * M.g k ω‖
          ∂(volume : Measure M.Ω) := by
      apply integral_mono hterm hcomplex
      intro ω
      change ‖(c * M.g k ω).re‖ ≤ ‖c * M.g k ω‖
      simpa only [Real.norm_eq_abs] using
        abs_re_le_norm (c * M.g k ω)
    _ = ‖c‖ * ∫ ω, ‖M.g k ω‖
        ∂(volume : Measure M.Ω) := by
      simp_rw [norm_mul]
      rw [integral_const_mul]
    _ ≤ ‖c‖ := by
      exact mul_le_of_le_one_right (norm_nonneg _)
        (M.integral_norm_g_le_one k)

theorem integral_xiEpsLinearCombination {n : ℕ}
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → T4) (a : Fin n → ℝ) :
    ∫ ω, M.xiEpsLinearCombination ρ ε x a ω
        ∂(volume : Measure M.Ω) = 0 := by
  have hint (k : Z4) :
      Integrable (M.xiEpsLinearModeTerm ρ ε x a k)
        (volume : Measure M.Ω) :=
    (M.memLp_xiEpsLinearModeTerm ρ ε x a k).integrable
      (by norm_num)
  have hnorm :
      Summable fun k : Z4 =>
        ∫ ω, ‖M.xiEpsLinearModeTerm ρ ε x a k ω‖
          ∂(volume : Measure M.Ω) := by
    exact
      (summable_norm_xiEpsLinearModeCoeff ρ hε x a).of_nonneg_of_le
        (fun _ => integral_nonneg fun _ => norm_nonneg _)
        (M.integral_norm_xiEpsLinearModeTerm_le ρ ε x a)
  rw [integral_congr_ae
    (M.ae_tsum_xiEpsLinearModeTerm_eq ρ hε x a).symm]
  rw [← integral_tsum_of_summable_integral_norm hint hnorm]
  simp_rw [M.integral_xiEpsLinearModeTerm ρ ε x a]
  simp

/-- Finite spatial vector of mollified-field evaluations. -/
def xiEpsVector {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) (ω : M.Ω) :
    Fin n → ℝ :=
  fun i => M.xiEps ρ ε ω (x i)

theorem measurable_xiEpsVector {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) :
    Measurable (M.xiEpsVector ρ ε x) := by
  apply measurable_pi_lambda
  intro i
  exact M.measurable_xiEps ρ ε (x i)

/-- Coefficients of a functional on the finite spatial vector. -/
def xiEpsVectorDualCoeff {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] ℝ) (i : Fin n) : ℝ :=
  L (fun j => if i = j then 1 else 0)

theorem apply_xiEpsVector_eq_linearCombination {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4)
    (L : (Fin n → ℝ) →L[ℝ] ℝ) (ω : M.Ω) :
    L (M.xiEpsVector ρ ε x ω) =
      M.xiEpsLinearCombination ρ ε x (xiEpsVectorDualCoeff L) ω := by
  change L.toLinearMap (M.xiEpsVector ρ ε x ω) = _
  rw [LinearMap.pi_apply_eq_sum_univ]
  unfold xiEpsVector xiEpsVectorDualCoeff xiEpsLinearCombination
  simp only [smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [mul_comm]
  change
    L (fun j => if i = j then 1 else 0) *
        M.xiEps ρ ε ω (x i) =
      L (fun j => if i = j then 1 else 0) *
        M.xiEps ρ ε ω (x i)
  rfl

theorem isGaussian_map_xiEpsVector {n : ℕ}
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → T4) :
    IsGaussian
      (Measure.map (M.xiEpsVector ρ ε x)
        (volume : Measure M.Ω)) := by
  apply isGaussian_of_map_eq_gaussianReal
  intro L
  let a : Fin n → ℝ := xiEpsVectorDualCoeff L
  have hG := M.hasGaussianLaw_xiEpsLinearCombination ρ hε x a
  refine
    ⟨∫ ω, M.xiEpsLinearCombination ρ ε x a ω
        ∂(volume : Measure M.Ω),
      Var[M.xiEpsLinearCombination ρ ε x a;
        (volume : Measure M.Ω)].toNNReal, ?_⟩
  rw [← hG.map_eq_gaussianReal]
  rw [Measure.map_map]
  · apply Measure.map_congr
    filter_upwards with ω
    exact M.apply_xiEpsVector_eq_linearCombination ρ ε x L ω
  · fun_prop
  · exact M.measurable_xiEpsVector ρ ε x

/-- The finite spatial vector in its canonical Euclidean realization. -/
def xiEpsEuclideanVector {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) (ω : M.Ω) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (M.xiEpsVector ρ ε x ω)

theorem measurable_xiEpsEuclideanVector {n : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin n → T4) :
    Measurable (M.xiEpsEuclideanVector ρ ε x) := by
  let L : (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  exact L.continuous.measurable.comp
    (M.measurable_xiEpsVector ρ ε x)

theorem isGaussian_map_xiEpsEuclideanVector {n : ℕ}
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → T4) :
    IsGaussian
      (Measure.map (M.xiEpsEuclideanVector ρ ε x)
        (volume : Measure M.Ω)) := by
  let μv : Measure (Fin n → ℝ) :=
    Measure.map (M.xiEpsVector ρ ε x) (volume : Measure M.Ω)
  letI : IsGaussian μv := M.isGaussian_map_xiEpsVector ρ hε x
  let L : (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  change IsGaussian
    (Measure.map (L ∘ M.xiEpsVector ρ ε x)
      (volume : Measure M.Ω))
  rw [← Measure.map_map L.continuous.measurable
    (M.measurable_xiEpsVector ρ ε x)]
  infer_instance

theorem integral_xiEps
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (z : T4) :
    ∫ ω, M.xiEps ρ ε ω z ∂(volume : Measure M.Ω) = 0 := by
  let x : Fin 1 → T4 := fun _ => z
  let a : Fin 1 → ℝ := fun _ => 1
  have h := M.integral_xiEpsLinearCombination ρ hε x a
  simpa [xiEpsLinearCombination, x, a] using h

theorem integral_id_map_xiEpsVector {n : ℕ}
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → T4) :
    ∫ y, y ∂Measure.map (M.xiEpsVector ρ ε x)
      (volume : Measure M.Ω) = 0 := by
  let μv : Measure (Fin n → ℝ) :=
    Measure.map (M.xiEpsVector ρ ε x) (volume : Measure M.Ω)
  letI : IsGaussian μv := M.isGaussian_map_xiEpsVector ρ hε x
  apply funext
  intro i
  let L : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hscalar : ∫ y, L y ∂μv = 0 := by
    rw [integral_map
      (M.measurable_xiEpsVector ρ ε x).aemeasurable
      (IsGaussian.integrable_dual μv L).aestronglyMeasurable]
    exact M.integral_xiEps ρ hε (x i)
  change L (∫ y, y ∂μv) = L 0
  calc
    L (∫ y, y ∂μv) = ∫ y, L y ∂μv :=
      (L.integral_comp_comm IsGaussian.integrable_id).symm
    _ = 0 := hscalar
    _ = L 0 := L.map_zero.symm

theorem integral_id_map_xiEpsEuclideanVector {n : ℕ}
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → T4) :
    ∫ y, y ∂Measure.map (M.xiEpsEuclideanVector ρ ε x)
      (volume : Measure M.Ω) = 0 := by
  let μv : Measure (Fin n → ℝ) :=
    Measure.map (M.xiEpsVector ρ ε x) (volume : Measure M.Ω)
  letI : IsGaussian μv := M.isGaussian_map_xiEpsVector ρ hε x
  let L : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap
  change ∫ y, y ∂Measure.map (L ∘ M.xiEpsVector ρ ε x)
    (volume : Measure M.Ω) = 0
  rw [← Measure.map_map L.continuous.measurable
    (M.measurable_xiEpsVector ρ ε x)]
  calc
    (∫ y, y ∂μv.map L) = L (∫ y, y ∂μv) := by
      haveI : IsGaussian (μv.map L) := inferInstance
      calc
        _ = ∫ y, L y ∂μv :=
          integral_map (μ := μv) (φ := L) (f := id)
            L.continuous.measurable.aemeasurable
            (IsGaussian.integrable_id
              (μ := μv.map L)).aestronglyMeasurable
        _ = _ := L.integral_comp_comm
          (IsGaussian.integrable_id (μ := μv))
    _ = 0 := by
      rw [M.integral_id_map_xiEpsVector ρ hε x]
      exact L.map_zero

end NoiseModel

end

end Anderson4D
