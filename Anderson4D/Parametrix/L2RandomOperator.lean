import Anderson4D.Parametrix.L2Realization
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Measurable random multiplication operators

This file refines the samplewise construction in `L2Realization.lean`.
The mollified Fourier series is summed in the separable Banach space of
continuous functions on the compact torus.  Continuous functions then map
continuously to multiplication operators on `L²`.  Consequently the
random potential and `K = G M` are honest strongly measurable
operator-valued random variables, rather than merely a.e.-defined
samplewise operators.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

/- The continuous-map space does not carry a global measurable-space
instance in mathlib; this project consistently uses its Borel structure. -/
noncomputable instance instMeasurableSpaceContinuousMapT4 :
    MeasurableSpace C(T4, ℂ) :=
  borel C(T4, ℂ)

instance instBorelSpaceContinuousMapT4 :
    BorelSpace C(T4, ℂ) where
  measurable_eq := rfl

noncomputable instance instMeasurableSpaceTorusL2Operator :
    MeasurableSpace (TorusL2 →L[ℂ] TorusL2) :=
  borel (TorusL2 →L[ℂ] TorusL2)

instance instBorelSpaceTorusL2Operator :
    BorelSpace (TorusL2 →L[ℂ] TorusL2) where
  measurable_eq := rfl

/-! ## Continuous functions act continuously on `L²` -/

/-- Multiplication by a continuous torus function. -/
def continuousMultiplicationOp (m : C(T4, ℂ)) :
    TorusL2 →L[ℂ] TorusL2 :=
  boundedMultiplicationCLM m ‖m‖ (norm_nonneg m)
    m.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => m.norm_coe_le_norm x)

@[simp] theorem continuousMultiplicationOp_apply_ae
    (m : C(T4, ℂ)) (f : TorusL2) :
    continuousMultiplicationOp m f =ᵐ[haarT4]
      fun x => m x * f x :=
  boundedMultiplicationCLM_apply_ae m ‖m‖ (norm_nonneg m)
    m.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => m.norm_coe_le_norm x) f

theorem continuousMultiplicationOp_norm_le (m : C(T4, ℂ)) :
    ‖continuousMultiplicationOp m‖ ≤ ‖m‖ :=
  boundedMultiplicationCLM_norm_le m ‖m‖ (norm_nonneg m)
    m.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => m.norm_coe_le_norm x)

/-- Linearity of the continuous-function multiplication construction. -/
def continuousMultiplicationLM :
    C(T4, ℂ) →ₗ[ℂ] (TorusL2 →L[ℂ] TorusL2) where
  toFun := continuousMultiplicationOp
  map_add' m n := by
    apply ContinuousLinearMap.ext
    intro f
    change continuousMultiplicationOp (m + n) f =
      continuousMultiplicationOp m f + continuousMultiplicationOp n f
    apply Lp.ext
    filter_upwards
      [continuousMultiplicationOp_apply_ae (m + n) f,
        continuousMultiplicationOp_apply_ae m f,
        continuousMultiplicationOp_apply_ae n f,
        Lp.coeFn_add
          (continuousMultiplicationOp m f)
          (continuousMultiplicationOp n f)] with x hmn hm hn hadd
    rw [hmn, hadd]
    change (m x + n x) * f x =
      continuousMultiplicationOp m f x +
        continuousMultiplicationOp n f x
    rw [hm, hn]
    ring
  map_smul' c m := by
    apply ContinuousLinearMap.ext
    intro f
    change continuousMultiplicationOp (c • m) f =
      c • continuousMultiplicationOp m f
    apply Lp.ext
    filter_upwards
      [continuousMultiplicationOp_apply_ae (c • m) f,
        continuousMultiplicationOp_apply_ae m f,
        Lp.coeFn_smul c (continuousMultiplicationOp m f)] with x hcm hm hsmul
    rw [hcm, hsmul]
    change (c * m x) * f x = c * continuousMultiplicationOp m f x
    rw [hm]
    ring

/-- Continuous dependence of the `L²` multiplication operator on its
continuous multiplier. -/
def continuousMultiplicationCLM :
    C(T4, ℂ) →L[ℂ] (TorusL2 →L[ℂ] TorusL2) :=
  LinearMap.mkContinuous continuousMultiplicationLM 1 fun m => by
    change ‖continuousMultiplicationOp m‖ ≤ 1 * ‖m‖
    simpa using continuousMultiplicationOp_norm_le m

@[simp] theorem continuousMultiplicationCLM_apply
    (m : C(T4, ℂ)) :
    continuousMultiplicationCLM m = continuousMultiplicationOp m :=
  rfl

theorem continuousMultiplicationCLM_norm_le_one :
    ‖continuousMultiplicationCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro m
  simpa using continuousMultiplicationOp_norm_le m

/-! ## A continuous-map version of the mollified Fourier series -/

theorem norm_charT4Continuous (k : Z4) :
    ‖charT4Continuous k‖ = 1 := by
  apply le_antisymm
  · exact ((charT4Continuous k).norm_le zero_le_one).2 fun x =>
      (norm_charT4 k x).le
  · have h := ContinuousMap.norm_coe_le_norm
      (charT4Continuous k) (0 : T4)
    simpa [norm_charT4] using h

/-- One continuous-function-valued Fourier summand of the mollified
noise. -/
def mollifiedNoiseContinuousTerm
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (k : Z4) (ω : M.Ω) : C(T4, ℂ) :=
  ((NoiseModel.whiteNoiseFourierScale : ℂ) *
      M.mollifiedRandomCoeff ρ ε k ω) •
    charT4Continuous k

theorem measurable_mollifiedNoiseContinuousTerm
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    Measurable (mollifiedNoiseContinuousTerm M ρ ε k) := by
  unfold mollifiedNoiseContinuousTerm
  exact
    (Measurable.const_mul
      (M.measurable_mollifiedRandomCoeff ρ ε k)
      (NoiseModel.whiteNoiseFourierScale : ℂ)).smul_const _

theorem norm_mollifiedNoiseContinuousTerm
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (k : Z4) (ω : M.Ω) :
    ‖mollifiedNoiseContinuousTerm M ρ ε k ω‖ =
      ‖NoiseModel.whiteNoiseFourierScale‖ *
        ‖M.mollifiedRandomCoeff ρ ε k ω‖ := by
  simp only [mollifiedNoiseContinuousTerm, norm_smul,
    norm_mul, norm_charT4Continuous, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

/-- Canonical continuous-function-valued mollified noise.  The Banach
space `tsum` is zero off summability, giving a measurable totalization
that agrees with `xiEps` almost surely at every positive scale. -/
def xiEpsContinuousMap
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (ω : M.Ω) : C(T4, ℂ) :=
  ∑' k : Z4, mollifiedNoiseContinuousTerm M ρ ε k ω

theorem measurable_xiEpsContinuousMap
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) :
    Measurable (xiEpsContinuousMap M ρ ε) := by
  unfold xiEpsContinuousMap
  exact Measurable.tsum fun k =>
    measurable_mollifiedNoiseContinuousTerm M ρ ε k

theorem summable_mollifiedNoiseContinuousTerm_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖) :
    Summable fun k : Z4 =>
      mollifiedNoiseContinuousTerm M ρ ε k ω := by
  apply Summable.of_norm
  exact
    (hω.mul_left ‖NoiseModel.whiteNoiseFourierScale‖).congr
      (fun k => (norm_mollifiedNoiseContinuousTerm
        M ρ ε k ω).symm)

theorem xiEpsContinuousMap_apply_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖)
    (x : T4) :
    xiEpsContinuousMap M ρ ε ω x =
      (NoiseModel.whiteNoiseFourierScale : ℂ) *
        ∑' k : Z4,
          M.mollifiedRandomCoeff ρ ε k ω * charT4 k x := by
  have hterm :=
    summable_mollifiedNoiseContinuousTerm_of_summable
      M ρ ε ω hω
  rw [xiEpsContinuousMap,
    ← ContinuousMap.tsum_apply hterm x, ← tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [mollifiedNoiseContinuousTerm,
    ContinuousMap.smul_apply, charT4Continuous_apply,
    smul_eq_mul]
  ring

theorem xiEpsContinuousMap_re_eq_xiEps_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖)
    (x : T4) :
    (xiEpsContinuousMap M ρ ε ω x).re =
      M.xiEps ρ ε ω x := by
  rw [xiEpsContinuousMap_apply_of_summable M ρ ε ω hω x]
  unfold NoiseModel.xiEps NoiseModel.mollifiedRandomCoeff
  simp [Complex.mul_re]

theorem xiEpsContinuousMap_eq_xiEps_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖)
    (x : T4) :
    xiEpsContinuousMap M ρ ε ω x =
      (M.xiEps ρ ε ω x : ℂ) := by
  apply Complex.ext
  · simpa using
      xiEpsContinuousMap_re_eq_xiEps_of_summable
        M ρ ε ω hω x
  · rw [xiEpsContinuousMap_apply_of_summable M ρ ε ω hω x]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.ofReal_im]
    unfold NoiseModel.mollifiedRandomCoeff
    rw [NoiseModel.tsum_mollified_fourier_im_eq_zero]
    simp

/-- At positive scale the continuous-map totalization agrees with the
original scalar Fourier-series definition, simultaneously at all torus
points. -/
theorem ae_forall_xiEpsContinuousMap_re_eq_xiEps
    (M : NoiseModel) (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂(volume : Measure M.Ω), ∀ x : T4,
      (xiEpsContinuousMap M ρ ε ω x).re =
        M.xiEps ρ ε ω x := by
  filter_upwards
    [M.ae_summable_norm_mollifiedRandomCoeff ρ hε] with ω hω
  exact xiEpsContinuousMap_re_eq_xiEps_of_summable
    M ρ ε ω hω

/-! ## Measurable random potential and `K` -/

/-- The continuous-map-valued Anderson potential.  Its Banach `tsum`
totalization is measurable for every sample and agrees a.s. with
`multFun` at positive scale. -/
def measurableMollifiedPotential
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) : C(T4, ℂ) :=
  (lamEps lam ε : ℂ) • xiEpsContinuousMap M ρ ε ω -
    ContinuousMap.const T4 (renormCEps ρ lam ε : ℂ)

theorem measurable_measurableMollifiedPotential
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) :
    Measurable (measurableMollifiedPotential M ρ lam ε) := by
  unfold measurableMollifiedPotential
  exact
    (measurable_xiEpsContinuousMap M ρ ε).const_smul
      (lamEps lam ε : ℂ) |>.sub measurable_const

theorem measurableMollifiedPotential_apply_eq_multFun_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖)
    (x : T4) :
    measurableMollifiedPotential M ρ lam ε ω x =
      (multFun M ρ lam ε x ω : ℝ) := by
  rw [measurableMollifiedPotential,
    ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    xiEpsContinuousMap_eq_xiEps_of_summable M ρ ε ω hω x]
  simp [multFun]

/-- Preferred measurable multiplication-operator realization of the
mollified potential. -/
def measurableMollifiedPotentialL2Op
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) :
    TorusL2 →L[ℂ] TorusL2 :=
  continuousMultiplicationCLM
    (measurableMollifiedPotential M ρ lam ε ω)

theorem measurable_measurableMollifiedPotentialL2Op
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) :
    Measurable (measurableMollifiedPotentialL2Op M ρ lam ε) :=
  continuousMultiplicationCLM.measurable.comp
    (measurable_measurableMollifiedPotential M ρ lam ε)

theorem measurableMollifiedPotentialL2Op_apply_ae_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖)
    (f : TorusL2) :
    measurableMollifiedPotentialL2Op M ρ lam ε ω f =ᵐ[haarT4]
      fun x => (multFun M ρ lam ε x ω : ℝ) * f x := by
  filter_upwards
    [continuousMultiplicationOp_apply_ae
      (measurableMollifiedPotential M ρ lam ε ω) f] with x hx
  change continuousMultiplicationOp
      (measurableMollifiedPotential M ρ lam ε ω) f x =
    (multFun M ρ lam ε x ω : ℂ) * f x
  rw [hx,
    measurableMollifiedPotential_apply_eq_multFun_of_summable
      M ρ lam ε ω hω x]

/-- The measurable random bounded operator `Kε = G ∘ Mε`. -/
def measurableAndersonK
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) :
    TorusL2 →L[ℂ] TorusL2 :=
  Kop greenL2Op (measurableMollifiedPotentialL2Op M ρ lam ε ω)

theorem measurable_measurableAndersonK
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) :
    Measurable (measurableAndersonK M ρ lam ε) := by
  exact
    ((continuous_const.mul continuous_id).measurable).comp
      (measurable_measurableMollifiedPotentialL2Op M ρ lam ε)

theorem measurable_norm_sq_measurableAndersonK
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) :
    Measurable fun ω => ‖measurableAndersonK M ρ lam ε ω‖ ^ 2 :=
  (measurable_measurableAndersonK M ρ lam ε).norm.pow_const 2

/-! ## Quantitative `L²(Ω)` control -/

/-- A noise Fourier coefficient as an element of `L²(Ω; ℂ)`. -/
def noiseCoeffLp (M : NoiseModel) (k : Z4) :
    Lp ℂ 2 (volume : Measure M.Ω) :=
  (M.memLp_g k 2 (by norm_num)).toLp (M.g k)

theorem norm_noiseCoeffLp (M : NoiseModel) (k : Z4) :
    ‖noiseCoeffLp M k‖ = 1 := by
  let hg : MemLp (M.g k) 2 (volume : Measure M.Ω) :=
    M.memLp_g k 2 (by norm_num)
  have hinner :
      ⟪noiseCoeffLp M k, noiseCoeffLp M k⟫_ℂ = 1 := by
    rw [MeasureTheory.L2.inner_def]
    calc
      (∫ ω, ⟪noiseCoeffLp M k ω,
          noiseCoeffLp M k ω⟫_ℂ) =
          ∫ ω, ((‖M.g k ω‖ ^ 2 : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [hg.coeFn_toLp] with ω hω
        rw [noiseCoeffLp, hω, inner_self_eq_norm_sq_to_K]
        norm_cast
      _ = ((∫ ω, ‖M.g k ω‖ ^ 2 : ℝ) : ℂ) :=
        integral_complex_ofReal
      _ = 1 := by rw [M.integral_norm_g_sq]; norm_num
  have hsqC :
      ((‖noiseCoeffLp M k‖ : ℂ) ^ 2) = 1 :=
    (inner_self_eq_norm_sq_to_K (noiseCoeffLp M k)).symm.trans
      hinner
  have hsq : ‖noiseCoeffLp M k‖ ^ 2 = 1 := by
    exact_mod_cast hsqC
  nlinarith [norm_nonneg (noiseCoeffLp M k)]

/-- Each continuous Fourier summand has the expected `L²(Ω)` bound. -/
theorem memLp_mollifiedNoiseContinuousTerm
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    MemLp (mollifiedNoiseContinuousTerm M ρ ε k) 2
      (volume : Measure M.Ω) := by
  apply (M.memLp_g k 2 (by norm_num)).of_le_mul
    (c := ‖NoiseModel.whiteNoiseFourierScale‖ *
      ‖ρ.symbol ε k‖)
  · exact
      Measurable.aestronglyMeasurable
        (measurable_mollifiedNoiseContinuousTerm M ρ ε k)
  · filter_upwards with ω
    rw [norm_mollifiedNoiseContinuousTerm,
      NoiseModel.mollifiedRandomCoeff, norm_mul]
    ring_nf
    exact le_rfl

/-- One continuous Fourier summand in `L²(Ω; C(𝕋⁴))`. -/
def mollifiedNoiseContinuousTermLp
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    Lp C(T4, ℂ) 2 (volume : Measure M.Ω) :=
  (memLp_mollifiedNoiseContinuousTerm M ρ ε k).toLp
    (mollifiedNoiseContinuousTerm M ρ ε k)

theorem norm_mollifiedNoiseContinuousTermLp_le
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    ‖mollifiedNoiseContinuousTermLp M ρ ε k‖ ≤
      ‖NoiseModel.whiteNoiseFourierScale‖ *
        ‖ρ.symbol ε k‖ := by
  let hterm :=
    memLp_mollifiedNoiseContinuousTerm M ρ ε k
  let hg : MemLp (M.g k) 2 (volume : Measure M.Ω) :=
    M.memLp_g k 2 (by norm_num)
  have hbound :
      ‖mollifiedNoiseContinuousTermLp M ρ ε k‖ ≤
        (‖NoiseModel.whiteNoiseFourierScale‖ *
          ‖ρ.symbol ε k‖) * ‖noiseCoeffLp M k‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hterm.coeFn_toLp, hg.coeFn_toLp] with ω hωterm hωg
    rw [mollifiedNoiseContinuousTermLp, hωterm,
      noiseCoeffLp, hωg, norm_mollifiedNoiseContinuousTerm,
      NoiseModel.mollifiedRandomCoeff, norm_mul]
    ring_nf
    exact le_rfl
  simpa [norm_noiseCoeffLp M k] using hbound

/-- The continuous Fourier series is summable in `L²(Ω)`, with the
deterministic sum of cutoff symbols as a norm majorant. -/
theorem summable_mollifiedNoiseContinuousTermLp
    (M : NoiseModel) (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) :
    Summable fun k : Z4 =>
      mollifiedNoiseContinuousTermLp M ρ ε k := by
  apply Summable.of_norm_bounded
  · exact
      (ρ.summable_norm_symbol hε).mul_left
        ‖NoiseModel.whiteNoiseFourierScale‖
  · exact norm_mollifiedNoiseContinuousTermLp_le M ρ ε

/-- The mollified continuous field as an `L²(Ω; C(𝕋⁴))` random
variable. -/
def xiEpsContinuousMapLp
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) :
    Lp C(T4, ℂ) 2 (volume : Measure M.Ω) :=
  ∑' k : Z4, mollifiedNoiseContinuousTermLp M ρ ε k

theorem ae_xiEpsContinuousMapLp_eq
    (M : NoiseModel) (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) :
    xiEpsContinuousMapLp M ρ ε =ᵐ[(volume : Measure M.Ω)]
      xiEpsContinuousMap M ρ ε := by
  have hsumLp :=
    summable_mollifiedNoiseContinuousTermLp M ρ hε
  have hb :
      Summable fun k : Z4 =>
        ‖NoiseModel.whiteNoiseFourierScale‖ *
          ‖ρ.symbol ε k‖ :=
    (ρ.summable_norm_symbol hε).mul_left
      ‖NoiseModel.whiteNoiseFourierScale‖
  have hnormLp :
      Summable fun k : Z4 =>
        ‖mollifiedNoiseContinuousTermLp M ρ ε k‖ :=
    hb.of_nonneg_of_le
      (fun k => norm_nonneg _)
      (norm_mollifiedNoiseContinuousTermLp_le M ρ ε)
  have henorm :
      ∑' k : Z4,
          ‖mollifiedNoiseContinuousTermLp M ρ ε k‖ₑ ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hnormLp
  have hcoe :
      ∀ᵐ ω ∂(volume : Measure M.Ω), ∀ k : Z4,
        mollifiedNoiseContinuousTermLp M ρ ε k ω =
          mollifiedNoiseContinuousTerm M ρ ε k ω := by
    rw [ae_all_iff]
    intro k
    exact
      (memLp_mollifiedNoiseContinuousTerm M ρ ε k).coeFn_toLp
  filter_upwards
    [MeasureTheory.Lp.hasSum_coeFn_tsum henorm, hcoe,
      M.ae_summable_norm_mollifiedRandomCoeff ρ hε] with
      ω hLpω hcoeω hsummableω
  have hcontinuous :
      HasSum
        (fun k : Z4 => mollifiedNoiseContinuousTerm M ρ ε k ω)
        (xiEpsContinuousMap M ρ ε ω) :=
    (summable_mollifiedNoiseContinuousTerm_of_summable
      M ρ ε ω hsummableω).hasSum
  have hLpω' :
      HasSum
        (fun k : Z4 => mollifiedNoiseContinuousTerm M ρ ε k ω)
        (xiEpsContinuousMapLp M ρ ε ω) :=
    hLpω.congr_fun fun k => (hcoeω k).symm
  exact hLpω'.unique hcontinuous

theorem norm_xiEpsContinuousMapLp_le
    (M : NoiseModel) (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) :
    ‖xiEpsContinuousMapLp M ρ ε‖ ≤
      ‖NoiseModel.whiteNoiseFourierScale‖ *
        ∑' k : Z4, ‖ρ.symbol ε k‖ := by
  let b : Z4 → ℝ := fun k =>
    ‖NoiseModel.whiteNoiseFourierScale‖ * ‖ρ.symbol ε k‖
  have hb : Summable b :=
    (ρ.summable_norm_symbol hε).mul_left
      ‖NoiseModel.whiteNoiseFourierScale‖
  have hnorm :
      Summable fun k : Z4 =>
        ‖mollifiedNoiseContinuousTermLp M ρ ε k‖ :=
    hb.of_nonneg_of_le
      (fun k => norm_nonneg _)
      (norm_mollifiedNoiseContinuousTermLp_le M ρ ε)
  calc
    ‖xiEpsContinuousMapLp M ρ ε‖ ≤
        ∑' k : Z4,
          ‖mollifiedNoiseContinuousTermLp M ρ ε k‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : Z4, b k :=
      hnorm.tsum_le_tsum
        (norm_mollifiedNoiseContinuousTermLp_le M ρ ε) hb
    _ = ‖NoiseModel.whiteNoiseFourierScale‖ *
        ∑' k : Z4, ‖ρ.symbol ε k‖ := by
      exact tsum_mul_left

/-- The measurable continuous-map totalization belongs to `L²(Ω)`. -/
theorem memLp_xiEpsContinuousMap
    (M : NoiseModel) (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) :
    MemLp (xiEpsContinuousMap M ρ ε) 2
      (volume : Measure M.Ω) :=
  (Lp.memLp (xiEpsContinuousMapLp M ρ ε)).ae_eq
    (ae_xiEpsContinuousMapLp_eq M ρ hε)

/-- The squared `L²` norm of a strongly measurable representative is
its second moment.  This small adapter avoids repeatedly unfolding the
real-valued `lpNorm`. -/
theorem norm_sq_toLp_two_eq_integral_norm_sq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [Lp.norm_toLp, toReal_eLpNorm hf.aestronglyMeasurable]
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num)
    (by simp) hf.aestronglyMeasurable]
  norm_num
  simpa [one_div] using
    (Real.rpow_inv_natCast_pow
      (x := ∫ x, ‖f x‖ ^ 2 ∂μ)
      (integral_nonneg fun _ => sq_nonneg _)
      (by norm_num : (2 : ℕ) ≠ 0))

theorem xiEpsContinuousMapLp_eq_toLp
    (M : NoiseModel) (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) :
    xiEpsContinuousMapLp M ρ ε =
      (memLp_xiEpsContinuousMap M ρ hε).toLp
        (xiEpsContinuousMap M ρ ε) := by
  apply Lp.ext
  filter_upwards
    [ae_xiEpsContinuousMapLp_eq M ρ hε,
      (memLp_xiEpsContinuousMap M ρ hε).coeFn_toLp] with
      ω hsum htoLp
  exact hsum.trans htoLp.symm

/-- Exact identification of the continuous field's second moment with
the squared norm of its canonical `L²` sum. -/
theorem integral_norm_sq_xiEpsContinuousMap
    (M : NoiseModel) (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ ω, ‖xiEpsContinuousMap M ρ ε ω‖ ^ 2
      ∂(volume : Measure M.Ω)) =
      ‖xiEpsContinuousMapLp M ρ ε‖ ^ 2 := by
  rw [xiEpsContinuousMapLp_eq_toLp M ρ hε]
  exact
    (norm_sq_toLp_two_eq_integral_norm_sq
      (memLp_xiEpsContinuousMap M ρ hε)).symm

theorem integrable_norm_sq_xiEpsContinuousMap
    (M : NoiseModel) (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun ω => ‖xiEpsContinuousMap M ρ ε ω‖ ^ 2)
      (volume : Measure M.Ω) :=
  (memLp_two_iff_integrable_sq_norm
    (memLp_xiEpsContinuousMap M ρ hε).aestronglyMeasurable).1
      (memLp_xiEpsContinuousMap M ρ hε)

/-- A fully explicit (though deliberately crude) second-moment bound
obtained from absolute Fourier summability.  The sharper powers of
`ε` used by the paper require the kernel estimates of P-err. -/
theorem integral_norm_sq_xiEpsContinuousMap_le
    (M : NoiseModel) (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ ω, ‖xiEpsContinuousMap M ρ ε ω‖ ^ 2
      ∂(volume : Measure M.Ω)) ≤
      (‖NoiseModel.whiteNoiseFourierScale‖ *
        ∑' k : Z4, ‖ρ.symbol ε k‖) ^ 2 := by
  rw [integral_norm_sq_xiEpsContinuousMap M ρ hε]
  exact pow_le_pow_left₀
    (norm_nonneg (xiEpsContinuousMapLp M ρ ε))
    (norm_xiEpsContinuousMapLp_le M ρ hε) 2

/-! ## Agreement with the samplewise realization -/

/-- At positive mollification scale, the measurable multiplication
operator agrees almost surely with the original samplewise
totalization from `L2Realization`. -/
theorem ae_measurableMollifiedPotentialL2Op_eq
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    measurableMollifiedPotentialL2Op M ρ lam ε =ᵐ[
      (volume : Measure M.Ω)]
      mollifiedPotentialL2Op M ρ lam ε := by
  filter_upwards
    [M.ae_summable_norm_mollifiedRandomCoeff ρ hε,
      M.ae_continuous_xiEps ρ hε] with ω hsummable hcontinuous
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards
    [measurableMollifiedPotentialL2Op_apply_ae_of_summable
      M ρ lam ε ω hsummable f,
      mollifiedPotentialL2Op_apply_ae_of_continuous
        M ρ lam ε ω hcontinuous f] with x hmeasurable hsamplewise
  exact hmeasurable.trans hsamplewise.symm

/-- Consequently the measurable and samplewise realizations of
`Kε = G Mε` agree almost surely. -/
theorem ae_measurableAndersonK_eq_andersonK
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    measurableAndersonK M ρ lam ε =ᵐ[(volume : Measure M.Ω)]
      andersonK M ρ lam ε := by
  filter_upwards
    [ae_measurableMollifiedPotentialL2Op_eq M ρ lam hε] with
      ω hω
  simp only [measurableAndersonK, andersonK, hω]

theorem ae_norm_sq_measurableAndersonK_eq_andersonK
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    (fun ω => ‖measurableAndersonK M ρ lam ε ω‖ ^ 2) =ᵐ[
      (volume : Measure M.Ω)]
      fun ω => ‖andersonK M ρ lam ε ω‖ ^ 2 :=
  (ae_measurableAndersonK_eq_andersonK M ρ lam hε).fun_comp
    fun A => ‖A‖ ^ 2

/-! ## Second moment of the random operator -/

theorem measurableAndersonK_norm_le_potential
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) :
    ‖measurableAndersonK M ρ lam ε ω‖ ≤
      ‖measurableMollifiedPotential M ρ lam ε ω‖ := by
  calc
    ‖measurableAndersonK M ρ lam ε ω‖ ≤
        ‖greenL2Op‖ *
          ‖measurableMollifiedPotentialL2Op M ρ lam ε ω‖ :=
      norm_mul_le _ _
    _ ≤ 1 * ‖measurableMollifiedPotentialL2Op M ρ lam ε ω‖ :=
      mul_le_mul_of_nonneg_right norm_greenL2Op_le_one
        (norm_nonneg _)
    _ ≤ ‖measurableMollifiedPotential M ρ lam ε ω‖ := by
      rw [one_mul]
      change ‖continuousMultiplicationCLM
        (measurableMollifiedPotential M ρ lam ε ω)‖ ≤ _
      rw [continuousMultiplicationCLM_apply]
      exact continuousMultiplicationOp_norm_le
        (measurableMollifiedPotential M ρ lam ε ω)

theorem norm_measurableMollifiedPotential_le
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) :
    ‖measurableMollifiedPotential M ρ lam ε ω‖ ≤
      ‖(lamEps lam ε : ℂ)‖ *
          ‖xiEpsContinuousMap M ρ ε ω‖ +
        ‖(renormCEps ρ lam ε : ℂ)‖ := by
  unfold measurableMollifiedPotential
  calc
    ‖(lamEps lam ε : ℂ) • xiEpsContinuousMap M ρ ε ω -
        ContinuousMap.const T4 (renormCEps ρ lam ε : ℂ)‖ ≤
        ‖(lamEps lam ε : ℂ) • xiEpsContinuousMap M ρ ε ω‖ +
          ‖ContinuousMap.const T4 (renormCEps ρ lam ε : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ ‖(lamEps lam ε : ℂ)‖ *
          ‖xiEpsContinuousMap M ρ ε ω‖ +
        ‖(renormCEps ρ lam ε : ℂ)‖ := by
      rw [norm_smul]
      gcongr
      exact
        ((ContinuousMap.const T4
          (renormCEps ρ lam ε : ℂ)).norm_le
            (norm_nonneg (renormCEps ρ lam ε : ℂ))).2
          fun _ => le_rfl

/-- Pointwise quadratic domination used for both integrability and
the Markov bound. -/
theorem norm_sq_measurableAndersonK_le
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) :
    ‖measurableAndersonK M ρ lam ε ω‖ ^ 2 ≤
      2 * ‖(lamEps lam ε : ℂ)‖ ^ 2 *
          ‖xiEpsContinuousMap M ρ ε ω‖ ^ 2 +
        2 * ‖(renormCEps ρ lam ε : ℂ)‖ ^ 2 := by
  have hK :=
    (measurableAndersonK_norm_le_potential M ρ lam ε ω).trans
      (norm_measurableMollifiedPotential_le M ρ lam ε ω)
  have hKnonneg := norm_nonneg (measurableAndersonK M ρ lam ε ω)
  have hξnonneg := norm_nonneg (xiEpsContinuousMap M ρ ε ω)
  have hlamnonneg := norm_nonneg (lamEps lam ε : ℂ)
  have hcnonneg := norm_nonneg (renormCEps ρ lam ε : ℂ)
  nlinarith [sq_nonneg
    (‖(lamEps lam ε : ℂ)‖ *
      ‖xiEpsContinuousMap M ρ ε ω‖ -
      ‖(renormCEps ρ lam ε : ℂ)‖)]

theorem memLp_measurableMollifiedPotential
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    MemLp (measurableMollifiedPotential M ρ lam ε) 2
      (volume : Measure M.Ω) := by
  unfold measurableMollifiedPotential
  exact
    ((memLp_xiEpsContinuousMap M ρ hε).const_smul
      (lamEps lam ε : ℂ)).sub
        (memLp_const
          (ContinuousMap.const T4 (renormCEps ρ lam ε : ℂ)))

theorem integrable_norm_sq_measurableAndersonK
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    Integrable
      (fun ω => ‖measurableAndersonK M ρ lam ε ω‖ ^ 2)
      (volume : Measure M.Ω) := by
  let a : ℝ := ‖(lamEps lam ε : ℂ)‖
  let c : ℝ := ‖(renormCEps ρ lam ε : ℂ)‖
  have hmajorant :
      Integrable
        (fun ω =>
          2 * a ^ 2 * ‖xiEpsContinuousMap M ρ ε ω‖ ^ 2 +
            2 * c ^ 2)
        (volume : Measure M.Ω) := by
    exact
      ((integrable_norm_sq_xiEpsContinuousMap M ρ hε).const_mul
        (2 * a ^ 2)).add (integrable_const (2 * c ^ 2))
  apply hmajorant.mono'
    (measurable_norm_sq_measurableAndersonK M ρ lam ε).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact norm_sq_measurableAndersonK_le M ρ lam ε ω

theorem integrable_norm_sq_andersonK
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun ω => ‖andersonK M ρ lam ε ω‖ ^ 2)
      (volume : Measure M.Ω) :=
  (integrable_norm_sq_measurableAndersonK M ρ lam hε).congr
    (ae_norm_sq_measurableAndersonK_eq_andersonK
      M ρ lam hε)

theorem integral_norm_sq_measurableAndersonK_le
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ ω, ‖measurableAndersonK M ρ lam ε ω‖ ^ 2
      ∂(volume : Measure M.Ω)) ≤
      2 * ‖(lamEps lam ε : ℂ)‖ ^ 2 *
          (‖NoiseModel.whiteNoiseFourierScale‖ *
            ∑' k : Z4, ‖ρ.symbol ε k‖) ^ 2 +
        2 * ‖(renormCEps ρ lam ε : ℂ)‖ ^ 2 := by
  let a : ℝ := ‖(lamEps lam ε : ℂ)‖
  let c : ℝ := ‖(renormCEps ρ lam ε : ℂ)‖
  let B : ℝ :=
    ‖NoiseModel.whiteNoiseFourierScale‖ *
      ∑' k : Z4, ‖ρ.symbol ε k‖
  have hxi :=
    integrable_norm_sq_xiEpsContinuousMap M ρ hε
  have hmajorant :
      Integrable
        (fun ω =>
          2 * a ^ 2 * ‖xiEpsContinuousMap M ρ ε ω‖ ^ 2 +
            2 * c ^ 2)
        (volume : Measure M.Ω) :=
    (hxi.const_mul (2 * a ^ 2)).add
      (integrable_const (2 * c ^ 2))
  calc
    (∫ ω, ‖measurableAndersonK M ρ lam ε ω‖ ^ 2
        ∂(volume : Measure M.Ω)) ≤
        ∫ ω,
          (2 * a ^ 2 * ‖xiEpsContinuousMap M ρ ε ω‖ ^ 2 +
            2 * c ^ 2)
          ∂(volume : Measure M.Ω) := by
      apply integral_mono_ae
        (integrable_norm_sq_measurableAndersonK M ρ lam hε)
        hmajorant
      filter_upwards with ω
      exact norm_sq_measurableAndersonK_le M ρ lam ε ω
    _ = 2 * a ^ 2 *
          (∫ ω, ‖xiEpsContinuousMap M ρ ε ω‖ ^ 2
            ∂(volume : Measure M.Ω)) +
        2 * c ^ 2 := by
      rw [integral_add (hxi.const_mul (2 * a ^ 2))
        (integrable_const (2 * c ^ 2)),
        integral_const_mul, integral_const]
      simp
    _ ≤ 2 * a ^ 2 * B ^ 2 + 2 * c ^ 2 := by
      gcongr
      exact integral_norm_sq_xiEpsContinuousMap_le M ρ hε

/-- The requested quantitative second moment for the original
samplewise operator.  All measurability work is discharged by its
a.s. agreement with the canonical measurable realization. -/
theorem integral_norm_sq_andersonK_le
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ ω, ‖andersonK M ρ lam ε ω‖ ^ 2
      ∂(volume : Measure M.Ω)) ≤
      2 * ‖(lamEps lam ε : ℂ)‖ ^ 2 *
          (‖NoiseModel.whiteNoiseFourierScale‖ *
            ∑' k : Z4, ‖ρ.symbol ε k‖) ^ 2 +
        2 * ‖(renormCEps ρ lam ε : ℂ)‖ ^ 2 := by
  calc
    (∫ ω, ‖andersonK M ρ lam ε ω‖ ^ 2
        ∂(volume : Measure M.Ω)) =
        ∫ ω, ‖measurableAndersonK M ρ lam ε ω‖ ^ 2
          ∂(volume : Measure M.Ω) :=
      integral_congr_ae
        (ae_norm_sq_measurableAndersonK_eq_andersonK
          M ρ lam hε).symm
    _ ≤ _ := integral_norm_sq_measurableAndersonK_le M ρ lam hε

/-- Markov's inequality with all analytic premises instantiated.  This
controls the abstract norm-small event, but is not the paper's
parametrix good event: the displayed crude bound need not vanish with
`ε`. -/
theorem measureReal_compl_andersonResolventGoodEvent_explicit_le
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    (volume : Measure M.Ω).real
        (andersonResolventGoodEvent M ρ lam ε)ᶜ ≤
      4 *
        (2 * ‖(lamEps lam ε : ℂ)‖ ^ 2 *
            (‖NoiseModel.whiteNoiseFourierScale‖ *
              ∑' k : Z4, ‖ρ.symbol ε k‖) ^ 2 +
          2 * ‖(renormCEps ρ lam ε : ℂ)‖ ^ 2) := by
  exact measureReal_compl_andersonResolventGoodEvent_le
    M ρ lam ε
    (2 * ‖(lamEps lam ε : ℂ)‖ ^ 2 *
        (‖NoiseModel.whiteNoiseFourierScale‖ *
          ∑' k : Z4, ‖ρ.symbol ε k‖) ^ 2 +
      2 * ‖(renormCEps ρ lam ε : ℂ)‖ ^ 2)
    (integrable_norm_sq_andersonK M ρ lam hε)
    (integral_norm_sq_andersonK_le M ρ lam hε)

end

end Anderson4D
