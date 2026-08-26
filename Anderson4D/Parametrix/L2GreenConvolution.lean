import Anderson4D.Parametrix.L2Realization
import Anderson4D.Continuum.SingularConv
import Mathlib.Analysis.Convolution

/-!
# Physical Green convolution and the Fourier-multiplier realization

The bounded Green operator on `TorusL2` was defined spectrally.  This
file proves that on continuous inputs it agrees with convolution by
the paper's heat-kernel Green function against `paperMeasure`.  This
is the analytic adapter needed to iterate physical parametrix kernels.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ComplexConjugate
open scoped InnerProductSpace Convolution

local instance instPaperMeasureIsAddLeftInvariant :
    paperMeasure.IsAddLeftInvariant := by
  rw [paperMeasure_eq_volume]
  infer_instance

local instance instPaperMeasureIsAddRightInvariant :
    paperMeasure.IsAddRightInvariant := by
  rw [paperMeasure_eq_volume]
  infer_instance

local instance instPaperMeasureIsNegInvariant :
    paperMeasure.IsNegInvariant := by
  constructor
  unfold Measure.neg
  rw [paperMeasure_eq_volume]
  have hpi :
      MeasurePreserving
        (fun x : T4 => fun i => -(x i))
        (volume : Measure T4) (volume : Measure T4) :=
    measurePreserving_pi
      (fun _ : Fin dim =>
        (volume : Measure (AddCircle (2 * Real.pi))))
      (fun _ : Fin dim =>
        (volume : Measure (AddCircle (2 * Real.pi))))
      (f := fun _ x => -x) fun _ =>
        Measure.measurePreserving_neg _
  have hfun :
      (Neg.neg : T4 → T4) =
        fun x : T4 => fun i => -(x i) := rfl
  rw [hfun]
  exact hpi.map_eq

private theorem fourier_arg_add_greenConvolution
    (n : ℤ) (x y : AddCircle (2 * Real.pi)) :
    fourier n (x + y) = fourier n x * fourier n y := by
  change
    (AddCircle.toCircle (n • (x + y)) : ℂ) =
      (AddCircle.toCircle (n • x) : ℂ) *
        (AddCircle.toCircle (n • y) : ℂ)
  rw [zsmul_add, AddCircle.toCircle_add]
  exact Circle.coe_mul _ _

/-- Spatial addition law for a fixed torus character. -/
theorem charT4_add_apply (k : Z4) (x y : T4) :
    charT4 k (x + y) =
      charT4 k x * charT4 k y := by
  unfold charT4
  simp_rw [Pi.add_apply, fourier_arg_add_greenConvolution,
    Finset.prod_mul_distrib]

private theorem integrable_greenFn_complex :
    Integrable (fun z : T4 => (greenFn z : ℂ)) paperMeasure :=
  integrable_greenFn_paper.ofReal

/-- Convolution by the physical Green kernel on a continuous input.
The integral uses the paper's unnormalized torus measure. -/
def greenPhysicalConvolution (f : C(T4, ℂ)) : C(T4, ℂ) where
  toFun :=
    (fun z : T4 => (greenFn z : ℂ)) ⋆[
      ContinuousLinearMap.mul ℂ ℂ, paperMeasure] f
  continuous_toFun := by
    exact
      HasCompactSupport.continuous_convolution_right
        (ContinuousLinearMap.mul ℂ ℂ)
        (HasCompactSupport.of_compactSpace (f : T4 → ℂ))
        integrable_greenFn_complex.locallyIntegrable
        f.continuous

/-- Symmetric integral form of physical Green convolution. -/
theorem greenPhysicalConvolution_apply
    (f : C(T4, ℂ)) (x : T4) :
    greenPhysicalConvolution f x =
      ∫ y : T4,
        (greenFn (x - y) : ℂ) * f y ∂paperMeasure := by
  exact convolution_mul_swap

private theorem integrable_char_mul_greenFn (k : Z4) :
    Integrable
      (fun z : T4 => charT4 k z * (greenFn z : ℂ))
      paperMeasure :=
  integrable_greenFn_complex.bdd_mul
    (continuous_charT4 k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      rw [norm_charT4])

private theorem integrable_char_mul_continuous
    (f : C(T4, ℂ)) (k : Z4) :
    Integrable (fun z : T4 => charT4 k z * f z)
      paperMeasure := by
  have hf : Integrable (f : T4 → ℂ) paperMeasure :=
    f.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact hf.bdd_mul
    (continuous_charT4 k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      rw [norm_charT4])

/-- Fourier transform turns physical Green convolution into
multiplication.  This version keeps the paper's positive-frequency,
unnormalized convention. -/
theorem paperFourierCoeff_greenPhysicalConvolution
    (f : C(T4, ℂ)) (k : Z4) :
    paperFourierCoeff (greenPhysicalConvolution f) k =
      paperFourierCoeff (fun z : T4 => (greenFn z : ℂ)) k *
        paperFourierCoeff f k := by
  let greenTwist : T4 → ℂ :=
    fun z => charT4 k z * (greenFn z : ℂ)
  let fTwist : T4 → ℂ :=
    fun z => charT4 k z * f z
  have hpoint : ∀ x : T4,
      charT4 k x * greenPhysicalConvolution f x =
        (greenTwist ⋆[
          ContinuousLinearMap.mul ℂ ℂ, paperMeasure] fTwist) x := by
    intro x
    change
      charT4 k x *
          (((fun z : T4 => (greenFn z : ℂ)) ⋆[
            ContinuousLinearMap.mul ℂ ℂ, paperMeasure] f) x) =
        (greenTwist ⋆[
          ContinuousLinearMap.mul ℂ ℂ, paperMeasure] fTwist) x
    rw [convolution_def, convolution_def, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    change
      charT4 k x *
          ((greenFn y : ℂ) * f (x - y)) =
        (charT4 k y * (greenFn y : ℂ)) *
          (charT4 k (x - y) * f (x - y))
    have hchar :
        charT4 k x =
          charT4 k y * charT4 k (x - y) := by
      rw [← charT4_add_apply]
      congr 1
      abel
    rw [hchar]
    ring
  unfold paperFourierCoeff
  rw [integral_congr_ae
    (Filter.Eventually.of_forall hpoint)]
  simpa [greenTwist, fTwist] using
    integral_convolution
      (ContinuousLinearMap.mul ℂ ℂ)
      (integrable_char_mul_greenFn k)
      (integrable_char_mul_continuous f k)

theorem paperFourierCoeff_greenFn_complex_eq_greenL2Symbol
    (k : Z4) :
    paperFourierCoeff (fun z : T4 => (greenFn z : ℂ)) k =
      greenL2Symbol k := by
  unfold paperFourierCoeff
  simpa [mul_comm] using
    paperFourierCoeff_greenFn_eq_greenL2Symbol k

/-- Probability-Haar Fourier coefficient of physical Green
convolution.  The two measure normalizations cancel exactly. -/
theorem torusFourierCoeff_greenPhysicalConvolution
    (f : C(T4, ℂ)) (k : Z4) :
    torusFourierCoeff (greenPhysicalConvolution f) k =
      greenL2Symbol k * torusFourierCoeff f k := by
  have h :=
    paperFourierCoeff_greenPhysicalConvolution f (-k)
  rw [paperFourierCoeff_eq_volume_mul_torusFourierCoeff_neg,
    paperFourierCoeff_greenFn_complex_eq_greenL2Symbol,
    paperFourierCoeff_eq_volume_mul_torusFourierCoeff_neg,
    neg_neg] at h
  simp only [show greenL2Symbol (-k) = greenL2Symbol k by
    simp [greenL2Symbol]] at h
  have hvolume :
      ((((2 * Real.pi) ^ dim : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast
      (ne_of_gt (by positivity :
        0 < (2 * Real.pi) ^ dim))
  exact mul_left_cancel₀ hvolume (by
    calc
      ((((2 * Real.pi) ^ dim : ℝ) : ℂ)) *
          torusFourierCoeff (greenPhysicalConvolution f) k =
          greenL2Symbol k *
            (((((2 * Real.pi) ^ dim : ℝ) : ℂ)) *
              torusFourierCoeff f k) := h
      _ = ((((2 * Real.pi) ^ dim : ℝ) : ℂ)) *
          (greenL2Symbol k * torusFourierCoeff f k) := by ring)

private theorem torusFourierCoeff_continuousMap_toLp
    (f : C(T4, ℂ)) (k : Z4) :
    torusFourierCoeff
        (ContinuousMap.toLp (E := ℂ) 2 haarT4 ℂ f) k =
      torusFourierCoeff f k := by
  unfold torusFourierCoeff
  apply integral_congr_ae
  filter_upwards
    [ContinuousMap.coeFn_toLp
      (p := 2) (μ := haarT4) (𝕜 := ℂ) f] with x hx
  rw [hx]

/-- The spectral bounded operator and the physical Green convolution
agree on every continuous input. -/
theorem greenL2Op_continuousMap
    (f : C(T4, ℂ)) :
    greenL2Op
        (ContinuousMap.toLp (E := ℂ) 2 haarT4 ℂ f) =
      ContinuousMap.toLp (E := ℂ) 2 haarT4 ℂ
        (greenPhysicalConvolution f) := by
  apply torusFourierCoeff_l2_ext
  intro k
  rw [torusFourierCoeff_greenL2Op]
  rw [torusFourierCoeff_continuousMap_toLp f k]
  rw [torusFourierCoeff_continuousMap_toLp
    (greenPhysicalConvolution f) k]
  rw [torusFourierCoeff_greenPhysicalConvolution]

/-- Almost-everywhere pointwise form of the preceding operator
identity. -/
theorem greenL2Op_continuousMap_action
    (f : C(T4, ℂ)) :
    greenL2Op
        (ContinuousMap.toLp (E := ℂ) 2 haarT4 ℂ f) =ᵐ[haarT4]
      fun x =>
        ∫ y : T4,
          (greenFn (x - y) : ℂ) * f y
          ∂paperMeasure := by
  rw [greenL2Op_continuousMap]
  filter_upwards
    [ContinuousMap.coeFn_toLp
      (p := 2) (μ := haarT4) (𝕜 := ℂ)
      (greenPhysicalConvolution f)] with x hx
  rw [hx, greenPhysicalConvolution_apply]

end

end Anderson4D
