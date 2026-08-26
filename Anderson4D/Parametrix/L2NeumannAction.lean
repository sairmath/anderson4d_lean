import Anderson4D.Parametrix.L2KernelBridge

/-!
# Recursive physical realization of the `L²` Neumann powers

This file iterates the Green-convolution theorem.  For a continuous
multiplier `m`, it packages the alternating sequence

`G eβ`, `G(m G eβ)`, `G(m G(m G eβ))`, ...

as continuous functions and proves that their `L²` classes are exactly
`(G M_m)^n G eβ`.  For samples on which the mollified Fourier series is
absolutely summable, the multiplier is pointwise the paper's
`multFun`, and the measurable and samplewise operator realizations
coincide.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

local instance instPaperMeasureIsAddRightInvariantNeumannAction :
    paperMeasure.IsAddRightInvariant := by
  rw [paperMeasure_eq_volume]
  infer_instance

/-- Multiplication of two continuous functions commutes with passage
to `L²`. -/
theorem continuousMultiplicationOp_toLp
    (m f : C(T4, ℂ)) :
    continuousMultiplicationOp m
        (ContinuousMap.toLp (E := ℂ) 2 haarT4 ℂ f) =
      ContinuousMap.toLp (E := ℂ) 2 haarT4 ℂ (m * f) := by
  apply Lp.ext
  filter_upwards
    [continuousMultiplicationOp_apply_ae m
      (ContinuousMap.toLp (E := ℂ) 2 haarT4 ℂ f),
      ContinuousMap.coeFn_toLp
        (p := 2) (μ := haarT4) (𝕜 := ℂ) f,
      ContinuousMap.coeFn_toLp
        (p := 2) (μ := haarT4) (𝕜 := ℂ) (m * f)] with
      x hmul hf hprod
  rw [hmul, hf, hprod]
  rfl

/-- Recursive continuous representative of the physical Neumann
action with multiplier `m`. -/
def continuousNeumannAction
    (m : C(T4, ℂ)) (β : Z4) : ℕ → C(T4, ℂ)
  | 0 => greenPhysicalConvolution (charT4Continuous β)
  | n + 1 =>
      greenPhysicalConvolution
        (m * continuousNeumannAction m β n)

@[simp] theorem continuousNeumannAction_zero
    (m : C(T4, ℂ)) (β : Z4) :
    continuousNeumannAction m β 0 =
      greenPhysicalConvolution (charT4Continuous β) :=
  rfl

@[simp] theorem continuousNeumannAction_succ
    (m : C(T4, ℂ)) (β : Z4) (n : ℕ) :
    continuousNeumannAction m β (n + 1) =
      greenPhysicalConvolution
        (m * continuousNeumannAction m β n) :=
  rfl

theorem continuousNeumannAction_zero_apply
    (m : C(T4, ℂ)) (β : Z4) (x : T4) :
    continuousNeumannAction m β 0 x =
      ∫ y : T4,
        (greenFn (x - y) : ℂ) * charT4 β y
        ∂paperMeasure := by
  rw [continuousNeumannAction_zero,
    greenPhysicalConvolution_apply]
  rfl

theorem continuousNeumannAction_succ_apply
    (m : C(T4, ℂ)) (β : Z4) (n : ℕ) (x : T4) :
    continuousNeumannAction m β (n + 1) x =
      ∫ y : T4,
        (greenFn (x - y) : ℂ) *
          (m y * continuousNeumannAction m β n y)
        ∂paperMeasure := by
  rw [continuousNeumannAction_succ,
    greenPhysicalConvolution_apply]
  rfl

/-- Exact operator realization of every recursive physical Neumann
action. -/
theorem pow_green_mul_continuousMultiplication_apply_char
    (m : C(T4, ℂ)) (β : Z4) (n : ℕ) :
    ((Kop greenL2Op (continuousMultiplicationOp m)) ^ n *
        greenL2Op) (charT4Lp 2 β) =
      ContinuousMap.toLp (E := ℂ) 2 haarT4 ℂ
        (continuousNeumannAction m β n) := by
  induction n with
  | zero =>
      simpa [continuousNeumannAction] using
        greenL2Op_continuousMap (charT4Continuous β)
  | succ n ih =>
      have ihApply :
          ((Kop greenL2Op (continuousMultiplicationOp m)) ^ n)
              (greenL2Op (charT4Lp 2 β)) =
            ContinuousMap.toLp (E := ℂ) 2 haarT4 ℂ
              (continuousNeumannAction m β n) := by
        simpa only [mul_apply_eq_comp] using ih
      unfold Kop at ihApply
      rw [pow_succ']
      simp only [mul_assoc, mul_apply_eq_comp, Kop]
      rw [ihApply]
      rw [continuousMultiplicationOp_toLp]
      exact greenL2Op_continuousMap
        (m * continuousNeumannAction m β n)

/-- The continuous totalization of the random potential gives the
same formula for the preferred measurable random operator. -/
theorem pow_measurableAndersonK_apply_char
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) (β : Z4) (n : ℕ) :
    ((measurableAndersonK M ρ lam ε ω) ^ n *
        greenL2Op) (charT4Lp 2 β) =
      ContinuousMap.toLp (E := ℂ) 2 haarT4 ℂ
        (continuousNeumannAction
          (measurableMollifiedPotential M ρ lam ε ω) β n) := by
  exact pow_green_mul_continuousMultiplication_apply_char
    (measurableMollifiedPotential M ρ lam ε ω) β n

/-- Absolute Fourier summability forces the original real field
totalization to be continuous. -/
theorem continuous_xiEps_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖) :
    Continuous (M.xiEps ρ ε ω) := by
  have heq :
      M.xiEps ρ ε ω =
        fun x => (xiEpsContinuousMap M ρ ε ω x).re := by
    funext x
    exact
      (xiEpsContinuousMap_re_eq_xiEps_of_summable
        M ρ ε ω hω x).symm
  rw [heq]
  exact
    Complex.continuous_re.comp
      (xiEpsContinuousMap M ρ ε ω).continuous

/-- On an absolutely summable sample, the measurable continuous-map
multiplier equals the original samplewise multiplication operator. -/
theorem measurableMollifiedPotentialL2Op_eq_mollifiedPotentialL2Op
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖) :
    measurableMollifiedPotentialL2Op M ρ lam ε ω =
      mollifiedPotentialL2Op M ρ lam ε ω := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards
    [measurableMollifiedPotentialL2Op_apply_ae_of_summable
      M ρ lam ε ω hω f,
      mollifiedPotentialL2Op_apply_ae_of_continuous
        M ρ lam ε ω
          (continuous_xiEps_of_summable M ρ ε ω hω) f] with
      x hmeasurable hsamplewise
  exact hmeasurable.trans hsamplewise.symm

theorem continuousNeumannAction_succ_apply_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖)
    (β : Z4) (n : ℕ) (x : T4) :
    continuousNeumannAction
        (measurableMollifiedPotential M ρ lam ε ω)
        β (n + 1) x =
      ∫ y : T4,
        (greenFn (x - y) : ℂ) *
          ((multFun M ρ lam ε y ω : ℝ) *
            continuousNeumannAction
              (measurableMollifiedPotential M ρ lam ε ω)
              β n y)
        ∂paperMeasure := by
  rw [continuousNeumannAction_succ_apply]
  apply integral_congr_ae
  filter_upwards with y
  rw [measurableMollifiedPotential_apply_eq_multFun_of_summable
    M ρ lam ε ω hω y]

theorem measurableAndersonK_eq_andersonK_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖) :
    measurableAndersonK M ρ lam ε ω =
      andersonK M ρ lam ε ω := by
  unfold measurableAndersonK andersonK
  rw [measurableMollifiedPotentialL2Op_eq_mollifiedPotentialL2Op
    M ρ lam ε ω hω]

/-- Every samplewise operator power has the explicit recursive
physical-convolution representative on the full-measure Fourier
summability event. -/
theorem pow_andersonK_apply_char_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖)
    (β : Z4) (n : ℕ) :
    ((andersonK M ρ lam ε ω) ^ n *
        greenL2Op) (charT4Lp 2 β) =
      ContinuousMap.toLp (E := ℂ) 2 haarT4 ℂ
        (continuousNeumannAction
          (measurableMollifiedPotential M ρ lam ε ω) β n) := by
  rw [← measurableAndersonK_eq_andersonK_of_summable
    M ρ lam ε ω hω]
  exact pow_measurableAndersonK_apply_char
    M ρ lam ε ω β n

/-- Almost-everywhere pointwise form of the recursive action. -/
theorem pow_andersonK_apply_char_ae_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖)
    (β : Z4) (n : ℕ) :
    ((andersonK M ρ lam ε ω) ^ n *
        greenL2Op) (charT4Lp 2 β) =ᵐ[haarT4]
      continuousNeumannAction
        (measurableMollifiedPotential M ρ lam ε ω) β n := by
  rw [pow_andersonK_apply_char_of_summable
    M ρ lam ε ω hω β n]
  exact ContinuousMap.coeFn_toLp
    (p := 2) (μ := haarT4) (𝕜 := ℂ)
    (continuousNeumannAction
      (measurableMollifiedPotential M ρ lam ε ω) β n)

/-! ## The first nontrivial flat-chain check -/

private theorem integrable_greenFn_complex_neumannAction :
    Integrable (fun z : T4 => (greenFn z : ℂ)) paperMeasure :=
  integrable_greenFn_paper.ofReal

private theorem integrable_greenFn_sub_complex_neumannAction
    (x : T4) :
    Integrable (fun z : T4 => (greenFn (z - x) : ℂ))
      paperMeasure :=
  ((measurePreserving_sub_paper x).integrable_comp
    integrable_greenFn_complex_neumannAction.aestronglyMeasurable).mpr
      integrable_greenFn_complex_neumannAction

private theorem integrable_greenFn_left_sub_complex_neumannAction
    (x : T4) :
    Integrable (fun z : T4 => (greenFn (x - z) : ℂ))
      paperMeasure := by
  apply
    (integrable_greenFn_sub_complex_neumannAction x).congr
  filter_upwards with z
  congr 1
  simpa only [neg_sub] using
    (greenFn_memE.neg_invariant (z - x)).symm

private theorem integrable_green_mul_continuous
    (m : C(T4, ℂ)) (x : T4) :
    Integrable
      (fun z : T4 => (greenFn (x - z) : ℂ) * m z)
      paperMeasure :=
  (integrable_greenFn_left_sub_complex_neumannAction x).mul_bdd
    m.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z =>
      ContinuousMap.norm_coe_le_norm m z)

private theorem integrable_firstNeumannJoint
    (m : C(T4, ℂ)) (β : Z4) (x : T4) :
    Integrable
      (Function.uncurry fun y z : T4 =>
        ((greenFn (x - z) : ℂ) * m z) *
          (greenFn (y - z) : ℂ) * charT4 β y)
      (paperMeasure.prod paperMeasure) := by
  let f : T4 → ℂ :=
    fun z => (greenFn (x - z) : ℂ) * m z
  let g : T4 → ℂ := fun u => (greenFn u : ℂ)
  have hf : Integrable f paperMeasure :=
    integrable_green_mul_continuous m x
  have hg : Integrable g paperMeasure :=
    integrable_greenFn_complex_neumannAction
  have hjoint :
      Integrable
        (Function.uncurry fun y z : T4 =>
          f z * g (y - z))
        (paperMeasure.prod paperMeasure) :=
    hf.convolution_integrand
      (ContinuousLinearMap.mul ℂ ℂ) hg
  exact hjoint.mul_bdd
    (((continuous_charT4 β).comp
      continuous_fst).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p => by
      rw [norm_charT4])

/-- The first recursive action is the Fubini flattening of its
two-Green chain. -/
theorem continuousNeumannAction_one_eq_flat
    (m : C(T4, ℂ)) (β : Z4) (x : T4) :
    continuousNeumannAction m β 1 x =
      ∫ y : T4,
        (∫ z : T4,
          (greenFn (x - z) : ℂ) * m z *
            (greenFn (z - y) : ℂ)
          ∂paperMeasure) *
        charT4 β y ∂paperMeasure := by
  let H : T4 → T4 → ℂ := fun y z =>
    ((greenFn (x - z) : ℂ) * m z) *
      (greenFn (y - z) : ℂ) * charT4 β y
  have hH :
      Integrable (Function.uncurry H)
        (paperMeasure.prod paperMeasure) :=
    integrable_firstNeumannJoint m β x
  rw [show (1 : ℕ) = 0 + 1 by norm_num,
    continuousNeumannAction_succ_apply]
  simp_rw [continuousNeumannAction_zero_apply]
  calc
    (∫ z : T4,
        (greenFn (x - z) : ℂ) *
          (m z *
            ∫ y : T4,
              (greenFn (z - y) : ℂ) * charT4 β y
              ∂paperMeasure)
        ∂paperMeasure) =
        ∫ z : T4, ∫ y : T4, H y z
          ∂paperMeasure ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with z
      rw [← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      have heven :
          greenFn (z - y) = greenFn (y - z) := by
        have h :=
          greenFn_memE.neg_invariant (y - z)
        rw [neg_sub] at h
        exact h
      rw [heven]
      unfold H
      ring
    _ = ∫ y : T4, ∫ z : T4, H y z
          ∂paperMeasure ∂paperMeasure :=
      (integral_integral_swap hH).symm
    _ = ∫ y : T4,
        (∫ z : T4,
          (greenFn (x - z) : ℂ) * m z *
            (greenFn (z - y) : ℂ)
          ∂paperMeasure) *
        charT4 β y ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with y
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with z
      have heven :
          greenFn (y - z) = greenFn (z - y) := by
        have h :=
          greenFn_memE.neg_invariant (z - y)
        rw [neg_sub] at h
        exact h
      change
        (greenFn (x - z) : ℂ) * m z *
            (greenFn (y - z) : ℂ) * charT4 β y =
          (greenFn (x - z) : ℂ) * m z *
            (greenFn (z - y) : ℂ) * charT4 β y
      rw [heven]

/-- Closed form of the one-internal-vertex flat kernel. -/
theorem neumannTermKernel_one
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (x y : T4) (ω : M.Ω) :
    neumannTermKernel M ρ lam ε 1 x y ω =
      ∫ z : T4,
        ((greenFn (x - z) * multFun M ρ lam ε z ω *
          greenFn (z - y) : ℝ) : ℂ) ∂paperMeasure := by
  unfold neumannTermKernel
  let e : (Fin 1 → T4) ≃ᵐ T4 :=
    MeasurableEquiv.funUnique (Fin 1) T4
  let F : (Fin 1 → T4) → ℂ := fun v =>
    (((∏ j : Fin 2,
        greenFn
          ((assemble x y v) j.castSucc -
            (assemble x y v) j.succ)) *
      ∏ i, multFun M ρ lam ε (v i) ω : ℝ) : ℂ)
  let g : T4 → ℂ := fun z => F (e.symm z)
  have hp :
      MeasurePreserving e
        (Measure.pi fun _ : Fin 1 => paperMeasure)
        paperMeasure :=
    measurePreserving_funUnique paperMeasure (Fin 1)
  calc
    (∫ v : Fin 1 → T4, F v
        ∂(Measure.pi fun _ => paperMeasure)) =
        ∫ z : T4, g z ∂paperMeasure := by
      simpa [g] using hp.integral_comp' g
    _ = ∫ z : T4,
        ((greenFn (x - z) * multFun M ρ lam ε z ω *
          greenFn (z - y) : ℝ) : ℂ) ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with z
      simp [g, F, e, Fin.prod_univ_succ, assemble]
      ring

/-- The physical/operator kernel bridge is unconditional at the first
nontrivial order on every absolutely summable noise sample. -/
theorem neumannTermKernelAction_one_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖)
    (β : Z4) :
    NeumannTermKernelAction M ρ lam ε 1 β ω := by
  unfold NeumannTermKernelAction
  filter_upwards
    [pow_andersonK_apply_char_ae_of_summable
      M ρ lam ε ω hω β 1] with x hx
  rw [hx]
  rw [continuousNeumannAction_one_eq_flat]
  apply integral_congr_ae
  filter_upwards with y
  rw [neumannTermKernel_one]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  rw [measurableMollifiedPotential_apply_eq_multFun_of_summable
    M ρ lam ε ω hω z]
  push_cast
  ring

end

end Anderson4D
