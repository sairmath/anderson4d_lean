import Anderson4D.Continuum.GreenFourier
import Anderson4D.Continuum.TorusFourier
import Anderson4D.Parametrix.GoodEvent
import Anderson4D.Parametrix.Random
import Anderson4D.Probability.NoiseRegularity
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Concrete bounded operators on torus `L²`

This file realizes the abstract bounded-operator layer used in paper
§3.4, Step 1, on `L²(𝕋⁴, haarT4)`.

The Green operator is the Fourier multiplier with symbol
`(1 + |k|²)⁻¹`.  Multiplication by a measurable essentially bounded
function is constructed directly on `L²`, with its pointwise action and
operator-norm bound exposed.  The mollified Anderson potential is then
an instance whenever its almost-sure continuity (hence boundedness on
the compact torus) is supplied.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

/-- The Hilbert space used by the bounded resolvent realization. -/
abbrev TorusL2 := Lp ℂ 2 haarT4

/-! ## The Green Fourier multiplier -/

/-- Fourier symbol of `(1 - Δ)⁻¹` on the four-dimensional torus. -/
def greenL2Symbol (k : Z4) : ℂ :=
  ((1 + ∑ i, (k i : ℝ) ^ 2)⁻¹ : ℝ)

theorem greenL2Symbol_norm_le_one (k : Z4) :
    ‖greenL2Symbol k‖ ≤ 1 := by
  have hk : 0 ≤ ∑ i, (k i : ℝ) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (k i : ℝ)
  have hpos : 0 < 1 + ∑ i, (k i : ℝ) ^ 2 := by linarith
  simp only [greenL2Symbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hpos.le)]
  exact (inv_le_one₀ hpos).2 (by linarith)

/-- The bounded Green operator on torus `L²`, defined by its Fourier
multiplier rather than by an ill-defined pointwise Fourier series. -/
def greenL2Op : TorusL2 →L[ℂ] TorusL2 :=
  torusL2MultiplierCLM greenL2Symbol 1 zero_le_one
    greenL2Symbol_norm_le_one

@[simp] theorem torusFourierCoeff_greenL2Op (f : TorusL2) (k : Z4) :
    torusFourierCoeff (greenL2Op f) k =
      greenL2Symbol k * torusFourierCoeff f k :=
  torusFourierCoeff_l2MultiplierCLM
    greenL2Symbol 1 zero_le_one greenL2Symbol_norm_le_one f k

theorem norm_greenL2Op_le_one : ‖greenL2Op‖ ≤ 1 :=
  torusL2MultiplierCLM_norm_le
    greenL2Symbol 1 zero_le_one greenL2Symbol_norm_le_one

/-- The concrete multiplier symbol agrees with the coefficient of the
heat-kernel definition of `greenFn` against the paper measure. -/
theorem paperFourierCoeff_greenFn_eq_greenL2Symbol (k : Z4) :
    ∫ z : T4, charT4 k z * (greenFn z : ℂ) ∂paperMeasure =
      greenL2Symbol k := by
  simpa [greenL2Symbol] using paperFourierCoeff_greenFn k

/-! ## Multiplication by an essentially bounded function -/

/-- A pointwise bound turns multiplication by `m` into an `L²`
function. -/
theorem memLp_bounded_mul
    (m : T4 → ℂ) (C : ℝ)
    (hm : AEStronglyMeasurable m haarT4)
    (hC : ∀ᵐ x ∂haarT4, ‖m x‖ ≤ C)
    (f : TorusL2) :
    MemLp (fun x => m x * f x) 2 haarT4 := by
  apply (Lp.memLp f).of_le_mul
  · exact hm.mul (Lp.aestronglyMeasurable f)
  · filter_upwards [hC] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))

/-- Multiplication by a measurable function bounded by `C`, as a linear
map on torus `L²`. -/
def boundedMultiplicationLM
    (m : T4 → ℂ) (C : ℝ)
    (hm : AEStronglyMeasurable m haarT4)
    (hC : ∀ᵐ x ∂haarT4, ‖m x‖ ≤ C) :
    TorusL2 →ₗ[ℂ] TorusL2 where
  toFun f :=
    (memLp_bounded_mul m C hm hC f).toLp
      (fun x => m x * f x)
  map_add' f g := by
    apply Lp.ext
    filter_upwards
      [(memLp_bounded_mul m C hm hC (f + g)).coeFn_toLp,
        (memLp_bounded_mul m C hm hC f).coeFn_toLp,
        (memLp_bounded_mul m C hm hC g).coeFn_toLp,
        Lp.coeFn_add f g,
        Lp.coeFn_add
          ((memLp_bounded_mul m C hm hC f).toLp
            (fun x => m x * f x))
          ((memLp_bounded_mul m C hm hC g).toLp
            (fun x => m x * g x))] with x hfg hf hg hadd hout
    rw [hfg, hout, hadd]
    change m x * (f x + g x) =
      (memLp_bounded_mul m C hm hC f).toLp
          (fun x => m x * f x) x +
        (memLp_bounded_mul m C hm hC g).toLp
          (fun x => m x * g x) x
    rw [hf, hg]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards
      [(memLp_bounded_mul m C hm hC (c • f)).coeFn_toLp,
        (memLp_bounded_mul m C hm hC f).coeFn_toLp,
        Lp.coeFn_smul c f,
        Lp.coeFn_smul c
          ((memLp_bounded_mul m C hm hC f).toLp
            (fun x => m x * f x))] with x hcf hf hsmul hout
    rw [hcf, hsmul]
    change m x * (c * f x) =
      ((RingHom.id ℂ) c •
        (memLp_bounded_mul m C hm hC f).toLp
          (fun x => m x * f x)) x
    rw [show (RingHom.id ℂ) c = c by rfl, hout]
    change m x * (c * f x) =
      c * (memLp_bounded_mul m C hm hC f).toLp
        (fun x => m x * f x) x
    rw [hf]
    ring

@[simp] theorem boundedMultiplicationLM_apply_ae
    (m : T4 → ℂ) (C : ℝ)
    (hm : AEStronglyMeasurable m haarT4)
    (hC : ∀ᵐ x ∂haarT4, ‖m x‖ ≤ C)
    (f : TorusL2) :
    boundedMultiplicationLM m C hm hC f =ᵐ[haarT4]
      fun x => m x * f x :=
  (memLp_bounded_mul m C hm hC f).coeFn_toLp

theorem norm_boundedMultiplicationLM_apply_le
    (m : T4 → ℂ) (C : ℝ)
    (hm : AEStronglyMeasurable m haarT4)
    (hC : ∀ᵐ x ∂haarT4, ‖m x‖ ≤ C)
    (f : TorusL2) :
    ‖boundedMultiplicationLM m C hm hC f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards
    [boundedMultiplicationLM_apply_ae m C hm hC f, hC] with x hmul hx
  rw [hmul, norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))

/-- Multiplication by an essentially bounded function, as a continuous
linear map on torus `L²`. -/
def boundedMultiplicationCLM
    (m : T4 → ℂ) (C : ℝ) (_hC0 : 0 ≤ C)
    (hm : AEStronglyMeasurable m haarT4)
    (hC : ∀ᵐ x ∂haarT4, ‖m x‖ ≤ C) :
    TorusL2 →L[ℂ] TorusL2 :=
  LinearMap.mkContinuous
    (boundedMultiplicationLM m C hm hC) C
    (norm_boundedMultiplicationLM_apply_le m C hm hC)

@[simp] theorem boundedMultiplicationCLM_apply_ae
    (m : T4 → ℂ) (C : ℝ) (hC0 : 0 ≤ C)
    (hm : AEStronglyMeasurable m haarT4)
    (hC : ∀ᵐ x ∂haarT4, ‖m x‖ ≤ C)
    (f : TorusL2) :
    boundedMultiplicationCLM m C hC0 hm hC f =ᵐ[haarT4]
      fun x => m x * f x :=
  boundedMultiplicationLM_apply_ae m C hm hC f

theorem boundedMultiplicationCLM_norm_le
    (m : T4 → ℂ) (C : ℝ) (hC0 : 0 ≤ C)
    (hm : AEStronglyMeasurable m haarT4)
    (hC : ∀ᵐ x ∂haarT4, ‖m x‖ ≤ C) :
    ‖boundedMultiplicationCLM m C hC0 hm hC‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC0
    (norm_boundedMultiplicationLM_apply_le m C hm hC)

/-! ## The mollified Anderson potential -/

/-- The real mollified potential, embedded into `ℂ` for its action on the
complex Hilbert space. -/
def mollifiedPotentialC
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) (x : T4) : ℂ :=
  (multFun M ρ lam ε x ω : ℝ)

theorem continuous_mollifiedPotentialC
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    Continuous (mollifiedPotentialC M ρ lam ε ω) := by
  apply Complex.continuous_ofReal.comp
  exact (continuous_const.mul hξ).sub continuous_const

/-- Continuous-map packaging of a sample of the mollified potential.
Its norm is the concrete `L∞` bound used below. -/
def mollifiedPotentialContinuousMap
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    C(T4, ℂ) where
  toFun := mollifiedPotentialC M ρ lam ε ω
  continuous_toFun :=
    continuous_mollifiedPotentialC M ρ lam ε ω hξ

/-- Multiplication by the mollified potential on `L²`, with a junk-zero
value on the exceptional samples where the totalized Fourier series is
not continuous.  Positive scales lie in the non-junk branch almost
surely. -/
def mollifiedPotentialL2Op
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) :
    TorusL2 →L[ℂ] TorusL2 := by
  classical
  exact if hξ : Continuous (M.xiEps ρ ε ω) then
    let m := mollifiedPotentialContinuousMap M ρ lam ε ω hξ
    boundedMultiplicationCLM m ‖m‖ (norm_nonneg m)
      m.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x =>
        ContinuousMap.norm_coe_le_norm m x)
  else 0

theorem mollifiedPotentialL2Op_apply_ae_of_continuous
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω))
    (f : TorusL2) :
    mollifiedPotentialL2Op M ρ lam ε ω f =ᵐ[haarT4]
      fun x => mollifiedPotentialC M ρ lam ε ω x * f x := by
  rw [mollifiedPotentialL2Op, dif_pos hξ]
  exact boundedMultiplicationCLM_apply_ae
    (mollifiedPotentialContinuousMap M ρ lam ε ω hξ)
    ‖mollifiedPotentialContinuousMap M ρ lam ε ω hξ‖
    (norm_nonneg _)
    (Continuous.aestronglyMeasurable
      (mollifiedPotentialContinuousMap M ρ lam ε ω hξ).continuous)
    (Filter.Eventually.of_forall fun x =>
      ContinuousMap.norm_coe_le_norm
        (mollifiedPotentialContinuousMap M ρ lam ε ω hξ) x)
    f

theorem mollifiedPotentialL2Op_norm_le_of_continuous
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω)) :
    ‖mollifiedPotentialL2Op M ρ lam ε ω‖ ≤
      ‖mollifiedPotentialContinuousMap M ρ lam ε ω hξ‖ := by
  rw [mollifiedPotentialL2Op, dif_pos hξ]
  exact boundedMultiplicationCLM_norm_le
    (mollifiedPotentialContinuousMap M ρ lam ε ω hξ)
    ‖mollifiedPotentialContinuousMap M ρ lam ε ω hξ‖
    (norm_nonneg _)
    (Continuous.aestronglyMeasurable
      (mollifiedPotentialContinuousMap M ρ lam ε ω hξ).continuous)
    (Filter.Eventually.of_forall fun x =>
      ContinuousMap.norm_coe_le_norm
        (mollifiedPotentialContinuousMap M ρ lam ε ω hξ) x)

/-- At positive scale, the concrete multiplier acts by the intended
potential almost surely in the noise sample. -/
theorem ae_mollifiedPotentialL2Op_apply_ae
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (f : TorusL2) :
    ∀ᵐ ω ∂(volume : Measure M.Ω),
      mollifiedPotentialL2Op M ρ lam ε ω f =ᵐ[haarT4]
        fun x => mollifiedPotentialC M ρ lam ε ω x * f x := by
  filter_upwards [M.ae_continuous_xiEps ρ hε] with ω hξ
  exact mollifiedPotentialL2Op_apply_ae_of_continuous
    M ρ lam ε ω hξ f

/-! ## The concrete random `K = G M` and good event -/

/-- The bounded random operator `Kε = G ∘ Mε` of DESIGN §5.2. -/
def andersonK
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) :
    TorusL2 →L[ℂ] TorusL2 :=
  Kop greenL2Op (mollifiedPotentialL2Op M ρ lam ε ω)

@[simp] theorem andersonK_apply
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) (f : TorusL2) :
    andersonK M ρ lam ε ω f =
      greenL2Op (mollifiedPotentialL2Op M ρ lam ε ω f) := by
  rfl

@[simp] theorem torusFourierCoeff_andersonK
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) (f : TorusL2) (k : Z4) :
    torusFourierCoeff (andersonK M ρ lam ε ω f) k =
      greenL2Symbol k *
        torusFourierCoeff
          (mollifiedPotentialL2Op M ρ lam ε ω f) k := by
  rw [andersonK_apply, torusFourierCoeff_greenL2Op]

theorem norm_andersonK_le_potential
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) :
    ‖andersonK M ρ lam ε ω‖ ≤
      ‖mollifiedPotentialL2Op M ρ lam ε ω‖ := by
  calc
    ‖andersonK M ρ lam ε ω‖ ≤
        ‖greenL2Op‖ * ‖mollifiedPotentialL2Op M ρ lam ε ω‖ :=
      norm_mul_le _ _
    _ ≤ 1 * ‖mollifiedPotentialL2Op M ρ lam ε ω‖ :=
      mul_le_mul_of_nonneg_right norm_greenL2Op_le_one
        (norm_nonneg _)
    _ = ‖mollifiedPotentialL2Op M ρ lam ε ω‖ := one_mul _

/-- The concrete half-ball event on which the resolvent exists. -/
def andersonResolventGoodEvent
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) :
    Set M.Ω :=
  resolventGoodEvent greenL2Op
    (mollifiedPotentialL2Op M ρ lam ε)

theorem lopInvertible_on_andersonResolventGoodEvent
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    {ω : M.Ω} (hω : ω ∈ andersonResolventGoodEvent M ρ lam ε) :
    LopInvertible greenL2Op
      (mollifiedPotentialL2Op M ρ lam ε ω) := by
  exact lopInvertible_on_resolventGoodEvent greenL2Op
    (mollifiedPotentialL2Op M ρ lam ε) hω

/-- The recentered inverse, totalized to zero off the invertibility
event.  This is the operator whose fixed matrix coefficients enter the
finite-mode convergence statement. -/
def andersonRecenteredInverse
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) :
    TorusL2 →L[ℂ] TorusL2 := by
  classical
  exact if h : LopInvertible greenL2Op
      (mollifiedPotentialL2Op M ρ lam ε ω) then
    inverseGreen greenL2Op
      (mollifiedPotentialL2Op M ρ lam ε ω) h - greenL2Op
  else 0

theorem andersonRecenteredInverse_eq_on_good
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    {ω : M.Ω} (hω : ω ∈ andersonResolventGoodEvent M ρ lam ε) :
    andersonRecenteredInverse M ρ lam ε ω =
      inverseGreen greenL2Op
        (mollifiedPotentialL2Op M ρ lam ε ω)
        (lopInvertible_on_andersonResolventGoodEvent
          M ρ lam ε hω) - greenL2Op := by
  rw [andersonRecenteredInverse, dif_pos
    (lopInvertible_on_andersonResolventGoodEvent M ρ lam ε hω)]

/-- `(3.23)`-signed Fourier matrix coefficient of the concrete
recentered inverse. -/
def torusOperatorModeCoeffH
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (α β : Z4) (ω : M.Ω) : ℂ :=
  ⟪charT4Lp 2 (-α),
    andersonRecenteredInverse M ρ lam ε ω (charT4Lp 2 β)⟫_ℂ

theorem torusOperatorModeCoeffH_eq_abstract
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (α β : Z4) (ω : M.Ω) :
    torusOperatorModeCoeffH M ρ lam ε α β ω =
      operatorModeCoeffH greenL2Op
        (mollifiedPotentialL2Op M ρ lam ε ω)
        (charT4Lp 2) α β := by
  classical
  unfold torusOperatorModeCoeffH andersonRecenteredInverse
    operatorModeCoeffH
  split_ifs with h
  · simp only [sub_apply]
  · simp

/-- In the norm-small regime, the selected inverse is the actual
operator-valued Neumann series followed by `G`. -/
theorem inverseGreen_eq_neumann_andersonK
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) (hK : ‖andersonK M ρ lam ε ω‖ < 1) :
    inverseGreen greenL2Op
        (mollifiedPotentialL2Op M ρ lam ε ω)
        (lopInvertible_of_norm_Kop_lt_one greenL2Op
          (mollifiedPotentialL2Op M ρ lam ε ω) hK) =
      neumannInverse (andersonK M ρ lam ε ω) hK * greenL2Op := by
  exact inverseGreen_of_norm_lt_one greenL2Op
    (mollifiedPotentialL2Op M ρ lam ε ω) hK

/-- The abstract second-moment/Markov estimate specialized to the
concrete torus operators.  Establishing its two analytic premises is
the remaining estimate in P-L2, not an operator-definition gap. -/
theorem measureReal_compl_andersonResolventGoodEvent_le
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε δ : ℝ)
    (hint :
      Integrable (fun ω =>
        ‖andersonK M ρ lam ε ω‖ ^ 2)
        (volume : Measure M.Ω))
    (hsecond :
      (∫ ω, ‖andersonK M ρ lam ε ω‖ ^ 2
        ∂(volume : Measure M.Ω)) ≤ δ) :
    (volume : Measure M.Ω).real
        (andersonResolventGoodEvent M ρ lam ε)ᶜ ≤ 4 * δ := by
  exact measureReal_compl_resolventGoodEvent_le
    (volume : Measure M.Ω) greenL2Op
    (mollifiedPotentialL2Op M ρ lam ε) δ hint hsecond

end

end Anderson4D
