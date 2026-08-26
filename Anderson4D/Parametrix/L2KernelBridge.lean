import Anderson4D.Parametrix.L2RandomOperator
import Anderson4D.Parametrix.L2GreenConvolution

/-!
# Kernel-to-operator normalization bridge on torus `L²`

The physical coefficients in paper (3.23) integrate both external
variables against the unnormalized torus measure `paperMeasure`, while
`TorusL2` uses probability Haar measure.  Therefore a kernel acting by
integration against `paperMeasure` has

`paperKernelCoeff K α β =
  volume(T⁴) * ⟪e_{-α}, T_K e_β⟫`.

This factor is essential.  The file packages that ledger identity,
defines the physical Neumann-term kernel, and states the exact
kernel-action interface required to identify it with the bounded
operator power `K^n G`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ComplexConjugate
open scoped InnerProductSpace Convolution

/-- Total mass of the paper's four-dimensional torus measure. -/
def paperTorusVolume : ℝ :=
  (2 * Real.pi) ^ dim

theorem paperTorusVolume_pos : 0 < paperTorusVolume := by
  unfold paperTorusVolume
  positivity

theorem paperTorusVolume_ne_zero : paperTorusVolume ≠ 0 :=
  ne_of_gt paperTorusVolume_pos

/-! ## Generic kernel action -/

/-- It suffices to know the action of a kernel operator on one Fourier
character in order to identify the corresponding matrix coefficient.
No Fubini hypothesis is hidden here: both sides use the same iterated
integral order. -/
theorem paperKernelCoeff_eq_volume_mul_inner_of_action
    (A : TorusL2 →L[ℂ] TorusL2)
    (kernel : T4 → T4 → ℂ) (α β : Z4)
    (hAction :
      A (charT4Lp 2 β) =ᵐ[haarT4]
        fun x => ∫ y, kernel x y * charT4 β y ∂paperMeasure) :
    paperKernelCoeff kernel α β =
      (paperTorusVolume : ℂ) *
        ⟪charT4Lp 2 (-α), A (charT4Lp 2 β)⟫_ℂ := by
  have hfactor : ∀ x : T4,
      (∫ y,
          charT4 α x * charT4 β y * kernel x y
          ∂paperMeasure) =
        charT4 α x *
          ∫ y, kernel x y * charT4 β y ∂paperMeasure := by
    intro x
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    ring
  unfold paperKernelCoeff
  simp_rw [hfactor]
  have h2π :
      (ENNReal.ofReal paperTorusVolume).toReal =
        paperTorusVolume :=
    ENNReal.toReal_ofReal paperTorusVolume_pos.le
  rw [paperMeasure, show (2 * Real.pi) ^ dim = paperTorusVolume by rfl,
    integral_smul_measure, h2π, Complex.real_smul]
  rw [MeasureTheory.L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards
    [coeFn_charT4Lp 2 (-α), hAction] with x hchar hA
  rw [hchar, hA]
  simp only [RCLike.inner_apply]
  rw [conj_charT4_neg]
  change
    charT4 α x *
        (∫ y, kernel x y * charT4 β y ∂paperMeasure) =
      (∫ y, kernel x y * charT4 β y ∂paperMeasure) *
        charT4 α x
  exact mul_comm _ _

/-- Division form of the normalization ledger. -/
theorem inner_eq_volume_inv_mul_paperKernelCoeff_of_action
    (A : TorusL2 →L[ℂ] TorusL2)
    (kernel : T4 → T4 → ℂ) (α β : Z4)
    (hAction :
      A (charT4Lp 2 β) =ᵐ[haarT4]
        fun x => ∫ y, kernel x y * charT4 β y ∂paperMeasure) :
    ⟪charT4Lp 2 (-α), A (charT4Lp 2 β)⟫_ℂ =
      (paperTorusVolume : ℂ)⁻¹ *
        paperKernelCoeff kernel α β := by
  have hledger :=
    paperKernelCoeff_eq_volume_mul_inner_of_action
      A kernel α β hAction
  calc
    ⟪charT4Lp 2 (-α), A (charT4Lp 2 β)⟫_ℂ =
        (paperTorusVolume : ℂ)⁻¹ *
          ((paperTorusVolume : ℂ) *
            ⟪charT4Lp 2 (-α), A (charT4Lp 2 β)⟫_ℂ) := by
      field_simp [paperTorusVolume_ne_zero]
    _ = (paperTorusVolume : ℂ)⁻¹ *
        paperKernelCoeff kernel α β := by rw [hledger]

/-! ## Physical Neumann kernels -/

/-- Kernel of the `n`-th physical Neumann term, with all `n`
multiplication points integrated against the paper measure. -/
def neumannTermKernel
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ)
    (x y : T4) (ω : M.Ω) : ℂ :=
  ∫ v : Fin n → T4,
    (((∏ e : Fin (n + 1),
        greenFn
          ((assemble x y v) e.castSucc -
            (assemble x y v) e.succ)) *
      ∏ i, multFun M ρ lam ε (v i) ω : ℝ) : ℂ)
    ∂(Measure.pi fun _ => paperMeasure)

theorem neumannCoeff_eq_paperKernelCoeff
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ)
    (α β : Z4) (ω : M.Ω) :
    neumannCoeff M ρ lam ε n α β ω =
      paperKernelCoeff
        (neumannTermKernel M ρ lam ε n · · ω) α β := by
  unfold neumannCoeff paperKernelCoeff neumannTermKernel
  apply integral_congr_ae
  filter_upwards with x
  apply integral_congr_ae
  filter_upwards with y
  rw [← integral_const_mul]

/-- The exact upstream interface for the physical/operator bridge:
`K^n G` acts on a Fourier character by the chain kernel from
`neumannCoeff`. -/
def NeumannTermKernelAction
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (β : Z4) (ω : M.Ω) : Prop :=
  ((andersonK M ρ lam ε ω) ^ n * greenL2Op)
      (charT4Lp 2 β) =ᵐ[haarT4]
    fun x =>
      ∫ y,
        neumannTermKernel M ρ lam ε n x y ω *
          charT4 β y
        ∂paperMeasure

/-- Once the kernel-action identity is available, the matrix
coefficient is the physical Neumann coefficient divided by exactly one
torus-volume factor. -/
theorem inner_pow_andersonK_mul_green_eq_neumannCoeff
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (α β : Z4) (ω : M.Ω)
    (hAction :
      NeumannTermKernelAction M ρ lam ε n β ω) :
    ⟪charT4Lp 2 (-α),
      (((andersonK M ρ lam ε ω) ^ n * greenL2Op)
        (charT4Lp 2 β))⟫_ℂ =
      (paperTorusVolume : ℂ)⁻¹ *
        neumannCoeff M ρ lam ε n α β ω := by
  rw [neumannCoeff_eq_paperKernelCoeff]
  exact inner_eq_volume_inv_mul_paperKernelCoeff_of_action
    ((andersonK M ρ lam ε ω) ^ n * greenL2Op)
    (neumannTermKernel M ρ lam ε n · · ω)
    α β hAction

/-! ## The order-zero sanity check -/

@[simp] theorem greenL2Symbol_neg (k : Z4) :
    greenL2Symbol (-k) = greenL2Symbol k := by
  simp [greenL2Symbol]

/-- The Fourier multiplier acts diagonally on a character. -/
theorem greenL2Op_char (k : Z4) :
    greenL2Op (charT4Lp 2 k) =
      greenL2Symbol k • charT4Lp 2 k := by
  have hbasis :
      torusFourierBasis k = charT4Lp 2 k :=
    congrFun coe_torusFourierBasis k
  have hdiag :
      torusDiagonalCLM greenL2Symbol 1 zero_le_one
          greenL2Symbol_norm_le_one
          (torusFourierBasis.repr (charT4Lp 2 k)) =
        greenL2Symbol k •
          torusFourierBasis.repr (charT4Lp 2 k) := by
    rw [← hbasis]
    rw [torusFourierBasis.repr_self]
    ext l
    simp only [torusDiagonalCLM_apply]
    by_cases h : l = k
    · subst l
      simp [lp.single_apply]
    · simp [lp.single_apply, h]
  apply torusFourierBasis.repr.injective
  change
    torusFourierBasis.repr
        (torusFourierBasis.repr.symm
          (torusDiagonalCLM greenL2Symbol 1 zero_le_one
            greenL2Symbol_norm_le_one
            (torusFourierBasis.repr (charT4Lp 2 k)))) =
      torusFourierBasis.repr
        (greenL2Symbol k • charT4Lp 2 k)
  calc
    torusFourierBasis.repr
        (torusFourierBasis.repr.symm
          (torusDiagonalCLM greenL2Symbol 1 zero_le_one
            greenL2Symbol_norm_le_one
            (torusFourierBasis.repr (charT4Lp 2 k)))) =
        torusDiagonalCLM greenL2Symbol 1 zero_le_one
          greenL2Symbol_norm_le_one
          (torusFourierBasis.repr (charT4Lp 2 k)) :=
      torusFourierBasis.repr.apply_symm_apply _
    _ = greenL2Symbol k •
        torusFourierBasis.repr (charT4Lp 2 k) :=
      hdiag
    _ = torusFourierBasis.repr
        (greenL2Symbol k • charT4Lp 2 k) := by
      rw [map_smul]

private theorem fourier_arg_neg
    (n : ℤ) (x : AddCircle (2 * Real.pi)) :
    fourier n (-x) = conj (fourier n x) := by
  change
    (AddCircle.toCircle (n • (-x)) : ℂ) =
      conj (fourier n x)
  rw [zsmul_neg]
  exact fourier_neg'

/-- A character turns spatial subtraction into multiplication by its
conjugate. -/
theorem charT4_sub_apply (k : Z4) (x y : T4) :
    charT4 k (x - y) =
      charT4 k x * conj (charT4 k y) := by
  rw [sub_eq_add_neg, charT4_add_apply]
  congr 1
  unfold charT4
  simp_rw [Pi.neg_apply, fourier_arg_neg, map_prod]

set_option maxHeartbeats 800000 in
/-- The heat-kernel Green function, integrated against the paper
measure, realizes the same multiplier on a single character. -/
theorem integral_greenFn_sub_mul_char
    (k : Z4) (x : T4) :
    (∫ y : T4,
        (greenFn (x - y) : ℂ) * charT4 k y
        ∂paperMeasure) =
      greenL2Symbol k * charT4 k x := by
  let f : T4 → ℂ := fun z =>
    (greenFn (-z) : ℂ) * charT4 k (x + z)
  calc
    (∫ y : T4,
        (greenFn (x - y) : ℂ) * charT4 k y
        ∂paperMeasure) =
        ∫ y : T4, f (y - x) ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with y
      change
        (greenFn (x - y) : ℂ) * charT4 k y =
          (greenFn (-(y - x)) : ℂ) *
            charT4 k (x + (y - x))
      congr 2 <;> abel
    _ = ∫ z : T4, f z ∂paperMeasure :=
      by
        have hfmeas : AEStronglyMeasurable f paperMeasure := by
          have hgreenc :
              Integrable (fun z : T4 => (greenFn z : ℂ))
                paperMeasure :=
            integrable_greenFn_paper.ofReal
          have hf_eq :
              f = fun z : T4 =>
                (greenFn z : ℂ) * charT4 k (x + z) := by
            funext z
            unfold f
            rw [greenFn_memE.neg_invariant]
          rw [hf_eq]
          exact hgreenc.aestronglyMeasurable.mul
            ((continuous_charT4 k).measurable.comp
              (measurable_const.add measurable_id)).aestronglyMeasurable
        have hfmeasMap :
            AEStronglyMeasurable f
              (Measure.map (fun z : T4 => z - x) paperMeasure) := by
          rw [(measurePreserving_sub_paper x).map_eq]
          exact hfmeas
        have hmap :=
          integral_map
            (μ := paperMeasure) (φ := fun z : T4 => z - x)
            (measurePreserving_sub_paper x).measurable.aemeasurable
            (f := f) hfmeasMap
        rw [(measurePreserving_sub_paper x).map_eq] at hmap
        exact hmap.symm
    _ = charT4 k x *
        ∫ z : T4, charT4 k z * (greenFn z : ℂ)
          ∂paperMeasure := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      change
        (greenFn (-z) : ℂ) * charT4 k (x + z) =
          charT4 k x * (charT4 k z * (greenFn z : ℂ))
      rw [greenFn_memE.neg_invariant z, charT4_add_apply]
      ring
    _ = charT4 k x * greenL2Symbol k := by
      rw [paperFourierCoeff_greenFn_eq_greenL2Symbol]
    _ = greenL2Symbol k * charT4 k x := by
      ring

/-- Concrete kernel action for the zeroth Neumann term. -/
theorem greenL2Op_char_action
    (k : Z4) :
    greenL2Op (charT4Lp 2 k) =ᵐ[haarT4]
      fun x =>
        ∫ y : T4,
          (greenFn (x - y) : ℂ) * charT4 k y
          ∂paperMeasure := by
  rw [greenL2Op_char]
  filter_upwards
    [Lp.coeFn_smul (greenL2Symbol k) (charT4Lp 2 k),
      coeFn_charT4Lp 2 k] with x hsmul hchar
  rw [hsmul]
  change greenL2Symbol k * (charT4Lp 2 k : T4 → ℂ) x = _
  rw [hchar, integral_greenFn_sub_mul_char]

@[simp] theorem neumannTermKernel_zero
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (x y : T4) (ω : M.Ω) :
    neumannTermKernel M ρ lam ε 0 x y ω =
      greenFn (x - y) := by
  unfold neumannTermKernel
  rw [integral_unique]
  have hmass :
      (Measure.pi fun _ : Fin 0 => paperMeasure).real Set.univ = 1 := by
    rw [measureReal_def, Measure.pi_empty_univ]
    simp
  rw [hmass, one_smul]
  simp [assemble]

/-- The physical/operator bridge is unconditional at order zero. -/
theorem neumannTermKernelAction_zero
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (β : Z4) (ω : M.Ω) :
    NeumannTermKernelAction M ρ lam ε 0 β ω := by
  unfold NeumannTermKernelAction
  simpa using greenL2Op_char_action β

theorem inner_greenL2Op_eq_neumannCoeff_zero
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (α β : Z4) (ω : M.Ω) :
    ⟪charT4Lp 2 (-α), greenL2Op (charT4Lp 2 β)⟫_ℂ =
      (paperTorusVolume : ℂ)⁻¹ *
        neumannCoeff M ρ lam ε 0 α β ω := by
  simpa using inner_pow_andersonK_mul_green_eq_neumannCoeff
    M ρ lam ε 0 α β ω
      (neumannTermKernelAction_zero M ρ lam ε β ω)

/-! ## The norm-small Neumann tail -/

/-- Pointwise subtraction of the zeroth term from the operator-valued
Neumann series. -/
theorem neumannInverse_mul_apply_sub_eq_tsum_tail
    (K G : TorusL2 →L[ℂ] TorusL2) (hK : ‖K‖ < 1)
    (f : TorusL2) :
    (neumannInverse K hK * G - G) f =
      ∑' n : ℕ, (K ^ (n + 1) * G) f := by
  have hsOp : Summable (fun n : ℕ => K ^ n) :=
    summable_pow_of_norm_lt_one K hK
  have hsVec : Summable (fun n : ℕ => (K ^ n) (G f)) :=
    (ContinuousLinearMap.apply ℂ TorusL2 (G f)).summable hsOp
  have hsplit := hsVec.sum_add_tsum_nat_add 1
  simp only [sub_apply, mul_apply_eq_comp]
  rw [neumannInverse_apply_eq_tsum K hK]
  rw [← hsplit]
  simp

/-- Taking a fixed Hilbert-space matrix coefficient commutes with the
norm-small Neumann tail. -/
theorem inner_neumannInverse_mul_apply_sub_eq_tsum_tail
    (K G : TorusL2 →L[ℂ] TorusL2) (hK : ‖K‖ < 1)
    (e f : TorusL2) :
    ⟪e, (neumannInverse K hK * G - G) f⟫_ℂ =
      ∑' n : ℕ, ⟪e, (K ^ (n + 1) * G) f⟫_ℂ := by
  rw [neumannInverse_mul_apply_sub_eq_tsum_tail K G hK f]
  exact (innerSL ℂ e).map_tsum
    ((ContinuousLinearMap.apply ℂ TorusL2 (G f)).summable
      ((summable_pow_of_norm_lt_one K hK).comp_injective
        (fun _ _ h => Nat.succ.inj h)))

/-- If the physical chain kernel realizes every positive operator
power on the chosen input mode, the full recentered Neumann matrix
coefficient is the physical coefficient tail divided by one torus
volume. -/
theorem inner_neumannInverse_mul_green_sub_eq_neumannCoeff_tail
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (α β : Z4) (ω : M.Ω)
    (hK : ‖andersonK M ρ lam ε ω‖ < 1)
    (hAction : ∀ n : ℕ,
      NeumannTermKernelAction M ρ lam ε (n + 1) β ω) :
    ⟪charT4Lp 2 (-α),
      (neumannInverse (andersonK M ρ lam ε ω) hK *
          greenL2Op - greenL2Op)
        (charT4Lp 2 β)⟫_ℂ =
      (paperTorusVolume : ℂ)⁻¹ *
        ∑' n : ℕ,
          neumannCoeff M ρ lam ε (n + 1) α β ω := by
  rw [inner_neumannInverse_mul_apply_sub_eq_tsum_tail]
  calc
    (∑' n : ℕ,
        ⟪charT4Lp 2 (-α),
          (((andersonK M ρ lam ε ω) ^ (n + 1) *
              greenL2Op) (charT4Lp 2 β))⟫_ℂ) =
        ∑' n : ℕ,
          (paperTorusVolume : ℂ)⁻¹ *
            neumannCoeff M ρ lam ε (n + 1) α β ω := by
      apply tsum_congr
      intro n
      exact inner_pow_andersonK_mul_green_eq_neumannCoeff
        M ρ lam ε (n + 1) α β ω (hAction n)
    _ = (paperTorusVolume : ℂ)⁻¹ *
        ∑' n : ℕ,
          neumannCoeff M ρ lam ε (n + 1) α β ω :=
      tsum_mul_left

/-- On the norm-small event, the project's totalized concrete inverse
selects the Neumann inverse, so its Fourier matrix coefficient equals
the physical coefficient tail with the normalization ledger applied. -/
theorem torusOperatorModeCoeffH_eq_neumannCoeff_tail
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (α β : Z4) (ω : M.Ω)
    (hK : ‖andersonK M ρ lam ε ω‖ < 1)
    (hAction : ∀ n : ℕ,
      NeumannTermKernelAction M ρ lam ε (n + 1) β ω) :
    torusOperatorModeCoeffH M ρ lam ε α β ω =
      (paperTorusVolume : ℂ)⁻¹ *
        ∑' n : ℕ,
          neumannCoeff M ρ lam ε (n + 1) α β ω := by
  unfold torusOperatorModeCoeffH andersonRecenteredInverse
  rw [dif_pos (lopInvertible_of_norm_Kop_lt_one greenL2Op
    (mollifiedPotentialL2Op M ρ lam ε ω) hK)]
  rw [inverseGreen_eq_neumann_andersonK M ρ lam ε ω hK]
  exact inner_neumannInverse_mul_green_sub_eq_neumannCoeff_tail
    M ρ lam ε α β ω hK hAction

/-- Exact comparison with the paper's coefficient-route definition.
There are two indispensable scalars: `lamEps` because `modeHcoeff`
describes `lamEps⁻¹ (Gε - G)`, and `paperTorusVolume⁻¹` because the
physical coefficient uses the unnormalized torus measure in both
external variables while `TorusL2` uses probability Haar. -/
theorem torusOperatorModeCoeffH_eq_scaled_modeHcoeff
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (α β : Z4) (ω : M.Ω)
    (hK : ‖andersonK M ρ lam ε ω‖ < 1)
    (hLam : lamEps lam ε ≠ 0)
    (hAction : ∀ n : ℕ,
      NeumannTermKernelAction M ρ lam ε (n + 1) β ω) :
    torusOperatorModeCoeffH M ρ lam ε α β ω =
      (lamEps lam ε / paperTorusVolume) •
        modeHcoeff M ρ lam ε α β ω := by
  rw [torusOperatorModeCoeffH_eq_neumannCoeff_tail
    M ρ lam ε α β ω hK hAction]
  unfold modeHcoeff
  rw [smul_smul]
  congr 1
  field_simp [hLam, paperTorusVolume_ne_zero]
  simp [paperTorusVolume_ne_zero]

end

end Anderson4D
