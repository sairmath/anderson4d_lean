import Anderson4D.Continuum.FourPointCoefficient
import Anderson4D.Continuum.GreenFourier
import Anderson4D.Continuum.TorusFourier

/-!
# Fourier and Gram form of the four-point Green kernel

This file supplies the analytic bridge needed by node `D-limit`.  It
first computes the Fourier coefficient of a translated Green kernel,
then packages two such coefficients as a mode profile.  The final
Fubini theorem identifies `fourPointHCoeff` with the bilinear Gram
integral of two profiles.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set
open scoped BigOperators ComplexConjugate

/-! ## Measurability and translation of the Green kernel -/

private theorem measurable_torusLift_coord_fourPoint (i : Fin dim) :
    Measurable fun z : T4 => torusLift z i := by
  unfold torusLift
  exact measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco (2 * Real.pi) (-Real.pi)).measurable.comp
      (measurable_pi_apply i))

/-- Joint measurability of the heat kernel, exposed here because the
corresponding implementation lemma in `GreenFourier` is private. -/
theorem measurable_heatKernelT4_prod :
    Measurable fun p : ℝ × T4 => heatKernelT4 p.1 p.2 := by
  unfold heatKernelT4
  apply Measurable.tsum
  intro k
  have hlattice :
      Measurable fun p : ℝ × T4 => latticeDistSq p.2 k := by
    unfold latticeDistSq
    apply Finset.measurable_sum
    intro i _hi
    exact
      (((measurable_torusLift_coord_fourPoint i).comp measurable_snd).add
        measurable_const).pow_const 2
  have hcoeff : Measurable fun p : ℝ × T4 =>
      (4 * Real.pi * p.1) ^ (-2 : ℤ) :=
    ((measurable_const.mul measurable_fst).pow_const (-2 : ℤ))
  have hexp : Measurable fun p : ℝ × T4 =>
      Real.exp (-latticeDistSq p.2 k / (4 * p.1)) :=
    Real.measurable_exp.comp
      (hlattice.neg.div (measurable_const.mul measurable_fst))
  exact hcoeff.mul hexp

/-- The heat-integral construction of the Green kernel is measurable. -/
theorem measurable_greenFn : Measurable greenFn := by
  have hjoint : Measurable fun p : T4 × ℝ =>
      Real.exp (-p.2) * heatKernelT4 p.2 p.1 :=
    (Real.measurable_exp.comp measurable_snd.neg).mul
      (measurable_heatKernelT4_prod.comp
        (measurable_snd.prodMk measurable_fst))
  have hint :
      StronglyMeasurable fun z : T4 =>
        ∫ t : ℝ in Ioi 0,
          Real.exp (-t) * heatKernelT4 t z :=
    hjoint.stronglyMeasurable.integral_prod_right
  exact hint.measurable

/-- Translation preserves the `L¹` property of the Green kernel. -/
theorem integrable_greenFn_sub (z : T4) :
    Integrable (fun x : T4 => greenFn (x - z)) paperMeasure := by
  have hG := integrable_greenFn_paper
  rw [paperMeasure_eq_volume] at hG ⊢
  have h :=
    (measurePreserving_add_right (volume : Measure T4) (-z)).integrable_comp
      hG.aestronglyMeasurable
  simpa only [Function.comp_def, sub_eq_add_neg] using
    h.mpr hG

/-- Every translate of the Green kernel has paper mass one. -/
theorem integral_greenFn_sub (z : T4) :
    ∫ x : T4, greenFn (x - z) ∂paperMeasure = 1 := by
  rw [paperMeasure_eq_volume]
  calc
    (∫ x : T4, greenFn (x - z) ∂(volume : Measure T4)) =
        ∫ x : T4, greenFn x ∂(volume : Measure T4) := by
      simpa only [sub_eq_add_neg] using
        integral_add_right_eq_self greenFn (-z)
    _ = 1 := by
      rw [← paperMeasure_eq_volume]
      exact integral_greenFn_paper

/-! ## One-mode coefficients and two-mode profiles -/

/-- The positive-exponential Fourier coefficient of the Green kernel
translated to the point `z`. -/
def translatedGreenMode (k : Z4) (z : T4) : ℂ :=
  ∫ x : T4,
    charT4 k x * (greenFn (x - z) : ℂ) ∂paperMeasure

private theorem charT4_add_point (k : Z4) (x z : T4) :
    charT4 k (x + z) = charT4 k x * charT4 k z := by
  unfold charT4
  simp only [Pi.add_apply]
  calc
    (∏ i, fourier (k i) (x i + z i)) =
        ∏ i, (fourier (k i) (x i) *
          fourier (k i) (z i)) := by
      apply Finset.prod_congr rfl
      intro i _hi
      rw [fourier_apply, zsmul_add, AddCircle.toCircle_add,
        Circle.coe_mul]
      rfl
    _ = _ := Finset.prod_mul_distrib

/-- Explicit translated Fourier coefficient of `G`. -/
theorem translatedGreenMode_eq (k : Z4) (z : T4) :
    translatedGreenMode k z =
      charT4 k z *
        (((1 + ∑ i, (k i : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
  unfold translatedGreenMode
  rw [paperMeasure_eq_volume]
  calc
    (∫ x : T4, charT4 k x * (greenFn (x - z) : ℂ)
        ∂(volume : Measure T4)) =
        ∫ x : T4,
          charT4 k (x + z) *
            (greenFn ((x + z) - z) : ℂ)
          ∂(volume : Measure T4) := by
      symm
      simpa only using
        integral_add_right_eq_self
          (fun x : T4 =>
            charT4 k x * (greenFn (x - z) : ℂ)) z
    _ = charT4 k z *
        ∫ x : T4, charT4 k x * (greenFn x : ℂ)
          ∂(volume : Measure T4) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change
          charT4 k (x + z) *
              (greenFn ((x + z) - z) : ℂ) =
            charT4 k z *
              (charT4 k x * (greenFn x : ℂ))
        rw [charT4_add_point, add_sub_cancel_right]
        ring
    _ = charT4 k z *
        ∫ x : T4, charT4 k x * (greenFn x : ℂ)
          ∂paperMeasure := by
      rw [paperMeasure_eq_volume]
    _ = _ := by rw [paperFourierCoeff_greenFn]

/-- The two-external-leg mode profile at the common contraction point. -/
def fourPointModeProfile (α β : Z4) (z : T4) : ℂ :=
  ∫ x : T4, ∫ y : T4,
    charT4 α x * charT4 β y *
      ((greenFn (x - z) * greenFn (y - z) : ℝ) : ℂ)
    ∂paperMeasure ∂paperMeasure

/-- The double integral defining a profile factors into the two
translated one-mode coefficients. -/
theorem fourPointModeProfile_eq_mul_translated
    (α β : Z4) (z : T4) :
    fourPointModeProfile α β z =
      translatedGreenMode α z * translatedGreenMode β z := by
  unfold fourPointModeProfile translatedGreenMode
  calc
    (∫ x : T4, ∫ y : T4,
        charT4 α x * charT4 β y *
          ((greenFn (x - z) * greenFn (y - z) : ℝ) : ℂ)
        ∂paperMeasure ∂paperMeasure) =
        ∫ x : T4,
          (charT4 α x * (greenFn (x - z) : ℂ)) *
            ∫ y : T4,
              charT4 β y * (greenFn (y - z) : ℂ)
              ∂paperMeasure
          ∂paperMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change
          (∫ y : T4,
            charT4 α x * charT4 β y *
              ((greenFn (x - z) * greenFn (y - z) : ℝ) : ℂ)
            ∂paperMeasure) =
            (charT4 α x * (greenFn (x - z) : ℂ)) *
              ∫ y : T4,
                charT4 β y * (greenFn (y - z) : ℂ)
                ∂paperMeasure
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          push_cast
          ring
    _ = _ := integral_mul_const _ _

/-- Explicit Fourier character formula for the mode profile. -/
theorem fourPointModeProfile_eq
    (α β : Z4) (z : T4) :
    fourPointModeProfile α β z =
      (charT4 α z *
          (((1 + ∑ i, (α i : ℝ) ^ 2)⁻¹ : ℝ) : ℂ)) *
        (charT4 β z *
          (((1 + ∑ i, (β i : ℝ) ^ 2)⁻¹ : ℝ) : ℂ)) := by
  rw [fourPointModeProfile_eq_mul_translated,
    translatedGreenMode_eq, translatedGreenMode_eq]

/-! ## Absolute integrability of the five-variable kernel -/

/-- Right-associated carrier for the four external variables
`(x₁,y₁,x₂,y₂)`. -/
abbrev FourPointExternal :=
  T4 × (T4 × (T4 × T4))

/-- Product paper measure on the four external variables. -/
def fourPointExternalMeasure : Measure FourPointExternal :=
  paperMeasure.prod
    (paperMeasure.prod (paperMeasure.prod paperMeasure))

instance : SFinite fourPointExternalMeasure := by
  unfold fourPointExternalMeasure
  infer_instance

instance : IsFiniteMeasure fourPointExternalMeasure := by
  unfold fourPointExternalMeasure
  infer_instance

/-- One character-decorated Green leg. -/
def greenModeFactor (k : Z4) (z x : T4) : ℂ :=
  charT4 k x * (greenFn (x - z) : ℂ)

/-- The full five-variable Fourier integrand, with the four external
variables grouped separately from their common contraction point. -/
def fourPointFourierIntegrand
    (α₁ β₁ α₂ β₂ : Z4)
    (p : FourPointExternal) (z : T4) : ℂ :=
  greenModeFactor α₁ z p.1 *
    (greenModeFactor β₁ z p.2.1 *
      (greenModeFactor α₂ z p.2.2.1 *
        greenModeFactor β₂ z p.2.2.2))

theorem measurable_greenModeFactor_joint (k : Z4) :
    Measurable fun p : T4 × T4 =>
      greenModeFactor k p.2 p.1 := by
  unfold greenModeFactor
  exact
    ((continuous_charT4 k).measurable.comp measurable_fst).mul
      ((measurable_greenFn.comp
        (measurable_fst.sub measurable_snd)).complex_ofReal)

private theorem measurable_greenModeFactor_comp
    {γ : Type*} [MeasurableSpace γ]
    (k : Z4) {x z : γ → T4}
    (hx : Measurable x) (hz : Measurable z) :
    Measurable fun q => greenModeFactor k (z q) (x q) := by
  unfold greenModeFactor
  exact
    ((continuous_charT4 k).measurable.comp hx).mul
      ((measurable_greenFn.comp (hx.sub hz)).complex_ofReal)

/-- A character-decorated translated Green leg is integrable. -/
theorem integrable_greenModeFactor (k : Z4) (z : T4) :
    Integrable (greenModeFactor k z) paperMeasure := by
  have hG :
      Integrable (fun x : T4 => (greenFn (x - z) : ℂ))
        paperMeasure :=
    (integrable_greenFn_sub z).ofReal
  exact hG.bdd_mul
    (continuous_charT4 k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [norm_charT4])

/-- The `L¹` norm of one decorated leg is exactly one. -/
theorem integral_norm_greenModeFactor (k : Z4) (z : T4) :
    ∫ x : T4, ‖greenModeFactor k z x‖ ∂paperMeasure = 1 := by
  calc
    (∫ x : T4, ‖greenModeFactor k z x‖ ∂paperMeasure) =
        ∫ x : T4, greenFn (x - z) ∂paperMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        unfold greenModeFactor
        change
          ‖charT4 k x * (greenFn (x - z) : ℂ)‖ =
            greenFn (x - z)
        rw [norm_mul, norm_charT4, one_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (greenFn_nonneg _)]
    _ = 1 := integral_greenFn_sub z

/-- For each fixed contraction point, the product of the four external
Green legs is integrable. -/
theorem integrable_fourPointFourierIntegrand_section
    (α₁ β₁ α₂ β₂ : Z4) (z : T4) :
    Integrable
      (fun p : FourPointExternal =>
        fourPointFourierIntegrand α₁ β₁ α₂ β₂ p z)
      fourPointExternalMeasure := by
  have h₂ :=
    (integrable_greenModeFactor α₂ z).mul_prod
      (integrable_greenModeFactor β₂ z)
  have h₁ :=
    (integrable_greenModeFactor β₁ z).mul_prod h₂
  have h₀ :=
    (integrable_greenModeFactor α₁ z).mul_prod h₁
  simpa only [fourPointExternalMeasure,
    fourPointFourierIntegrand] using h₀

/-- The integral of the norm of the four-leg section is one. -/
theorem integral_norm_fourPointFourierIntegrand_section
    (α₁ β₁ α₂ β₂ : Z4) (z : T4) :
    ∫ p : FourPointExternal,
        ‖fourPointFourierIntegrand α₁ β₁ α₂ β₂ p z‖
        ∂fourPointExternalMeasure = 1 := by
  unfold fourPointExternalMeasure fourPointFourierIntegrand
  simp only [norm_mul]
  calc
    (∫ p : T4 × (T4 × (T4 × T4)),
        ‖greenModeFactor α₁ z p.1‖ *
          (‖greenModeFactor β₁ z p.2.1‖ *
            (‖greenModeFactor α₂ z p.2.2.1‖ *
              ‖greenModeFactor β₂ z p.2.2.2‖))
        ∂(paperMeasure.prod
          (paperMeasure.prod (paperMeasure.prod paperMeasure)))) =
        (∫ x : T4, ‖greenModeFactor α₁ z x‖ ∂paperMeasure) *
          ∫ q : T4 × (T4 × T4),
            ‖greenModeFactor β₁ z q.1‖ *
              (‖greenModeFactor α₂ z q.2.1‖ *
                ‖greenModeFactor β₂ z q.2.2‖)
            ∂(paperMeasure.prod (paperMeasure.prod paperMeasure)) :=
      integral_prod_mul
        (μ := paperMeasure)
        (ν := paperMeasure.prod (paperMeasure.prod paperMeasure))
        (fun x : T4 => ‖greenModeFactor α₁ z x‖)
        (fun q : T4 × (T4 × T4) =>
          ‖greenModeFactor β₁ z q.1‖ *
            (‖greenModeFactor α₂ z q.2.1‖ *
              ‖greenModeFactor β₂ z q.2.2‖))
    _ = (∫ x : T4, ‖greenModeFactor α₁ z x‖ ∂paperMeasure) *
        ((∫ y : T4, ‖greenModeFactor β₁ z y‖ ∂paperMeasure) *
          ∫ q : T4 × T4,
            ‖greenModeFactor α₂ z q.1‖ *
              ‖greenModeFactor β₂ z q.2‖
            ∂(paperMeasure.prod paperMeasure)) := by
      exact congrArg
        ((∫ x : T4, ‖greenModeFactor α₁ z x‖
          ∂paperMeasure) * ·)
        (integral_prod_mul
          (μ := paperMeasure)
          (ν := paperMeasure.prod paperMeasure)
          (fun y : T4 => ‖greenModeFactor β₁ z y‖)
          (fun q : T4 × T4 =>
            ‖greenModeFactor α₂ z q.1‖ *
              ‖greenModeFactor β₂ z q.2‖))
    _ = (∫ x : T4, ‖greenModeFactor α₁ z x‖ ∂paperMeasure) *
        ((∫ y : T4, ‖greenModeFactor β₁ z y‖ ∂paperMeasure) *
          ((∫ x : T4, ‖greenModeFactor α₂ z x‖ ∂paperMeasure) *
            ∫ y : T4, ‖greenModeFactor β₂ z y‖ ∂paperMeasure)) := by
      exact congrArg
        (fun u =>
          (∫ x : T4, ‖greenModeFactor α₁ z x‖ ∂paperMeasure) *
            ((∫ y : T4, ‖greenModeFactor β₁ z y‖
              ∂paperMeasure) * u))
        (integral_prod_mul
          (μ := paperMeasure) (ν := paperMeasure)
          (fun x : T4 => ‖greenModeFactor α₂ z x‖)
          (fun y : T4 => ‖greenModeFactor β₂ z y‖))
    _ = 1 := by
      rw [integral_norm_greenModeFactor,
        integral_norm_greenModeFactor,
        integral_norm_greenModeFactor,
        integral_norm_greenModeFactor]
      norm_num

/-- Joint measurability of the five-variable Fourier integrand. -/
theorem measurable_fourPointFourierIntegrand
    (α₁ β₁ α₂ β₂ : Z4) :
    Measurable fun q : FourPointExternal × T4 =>
      fourPointFourierIntegrand α₁ β₁ α₂ β₂ q.1 q.2 := by
  unfold fourPointFourierIntegrand
  exact
    (measurable_greenModeFactor_comp α₁
      (by fun_prop) (by fun_prop)).mul
      ((measurable_greenModeFactor_comp β₁
        (by fun_prop) (by fun_prop)).mul
        ((measurable_greenModeFactor_comp α₂
          (by fun_prop) (by fun_prop)).mul
          (measurable_greenModeFactor_comp β₂
            (by fun_prop) (by fun_prop))))

/-- The complete five-variable Fourier kernel is absolutely integrable.
This global statement is what permits the safe block Fubini swap; some
lower-dimensional pointwise sections at coincident external points are
not integrable. -/
theorem integrable_fourPointFourierIntegrand
    (α₁ β₁ α₂ β₂ : Z4) :
    Integrable
      (fun q : FourPointExternal × T4 =>
        fourPointFourierIntegrand α₁ β₁ α₂ β₂ q.1 q.2)
      (fourPointExternalMeasure.prod paperMeasure) := by
  have hswap :
      Integrable
        (fun q : T4 × FourPointExternal =>
          fourPointFourierIntegrand α₁ β₁ α₂ β₂ q.2 q.1)
        (paperMeasure.prod fourPointExternalMeasure) := by
    have hmeas :
        AEStronglyMeasurable
          (fun q : T4 × FourPointExternal =>
            fourPointFourierIntegrand α₁ β₁ α₂ β₂ q.2 q.1)
          (paperMeasure.prod fourPointExternalMeasure) := by
      have hM : Measurable fun q : T4 × FourPointExternal =>
          fourPointFourierIntegrand α₁ β₁ α₂ β₂ q.2 q.1 := by
        unfold fourPointFourierIntegrand
        exact
          (measurable_greenModeFactor_comp α₁
            (x := fun q : T4 × FourPointExternal => q.2.1)
            (z := fun q => q.1)
            (by fun_prop) (by fun_prop)).mul
            ((measurable_greenModeFactor_comp β₁
              (x := fun q : T4 × FourPointExternal => q.2.2.1)
              (z := fun q => q.1)
              (by fun_prop) (by fun_prop)).mul
              ((measurable_greenModeFactor_comp α₂
                (x := fun q : T4 × FourPointExternal => q.2.2.2.1)
                (z := fun q => q.1)
                (by fun_prop) (by fun_prop)).mul
                (measurable_greenModeFactor_comp β₂
                  (x := fun q : T4 × FourPointExternal => q.2.2.2.2)
                  (z := fun q => q.1)
                  (by fun_prop) (by fun_prop))))
      exact hM.aestronglyMeasurable
    rw [integrable_prod_iff hmeas]
    constructor
    · exact Filter.Eventually.of_forall fun z =>
        integrable_fourPointFourierIntegrand_section α₁ β₁ α₂ β₂ z
    · have hnorm :
          (fun z : T4 =>
            ∫ p : FourPointExternal,
              ‖fourPointFourierIntegrand α₁ β₁ α₂ β₂ p z‖
              ∂fourPointExternalMeasure) =
            fun _ => 1 := by
          funext z
          exact
            integral_norm_fourPointFourierIntegrand_section
              α₁ β₁ α₂ β₂ z
      rw [hnorm]
      exact integrable_const 1
  have hs := hswap.swap
  refine hs.congr ?_
  exact Filter.Eventually.of_forall fun q => by rfl

/-! ## Block Fubini and the Gram identity -/

private theorem integral_fourPointExternal_eq_iterated
    (f : FourPointExternal → ℂ)
    (hf : Integrable f fourPointExternalMeasure) :
    (∫ p : FourPointExternal, f p ∂fourPointExternalMeasure) =
      ∫ x₁ : T4, ∫ y₁ : T4, ∫ x₂ : T4, ∫ y₂ : T4,
        f (x₁, y₁, x₂, y₂)
        ∂paperMeasure ∂paperMeasure ∂paperMeasure ∂paperMeasure := by
  unfold fourPointExternalMeasure at hf ⊢
  calc
    (∫ p : FourPointExternal, f p
        ∂(paperMeasure.prod
          (paperMeasure.prod (paperMeasure.prod paperMeasure)))) =
        ∫ x₁ : T4, ∫ q : T4 × (T4 × T4),
          f (x₁, q) ∂(paperMeasure.prod (paperMeasure.prod paperMeasure))
          ∂paperMeasure :=
      integral_prod _ hf
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf.prod_right_ae] with x₁ hx₁
      calc
        (∫ q : T4 × (T4 × T4), f (x₁, q)
            ∂(paperMeasure.prod (paperMeasure.prod paperMeasure))) =
            ∫ y₁ : T4, ∫ q : T4 × T4,
              f (x₁, y₁, q)
              ∂(paperMeasure.prod paperMeasure) ∂paperMeasure :=
          integral_prod _ hx₁
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [hx₁.prod_right_ae] with y₁ hy₁
          exact integral_prod _ hy₁

/-- Integrating the external variables of the five-variable kernel
produces the product of its two mode profiles. -/
theorem integral_fourPointFourierIntegrand_external
    (α₁ β₁ α₂ β₂ : Z4) (z : T4) :
    (∫ p : FourPointExternal,
        fourPointFourierIntegrand α₁ β₁ α₂ β₂ p z
        ∂fourPointExternalMeasure) =
      fourPointModeProfile α₁ β₁ z *
        fourPointModeProfile α₂ β₂ z := by
  unfold fourPointExternalMeasure fourPointFourierIntegrand
  calc
    (∫ p : T4 × (T4 × (T4 × T4)),
        greenModeFactor α₁ z p.1 *
          (greenModeFactor β₁ z p.2.1 *
            (greenModeFactor α₂ z p.2.2.1 *
              greenModeFactor β₂ z p.2.2.2))
        ∂(paperMeasure.prod
          (paperMeasure.prod (paperMeasure.prod paperMeasure)))) =
        (∫ x : T4, greenModeFactor α₁ z x ∂paperMeasure) *
          ∫ q : T4 × (T4 × T4),
            greenModeFactor β₁ z q.1 *
              (greenModeFactor α₂ z q.2.1 *
                greenModeFactor β₂ z q.2.2)
            ∂(paperMeasure.prod (paperMeasure.prod paperMeasure)) :=
      integral_prod_mul
        (μ := paperMeasure)
        (ν := paperMeasure.prod (paperMeasure.prod paperMeasure))
        (greenModeFactor α₁ z)
        (fun q : T4 × (T4 × T4) =>
          greenModeFactor β₁ z q.1 *
            (greenModeFactor α₂ z q.2.1 *
              greenModeFactor β₂ z q.2.2))
    _ = (∫ x : T4, greenModeFactor α₁ z x ∂paperMeasure) *
        ((∫ y : T4, greenModeFactor β₁ z y ∂paperMeasure) *
          ∫ q : T4 × T4,
            greenModeFactor α₂ z q.1 *
              greenModeFactor β₂ z q.2
            ∂(paperMeasure.prod paperMeasure)) := by
      exact congrArg
        ((∫ x : T4, greenModeFactor α₁ z x
          ∂paperMeasure) * ·)
        (integral_prod_mul
          (μ := paperMeasure)
          (ν := paperMeasure.prod paperMeasure)
          (greenModeFactor β₁ z)
          (fun q : T4 × T4 =>
            greenModeFactor α₂ z q.1 *
              greenModeFactor β₂ z q.2))
    _ = (∫ x : T4, greenModeFactor α₁ z x ∂paperMeasure) *
        ((∫ y : T4, greenModeFactor β₁ z y ∂paperMeasure) *
          ((∫ x : T4, greenModeFactor α₂ z x ∂paperMeasure) *
            ∫ y : T4, greenModeFactor β₂ z y ∂paperMeasure)) := by
      exact congrArg
        (fun u =>
          (∫ x : T4, greenModeFactor α₁ z x ∂paperMeasure) *
            ((∫ y : T4, greenModeFactor β₁ z y
              ∂paperMeasure) * u))
        (integral_prod_mul
          (μ := paperMeasure) (ν := paperMeasure)
          (greenModeFactor α₂ z) (greenModeFactor β₂ z))
    _ = translatedGreenMode α₁ z *
          (translatedGreenMode β₁ z *
            (translatedGreenMode α₂ z *
              translatedGreenMode β₂ z)) := by
      rfl
    _ = fourPointModeProfile α₁ β₁ z *
        fourPointModeProfile α₂ β₂ z := by
      rw [fourPointModeProfile_eq_mul_translated,
        fourPointModeProfile_eq_mul_translated]
      ring

private theorem fourPointCoeffIntegrand_eq
    (α₁ β₁ α₂ β₂ : Z4) (x₁ y₁ x₂ y₂ : T4) :
    charT4 α₁ x₁ * charT4 β₁ y₁ *
        charT4 α₂ x₂ * charT4 β₂ y₂ *
        (fourPointH x₁ y₁ x₂ y₂ : ℂ) =
      ∫ z : T4,
        fourPointFourierIntegrand α₁ β₁ α₂ β₂
          (x₁, y₁, x₂, y₂) z
        ∂paperMeasure := by
  unfold fourPointH
  rw [← integral_complex_ofReal, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    unfold fourPointFourierIntegrand greenModeFactor
    push_cast
    ring

/-- **Gram bridge for `D-limit`.**  The four-point Fourier coefficient
is the bilinear Gram integral of the two mode profiles. -/
theorem fourPointHCoeff_eq_profileGram
    (α₁ β₁ α₂ β₂ : Z4) :
    fourPointHCoeff α₁ β₁ α₂ β₂ =
      ∫ z : T4,
        fourPointModeProfile α₁ β₁ z *
          fourPointModeProfile α₂ β₂ z
        ∂paperMeasure := by
  have hjoint :=
    integrable_fourPointFourierIntegrand α₁ β₁ α₂ β₂
  have hexternal :
      Integrable
        (fun p : FourPointExternal =>
          ∫ z : T4,
            fourPointFourierIntegrand α₁ β₁ α₂ β₂ p z
            ∂paperMeasure)
        fourPointExternalMeasure :=
    hjoint.integral_prod_left
  calc
    fourPointHCoeff α₁ β₁ α₂ β₂ =
        ∫ x₁ : T4, ∫ y₁ : T4, ∫ x₂ : T4, ∫ y₂ : T4,
          ∫ z : T4,
            fourPointFourierIntegrand α₁ β₁ α₂ β₂
              (x₁, y₁, x₂, y₂) z
            ∂paperMeasure
          ∂paperMeasure ∂paperMeasure ∂paperMeasure ∂paperMeasure := by
      unfold fourPointHCoeff
      simp_rw [fourPointCoeffIntegrand_eq]
    _ = ∫ p : FourPointExternal,
          ∫ z : T4,
            fourPointFourierIntegrand α₁ β₁ α₂ β₂ p z
            ∂paperMeasure
          ∂fourPointExternalMeasure :=
      (integral_fourPointExternal_eq_iterated _ hexternal).symm
    _ = ∫ z : T4,
          ∫ p : FourPointExternal,
            fourPointFourierIntegrand α₁ β₁ α₂ β₂ p z
            ∂fourPointExternalMeasure
          ∂paperMeasure :=
      integral_integral_swap hjoint
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z =>
        integral_fourPointFourierIntegrand_external
          α₁ β₁ α₂ β₂ z

/-! ## Hermitian and explicit Fourier forms -/

/-- The real nonnegative Fourier multiplier of one Green leg. -/
def greenModeWeight (k : Z4) : ℝ :=
  (1 + ∑ i, (k i : ℝ) ^ 2)⁻¹

theorem greenModeWeight_nonneg (k : Z4) :
    0 ≤ greenModeWeight k := by
  unfold greenModeWeight
  positivity

@[simp]
theorem greenModeWeight_neg (k : Z4) :
    greenModeWeight (-k) = greenModeWeight k := by
  unfold greenModeWeight
  congr 2
  apply Finset.sum_congr rfl
  intro i _hi
  simp

/-- Compact character presentation of the two-leg profile. -/
theorem fourPointModeProfile_eq_character
    (α β : Z4) (z : T4) :
    fourPointModeProfile α β z =
      ((greenModeWeight α * greenModeWeight β : ℝ) : ℂ) *
        charT4 (α + β) z := by
  rw [fourPointModeProfile_eq, charT4_add]
  unfold greenModeWeight
  push_cast
  ring

/-- Negating both modes conjugates the profile. -/
theorem fourPointModeProfile_neg
    (α β : Z4) (z : T4) :
    fourPointModeProfile (-α) (-β) z =
      conj (fourPointModeProfile α β z) := by
  rw [fourPointModeProfile_eq_character,
    fourPointModeProfile_eq_character]
  rw [greenModeWeight_neg, greenModeWeight_neg]
  have hneg : -α + -β = -(α + β) := by
    abel
  rw [hneg, charT4_neg, map_mul, Complex.conj_ofReal]

/-- Hermitian Gram form obtained by negating the modes of the second
profile.  This is the form directly consumed by covariance PSD proofs. -/
theorem fourPointHCoeff_neg_eq_profileInner
    (α₁ β₁ α₂ β₂ : Z4) :
    fourPointHCoeff α₁ β₁ (-α₂) (-β₂) =
      ∫ z : T4,
        fourPointModeProfile α₁ β₁ z *
          conj (fourPointModeProfile α₂ β₂ z)
        ∂paperMeasure := by
  rw [fourPointHCoeff_eq_profileGram]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change
      fourPointModeProfile α₁ β₁ z *
          fourPointModeProfile (-α₂) (-β₂) z =
        fourPointModeProfile α₁ β₁ z *
          conj (fourPointModeProfile α₂ β₂ z)
    rw [fourPointModeProfile_neg]

/-- Paper-normalized integral of one product character. -/
theorem integral_charT4_paper (k : Z4) :
    ∫ z : T4, charT4 k z ∂paperMeasure =
      if k = 0 then (((2 * Real.pi) ^ dim : ℝ) : ℂ) else 0 := by
  have h := paperFourierCoeff_char (0 : Z4) k
  unfold paperFourierCoeff at h
  simpa only [charT4_zero, one_mul, neg_zero] using h

/-- Fully explicit four-point Fourier coefficient.  Frequency is
conserved at the common contraction point, and the remaining factor is
the product of the four Green multipliers. -/
theorem fourPointHCoeff_eq_indicator
    (α₁ β₁ α₂ β₂ : Z4) :
    fourPointHCoeff α₁ β₁ α₂ β₂ =
      if α₁ + β₁ + (α₂ + β₂) = 0 then
        (((2 * Real.pi) ^ dim : ℝ) : ℂ) *
          ((greenModeWeight α₁ * greenModeWeight β₁ *
            greenModeWeight α₂ * greenModeWeight β₂ : ℝ) : ℂ)
      else 0 := by
  rw [fourPointHCoeff_eq_profileGram]
  simp_rw [fourPointModeProfile_eq_character]
  calc
    (∫ z : T4,
        (((greenModeWeight α₁ * greenModeWeight β₁ : ℝ) : ℂ) *
            charT4 (α₁ + β₁) z) *
          (((greenModeWeight α₂ * greenModeWeight β₂ : ℝ) : ℂ) *
            charT4 (α₂ + β₂) z)
        ∂paperMeasure) =
        (((greenModeWeight α₁ * greenModeWeight β₁ *
          greenModeWeight α₂ * greenModeWeight β₂ : ℝ) : ℂ)) *
          ∫ z : T4,
            charT4 (α₁ + β₁ + (α₂ + β₂)) z
            ∂paperMeasure := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change
          (((greenModeWeight α₁ * greenModeWeight β₁ : ℝ) : ℂ) *
              charT4 (α₁ + β₁) z) *
            (((greenModeWeight α₂ * greenModeWeight β₂ : ℝ) : ℂ) *
              charT4 (α₂ + β₂) z) =
            (((greenModeWeight α₁ * greenModeWeight β₁ *
              greenModeWeight α₂ * greenModeWeight β₂ : ℝ) : ℂ)) *
              charT4 (α₁ + β₁ + (α₂ + β₂)) z
        rw [charT4_add (α₁ + β₁) (α₂ + β₂) z]
        push_cast
        ring
    _ = _ := by
      rw [integral_charT4_paper]
      split_ifs
      · push_cast
        ring
      · simp

/-! ## Finite Gram quadratic forms -/

/-- Finite linear combination of two-leg mode profiles. -/
def fourPointProfileCombination {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) (z : T4) : ℂ :=
  ∑ i, c i *
    fourPointModeProfile (modes i).1 (modes i).2 z

theorem continuous_fourPointModeProfile (α β : Z4) :
    Continuous (fourPointModeProfile α β) := by
  have hfun :
      fourPointModeProfile α β =
        fun z =>
          ((greenModeWeight α * greenModeWeight β : ℝ) : ℂ) *
            charT4 (α + β) z := by
    funext z
    exact fourPointModeProfile_eq_character α β z
  rw [hfun]
  exact continuous_const.mul (continuous_charT4 (α + β))

theorem continuous_fourPointProfileCombination {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    Continuous (fourPointProfileCombination modes c) := by
  unfold fourPointProfileCombination
  apply continuous_finsetSum
  intro i _hi
  exact continuous_const.mul
    (continuous_fourPointModeProfile
      (modes i).1 (modes i).2)

theorem integrable_fourPointProfileCombination_mul_conj {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    Integrable
      (fun z =>
        fourPointProfileCombination modes c z *
          conj (fourPointProfileCombination modes c z))
      paperMeasure := by
  have hcont :
      Continuous
        (fun z =>
          fourPointProfileCombination modes c z *
            conj (fourPointProfileCombination modes c z)) :=
    (continuous_fourPointProfileCombination modes c).mul
      (continuous_fourPointProfileCombination modes c).star
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Finite Hermitian covariance quadratic form equals the squared
`L²` norm of the corresponding profile combination. -/
theorem sum_fourPointHCoeff_neg_eq_profileCombination
    {s : ℕ} (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    (∑ i, ∑ j,
      c i * conj (c j) *
        fourPointHCoeff
          (modes i).1 (modes i).2
          (-(modes j).1) (-(modes j).2)) =
      ∫ z : T4,
        fourPointProfileCombination modes c z *
          conj (fourPointProfileCombination modes c z)
        ∂paperMeasure := by
  have hterm : ∀ i j : Fin s,
      Integrable
        (fun z =>
          (c i *
            fourPointModeProfile (modes i).1 (modes i).2 z) *
          (conj (c j) *
            conj (fourPointModeProfile
              (modes j).1 (modes j).2 z)))
        paperMeasure := by
    intro i j
    have hcont :
        Continuous
          (fun z =>
            (c i *
              fourPointModeProfile (modes i).1 (modes i).2 z) *
            (conj (c j) *
              conj (fourPointModeProfile
                (modes j).1 (modes j).2 z))) :=
      (continuous_const.mul
        (continuous_fourPointModeProfile
          (modes i).1 (modes i).2)).mul
        (continuous_const.mul
          (continuous_fourPointModeProfile
            (modes j).1 (modes j).2).star)
    exact hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∑ i, ∑ j,
        c i * conj (c j) *
          fourPointHCoeff
            (modes i).1 (modes i).2
            (-(modes j).1) (-(modes j).2)) =
        ∑ i, ∑ j,
          ∫ z : T4,
            (c i *
              fourPointModeProfile (modes i).1 (modes i).2 z) *
            (conj (c j) *
              conj (fourPointModeProfile
                (modes j).1 (modes j).2 z))
            ∂paperMeasure := by
      apply Fintype.sum_congr
      intro i
      apply Fintype.sum_congr
      intro j
      rw [fourPointHCoeff_neg_eq_profileInner,
        ← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
    _ = ∫ z : T4,
        ∑ i, ∑ j,
          (c i *
            fourPointModeProfile (modes i).1 (modes i).2 z) *
          (conj (c j) *
            conj (fourPointModeProfile
              (modes j).1 (modes j).2 z))
        ∂paperMeasure := by
      symm
      rw [integral_finsetSum]
      · apply Fintype.sum_congr
        intro i
        rw [integral_finsetSum]
        intro j _hj
        exact hterm i j
      · intro i _hi
        exact integrable_finsetSum _ fun j _hj => hterm i j
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        unfold fourPointProfileCombination
        simp only [map_sum, map_mul]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]

/-- The finite Hermitian four-point covariance form is positive
semidefinite. -/
theorem sum_fourPointHCoeff_neg_re_nonneg
    {s : ℕ} (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    0 ≤
      (∑ i, ∑ j,
        c i * conj (c j) *
          fourPointHCoeff
            (modes i).1 (modes i).2
            (-(modes j).1) (-(modes j).2)).re := by
  rw [sum_fourPointHCoeff_neg_eq_profileCombination]
  have hint :=
    integrable_fourPointProfileCombination_mul_conj modes c
  calc
    0 ≤ ∫ z : T4,
        (fourPointProfileCombination modes c z *
          conj (fourPointProfileCombination modes c z)).re
        ∂paperMeasure := by
      apply integral_nonneg
      intro z
      change
        0 ≤ (fourPointProfileCombination modes c z *
          conj (fourPointProfileCombination modes c z)).re
      rw [Complex.mul_conj]
      exact Complex.normSq_nonneg _
    _ = (∫ z : T4,
        fourPointProfileCombination modes c z *
          conj (fourPointProfileCombination modes c z)
        ∂paperMeasure).re :=
      integral_re hint

end

end Anderson4D
