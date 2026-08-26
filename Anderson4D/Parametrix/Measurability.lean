import Anderson4D.Parametrix.Random
import Anderson4D.Probability.NoiseRegularity
import Anderson4D.Continuum.FourPointFourier
import Anderson4D.DetParametrix.Core.MeasurableAssembly
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Measurability of random parametrix coefficients

The coefficient-level resolvent route uses totalized Bochner integrals
and `tsum`.  This file proves that these totalizations remain measurable
in the noise sample.  In particular, no measurability is hidden in the
good-event replacement step.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- The random multiplication potential is jointly measurable in the
sample and spatial point. -/
theorem NoiseModel.measurable_multFun_joint
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) :
    Measurable fun p : M.Ω × T4 =>
      multFun M ρ lam ε p.2 p.1 := by
  unfold multFun
  exact
    (measurable_const.mul
      (M.measurable_xiEps_joint ρ ε)).sub
      measurable_const

/-- The unintegrated coefficient-chain integrand. -/
def neumannRawIntegrand
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ)
    (α β : Z4) (ω : M.Ω) (x y : T4)
    (v : Fin n → T4) : ℂ :=
  charT4 α x * charT4 β y *
    (((∏ e : Fin (n + 1),
        greenFn
          ((assemble x y v) e.castSucc -
            (assemble x y v) e.succ)) *
      ∏ i, multFun M ρ lam ε (v i) ω : ℝ) : ℂ)

/-- Joint measurability of the complete unintegrated Neumann
coefficient chain. -/
theorem measurable_neumannRawIntegrand
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ)
    (α β : Z4) :
    Measurable fun p :
        (((M.Ω × T4) × T4) × (Fin n → T4)) =>
      neumannRawIntegrand M ρ lam ε n α β
        p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  have hω :
      Measurable fun p :
          (((M.Ω × T4) × T4) × (Fin n → T4)) =>
        p.1.1.1 :=
    measurable_fst.comp
      (measurable_fst.comp measurable_fst)
  have hx :
      Measurable fun p :
          (((M.Ω × T4) × T4) × (Fin n → T4)) =>
        p.1.1.2 :=
    measurable_snd.comp
      (measurable_fst.comp measurable_fst)
  have hy :
      Measurable fun p :
          (((M.Ω × T4) × T4) × (Fin n → T4)) =>
        p.1.2 :=
    measurable_snd.comp measurable_fst
  have hassemble :
      Measurable fun p :
          (((M.Ω × T4) × T4) × (Fin n → T4)) =>
        assemble p.1.1.2 p.1.2 p.2 :=
    (measurable_assemble_prod n).comp
      (hx.prodMk (hy.prodMk measurable_snd))
  have hgreen :
      Measurable fun p :
          (((M.Ω × T4) × T4) × (Fin n → T4)) =>
        ∏ e : Fin (n + 1),
          greenFn
            ((assemble p.1.1.2 p.1.2 p.2) e.castSucc -
              (assemble p.1.1.2 p.1.2 p.2) e.succ) := by
    apply Finset.measurable_prod
    intro e he
    exact measurable_greenFn.comp
      (((measurable_pi_apply e.castSucc).comp hassemble).sub
        ((measurable_pi_apply e.succ).comp hassemble))
  have hmult :
      Measurable fun p :
          (((M.Ω × T4) × T4) × (Fin n → T4)) =>
        ∏ i, multFun M ρ lam ε (p.2 i) p.1.1.1 := by
    apply Finset.measurable_prod
    intro i hi
    have hv :
        Measurable fun p :
            (((M.Ω × T4) × T4) × (Fin n → T4)) =>
          p.2 i :=
      (measurable_pi_apply i).comp measurable_snd
    unfold multFun
    exact
      (measurable_const.mul
        ((M.measurable_xiEps_joint ρ ε).comp
          (hω.prodMk hv))).sub
        measurable_const
  unfold neumannRawIntegrand
  exact
    (((continuous_charT4 α).measurable.comp
      hx).mul
      ((continuous_charT4 β).measurable.comp
        hy)).mul
      (Complex.measurable_ofReal.comp (hgreen.mul hmult))

/-- Each totalized Neumann coefficient is measurable in the noise
sample. -/
theorem measurable_neumannCoeff
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ)
    (α β : Z4) :
    Measurable (neumannCoeff M ρ lam ε n α β) := by
  let V := Fin n → T4
  have hraw :=
    measurable_neumannRawIntegrand M ρ lam ε n α β
  have hrawV :
      StronglyMeasurable fun p :
          (((M.Ω × T4) × T4) × V) =>
        neumannRawIntegrand M ρ lam ε n α β
          p.1.1.1 p.1.1.2 p.1.2 p.2 := by
    exact hraw.stronglyMeasurable
  have hintV :
      StronglyMeasurable fun p : (M.Ω × T4) × T4 =>
        ∫ v : V,
          neumannRawIntegrand M ρ lam ε n α β
            p.1.1 p.1.2 p.2 v
          ∂(Measure.pi fun _ => paperMeasure) :=
    hrawV.integral_prod_right
  have hrawY :
      StronglyMeasurable fun p : (M.Ω × T4) × T4 =>
        ∫ v : V,
          neumannRawIntegrand M ρ lam ε n α β
            p.1.1 p.1.2 p.2 v
          ∂(Measure.pi fun _ => paperMeasure) := by
    exact hintV
  have hintY :
      StronglyMeasurable fun p : M.Ω × T4 =>
        ∫ y : T4, ∫ v : V,
          neumannRawIntegrand M ρ lam ε n α β
            p.1 p.2 y v
          ∂(Measure.pi fun _ => paperMeasure)
          ∂paperMeasure :=
    hrawY.integral_prod_right
  have hrawX :
      StronglyMeasurable fun p : M.Ω × T4 =>
        ∫ y : T4, ∫ v : V,
          neumannRawIntegrand M ρ lam ε n α β
            p.1 p.2 y v
          ∂(Measure.pi fun _ => paperMeasure)
          ∂paperMeasure :=
    hintY
  have hintX :
      StronglyMeasurable fun ω : M.Ω =>
        ∫ x : T4, ∫ y : T4, ∫ v : V,
          neumannRawIntegrand M ρ lam ε n α β
            ω x y v
          ∂(Measure.pi fun _ => paperMeasure)
          ∂paperMeasure ∂paperMeasure :=
    hrawX.integral_prod_right
  exact hintX.measurable

/-- The totalized Neumann tail is measurable. -/
theorem measurable_modeHcoeff
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (α β : Z4) :
    Measurable (modeHcoeff M ρ lam ε α β) := by
  unfold modeHcoeff
  exact
    (Measurable.tsum fun n =>
      measurable_neumannCoeff M ρ lam ε (n + 1) α β).const_smul
        (lamEps lam ε)⁻¹

end

end Anderson4D
