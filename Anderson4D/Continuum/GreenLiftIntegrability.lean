import Anderson4D.Continuum.FourPointFourier

/-!
# Haar-product integrability for one lifted Green edge

This deterministic helper adjoins one translated Green edge to an integrable
function on an arbitrary `SFinite` measure space.  It is the common induction
step for both deterministic increasing Green trees and random-parametrix
Green paths, so it lives below both layers.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

private theorem integrable_greenFn_complex_lift :
    Integrable (fun z : T4 => (greenFn z : ℂ)) paperMeasure :=
  integrable_greenFn_paper.ofReal

/-- Multiplying an integrable function by a translated Green kernel in a
new Haar variable preserves joint integrability.  The translation may
depend measurably on all old variables. -/
theorem integrable_greenFn_sub_mul_lift
    {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} [SFinite ν]
    (f : Y → ℂ) (shift : Y → T4)
    (hf : Integrable f ν) (hshift : Measurable shift) :
    Integrable
      (fun p : T4 × Y =>
        (greenFn (p.1 - shift p.2) : ℂ) * f p.2)
      (paperMeasure.prod ν) := by
  let Gnorm : T4 → ℝ :=
    fun z => ‖(greenFn z : ℂ)‖
  have hGnorm : Integrable Gnorm paperMeasure :=
    integrable_greenFn_complex_lift.norm
  have hgreenMeas :
      AEStronglyMeasurable
        (fun p : T4 × Y =>
          (greenFn (p.1 - shift p.2) : ℂ))
        (paperMeasure.prod ν) :=
    Measurable.aestronglyMeasurable
      ((measurable_greenFn.comp
        (measurable_fst.sub
          (hshift.comp measurable_snd))).complex_ofReal)
  have hfLift :
      AEStronglyMeasurable
        (fun p : T4 × Y => f p.2)
        (paperMeasure.prod ν) :=
    hf.aestronglyMeasurable.comp_snd
  have hjoint :
      AEStronglyMeasurable
        (fun p : T4 × Y =>
          (greenFn (p.1 - shift p.2) : ℂ) * f p.2)
        (paperMeasure.prod ν) :=
    hgreenMeas.mul hfLift
  rw [integrable_prod_iff' hjoint]
  constructor
  · filter_upwards with y
    have htranslated :
        Integrable
          (fun x : T4 =>
            (greenFn (x - shift y) : ℂ))
          paperMeasure :=
      ((measurePreserving_sub_paper (shift y)).integrable_comp
        integrable_greenFn_complex_lift.aestronglyMeasurable).mpr
          integrable_greenFn_complex_lift
    exact htranslated.mul_const (f y)
  · have hnormIntegral (y : Y) :
        (∫ x : T4,
            ‖(greenFn (x - shift y) : ℂ) * f y‖
            ∂paperMeasure) =
          (∫ x : T4, Gnorm x ∂paperMeasure) * ‖f y‖ := by
      calc
        (∫ x : T4,
            ‖(greenFn (x - shift y) : ℂ) * f y‖
            ∂paperMeasure) =
            ∫ x : T4,
              Gnorm (x - shift y) * ‖f y‖
              ∂paperMeasure := by
                apply integral_congr_ae
                filter_upwards with x
                simp only [norm_mul, Gnorm]
        _ =
            (∫ x : T4, Gnorm (x - shift y)
              ∂paperMeasure) * ‖f y‖ := by
                rw [integral_mul_const]
        _ =
            (∫ x : T4, Gnorm x ∂paperMeasure) * ‖f y‖ := by
                have hp :
                    MeasurePreserving
                      (MeasurableEquiv.subRight (shift y))
                      paperMeasure paperMeasure :=
                  (measurePreserving_sub_paper (shift y)).congr
                    (MeasurableEquiv.subRight
                      (shift y)).measurable
                    (Filter.Eventually.of_forall fun _ => rfl)
                have hpi := hp.integral_comp' Gnorm
                change
                  (∫ x : T4, Gnorm (x - shift y)
                    ∂paperMeasure) =
                    ∫ x : T4, Gnorm x ∂paperMeasure at hpi
                rw [hpi]
    convert
      hf.norm.const_mul
        (∫ x : T4, Gnorm x ∂paperMeasure) using 1
    funext y
    exact hnormIntegral y

end

end Anderson4D
