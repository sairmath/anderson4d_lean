import Anderson4D.DetParametrix.Core.MomentReduction
import Anderson4D.Continuum.CriticalLogWeight

/-!
# Haar reindexing for the proper R-324 convolution

The proper cross-block estimate contains two surviving inverse-square
connector edges and one translation-invariant inserted kernel.  This file
performs the exact product-Haar shear that exposes the binary convolution
of the two connector edges.  No inequality is used here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- Product-space integrand with a generic kernel on the endpoint
difference. -/
def r324KernelTriple
    (q : T4 → ℝ) (u v : T4)
    (p : T4 × T4) : ℝ :=
  invSqKer (u - p.1) * q (p.1 - p.2) *
    invSqKer (p.2 - v)

private def r324AddProdMeasurableEquiv :
    T4 × T4 ≃ᵐ T4 × T4 :=
  (MeasurableEquiv.prodComm :
      T4 × T4 ≃ᵐ T4 × T4).trans
    ((MeasurableEquiv.shearAddRight T4).trans
      (MeasurableEquiv.prodComm :
        T4 × T4 ≃ᵐ T4 × T4))

private def r324KernelTripleShearMeasurableEquiv
    (v : T4) :
    T4 × T4 ≃ᵐ T4 × T4 :=
  (MeasurableEquiv.prodCongr
    (MeasurableEquiv.refl T4)
    (MeasurableEquiv.addRight v)).trans
      r324AddProdMeasurableEquiv

@[simp]
private theorem r324KernelTripleShearMeasurableEquiv_apply
    (v : T4) (p : T4 × T4) :
    r324KernelTripleShearMeasurableEquiv v p =
      (p.1 + (p.2 + v), p.2 + v) := by
  unfold r324KernelTripleShearMeasurableEquiv
    r324AddProdMeasurableEquiv
  change
    (p.2 + v + p.1, p.2 + v) =
      (p.1 + (p.2 + v), p.2 + v)
  rw [add_comm]

/-- The affine shear `(h,z) ↦ (h+z+v,z+v)` preserves product Haar
measure.  In these coordinates `h` is the inserted endpoint difference
and `z` is the right connector displacement. -/
theorem measurePreserving_r324KernelTripleShear
    (v : T4) :
    MeasurePreserving
      (r324KernelTripleShearMeasurableEquiv v)
      (paperMeasure.prod paperMeasure)
      (paperMeasure.prod paperMeasure) := by
  have htranslate :
      MeasurePreserving
        (fun p : T4 × T4 => (p.1, p.2 + v))
        (paperMeasure.prod paperMeasure)
        (paperMeasure.prod paperMeasure) := by
    rw [paperMeasure_eq_volume]
    exact
      (MeasurePreserving.id (volume : Measure T4)).prod
        (measurePreserving_add_right
          (volume : Measure T4) v)
  have hshear :
      MeasurePreserving
        (fun p : T4 × T4 => (p.1 + p.2, p.2))
        (paperMeasure.prod paperMeasure)
        (paperMeasure.prod paperMeasure) := by
    rw [paperMeasure_eq_volume]
    exact
      measurePreserving_add_prod
        (μ := (volume : Measure T4))
        (ν := (volume : Measure T4))
  have hfun :
      (r324KernelTripleShearMeasurableEquiv v :
        T4 × T4 → T4 × T4) =
        fun p => (p.1 + (p.2 + v), p.2 + v) := by
    funext p
    exact
      r324KernelTripleShearMeasurableEquiv_apply v p
  rw [hfun]
  exact hshear.comp htranslate

theorem r324KernelTriple_shear
    (q : T4 → ℝ) (u v h z : T4) :
    r324KernelTriple q u v
        (h + (z + v), z + v) =
      q h *
        (invSqKer ((u - v - h) - z) * invSqKer z) := by
  unfold r324KernelTriple
  have hleft :
      u - (h + (z + v)) =
        (u - v - h) - z := by
    abel
  rw [hleft]
  simp only [add_sub_cancel_right]
  ring

theorem integrable_r324KernelTriple_shear
    (q : T4 → ℝ) (u v : T4)
    (hint :
      Integrable (r324KernelTriple q u v)
        (paperMeasure.prod paperMeasure)) :
    Integrable
      (fun p : T4 × T4 =>
        r324KernelTriple q u v
          (p.1 + (p.2 + v), p.2 + v))
      (paperMeasure.prod paperMeasure) := by
  have hp :=
    measurePreserving_r324KernelTripleShear v
  have hcomp :=
    (hp.integrable_comp
      hint.aestronglyMeasurable).mpr hint
  convert hcomp using 1
  funext p
  rw [Function.comp_apply,
    r324KernelTripleShearMeasurableEquiv_apply]

theorem integral_r324KernelTriple_eq_sheared
    (q : T4 → ℝ) (u v : T4) :
    (∫ p, r324KernelTriple q u v p
        ∂(paperMeasure.prod paperMeasure)) =
      ∫ p,
        r324KernelTriple q u v
          (p.1 + (p.2 + v), p.2 + v)
        ∂(paperMeasure.prod paperMeasure) := by
  have h :=
    (measurePreserving_r324KernelTripleShear v).integral_comp'
      (r324KernelTriple q u v)
  simpa only [r324KernelTripleShearMeasurableEquiv_apply]
    using h.symm

theorem integral_r324KernelTriple_sheared_eq_iterated
    (q : T4 → ℝ) (u v : T4)
    (hint :
      Integrable (r324KernelTriple q u v)
        (paperMeasure.prod paperMeasure)) :
    (∫ p,
      r324KernelTriple q u v
        (p.1 + (p.2 + v), p.2 + v)
      ∂(paperMeasure.prod paperMeasure)) =
      ∫ h, ∫ z,
        r324KernelTriple q u v
          (h + (z + v), z + v)
        ∂paperMeasure ∂paperMeasure := by
  exact integral_prod _
    (integrable_r324KernelTriple_shear q u v hint)

theorem integral_r324KernelTriple_shear_section_eq_weightedBinary
    (q : T4 → ℝ) (u v h : T4) :
    (∫ z,
      r324KernelTriple q u v
        (h + (z + v), z + v)
      ∂paperMeasure) =
      q h *
        (∫ z,
          invSqKer ((u - v - h) - z) * invSqKer z
          ∂paperMeasure) := by
  calc
    (∫ z,
      r324KernelTriple q u v
        (h + (z + v), z + v)
      ∂paperMeasure) =
        ∫ z, q h *
          (invSqKer ((u - v - h) - z) * invSqKer z)
          ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with z
      exact r324KernelTriple_shear q u v h z
    _ =
        q h *
          (∫ z,
            invSqKer ((u - v - h) - z) * invSqKer z
            ∂paperMeasure) := by
      rw [integral_const_mul]

theorem integrable_r324KernelTriple_weightedBinary
    (q : T4 → ℝ) (u v : T4)
    (hint :
      Integrable (r324KernelTriple q u v)
        (paperMeasure.prod paperMeasure)) :
    Integrable
      (fun h => q h *
        (∫ z,
          invSqKer ((u - v - h) - z) * invSqKer z
          ∂paperMeasure))
      paperMeasure := by
  have hout :=
    (integrable_r324KernelTriple_shear q u v hint).integral_prod_left
  apply hout.congr
  filter_upwards with h
  exact
    integral_r324KernelTriple_shear_section_eq_weightedBinary
      q u v h

theorem integral_r324KernelTriple_iterated_eq_weightedBinary
    (q : T4 → ℝ) (u v : T4) :
    (∫ h, ∫ z,
      r324KernelTriple q u v
        (h + (z + v), z + v)
      ∂paperMeasure ∂paperMeasure) =
      ∫ h, q h *
        (∫ z,
          invSqKer ((u - v - h) - z) * invSqKer z
          ∂paperMeasure)
        ∂paperMeasure := by
  apply integral_congr_ae
  filter_upwards with h
  exact
    integral_r324KernelTriple_shear_section_eq_weightedBinary
      q u v h

/-- Exact Fubini form after the product-Haar shear.  The right-hand side
is the inserted kernel averaged against the binary inverse-square
convolution at `u-v-h`. -/
theorem integral_r324KernelTriple_eq_weightedBinary
    (q : T4 → ℝ) (u v : T4)
    (hint :
      Integrable (r324KernelTriple q u v)
        (paperMeasure.prod paperMeasure)) :
    (∫ p, r324KernelTriple q u v p
        ∂(paperMeasure.prod paperMeasure)) =
      ∫ h, q h *
        (∫ z,
          invSqKer ((u - v - h) - z) * invSqKer z
          ∂paperMeasure)
        ∂paperMeasure := by
  calc
    (∫ p, r324KernelTriple q u v p
        ∂(paperMeasure.prod paperMeasure)) =
        ∫ p, r324KernelTriple q u v
          (p.1 + (p.2 + v), p.2 + v)
          ∂(paperMeasure.prod paperMeasure) :=
      integral_r324KernelTriple_eq_sheared q u v
    _ =
        ∫ h, ∫ z,
          r324KernelTriple q u v
            (h + (z + v), z + v)
          ∂paperMeasure ∂paperMeasure :=
      integral_r324KernelTriple_sheared_eq_iterated
        q u v hint
    _ =
        ∫ h, q h *
          (∫ z,
            invSqKer ((u - v - h) - z) * invSqKer z
            ∂paperMeasure)
          ∂paperMeasure :=
      integral_r324KernelTriple_iterated_eq_weightedBinary
        q u v

end

end Anderson4D
