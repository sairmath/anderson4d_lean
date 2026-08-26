import Anderson4D.DetParametrix.Paper41_Renorm.R322SelectorFubiniClosure

/-!
# One-selected-block Fubini closure for R-322

This file isolates the signed Fubini step used when the deterministic
smallest-leftmost selector removes one proper primitive block.  The first
checkpoint is the exact product-measure reindex: selected coordinates are
integrated on the inside and all complement coordinates remain on the
outside.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- Exact signed Fubini reindex for one selected finite coordinate block.

The measurable equivalence remembers both pieces of the original tuple, so
the integrand is not replaced by an absolute-value majorant.  The selected
coordinates occur in the inner integral, as required by the inside-to-outside
collapse in paper Section 4.1. -/
theorem integral_pi_eq_integral_complement_integral_selected
    {ι X : Type*} [Fintype ι]
    [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ]
    (selected : ι → Prop) [DecidablePred selected]
    (f : (ι → X) → ℝ)
    (hf :
      Integrable f
        (Measure.pi fun _ : ι => μ)) :
    (∫ x, f x ∂Measure.pi fun _ : ι => μ) =
      ∫ xC : (i : {i : ι // ¬ selected i}) → X,
        ∫ xB : (i : {i : ι // selected i}) → X,
          f
            ((MeasurableEquiv.piEquivPiSubtypeProd
                (fun _ : ι => X) selected).symm
              (xB, xC))
          ∂Measure.pi fun _ : {i : ι // selected i} => μ
        ∂Measure.pi fun _ : {i : ι // ¬ selected i} => μ := by
  let e :=
    MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : ι => X) selected
  let μB : Measure ((i : {i : ι // selected i}) → X) :=
    Measure.pi fun _ : {i : ι // selected i} => μ
  let μC : Measure ((i : {i : ι // ¬ selected i}) → X) :=
    Measure.pi fun _ : {i : ι // ¬ selected i} => μ
  have hpres :
      MeasurePreserving e
        (Measure.pi fun _ : ι => μ)
        (μB.prod μC) := by
    exact
      measurePreserving_piEquivPiSubtypeProd
        (fun _ : ι => μ) selected
  have hsplit :
      Integrable (fun x => f (e.symm x))
        (μB.prod μC) := by
    have hiff :=
      hpres.symm.integrable_comp_emb
        e.symm.measurableEmbedding
        (g := f)
    change Integrable (f ∘ e.symm) (μB.prod μC)
    exact hiff.mpr hf
  calc
    (∫ x, f x ∂Measure.pi fun _ : ι => μ) =
        ∫ x, f (e.symm x) ∂μB.prod μC := by
          symm
          simpa only [Function.comp_apply] using
            hpres.symm.integral_comp' f
    _ =
        ∫ xC, ∫ xB, f (e.symm (xB, xC)) ∂μB
          ∂μC :=
      integral_prod_symm _ hsplit

end

end Anderson4D
