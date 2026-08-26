import Anderson4D.DetParametrix.Core.ReductionPrimitive

/-!
# One concrete proper-block collapse for R-322

Paper: R-322 — §4.1 (4.8) — one proper-block collapse

This file formalizes the analytic operation in paper (4.7)--(4.8).  A
primitive block with profile `J` sits between a left input `Gp` and the
endpoint difference of a right input `Gr`.  Integrating the two block
endpoints produces a new one-variable input kernel.

The construction below is concrete: it is the nested Bochner integral from
(4.8), not an output predicate.  We prove

* equality with the difference form of the renormalization step;
* equality with raw insertion minus its scalar counterterm under the exact
  Fubini/integrability hypotheses already isolated for Proposition 3.2;
* a product-measure Fubini form;
* preservation of the hyperoctahedral class `E`.

The pointwise `|z|⁻²` estimate is a separate quantitative step: it combines
Proposition 4.1 with the three regions (4.10)--(4.12).
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- The two-variable integrand in paper (4.8), after translating the right
external endpoint to zero. -/
def r322CollapseIntegrand
    (Gp J Gr : T4 → ℝ) (u : T4) (p : T4 × T4) : ℝ :=
  Gp (u - p.1) * J (p.1 - p.2) * (Gr p.2 - Gr p.1)

/-- One concrete proper-block collapse, paper (4.8). -/
def r322Collapse (Gp J Gr : T4 → ℝ) (u : T4) : ℝ :=
  ∫ p, r322CollapseIntegrand Gp J Gr u p
    ∂(paperMeasure.prod paperMeasure)

/-- The translated collapse is exactly the difference-renormalization step
of paper (3.7), with right endpoint fixed at zero. -/
theorem r322Collapse_eq_differenceRenormalizationStep
    (Gp J Gr : T4 → ℝ) (u : T4)
    (hint :
      Integrable (r322CollapseIntegrand Gp J Gr u)
        (paperMeasure.prod paperMeasure)) :
    r322Collapse Gp J Gr u =
      differenceRenormalizationStep Gp J Gr u 0 := by
  unfold r322Collapse differenceRenormalizationStep
  rw [integral_prod _ hint]
  apply integral_congr_ae
  filter_upwards with z
  apply integral_congr_ae
  filter_upwards with w
  unfold r322CollapseIntegrand
  simp only [sub_zero]

/-- Concrete one-step version of (3.7)/(4.8): raw insertion minus the
counterterm is the collapsed input kernel. -/
theorem raw_sub_counterterm_eq_r322Collapse
    (Gp J Gr : T4 → ℝ) (u : T4)
    (hshift : ∀ z : T4,
      (∫ w, J (z - w) ∂paperMeasure) =
        ∫ v, J v ∂paperMeasure)
    (hrawInner : ∀ z : T4, Integrable
      (fun w => Gp (u - z) * J (z - w) * Gr w)
      paperMeasure)
    (hdiagInner : ∀ z : T4, Integrable
      (fun w => Gp (u - z) * J (z - w) * Gr z)
      paperMeasure)
    (hrawOuter : Integrable
      (fun z => ∫ w,
        Gp (u - z) * J (z - w) * Gr w
          ∂paperMeasure) paperMeasure)
    (hdiagOuter : Integrable
      (fun z => ∫ w,
        Gp (u - z) * J (z - w) * Gr z
          ∂paperMeasure) paperMeasure)
    (hjoint :
      Integrable (r322CollapseIntegrand Gp J Gr u)
        (paperMeasure.prod paperMeasure)) :
    rawRenormalizationStep Gp J Gr u 0 -
        renormalizationCounterterm Gp J Gr u 0 =
      r322Collapse Gp J Gr u := by
  rw [r322Collapse_eq_differenceRenormalizationStep
    Gp J Gr u hjoint]
  exact raw_sub_counterterm_eq_difference
    Gp J Gr u 0
      (fun z => hshift z)
      (by simpa only [sub_zero] using hrawInner)
      (by simpa only [sub_zero] using hdiagInner)
      (by simpa only [sub_zero] using hrawOuter)
      (by simpa only [sub_zero] using hdiagOuter)

/-! ## Product-measure Fubini form -/

/-- Joint integrability licenses the product-measure form of the collapse.
This prevents any later use of a junk-totalized iterated integral. -/
theorem r322Collapse_eq_prodIntegral
    (Gp J Gr : T4 → ℝ) (u : T4) :
    r322Collapse Gp J Gr u =
      ∫ p, r322CollapseIntegrand Gp J Gr u p
        ∂(paperMeasure.prod paperMeasure) := by
  rfl

/-! ## Hyperoctahedral symmetry propagation -/

private def permuteT4ProdMeasurableEquiv
    (σ : Equiv.Perm (Fin dim)) :
    T4 × T4 ≃ᵐ T4 × T4 :=
  MeasurableEquiv.prodCongr
    (permuteT4MeasurableEquiv σ)
    (permuteT4MeasurableEquiv σ)

@[simp]
private theorem permuteT4ProdMeasurableEquiv_apply
    (σ : Equiv.Perm (Fin dim)) (p : T4 × T4) :
    permuteT4ProdMeasurableEquiv σ p =
      (permuteT4 σ p.1, permuteT4 σ p.2) := by
  apply Prod.ext
  · exact permuteT4MeasurableEquiv_apply σ p.1
  · exact permuteT4MeasurableEquiv_apply σ p.2

private def coordinateFlipT4ProdMeasurableEquiv
    (i : Fin dim) :
    T4 × T4 ≃ᵐ T4 × T4 :=
  MeasurableEquiv.prodCongr
    (coordinateFlipMeasurableEquiv i)
    (coordinateFlipMeasurableEquiv i)

@[simp]
private theorem coordinateFlipT4ProdMeasurableEquiv_apply
    (i : Fin dim) (p : T4 × T4) :
    coordinateFlipT4ProdMeasurableEquiv i p =
      (coordinateFlipT4 i p.1,
        coordinateFlipT4 i p.2) := by
  rfl

private theorem measurePreserving_permuteT4_prod
    (σ : Equiv.Perm (Fin dim)) :
    MeasurePreserving
      (permuteT4ProdMeasurableEquiv σ)
      (paperMeasure.prod paperMeasure)
      (paperMeasure.prod paperMeasure) := by
  change MeasurePreserving
    (fun p : T4 × T4 =>
      (permuteT4MeasurableEquiv σ p.1,
        permuteT4MeasurableEquiv σ p.2))
    (paperMeasure.prod paperMeasure)
    (paperMeasure.prod paperMeasure)
  exact (measurePreserving_permuteT4 σ).prod
    (measurePreserving_permuteT4 σ)

private theorem measurePreserving_coordinateFlipT4_prod
    (i : Fin dim) :
    MeasurePreserving
      (coordinateFlipT4ProdMeasurableEquiv i)
      (paperMeasure.prod paperMeasure)
      (paperMeasure.prod paperMeasure) := by
  change MeasurePreserving
    (fun p : T4 × T4 =>
      (coordinateFlipMeasurableEquiv i p.1,
        coordinateFlipMeasurableEquiv i p.2))
    (paperMeasure.prod paperMeasure)
    (paperMeasure.prod paperMeasure)
  exact (measurePreserving_coordinateFlipT4 i).prod
    (measurePreserving_coordinateFlipT4 i)

/-- A concrete proper-block collapse preserves the paper's class `E`. -/
theorem r322Collapse_memE
    {Gp J Gr : T4 → ℝ}
    (hGp : MemEClassT4 Gp)
    (hJ : MemEClassT4 J)
    (hGr : MemEClassT4 Gr) :
    MemEClassT4 (r322Collapse Gp J Gr) where
  perm_invariant := by
    intro σ u
    let F : T4 × T4 → ℝ :=
      r322CollapseIntegrand Gp J Gr (permuteT4 σ u)
    calc
      r322Collapse Gp J Gr (u ∘ σ) =
          ∫ p, F p ∂(paperMeasure.prod paperMeasure) := by
        rfl
      _ = ∫ p, F
            (permuteT4 σ p.1, permuteT4 σ p.2)
            ∂(paperMeasure.prod paperMeasure) := by
        have hchange :
            (∫ p, F (permuteT4ProdMeasurableEquiv σ p)
                ∂(paperMeasure.prod paperMeasure)) =
              ∫ p, F p
                ∂(paperMeasure.prod paperMeasure) :=
          (measurePreserving_permuteT4_prod σ).integral_comp' F
        simpa only [permuteT4ProdMeasurableEquiv_apply] using
          hchange.symm
      _ = ∫ p, r322CollapseIntegrand Gp J Gr u p
              ∂(paperMeasure.prod paperMeasure) := by
        apply integral_congr_ae
        filter_upwards with p
        unfold F r322CollapseIntegrand
        have hGp' :
            Gp (permuteT4 σ (u - p.1)) =
              Gp (u - p.1) := by
          change Gp ((u - p.1) ∘ σ) = _
          exact hGp.perm_invariant σ _
        have hJ' :
            J (permuteT4 σ (p.1 - p.2)) =
              J (p.1 - p.2) := by
          change J ((p.1 - p.2) ∘ σ) = _
          exact hJ.perm_invariant σ _
        have hGr₁ :
            Gr (permuteT4 σ p.1) = Gr p.1 := by
          exact hGr.perm_invariant σ p.1
        have hGr₂ :
            Gr (permuteT4 σ p.2) = Gr p.2 := by
          exact hGr.perm_invariant σ p.2
        rw [← permuteT4_sub, ← permuteT4_sub,
          hGp', hJ', hGr₁, hGr₂]
      _ = r322Collapse Gp J Gr u := rfl
  even_coord := by
    intro i u
    let F : T4 × T4 → ℝ :=
      r322CollapseIntegrand Gp J Gr
        (coordinateFlipT4 i u)
    calc
      r322Collapse Gp J Gr
          (Function.update u i (-(u i))) =
          ∫ p, F p ∂(paperMeasure.prod paperMeasure) := by
        rfl
      _ = ∫ p, F
            (coordinateFlipT4 i p.1,
              coordinateFlipT4 i p.2)
            ∂(paperMeasure.prod paperMeasure) := by
        have hchange :
            (∫ p, F
              (coordinateFlipT4ProdMeasurableEquiv i p)
                ∂(paperMeasure.prod paperMeasure)) =
              ∫ p, F p
                ∂(paperMeasure.prod paperMeasure) :=
          (measurePreserving_coordinateFlipT4_prod i).integral_comp' F
        simpa only [coordinateFlipT4ProdMeasurableEquiv_apply] using
          hchange.symm
      _ = ∫ p, r322CollapseIntegrand Gp J Gr u p
              ∂(paperMeasure.prod paperMeasure) := by
        apply integral_congr_ae
        filter_upwards with p
        unfold F r322CollapseIntegrand
        have hGp' :
            Gp (coordinateFlipT4 i (u - p.1)) =
              Gp (u - p.1) := by
          change
            Gp (Function.update (u - p.1) i
              (-((u - p.1) i))) = _
          exact hGp.even_coord i _
        have hJ' :
            J (coordinateFlipT4 i (p.1 - p.2)) =
              J (p.1 - p.2) := by
          change
            J (Function.update (p.1 - p.2) i
              (-((p.1 - p.2) i))) = _
          exact hJ.even_coord i _
        have hGr₁ :
            Gr (coordinateFlipT4 i p.1) = Gr p.1 := by
          exact hGr.even_coord i p.1
        have hGr₂ :
            Gr (coordinateFlipT4 i p.2) = Gr p.2 := by
          exact hGr.even_coord i p.2
        rw [← coordinateFlipT4_sub,
          ← coordinateFlipT4_sub,
          hGp', hJ', hGr₁, hGr₂]
      _ = r322Collapse Gp J Gr u := rfl

end

end Anderson4D
