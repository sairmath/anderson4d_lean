import Anderson4D.DetParametrix.Paper42_Moment.R324SignedPhaseAOneBlockUpdate

/-!
# Gap-first coordinates for an incoming R-324 head

The primitive-block coordinate split used by the signed R-324 reduction
first exposes the ordered endpoint pair `(first, last)`.  The exceptional
Fourier calculation instead uses `(gap, first)`, with
`gap = last - first`.  This file records the exact product-Haar
reindexing, including the internal primitive coordinates.

No estimate and no absolute value is used here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## The endpoint shear -/

/-- Reindex an ordered endpoint pair `(first, last)` by
`(last - first, first)`. -/
def r324EndpointGapFirstMeasurableEquiv :
    T4 × T4 ≃ᵐ T4 × T4 :=
  (MeasurableEquiv.shearSubRight T4).trans
    (MeasurableEquiv.prodComm :
      T4 × T4 ≃ᵐ T4 × T4)

@[simp]
theorem r324EndpointGapFirstMeasurableEquiv_apply
    (first last : T4) :
    r324EndpointGapFirstMeasurableEquiv (first, last) =
      (last - first, first) := by
  rfl

@[simp]
theorem r324EndpointGapFirstMeasurableEquiv_symm_apply
    (gap first : T4) :
    r324EndpointGapFirstMeasurableEquiv.symm (gap, first) =
      (first, first + gap) := by
  change (first, gap + first) = (first, first + gap)
  rw [add_comm]

/-- The endpoint gap-first shear preserves the paper product measure. -/
theorem measurePreserving_r324EndpointGapFirstMeasurableEquiv :
    MeasurePreserving
      r324EndpointGapFirstMeasurableEquiv
      (paperMeasure.prod paperMeasure)
      (paperMeasure.prod paperMeasure) := by
  have hshear :
      MeasurePreserving
        (fun p : T4 × T4 => (p.1, p.2 - p.1))
        (paperMeasure.prod paperMeasure)
        (paperMeasure.prod paperMeasure) := by
    rw [paperMeasure_eq_volume]
    exact
      measurePreserving_prod_sub
        (μ := (volume : Measure T4))
        (ν := (volume : Measure T4))
  have hswap :
      MeasurePreserving
        (fun p : T4 × T4 => (p.2, p.1))
        (paperMeasure.prod paperMeasure)
        (paperMeasure.prod paperMeasure) :=
    Measure.measurePreserving_swap
  have hfun :
      (r324EndpointGapFirstMeasurableEquiv :
        T4 × T4 → T4 × T4) =
          fun p => (p.2 - p.1, p.1) := by
    funext p
    exact
      r324EndpointGapFirstMeasurableEquiv_apply p.1 p.2
  rw [hfun]
  exact hswap.comp hshear

/-! ## The full primitive head -/

/-- Split a positive-order primitive head directly into
`((gap, first), internal)`. -/
def r324PrimitiveHeadGapFirstMeasurableEquiv
    (n : ℕ) (hn : 1 ≤ n) :
    (Fin (2 * n) → T4) ≃ᵐ
      (T4 × T4) × (Fin (2 * n - 2) → T4) :=
  (r324PrimitiveBlockTupleMeasurableEquiv n hn).trans
    (MeasurableEquiv.prodCongr
      r324EndpointGapFirstMeasurableEquiv
      (MeasurableEquiv.refl
        (Fin (2 * n - 2) → T4)))

@[simp]
theorem r324PrimitiveHeadGapFirstMeasurableEquiv_symm_apply
    (n : ℕ) (hn : 1 ≤ n)
    (gap first : T4)
    (u : Fin (2 * n - 2) → T4) :
    (r324PrimitiveHeadGapFirstMeasurableEquiv n hn).symm
        ((gap, first), u) =
      primitiveAssemble n hn first (first + gap) u := by
  change
    (r324PrimitiveBlockTupleMeasurableEquiv n hn).symm
        (r324EndpointGapFirstMeasurableEquiv.symm
          (gap, first), u) =
      primitiveAssemble n hn first (first + gap) u
  rw [r324EndpointGapFirstMeasurableEquiv_symm_apply]
  exact
    r324PrimitiveBlockTupleMeasurableEquiv_symm_apply
      n hn (first, first + gap) u

/-- The complete primitive-head gap-first split preserves product Haar
measure exactly. -/
theorem measurePreserving_r324PrimitiveHeadGapFirstMeasurableEquiv
    (n : ℕ) (hn : 1 ≤ n) :
    MeasurePreserving
      (r324PrimitiveHeadGapFirstMeasurableEquiv n hn)
      (Measure.pi fun _ : Fin (2 * n) => paperMeasure)
      ((paperMeasure.prod paperMeasure).prod
        (Measure.pi fun _ : Fin (2 * n - 2) =>
          paperMeasure)) := by
  have htail :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          r324EndpointGapFirstMeasurableEquiv
          (MeasurableEquiv.refl
            (Fin (2 * n - 2) → T4)))
        ((paperMeasure.prod paperMeasure).prod
          (Measure.pi fun _ : Fin (2 * n - 2) =>
            paperMeasure))
        ((paperMeasure.prod paperMeasure).prod
          (Measure.pi fun _ : Fin (2 * n - 2) =>
            paperMeasure)) :=
    measurePreserving_r324EndpointGapFirstMeasurableEquiv.prod
      (MeasurePreserving.id
        (Measure.pi fun _ : Fin (2 * n - 2) =>
          paperMeasure))
  exact
    htail.comp
      (measurePreserving_r324PrimitiveBlockTupleMeasurableEquiv n hn)

/-! ## Integral normal form -/

/-- Bochner integration over a genuine positive-order primitive head in
the exact `(gap, first, internal)` order used by the incoming exceptional
Fourier calculation. -/
theorem integral_standardBlock_eq_integral_gap_first_internal
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (n : ℕ) (hn : 1 ≤ n)
    (f : (Fin (2 * n) → T4) → E)
    (hf :
      Integrable f
        (Measure.pi fun _ : Fin (2 * n) =>
          paperMeasure)) :
    (∫ t, f t
        ∂Measure.pi fun _ : Fin (2 * n) =>
          paperMeasure) =
      ∫ gap : T4,
        ∫ first : T4,
          ∫ u : Fin (2 * n - 2) → T4,
            f (primitiveAssemble n hn
              first (first + gap) u)
            ∂Measure.pi fun _ => paperMeasure
          ∂paperMeasure
        ∂paperMeasure := by
  let e :=
    r324PrimitiveHeadGapFirstMeasurableEquiv n hn
  let μ :=
    Measure.pi fun _ : Fin (2 * n) => paperMeasure
  let νInternal :=
    Measure.pi fun _ : Fin (2 * n - 2) =>
      paperMeasure
  let ν :=
    (paperMeasure.prod paperMeasure).prod νInternal
  have hp : MeasurePreserving e μ ν :=
    measurePreserving_r324PrimitiveHeadGapFirstMeasurableEquiv n hn
  have htarget :
      Integrable (fun q => f (e.symm q)) ν := by
    have hiff :=
      hp.symm.integrable_comp_emb
        e.symm.measurableEmbedding
        (g := f)
    change Integrable (f ∘ e.symm) ν
    exact hiff.mpr hf
  have houter :
      Integrable
        (fun p : T4 × T4 =>
          ∫ u : Fin (2 * n - 2) → T4,
            f (e.symm (p, u)) ∂νInternal)
        (paperMeasure.prod paperMeasure) :=
    htarget.integral_prod_left
  calc
    (∫ t, f t ∂μ) =
        ∫ q, f (e.symm q) ∂ν := by
      symm
      simpa only [Function.comp_apply] using
        hp.symm.integral_comp' f
    _ =
        ∫ p : T4 × T4,
          ∫ u : Fin (2 * n - 2) → T4,
            f (e.symm (p, u)) ∂νInternal
          ∂(paperMeasure.prod paperMeasure) :=
      integral_prod _ htarget
    _ =
        ∫ gap : T4,
          ∫ first : T4,
            ∫ u : Fin (2 * n - 2) → T4,
              f (e.symm ((gap, first), u))
              ∂νInternal
            ∂paperMeasure
          ∂paperMeasure :=
      integral_prod _ houter
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with gap
      apply integral_congr_ae
      filter_upwards with first
      apply integral_congr_ae
      filter_upwards with u
      rw [r324PrimitiveHeadGapFirstMeasurableEquiv_symm_apply]

end

end Anderson4D
