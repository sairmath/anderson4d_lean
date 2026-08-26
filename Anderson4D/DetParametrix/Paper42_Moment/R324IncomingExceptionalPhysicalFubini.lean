import Anderson4D.DetParametrix.Paper42_Moment.R324StopBeforeStepProjection
import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingPreCollapseFourier

/-!
# Physical Fubini at an exceptional incoming R-324 stop

This module performs only the endpoint Fubini step at a certified stop
immediately before an exceptional incoming head.  The consumed prefix is
not treated here, and the retained head and its complete suffix are not
absorbed.

The source density is jointly integrable in the incoming endpoint, an
arbitrary measured parameter, and the genuine stop coordinates.  The stop
coordinates are split into the retained head tuple and the after-head
surviving tuple.  Fubini then puts the incoming endpoint on the inside,
where the pre-collapse Fourier identity applies while the incoming edge is
still the free Green kernel.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix
namespace R324IncomingExceptionalStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- The signed stop density before the incoming endpoint is integrated.
The arbitrary outer factor lives only on the genuine after-head surviving
coordinates and on the measured parameter. -/
def incomingExceptionalStopSourceDensity
    {Ω : Type*}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (k : Z4) (y : Ω → T4)
    (postOuter :
      Ω →
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4) → ℂ)
    (p :
      (T4 × Ω) ×
        (data.trace.stopPrefix.SurvivingCoordinate → T4)) : ℂ :=
  (data.trace.stopPrefix.residualIntegrand
      ρ ε p.1.1 (y p.1.2)
      (data.trace.stopPrefix.reconstruct p.2) : ℂ) *
    (charT4 k p.1.1 *
      postOuter p.1.2
        (data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq p.2).2)

/-- The density after the incoming endpoint integral has been evaluated.
The retained head tuple and the after-head coordinates are both still
present; in particular this definition performs no head collapse. -/
def incomingExceptionalStopFourierDensity
    {Ω : Type*}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (k : Z4) (y : Ω → T4)
    (postOuter :
      Ω →
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4) → ℂ)
    (p :
      Ω ×
        ((Fin (2 * residualBlockOrder data.terminal.2) → T4) ×
          ((data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
              T4))) : ℂ :=
  let post :=
    data.trace.stopPrefix.afterHead
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
  let a :=
    data.trace.stopPrefix.headSuccessorPoint
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
      0 (y p.1) p.2.2
  translatedGreenMode k
      (p.2.1 ⟨0, by
        have hn := data.stopContext.one_le_blockOrder
        exact Nat.mul_pos (by decide) (Nat.zero_lt_of_lt hn)⟩) *
    data.stopContext.incomingErasedTranslatedRawLocalCore
      ρ ε a p.2.1 *
    ((data.trace.stopPrefix.headOuterFactor
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq
        ρ ε 0 (y p.1) p.2.2 : ℂ) *
      postOuter p.1 p.2.2)

/-- Pointwise inner-endpoint evaluation after the genuine stop-coordinate
split.  This is the analytic heart of the global Fubini theorem below. -/
theorem integral_incomingExceptionalStop_splitSection_eq
    {Ω : Type*}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (hm : 0 < m)
    (k : Z4) (y : Ω → T4)
    (postOuter :
      Ω →
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4) → ℂ)
    (ω : Ω)
    (t : Fin (2 * residualBlockOrder data.terminal.2) → T4)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate → T4) :
    (∫ x : T4,
        (data.trace.stopPrefix.residualIntegrand
            ρ ε x (y ω)
            (data.trace.stopPrefix.reconstruct
              ((data.trace.stopPrefix
                |>.splitSurvivingPiMeasurableEquiv
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq).symm
                (t, v))) : ℂ) *
          (charT4 k x * postOuter ω v)
        ∂paperMeasure) =
      data.incomingExceptionalStopFourierDensity
        k y postOuter (ω, t, v) := by
  let res := data.trace.stopPrefix
  let post :=
    res.afterHead data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
  let ctx := data.stopContext
  let split :=
    res.splitSurvivingPiMeasurableEquiv
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
  let a : T4 :=
    res.headSuccessorPoint
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
      0 (y ω) v
  let outer : ℂ :=
    (res.headOuterFactor
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq
        ρ ε 0 (y ω) v : ℂ) *
      postOuter ω v
  have hpoint (x : T4) :
      (res.residualIntegrand ρ ε x (y ω)
          (res.reconstruct (split.symm (t, v))) : ℂ) *
          (charT4 k x * postOuter ω v) =
        charT4 k x *
          ((ctx.rawLocalIntegrand ρ ε (x - a)
              (fun j => t j - a) : ℂ) * outer) := by
    rw [
      res.residualIntegrand_reconstruct_split
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq
        ρ ε x (y ω),
      res.headLocalFactor_reconstruct_split
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq
        ρ ε x (y ω),
      res.headPredecessorPoint_eq_incoming_of_head_left_eq_zero
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq
        data.left_eq_zero x (y ω) v,
      res.headSuccessorPoint_eq_of_incoming_endpoint
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq
        x 0 (y ω) v,
      res.headOuterFactor_eq_of_incoming_endpoint_of_head_left_eq_zero
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq
        data.left_eq_zero x 0 (y ω) v]
    dsimp only [ctx, a, outer, stopContext]
    push_cast
    ring
  calc
    _ =
        ∫ x : T4,
          charT4 k x *
            ((ctx.rawLocalIntegrand ρ ε (x - a)
                (fun j => t j - a) : ℂ) * outer)
          ∂paperMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ =
        translatedGreenMode k
            (t ⟨0, by
              have hn := ctx.one_le_blockOrder
              exact Nat.mul_pos (by decide) (Nat.zero_lt_of_lt hn)⟩) *
          ctx.incomingErasedTranslatedRawLocalCore
            ρ ε a t *
          outer := by
      exact
        data.incomingStop.integral_char_mul_rawLocal_translated_eq
          hm k a t outer
    _ = _ := by
      rfl

/-- Joint integrability of the exact stop density licenses the endpoint-first
Fubini order.  After the genuine stop coordinates are split, the incoming
endpoint is integrated out and the retained head and complete post tuple
remain as jointly integrable variables. -/
theorem integrable_incomingExceptionalStopFourierDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [SFinite ν]
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (hm : 0 < m)
    (k : Z4) (y : Ω → T4)
    (postOuter :
      Ω →
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4) → ℂ)
    (hsource :
      Integrable
        (data.incomingExceptionalStopSourceDensity
          k y postOuter)
        ((paperMeasure.prod ν).prod
          (Measure.pi fun _ :
            data.trace.stopPrefix.SurvivingCoordinate =>
              paperMeasure))) :
    Integrable
      (data.incomingExceptionalStopFourierDensity
        k y postOuter)
      (ν.prod
        ((Measure.pi fun _ :
            Fin (2 * residualBlockOrder data.terminal.2) =>
              paperMeasure).prod
          (Measure.pi fun _ :
            (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                paperMeasure))) := by
  let res := data.trace.stopPrefix
  let post :=
    res.afterHead data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
  let HeadCoordinate :=
    Fin (2 * residualBlockOrder data.terminal.2)
  let μStop : Measure (res.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μHead : Measure (HeadCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μPost : Measure (post.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μRest :
      Measure
        (Ω ×
          ((HeadCoordinate → T4) ×
            (post.SurvivingCoordinate → T4))) :=
    ν.prod (μHead.prod μPost)
  let split :=
    res.splitSurvivingPiMeasurableEquiv
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
  let splitWithParameter :
      (T4 × Ω) × (res.SurvivingCoordinate → T4) ≃ᵐ
        (T4 × Ω) ×
          ((HeadCoordinate → T4) ×
            (post.SurvivingCoordinate → T4)) :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl (T4 × Ω)) split
  let reassociate :
      (T4 × Ω) ×
          ((HeadCoordinate → T4) ×
            (post.SurvivingCoordinate → T4)) ≃ᵐ
        T4 ×
          (Ω ×
            ((HeadCoordinate → T4) ×
              (post.SurvivingCoordinate → T4))) :=
    MeasurableEquiv.prodAssoc
  let e := splitWithParameter.trans reassociate
  have hsplitWithParameter :
      MeasurePreserving splitWithParameter
        ((paperMeasure.prod ν).prod μStop)
        ((paperMeasure.prod ν).prod (μHead.prod μPost)) :=
    (MeasurePreserving.id (paperMeasure.prod ν)).prod
      (res.measurePreserving_splitSurvivingPiMeasurableEquiv
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq)
  have hreassociate :
      MeasurePreserving reassociate
        ((paperMeasure.prod ν).prod (μHead.prod μPost))
        (paperMeasure.prod μRest) :=
    measurePreserving_prodAssoc
      paperMeasure ν (μHead.prod μPost)
  have he :
      MeasurePreserving e
        ((paperMeasure.prod ν).prod μStop)
        (paperMeasure.prod μRest) :=
    hreassociate.comp hsplitWithParameter
  have he_apply
      (x : T4) (ω : Ω)
      (w : res.SurvivingCoordinate → T4) :
      e ((x, ω), w) =
        (x, ω, split w) := by
    rfl
  let g :
      T4 ×
        (Ω ×
          ((HeadCoordinate → T4) ×
            (post.SurvivingCoordinate → T4))) → ℂ :=
    fun q =>
      (res.residualIntegrand
          ρ ε q.1 (y q.2.1)
          (res.reconstruct (split.symm q.2.2)) : ℂ) *
        (charT4 k q.1 *
          postOuter q.2.1 q.2.2.2)
  have hcomp :
      Integrable (g ∘ e)
        ((paperMeasure.prod ν).prod μStop) := by
    apply hsource.congr
    filter_upwards with p
    rcases p with ⟨⟨x, ω⟩, w⟩
    change
      (res.residualIntegrand ρ ε x (y ω)
          (res.reconstruct w) : ℂ) *
          (charT4 k x * postOuter ω (split w).2) =
        g (e ((x, ω), w))
    rw [he_apply]
    dsimp only [g]
    rw [split.symm_apply_apply]
  have hg :
      Integrable g (paperMeasure.prod μRest) :=
    (he.integrable_comp_emb e.measurableEmbedding).mp hcomp
  have hinner :
      Integrable
        (fun q :
            Ω ×
              ((HeadCoordinate → T4) ×
                (post.SurvivingCoordinate → T4)) =>
          ∫ x : T4, g (x, q) ∂paperMeasure)
        μRest :=
    hg.integral_prod_right
  apply hinner.congr
  filter_upwards with q
  rcases q with ⟨ω, t, v⟩
  exact
    data.integral_incomingExceptionalStop_splitSection_eq
      hm k y postOuter ω t v

/-- Exact product-space Fubini identity at an exceptional incoming stop.
The retained head tuple and the complete post tuple remain outside the
incoming endpoint integral, with no collapse or trace weight applied. -/
theorem integral_incomingExceptionalStopSourceDensity_eq_fourierDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [SFinite ν]
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (hm : 0 < m)
    (k : Z4) (y : Ω → T4)
    (postOuter :
      Ω →
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4) → ℂ)
    (hsource :
      Integrable
        (data.incomingExceptionalStopSourceDensity
          k y postOuter)
        ((paperMeasure.prod ν).prod
          (Measure.pi fun _ :
            data.trace.stopPrefix.SurvivingCoordinate =>
              paperMeasure))) :
    (∫ p,
        data.incomingExceptionalStopSourceDensity
          k y postOuter p
        ∂((paperMeasure.prod ν).prod
          (Measure.pi fun _ :
            data.trace.stopPrefix.SurvivingCoordinate =>
              paperMeasure))) =
      ∫ p,
        data.incomingExceptionalStopFourierDensity
          k y postOuter p
        ∂(ν.prod
          ((Measure.pi fun _ :
              Fin (2 * residualBlockOrder data.terminal.2) =>
                paperMeasure).prod
            (Measure.pi fun _ :
              (data.trace.stopPrefix.afterHead
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                  paperMeasure))) := by
  let res := data.trace.stopPrefix
  let post :=
    res.afterHead data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
  let HeadCoordinate :=
    Fin (2 * residualBlockOrder data.terminal.2)
  let μStop : Measure (res.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μHead : Measure (HeadCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μPost : Measure (post.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μRest :
      Measure
        (Ω ×
          ((HeadCoordinate → T4) ×
            (post.SurvivingCoordinate → T4))) :=
    ν.prod (μHead.prod μPost)
  let split :=
    res.splitSurvivingPiMeasurableEquiv
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
  let splitWithParameter :
      (T4 × Ω) × (res.SurvivingCoordinate → T4) ≃ᵐ
        (T4 × Ω) ×
          ((HeadCoordinate → T4) ×
            (post.SurvivingCoordinate → T4)) :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl (T4 × Ω)) split
  let reassociate :
      (T4 × Ω) ×
          ((HeadCoordinate → T4) ×
            (post.SurvivingCoordinate → T4)) ≃ᵐ
        T4 ×
          (Ω ×
            ((HeadCoordinate → T4) ×
              (post.SurvivingCoordinate → T4))) :=
    MeasurableEquiv.prodAssoc
  let e := splitWithParameter.trans reassociate
  have hsplitWithParameter :
      MeasurePreserving splitWithParameter
        ((paperMeasure.prod ν).prod μStop)
        ((paperMeasure.prod ν).prod (μHead.prod μPost)) :=
    (MeasurePreserving.id (paperMeasure.prod ν)).prod
      (res.measurePreserving_splitSurvivingPiMeasurableEquiv
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq)
  have hreassociate :
      MeasurePreserving reassociate
        ((paperMeasure.prod ν).prod (μHead.prod μPost))
        (paperMeasure.prod μRest) :=
    measurePreserving_prodAssoc
      paperMeasure ν (μHead.prod μPost)
  have he :
      MeasurePreserving e
        ((paperMeasure.prod ν).prod μStop)
        (paperMeasure.prod μRest) :=
    hreassociate.comp hsplitWithParameter
  have he_apply
      (x : T4) (ω : Ω)
      (w : res.SurvivingCoordinate → T4) :
      e ((x, ω), w) =
        (x, ω, split w) := by
    rfl
  let g :
      T4 ×
        (Ω ×
          ((HeadCoordinate → T4) ×
            (post.SurvivingCoordinate → T4))) → ℂ :=
    fun q =>
      (res.residualIntegrand
          ρ ε q.1 (y q.2.1)
          (res.reconstruct (split.symm q.2.2)) : ℂ) *
        (charT4 k q.1 *
          postOuter q.2.1 q.2.2.2)
  have hsourcePoint
      (p :
        (T4 × Ω) ×
          (res.SurvivingCoordinate → T4)) :
      data.incomingExceptionalStopSourceDensity
          k y postOuter p =
        g (e p) := by
    rcases p with ⟨⟨x, ω⟩, w⟩
    change
      (res.residualIntegrand ρ ε x (y ω)
          (res.reconstruct w) : ℂ) *
          (charT4 k x * postOuter ω (split w).2) =
        g (e ((x, ω), w))
    rw [he_apply]
    dsimp only [g]
    rw [split.symm_apply_apply]
  have hcomp :
      Integrable (g ∘ e)
        ((paperMeasure.prod ν).prod μStop) := by
    apply hsource.congr
    exact
      Filter.Eventually.of_forall hsourcePoint
  have hg :
      Integrable g (paperMeasure.prod μRest) :=
    (he.integrable_comp_emb e.measurableEmbedding).mp hcomp
  have hsection
      (q :
        Ω ×
          ((HeadCoordinate → T4) ×
            (post.SurvivingCoordinate → T4))) :
      (∫ x : T4, g (x, q) ∂paperMeasure) =
        data.incomingExceptionalStopFourierDensity
          k y postOuter q := by
    rcases q with ⟨ω, t, v⟩
    exact
      data.integral_incomingExceptionalStop_splitSection_eq
        hm k y postOuter ω t v
  calc
    (∫ p,
        data.incomingExceptionalStopSourceDensity
          k y postOuter p
        ∂((paperMeasure.prod ν).prod μStop)) =
        ∫ p, g (e p)
          ∂((paperMeasure.prod ν).prod μStop) := by
      apply integral_congr_ae
      exact
        Filter.Eventually.of_forall hsourcePoint
    _ =
        ∫ q, g q ∂(paperMeasure.prod μRest) :=
      he.integral_comp e.measurableEmbedding g
    _ =
        ∫ q,
          ∫ x : T4, g (x, q) ∂paperMeasure
          ∂μRest :=
      integral_prod_symm _ hg
    _ =
        ∫ q,
          data.incomingExceptionalStopFourierDensity
            k y postOuter q
          ∂μRest := by
      apply integral_congr_ae
      exact
        Filter.Eventually.of_forall hsection

end R324IncomingExceptionalStopTraceAssembly
end R324WithinHalfResidualPrefix

end

end Anderson4D
