import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingPhasedOrdinaryStep
import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalStep4HeadBound
import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalPhysicalRootBridge

/-!
# Integral seam after the exceptional incoming head

The exceptional-stop endpoint produces the perturbatively weighted stop
Fourier integral over the measured parameter, the retained head tuple, and
the after-head surviving tuple.  This file integrates the retained head
tuple out and identifies the result as exactly the after-head phased
residual density consumed by the ordinary-head iteration.

The pointwise head collapse is the genuine-stop anchor decomposition: the
head block contributes the squared paper second-order decay, the primitive
Step-4 defect, and the transported character at the after-head phase
anchor.  The decay, the defect, and the untouched post outer factor are
absorbed into a genuinely coordinate-dependent post coefficient, while the
anchor character and the slot-zero-erased after-head core reassemble the
phased density itself.  The integrability handover for that density closes
the recursion seam.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## Pulling the retained head tuple in front of the parameters -/

/-- Reorder `(ω, (t, v))` to `(t, (ω, v))`, so that the retained head
tuple can be integrated first while the measured parameter and the
after-head tuple stay joint. -/
def r324IncomingExceptionalHeadPullMeasurableEquiv
    (A B C : Type*)
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] :
    A × (B × C) ≃ᵐ B × (A × C) :=
  MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.prodAssoc.trans
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl B)
        MeasurableEquiv.prodComm))

@[simp]
theorem r324IncomingExceptionalHeadPullMeasurableEquiv_apply
    {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (a : A) (b : B) (c : C) :
    r324IncomingExceptionalHeadPullMeasurableEquiv A B C (a, b, c) =
      (b, a, c) := by
  rfl

/-- The head pull preserves the corresponding triple product measures. -/
theorem measurePreserving_r324IncomingExceptionalHeadPullMeasurableEquiv
    {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μA : Measure A) (μB : Measure B) (μC : Measure C)
    [SFinite μA] [SFinite μB] [SFinite μC] :
    MeasurePreserving
      (r324IncomingExceptionalHeadPullMeasurableEquiv A B C)
      (μA.prod (μB.prod μC))
      (μB.prod (μA.prod μC)) := by
  have hswap :
      MeasurePreserving
        (MeasurableEquiv.prodComm : A × (B × C) ≃ᵐ (B × C) × A)
        (μA.prod (μB.prod μC))
        ((μB.prod μC).prod μA) :=
    Measure.measurePreserving_swap
  have hassoc :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc : (B × C) × A ≃ᵐ B × (C × A))
        ((μB.prod μC).prod μA)
        (μB.prod (μC.prod μA)) :=
    measurePreserving_prodAssoc μB μC μA
  have hinner :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl B)
          (MeasurableEquiv.prodComm : C × A ≃ᵐ A × C))
        (μB.prod (μC.prod μA))
        (μB.prod (μA.prod μC)) :=
    (MeasurePreserving.id μB).prod
      Measure.measurePreserving_swap
  exact hinner.comp (hassoc.comp hswap)

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-! ## The erased post-head core at a slot-zero head -/

/-- At a slot-zero-fed head the erased slot is one of the consumed local
slots, so the slot-zero-erased post-head core carries no leftover
predecessor factor: it is exactly the ordinary head outer factor. -/
theorem afterHead_incomingErasedResidualIntegrand_of_eq_zero
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (hpred :
      r324WithinHalfPredecessorSlot res.state head = 0)
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    (res.afterHead
      head tail hremaining).incomingErasedResidualIntegrand
        ρ' ε' x y
        ((res.afterHead
          head tail hremaining).reconstruct v) =
      res.headOuterFactor
        head tail hremaining ρ' ε' x y v := by
  let post :=
    res.afterHead head tail hremaining
  let postTuple := post.reconstruct v
  let erased :=
    (Finset.univ : Finset (Fin (m + 1))).erase 0
  let localSlots :=
    res.headChainSlots head tail hremaining
  have hzeroInternal :
      (0 : Fin (m + 1)) ∉
        res.headInternalSlots head tail hremaining := by
    intro hmem
    rw [← hpred] at hmem
    exact
      res.predecessorSlot_not_mem_headInternalSlots
        head tail hremaining hmem
  have hzeroLocal :
      (0 : Fin (m + 1)) ∈ localSlots := by
    dsimp only [localSlots]
    unfold headChainSlots
    exact
      Finset.mem_union.mpr
        (Or.inl (Finset.mem_singleton.mpr hpred.symm))
  have hinter :
      erased ∩ localSlots =
        res.headInternalSlots head tail hremaining := by
    dsimp only [erased, localSlots]
    ext edge
    unfold headChainSlots
    simp only [Finset.mem_inter, Finset.mem_erase,
      Finset.mem_univ, and_true, Finset.mem_union,
      Finset.mem_singleton, hpred]
    constructor
    · rintro ⟨hne, h0 | hint⟩
      · exact absurd h0 hne
      · exact hint
    · intro hint
      exact
        ⟨fun h0 => hzeroInternal (h0 ▸ hint),
          Or.inr hint⟩
  have hdiff :
      erased \ localSlots =
        Finset.univ \ localSlots := by
    dsimp only [erased]
    ext edge
    simp only [Finset.mem_sdiff, Finset.mem_erase,
      Finset.mem_univ, and_true, true_and]
    constructor
    · rintro ⟨_hne, hnl⟩
      exact hnl
    · intro hnl
      exact
        ⟨fun h0 => hnl (by rw [h0]; exact hzeroLocal),
          hnl⟩
  have hinternalOne :
      (∏ edge ∈
          res.headInternalSlots head tail hremaining,
        post.residualChainEdgeFactor x y postTuple edge) =
        1 := by
    rw [res.prod_headInternalSlots head tail hremaining]
    exact
      Finset.prod_eq_one fun j _ =>
        res.afterHead_residualChainEdgeFactor_internal
          head tail hremaining x y postTuple j
  have hpartition :=
    Finset.prod_inter_mul_prod_sdiff
      erased localSlots
      (post.residualChainEdgeFactor x y postTuple)
  rw [hinter, hdiff, hinternalOne, one_mul] at hpartition
  unfold incomingErasedResidualIntegrand
    incomingErasedResidualChainProduct
    headOuterFactor headOuterChainProductAfter
  dsimp only [post, postTuple, erased, localSlots]
    at hpartition ⊢
  rw [← hpartition]

namespace R324IncomingExceptionalStopTraceAssembly

variable {C K : ℝ} {κ : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-! ## The after-head phased density produced by the head collapse -/

/-- The genuinely coordinate-dependent coefficient left on the after-head
phased density once the retained exceptional head has been integrated out:
the squared paper second-order decay, the primitive Step-4 defect of the
head internal edges, and the untouched post outer factor. -/
def incomingExceptionalPostCoefficient
    {Ω : Type*}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (k : Z4)
    (postOuter :
      Ω →
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4) → ℂ)
    (ω : Ω)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
          T4) : ℂ :=
  (paperSecondOrderModeDecay k : ℂ) ^ 2 *
    incomingExceptionalPrimitiveDefect ρ lam ε
      (residualBlockOrder data.terminal.2)
      data.stopContext.one_le_blockOrder
      data.stopContext.internalEdges k *
    postOuter ω v

/-- The after-head phased residual density carrying the collapsed head as
its coordinate-dependent coefficient.  This is exactly the incoming phased
density form consumed by the ordinary one-head transport equation, at the
Fourier-evaluated incoming endpoint `0`. -/
def incomingExceptionalAfterHeadPhasedIntegrand
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
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4)) : ℂ :=
  (data.trace.stopPrefix.afterHead
    data.terminal data.suffix
    data.trace.stopPrefix_remaining_eq).incomingPhasedResidualDensity
      (data.incomingExceptionalPostCoefficient
        k postOuter p.1 p.2)
      k ρ ε 0 (y p.1) p.2

/-- Fixed parameter and after-head coordinates: integrating the retained
head tuple produces exactly the after-head phased residual density with
the collapsed-head post coefficient. -/
theorem
    lamEps_pow_integral_incomingExceptionalStopFourierDensity_head_eq_afterHeadPhased
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
    (ω : Ω)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate → T4)
    (hhead :
      Integrable
        (fun t :
            Fin (2 * residualBlockOrder data.terminal.2) → T4 =>
          data.incomingExceptionalStopFourierDensity
            k y postOuter (ω, t, v))
        (Measure.pi fun _ => paperMeasure))
    (hG :
      ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder data.terminal.2)
              κB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder data.terminal.2) *
        (∫ t :
            Fin (2 * residualBlockOrder data.terminal.2) → T4,
          data.incomingExceptionalStopFourierDensity
            k y postOuter (ω, t, v)
          ∂Measure.pi fun _ => paperMeasure) =
      data.incomingExceptionalAfterHeadPhasedIntegrand
        k y postOuter (ω, v) := by
  have hbridge :=
    data.trace.stopPrefix.afterHead_incomingErasedResidualIntegrand_of_eq_zero
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
      data.stop_predecessorSlot_eq_zero
      ρ ε 0 (y ω) v
  rw [
    data.lamEps_pow_integral_incomingExceptionalStopFourierDensity_head_eq_decay_sq_mul_anchor
      k y postOuter ω v hhead hG hint]
  unfold incomingExceptionalAfterHeadPhasedIntegrand
    incomingExceptionalPostCoefficient
    incomingPhasedResidualDensity
  rw [hbridge]
  ring

/-- Joint integrability of the stop Fourier density with the retained head
tuple pulled in front of the measured parameter and after-head tuple. -/
theorem integrable_incomingExceptionalStopFourierDensity_headPull
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
      (fun q :
          (Fin (2 * residualBlockOrder data.terminal.2) → T4) ×
            (Ω ×
              ((data.trace.stopPrefix.afterHead
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
                  T4)) =>
        data.incomingExceptionalStopFourierDensity
          k y postOuter (q.2.1, q.1, q.2.2))
      ((Measure.pi fun _ :
          Fin (2 * residualBlockOrder data.terminal.2) =>
            paperMeasure).prod
        (ν.prod
          (Measure.pi fun _ :
            (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                paperMeasure))) := by
  let post :=
    data.trace.stopPrefix.afterHead
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
  let μHead :
      Measure
        (Fin (2 * residualBlockOrder data.terminal.2) → T4) :=
    Measure.pi fun _ => paperMeasure
  let μPost : Measure (post.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  have hfourier :
      Integrable
        (data.incomingExceptionalStopFourierDensity
          k y postOuter)
        (ν.prod (μHead.prod μPost)) :=
    data.integrable_incomingExceptionalStopFourierDensity
      ν hm k y postOuter hsource
  let e :=
    r324IncomingExceptionalHeadPullMeasurableEquiv
      Ω
      (Fin (2 * residualBlockOrder data.terminal.2) → T4)
      (post.SurvivingCoordinate → T4)
  have he :
      MeasurePreserving e
        (ν.prod (μHead.prod μPost))
        (μHead.prod (ν.prod μPost)) :=
    measurePreserving_r324IncomingExceptionalHeadPullMeasurableEquiv
      ν μHead μPost
  let g :
      (Fin (2 * residualBlockOrder data.terminal.2) → T4) ×
        (Ω × (post.SurvivingCoordinate → T4)) → ℂ :=
    fun q =>
      data.incomingExceptionalStopFourierDensity
        k y postOuter (q.2.1, q.1, q.2.2)
  have hcomp :
      Integrable (g ∘ e) (ν.prod (μHead.prod μPost)) := by
    apply hfourier.congr
    filter_upwards with p
    rcases p with ⟨ω, t, v⟩
    rfl
  exact
    (he.integrable_comp_emb e.measurableEmbedding).mp hcomp

/-- **Integrability handover.**  The after-head phased density with the
collapsed-head coordinate-dependent coefficient is jointly integrable in
the measured parameter and the after-head coordinates.  This is the
recursion seam feeding the ordinary one-head transport iteration. -/
theorem integrable_incomingExceptionalAfterHeadPhasedIntegrand
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
              paperMeasure)))
    (hG :
      ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder data.terminal.2)
              κB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    Integrable
      (data.incomingExceptionalAfterHeadPhasedIntegrand
        k y postOuter)
      (ν.prod
        (Measure.pi fun _ :
          (data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
              paperMeasure)) := by
  have hg :=
    data.integrable_incomingExceptionalStopFourierDensity_headPull
      ν hm k y postOuter hsource
  have hmarg := hg.integral_prod_right
  have hscaled :=
    hmarg.const_mul
      ((lamEps lam ε : ℂ) ^
        (2 * residualBlockOrder data.terminal.2))
  apply hscaled.congr
  filter_upwards [hg.prod_left_ae] with q hq
  rcases q with ⟨ω, v⟩
  exact
    data.lamEps_pow_integral_incomingExceptionalStopFourierDensity_head_eq_afterHeadPhased
      k y postOuter ω v hq hG hint

/-- **Exceptional head absorption at the integral level.**  The weighted
stop Fourier integral collapses its retained head tuple: the perturbative
power drops by twice the head block order and the integrand becomes
exactly the after-head phased residual density with the collapsed-head
coordinate-dependent coefficient. -/
theorem
    lamEps_pow_integral_incomingExceptionalStopFourierDensity_eq_afterHead
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
              paperMeasure)))
    (hG :
      ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder data.terminal.2)
              κB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^
          (2 * data.trace.stopPrefix.remainingOrder) *
        (∫ q,
          data.incomingExceptionalStopFourierDensity
            k y postOuter q
          ∂(ν.prod
            ((Measure.pi fun _ :
                Fin (2 * residualBlockOrder data.terminal.2) =>
                  paperMeasure).prod
              (Measure.pi fun _ :
                (data.trace.stopPrefix.afterHead
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                    paperMeasure)))) =
      (lamEps lam ε : ℂ) ^
          (2 *
            (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).remainingOrder) *
        (∫ p,
          data.incomingExceptionalAfterHeadPhasedIntegrand
            k y postOuter p
          ∂(ν.prod
            (Measure.pi fun _ :
              (data.trace.stopPrefix.afterHead
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                  paperMeasure))) := by
  let post :=
    data.trace.stopPrefix.afterHead
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
  let μHead :
      Measure
        (Fin (2 * residualBlockOrder data.terminal.2) → T4) :=
    Measure.pi fun _ => paperMeasure
  let μPost : Measure (post.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let e :=
    r324IncomingExceptionalHeadPullMeasurableEquiv
      Ω
      (Fin (2 * residualBlockOrder data.terminal.2) → T4)
      (post.SurvivingCoordinate → T4)
  have he :
      MeasurePreserving e
        (ν.prod (μHead.prod μPost))
        (μHead.prod (ν.prod μPost)) :=
    measurePreserving_r324IncomingExceptionalHeadPullMeasurableEquiv
      ν μHead μPost
  let g :
      (Fin (2 * residualBlockOrder data.terminal.2) → T4) ×
        (Ω × (post.SurvivingCoordinate → T4)) → ℂ :=
    fun q =>
      data.incomingExceptionalStopFourierDensity
        k y postOuter (q.2.1, q.1, q.2.2)
  have hg : Integrable g (μHead.prod (ν.prod μPost)) :=
    data.integrable_incomingExceptionalStopFourierDensity_headPull
      ν hm k y postOuter hsource
  have hexponent :
      2 * data.trace.stopPrefix.remainingOrder =
        2 * post.remainingOrder +
          2 * residualBlockOrder data.terminal.2 := by
    have horder :=
      data.trace.stopPrefix.remainingOrder_head
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq
    dsimp only [post]
    omega
  calc
    (lamEps lam ε : ℂ) ^
          (2 * data.trace.stopPrefix.remainingOrder) *
        (∫ q,
          data.incomingExceptionalStopFourierDensity
            k y postOuter q
          ∂(ν.prod (μHead.prod μPost))) =
      (lamEps lam ε : ℂ) ^
          (2 * data.trace.stopPrefix.remainingOrder) *
        (∫ q, g q ∂(μHead.prod (ν.prod μPost))) := by
      congr 1
      exact he.integral_comp e.measurableEmbedding g
    _ =
      (lamEps lam ε : ℂ) ^
          (2 * data.trace.stopPrefix.remainingOrder) *
        (∫ q, (∫ t, g (t, q) ∂μHead) ∂(ν.prod μPost)) := by
      congr 1
      exact integral_prod_symm g hg
    _ =
      (lamEps lam ε : ℂ) ^ (2 * post.remainingOrder) *
        (∫ q,
          (lamEps lam ε : ℂ) ^
              (2 * residualBlockOrder data.terminal.2) *
            (∫ t, g (t, q) ∂μHead)
          ∂(ν.prod μPost)) := by
      rw [integral_const_mul, hexponent, pow_add]
      ring
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hg.prod_left_ae] with q hq
      rcases q with ⟨ω, v⟩
      exact
        data.lamEps_pow_integral_incomingExceptionalStopFourierDensity_head_eq_afterHeadPhased
          k y postOuter ω v hq hG hint

/-! ## The genuine refined root -/

/-- The already-proved refined-root joint integrability, transported by
the certified trace to the exceptional stop.  This is the exact `hsource`
premise of the stop Fubini exchange and of the head absorption. -/
theorem integrable_incomingExceptionalRefinedRootStopSource
    (p : R324RefinedScheduleIndex m)
    (e₀ : MomentContraction m)
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) e₀.1 initialScale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (α β : Z4) :
    Integrable
      (data.incomingExceptionalStopSourceDensity
        α
        (fun ω :
            R324IncomingExceptionalRootParameter
              ρ lam ε e₀.2.1 =>
          ω.1.1)
        (data.incomingExceptionalRefinedRootPostOuter
          α β e₀.2.2))
      ((paperMeasure.prod
          (r324IncomingExceptionalRootParameterMeasure
            ρ lam ε e₀.2.1)).prod
        (Measure.pi fun _ :
          data.trace.stopPrefix.SurvivingCoordinate =>
            paperMeasure)) := by
  let Ω :=
    R324IncomingExceptionalRootParameter
      ρ lam ε e₀.2.1
  let ν :=
    r324IncomingExceptionalRootParameterMeasure
      ρ lam ε e₀.2.1
  let initial :=
    R324WithinHalfResidualPrefix.initial ρ lam ε e₀.1
  let split :=
    data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
  let y : Ω → T4 := fun ω => ω.1.1
  let postOuter :=
    data.incomingExceptionalRefinedRootPostOuter
      α β e₀.2.2
  let stopOuter :
      T4 × Ω →
        (data.trace.stopPrefix.SurvivingCoordinate → T4) → ℂ :=
    fun ep w =>
      charT4 α ep.1 * postOuter ep.2 (split w).2
  have hcurrent :=
    data.integrable_incomingExceptionalRefinedInitialSource
      p e₀ he₀ hε hε1 α β
  have hcurrent' :
      Integrable
        (fun q :
            (T4 × Ω) ×
              (initial.SurvivingCoordinate → T4) =>
          (initial.residualIntegrand
              ρ ε q.1.1 (y q.1.2)
              (initial.reconstruct q.2) : ℂ) *
            stopOuter q.1
              (data.trace.stopProjection q.2))
        ((paperMeasure.prod ν).prod
          (Measure.pi fun _ :
            initial.SurvivingCoordinate =>
              paperMeasure)) := by
    exact hcurrent
  exact
    data.trace.integrable_joint_residualIntegrand_mul_stopOuter_stopPrefix
      (paperMeasure.prod ν)
      (fun ep : T4 × Ω => ep.1)
      (fun ep : T4 × Ω => y ep.2)
      stopOuter hcurrent'

/-- **Seam-2 endpoint.**  The genuine single-fibre physical root integral
with the retained exceptional head fully absorbed: the right-hand side is
the after-head phased density integral over the root parameter and the
after-head coordinates, ready for the ordinary-head iteration. -/
theorem
    lamEps_pow_r324RefinedPhysicalIntegral_eq_incomingExceptionalAfterHead
    (p : R324RefinedScheduleIndex m)
    (e₀ : MomentContraction m)
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) e₀.1 initialScale)
    (hm : 0 < m)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hG :
      ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder data.terminal.2)
              κB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (α β : Z4) :
    (lamEps lam ε : ℂ) ^
          (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).remainingOrder) *
        r324RefinedPhysicalIntegral
          ρ ε m α β p =
      (lamEps lam ε : ℂ) ^
          (2 *
            (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).remainingOrder) *
        (∫ q,
          data.incomingExceptionalAfterHeadPhasedIntegrand
            α
            (fun ω :
                R324IncomingExceptionalRootParameter
                  ρ lam ε e₀.2.1 =>
              ω.1.1)
            (data.incomingExceptionalRefinedRootPostOuter
              α β e₀.2.2) q
          ∂((r324IncomingExceptionalRootParameterMeasure
              ρ lam ε e₀.2.1).prod
            (Measure.pi fun _ :
              (data.trace.stopPrefix.afterHead
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                  paperMeasure))) :=
  (data.lamEps_pow_r324RefinedPhysicalIntegral_eq_incomingExceptionalStopFourier
      p e₀ he₀ hm hε hε1 α β).trans
    (data.lamEps_pow_integral_incomingExceptionalStopFourierDensity_eq_afterHead
      (r324IncomingExceptionalRootParameterMeasure
        ρ lam ε e₀.2.1)
      hm α
      (fun ω :
          R324IncomingExceptionalRootParameter
            ρ lam ε e₀.2.1 =>
        ω.1.1)
      (data.incomingExceptionalRefinedRootPostOuter
        α β e₀.2.2)
      (data.integrable_incomingExceptionalRefinedRootStopSource
        p e₀ he₀ hε hε1 α β)
      hG hint)

/-- Integrability handover for the genuine refined root: the seam-2
right-hand density is integrable over the root parameter and the
after-head coordinates. -/
theorem integrable_incomingExceptionalRefinedRootAfterHeadPhasedIntegrand
    (p : R324RefinedScheduleIndex m)
    (e₀ : MomentContraction m)
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) e₀.1 initialScale)
    (hm : 0 < m)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hG :
      ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder data.terminal.2)
              κB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (α β : Z4) :
    Integrable
      (data.incomingExceptionalAfterHeadPhasedIntegrand
        α
        (fun ω :
            R324IncomingExceptionalRootParameter
              ρ lam ε e₀.2.1 =>
          ω.1.1)
        (data.incomingExceptionalRefinedRootPostOuter
          α β e₀.2.2))
      ((r324IncomingExceptionalRootParameterMeasure
          ρ lam ε e₀.2.1).prod
        (Measure.pi fun _ :
          (data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
              paperMeasure)) :=
  data.integrable_incomingExceptionalAfterHeadPhasedIntegrand
    (r324IncomingExceptionalRootParameterMeasure
      ρ lam ε e₀.2.1)
    hm α
    (fun ω :
        R324IncomingExceptionalRootParameter
          ρ lam ε e₀.2.1 =>
      ω.1.1)
    (data.incomingExceptionalRefinedRootPostOuter
      α β e₀.2.2)
    (data.integrable_incomingExceptionalRefinedRootStopSource
      p e₀ he₀ hε hε1 α β)
    hG hint

end R324IncomingExceptionalStopTraceAssembly

end R324WithinHalfResidualPrefix

end

end Anderson4D
