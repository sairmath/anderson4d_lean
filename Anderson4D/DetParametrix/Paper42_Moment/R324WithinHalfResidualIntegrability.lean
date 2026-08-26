import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfQuantitativeStep

/-!
# Integrability carried through an R-324 within-half residual trace

The exact residual transition needs integrability of the *weighted* local
section almost everywhere in the post-head coordinates.  Full current
integrability supplies precisely that statement after the genuine
head/post split.

It is important not to replace this by unweighted local integrability almost
everywhere in the local endpoint parameter.  The map from a post tuple to
the predecessor-minus-successor point may be constant or otherwise
degenerate (in particular when there are no post coordinates), so such an
a.e. statement cannot in general be pulled back.  The weighted formulation
also handles a zero outer factor without dividing by it.

No global moment estimate is stored here.  The state below contains only:

* the actual scale of every named edge;
* the corresponding off-diagonal edge certificate; and
* full integrability of the current physical residual integrand.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Integrability supplied by a slotwise edge certificate -/

namespace R324WithinHalfEdgeCertificate

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {ctx : R324WithinHalfStepContext pairing}
    {scale : Fin (m + 1) → ℝ}

/-- Every closed primitive summand in one actual within-half head has an
integrable internal section, pointwise in its two displayed endpoints. -/
theorem integrable_stepClosedIntegrand_section
    (hcert : R324WithinHalfEdgeCertificate ctx.state scale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (κB :
      {κ : PartialPairing
          (Fin (2 * residualBlockOrder ctx.step.2)) //
        κ ∈ primitiveFullPairings
          (residualBlockOrder ctx.step.2)})
    (z w : T4) :
    Integrable
      (fun v :
          Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
        detJclosedIntegrandWith ρ ε
          (2 * residualBlockOrder ctx.step.2)
          κB.1 ctx.internalEdges
          (primitiveAssemble
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder z w v))
      (Measure.pi fun _ => paperMeasure) := by
  obtain ⟨hfull, hprimitive⟩ :=
    mem_primitiveFullPairings.mp κB.2
  have hraw :
      Integrable
        (fun v :
            Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
          primitiveIntegrand ρ ε
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder ctx.internalEdges κB.1
            (primitiveAssemble
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder z w v))
        (Measure.pi fun _ => paperMeasure) :=
    integrable_primitiveIntegrand_assemble_of_scaled_offDiagonal
      ρ hε hε1 ctx.one_le_blockOrder
      ctx.internalEdges
      (fun j => scale (ctx.internalSlot j))
      (fun j => hcert.measurable (ctx.internalSlot j))
      (fun j => hcert.scale_pos (ctx.internalSlot j))
      (fun j => hcert.memE (ctx.internalSlot j))
      (fun j u hu => hcert.bound (ctx.internalSlot j) u hu)
      κB z w
  apply hraw.congr
  filter_upwards with v
  exact
    (detJclosedIntegrandWith_eq_primitiveIntegrand_of_full_primitive
      ρ ε (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges
      κB.1 hfull hprimitive
      (primitiveAssemble
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder z w v)).symm

/-- Uniform-in-pairing endpoint form used by the local-collapse Fubini
identity.  The preceding theorem is pointwise, so the a.e. packaging costs
nothing. -/
theorem eventually_integrable_stepClosedIntegrand_section
    (hcert : R324WithinHalfEdgeCertificate ctx.state scale)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
      ∀ κB :
          {κ : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κ ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)},
        Integrable
          (fun v :
              Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder ctx.step.2)
              κB.1 ctx.internalEdges
              (primitiveAssemble
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder p.1 p.2 v))
          (Measure.pi fun _ => paperMeasure) := by
  filter_upwards with p
  intro κB
  exact hcert.integrable_stepClosedIntegrand_section
    hε hε1 κB p.1 p.2

end R324WithinHalfEdgeCertificate

namespace R324WithinHalfStepContext

variable {m : ℕ} {pairing : PartialPairing (Fin m)}
    (ctx : R324WithinHalfStepContext pairing)

/-- A weighted complex local section is sufficient for the exact processed
collapse.  On the zero-weight set both sides vanish; off that set, complex
scalar cancellation recovers the real unweighted integrability premise of
the existing local theorem. -/
theorem rawLocalSpatialIntegral_mul_complexOuter_eq_absorb_of_weighted
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (u : T4) (outer : ℂ)
    (hweighted :
      Integrable
        (fun t :
            Fin (2 * residualBlockOrder ctx.step.2) → T4 =>
          (ctx.rawLocalIntegrand ρ ε u t : ℂ) * outer)
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder ctx.step.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder ctx.step.2)},
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder ctx.step.2)
                κB.1 ctx.internalEdges
                (primitiveAssemble
                  (residualBlockOrder ctx.step.2)
                  ctx.one_le_blockOrder p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε ^
          (2 * residualBlockOrder ctx.step.2) : ℂ) *
        (∫ t :
            Fin (2 * residualBlockOrder ctx.step.2) → T4,
          (ctx.rawLocalIntegrand ρ ε u t : ℂ) * outer
          ∂Measure.pi fun _ => paperMeasure) =
      ((ctx.absorb ρ lam ε).edges
          (r324WithinHalfPredecessorSlot
            ctx.state ctx.step) u : ℂ) * outer := by
  by_cases houter : outer = 0
  · simp [houter]
  · have hscaled := hweighted.const_mul outer⁻¹
    have hcomplex :
        Integrable
          (fun t :
              Fin (2 * residualBlockOrder ctx.step.2) → T4 =>
            (ctx.localIntegrand ρ ε u t : ℂ))
          (Measure.pi fun _ => paperMeasure) := by
      apply hscaled.congr
      filter_upwards with t
      rw [← ctx.rawLocalIntegrand_eq_localIntegrand
        ρ ε u t]
      field_simp
    have hstandard :
        Integrable (ctx.localIntegrand ρ ε u)
          (Measure.pi fun _ => paperMeasure) := by
      simpa using hcomplex.re
    exact
      ctx.rawLocalSpatialIntegral_mul_complexOuter_eq_absorb
        ρ lam ε u outer hstandard hinternal

end R324WithinHalfStepContext

/-! ## Full residual integrability and one-step advance -/

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- Physical analytic state carried at one literal within-half suffix. -/
structure R324WithinHalfResidualAnalyticState
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (x y : T4) where
  scale : Fin (m + 1) → ℝ
  certificate :
    R324WithinHalfEdgeCertificate res.state scale
  full :
    Integrable
      (fun w : res.SurvivingCoordinate → T4 =>
        (res.residualIntegrand ρ ε x y
          (res.reconstruct w) : ℂ))
      (Measure.pi fun _ => paperMeasure)

/-- Endpoint-independent analytic evidence for one within-half transition.

There is deliberately no full residual integrability and no unweighted
`standard` field here.  The former belongs to the actual scalar integral
being transported, while the latter is recovered only off the zero set of
its genuine outer weight. -/
structure R324WithinHalfResidualInternalReady
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail) : Prop where
  internal :
    ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
      ∀ κB :
          {κ : PartialPairing
              (Fin (2 * residualBlockOrder head.2)) //
            κ ∈ primitiveFullPairings
              (residualBlockOrder head.2)},
        Integrable
          (fun w :
              Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder head.2)
              κB.1
              (res.headContext
                head tail hremaining).internalEdges
              (primitiveAssemble
                (residualBlockOrder head.2)
                (res.headContext
                  head tail hremaining).one_le_blockOrder
                p.1 p.2 w))
          (Measure.pi fun _ => paperMeasure)

/-- Full integrability with an arbitrary post-coordinate outer function
gives the exact weighted local sections at almost every post-head tuple.

The local weight is the product of the actual physical outer factor and the
carried post-coordinate factor; neither is cancelled. -/
theorem eventually_integrable_weightedHeadLocal_mul_postOuter_of_integrable
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (x y : T4)
    (postOuter :
      ((res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) → ℂ)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          (res.residualIntegrand ρ ε x y
              (res.reconstruct w) : ℂ) *
            postOuter
              (res.splitSurvivingPiMeasurableEquiv
                head tail hremaining w).2)
        (Measure.pi fun _ => paperMeasure)) :
    ∀ᵐ v ∂(Measure.pi fun _ :
        (res.afterHead
          head tail hremaining).SurvivingCoordinate =>
          paperMeasure),
      Integrable
        (fun t :
            Fin (2 * residualBlockOrder head.2) → T4 =>
          ((res.headContext
              head tail hremaining).rawLocalIntegrand ρ ε
              (res.headPredecessorPoint
                  head tail hremaining x y v -
                res.headSuccessorPoint
                  head tail hremaining x y v) t : ℂ) *
            ((res.headOuterFactor
                head tail hremaining ρ ε x y v : ℂ) *
              postOuter v))
        (Measure.pi fun _ => paperMeasure) := by
  let post :=
    res.afterHead head tail hremaining
  let ctx :=
    res.headContext head tail hremaining
  let μPre : Measure (res.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μHead :
      Measure (Fin (2 * residualBlockOrder head.2) → T4) :=
    Measure.pi fun _ => paperMeasure
  let μPost : Measure (post.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let e :=
    res.splitSurvivingPiMeasurableEquiv
      head tail hremaining
  let g :
      ((Fin (2 * residualBlockOrder head.2) → T4) ×
        (post.SurvivingCoordinate → T4)) → ℂ :=
    fun p =>
      (res.residualIntegrand ρ ε x y
          (res.reconstruct (e.symm p)) : ℂ) *
        postOuter p.2
  have hcomp : Integrable (g ∘ e) μPre := by
    apply hfull.congr
    filter_upwards with w
    dsimp only [Function.comp_apply, g]
    rw [e.symm_apply_apply]
  have hg : Integrable g (μHead.prod μPost) :=
    (res.measurePreserving_splitSurvivingPiMeasurableEquiv
      head tail hremaining).integrable_comp_emb
        e.measurableEmbedding |>.mp hcomp
  filter_upwards [hg.prod_left_ae] with v hv
  let u : T4 :=
    res.headPredecessorPoint
        head tail hremaining x y v -
      res.headSuccessorPoint
        head tail hremaining x y v
  let a : T4 :=
    res.headSuccessorPoint
      head tail hremaining x y v
  let outer : ℂ :=
    (res.headOuterFactor
        head tail hremaining ρ ε x y v : ℂ) *
      postOuter v
  change
    Integrable
      (fun t :
          Fin (2 * residualBlockOrder ctx.step.2) → T4 =>
        (ctx.rawLocalIntegrand ρ ε u t : ℂ) * outer)
      (Measure.pi fun _ => paperMeasure)
  have hshifted :
      Integrable
        (fun t :
            Fin (2 * residualBlockOrder ctx.step.2) → T4 =>
          (ctx.rawLocalIntegrand ρ ε u
            (fun j => t j - a) : ℂ) * outer)
        μHead := by
    apply hv.congr
    filter_upwards with t
    dsimp only [g, e, ctx, u, a, outer]
    rw [
      res.residualIntegrand_reconstruct_split
        head tail hremaining ρ ε x y,
      res.headLocalFactor_reconstruct_split
        head tail hremaining ρ ε x y]
    push_cast
    ring
  let translation := ctx.physicalBlockTranslation a
  have htranslated :
      Integrable
        ((fun t :
            Fin (2 * residualBlockOrder ctx.step.2) → T4 =>
          (ctx.rawLocalIntegrand ρ ε u
            (fun j => t j - a) : ℂ) * outer) ∘
          translation)
        μHead :=
    (ctx.measurePreserving_physicalBlockTranslation a)
      |>.integrable_comp_emb translation.measurableEmbedding
      |>.mpr hshifted
  apply htranslated.congr
  filter_upwards with t
  dsimp only [Function.comp_apply]
  rw [show translation t = fun j => t j + a by
    exact ctx.physicalBlockTranslation_apply a t]
  change
    (ctx.rawLocalIntegrand ρ ε u
        (fun j => (t j + a) - a) : ℂ) * outer =
      (ctx.rawLocalIntegrand ρ ε u t : ℂ) * outer
  have ht : (fun j => (t j + a) - a) = t := by
    funext j
    abel
  rw [ht]

/-- Unweighted-current specialization of the preceding weighted-section
theorem.  This is useful for the optional scalar analytic-state corollary. -/
theorem eventually_integrable_weightedHeadLocal_of_integrable
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (x y : T4)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          (res.residualIntegrand ρ ε x y
            (res.reconstruct w) : ℂ))
        (Measure.pi fun _ => paperMeasure)) :
    ∀ᵐ v ∂(Measure.pi fun _ :
        (res.afterHead
          head tail hremaining).SurvivingCoordinate =>
          paperMeasure),
      Integrable
        (fun t :
            Fin (2 * residualBlockOrder head.2) → T4 =>
          ((res.headContext
              head tail hremaining).rawLocalIntegrand ρ ε
              (res.headPredecessorPoint
                  head tail hremaining x y v -
                res.headSuccessorPoint
                  head tail hremaining x y v) t : ℂ) *
            (res.headOuterFactor
              head tail hremaining ρ ε x y v : ℂ))
        (Measure.pi fun _ => paperMeasure) := by
  have hfull' :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          (res.residualIntegrand ρ ε x y
              (res.reconstruct w) : ℂ) *
            (1 : ℂ))
        (Measure.pi fun _ => paperMeasure) := by
    simpa only [mul_one] using hfull
  simpa only [mul_one] using
    eventually_integrable_weightedHeadLocal_mul_postOuter_of_integrable
      res head tail hremaining x y (fun _ => (1 : ℂ)) hfull'

/-- One exact head transition with an arbitrary post-coordinate complex
outer factor, using only full *weighted* current integrability and the
endpoint-independent internal certificate.

Its premise uses weighted current integrability instead of unweighted local
integrability at every post tuple. -/
theorem lamEps_pow_integral_residual_mul_postOuter_eq_afterHead_of_weighted
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (x y : T4)
    (postOuter :
      ((res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) → ℂ)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          (res.residualIntegrand ρ ε x y
              (res.reconstruct w) : ℂ) *
            postOuter
              (res.splitSurvivingPiMeasurableEquiv
                head tail hremaining w).2)
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder head.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder head.2)},
          Integrable
            (fun w :
                Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder head.2)
                κB.1
                (res.headContext
                  head tail hremaining).internalEdges
                (primitiveAssemble
                  (residualBlockOrder head.2)
                  (res.headContext
                    head tail hremaining).one_le_blockOrder
                  p.1 p.2 w))
            (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
        (∫ w : res.SurvivingCoordinate → T4,
          (res.residualIntegrand ρ ε x y
              (res.reconstruct w) : ℂ) *
            postOuter
              (res.splitSurvivingPiMeasurableEquiv
                head tail hremaining w).2
          ∂Measure.pi fun _ => paperMeasure) =
      (lamEps lam ε : ℂ) ^
          (2 *
            (res.afterHead
              head tail hremaining).remainingOrder) *
        (∫ v :
            (res.afterHead
              head tail hremaining).SurvivingCoordinate → T4,
          ((res.afterHead
              head tail hremaining).residualIntegrand
                ρ ε x y
                ((res.afterHead
                  head tail hremaining).reconstruct v) : ℂ) *
            postOuter v
          ∂Measure.pi fun _ => paperMeasure) := by
  have hsplit :=
    res.integral_splitSurviving_post_first
      head tail hremaining
      (fun w : res.SurvivingCoordinate → T4 =>
        (res.residualIntegrand ρ ε x y
            (res.reconstruct w) : ℂ) *
          postOuter
            (res.splitSurvivingPiMeasurableEquiv
              head tail hremaining w).2)
      hfull
  have hexponent :
      2 * res.remainingOrder =
        2 *
            (res.afterHead
              head tail hremaining).remainingOrder +
          2 * residualBlockOrder head.2 := by
    have horder :=
      res.remainingOrder_head head tail hremaining
    omega
  rw [hexponent, pow_add, hsplit, mul_assoc,
    ← integral_const_mul]
  apply congrArg (fun value : ℂ =>
    (lamEps lam ε : ℂ) ^
      (2 *
        (res.afterHead
          head tail hremaining).remainingOrder) * value)
  apply integral_congr_ae
  have hweighted :=
    eventually_integrable_weightedHeadLocal_mul_postOuter_of_integrable
      res head tail hremaining x y postOuter hfull
  filter_upwards [hweighted] with v hv
  have hsplitSnd :
      ∀ t : Fin (2 * residualBlockOrder head.2) → T4,
        (res.splitSurvivingPiMeasurableEquiv
            head tail hremaining
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v))).2 =
          v := by
    intro t
    exact congrArg Prod.snd
      ((res.splitSurvivingPiMeasurableEquiv
        head tail hremaining).apply_symm_apply (t, v))
  simp_rw [hsplitSnd]
  let ctx :=
    res.headContext head tail hremaining
  let u : T4 :=
    res.headPredecessorPoint
        head tail hremaining x y v -
      res.headSuccessorPoint
        head tail hremaining x y v
  let outer : ℂ :=
    (res.headOuterFactor
        head tail hremaining ρ ε x y v : ℂ) *
      postOuter v
  have hinner :
      (∫ t :
          Fin (2 * residualBlockOrder head.2) → T4,
        (res.residualIntegrand ρ ε x y
            (res.reconstruct
              ((res.splitSurvivingPiMeasurableEquiv
                head tail hremaining).symm (t, v))) : ℂ) *
          postOuter v
        ∂Measure.pi fun _ => paperMeasure) =
        ∫ t :
            Fin (2 * residualBlockOrder head.2) → T4,
          (ctx.rawLocalIntegrand ρ ε u t : ℂ) * outer
          ∂Measure.pi fun _ => paperMeasure := by
    calc
      _ =
          ∫ t :
              Fin (2 * residualBlockOrder head.2) → T4,
            ((res.headLocalFactor
                head tail hremaining ρ ε x y
                (res.reconstruct
                  ((res.splitSurvivingPiMeasurableEquiv
                    head tail hremaining).symm (t, v))) : ℝ) : ℂ) *
              outer
            ∂Measure.pi fun _ => paperMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        rw [
          res.residualIntegrand_reconstruct_split
            head tail hremaining ρ ε x y]
        dsimp only [outer]
        push_cast
        ring
      _ =
          ∫ t :
              Fin (2 * residualBlockOrder head.2) → T4,
            (ctx.rawLocalIntegrand ρ ε u
              (fun j =>
                t j -
                  res.headSuccessorPoint
                    head tail hremaining x y v) : ℂ) *
              outer
            ∂Measure.pi fun _ => paperMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp only [ctx, u]
        rw [
          res.headLocalFactor_reconstruct_split
            head tail hremaining ρ ε x y]
      _ = _ :=
        res.integral_head_rawLocal_sub_const_mul_complex
          head tail hremaining u
          (res.headSuccessorPoint
            head tail hremaining x y v) outer
  have hcollapse :=
    ctx.rawLocalSpatialIntegral_mul_complexOuter_eq_absorb_of_weighted
      ρ lam ε u outer hv hinternal
  have hpost :
      ((res.afterHead
          head tail hremaining).residualIntegrand
            ρ ε x y
            ((res.afterHead
              head tail hremaining).reconstruct v) : ℂ) *
          postOuter v =
        (((res.afterHead
            head tail hremaining).state.edges
              (r324WithinHalfPredecessorSlot
                res.state head) u : ℝ) : ℂ) *
          outer := by
    rw [
      res.afterHead_residualIntegrand
        head tail hremaining ρ ε x y v,
      res.afterHead_residualChainEdgeFactor_predecessor_reconstruct
        head tail hremaining x y v]
    dsimp only [u, outer]
    push_cast
    ring
  rw [hinner, hpost]
  convert hcollapse using 1 <;>
    simp only [ctx, u,
      R324WithinHalfResidualPrefix.headContext,
      R324WithinHalfResidualPrefix.afterHead_state] ;
    rfl

/-- Full residual integrability is preserved by one literal head collapse.

The proof transports the current integrand through the actual
measure-preserving head/post split, integrates the head section, and uses
the already proved exact one-section transition. -/
theorem integrable_residualIntegrand_afterHead
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (x y : T4)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          (res.residualIntegrand ρ ε x y
            (res.reconstruct w) : ℂ))
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder head.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder head.2)},
          Integrable
            (fun w :
                Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder head.2)
                κB.1
                (res.headContext
                  head tail hremaining).internalEdges
                (primitiveAssemble
                  (residualBlockOrder head.2)
                  (res.headContext
                    head tail hremaining).one_le_blockOrder
                  p.1 p.2 w))
            (Measure.pi fun _ => paperMeasure)) :
    Integrable
      (fun v :
          (res.afterHead
            head tail hremaining).SurvivingCoordinate → T4 =>
        ((res.afterHead
          head tail hremaining).residualIntegrand
            ρ ε x y
            ((res.afterHead
              head tail hremaining).reconstruct v) : ℂ))
      (Measure.pi fun _ => paperMeasure) := by
  let post :=
    res.afterHead head tail hremaining
  let μPre : Measure (res.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μHead :
      Measure (Fin (2 * residualBlockOrder head.2) → T4) :=
    Measure.pi fun _ => paperMeasure
  let μPost : Measure (post.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let e :=
    res.splitSurvivingPiMeasurableEquiv
      head tail hremaining
  let g :
      ((Fin (2 * residualBlockOrder head.2) → T4) ×
        (post.SurvivingCoordinate → T4)) → ℂ :=
    fun p =>
      (res.residualIntegrand ρ ε x y
        (res.reconstruct (e.symm p)) : ℂ)
  have hcomp : Integrable (g ∘ e) μPre := by
    apply hfull.congr
    filter_upwards with w
    simp only [Function.comp_apply, g, e.symm_apply_apply]
  have hg : Integrable g (μHead.prod μPost) :=
    (res.measurePreserving_splitSurvivingPiMeasurableEquiv
      head tail hremaining).integrable_comp_emb
        e.measurableEmbedding |>.mp hcomp
  have hintegral :
      Integrable
        (fun v : post.SurvivingCoordinate → T4 =>
          ∫ t, g (t, v) ∂μHead)
        μPost :=
    hg.integral_prod_right
  have hscaled :
      Integrable
        (fun v : post.SurvivingCoordinate → T4 =>
          (lamEps lam ε : ℂ) ^
              (2 * residualBlockOrder head.2) *
            (∫ t, g (t, v) ∂μHead))
        μPost :=
    hintegral.const_mul _
  have hweighted :=
    eventually_integrable_weightedHeadLocal_of_integrable
      res head tail hremaining x y hfull
  apply hscaled.congr
  filter_upwards [hweighted] with v hv
  let ctx :=
    res.headContext head tail hremaining
  let u : T4 :=
    res.headPredecessorPoint
        head tail hremaining x y v -
      res.headSuccessorPoint
        head tail hremaining x y v
  let outer : ℂ :=
    (res.headOuterFactor
      head tail hremaining ρ ε x y v : ℂ)
  have hinner :
      (∫ t, g (t, v) ∂μHead) =
        ∫ t :
            Fin (2 * residualBlockOrder head.2) → T4,
          (ctx.rawLocalIntegrand ρ ε u t : ℂ) * outer
          ∂Measure.pi fun _ => paperMeasure := by
    calc
      (∫ t, g (t, v) ∂μHead) =
          ∫ t :
              Fin (2 * residualBlockOrder head.2) → T4,
            ((res.headLocalFactor
                head tail hremaining ρ ε x y
                (res.reconstruct
                  ((res.splitSurvivingPiMeasurableEquiv
                    head tail hremaining).symm (t, v))) : ℝ) : ℂ) *
              outer
            ∂Measure.pi fun _ => paperMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp only [g, e, outer]
        rw [
          res.residualIntegrand_reconstruct_split
            head tail hremaining ρ ε x y]
        push_cast
        rfl
      _ =
          ∫ t :
              Fin (2 * residualBlockOrder head.2) → T4,
            (ctx.rawLocalIntegrand ρ ε u
              (fun j =>
                t j -
                  res.headSuccessorPoint
                    head tail hremaining x y v) : ℂ) *
              outer
            ∂Measure.pi fun _ => paperMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp only [ctx, u]
        rw [
          res.headLocalFactor_reconstruct_split
            head tail hremaining ρ ε x y]
      _ = _ :=
        res.integral_head_rawLocal_sub_const_mul_complex
          head tail hremaining u
          (res.headSuccessorPoint
            head tail hremaining x y v) outer
  have hcollapse :=
    ctx.rawLocalSpatialIntegral_mul_complexOuter_eq_absorb_of_weighted
      ρ lam ε u outer hv hinternal
  have hpost :
      ((res.afterHead
          head tail hremaining).residualIntegrand ρ ε x y
          ((res.afterHead
            head tail hremaining).reconstruct v) : ℂ) =
        (((res.afterHead
          head tail hremaining).state.edges
            (r324WithinHalfPredecessorSlot
              res.state head) u : ℝ) : ℂ) * outer := by
    rw [
      res.afterHead_residualIntegrand
        head tail hremaining ρ ε x y v,
      res.afterHead_residualChainEdgeFactor_predecessor_reconstruct
        head tail hremaining x y v]
    dsimp only [u, outer]
    push_cast
    rfl
  change
    (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder head.2) *
        (∫ t, g (t, v) ∂μHead) =
      (post.residualIntegrand ρ ε x y
        (post.reconstruct v) : ℂ)
  rw [hinner, hpost]
  convert hcollapse using 1 <;>
    simp only [ctx, u,
      R324WithinHalfResidualPrefix.headContext,
      R324WithinHalfResidualPrefix.afterHead_state] ;
    rfl

/-- Build the honest weighted ready evidence at one certified analytic
state. -/
theorem R324WithinHalfResidualAnalyticState.internalReady
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {x y : T4}
    (state : R324WithinHalfResidualAnalyticState res x y)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    R324WithinHalfResidualInternalReady
      res head tail hremaining := by
  refine ⟨?_⟩
  exact
    R324WithinHalfEdgeCertificate.eventually_integrable_stepClosedIntegrand_section
      (ctx := res.headContext head tail hremaining)
      state.certificate hε hε1

/-- Advance a certified analytic state through one actual schedule head.
The caller supplies only the genuine next edge certificate, normally
produced by the local Proposition 4.1 certificate transport. -/
def R324WithinHalfResidualAnalyticState.advance
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {x y : T4}
    (state : R324WithinHalfResidualAnalyticState res x y)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (nextScale : Fin (m + 1) → ℝ)
    (nextCertificate :
      R324WithinHalfEdgeCertificate
        (res.afterHead head tail hremaining).state
        nextScale) :
    R324WithinHalfResidualAnalyticState
      (res.afterHead head tail hremaining) x y := by
  let ready :=
    state.internalReady head tail hremaining hε hε1
  refine ⟨nextScale, nextCertificate, ?_⟩
  exact
    integrable_residualIntegrand_afterHead
      res head tail hremaining x y
      state.full ready.internal

/-! ## Endpoint-independent certified analytic trace -/

/-- A data-valued analytic trace through the literal within-half suffix.

At a nonterminal node the trace stores exactly the internal Fubini evidence
needed for the local primitive collapse and the certificate of the new edge
state.  Full weighted integrability is intentionally not stored: it depends
on the endpoints and on the terminal outer functional, and is supplied to
the exact iteration theorem below. -/
inductive R324WithinHalfCertifiedAnalyticTrace
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)} :
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing) →
    (Fin (m + 1) → ℝ) → Type
  | terminal
      (res :
        R324WithinHalfResidualPrefix ρ lam ε pairing)
      (scale : Fin (m + 1) → ℝ)
      (hremaining : res.remaining = [])
      (certificate :
        R324WithinHalfEdgeCertificate res.state scale) :
      R324WithinHalfCertifiedAnalyticTrace res scale
  | step
      (res :
        R324WithinHalfResidualPrefix ρ lam ε pairing)
      (head : R322ExtractionStep m)
      (tail : List (R322ExtractionStep m))
      (hremaining : res.remaining = head :: tail)
      (scale : Fin (m + 1) → ℝ)
      (internal :
        R324WithinHalfResidualInternalReady
          res head tail hremaining)
      (nextScale : Fin (m + 1) → ℝ)
      (nextCertificate :
        R324WithinHalfEdgeCertificate
          (res.afterHead head tail hremaining).state
          nextScale)
      (next :
        R324WithinHalfCertifiedAnalyticTrace
          (res.afterHead head tail hremaining) nextScale) :
      R324WithinHalfCertifiedAnalyticTrace res scale

namespace R324WithinHalfCertifiedAnalyticTrace

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- Structural recursion on the literal suffix turns the quantitative local
provider into the endpoint-independent analytic trace. -/
def of_localBlockProvider
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K pairing)
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing)
    (scale : Fin (m + 1) → ℝ)
    (certificate :
      R324WithinHalfEdgeCertificate res.state scale) :
    R324WithinHalfCertifiedAnalyticTrace res scale := by
  cases hremaining : res.remaining with
  | nil =>
      exact
        R324WithinHalfCertifiedAnalyticTrace.terminal
          res scale hremaining certificate
  | cons head tail =>
      obtain ⟨_localBound, nextCertificate⟩ :=
        provider res head tail hremaining scale certificate
      let nextScale :=
        r324WithinHalfUpdatedEdgeScale
          (res.headContext head tail hremaining)
          scale C lam K
      let internal :
          R324WithinHalfResidualInternalReady
            res head tail hremaining :=
        ⟨R324WithinHalfEdgeCertificate.eventually_integrable_stepClosedIntegrand_section
          (ctx := res.headContext head tail hremaining)
          certificate hε hε1⟩
      exact
        R324WithinHalfCertifiedAnalyticTrace.step
          res head tail hremaining scale internal
          nextScale nextCertificate
          (of_localBlockProvider hε hε1 provider
            (res.afterHead head tail hremaining)
            nextScale nextCertificate)
termination_by res.remaining.length
decreasing_by simp [hremaining]

/-- The literal terminal residual prefix reached by a certified trace. -/
def terminalPrefix
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale) :
    R324WithinHalfResidualPrefix ρ lam ε pairing :=
  match trace with
  | .terminal .. => res
  | @R324WithinHalfCertifiedAnalyticTrace.step
      _ _ _ _ _
      _ _ _ _ _ _ _ _ next => next.terminalPrefix

/-- Restrict a current surviving tuple through every genuine head/post
split until it lies on the actual terminal carrier. -/
def terminalProjection
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale) :
    (res.SurvivingCoordinate → T4) →
      (trace.terminalPrefix.SurvivingCoordinate → T4) :=
  match trace with
  | .terminal .. => fun v => v
  | @R324WithinHalfCertifiedAnalyticTrace.step
      _ _ _ _ _
      current head tail hremaining _ _ _ _ next =>
      fun v =>
        next.terminalProjection
          (current.splitSurvivingPiMeasurableEquiv
            head tail hremaining v).2

/-- Full weighted integrability at precisely the nonterminal scalar
integrals traversed by the trace. -/
def WeightedIntegrableAlong
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (x y : T4)
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale)
    (outer :
      (trace.terminalPrefix.SurvivingCoordinate → T4) → ℂ) :
    Prop :=
  match trace with
  | .terminal .. => True
  | @R324WithinHalfCertifiedAnalyticTrace.step
      _ _ _ _ _
      current head tail hremaining _ _ _ _ next =>
      Integrable
          (fun v : current.SurvivingCoordinate → T4 =>
            (current.residualIntegrand ρ ε x y
                (current.reconstruct v) : ℂ) *
              outer
                (next.terminalProjection
                  (current.splitSurvivingPiMeasurableEquiv
                    head tail hremaining v).2))
          (Measure.pi fun _ => paperMeasure) ∧
        next.WeightedIntegrableAlong x y outer

/-- The terminal prefix has the literal empty suffix. -/
theorem terminalPrefix_remaining_eq_nil
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale) :
    trace.terminalPrefix.remaining = [] := by
  induction trace with
  | terminal terminal scale hremaining certificate =>
      change terminal.remaining = []
      exact hremaining
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      exact ih

/-- The terminal prefix has processed the complete analytic schedule. -/
theorem terminalPrefix_processed_eq_schedule
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale) :
    trace.terminalPrefix.state.processed =
      r322AnalyticSchedule pairing := by
  induction trace with
  | terminal terminal scale hremaining certificate =>
      have hschedule := terminal.schedule_eq
      rw [hremaining, List.append_nil] at hschedule
      change terminal.state.processed =
        r322AnalyticSchedule pairing
      exact hschedule.symm
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      exact ih

/-- Exact weighted iteration through every certified head in the literal
suffix. -/
theorem lamEps_pow_integral_mul_terminalOuter_eq_terminal
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (x y : T4)
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale)
    (outer :
      (trace.terminalPrefix.SurvivingCoordinate → T4) → ℂ)
    (hweighted :
      trace.WeightedIntegrableAlong x y outer) :
    (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
        (∫ v : res.SurvivingCoordinate → T4,
          (res.residualIntegrand ρ ε x y
              (res.reconstruct v) : ℂ) *
            outer (trace.terminalProjection v)
          ∂Measure.pi fun _ => paperMeasure) =
      ∫ v :
          trace.terminalPrefix.SurvivingCoordinate → T4,
        ((trace.terminalPrefix.residualIntegrand
            ρ ε x y
            (trace.terminalPrefix.reconstruct v) : ℂ) *
          outer v)
        ∂Measure.pi fun _ => paperMeasure := by
  induction trace with
  | terminal terminal scale hremaining certificate =>
      have horder :
          terminal.remainingOrder = 0 := by
        unfold R324WithinHalfResidualPrefix.remainingOrder
        rw [hremaining]
        rfl
      simp only [terminalPrefix, terminalProjection]
      rw [horder]
      simp
      rfl
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      have hcurrent :
          Integrable
            (fun v : current.SurvivingCoordinate → T4 =>
              (current.residualIntegrand ρ ε x y
                  (current.reconstruct v) : ℂ) *
                outer
                  (next.terminalProjection
                    (current.splitSurvivingPiMeasurableEquiv
                      head tail hremaining v).2))
            (Measure.pi fun _ => paperMeasure) :=
        hweighted.1
      have hnext :
          next.WeightedIntegrableAlong x y outer :=
        hweighted.2
      change
        (lamEps lam ε : ℂ) ^
              (2 * current.remainingOrder) *
            (∫ v : current.SurvivingCoordinate → T4,
              (current.residualIntegrand ρ ε x y
                  (current.reconstruct v) : ℂ) *
                outer
                  (next.terminalProjection
                    (current.splitSurvivingPiMeasurableEquiv
                      head tail hremaining v).2)
              ∂Measure.pi fun _ => paperMeasure) =
          ∫ v :
              next.terminalPrefix.SurvivingCoordinate → T4,
            ((next.terminalPrefix.residualIntegrand
                ρ ε x y
                (next.terminalPrefix.reconstruct v) : ℂ) *
              outer v)
            ∂Measure.pi fun _ => paperMeasure
      rw [
        current.lamEps_pow_integral_residual_mul_postOuter_eq_afterHead_of_weighted
          head tail hremaining x y
          (fun v => outer (next.terminalProjection v))
          hcurrent internal.internal]
      exact ih outer hnext

end R324WithinHalfCertifiedAnalyticTrace

end R324WithinHalfResidualPrefix

end

end Anderson4D
