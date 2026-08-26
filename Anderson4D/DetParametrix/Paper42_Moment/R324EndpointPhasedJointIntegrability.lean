import Anderson4D.DetParametrix.Paper42_Moment.R324OrdinaryAlongDischarge
import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalSeam

/-!
# Joint integrability for the retained-endpoint transport

Paper Step 4(A) keeps all untouched endpoint parameters outside the signed
within-half eliminations.  The scalar transport in the alternating driver is
therefore not enough at the retained outgoing block: Fubini needs genuine
joint integrability in those parameters and the surviving spatial carrier.

This file is the parameter-carrying version of the two existing scalar
handover proofs.  It uses the same head/post splitting equivalence and the
same fixed-section collapse identities.  No norm estimate or new route is
introduced.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}

/-! ## One ordinary head -/

/-- Fixed post coordinates: the ordinary phased head integral is exactly the
post-head phased density.  This is the pointwise identity used implicitly in
the scalar integrability handover, exposed here so an arbitrary measured
parameter can remain outside the head integral. -/
theorem
    lamEps_pow_integral_incomingPhasedResidualDensity_head_eq_afterHead_of_ne_zero
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (hpred : r324WithinHalfPredecessorSlot res.state head ≠ 0)
    (x y : T4)
    (postCoefficient :
      ((res.afterHead head tail hremaining).SurvivingCoordinate -> T4) ->
        Complex)
    (k : Z4)
    (v : (res.afterHead head tail hremaining).SurvivingCoordinate -> T4)
    (hhead :
      Integrable
        (fun t : Fin (2 * residualBlockOrder head.2) -> T4 =>
          res.incomingPhasedResidualDensity
            (postCoefficient v) k rho eps x y
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v)))
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ ae_p ∂(paperMeasure.prod paperMeasure),
        forall kappaB :
            {kappa : PartialPairing
                (Fin (2 * residualBlockOrder head.2)) //
              kappa ∈ primitiveFullPairings
                (residualBlockOrder head.2)},
          Integrable
            (fun w : Fin (2 * residualBlockOrder head.2 - 2) -> T4 =>
              detJclosedIntegrandWith rho eps
                (2 * residualBlockOrder head.2) kappaB.1
                (res.headContext head tail hremaining).internalEdges
                (primitiveAssemble
                  (residualBlockOrder head.2)
                  (res.headContext head tail hremaining).one_le_blockOrder
                  ae_p.1 ae_p.2 w))
            (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam eps : Complex) ^ (2 * residualBlockOrder head.2) *
        (∫ t : Fin (2 * residualBlockOrder head.2) -> T4,
            res.incomingPhasedResidualDensity
              (postCoefficient v) k rho eps x y
              ((res.splitSurvivingPiMeasurableEquiv
                head tail hremaining).symm (t, v))
          ∂Measure.pi fun _ => paperMeasure) =
      (res.afterHead head tail hremaining).incomingPhasedResidualDensity
        (postCoefficient v) k rho eps x y v := by
  let post := res.afterHead head tail hremaining
  let split := res.splitSurvivingPiMeasurableEquiv head tail hremaining
  let muHead := Measure.pi fun _ : Fin (2 * residualBlockOrder head.2) =>
    paperMeasure
  let ctx := res.headContext head tail hremaining
  let u : T4 :=
    res.headPredecessorPoint head tail hremaining x y v -
      res.headSuccessorPoint head tail hremaining x y v
  let a : T4 := res.headSuccessorPoint head tail hremaining x y v
  let erasedOuter : Complex :=
    (res.incomingErasedHeadOuterFactor
      head tail hremaining rho eps x y v : Complex)
  let outer : Complex :=
    postCoefficient v * charT4 k (post.incomingPhaseAnchor x y v) *
      erasedOuter
  have hpre
      (t : Fin (2 * residualBlockOrder head.2) -> T4) :=
    res.incomingPhasedResidualDensity_reconstruct_split_of_ne_zero
      head tail hremaining hpred (postCoefficient v) k
      rho eps x y t v
  have hpost :=
    res.afterHead_incomingErasedResidualIntegrand_of_ne_zero
      head tail hremaining hpred rho eps x y v
  have hinner :
      (∫ t : Fin (2 * residualBlockOrder head.2) -> T4,
            res.incomingPhasedResidualDensity
              (postCoefficient v) k rho eps x y (split.symm (t, v))
          ∂muHead) =
        ∫ t : Fin (2 * residualBlockOrder head.2) -> T4,
          (ctx.rawLocalIntegrand rho eps u t : Complex) * outer
          ∂Measure.pi fun _ => paperMeasure := by
    calc
      _ = ∫ t : Fin (2 * residualBlockOrder head.2) -> T4,
            (res.headLocalFactor head tail hremaining rho eps x y
              (res.reconstruct (split.symm (t, v))) : Complex) * outer
          ∂Measure.pi fun _ => paperMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hpre t]
        dsimp only [outer, erasedOuter, post, split]
        ring
      _ = ∫ t : Fin (2 * residualBlockOrder head.2) -> T4,
            (ctx.rawLocalIntegrand rho eps u (fun j => t j - a) : Complex) *
              outer
          ∂Measure.pi fun _ => paperMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp only [ctx, u, a]
        rw [res.headLocalFactor_reconstruct_split
          head tail hremaining rho eps x y]
      _ = _ :=
        res.integral_head_rawLocal_sub_const_mul_complex
          head tail hremaining u a outer
  have hshifted :
      Integrable
        (fun t : Fin (2 * residualBlockOrder ctx.step.2) -> T4 =>
          (ctx.rawLocalIntegrand rho eps u (fun j => t j - a) : Complex) *
            outer)
        muHead := by
    apply hhead.congr
    filter_upwards with t
    rw [hpre t,
      res.headLocalFactor_reconstruct_split
        head tail hremaining rho eps x y]
    dsimp only [ctx, u, a, outer, erasedOuter, post, split]
    ring
  let translation := ctx.physicalBlockTranslation a
  have htranslated :
      Integrable
        ((fun t : Fin (2 * residualBlockOrder ctx.step.2) -> T4 =>
          (ctx.rawLocalIntegrand rho eps u (fun j => t j - a) : Complex) *
            outer) ∘ translation)
        muHead :=
    (ctx.measurePreserving_physicalBlockTranslation a)
      |>.integrable_comp_emb translation.measurableEmbedding
      |>.mpr hshifted
  have hweighted :
      Integrable
        (fun t : Fin (2 * residualBlockOrder ctx.step.2) -> T4 =>
          (ctx.rawLocalIntegrand rho eps u t : Complex) * outer)
        muHead := by
    apply htranslated.congr
    filter_upwards with t
    dsimp only [Function.comp_apply]
    rw [show translation t = fun j => t j + a by
      exact ctx.physicalBlockTranslation_apply a t]
    change
      (ctx.rawLocalIntegrand rho eps u
          (fun j => (t j + a) - a) : Complex) * outer =
        (ctx.rawLocalIntegrand rho eps u t : Complex) * outer
    have ht : (fun j => (t j + a) - a) = t := by
      funext j
      abel
    rw [ht]
  have hlocal :=
    ctx.rawLocalSpatialIntegral_mul_complexOuter_eq_absorb_of_weighted
      rho lam eps u outer hweighted hinternal
  have hpostDensity :
      post.incomingPhasedResidualDensity
          (postCoefficient v) k rho eps x y v =
        (((post.state.edges
            (r324WithinHalfPredecessorSlot res.state head) u : Real) :
              Complex) * outer) := by
    unfold incomingPhasedResidualDensity
    rw [hpost,
      res.afterHead_residualChainEdgeFactor_predecessor_reconstruct
        head tail hremaining x y v]
    dsimp only [u, outer, erasedOuter]
    push_cast
    ring
  calc
    (lamEps lam eps : Complex) ^ (2 * residualBlockOrder head.2) *
        (∫ t : Fin (2 * residualBlockOrder head.2) -> T4,
            res.incomingPhasedResidualDensity
              (postCoefficient v) k rho eps x y (split.symm (t, v))
          ∂muHead) =
      (lamEps lam eps : Complex) ^ (2 * residualBlockOrder head.2) *
        (∫ t : Fin (2 * residualBlockOrder head.2) -> T4,
          (ctx.rawLocalIntegrand rho eps u t : Complex) * outer
          ∂Measure.pi fun _ => paperMeasure) := by rw [hinner]
    _ = (((ctx.absorb rho lam eps).edges
          (r324WithinHalfPredecessorSlot res.state head) u : Real) :
            Complex) * outer := hlocal
    _ = post.incomingPhasedResidualDensity
          (postCoefficient v) k rho eps x y v := by
      rw [hpostDensity]
      rfl

/-- Joint integrability crosses one ordinary head while arbitrary measured
endpoint parameters remain outside the head integral. -/
theorem integrable_joint_afterHead_incomingPhasedResidualDensity_of_ne_zero
    {Y : Type*} [MeasurableSpace Y]
    (nu : Measure Y) [SFinite nu]
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (hpred : r324WithinHalfPredecessorSlot res.state head ≠ 0)
    (x y : Y -> T4)
    (postCoefficient : Y ->
      ((res.afterHead head tail hremaining).SurvivingCoordinate -> T4) ->
        Complex)
    (k : Z4)
    (hfull :
      Integrable
        (fun p : Y × (res.SurvivingCoordinate -> T4) =>
          res.incomingPhasedResidualDensity
            (postCoefficient p.1
              (res.splitSurvivingPiMeasurableEquiv
                head tail hremaining p.2).2)
            k rho eps (x p.1) (y p.1) p.2)
        (nu.prod (Measure.pi fun _ => paperMeasure)))
    (hinternal :
      ∀ᵐ ae_p ∂(paperMeasure.prod paperMeasure),
        forall kappaB :
            {kappa : PartialPairing
                (Fin (2 * residualBlockOrder head.2)) //
              kappa ∈ primitiveFullPairings
                (residualBlockOrder head.2)},
          Integrable
            (fun w : Fin (2 * residualBlockOrder head.2 - 2) -> T4 =>
              detJclosedIntegrandWith rho eps
                (2 * residualBlockOrder head.2) kappaB.1
                (res.headContext head tail hremaining).internalEdges
                (primitiveAssemble
                  (residualBlockOrder head.2)
                  (res.headContext head tail hremaining).one_le_blockOrder
                  ae_p.1 ae_p.2 w))
            (Measure.pi fun _ => paperMeasure)) :
    Integrable
      (fun p : Y ×
          ((res.afterHead head tail hremaining).SurvivingCoordinate -> T4) =>
        (res.afterHead head tail hremaining).incomingPhasedResidualDensity
          (postCoefficient p.1 p.2) k rho eps (x p.1) (y p.1) p.2)
      (nu.prod (Measure.pi fun _ => paperMeasure)) := by
  let post := res.afterHead head tail hremaining
  let split := res.splitSurvivingPiMeasurableEquiv head tail hremaining
  let muPre := Measure.pi fun _ : res.SurvivingCoordinate => paperMeasure
  let muHead := Measure.pi fun _ : Fin (2 * residualBlockOrder head.2) =>
    paperMeasure
  let muPost := Measure.pi fun _ : post.SurvivingCoordinate => paperMeasure
  let splitWithParameter :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl Y) split
  have hsplit : MeasurePreserving splitWithParameter
      (nu.prod muPre) (nu.prod (muHead.prod muPost)) :=
    (MeasurePreserving.id nu).prod
      (res.measurePreserving_splitSurvivingPiMeasurableEquiv
        head tail hremaining)
  let f : Y ×
      ((Fin (2 * residualBlockOrder head.2) -> T4) ×
        (post.SurvivingCoordinate -> T4)) -> Complex :=
    fun q => res.incomingPhasedResidualDensity
      (postCoefficient q.1 q.2.2) k rho eps (x q.1) (y q.1)
      (split.symm q.2)
  have hf : Integrable f (nu.prod (muHead.prod muPost)) := by
    refine (hsplit.integrable_comp_emb
      splitWithParameter.measurableEmbedding).mp ?_
    apply hfull.congr
    filter_upwards with p
    rcases p with ⟨parameter, coordinates⟩
    change _ = res.incomingPhasedResidualDensity
      (postCoefficient parameter (split coordinates).2) k rho eps
      (x parameter) (y parameter) (split.symm (split coordinates))
    rw [split.symm_apply_apply]
  let pull := r324IncomingExceptionalHeadPullMeasurableEquiv
    Y (Fin (2 * residualBlockOrder head.2) -> T4)
      (post.SurvivingCoordinate -> T4)
  have hpull : MeasurePreserving pull
      (nu.prod (muHead.prod muPost)) (muHead.prod (nu.prod muPost)) :=
    measurePreserving_r324IncomingExceptionalHeadPullMeasurableEquiv
      nu muHead muPost
  let g : (Fin (2 * residualBlockOrder head.2) -> T4) ×
      (Y × (post.SurvivingCoordinate -> T4)) -> Complex :=
    fun q => res.incomingPhasedResidualDensity
      (postCoefficient q.2.1 q.2.2) k rho eps
      (x q.2.1) (y q.2.1) (split.symm (q.1, q.2.2))
  have hg : Integrable g (muHead.prod (nu.prod muPost)) := by
    refine (hpull.integrable_comp_emb pull.measurableEmbedding).mp ?_
    apply hf.congr
    filter_upwards with q
    rcases q with ⟨parameter, headTuple, postTuple⟩
    rfl
  have hmarg := hg.integral_prod_right
  have hscaled := hmarg.const_mul
    ((lamEps lam eps : Complex) ^ (2 * residualBlockOrder head.2))
  apply hscaled.congr
  filter_upwards [hg.prod_left_ae] with q hq
  rcases q with ⟨parameter, postTuple⟩
  exact
    res.lamEps_pow_integral_incomingPhasedResidualDensity_head_eq_afterHead_of_ne_zero
      head tail hremaining hpred (x parameter) (y parameter)
      (postCoefficient parameter) k postTuple hq hinternal

/-! ## Parameter-carrying ordinary traces -/

namespace R324WithinHalfCertifiedAnalyticTrace

/-- Joint form of the ordinary trace handover.  The external parameter is
untouched by every head elimination, exactly as in paper Step 2(f). -/
theorem integrable_joint_trace_end_incomingPhasedResidualDensity
    {Y : Type*} [MeasurableSpace Y]
    (nu : Measure Y) [SFinite nu]
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    {scale : Fin (m + 1) -> Real}
    (trace : R324WithinHalfCertifiedAnalyticTrace res scale)
    (hordinary : trace.OrdinaryAlong)
    (x y : Y -> T4)
    (coefficient : Y ->
      (trace.terminalPrefix.SurvivingCoordinate -> T4) -> Complex)
    (k : Z4)
    (hfull :
      Integrable
        (fun p : Y × (res.SurvivingCoordinate -> T4) =>
          res.incomingPhasedResidualDensity
            (coefficient p.1 (trace.terminalProjection p.2))
            k rho eps (x p.1) (y p.1) p.2)
        (nu.prod (Measure.pi fun _ => paperMeasure))) :
    Integrable
      (fun p : Y ×
          (trace.terminalPrefix.SurvivingCoordinate -> T4) =>
        trace.terminalPrefix.incomingPhasedResidualDensity
          (coefficient p.1 p.2) k rho eps
          (x p.1) (y p.1) p.2)
      (nu.prod (Measure.pi fun _ => paperMeasure)) := by
  induction trace with
  | terminal terminal scale hremaining certificate => exact hfull
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      obtain ⟨hpred, hnext⟩ := hordinary
      have hcurrent :
          Integrable
            (fun p : Y × (current.SurvivingCoordinate -> T4) =>
              current.incomingPhasedResidualDensity
                (coefficient p.1
                  (next.terminalProjection
                    ((current.splitSurvivingPiMeasurableEquiv
                      head tail hremaining p.2).2)))
                k rho eps (x p.1) (y p.1) p.2)
            (nu.prod (Measure.pi fun _ => paperMeasure)) := hfull
      have hpost :=
        current.integrable_joint_afterHead_incomingPhasedResidualDensity_of_ne_zero
          nu head tail hremaining hpred x y
          (fun parameter post =>
            coefficient parameter (next.terminalProjection post))
          k hcurrent internal.internal
      exact ih hnext coefficient hpost

end R324WithinHalfCertifiedAnalyticTrace

/-! ## Ordinary stopped traces and the two-phase exceptional combinator -/

namespace R324WithinHalfStopBeforeStepTrace

variable {terminal : R322ExtractionStep m}
    {suffix : List (R322ExtractionStep m)}

/-- Parameter-carrying ordinary transport to a retained stop. -/
theorem integrable_joint_stop_incomingPhasedResidualDensity
    {Y : Type*} [MeasurableSpace Y]
    (nu : Measure Y) [SFinite nu]
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    {scale : Fin (m + 1) -> Real}
    (trace : R324WithinHalfStopBeforeStepTrace
      terminal suffix res scale)
    (hordinary : trace.OrdinaryAlong)
    (x y : Y -> T4)
    (coefficient : Y ->
      (trace.stopPrefix.SurvivingCoordinate -> T4) -> Complex)
    (k : Z4)
    (hfull :
      Integrable
        (fun p : Y × (res.SurvivingCoordinate -> T4) =>
          res.incomingPhasedResidualDensity
            (coefficient p.1 (trace.stopProjection p.2))
            k rho eps (x p.1) (y p.1) p.2)
        (nu.prod (Measure.pi fun _ => paperMeasure))) :
    Integrable
      (fun p : Y ×
          (trace.stopPrefix.SurvivingCoordinate -> T4) =>
        trace.stopPrefix.incomingPhasedResidualDensity
          (coefficient p.1 p.2) k rho eps (x p.1) (y p.1) p.2)
      (nu.prod (Measure.pi fun _ => paperMeasure)) := by
  induction trace with
  | stop stop scale hremaining certificate => exact hfull
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      obtain ⟨hpred, hnext⟩ := hordinary
      have hpost :=
        current.integrable_joint_afterHead_incomingPhasedResidualDensity_of_ne_zero
          nu head tail hremaining hpred x y
          (fun parameter post =>
            coefficient parameter (next.stopProjection post))
          k hfull internal.internal
      exact ih hnext coefficient hpost

end R324WithinHalfStopBeforeStepTrace

end R324WithinHalfResidualPrefix

end

end Anderson4D
