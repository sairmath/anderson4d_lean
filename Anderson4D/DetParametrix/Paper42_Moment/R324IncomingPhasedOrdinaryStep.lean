import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingPhasedResidualCore
import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfResidualIntegrability

/-!
# Ordinary one-head transport of an incoming Fourier phase

Once the incoming endpoint has been Fourier-integrated, its character is
carried by the sparse successor of slot zero.  If a later primitive head is
not fed by slot zero, that anchor is entirely a post-head coordinate.  The
existing weighted one-head collapse therefore applies verbatim with the
character included in the post outer factor.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-! ## Weighted local sections -/

/-- Full integrability of a phased erased density with a genuinely
post-coordinate-dependent coefficient supplies the exact weighted local
sections almost everywhere.

The complete local weight is retained.  In particular, this statement
does not divide by the coefficient or pull an a.e. unweighted statement
back through the predecessor-minus-successor map. -/
theorem
    eventually_integrable_weightedIncomingPhasedHeadLocal_of_integrable
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (hpred :
      r324WithinHalfPredecessorSlot res.state head ≠ 0)
    (x y : T4)
    (postCoefficient :
      ((res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) → ℂ)
    (k : Z4)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          res.incomingPhasedResidualDensity
            (postCoefficient
              (res.splitSurvivingPiMeasurableEquiv
                head tail hremaining w).2)
            k ρ ε x y w)
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
            (postCoefficient v *
              charT4 k
                ((res.afterHead
                  head tail hremaining).incomingPhaseAnchor
                    x y v) *
              (res.incomingErasedHeadOuterFactor
                head tail hremaining ρ ε x y v : ℂ)))
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
  let split :=
    res.splitSurvivingPiMeasurableEquiv
      head tail hremaining
  let g :
      ((Fin (2 * residualBlockOrder head.2) → T4) ×
        (post.SurvivingCoordinate → T4)) → ℂ :=
    fun p =>
      res.incomingPhasedResidualDensity
        (postCoefficient p.2) k ρ ε x y
        (split.symm p)
  have hcomp : Integrable (g ∘ split) μPre := by
    apply hfull.congr
    filter_upwards with w
    dsimp only [Function.comp_apply, g]
    rw [split.symm_apply_apply]
  have hg : Integrable g (μHead.prod μPost) :=
    (res.measurePreserving_splitSurvivingPiMeasurableEquiv
      head tail hremaining).integrable_comp_emb
        split.measurableEmbedding |>.mp hcomp
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
    postCoefficient v *
      charT4 k (post.incomingPhaseAnchor x y v) *
      (res.incomingErasedHeadOuterFactor
        head tail hremaining ρ ε x y v : ℂ)
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
    dsimp only [g, split]
    rw [
      res.incomingPhasedResidualDensity_reconstruct_split_of_ne_zero
        head tail hremaining hpred
        (postCoefficient v) k ρ ε x y t v,
      res.headLocalFactor_reconstruct_split
        head tail hremaining ρ ε x y]
    dsimp only [ctx, u, a, outer, post]
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

/-! ## One ordinary head -/

/-- A head whose predecessor is not slot zero transports the incoming
Fourier character and the slot-zero-erased residual core exactly to the
post-head phased density.

The coefficient may depend on every surviving post-head coordinate.  This
is essential for the actual exceptional root, whose untouched outer
primitive product is not constant on the residual suffix. -/
theorem
    lamEps_pow_integral_incomingPhasedResidualDensity_eq_afterHead_of_ne_zero
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (hpred :
      r324WithinHalfPredecessorSlot res.state head ≠ 0)
    (x y : T4)
    (postCoefficient :
      ((res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) → ℂ)
    (k : Z4)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          res.incomingPhasedResidualDensity
            (postCoefficient
              (res.splitSurvivingPiMeasurableEquiv
                head tail hremaining w).2)
            k ρ ε x y w)
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
          res.incomingPhasedResidualDensity
            (postCoefficient
              (res.splitSurvivingPiMeasurableEquiv
                head tail hremaining w).2)
            k ρ ε x y w
          ∂Measure.pi fun _ => paperMeasure) =
      (lamEps lam ε : ℂ) ^
          (2 *
            (res.afterHead
              head tail hremaining).remainingOrder) *
        (∫ v :
            (res.afterHead
              head tail hremaining).SurvivingCoordinate → T4,
          (res.afterHead
            head tail hremaining).incomingPhasedResidualDensity
              (postCoefficient v) k ρ ε x y v
          ∂Measure.pi fun _ => paperMeasure) := by
  let post :=
    res.afterHead head tail hremaining
  let split :=
    res.splitSurvivingPiMeasurableEquiv
      head tail hremaining
  have hsplit :=
    res.integral_splitSurviving_post_first
      head tail hremaining
      (fun w : res.SurvivingCoordinate → T4 =>
        res.incomingPhasedResidualDensity
          (postCoefficient (split w).2)
          k ρ ε x y w)
      hfull
  have hsplit' :
      (∫ w : res.SurvivingCoordinate → T4,
          res.incomingPhasedResidualDensity
            (postCoefficient (split w).2)
            k ρ ε x y w
          ∂Measure.pi fun _ => paperMeasure) =
        ∫ v : post.SurvivingCoordinate → T4,
          ∫ t :
              Fin (2 * residualBlockOrder head.2) → T4,
            res.incomingPhasedResidualDensity
              (postCoefficient v) k ρ ε x y
              (split.symm (t, v))
            ∂Measure.pi fun _ => paperMeasure
          ∂Measure.pi fun _ => paperMeasure := by
    calc
      _ =
          ∫ v : post.SurvivingCoordinate → T4,
            ∫ t :
                Fin (2 * residualBlockOrder head.2) → T4,
              res.incomingPhasedResidualDensity
                (postCoefficient
                  (split (split.symm (t, v))).2)
                k ρ ε x y (split.symm (t, v))
              ∂Measure.pi fun _ => paperMeasure
            ∂Measure.pi fun _ => paperMeasure := hsplit
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with v
        apply integral_congr_ae
        filter_upwards with t
        rw [show (split (split.symm (t, v))).2 = v by
          exact congrArg Prod.snd
            (split.apply_symm_apply (t, v))]
  have hweighted :=
    res.eventually_integrable_weightedIncomingPhasedHeadLocal_of_integrable
      head tail hremaining hpred x y
      postCoefficient k hfull
  have hexponent :
      2 * res.remainingOrder =
        2 * post.remainingOrder +
          2 * residualBlockOrder head.2 := by
    have horder :=
      res.remainingOrder_head head tail hremaining
    dsimp only [post]
    omega
  calc
    (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
          (∫ w : res.SurvivingCoordinate → T4,
            res.incomingPhasedResidualDensity
              (postCoefficient (split w).2)
              k ρ ε x y w
            ∂Measure.pi fun _ => paperMeasure) =
        (lamEps lam ε : ℂ) ^ (2 * post.remainingOrder) *
          ((lamEps lam ε : ℂ) ^
              (2 * residualBlockOrder head.2) *
            ∫ v : post.SurvivingCoordinate → T4,
              ∫ t :
                  Fin (2 * residualBlockOrder head.2) → T4,
                res.incomingPhasedResidualDensity
                  (postCoefficient v) k ρ ε x y
                  (split.symm (t, v))
                ∂Measure.pi fun _ => paperMeasure
              ∂Measure.pi fun _ => paperMeasure) := by
      rw [hexponent, pow_add, hsplit']
      ring
    _ =
        (lamEps lam ε : ℂ) ^ (2 * post.remainingOrder) *
          (∫ v : post.SurvivingCoordinate → T4,
            (lamEps lam ε : ℂ) ^
                (2 * residualBlockOrder head.2) *
              (∫ t :
                  Fin (2 * residualBlockOrder head.2) → T4,
                res.incomingPhasedResidualDensity
                  (postCoefficient v) k ρ ε x y
                  (split.symm (t, v))
                ∂Measure.pi fun _ => paperMeasure)
            ∂Measure.pi fun _ => paperMeasure) := by
      rw [integral_const_mul]
    _ =
        (lamEps lam ε : ℂ) ^ (2 * post.remainingOrder) *
          (∫ v : post.SurvivingCoordinate → T4,
            post.incomingPhasedResidualDensity
              (postCoefficient v) k ρ ε x y v
            ∂Measure.pi fun _ => paperMeasure) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hweighted] with v hv
      let ctx :=
        res.headContext head tail hremaining
      let u : T4 :=
        res.headPredecessorPoint
            head tail hremaining x y v -
          res.headSuccessorPoint
            head tail hremaining x y v
      let a : T4 :=
        res.headSuccessorPoint
          head tail hremaining x y v
      let erasedOuter : ℂ :=
        (res.incomingErasedHeadOuterFactor
          head tail hremaining ρ ε x y v : ℂ)
      let outer : ℂ :=
        postCoefficient v *
          charT4 k (post.incomingPhaseAnchor x y v) *
          erasedOuter
      have hpre
          (t :
            Fin (2 * residualBlockOrder head.2) → T4) :=
        res.incomingPhasedResidualDensity_reconstruct_split_of_ne_zero
          head tail hremaining hpred (postCoefficient v) k
          ρ ε x y t v
      have hpost :=
        res.afterHead_incomingErasedResidualIntegrand_of_ne_zero
          head tail hremaining hpred ρ ε x y v
      have hinner :
          (∫ t :
              Fin (2 * residualBlockOrder head.2) → T4,
            res.incomingPhasedResidualDensity
              (postCoefficient v) k ρ ε x y
              (split.symm (t, v))
            ∂Measure.pi fun _ => paperMeasure) =
            ∫ t :
                Fin (2 * residualBlockOrder head.2) → T4,
              (ctx.rawLocalIntegrand ρ ε u t : ℂ) *
                outer
              ∂Measure.pi fun _ => paperMeasure := by
        calc
          _ =
              ∫ t :
                  Fin (2 * residualBlockOrder head.2) → T4,
                (res.headLocalFactor
                  head tail hremaining ρ ε x y
                  (res.reconstruct (split.symm (t, v))) : ℂ) *
                  outer
                ∂Measure.pi fun _ => paperMeasure := by
            apply integral_congr_ae
            filter_upwards with t
            rw [hpre t]
            dsimp only [outer, erasedOuter, post, split]
            ring
          _ =
              ∫ t :
                  Fin (2 * residualBlockOrder head.2) → T4,
                (ctx.rawLocalIntegrand ρ ε u
                  (fun j => t j - a) : ℂ) * outer
                ∂Measure.pi fun _ => paperMeasure := by
            apply integral_congr_ae
            filter_upwards with t
            dsimp only [ctx, u, a]
            rw [
              res.headLocalFactor_reconstruct_split
                head tail hremaining ρ ε x y]
          _ = _ :=
            res.integral_head_rawLocal_sub_const_mul_complex
              head tail hremaining u a outer
      have hlocal :=
        ctx.rawLocalSpatialIntegral_mul_complexOuter_eq_absorb_of_weighted
          ρ lam ε u outer hv hinternal
      have hpostDensity :
          post.incomingPhasedResidualDensity
              (postCoefficient v) k ρ ε x y v =
            (((post.state.edges
                (r324WithinHalfPredecessorSlot
                  res.state head) u : ℝ) : ℂ) *
              outer) := by
        unfold incomingPhasedResidualDensity
        rw [
          hpost,
          res.afterHead_residualChainEdgeFactor_predecessor_reconstruct
            head tail hremaining x y v]
        dsimp only [u, outer, erasedOuter]
        push_cast
        ring
      calc
        (lamEps lam ε : ℂ) ^
              (2 * residualBlockOrder head.2) *
            (∫ t :
                Fin (2 * residualBlockOrder head.2) → T4,
              res.incomingPhasedResidualDensity
                (postCoefficient v) k ρ ε x y
                (split.symm (t, v))
              ∂Measure.pi fun _ => paperMeasure) =
          (lamEps lam ε : ℂ) ^
              (2 * residualBlockOrder head.2) *
            (∫ t :
                Fin (2 * residualBlockOrder head.2) → T4,
              (ctx.rawLocalIntegrand ρ ε u t : ℂ) *
                outer
              ∂Measure.pi fun _ => paperMeasure) := by
            rw [hinner]
        _ =
          ((((ctx.absorb ρ lam ε).edges
              (r324WithinHalfPredecessorSlot
                res.state head) u : ℝ) : ℂ) *
            outer) := hlocal
        _ =
          post.incomingPhasedResidualDensity
            (postCoefficient v) k ρ ε x y v := by
            rw [hpostDensity]
            rfl
    _ = _ := by
      rfl

end R324WithinHalfResidualPrefix

end

end Anderson4D
