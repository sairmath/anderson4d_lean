import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingPhasedOrdinaryStep

/-!
# Integrability seam after one ordinary phased head

The one-head transport equation
`lamEps_pow_integral_incomingPhasedResidualDensity_eq_afterHead_of_ne_zero`
consumes full integrability of the incoming phased density and produces the
post-head integral.  Iterating it along the remaining suffix needs the same
integrability statement for the post-head density itself.  This file closes
that seam: the post-head phased density, with its genuinely
coordinate-dependent coefficient, is integrable.

Route: the incoming integrability is transported across the head/post
splitting equivalence (measure-preserving), Fubini yields integrability of
the head-block marginal, and on the almost-everywhere event carrying the
weighted local sections the scaled marginal is exactly the post-head phased
density, by the same reconstruction chain as the transport equation.
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

/-- After an ordinary (non-slot-zero-fed) head, the post-head phased
density with a post-coordinate-dependent coefficient is integrable.  This
is the recursion seam matching the one-head transport equation. -/
theorem integrable_afterHead_incomingPhasedResidualDensity_of_ne_zero
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
    Integrable
      (fun v :
          (res.afterHead
            head tail hremaining).SurvivingCoordinate → T4 =>
        (res.afterHead
          head tail hremaining).incomingPhasedResidualDensity
            (postCoefficient v) k ρ ε x y v)
      (Measure.pi fun _ => paperMeasure) := by
  let post :=
    res.afterHead head tail hremaining
  let split :=
    res.splitSurvivingPiMeasurableEquiv
      head tail hremaining
  let μ :=
    Measure.pi fun _ : res.SurvivingCoordinate =>
      paperMeasure
  let μhead :=
    Measure.pi fun _ :
        Fin (2 * residualBlockOrder head.2) =>
      paperMeasure
  let μpost :=
    Measure.pi fun _ : post.SurvivingCoordinate =>
      paperMeasure
  have hp :
      MeasurePreserving split μ (μhead.prod μpost) :=
    res.measurePreserving_splitSurvivingPiMeasurableEquiv
      head tail hremaining
  -- Product-space integrability of the split incoming density.
  have hprod :
      Integrable
        (fun p :
            (Fin (2 * residualBlockOrder head.2) → T4) ×
              (post.SurvivingCoordinate → T4) =>
          res.incomingPhasedResidualDensity
            (postCoefficient p.2) k ρ ε x y (split.symm p))
        (μhead.prod μpost) := by
    have hiff :=
      hp.integrable_comp_emb split.measurableEmbedding
        (g := fun p :
            (Fin (2 * residualBlockOrder head.2) → T4) ×
              (post.SurvivingCoordinate → T4) =>
          res.incomingPhasedResidualDensity
            (postCoefficient p.2) k ρ ε x y (split.symm p))
    apply hiff.mp
    apply hfull.congr
    filter_upwards with w
    dsimp only [Function.comp_apply]
    rw [split.symm_apply_apply]
  -- Fubini marginal in the post coordinates.
  have hmarg :
      Integrable
        (fun v : post.SurvivingCoordinate → T4 =>
          ∫ t :
              Fin (2 * residualBlockOrder head.2) → T4,
            res.incomingPhasedResidualDensity
              (postCoefficient v) k ρ ε x y
              (split.symm (t, v))
            ∂μhead)
        μpost :=
    hprod.integral_prod_right
  have hscaled :=
    hmarg.const_mul
      ((lamEps lam ε : ℂ) ^
        (2 * residualBlockOrder head.2))
  -- On the weighted event the scaled marginal is the post-head density.
  have hweighted :=
    res.eventually_integrable_weightedIncomingPhasedHeadLocal_of_integrable
      head tail hremaining hpred x y
      postCoefficient k hfull
  apply hscaled.congr
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
        ∂μhead) =
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
          ∂μhead) =
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

end R324WithinHalfResidualPrefix

end

end Anderson4D
