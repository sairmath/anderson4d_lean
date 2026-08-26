import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfResidualIntegrability

/-!
# Joint integrability through one R-324 residual head

The scalar one-head theorem in `R324ConcretePhaseATraceAssembly` preserves
integrability at fixed endpoints.  The physical two-half argument also needs
the corresponding statement with an arbitrary measured parameter carried
jointly with the surviving coordinates.

The proof does not infer joint integrability from pointwise section
integrability.  Instead it transports the current joint density through the
actual head/post coordinate split, moves the head coordinates to the front,
and obtains an integrable parameterized head integral by Bochner--Fubini.
The existing weighted local collapse then identifies that integral with the
post-head residual density almost everywhere.
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

/-- One concrete residual head preserves integrability jointly with an
arbitrary measured parameter.

The parameter may control both displayed endpoints and the post-head outer
factor.  The only analytic hypotheses are joint integrability of the genuine
current weighted residual density and the endpoint-independent internal
certificate already carried by a certified R-324 trace. -/
theorem integrable_joint_residualIntegrand_mul_postOuter_afterHead
    {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [SFinite ν]
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (x y : Y → T4)
    (postOuter :
      Y →
        ((res.afterHead
          head tail hremaining).SurvivingCoordinate → T4) → ℂ)
    (hfull :
      Integrable
        (fun p :
            Y × (res.SurvivingCoordinate → T4) =>
          (res.residualIntegrand ρ ε
              (x p.1) (y p.1)
              (res.reconstruct p.2) : ℂ) *
            postOuter p.1
              (res.splitSurvivingPiMeasurableEquiv
                head tail hremaining p.2).2)
        (ν.prod
          (Measure.pi fun _ :
            res.SurvivingCoordinate => paperMeasure)))
    (internal :
      R324WithinHalfResidualInternalReady
        res head tail hremaining) :
    Integrable
      (fun p :
          Y ×
            ((res.afterHead
              head tail hremaining).SurvivingCoordinate → T4) =>
        ((res.afterHead
          head tail hremaining).residualIntegrand
            ρ ε (x p.1) (y p.1)
            ((res.afterHead
              head tail hremaining).reconstruct p.2) : ℂ) *
          postOuter p.1 p.2)
      (ν.prod
        (Measure.pi fun _ :
          (res.afterHead
            head tail hremaining).SurvivingCoordinate =>
            paperMeasure)) := by
  let post :=
    res.afterHead head tail hremaining
  let HeadCoordinate :=
    Fin (2 * residualBlockOrder head.2)
  let μPre : Measure (res.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μHead : Measure (HeadCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μPost : Measure (post.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let split :=
    res.splitSurvivingPiMeasurableEquiv
      head tail hremaining
  let splitWithParameter :
      Y × (res.SurvivingCoordinate → T4) ≃ᵐ
        Y ×
          ((HeadCoordinate → T4) ×
            (post.SurvivingCoordinate → T4)) :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl Y) split
  let moveHead :=
    r324MoveMiddleMeasurableEquiv
      Y (HeadCoordinate → T4)
        (post.SurvivingCoordinate → T4)
  let e :=
    splitWithParameter.trans moveHead
  have hsplitWithParameter :
      MeasurePreserving splitWithParameter
        (ν.prod μPre)
        (ν.prod (μHead.prod μPost)) :=
    (MeasurePreserving.id ν).prod
      (res.measurePreserving_splitSurvivingPiMeasurableEquiv
        head tail hremaining)
  have hmoveHead :
      MeasurePreserving moveHead
        (ν.prod (μHead.prod μPost))
        (μHead.prod (ν.prod μPost)) :=
    measurePreserving_r324MoveMiddleMeasurableEquiv
      ν μHead μPost
  have he :
      MeasurePreserving e
        (ν.prod μPre)
        (μHead.prod (ν.prod μPost)) :=
    hmoveHead.comp hsplitWithParameter
  have he_apply
      (a : Y) (w : res.SurvivingCoordinate → T4) :
      e (a, w) =
        ((split w).1, a, (split w).2) := by
    rfl
  let g :
      (HeadCoordinate → T4) ×
          (Y × (post.SurvivingCoordinate → T4)) → ℂ :=
    fun q =>
      (res.residualIntegrand ρ ε
          (x q.2.1) (y q.2.1)
          (res.reconstruct
            (split.symm (q.1, q.2.2))) : ℂ) *
        postOuter q.2.1 q.2.2
  have hcomp :
      Integrable (g ∘ e) (ν.prod μPre) := by
    apply hfull.congr
    filter_upwards with p
    rcases p with ⟨a, w⟩
    change
      (res.residualIntegrand ρ ε
          (x a) (y a) (res.reconstruct w) : ℂ) *
            postOuter a (split w).2 =
        g (e (a, w))
    rw [he_apply]
    dsimp only [g]
    rw [split.symm_apply_apply]
  have hg :
      Integrable g (μHead.prod (ν.prod μPost)) :=
    (he.integrable_comp_emb e.measurableEmbedding).mp hcomp
  have hintegral :
      Integrable
        (fun p : Y × (post.SurvivingCoordinate → T4) =>
          ∫ t, g (t, p) ∂μHead)
        (ν.prod μPost) :=
    hg.integral_prod_right
  have hscaled :
      Integrable
        (fun p : Y × (post.SurvivingCoordinate → T4) =>
          (lamEps lam ε : ℂ) ^
              (2 * residualBlockOrder head.2) *
            (∫ t, g (t, p) ∂μHead))
        (ν.prod μPost) :=
    hintegral.const_mul _
  have hweighted :
      ∀ᵐ p ∂(ν.prod μPost),
        Integrable
          (fun t : HeadCoordinate → T4 =>
            ((res.headContext
                head tail hremaining).rawLocalIntegrand ρ ε
                (res.headPredecessorPoint
                    head tail hremaining
                    (x p.1) (y p.1) p.2 -
                  res.headSuccessorPoint
                    head tail hremaining
                    (x p.1) (y p.1) p.2) t : ℂ) *
              ((res.headOuterFactor
                  head tail hremaining ρ ε
                  (x p.1) (y p.1) p.2 : ℂ) *
                postOuter p.1 p.2))
          μHead := by
    filter_upwards [hg.prod_left_ae] with p hp
    let ctx :=
      res.headContext head tail hremaining
    let u : T4 :=
      res.headPredecessorPoint
          head tail hremaining
          (x p.1) (y p.1) p.2 -
        res.headSuccessorPoint
          head tail hremaining
          (x p.1) (y p.1) p.2
    let a : T4 :=
      res.headSuccessorPoint
        head tail hremaining
        (x p.1) (y p.1) p.2
    let outer : ℂ :=
      (res.headOuterFactor
          head tail hremaining ρ ε
          (x p.1) (y p.1) p.2 : ℂ) *
        postOuter p.1 p.2
    change
      Integrable
        (fun t : HeadCoordinate → T4 =>
          (ctx.rawLocalIntegrand ρ ε u t : ℂ) * outer)
        μHead
    have hshifted :
        Integrable
          (fun t : HeadCoordinate → T4 =>
            (ctx.rawLocalIntegrand ρ ε u
              (fun j => t j - a) : ℂ) * outer)
          μHead := by
      apply hp.congr
      filter_upwards with t
      dsimp only [g, ctx, u, a, outer]
      rw [
        res.residualIntegrand_reconstruct_split
          head tail hremaining ρ ε
          (x p.1) (y p.1),
        res.headLocalFactor_reconstruct_split
          head tail hremaining ρ ε
          (x p.1) (y p.1)]
      push_cast
      ring
    let translation := ctx.physicalBlockTranslation a
    have htranslated :
        Integrable
          ((fun t : HeadCoordinate → T4 =>
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
  apply hscaled.congr
  filter_upwards [hweighted] with p hp
  let ctx :=
    res.headContext head tail hremaining
  let u : T4 :=
    res.headPredecessorPoint
        head tail hremaining
        (x p.1) (y p.1) p.2 -
      res.headSuccessorPoint
        head tail hremaining
        (x p.1) (y p.1) p.2
  let outer : ℂ :=
    (res.headOuterFactor
        head tail hremaining ρ ε
        (x p.1) (y p.1) p.2 : ℂ) *
      postOuter p.1 p.2
  have hinner :
      (∫ t, g (t, p) ∂μHead) =
        ∫ t : HeadCoordinate → T4,
          (ctx.rawLocalIntegrand ρ ε u t : ℂ) * outer
          ∂Measure.pi fun _ => paperMeasure := by
    calc
      (∫ t, g (t, p) ∂μHead) =
          ∫ t : HeadCoordinate → T4,
            ((res.headLocalFactor
                head tail hremaining ρ ε
                (x p.1) (y p.1)
                (res.reconstruct
                  (split.symm (t, p.2))) : ℝ) : ℂ) *
              outer
            ∂Measure.pi fun _ => paperMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp only [g, outer]
        rw [
          res.residualIntegrand_reconstruct_split
            head tail hremaining ρ ε
            (x p.1) (y p.1)]
        push_cast
        ring
      _ =
          ∫ t : HeadCoordinate → T4,
            (ctx.rawLocalIntegrand ρ ε u
              (fun j =>
                t j -
                  res.headSuccessorPoint
                    head tail hremaining
                    (x p.1) (y p.1) p.2) : ℂ) *
              outer
            ∂Measure.pi fun _ => paperMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp only [ctx, u]
        rw [
          res.headLocalFactor_reconstruct_split
            head tail hremaining ρ ε
            (x p.1) (y p.1)]
      _ = _ :=
        res.integral_head_rawLocal_sub_const_mul_complex
          head tail hremaining u
          (res.headSuccessorPoint
            head tail hremaining
            (x p.1) (y p.1) p.2) outer
  have hcollapse :=
    ctx.rawLocalSpatialIntegral_mul_complexOuter_eq_absorb_of_weighted
      ρ lam ε u outer hp internal.internal
  have hpost :
      (post.residualIntegrand ρ ε
          (x p.1) (y p.1)
          (post.reconstruct p.2) : ℂ) *
          postOuter p.1 p.2 =
        ((post.state.edges
            (r324WithinHalfPredecessorSlot
              res.state head) u : ℝ) : ℂ) * outer := by
    rw [
      res.afterHead_residualIntegrand
        head tail hremaining ρ ε
        (x p.1) (y p.1) p.2,
      res.afterHead_residualChainEdgeFactor_predecessor_reconstruct
        head tail hremaining
        (x p.1) (y p.1) p.2]
    dsimp only [post, u, outer]
    push_cast
    ring
  change
    (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder head.2) *
        (∫ t, g (t, p) ∂μHead) =
      (post.residualIntegrand ρ ε
          (x p.1) (y p.1)
          (post.reconstruct p.2) : ℂ) *
        postOuter p.1 p.2
  rw [hinner, hpost]
  convert hcollapse using 1 <;>
    simp only [ctx, u,
      R324WithinHalfResidualPrefix.headContext] <;>
    rfl

end R324WithinHalfResidualPrefix

end

end Anderson4D
