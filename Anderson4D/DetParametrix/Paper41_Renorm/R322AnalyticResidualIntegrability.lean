import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticResidualPrefixInvariant

/-!
# Integrability propagated by one exact R-322 residual collapse

The proper-prefix value identity needs full integrability of the current
residual in order to apply Fubini.  This file proves that the same property
is inherited by the post-collapse residual.  The proof transports the
current integrable function through the genuine coordinate split, integrates
the removed block, and then uses the exact local collapse identity.  No
pointwise majorant for the complete residual is assumed.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R322AnalyticResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {q : ℕ} {hq : 1 ≤ q}
    (res : R322AnalyticResidualPrefix ρ lam ε q hq)
    (step : R322ExtractionStep (2 * q))
    (suffix : List (R322ExtractionStep (2 * q)))
    (hremaining : res.remaining = step :: suffix)
    (hproper : step.1 ≠ r322WholeEndpoint q hq)

/-- Full residual integrability is preserved by one genuine proper
collapse.  The section hypotheses are precisely those already consumed by
`residualValue_eq_afterProper`. -/
theorem integrable_residualIntegrand_afterProper
    (z : T4)
    (hint :
      Integrable
        (fun v : res.SurvivingCoordinate → T4 =>
          res.residualIntegrand ρ ε
            (res.reconstruct z v))
        (Measure.pi fun _ => paperMeasure))
    (hstandard :
      ∀ᵐ outer ∂(Measure.pi fun _ :
          (res.afterProper step suffix
            hremaining hproper).SurvivingCoordinate =>
            paperMeasure),
        Integrable
          ((res.properStepContext
              step suffix hremaining hproper).localIntegrand
            ρ ε
            ((res.properStepContext
                step suffix hremaining hproper).predecessorPoint
                ((res.afterProper step suffix
                  hremaining hproper).reconstruct z outer) -
              (res.properStepContext
                step suffix hremaining hproper).successorPoint
                ((res.afterProper step suffix
                  hremaining hproper).reconstruct z outer)))
          (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin
                  (2 * residualBlockOrder step.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder step.2)},
          Integrable
            (fun v :
                Fin
                  (2 * residualBlockOrder step.2 - 2) →
                    T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder step.2)
                κB.1
                (res.properStepContext
                  step suffix hremaining hproper).internalEdges
                (primitiveAssemble
                  (residualBlockOrder step.2)
                  (res.properStepContext
                    step suffix hremaining hproper).one_le_blockOrder
                  p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    Integrable
      (fun outer :
          (res.afterProper step suffix
            hremaining hproper).SurvivingCoordinate → T4 =>
        (res.afterProper step suffix
          hremaining hproper).residualIntegrand ρ ε
            ((res.afterProper step suffix
              hremaining hproper).reconstruct z outer))
      (Measure.pi fun _ => paperMeasure) := by
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  let post :=
    res.afterProper
      step suffix hremaining hproper
  let μPre : Measure (res.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μOuter :
      Measure (post.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μBlock :
      Measure
        (Fin (2 * residualBlockOrder step.2) → T4) :=
    Measure.pi fun _ => paperMeasure
  let e :=
    res.properOuterBlockPiMeasurableEquiv
      step suffix hremaining hproper
  let base :
      (post.SurvivingCoordinate → T4) →
        Fin (2 * q) → T4 :=
    fun outer => post.reconstruct z outer
  let outerFactor :
      (post.SurvivingCoordinate → T4) → ℝ :=
    fun outer =>
      res.properOuterIntegrand
        step suffix hremaining hproper
        ρ ε (base outer)
  let g :
      ((post.SurvivingCoordinate → T4) ×
        (Fin (2 * residualBlockOrder step.2) → T4)) → ℝ :=
    fun p =>
      res.residualIntegrand ρ ε
        (res.properReconstructBlockTuple
          step suffix hremaining hproper
          (base p.1) p.2)
  have hcomp : Integrable (g ∘ e) μPre := by
    apply hint.congr
    filter_upwards with v
    change
      res.residualIntegrand ρ ε
          (res.reconstruct z v) =
        g (e v)
    unfold g e
    rw [
      res.reconstructBlockTuple_properOuterBlockSplit
        step suffix hremaining hproper z v]
  have hg : Integrable g (μOuter.prod μBlock) :=
    (res.measurePreserving_properOuterBlockPiMeasurableEquiv
      step suffix hremaining hproper).integrable_comp_emb
        e.measurableEmbedding |>.mp hcomp
  have hintegral :
      Integrable
        (fun outer =>
          ∫ t, g (outer, t) ∂μBlock)
        μOuter :=
    hg.integral_prod_left
  have hscaled :
      Integrable
        (fun outer =>
          lamEps lam ε ^
              (2 * residualBlockOrder step.2) *
            (∫ t, g (outer, t) ∂μBlock))
        μOuter :=
    hintegral.const_mul _
  apply hscaled.congr
  filter_upwards [hstandard] with outer houter
  have hinner :
      (∫ t, g (outer, t) ∂μBlock) =
        ∫ t :
            Fin (2 * residualBlockOrder step.2) → T4,
          ctx.rawLocalIntegrand ρ ε
              (ctx.predecessorPoint (base outer) -
                ctx.successorPoint (base outer)) t *
            outerFactor outer
          ∂Measure.pi fun _ => paperMeasure := by
    calc
      (∫ t, g (outer, t) ∂μBlock) =
          ∫ t :
              Fin (2 * residualBlockOrder step.2) → T4,
            ctx.ambientLocalIntegrand ρ ε
                (ctx.reconstructBlockTuple
                  (base outer) t) *
              outerFactor outer
            ∂Measure.pi fun _ => paperMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp only [g, ctx, properStepContext]
        rw [
          res.residualIntegrand_eq_ambientLocal_mul_outer
            step suffix hremaining hproper ρ ε,
          res.properOuterIntegrand_properReconstructBlockTuple
            step suffix hremaining hproper
            ρ ε (base outer) t,
          res.properReconstructBlockTuple_eq_context
            step suffix hremaining hproper
            (base outer) t]
        rfl
      _ =
          ∫ t :
              Fin (2 * residualBlockOrder step.2) → T4,
            ctx.ambientLocalIntegrand ρ ε
                (ctx.reconstructRelativeBlockTuple
                  (base outer) t) *
              outerFactor outer
            ∂Measure.pi fun _ => paperMeasure :=
        ctx.integral_actualBlock_eq_relativeBlock
          ρ ε (base outer) (outerFactor outer)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with t
        rw [
          ctx.ambientLocalIntegrand_reconstructRelativeBlockTuple]
  have hcollapse :=
    ctx.rawLocalSpatialIntegral_mul_outer_eq_nextState
      ρ lam ε
      (ctx.predecessorPoint (base outer) -
        ctx.successorPoint (base outer))
      (outerFactor outer) houter hinternal
  have hpost :
      post.residualIntegrand ρ ε (base outer) =
        (ctx.nextState ρ lam ε).edges
            ctx.predecessorEdge
            (ctx.predecessorPoint (base outer) -
              ctx.successorPoint (base outer)) *
          outerFactor outer := by
    have hstate :
        post.state = ctx.nextState ρ lam ε := by
      dsimp only [post, ctx, afterProper, properStepContext]
    rw [← hstate]
    simpa only [ctx, post, base, outerFactor] using
      res.afterProper_residualIntegrand_eq_updated_mul_outer
        step suffix hremaining hproper
        ρ ε (base outer)
  rw [hpost, hinner]
  exact hcollapse

/-! ## Initial residual ledger -/

/-- At the initial all-active state, one sparse residual chain factor is
literally the corresponding free-Green analytic chain factor. -/
theorem initial_residualChainEdgeFactor_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (x : Fin (2 * q) → T4)
    (edge : Fin (2 * q - 1)) :
    (initial ρ lam ε hq κ hκ).residualChainEdgeFactor
        x edge =
      r322AnalyticChainEdgeFactorWith
        (fun _ : Fin (2 * q - 1) => greenFn)
        κ x edge := by
  let res := initial ρ lam ε hq κ hκ
  have hactive :
      r322AnalyticEdgeLeftVertex edge ∈
        res.state.active := by
    simp [res, initial, r322InitialAnalyticEdgeState,
      R322AnalyticEdgeState.active]
  have hright :
      r322JChainEdgeRight edge ∈
        res.state.active := by
    simp [res, initial, r322InitialAnalyticEdgeState,
      R322AnalyticEdgeState.active]
  have hsuccessor :
      res.edgeSuccessor edge =
        r322JChainEdgeRight edge :=
    edgeSuccessor_eq_adjacent_of_right_mem_active
      res edge hright
  unfold residualChainEdgeFactor
    r322AnalyticChainEdgeFactorWith
  rw [if_pos hactive]
  change
    (if edge.val ∈
        (r322AnalyticSchedule κ).map
          (fun step => step.1.2.val) then
      1
    else
      greenFn
        (x (r322AnalyticEdgeLeftVertex edge) -
          x (res.edgeSuccessor edge))) =
      if edge.val ∈
          (r322AnalyticSchedule κ).map
            (fun step => step.1.2.val) then
        1
      else
        jChainEdgeWith
          (fun _ : Fin (2 * q - 1) => greenFn)
          x edge
  by_cases hrightValue :
      edge.val ∈
        (r322AnalyticSchedule κ).map
          (fun step => step.1.2.val)
  · simp only [hrightValue, if_true]
  · simp only [hrightValue, if_false]
    rw [hsuccessor]
    rfl

/-- The complete initial sparse chain is the frozen analytic Green chain. -/
theorem initial_residualChainProduct_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (x : Fin (2 * q) → T4) :
    (initial ρ lam ε hq κ hκ).residualChainProduct x =
      r322AnalyticChainProductWith
        (fun _ : Fin (2 * q - 1) => greenFn)
        κ x := by
  unfold residualChainProduct
    r322AnalyticChainProductWith
  apply Finset.prod_congr rfl
  intro edge _hedge
  exact initial_residualChainEdgeFactor_eq
    ρ lam ε hq κ hκ x edge

/-- At the initial state, every residual signed difference reads the
ordinary adjacent Green edge and hence equals `diffFactorJWith`. -/
theorem initial_residualStepDifference_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (x : Fin (2 * q) → T4)
    (step : R322ExtractionStep (2 * q)) :
    (initial ρ lam ε hq κ hκ).residualStepDifference
        x step =
      diffFactorJWith
        (fun _ : Fin (2 * q - 1) => greenFn)
        x step.1 := by
  let res := initial ρ lam ε hq κ hκ
  by_cases hguard :
      step.1.2.val < 2 * q - 1
  · let edge : Fin (2 * q - 1) :=
      ⟨step.1.2.val, hguard⟩
    have hguard' :
        step.1.2.val + 1 < 2 * q := by
      omega
    have hright :
        r322JChainEdgeRight edge ∈
          res.state.active := by
      simp [res, initial, r322InitialAnalyticEdgeState,
        R322AnalyticEdgeState.active]
    have hsuccessor :
        r322AnalyticSuccessorVertex
            res.state step.1.2 hguard =
          r322JChainEdgeRight edge := by
      simpa only [edgeSuccessor, edge,
        r322AnalyticEdgeLeftVertex] using
        edgeSuccessor_eq_adjacent_of_right_mem_active
          res edge hright
    unfold residualStepDifference
    rw [dif_pos hguard]
    unfold diffFactorJWith
    rw [dif_pos hguard']
    change
      res.state.edges edge
          (x step.1.2 -
            x (r322AnalyticSuccessorVertex
              res.state step.1.2 hguard)) -
        res.state.edges edge
          (x step.1.1 -
            x (r322AnalyticSuccessorVertex
              res.state step.1.2 hguard)) =
        greenFn
            (x step.1.2 -
              x ⟨step.1.2.val + 1, hguard'⟩) -
          greenFn
            (x step.1.1 -
              x ⟨step.1.2.val + 1, hguard'⟩)
    rw [hsuccessor]
    simp [res, initial, r322InitialAnalyticEdgeState,
      edge, r322JChainEdgeRight]
  · have hguard' :
        ¬step.1.2.val + 1 < 2 * q := by
      omega
    unfold residualStepDifference
    rw [dif_neg hguard]
    unfold diffFactorJWith
    rw [dif_neg hguard']

/-- The complete initial signed-difference product is the analytic schedule
difference product. -/
theorem initial_residualDifferenceProduct_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (x : Fin (2 * q) → T4) :
    (initial ρ lam ε hq κ hκ).residualDifferenceProduct x =
      r322AnalyticDiffProductWith
        (fun _ : Fin (2 * q - 1) => greenFn)
        (r322AnalyticSchedule κ) x := by
  unfold residualDifferenceProduct
    r322AnalyticDiffProductWith
  apply congrArg List.prod
  apply List.map_congr_left
  intro step _hstep
  exact initial_residualStepDifference_eq
    ρ lam ε hq κ hκ x step

/-- The initial remaining-block coordinate is exactly the canonical
analytic-schedule block coordinate. -/
theorem initial_remainingBlockIndex_eq_analyticBlockEquiv
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (j : Fin (r322AnalyticSchedule κ).length) :
    (initial ρ lam ε hq κ hκ).remainingBlockIndex j =
      r322AnalyticBlockEquiv κ j := by
  apply Subtype.ext
  rw [
    (initial ρ lam ε hq κ hκ).remainingBlockIndex_val,
    r322AnalyticBlockEquiv_apply_val]
  rfl

/-- The initial primitive product contains every extraction block exactly
once. -/
theorem initial_residualPrimitiveProduct_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (x : Fin (2 * q) → T4) :
    (initial ρ lam ε hq κ hκ).residualPrimitiveProduct
        ρ ε x =
      ∏ B : ExtractionBlockIndex κ,
        r322ExtractionBlockPrimitiveSum ρ ε κ B x := by
  unfold residualPrimitiveProduct
  rw [extractionBlock_prod_eq_analyticSchedule]
  apply Finset.prod_congr rfl
  intro j _hj
  change
    r322ExtractionBlockPrimitiveSum ρ ε κ
        ((initial ρ lam ε hq κ hκ).remainingBlockIndex j) x =
      r322ExtractionBlockPrimitiveSum ρ ε κ
        (r322AnalyticBlockEquiv κ j) x
  rw [initial_remainingBlockIndex_eq_analyticBlockEquiv]

/-- The complete initial residual integrand is exactly the existing
endpoint-fibre integrand, expressed in the head-local/outer coordinates. -/
theorem initial_residualIntegrand_eq_initialResidualIntegrand
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (x : Fin (2 * q) → T4) :
    (initial ρ lam ε hq κ hκ).residualIntegrand
        ρ ε x =
      r322InitialResidualIntegrand
        ρ ε κ head tail hschedule x := by
  calc
    (initial ρ lam ε hq κ hκ).residualIntegrand
          ρ ε x =
        r322AnalyticSkeletonWith
            (fun _ : Fin (2 * q - 1) => greenFn)
            κ x *
          ∏ B : ExtractionBlockIndex κ,
            r322ExtractionBlockPrimitiveSum
              ρ ε κ B x := by
      unfold residualIntegrand
        r322AnalyticSkeletonWith
      rw [
        initial_residualChainProduct_eq
          ρ lam ε hq κ hκ x,
        initial_residualDifferenceProduct_eq
          ρ lam ε hq κ hκ x,
        initial_residualPrimitiveProduct_eq
          ρ lam ε hq κ hκ x]
    _ =
        (∑ τ : ReductionEndpointFiberAt κ,
          detJintegrand ρ ε q τ.1 x) := by
      rw [
        r322AnalyticSkeletonWith_green_eq,
        r322AnalyticGreenSkeleton_eq_renormalized]
      symm
      exact
        sum_endpointFiber_detJintegrand_eq_skeleton_mul_prod_primitiveSums
          ρ ε κ (mem_nonSplitPairings.mp hκ).1 x
    _ =
        r322InitialResidualIntegrand
          ρ ε κ head tail hschedule x :=
      sum_endpointFiber_detJintegrand_eq_initialResidualIntegrand
        ρ ε κ hκ head tail hschedule x

/-! ## Initial surviving-coordinate reindex -/

/-- The initial residual surviving coordinates are exactly the ordinary
internal coordinates `1, ..., 2q-2`. -/
def initialInternalEquivSurviving
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q) :
    Fin (2 * q - 2) ≃
      (initial ρ lam ε hq κ hκ).SurvivingCoordinate where
  toFun j :=
    ⟨primitiveInternalIdx q hq j,
      by
        simp [initial, r322InitialAnalyticEdgeState,
          R322AnalyticEdgeState.active],
      by
        rw [primitiveInternalIdx_val_residual]
        omega,
      by
        rw [primitiveInternalIdx_val_residual]
        omega⟩
  invFun i :=
    ⟨i.1.val - 1, by
      have hpos := i.2.2.1
      have hlt := i.2.2.2
      omega⟩
  left_inv j := by
    apply Fin.ext
    change
      (primitiveInternalIdx q hq j).val - 1 =
        j.val
    rw [primitiveInternalIdx_val_residual]
    omega
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    change
      (primitiveInternalIdx q hq
          ⟨i.1.val - 1, by
            have hpos := i.2.2.1
            have hlt := i.2.2.2
            omega⟩).val =
        i.1.val
    rw [primitiveInternalIdx_val_residual]
    change (i.1.val - 1) + 1 = i.1.val
    have hpos := i.2.2.1
    omega

/-- Measurable reindex from the initial sparse carrier to the standard
internal-coordinate tuple. -/
def initialInternalPiMeasurableEquiv
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q) :
    ((initial ρ lam ε hq κ hκ).SurvivingCoordinate → T4) ≃ᵐ
      (Fin (2 * q - 2) → T4) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ :
      (initial ρ lam ε hq κ hκ).SurvivingCoordinate =>
        T4)
    (initialInternalEquivSurviving
      (q := q) ρ lam ε hq κ hκ)).symm

/-- The initial internal-coordinate reindex preserves the paper product
measure exactly. -/
theorem measurePreserving_initialInternalPiMeasurableEquiv
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q) :
    MeasurePreserving
      (initialInternalPiMeasurableEquiv
        ρ lam ε hq κ hκ)
      (Measure.pi fun _ :
        (initial ρ lam ε hq κ hκ).SurvivingCoordinate =>
          paperMeasure)
      (Measure.pi fun _ : Fin (2 * q - 2) =>
        paperMeasure) := by
  simpa only [initialInternalPiMeasurableEquiv] using
    (measurePreserving_piCongrLeft
      (fun _ :
        (initial ρ lam ε hq κ hκ).SurvivingCoordinate =>
          paperMeasure)
      (initialInternalEquivSurviving
        (q := q) ρ lam ε hq κ hκ)).symm

@[simp]
theorem initialInternalPiMeasurableEquiv_apply
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (v :
      (initial ρ lam ε hq κ hκ).SurvivingCoordinate → T4)
    (j : Fin (2 * q - 2)) :
    initialInternalPiMeasurableEquiv
        ρ lam ε hq κ hκ v j =
      v (initialInternalEquivSurviving
        (q := q) ρ lam ε hq κ hκ j) :=
  rfl

/-- Reconstructing the ambient tuple after the initial reindex gives the
standard primitive assembly with endpoints `z` and `0`. -/
theorem initial_reconstruct_eq_primitiveAssemble
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (z : T4)
    (v :
      (initial ρ lam ε hq κ hκ).SurvivingCoordinate → T4) :
    (initial ρ lam ε hq κ hκ).reconstruct z v =
      primitiveAssemble q hq z 0
        (initialInternalPiMeasurableEquiv
          ρ lam ε hq κ hκ v) := by
  let res := initial ρ lam ε hq κ hκ
  funext i
  by_cases hzero : i.val = 0
  · have hi :
        i = (⟨0, by omega⟩ : Fin (2 * q)) :=
      Fin.ext hzero
    rw [hi, res.reconstruct_zero,
      primitiveAssemble_zero]
  by_cases hlast : i.val = 2 * q - 1
  · have hi :
        i =
          (⟨2 * q - 1, by omega⟩ :
            Fin (2 * q)) :=
      Fin.ext hlast
    have hlastIndex :
        (⟨2 * q - 1, by omega⟩ :
          Fin (2 * q)) =
        primitiveLast q hq := by
      apply Fin.ext
      rfl
    rw [hi, res.reconstruct_last,
      hlastIndex, primitiveAssemble_last]
  · let j : Fin (2 * q - 2) :=
      ⟨i.val - 1, by omega⟩
    have hij :
        primitiveInternalIdx q hq j = i := by
      apply Fin.ext
      rw [primitiveInternalIdx_val_residual]
      dsimp only [j]
      omega
    have hactive : i ∈ res.state.active := by
      simp [res, initial, r322InitialAnalyticEdgeState,
        R322AnalyticEdgeState.active]
    let si : res.SurvivingCoordinate :=
      ⟨i, hactive, by omega, by omega⟩
    calc
      res.reconstruct z v i = v si :=
        res.reconstruct_surviving z v si
      _ =
          initialInternalPiMeasurableEquiv
            ρ lam ε hq κ hκ v j := by
        rw [initialInternalPiMeasurableEquiv_apply]
        apply congrArg v
        apply Subtype.ext
        exact hij.symm
      _ =
          primitiveAssemble q hq z 0
            (initialInternalPiMeasurableEquiv
              ρ lam ε hq κ hκ v) i := by
        rw [← hij, primitiveAssemble_internal]

/-- Integrability of the genuine endpoint-fibre sections transports to the
initial sparse residual for a displayed nonempty analytic schedule. -/
theorem integrable_initial_residualIntegrand_of_schedule
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (z : T4)
    (hint :
      ∀ τ : ReductionEndpointFiberAt κ,
        Integrable
          (fun v : Fin (2 * q - 2) → T4 =>
            detJintegrand ρ ε q τ.1
              (primitiveAssemble q hq z 0 v))
          (Measure.pi fun _ => paperMeasure)) :
    Integrable
      (fun v :
          (initial ρ lam ε hq κ hκ).SurvivingCoordinate → T4 =>
        (initial ρ lam ε hq κ hκ).residualIntegrand
          ρ ε
          ((initial ρ lam ε hq κ hκ).reconstruct z v))
      (Measure.pi fun _ => paperMeasure) := by
  let res := initial ρ lam ε hq κ hκ
  let e :=
    initialInternalPiMeasurableEquiv
      ρ lam ε hq κ hκ
  let F : (Fin (2 * q - 2) → T4) → ℝ :=
    fun v =>
      ∑ τ : ReductionEndpointFiberAt κ,
        detJintegrand ρ ε q τ.1
          (primitiveAssemble q hq z 0 v)
  have hF :
      Integrable F
        (Measure.pi fun _ : Fin (2 * q - 2) =>
          paperMeasure) := by
    apply integrable_finsetSum
    intro τ _hτ
    exact hint τ
  have hcomp :
      Integrable (F ∘ e)
        (Measure.pi fun _ :
          res.SurvivingCoordinate => paperMeasure) :=
    (measurePreserving_initialInternalPiMeasurableEquiv
      ρ lam ε hq κ hκ).integrable_comp_emb
        e.measurableEmbedding |>.mpr hF
  apply hcomp.congr
  filter_upwards with v
  change
    F (e v) =
      res.residualIntegrand ρ ε
        (res.reconstruct z v)
  dsimp only [F, e, res]
  rw [
    ← initial_reconstruct_eq_primitiveAssemble
      ρ lam ε hq κ hκ z v,
    sum_endpointFiber_detJintegrand_eq_initialResidualIntegrand
      ρ ε κ hκ head tail hschedule]
  exact
    (initial_residualIntegrand_eq_initialResidualIntegrand
      ρ lam ε hq κ hκ head tail hschedule
      ((initial ρ lam ε hq κ hκ).reconstruct z v)).symm

/-- Integrability of the genuine endpoint-fibre sections gives full
integrability of the canonical initial residual.  Schedule nonemptiness is
derived from non-splitting rather than assumed. -/
theorem integrable_initial_residualIntegrand
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (z : T4)
    (hint :
      ∀ τ : ReductionEndpointFiberAt κ,
        Integrable
          (fun v : Fin (2 * q - 2) → T4 =>
            detJintegrand ρ ε q τ.1
              (primitiveAssemble q hq z 0 v))
          (Measure.pi fun _ => paperMeasure)) :
    Integrable
      (fun v :
          (initial ρ lam ε hq κ hκ).SurvivingCoordinate → T4 =>
        (initial ρ lam ε hq κ hκ).residualIntegrand
          ρ ε
          ((initial ρ lam ε hq κ hκ).reconstruct z v))
      (Measure.pi fun _ => paperMeasure) := by
  obtain ⟨proper, terminal,
      hschedule, _hterminal, _hproper⟩ :=
    r322AnalyticSchedule_eq_proper_append_terminal_of_isNonSplit
      hq (mem_nonSplitPairings.mp hκ)
  cases proper with
  | nil =>
      apply integrable_initial_residualIntegrand_of_schedule
        ρ lam ε hq κ hκ terminal [] _ z hint
      simpa using hschedule
  | cons head rest =>
      apply integrable_initial_residualIntegrand_of_schedule
        ρ lam ε hq κ hκ head
          (rest ++ [terminal]) _ z hint
      simpa [List.cons_append] using hschedule

/-- The grouped endpoint fibre is exactly the scalar value of the canonical
initial residual.  This is only the finite-sum and product-coordinate
reindexing ledger; no collapse estimate is used. -/
theorem endpointFiberDetJSum_eq_initial_residualValue
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (z : T4)
    (hint :
      ∀ τ : ReductionEndpointFiberAt κ,
        Integrable
          (fun v : Fin (2 * q - 2) → T4 =>
            detJintegrand ρ ε q τ.1
              (primitiveAssemble q hq z 0 v))
          (Measure.pi fun _ => paperMeasure)) :
    endpointFiberDetJSum ρ lam ε q
        (reductionEndpointSignature κ) z =
      (initial ρ lam ε hq κ hκ).residualValue
        ρ lam ε z := by
  let res := initial ρ lam ε hq κ hκ
  let e :=
    initialInternalPiMeasurableEquiv
      ρ lam ε hq κ hκ
  let F : (Fin (2 * q - 2) → T4) → ℝ :=
    fun v =>
      ∑ τ : ReductionEndpointFiberAt κ,
        detJintegrand ρ ε q τ.1
          (primitiveAssemble q hq z 0 v)
  obtain ⟨proper, terminal,
      hschedule, _hterminal, _hproper⟩ :=
    r322AnalyticSchedule_eq_proper_append_terminal_of_isNonSplit
      hq (mem_nonSplitPairings.mp hκ)
  have hpoint :
      ∀ v : res.SurvivingCoordinate → T4,
        F (e v) =
          res.residualIntegrand ρ ε
            (res.reconstruct z v) := by
    intro v
    cases proper with
    | nil =>
        have hs :
            r322AnalyticSchedule κ = terminal :: [] := by
          simpa using hschedule
        dsimp only [F, e, res]
        rw [
          ← initial_reconstruct_eq_primitiveAssemble
            ρ lam ε hq κ hκ z v,
          sum_endpointFiber_detJintegrand_eq_initialResidualIntegrand
            ρ ε κ hκ terminal [] hs]
        exact
          (initial_residualIntegrand_eq_initialResidualIntegrand
            ρ lam ε hq κ hκ terminal [] hs
            ((initial ρ lam ε hq κ hκ).reconstruct z v)).symm
    | cons head rest =>
        have hs :
            r322AnalyticSchedule κ =
              head :: (rest ++ [terminal]) := by
          simpa [List.cons_append] using hschedule
        dsimp only [F, e, res]
        rw [
          ← initial_reconstruct_eq_primitiveAssemble
            ρ lam ε hq κ hκ z v,
          sum_endpointFiber_detJintegrand_eq_initialResidualIntegrand
            ρ ε κ hκ head (rest ++ [terminal]) hs]
        exact
          (initial_residualIntegrand_eq_initialResidualIntegrand
            ρ lam ε hq κ hκ head (rest ++ [terminal]) hs
            ((initial ρ lam ε hq κ hκ).reconstruct z v)).symm
  have hreindex :
      (∫ v : res.SurvivingCoordinate → T4,
          F (e v)
        ∂Measure.pi fun _ => paperMeasure) =
        ∫ u : Fin (2 * q - 2) → T4,
          F u
        ∂Measure.pi fun _ => paperMeasure := by
    exact
      (measurePreserving_initialInternalPiMeasurableEquiv
        ρ lam ε hq κ hκ).integral_comp' F
  have horder : res.remainingOrder = q := by
    have hledger := res.processedOrder_add_remainingOrder
    simpa [res, initial, r322InitialAnalyticEdgeState] using hledger
  calc
    endpointFiberDetJSum ρ lam ε q
        (reductionEndpointSignature κ) z =
        lamEps lam ε ^ (2 * q) *
          ∫ u : Fin (2 * q - 2) → T4,
            F u
          ∂Measure.pi fun _ => paperMeasure :=
      endpointFiberDetJSum_eq_integral_sum_detJintegrand
        ρ lam ε hq κ hκ z hint
    _ =
        lamEps lam ε ^ (2 * q) *
          ∫ v : res.SurvivingCoordinate → T4,
            F (e v)
          ∂Measure.pi fun _ => paperMeasure := by
      exact congrArg
        (fun value : ℝ =>
          lamEps lam ε ^ (2 * q) * value)
        hreindex.symm
    _ = res.residualValue ρ lam ε z := by
      unfold residualValue
      rw [horder]
      apply congrArg
        (fun value : ℝ =>
          lamEps lam ε ^ (2 * q) * value)
      apply integral_congr_ae
      filter_upwards with v
      exact hpoint v

end R322AnalyticResidualPrefix

end

end Anderson4D
