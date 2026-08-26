import Anderson4D.Continuum.PrimitiveProposition41
import Anderson4D.DetParametrix.Paper42_Moment.R324CertifiedTwoHalfPhysicalCollapse
import Anderson4D.DetParametrix.Paper42_Moment.R324InitialNestedContextFactorization
import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfBudgetInvariant

/-!
# Concrete Phase-A trace assembly for R-324

This file closes two local gaps at the entrance to the physical R-324
collapse.

* Proposition 4.1 at the actual truncation constructs the two
  endpoint-independent certified within-half traces from the all-Green
  initial states.
* Full integrability at the root of a certified trace propagates through
  every genuine head.  Consequently the two `WeightedIntegrableAlong`
  hypotheses used by the exact two-half collapse follow from one
  left-section premise and the genuine joint root integrability.

The two remaining premises in the last theorem are literal integrability
statements for the uncollapsed physical density.  They do not assert a
moment estimate or a target-shaped bound.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## Proposition 4.1 constructs both certified within-half traces -/

/-- Every literal within-half block has order at most the ambient
perturbative order. -/
theorem R324WithinHalfStepContext.order_le_ambient
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (ctx : R324WithinHalfStepContext pairing) :
    residualBlockOrder ctx.step.2 ≤ m := by
  unfold residualBlockOrder
  exact
    (Nat.div_le_self _ _).trans
      (by simpa using Finset.card_le_univ ctx.step.2)

/-- The proved truncation form of Proposition 4.1 supplies a complete
local block provider for either within-half pairing. -/
theorem exists_r324WithinHalfLocalBlockProvider_at_truncation
    (ρ : SmoothCutoff) :
    ∃ supportConstant C K : ℝ,
      0 < supportConstant ∧ 0 < C ∧ 0 < K ∧
        ∀ (lam ε : ℝ) (m : ℕ)
          (pairing : PartialPairing (Fin m)),
          0 < lam → 0 < ε → ε ≤ 1 →
          1 ≤ |Real.log ε| →
          m ≤ truncOrder ε →
          R324WithinHalfLocalBlockProvider
            ρ C lam ε K pairing := by
  obtain ⟨supportConstant, C, hsupport, hC, hprop⟩ :=
    proposition41_at_truncation ρ
  obtain ⟨K, hK, hlocal⟩ :=
    exists_r324WithinHalf_localBlockClosure hsupport
  refine
    ⟨supportConstant, C, K, hsupport, hC, hK, ?_⟩
  intro lam ε m pairing hlam hε hε1 hlog hm
    res head tail hremaining scale hcertificate
  exact
    hlocal ρ C lam ε m pairing
      res head tail hremaining scale hcertificate
      hC hlam hε hε1 hlog
      (fun H hH =>
        hprop lam ε
          (residualBlockOrder head.2)
          (res.headContext
            head tail hremaining).one_le_blockOrder
          H hlam hε hε1
          ((res.headContext
            head tail hremaining).order_le_ambient.trans hm)
          hH)

/-- Concrete simultaneous construction of the two endpoint-independent
certified traces used by the R-324 two-half bridge.

All numerical constants are selected before the ambient order and the two
pairings.  The only analytic input is the already proved
`proposition41_at_truncation`. -/
theorem exists_r324InitialCertifiedAnalyticTraces_at_truncation
    (ρ : SmoothCutoff) :
    ∃ supportConstant C K A : ℝ,
      0 < supportConstant ∧ 0 < C ∧ 0 < K ∧ 1 ≤ A ∧
        ∀ (lam ε : ℝ) (m : ℕ)
          (κp κm : PartialPairing (Fin m)),
          0 < lam → 0 < ε → ε ≤ 1 →
          1 ≤ |Real.log ε| →
          m ≤ truncOrder ε →
          Nonempty
            (R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
                (R324WithinHalfResidualPrefix.initial
                  ρ lam ε κp) (fun _ => A) ×
              R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
                (R324WithinHalfResidualPrefix.initial
                  ρ lam ε κm) (fun _ => A)) := by
  obtain
      ⟨supportConstant, C, K,
        hsupport, hC, hK, hprovider⟩ :=
    exists_r324WithinHalfLocalBlockProvider_at_truncation ρ
  obtain ⟨A, hA, hinitial⟩ :=
    exists_r324InitialWithinHalfEdgeCertificate_one_le_uniform
  refine
    ⟨supportConstant, C, K, A,
      hsupport, hC, hK, hA, ?_⟩
  intro lam ε m κp κm hlam hε hε1 hlog hm
  let leftProvider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K κp :=
    hprovider lam ε m κp hlam hε hε1 hlog hm
  let rightProvider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K κm :=
    hprovider lam ε m κm hlam hε hε1 hlog hm
  let leftTrace :=
    R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace.of_localBlockProvider
      hε hε1 leftProvider
      (R324WithinHalfResidualPrefix.initial ρ lam ε κp)
      (fun _ => A) (hinitial m)
  let rightTrace :=
    R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace.of_localBlockProvider
      hε hε1 rightProvider
      (R324WithinHalfResidualPrefix.initial ρ lam ε κm)
      (fun _ => A) (hinitial m)
  exact ⟨leftTrace, rightTrace⟩

/-! ## The honest terminal case of the nested physical factorization -/

/-- If the marked carrier is already the literal first cross block, the
physical norm boundary itself is the terminal context factorization.

This constructor is restricted to that terminal case.  A marked carrier
deeper in the schedule uses the preceding-block factorization hypothesis; the
canonical proper-prefix run alone does not provide that comparison. -/
def R324InitialNestedContextFactorization.of_initial_marked_head
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {selected : R324ResidualCovarianceSlot κp}
    {terminal :
      R324TwoHalfTerminalData ρ lam ε κp κm}
    {L : ℝ} {x y z w : T4}
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial
        κp κm π).remaining = head :: tail)
    (hhead :
      head.carrier =
        r324MarkedResidualBlock κp κm π selected)
    (hphysical :
      Integrable
        (terminal.initialNestedMarkedPhysicalCore
          π selected L x y z w)
        (Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure)) :
    R324InitialNestedContextFactorization
      ρ lam ε κp κm π selected terminal L x y z w := by
  let initial :=
    R324NestedCrossResidualPrefix.initial κp κm π
  let step :=
    initial.headContext head tail hremaining
  let context :
      T4 → T4 → T4 → T4 →
        (step.SurvivingCoordinate → T4) → ℝ :=
    fun x' y' z' w' v =>
      terminal.initialNestedMarkedNormDensity
        π selected L x' y' z' w' v
  let source :
      (terminal.NestedCoordinate π → T4) → ℝ :=
    terminal.initialNestedWeightedNormDensity
      π selected L x y z w
  have hsource :
      Integrable source
        (Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure) := by
    exact
      terminal.integrable_initialNestedWeightedNormDensity
        π selected L x y z w hphysical
  refine
    { majorant := source
      prefixOrder := 0
      terminalOrder := initial.remainingOrder
      factorization := ?_ }
  exact
    R324NestedCrossContextFactorization.stop
      step hhead context source
      (fun v =>
        terminal.initialNestedMarkedNormDensity_nonneg
          π selected L x y z w v)
      hsource
      (Filter.Eventually.of_forall fun _ => le_rfl)

/-! ## Weighted integrability propagates from one honest root premise -/

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- Full integrability with an arbitrary post-coordinate outer function is
preserved by one certified head collapse.

This is the weighted counterpart of
`integrable_residualIntegrand_afterHead`; crucially, it never cancels the
outer factor on its zero set. -/
theorem integrable_residualIntegrand_mul_postOuter_afterHead
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
    Integrable
      (fun v :
          (res.afterHead
            head tail hremaining).SurvivingCoordinate → T4 =>
        ((res.afterHead
          head tail hremaining).residualIntegrand
            ρ ε x y
            ((res.afterHead
              head tail hremaining).reconstruct v) : ℂ) *
          postOuter v)
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
          (res.reconstruct (e.symm p)) : ℂ) *
        postOuter p.2
  have hcomp : Integrable (g ∘ e) μPre := by
    apply hfull.congr
    filter_upwards with w
    simp only [Function.comp_apply, g, e.symm_apply_apply]
    rfl
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
    eventually_integrable_weightedHeadLocal_mul_postOuter_of_integrable
      res head tail hremaining x y postOuter hfull
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
      head tail hremaining ρ ε x y v : ℂ) *
        postOuter v
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
          head tail hremaining).residualIntegrand ρ ε x y
          ((res.afterHead
            head tail hremaining).reconstruct v) : ℂ) *
          postOuter v =
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
    ring
  change
    (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder head.2) *
        (∫ t, g (t, v) ∂μHead) =
      (post.residualIntegrand ρ ε x y
        (post.reconstruct v) : ℂ) * postOuter v
  rw [hinner, hpost]
  convert hcollapse using 1 <;>
    simp only [ctx, u,
      R324WithinHalfResidualPrefix.headContext,
      R324WithinHalfResidualPrefix.afterHead_state] ;
    rfl

namespace R324WithinHalfCertifiedAnalyticTrace

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- A single honest weighted-integrability premise at the root propagates
through every scalar integral traversed by a certified trace. -/
theorem weightedIntegrableAlong_of_integrable
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (x y : T4)
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale)
    (outer :
      (trace.terminalPrefix.SurvivingCoordinate → T4) → ℂ)
    (hroot :
      Integrable
        (fun v : res.SurvivingCoordinate → T4 =>
          (res.residualIntegrand ρ ε x y
              (res.reconstruct v) : ℂ) *
            outer (trace.terminalProjection v))
        (Measure.pi fun _ => paperMeasure)) :
    trace.WeightedIntegrableAlong x y outer := by
  induction trace with
  | terminal terminal scale hremaining certificate =>
      trivial
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      refine ⟨hroot, ?_⟩
      apply ih
      exact
        current.integrable_residualIntegrand_mul_postOuter_afterHead
          head tail hremaining x y
          (fun v => outer (next.terminalProjection v))
          hroot internal.internal

end R324WithinHalfCertifiedAnalyticTrace

end R324WithinHalfResidualPrefix

/-! ## The two weighted hypotheses from root physical integrability -/

namespace R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {x y z w : T4}
    {leftRes :
      R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes :
      R324WithinHalfResidualPrefix ρ lam ε κm}
    {leftScale rightScale : Fin (m + 1) → ℝ}

/-- The exact `WeightedIntegrableAlong` hypotheses for the two-half
collapse follow from:

* integrability of the genuine left section for almost every right
  configuration; and
* joint integrability of the genuine uncollapsed two-half density.

These are root-level physical integrability statements, not recursive
providers and not quantitative bounds. -/
theorem twoHalf_weightedIntegrableAlong_of_root_integrable
    (leftTrace :
      R324WithinHalfCertifiedAnalyticTrace
        leftRes leftScale)
    (rightTrace :
      R324WithinHalfCertifiedAnalyticTrace
        rightRes rightScale)
    (cross :
      (leftTrace.terminalPrefix.SurvivingCoordinate → T4) →
        (rightTrace.terminalPrefix.SurvivingCoordinate → T4) → ℂ)
    (hleftRoot :
      ∀ᵐ vr ∂(Measure.pi fun _ :
          rightRes.SurvivingCoordinate => paperMeasure),
        Integrable
          (fun vl : leftRes.SurvivingCoordinate → T4 =>
            (leftRes.residualIntegrand ρ ε x y
                (leftRes.reconstruct vl) : ℂ) *
              cross
                (leftTrace.terminalProjection vl)
                (rightTrace.terminalProjection vr))
          (Measure.pi fun _ => paperMeasure))
    (hjoint :
      Integrable
        (fun p :
            (leftRes.SurvivingCoordinate → T4) ×
              (rightRes.SurvivingCoordinate → T4) =>
          (leftRes.residualIntegrand ρ ε x y
              (leftRes.reconstruct p.1) : ℂ) *
            ((rightRes.residualIntegrand ρ ε z w
                (rightRes.reconstruct p.2) : ℂ) *
              cross
                (leftTrace.terminalProjection p.1)
                (rightTrace.terminalProjection p.2)))
        ((Measure.pi fun _ :
            leftRes.SurvivingCoordinate => paperMeasure).prod
          (Measure.pi fun _ :
            rightRes.SurvivingCoordinate => paperMeasure))) :
    (∀ᵐ vr ∂(Measure.pi fun _ :
        rightRes.SurvivingCoordinate => paperMeasure),
      leftTrace.WeightedIntegrableAlong x y
        (fun vl =>
          cross vl (rightTrace.terminalProjection vr))) ∧
      rightTrace.WeightedIntegrableAlong z w
        (fun vr =>
          ∫ vl :
              leftTrace.terminalPrefix.SurvivingCoordinate → T4,
            ((leftTrace.terminalPrefix.residualIntegrand
                ρ ε x y
                (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
              cross vl vr)
            ∂Measure.pi fun _ => paperMeasure) := by
  have hleft :
      ∀ᵐ vr ∂(Measure.pi fun _ :
          rightRes.SurvivingCoordinate => paperMeasure),
        leftTrace.WeightedIntegrableAlong x y
          (fun vl =>
            cross vl (rightTrace.terminalProjection vr)) := by
    filter_upwards [hleftRoot] with vr hvr
    exact
      leftTrace.weightedIntegrableAlong_of_integrable
        x y
        (fun vl =>
          cross vl (rightTrace.terminalProjection vr))
        hvr
  have hleftEq :
      ∀ᵐ vr ∂(Measure.pi fun _ :
          rightRes.SurvivingCoordinate => paperMeasure),
        (lamEps lam ε : ℂ) ^ (2 * leftRes.remainingOrder) *
            (∫ vl : leftRes.SurvivingCoordinate → T4,
              (leftRes.residualIntegrand ρ ε x y
                  (leftRes.reconstruct vl) : ℂ) *
                cross
                  (leftTrace.terminalProjection vl)
                  (rightTrace.terminalProjection vr)
              ∂Measure.pi fun _ => paperMeasure) =
          ∫ vl :
              leftTrace.terminalPrefix.SurvivingCoordinate → T4,
            ((leftTrace.terminalPrefix.residualIntegrand
                ρ ε x y
                (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
              cross vl (rightTrace.terminalProjection vr))
            ∂Measure.pi fun _ => paperMeasure := by
    filter_upwards [hleft] with vr hvr
    exact
      leftTrace.lamEps_pow_integral_mul_terminalOuter_eq_terminal
        x y
        (fun vl =>
          cross vl (rightTrace.terminalProjection vr))
        hvr
  have hiterated :
      Integrable
        (fun vr : rightRes.SurvivingCoordinate → T4 =>
          ∫ vl : leftRes.SurvivingCoordinate → T4,
            (leftRes.residualIntegrand ρ ε x y
                (leftRes.reconstruct vl) : ℂ) *
              ((rightRes.residualIntegrand ρ ε z w
                  (rightRes.reconstruct vr) : ℂ) *
                cross
                  (leftTrace.terminalProjection vl)
                  (rightTrace.terminalProjection vr))
            ∂Measure.pi fun _ => paperMeasure)
        (Measure.pi fun _ => paperMeasure) :=
    hjoint.integral_prod_right
  have hrightRootUnscaled :
      Integrable
        (fun vr : rightRes.SurvivingCoordinate → T4 =>
          (rightRes.residualIntegrand ρ ε z w
              (rightRes.reconstruct vr) : ℂ) *
            (∫ vl : leftRes.SurvivingCoordinate → T4,
              (leftRes.residualIntegrand ρ ε x y
                  (leftRes.reconstruct vl) : ℂ) *
                cross
                  (leftTrace.terminalProjection vl)
                  (rightTrace.terminalProjection vr)
              ∂Measure.pi fun _ => paperMeasure))
        (Measure.pi fun _ => paperMeasure) := by
    apply hiterated.congr
    filter_upwards with vr
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with vl
    ring
  have hrightScaled :=
    hrightRootUnscaled.const_mul
      ((lamEps lam ε : ℂ) ^
        (2 * leftRes.remainingOrder))
  have hrightRoot :
      Integrable
        (fun vr : rightRes.SurvivingCoordinate → T4 =>
          (rightRes.residualIntegrand ρ ε z w
              (rightRes.reconstruct vr) : ℂ) *
            (∫ vl :
                leftTrace.terminalPrefix.SurvivingCoordinate → T4,
              ((leftTrace.terminalPrefix.residualIntegrand
                  ρ ε x y
                  (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
                cross vl (rightTrace.terminalProjection vr))
              ∂Measure.pi fun _ => paperMeasure))
        (Measure.pi fun _ => paperMeasure) := by
    apply hrightScaled.congr
    filter_upwards [hleftEq] with vr hvr
    rw [← hvr]
    ring
  exact
    ⟨hleft,
      rightTrace.weightedIntegrableAlong_of_integrable
        z w
        (fun vr =>
          ∫ vl :
              leftTrace.terminalPrefix.SurvivingCoordinate → T4,
            ((leftTrace.terminalPrefix.residualIntegrand
                ρ ε x y
                (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
              cross vl vr)
            ∂Measure.pi fun _ => paperMeasure)
        hrightRoot⟩

end R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

end

end Anderson4D
