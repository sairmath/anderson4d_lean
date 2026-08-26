import Anderson4D.DetParametrix.Paper42_Moment.R324DirectBoundaryBranch
import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalStopTraceAssembly
import Anderson4D.DetParametrix.Paper42_Moment.R324ShortcutTerminalSchedule
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRefinedStep23Closure
import Anderson4D.DetParametrix.Paper42_Moment.R324SignedRoutedEndpointBudget
import Anderson4D.DetParametrix.Paper42_Moment.R324DriverClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalCrossProjection
import Anderson4D.DetParametrix.Paper42_Moment.R324TerminalJointIntegrability
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperOutgoingEndpointFubini
import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfEndpointTerminalGeometry
import Anderson4D.DetParametrix.Paper42_Moment.R324InitialEndpointGroupedToCompleteRun
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointHalfGlue
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointCaseAssembly
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperBudgetedAlternatingTransport

/-!
# Paper Step 4(A): structural two-half endpoint splice

This file records two facts used when the four external Fourier variables
are integrated only after the signed within-half removals.

* On a residual half, the exceptional incoming block and an exceptional
  outgoing block cannot be the same analytic step.  If they were, that
  step would span the whole current carrier and, being the last step, would
  leave no final single.  Thus the same-block case belongs to the full/full
  Step-1 branch.
* When both endpoints of both residual halves are direct, the genuine
  terminal density factors exactly through four translated Green modes.
  The displayed norm identity is taken only after this signed four-endpoint
  identity; the complete cross-covariance core is never split.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open SmoothCutoff

/-! ## The one-endpoint ordinary-to-inserted integral bridge -/

/-- Integrated form of the paper's one exceptional-endpoint sacrifice.

This lemma is deliberately applied only after the corresponding signed
endpoint identity has been completed.  It turns the ordinary primitive
majorant produced by that identity into the inserted majorant, charging
exactly the single `eps^-2` cost prescribed in Step 4(A). -/
theorem integral_primitiveKernelMajorant_le_endpointSacrifice_mul_inserted
    (C lam supportConstant : ℝ) (n : ℕ)
    {eps : ℝ} (heps : 0 < eps) :
    (∫ z : T4,
        primitiveKernelMajorant C lam eps supportConstant n z
        ∂paperMeasure) ≤
      r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
        ∫ z : T4,
          primitiveInsertedMajorant C lam eps supportConstant n z
          ∂paperMeasure := by
  calc
    (∫ z : T4,
        primitiveKernelMajorant C lam eps supportConstant n z
        ∂paperMeasure) ≤
        ∫ z : T4,
          r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
            primitiveInsertedMajorant C lam eps supportConstant n z
          ∂paperMeasure := by
      apply integral_mono
        (integrable_primitiveKernelMajorant
          C lam eps supportConstant n heps)
        ((integrable_primitiveInsertedMajorant
          C lam eps supportConstant n heps).const_mul
            (r324EndpointPrimitiveSacrifice eps .insertedSacrifice))
      intro z
      simpa [r324EndpointCasePrimitiveMajorant] using
        r324EndpointCasePrimitiveMajorant_le_sacrifice_mul_inserted
          R324EndpointReductionCase.insertedSacrifice
          C lam supportConstant n heps z
    _ =
        r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
          ∫ z : T4,
            primitiveInsertedMajorant C lam eps supportConstant n z
            ∂paperMeasure := by
      rw [integral_const_mul]

/-! ## The retained outgoing terminal, jointly in its endpoint variables -/

/-- Regroup the free outgoing variable, the retained primitive tuple, and
the post-terminal carrier in the paper order
`(y,(t,v)) ↦ (v,(t,y))`. -/
def r324OutgoingTerminalJointRegroupMeasurableEquiv
    (Y T V : Type*) [MeasurableSpace Y] [MeasurableSpace T]
    [MeasurableSpace V] :
    Y × (T × V) ≃ᵐ V × (T × Y) :=
  (MeasurableEquiv.prodAssoc
      (α := Y) (β := T) (γ := V)).symm.trans
    ((MeasurableEquiv.prodComm : (Y × T) × V ≃ᵐ V × (Y × T)).trans
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl V)
        (MeasurableEquiv.prodComm : Y × T ≃ᵐ T × Y)))

@[simp]
theorem r324OutgoingTerminalJointRegroupMeasurableEquiv_apply
    {Y T V : Type*} [MeasurableSpace Y] [MeasurableSpace T]
    [MeasurableSpace V] (q : Y × (T × V)) :
    r324OutgoingTerminalJointRegroupMeasurableEquiv Y T V q =
      (q.2.2, q.2.1, q.1) :=
  rfl

/-- The endpoint/primitive/post regroup preserves the corresponding
product measures. -/
theorem measurePreserving_r324OutgoingTerminalJointRegroupMeasurableEquiv
    {Y T V : Type*} [MeasurableSpace Y] [MeasurableSpace T]
    [MeasurableSpace V]
    (muY : Measure Y) (muT : Measure T) (muV : Measure V)
    [SFinite muY] [SFinite muT] [SFinite muV] :
    MeasurePreserving
      (r324OutgoingTerminalJointRegroupMeasurableEquiv Y T V)
      (muY.prod (muT.prod muV))
      (muV.prod (muT.prod muY)) := by
  let hAssoc := (measurePreserving_prodAssoc muY muT muV).symm
  let hSwap := Measure.measurePreserving_swap
    (μ := muY.prod muT) (ν := muV)
  let hInner := (MeasurePreserving.id muV).prod
    (Measure.measurePreserving_swap (μ := muY) (ν := muT))
  exact (hInner.comp (hSwap.comp hAssoc)).congr
    (r324OutgoingTerminalJointRegroupMeasurableEquiv Y T V).measurable
    (Filter.Eventually.of_forall fun _ => rfl)

namespace R324WithinHalfResidualPrefix
namespace R324PaperOutgoingEndpointTerminal

variable {rho : SmoothCutoff} {lam eps : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}

/-- The signed post-terminal density after the retained primitive tuple and
outgoing Fourier variable have both been evaluated. -/
def outgoingEndpointDefectDensity
    (data : R324PaperOutgoingEndpointTerminal res)
    (coefficient : (data.terminalPost.SurvivingCoordinate → T4) → ℂ)
    (incomingMode outgoingMode : Z4) (x : T4)
    (v : data.terminalPost.SurvivingCoordinate → T4)
    (first : T4) : ℂ :=
  ((data.terminalContext.state.edges
      (r324WithinHalfPredecessorSlot
        data.terminalContext.state data.terminalContext.step)
      (data.terminalPredecessorPoint x v - first) : ℝ) : ℂ) *
    (paperSecondOrderModeDecay outgoingMode : ℂ) *
    charT4 outgoingMode first *
    incomingExceptionalPrimitiveDefect rho lam eps
      (residualBlockOrder data.terminalData.terminal.2)
      data.terminalContext.one_le_blockOrder
      data.terminalContext.internalEdges outgoingMode *
    data.terminalSplitOuter coefficient incomingMode x v

/-- Joint stop-carrier form of the retained outgoing operation.  This is
the consumer used after an exceptional incoming endpoint has already been
collapsed and transported to the stop immediately before the distinct
outgoing terminal. -/
theorem lamEps_pow_integral_stop_outgoingEndpoint_eq_defect
    (data : R324PaperOutgoingEndpointTerminal res)
    (hpred :
      r324WithinHalfPredecessorSlot data.endpoint.stop.state
          data.terminalData.terminal ≠ 0)
    (hactive : data.terminalPost.state.active.Nonempty)
    (coefficient : (data.terminalPost.SurvivingCoordinate → T4) → ℂ)
    (incomingMode outgoingMode : Z4) (x : T4)
    (hsource :
      Integrable
        (fun q : T4 × (data.endpoint.stop.SurvivingCoordinate → T4) =>
          data.endpoint.stop.incomingPhasedResidualDensity
            (coefficient
              ((data.endpoint.stop.splitSurvivingPiMeasurableEquiv
                data.terminalData.terminal [] data.endpoint.stop_remaining
                q.2).2))
            incomingMode rho eps x q.1 q.2)
        (paperMeasure.prod (Measure.pi fun _ => paperMeasure)))
    (hint :
      ∀ (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminalData.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder data.terminalData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder
              data.terminalData.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder data.terminalData.terminal.2)
              kappaB.1 data.terminalContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder
                first (first - gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam eps : ℂ) ^ (2 * data.endpoint.stop.remainingOrder) *
        (∫ q : T4 × (data.endpoint.stop.SurvivingCoordinate → T4),
          charT4 outgoingMode q.1 *
            data.endpoint.stop.incomingPhasedResidualDensity
              (coefficient
                ((data.endpoint.stop.splitSurvivingPiMeasurableEquiv
                  data.terminalData.terminal [] data.endpoint.stop_remaining
                  q.2).2))
              incomingMode rho eps x q.1 q.2
          ∂(paperMeasure.prod (Measure.pi fun _ => paperMeasure))) =
      ∫ v : data.terminalPost.SurvivingCoordinate → T4,
        ∫ first : T4,
          data.outgoingEndpointDefectDensity
            coefficient incomingMode outgoingMode x v first
          ∂paperMeasure
        ∂Measure.pi fun _ => paperMeasure := by
  let split := data.endpoint.stop.splitSurvivingPiMeasurableEquiv
    data.terminalData.terminal [] data.endpoint.stop_remaining
  let muStop := Measure.pi fun _ : data.endpoint.stop.SurvivingCoordinate => paperMeasure
  let muTuple := Measure.pi fun _ :
      Fin (2 * residualBlockOrder data.terminalData.terminal.2) => paperMeasure
  let muPost := Measure.pi fun _ : data.terminalPost.SurvivingCoordinate => paperMeasure
  have hphaseMeas : Measurable (fun q : T4 ×
      (data.endpoint.stop.SurvivingCoordinate → T4) =>
        charT4 outgoingMode q.1) :=
    (continuous_charT4 outgoingMode).measurable.comp measurable_fst
  have hphase :
      Integrable
        (fun q : T4 × (data.endpoint.stop.SurvivingCoordinate → T4) =>
          charT4 outgoingMode q.1 *
            data.endpoint.stop.incomingPhasedResidualDensity
              (coefficient (split q.2).2)
              incomingMode rho eps x q.1 q.2)
        (paperMeasure.prod muStop) :=
    hsource.bdd_mul hphaseMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by rw [norm_charT4])
  let splitProduct :
      T4 × (data.endpoint.stop.SurvivingCoordinate → T4) ≃ᵐ
        T4 ×
          ((Fin (2 * residualBlockOrder data.terminalData.terminal.2) → T4) ×
            (data.terminalPost.SurvivingCoordinate → T4)) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl T4) split
  let regroup := splitProduct.trans
    (r324OutgoingTerminalJointRegroupMeasurableEquiv
      T4
      (Fin (2 * residualBlockOrder data.terminalData.terminal.2) → T4)
      (data.terminalPost.SurvivingCoordinate → T4))
  have hsplit : MeasurePreserving split muStop (muTuple.prod muPost) :=
    data.endpoint.stop.measurePreserving_splitSurvivingPiMeasurableEquiv
      data.terminalData.terminal [] data.endpoint.stop_remaining
  have hregroup :
      MeasurePreserving regroup
        (paperMeasure.prod muStop)
        (muPost.prod (muTuple.prod paperMeasure)) :=
    (measurePreserving_r324OutgoingTerminalJointRegroupMeasurableEquiv
      paperMeasure muTuple muPost).comp
        ((MeasurePreserving.id paperMeasure).prod hsplit)
  let G :
      (data.terminalPost.SurvivingCoordinate → T4) ×
        ((Fin (2 * residualBlockOrder data.terminalData.terminal.2) → T4) × T4) → ℂ :=
    fun q => charT4 outgoingMode q.2.2 *
      data.endpoint.stop.incomingPhasedResidualDensity
        (coefficient q.1) incomingMode rho eps x q.2.2
        (split.symm (q.2.1, q.1))
  have hG : Integrable G (muPost.prod (muTuple.prod paperMeasure)) := by
    refine (hregroup.integrable_comp_emb regroup.measurableEmbedding).mp ?_
    apply hphase.congr
    filter_upwards with q
    change
      charT4 outgoingMode q.1 *
          data.endpoint.stop.incomingPhasedResidualDensity
            (coefficient (split q.2).2) incomingMode rho eps x q.1 q.2 =
        charT4 outgoingMode q.1 *
          data.endpoint.stop.incomingPhasedResidualDensity
            (coefficient (split q.2).2) incomingMode rho eps x q.1
            (split.symm ((split q.2).1, (split q.2).2))
    rw [Prod.eta (split q.2), MeasurableEquiv.symm_apply_apply]
  have hintegral :
      (∫ q, charT4 outgoingMode q.1 *
          data.endpoint.stop.incomingPhasedResidualDensity
            (coefficient (split q.2).2) incomingMode rho eps x q.1 q.2
          ∂(paperMeasure.prod muStop)) =
        ∫ q, G q ∂(muPost.prod (muTuple.prod paperMeasure)) := by
    rw [← hregroup.integral_comp' G]
    apply integral_congr_ae
    filter_upwards with q
    change
      charT4 outgoingMode q.1 *
          data.endpoint.stop.incomingPhasedResidualDensity
            (coefficient (split q.2).2) incomingMode rho eps x q.1 q.2 =
        charT4 outgoingMode q.1 *
          data.endpoint.stop.incomingPhasedResidualDensity
            (coefficient (split q.2).2) incomingMode rho eps x q.1
            (split.symm ((split q.2).1, (split q.2).2))
    rw [Prod.eta (split q.2), MeasurableEquiv.symm_apply_apply]
  have hsections : ∀ᵐ v ∂muPost,
      Integrable (fun q => G (v, q)) (muTuple.prod paperMeasure) :=
    hG.prod_right_ae
  rw [hintegral, integral_prod _ hG, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hsections] with v hv
  rw [integral_prod _ hv, data.stop_remainingOrder_eq_terminal]
  have hsection := data.lamEps_pow_integral_standardBlock_outgoingFourier_eq_defect
    hpred hactive coefficient incomingMode outgoingMode x v
    hv.integral_prod_left hint
  simpa only [outgoingEndpointDefectDensity,
    incomingExceptionalPrimitiveDefect] using hsection

end R324PaperOutgoingEndpointTerminal
namespace R324WithinHalfEndpointTerminalGeometry

variable {rho : SmoothCutoff} {lam eps : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- View the canonical endpoint-terminal geometry as the arbitrary-prefix
terminal package used by the exact outgoing Fourier calculation. -/
def paperOutgoingTerminal
    (data :
      R324WithinHalfEndpointTerminalGeometry
        (ρ := rho) (lam := lam) (ε := eps) (κ := pairing)) :
    R324PaperOutgoingEndpointTerminal
      (R324WithinHalfResidualPrefix.initial rho lam eps pairing) where
  terminalData := data.terminalData
  endpoint := data.transport

/-- After the retained outgoing head is removed, its erased outer factor
is exactly the completed post-terminal chain with both genuine boundary
slots deleted.  This is the pointwise seam needed to Fourier-integrate a
direct incoming Green leg after the outgoing ordinary-`J` operation. -/
theorem incomingErasedHeadOuterFactor_eq_terminalPost_endpointErasedSignedChain
    (data :
      R324WithinHalfEndpointTerminalGeometry
        (ρ := rho) (lam := lam) (ε := eps) (κ := pairing))
    (hpred :
      r324WithinHalfPredecessorSlot data.transport.stop.state
          data.terminalData.terminal ≠ 0)
    (hactive :
      (data.transport.stop.afterHead data.terminalData.terminal []
        data.stop_remaining_eq_singleton).state.active.Nonempty)
    (x y : T4)
    (v :
      (data.transport.stop.afterHead data.terminalData.terminal []
        data.stop_remaining_eq_singleton).SurvivingCoordinate → T4) :
    data.transport.stop.incomingErasedHeadOuterFactor
        data.terminalData.terminal [] data.stop_remaining_eq_singleton
        rho eps x y v =
      (data.transport.stop.afterHead data.terminalData.terminal []
        data.stop_remaining_eq_singleton).endpointErasedSignedChain
        hactive x y
        ((data.transport.stop.afterHead data.terminalData.terminal []
          data.stop_remaining_eq_singleton).reconstruct v) := by
  have hpredOut :
      r324WithinHalfPredecessorSlot data.transport.stop.state
          data.terminalData.terminal =
        (data.transport.stop.afterHead data.terminalData.terminal []
          data.stop_remaining_eq_singleton).terminalOutgoingEdgeSlot
            hactive := by
    simpa only [paperOutgoingTerminal,
      R324PaperOutgoingEndpointTerminal.terminalPost] using
      data.paperOutgoingTerminal.predecessorSlot_eq_terminalPost_outgoing
        hpred hactive
  unfold R324WithinHalfResidualPrefix.incomingErasedHeadOuterFactor
  rw [(data.transport.stop.afterHead data.terminalData.terminal []
        data.stop_remaining_eq_singleton)
      |>.residualDifferenceProduct_of_remaining_nil
      rfl x y,
    (data.transport.stop.afterHead data.terminalData.terminal []
      data.stop_remaining_eq_singleton)
      |>.residualPrimitiveProduct_of_remaining_nil
      rfl rho eps]
  simp only [mul_one]
  unfold R324WithinHalfResidualPrefix.incomingErasedHeadOuterChainProductAfter
    R324WithinHalfResidualPrefix.endpointErasedSignedChain
  symm
  apply Finset.prod_subset
  · intro edge hedge
    have hedgeOut := (Finset.mem_erase.mp hedge).1
    have hedgeZero := (Finset.mem_erase.mp
      (Finset.mem_erase.mp hedge).2).1
    have hedgeActive := (Finset.mem_erase.mp
      (Finset.mem_erase.mp hedge).2).2
    apply Finset.mem_erase.mpr
    refine ⟨hedgeZero, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [R324WithinHalfResidualPrefix.headChainSlots,
      Finset.mem_union, Finset.mem_singleton]
    push Not
    constructor
    · intro hedgePred
      apply hedgeOut
      exact hedgePred.trans hpredOut
    · intro hedgeInternal
      have hpostSlots := data.transport.stop.afterHead_activeEdgeSlots
        data.terminalData.terminal [] data.stop_remaining_eq_singleton
      rw [hpostSlots] at hedgeActive
      exact (Finset.mem_sdiff.mp hedgeActive).2
        (Finset.mem_union_left _ hedgeInternal)
  · intro edge hedgeOuter hedgeNotEndpoint
    have hedgeZero := (Finset.mem_erase.mp hedgeOuter).1
    have hedgeNotHead := (Finset.mem_sdiff.mp
      (Finset.mem_erase.mp hedgeOuter).2).2
    by_cases hedgeActive :
        edge ∈ (data.transport.stop.afterHead data.terminalData.terminal []
          data.stop_remaining_eq_singleton).activeEdgeSlots
    · have hedgeOut : edge =
          (data.transport.stop.afterHead data.terminalData.terminal []
            data.stop_remaining_eq_singleton).terminalOutgoingEdgeSlot hactive := by
        by_contra hne
        apply hedgeNotEndpoint
        exact Finset.mem_erase.mpr
          ⟨hne, Finset.mem_erase.mpr ⟨hedgeZero, hedgeActive⟩⟩
      exfalso
      apply hedgeNotHead
      rw [R324WithinHalfResidualPrefix.headChainSlots,
        Finset.mem_union, Finset.mem_singleton]
      left
      exact hedgeOut.trans hpredOut.symm
    · rw [(data.transport.stop.afterHead data.terminalData.terminal []
          data.stop_remaining_eq_singleton)
          |>.residualChainEdgeFactor_of_remaining_nil
          rfl,
        if_neg hedgeActive]

/-- Exact joint outgoing-endpoint operation, starting at the initial
residual half.  The proper prefix is transported while the expression is
still signed; the terminal primitive tuple and the outgoing endpoint are
then regrouped and integrated in the paper order.  The norm is nowhere
taken. -/
theorem lamEps_pow_integral_initial_outgoingEndpoint_eq_defect
    (data :
      R324WithinHalfEndpointTerminalGeometry
        (ρ := rho) (lam := lam) (ε := eps) (κ := pairing))
    (hpred :
      r324WithinHalfPredecessorSlot data.transport.stop.state
          data.terminalData.terminal ≠ 0)
    (hactive : data.paperOutgoingTerminal.terminalPost.state.active.Nonempty)
    (coefficient :
      (data.paperOutgoingTerminal.terminalPost.SurvivingCoordinate → T4) → ℂ)
    (incomingMode outgoingMode : Z4) (x : T4)
    (hcurrent :
      Integrable
        (fun q : T4 ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate → T4) =>
          (R324WithinHalfResidualPrefix.initial rho lam eps pairing
            |>.incomingPhasedResidualDensity
              (coefficient
                ((data.transport.stop.splitSurvivingPiMeasurableEquiv
                    data.terminalData.terminal []
                    data.stop_remaining_eq_singleton
                    (data.transport.projection q.2)).2))
              incomingMode rho eps x q.1 q.2))
        (paperMeasure.prod
          (Measure.pi fun _ => paperMeasure)))
    (hstop :
      Integrable
        (fun q : T4 × (data.transport.stop.SurvivingCoordinate → T4) =>
          data.transport.stop.incomingPhasedResidualDensity
            (data.transport.multiplier incomingMode *
              coefficient
                ((data.transport.stop.splitSurvivingPiMeasurableEquiv
                  data.terminalData.terminal []
                  data.stop_remaining_eq_singleton q.2).2))
            incomingMode rho eps x q.1 q.2)
        (paperMeasure.prod
          (Measure.pi fun _ => paperMeasure)))
    (hint :
      ∀ (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminalData.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder data.terminalData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder
              data.terminalData.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder data.terminalData.terminal.2)
              kappaB.1 data.paperOutgoingTerminal.terminalContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminalData.terminal.2)
                data.paperOutgoingTerminal.terminalContext.one_le_blockOrder
                first (first - gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam eps : ℂ) ^
          (2 * (R324WithinHalfResidualPrefix.initial
            rho lam eps pairing).remainingOrder) *
        (∫ q : T4 ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate → T4),
          charT4 outgoingMode q.1 *
            (R324WithinHalfResidualPrefix.initial rho lam eps pairing
              |>.incomingPhasedResidualDensity
                (coefficient
                  ((data.transport.stop.splitSurvivingPiMeasurableEquiv
                      data.terminalData.terminal []
                      data.stop_remaining_eq_singleton
                      (data.transport.projection q.2)).2))
                incomingMode rho eps x q.1 q.2)
          ∂(paperMeasure.prod (Measure.pi fun _ => paperMeasure))) =
      ∫ v : data.paperOutgoingTerminal.terminalPost.SurvivingCoordinate → T4,
        ∫ first : T4,
          ((data.paperOutgoingTerminal.terminalContext.state.edges
              (r324WithinHalfPredecessorSlot
                data.paperOutgoingTerminal.terminalContext.state
                data.paperOutgoingTerminal.terminalContext.step)
              (data.paperOutgoingTerminal.terminalPredecessorPoint x v - first) :
                ℝ) : ℂ) *
            (paperSecondOrderModeDecay outgoingMode : ℂ) *
            charT4 outgoingMode first *
            (∫ gap : T4,
              (primitiveKernelDiff rho lam eps
                  (residualBlockOrder data.terminalData.terminal.2)
                  data.paperOutgoingTerminal.terminalContext.one_le_blockOrder
                  data.paperOutgoingTerminal.terminalContext.internalEdges gap : ℂ) *
                (charT4 (-outgoingMode) gap - 1)
              ∂paperMeasure) *
            data.paperOutgoingTerminal.terminalSplitOuter
              (fun v => data.transport.multiplier incomingMode * coefficient v)
              incomingMode x v
          ∂paperMeasure
∂Measure.pi fun _ => paperMeasure := by
  let initial := R324WithinHalfResidualPrefix.initial rho lam eps pairing
  let split :=
    data.transport.stop.splitSurvivingPiMeasurableEquiv
      data.terminalData.terminal [] data.stop_remaining_eq_singleton
  let muInitial := Measure.pi fun _ : initial.SurvivingCoordinate => paperMeasure
  let muStop := Measure.pi fun _ : data.transport.stop.SurvivingCoordinate => paperMeasure
  let muTuple := Measure.pi fun _ :
      Fin (2 * residualBlockOrder data.terminalData.terminal.2) => paperMeasure
  let muPost := Measure.pi fun _ :
      data.paperOutgoingTerminal.terminalPost.SurvivingCoordinate => paperMeasure
  let currentBare : T4 × (initial.SurvivingCoordinate → T4) → ℂ :=
    fun q => initial.incomingPhasedResidualDensity
      (coefficient (split (data.transport.projection q.2)).2)
      incomingMode rho eps x q.1 q.2
  let stopBare : T4 × (data.transport.stop.SurvivingCoordinate → T4) → ℂ :=
    fun q => data.transport.stop.incomingPhasedResidualDensity
      (data.transport.multiplier incomingMode * coefficient (split q.2).2)
      incomingMode rho eps x q.1 q.2
  have hphaseMeas : Measurable (fun q : T4 ×
      (initial.SurvivingCoordinate → T4) => charT4 outgoingMode q.1) :=
    (continuous_charT4 outgoingMode).measurable.comp measurable_fst
  have hcurrentPhase :
      Integrable (fun q => charT4 outgoingMode q.1 * currentBare q)
        (paperMeasure.prod muInitial) :=
    hcurrent.bdd_mul hphaseMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by rw [norm_charT4])
  have hstopPhase :
      Integrable (fun q => charT4 outgoingMode q.1 * stopBare q)
        (paperMeasure.prod muStop) := by
    have hmeas : Measurable (fun q : T4 ×
        (data.transport.stop.SurvivingCoordinate → T4) =>
          charT4 outgoingMode q.1) :=
      (continuous_charT4 outgoingMode).measurable.comp measurable_fst
    exact hstop.bdd_mul hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by rw [norm_charT4])
  have htransport :
      (lamEps lam eps : ℂ) ^ (2 * initial.remainingOrder) *
          (∫ q, charT4 outgoingMode q.1 * currentBare q
            ∂(paperMeasure.prod muInitial)) =
        (lamEps lam eps : ℂ) ^ (2 * data.transport.stop.remainingOrder) *
          (∫ q, charT4 outgoingMode q.1 * stopBare q
            ∂(paperMeasure.prod muStop)) := by
    rw [integral_prod _ hcurrentPhase, integral_prod _ hstopPhase]
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hcurrent.prod_right_ae] with y hy
    have ht := data.transport.transport x y incomingMode
      (fun u => coefficient (split u).2) hy
    calc
      (lamEps lam eps : ℂ) ^ (2 * initial.remainingOrder) *
          (∫ u, charT4 outgoingMode y * currentBare (y, u) ∂muInitial) =
        charT4 outgoingMode y *
          ((lamEps lam eps : ℂ) ^ (2 * initial.remainingOrder) *
            ∫ u, currentBare (y, u) ∂muInitial) := by
          rw [integral_const_mul]
          ring
      _ = charT4 outgoingMode y *
          ((lamEps lam eps : ℂ) ^ (2 * data.transport.stop.remainingOrder) *
            ∫ u, stopBare (y, u) ∂muStop) := by rw [ht]
      _ = (lamEps lam eps : ℂ) ^ (2 * data.transport.stop.remainingOrder) *
          (∫ u, charT4 outgoingMode y * stopBare (y, u) ∂muStop) := by
          rw [integral_const_mul]
          ring
  let splitProduct :
      T4 × (data.transport.stop.SurvivingCoordinate → T4) ≃ᵐ
        T4 ×
          ((Fin (2 * residualBlockOrder data.terminalData.terminal.2) → T4) ×
            (data.paperOutgoingTerminal.terminalPost.SurvivingCoordinate → T4)) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl T4) split
  let regroup := splitProduct.trans
    (r324OutgoingTerminalJointRegroupMeasurableEquiv
      T4
      (Fin (2 * residualBlockOrder data.terminalData.terminal.2) → T4)
      (data.paperOutgoingTerminal.terminalPost.SurvivingCoordinate → T4))
  have hsplit : MeasurePreserving split muStop (muTuple.prod muPost) :=
    data.transport.stop.measurePreserving_splitSurvivingPiMeasurableEquiv
      data.terminalData.terminal [] data.stop_remaining_eq_singleton
  have hsplitProduct :
      MeasurePreserving splitProduct
        (paperMeasure.prod muStop)
        (paperMeasure.prod (muTuple.prod muPost)) :=
    (MeasurePreserving.id paperMeasure).prod hsplit
  have hregroup :
      MeasurePreserving regroup
        (paperMeasure.prod muStop)
        (muPost.prod (muTuple.prod paperMeasure)) :=
    (measurePreserving_r324OutgoingTerminalJointRegroupMeasurableEquiv
      paperMeasure muTuple muPost).comp hsplitProduct
  let G :
      (data.paperOutgoingTerminal.terminalPost.SurvivingCoordinate → T4) ×
        ((Fin (2 * residualBlockOrder data.terminalData.terminal.2) → T4) × T4) → ℂ :=
    fun q => charT4 outgoingMode q.2.2 *
      data.transport.stop.incomingPhasedResidualDensity
        (data.transport.multiplier incomingMode * coefficient q.1)
        incomingMode rho eps x q.2.2
        (split.symm (q.2.1, q.1))
  have hG : Integrable G (muPost.prod (muTuple.prod paperMeasure)) := by
    refine (hregroup.integrable_comp_emb regroup.measurableEmbedding).mp ?_
    apply hstopPhase.congr
    filter_upwards with q
    show charT4 outgoingMode q.1 * stopBare q = G (regroup q)
    change
      charT4 outgoingMode q.1 *
          data.transport.stop.incomingPhasedResidualDensity
            (data.transport.multiplier incomingMode * coefficient (split q.2).2)
            incomingMode rho eps x q.1 q.2 =
        charT4 outgoingMode q.1 *
          data.transport.stop.incomingPhasedResidualDensity
            (data.transport.multiplier incomingMode * coefficient (split q.2).2)
            incomingMode rho eps x q.1
            (split.symm ((split q.2).1, (split q.2).2))
    rw [Prod.eta (split q.2), MeasurableEquiv.symm_apply_apply]
  have hregroupIntegral :
      (∫ q, charT4 outgoingMode q.1 * stopBare q
          ∂(paperMeasure.prod muStop)) =
        ∫ q, G q ∂(muPost.prod (muTuple.prod paperMeasure)) := by
    rw [← hregroup.integral_comp' G]
    apply integral_congr_ae
    filter_upwards with q
    change
      charT4 outgoingMode q.1 *
          data.transport.stop.incomingPhasedResidualDensity
            (data.transport.multiplier incomingMode * coefficient (split q.2).2)
            incomingMode rho eps x q.1 q.2 =
        charT4 outgoingMode q.1 *
          data.transport.stop.incomingPhasedResidualDensity
            (data.transport.multiplier incomingMode * coefficient (split q.2).2)
            incomingMode rho eps x q.1
            (split.symm ((split q.2).1, (split q.2).2))
    rw [Prod.eta (split q.2), MeasurableEquiv.symm_apply_apply]
  have hsections :
      ∀ᵐ v ∂muPost,
        Integrable (fun q => G (v, q)) (muTuple.prod paperMeasure) :=
    hG.prod_right_ae
  calc
    (lamEps lam eps : ℂ) ^ (2 * initial.remainingOrder) *
          (∫ q, charT4 outgoingMode q.1 * currentBare q
            ∂(paperMeasure.prod muInitial)) =
        (lamEps lam eps : ℂ) ^ (2 * data.transport.stop.remainingOrder) *
          (∫ q, charT4 outgoingMode q.1 * stopBare q
            ∂(paperMeasure.prod muStop)) := htransport
    _ = (lamEps lam eps : ℂ) ^ (2 * data.transport.stop.remainingOrder) *
          (∫ q, G q ∂(muPost.prod (muTuple.prod paperMeasure))) := by
      rw [hregroupIntegral]
    _ = ∫ v,
          (lamEps lam eps : ℂ) ^ (2 * data.transport.stop.remainingOrder) *
            (∫ t, ∫ y, G (v, (t, y)) ∂paperMeasure ∂muTuple)
          ∂muPost := by
      rw [integral_prod _ hG, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hsections] with v hv
      rw [integral_prod _ hv]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hsections] with v hv
      have hhead := hv.integral_prod_left
      rw [data.stop_remainingOrder_eq_terminal]
      exact data.paperOutgoingTerminal
        |>.lamEps_pow_integral_standardBlock_outgoingFourier_eq_defect
        hpred hactive
        (fun v => data.transport.multiplier incomingMode * coefficient v)
        incomingMode outgoingMode x v hhead hint

/-- The signed density exposed after the retained outgoing primitive tuple
and external endpoint have both been integrated. -/
def outgoingEndpointDefectDensity
    (data :
      R324WithinHalfEndpointTerminalGeometry
        (ρ := rho) (lam := lam) (ε := eps) (κ := pairing))
    (coefficient :
      (data.paperOutgoingTerminal.terminalPost.SurvivingCoordinate → T4) → ℂ)
    (incomingMode outgoingMode : Z4) (x : T4)
    (v : data.paperOutgoingTerminal.terminalPost.SurvivingCoordinate → T4)
    (first : T4) : ℂ :=
  ((data.paperOutgoingTerminal.terminalContext.state.edges
      (r324WithinHalfPredecessorSlot
        data.paperOutgoingTerminal.terminalContext.state
        data.paperOutgoingTerminal.terminalContext.step)
      (data.paperOutgoingTerminal.terminalPredecessorPoint x v - first) : ℝ) : ℂ) *
    (paperSecondOrderModeDecay outgoingMode : ℂ) *
    charT4 outgoingMode first *
    incomingExceptionalPrimitiveDefect rho lam eps
      (residualBlockOrder data.terminalData.terminal.2)
      data.paperOutgoingTerminal.terminalContext.one_le_blockOrder
      data.paperOutgoingTerminal.terminalContext.internalEdges outgoingMode *
    data.paperOutgoingTerminal.terminalSplitOuter
      (fun v => data.transport.multiplier incomingMode * coefficient v)
      incomingMode x v

/-- Quantitative form of the local outgoing endpoint operation.  The norm
is taken only after the ordinary primitive phase defect has been formed;
the retained terminal is then charged by its transported edge certificate.
-/
theorem norm_outgoingEndpointDefectDensity_le_scaled
    {C supportConstant : ℝ}
    (data :
      R324WithinHalfEndpointTerminalGeometry
        (ρ := rho) (lam := lam) (ε := eps) (κ := pairing))
    (coefficient :
      (data.paperOutgoingTerminal.terminalPost.SurvivingCoordinate → T4) → ℂ)
    (incomingMode outgoingMode : Z4) (x : T4)
    (v : data.paperOutgoingTerminal.terminalPost.SurvivingCoordinate → T4)
    (first : T4)
    (heps : 0 < eps) (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hprop :
      ∀ (H : Fin (2 * residualBlockOrder
            data.terminalData.terminal.2 - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput
            (residualBlockOrder data.terminalData.terminal.2) H →
          MemEClassT4
              (primitiveKernelDiff rho lam eps
                (residualBlockOrder data.terminalData.terminal.2)
                data.paperOutgoingTerminal.terminalContext.one_le_blockOrder H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff rho lam eps
                (residualBlockOrder data.terminalData.terminal.2)
                data.paperOutgoingTerminal.terminalContext.one_le_blockOrder H) ∧
            PrimitiveKernelBounds rho lam eps
              (residualBlockOrder data.terminalData.terminal.2)
              data.paperOutgoingTerminal.terminalContext.one_le_blockOrder
              H supportConstant C) :
    ‖data.outgoingEndpointDefectDensity coefficient
        incomingMode outgoingMode x v first‖ ≤
      |data.paperOutgoingTerminal.terminalContext.state.edges
          (r324WithinHalfPredecessorSlot
            data.paperOutgoingTerminal.terminalContext.state
            data.paperOutgoingTerminal.terminalContext.step)
          (data.paperOutgoingTerminal.terminalPredecessorPoint x v - first)| *
        paperSecondOrderModeDecay outgoingMode *
        (2 * r324WithinHalfInternalEdgeScaleProduct
            data.paperOutgoingTerminal.terminalContext
            data.transport.stopScale *
          ∫ gap : T4,
            primitiveKernelMajorant C lam eps supportConstant
              (residualBlockOrder data.terminalData.terminal.2) gap
            ∂paperMeasure) *
        ‖data.paperOutgoingTerminal.terminalSplitOuter
          (fun v => data.transport.multiplier incomingMode * coefficient v)
          incomingMode x v‖ := by
  have hdefect :=
    norm_incomingExceptionalPrimitiveDefect_le_scaled_of_certificate
      data.paperOutgoingTerminal.terminalContext
      data.transport.stopScale data.transport.stopCertificate
      heps hC hlam hprop outgoingMode
  unfold outgoingEndpointDefectDensity
  rw [norm_mul, norm_mul, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperSecondOrderModeDecay_nonneg outgoingMode),
    norm_charT4, mul_one]
  exact
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdefect
        (mul_nonneg (abs_nonneg _)
          (paperSecondOrderModeDecay_nonneg outgoingMode)))
      (norm_nonneg _)

/-- Parameter-carrier form of the retained outgoing endpoint operation.
An already completed opposite half may be carried in `U`; the terminal
tuple and endpoint are still integrated sectionwise before the parameter
integral and before any norm. -/
theorem lamEps_pow_integral_parameter_initial_outgoingEndpoint_eq_defect
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U) [SFinite muU]
    (data :
      R324WithinHalfEndpointTerminalGeometry
        (ρ := rho) (lam := lam) (ε := eps) (κ := pairing))
    (hpred :
      r324WithinHalfPredecessorSlot data.transport.stop.state
          data.terminalData.terminal ≠ 0)
    (hactive : data.paperOutgoingTerminal.terminalPost.state.active.Nonempty)
    (coefficient : U →
      (data.paperOutgoingTerminal.terminalPost.SurvivingCoordinate → T4) → ℂ)
    (incomingMode outgoingMode : Z4) (x : U → T4)
    (hcurrent :
      Integrable
        (fun q : U × (T4 ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate → T4)) =>
          (R324WithinHalfResidualPrefix.initial rho lam eps pairing
            |>.incomingPhasedResidualDensity
              (coefficient q.1
                ((data.transport.stop.splitSurvivingPiMeasurableEquiv
                    data.terminalData.terminal []
                    data.stop_remaining_eq_singleton
                    (data.transport.projection q.2.2)).2))
              incomingMode rho eps (x q.1) q.2.1 q.2.2))
        (muU.prod (paperMeasure.prod
          (Measure.pi fun _ => paperMeasure))))
    (hstop :
      Integrable
        (fun q : U ×
            (T4 × (data.transport.stop.SurvivingCoordinate → T4)) =>
          data.transport.stop.incomingPhasedResidualDensity
            (data.transport.multiplier incomingMode *
              coefficient q.1
                ((data.transport.stop.splitSurvivingPiMeasurableEquiv
                  data.terminalData.terminal []
                  data.stop_remaining_eq_singleton q.2.2).2))
            incomingMode rho eps (x q.1) q.2.1 q.2.2)
        (muU.prod (paperMeasure.prod
          (Measure.pi fun _ => paperMeasure))))
    (hint :
      ∀ (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminalData.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder data.terminalData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder
              data.terminalData.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder data.terminalData.terminal.2)
              kappaB.1 data.paperOutgoingTerminal.terminalContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminalData.terminal.2)
                data.paperOutgoingTerminal.terminalContext.one_le_blockOrder
                first (first - gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam eps : ℂ) ^
          (2 * (R324WithinHalfResidualPrefix.initial
            rho lam eps pairing).remainingOrder) *
        (∫ q : U × (T4 ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate → T4)),
          charT4 outgoingMode q.2.1 *
            (R324WithinHalfResidualPrefix.initial rho lam eps pairing
              |>.incomingPhasedResidualDensity
                (coefficient q.1
                  ((data.transport.stop.splitSurvivingPiMeasurableEquiv
                      data.terminalData.terminal []
                      data.stop_remaining_eq_singleton
                      (data.transport.projection q.2.2)).2))
                incomingMode rho eps (x q.1) q.2.1 q.2.2)
          ∂(muU.prod (paperMeasure.prod
            (Measure.pi fun _ => paperMeasure)))) =
      ∫ u : U,
        ∫ v : data.paperOutgoingTerminal.terminalPost.SurvivingCoordinate → T4,
          ∫ first : T4,
            data.outgoingEndpointDefectDensity
              (coefficient u) incomingMode outgoingMode (x u) v first
            ∂paperMeasure
          ∂Measure.pi fun _ => paperMeasure
        ∂muU := by
  let initial := R324WithinHalfResidualPrefix.initial rho lam eps pairing
  let muInitial := Measure.pi fun _ : initial.SurvivingCoordinate => paperMeasure
  have hphaseMeas : Measurable
      (fun q : U × (T4 × (initial.SurvivingCoordinate → T4)) =>
        charT4 outgoingMode q.2.1) :=
    (continuous_charT4 outgoingMode).measurable.comp
      (measurable_fst.comp measurable_snd)
  have hcurrentPhase :
      Integrable
        (fun q : U × (T4 × (initial.SurvivingCoordinate → T4)) =>
          charT4 outgoingMode q.2.1 *
            initial.incomingPhasedResidualDensity
              (coefficient q.1
                ((data.transport.stop.splitSurvivingPiMeasurableEquiv
                  data.terminalData.terminal []
                  data.stop_remaining_eq_singleton
                  (data.transport.projection q.2.2)).2))
              incomingMode rho eps (x q.1) q.2.1 q.2.2)
        (muU.prod (paperMeasure.prod muInitial)) :=
    hcurrent.bdd_mul hphaseMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by rw [norm_charT4])
  rw [integral_prod _ hcurrentPhase, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hcurrent.prod_right_ae, hstop.prod_right_ae]
      with u hcurrentU hstopU
  have hsection :=
    data.lamEps_pow_integral_initial_outgoingEndpoint_eq_defect
      hpred hactive (coefficient u) incomingMode outgoingMode (x u)
      hcurrentU hstopU hint
  simpa only [outgoingEndpointDefectDensity,
    incomingExceptionalPrimitiveDefect] using hsection

end R324WithinHalfEndpointTerminalGeometry
end R324WithinHalfResidualPrefix

/-! ## Exact root regrouping for a direct outgoing endpoint -/

/-- Exact, signed version of the outgoing-endpoint regroup used in paper
Step 4(A).  The free outgoing variable is moved next to the completed half,
its Green leg is Fourier-integrated, and the untouched opposite half and
cross-covariance factor stay inside the outer integral.  In particular,
there is no triangle inequality in this statement. -/
theorem integral_rootProd_incomingPhasedResidualDensity_eq_directOutgoing
    {rho : SmoothCutoff} {lam eps : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (hnil : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (hedge :
      res.state.edges (res.terminalOutgoingEdgeSlot hactive) = greenFn)
    {ZW VR : Type*} [MeasurableSpace ZW] [MeasurableSpace VR]
    (muZW : Measure ZW) (muVR : Measure VR)
    [SFinite muZW] [SFinite muVR]
    (red : ZW → VR → (res.SurvivingCoordinate → T4) → ℂ)
    (beta k : Z4)
    (hjoint :
      Integrable
        (fun q :
            ((T4 × ZW) × VR) ×
              (res.SurvivingCoordinate → T4) =>
          res.incomingPhasedResidualDensity
            (charT4 beta q.1.1.1 * red q.1.1.2 q.1.2 q.2)
            k rho eps 0 q.1.1.1 q.2)
        (((paperMeasure.prod muZW).prod muVR).prod
          (Measure.pi fun _ => paperMeasure))) :
    (∫ q :
        ((T4 × ZW) × VR) ×
          (res.SurvivingCoordinate → T4),
        res.incomingPhasedResidualDensity
          (charT4 beta q.1.1.1 * red q.1.1.2 q.1.2 q.2)
          k rho eps 0 q.1.1.1 q.2
        ∂(((paperMeasure.prod muZW).prod muVR).prod
          (Measure.pi fun _ => paperMeasure))) =
      ∫ s : ZW × VR,
        ∫ u : res.SurvivingCoordinate → T4,
          red s.1 s.2 u *
            charT4 k
              (res.terminalIncomingAnchor (res.reconstruct u)) *
            ((res.endpointErasedSignedChain hactive 0 0
              (res.reconstruct u) : ℝ) : ℂ) *
            translatedGreenMode beta
              (res.terminalOutgoingAnchor hactive
                (res.reconstruct u))
          ∂Measure.pi fun _ => paperMeasure
        ∂(muZW.prod muVR) := by
  let muU :=
    Measure.pi fun _ : res.SurvivingCoordinate => paperMeasure
  let F :
      (((T4 × ZW) × VR) ×
        (res.SurvivingCoordinate → T4)) → ℂ :=
    fun q =>
      res.incomingPhasedResidualDensity
        (charT4 beta q.1.1.1 * red q.1.1.2 q.1.2 q.2)
        k rho eps 0 q.1.1.1 q.2
  let sigma :=
    r324DriverTerminalRegroupMeasurableEquiv
      T4 ZW VR (res.SurvivingCoordinate → T4)
  have hsigma :
      MeasurePreserving sigma
        (((paperMeasure.prod muZW).prod muVR).prod muU)
        ((muZW.prod muVR).prod (paperMeasure.prod muU)) :=
    measurePreserving_r324DriverTerminalRegroupMeasurableEquiv
      paperMeasure muZW muVR muU
  let G :
      ((ZW × VR) ×
        (T4 × (res.SurvivingCoordinate → T4))) → ℂ :=
    fun p => F (sigma.symm p)
  have hGF : ∀ q, G (sigma q) = F q := by
    intro q
    show F (sigma.symm (sigma q)) = F q
    rw [MeasurableEquiv.symm_apply_apply]
  have hGint :
      Integrable G
        ((muZW.prod muVR).prod (paperMeasure.prod muU)) := by
    refine (hsigma.integrable_comp_emb sigma.measurableEmbedding).mp ?_
    apply hjoint.congr
    filter_upwards with q
    exact (hGF q).symm
  have hintegral :
      (∫ q, F q
          ∂(((paperMeasure.prod muZW).prod muVR).prod muU)) =
        ∫ p, G p
          ∂((muZW.prod muVR).prod (paperMeasure.prod muU)) := by
    rw [← hsigma.integral_comp' G]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun q => (hGF q).symm)
  have hGs :
      ∀ (s : ZW × VR)
        (yu : T4 × (res.SurvivingCoordinate → T4)),
        G (s, yu) =
          res.incomingPhasedResidualDensity
            (charT4 beta yu.1 * red s.1 s.2 yu.2)
            k rho eps 0 yu.1 yu.2 := by
    intro s yu
    rfl
  have hyeval :
      ∀ (s : ZW × VR)
        (u : res.SurvivingCoordinate → T4),
        (∫ y, G (s, (y, u)) ∂paperMeasure) =
          red s.1 s.2 u *
            charT4 k
              (res.terminalIncomingAnchor (res.reconstruct u)) *
            ((res.endpointErasedSignedChain hactive 0 0
              (res.reconstruct u) : ℝ) : ℂ) *
            translatedGreenMode beta
              (res.terminalOutgoingAnchor hactive
                (res.reconstruct u)) := by
    intro s u
    calc
      (∫ y, G (s, (y, u)) ∂paperMeasure) =
          ∫ y,
            charT4 beta y *
              res.incomingPhasedResidualDensity
                (red s.1 s.2 u) k rho eps 0 y u
            ∂paperMeasure := by
        apply integral_congr_ae
        filter_upwards with y
        rw [hGs s (y, u)]
        exact
          res.incomingPhasedResidualDensity_const_mul
            (charT4 beta y) (red s.1 s.2 u)
            k rho eps 0 y u
      _ = _ :=
        res.integral_char_mul_terminal_incomingPhasedResidualDensity_eq
          hnil hactive hedge (red s.1 s.2 u)
          k beta rho eps 0 u
  change (∫ q, F q
      ∂(((paperMeasure.prod muZW).prod muVR).prod muU)) = _
  rw [hintegral, integral_prod _ hGint]
  apply integral_congr_ae
  filter_upwards [hGint.prod_right_ae] with s hs
  rw [integral_prod_symm _ hs]
  apply integral_congr_ae
  filter_upwards with u
  exact hyeval s u

/-! The same terminal regrouping with one arbitrary untouched carrier. -/

/-- Move the outgoing endpoint next to the terminal coordinates while
leaving one arbitrary parameter carrier outside. -/
def r324SingleParameterTerminalRegroupMeasurableEquiv
    (Y U V : Type*) [MeasurableSpace Y] [MeasurableSpace U]
    [MeasurableSpace V] :
    ((Y × U) × V) ≃ᵐ U × (Y × V) :=
  (MeasurableEquiv.prodAssoc
    (α := Y) (β := U) (γ := V)).trans
      (r324IncomingExceptionalHeadPullMeasurableEquiv Y U V)

@[simp]
theorem r324SingleParameterTerminalRegroupMeasurableEquiv_apply
    {Y U V : Type*} [MeasurableSpace Y] [MeasurableSpace U]
    [MeasurableSpace V] (q : (Y × U) × V) :
    r324SingleParameterTerminalRegroupMeasurableEquiv Y U V q =
      (q.1.2, q.1.1, q.2) :=
  rfl

@[simp]
theorem r324SingleParameterTerminalRegroupMeasurableEquiv_symm_apply
    {Y U V : Type*} [MeasurableSpace Y] [MeasurableSpace U]
    [MeasurableSpace V] (q : U × (Y × V)) :
    (r324SingleParameterTerminalRegroupMeasurableEquiv Y U V).symm q =
      ((q.2.1, q.1), q.2.2) :=
  rfl

/-- The one-parameter terminal regroup preserves product measure. -/
theorem measurePreserving_r324SingleParameterTerminalRegroupMeasurableEquiv
    {Y U V : Type*} [MeasurableSpace Y] [MeasurableSpace U]
    [MeasurableSpace V]
    (muY : Measure Y) (muU : Measure U) (muV : Measure V)
    [SFinite muY] [SFinite muU] [SFinite muV] :
    MeasurePreserving
      (r324SingleParameterTerminalRegroupMeasurableEquiv Y U V)
      ((muY.prod muU).prod muV)
      (muU.prod (muY.prod muV)) :=
  (measurePreserving_r324IncomingExceptionalHeadPullMeasurableEquiv
      muY muU muV).comp
    (measurePreserving_prodAssoc muY muU muV)

namespace R324WithinHalfResidualPrefix
namespace R324PaperOutgoingEndpointTerminal

/-- Parameterized joint stop-carrier form of the retained outgoing operation.
The untouched carrier is placed outside only after the signed endpoint
integrand has been formed.  This is the exact Fubini seam needed when the
opposite half has already been collapsed by the exceptional incoming
operation. -/
theorem lamEps_pow_integral_singleParameter_stop_outgoingEndpoint_eq_defect
    {rho : SmoothCutoff} {lam eps : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    (data : R324PaperOutgoingEndpointTerminal res)
    (hpred :
      r324WithinHalfPredecessorSlot data.endpoint.stop.state
          data.terminalData.terminal ≠ 0)
    (hactive : data.terminalPost.state.active.Nonempty)
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U) [SFinite muU]
    (coefficient : U →
      (data.terminalPost.SurvivingCoordinate → T4) → ℂ)
    (incomingMode outgoingMode : Z4) (x : U → T4)
    (hsource :
      Integrable
        (fun q : (T4 × U) ×
              (data.endpoint.stop.SurvivingCoordinate → T4) =>
          data.endpoint.stop.incomingPhasedResidualDensity
            (coefficient q.1.2
              ((data.endpoint.stop.splitSurvivingPiMeasurableEquiv
                data.terminalData.terminal [] data.endpoint.stop_remaining
                q.2).2))
            incomingMode rho eps (x q.1.2) q.1.1 q.2)
        ((paperMeasure.prod muU).prod
          (Measure.pi fun _ => paperMeasure)))
    (hint :
      ∀ (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminalData.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder data.terminalData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder
              data.terminalData.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder data.terminalData.terminal.2)
              kappaB.1 data.terminalContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder
                first (first - gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam eps : ℂ) ^ (2 * data.endpoint.stop.remainingOrder) *
        (∫ q : (T4 × U) ×
              (data.endpoint.stop.SurvivingCoordinate → T4),
          charT4 outgoingMode q.1.1 *
            data.endpoint.stop.incomingPhasedResidualDensity
              (coefficient q.1.2
                ((data.endpoint.stop.splitSurvivingPiMeasurableEquiv
                  data.terminalData.terminal [] data.endpoint.stop_remaining
                  q.2).2))
              incomingMode rho eps (x q.1.2) q.1.1 q.2
          ∂((paperMeasure.prod muU).prod
            (Measure.pi fun _ => paperMeasure))) =
      ∫ u : U,
        ∫ v : data.terminalPost.SurvivingCoordinate → T4,
          ∫ first : T4,
            data.outgoingEndpointDefectDensity
              (coefficient u) incomingMode outgoingMode (x u) v first
            ∂paperMeasure
          ∂Measure.pi fun _ => paperMeasure
        ∂muU := by
  let muStop :=
    Measure.pi fun _ : data.endpoint.stop.SurvivingCoordinate => paperMeasure
  let sigma :=
    r324SingleParameterTerminalRegroupMeasurableEquiv
      T4 U (data.endpoint.stop.SurvivingCoordinate → T4)
  have hsigma :
      MeasurePreserving sigma
        ((paperMeasure.prod muU).prod muStop)
        (muU.prod (paperMeasure.prod muStop)) :=
    measurePreserving_r324SingleParameterTerminalRegroupMeasurableEquiv
      paperMeasure muU muStop
  let F :
      ((T4 × U) ×
        (data.endpoint.stop.SurvivingCoordinate → T4)) → ℂ :=
    fun q =>
      data.endpoint.stop.incomingPhasedResidualDensity
        (coefficient q.1.2
          ((data.endpoint.stop.splitSurvivingPiMeasurableEquiv
            data.terminalData.terminal [] data.endpoint.stop_remaining
            q.2).2))
        incomingMode rho eps (x q.1.2) q.1.1 q.2
  let Fphase :
      ((T4 × U) ×
        (data.endpoint.stop.SurvivingCoordinate → T4)) → ℂ :=
    fun q => charT4 outgoingMode q.1.1 * F q
  have hphaseMeas : Measurable
      (fun q : (T4 × U) ×
          (data.endpoint.stop.SurvivingCoordinate → T4) =>
        charT4 outgoingMode q.1.1) :=
    (continuous_charT4 outgoingMode).measurable.comp
      (measurable_fst.comp measurable_fst)
  have hphase : Integrable Fphase
      ((paperMeasure.prod muU).prod muStop) := by
    exact hsource.bdd_mul hphaseMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by rw [norm_charT4])
  let G : U ×
      (T4 × (data.endpoint.stop.SurvivingCoordinate → T4)) → ℂ :=
    fun p => Fphase (sigma.symm p)
  let H : U ×
      (T4 × (data.endpoint.stop.SurvivingCoordinate → T4)) → ℂ :=
    fun p => F (sigma.symm p)
  have hGint : Integrable G (muU.prod (paperMeasure.prod muStop)) := by
    refine (hsigma.integrable_comp_emb sigma.measurableEmbedding).mp ?_
    apply hphase.congr
    filter_upwards with q
    show Fphase q = G (sigma q)
    unfold G
    rw [MeasurableEquiv.symm_apply_apply]
  have hHint : Integrable H (muU.prod (paperMeasure.prod muStop)) := by
    refine (hsigma.integrable_comp_emb sigma.measurableEmbedding).mp ?_
    apply hsource.congr
    filter_upwards with q
    show F q = H (sigma q)
    unfold H
    rw [MeasurableEquiv.symm_apply_apply]
  have hintegral :
      (∫ q, Fphase q ∂((paperMeasure.prod muU).prod muStop)) =
        ∫ p, G p ∂(muU.prod (paperMeasure.prod muStop)) := by
    rw [← hsigma.integral_comp' G]
    apply integral_congr_ae
    filter_upwards with q
    show Fphase q = G (sigma q)
    unfold G
    rw [MeasurableEquiv.symm_apply_apply]
  change (lamEps lam eps : ℂ) ^
      (2 * data.endpoint.stop.remainingOrder) *
        (∫ q, Fphase q ∂((paperMeasure.prod muU).prod muStop)) = _
  rw [hintegral, integral_prod _ hGint, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hGint.prod_right_ae, hHint.prod_right_ae]
      with u hGu hHu
  have hsection :=
    data.lamEps_pow_integral_stop_outgoingEndpoint_eq_defect
      hpred hactive (coefficient u) incomingMode outgoingMode (x u)
      hHu hint
  simpa only [G, H, Fphase, F, sigma,
    r324SingleParameterTerminalRegroupMeasurableEquiv_symm_apply] using hsection

/-- Certificate-ready bound for the generic retained outgoing defect.
The exact ordinary primitive phase defect has already been formed, so this
is the first point where its norm is taken. -/
theorem norm_outgoingEndpointDefectDensity_le_scaled_of_certificate
    {rho : SmoothCutoff} {lam eps : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    (data : R324PaperOutgoingEndpointTerminal res)
    (scale : Fin (m + 1) → ℝ)
    (hcertificate :
      R324WithinHalfEdgeCertificate data.terminalContext.state scale)
    (coefficient :
      (data.terminalPost.SurvivingCoordinate → T4) → ℂ)
    (incomingMode outgoingMode : Z4) (x : T4)
    (v : data.terminalPost.SurvivingCoordinate → T4)
    (first : T4)
    {primitiveConstant supportConstant : ℝ}
    (heps : 0 < eps) (hprimitive : 0 ≤ primitiveConstant)
    (hlam : 0 ≤ lam)
    (hprop :
      ∀ (H : Fin (2 * residualBlockOrder
            data.terminalData.terminal.2 - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput
            (residualBlockOrder data.terminalData.terminal.2) H →
          MemEClassT4
              (primitiveKernelDiff rho lam eps
                (residualBlockOrder data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff rho lam eps
                (residualBlockOrder data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder H) ∧
            PrimitiveKernelBounds rho lam eps
              (residualBlockOrder data.terminalData.terminal.2)
              data.terminalContext.one_le_blockOrder H
              supportConstant primitiveConstant) :
    ‖data.outgoingEndpointDefectDensity coefficient
        incomingMode outgoingMode x v first‖ ≤
      |data.terminalContext.state.edges
          (r324WithinHalfPredecessorSlot
            data.terminalContext.state data.terminalContext.step)
          (data.terminalPredecessorPoint x v - first)| *
        paperSecondOrderModeDecay outgoingMode *
        (2 * r324WithinHalfInternalEdgeScaleProduct
            data.terminalContext scale *
          ∫ gap : T4,
            primitiveKernelMajorant primitiveConstant lam eps
              supportConstant
              (residualBlockOrder data.terminalData.terminal.2) gap
            ∂paperMeasure) *
        ‖data.terminalSplitOuter coefficient incomingMode x v‖ := by
  have hdefect :=
    norm_incomingExceptionalPrimitiveDefect_le_scaled_of_certificate
      data.terminalContext scale hcertificate heps hprimitive hlam
      hprop outgoingMode
  unfold outgoingEndpointDefectDensity
  rw [norm_mul, norm_mul, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperSecondOrderModeDecay_nonneg outgoingMode),
    norm_charT4, mul_one]
  exact
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdefect
        (mul_nonneg (abs_nonneg _)
          (paperSecondOrderModeDecay_nonneg outgoingMode)))
      (norm_nonneg _)

/-- Integrating the remaining predecessor endpoint preserves the outgoing
Fourier decay and costs exactly the `L¹` mass of that certified named edge.
The triangle inequality is used only after the complete signed terminal
defect has been formed. -/
theorem norm_integral_outgoingEndpointDefectDensity_le_scaled_of_certificate
    {rho : SmoothCutoff} {lam eps : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    (data : R324PaperOutgoingEndpointTerminal res)
    (scale : Fin (m + 1) → ℝ)
    (hcertificate :
      R324WithinHalfEdgeCertificate data.terminalContext.state scale)
    (coefficient :
      (data.terminalPost.SurvivingCoordinate → T4) → ℂ)
    (incomingMode outgoingMode : Z4) (x : T4)
    (v : data.terminalPost.SurvivingCoordinate → T4)
    {primitiveConstant supportConstant : ℝ}
    (heps : 0 < eps) (hprimitive : 0 ≤ primitiveConstant)
    (hlam : 0 ≤ lam)
    (hprop :
      ∀ (H : Fin (2 * residualBlockOrder
            data.terminalData.terminal.2 - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput
            (residualBlockOrder data.terminalData.terminal.2) H →
          MemEClassT4
              (primitiveKernelDiff rho lam eps
                (residualBlockOrder data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff rho lam eps
                (residualBlockOrder data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder H) ∧
            PrimitiveKernelBounds rho lam eps
              (residualBlockOrder data.terminalData.terminal.2)
              data.terminalContext.one_le_blockOrder H
              supportConstant primitiveConstant) :
    ‖∫ first : T4,
        data.outgoingEndpointDefectDensity coefficient
          incomingMode outgoingMode x v first
        ∂paperMeasure‖ ≤
      (scale
          (r324WithinHalfPredecessorSlot
            data.terminalContext.state data.terminalContext.step) *
          invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode *
        (2 * r324WithinHalfInternalEdgeScaleProduct
            data.terminalContext scale *
          ∫ gap : T4,
            primitiveKernelMajorant primitiveConstant lam eps
              supportConstant
              (residualBlockOrder data.terminalData.terminal.2) gap
            ∂paperMeasure) *
        ‖data.terminalSplitOuter coefficient incomingMode x v‖ := by
  let predecessor :=
    r324WithinHalfPredecessorSlot
      data.terminalContext.state data.terminalContext.step
  let anchor := data.terminalPredecessorPoint x v
  let endpointIntegral : ℂ :=
    ∫ first : T4,
      charT4 outgoingMode first *
        (data.terminalContext.state.edges predecessor
          (anchor - first) : ℂ)
      ∂paperMeasure
  let terminalConstant : ℂ :=
    (paperSecondOrderModeDecay outgoingMode : ℂ) *
      incomingExceptionalPrimitiveDefect rho lam eps
        (residualBlockOrder data.terminalData.terminal.2)
        data.terminalContext.one_le_blockOrder
        data.terminalContext.internalEdges outgoingMode *
      data.terminalSplitOuter coefficient incomingMode x v
  have hfactor :
      (∫ first : T4,
          data.outgoingEndpointDefectDensity coefficient
            incomingMode outgoingMode x v first
          ∂paperMeasure) = endpointIntegral * terminalConstant := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with first
    unfold outgoingEndpointDefectDensity
    dsimp only [endpointIntegral, terminalConstant, predecessor, anchor]
    ring
  have hendpoint :
      ‖endpointIntegral‖ ≤ scale predecessor * invSqKerMass := by
    exact hcertificate.norm_integral_char_mul_edge_sub_left_le
      predecessor outgoingMode anchor
  have hdefect :=
    norm_incomingExceptionalPrimitiveDefect_le_scaled_of_certificate
      data.terminalContext scale hcertificate heps hprimitive hlam
      hprop outgoingMode
  rw [hfactor, norm_mul]
  dsimp only [terminalConstant]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperSecondOrderModeDecay_nonneg outgoingMode)]
  have hscaleMass : 0 ≤ scale predecessor * invSqKerMass :=
    mul_nonneg (hcertificate.scale_pos predecessor).le
      invSqKerMass_nonneg
  have hdecay : 0 ≤ paperSecondOrderModeDecay outgoingMode :=
    paperSecondOrderModeDecay_nonneg outgoingMode
  have hmajorant :
      0 ≤
        2 * r324WithinHalfInternalEdgeScaleProduct
            data.terminalContext scale *
          ∫ gap : T4,
            primitiveKernelMajorant primitiveConstant lam eps
              supportConstant
              (residualBlockOrder data.terminalData.terminal.2) gap
            ∂paperMeasure :=
    le_trans (norm_nonneg _) hdefect
  calc
    ‖endpointIntegral‖ *
          (paperSecondOrderModeDecay outgoingMode *
            ‖incomingExceptionalPrimitiveDefect rho lam eps
              (residualBlockOrder data.terminalData.terminal.2)
              data.terminalContext.one_le_blockOrder
              data.terminalContext.internalEdges outgoingMode‖ *
            ‖data.terminalSplitOuter coefficient incomingMode x v‖) =
        (‖endpointIntegral‖ *
            paperSecondOrderModeDecay outgoingMode *
            ‖incomingExceptionalPrimitiveDefect rho lam eps
              (residualBlockOrder data.terminalData.terminal.2)
              data.terminalContext.one_le_blockOrder
              data.terminalContext.internalEdges outgoingMode‖) *
          ‖data.terminalSplitOuter coefficient incomingMode x v‖ := by
      ring
    _ ≤
        ((scale predecessor * invSqKerMass) *
            paperSecondOrderModeDecay outgoingMode *
            (2 * r324WithinHalfInternalEdgeScaleProduct
                data.terminalContext scale *
              ∫ gap : T4,
                primitiveKernelMajorant primitiveConstant lam eps
                  supportConstant
                  (residualBlockOrder data.terminalData.terminal.2) gap
                ∂paperMeasure)) *
          ‖data.terminalSplitOuter coefficient incomingMode x v‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc
        ‖endpointIntegral‖ *
              paperSecondOrderModeDecay outgoingMode *
              ‖incomingExceptionalPrimitiveDefect rho lam eps
                (residualBlockOrder data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder
                data.terminalContext.internalEdges outgoingMode‖ ≤
            ((scale predecessor * invSqKerMass) *
                paperSecondOrderModeDecay outgoingMode) *
              ‖incomingExceptionalPrimitiveDefect rho lam eps
                (residualBlockOrder data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder
                data.terminalContext.internalEdges outgoingMode‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hendpoint hdecay)
            (norm_nonneg _)
        _ ≤
            ((scale predecessor * invSqKerMass) *
                paperSecondOrderModeDecay outgoingMode) *
              (2 * r324WithinHalfInternalEdgeScaleProduct
                  data.terminalContext scale *
                ∫ gap : T4,
                  primitiveKernelMajorant primitiveConstant lam eps
                    supportConstant
                    (residualBlockOrder data.terminalData.terminal.2) gap
                  ∂paperMeasure) :=
          mul_le_mul_of_nonneg_left hdefect
            (mul_nonneg hscaleMass hdecay)
    _ = _ := by
      dsimp only [predecessor]

/-- The same completed terminal estimate in the budget's inserted-kernel
currency.  Exactly one exceptional endpoint sacrifice is introduced; no
cost is charged to the direct incoming endpoint carried by `coefficient`. -/
theorem norm_integral_outgoingEndpointDefectDensity_le_inserted_of_certificate
    {rho : SmoothCutoff} {lam eps : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    (data : R324PaperOutgoingEndpointTerminal res)
    (scale : Fin (m + 1) → ℝ)
    (hcertificate :
      R324WithinHalfEdgeCertificate data.terminalContext.state scale)
    (coefficient :
      (data.terminalPost.SurvivingCoordinate → T4) → ℂ)
    (incomingMode outgoingMode : Z4) (x : T4)
    (v : data.terminalPost.SurvivingCoordinate → T4)
    {primitiveConstant supportConstant : ℝ}
    (heps : 0 < eps) (hprimitive : 0 ≤ primitiveConstant)
    (hlam : 0 ≤ lam)
    (hprop :
      ∀ (H : Fin (2 * residualBlockOrder
            data.terminalData.terminal.2 - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput
            (residualBlockOrder data.terminalData.terminal.2) H →
          MemEClassT4
              (primitiveKernelDiff rho lam eps
                (residualBlockOrder data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff rho lam eps
                (residualBlockOrder data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder H) ∧
            PrimitiveKernelBounds rho lam eps
              (residualBlockOrder data.terminalData.terminal.2)
              data.terminalContext.one_le_blockOrder H
              supportConstant primitiveConstant) :
    ‖∫ first : T4,
        data.outgoingEndpointDefectDensity coefficient
          incomingMode outgoingMode x v first
        ∂paperMeasure‖ ≤
      (scale
          (r324WithinHalfPredecessorSlot
            data.terminalContext.state data.terminalContext.step) *
          invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode *
        (2 * r324WithinHalfInternalEdgeScaleProduct
            data.terminalContext scale *
          (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
            ∫ gap : T4,
              primitiveInsertedMajorant primitiveConstant lam eps
                supportConstant
                (residualBlockOrder data.terminalData.terminal.2) gap
              ∂paperMeasure)) *
        ‖data.terminalSplitOuter coefficient incomingMode x v‖ := by
  refine
    (data.norm_integral_outgoingEndpointDefectDensity_le_scaled_of_certificate
      scale hcertificate coefficient incomingMode outgoingMode x v
      heps hprimitive hlam hprop).trans ?_
  have hbridge :=
    integral_primitiveKernelMajorant_le_endpointSacrifice_mul_inserted
      primitiveConstant lam supportConstant
      (residualBlockOrder data.terminalData.terminal.2) heps
  have hfront :
      0 ≤
        scale
            (r324WithinHalfPredecessorSlot
              data.terminalContext.state data.terminalContext.step) *
          invSqKerMass *
        paperSecondOrderModeDecay outgoingMode :=
    mul_nonneg
      (mul_nonneg
        (hcertificate.scale_pos _).le invSqKerMass_nonneg)
      (paperSecondOrderModeDecay_nonneg outgoingMode)
  have hinternal :
      0 ≤
        2 * r324WithinHalfInternalEdgeScaleProduct
          data.terminalContext scale :=
    mul_nonneg (by positivity)
      hcertificate.internalEdgeScaleProduct_pos.le
  gcongr

end R324PaperOutgoingEndpointTerminal
end R324WithinHalfResidualPrefix

/-- One-parameter form of the exact direct-outgoing Fourier regroup.  This
is the form used when the untouched parameter is the already-completed
opposite half. -/
theorem integral_singleParameter_incomingPhasedResidualDensity_eq_directOutgoing
    {rho : SmoothCutoff} {lam eps : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (hnil : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (hedge :
      res.state.edges (res.terminalOutgoingEdgeSlot hactive) = greenFn)
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U) [SFinite muU]
    (red : U → (res.SurvivingCoordinate → T4) → ℂ)
    (beta k : Z4)
    (hjoint :
      Integrable
        (fun q : (T4 × U) ×
              (res.SurvivingCoordinate → T4) =>
          res.incomingPhasedResidualDensity
            (charT4 beta q.1.1 * red q.1.2 q.2)
            k rho eps 0 q.1.1 q.2)
        ((paperMeasure.prod muU).prod
          (Measure.pi fun _ => paperMeasure))) :
    (∫ q : (T4 × U) ×
          (res.SurvivingCoordinate → T4),
        res.incomingPhasedResidualDensity
          (charT4 beta q.1.1 * red q.1.2 q.2)
          k rho eps 0 q.1.1 q.2
        ∂((paperMeasure.prod muU).prod
          (Measure.pi fun _ => paperMeasure))) =
      ∫ s : U,
        ∫ u : res.SurvivingCoordinate → T4,
          red s u *
            charT4 k
              (res.terminalIncomingAnchor (res.reconstruct u)) *
            ((res.endpointErasedSignedChain hactive 0 0
              (res.reconstruct u) : ℝ) : ℂ) *
            translatedGreenMode beta
              (res.terminalOutgoingAnchor hactive
                (res.reconstruct u))
          ∂Measure.pi fun _ => paperMeasure
        ∂muU := by
  let muV :=
    Measure.pi fun _ : res.SurvivingCoordinate => paperMeasure
  let F :
      ((T4 × U) ×
        (res.SurvivingCoordinate → T4)) → ℂ :=
    fun q =>
      res.incomingPhasedResidualDensity
        (charT4 beta q.1.1 * red q.1.2 q.2)
        k rho eps 0 q.1.1 q.2
  let sigma :=
    r324SingleParameterTerminalRegroupMeasurableEquiv
      T4 U (res.SurvivingCoordinate → T4)
  have hsigma :
      MeasurePreserving sigma
        ((paperMeasure.prod muU).prod muV)
        (muU.prod (paperMeasure.prod muV)) :=
    measurePreserving_r324SingleParameterTerminalRegroupMeasurableEquiv
      paperMeasure muU muV
  let G :
      U × (T4 × (res.SurvivingCoordinate → T4)) → ℂ :=
    fun p => F (sigma.symm p)
  have hGF : ∀ q, G (sigma q) = F q := by
    intro q
    show F (sigma.symm (sigma q)) = F q
    rw [MeasurableEquiv.symm_apply_apply]
  have hGint :
      Integrable G (muU.prod (paperMeasure.prod muV)) := by
    refine (hsigma.integrable_comp_emb sigma.measurableEmbedding).mp ?_
    apply hjoint.congr
    filter_upwards with q
    exact (hGF q).symm
  have hintegral :
      (∫ q, F q ∂((paperMeasure.prod muU).prod muV)) =
        ∫ p, G p ∂(muU.prod (paperMeasure.prod muV)) := by
    rw [← hsigma.integral_comp' G]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun q => (hGF q).symm)
  have hGs :
      ∀ (s : U)
        (yu : T4 × (res.SurvivingCoordinate → T4)),
        G (s, yu) =
          res.incomingPhasedResidualDensity
            (charT4 beta yu.1 * red s yu.2)
            k rho eps 0 yu.1 yu.2 := by
    intro s yu
    rfl
  have hyeval :
      ∀ (s : U) (u : res.SurvivingCoordinate → T4),
        (∫ y, G (s, (y, u)) ∂paperMeasure) =
          red s u *
            charT4 k
              (res.terminalIncomingAnchor (res.reconstruct u)) *
            ((res.endpointErasedSignedChain hactive 0 0
              (res.reconstruct u) : ℝ) : ℂ) *
            translatedGreenMode beta
              (res.terminalOutgoingAnchor hactive
                (res.reconstruct u)) := by
    intro s u
    calc
      (∫ y, G (s, (y, u)) ∂paperMeasure) =
          ∫ y,
            charT4 beta y *
              res.incomingPhasedResidualDensity
                (red s u) k rho eps 0 y u
            ∂paperMeasure := by
        apply integral_congr_ae
        filter_upwards with y
        rw [hGs s (y, u)]
        exact
          res.incomingPhasedResidualDensity_const_mul
            (charT4 beta y) (red s u)
            k rho eps 0 y u
      _ = _ :=
        res.integral_char_mul_terminal_incomingPhasedResidualDensity_eq
          hnil hactive hedge (red s u) k beta rho eps 0 u
  change (∫ q, F q ∂((paperMeasure.prod muU).prod muV)) = _
  rw [hintegral, integral_prod _ hGint]
  apply integral_congr_ae
  filter_upwards [hGint.prod_right_ae] with s hs
  rw [integral_prod_symm _ hs]
  apply integral_congr_ae
  filter_upwards with u
  exact hyeval s u

/-- Joint integrability survives the exact direct-outgoing Fourier
evaluation.  This is the Fubini license needed to hand a completed first
half to the second half; it is derived from the same pre-Fourier joint
integrability, not assumed independently. -/
theorem integrable_singleParameter_directOutgoingResult
    {rho : SmoothCutoff} {lam eps : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (hnil : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (hedge :
      res.state.edges (res.terminalOutgoingEdgeSlot hactive) = greenFn)
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U) [SFinite muU]
    (red : U → (res.SurvivingCoordinate → T4) → ℂ)
    (beta k : Z4)
    (hjoint :
      Integrable
        (fun q : (T4 × U) ×
              (res.SurvivingCoordinate → T4) =>
          res.incomingPhasedResidualDensity
            (charT4 beta q.1.1 * red q.1.2 q.2)
            k rho eps 0 q.1.1 q.2)
        ((paperMeasure.prod muU).prod
          (Measure.pi fun _ => paperMeasure))) :
    Integrable
      (fun q : U × (res.SurvivingCoordinate → T4) =>
        red q.1 q.2 *
          charT4 k
            (res.terminalIncomingAnchor (res.reconstruct q.2)) *
          ((res.endpointErasedSignedChain hactive 0 0
            (res.reconstruct q.2) : ℝ) : ℂ) *
          translatedGreenMode beta
            (res.terminalOutgoingAnchor hactive
              (res.reconstruct q.2)))
      (muU.prod (Measure.pi fun _ => paperMeasure)) := by
  let muV :=
    Measure.pi fun _ : res.SurvivingCoordinate => paperMeasure
  let F :
      ((T4 × U) ×
        (res.SurvivingCoordinate → T4)) → ℂ :=
    fun q =>
      res.incomingPhasedResidualDensity
        (charT4 beta q.1.1 * red q.1.2 q.2)
        k rho eps 0 q.1.1 q.2
  let sigma :=
    r324SingleParameterTerminalRegroupMeasurableEquiv
      T4 U (res.SurvivingCoordinate → T4)
  have hsigma :
      MeasurePreserving sigma
        ((paperMeasure.prod muU).prod muV)
        (muU.prod (paperMeasure.prod muV)) :=
    measurePreserving_r324SingleParameterTerminalRegroupMeasurableEquiv
      paperMeasure muU muV
  let G : U × (T4 × (res.SurvivingCoordinate → T4)) → ℂ :=
    fun p => F (sigma.symm p)
  have hGint :
      Integrable G (muU.prod (paperMeasure.prod muV)) := by
    refine (hsigma.integrable_comp_emb sigma.measurableEmbedding).mp ?_
    apply hjoint.congr
    filter_upwards with q
    show F q = G (sigma q)
    unfold G
    rw [MeasurableEquiv.symm_apply_apply]
  let tau :=
    r324MoveMiddleMeasurableEquiv
      U T4 (res.SurvivingCoordinate → T4)
  have htau :
      MeasurePreserving tau
        (muU.prod (paperMeasure.prod muV))
        (paperMeasure.prod (muU.prod muV)) :=
    measurePreserving_r324MoveMiddleMeasurableEquiv
      muU paperMeasure muV
  let H : T4 × (U × (res.SurvivingCoordinate → T4)) → ℂ :=
    fun p => G (tau.symm p)
  have hHint :
      Integrable H (paperMeasure.prod (muU.prod muV)) := by
    refine (htau.integrable_comp_emb tau.measurableEmbedding).mp ?_
    apply hGint.congr
    filter_upwards with q
    show G q = H (tau q)
    unfold H
    rw [MeasurableEquiv.symm_apply_apply]
  have hmarg :
      Integrable
        (fun q : U × (res.SurvivingCoordinate → T4) =>
          ∫ y : T4, H (y, q) ∂paperMeasure)
        (muU.prod muV) :=
    hHint.integral_prod_right
  apply hmarg.congr
  filter_upwards with q
  change
    (∫ y : T4,
      res.incomingPhasedResidualDensity
        (charT4 beta y * red q.1 q.2)
        k rho eps 0 y q.2 ∂paperMeasure) = _
  calc
    (∫ y : T4,
      res.incomingPhasedResidualDensity
        (charT4 beta y * red q.1 q.2)
        k rho eps 0 y q.2 ∂paperMeasure) =
      ∫ y : T4,
        charT4 beta y *
          res.incomingPhasedResidualDensity
            (red q.1 q.2) k rho eps 0 y q.2
        ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with y
      exact
        res.incomingPhasedResidualDensity_const_mul
          (charT4 beta y) (red q.1 q.2)
          k rho eps 0 y q.2
    _ = _ :=
      res.integral_char_mul_terminal_incomingPhasedResidualDensity_eq
        hnil hactive hedge (red q.1 q.2) k beta rho eps 0 q.2

/-! Reindex the completed left endpoint carrier as the untouched parameter
of the right initial source: `(((z,w),v),u) ↦ ((z,(w,u)),v)`. -/

def r324TwoHalfRightInitialSourceRegroupMeasurableEquiv
    (Z W V U : Type*) [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace V] [MeasurableSpace U] :
    (((Z × W) × V) × U) ≃ᵐ ((Z × (W × U)) × V) :=
  (MeasurableEquiv.prodAssoc
      (α := Z × W) (β := V) (γ := U)).trans
    ((MeasurableEquiv.prodAssoc
        (α := Z) (β := W) (γ := V × U)).trans
      ((MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl Z)
          (MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl W)
            (MeasurableEquiv.prodComm : V × U ≃ᵐ U × V))).trans
        ((MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl Z)
            (MeasurableEquiv.prodAssoc
              (α := W) (β := U) (γ := V)).symm).trans
          (MeasurableEquiv.prodAssoc
            (α := Z) (β := W × U) (γ := V)).symm)))

@[simp]
theorem r324TwoHalfRightInitialSourceRegroupMeasurableEquiv_apply
    {Z W V U : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace V] [MeasurableSpace U]
    (q : ((Z × W) × V) × U) :
    r324TwoHalfRightInitialSourceRegroupMeasurableEquiv Z W V U q =
      ((q.1.1.1, (q.1.1.2, q.2)), q.1.2) :=
  rfl

theorem measurePreserving_r324TwoHalfRightInitialSourceRegroupMeasurableEquiv
    {Z W V U : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace V] [MeasurableSpace U]
    (muZ : Measure Z) (muW : Measure W)
    (muV : Measure V) (muU : Measure U)
    [SFinite muZ] [SFinite muW] [SFinite muV] [SFinite muU] :
    MeasurePreserving
      (r324TwoHalfRightInitialSourceRegroupMeasurableEquiv Z W V U)
      (((muZ.prod muW).prod muV).prod muU)
      ((muZ.prod (muW.prod muU)).prod muV) := by
  exact
    ((measurePreserving_prodAssoc muZ (muW.prod muU) muV).symm.comp
      (((MeasurePreserving.id muZ).prod
          (measurePreserving_prodAssoc muW muU muV).symm).comp
        (((MeasurePreserving.id muZ).prod
            ((MeasurePreserving.id muW).prod
              (Measure.measurePreserving_swap
                (μ := muV) (ν := muU)))).comp
          ((measurePreserving_prodAssoc muZ muW (muV.prod muU)).comp
            (measurePreserving_prodAssoc
              (muZ.prod muW) muV muU)))))

namespace R324WithinHalfResidualPrefix
namespace R324IncomingExceptionalStopTraceAssembly

variable {rho : SmoothCutoff} {C lam eps K : ℝ}
    {m : ℕ} {kappaP kappaM : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-! ### The paired-incoming/retained-outgoing endpoint coefficient -/

/-- The coefficient left after the paired incoming operation, with the
free outgoing character removed.  The remaining parameter consists of
the two opposite-half external variables and its still-signed residual
carrier.  This is an exact signed object; the ordinary primitive defects
at both endpoints are estimated only after the outgoing operation. -/
def incomingExceptionalRefinedRootEndpointReducedCoefficient
    {outgoingTerminal : R322ExtractionStep m}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP initialScale)
    (endpoint :
      R324WithinHalfEndpointStopAtTerminal outgoingTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (alpha beta : Z4)
    (pi : kappaP.singles ≃ kappaM.singles)
    (s : (T4 × T4) ×
      ((R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate → T4))
    (u : endpoint.stop.SurvivingCoordinate → T4) : ℂ :=
  endpoint.multiplier alpha *
    ((paperSecondOrderModeDecay alpha : ℂ) ^ 2 *
      incomingExceptionalPrimitiveDefect rho lam eps
        (residualBlockOrder data.terminal.2)
        data.stopContext.one_le_blockOrder
        data.stopContext.internalEdges alpha *
      (charT4 (-alpha) s.1.1 *
        charT4 (-beta) s.1.2 *
        (((R324WithinHalfResidualPrefix.initial
            rho lam eps kappaM).residualIntegrand
          rho eps s.1.1 s.1.2
          ((R324WithinHalfResidualPrefix.initial
            rho lam eps kappaM).reconstruct s.2) : ℂ) *
          (r324ResidualPrimitiveSumProduct
            rho eps kappaP kappaM pi
            (r324TwoHalfRootDoubledReconstruct
              endpoint.stop
              (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
              (u, s.2)) : ℂ))))

/-- The original endpoint-stop coefficient factors as the free outgoing
character times the reduced coefficient.  This is precisely the algebraic
seam required before the retained outgoing Fourier integration. -/
theorem multiplier_mul_incomingExceptionalRefinedRootEndpointCoefficient_eq_char_mul_reduced
    {outgoingTerminal : R322ExtractionStep m}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP initialScale)
    (endpoint :
      R324WithinHalfEndpointStopAtTerminal outgoingTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (alpha beta : Z4)
    (pi : kappaP.singles ≃ kappaM.singles)
    (y : T4)
    (s : (T4 × T4) ×
      ((R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate → T4))
    (u : endpoint.stop.SurvivingCoordinate → T4) :
    endpoint.multiplier alpha *
        data.incomingExceptionalRefinedRootEndpointCoefficient
          endpoint alpha beta pi ((y, s.1), s.2) u =
      charT4 beta y *
        data.incomingExceptionalRefinedRootEndpointReducedCoefficient
          endpoint alpha beta pi s u := by
  unfold incomingExceptionalRefinedRootEndpointCoefficient
    incomingExceptionalRefinedRootEndpointPostOuter
    incomingExceptionalRefinedRootEndpointReducedCoefficient
  ring

/-- Pointwise density form of the preceding coefficient factorization.
The outgoing character is pulled out by linearity, while the signed stop
density itself is left untouched. -/
theorem incomingPhasedResidualDensity_endpointCoefficient_eq_char_mul_reduced
    {outgoingTerminal : R322ExtractionStep m}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP initialScale)
    (endpoint :
      R324WithinHalfEndpointStopAtTerminal outgoingTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (alpha beta : Z4)
    (pi : kappaP.singles ≃ kappaM.singles)
    (y : T4)
    (s : (T4 × T4) ×
      ((R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate → T4))
    (u : endpoint.stop.SurvivingCoordinate → T4) :
    endpoint.stop.incomingPhasedResidualDensity
        (endpoint.multiplier alpha *
          data.incomingExceptionalRefinedRootEndpointCoefficient
            endpoint alpha beta pi ((y, s.1), s.2) u)
        alpha rho eps 0 y u =
      charT4 beta y *
        endpoint.stop.incomingPhasedResidualDensity
          (data.incomingExceptionalRefinedRootEndpointReducedCoefficient
            endpoint alpha beta pi s u)
          alpha rho eps 0 y u := by
  rw [data.multiplier_mul_incomingExceptionalRefinedRootEndpointCoefficient_eq_char_mul_reduced
    endpoint alpha beta pi y s u]
  exact
    endpoint.stop.incomingPhasedResidualDensity_const_mul
      (charT4 beta y)
      (data.incomingExceptionalRefinedRootEndpointReducedCoefficient
        endpoint alpha beta pi s u)
      alpha rho eps 0 y u

/-- Removing the retained outgoing terminal does not change the cross-cut
primitive factor: that factor is indexed only by residual singles, hence
only by coordinates surviving in the post-terminal carrier. -/
theorem r324ResidualPrimitiveSumProduct_eq_leftOutgoingTerminalPost
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP initialScale)
    (outgoing :
      R324PaperOutgoingEndpointTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (pi : kappaP.singles ≃ kappaM.singles)
    (u : outgoing.endpoint.stop.SurvivingCoordinate → T4)
    (v : (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaM).SurvivingCoordinate → T4) :
    r324ResidualPrimitiveSumProduct
        rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          outgoing.endpoint.stop
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
          (u, v)) =
      r324ResidualPrimitiveSumProduct
        rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          outgoing.terminalPost
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
          ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
            outgoing.terminalData.terminal []
            outgoing.endpoint.stop_remaining u).2, v)) := by
  apply r324ResidualPrimitiveSumProduct_congr_on_active
  intro q hq
  by_cases hqLeft : q.val < m
  · obtain ⟨i, hiFinal, rfl⟩ :=
      exists_leftMomentIndex_of_mem_momentResidualActive hq hqLeft
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_leftMomentIndex]
    have hiPost : i ∈ outgoing.terminalPost.state.active := by
      rw [outgoing.terminalPost_active_eq_finalActive]
      exact hiFinal
    let iPost : outgoing.terminalPost.SurvivingCoordinate :=
      ⟨i, hiPost⟩
    let iStop : outgoing.endpoint.stop.SurvivingCoordinate :=
      outgoing.endpoint.stop.postSurvivingCoordinate
        outgoing.terminalData.terminal []
        outgoing.endpoint.stop_remaining iPost
    calc
      outgoing.endpoint.stop.reconstruct u i = u iStop := by
        exact outgoing.endpoint.stop.reconstruct_surviving u iStop
      _ =
          (outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
            outgoing.terminalData.terminal []
            outgoing.endpoint.stop_remaining u).2 iPost := by
        exact
          (outgoing.endpoint.stop
            |>.splitSurvivingPiMeasurableEquiv_apply_snd
              outgoing.terminalData.terminal []
              outgoing.endpoint.stop_remaining u iPost).symm
      _ = outgoing.terminalPost.reconstruct
          ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
            outgoing.terminalData.terminal []
            outgoing.endpoint.stop_remaining u).2) i := by
        exact
          (outgoing.terminalPost.reconstruct_surviving
            ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
              outgoing.terminalData.terminal []
              outgoing.endpoint.stop_remaining u).2) iPost).symm
  · have hqRight : m ≤ q.val := by omega
    obtain ⟨i, _hiFinal, rfl⟩ :=
      exists_rightMomentIndex_of_mem_momentResidualActive hq hqRight
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_rightMomentIndex]

/-- The post-terminal coefficient used by the retained outgoing theorem.
Its only left-half coordinates are the residual singles surviving after
the terminal block; the terminal primitive tuple is absent by definition. -/
def incomingExceptionalRefinedRootOutgoingPostCoefficient
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP initialScale)
    (outgoing :
      R324PaperOutgoingEndpointTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (alpha beta : Z4)
    (pi : kappaP.singles ≃ kappaM.singles)
    (s : (T4 × T4) ×
      ((R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate → T4))
    (v : outgoing.terminalPost.SurvivingCoordinate → T4) : ℂ :=
  outgoing.endpoint.multiplier alpha *
    ((paperSecondOrderModeDecay alpha : ℂ) ^ 2 *
      incomingExceptionalPrimitiveDefect rho lam eps
        (residualBlockOrder data.terminal.2)
        data.stopContext.one_le_blockOrder
        data.stopContext.internalEdges alpha *
      (charT4 (-alpha) s.1.1 *
        charT4 (-beta) s.1.2 *
        (((R324WithinHalfResidualPrefix.initial
            rho lam eps kappaM).residualIntegrand
          rho eps s.1.1 s.1.2
          ((R324WithinHalfResidualPrefix.initial
            rho lam eps kappaM).reconstruct s.2) : ℂ) *
          (r324ResidualPrimitiveSumProduct
            rho eps kappaP kappaM pi
            (r324TwoHalfRootDoubledReconstruct
              outgoing.terminalPost
              (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
              (v, s.2)) : ℂ))))

/-- The reduced stop coefficient factors literally through the
post-terminal projection used by the outgoing primitive split. -/
theorem incomingExceptionalRefinedRootEndpointReducedCoefficient_eq_post
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP initialScale)
    (outgoing :
      R324PaperOutgoingEndpointTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (alpha beta : Z4)
    (pi : kappaP.singles ≃ kappaM.singles)
    (s : (T4 × T4) ×
      ((R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate → T4))
    (u : outgoing.endpoint.stop.SurvivingCoordinate → T4) :
    data.incomingExceptionalRefinedRootEndpointReducedCoefficient
        outgoing.endpoint alpha beta pi s u =
      data.incomingExceptionalRefinedRootOutgoingPostCoefficient
        outgoing alpha beta pi s
        ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
          outgoing.terminalData.terminal []
          outgoing.endpoint.stop_remaining u).2) := by
  unfold incomingExceptionalRefinedRootEndpointReducedCoefficient
    incomingExceptionalRefinedRootOutgoingPostCoefficient
  rw [data.r324ResidualPrimitiveSumProduct_eq_leftOutgoingTerminalPost
    outgoing pi u s.2]

/-- Exact paired-incoming/retained-outgoing splice at the genuine refined
root.  The incoming exceptional head and every proper-prefix interval are
removed first.  The root parameters are then only reassociated, and the
retained terminal's primitive tuple and outgoing endpoint are integrated
by the paper's ordinary-`J` operation.  No norm occurs in this theorem. -/
theorem lamEps_pow_r324RefinedPhysicalIntegral_eq_incomingExceptional_outgoingExceptional
    (p : R324RefinedScheduleIndex m)
    (e0 : MomentContraction m)
    (he0 : e0 ∈ momentRefinedContractionFiber m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) e0.1 initialScale)
    (outgoing :
      R324PaperOutgoingEndpointTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (hm : 0 < m) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hG : ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hincoming :
      ∀ (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder data.terminal.2)
              kappaB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hpred :
      r324WithinHalfPredecessorSlot outgoing.endpoint.stop.state
          outgoing.terminalData.terminal ≠ 0)
    (hactive : outgoing.terminalPost.state.active.Nonempty)
    (houtgoing :
      ∀ (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder
                outgoing.terminalData.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder outgoing.terminalData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder
              outgoing.terminalData.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder outgoing.terminalData.terminal.2)
              kappaB.1 outgoing.terminalContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder outgoing.terminalData.terminal.2)
                outgoing.terminalContext.one_le_blockOrder
                first (first - gap) r))
          (Measure.pi fun _ => paperMeasure))
    (alpha beta : Z4)
    (hsource :
      Integrable
        (fun q :
            (T4 × ((T4 × T4) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps e0.2.1).SurvivingCoordinate → T4))) ×
              (outgoing.endpoint.stop.SurvivingCoordinate → T4) =>
          outgoing.endpoint.stop.incomingPhasedResidualDensity
            (data.incomingExceptionalRefinedRootOutgoingPostCoefficient
              outgoing alpha beta e0.2.2 q.1.2
              ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
                outgoing.terminalData.terminal []
                outgoing.endpoint.stop_remaining q.2).2))
            alpha rho eps 0 q.1.1 q.2)
        ((paperMeasure.prod
          ((paperMeasure.prod paperMeasure).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps e0.2.1).SurvivingCoordinate => paperMeasure))).prod
          (Measure.pi fun _ :
            outgoing.endpoint.stop.SurvivingCoordinate => paperMeasure))) :
    (lamEps lam eps : ℂ) ^
          (2 * (R324WithinHalfResidualPrefix.initial
            rho lam eps e0.1).remainingOrder) *
        r324RefinedPhysicalIntegral rho eps m alpha beta p =
      ∫ s : (T4 × T4) ×
          ((R324WithinHalfResidualPrefix.initial
            rho lam eps e0.2.1).SurvivingCoordinate → T4),
        ∫ v : outgoing.terminalPost.SurvivingCoordinate → T4,
          ∫ first : T4,
            outgoing.outgoingEndpointDefectDensity
              (data.incomingExceptionalRefinedRootOutgoingPostCoefficient
                outgoing alpha beta e0.2.2 s)
              alpha beta 0 v first
            ∂paperMeasure
          ∂Measure.pi fun _ => paperMeasure
        ∂((paperMeasure.prod paperMeasure).prod
          (Measure.pi fun _ => paperMeasure)) := by
  let muRight :=
    Measure.pi fun _ :
      (R324WithinHalfResidualPrefix.initial
        rho lam eps e0.2.1).SurvivingCoordinate => paperMeasure
  let muParameter := (paperMeasure.prod paperMeasure).prod muRight
  let muStop :=
    Measure.pi fun _ :
      outgoing.endpoint.stop.SurvivingCoordinate => paperMeasure
  let muRoot :=
    r324IncomingExceptionalRootParameterMeasure
      rho lam eps e0.2.1
  let sigma :
      (R324IncomingExceptionalRootParameter rho lam eps e0.2.1 ×
          (outgoing.endpoint.stop.SurvivingCoordinate → T4)) ≃ᵐ
        ((T4 × ((T4 × T4) ×
            ((R324WithinHalfResidualPrefix.initial
              rho lam eps e0.2.1).SurvivingCoordinate → T4))) ×
          (outgoing.endpoint.stop.SurvivingCoordinate → T4)) :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodAssoc
        (α := T4) (β := T4 × T4)
        (γ := (R324WithinHalfResidualPrefix.initial
          rho lam eps e0.2.1).SurvivingCoordinate → T4))
      (MeasurableEquiv.refl
        (outgoing.endpoint.stop.SurvivingCoordinate → T4))
  have hsigma :
      MeasurePreserving sigma (muRoot.prod muStop)
        ((paperMeasure.prod muParameter).prod muStop) := by
    dsimp only [sigma, muRoot, muParameter]
    unfold r324IncomingExceptionalRootParameterMeasure
    exact
      (measurePreserving_prodAssoc paperMeasure
        (paperMeasure.prod paperMeasure) muRight).prod
          (MeasurePreserving.id muStop)
  let Froot :
      R324IncomingExceptionalRootParameter rho lam eps e0.2.1 ×
        (outgoing.endpoint.stop.SurvivingCoordinate → T4) → ℂ :=
    fun q =>
      outgoing.endpoint.stop.incomingPhasedResidualDensity
        (outgoing.endpoint.multiplier alpha *
          data.incomingExceptionalRefinedRootEndpointCoefficient
            outgoing.endpoint alpha beta e0.2.2 q.1 q.2)
        alpha rho eps 0 q.1.1.1 q.2
  let Fbare :
      (T4 × ((T4 × T4) ×
          ((R324WithinHalfResidualPrefix.initial
            rho lam eps e0.2.1).SurvivingCoordinate → T4))) ×
        (outgoing.endpoint.stop.SurvivingCoordinate → T4) → ℂ :=
    fun q =>
      outgoing.endpoint.stop.incomingPhasedResidualDensity
        (data.incomingExceptionalRefinedRootOutgoingPostCoefficient
          outgoing alpha beta e0.2.2 q.1.2
          ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
            outgoing.terminalData.terminal []
            outgoing.endpoint.stop_remaining q.2).2))
        alpha rho eps 0 q.1.1 q.2
  let Fphase :
      (T4 × ((T4 × T4) ×
          ((R324WithinHalfResidualPrefix.initial
            rho lam eps e0.2.1).SurvivingCoordinate → T4))) ×
        (outgoing.endpoint.stop.SurvivingCoordinate → T4) → ℂ :=
    fun q => charT4 beta q.1.1 * Fbare q
  have hphaseMeas : Measurable
      (fun q :
          (T4 × ((T4 × T4) ×
            ((R324WithinHalfResidualPrefix.initial
              rho lam eps e0.2.1).SurvivingCoordinate → T4))) ×
            (outgoing.endpoint.stop.SurvivingCoordinate → T4) =>
        charT4 beta q.1.1) :=
    (continuous_charT4 beta).measurable.comp
      (measurable_fst.comp measurable_fst)
  have hphase : Integrable Fphase
      ((paperMeasure.prod muParameter).prod muStop) := by
    exact hsource.bdd_mul hphaseMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by rw [norm_charT4])
  have hpoint : ∀ q, Froot q = Fphase (sigma q) := by
    intro q
    change
      outgoing.endpoint.stop.incomingPhasedResidualDensity
          (outgoing.endpoint.multiplier alpha *
            data.incomingExceptionalRefinedRootEndpointCoefficient
              outgoing.endpoint alpha beta e0.2.2 q.1 q.2)
          alpha rho eps 0 q.1.1.1 q.2 =
        charT4 beta q.1.1.1 *
          outgoing.endpoint.stop.incomingPhasedResidualDensity
            (data.incomingExceptionalRefinedRootOutgoingPostCoefficient
              outgoing alpha beta e0.2.2 (q.1.1.2, q.1.2)
              ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
                outgoing.terminalData.terminal []
                outgoing.endpoint.stop_remaining q.2).2))
            alpha rho eps 0 q.1.1.1 q.2
    rw [data.incomingPhasedResidualDensity_endpointCoefficient_eq_char_mul_reduced
      outgoing.endpoint alpha beta e0.2.2 q.1.1.1
      (q.1.1.2, q.1.2) q.2]
    apply congrArg (fun z : ℂ => charT4 beta q.1.1.1 * z)
    apply congrArg (fun coefficient : ℂ =>
      outgoing.endpoint.stop.incomingPhasedResidualDensity
        coefficient alpha rho eps 0 q.1.1.1 q.2)
    exact
      data.incomingExceptionalRefinedRootEndpointReducedCoefficient_eq_post
        outgoing alpha beta e0.2.2 (q.1.1.2, q.1.2) q.2
  have hrootJoint : Integrable Froot (muRoot.prod muStop) := by
    have hcomp : Integrable (fun q => Fphase (sigma q))
        (muRoot.prod muStop) :=
      (hsigma.integrable_comp_emb sigma.measurableEmbedding
        (g := Fphase)).mpr hphase
    exact hcomp.congr
      (Filter.Eventually.of_forall fun q => (hpoint q).symm)
  have hroot :=
    data.lamEps_pow_r324RefinedPhysicalIntegral_eq_incomingEndpointStop
      p e0 he0 outgoing.endpoint hm heps heps1 hG hincoming alpha beta
  have hproduct :
      (∫ omega : R324IncomingExceptionalRootParameter
            rho lam eps e0.2.1,
          (lamEps lam eps : ℂ) ^
              (2 * outgoing.endpoint.stop.remainingOrder) *
            (∫ u : outgoing.endpoint.stop.SurvivingCoordinate → T4,
              Froot (omega, u) ∂muStop)
          ∂muRoot) =
        (lamEps lam eps : ℂ) ^
            (2 * outgoing.endpoint.stop.remainingOrder) *
          ∫ q, Froot q ∂(muRoot.prod muStop) := by
    rw [integral_const_mul, integral_prod _ hrootJoint]
  have hreindex :
      (∫ q, Froot q ∂(muRoot.prod muStop)) =
        ∫ q, Fphase q ∂((paperMeasure.prod muParameter).prod muStop) := by
    rw [← hsigma.integral_comp' Fphase]
    exact integral_congr_ae
      (Filter.Eventually.of_forall hpoint)
  have hout :=
    outgoing.lamEps_pow_integral_singleParameter_stop_outgoingEndpoint_eq_defect
      hpred hactive muParameter
      (data.incomingExceptionalRefinedRootOutgoingPostCoefficient
        outgoing alpha beta e0.2.2)
      alpha beta (fun _ => 0) hsource houtgoing
  calc
    (lamEps lam eps : ℂ) ^
          (2 * (R324WithinHalfResidualPrefix.initial
            rho lam eps e0.1).remainingOrder) *
        r324RefinedPhysicalIntegral rho eps m alpha beta p =
      ∫ omega : R324IncomingExceptionalRootParameter
            rho lam eps e0.2.1,
        (lamEps lam eps : ℂ) ^
            (2 * outgoing.endpoint.stop.remainingOrder) *
          (∫ u : outgoing.endpoint.stop.SurvivingCoordinate → T4,
            Froot (omega, u) ∂muStop)
        ∂muRoot := by
      simpa only [Froot, muRoot, muStop] using hroot
    _ = (lamEps lam eps : ℂ) ^
          (2 * outgoing.endpoint.stop.remainingOrder) *
        ∫ q, Froot q ∂(muRoot.prod muStop) := hproduct
    _ = (lamEps lam eps : ℂ) ^
          (2 * outgoing.endpoint.stop.remainingOrder) *
        ∫ q, Fphase q
          ∂((paperMeasure.prod muParameter).prod muStop) := by
      rw [hreindex]
    _ = _ := by
      simpa only [Fphase, Fbare, muParameter, muStop] using hout

/-! ### The right-half cross-factor projection

The pre-existing exceptional-stop projection theorem is stated for the
first half of the doubled carrier.  The paper uses the same operation on
the second half after the first half has already been reduced.  The next
two lemmas are the literal right-half mirror and its composition with the
complete after-head alternating transport.  They are signed coordinate
identities; no estimate is made here. -/

/-- Projecting the right initial tuple through its exceptional incoming
stop and discarding the retained head does not change the cross-cut
primitive factor.  The already-completed left half is untouched. -/
theorem r324ResidualPrimitiveSumProduct_eq_rightAfterHeadProjection
    (left : R324WithinHalfResidualPrefix rho lam eps kappaP)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM initialScale)
    (pi : kappaP.singles ≃ kappaM.singles)
    (vl : left.SurvivingCoordinate → T4)
    (vr :
      (R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate → T4) :
    r324ResidualPrimitiveSumProduct
        rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          left
          (R324WithinHalfResidualPrefix.initial
            rho lam eps kappaM)
          (vl, vr)) =
      r324ResidualPrimitiveSumProduct
        rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          left
          (data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq)
          (vl,
            (data.trace.stopPrefix
              |>.splitSurvivingPiMeasurableEquiv
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq
                (data.trace.stopProjection vr)).2)) := by
  apply r324ResidualPrimitiveSumProduct_congr_on_active
  intro q hq
  by_cases hqLeft : q.val < m
  · obtain ⟨i, _hiFinal, rfl⟩ :=
      exists_leftMomentIndex_of_mem_momentResidualActive hq hqLeft
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_leftMomentIndex]
  · have hqRight : m ≤ q.val := by omega
    obtain ⟨i, hiFinal, rfl⟩ :=
      exists_rightMomentIndex_of_mem_momentResidualActive hq hqRight
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_rightMomentIndex]
    have hiStop : i ∈ data.trace.stopPrefix.state.active :=
      data.trace.finalActive_subset_stopPrefix_active hiFinal
    have hiNotTerminal : i ∉ data.terminal.2 := by
      intro hiTerminal
      have hiRemoved :
          i ∈ finsetUnionList (extractionBlocks kappaM) :=
        (mem_finsetUnionList_iff (extractionBlocks kappaM)).mpr
          ⟨data.terminal.2,
            data.stopContext.block_mem_extractionBlocks,
            hiTerminal⟩
      exact
        (Finset.disjoint_left.mp
          (extractionBlocks_disjoint_finalActive kappaM))
          hiRemoved hiFinal
    have hiPost :
        i ∈
          (data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq).state.active := by
      change i ∈ (data.stopContext.absorb rho lam eps).active
      rw [R324WithinHalfStepContext.absorb_active]
      exact Finset.mem_sdiff.mpr ⟨hiStop, hiNotTerminal⟩
    let iStop : data.trace.stopPrefix.SurvivingCoordinate :=
      ⟨i, hiStop⟩
    let iPost :
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate :=
      ⟨i, hiPost⟩
    calc
      (R324WithinHalfResidualPrefix.initial
          rho lam eps kappaM).reconstruct vr i =
          data.trace.stopPrefix.reconstruct
            (data.trace.stopProjection vr) i :=
        data.trace.reconstruct_stopProjection vr iStop
      _ = data.trace.stopProjection vr iStop :=
        data.trace.stopPrefix.reconstruct_surviving
          (data.trace.stopProjection vr) iStop
      _ =
          data.trace.stopProjection vr
            (data.trace.stopPrefix.postSurvivingCoordinate
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq iPost) := by
        apply congrArg (data.trace.stopProjection vr)
        apply Subtype.ext
        rfl
      _ =
          (data.trace.stopPrefix
              |>.splitSurvivingPiMeasurableEquiv
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq
                (data.trace.stopProjection vr)).2 iPost := by
        exact
          (data.trace.stopPrefix
            |>.splitSurvivingPiMeasurableEquiv_apply_snd
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq
              (data.trace.stopProjection vr) iPost).symm
      _ =
          (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).reconstruct
            (data.trace.stopPrefix
                |>.splitSurvivingPiMeasurableEquiv
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq
                  (data.trace.stopProjection vr)).2 i :=
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).reconstruct_surviving
            (data.trace.stopPrefix
                |>.splitSurvivingPiMeasurableEquiv
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq
                  (data.trace.stopProjection vr)).2
            iPost).symm

/-- The same right-half cross factor may be read on the terminal carrier of
the complete after-head alternating transport. -/
theorem r324ResidualPrimitiveSumProduct_eq_rightDriverProjection
    (left : R324WithinHalfResidualPrefix rho lam eps kappaP)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM initialScale)
    (sub :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (pi : kappaP.singles ≃ kappaM.singles)
    (vl : left.SurvivingCoordinate → T4)
    (vr :
      (R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate → T4) :
    r324ResidualPrimitiveSumProduct
        rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          left
          (R324WithinHalfResidualPrefix.initial
            rho lam eps kappaM)
          (vl, vr)) =
      r324ResidualPrimitiveSumProduct
        rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          left sub.final
          (vl,
            sub.projection
              (data.trace.stopPrefix
                |>.splitSurvivingPiMeasurableEquiv
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq
                  (data.trace.stopProjection vr)).2)) := by
  rw [r324ResidualPrimitiveSumProduct_eq_rightAfterHeadProjection
    left data pi vl vr]
  apply r324ResidualPrimitiveSumProduct_congr_on_active
  intro q hq
  by_cases hqLeft : q.val < m
  · obtain ⟨i, _hiFinal, rfl⟩ :=
      exists_leftMomentIndex_of_mem_momentResidualActive hq hqLeft
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_leftMomentIndex]
  · have hqRight : m ≤ q.val := by omega
    obtain ⟨i, hiFinal, rfl⟩ :=
      exists_rightMomentIndex_of_mem_momentResidualActive hq hqRight
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_rightMomentIndex]
    let iFinal : sub.final.SurvivingCoordinate :=
      ⟨i, by
        rw [sub.final_active_eq_finalActive]
        exact hiFinal⟩
    exact sub.reconstruct_projection _ iFinal

/-- The initial-source Fubini license propagates to the certified
exceptional stop.  This is the integrability subproof already present in
the trace/Fourier bridge, exposed here so the second half of the paper
splice does not carry a redundant hypothesis. -/
theorem integrable_incomingExceptionalStopSourceDensity_of_initial
    {pairing : PartialPairing (Fin m)}
    {Omega : Type*} [MeasurableSpace Omega]
    (nu : Measure Omega) [SFinite nu]
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) pairing initialScale)
    (k : Z4) (y : Omega → T4)
    (postOuter :
      Omega →
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4) → ℂ)
    (hcurrent :
      Integrable
        (data.incomingExceptionalInitialSourceDensity k y postOuter)
        ((paperMeasure.prod nu).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps pairing).SurvivingCoordinate => paperMeasure))) :
    Integrable
      (data.incomingExceptionalStopSourceDensity k y postOuter)
      ((paperMeasure.prod nu).prod
        (Measure.pi fun _ :
          data.trace.stopPrefix.SurvivingCoordinate => paperMeasure)) := by
  let initial :=
    R324WithinHalfResidualPrefix.initial rho lam eps pairing
  let split :=
    data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
  let stopOuter :
      T4 × Omega →
        (data.trace.stopPrefix.SurvivingCoordinate → T4) → ℂ :=
    fun ep w =>
      charT4 k ep.1 * postOuter ep.2 (split w).2
  have hcurrent' :
      Integrable
        (fun p :
            (T4 × Omega) ×
              (initial.SurvivingCoordinate → T4) =>
          (initial.residualIntegrand
              rho eps p.1.1 (y p.1.2)
              (initial.reconstruct p.2) : ℂ) *
            stopOuter p.1 (data.trace.stopProjection p.2))
        ((paperMeasure.prod nu).prod
          (Measure.pi fun _ : initial.SurvivingCoordinate =>
            paperMeasure)) :=
    hcurrent
  exact
    data.trace.integrable_joint_residualIntegrand_mul_stopOuter_stopPrefix
      (paperMeasure.prod nu)
      (fun ep : T4 × Omega => ep.1)
      (fun ep : T4 × Omega => y ep.2)
      stopOuter hcurrent'

/-- The complete signed left-half splice in the
incoming-exceptional/outgoing-direct case.  The exceptional incoming head
and every later left-half interval are removed exactly by the alternating
transport.  Only then is the free outgoing variable regrouped and
Fourier-integrated.  The right half and the entire cross-covariance factor
remain signed inside the displayed outer integral. -/
theorem lamEps_pow_r324RefinedPhysicalIntegral_eq_incomingExceptional_directOutgoing
    (p : R324RefinedScheduleIndex m)
    (e0 : MomentContraction m)
    (he0 : e0 ∈ momentRefinedContractionFiber m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) e0.1 initialScale)
    (transport :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (hm : 0 < m)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hG : ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder data.terminal.2)
              kappaB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (alpha beta : Z4)
    (hjoint : data.DriverTerminalJointIntegrable
      transport alpha beta e0.2.2)
    (hactive : transport.final.state.active.Nonempty)
    (hdirect : r324OutgoingIsShortcut e0.1 = false) :
    (lamEps lam eps : ℂ) ^
          (2 *
            (R324WithinHalfResidualPrefix.initial
              rho lam eps e0.1).remainingOrder) *
        r324RefinedPhysicalIntegral rho eps m alpha beta p =
      ∫ s :
          (T4 × T4) ×
            ((R324WithinHalfResidualPrefix.initial
              rho lam eps e0.2.1).SurvivingCoordinate → T4),
        ∫ u : transport.final.SurvivingCoordinate → T4,
          data.incomingExceptionalRefinedRootDriverReducedCoefficient
              transport alpha beta e0.2.2 s.1 s.2 u *
            charT4 alpha
              (transport.final.terminalIncomingAnchor
                (transport.final.reconstruct u)) *
            ((transport.final.endpointErasedSignedChain
              hactive 0 0 (transport.final.reconstruct u) : ℝ) : ℂ) *
            translatedGreenMode beta
              (transport.final.terminalOutgoingAnchor hactive
                (transport.final.reconstruct u))
          ∂Measure.pi fun _ => paperMeasure
        ∂((paperMeasure.prod paperMeasure).prod
          (Measure.pi fun _ => paperMeasure)) := by
  have hroot :=
    data.lamEps_pow_r324RefinedPhysicalIntegral_eq_driverTerminal
      p e0 he0 transport hm heps heps1 hG hint alpha beta
  have hedge :
      transport.final.state.edges
          (transport.final.terminalOutgoingEdgeSlot hactive) =
        greenFn :=
    transport.final.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_not_shortcut
      hm transport.final_processed_eq_schedule hdirect hactive
  let muRight :=
    Measure.pi fun _ :
      (R324WithinHalfResidualPrefix.initial
        rho lam eps e0.2.1).SurvivingCoordinate => paperMeasure
  let muFinal :=
    Measure.pi fun _ : transport.final.SurvivingCoordinate => paperMeasure
  have hproduct :
      (∫ omega : R324IncomingExceptionalRootParameter
            rho lam eps e0.2.1,
          ∫ u : transport.final.SurvivingCoordinate → T4,
            transport.final.incomingPhasedResidualDensity
              (transport.multiplier alpha *
                data.incomingExceptionalRefinedRootDriverCoefficient
                  transport alpha beta e0.2.2 omega u)
              alpha rho eps 0 omega.1.1 u
            ∂muFinal
          ∂r324IncomingExceptionalRootParameterMeasure
            rho lam eps e0.2.1) =
        ∫ q :
            R324IncomingExceptionalRootParameter
                rho lam eps e0.2.1 ×
              (transport.final.SurvivingCoordinate → T4),
          transport.final.incomingPhasedResidualDensity
            (transport.multiplier alpha *
              data.incomingExceptionalRefinedRootDriverCoefficient
                transport alpha beta e0.2.2 q.1 q.2)
            alpha rho eps 0 q.1.1.1 q.2
          ∂((r324IncomingExceptionalRootParameterMeasure
              rho lam eps e0.2.1).prod muFinal) := by
    exact (integral_prod _ hjoint).symm
  have hstrip :
      (∫ q :
          R324IncomingExceptionalRootParameter
              rho lam eps e0.2.1 ×
            (transport.final.SurvivingCoordinate → T4),
        transport.final.incomingPhasedResidualDensity
          (transport.multiplier alpha *
            data.incomingExceptionalRefinedRootDriverCoefficient
              transport alpha beta e0.2.2 q.1 q.2)
          alpha rho eps 0 q.1.1.1 q.2
        ∂((r324IncomingExceptionalRootParameterMeasure
            rho lam eps e0.2.1).prod muFinal)) =
      ∫ q :
          (((T4 × (T4 × T4)) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps e0.2.1).SurvivingCoordinate → T4)) ×
            (transport.final.SurvivingCoordinate → T4)),
        transport.final.incomingPhasedResidualDensity
          (charT4 beta q.1.1.1 *
            data.incomingExceptionalRefinedRootDriverReducedCoefficient
              transport alpha beta e0.2.2 q.1.1.2 q.1.2 q.2)
          alpha rho eps 0 q.1.1.1 q.2
        ∂((((paperMeasure.prod (paperMeasure.prod paperMeasure)).prod
            muRight).prod muFinal)) := by
    unfold r324IncomingExceptionalRootParameterMeasure
    apply integral_congr_ae
    filter_upwards with q
    rw [data.multiplier_mul_driverCoefficient_eq_char_mul_reduced
      transport alpha beta e0.2.2 q.1 q.2]
  have hjointStripped :
      Integrable
        (fun q :
            (((T4 × (T4 × T4)) ×
                ((R324WithinHalfResidualPrefix.initial
                  rho lam eps e0.2.1).SurvivingCoordinate → T4)) ×
              (transport.final.SurvivingCoordinate → T4)) =>
          transport.final.incomingPhasedResidualDensity
            (charT4 beta q.1.1.1 *
              data.incomingExceptionalRefinedRootDriverReducedCoefficient
                transport alpha beta e0.2.2 q.1.1.2 q.1.2 q.2)
            alpha rho eps 0 q.1.1.1 q.2)
        ((((paperMeasure.prod (paperMeasure.prod paperMeasure)).prod
            muRight).prod muFinal)) := by
    unfold DriverTerminalJointIntegrable at hjoint
    unfold r324IncomingExceptionalRootParameterMeasure at hjoint
    apply hjoint.congr
    filter_upwards with q
    rw [data.multiplier_mul_driverCoefficient_eq_char_mul_reduced
      transport alpha beta e0.2.2 q.1 q.2]
  calc
    (lamEps lam eps : ℂ) ^
          (2 *
            (R324WithinHalfResidualPrefix.initial
              rho lam eps e0.1).remainingOrder) *
        r324RefinedPhysicalIntegral rho eps m alpha beta p =
        ∫ omega : R324IncomingExceptionalRootParameter
              rho lam eps e0.2.1,
          ∫ u : transport.final.SurvivingCoordinate → T4,
            transport.final.incomingPhasedResidualDensity
              (transport.multiplier alpha *
                data.incomingExceptionalRefinedRootDriverCoefficient
                  transport alpha beta e0.2.2 omega u)
              alpha rho eps 0 omega.1.1 u
            ∂muFinal
          ∂r324IncomingExceptionalRootParameterMeasure
            rho lam eps e0.2.1 := hroot
    _ = ∫ q :
            R324IncomingExceptionalRootParameter
                rho lam eps e0.2.1 ×
              (transport.final.SurvivingCoordinate → T4),
          transport.final.incomingPhasedResidualDensity
            (transport.multiplier alpha *
              data.incomingExceptionalRefinedRootDriverCoefficient
                transport alpha beta e0.2.2 q.1 q.2)
            alpha rho eps 0 q.1.1.1 q.2
          ∂((r324IncomingExceptionalRootParameterMeasure
              rho lam eps e0.2.1).prod muFinal) := hproduct
    _ = ∫ q :
          (((T4 × (T4 × T4)) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps e0.2.1).SurvivingCoordinate → T4)) ×
            (transport.final.SurvivingCoordinate → T4)),
        transport.final.incomingPhasedResidualDensity
          (charT4 beta q.1.1.1 *
            data.incomingExceptionalRefinedRootDriverReducedCoefficient
              transport alpha beta e0.2.2 q.1.1.2 q.1.2 q.2)
          alpha rho eps 0 q.1.1.1 q.2
        ∂((((paperMeasure.prod (paperMeasure.prod paperMeasure)).prod
            muRight).prod muFinal)) := hstrip
    _ = _ :=
      integral_rootProd_incomingPhasedResidualDensity_eq_directOutgoing
        transport.final transport.final_remaining hactive hedge
        (paperMeasure.prod paperMeasure) muRight
        (data.incomingExceptionalRefinedRootDriverReducedCoefficient
          transport alpha beta e0.2.2)
        beta alpha hjointStripped

/-- Generic signed two-endpoint splice for one half.  It is the reusable
paper Step-4(A) operation needed on the right copy: first transport the
all-Green initial half to its exceptional incoming head, then collapse that
head and every later half-block, and finally Fourier-integrate a direct
outgoing Green leg.  All parameters in `ZW` and `VR` remain untouched. -/
theorem lamEps_pow_integral_initialResidual_eq_incomingExceptional_directOutgoing
    {pairing : PartialPairing (Fin m)}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) pairing initialScale)
    (sub :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    {ZW VR : Type*} [MeasurableSpace ZW] [MeasurableSpace VR]
    (muZW : Measure ZW) (muVR : Measure VR)
    [SFinite muZW] [SFinite muVR]
    (red : ZW → VR → (sub.final.SurvivingCoordinate → T4) → ℂ)
    (incomingMode outgoingMode : Z4)
    (hm : 0 < m)
    (hG : ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder data.terminal.2)
              kappaB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hcurrent :
      Integrable
        (data.incomingExceptionalInitialSourceDensity
          incomingMode
          (fun omega : (T4 × ZW) × VR => omega.1.1)
          (fun omega v =>
            charT4 outgoingMode omega.1.1 *
              red omega.1.2 omega.2 (sub.projection v)))
        ((paperMeasure.prod ((paperMeasure.prod muZW).prod muVR)).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps pairing).SurvivingCoordinate => paperMeasure)))
    (hsource :
      Integrable
        (data.incomingExceptionalStopSourceDensity
          incomingMode
          (fun omega : (T4 × ZW) × VR => omega.1.1)
          (fun omega v =>
            charT4 outgoingMode omega.1.1 *
              red omega.1.2 omega.2 (sub.projection v)))
        ((paperMeasure.prod ((paperMeasure.prod muZW).prod muVR)).prod
          (Measure.pi fun _ :
            data.trace.stopPrefix.SurvivingCoordinate => paperMeasure)))
    (hactive : sub.final.state.active.Nonempty)
    (hedge :
      sub.final.state.edges
          (sub.final.terminalOutgoingEdgeSlot hactive) = greenFn)
    (hterminal :
      Integrable
        (fun q :
            (((T4 × ZW) × VR) ×
              (sub.final.SurvivingCoordinate → T4)) =>
          sub.final.incomingPhasedResidualDensity
            (charT4 outgoingMode q.1.1.1 *
              (sub.multiplier incomingMode *
                ((paperSecondOrderModeDecay incomingMode : ℂ) ^ 2 *
                  incomingExceptionalPrimitiveDefect rho lam eps
                    (residualBlockOrder data.terminal.2)
                    data.stopContext.one_le_blockOrder
                    data.stopContext.internalEdges incomingMode *
                  red q.1.1.2 q.1.2 q.2)))
            incomingMode rho eps 0 q.1.1.1 q.2)
        ((((paperMeasure.prod muZW).prod muVR).prod
          (Measure.pi fun _ => paperMeasure)))) :
    (lamEps lam eps : ℂ) ^
          (2 * (R324WithinHalfResidualPrefix.initial
            rho lam eps pairing).remainingOrder) *
        (∫ p,
          data.incomingExceptionalInitialSourceDensity
            incomingMode
            (fun omega : (T4 × ZW) × VR => omega.1.1)
            (fun omega v =>
              charT4 outgoingMode omega.1.1 *
                red omega.1.2 omega.2 (sub.projection v)) p
          ∂((paperMeasure.prod ((paperMeasure.prod muZW).prod muVR)).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate => paperMeasure))) =
      ∫ s : ZW × VR,
        ∫ u : sub.final.SurvivingCoordinate → T4,
          (sub.multiplier incomingMode *
              ((paperSecondOrderModeDecay incomingMode : ℂ) ^ 2 *
                incomingExceptionalPrimitiveDefect rho lam eps
                  (residualBlockOrder data.terminal.2)
                  data.stopContext.one_le_blockOrder
                  data.stopContext.internalEdges incomingMode *
                red s.1 s.2 u)) *
            charT4 incomingMode
              (sub.final.terminalIncomingAnchor
                (sub.final.reconstruct u)) *
            ((sub.final.endpointErasedSignedChain
              hactive 0 0 (sub.final.reconstruct u) : ℝ) : ℂ) *
            translatedGreenMode outgoingMode
              (sub.final.terminalOutgoingAnchor hactive
                (sub.final.reconstruct u))
          ∂Measure.pi fun _ => paperMeasure
        ∂(muZW.prod muVR) := by
  let nu := (paperMeasure.prod muZW).prod muVR
  let postOuter :
      ((T4 × ZW) × VR) →
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate → T4) → ℂ :=
    fun omega v =>
      charT4 outgoingMode omega.1.1 *
        red omega.1.2 omega.2 (sub.projection v)
  let reduced :
      ZW → VR → (sub.final.SurvivingCoordinate → T4) → ℂ :=
    fun zw vr u =>
      sub.multiplier incomingMode *
        ((paperSecondOrderModeDecay incomingMode : ℂ) ^ 2 *
          incomingExceptionalPrimitiveDefect rho lam eps
            (residualBlockOrder data.terminal.2)
            data.stopContext.one_le_blockOrder
            data.stopContext.internalEdges incomingMode *
          red zw vr u)
  have hinitial :=
    data.lamEps_pow_integral_initialResidual_eq_incomingExceptionalStopFourier
      nu hm incomingMode
      (fun omega : (T4 × ZW) × VR => omega.1.1)
      postOuter hcurrent
  have hhead :=
    data.lamEps_pow_integral_incomingExceptionalStopFourierDensity_eq_afterHead
      nu hm incomingMode
      (fun omega : (T4 × ZW) × VR => omega.1.1)
      postOuter hsource hG hint
  have hafter :
      Integrable
        (data.incomingExceptionalAfterHeadPhasedIntegrand
          incomingMode
          (fun omega : (T4 × ZW) × VR => omega.1.1)
          postOuter)
        (nu.prod
          (Measure.pi fun _ :
            (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                paperMeasure)) :=
    data.integrable_incomingExceptionalAfterHeadPhasedIntegrand
      nu hm incomingMode
      (fun omega : (T4 × ZW) × VR => omega.1.1)
      postOuter hsource hG hint
  have htransport :
      (lamEps lam eps : ℂ) ^
            (2 *
              (data.trace.stopPrefix.afterHead
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq).remainingOrder) *
          (∫ p,
            data.incomingExceptionalAfterHeadPhasedIntegrand
              incomingMode
              (fun omega : (T4 × ZW) × VR => omega.1.1)
              postOuter p
            ∂(nu.prod
              (Measure.pi fun _ :
                (data.trace.stopPrefix.afterHead
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                    paperMeasure))) =
        ∫ q :
            (((T4 × ZW) × VR) ×
              (sub.final.SurvivingCoordinate → T4)),
          sub.final.incomingPhasedResidualDensity
            (charT4 outgoingMode q.1.1.1 *
              reduced q.1.1.2 q.1.2 q.2)
            incomingMode rho eps 0 q.1.1.1 q.2
          ∂(nu.prod (Measure.pi fun _ => paperMeasure)) := by
    rw [integral_prod _ hafter, ← integral_const_mul]
    have hterminal' :
        Integrable
          (fun q :
              (((T4 × ZW) × VR) ×
                (sub.final.SurvivingCoordinate → T4)) =>
            sub.final.incomingPhasedResidualDensity
              (charT4 outgoingMode q.1.1.1 *
                reduced q.1.1.2 q.1.2 q.2)
              incomingMode rho eps 0 q.1.1.1 q.2)
          (nu.prod (Measure.pi fun _ => paperMeasure)) := by
      simpa only [nu, reduced] using hterminal
    rw [integral_prod _ hterminal']
    apply integral_congr_ae
    filter_upwards [hafter.prod_right_ae] with omega homega
    have hsection :=
      sub.transport 0 omega.1.1 incomingMode
        (fun u =>
          (paperSecondOrderModeDecay incomingMode : ℂ) ^ 2 *
            incomingExceptionalPrimitiveDefect rho lam eps
              (residualBlockOrder data.terminal.2)
              data.stopContext.one_le_blockOrder
              data.stopContext.internalEdges incomingMode *
            (charT4 outgoingMode omega.1.1 *
              red omega.1.2 omega.2 u))
        (by
          simpa only [postOuter,
            incomingExceptionalAfterHeadPhasedIntegrand,
            incomingExceptionalPostCoefficient] using homega)
    calc
      (lamEps lam eps : ℂ) ^
            (2 *
              (data.trace.stopPrefix.afterHead
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq).remainingOrder) *
          (∫ v,
            data.incomingExceptionalAfterHeadPhasedIntegrand
              incomingMode
              (fun omega' : (T4 × ZW) × VR => omega'.1.1)
              postOuter (omega, v)
            ∂Measure.pi fun _ => paperMeasure) =
          ∫ u : sub.final.SurvivingCoordinate → T4,
            sub.final.incomingPhasedResidualDensity
              (sub.multiplier incomingMode *
                ((paperSecondOrderModeDecay incomingMode : ℂ) ^ 2 *
                  incomingExceptionalPrimitiveDefect rho lam eps
                    (residualBlockOrder data.terminal.2)
                    data.stopContext.one_le_blockOrder
                    data.stopContext.internalEdges incomingMode *
                  (charT4 outgoingMode omega.1.1 *
                    red omega.1.2 omega.2 u)))
              incomingMode rho eps 0 omega.1.1 u
            ∂Measure.pi fun _ => paperMeasure := hsection
      _ = ∫ u : sub.final.SurvivingCoordinate → T4,
            sub.final.incomingPhasedResidualDensity
              (charT4 outgoingMode omega.1.1 *
                reduced omega.1.2 omega.2 u)
              incomingMode rho eps 0 omega.1.1 u
            ∂Measure.pi fun _ => paperMeasure := by
          apply integral_congr_ae
          filter_upwards with u
          dsimp only [reduced]
          congr 1
          ring
  have hout :=
    integral_rootProd_incomingPhasedResidualDensity_eq_directOutgoing
      sub.final sub.final_remaining hactive hedge muZW muVR reduced
      outgoingMode incomingMode
      (by simpa only [nu, reduced] using hterminal)
  calc
    (lamEps lam eps : ℂ) ^
          (2 * (R324WithinHalfResidualPrefix.initial
            rho lam eps pairing).remainingOrder) *
        (∫ p,
          data.incomingExceptionalInitialSourceDensity
            incomingMode
            (fun omega : (T4 × ZW) × VR => omega.1.1)
            (fun omega v =>
              charT4 outgoingMode omega.1.1 *
                red omega.1.2 omega.2 (sub.projection v)) p
          ∂((paperMeasure.prod ((paperMeasure.prod muZW).prod muVR)).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate => paperMeasure))) =
        (lamEps lam eps : ℂ) ^
          (2 * data.trace.stopPrefix.remainingOrder) *
        (∫ p,
          data.incomingExceptionalStopFourierDensity
            incomingMode
            (fun omega : (T4 × ZW) × VR => omega.1.1)
            postOuter p
          ∂(nu.prod
            ((Measure.pi fun _ :
              Fin (2 * residualBlockOrder data.terminal.2) => paperMeasure).prod
            (Measure.pi fun _ :
              (data.trace.stopPrefix.afterHead
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                  paperMeasure)))) := hinitial
    _ = (lamEps lam eps : ℂ) ^
          (2 *
            (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).remainingOrder) *
        (∫ p,
          data.incomingExceptionalAfterHeadPhasedIntegrand
            incomingMode
            (fun omega : (T4 × ZW) × VR => omega.1.1)
            postOuter p
          ∂(nu.prod
            (Measure.pi fun _ :
              (data.trace.stopPrefix.afterHead
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                paperMeasure))) := hhead
    _ = ∫ q :
          (((T4 × ZW) × VR) ×
            (sub.final.SurvivingCoordinate → T4)),
        sub.final.incomingPhasedResidualDensity
          (charT4 outgoingMode q.1.1.1 *
            reduced q.1.1.2 q.1.2 q.2)
          incomingMode rho eps 0 q.1.1.1 q.2
        ∂(nu.prod (Measure.pi fun _ => paperMeasure)) := htransport
    _ = _ := by
      simpa only [nu, reduced] using hout

/-- Single-parameter form of the complete exceptional-incoming/direct-
outgoing half splice.  Its untouched parameter will be the terminal
coordinate of the opposite half, so no dummy product carrier is needed in
the two-half paper assembly. -/
theorem
    lamEps_pow_integral_initialResidual_eq_singleParameter_incomingExceptional_directOutgoing
    {pairing : PartialPairing (Fin m)}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) pairing initialScale)
    (sub :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U) [SFinite muU]
    (red : U → (sub.final.SurvivingCoordinate → T4) → ℂ)
    (incomingMode outgoingMode : Z4)
    (hm : 0 < m)
    (hG : ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder data.terminal.2)
              kappaB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hcurrent :
      Integrable
        (data.incomingExceptionalInitialSourceDensity
          incomingMode
          (fun omega : T4 × U => omega.1)
          (fun omega v =>
            charT4 outgoingMode omega.1 *
              red omega.2 (sub.projection v)))
        ((paperMeasure.prod (paperMeasure.prod muU)).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps pairing).SurvivingCoordinate => paperMeasure)))
    (hsource :
      Integrable
        (data.incomingExceptionalStopSourceDensity
          incomingMode
          (fun omega : T4 × U => omega.1)
          (fun omega v =>
            charT4 outgoingMode omega.1 *
              red omega.2 (sub.projection v)))
        ((paperMeasure.prod (paperMeasure.prod muU)).prod
          (Measure.pi fun _ :
            data.trace.stopPrefix.SurvivingCoordinate => paperMeasure)))
    (hactive : sub.final.state.active.Nonempty)
    (hedge :
      sub.final.state.edges
          (sub.final.terminalOutgoingEdgeSlot hactive) = greenFn)
    (hterminal :
      Integrable
        (fun q : (T4 × U) ×
              (sub.final.SurvivingCoordinate → T4) =>
          sub.final.incomingPhasedResidualDensity
            (charT4 outgoingMode q.1.1 *
              (sub.multiplier incomingMode *
                ((paperSecondOrderModeDecay incomingMode : ℂ) ^ 2 *
                  incomingExceptionalPrimitiveDefect rho lam eps
                    (residualBlockOrder data.terminal.2)
                    data.stopContext.one_le_blockOrder
                    data.stopContext.internalEdges incomingMode *
                  red q.1.2 q.2)))
            incomingMode rho eps 0 q.1.1 q.2)
        ((paperMeasure.prod muU).prod
          (Measure.pi fun _ => paperMeasure))) :
    (lamEps lam eps : ℂ) ^
          (2 * (R324WithinHalfResidualPrefix.initial
            rho lam eps pairing).remainingOrder) *
        (∫ p,
          data.incomingExceptionalInitialSourceDensity
            incomingMode
            (fun omega : T4 × U => omega.1)
            (fun omega v =>
              charT4 outgoingMode omega.1 *
                red omega.2 (sub.projection v)) p
          ∂((paperMeasure.prod (paperMeasure.prod muU)).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate => paperMeasure))) =
      ∫ s : U,
        ∫ u : sub.final.SurvivingCoordinate → T4,
          (sub.multiplier incomingMode *
              ((paperSecondOrderModeDecay incomingMode : ℂ) ^ 2 *
                incomingExceptionalPrimitiveDefect rho lam eps
                  (residualBlockOrder data.terminal.2)
                  data.stopContext.one_le_blockOrder
                  data.stopContext.internalEdges incomingMode *
                red s u)) *
            charT4 incomingMode
              (sub.final.terminalIncomingAnchor
                (sub.final.reconstruct u)) *
            ((sub.final.endpointErasedSignedChain
              hactive 0 0 (sub.final.reconstruct u) : ℝ) : ℂ) *
            translatedGreenMode outgoingMode
              (sub.final.terminalOutgoingAnchor hactive
                (sub.final.reconstruct u))
          ∂Measure.pi fun _ => paperMeasure
        ∂muU := by
  let nu := paperMeasure.prod muU
  let postOuter :
      (T4 × U) →
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate → T4) → ℂ :=
    fun omega v =>
      charT4 outgoingMode omega.1 *
        red omega.2 (sub.projection v)
  let reduced :
      U → (sub.final.SurvivingCoordinate → T4) → ℂ :=
    fun u v =>
      sub.multiplier incomingMode *
        ((paperSecondOrderModeDecay incomingMode : ℂ) ^ 2 *
          incomingExceptionalPrimitiveDefect rho lam eps
            (residualBlockOrder data.terminal.2)
            data.stopContext.one_le_blockOrder
            data.stopContext.internalEdges incomingMode *
          red u v)
  have hinitial :=
    data.lamEps_pow_integral_initialResidual_eq_incomingExceptionalStopFourier
      nu hm incomingMode
      (fun omega : T4 × U => omega.1)
      postOuter hcurrent
  have hhead :=
    data.lamEps_pow_integral_incomingExceptionalStopFourierDensity_eq_afterHead
      nu hm incomingMode
      (fun omega : T4 × U => omega.1)
      postOuter hsource hG hint
  have hafter :
      Integrable
        (data.incomingExceptionalAfterHeadPhasedIntegrand
          incomingMode
          (fun omega : T4 × U => omega.1)
          postOuter)
        (nu.prod
          (Measure.pi fun _ :
            (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                paperMeasure)) :=
    data.integrable_incomingExceptionalAfterHeadPhasedIntegrand
      nu hm incomingMode
      (fun omega : T4 × U => omega.1)
      postOuter hsource hG hint
  have htransport :
      (lamEps lam eps : ℂ) ^
            (2 *
              (data.trace.stopPrefix.afterHead
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq).remainingOrder) *
          (∫ p,
            data.incomingExceptionalAfterHeadPhasedIntegrand
              incomingMode
              (fun omega : T4 × U => omega.1)
              postOuter p
            ∂(nu.prod
              (Measure.pi fun _ :
                (data.trace.stopPrefix.afterHead
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                    paperMeasure))) =
        ∫ q : (T4 × U) ×
              (sub.final.SurvivingCoordinate → T4),
          sub.final.incomingPhasedResidualDensity
            (charT4 outgoingMode q.1.1 * reduced q.1.2 q.2)
            incomingMode rho eps 0 q.1.1 q.2
          ∂(nu.prod (Measure.pi fun _ => paperMeasure)) := by
    rw [integral_prod _ hafter, ← integral_const_mul]
    have hterminal' :
        Integrable
          (fun q : (T4 × U) ×
                (sub.final.SurvivingCoordinate → T4) =>
            sub.final.incomingPhasedResidualDensity
              (charT4 outgoingMode q.1.1 * reduced q.1.2 q.2)
              incomingMode rho eps 0 q.1.1 q.2)
          (nu.prod (Measure.pi fun _ => paperMeasure)) := by
      simpa only [nu, reduced] using hterminal
    rw [integral_prod _ hterminal']
    apply integral_congr_ae
    filter_upwards [hafter.prod_right_ae] with omega homega
    have hsection :=
      sub.transport 0 omega.1 incomingMode
        (fun u =>
          (paperSecondOrderModeDecay incomingMode : ℂ) ^ 2 *
            incomingExceptionalPrimitiveDefect rho lam eps
              (residualBlockOrder data.terminal.2)
              data.stopContext.one_le_blockOrder
              data.stopContext.internalEdges incomingMode *
            (charT4 outgoingMode omega.1 * red omega.2 u))
        (by
          simpa only [postOuter,
            incomingExceptionalAfterHeadPhasedIntegrand,
            incomingExceptionalPostCoefficient] using homega)
    calc
      (lamEps lam eps : ℂ) ^
            (2 *
              (data.trace.stopPrefix.afterHead
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq).remainingOrder) *
          (∫ v,
            data.incomingExceptionalAfterHeadPhasedIntegrand
              incomingMode
              (fun omega' : T4 × U => omega'.1)
              postOuter (omega, v)
            ∂Measure.pi fun _ => paperMeasure) =
          ∫ u : sub.final.SurvivingCoordinate → T4,
            sub.final.incomingPhasedResidualDensity
              (sub.multiplier incomingMode *
                ((paperSecondOrderModeDecay incomingMode : ℂ) ^ 2 *
                  incomingExceptionalPrimitiveDefect rho lam eps
                    (residualBlockOrder data.terminal.2)
                    data.stopContext.one_le_blockOrder
                    data.stopContext.internalEdges incomingMode *
                  (charT4 outgoingMode omega.1 * red omega.2 u)))
              incomingMode rho eps 0 omega.1 u
            ∂Measure.pi fun _ => paperMeasure := hsection
      _ = ∫ u : sub.final.SurvivingCoordinate → T4,
            sub.final.incomingPhasedResidualDensity
              (charT4 outgoingMode omega.1 * reduced omega.2 u)
              incomingMode rho eps 0 omega.1 u
            ∂Measure.pi fun _ => paperMeasure := by
          apply integral_congr_ae
          filter_upwards with u
          dsimp only [reduced]
          congr 1
          ring
  have hout :=
    integral_singleParameter_incomingPhasedResidualDensity_eq_directOutgoing
      sub.final sub.final_remaining hactive hedge muU reduced
      outgoingMode incomingMode
      (by simpa only [nu, reduced] using hterminal)
  calc
    (lamEps lam eps : ℂ) ^
          (2 * (R324WithinHalfResidualPrefix.initial
            rho lam eps pairing).remainingOrder) *
        (∫ p,
          data.incomingExceptionalInitialSourceDensity
            incomingMode
            (fun omega : T4 × U => omega.1)
            (fun omega v =>
              charT4 outgoingMode omega.1 *
                red omega.2 (sub.projection v)) p
          ∂((paperMeasure.prod (paperMeasure.prod muU)).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate => paperMeasure))) =
        (lamEps lam eps : ℂ) ^
          (2 * data.trace.stopPrefix.remainingOrder) *
        (∫ p,
          data.incomingExceptionalStopFourierDensity
            incomingMode
            (fun omega : T4 × U => omega.1)
            postOuter p
          ∂(nu.prod
            ((Measure.pi fun _ :
              Fin (2 * residualBlockOrder data.terminal.2) => paperMeasure).prod
            (Measure.pi fun _ :
              (data.trace.stopPrefix.afterHead
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                  paperMeasure)))) := hinitial
    _ = (lamEps lam eps : ℂ) ^
          (2 *
            (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).remainingOrder) *
        (∫ p,
          data.incomingExceptionalAfterHeadPhasedIntegrand
            incomingMode
            (fun omega : T4 × U => omega.1)
            postOuter p
          ∂(nu.prod
            (Measure.pi fun _ :
              (data.trace.stopPrefix.afterHead
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                  paperMeasure))) := hhead
    _ = ∫ q : (T4 × U) ×
            (sub.final.SurvivingCoordinate → T4),
        sub.final.incomingPhasedResidualDensity
          (charT4 outgoingMode q.1.1 * reduced q.1.2 q.2)
          incomingMode rho eps 0 q.1.1 q.2
        ∂(nu.prod (Measure.pi fun _ => paperMeasure)) := htransport
    _ = _ := by
      simpa only [nu, reduced] using hout

/-! ### Pointwise splice of the two exceptional-incoming/direct-outgoing halves -/

/-- The untouched coefficient carried from the completed left half while
the right exceptional incoming endpoint is processed.  It contains the
left incoming defect, both exact left boundary coefficients, and the
still-signed cross-cut primitive product on the two terminal carriers. -/
def incomingExceptionalTwoHalfDirectReducedCoefficient
    {leftScale rightScale : Fin (m + 1) → ℝ}
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftSub :
      R324WithinHalfAlternatingTransport
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM rightScale)
    (rightSub :
      R324WithinHalfAlternatingTransport
        (rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq))
    (hleft : leftSub.final.state.active.Nonempty)
    (alpha beta : Z4) (pi : kappaP.singles ≃ kappaM.singles)
    (u : leftSub.final.SurvivingCoordinate → T4)
    (v : rightSub.final.SurvivingCoordinate → T4) : ℂ :=
  (leftSub.multiplier alpha *
      ((paperSecondOrderModeDecay alpha : ℂ) ^ 2 *
        incomingExceptionalPrimitiveDefect rho lam eps
          (residualBlockOrder leftData.terminal.2)
          leftData.stopContext.one_le_blockOrder
          leftData.stopContext.internalEdges alpha)) *
    charT4 alpha
      (leftSub.final.terminalIncomingAnchor
        (leftSub.final.reconstruct u)) *
    ((leftSub.final.endpointErasedSignedChain
      hleft 0 0 (leftSub.final.reconstruct u) : ℝ) : ℂ) *
    translatedGreenMode beta
      (leftSub.final.terminalOutgoingAnchor hleft
        (leftSub.final.reconstruct u)) *
    (r324ResidualPrimitiveSumProduct
      rho eps kappaP kappaM pi
      (r324TwoHalfRootDoubledReconstruct
        leftSub.final rightSub.final (u, v)) : ℂ)

/-- The signed integrand left by the completed left half is literally the
right half's exceptional-incoming initial source after projecting the
cross factor through the right trace.  This is the paper's two-half splice
before the right endpoint integrations and before any norm. -/
theorem
    incomingExceptionalLeftDirectIntegrand_eq_rightInitialSource
    {leftScale rightScale : Fin (m + 1) → ℝ}
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftSub :
      R324WithinHalfAlternatingTransport
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM rightScale)
    (rightSub :
      R324WithinHalfAlternatingTransport
        (rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq))
    (hleft : leftSub.final.state.active.Nonempty)
    (alpha beta : Z4) (pi : kappaP.singles ≃ kappaM.singles)
    (z w : T4)
    (vr :
      (R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate → T4)
    (u : leftSub.final.SurvivingCoordinate → T4) :
    leftData.incomingExceptionalRefinedRootDriverReducedCoefficient
          leftSub alpha beta pi (z, w) vr u *
        charT4 alpha
          (leftSub.final.terminalIncomingAnchor
            (leftSub.final.reconstruct u)) *
        ((leftSub.final.endpointErasedSignedChain
          hleft 0 0 (leftSub.final.reconstruct u) : ℝ) : ℂ) *
        translatedGreenMode beta
          (leftSub.final.terminalOutgoingAnchor hleft
            (leftSub.final.reconstruct u)) =
      rightData.incomingExceptionalInitialSourceDensity
        (-alpha)
        (fun omega : T4 ×
            (leftSub.final.SurvivingCoordinate → T4) => omega.1)
        (fun omega v =>
          charT4 (-beta) omega.1 *
            incomingExceptionalTwoHalfDirectReducedCoefficient
              leftData leftSub rightData rightSub hleft alpha beta pi
              omega.2 (rightSub.projection v))
        ((z, (w, u)), vr) := by
  have hcross :=
    rightData.r324ResidualPrimitiveSumProduct_eq_rightDriverProjection
      leftSub.final rightSub pi u vr
  unfold incomingExceptionalRefinedRootDriverReducedCoefficient
    incomingExceptionalInitialSourceDensity
    incomingExceptionalTwoHalfDirectReducedCoefficient
  rw [hcross]
  ring

/-- The completed left-half integrand is jointly integrable in the two
right boundary variables, the right initial carrier, and the left terminal
carrier.  This is obtained by marginalizing the left outgoing Fourier
variable from the already available driver-terminal joint integrability. -/
theorem integrable_incomingExceptionalLeftDirectIntegrand
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP initialScale)
    (sub :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (hm : 0 < m) (alpha beta : Z4)
    (pi : kappaP.singles ≃ kappaM.singles)
    (hjoint : data.DriverTerminalJointIntegrable sub alpha beta pi)
    (hactive : sub.final.state.active.Nonempty)
    (hdirect : r324OutgoingIsShortcut kappaP = false) :
    Integrable
      (fun q :
          (((T4 × T4) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).SurvivingCoordinate → T4)) ×
            (sub.final.SurvivingCoordinate → T4)) =>
        data.incomingExceptionalRefinedRootDriverReducedCoefficient
            sub alpha beta pi q.1.1 q.1.2 q.2 *
          charT4 alpha
            (sub.final.terminalIncomingAnchor
              (sub.final.reconstruct q.2)) *
          ((sub.final.endpointErasedSignedChain
            hactive 0 0 (sub.final.reconstruct q.2) : ℝ) : ℂ) *
          translatedGreenMode beta
            (sub.final.terminalOutgoingAnchor hactive
              (sub.final.reconstruct q.2)))
      ((((paperMeasure.prod paperMeasure).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps kappaM).SurvivingCoordinate => paperMeasure)).prod
        (Measure.pi fun _ : sub.final.SurvivingCoordinate =>
          paperMeasure))) := by
  let muRight :=
    Measure.pi fun _ :
      (R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate => paperMeasure
  let muParam := (paperMeasure.prod paperMeasure).prod muRight
  have hedge :
      sub.final.state.edges
          (sub.final.terminalOutgoingEdgeSlot hactive) = greenFn :=
    sub.final.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_not_shortcut
      hm sub.final_processed_eq_schedule hdirect hactive
  have hstripped :
      Integrable
        (fun q :
            (T4 ×
              ((T4 × T4) ×
                ((R324WithinHalfResidualPrefix.initial
                  rho lam eps kappaM).SurvivingCoordinate → T4))) ×
              (sub.final.SurvivingCoordinate → T4) =>
          sub.final.incomingPhasedResidualDensity
            (charT4 beta q.1.1 *
              data.incomingExceptionalRefinedRootDriverReducedCoefficient
                sub alpha beta pi q.1.2.1 q.1.2.2 q.2)
            alpha rho eps 0 q.1.1 q.2)
        ((paperMeasure.prod muParam).prod
          (Measure.pi fun _ => paperMeasure)) := by
    unfold DriverTerminalJointIntegrable at hjoint
    unfold r324IncomingExceptionalRootParameterMeasure at hjoint
    let assoc :
        (((T4 × (T4 × T4)) ×
            ((R324WithinHalfResidualPrefix.initial
              rho lam eps kappaM).SurvivingCoordinate → T4)) ×
          (sub.final.SurvivingCoordinate → T4)) ≃ᵐ
        ((T4 ×
            ((T4 × T4) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).SurvivingCoordinate → T4))) ×
          (sub.final.SurvivingCoordinate → T4)) :=
      MeasurableEquiv.prodCongr
        (MeasurableEquiv.prodAssoc
          (α := T4) (β := T4 × T4)
          (γ :=
            (R324WithinHalfResidualPrefix.initial
              rho lam eps kappaM).SurvivingCoordinate → T4))
        (MeasurableEquiv.refl
          (sub.final.SurvivingCoordinate → T4))
    have hassoc :
        MeasurePreserving assoc
          (((paperMeasure.prod (paperMeasure.prod paperMeasure)).prod
              muRight).prod
            (Measure.pi fun _ : sub.final.SurvivingCoordinate =>
              paperMeasure))
          ((paperMeasure.prod muParam).prod
            (Measure.pi fun _ : sub.final.SurvivingCoordinate =>
              paperMeasure)) := by
      dsimp only [assoc, muParam]
      exact
        (measurePreserving_prodAssoc paperMeasure
          (paperMeasure.prod paperMeasure) muRight).prod
            (MeasurePreserving.id
              (Measure.pi fun _ : sub.final.SurvivingCoordinate =>
                paperMeasure))
    refine (hassoc.integrable_comp_emb assoc.measurableEmbedding).mp ?_
    apply hjoint.congr
    filter_upwards with q
    show
      sub.final.incomingPhasedResidualDensity
          (sub.multiplier alpha *
            data.incomingExceptionalRefinedRootDriverCoefficient
              sub alpha beta pi q.1 q.2)
          alpha rho eps 0 q.1.1.1 q.2 = _
    rw [data.multiplier_mul_driverCoefficient_eq_char_mul_reduced
      sub alpha beta pi q.1 q.2]
    rfl
  simpa only [muParam, muRight] using
    (integrable_singleParameter_directOutgoingResult
      sub.final sub.final_remaining hactive hedge muParam
      (fun s u =>
        data.incomingExceptionalRefinedRootDriverReducedCoefficient
          sub alpha beta pi s.1 s.2 u)
      beta alpha hstripped)

/-- A terminal half with both boundary Green legs direct has an integrable
two-endpoint Fourier coefficient after the outgoing variable is evaluated.
The proof is the terminal-certificate `L1` theorem followed by the exact
Fourier identity, so it introduces no majorant into the signed chain. -/
theorem integrable_terminalDirectBoundaryCoefficient
    {pairing : PartialPairing (Fin m)}
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (hnil : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (hedge :
      res.state.edges (res.terminalOutgoingEdgeSlot hactive) = greenFn)
    (scale : Fin (m + 1) → ℝ)
    (hcert : R324WithinHalfEdgeCertificate res.state scale)
    (incomingMode outgoingMode : Z4) :
    Integrable
      (fun u : res.SurvivingCoordinate → T4 =>
        charT4 incomingMode
            (res.terminalIncomingAnchor (res.reconstruct u)) *
          ((res.endpointErasedSignedChain
            hactive 0 0 (res.reconstruct u) : ℝ) : ℂ) *
          translatedGreenMode outgoingMode
            (res.terminalOutgoingAnchor hactive
              (res.reconstruct u)))
      (Measure.pi fun _ => paperMeasure) := by
  have hrawReal :=
    res.integrable_terminal_incomingErasedResidualIntegrand
      hnil rho eps scale hcert
  have hraw :
      Integrable
        (fun p : T4 × (res.SurvivingCoordinate → T4) =>
          ((res.incomingErasedResidualIntegrand
            rho eps 0 p.1 (res.reconstruct p.2) : ℝ) : ℂ))
        (paperMeasure.prod (Measure.pi fun _ => paperMeasure)) :=
    hrawReal.ofReal
  let phase : T4 × (res.SurvivingCoordinate → T4) → ℂ :=
    fun p =>
      charT4 outgoingMode p.1 *
        charT4 incomingMode (res.incomingPhaseAnchor 0 p.1 p.2)
  have hyMeas :
      Measurable
        (fun p : T4 × (res.SurvivingCoordinate → T4) => p.1) :=
    measurable_fst
  have hanchorMeas :
      Measurable
        (fun p : T4 × (res.SurvivingCoordinate → T4) =>
          res.incomingPhaseAnchor 0 p.1 p.2) := by
    have hassembleMeas :
        Measurable
          (fun p : T4 × (res.SurvivingCoordinate → T4) =>
            assemble (0 : T4) p.1 (res.reconstruct p.2)) :=
      (measurable_assemble_prod m).comp
        (measurable_const.prodMk
          (measurable_fst.prodMk
            (res.measurable_reconstruct.comp measurable_snd)))
    exact
      (measurable_pi_apply (res.edgeSuccessor 0)).comp hassembleMeas
  have hphaseMeas : Measurable phase :=
    (continuous_charT4 outgoingMode).measurable.comp hyMeas |>.mul
      ((continuous_charT4 incomingMode).measurable.comp hanchorMeas)
  have hphaseBound : ∀ p, ‖phase p‖ ≤ 1 := by
    intro p
    unfold phase
    rw [norm_mul, norm_charT4, norm_charT4]
    norm_num
  have hpre :
      Integrable
        (fun p : T4 × (res.SurvivingCoordinate → T4) =>
          charT4 outgoingMode p.1 *
            res.incomingPhasedResidualDensity
              1 incomingMode rho eps 0 p.1 p.2)
        (paperMeasure.prod (Measure.pi fun _ => paperMeasure)) := by
    have h :=
      hraw.bdd_mul hphaseMeas.aestronglyMeasurable
        (Filter.Eventually.of_forall hphaseBound)
    apply h.congr
    filter_upwards with p
    unfold phase R324WithinHalfResidualPrefix.incomingPhasedResidualDensity
    ring
  have hmarg := hpre.integral_prod_right
  apply hmarg.congr
  filter_upwards with u
  exact
    (res.integral_char_mul_terminal_incomingPhasedResidualDensity_eq
      hnil hactive hedge 1 incomingMode outgoingMode rho eps 0 u).trans
      (by ring)

/-- Terminal joint integrability for the two-half
exceptional-incoming/direct-outgoing splice.  A certificate gives `L1` for
each completed half-chain; the cross primitive factor is bounded and
measurable.  Hence the only remaining factors are unimodular characters
and constant primitive defects. -/
theorem
    integrable_twoIncomingExceptional_twoDirectTerminal_of_certificates
    {leftScale rightScale : Fin (m + 1) → ℝ}
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftSub :
      R324WithinHalfAlternatingTransport
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM rightScale)
    (rightSub :
      R324WithinHalfAlternatingTransport
        (rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq))
    (hm : 0 < m) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hleft : leftSub.final.state.active.Nonempty)
    (hleftDirect : r324OutgoingIsShortcut kappaP = false)
    (leftFinalScale rightFinalScale : Fin (m + 1) → ℝ)
    (hleftCert :
      R324WithinHalfEdgeCertificate leftSub.final.state leftFinalScale)
    (hrightCert :
      R324WithinHalfEdgeCertificate rightSub.final.state rightFinalScale)
    (alpha beta : Z4) (pi : kappaP.singles ≃ kappaM.singles) :
    let red :=
      incomingExceptionalTwoHalfDirectReducedCoefficient
        leftData leftSub rightData rightSub hleft alpha beta pi
    Integrable
      (fun q :
          (T4 × (leftSub.final.SurvivingCoordinate → T4)) ×
            (rightSub.final.SurvivingCoordinate → T4) =>
        rightSub.final.incomingPhasedResidualDensity
          (charT4 (-beta) q.1.1 *
            (rightSub.multiplier (-alpha) *
              ((paperSecondOrderModeDecay (-alpha) : ℂ) ^ 2 *
                incomingExceptionalPrimitiveDefect rho lam eps
                  (residualBlockOrder rightData.terminal.2)
                  rightData.stopContext.one_le_blockOrder
                  rightData.stopContext.internalEdges (-alpha) *
                red q.1.2 q.2)))
          (-alpha) rho eps 0 q.1.1 q.2)
      ((paperMeasure.prod
          (Measure.pi fun _ : leftSub.final.SurvivingCoordinate =>
            paperMeasure)).prod
        (Measure.pi fun _ : rightSub.final.SurvivingCoordinate =>
          paperMeasure)) := by
  dsimp only
  let muLeft :=
    Measure.pi fun _ : leftSub.final.SurvivingCoordinate => paperMeasure
  let muRight :=
    Measure.pi fun _ : rightSub.final.SurvivingCoordinate => paperMeasure
  have hleftEdge :
      leftSub.final.state.edges
          (leftSub.final.terminalOutgoingEdgeSlot hleft) = greenFn :=
    leftSub.final.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_not_shortcut
      hm leftSub.final_processed_eq_schedule hleftDirect hleft
  let leftBoundary :
      (leftSub.final.SurvivingCoordinate → T4) → ℂ :=
    fun u =>
      charT4 alpha
          (leftSub.final.terminalIncomingAnchor
            (leftSub.final.reconstruct u)) *
        ((leftSub.final.endpointErasedSignedChain
          hleft 0 0 (leftSub.final.reconstruct u) : ℝ) : ℂ) *
        translatedGreenMode beta
          (leftSub.final.terminalOutgoingAnchor hleft
            (leftSub.final.reconstruct u))
  have hleftBoundary : Integrable leftBoundary muLeft := by
    exact integrable_terminalDirectBoundaryCoefficient
      leftSub.final
      leftSub.final_remaining hleft hleftEdge leftFinalScale hleftCert
      alpha beta
  have hrightRawReal :=
    rightSub.final.integrable_terminal_incomingErasedResidualIntegrand
      rightSub.final_remaining rho eps rightFinalScale hrightCert
  have hsource :
      Integrable
        (fun p :
            (leftSub.final.SurvivingCoordinate → T4) ×
              (T4 × (rightSub.final.SurvivingCoordinate → T4)) =>
          leftBoundary p.1 *
            ((rightSub.final.incomingErasedResidualIntegrand
              rho eps 0 p.2.1
              (rightSub.final.reconstruct p.2.2) : ℝ) : ℂ))
        (muLeft.prod (paperMeasure.prod muRight)) :=
    hleftBoundary.mul_prod hrightRawReal.ofReal
  let e :=
    r324SingleParameterTerminalRegroupMeasurableEquiv
      T4
      (leftSub.final.SurvivingCoordinate → T4)
      (rightSub.final.SurvivingCoordinate → T4)
  have hp :
      MeasurePreserving e
        ((paperMeasure.prod muLeft).prod muRight)
        (muLeft.prod (paperMeasure.prod muRight)) :=
    measurePreserving_r324SingleParameterTerminalRegroupMeasurableEquiv
      paperMeasure muLeft muRight
  have hbare :
      Integrable
        (fun q :
            (T4 × (leftSub.final.SurvivingCoordinate → T4)) ×
              (rightSub.final.SurvivingCoordinate → T4) =>
          leftBoundary (e q).1 *
            ((rightSub.final.incomingErasedResidualIntegrand
              rho eps 0 (e q).2.1
              (rightSub.final.reconstruct (e q).2.2) : ℝ) : ℂ))
        ((paperMeasure.prod muLeft).prod muRight) :=
    (hp.integrable_comp_emb e.measurableEmbedding).mpr hsource
  let cross :
      ((T4 × (leftSub.final.SurvivingCoordinate → T4)) ×
        (rightSub.final.SurvivingCoordinate → T4)) → ℂ :=
    fun q =>
      (r324ResidualPrimitiveSumProduct
        rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          leftSub.final rightSub.final (q.1.2, q.2)) : ℂ)
  have hcrossMeas : Measurable cross := by
    apply Complex.measurable_ofReal.comp
    apply (rho.measurable_r324ResidualPrimitiveSumProduct
      eps kappaP kappaM pi).comp
    apply (measurable_r324TwoHalfRootDoubledReconstruct
      leftSub.final rightSub.final).comp
    exact (measurable_snd.comp measurable_fst).prodMk measurable_snd
  obtain ⟨Bcross, _hBcross, hcrossBound⟩ :=
    rho.exists_norm_r324ResidualPrimitiveSumProduct_le
      heps heps1 kappaP kappaM pi
  have hwithCross :=
    hbare.mul_bdd hcrossMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by
        simpa only [cross, Complex.norm_real] using
          hcrossBound
            (r324TwoHalfRootDoubledReconstruct
              leftSub.final rightSub.final (q.1.2, q.2)))
  let leftConstant : ℂ :=
    leftSub.multiplier alpha *
      ((paperSecondOrderModeDecay alpha : ℂ) ^ 2 *
        incomingExceptionalPrimitiveDefect rho lam eps
          (residualBlockOrder leftData.terminal.2)
          leftData.stopContext.one_le_blockOrder
          leftData.stopContext.internalEdges alpha)
  let rightConstant : ℂ :=
    rightSub.multiplier (-alpha) *
      ((paperSecondOrderModeDecay (-alpha) : ℂ) ^ 2 *
        incomingExceptionalPrimitiveDefect rho lam eps
          (residualBlockOrder rightData.terminal.2)
          rightData.stopContext.one_le_blockOrder
          rightData.stopContext.internalEdges (-alpha))
  let phase :
      ((T4 × (leftSub.final.SurvivingCoordinate → T4)) ×
        (rightSub.final.SurvivingCoordinate → T4)) → ℂ :=
    fun q =>
      rightConstant * leftConstant *
        (charT4 (-beta) q.1.1 *
          charT4 (-alpha)
            (rightSub.final.incomingPhaseAnchor 0 q.1.1 q.2))
  have hyMeas :
      Measurable
        (fun q :
            (T4 × (leftSub.final.SurvivingCoordinate → T4)) ×
              (rightSub.final.SurvivingCoordinate → T4) => q.1.1) :=
    measurable_fst.comp measurable_fst
  have hanchorMeas :
      Measurable
        (fun q :
            (T4 × (leftSub.final.SurvivingCoordinate → T4)) ×
              (rightSub.final.SurvivingCoordinate → T4) =>
          rightSub.final.incomingPhaseAnchor 0 q.1.1 q.2) := by
    have hassembleMeas :
        Measurable
          (fun q :
              (T4 × (leftSub.final.SurvivingCoordinate → T4)) ×
                (rightSub.final.SurvivingCoordinate → T4) =>
            assemble (0 : T4) q.1.1
              (rightSub.final.reconstruct q.2)) :=
      (measurable_assemble_prod m).comp
        (measurable_const.prodMk
          (hyMeas.prodMk
            (rightSub.final.measurable_reconstruct.comp measurable_snd)))
    exact
      (measurable_pi_apply
        (rightSub.final.edgeSuccessor 0)).comp hassembleMeas
  have hphaseMeas : Measurable phase := by
    unfold phase
    exact measurable_const.mul
      (((continuous_charT4 (-beta)).measurable.comp hyMeas).mul
        ((continuous_charT4 (-alpha)).measurable.comp hanchorMeas))
  have hphaseBound :
      ∀ q, ‖phase q‖ ≤ ‖rightConstant * leftConstant‖ := by
    intro q
    unfold phase
    simp only [norm_mul, norm_charT4, mul_one]
    exact le_rfl
  have hfull :=
    hwithCross.bdd_mul hphaseMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hphaseBound)
  apply hfull.congr
  filter_upwards with q
  unfold R324WithinHalfResidualPrefix.incomingPhasedResidualDensity
    incomingExceptionalTwoHalfDirectReducedCoefficient
    leftBoundary cross phase leftConstant rightConstant
  rw [r324SingleParameterTerminalRegroupMeasurableEquiv_apply]
  ring

/-- Regrouping the completed left half produces exactly the right half's
exceptional initial source, and transports integrability with it. -/
theorem
    integrable_and_integral_leftDirect_eq_rightExceptionalInitialSource
    {leftScale rightScale : Fin (m + 1) → ℝ}
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftSub :
      R324WithinHalfAlternatingTransport
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM rightScale)
    (rightSub :
      R324WithinHalfAlternatingTransport
        (rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq))
    (hleft : leftSub.final.state.active.Nonempty)
    (alpha beta : Z4) (pi : kappaP.singles ≃ kappaM.singles)
    (hleftIntegrable :
      Integrable
        (fun q :
            (((T4 × T4) ×
                ((R324WithinHalfResidualPrefix.initial
                  rho lam eps kappaM).SurvivingCoordinate → T4)) ×
              (leftSub.final.SurvivingCoordinate → T4)) =>
          leftData.incomingExceptionalRefinedRootDriverReducedCoefficient
              leftSub alpha beta pi q.1.1 q.1.2 q.2 *
            charT4 alpha
              (leftSub.final.terminalIncomingAnchor
                (leftSub.final.reconstruct q.2)) *
            ((leftSub.final.endpointErasedSignedChain
              hleft 0 0 (leftSub.final.reconstruct q.2) : ℝ) : ℂ) *
            translatedGreenMode beta
              (leftSub.final.terminalOutgoingAnchor hleft
                (leftSub.final.reconstruct q.2)))
        ((((paperMeasure.prod paperMeasure).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).SurvivingCoordinate => paperMeasure)).prod
          (Measure.pi fun _ : leftSub.final.SurvivingCoordinate =>
            paperMeasure)))) :
    let red :=
      incomingExceptionalTwoHalfDirectReducedCoefficient
        leftData leftSub rightData rightSub hleft alpha beta pi
    Integrable
        (rightData.incomingExceptionalInitialSourceDensity
          (-alpha)
          (fun omega : T4 ×
              (leftSub.final.SurvivingCoordinate → T4) => omega.1)
          (fun omega v =>
            charT4 (-beta) omega.1 *
              red omega.2 (rightSub.projection v)))
        ((paperMeasure.prod
            (paperMeasure.prod
              (Measure.pi fun _ : leftSub.final.SurvivingCoordinate =>
                paperMeasure))).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps kappaM).SurvivingCoordinate => paperMeasure)) ∧
      (∫ s :
          (T4 × T4) ×
            ((R324WithinHalfResidualPrefix.initial
              rho lam eps kappaM).SurvivingCoordinate → T4),
        ∫ u : leftSub.final.SurvivingCoordinate → T4,
          leftData.incomingExceptionalRefinedRootDriverReducedCoefficient
              leftSub alpha beta pi s.1 s.2 u *
            charT4 alpha
              (leftSub.final.terminalIncomingAnchor
                (leftSub.final.reconstruct u)) *
            ((leftSub.final.endpointErasedSignedChain
              hleft 0 0 (leftSub.final.reconstruct u) : ℝ) : ℂ) *
            translatedGreenMode beta
              (leftSub.final.terminalOutgoingAnchor hleft
                (leftSub.final.reconstruct u))
          ∂Measure.pi fun _ => paperMeasure
        ∂((paperMeasure.prod paperMeasure).prod
          (Measure.pi fun _ => paperMeasure))) =
        ∫ p,
          rightData.incomingExceptionalInitialSourceDensity
            (-alpha)
            (fun omega : T4 ×
                (leftSub.final.SurvivingCoordinate → T4) => omega.1)
            (fun omega v =>
              charT4 (-beta) omega.1 *
                red omega.2 (rightSub.projection v)) p
          ∂((paperMeasure.prod
              (paperMeasure.prod
                (Measure.pi fun _ : leftSub.final.SurvivingCoordinate =>
                  paperMeasure))).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).SurvivingCoordinate => paperMeasure)) := by
  dsimp only
  let muRight :=
    Measure.pi fun _ :
      (R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate => paperMeasure
  let muLeft :=
    Measure.pi fun _ : leftSub.final.SurvivingCoordinate => paperMeasure
  let muOuter := (paperMeasure.prod paperMeasure).prod muRight
  let leftF :
      (((T4 × T4) ×
          ((R324WithinHalfResidualPrefix.initial
            rho lam eps kappaM).SurvivingCoordinate → T4)) ×
        (leftSub.final.SurvivingCoordinate → T4)) → ℂ :=
    fun q =>
      leftData.incomingExceptionalRefinedRootDriverReducedCoefficient
          leftSub alpha beta pi q.1.1 q.1.2 q.2 *
        charT4 alpha
          (leftSub.final.terminalIncomingAnchor
            (leftSub.final.reconstruct q.2)) *
        ((leftSub.final.endpointErasedSignedChain
          hleft 0 0 (leftSub.final.reconstruct q.2) : ℝ) : ℂ) *
        translatedGreenMode beta
          (leftSub.final.terminalOutgoingAnchor hleft
            (leftSub.final.reconstruct q.2))
  let red :=
    incomingExceptionalTwoHalfDirectReducedCoefficient
      leftData leftSub rightData rightSub hleft alpha beta pi
  let rightF :
      ((T4 × (T4 ×
          (leftSub.final.SurvivingCoordinate → T4))) ×
        ((R324WithinHalfResidualPrefix.initial
          rho lam eps kappaM).SurvivingCoordinate → T4)) → ℂ :=
    fun p =>
      rightData.incomingExceptionalInitialSourceDensity
        (-alpha)
        (fun omega : T4 ×
            (leftSub.final.SurvivingCoordinate → T4) => omega.1)
        (fun omega v =>
          charT4 (-beta) omega.1 *
            red omega.2 (rightSub.projection v)) p
  let sigma :=
    r324TwoHalfRightInitialSourceRegroupMeasurableEquiv
      T4 T4
      ((R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate → T4)
      (leftSub.final.SurvivingCoordinate → T4)
  have hsigma :
      MeasurePreserving sigma
        (muOuter.prod muLeft)
        ((paperMeasure.prod (paperMeasure.prod muLeft)).prod muRight) :=
    measurePreserving_r324TwoHalfRightInitialSourceRegroupMeasurableEquiv
      paperMeasure paperMeasure muRight muLeft
  have hpoint : ∀ q, leftF q = rightF (sigma q) := by
    intro q
    exact
      leftData.incomingExceptionalLeftDirectIntegrand_eq_rightInitialSource
        leftSub rightData rightSub hleft alpha beta pi
        q.1.1.1 q.1.1.2 q.1.2 q.2
  have hright :
      Integrable rightF
        ((paperMeasure.prod (paperMeasure.prod muLeft)).prod muRight) := by
    refine (hsigma.integrable_comp_emb sigma.measurableEmbedding).mp ?_
    apply hleftIntegrable.congr
    filter_upwards with q
    exact hpoint q
  refine ⟨hright, ?_⟩
  change (∫ s, ∫ u, leftF (s, u) ∂muLeft ∂muOuter) =
    ∫ p, rightF p
      ∂((paperMeasure.prod (paperMeasure.prod muLeft)).prod muRight)
  rw [← integral_prod _ hleftIntegrable]
  rw [← hsigma.integral_comp' rightF]
  exact integral_congr_ae
    (Filter.Eventually.of_forall hpoint)

/-- Exact two-half paper splice when both incoming endpoints are paired
exceptional heads and both outgoing endpoints are direct Green legs.  The
left half is removed first, its terminal coordinate becomes an untouched
parameter of the right trace, and the right half is then removed with
modes `-alpha,-beta`.  No norm occurs in the statement or proof. -/
theorem
    lamEps_pow_r324RefinedPhysicalIntegral_eq_twoIncomingExceptional_twoDirectOutgoing
    (p : R324RefinedScheduleIndex m)
    (e0 : MomentContraction m)
    (he0 : e0 ∈ momentRefinedContractionFiber m p.1.1 p.2.1)
    {leftScale rightScale : Fin (m + 1) → ℝ}
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) e0.1 leftScale)
    (leftSub :
      R324WithinHalfAlternatingTransport
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) e0.2.1 rightScale)
    (rightSub :
      R324WithinHalfAlternatingTransport
        (rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq))
    (hm : 0 < m) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hleftG : ∀ j, MemEClassT4 (leftData.stopContext.internalEdges j))
    (hleftHint :
      ∀ (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder leftData.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder leftData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder leftData.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder leftData.terminal.2)
              kappaB.1 leftData.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder leftData.terminal.2)
                leftData.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hrightG : ∀ j, MemEClassT4 (rightData.stopContext.internalEdges j))
    (hrightHint :
      ∀ (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder rightData.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder rightData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder rightData.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder rightData.terminal.2)
              kappaB.1 rightData.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder rightData.terminal.2)
                rightData.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (alpha beta : Z4)
    (hleftActive : leftSub.final.state.active.Nonempty)
    (hleftDirect : r324OutgoingIsShortcut e0.1 = false)
    (hrightActive : rightSub.final.state.active.Nonempty)
    (hrightDirect : r324OutgoingIsShortcut e0.2.1 = false)
    (leftFinalScale rightFinalScale : Fin (m + 1) → ℝ)
    (hleftCert :
      R324WithinHalfEdgeCertificate leftSub.final.state leftFinalScale)
    (hrightCert :
      R324WithinHalfEdgeCertificate rightSub.final.state rightFinalScale) :
    let red :=
      incomingExceptionalTwoHalfDirectReducedCoefficient
        leftData leftSub rightData rightSub hleftActive
        alpha beta e0.2.2
    (lamEps lam eps : ℂ) ^
          (2 *
            ((R324WithinHalfResidualPrefix.initial
                rho lam eps e0.1).remainingOrder +
              (R324WithinHalfResidualPrefix.initial
                rho lam eps e0.2.1).remainingOrder)) *
        r324RefinedPhysicalIntegral rho eps m alpha beta p =
      ∫ u : leftSub.final.SurvivingCoordinate → T4,
        ∫ v : rightSub.final.SurvivingCoordinate → T4,
          (rightSub.multiplier (-alpha) *
              ((paperSecondOrderModeDecay (-alpha) : ℂ) ^ 2 *
                incomingExceptionalPrimitiveDefect rho lam eps
                  (residualBlockOrder rightData.terminal.2)
                  rightData.stopContext.one_le_blockOrder
                  rightData.stopContext.internalEdges (-alpha) *
                red u v)) *
            charT4 (-alpha)
              (rightSub.final.terminalIncomingAnchor
                (rightSub.final.reconstruct v)) *
            ((rightSub.final.endpointErasedSignedChain
              hrightActive 0 0
              (rightSub.final.reconstruct v) : ℝ) : ℂ) *
            translatedGreenMode (-beta)
              (rightSub.final.terminalOutgoingAnchor hrightActive
                (rightSub.final.reconstruct v))
          ∂Measure.pi fun _ => paperMeasure
        ∂Measure.pi fun _ => paperMeasure := by
  dsimp only
  let red :=
    incomingExceptionalTwoHalfDirectReducedCoefficient
      leftData leftSub rightData rightSub hleftActive
      alpha beta e0.2.2
  have hleftJoint :
      leftData.DriverTerminalJointIntegrable
        leftSub alpha beta e0.2.2 :=
    leftData.driverTerminalJointIntegrable_of_terminal_certificate
      leftSub alpha beta e0.2.2 heps heps1
      leftFinalScale hleftCert
  have hrightTerminal :=
    integrable_twoIncomingExceptional_twoDirectTerminal_of_certificates
      leftData leftSub rightData rightSub hm heps heps1
      hleftActive hleftDirect leftFinalScale rightFinalScale
      hleftCert hrightCert alpha beta e0.2.2
  have hleftEq :=
    leftData.lamEps_pow_r324RefinedPhysicalIntegral_eq_incomingExceptional_directOutgoing
      p e0 he0 leftSub hm heps heps1 hleftG hleftHint alpha beta
      hleftJoint hleftActive hleftDirect
  have hleftIntegrable :=
    leftData.integrable_incomingExceptionalLeftDirectIntegrand
      leftSub hm alpha beta e0.2.2 hleftJoint
      hleftActive hleftDirect
  obtain ⟨hrightCurrent, hregroup⟩ :=
    leftData.integrable_and_integral_leftDirect_eq_rightExceptionalInitialSource
      leftSub rightData rightSub hleftActive alpha beta e0.2.2
      hleftIntegrable
  have hrightSource :=
    rightData.integrable_incomingExceptionalStopSourceDensity_of_initial
      (paperMeasure.prod
        (Measure.pi fun _ : leftSub.final.SurvivingCoordinate =>
          paperMeasure))
      (-alpha)
      (fun omega : T4 ×
          (leftSub.final.SurvivingCoordinate → T4) => omega.1)
      (fun omega v =>
        charT4 (-beta) omega.1 *
          red omega.2 (rightSub.projection v))
      hrightCurrent
  have hrightEdge :
      rightSub.final.state.edges
          (rightSub.final.terminalOutgoingEdgeSlot hrightActive) =
        greenFn :=
    rightSub.final.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_not_shortcut
      hm rightSub.final_processed_eq_schedule hrightDirect hrightActive
  have hrightEq :=
    rightData.lamEps_pow_integral_initialResidual_eq_singleParameter_incomingExceptional_directOutgoing
      rightSub
      (Measure.pi fun _ : leftSub.final.SurvivingCoordinate => paperMeasure)
      red (-alpha) (-beta) hm hrightG hrightHint
      hrightCurrent hrightSource hrightActive hrightEdge hrightTerminal
  let leftOrder :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps e0.1).remainingOrder
  let rightOrder :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps e0.2.1).remainingOrder
  calc
    (lamEps lam eps : ℂ) ^ (2 * (leftOrder + rightOrder)) *
          r324RefinedPhysicalIntegral rho eps m alpha beta p =
        (lamEps lam eps : ℂ) ^ (2 * rightOrder) *
          ((lamEps lam eps : ℂ) ^ (2 * leftOrder) *
            r324RefinedPhysicalIntegral rho eps m alpha beta p) := by
      rw [Nat.mul_add, pow_add]
      ring
    _ = (lamEps lam eps : ℂ) ^ (2 * rightOrder) *
        (∫ s :
            (T4 × T4) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps e0.2.1).SurvivingCoordinate → T4),
          ∫ u : leftSub.final.SurvivingCoordinate → T4,
            leftData.incomingExceptionalRefinedRootDriverReducedCoefficient
                leftSub alpha beta e0.2.2 s.1 s.2 u *
              charT4 alpha
                (leftSub.final.terminalIncomingAnchor
                  (leftSub.final.reconstruct u)) *
              ((leftSub.final.endpointErasedSignedChain
                hleftActive 0 0
                (leftSub.final.reconstruct u) : ℝ) : ℂ) *
              translatedGreenMode beta
                (leftSub.final.terminalOutgoingAnchor hleftActive
                  (leftSub.final.reconstruct u))
            ∂Measure.pi fun _ => paperMeasure
          ∂((paperMeasure.prod paperMeasure).prod
            (Measure.pi fun _ => paperMeasure))) := by
      rw [hleftEq]
    _ = (lamEps lam eps : ℂ) ^ (2 * rightOrder) *
        (∫ p,
          rightData.incomingExceptionalInitialSourceDensity
            (-alpha)
            (fun omega : T4 ×
                (leftSub.final.SurvivingCoordinate → T4) => omega.1)
            (fun omega v =>
              charT4 (-beta) omega.1 *
                red omega.2 (rightSub.projection v)) p
          ∂((paperMeasure.prod
              (paperMeasure.prod
                (Measure.pi fun _ : leftSub.final.SurvivingCoordinate =>
                  paperMeasure))).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps e0.2.1).SurvivingCoordinate =>
                  paperMeasure))) := by
      rw [hregroup]
    _ = _ := hrightEq

end R324IncomingExceptionalStopTraceAssembly
end R324WithinHalfResidualPrefix

/-! ## The actual refined-root endpoint cases -/

/-- At positive order, the four entries of the canonical endpoint pattern
are exactly the four tests appearing in paper Step 4(A): survival of the
incoming internal vertex, and absence of an extracted outgoing chain edge,
on the left and right halves respectively.  Thus `directFourier` means that
the external Green leg is integrated directly; its complementary case is
the ordinary-`J` sacrifice.

This is a definitional classification only.  It contains no estimate and,
in particular, introduces no modulus before the signed removals. -/
theorem r324RefinedEndpointReductionCase_direct_iff
    {m : ℕ} (hm : 0 < m) (p : R324RefinedScheduleIndex m) :
    (r324RefinedEndpointReductionCase p 0 =
        R324EndpointReductionCase.directFourier ↔
      (⟨0, hm⟩ : Fin m) ∈
        finalActive (r324RefinedScheduleRepresentative p).1) ∧
    (r324RefinedEndpointReductionCase p 1 =
        R324EndpointReductionCase.directFourier ↔
      Fin.last m ∉
        extractedRightEdges (r324RefinedScheduleRepresentative p).1) ∧
    (r324RefinedEndpointReductionCase p 2 =
        R324EndpointReductionCase.directFourier ↔
      (⟨0, hm⟩ : Fin m) ∈
        finalActive (r324RefinedScheduleRepresentative p).2.1) ∧
    (r324RefinedEndpointReductionCase p 3 =
        R324EndpointReductionCase.directFourier ↔
      Fin.last m ∉
        extractedRightEdges
          (r324RefinedScheduleRepresentative p).2.1) := by
  by_cases hleft :
      Fin.last m ∈
        extractedRightEdges (r324RefinedScheduleRepresentative p).1 <;>
    by_cases hright :
      Fin.last m ∈
        extractedRightEdges
          (r324RefinedScheduleRepresentative p).2.1 <;>
    simp [r324RefinedEndpointReductionCase,
      r324IncomingEndpointReductionCase, hm,
      r324OutgoingIsShortcut, r324EndpointReductionCaseOfFlag,
      hleft, hright]

/-- The actual refined schedule has precisely the paper's branch split:
either every contraction in the fibre is full/full (Step 1), or the
representative has a residual single and each of its four external
endpoints is one of the two Step-4(A) cases.  The latter is recorded through
the canonical case pattern, so downstream code can eliminate the sixteen
combinations without inventing a separate routing interface. -/
theorem r324RefinedSchedule_step4A_caseClassification
    {m : ℕ} (p : R324RefinedScheduleIndex m) :
    (∀ e ∈ momentRefinedContractionFiber m p.1.1 p.2.1,
        e.1.IsFull ∧ e.2.1.IsFull) ∨
      ((r324RefinedScheduleRepresentative p).1.singles.Nonempty ∧
        ∀ j : Fin 4,
          r324RefinedEndpointReductionCase p j =
              R324EndpointReductionCase.directFourier ∨
            r324RefinedEndpointReductionCase p j =
              R324EndpointReductionCase.insertedSacrifice) := by
  rcases r324RefinedSchedule_branchDichotomy p with hresidual | hfull
  · right
    refine ⟨hresidual, ?_⟩
    intro j
    cases hcase : r324RefinedEndpointReductionCase p j <;> simp
  · exact Or.inl hfull

/-- A full within-half pairing necessarily removes the outgoing chain edge.
This is the right-endpoint half of the fact that every external endpoint is
in the ordinary-`J` branch of paper Step 1. -/
theorem last_mem_extractedRightEdges_of_isFull
    {m : ℕ} (hm : 0 < m) (pairing : PartialPairing (Fin m))
    (hfull : pairing.IsFull) :
    Fin.last m ∈ extractedRightEdges pairing := by
  obtain ⟨terminal⟩ :=
    exists_r324FullPairingTerminalSchedule (m := m) hm pairing hfull
  have hterminalMem :
      terminal.terminal ∈ r322AnalyticSchedule pairing := by
    rw [terminal.schedule_eq]
    simp
  have hterminalExtract : terminal.terminal.1 ∈ extract pairing :=
    r322AnalyticSchedule_endpoint_mem_extract pairing hterminalMem
  have hedge :
      extractedRightEdge terminal.terminal.1 ∈
        extractedRightEdges pairing :=
    extractedRightEdge_mem_extractedRightEdges
      pairing terminal.terminal.1 hterminalExtract
  have hedgeLast :
      extractedRightEdge terminal.terminal.1 = Fin.last m := by
    apply Fin.ext
    simp only [extractedRightEdge_val, Fin.val_last]
    have hright := terminal.terminal_right
    omega
  rwa [hedgeLast] at hedge

/-- In the full/full branch every one of the four external endpoints is an
`insertedSacrifice` endpoint.  This is exactly paper Step 1: both copies are
exhausted by fully paired intervals, so neither incoming vertex survives and
both outgoing chain edges are removed. -/
theorem r324RefinedEndpointReductionCase_eq_all_inserted_of_isFull
    {m : ℕ} (hm : 0 < m) (p : R324RefinedScheduleIndex m)
    (hfull :
      (r324RefinedScheduleRepresentative p).1.IsFull ∧
        (r324RefinedScheduleRepresentative p).2.1.IsFull) :
    r324RefinedEndpointReductionCase p =
      fun _ => R324EndpointReductionCase.insertedSacrifice := by
  let e := r324RefinedScheduleRepresentative p
  have hleftFinal : finalActive e.1 = ∅ :=
    finalActive_eq_empty_of_full hfull.1
  have hrightFinal : finalActive e.2.1 = ∅ :=
    finalActive_eq_empty_of_full hfull.2
  have hleftOutgoing : Fin.last m ∈ extractedRightEdges e.1 :=
    last_mem_extractedRightEdges_of_isFull hm e.1 hfull.1
  have hrightOutgoing : Fin.last m ∈ extractedRightEdges e.2.1 :=
    last_mem_extractedRightEdges_of_isFull hm e.2.1 hfull.2
  funext j
  fin_cases j <;>
    simp [r324RefinedEndpointReductionCase,
      r324IncomingEndpointReductionCase, hm,
      r324OutgoingIsShortcut, r324EndpointReductionCaseOfFlag,
      e, hleftFinal, hrightFinal, hleftOutgoing, hrightOutgoing]

/-- Consequently the full/full branch spends exactly the four ordinary-`J`
sacrifices, namely `epsilon^{-8}`.  This is the scalar endpoint ledger that
will be multiplied only after the two signed Step-1 halves are assembled. -/
theorem r324EndpointPrimitiveSacrificeProduct_refined_eq_of_isFull
    {m : ℕ} (hm : 0 < m) (p : R324RefinedScheduleIndex m)
    (hfull :
      (r324RefinedScheduleRepresentative p).1.IsFull ∧
        (r324RefinedScheduleRepresentative p).2.1.IsFull)
    (epsilon : ℝ) :
    r324EndpointPrimitiveSacrificeProduct epsilon
        (r324RefinedEndpointReductionCase p) =
      epsilon⁻¹ ^ (8 : ℕ) := by
  rw [r324RefinedEndpointReductionCase_eq_all_inserted_of_isFull
    hm p hfull]
  unfold r324EndpointPrimitiveSacrificeProduct
    r324EndpointPrimitiveSacrifice
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/-! ## The residual incoming/outgoing exceptional blocks are distinct -/

namespace R324WithinHalfResidualPrefix
namespace R324IncomingExceptionalStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- If a half has a residual single, its block beginning at the first
internal vertex cannot also be the terminal block ending at the last
internal vertex.  Equality would make the terminal block the entire active
carrier, so completing the schedule would leave `finalActive = empty`. -/
theorem terminal_ne_outgoingTerminal_of_singles_nonempty
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) pairing initialScale)
    (outgoing : R324ShortcutTerminalSchedule pairing)
    (hm : 0 < m)
    (hsingles : pairing.singles.Nonempty) :
    data.terminal ≠ outgoing.terminal := by
  intro heq
  have hsuffix : data.suffix = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro later hlater
    have hright :=
      data.trace.stopPrefix.head_right_lt_tail_right
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq later hlater
    have houtRight : data.terminal.1.2.val = m - 1 := by
      rw [heq]
      exact outgoing.terminal_right
    have hlaterLt := later.1.2.isLt
    change data.terminal.1.2.val < later.1.2.val at hright
    omega
  have hremaining :
      data.trace.stopPrefix.remaining = data.terminal :: [] := by
    simpa only [hsuffix] using data.trace.stopPrefix_remaining_eq
  let post :=
    data.trace.stopPrefix.afterHead data.terminal [] hremaining
  have hleft : data.terminal.1.1 = (⟨0, hm⟩ : Fin m) := by
    apply Fin.ext
    exact data.left_eq_zero
  have hright :
      data.terminal.1.2 = (⟨m - 1, by omega⟩ : Fin m) := by
    apply Fin.ext
    rw [heq]
    exact outgoing.terminal_right
  have hinterval :
      Finset.Icc data.terminal.1.1 data.terminal.1.2 =
        (Finset.univ : Finset (Fin m)) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_univ, iff_true]
    constructor
    · rw [hleft]
      change 0 ≤ i.val
      omega
    · rw [hright]
      change i.val ≤ m - 1
      omega
  have hblock :
      data.terminal.2 = data.trace.stopPrefix.state.active := by
    have hgeometry :=
      r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
        pairing data.trace.stopPrefix.state.processed []
        data.terminal (by
          rw [data.trace.stopPrefix.schedule_eq, hremaining])
    change
      data.terminal.2 =
        data.trace.stopPrefix.state.active ∩
          Finset.Icc data.terminal.1.1 data.terminal.1.2
        at hgeometry
    rw [hinterval, Finset.inter_univ] at hgeometry
    exact hgeometry
  have hpostActive : post.state.active = ∅ := by
    dsimp only [post]
    rw [data.trace.stopPrefix.afterHead_active
      data.terminal [] hremaining, hblock]
    simp
  have hpostProcessed :
      post.state.processed = r322AnalyticSchedule pairing := by
    have hschedule := post.schedule_eq
    have hpostRemaining : post.remaining = [] := by
      rfl
    rw [hpostRemaining, List.append_nil] at hschedule
    exact hschedule.symm
  have hfinal : finalActive pairing = ∅ := by
    rw [← post.active_eq_finalActive_of_processed_eq_schedule
      hpostProcessed]
    exact hpostActive
  obtain ⟨i, hi⟩ := hsingles
  have hiFinal : i ∈ finalActive pairing :=
    singles_subset_finalActive pairing hi
  rw [hfinal] at hiFinal
  have hiNot : i ∉ (∅ : Finset (Fin m)) := by simp
  exact hiNot hiFinal

end R324IncomingExceptionalStopTraceAssembly
end R324WithinHalfResidualPrefix

/-! ## Exact direct/direct splice of the two completed halves -/

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)

/-- After all signed within-half removals, four direct external legs give
the literal product of their four translated Green modes and the still
grouped endpoint-erased residual core. -/
theorem endpointIntegratedResidualDensity_eq_of_four_direct
    (hm : 0 < m)
    (hleftOutgoing : Fin.last m ∉ extractedRightEdges κp)
    (hleftIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive κp)
    (hrightOutgoing : Fin.last m ∉ extractedRightEdges κm)
    (hrightIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive κm)
    (π : κp.singles ≃ κm.singles)
    (α β : Z4)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4)) :
    terminal.endpointIntegratedResidualDensity
        π (terminal.leftDirectOutgoingActive hm hleftOutgoing)
          (terminal.rightDirectOutgoingActive hm hrightOutgoing)
        α β p =
      (translatedGreenMode α
          (terminal.left.terminalIncomingAnchor
            (terminal.left.reconstruct p.1)) *
        translatedGreenMode β
          (terminal.left.terminalOutgoingAnchor
            (terminal.leftDirectOutgoingActive hm hleftOutgoing)
            (terminal.left.reconstruct p.1))) *
      (translatedGreenMode (-α)
          (terminal.right.terminalIncomingAnchor
            (terminal.right.reconstruct p.2)) *
        translatedGreenMode (-β)
          (terminal.right.terminalOutgoingAnchor
            (terminal.rightDirectOutgoingActive hm hrightOutgoing)
            (terminal.right.reconstruct p.2))) *
      terminal.endpointErasedResidualSumTerminalCore
        π (terminal.leftDirectOutgoingActive hm hleftOutgoing)
          (terminal.rightDirectOutgoingActive hm hrightOutgoing) p := by
  unfold endpointIntegratedResidualDensity
  rw [terminal.leftBoundaryModeCoefficient_eq_of_directBoundary
      hm hleftOutgoing hleftIncoming α β p.1,
    terminal.rightBoundaryModeCoefficient_eq_of_directBoundary
      hm hrightOutgoing hrightIncoming α β p.2]

/-- The first norm in the four-direct branch is taken after all four exact
Fourier integrations.  Its multiplier is precisely
`<alpha>^-4 <beta>^-4`. -/
theorem norm_endpointIntegratedResidualDensity_eq_of_four_direct
    (hm : 0 < m)
    (hleftOutgoing : Fin.last m ∉ extractedRightEdges κp)
    (hleftIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive κp)
    (hrightOutgoing : Fin.last m ∉ extractedRightEdges κm)
    (hrightIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive κm)
    (π : κp.singles ≃ κm.singles)
    (α β : Z4)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4)) :
    ‖terminal.endpointIntegratedResidualDensity
        π (terminal.leftDirectOutgoingActive hm hleftOutgoing)
          (terminal.rightDirectOutgoingActive hm hrightOutgoing)
        α β p‖ =
      (paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β) *
        ‖terminal.endpointErasedResidualSumTerminalCore
          π (terminal.leftDirectOutgoingActive hm hleftOutgoing)
            (terminal.rightDirectOutgoingActive hm hrightOutgoing) p‖ := by
  rw [terminal.norm_endpointIntegratedResidualDensity]
  rw [terminal.norm_leftBoundaryModeCoefficient_eq_of_directBoundary
      hm hleftOutgoing hleftIncoming α β p.1,
    terminal.norm_rightBoundaryModeCoefficient_eq_of_directBoundary
      hm hrightOutgoing hrightIncoming α β p.2]
  rw [← paperSecondOrderModeDecay_sq,
    ← paperSecondOrderModeDecay_sq]
  ring

end R324TwoHalfTerminalData

/-! ## Actual refined root, with all four direct endpoints -/

/-- Exact signed collapse from the genuine refined physical root to the
endpoint-integrated nested carrier.  This is the physical-integral form of
the Steps 2--3 identity; no norm is introduced by the adapter. -/
theorem lamEps_pow_r324RefinedPhysicalIntegral_eq_initialNestedEndpoint
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {leftScale rightScale : Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial ρ lam ε κp) leftScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial ρ lam ε κm) rightScale)
    (π : κp.singles ≃ κm.singles)
    (hleft : leftTrace.terminalPrefix.state.active.Nonempty)
    (hright : rightTrace.terminalPrefix.state.active.Nonempty)
    (α β : Z4)
    (s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hs : s ∈ momentContractionSignatures m)
    (hr : r ∈ momentResidualChainSignaturesAt m s)
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (hκp : e₀.1 = κp) (hκm : e₀.2.1 = κm)
    (hπ : HEq e₀.2.2 π)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
    (lamEps lam ε : ℂ) ^
          (2 *
            ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κp).remainingOrder +
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).remainingOrder)) *
        r324RefinedPhysicalIntegral ρ ε m α β
          (⟨⟨s, hs⟩, ⟨r, hr⟩⟩ : R324RefinedScheduleIndex m) =
      ∫ v : terminal.NestedCoordinate π → T4,
        terminal.initialNestedEndpointIntegratedResidualDensity
          π hleft hright α β v
        ∂Measure.pi fun _ => paperMeasure := by
  rw [← momentRefinedDeterministicTermSum_eq_r324RefinedPhysicalIntegral
    ρ hε hε1 α β s hs r hr]
  exact
    lamEps_pow_momentRefinedDeterministicTermSum_eq_initialNestedEndpoint
      leftTrace rightTrace π hleft hright α β s r hs hr e₀ he₀
      hκp hκm hπ hε hε1

/-- In the four-direct residual branch, the genuine refined root has the
paper's `⟨α⟩⁻⁴⟨β⟩⁻⁴` factor before any absolute-value estimate is made on
the complete endpoint-erased core. -/
theorem norm_lamEps_pow_r324RefinedPhysicalIntegral_le_of_four_direct
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {leftScale rightScale : Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial ρ lam ε κp) leftScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial ρ lam ε κm) rightScale)
    (π : κp.singles ≃ κm.singles)
    (hm : 0 < m)
    (hleftOutgoing : Fin.last m ∉ extractedRightEdges κp)
    (hleftIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive κp)
    (hrightOutgoing : Fin.last m ∉ extractedRightEdges κm)
    (hrightIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive κm)
    (α β : Z4)
    (s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hs : s ∈ momentContractionSignatures m)
    (hr : r ∈ momentResidualChainSignaturesAt m s)
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (hκp : e₀.1 = κp) (hκm : e₀.2.1 = κm)
    (hπ : HEq e₀.2.2 π)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
    let hleft := terminal.leftDirectOutgoingActive hm hleftOutgoing
    let hright := terminal.rightDirectOutgoingActive hm hrightOutgoing
    |lamEps lam ε| ^
          (2 *
            ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κp).remainingOrder +
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).remainingOrder)) *
        ‖r324RefinedPhysicalIntegral ρ ε m α β
          (⟨⟨s, hs⟩, ⟨r, hr⟩⟩ : R324RefinedScheduleIndex m)‖ ≤
      (paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β) *
        ∫ v : terminal.NestedCoordinate π → T4,
          ‖terminal.endpointErasedResidualSumTerminalCore
            π hleft hright
            ((terminal.terminalProductPiMeasurableEquivNested π).symm v)‖
          ∂Measure.pi fun _ => paperMeasure := by
  dsimp only
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
  let hleft := terminal.leftDirectOutgoingActive hm hleftOutgoing
  let hright := terminal.rightDirectOutgoingActive hm hrightOutgoing
  let order :=
    2 *
      ((R324WithinHalfResidualPrefix.initial
          ρ lam ε κp).remainingOrder +
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κm).remainingOrder)
  have hcollapse :=
    lamEps_pow_r324RefinedPhysicalIntegral_eq_initialNestedEndpoint
      leftTrace rightTrace π hleft hright α β s r hs hr e₀ he₀
      hκp hκm hπ hε hε1
  calc
    |lamEps lam ε| ^ order *
          ‖r324RefinedPhysicalIntegral ρ ε m α β
            (⟨⟨s, hs⟩, ⟨r, hr⟩⟩ : R324RefinedScheduleIndex m)‖ =
        ‖(lamEps lam ε : ℂ) ^ order *
          r324RefinedPhysicalIntegral ρ ε m α β
            (⟨⟨s, hs⟩, ⟨r, hr⟩⟩ : R324RefinedScheduleIndex m)‖ := by
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ = ‖∫ v : terminal.NestedCoordinate π → T4,
          terminal.initialNestedEndpointIntegratedResidualDensity
            π hleft hright α β v
          ∂Measure.pi fun _ => paperMeasure‖ :=
      congrArg norm hcollapse
    _ ≤ ∫ v : terminal.NestedCoordinate π → T4,
          ‖terminal.initialNestedEndpointIntegratedResidualDensity
            π hleft hright α β v‖
          ∂Measure.pi fun _ => paperMeasure :=
      norm_integral_le_integral_norm _
    _ = ∫ v : terminal.NestedCoordinate π → T4,
          (paperFourthOrderModeDecay α *
              paperFourthOrderModeDecay β) *
            ‖terminal.endpointErasedResidualSumTerminalCore
              π hleft hright
              ((terminal.terminalProductPiMeasurableEquivNested π).symm v)‖
          ∂Measure.pi fun _ => paperMeasure := by
      apply integral_congr_ae
      filter_upwards with v
      unfold R324TwoHalfTerminalData.initialNestedEndpointIntegratedResidualDensity
      exact terminal.norm_endpointIntegratedResidualDensity_eq_of_four_direct
        hm hleftOutgoing hleftIncoming hrightOutgoing hrightIncoming
        π α β _
    _ = (paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β) *
          ∫ v : terminal.NestedCoordinate π → T4,
            ‖terminal.endpointErasedResidualSumTerminalCore
              π hleft hright
              ((terminal.terminalProductPiMeasurableEquivNested π).symm v)‖
            ∂Measure.pi fun _ => paperMeasure := by
      rw [integral_const_mul]

/-! ### The four-direct core in complete-run currency -/

/-- The inverse-square model kernel has strictly positive total mass.
This small fact lets the public grouped-to-complete-run identity be
cancelled down to its endpoint-erased core, instead of duplicating its
coordinate-reindexing proof. -/
theorem r324_invSqKerMass_pos : 0 < invSqKerMass := by
  obtain ⟨Cgreen, hCgreen, hgreen⟩ := greenFn_le
  letI : NullSingletonClass paperMeasure :=
    ⟨paperMeasure_singleton⟩
  have hae :
      (fun z : T4 => greenFn z) ≤ᵐ[paperMeasure]
        fun z => Cgreen * invSqKer z := by
    filter_upwards [paperMeasure.ae_ne (0 : T4)] with z hz
    have hdist : torusDistSq z ≠ 0 := by
      intro hzero
      exact hz ((torusDistSq_eq_zero_iff z).mp hzero)
    simpa only [invSqKer, div_eq_mul_inv] using hgreen z hdist
  have hle :
      (∫ z : T4, greenFn z ∂paperMeasure) ≤
        ∫ z : T4, Cgreen * invSqKer z ∂paperMeasure :=
    integral_mono_ae integrable_greenFn_paper
      (integrable_invSqKer.const_mul Cgreen) hae
  rw [integral_greenFn_paper, integral_const_mul] at hle
  unfold invSqKerMass
  by_contra hnot
  have hmass : (∫ z : T4, invSqKer z ∂paperMeasure) ≤ 0 :=
    le_of_not_gt hnot
  have hprod :
      Cgreen * (∫ z : T4, invSqKer z ∂paperMeasure) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hCgreen.le hmass
  linarith

namespace R324TwoHalfTerminalData

/-- Pointwise four-direct endpoint estimate with only the two
endpoint-erased terminal paths majorized.

The four external Green legs have already been Fourier-integrated in
`norm_endpointIntegratedResidualDensity_eq_of_four_direct`, so their exact
fourth-order mode weights stay outside.  The only subsequent inequalities
are the two terminal certificate bounds and the nonnegativity of the still
grouped residual primitive sum.  This is the paper-order input for the
complete nested run: no external endpoint scale or inverse-square mass is
introduced. -/
theorem norm_endpointIntegratedResidualDensity_le_fourDirectCore_of_offDiagonal
    {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {leftInitialScale rightInitialScale : Fin (m + 1) -> Real}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
        leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
        rightInitialScale)
    (pi : kappaP.singles ≃ kappaM.singles)
    (hm : 0 < m)
    (hleftOutgoing : Fin.last m ∉ extractedRightEdges kappaP)
    (hleftIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive kappaP)
    (hrightOutgoing : Fin.last m ∉ extractedRightEdges kappaM)
    (hrightIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive kappaM)
    (alpha beta : Z4)
    (p :
      (leftTrace.terminalPrefix.SurvivingCoordinate -> T4) ×
        (rightTrace.terminalPrefix.SurvivingCoordinate -> T4))
    (hneLeft :
      ∀ edge ∈
          leftTrace.terminalPrefix.endpointErasedActiveEdgeSlots
            ((R324TwoHalfTerminalData.ofCertifiedTraces
              leftTrace rightTrace).leftDirectOutgoingActive
                hm hleftOutgoing),
        leftTrace.terminalPrefix.edgeDisplacement 0 0
          (leftTrace.terminalPrefix.reconstruct p.1) edge ≠ 0)
    (hneRight :
      ∀ edge ∈
          rightTrace.terminalPrefix.endpointErasedActiveEdgeSlots
            ((R324TwoHalfTerminalData.ofCertifiedTraces
              leftTrace rightTrace).rightDirectOutgoingActive
                hm hrightOutgoing),
        rightTrace.terminalPrefix.edgeDisplacement 0 0
          (rightTrace.terminalPrefix.reconstruct p.2) edge ≠ 0) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
    let hleft := terminal.leftDirectOutgoingActive hm hleftOutgoing
    let hright := terminal.rightDirectOutgoingActive hm hrightOutgoing
    norm (terminal.endpointIntegratedResidualDensity
        pi hleft hright alpha beta p) <=
      (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        ((leftTrace.terminalPrefix.endpointErasedScaleProduct
              hleft leftTrace.terminalScale *
            leftTrace.terminalPrefix.endpointErasedInvSqChainProduct
              hleft p.1) *
          (rightTrace.terminalPrefix.endpointErasedScaleProduct
              hright rightTrace.terminalScale *
            rightTrace.terminalPrefix.endpointErasedInvSqChainProduct
              hright p.2) *
          r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
            ((R324TwoHalfTerminalData.ofCertifiedTraces
              leftTrace rightTrace).terminalDoubledReconstruct p)) := by
  dsimp only
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
  let hleft := terminal.leftDirectOutgoingActive hm hleftOutgoing
  let hright := terminal.rightDirectOutgoingActive hm hrightOutgoing
  have hleftChain :=
    leftTrace.terminalPrefix.abs_endpointErasedSignedChain_le
      hleft leftTrace.terminalCertificate
      leftTrace.terminalPrefix_remaining_eq_nil
      0 0 (leftTrace.terminalPrefix.reconstruct p.1) hneLeft
  have hrightChain :=
    rightTrace.terminalPrefix.abs_endpointErasedSignedChain_le
      hright rightTrace.terminalCertificate
      rightTrace.terminalPrefix_remaining_eq_nil
      0 0 (rightTrace.terminalPrefix.reconstruct p.2) hneRight
  have hresidual :
      0 <= r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
        (terminal.terminalDoubledReconstruct p) :=
    r324ResidualPrimitiveSumProduct_nonneg rho eps kappaP kappaM pi _
  have hleftPath :
      0 <= leftTrace.terminalPrefix.endpointErasedInvSqChainProduct
        hleft p.1 :=
    leftTrace.terminalPrefix.endpointErasedInvSqChainProduct_nonneg
      hleft p.1
  have hrightPath :
      0 <= rightTrace.terminalPrefix.endpointErasedInvSqChainProduct
        hright p.2 :=
    rightTrace.terminalPrefix.endpointErasedInvSqChainProduct_nonneg
      hright p.2
  have hleftScale :
      0 <= leftTrace.terminalPrefix.endpointErasedScaleProduct
        hleft leftTrace.terminalScale := by
    unfold R324WithinHalfResidualPrefix.endpointErasedScaleProduct
    exact Finset.prod_nonneg fun edge _ =>
      (leftTrace.terminalCertificate.scale_pos edge).le
  have hrightScale :
      0 <= rightTrace.terminalPrefix.endpointErasedScaleProduct
        hright rightTrace.terminalScale := by
    unfold R324WithinHalfResidualPrefix.endpointErasedScaleProduct
    exact Finset.prod_nonneg fun edge _ =>
      (rightTrace.terminalCertificate.scale_pos edge).le
  have hchains :
      abs (leftTrace.terminalPrefix.endpointErasedSignedChain
            hleft 0 0 (leftTrace.terminalPrefix.reconstruct p.1)) *
          abs (rightTrace.terminalPrefix.endpointErasedSignedChain
            hright 0 0 (rightTrace.terminalPrefix.reconstruct p.2)) <=
        (leftTrace.terminalPrefix.endpointErasedScaleProduct
              hleft leftTrace.terminalScale *
            leftTrace.terminalPrefix.endpointErasedInvSqChainProduct
              hleft p.1) *
          (rightTrace.terminalPrefix.endpointErasedScaleProduct
              hright rightTrace.terminalScale *
            rightTrace.terminalPrefix.endpointErasedInvSqChainProduct
              hright p.2) := by
    calc
      _ <=
          (leftTrace.terminalPrefix.endpointErasedScaleProduct
                hleft leftTrace.terminalScale *
              leftTrace.terminalPrefix.endpointErasedInvSqChainProduct
                hleft p.1) *
            abs (rightTrace.terminalPrefix.endpointErasedSignedChain
              hright 0 0
                (rightTrace.terminalPrefix.reconstruct p.2)) :=
        mul_le_mul_of_nonneg_right hleftChain (abs_nonneg _)
      _ <= _ :=
        mul_le_mul_of_nonneg_left hrightChain
          (mul_nonneg hleftScale hleftPath)
  have hcore :
      norm (terminal.endpointErasedResidualSumTerminalCore
          pi hleft hright p) <=
        (leftTrace.terminalPrefix.endpointErasedScaleProduct
              hleft leftTrace.terminalScale *
            leftTrace.terminalPrefix.endpointErasedInvSqChainProduct
              hleft p.1) *
          (rightTrace.terminalPrefix.endpointErasedScaleProduct
              hright rightTrace.terminalScale *
            rightTrace.terminalPrefix.endpointErasedInvSqChainProduct
              hright p.2) *
          r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
            (terminal.terminalDoubledReconstruct p) := by
    unfold endpointErasedResidualSumTerminalCore
      endpointErasedSignedTerminalCoreOfActive residualSumCrossFactor
    dsimp only [terminal, R324TwoHalfTerminalData.ofCertifiedTraces]
    dsimp only [terminal, R324TwoHalfTerminalData.ofCertifiedTraces] at hresidual
    have hpeta : (p.1, p.2) = p := Prod.eta p
    rw [hpeta]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hresidual]
    exact mul_le_mul_of_nonneg_right hchains hresidual
  rw [terminal.norm_endpointIntegratedResidualDensity_eq_of_four_direct
    hm hleftOutgoing hleftIncoming hrightOutgoing hrightIncoming
    pi alpha beta p]
  exact mul_le_mul_of_nonneg_left hcore
    (mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
      (paperFourthOrderModeDecay_nonneg beta))

/-- The positive terminal core remaining after four direct Fourier
integrations.  In contrast to `endpointIntegratedGroupedMajorant`, the two
external scales and four inverse-square endpoint masses are absent. -/
def fourDirectEndpointErasedGroupedCore
    {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    (terminal : R324TwoHalfTerminalData rho lam eps kappaP kappaM)
    (leftScale rightScale : Fin (m + 1) -> Real)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (pi : kappaP.singles ≃ kappaM.singles)
    (p :
      (terminal.left.SurvivingCoordinate -> T4) ×
        (terminal.right.SurvivingCoordinate -> T4)) : Real :=
  (terminal.left.endpointErasedScaleProduct hleft leftScale *
      terminal.left.endpointErasedInvSqChainProduct hleft p.1) *
    (terminal.right.endpointErasedScaleProduct hright rightScale *
      terminal.right.endpointErasedInvSqChainProduct hright p.2) *
    r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
      (terminal.terminalDoubledReconstruct p)

/-- Almost-everywhere terminal-product form of the preceding four-direct
estimate.  This is the exact boundary consumed by the nested-cross
reindexing: the Fourier decay is already outside and all diagonal
exceptions have been removed under product Haar measure. -/
theorem ae_norm_endpointIntegratedResidualDensity_le_fourDirectCore
    {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {leftInitialScale rightInitialScale : Fin (m + 1) -> Real}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
        leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
        rightInitialScale)
    (pi : kappaP.singles ≃ kappaM.singles)
    (hm : 0 < m)
    (hleftOutgoing : Fin.last m ∉ extractedRightEdges kappaP)
    (hleftIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive kappaP)
    (hrightOutgoing : Fin.last m ∉ extractedRightEdges kappaM)
    (hrightIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive kappaM)
    (alpha beta : Z4) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
    let hleft := terminal.leftDirectOutgoingActive hm hleftOutgoing
    let hright := terminal.rightDirectOutgoingActive hm hrightOutgoing
    (fun p =>
      norm (terminal.endpointIntegratedResidualDensity
        pi hleft hright alpha beta p)) ≤ᵐ[
      (Measure.pi fun _ :
          leftTrace.terminalPrefix.SurvivingCoordinate => paperMeasure).prod
        (Measure.pi fun _ :
          rightTrace.terminalPrefix.SurvivingCoordinate => paperMeasure)]
      fun p =>
        (paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          terminal.fourDirectEndpointErasedGroupedCore
            leftTrace.terminalScale rightTrace.terminalScale
            hleft hright pi p := by
  dsimp only
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
  let hleft := terminal.leftDirectOutgoingActive hm hleftOutgoing
  let hright := terminal.rightDirectOutgoingActive hm hrightOutgoing
  have hleftOff :=
    leftTrace.terminalPrefix.ae_endpointErased_edgeDisplacement_ne_zero
      hleft
  have hrightOff :=
    rightTrace.terminalPrefix.ae_endpointErased_edgeDisplacement_ne_zero
      hright
  have hleftProd :=
    (Measure.quasiMeasurePreserving_fst
      (μ := Measure.pi fun _ :
        leftTrace.terminalPrefix.SurvivingCoordinate => paperMeasure)
      (ν := Measure.pi fun _ :
        rightTrace.terminalPrefix.SurvivingCoordinate => paperMeasure)).tendsto_ae
        hleftOff
  have hrightProd :=
    (Measure.quasiMeasurePreserving_snd
      (μ := Measure.pi fun _ :
        leftTrace.terminalPrefix.SurvivingCoordinate => paperMeasure)
      (ν := Measure.pi fun _ :
        rightTrace.terminalPrefix.SurvivingCoordinate => paperMeasure)).tendsto_ae
        hrightOff
  filter_upwards [hleftProd, hrightProd] with p hp hq
  simpa only [fourDirectEndpointErasedGroupedCore, terminal, hleft, hright,
    R324TwoHalfTerminalData.ofCertifiedTraces] using
    norm_endpointIntegratedResidualDensity_le_fourDirectCore_of_offDiagonal
      leftTrace rightTrace pi hm hleftOutgoing hleftIncoming
      hrightOutgoing hrightIncoming alpha beta p hp hq

/-- Pull the endpoint-erased four-direct core back to the literal initial
nested-cross carrier. -/
def initialNestedFourDirectEndpointErasedGroupedCore
    {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    (terminal : R324TwoHalfTerminalData rho lam eps kappaP kappaM)
    (leftScale rightScale : Fin (m + 1) -> Real)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (pi : kappaP.singles ≃ kappaM.singles)
    (v : terminal.NestedCoordinate pi -> T4) : Real :=
  terminal.fourDirectEndpointErasedGroupedCore
    leftScale rightScale hleft hright pi
    ((terminal.terminalProductPiMeasurableEquivNested pi).symm v)

/-- Initial nested-carrier form of the four-direct endpoint estimate. -/
theorem ae_norm_initialNestedEndpointIntegratedResidualDensity_le_fourDirectCore
    {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {leftInitialScale rightInitialScale : Fin (m + 1) -> Real}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
        leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
        rightInitialScale)
    (pi : kappaP.singles ≃ kappaM.singles)
    (hm : 0 < m)
    (hleftOutgoing : Fin.last m ∉ extractedRightEdges kappaP)
    (hleftIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive kappaP)
    (hrightOutgoing : Fin.last m ∉ extractedRightEdges kappaM)
    (hrightIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive kappaM)
    (alpha beta : Z4) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
    let hleft := terminal.leftDirectOutgoingActive hm hleftOutgoing
    let hright := terminal.rightDirectOutgoingActive hm hrightOutgoing
    (fun v =>
      norm (terminal.initialNestedEndpointIntegratedResidualDensity
        pi hleft hright alpha beta v)) ≤ᵐ[
      Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure]
      fun v =>
        (paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          terminal.initialNestedFourDirectEndpointErasedGroupedCore
            leftTrace.terminalScale rightTrace.terminalScale
            hleft hright pi v := by
  dsimp only
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
  let hleft := terminal.leftDirectOutgoingActive hm hleftOutgoing
  let hright := terminal.rightDirectOutgoingActive hm hrightOutgoing
  let e := terminal.terminalProductPiMeasurableEquivNested pi
  have hprod :=
    ae_norm_endpointIntegratedResidualDensity_le_fourDirectCore
      leftTrace rightTrace pi hm hleftOutgoing hleftIncoming
      hrightOutgoing hrightIncoming alpha beta
  have hp :=
    terminal.measurePreserving_terminalProductPiMeasurableEquivNested pi
  have hinv := MeasurePreserving.symm e hp
  have hpull := hinv.quasiMeasurePreserving.tendsto_ae hprod
  filter_upwards [hpull] with v hv
  change
    norm (terminal.endpointIntegratedResidualDensity
        pi hleft hright alpha beta (e.symm v)) ≤
      (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        terminal.fourDirectEndpointErasedGroupedCore
          leftTrace.terminalScale rightTrace.terminalScale
          hleft hright pi (e.symm v) at hv
  simpa only [initialNestedEndpointIntegratedResidualDensity,
    initialNestedFourDirectEndpointErasedGroupedCore,
    terminal, hleft, hright, e] using hv

/-- Exact coupling identity for the four-direct core.

The existing grouped-to-complete-run theorem contains four artificial
inverse-square endpoint masses because it was designed for arbitrary
terminal kernels.  Here all four endpoint kernels have already been
Fourier-integrated.  We instantiate that theorem with unit scales and
cancel its strictly positive inverse-square mass, leaving exactly the two
endpoint-erased scale products times the literal complete nested run. -/
theorem initialNestedFourDirectEndpointErasedGroupedCore_mul_coupling_eq
    {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    (terminal : R324TwoHalfTerminalData rho lam eps kappaP kappaM)
    (leftScale rightScale : Fin (m + 1) -> Real)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (pi : kappaP.singles ≃ kappaM.singles)
    (head : R324NestedCrossBlock kappaP kappaM pi)
    (tail : List (R324NestedCrossBlock kappaP kappaM pi))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial kappaP kappaM pi).remaining =
        head :: tail)
    (v : terminal.NestedCoordinate pi -> T4) :
    let step :=
      r324InitialNestedCrossStepContext
        kappaP kappaM pi head tail hremaining
    let hleftInitial :
        (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
      exact step.finalLeftHeadNonempty.mono fun i hi => by
        apply mem_r324LeftHalfPullback.mpr
        exact step.head_subset_activeCarrier
          (mem_r324LeftHalfPullback.mp hi)
    let hrightInitial :
        (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
      exact step.finalRightHeadNonempty.mono fun i hi => by
        apply mem_r324RightHalfPullback.mpr
        exact step.head_subset_activeCarrier
          (mem_r324RightHalfPullback.mp hi)
    lamEps lam eps ^ (2 * step.residual.remainingOrder) *
        terminal.initialNestedFourDirectEndpointErasedGroupedCore
          leftScale rightScale hleft hright pi v =
      (terminal.left.endpointErasedScaleProduct hleft leftScale *
          terminal.right.endpointErasedScaleProduct hright rightScale) *
        terminal.completeNestedRunDensity
          step hleftInitial hrightInitial v := by
  dsimp only
  let step :=
    r324InitialNestedCrossStepContext
      kappaP kappaM pi head tail hremaining
  change step.SurvivingCoordinate -> T4 at v
  have hleftInitial :
      (r324LeftHalfPullback step.residual.activeCarrier).Nonempty :=
    step.finalLeftHeadNonempty.mono fun i hi => by
      apply mem_r324LeftHalfPullback.mpr
      exact step.head_subset_activeCarrier
        (mem_r324LeftHalfPullback.mp hi)
  have hrightInitial :
      (r324RightHalfPullback step.residual.activeCarrier).Nonempty :=
    step.finalRightHeadNonempty.mono fun i hi => by
      apply mem_r324RightHalfPullback.mpr
      exact step.head_subset_activeCarrier
        (mem_r324RightHalfPullback.mp hi)
  let p :=
    (terminal.terminalProductPiMeasurableEquivNested pi).symm v
  let raw : Real :=
    terminal.left.endpointErasedInvSqChainProduct hleft p.1 *
      terminal.right.endpointErasedInvSqChainProduct hright p.2 *
      r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
        (terminal.terminalDoubledReconstruct p)
  have hgeneric :=
    initialNestedEndpointIntegratedGroupedMajorant_mul_coupling_eq
      terminal (fun _ => (1 : Real)) (fun _ => (1 : Real))
      hleft hright pi head tail hremaining v
  have hscaled :
      invSqKerMass ^ (4 : Nat) *
          (lamEps lam eps ^ (2 * step.residual.remainingOrder) * raw) =
        invSqKerMass ^ (4 : Nat) *
          terminal.completeNestedRunDensity
            step hleftInitial hrightInitial v := by
    calc
      _ = lamEps lam eps ^ (2 * step.residual.remainingOrder) *
          terminal.initialNestedEndpointIntegratedGroupedMajorant
            (fun _ => (1 : Real)) (fun _ => (1 : Real))
            hleft hright pi v := by
        unfold initialNestedEndpointIntegratedGroupedMajorant
          endpointIntegratedGroupedMajorant raw p
        simp only [Finset.prod_const_one, one_mul]
        ring
      _ = _ := by
        simpa only [step, Finset.prod_const_one, one_mul] using hgeneric
  have hmass : invSqKerMass ^ (4 : Nat) ≠ 0 :=
    pow_ne_zero _ r324_invSqKerMass_pos.ne'
  have hbase :
      lamEps lam eps ^ (2 * step.residual.remainingOrder) * raw =
        terminal.completeNestedRunDensity
          step hleftInitial hrightInitial v :=
    mul_left_cancel₀ hmass hscaled
  change
    lamEps lam eps ^ (2 * step.residual.remainingOrder) *
        ((terminal.left.endpointErasedScaleProduct hleft leftScale *
            terminal.left.endpointErasedInvSqChainProduct hleft p.1) *
          (terminal.right.endpointErasedScaleProduct hright rightScale *
            terminal.right.endpointErasedInvSqChainProduct hright p.2) *
          r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
            (terminal.terminalDoubledReconstruct p)) =
      (terminal.left.endpointErasedScaleProduct hleft leftScale *
          terminal.right.endpointErasedScaleProduct hright rightScale) *
        terminal.completeNestedRunDensity
          step hleftInitial hrightInitial v
  dsimp only [raw] at hbase
  calc
    _ =
        (terminal.left.endpointErasedScaleProduct hleft leftScale *
          terminal.right.endpointErasedScaleProduct hright rightScale) *
          (lamEps lam eps ^ (2 * step.residual.remainingOrder) * raw) := by
      ring
    _ = _ := by rw [hbase]

/-- Paper-order four-direct endpoint estimate in the literal complete-run
currency.  The coupling power is inserted only after the four exact
Fourier operations and the first norm; the preceding exact identity then
moves it onto the nested run. -/
theorem ae_coupling_mul_norm_initialNestedEndpointIntegratedResidualDensity_le_fourDirectRun
    {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {leftInitialScale rightInitialScale : Fin (m + 1) -> Real}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
        leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
        rightInitialScale)
    (pi : kappaP.singles ≃ kappaM.singles)
    (hm : 0 < m)
    (hleftOutgoing : Fin.last m ∉ extractedRightEdges kappaP)
    (hleftIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive kappaP)
    (hrightOutgoing : Fin.last m ∉ extractedRightEdges kappaM)
    (hrightIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive kappaM)
    (head : R324NestedCrossBlock kappaP kappaM pi)
    (tail : List (R324NestedCrossBlock kappaP kappaM pi))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial kappaP kappaM pi).remaining =
        head :: tail)
    (alpha beta : Z4) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
    let hleft := terminal.leftDirectOutgoingActive hm hleftOutgoing
    let hright := terminal.rightDirectOutgoingActive hm hrightOutgoing
    let step :=
      r324InitialNestedCrossStepContext
        kappaP kappaM pi head tail hremaining
    let hleftInitial :
        (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
      exact step.finalLeftHeadNonempty.mono fun i hi => by
        apply mem_r324LeftHalfPullback.mpr
        exact step.head_subset_activeCarrier
          (mem_r324LeftHalfPullback.mp hi)
    let hrightInitial :
        (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
      exact step.finalRightHeadNonempty.mono fun i hi => by
        apply mem_r324RightHalfPullback.mpr
        exact step.head_subset_activeCarrier
          (mem_r324RightHalfPullback.mp hi)
    (fun v =>
      lamEps lam eps ^ (2 * step.residual.remainingOrder) *
        norm (terminal.initialNestedEndpointIntegratedResidualDensity
          pi hleft hright alpha beta v)) ≤ᵐ[
      Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure]
      fun v =>
        (paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          ((terminal.left.endpointErasedScaleProduct
                hleft leftTrace.terminalScale *
              terminal.right.endpointErasedScaleProduct
                hright rightTrace.terminalScale) *
            terminal.completeNestedRunDensity
              step hleftInitial hrightInitial v) := by
  dsimp only
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
  let hleft := terminal.leftDirectOutgoingActive hm hleftOutgoing
  let hright := terminal.rightDirectOutgoingActive hm hrightOutgoing
  let step :=
    r324InitialNestedCrossStepContext
      kappaP kappaM pi head tail hremaining
  have hleftInitial :
      (r324LeftHalfPullback step.residual.activeCarrier).Nonempty :=
    step.finalLeftHeadNonempty.mono fun i hi => by
      apply mem_r324LeftHalfPullback.mpr
      exact step.head_subset_activeCarrier
        (mem_r324LeftHalfPullback.mp hi)
  have hrightInitial :
      (r324RightHalfPullback step.residual.activeCarrier).Nonempty :=
    step.finalRightHeadNonempty.mono fun i hi => by
      apply mem_r324RightHalfPullback.mpr
      exact step.head_subset_activeCarrier
        (mem_r324RightHalfPullback.mp hi)
  have hendpoint :=
    ae_norm_initialNestedEndpointIntegratedResidualDensity_le_fourDirectCore
      leftTrace rightTrace pi hm hleftOutgoing hleftIncoming
      hrightOutgoing hrightIncoming alpha beta
  filter_upwards [hendpoint] with v hv
  have hcore :=
    initialNestedFourDirectEndpointErasedGroupedCore_mul_coupling_eq
      terminal leftTrace.terminalScale rightTrace.terminalScale
      hleft hright pi head tail hremaining v
  have hcoupling :
      0 <= lamEps lam eps ^ (2 * step.residual.remainingOrder) :=
    (even_two_mul step.residual.remainingOrder).pow_nonneg _
  calc
    _ <= lamEps lam eps ^ (2 * step.residual.remainingOrder) *
        ((paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          terminal.initialNestedFourDirectEndpointErasedGroupedCore
            leftTrace.terminalScale rightTrace.terminalScale
            hleft hright pi v) :=
      mul_le_mul_of_nonneg_left hv hcoupling
    _ = (paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
        (lamEps lam eps ^ (2 * step.residual.remainingOrder) *
          terminal.initialNestedFourDirectEndpointErasedGroupedCore
            leftTrace.terminalScale rightTrace.terminalScale
            hleft hright pi v) := by ring
    _ = _ := by rw [hcore]

/-- Integrated four-direct endpoint estimate.  The right-hand side is the
literal complete nested run multiplied only by the two endpoint-erased
terminal scale products and the exact Fourier weights. -/
theorem integral_coupling_mul_norm_initialNestedEndpointIntegratedResidualDensity_le_fourDirectRun
    {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {leftInitialScale rightInitialScale : Fin (m + 1) -> Real}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
        leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
        rightInitialScale)
    (pi : kappaP.singles ≃ kappaM.singles)
    (hm : 0 < m)
    (hleftOutgoing : Fin.last m ∉ extractedRightEdges kappaP)
    (hleftIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive kappaP)
    (hrightOutgoing : Fin.last m ∉ extractedRightEdges kappaM)
    (hrightIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive kappaM)
    (head : R324NestedCrossBlock kappaP kappaM pi)
    (tail : List (R324NestedCrossBlock kappaP kappaM pi))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial kappaP kappaM pi).remaining =
        head :: tail)
    (alpha beta : Z4)
    (hlam : 0 < lam) (heps : 0 < eps) (heps1 : eps <= 1)
    (hlog : 1 <= abs (Real.log eps))
    (hmtrunc : m <= truncOrder eps) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
    let hleft := terminal.leftDirectOutgoingActive hm hleftOutgoing
    let hright := terminal.rightDirectOutgoingActive hm hrightOutgoing
    let step :=
      r324InitialNestedCrossStepContext
        kappaP kappaM pi head tail hremaining
    let hleftInitial :
        (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
      exact step.finalLeftHeadNonempty.mono fun i hi => by
        apply mem_r324LeftHalfPullback.mpr
        exact step.head_subset_activeCarrier
          (mem_r324LeftHalfPullback.mp hi)
    let hrightInitial :
        (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
      exact step.finalRightHeadNonempty.mono fun i hi => by
        apply mem_r324RightHalfPullback.mpr
        exact step.head_subset_activeCarrier
          (mem_r324RightHalfPullback.mp hi)
    (∫ v : terminal.NestedCoordinate pi → T4,
      lamEps lam eps ^ (2 * step.residual.remainingOrder) *
        norm (terminal.initialNestedEndpointIntegratedResidualDensity
          pi hleft hright alpha beta v)
      ∂Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure) <=
      (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        (terminal.left.endpointErasedScaleProduct
            hleft leftTrace.terminalScale *
          terminal.right.endpointErasedScaleProduct
            hright rightTrace.terminalScale) *
        ∫ v : step.SurvivingCoordinate → T4,
          terminal.completeNestedRunDensity
            step hleftInitial hrightInitial v
          ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure := by
  dsimp only
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
  let hleft := terminal.leftDirectOutgoingActive hm hleftOutgoing
  let hright := terminal.rightDirectOutgoingActive hm hrightOutgoing
  let step :=
    r324InitialNestedCrossStepContext
      kappaP kappaM pi head tail hremaining
  have hleftInitial :
      (r324LeftHalfPullback step.residual.activeCarrier).Nonempty :=
    step.finalLeftHeadNonempty.mono fun i hi => by
      apply mem_r324LeftHalfPullback.mpr
      exact step.head_subset_activeCarrier
        (mem_r324LeftHalfPullback.mp hi)
  have hrightInitial :
      (r324RightHalfPullback step.residual.activeCarrier).Nonempty :=
    step.finalRightHeadNonempty.mono fun i hi => by
      apply mem_r324RightHalfPullback.mpr
      exact step.head_subset_activeCarrier
        (mem_r324RightHalfPullback.mp hi)
  let scaleProduct : Real :=
    terminal.left.endpointErasedScaleProduct
        hleft leftTrace.terminalScale *
      terminal.right.endpointErasedScaleProduct
        hright rightTrace.terminalScale
  let decay : Real :=
    paperFourthOrderModeDecay alpha *
      paperFourthOrderModeDecay beta
  have hrun :
      Integrable (terminal.completeNestedRunDensity
        step hleftInitial hrightInitial)
        (Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) :=
    terminal.integrable_completeNestedRunDensity_at_truncation
      hlam heps heps1 hlog hmtrunc step hleftInitial hrightInitial
  have htarget :
      Integrable (fun v => decay *
        (scaleProduct * terminal.completeNestedRunDensity
          step hleftInitial hrightInitial v))
        (Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) :=
    (hrun.const_mul scaleProduct).const_mul decay
  have hsourceNonneg :
      ∀ᵐ v ∂Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure,
        0 <= lamEps lam eps ^ (2 * step.residual.remainingOrder) *
          norm (terminal.initialNestedEndpointIntegratedResidualDensity
            pi hleft hright alpha beta v) :=
    Filter.Eventually.of_forall fun v =>
      mul_nonneg
        ((even_two_mul step.residual.remainingOrder).pow_nonneg _)
        (norm_nonneg _)
  have hpoint :=
    ae_coupling_mul_norm_initialNestedEndpointIntegratedResidualDensity_le_fourDirectRun
      leftTrace rightTrace pi hm hleftOutgoing hleftIncoming
      hrightOutgoing hrightIncoming head tail hremaining alpha beta
  have hintegral :
      (∫ v : terminal.NestedCoordinate pi → T4,
        lamEps lam eps ^ (2 * step.residual.remainingOrder) *
          norm (terminal.initialNestedEndpointIntegratedResidualDensity
            pi hleft hright alpha beta v)
        ∂Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure) <=
        ∫ v : step.SurvivingCoordinate → T4, decay *
          (scaleProduct * terminal.completeNestedRunDensity
            step hleftInitial hrightInitial v)
          ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure := by
    exact integral_mono_of_nonneg hsourceNonneg htarget
      (by
        filter_upwards [hpoint] with v hv
        simpa only [terminal, hleft, hright, step, hleftInitial,
          hrightInitial, scaleProduct, decay] using hv)
  calc
    _ <= ∫ v : step.SurvivingCoordinate → T4, decay *
          (scaleProduct * terminal.completeNestedRunDensity
            step hleftInitial hrightInitial v)
        ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure :=
      hintegral
    _ = decay * scaleProduct *
        ∫ v : step.SurvivingCoordinate → T4,
          terminal.completeNestedRunDensity
            step hleftInitial hrightInitial v
          ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure := by
      rw [integral_const_mul, integral_const_mul]
      ring
    _ = _ := by rfl

/-- Consume the existing complete-run primitive-majorant estimate without
changing the four-direct endpoint ledger.  In particular, the exact two
Fourier decays and the endpoint-erased terminal scale product stay outside
the run integral. -/
theorem integral_coupling_mul_norm_initialNestedEndpointIntegratedResidualDensity_le_fourDirectMajorant
    {rho : SmoothCutoff} {lam eps B supportConstant : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {leftInitialScale rightInitialScale : Fin (m + 1) -> Real}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
        leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
        rightInitialScale)
    (pi : kappaP.singles ≃ kappaM.singles)
    (hm : 0 < m)
    (hleftOutgoing : Fin.last m ∉ extractedRightEdges kappaP)
    (hleftIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive kappaP)
    (hrightOutgoing : Fin.last m ∉ extractedRightEdges kappaM)
    (hrightIncoming : (⟨0, hm⟩ : Fin m) ∈ finalActive kappaM)
    (head : R324NestedCrossBlock kappaP kappaM pi)
    (tail : List (R324NestedCrossBlock kappaP kappaM pi))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial kappaP kappaM pi).remaining =
        head :: tail)
    (alpha beta : Z4)
    (hlam : 0 < lam) (heps : 0 < eps) (heps1 : eps <= 1)
    (hlog : 1 <= abs (Real.log eps))
    (hmtrunc : m <= truncOrder eps)
    (hrunBound :
      let terminal :=
        R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
      let step :=
        r324InitialNestedCrossStepContext
          kappaP kappaM pi head tail hremaining
      let hleftInitial :
          (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
        exact step.finalLeftHeadNonempty.mono fun i hi => by
          apply mem_r324LeftHalfPullback.mpr
          exact step.head_subset_activeCarrier
            (mem_r324LeftHalfPullback.mp hi)
      let hrightInitial :
          (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
        exact step.finalRightHeadNonempty.mono fun i hi => by
          apply mem_r324RightHalfPullback.mpr
          exact step.head_subset_activeCarrier
            (mem_r324RightHalfPullback.mp hi)
      (∫ v : step.SurvivingCoordinate → T4,
          terminal.completeNestedRunDensity
            step hleftInitial hrightInitial v
          ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) <=
        ∫ z : T4,
          primitiveInsertedMajorant
            B lam eps supportConstant step.residual.remainingOrder z
          ∂paperMeasure) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
    let hleft := terminal.leftDirectOutgoingActive hm hleftOutgoing
    let hright := terminal.rightDirectOutgoingActive hm hrightOutgoing
    let step :=
      r324InitialNestedCrossStepContext
        kappaP kappaM pi head tail hremaining
    (∫ v : terminal.NestedCoordinate pi → T4,
      lamEps lam eps ^ (2 * step.residual.remainingOrder) *
        norm (terminal.initialNestedEndpointIntegratedResidualDensity
          pi hleft hright alpha beta v)
      ∂Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure) <=
      (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        (terminal.left.endpointErasedScaleProduct
            hleft leftTrace.terminalScale *
          terminal.right.endpointErasedScaleProduct
            hright rightTrace.terminalScale) *
        ∫ z : T4,
          primitiveInsertedMajorant
            B lam eps supportConstant step.residual.remainingOrder z
          ∂paperMeasure := by
  dsimp only at hrunBound ⊢
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
  let hleft := terminal.leftDirectOutgoingActive hm hleftOutgoing
  let hright := terminal.rightDirectOutgoingActive hm hrightOutgoing
  let step :=
    r324InitialNestedCrossStepContext
      kappaP kappaM pi head tail hremaining
  have hleftScale :
      0 <= terminal.left.endpointErasedScaleProduct
        hleft leftTrace.terminalScale := by
    unfold R324WithinHalfResidualPrefix.endpointErasedScaleProduct
    exact Finset.prod_nonneg fun edge _ =>
      (leftTrace.terminalCertificate.scale_pos edge).le
  have hrightScale :
      0 <= terminal.right.endpointErasedScaleProduct
        hright rightTrace.terminalScale := by
    unfold R324WithinHalfResidualPrefix.endpointErasedScaleProduct
    exact Finset.prod_nonneg fun edge _ =>
      (rightTrace.terminalCertificate.scale_pos edge).le
  have hcoefficient :
      0 <=
        (paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          (terminal.left.endpointErasedScaleProduct
              hleft leftTrace.terminalScale *
            terminal.right.endpointErasedScaleProduct
              hright rightTrace.terminalScale) :=
    mul_nonneg
      (mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
        (paperFourthOrderModeDecay_nonneg beta))
      (mul_nonneg hleftScale hrightScale)
  exact
    (integral_coupling_mul_norm_initialNestedEndpointIntegratedResidualDensity_le_fourDirectRun
      leftTrace rightTrace pi hm hleftOutgoing hleftIncoming
      hrightOutgoing hrightIncoming head tail hremaining alpha beta
      hlam heps heps1 hlog hmtrunc).trans
      (mul_le_mul_of_nonneg_left hrunBound hcoefficient)

end R324TwoHalfTerminalData

namespace R324WithinHalfBudgetScaleReachable

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}
    {state : R324WithinHalfEdgeState m}
    {scale : Fin (m + 1) -> Real}

/-- Budget counterpart of the direct incoming geometry: if the first
internal vertex survives, no literal head can have updated slot zero, so
its numerical scale is still the initial Green base. -/
theorem edge_zero_eq_base_of_first_mem_active
    (hreach :
      R324WithinHalfBudgetScaleReachable
        pairing rho C lam eps K A state scale)
    (hm : 0 < m)
    (hfirst : (⟨0, hm⟩ : Fin m) ∈ state.active) :
    scale 0 = A := by
  let first : Fin m := ⟨0, hm⟩
  induction hreach with
  | initial => rfl
  | @afterHead oldScale res head tail hremaining previous ih =>
      have hfirstPost :
          first ∈ (res.afterHead head tail hremaining).state.active := by
        simpa only [first] using hfirst
      have hfirstOld : first ∈ res.state.active := by
        rw [res.afterHead_active head tail hremaining] at hfirstPost
        exact (Finset.mem_sdiff.mp hfirstPost).1
      have hfirstNotBlock : first ∉ head.2 := by
        rw [res.afterHead_active head tail hremaining] at hfirstPost
        exact (Finset.mem_sdiff.mp hfirstPost).2
      have hleftPos : 0 < head.1.1.val := by
        by_contra hnot
        have hleftZero : head.1.1 = first := by
          apply Fin.ext
          dsimp only [first]
          omega
        have haligned :=
          r322AnalyticSchedule_forall_aligned
            pairing head
            (res.headContext head tail hremaining).step_mem_schedule
        exact hfirstNotBlock (hleftZero ▸ haligned.1)
      have hcandidate :
          r324InternalVertexEdgeSlot first ∈
            r324WithinHalfPredecessorCandidates
              res.state head := by
        unfold r324WithinHalfPredecessorCandidates
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨first, ?_, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨hfirstOld, by
            change first.val < head.1.1.val
            simpa only [first] using hleftPos⟩
      have hle :
          r324InternalVertexEdgeSlot first <=
            r324WithinHalfPredecessorSlot res.state head :=
        Finset.le_max'
          (r324WithinHalfPredecessorCandidates res.state head)
          (r324InternalVertexEdgeSlot first) hcandidate
      have hzeroNe :
          (0 : Fin (m + 1)) ≠
            r324WithinHalfPredecessorSlot res.state head := by
        intro heq
        have hval := Fin.mk_le_mk.mp hle
        have heqVal := congrArg Fin.val heq
        change first.val + 1 <=
          (r324WithinHalfPredecessorSlot res.state head).val at hval
        dsimp only [first] at hval
        change 0 =
          (r324WithinHalfPredecessorSlot res.state head).val at heqVal
        omega
      rw [res.budgetUpdatedEdgeScale_of_ne
        head tail hremaining oldScale C lam K 0 hzeroNe]
      exact ih hfirstOld

end R324WithinHalfBudgetScaleReachable

namespace R324WithinHalfResidualPrefix.R324CompatibleAnalyticBudgetTrace

/-- In a direct/direct half, deleting the two external scale slots can only
decrease the compatible complete budget: both omitted numerical boundary
slots are still the initial base `A`, and `A >= 1`. -/
theorem initial_analytic_endpointErasedScaleProduct_le_closedForm_of_direct
    {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}
    (data :
      R324CompatibleAnalyticBudgetTrace
        (C := C) (K := K) (A := A)
        (R324WithinHalfResidualPrefix.initial rho lam eps pairing)
        (fun _ => A))
    (hA : 1 <= A)
    (hm : 0 < m)
    (houtgoing : Fin.last m ∉ extractedRightEdges pairing)
    (hincoming : (⟨0, hm⟩ : Fin m) ∈ finalActive pairing)
    (hactive : data.analytic.terminalPrefix.state.active.Nonempty) :
    data.analytic.terminalPrefix.endpointErasedScaleProduct
        hactive data.analytic.terminalScale <=
      A ^ (m + 1) *
        (C * lam) ^
          (2 * (R324WithinHalfResidualPrefix.initial
            rho lam eps pairing).remainingOrder) *
        K ^ data.analytic.terminalPrefix.state.processed.length := by
  let terminal := data.analytic.terminalPrefix
  have hprocessed :
      terminal.state.processed = r322AnalyticSchedule pairing :=
    data.analytic.terminalPrefix_processed_eq_schedule
  have hfirstActive :
      (⟨0, hm⟩ : Fin m) ∈ terminal.state.active := by
    rw [terminal.active_eq_finalActive_of_processed_eq_schedule hprocessed]
    exact hincoming
  have hzero : data.budgetScale 0 = A :=
    data.budgetReachable.edge_zero_eq_base_of_first_mem_active
      hm hfirstActive
  have hlast : data.budgetScale (Fin.last m) = A := by
    apply data.budgetReachable.edgeScale_eq_base_of_processed_right_lt
    intro earlier _
    change earlier.1.2.val < m
    exact earlier.1.2.isLt
  have houtSlot :
      terminal.terminalOutgoingEdgeSlot hactive = Fin.last m :=
    terminal.terminalOutgoingEdgeSlot_eq_finLast_of_directOutgoing
      hm hprocessed houtgoing hactive
  have hout :
      data.budgetScale (terminal.terminalOutgoingEdgeSlot hactive) = A := by
    rw [houtSlot]
    exact hlast
  have herasedAnalyticBudget :
      terminal.endpointErasedScaleProduct
          hactive data.analytic.terminalScale <=
        terminal.endpointErasedScaleProduct
          hactive data.budgetScale := by
    unfold R324WithinHalfResidualPrefix.endpointErasedScaleProduct
    exact Finset.prod_le_prod
      (fun edge _ =>
        (data.analytic.terminalCertificate.scale_pos edge).le)
      (fun edge _ => data.terminalScale_le edge)
  have herasedBudgetNonneg :
      0 <= terminal.endpointErasedScaleProduct
        hactive data.budgetScale := by
    unfold R324WithinHalfResidualPrefix.endpointErasedScaleProduct
    exact Finset.prod_nonneg fun edge _ =>
      (data.budgetCertificate.scale_pos edge).le
  have hAA : 1 <= A * A := by
    have hA0 : 0 <= A := zero_le_one.trans hA
    exact hA.trans (by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hA hA0))
  have hpartition :=
    terminal.activeEdgeScaleProduct_eq_boundary_mul_endpointErased
      hactive data.budgetScale
  have herasedBudgetFull :
      terminal.endpointErasedScaleProduct
          hactive data.budgetScale <=
        ∏ edge ∈ terminal.activeEdgeSlots, data.budgetScale edge := by
    calc
      terminal.endpointErasedScaleProduct
          hactive data.budgetScale =
          1 * terminal.endpointErasedScaleProduct
            hactive data.budgetScale := by ring
      _ <= (A * A) * terminal.endpointErasedScaleProduct
            hactive data.budgetScale :=
        mul_le_mul_of_nonneg_right hAA herasedBudgetNonneg
      _ = ∏ edge ∈ terminal.activeEdgeSlots,
            data.budgetScale edge := by
        rw [hzero, hout] at hpartition
        simpa only [terminal] using hpartition.symm
  have hbudgetClosed :
      (∏ edge ∈ terminal.activeEdgeSlots, data.budgetScale edge) =
        A ^ (m + 1) *
          (C * lam) ^
            (2 * (R324WithinHalfResidualPrefix.initial
              rho lam eps pairing).remainingOrder) *
          K ^ terminal.state.processed.length := by
    calc
      (∏ edge ∈ terminal.activeEdgeSlots, data.budgetScale edge) =
          (∏ _edge ∈
              ({0} ∪
                (r324InitialWithinHalfEdgeState m).active.image
                  r324InternalVertexEdgeSlot), A) *
            (C * lam) ^
              (2 * r324WithinHalfProcessedOrder terminal.state) *
            K ^ terminal.state.processed.length :=
        data.budgetReachable.activeEdgeScaleProduct_eq
      _ = _ := by
        rw [r324InitialActiveScaleProduct_eq_pow
          rho lam eps pairing A,
          data.analytic.terminal_processedOrder_eq_initialRemainingOrder]
  exact herasedAnalyticBudget.trans
    (herasedBudgetFull.trans (by simpa only [terminal] using hbudgetClosed.le))

end R324WithinHalfResidualPrefix.R324CompatibleAnalyticBudgetTrace

/-! ## Complete-budget terminal scales, independent of endpoint cases -/

/-- Two completed budget histories, possibly obtained through exceptional
endpoint stops rather than the ordinary certified trace, have the same
ambient-order scale closure.  This is the common numerical consumer for
all sixteen endpoint patterns: the endpoint calculation may change the
dependent terminal carrier, but it does not change the exact complete
budget recurrence. -/
theorem r324_twoHalf_reachable_terminalScale_mul_majorant_le
    {rho : SmoothCutoff} {C K A B lam eps supportConstant : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    (hA : 0 <= A) (hC : 0 <= C) (hK : 0 <= K)
    (hB : 0 <= B) (hlam : 0 <= lam)
    (terminal : R324TwoHalfTerminalData rho lam eps kappaP kappaM)
    (leftScale rightScale : Fin (m + 1) → Real)
    (leftReachable :
      R324WithinHalfBudgetScaleReachable
        kappaP rho C lam eps K A terminal.left.state leftScale)
    (rightReachable :
      R324WithinHalfBudgetScaleReachable
        kappaM rho C lam eps K A terminal.right.state rightScale)
    (pi : kappaP.singles ≃ kappaM.singles)
    (hm : 1 <= m) (z : T4) :
    (((∏ edge ∈ terminal.left.activeEdgeSlots, leftScale edge) *
        (∏ edge ∈ terminal.right.activeEdgeSlots, rightScale edge)) *
      invSqKerMass ^ 4) *
        primitiveInsertedMajorant B lam eps supportConstant
          (R324NestedCrossResidualPrefix.initial
            kappaP kappaM pi).remainingOrder z <=
      primitiveInsertedMajorant
        (r324TwoHalfCompleteAbsorbedBase A C K B)
        lam eps supportConstant m z := by
  let pleft :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaP).remainingOrder
  let pright :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaM).remainingOrder
  let cross :=
    (R324NestedCrossResidualPrefix.initial
      kappaP kappaM pi).remainingOrder
  let leftLength := terminal.left.state.processed.length
  let rightLength := terminal.right.state.processed.length
  let leftProduct :=
    ∏ edge ∈ terminal.left.activeEdgeSlots, leftScale edge
  let rightProduct :=
    ∏ edge ∈ terminal.right.activeEdgeSlots, rightScale edge
  let leftBound :=
    A ^ (m + 1) * (C * lam) ^ (2 * pleft) * K ^ leftLength
  let rightBound :=
    A ^ (m + 1) * (C * lam) ^ (2 * pright) * K ^ rightLength
  have hleftOrder :
      r324WithinHalfProcessedOrder terminal.left.state = pleft := by
    change
      (terminal.left.state.processed.map
          (fun step => residualBlockOrder step.2)).sum =
        ((r322AnalyticSchedule kappaP).map
          (fun step => residualBlockOrder step.2)).sum
    exact congrArg
      (fun steps =>
        (steps.map (fun step => residualBlockOrder step.2)).sum)
      terminal.left_processed
  have hrightOrder :
      r324WithinHalfProcessedOrder terminal.right.state = pright := by
    change
      (terminal.right.state.processed.map
          (fun step => residualBlockOrder step.2)).sum =
        ((r322AnalyticSchedule kappaM).map
          (fun step => residualBlockOrder step.2)).sum
    exact congrArg
      (fun steps =>
        (steps.map (fun step => residualBlockOrder step.2)).sum)
      terminal.right_processed
  have hleft : leftProduct = leftBound := by
    calc
      leftProduct =
          (∏ _edge ∈
              ({0} ∪
                (r324InitialWithinHalfEdgeState m).active.image
                  r324InternalVertexEdgeSlot), A) *
            (C * lam) ^
              (2 * r324WithinHalfProcessedOrder terminal.left.state) *
            K ^ terminal.left.state.processed.length := by
        simpa only [leftProduct,
          R324WithinHalfResidualPrefix.activeEdgeSlots] using
          leftReachable.activeEdgeScaleProduct_eq
      _ = leftBound := by
        rw [r324InitialActiveScaleProduct_eq_pow
          rho lam eps kappaP A, hleftOrder]
  have hright : rightProduct = rightBound := by
    calc
      rightProduct =
          (∏ _edge ∈
              ({0} ∪
                (r324InitialWithinHalfEdgeState m).active.image
                  r324InternalVertexEdgeSlot), A) *
            (C * lam) ^
              (2 * r324WithinHalfProcessedOrder terminal.right.state) *
            K ^ terminal.right.state.processed.length := by
        simpa only [rightProduct,
          R324WithinHalfResidualPrefix.activeEdgeSlots] using
          rightReachable.activeEdgeScaleProduct_eq
      _ = rightBound := by
        rw [r324InitialActiveScaleProduct_eq_pow
          rho lam eps kappaM A, hrightOrder]
  have horder : pleft + pright + cross = m :=
    r324InitialSchedules_remainingOrders_eq_ambient
      rho lam eps kappaP kappaM pi
  have hleftLength : leftLength <= pleft := by
    dsimp only [leftLength, pleft]
    rw [terminal.left_processed]
    unfold R324WithinHalfResidualPrefix.remainingOrder
    exact r322AnalyticSchedule_length_le_orderSum kappaP
  have hrightLength : rightLength <= pright := by
    dsimp only [rightLength, pright]
    rw [terminal.right_processed]
    unfold R324WithinHalfResidualPrefix.remainingOrder
    exact r322AnalyticSchedule_length_le_orderSum kappaM
  rw [show
    (((∏ edge ∈ terminal.left.activeEdgeSlots, leftScale edge) *
        (∏ edge ∈ terminal.right.activeEdgeSlots, rightScale edge)) *
      invSqKerMass ^ 4) =
        (leftBound * rightBound) * invSqKerMass ^ 4 by
      simp only [leftProduct, rightProduct, hleft, hright]]
  simpa only [leftBound, rightBound, cross, mul_assoc] using
    r324_twoHalf_complete_majorant_le
      hA hC hK hB hlam hm horder hleftLength hrightLength z

/-- Integrated form of the complete-budget terminal-scale closure.  Unlike
the direct/direct specialization below, this theorem only asks that each
completed half carry a reachable budget scale, so it is available after
either direct or exceptional endpoint elimination. -/
theorem r324_twoHalf_reachable_terminalScale_mul_integral_majorant_le
    {rho : SmoothCutoff} {C K A B lam eps supportConstant : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    (hA : 0 <= A) (hC : 0 <= C) (hK : 0 <= K)
    (hB : 0 <= B) (hlam : 0 <= lam) (heps : 0 < eps)
    (terminal : R324TwoHalfTerminalData rho lam eps kappaP kappaM)
    (leftScale rightScale : Fin (m + 1) → Real)
    (leftReachable :
      R324WithinHalfBudgetScaleReachable
        kappaP rho C lam eps K A terminal.left.state leftScale)
    (rightReachable :
      R324WithinHalfBudgetScaleReachable
        kappaM rho C lam eps K A terminal.right.state rightScale)
    (pi : kappaP.singles ≃ kappaM.singles)
    (hm : 1 <= m) :
    (((∏ edge ∈ terminal.left.activeEdgeSlots, leftScale edge) *
        (∏ edge ∈ terminal.right.activeEdgeSlots, rightScale edge)) *
      invSqKerMass ^ 4) *
        (∫ z : T4,
          primitiveInsertedMajorant B lam eps supportConstant
            (R324NestedCrossResidualPrefix.initial
              kappaP kappaM pi).remainingOrder z
          ∂paperMeasure) <=
      ∫ z : T4,
        primitiveInsertedMajorant
          (r324TwoHalfCompleteAbsorbedBase A C K B)
          lam eps supportConstant m z
        ∂paperMeasure := by
  let scaleProduct :=
    ((∏ edge ∈ terminal.left.activeEdgeSlots, leftScale edge) *
      (∏ edge ∈ terminal.right.activeEdgeSlots, rightScale edge)) *
      invSqKerMass ^ 4
  let cross :=
    (R324NestedCrossResidualPrefix.initial
      kappaP kappaM pi).remainingOrder
  rw [← integral_const_mul]
  apply integral_mono
    ((integrable_primitiveInsertedMajorant
      B lam eps supportConstant cross heps).const_mul scaleProduct)
    (integrable_primitiveInsertedMajorant
      (r324TwoHalfCompleteAbsorbedBase A C K B)
      lam eps supportConstant m heps)
  intro z
  dsimp only [scaleProduct, cross]
  exact r324_twoHalf_reachable_terminalScale_mul_majorant_le
    hA hC hK hB hlam terminal leftScale rightScale
    leftReachable rightReachable pi hm z

namespace R324TwoHalfTerminalData

/-- Package the completed carriers of two literal alternating transports.
This is the endpoint-pattern analogue of `ofCertifiedTraces`: exceptional
heads may have occurred, but both transports still finish the same paper
schedule. -/
def ofAlternatingTransports
    {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {leftRes : R324WithinHalfResidualPrefix rho lam eps kappaP}
    {rightRes : R324WithinHalfResidualPrefix rho lam eps kappaM}
    (leftTransport :
      R324WithinHalfResidualPrefix.R324WithinHalfAlternatingTransport
        leftRes)
    (rightTransport :
      R324WithinHalfResidualPrefix.R324WithinHalfAlternatingTransport
        rightRes) :
    R324TwoHalfTerminalData rho lam eps kappaP kappaM where
  left := leftTransport.final
  right := rightTransport.final
  left_remaining := leftTransport.final_remaining
  right_remaining := rightTransport.final_remaining
  left_processed := leftTransport.final_processed_eq_schedule
  right_processed := rightTransport.final_processed_eq_schedule

/-- Pull an arbitrary density on two completed half carriers to the literal
initial nested-cross carrier. -/
def initialNestedPullback
    {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    (terminal : R324TwoHalfTerminalData rho lam eps kappaP kappaM)
    (pi : kappaP.singles ≃ kappaM.singles)
    (density :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4) → Complex)
    (v : terminal.NestedCoordinate pi → T4) : Complex :=
  density ((terminal.terminalProductPiMeasurableEquivNested pi).symm v)

@[simp]
theorem initialNestedPullback_reindex
    {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    (terminal : R324TwoHalfTerminalData rho lam eps kappaP kappaM)
    (pi : kappaP.singles ≃ kappaM.singles)
    (density :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4) → Complex)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4)) :
    terminal.initialNestedPullback pi density
        (terminal.terminalProductPiMeasurableEquivNested pi p) =
      density p := by
  unfold initialNestedPullback
  rw [MeasurableEquiv.symm_apply_apply]

/-- The product-terminal and initial nested integrals of an arbitrary
density agree exactly. -/
theorem integral_terminalProduct_eq_integral_initialNestedPullback
    {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    (terminal : R324TwoHalfTerminalData rho lam eps kappaP kappaM)
    (pi : kappaP.singles ≃ kappaM.singles)
    (density :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4) → Complex) :
    (∫ p, density p
      ∂((Measure.pi fun _ : terminal.left.SurvivingCoordinate =>
            paperMeasure).prod
        (Measure.pi fun _ : terminal.right.SurvivingCoordinate =>
            paperMeasure))) =
      ∫ v, terminal.initialNestedPullback pi density v
        ∂Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure := by
  have hp :=
    terminal.measurePreserving_terminalProductPiMeasurableEquivNested pi
  calc
    _ = ∫ p,
          terminal.initialNestedPullback pi density
            (terminal.terminalProductPiMeasurableEquivNested pi p)
        ∂((Measure.pi fun _ : terminal.left.SurvivingCoordinate =>
              paperMeasure).prod
          (Measure.pi fun _ : terminal.right.SurvivingCoordinate =>
              paperMeasure)) := by
      apply integral_congr_ae
      filter_upwards with p
      exact (terminal.initialNestedPullback_reindex pi density p).symm
    _ = _ := by
      simpa only [Function.comp_apply] using
        hp.integral_comp' (terminal.initialNestedPullback pi density)

/-- Pull an a.e. terminal-product bound to the initial nested carrier. -/
theorem ae_norm_initialNestedPullback_le
    {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    (terminal : R324TwoHalfTerminalData rho lam eps kappaP kappaM)
    (pi : kappaP.singles ≃ kappaM.singles)
    (density :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4) → Complex)
    (majorant :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4) → Real)
    (hbound :
      (fun p => ‖density p‖) ≤ᵐ[
        (Measure.pi fun _ : terminal.left.SurvivingCoordinate =>
            paperMeasure).prod
          (Measure.pi fun _ : terminal.right.SurvivingCoordinate =>
            paperMeasure)] majorant) :
    (fun v => ‖terminal.initialNestedPullback pi density v‖) ≤ᵐ[
      Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure]
      fun v =>
        majorant
          ((terminal.terminalProductPiMeasurableEquivNested pi).symm v) := by
  let e := terminal.terminalProductPiMeasurableEquivNested pi
  have hp := terminal.measurePreserving_terminalProductPiMeasurableEquivNested pi
  have hpull :=
    (MeasurePreserving.symm e hp).quasiMeasurePreserving.tendsto_ae hbound
  change
    ∀ᵐ v ∂Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure,
      ‖density (e.symm v)‖ <= majorant (e.symm v) at hpull
  change
    ∀ᵐ v ∂Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure,
      ‖density (e.symm v)‖ <= majorant (e.symm v)
  exact hpull

/-- Common Step 3 consumer for a completed signed endpoint branch.  The
branch-specific proof is required only to dominate its post-endpoint
density by the literal grouped majorant.  The coupling power is inserted
after that domination and then converted exactly to the complete nested
run. -/
theorem ae_coupling_mul_norm_endpointDensity_le_completeNestedRun_of_grouped
    {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    (terminal : R324TwoHalfTerminalData rho lam eps kappaP kappaM)
    (leftScale rightScale : Fin (m + 1) → Real)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (pi : kappaP.singles ≃ kappaM.singles)
    (head : R324NestedCrossBlock kappaP kappaM pi)
    (tail : List (R324NestedCrossBlock kappaP kappaM pi))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial kappaP kappaM pi).remaining =
        head :: tail)
    (endpointWeight : Real)
    (endpointDensity : (terminal.NestedCoordinate pi → T4) → Complex)
    (hendpoint :
      (fun v => ‖endpointDensity v‖) ≤ᵐ[
        Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure]
        fun v =>
          endpointWeight *
            terminal.initialNestedEndpointIntegratedGroupedMajorant
              leftScale rightScale hleft hright pi v) :
    let step :=
      r324InitialNestedCrossStepContext
        kappaP kappaM pi head tail hremaining
    let hleftInitial :
        (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
      change (r324LeftHalfPullback
        (R324NestedCrossResidualPrefix.initial
          kappaP kappaM pi).activeCarrier).Nonempty
      rw [initial_leftHalfPullback_eq_terminalActive terminal pi]
      exact hleft
    let hrightInitial :
        (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
      change (r324RightHalfPullback
        (R324NestedCrossResidualPrefix.initial
          kappaP kappaM pi).activeCarrier).Nonempty
      rw [initial_rightHalfPullback_eq_terminalActive terminal pi]
      exact hright
    (fun v =>
      lamEps lam eps ^ (2 * step.residual.remainingOrder) *
        ‖endpointDensity v‖) ≤ᵐ[
      Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure]
      fun v =>
        endpointWeight *
          ((((∏ edge ∈ terminal.left.activeEdgeSlots,
                leftScale edge) *
              (∏ edge ∈ terminal.right.activeEdgeSlots,
                rightScale edge)) *
            invSqKerMass ^ 4) *
            terminal.completeNestedRunDensity
              step hleftInitial hrightInitial v) := by
  dsimp only
  let step :=
    r324InitialNestedCrossStepContext
      kappaP kappaM pi head tail hremaining
  have hleftInitial :
      (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
    change (r324LeftHalfPullback
      (R324NestedCrossResidualPrefix.initial
        kappaP kappaM pi).activeCarrier).Nonempty
    rw [initial_leftHalfPullback_eq_terminalActive terminal pi]
    exact hleft
  have hrightInitial :
      (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
    change (r324RightHalfPullback
      (R324NestedCrossResidualPrefix.initial
        kappaP kappaM pi).activeCarrier).Nonempty
    rw [initial_rightHalfPullback_eq_terminalActive terminal pi]
    exact hright
  filter_upwards [hendpoint] with v hv
  have hcoupling :
      0 <= lamEps lam eps ^ (2 * step.residual.remainingOrder) :=
    (even_two_mul step.residual.remainingOrder).pow_nonneg _
  have hgrouped :=
    terminal.initialNestedEndpointIntegratedGroupedMajorant_mul_coupling_eq
      leftScale rightScale hleft hright pi head tail hremaining v
  calc
    lamEps lam eps ^ (2 * step.residual.remainingOrder) *
          ‖endpointDensity v‖ <=
        lamEps lam eps ^ (2 * step.residual.remainingOrder) *
          (endpointWeight *
            terminal.initialNestedEndpointIntegratedGroupedMajorant
              leftScale rightScale hleft hright pi v) :=
      mul_le_mul_of_nonneg_left hv hcoupling
    _ = endpointWeight *
        (lamEps lam eps ^ (2 * step.residual.remainingOrder) *
          terminal.initialNestedEndpointIntegratedGroupedMajorant
            leftScale rightScale hleft hright pi v) := by ring
    _ = _ := by rw [hgrouped]

/-- Integrated form of the common signed-endpoint consumer.  It keeps the
literal endpoint weight outside the complete-run integral. -/
theorem integral_coupling_mul_norm_endpointDensity_le_completeNestedRun_of_grouped
    {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    (terminal : R324TwoHalfTerminalData rho lam eps kappaP kappaM)
    (leftScale rightScale : Fin (m + 1) → Real)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (pi : kappaP.singles ≃ kappaM.singles)
    (head : R324NestedCrossBlock kappaP kappaM pi)
    (tail : List (R324NestedCrossBlock kappaP kappaM pi))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial kappaP kappaM pi).remaining =
        head :: tail)
    (endpointWeight : Real)
    (endpointDensity : (terminal.NestedCoordinate pi → T4) → Complex)
    (hendpoint :
      (fun v => ‖endpointDensity v‖) ≤ᵐ[
        Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure]
        fun v =>
          endpointWeight *
            terminal.initialNestedEndpointIntegratedGroupedMajorant
              leftScale rightScale hleft hright pi v)
    (hlam : 0 < lam) (heps : 0 < eps) (heps1 : eps <= 1)
    (hlog : 1 <= abs (Real.log eps))
    (hmtrunc : m <= truncOrder eps) :
    let step :=
      r324InitialNestedCrossStepContext
        kappaP kappaM pi head tail hremaining
    let hleftInitial :
        (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
      change (r324LeftHalfPullback
        (R324NestedCrossResidualPrefix.initial
          kappaP kappaM pi).activeCarrier).Nonempty
      rw [initial_leftHalfPullback_eq_terminalActive terminal pi]
      exact hleft
    let hrightInitial :
        (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
      change (r324RightHalfPullback
        (R324NestedCrossResidualPrefix.initial
          kappaP kappaM pi).activeCarrier).Nonempty
      rw [initial_rightHalfPullback_eq_terminalActive terminal pi]
      exact hright
    (∫ v : terminal.NestedCoordinate pi → T4,
      lamEps lam eps ^ (2 * step.residual.remainingOrder) *
        ‖endpointDensity v‖
      ∂Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure) <=
      endpointWeight *
        ((((∏ edge ∈ terminal.left.activeEdgeSlots, leftScale edge) *
              (∏ edge ∈ terminal.right.activeEdgeSlots, rightScale edge)) *
            invSqKerMass ^ 4) *
          ∫ v : step.SurvivingCoordinate → T4,
            terminal.completeNestedRunDensity
              step hleftInitial hrightInitial v
            ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) := by
  dsimp only
  let step :=
    r324InitialNestedCrossStepContext
      kappaP kappaM pi head tail hremaining
  have hleftInitial :
      (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
    change (r324LeftHalfPullback
      (R324NestedCrossResidualPrefix.initial
        kappaP kappaM pi).activeCarrier).Nonempty
    rw [initial_leftHalfPullback_eq_terminalActive terminal pi]
    exact hleft
  have hrightInitial :
      (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
    change (r324RightHalfPullback
      (R324NestedCrossResidualPrefix.initial
        kappaP kappaM pi).activeCarrier).Nonempty
    rw [initial_rightHalfPullback_eq_terminalActive terminal pi]
    exact hright
  let scaleProduct :=
    ((∏ edge ∈ terminal.left.activeEdgeSlots, leftScale edge) *
      (∏ edge ∈ terminal.right.activeEdgeSlots, rightScale edge)) *
      invSqKerMass ^ 4
  have hrun :
      Integrable (terminal.completeNestedRunDensity
        step hleftInitial hrightInitial)
        (Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) :=
    terminal.integrable_completeNestedRunDensity_at_truncation
      hlam heps heps1 hlog hmtrunc step hleftInitial hrightInitial
  have htarget :
      Integrable (fun v => endpointWeight *
        (scaleProduct * terminal.completeNestedRunDensity
          step hleftInitial hrightInitial v))
        (Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) :=
    (hrun.const_mul scaleProduct).const_mul endpointWeight
  have hsourceNonneg :
      ∀ᵐ v ∂Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure,
        0 <= lamEps lam eps ^ (2 * step.residual.remainingOrder) *
          ‖endpointDensity v‖ :=
    Filter.Eventually.of_forall fun v =>
      mul_nonneg
        ((even_two_mul step.residual.remainingOrder).pow_nonneg _)
        (norm_nonneg _)
  have hpoint :=
    terminal.ae_coupling_mul_norm_endpointDensity_le_completeNestedRun_of_grouped
      leftScale rightScale hleft hright pi head tail hremaining
      endpointWeight endpointDensity hendpoint
  have hintegral :
      (∫ v : terminal.NestedCoordinate pi → T4,
        lamEps lam eps ^ (2 * step.residual.remainingOrder) *
          ‖endpointDensity v‖
        ∂Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure) <=
        ∫ v : step.SurvivingCoordinate → T4,
          endpointWeight *
            (scaleProduct * terminal.completeNestedRunDensity
              step hleftInitial hrightInitial v)
          ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure := by
    exact integral_mono_of_nonneg hsourceNonneg htarget (by
      filter_upwards [hpoint] with v hv
      simpa only [step, hleftInitial, hrightInitial, scaleProduct] using hv)
  calc
    _ <= ∫ v : step.SurvivingCoordinate → T4,
          endpointWeight *
            (scaleProduct * terminal.completeNestedRunDensity
              step hleftInitial hrightInitial v)
        ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure :=
      hintegral
    _ = endpointWeight * scaleProduct *
        ∫ v : step.SurvivingCoordinate → T4,
          terminal.completeNestedRunDensity
            step hleftInitial hrightInitial v
          ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure := by
      rw [integral_const_mul, integral_const_mul]
      ring
    _ = _ := by
      dsimp only [scaleProduct, step]
      ring

/-- End-to-end numerical consumer for any signed endpoint pattern.  The
pattern-specific work stops at `hendpoint`; the existing complete-run
estimate and the exact reachable-scale recurrence then place the result in
one ambient-order primitive-majorant currency. -/
theorem integral_coupling_mul_norm_endpointDensity_le_ambientMajorant_of_grouped
    {rho : SmoothCutoff} {C K A B lam eps supportConstant : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    (hA : 0 <= A) (hC : 0 <= C) (hK : 0 <= K)
    (hB : 0 <= B) (hlam : 0 < lam)
    (terminal : R324TwoHalfTerminalData rho lam eps kappaP kappaM)
    (leftScale rightScale : Fin (m + 1) → Real)
    (leftReachable :
      R324WithinHalfBudgetScaleReachable
        kappaP rho C lam eps K A terminal.left.state leftScale)
    (rightReachable :
      R324WithinHalfBudgetScaleReachable
        kappaM rho C lam eps K A terminal.right.state rightScale)
    (leftCertificate :
      R324WithinHalfEdgeCertificate terminal.left.state leftScale)
    (rightCertificate :
      R324WithinHalfEdgeCertificate terminal.right.state rightScale)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (pi : kappaP.singles ≃ kappaM.singles)
    (head : R324NestedCrossBlock kappaP kappaM pi)
    (tail : List (R324NestedCrossBlock kappaP kappaM pi))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial kappaP kappaM pi).remaining =
        head :: tail)
    (endpointWeight : Real) (hendpointWeight : 0 <= endpointWeight)
    (endpointDensity : (terminal.NestedCoordinate pi → T4) → Complex)
    (hendpoint :
      (fun v => ‖endpointDensity v‖) ≤ᵐ[
        Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure]
        fun v =>
          endpointWeight *
            terminal.initialNestedEndpointIntegratedGroupedMajorant
              leftScale rightScale hleft hright pi v)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hlog : 1 <= abs (Real.log eps))
    (hm : 1 <= m) (hmtrunc : m <= truncOrder eps)
    (hrunBound :
      let step :=
        r324InitialNestedCrossStepContext
          kappaP kappaM pi head tail hremaining
      let hleftInitial :
          (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
        change (r324LeftHalfPullback
          (R324NestedCrossResidualPrefix.initial
            kappaP kappaM pi).activeCarrier).Nonempty
        rw [initial_leftHalfPullback_eq_terminalActive terminal pi]
        exact hleft
      let hrightInitial :
          (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
        change (r324RightHalfPullback
          (R324NestedCrossResidualPrefix.initial
            kappaP kappaM pi).activeCarrier).Nonempty
        rw [initial_rightHalfPullback_eq_terminalActive terminal pi]
        exact hright
      (∫ v : step.SurvivingCoordinate → T4,
          terminal.completeNestedRunDensity
            step hleftInitial hrightInitial v
          ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) <=
        ∫ z : T4,
          primitiveInsertedMajorant B lam eps supportConstant
            step.residual.remainingOrder z
          ∂paperMeasure) :
    let step :=
      r324InitialNestedCrossStepContext
        kappaP kappaM pi head tail hremaining
    (∫ v : terminal.NestedCoordinate pi → T4,
      lamEps lam eps ^ (2 * step.residual.remainingOrder) *
        ‖endpointDensity v‖
      ∂Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure) <=
      endpointWeight *
        ∫ z : T4,
          primitiveInsertedMajorant
            (r324TwoHalfCompleteAbsorbedBase A C K B)
            lam eps supportConstant m z
          ∂paperMeasure := by
  dsimp only at hrunBound ⊢
  let step :=
    r324InitialNestedCrossStepContext
      kappaP kappaM pi head tail hremaining
  have hleftInitial :
      (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
    change (r324LeftHalfPullback
      (R324NestedCrossResidualPrefix.initial
        kappaP kappaM pi).activeCarrier).Nonempty
    rw [initial_leftHalfPullback_eq_terminalActive terminal pi]
    exact hleft
  have hrightInitial :
      (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
    change (r324RightHalfPullback
      (R324NestedCrossResidualPrefix.initial
        kappaP kappaM pi).activeCarrier).Nonempty
    rw [initial_rightHalfPullback_eq_terminalActive terminal pi]
    exact hright
  let scaleProduct :=
    ((∏ edge ∈ terminal.left.activeEdgeSlots, leftScale edge) *
      (∏ edge ∈ terminal.right.activeEdgeSlots, rightScale edge)) *
      invSqKerMass ^ 4
  have hleftProduct :
      0 <= ∏ edge ∈ terminal.left.activeEdgeSlots, leftScale edge :=
    Finset.prod_nonneg fun edge _ => (leftCertificate.scale_pos edge).le
  have hrightProduct :
      0 <= ∏ edge ∈ terminal.right.activeEdgeSlots, rightScale edge :=
    Finset.prod_nonneg fun edge _ => (rightCertificate.scale_pos edge).le
  have hscaleProduct : 0 <= scaleProduct :=
    mul_nonneg (mul_nonneg hleftProduct hrightProduct)
      (pow_nonneg r324_invSqKerMass_pos.le _)
  have hrun :=
    terminal.integral_coupling_mul_norm_endpointDensity_le_completeNestedRun_of_grouped
      leftScale rightScale hleft hright pi head tail hremaining
      endpointWeight endpointDensity hendpoint
      hlam heps heps1 hlog hmtrunc
  have hrunScaled :
      endpointWeight * scaleProduct *
          (∫ v : step.SurvivingCoordinate → T4,
            terminal.completeNestedRunDensity
              step hleftInitial hrightInitial v
            ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) <=
        endpointWeight * scaleProduct *
          (∫ z : T4,
            primitiveInsertedMajorant B lam eps supportConstant
              step.residual.remainingOrder z
            ∂paperMeasure) :=
    mul_le_mul_of_nonneg_left hrunBound
      (mul_nonneg hendpointWeight hscaleProduct)
  have habsorb :=
    r324_twoHalf_reachable_terminalScale_mul_integral_majorant_le
      (supportConstant := supportConstant)
      hA hC hK hB hlam.le heps terminal leftScale rightScale
      leftReachable rightReachable pi hm
  have hstepOrder :
      step.residual.remainingOrder =
        (R324NestedCrossResidualPrefix.initial
          kappaP kappaM pi).remainingOrder := by
    rfl
  calc
    _ <= endpointWeight *
        (scaleProduct *
          ∫ v : step.SurvivingCoordinate → T4,
            terminal.completeNestedRunDensity
              step hleftInitial hrightInitial v
            ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) := by
      simpa only [step, hleftInitial, hrightInitial, scaleProduct] using hrun
    _ = endpointWeight * scaleProduct *
          (∫ v : step.SurvivingCoordinate → T4,
            terminal.completeNestedRunDensity
              step hleftInitial hrightInitial v
            ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) := by
      ring
    _ <= endpointWeight * scaleProduct *
          (∫ z : T4,
            primitiveInsertedMajorant B lam eps supportConstant
              step.residual.remainingOrder z
            ∂paperMeasure) := hrunScaled
    _ = endpointWeight *
        (scaleProduct *
          ∫ z : T4,
            primitiveInsertedMajorant B lam eps supportConstant
              (R324NestedCrossResidualPrefix.initial
                kappaP kappaM pi).remainingOrder z
            ∂paperMeasure) := by
      rw [hstepOrder]
      ring
    _ <= endpointWeight *
        (∫ z : T4,
          primitiveInsertedMajorant
            (r324TwoHalfCompleteAbsorbedBase A C K B)
            lam eps supportConstant m z
          ∂paperMeasure) :=
      mul_le_mul_of_nonneg_left habsorb hendpointWeight

end R324TwoHalfTerminalData

/-- Inflate the complete-run primitive constant just enough to replace the
four artificial inverse-square endpoint masses by the four exact Fourier
integrations of the direct/direct branch. -/
def r324FourDirectRunInflatedBase (B : Real) : Real :=
  max 1 (invSqKerMass⁻¹ ^ (2 : Nat)) * B

theorem r324FourDirectRunInflatedBase_nonneg
    {B : Real} (hB : 0 <= B) :
    0 <= r324FourDirectRunInflatedBase B := by
  unfold r324FourDirectRunInflatedBase
  exact mul_nonneg (zero_le_one.trans (le_max_left _ _)) hB

theorem r324FourDirectRunInflatedBase_pos
    {B : Real} (hB : 0 < B) :
    0 < r324FourDirectRunInflatedBase B := by
  unfold r324FourDirectRunInflatedBase
  exact mul_pos (zero_lt_one.trans_le (le_max_left _ _)) hB

/-- The single fixed inflation above compensates the missing four endpoint
masses at every nonempty nested-cross order. -/
theorem primitiveInsertedMajorant_le_invSqKerMass_pow_four_mul_fourDirectInflated
    (B lam eps supportConstant : Real) {n : Nat}
    (hn : 1 <= n) (z : T4) :
    primitiveInsertedMajorant B lam eps supportConstant n z <=
      invSqKerMass ^ (4 : Nat) *
        primitiveInsertedMajorant
          (r324FourDirectRunInflatedBase B)
          lam eps supportConstant n z := by
  let d : Real := max 1 (invSqKerMass⁻¹ ^ (2 : Nat))
  have hd1 : 1 <= d := by
    dsimp only [d]
    exact le_max_left _ _
  have hd0 : 0 <= d := zero_le_one.trans hd1
  have hinvSq0 : 0 <= invSqKerMass⁻¹ ^ (2 : Nat) := by positivity
  have hinvSqLe : invSqKerMass⁻¹ ^ (2 : Nat) <= d := by
    dsimp only [d]
    exact le_max_right _ _
  have hsq :
      (invSqKerMass⁻¹ ^ (2 : Nat)) ^ (2 : Nat) <= d ^ (2 : Nat) :=
    pow_le_pow_left₀ hinvSq0 hinvSqLe 2
  have hpow : d ^ (2 : Nat) <= d ^ (2 * n) :=
    pow_le_pow_right₀ hd1 (by omega)
  have hfactor :
      1 <= invSqKerMass ^ (4 : Nat) * d ^ (2 * n) := by
    calc
      1 = invSqKerMass ^ (4 : Nat) *
          (invSqKerMass⁻¹ ^ (2 : Nat)) ^ (2 : Nat) := by
        field_simp [r324_invSqKerMass_pos.ne']
      _ <= invSqKerMass ^ (4 : Nat) * d ^ (2 * n) :=
        mul_le_mul_of_nonneg_left (hsq.trans hpow)
          (pow_nonneg invSqKerMass_nonneg _)
  have hbaseNonneg : 0 <= (B * lam) ^ (2 * n) :=
    (even_two_mul n).pow_nonneg _
  have hcoefficient :
      (B * lam) ^ (2 * n) <=
        invSqKerMass ^ (4 : Nat) *
          ((d * B) * lam) ^ (2 * n) := by
    calc
      (B * lam) ^ (2 * n) = 1 * (B * lam) ^ (2 * n) := by ring
      _ <= (invSqKerMass ^ (4 : Nat) * d ^ (2 * n)) *
          (B * lam) ^ (2 * n) :=
        mul_le_mul_of_nonneg_right hfactor hbaseNonneg
      _ = invSqKerMass ^ (4 : Nat) *
          ((d * B) * lam) ^ (2 * n) := by
        rw [show (d * B) * lam = d * (B * lam) by ring, mul_pow]
        ring
  unfold primitiveInsertedMajorant
  have hkernel :
      0 <= ((eps⁻¹) ^ 2 / |Real.log eps|) * invSqKer z *
          primitiveSupportIndicator supportConstant eps z +
        (1 / |Real.log eps| ^ 2) *
          (torusDistSq z + eps ^ 2)⁻¹ ^ 2 := by
    apply add_nonneg
    · exact mul_nonneg
        (mul_nonneg (div_nonneg (by positivity) (abs_nonneg _))
          (invSqKer_nonneg z))
        (primitiveSupportIndicator_nonneg supportConstant eps z)
    · exact mul_nonneg (div_nonneg zero_le_one (sq_nonneg _))
        (pow_nonneg
          (inv_nonneg.mpr
            (add_nonneg (torusDistSq_nonneg z) (sq_nonneg eps))) 2)
  dsimp only [r324FourDirectRunInflatedBase, d] at hcoefficient ⊢
  calc
    _ <=
        (invSqKerMass ^ (4 : Nat) *
          (((max 1 (invSqKerMass⁻¹ ^ (2 : Nat)) * B) * lam) ^
            (2 * n))) *
          (((eps⁻¹) ^ 2 / |Real.log eps|) * invSqKer z *
              primitiveSupportIndicator supportConstant eps z +
            (1 / |Real.log eps| ^ 2) *
              (torusDistSq z + eps ^ 2)⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_right hcoefficient hkernel
    _ = _ := by ring

/-- Pointwise two-half scale absorption for the four-direct branch.  This
is the direct/direct analogue of
`r324_twoHalf_initial_terminalScale_mul_majorant_le`, with the endpoint
slots already Fourier-integrated and therefore absent from the analytic
scale product. -/
theorem r324_twoHalf_initial_fourDirectScale_mul_majorant_le
    {rho : SmoothCutoff}
    {C K A B lam eps supportConstant : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    (hA : 1 <= A) (hC : 0 <= C) (hK : 0 <= K)
    (hB : 0 <= B) (hlam : 0 <= lam)
    (leftData :
      R324WithinHalfResidualPrefix.R324CompatibleAnalyticBudgetTrace
        (C := C) (K := K) (A := A)
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
        (fun _ => A))
    (rightData :
      R324WithinHalfResidualPrefix.R324CompatibleAnalyticBudgetTrace
        (C := C) (K := K) (A := A)
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
        (fun _ => A))
    (pi : kappaP.singles ≃ kappaM.singles)
    (hm : 1 <= m)
    (hleftOutgoing : Fin.last m ∉ extractedRightEdges kappaP)
    (hleftIncoming : (⟨0, by omega⟩ : Fin m) ∈ finalActive kappaP)
    (hrightOutgoing : Fin.last m ∉ extractedRightEdges kappaM)
    (hrightIncoming : (⟨0, by omega⟩ : Fin m) ∈ finalActive kappaM)
    (head : R324NestedCrossBlock kappaP kappaM pi)
    (tail : List (R324NestedCrossBlock kappaP kappaM pi))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial kappaP kappaM pi).remaining =
        head :: tail)
    (z : T4) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces
        leftData.analytic rightData.analytic
    let hleft := terminal.leftDirectOutgoingActive (by omega) hleftOutgoing
    let hright := terminal.rightDirectOutgoingActive (by omega) hrightOutgoing
    (terminal.left.endpointErasedScaleProduct
          hleft leftData.analytic.terminalScale *
        terminal.right.endpointErasedScaleProduct
          hright rightData.analytic.terminalScale) *
        primitiveInsertedMajorant B lam eps supportConstant
          (R324NestedCrossResidualPrefix.initial
            kappaP kappaM pi).remainingOrder z <=
      primitiveInsertedMajorant
        (r324TwoHalfCompleteAbsorbedBase A C K
          (r324FourDirectRunInflatedBase B))
        lam eps supportConstant m z := by
  dsimp only
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces
      leftData.analytic rightData.analytic
  have hm0 : 0 < m := by omega
  let hleft := terminal.leftDirectOutgoingActive hm0 hleftOutgoing
  let hright := terminal.rightDirectOutgoingActive hm0 hrightOutgoing
  let pleft :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaP).remainingOrder
  let pright :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaM).remainingOrder
  let cross :=
    (R324NestedCrossResidualPrefix.initial
      kappaP kappaM pi).remainingOrder
  let leftLength :=
    leftData.analytic.terminalPrefix.state.processed.length
  let rightLength :=
    rightData.analytic.terminalPrefix.state.processed.length
  let leftProduct :=
    terminal.left.endpointErasedScaleProduct
      hleft leftData.analytic.terminalScale
  let rightProduct :=
    terminal.right.endpointErasedScaleProduct
      hright rightData.analytic.terminalScale
  let leftBound :=
    A ^ (m + 1) * (C * lam) ^ (2 * pleft) * K ^ leftLength
  let rightBound :=
    A ^ (m + 1) * (C * lam) ^ (2 * pright) * K ^ rightLength
  have hleft : leftProduct <= leftBound := by
    dsimp only [leftProduct, leftBound, pleft, leftLength, terminal]
    exact
      leftData.initial_analytic_endpointErasedScaleProduct_le_closedForm_of_direct
        hA hm0 hleftOutgoing hleftIncoming
          (terminal.leftDirectOutgoingActive hm0 hleftOutgoing)
  have hright : rightProduct <= rightBound := by
    dsimp only [rightProduct, rightBound, pright, rightLength, terminal]
    exact
      rightData.initial_analytic_endpointErasedScaleProduct_le_closedForm_of_direct
        hA hm0 hrightOutgoing hrightIncoming
          (terminal.rightDirectOutgoingActive hm0 hrightOutgoing)
  have hrightNonneg : 0 <= rightProduct := by
    dsimp only [rightProduct]
    unfold R324WithinHalfResidualPrefix.endpointErasedScaleProduct
    exact Finset.prod_nonneg fun edge _ =>
      (rightData.analytic.terminalCertificate.scale_pos edge).le
  have hleftBoundNonneg : 0 <= leftBound := by
    dsimp only [leftBound]
    positivity
  have hrightBoundNonneg : 0 <= rightBound := by
    dsimp only [rightBound]
    positivity
  have hproducts :
      leftProduct * rightProduct <= leftBound * rightBound :=
    mul_le_mul hleft hright hrightNonneg hleftBoundNonneg
  have hmajorantNonneg :
      0 <= primitiveInsertedMajorant
        B lam eps supportConstant cross z :=
    primitiveInsertedMajorant_nonneg' B lam eps supportConstant cross z
  let step :=
    r324InitialNestedCrossStepContext
      kappaP kappaM pi head tail hremaining
  have hcrossOne : 1 <= cross := by
    dsimp only [cross]
    change 1 <= step.residual.remainingOrder
    rw [step.remainingOrder_eq_order_add_next]
    have hstepOrder := step.one_le_order
    omega
  have hinflate :
      primitiveInsertedMajorant B lam eps supportConstant cross z <=
        invSqKerMass ^ (4 : Nat) *
          primitiveInsertedMajorant
            (r324FourDirectRunInflatedBase B)
            lam eps supportConstant cross z :=
    primitiveInsertedMajorant_le_invSqKerMass_pow_four_mul_fourDirectInflated
      B lam eps supportConstant hcrossOne z
  have horder : pleft + pright + cross = m :=
    r324InitialSchedules_remainingOrders_eq_ambient
      rho lam eps kappaP kappaM pi
  have hleftLength : leftLength <= pleft :=
    leftData.analytic.terminal_processedLength_le_initialRemainingOrder
  have hrightLength : rightLength <= pright :=
    rightData.analytic.terminal_processedLength_le_initialRemainingOrder
  have hBInflated : 0 <= r324FourDirectRunInflatedBase B :=
    r324FourDirectRunInflatedBase_nonneg hB
  have habsorb := r324_twoHalf_complete_majorant_le
    (ε := eps) (supportConstant := supportConstant)
    (zero_le_one.trans hA) hC hK hBInflated hlam hm horder
      hleftLength hrightLength z
  change
    (leftProduct * rightProduct) *
        primitiveInsertedMajorant B lam eps supportConstant cross z <=
      primitiveInsertedMajorant
        (r324TwoHalfCompleteAbsorbedBase A C K
          (r324FourDirectRunInflatedBase B))
        lam eps supportConstant m z
  calc
    (leftProduct * rightProduct) *
        primitiveInsertedMajorant B lam eps supportConstant cross z <=
      (leftBound * rightBound) *
        primitiveInsertedMajorant B lam eps supportConstant cross z :=
      mul_le_mul_of_nonneg_right hproducts hmajorantNonneg
    _ <= (leftBound * rightBound) *
        (invSqKerMass ^ (4 : Nat) *
          primitiveInsertedMajorant
            (r324FourDirectRunInflatedBase B)
            lam eps supportConstant cross z) :=
      mul_le_mul_of_nonneg_left hinflate
        (mul_nonneg hleftBoundNonneg hrightBoundNonneg)
    _ = (leftBound * rightBound) * invSqKerMass ^ (4 : Nat) *
        primitiveInsertedMajorant
          (r324FourDirectRunInflatedBase B)
          lam eps supportConstant cross z := by ring
    _ <= primitiveInsertedMajorant
        (r324TwoHalfCompleteAbsorbedBase A C K
          (r324FourDirectRunInflatedBase B))
        lam eps supportConstant m z := by
      simpa only [leftBound, rightBound, pleft, pright, cross,
        leftLength, rightLength] using habsorb

/-- Integrated form of the four-direct two-half scale absorption. -/
theorem r324_twoHalf_initial_fourDirectScale_mul_integral_majorant_le
    {rho : SmoothCutoff}
    {C K A B lam eps supportConstant : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    (hA : 1 <= A) (hC : 0 <= C) (hK : 0 <= K)
    (hB : 0 <= B) (hlam : 0 <= lam) (heps : 0 < eps)
    (leftData :
      R324WithinHalfResidualPrefix.R324CompatibleAnalyticBudgetTrace
        (C := C) (K := K) (A := A)
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
        (fun _ => A))
    (rightData :
      R324WithinHalfResidualPrefix.R324CompatibleAnalyticBudgetTrace
        (C := C) (K := K) (A := A)
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
        (fun _ => A))
    (pi : kappaP.singles ≃ kappaM.singles)
    (hm : 1 <= m)
    (hleftOutgoing : Fin.last m ∉ extractedRightEdges kappaP)
    (hleftIncoming : (⟨0, by omega⟩ : Fin m) ∈ finalActive kappaP)
    (hrightOutgoing : Fin.last m ∉ extractedRightEdges kappaM)
    (hrightIncoming : (⟨0, by omega⟩ : Fin m) ∈ finalActive kappaM)
    (head : R324NestedCrossBlock kappaP kappaM pi)
    (tail : List (R324NestedCrossBlock kappaP kappaM pi))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial kappaP kappaM pi).remaining =
        head :: tail) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces
        leftData.analytic rightData.analytic
    let hleft := terminal.leftDirectOutgoingActive (by omega) hleftOutgoing
    let hright := terminal.rightDirectOutgoingActive (by omega) hrightOutgoing
    (terminal.left.endpointErasedScaleProduct
          hleft leftData.analytic.terminalScale *
        terminal.right.endpointErasedScaleProduct
          hright rightData.analytic.terminalScale) *
        (∫ z : T4,
          primitiveInsertedMajorant B lam eps supportConstant
            (R324NestedCrossResidualPrefix.initial
              kappaP kappaM pi).remainingOrder z
          ∂paperMeasure) <=
      ∫ z : T4,
        primitiveInsertedMajorant
          (r324TwoHalfCompleteAbsorbedBase A C K
            (r324FourDirectRunInflatedBase B))
          lam eps supportConstant m z
        ∂paperMeasure := by
  dsimp only
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces
      leftData.analytic rightData.analytic
  have hm0 : 0 < m := by omega
  let hleft := terminal.leftDirectOutgoingActive hm0 hleftOutgoing
  let hright := terminal.rightDirectOutgoingActive hm0 hrightOutgoing
  let scaleProduct :=
    terminal.left.endpointErasedScaleProduct
        hleft leftData.analytic.terminalScale *
      terminal.right.endpointErasedScaleProduct
        hright rightData.analytic.terminalScale
  let cross :=
    (R324NestedCrossResidualPrefix.initial
      kappaP kappaM pi).remainingOrder
  rw [← integral_const_mul]
  apply integral_mono
    ((integrable_primitiveInsertedMajorant
      B lam eps supportConstant cross heps).const_mul scaleProduct)
    (integrable_primitiveInsertedMajorant
      (r324TwoHalfCompleteAbsorbedBase A C K
        (r324FourDirectRunInflatedBase B))
      lam eps supportConstant m heps)
  intro z
  dsimp only [scaleProduct, cross, terminal, hleft, hright]
  exact r324_twoHalf_initial_fourDirectScale_mul_majorant_le
    hA hC hK hB hlam leftData rightData pi hm
    hleftOutgoing hleftIncoming hrightOutgoing hrightIncoming
    head tail hremaining z

namespace R324TwoHalfTerminalData

/-- Direct/direct residual branch in ambient-order inserted-majorant
currency, for fixed compatible traces and a supplied complete-run bound. -/
theorem integral_coupling_mul_norm_initialNestedEndpointIntegratedResidualDensity_le_fourDirectAmbientMajorant
    {rho : SmoothCutoff} {C K A B lam eps supportConstant : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    (hA : 1 <= A) (hC : 0 <= C) (hK : 0 <= K)
    (hB : 0 <= B) (hlam : 0 < lam) (heps : 0 < eps)
    (heps1 : eps <= 1) (hlog : 1 <= abs (Real.log eps))
    (hm : 1 <= m) (hmtrunc : m <= truncOrder eps)
    (leftData :
      R324WithinHalfResidualPrefix.R324CompatibleAnalyticBudgetTrace
        (C := C) (K := K) (A := A)
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
        (fun _ => A))
    (rightData :
      R324WithinHalfResidualPrefix.R324CompatibleAnalyticBudgetTrace
        (C := C) (K := K) (A := A)
        (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
        (fun _ => A))
    (pi : kappaP.singles ≃ kappaM.singles)
    (hleftOutgoing : Fin.last m ∉ extractedRightEdges kappaP)
    (hleftIncoming : (⟨0, by omega⟩ : Fin m) ∈ finalActive kappaP)
    (hrightOutgoing : Fin.last m ∉ extractedRightEdges kappaM)
    (hrightIncoming : (⟨0, by omega⟩ : Fin m) ∈ finalActive kappaM)
    (head : R324NestedCrossBlock kappaP kappaM pi)
    (tail : List (R324NestedCrossBlock kappaP kappaM pi))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial kappaP kappaM pi).remaining =
        head :: tail)
    (alpha beta : Z4)
    (hrunBound :
      let terminal := R324TwoHalfTerminalData.ofCertifiedTraces
        leftData.analytic rightData.analytic
      let step := r324InitialNestedCrossStepContext
        kappaP kappaM pi head tail hremaining
      let hleftInitial :
          (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
        exact step.finalLeftHeadNonempty.mono fun i hi => by
          apply mem_r324LeftHalfPullback.mpr
          exact step.head_subset_activeCarrier
            (mem_r324LeftHalfPullback.mp hi)
      let hrightInitial :
          (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
        exact step.finalRightHeadNonempty.mono fun i hi => by
          apply mem_r324RightHalfPullback.mpr
          exact step.head_subset_activeCarrier
            (mem_r324RightHalfPullback.mp hi)
      (∫ v : step.SurvivingCoordinate → T4,
          terminal.completeNestedRunDensity
            step hleftInitial hrightInitial v
          ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) <=
        ∫ z : T4, primitiveInsertedMajorant B lam eps supportConstant
          step.residual.remainingOrder z ∂paperMeasure) :
    let terminal := R324TwoHalfTerminalData.ofCertifiedTraces
      leftData.analytic rightData.analytic
    let hleft := terminal.leftDirectOutgoingActive (by omega) hleftOutgoing
    let hright := terminal.rightDirectOutgoingActive (by omega) hrightOutgoing
    let step := r324InitialNestedCrossStepContext
      kappaP kappaM pi head tail hremaining
    (∫ v : terminal.NestedCoordinate pi → T4,
      lamEps lam eps ^ (2 * step.residual.remainingOrder) *
        norm (terminal.initialNestedEndpointIntegratedResidualDensity
          pi hleft hright alpha beta v)
      ∂Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure) <=
      (paperFourthOrderModeDecay alpha * paperFourthOrderModeDecay beta) *
        ∫ z : T4, primitiveInsertedMajorant
          (r324TwoHalfCompleteAbsorbedBase A C K
            (r324FourDirectRunInflatedBase B))
          lam eps supportConstant m z ∂paperMeasure := by
  dsimp only at hrunBound ⊢
  let terminal := R324TwoHalfTerminalData.ofCertifiedTraces
    leftData.analytic rightData.analytic
  have hm0 : 0 < m := by omega
  let scaleProduct :=
    terminal.left.endpointErasedScaleProduct
        (terminal.leftDirectOutgoingActive hm0 hleftOutgoing)
        leftData.analytic.terminalScale *
      terminal.right.endpointErasedScaleProduct
        (terminal.rightDirectOutgoingActive hm0 hrightOutgoing)
        rightData.analytic.terminalScale
  have hendpoint :=
    integral_coupling_mul_norm_initialNestedEndpointIntegratedResidualDensity_le_fourDirectMajorant
      leftData.analytic rightData.analytic pi hm0
      hleftOutgoing hleftIncoming hrightOutgoing hrightIncoming
      head tail hremaining alpha beta hlam heps heps1 hlog hmtrunc hrunBound
  have habsorb :=
    r324_twoHalf_initial_fourDirectScale_mul_integral_majorant_le
      (supportConstant := supportConstant)
      hA hC hK hB hlam.le heps leftData rightData pi hm
      hleftOutgoing hleftIncoming hrightOutgoing hrightIncoming
      head tail hremaining
  have hdecay :
      0 <= paperFourthOrderModeDecay alpha *
        paperFourthOrderModeDecay beta :=
    mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
      (paperFourthOrderModeDecay_nonneg beta)
  calc
    _ <= (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        (scaleProduct *
          (∫ z : T4, primitiveInsertedMajorant B lam eps supportConstant
            (r324InitialNestedCrossStepContext
              kappaP kappaM pi head tail hremaining).residual.remainingOrder
              z ∂paperMeasure)) := by
      simpa only [terminal, scaleProduct, mul_assoc] using hendpoint
    _ <= (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        (∫ z : T4, primitiveInsertedMajorant
          (r324TwoHalfCompleteAbsorbedBase A C K
            (r324FourDirectRunInflatedBase B))
          lam eps supportConstant m z ∂paperMeasure) :=
      mul_le_mul_of_nonneg_left habsorb hdecay

end R324TwoHalfTerminalData

/-- Uniform producer for the all-four-direct residual endpoint pattern.
The constants are chosen before the scale, order, refined schedule, and
Fourier modes. -/
theorem exists_r324PaperFourDirectEndpointWeightedMajorantBound
    (rho : SmoothCutoff) :
    ∃ primitiveConstant supportConstant : Real,
      0 < primitiveConstant ∧ 0 < supportConstant ∧
      ∀ {eps : Real} (m : Nat) (alpha beta : Z4),
        0 < eps → eps <= 1 / 4 →
        1 <= abs (Real.log eps) → 2 <= m →
        m <= truncOrder eps →
        ∀ p : R324RefinedScheduleIndex m,
          ∀ hm0 : 0 < m,
          (r324RefinedContractionRepresentative
              m p.1.1 p.2.1).1.singles.Nonempty →
          (⟨0, hm0⟩ : Fin m) ∈
              finalActive (r324RefinedContractionRepresentative
                m p.1.1 p.2.1).1 →
          Fin.last m ∉
              extractedRightEdges (r324RefinedContractionRepresentative
                m p.1.1 p.2.1).1 →
          (⟨0, hm0⟩ : Fin m) ∈
              finalActive (r324RefinedContractionRepresentative
                m p.1.1 p.2.1).2.1 →
          Fin.last m ∉ extractedRightEdges
              (r324RefinedContractionRepresentative
                m p.1.1 p.2.1).2.1 →
          abs (lamEps 1 eps) ^ (2 * m) *
              norm (r324RefinedPhysicalIntegral
                rho eps m alpha beta p) <=
            (paperFourthOrderModeDecay alpha *
                paperFourthOrderModeDecay beta) *
              ∫ z : T4, primitiveInsertedMajorant
                primitiveConstant 1 eps supportConstant m z
                ∂paperMeasure := by
  obtain ⟨_phaseSupport, C, K, A,
      _hphaseSupport, hC, hK, hA, htraces⟩ :=
    exists_r324InitialCompatibleAnalyticBudgetTrace_at_truncation rho
  obtain ⟨runSupport, B, hrunSupport, hB, hrun⟩ :=
    R324TwoHalfTerminalData.exists_integral_completeNestedRunDensity_le_primitiveInsertedMajorant
      rho
  let finalConstant :=
    r324TwoHalfCompleteAbsorbedBase A C K
      (r324FourDirectRunInflatedBase B)
  have hfinal : 0 < finalConstant :=
    r324TwoHalfCompleteAbsorbedBase_pos A C K
      (r324FourDirectRunInflatedBase B)
  refine ⟨finalConstant, runSupport, hfinal, hrunSupport, ?_⟩
  intro eps m alpha beta heps hepsSmall hlog hm2 hmtrunc p hm0 hsingles
    hleftIncoming hleftOutgoing hrightIncoming hrightOutgoing
  have heps1 : eps <= 1 := hepsSmall.trans (by norm_num)
  have hm : 1 <= m := by omega
  let e0 := r324RefinedContractionRepresentative m p.1.1 p.2.1
  obtain ⟨leftData⟩ :=
    htraces 1 eps m e0.1 one_pos heps heps1 hlog hmtrunc
  obtain ⟨rightData⟩ :=
    htraces 1 eps m e0.2.1 one_pos heps heps1 hlog hmtrunc
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces
      leftData.analytic rightData.analytic
  let hleft := terminal.leftDirectOutgoingActive hm0 hleftOutgoing
  let hright := terminal.rightDirectOutgoingActive hm0 hrightOutgoing
  obtain ⟨head, tail, hremaining⟩ :=
    exists_r324InitialNestedCross_head_of_singles_nonempty
      e0.1 e0.2.1 e0.2.2 hsingles
  let step :=
    r324InitialNestedCrossStepContext
      e0.1 e0.2.1 e0.2.2 head tail hremaining
  have hleftInitial :
      (r324LeftHalfPullback step.residual.activeCarrier).Nonempty :=
    step.finalLeftHeadNonempty.mono fun i hi => by
      apply mem_r324LeftHalfPullback.mpr
      exact step.head_subset_activeCarrier
        (mem_r324LeftHalfPullback.mp hi)
  have hrightInitial :
      (r324RightHalfPullback step.residual.activeCarrier).Nonempty :=
    step.finalRightHeadNonempty.mono fun i hi => by
      apply mem_r324RightHalfPullback.mpr
      exact step.head_subset_activeCarrier
        (mem_r324RightHalfPullback.mp hi)
  have hrunBound :
      (∫ v : step.SurvivingCoordinate → T4,
          terminal.completeNestedRunDensity
            step hleftInitial hrightInitial v
          ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) <=
        ∫ z : T4, primitiveInsertedMajorant
          B 1 eps runSupport step.residual.remainingOrder z
          ∂paperMeasure :=
    hrun terminal one_pos heps heps1 hlog hmtrunc
      step hleftInitial hrightInitial
  have hendpoint :=
    R324TwoHalfTerminalData.integral_coupling_mul_norm_initialNestedEndpointIntegratedResidualDensity_le_fourDirectAmbientMajorant
      hA hC.le hK.le hB.le one_pos heps heps1 hlog hm hmtrunc
      leftData rightData e0.2.2 hleftOutgoing hleftIncoming
      hrightOutgoing hrightIncoming head tail hremaining alpha beta
      hrunBound
  have he0 :
      e0 ∈ momentRefinedContractionFiber m p.1.1 p.2.1 := by
    exact r324RefinedContractionRepresentative_mem p.2.2
  have hcollapse :=
    lamEps_pow_r324RefinedPhysicalIntegral_eq_initialNestedEndpoint
      leftData.analytic rightData.analytic e0.2.2 hleft hright
      alpha beta p.1.1 p.2.1 p.1.2 p.2.2 e0 he0
      rfl rfl (HEq.rfl) heps heps1
  have horder :=
    r324InitialSchedules_remainingOrders_eq_ambient
      rho 1 eps e0.1 e0.2.1 e0.2.2
  have hweighted :=
    weighted_norm_le_of_collapsed_endpointIntegral
      (lam := 1) (ε := eps) (m := m)
      (leftOrder :=
        (R324WithinHalfResidualPrefix.initial
          rho 1 eps e0.1).remainingOrder)
      (rightOrder :=
        (R324WithinHalfResidualPrefix.initial
          rho 1 eps e0.2.1).remainingOrder)
      (crossOrder :=
        (R324NestedCrossResidualPrefix.initial
          e0.1 e0.2.1 e0.2.2).remainingOrder)
      horder
      (r324RefinedPhysicalIntegral rho eps m alpha beta p)
      (fun v : terminal.NestedCoordinate e0.2.2 → T4 =>
        terminal.initialNestedEndpointIntegratedResidualDensity
          e0.2.2 hleft hright alpha beta v)
      hcollapse hendpoint
  simpa only [finalConstant, e0, terminal, hleft, hright] using hweighted

/-! ## Endpoint classification on the actual refined-fibre representative -/

/-- The four endpoint cases attached to the representative which actually
appears in the signed physical-collapse theorem.  This deliberately does
not use `r324RefinedScheduleRepresentative`, whose choice is only made in
the coarser contraction fibre. -/
def r324ActualRefinedEndpointReductionCase
    {m : Nat} (p : R324RefinedScheduleIndex m) :
    Fin 4 → R324EndpointReductionCase :=
  let e := r324RefinedContractionRepresentative m p.1.1 p.2.1
  ![
    r324IncomingEndpointReductionCase e.1,
    r324EndpointReductionCaseOfFlag (r324OutgoingIsShortcut e.1),
    r324IncomingEndpointReductionCase e.2.1,
    r324EndpointReductionCaseOfFlag (r324OutgoingIsShortcut e.2.1)
  ]

/-- The endpoint pattern is independent of which representative of the
fixed within-half signature is used.  In particular, the representative
chosen in the residual-refined fibre has the same four paper endpoint
cases as the representative chosen in the coarser contraction fibre.

The proof uses the rigidity of the actual extraction recursion under a
fixed endpoint signature; it does not assume invariance of the refined
representative as extra data. -/
theorem r324ActualRefinedEndpointReductionCase_eq_refined
    {m : Nat} (p : R324RefinedScheduleIndex m) :
    r324ActualRefinedEndpointReductionCase p =
      r324RefinedEndpointReductionCase p := by
  let e := r324RefinedContractionRepresentative m p.1.1 p.2.1
  let eCoarse := r324RefinedScheduleRepresentative p
  have heSignature : momentContractionSignature e = p.1.1 :=
    (mem_momentRefinedContractionFiber.mp
      (r324RefinedContractionRepresentative_mem p.2.2)).1
  have heCoarseSignature : momentContractionSignature eCoarse = p.1.1 :=
    mem_momentContractionFiber.mp
      (r324RefinedScheduleRepresentative_mem p)
  obtain ⟨hleftSignature, hrightSignature⟩ :=
    reductionEndpointSignatures_eq_of_momentContractionSignature_eq
      e eCoarse (heSignature.trans heCoarseSignature.symm)
  have hleftFinal : finalActive e.1 = finalActive eCoarse.1 :=
    finalActive_eq_of_reductionEndpointSignature_eq
      e.1 eCoarse.1 hleftSignature
  have hrightFinal : finalActive e.2.1 = finalActive eCoarse.2.1 :=
    finalActive_eq_of_reductionEndpointSignature_eq
      e.2.1 eCoarse.2.1 hrightSignature
  have hleftExtract :
      extractedRightEdges e.1 = extractedRightEdges eCoarse.1 :=
    extractedRightEdges_eq_of_extract_perm e.1 eCoarse.1
      (extract_perm_of_reductionEndpointSignature_eq
        e.1 eCoarse.1 hleftSignature)
  have hrightExtract :
      extractedRightEdges e.2.1 = extractedRightEdges eCoarse.2.1 :=
    extractedRightEdges_eq_of_extract_perm e.2.1 eCoarse.2.1
      (extract_perm_of_reductionEndpointSignature_eq
        e.2.1 eCoarse.2.1 hrightSignature)
  funext j
  fin_cases j <;>
    simp [r324ActualRefinedEndpointReductionCase,
      r324RefinedEndpointReductionCase,
      r324IncomingEndpointReductionCase, r324OutgoingIsShortcut,
      e, eCoarse, hleftFinal, hrightFinal,
      hleftExtract, hrightExtract]

/-- A residual single in the coarse schedule representative is therefore
also present in the refined-fibre representative used by the exact signed
physical collapse. -/
theorem r324RefinedContractionRepresentative_singles_nonempty
    {m : Nat} (p : R324RefinedScheduleIndex m)
    (hsingles :
      (r324RefinedScheduleRepresentative p).1.singles.Nonempty) :
    (r324RefinedContractionRepresentative
      m p.1.1 p.2.1).1.singles.Nonempty := by
  let e := r324RefinedContractionRepresentative m p.1.1 p.2.1
  let eCoarse := r324RefinedScheduleRepresentative p
  have heSignature : momentContractionSignature e = p.1.1 :=
    (mem_momentRefinedContractionFiber.mp
      (r324RefinedContractionRepresentative_mem p.2.2)).1
  have heCoarseSignature : momentContractionSignature eCoarse = p.1.1 :=
    mem_momentContractionFiber.mp
      (r324RefinedScheduleRepresentative_mem p)
  have hleftSignature :
      reductionEndpointSignature e.1 =
        reductionEndpointSignature eCoarse.1 :=
    (reductionEndpointSignatures_eq_of_momentContractionSignature_eq
      e eCoarse (heSignature.trans heCoarseSignature.symm)).1
  have hcoarseNotFull : ¬eCoarse.1.IsFull := by
    rw [PartialPairing.isFull_iff_singles_eq_empty]
    exact Finset.nonempty_iff_ne_empty.mp hsingles
  have heNotFull : ¬e.1.IsFull := by
    intro heFull
    exact hcoarseNotFull
      (isFull_of_reductionEndpointSignature_eq
        e.1 eCoarse.1 heFull hleftSignature.symm)
  change e.1.singles.Nonempty
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hempty
  exact heNotFull
    (PartialPairing.isFull_iff_singles_eq_empty.mpr hempty)

/-- Definitional four-bit classification for the actual refined
representative. -/
theorem r324ActualRefinedEndpointReductionCase_direct_iff
    {m : Nat} (hm : 0 < m) (p : R324RefinedScheduleIndex m) :
    (r324ActualRefinedEndpointReductionCase p 0 =
        R324EndpointReductionCase.directFourier ↔
      (⟨0, hm⟩ : Fin m) ∈ finalActive
        (r324RefinedContractionRepresentative m p.1.1 p.2.1).1) ∧
    (r324ActualRefinedEndpointReductionCase p 1 =
        R324EndpointReductionCase.directFourier ↔
      Fin.last m ∉ extractedRightEdges
        (r324RefinedContractionRepresentative m p.1.1 p.2.1).1) ∧
    (r324ActualRefinedEndpointReductionCase p 2 =
        R324EndpointReductionCase.directFourier ↔
      (⟨0, hm⟩ : Fin m) ∈ finalActive
        (r324RefinedContractionRepresentative m p.1.1 p.2.1).2.1) ∧
    (r324ActualRefinedEndpointReductionCase p 3 =
        R324EndpointReductionCase.directFourier ↔
      Fin.last m ∉ extractedRightEdges
        (r324RefinedContractionRepresentative m p.1.1 p.2.1).2.1) := by
  by_cases hleft : Fin.last m ∈ extractedRightEdges
      (r324RefinedContractionRepresentative m p.1.1 p.2.1).1 <;>
    by_cases hright : Fin.last m ∈ extractedRightEdges
      (r324RefinedContractionRepresentative m p.1.1 p.2.1).2.1 <;>
    simp [r324ActualRefinedEndpointReductionCase,
      r324IncomingEndpointReductionCase, hm,
      r324OutgoingIsShortcut, r324EndpointReductionCaseOfFlag,
      hleft, hright]

theorem r324ActualRefinedEndpointReductionCase_cases
    {m : Nat} (p : R324RefinedScheduleIndex m) :
    ∀ j : Fin 4,
      r324ActualRefinedEndpointReductionCase p j =
          R324EndpointReductionCase.directFourier ∨
        r324ActualRefinedEndpointReductionCase p j =
          R324EndpointReductionCase.insertedSacrifice := by
  intro j
  cases hcase : r324ActualRefinedEndpointReductionCase p j <;> simp

/-! ## The exact two-half endpoint ledger -/

/-- The two endpoint cases belonging to the left half, in the paper order
incoming then outgoing. -/
def r324LeftHalfEndpointCases
    (cases : Fin 4 → R324EndpointReductionCase) :
    R324PaperHalfEndpointCases :=
  ![cases 0, cases 1]

/-- The two endpoint cases belonging to the right half, in the paper order
incoming then outgoing. -/
def r324RightHalfEndpointCases
    (cases : Fin 4 → R324EndpointReductionCase) :
    R324PaperHalfEndpointCases :=
  ![cases 2, cases 3]

/-- Multiplying the two genuine half-chain endpoint costs gives exactly the
four-endpoint cost of Step 4(A).  In particular no uniform `epsilon^{-2}` is
inserted at a direct endpoint while the two halves are spliced. -/
theorem r324PaperHalfEndpointSacrifice_mul_eq_product
    (eps : Real) (cases : Fin 4 → R324EndpointReductionCase) :
    r324PaperHalfEndpointSacrifice eps
          (r324LeftHalfEndpointCases cases) *
        r324PaperHalfEndpointSacrifice eps
          (r324RightHalfEndpointCases cases) =
      r324EndpointPrimitiveSacrificeProduct eps cases := by
  simp only [r324PaperHalfEndpointSacrifice,
    r324LeftHalfEndpointCases, r324RightHalfEndpointCases,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    r324EndpointPrimitiveSacrificeProduct, Fin.prod_univ_four]
  ring

/-- The paper-faithful residual endpoint interface before the last uniform
`epsilon^{-8}` enlargement.  The physical producer records the four cases
of the representative which actually occurs in the signed collapse; a
direct endpoint therefore still has cost exactly one here. -/
def R324PaperResidualEndpointPatternWeightedMajorantBound
    (rho : SmoothCutoff) (primitiveConstant supportConstant : Real) : Prop :=
  forall {eps : Real} (m : Nat) (alpha beta : Z4),
    0 < eps -> eps <= 1 / 4 ->
      1 <= abs (Real.log eps) -> 2 <= m ->
        m <= truncOrder eps ->
          forall p : R324RefinedScheduleIndex m,
            (r324RefinedScheduleRepresentative p).1.singles.Nonempty ->
            abs (lamEps 1 eps) ^ (2 * m) *
                  norm (r324RefinedPhysicalIntegral
                    rho eps m alpha beta p) <=
                (paperFourthOrderModeDecay alpha *
                    paperFourthOrderModeDecay beta) *
                  (r324EndpointPrimitiveSacrificeProduct eps
                      (r324ActualRefinedEndpointReductionCase p) *
                    ∫ z : T4, primitiveInsertedMajorant
                      primitiveConstant 1 eps supportConstant m z
                      ∂paperMeasure)

/-- Only after the four signed endpoint operations have been assembled do
we replace their literal case product by the paper's uniform
`epsilon^{-8}` budget. -/
theorem R324PaperResidualEndpointPatternWeightedMajorantBound.to_uniform
    {rho : SmoothCutoff} {primitiveConstant supportConstant : Real}
    (h : R324PaperResidualEndpointPatternWeightedMajorantBound
      rho primitiveConstant supportConstant) :
    R324PaperResidualEndpointWeightedMajorantBound
      rho primitiveConstant supportConstant := by
  intro eps m alpha beta heps hepsSmall hlog hm2 hmtrunc p hsingles
  have heps1 : eps <= 1 := hepsSmall.trans (by norm_num)
  refine (h m alpha beta heps hepsSmall hlog hm2 hmtrunc p hsingles).trans ?_
  have hcases :=
    r324EndpointPrimitiveSacrificeProduct_le heps heps1
      (r324ActualRefinedEndpointReductionCase p)
  have hintegral :
      0 <= ∫ z : T4, primitiveInsertedMajorant
        primitiveConstant 1 eps supportConstant m z ∂paperMeasure :=
    integral_nonneg fun z =>
      primitiveInsertedMajorant_nonneg' primitiveConstant 1 eps
        supportConstant m z
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hcases hintegral)
    (mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
      (paperFourthOrderModeDecay_nonneg beta))

/-- Coarse-interface form of the genuine all-four-direct producer.  The
public residual branch is stated using the schedule representative, while
the signed collapse uses the representative of the residual-refined fibre.
Endpoint-signature rigidity supplies the bridge, and the stronger direct
estimate is enlarged to the common paper `epsilon^{-8}` currency only at
the final scalar step. -/
theorem exists_r324PaperResidualFourDirectBranchWeightedMajorantBound
    (rho : SmoothCutoff) :
    ∃ primitiveConstant supportConstant : Real,
      0 < primitiveConstant ∧ 0 < supportConstant ∧
      ∀ {eps : Real} (m : Nat) (alpha beta : Z4),
        0 < eps → eps <= 1 / 4 →
        1 <= abs (Real.log eps) → 2 <= m →
        m <= truncOrder eps →
        ∀ p : R324RefinedScheduleIndex m,
          (r324RefinedScheduleRepresentative p).1.singles.Nonempty →
          r324RefinedEndpointReductionCase p =
              (fun _ => R324EndpointReductionCase.directFourier) →
          abs (lamEps 1 eps) ^ (2 * m) *
              norm (r324RefinedPhysicalIntegral
                rho eps m alpha beta p) <=
            (paperFourthOrderModeDecay alpha *
                paperFourthOrderModeDecay beta) *
              (eps⁻¹ ^ (8 : Nat) *
                ∫ z : T4, primitiveInsertedMajorant
                  primitiveConstant 1 eps supportConstant m z
                  ∂paperMeasure) := by
  obtain ⟨primitiveConstant, supportConstant,
      hprimitiveConstant, hsupportConstant, hdirect⟩ :=
    exists_r324PaperFourDirectEndpointWeightedMajorantBound rho
  refine ⟨primitiveConstant, supportConstant,
    hprimitiveConstant, hsupportConstant, ?_⟩
  intro eps m alpha beta heps hepsSmall hlog hm2 hmtrunc p
    hsingles hcases
  have hm0 : 0 < m := by omega
  have heps1 : eps <= 1 := hepsSmall.trans (by norm_num)
  have hactualCases :
      r324ActualRefinedEndpointReductionCase p =
        (fun _ => R324EndpointReductionCase.directFourier) := by
    rw [r324ActualRefinedEndpointReductionCase_eq_refined]
    exact hcases
  have hbits :=
    r324ActualRefinedEndpointReductionCase_direct_iff hm0 p
  have hbit0 :
      r324ActualRefinedEndpointReductionCase p 0 =
        R324EndpointReductionCase.directFourier := by
    rw [hactualCases]
  have hbit1 :
      r324ActualRefinedEndpointReductionCase p 1 =
        R324EndpointReductionCase.directFourier := by
    rw [hactualCases]
  have hbit2 :
      r324ActualRefinedEndpointReductionCase p 2 =
        R324EndpointReductionCase.directFourier := by
    rw [hactualCases]
  have hbit3 :
      r324ActualRefinedEndpointReductionCase p 3 =
        R324EndpointReductionCase.directFourier := by
    rw [hactualCases]
  have hbound :=
    hdirect m alpha beta heps hepsSmall hlog hm2 hmtrunc p hm0
      (r324RefinedContractionRepresentative_singles_nonempty p hsingles)
      (hbits.1.mp hbit0) (hbits.2.1.mp hbit1)
      (hbits.2.2.1.mp hbit2) (hbits.2.2.2.mp hbit3)
  refine hbound.trans ?_
  have hinv : 1 <= eps⁻¹ ^ (8 : Nat) :=
    one_le_pow₀ ((one_le_inv₀ heps).2 heps1)
  have hintegral :
      0 <= ∫ z : T4, primitiveInsertedMajorant
        primitiveConstant 1 eps supportConstant m z ∂paperMeasure :=
    integral_nonneg fun z =>
      primitiveInsertedMajorant_nonneg hprimitiveConstant.le (by norm_num)
  apply mul_le_mul_of_nonneg_left
  · simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hinv hintegral
  · exact mul_nonneg
      (paperFourthOrderModeDecay_nonneg alpha)
      (paperFourthOrderModeDecay_nonneg beta)

end

end Anderson4D
