import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTwoHalfRouteAssembly

/-!
# The direct/exceptional half in paper Step 4(A)

This file contains only the literal outgoing ordinary-`J` operation needed
by a `DE x DD` endpoint pattern.  The proper prefix is removed while the
integrand is signed; the retained terminal is then evaluated by the paper's
ordinary primitive defect.  Its norm is taken only after that evaluation.

No route mass, auxiliary tree sum, or uniform `eps ^ (-8)` estimate is
introduced here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open SmoothCutoff
open scoped BigOperators

namespace R324WithinHalfResidualPrefix

namespace R324PaperOutgoingEndpointTerminal

variable {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}

/-- Generic retained-terminal chain identity.  It is the literal last
algebraic step of paper Step 4(A), valid independently of which endpoint
case selected the outgoing terminal. -/
theorem incomingErasedHeadOuterFactor_eq_terminalPost_endpointErasedSignedChain
    (data : R324PaperOutgoingEndpointTerminal res)
    (hpred :
      r324WithinHalfPredecessorSlot data.endpoint.stop.state
          data.terminalData.terminal ≠ 0)
    (hactive : data.terminalPost.state.active.Nonempty)
    (x y : T4)
    (v : data.terminalPost.SurvivingCoordinate -> T4) :
    data.endpoint.stop.incomingErasedHeadOuterFactor
        data.terminalData.terminal [] data.endpoint.stop_remaining
        rho eps x y v =
      data.terminalPost.endpointErasedSignedChain
        hactive x y (data.terminalPost.reconstruct v) := by
  have hpredOut :
      r324WithinHalfPredecessorSlot data.endpoint.stop.state
          data.terminalData.terminal =
        data.terminalPost.terminalOutgoingEdgeSlot hactive :=
    data.predecessorSlot_eq_terminalPost_outgoing hpred hactive
  unfold R324WithinHalfResidualPrefix.incomingErasedHeadOuterFactor
  rw [data.terminalPost.residualDifferenceProduct_of_remaining_nil
        data.terminalPost_remaining x y,
    data.terminalPost.residualPrimitiveProduct_of_remaining_nil
      data.terminalPost_remaining rho eps]
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
      have hpostSlots := data.endpoint.stop.afterHead_activeEdgeSlots
        data.terminalData.terminal [] data.endpoint.stop_remaining
      rw [hpostSlots] at hedgeActive
      exact (Finset.mem_sdiff.mp hedgeActive).2
        (Finset.mem_union_left _ hedgeInternal)
  · intro edge hedgeOuter hedgeNotEndpoint
    have hedgeZero := (Finset.mem_erase.mp hedgeOuter).1
    have hedgeNotHead := (Finset.mem_sdiff.mp
      (Finset.mem_erase.mp hedgeOuter).2).2
    by_cases hedgeActive : edge ∈ data.terminalPost.activeEdgeSlots
    · have hedgeOut : edge =
          data.terminalPost.terminalOutgoingEdgeSlot hactive := by
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
    · rw [data.terminalPost.residualChainEdgeFactor_of_remaining_nil
          data.terminalPost_remaining,
        if_neg hedgeActive]

end R324PaperOutgoingEndpointTerminal

namespace R324PaperHalfDirectExceptionalRoute

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}
    {incomingMode : Z4}
    {providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode}

/-- The structural `DE` route is exactly the canonical retained-terminal
geometry consumed by the signed outgoing endpoint theorem. -/
def geometry (data : R324PaperHalfDirectExceptionalRoute providers) :
    R324WithinHalfEndpointTerminalGeometry
      (ρ := rho) (lam := lam) (ε := eps) pairing where
  terminalData := data.terminalData
  transport := data.endpoint

@[simp]
theorem geometry_paperOutgoingTerminal
    (data : R324PaperHalfDirectExceptionalRoute providers) :
    data.geometry.paperOutgoingTerminal = data.outgoing := by
  rw [data.outgoing_eq]
  rfl

/-- The synchronized budget retained on the literal pre-terminal state is
a certificate for the terminal context appearing in the signed outgoing
defect. -/
theorem stopBudgetCertificate
    (data : R324PaperHalfDirectExceptionalRoute providers) :
    R324WithinHalfEdgeCertificate
      data.outgoing.terminalContext.state data.stopBudgetScale := by
  rw [data.outgoing_eq, data.endpoint_eq]
  exact data.stopCertificate

/-- Proposition 4.1 specialized to the retained outgoing terminal. -/
theorem outgoingProp41
    (data : R324PaperHalfDirectExceptionalRoute providers) :
    forall (H : Fin (2 * residualBlockOrder
          data.outgoing.terminalData.terminal.2 - 1) -> T4 -> Real),
      IsAdmissiblePrimitiveInput
          (residualBlockOrder data.outgoing.terminalData.terminal.2) H ->
        MemEClassT4
            (primitiveKernelDiff rho lam eps
              (residualBlockOrder data.outgoing.terminalData.terminal.2)
              data.outgoing.terminalContext.one_le_blockOrder H) /\
          MemEClassT4
            (primitiveKernelInsertedDiff rho lam eps
              (residualBlockOrder data.outgoing.terminalData.terminal.2)
              data.outgoing.terminalContext.one_le_blockOrder H) /\
          PrimitiveKernelBounds rho lam eps
            (residualBlockOrder data.outgoing.terminalData.terminal.2)
            data.outgoing.terminalContext.one_le_blockOrder H
            providers.supportConstant C := by
  rw [data.outgoing_eq, data.endpoint_eq]
  intro H hH
  exact providers.prop41Provider
    data.trace.stopPrefix data.terminalData.terminal []
    (by simpa using data.trace.stopPrefix_remaining_eq) H hH

/-- The direct prefix of a literal `DE` half contributes no exceptional
incoming multiplier. -/
theorem endpoint_multiplier_eq_one
    (data : R324PaperHalfDirectExceptionalRoute providers)
    (mode : Z4) :
    data.endpoint.multiplier mode = 1 := by
  rw [data.endpoint_eq]
  rfl

/-- The complete-budget scale obtained by consuming the retained outgoing
terminal.  This is the literal Step-4 budget update, not a new estimate. -/
def postBudgetScale
    (data : R324PaperHalfDirectExceptionalRoute providers) :
    Fin (m + 1) -> Real :=
  data.endpoint.stop.budgetUpdatedEdgeScale
    data.terminalData.terminal [] data.endpoint.stop_remaining
    data.stopBudgetScale C lam K

theorem postBudgetReachable
    (data : R324PaperHalfDirectExceptionalRoute providers) :
    R324WithinHalfBudgetScaleReachable pairing rho C lam eps K A
      data.outgoing.terminalPost.state data.postBudgetScale := by
  have hreachable :
      R324WithinHalfBudgetScaleReachable pairing rho C lam eps K A
        data.endpoint.stop.state data.stopBudgetScale := by
    rw [data.endpoint_eq]
    exact data.stopReachable
  have hcertificate :
      R324WithinHalfEdgeCertificate
        data.endpoint.stop.state data.stopBudgetScale := by
    rw [data.endpoint_eq]
    exact data.stopCertificate
  obtain ⟨_bound, reachable, _certificate⟩ :=
    providers.budgetProvider data.endpoint.stop
      data.terminalData.terminal [] data.endpoint.stop_remaining
      data.stopBudgetScale hreachable hcertificate
  rw [data.outgoing_eq]
  simpa only [postBudgetScale,
    R324PaperOutgoingEndpointTerminal.terminalPost] using reachable

theorem postBudgetCertificate
    (data : R324PaperHalfDirectExceptionalRoute providers) :
    R324WithinHalfEdgeCertificate
      data.outgoing.terminalPost.state data.postBudgetScale := by
  have hreachable :
      R324WithinHalfBudgetScaleReachable pairing rho C lam eps K A
        data.endpoint.stop.state data.stopBudgetScale := by
    rw [data.endpoint_eq]
    exact data.stopReachable
  have hcertificate :
      R324WithinHalfEdgeCertificate
        data.endpoint.stop.state data.stopBudgetScale := by
    rw [data.endpoint_eq]
    exact data.stopCertificate
  obtain ⟨_bound, _reachable, certificate⟩ :=
    providers.budgetProvider data.endpoint.stop
      data.terminalData.terminal [] data.endpoint.stop_remaining
      data.stopBudgetScale hreachable hcertificate
  rw [data.outgoing_eq]
  simpa only [postBudgetScale,
    R324PaperOutgoingEndpointTerminal.terminalPost] using certificate

/-- The canonical post-terminal update and the completed route have the
same active scale product because both are complete reachable histories on
the same final state. -/
theorem postBudget_activeProduct_eq_route
    (data : R324PaperHalfDirectExceptionalRoute providers) :
    (∏ edge ∈ data.outgoing.terminalPost.activeEdgeSlots,
        data.postBudgetScale edge) =
      ∏ edge ∈ data.outgoing.terminalPost.activeEdgeSlots,
        data.route.terminalScale edge := by
  have hpost := data.postBudgetReachable.activeEdgeScaleProduct_eq
  have hroute := data.route.terminalReachable.activeEdgeScaleProduct_eq
  rw [data.route_final] at hroute
  exact hpost.trans hroute.symm

theorem postBudgetScale_zero_eq_stopBudget
    (data : R324PaperHalfDirectExceptionalRoute providers) :
    data.postBudgetScale 0 = data.stopBudgetScale 0 := by
  unfold postBudgetScale
  rw [data.endpoint.stop.budgetUpdatedEdgeScale_of_ne]
  exact Ne.symm data.predecessor_ne_zero

/-- The outgoing ordinary-`J` local block charge is exactly one boundary
slot of the post-terminal complete budget, up to the already assumed
`A >= 1`. -/
theorem outgoingBudgetCore_le_postBudget_outgoingScale
    (data : R324PaperHalfDirectExceptionalRoute providers) :
    data.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) *
        r324WithinHalfInternalEdgeScaleProduct
          data.outgoing.terminalContext data.stopBudgetScale *
        (C * lam) ^
          (2 * residualBlockOrder
            data.outgoing.terminalData.terminal.2) * K <=
      data.postBudgetScale
        (data.outgoing.terminalPost.terminalOutgoingEdgeSlot
          data.terminalPost_active) := by
  have hpred :
      r324WithinHalfPredecessorSlot data.outgoing.endpoint.stop.state
          data.outgoing.terminalData.terminal ≠ 0 := by
    rw [data.outgoing_eq]
    exact data.predecessor_ne_zero
  have hpredOut :=
    data.outgoing.predecessorSlot_eq_terminalPost_outgoing
      hpred data.terminalPost_active
  have hreachable :
      R324WithinHalfBudgetScaleReachable pairing rho C lam eps K A
        data.endpoint.stop.state data.stopBudgetScale := by
    rw [data.endpoint_eq]
    exact data.stopReachable
  have hout :
      data.stopBudgetScale
          (data.endpoint.stop.headContext data.terminalData.terminal []
            data.endpoint.stop_remaining).outgoingSlot = A := by
    exact hreachable.outgoingScale_eq_base
      data.endpoint.stop rfl data.terminalData.terminal []
      data.endpoint.stop_remaining
  rw [← hpredOut]
  rw [data.outgoing_eq] at ⊢
  unfold postBudgetScale
  rw [data.endpoint.stop.budgetUpdatedEdgeScale_predecessor,
    data.endpoint.stop.headBlockScaleProduct_eq_internal_mul_outgoing]
  change
    data.stopBudgetScale
          (r324WithinHalfPredecessorSlot data.endpoint.stop.state
            data.terminalData.terminal) *
        r324WithinHalfInternalEdgeScaleProduct
          (data.endpoint.stop.headContext data.terminalData.terminal []
            data.endpoint.stop_remaining) data.stopBudgetScale *
        (C * lam) ^
          (2 * residualBlockOrder data.terminalData.terminal.2) * K <=
      data.stopBudgetScale
          (r324WithinHalfPredecessorSlot data.endpoint.stop.state
            data.terminalData.terminal) *
        (r324WithinHalfInternalEdgeScaleProduct
            (data.endpoint.stop.headContext data.terminalData.terminal []
              data.endpoint.stop_remaining) data.stopBudgetScale *
          data.stopBudgetScale
            (data.endpoint.stop.headContext data.terminalData.terminal []
              data.endpoint.stop_remaining).outgoingSlot) *
        (C * lam) ^
          (2 * residualBlockOrder data.terminalData.terminal.2) * K
  rw [hout]
  have hpredScale :
      0 <= data.stopBudgetScale
        (r324WithinHalfPredecessorSlot data.endpoint.stop.state
          data.terminalData.terminal) :=
    data.stopCertificate.scale_pos _ |>.le
  have hinternal :
      0 <= r324WithinHalfInternalEdgeScaleProduct
        (data.endpoint.stop.headContext data.terminalData.terminal []
          data.endpoint.stop_remaining) data.stopBudgetScale :=
    (by
      have hcertificate :
          R324WithinHalfEdgeCertificate
            data.endpoint.stop.state data.stopBudgetScale := by
        rw [data.endpoint_eq]
        exact data.stopCertificate
      exact hcertificate.internalEdgeScaleProduct_pos.le)
  have hpow :
      0 <= (C * lam) ^
        (2 * residualBlockOrder data.terminalData.terminal.2) := by
    exact (even_two_mul
      (residualBlockOrder data.terminalData.terminal.2)).pow_nonneg _
  have hK0 : 0 <= K := zero_le_one.trans providers.hK
  let core :=
    data.stopBudgetScale
        (r324WithinHalfPredecessorSlot data.endpoint.stop.state
          data.terminalData.terminal) *
      r324WithinHalfInternalEdgeScaleProduct
        (data.endpoint.stop.headContext data.terminalData.terminal []
          data.endpoint.stop_remaining) data.stopBudgetScale *
      (C * lam) ^
        (2 * residualBlockOrder data.terminalData.terminal.2) * K
  have hcore : 0 <= core := by
    dsimp only [core]
    exact mul_nonneg (mul_nonneg (mul_nonneg hpredScale hinternal) hpow) hK0
  calc
    _ = core := by dsimp only [core]
    _ <= core * A := le_mul_of_one_le_right hcore providers.hA
    _ = _ := by dsimp only [core]; ring

/-- The direct incoming budget, the retained outgoing local charge, and
the erased post-terminal chain occupy precisely the three factors of the
completed active scale product. -/
theorem boundaryCore_mul_endpointErasedScale_le_routeActiveProduct
    (data : R324PaperHalfDirectExceptionalRoute providers) :
    data.stopBudgetScale 0 *
        (data.stopBudgetScale
            (r324WithinHalfPredecessorSlot
              data.outgoing.terminalContext.state
              data.outgoing.terminalContext.step) *
          r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.stopBudgetScale *
          (C * lam) ^
            (2 * residualBlockOrder
              data.outgoing.terminalData.terminal.2) * K) *
        data.outgoing.terminalPost.endpointErasedScaleProduct
          data.terminalPost_active data.postBudgetScale <=
      ∏ edge ∈ data.outgoing.terminalPost.activeEdgeSlots,
        data.route.terminalScale edge := by
  have hout := data.outgoingBudgetCore_le_postBudget_outgoingScale
  have hzero := data.postBudgetScale_zero_eq_stopBudget
  have herased :
      0 <= data.outgoing.terminalPost.endpointErasedScaleProduct
        data.terminalPost_active data.postBudgetScale := by
    unfold R324WithinHalfResidualPrefix.endpointErasedScaleProduct
    exact Finset.prod_nonneg fun edge _ =>
      (data.postBudgetCertificate.scale_pos edge).le
  calc
    data.stopBudgetScale 0 *
          (data.stopBudgetScale
              (r324WithinHalfPredecessorSlot
                data.outgoing.terminalContext.state
                data.outgoing.terminalContext.step) *
            r324WithinHalfInternalEdgeScaleProduct
              data.outgoing.terminalContext data.stopBudgetScale *
            (C * lam) ^
              (2 * residualBlockOrder
                data.outgoing.terminalData.terminal.2) * K) *
          data.outgoing.terminalPost.endpointErasedScaleProduct
            data.terminalPost_active data.postBudgetScale <=
        data.postBudgetScale 0 *
          data.postBudgetScale
            (data.outgoing.terminalPost.terminalOutgoingEdgeSlot
              data.terminalPost_active) *
          data.outgoing.terminalPost.endpointErasedScaleProduct
            data.terminalPost_active data.postBudgetScale := by
      rw [hzero]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hout
          (data.stopCertificate.scale_pos 0).le) herased
    _ = ∏ edge ∈ data.outgoing.terminalPost.activeEdgeSlots,
          data.postBudgetScale edge := by
      rw [data.outgoing.terminalPost
        |>.activeEdgeScaleProduct_eq_boundary_mul_endpointErased]
    _ = _ := data.postBudget_activeProduct_eq_route

/-- After the signed retained-terminal identity, its outer factor is the
literal endpoint-erased post chain. -/
theorem norm_terminalSplitOuter_le_postBudgetMajorant
    (data : R324PaperHalfDirectExceptionalRoute providers)
    (coefficient :
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (x : T4)
    (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4)
    (hne : ∀ edge,
      edge ∈ data.outgoing.terminalPost.endpointErasedActiveEdgeSlots
          data.terminalPost_active →
        data.outgoing.terminalPost.edgeDisplacement 0 0
          (data.outgoing.terminalPost.reconstruct v) edge ≠ 0) :
    ‖data.outgoing.terminalSplitOuter coefficient incomingMode x v‖ <=
      ‖coefficient v‖ *
        (data.outgoing.terminalPost.endpointErasedScaleProduct
            data.terminalPost_active data.postBudgetScale *
          data.outgoing.terminalPost.endpointErasedInvSqChainProduct
            data.terminalPost_active v) := by
  have hpred :
      r324WithinHalfPredecessorSlot data.outgoing.endpoint.stop.state
          data.outgoing.terminalData.terminal ≠ 0 := by
    rw [data.outgoing_eq]
    exact data.predecessor_ne_zero
  have hchain :=
    data.outgoing.terminalPost.abs_endpointErasedSignedChain_le
      data.terminalPost_active data.postBudgetCertificate
      data.outgoing.terminalPost_remaining 0 0
      (data.outgoing.terminalPost.reconstruct v) hne
  have herased :=
    data.outgoing
      |>.incomingErasedHeadOuterFactor_eq_terminalPost_endpointErasedSignedChain
        hpred data.terminalPost_active x 0 v
  unfold R324PaperOutgoingEndpointTerminal.terminalSplitOuter
  rw [herased,
    data.outgoing.terminalPost.endpointErasedSignedChain_eq_zeroEndpoints
      data.terminalPost_active x 0]
  simp only [norm_mul, norm_charT4, mul_one, Complex.norm_real,
    Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [R324WithinHalfResidualPrefix.endpointErasedInvSqChainProduct]
      using hchain)
    (norm_nonneg _)

/-- Literal numerical exit of the exceptional outgoing endpoint.  The
ordinary primitive defect is bounded by Proposition 4.1 and converted to
the inserted-kernel currency with exactly one endpoint sacrifice. -/
theorem norm_integral_outgoingEndpointDefectDensity_le_inserted
    (data : R324PaperHalfDirectExceptionalRoute providers)
    (coefficient :
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4) (x : T4)
    (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4) :
    ‖∫ first : T4,
        data.outgoing.outgoingEndpointDefectDensity coefficient
          incomingMode outgoingMode x v first
        ∂paperMeasure‖ <=
      (data.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) *
          invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode *
        (2 * r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.stopBudgetScale *
          (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
            ∫ gap : T4,
              primitiveInsertedMajorant C lam eps
                providers.supportConstant
                (residualBlockOrder
                  data.outgoing.terminalData.terminal.2) gap
              ∂paperMeasure)) *
        ‖data.outgoing.terminalSplitOuter
          coefficient incomingMode x v‖ := by
  exact data.outgoing
    |>.norm_integral_outgoingEndpointDefectDensity_le_inserted_of_certificate
      data.stopBudgetScale data.stopBudgetCertificate coefficient
      incomingMode outgoingMode x v providers.heps providers.hC
      providers.hlam data.outgoingProp41

/-- Pay the one inserted primitive integral by the existing local block
constant.  The literal exceptional endpoint sacrifice is not enlarged. -/
theorem norm_integral_outgoingEndpointDefectDensity_le_budgeted
    (data : R324PaperHalfDirectExceptionalRoute providers)
    (coefficient :
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4) (x : T4)
    (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4) :
    ‖∫ first : T4,
        data.outgoing.outgoingEndpointDefectDensity coefficient
          incomingMode outgoingMode x v first
        ∂paperMeasure‖ <=
      (data.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) *
          invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode *
        (r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.stopBudgetScale *
          (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
            ((C * lam) ^
              (2 * residualBlockOrder
                data.outgoing.terminalData.terminal.2) * K))) *
        ‖data.outgoing.terminalSplitOuter
          coefficient incomingMode x v‖ := by
  refine
    (data.norm_integral_outgoingEndpointDefectDensity_le_inserted
      coefficient outgoingMode x v).trans ?_
  have hcharge := providers.outgoingInsertedBudget
    (residualBlockOrder data.outgoing.terminalData.terminal.2)
    data.outgoing.terminalContext.one_le_blockOrder
  have hfront :
      0 <=
        (data.stopBudgetScale
            (r324WithinHalfPredecessorSlot
              data.outgoing.terminalContext.state
              data.outgoing.terminalContext.step) * invSqKerMass) *
          paperSecondOrderModeDecay outgoingMode := by
    exact mul_nonneg
      (mul_nonneg (data.stopBudgetCertificate.scale_pos _).le
        invSqKerMass_nonneg)
      (paperSecondOrderModeDecay_nonneg outgoingMode)
  have hinternal :
      0 <= r324WithinHalfInternalEdgeScaleProduct
        data.outgoing.terminalContext data.stopBudgetScale :=
    data.stopBudgetCertificate.internalEdgeScaleProduct_pos.le
  have hsac :
      0 <= r324EndpointPrimitiveSacrifice eps .insertedSacrifice :=
    r324EndpointPrimitiveSacrifice_nonneg eps _
  have houter :
      0 <= ‖data.outgoing.terminalSplitOuter
        coefficient incomingMode x v‖ := norm_nonneg _
  calc
    (data.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) * invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode *
        (2 * r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.stopBudgetScale *
          (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
            ∫ gap : T4,
              primitiveInsertedMajorant C lam eps
                providers.supportConstant
                (residualBlockOrder
                  data.outgoing.terminalData.terminal.2) gap
              ∂paperMeasure)) *
        ‖data.outgoing.terminalSplitOuter coefficient incomingMode x v‖ =
      ((data.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) * invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode) *
        (r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.stopBudgetScale *
          r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
          (2 * ∫ gap : T4,
            primitiveInsertedMajorant C lam eps
              providers.supportConstant
              (residualBlockOrder
                data.outgoing.terminalData.terminal.2) gap
            ∂paperMeasure)) *
        ‖data.outgoing.terminalSplitOuter coefficient incomingMode x v‖ := by
      ring
    _ <=
      ((data.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) * invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode) *
        (r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.stopBudgetScale *
          r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
          ((C * lam) ^
            (2 * residualBlockOrder
              data.outgoing.terminalData.terminal.2) * K)) *
        ‖data.outgoing.terminalSplitOuter coefficient incomingMode x v‖ := by
      gcongr
    _ = _ := by ring

/-- The direct incoming Green leg after its exact Fourier integration.
The phase is already carried by `terminalSplitOuter`; hence the only new
scalar is the literal second-order Fourier multiplier. -/
def directIncomingEndpointCoefficient
    (data : R324PaperHalfDirectExceptionalRoute providers)
    (coefficient :
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4) : Complex :=
  (paperSecondOrderModeDecay incomingMode : Complex) * coefficient v

theorem norm_directIncomingEndpointCoefficient
    (data : R324PaperHalfDirectExceptionalRoute providers)
    (coefficient :
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4) :
    ‖data.directIncomingEndpointCoefficient coefficient v‖ =
      paperSecondOrderModeDecay incomingMode * ‖coefficient v‖ := by
  unfold directIncomingEndpointCoefficient
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperSecondOrderModeDecay_nonneg incomingMode)]

/-- One complete literal `DE` half after the direct incoming Fourier
operation and the signed retained outgoing-terminal operation. -/
def endpointDensity
    (data : R324PaperHalfDirectExceptionalRoute providers)
    (coefficient :
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4) (x : T4)
    (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4) : Complex :=
  ∫ first : T4,
    data.outgoing.outgoingEndpointDefectDensity
      (data.directIncomingEndpointCoefficient coefficient)
      incomingMode outgoingMode x v first
    ∂paperMeasure

/-- Pointwise Step 4(A) estimate for the literal direct/exceptional half.
The norm is taken only after both endpoint operations.  The synchronized
ordinary prefix keeps `stopBudgetScale 0 = A`; its assumed `A >= 1` pays
the otherwise harmless direct incoming boundary slot. -/
theorem norm_endpointDensity_le
    (data : R324PaperHalfDirectExceptionalRoute providers)
    (coefficient :
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4) (x : T4)
    (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4)
    (hne : ∀ edge ∈
        data.outgoing.terminalPost.endpointErasedActiveEdgeSlots
          data.terminalPost_active,
      data.outgoing.terminalPost.edgeDisplacement 0 0
        (data.outgoing.terminalPost.reconstruct v) edge ≠ 0) :
    ‖data.endpointDensity coefficient outgoingMode x v‖ <=
      (paperSecondOrderModeDecay incomingMode *
          paperSecondOrderModeDecay outgoingMode) *
        (r324EndpointPrimitiveSacrifice eps .directFourier *
          r324EndpointPrimitiveSacrifice eps .insertedSacrifice) *
        ((∏ edge ∈ data.outgoing.terminalPost.activeEdgeSlots,
            data.route.terminalScale edge) * invSqKerMass) *
        data.outgoing.terminalPost.endpointErasedInvSqChainProduct
          data.terminalPost_active v * ‖coefficient v‖ := by
  have hout :=
    data.norm_integral_outgoingEndpointDefectDensity_le_budgeted
      (data.directIncomingEndpointCoefficient coefficient)
      outgoingMode x v
  have houter := data.norm_terminalSplitOuter_le_postBudgetMajorant
    (data.directIncomingEndpointCoefficient coefficient) x v hne
  have hincoming := data.norm_directIncomingEndpointCoefficient coefficient v
  have hboundary :=
    data.boundaryCore_mul_endpointErasedScale_le_routeActiveProduct
  have hstopOne : 1 <= data.stopBudgetScale 0 := by
    rw [data.stopBudgetScale_zero_eq_base]
    exact providers.hA
  have hdin := paperSecondOrderModeDecay_nonneg incomingMode
  have hdout := paperSecondOrderModeDecay_nonneg outgoingMode
  have hsac := r324EndpointPrimitiveSacrifice_nonneg eps
    R324EndpointReductionCase.insertedSacrifice
  have hmass := invSqKerMass_nonneg
  have hpath :=
    data.outgoing.terminalPost.endpointErasedInvSqChainProduct_nonneg
      data.terminalPost_active v
  have hprefix :
      0 <=
        (data.stopBudgetScale
              (r324WithinHalfPredecessorSlot
                data.outgoing.terminalContext.state
                data.outgoing.terminalContext.step) * invSqKerMass) *
          paperSecondOrderModeDecay outgoingMode *
          (r324WithinHalfInternalEdgeScaleProduct
              data.outgoing.terminalContext data.stopBudgetScale *
            (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
              ((C * lam) ^
                (2 * residualBlockOrder
                  data.outgoing.terminalData.terminal.2) * K))) := by
    have hpredecessor :=
      (data.stopBudgetCertificate.scale_pos
        (r324WithinHalfPredecessorSlot
          data.outgoing.terminalContext.state
          data.outgoing.terminalContext.step)).le
    have hinternal :=
      data.stopBudgetCertificate.internalEdgeScaleProduct_pos.le
    have hpow :
        0 <= (C * lam) ^
          (2 * residualBlockOrder
            data.outgoing.terminalData.terminal.2) :=
      (even_two_mul _).pow_nonneg _
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hpredecessor hmass) hdout)
      (mul_nonneg hinternal
        (mul_nonneg hsac (mul_nonneg hpow providers.hK_nonneg)))
  have hpostFactor :
      0 <=
        data.outgoing.terminalPost.endpointErasedScaleProduct
            data.terminalPost_active data.postBudgetScale *
          data.outgoing.terminalPost.endpointErasedInvSqChainProduct
            data.terminalPost_active v := by
    have hpostScale :
        0 <= data.outgoing.terminalPost.endpointErasedScaleProduct
          data.terminalPost_active data.postBudgetScale := by
      unfold R324WithinHalfResidualPrefix.endpointErasedScaleProduct
      exact Finset.prod_nonneg fun edge _ =>
        (data.postBudgetCertificate.scale_pos edge).le
    exact mul_nonneg hpostScale hpath
  refine hout.trans ?_
  calc
    (data.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) * invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode *
        (r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.stopBudgetScale *
          (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
            ((C * lam) ^
              (2 * residualBlockOrder
                data.outgoing.terminalData.terminal.2) * K))) *
        ‖data.outgoing.terminalSplitOuter
          (data.directIncomingEndpointCoefficient coefficient)
          incomingMode x v‖ <=
      (data.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) * invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode *
        (r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.stopBudgetScale *
          (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
            ((C * lam) ^
              (2 * residualBlockOrder
                data.outgoing.terminalData.terminal.2) * K))) *
        (‖data.directIncomingEndpointCoefficient coefficient v‖ *
          (data.outgoing.terminalPost.endpointErasedScaleProduct
              data.terminalPost_active data.postBudgetScale *
            data.outgoing.terminalPost.endpointErasedInvSqChainProduct
              data.terminalPost_active v)) := by
      exact mul_le_mul_of_nonneg_left houter hprefix
    _ =
      (data.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) * invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode *
        (r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.stopBudgetScale *
          (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
            ((C * lam) ^
              (2 * residualBlockOrder
                data.outgoing.terminalData.terminal.2) * K))) *
        ((paperSecondOrderModeDecay incomingMode * ‖coefficient v‖) *
          (data.outgoing.terminalPost.endpointErasedScaleProduct
              data.terminalPost_active data.postBudgetScale *
            data.outgoing.terminalPost.endpointErasedInvSqChainProduct
              data.terminalPost_active v)) := by rw [hincoming]
    _ =
      (paperSecondOrderModeDecay incomingMode *
          paperSecondOrderModeDecay outgoingMode) *
        r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
        invSqKerMass *
        ((data.stopBudgetScale
            (r324WithinHalfPredecessorSlot
              data.outgoing.terminalContext.state
              data.outgoing.terminalContext.step) *
          r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.stopBudgetScale *
          (C * lam) ^
            (2 * residualBlockOrder
              data.outgoing.terminalData.terminal.2) * K) *
          data.outgoing.terminalPost.endpointErasedScaleProduct
            data.terminalPost_active data.postBudgetScale) *
        data.outgoing.terminalPost.endpointErasedInvSqChainProduct
          data.terminalPost_active v * ‖coefficient v‖ := by
      ring
    _ <=
      (paperSecondOrderModeDecay incomingMode *
          paperSecondOrderModeDecay outgoingMode) *
        r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
        invSqKerMass *
        (data.stopBudgetScale 0 *
          (data.stopBudgetScale
              (r324WithinHalfPredecessorSlot
                data.outgoing.terminalContext.state
                data.outgoing.terminalContext.step) *
            r324WithinHalfInternalEdgeScaleProduct
              data.outgoing.terminalContext data.stopBudgetScale *
            (C * lam) ^
              (2 * residualBlockOrder
                data.outgoing.terminalData.terminal.2) * K) *
          data.outgoing.terminalPost.endpointErasedScaleProduct
            data.terminalPost_active data.postBudgetScale) *
        data.outgoing.terminalPost.endpointErasedInvSqChainProduct
          data.terminalPost_active v * ‖coefficient v‖ := by
      have hcore :
          0 <=
            (paperSecondOrderModeDecay incomingMode *
                paperSecondOrderModeDecay outgoingMode) *
              r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
              invSqKerMass *
              ((data.stopBudgetScale
                  (r324WithinHalfPredecessorSlot
                    data.outgoing.terminalContext.state
                    data.outgoing.terminalContext.step) *
                r324WithinHalfInternalEdgeScaleProduct
                  data.outgoing.terminalContext data.stopBudgetScale *
                (C * lam) ^
                  (2 * residualBlockOrder
                    data.outgoing.terminalData.terminal.2) * K) *
                data.outgoing.terminalPost.endpointErasedScaleProduct
                  data.terminalPost_active data.postBudgetScale) *
              data.outgoing.terminalPost.endpointErasedInvSqChainProduct
                data.terminalPost_active v * ‖coefficient v‖ := by
        have hpred :=
          (data.stopBudgetCertificate.scale_pos
            (r324WithinHalfPredecessorSlot
              data.outgoing.terminalContext.state
              data.outgoing.terminalContext.step)).le
        have hinternal :=
          data.stopBudgetCertificate.internalEdgeScaleProduct_pos.le
        have hpow :
            0 <= (C * lam) ^
              (2 * residualBlockOrder
                data.outgoing.terminalData.terminal.2) :=
          (even_two_mul _).pow_nonneg _
        have hpostScale :
            0 <= data.outgoing.terminalPost.endpointErasedScaleProduct
              data.terminalPost_active data.postBudgetScale := by
          unfold R324WithinHalfResidualPrefix.endpointErasedScaleProduct
          exact Finset.prod_nonneg fun edge _ =>
            (data.postBudgetCertificate.scale_pos edge).le
        have hK0 : 0 <= K := providers.hK_nonneg
        positivity
      calc
        _ = 1 * _ := by ring
        _ <= data.stopBudgetScale 0 * _ :=
          mul_le_mul_of_nonneg_right hstopOne hcore
        _ = _ := by ring
    _ <=
      (paperSecondOrderModeDecay incomingMode *
          paperSecondOrderModeDecay outgoingMode) *
        r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
        invSqKerMass *
        (∏ edge ∈ data.outgoing.terminalPost.activeEdgeSlots,
          data.route.terminalScale edge) *
        data.outgoing.terminalPost.endpointErasedInvSqChainProduct
          data.terminalPost_active v * ‖coefficient v‖ := by
      gcongr
    _ = _ := by
      simp only [r324EndpointPrimitiveSacrifice]
      ring

end R324PaperHalfDirectExceptionalRoute

namespace R324PaperTwoHalfEndpointRoutes

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {leftMode rightMode : Z4}
    {leftProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP leftMode}
    {rightProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM rightMode}

/-- The literal terminal carrier of the `DE x DD` row of the paper's
endpoint table. -/
def directExceptionalDirectDirectTerminalData
    (leftDE : R324PaperHalfDirectExceptionalRoute leftProviders)
    (rightDD : R324PaperHalfDirectDirectRoute rightProviders) :
    R324TwoHalfTerminalData rho lam eps kappaP kappaM where
  left := leftDE.outgoing.terminalPost
  right := rightDD.transport.final
  left_remaining := leftDE.outgoing.terminalPost_remaining
  right_remaining := rightDD.transport.final_remaining
  left_processed := leftDE.outgoing.terminalPost_processed_eq_schedule
  right_processed := rightDD.transport.final_processed_eq_schedule

/-- The common completed-route terminal does not forget either concrete
carrier used by the signed `DE x DD` splice. -/
theorem terminal_directExceptional_directDirect_eq
    (hleftFirst : (⟨0, leftProviders.hm⟩ : Fin m) ∈ finalActive kappaP)
    (hleftOutgoing : Fin.last m ∈ extractedRightEdges kappaP)
    (leftDE : R324PaperHalfDirectExceptionalRoute leftProviders)
    (hrightFirst : (⟨0, rightProviders.hm⟩ : Fin m) ∈ finalActive kappaM)
    (hrightOutgoing : Fin.last m ∉ extractedRightEdges kappaM)
    (rightDD : R324PaperHalfDirectDirectRoute rightProviders) :
    (R324PaperTwoHalfEndpointRoutes.terminal
      ({ left := .directExceptional hleftFirst hleftOutgoing leftDE
         right := .directDirect hrightFirst hrightOutgoing rightDD } :
        R324PaperTwoHalfEndpointRoutes leftProviders rightProviders)) =
      directExceptionalDirectDirectTerminalData leftDE rightDD := by
  unfold R324PaperTwoHalfEndpointRoutes.terminal
    R324PaperHalfEndpointRoute.completedRoute
    R324PaperHalfCompletedRoute.twoHalfTerminal
    directExceptionalDirectDirectTerminalData
  rw [R324TwoHalfTerminalData.mk.injEq]
  exact ⟨leftDE.route_final, rightDD.route_final⟩

/-- The concrete cost pattern is exactly `direct, inserted, direct,
direct`; no uniform `eps ^ (-8)` charge is inserted. -/
@[simp]
theorem cases_directExceptional_directDirect
    (hleftFirst : (⟨0, leftProviders.hm⟩ : Fin m) ∈ finalActive kappaP)
    (hleftOutgoing : Fin.last m ∈ extractedRightEdges kappaP)
    (leftDE : R324PaperHalfDirectExceptionalRoute leftProviders)
    (hrightFirst : (⟨0, rightProviders.hm⟩ : Fin m) ∈ finalActive kappaM)
    (hrightOutgoing : Fin.last m ∉ extractedRightEdges kappaM)
    (rightDD : R324PaperHalfDirectDirectRoute rightProviders) :
    (R324PaperTwoHalfEndpointRoutes.cases
      ({ left := .directExceptional hleftFirst hleftOutgoing leftDE
         right := .directDirect hrightFirst hrightOutgoing rightDD } :
        R324PaperTwoHalfEndpointRoutes leftProviders rightProviders)) =
      ![R324EndpointReductionCase.directFourier,
        R324EndpointReductionCase.insertedSacrifice,
        R324EndpointReductionCase.directFourier,
        R324EndpointReductionCase.directFourier] := by
  unfold R324PaperTwoHalfEndpointRoutes.cases
    R324PaperHalfEndpointRoute.completedRoute
    R324PaperHalfCompletedRoute.combinedCases
  rw [leftDE.route_cases, rightDD.route_cases]
  funext i
  fin_cases i <;> rfl

end R324PaperTwoHalfEndpointRoutes
end R324WithinHalfResidualPrefix

end

end Anderson4D
