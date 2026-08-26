import Anderson4D.DetParametrix.Paper42_Moment.R324PaperLeftTargetIntegrability
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfEndpointRouteCases
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRightDirectIncomingSourceBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324FrequencyConservation

/-!
# The completed left endpoint half, in all four literal cases

This is the paper Step 4(A) case split for the first half only.  Each branch
uses its existing exact signed transform and its existing joint `L¹` handoff.
No estimate and no absolute value occurs here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

/-! ## Common-translation geometry of a completed terminal half -/

variable {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}

/-- Reconstruction of a surviving terminal coordinate commutes with a
common translation. -/
theorem reconstruct_commonTranslate_of_active
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (v : res.SurvivingCoordinate → T4) (a : T4)
    (i : Fin m) (hi : i ∈ res.state.active) :
    res.reconstruct (fun j => v j + a) i =
      res.reconstruct v i + a := by
  simp only [R324WithinHalfResidualPrefix.reconstruct, hi, dite_true]

private theorem endpointErased_edgeDisplacement_commonTranslate
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (hactive : res.state.active.Nonempty)
    (x y : T4) (v : res.SurvivingCoordinate → T4) (a : T4)
    {edge : Fin (m + 1)}
    (hedge : edge ∈ res.endpointErasedActiveEdgeSlots hactive) :
    res.edgeDisplacement x y
        (res.reconstruct (fun j => v j + a)) edge =
      res.edgeDisplacement x y (res.reconstruct v) edge := by
  have hedgeActive :=
    res.mem_activeEdgeSlots_of_mem_endpointErased hactive hedge
  have hedgeZero := res.ne_zero_of_mem_endpointErased hactive hedge
  rw [R324WithinHalfResidualPrefix.activeEdgeSlots] at hedgeActive
  rcases Finset.mem_union.mp hedgeActive with hzero | hsource
  · exact (hedgeZero (by simpa using hzero)).elim
  · obtain ⟨source, hsourceActive, hsourceEdge⟩ :=
      Finset.mem_image.mp hsource
    obtain ⟨target, htargetEdge⟩ :=
      res.exists_targetInternalIndex_of_mem_endpointErased hactive hedge
    have htargetCandidate := res.edgeSuccessor_mem_candidates edge
    rw [R324WithinHalfResidualPrefix.edgeSuccessorCandidates]
      at htargetCandidate
    rcases Finset.mem_union.mp htargetCandidate with
      htargetLast | htargetInternal
    · have hvarLast : varIdx target = Fin.last (m + 1) := by
        rw [← htargetEdge]
        simpa using htargetLast
      have hval := congrArg Fin.val hvarLast
      simp only [varIdx_val, Fin.val_last] at hval
      omega
    · obtain ⟨target', htargetActive, htargetEq⟩ :=
        Finset.mem_image.mp htargetInternal
      have hsourceCast : edge.castSucc = varIdx source := by
        rw [← hsourceEdge]
        rfl
      have htarget' : res.edgeSuccessor edge = varIdx target' :=
        htargetEq.symm
      unfold R324WithinHalfResidualPrefix.edgeDisplacement
      rw [hsourceCast, htarget', assemble_varIdx, assemble_varIdx,
        assemble_varIdx, assemble_varIdx,
        reconstruct_commonTranslate_of_active res v a source hsourceActive,
        reconstruct_commonTranslate_of_active res v a target'
          (Finset.mem_filter.mp htargetActive).1,
        add_sub_add_right_eq_sub]

private theorem endpointErasedSignedChain_commonTranslate
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (hactive : res.state.active.Nonempty)
    (x y : T4) (v : res.SurvivingCoordinate → T4) (a : T4) :
    res.endpointErasedSignedChain hactive x y
        (res.reconstruct (fun j => v j + a)) =
      res.endpointErasedSignedChain hactive x y
        (res.reconstruct v) := by
  unfold R324WithinHalfResidualPrefix.endpointErasedSignedChain
  apply Finset.prod_congr rfl
  intro edge hedge
  unfold R324WithinHalfResidualPrefix.residualChainEdgeFactor
  rw [res.endpointErased_edgeDisplacement_commonTranslate
    hactive x y v a hedge]

private theorem terminalIncomingAnchor_commonTranslate
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (hactive : res.state.active.Nonempty)
    (v : res.SurvivingCoordinate → T4) (a : T4) :
    res.terminalIncomingAnchor
        (res.reconstruct (fun j => v j + a)) =
      res.terminalIncomingAnchor (res.reconstruct v) + a := by
  have hmem := res.edgeSuccessor_mem_candidates 0
  rw [R324WithinHalfResidualPrefix.edgeSuccessorCandidates] at hmem
  rcases Finset.mem_union.mp hmem with hlast | hinter
  · have hcontra : res.edgeSuccessor 0 = Fin.last (m + 1) := by
      simpa using hlast
    exact (res.edgeSuccessor_zero_ne_last_of_active hactive hcontra).elim
  · obtain ⟨i, hi, hieq⟩ := Finset.mem_image.mp hinter
    have hsuccessor : res.edgeSuccessor 0 = varIdx i := hieq.symm
    unfold R324WithinHalfResidualPrefix.terminalIncomingAnchor
    rw [hsuccessor, assemble_varIdx, assemble_varIdx,
      reconstruct_commonTranslate_of_active res v a i
        (Finset.mem_filter.mp hi).1]

private theorem terminalOutgoingAnchor_commonTranslate
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (hactive : res.state.active.Nonempty)
    (v : res.SurvivingCoordinate → T4) (a : T4) :
    res.terminalOutgoingAnchor hactive
        (res.reconstruct (fun j => v j + a)) =
      res.terminalOutgoingAnchor hactive (res.reconstruct v) + a := by
  let i := res.state.active.max' hactive
  have hi : i ∈ res.state.active := Finset.max'_mem _ _
  have hslot :
      (res.terminalOutgoingEdgeSlot hactive).castSucc = varIdx i := by
    apply Fin.ext
    rfl
  unfold R324WithinHalfResidualPrefix.terminalOutgoingAnchor
  rw [hslot, assemble_varIdx, assemble_varIdx,
    reconstruct_commonTranslate_of_active res v a i hi]

private theorem translatedGreenMode_commonTranslate
    (mode : Z4) (z a : T4) :
    translatedGreenMode mode (z + a) =
      charT4 mode a * translatedGreenMode mode z := by
  rw [translatedGreenMode_eq, translatedGreenMode_eq,
    charT4_add_argument]
  ring

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {alpha beta : Z4}
    {p : R324RefinedScheduleIndex m}
    {e0 : MomentContraction m}
    {providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) e0.1 alpha}

private theorem outgoingEndpointDefectDensity_congr_at
    {pairing : PartialPairing (Fin m)}
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    (data : R324PaperOutgoingEndpointTerminal res)
    (leftCoefficient rightCoefficient :
      (data.terminalPost.SurvivingCoordinate → T4) → ℂ)
    (incomingMode outgoingMode : Z4) (x : T4)
    (v : data.terminalPost.SurvivingCoordinate → T4)
    (first : T4)
    (h : leftCoefficient v = rightCoefficient v) :
    data.outgoingEndpointDefectDensity
        leftCoefficient incomingMode outgoingMode x v first =
      data.outgoingEndpointDefectDensity
        rightCoefficient incomingMode outgoingMode x v first := by
  unfold R324PaperOutgoingEndpointTerminal.outgoingEndpointDefectDensity
    R324PaperOutgoingEndpointTerminal.terminalSplitOuter
  rw [h]

private theorem terminalPredecessorPoint_eq_terminalOutgoingAnchor
    {pairing : PartialPairing (Fin m)}
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    (data : R324PaperOutgoingEndpointTerminal res)
    (hpred :
      r324WithinHalfPredecessorSlot data.endpoint.stop.state
          data.terminalData.terminal ≠ 0)
    (hactive : data.terminalPost.state.active.Nonempty)
    (x : T4)
    (v : data.terminalPost.SurvivingCoordinate → T4) :
    data.terminalPredecessorPoint x v =
      data.terminalPost.terminalOutgoingAnchor hactive
        (data.terminalPost.reconstruct v) := by
  unfold R324PaperOutgoingEndpointTerminal.terminalPredecessorPoint
  rw [← data.endpoint.stop.assemble_afterHead_predecessor_eq_headPredecessorPoint
      data.terminalData.terminal [] data.endpoint.stop_remaining x 0 v,
    data.predecessorSlot_eq_terminalPost_outgoing hpred hactive,
    data.terminalPost.assemble_terminalOutgoing_castSucc_eq_terminalOutgoingAnchor]

private theorem terminalSplitOuter_commonTranslate
    {pairing : PartialPairing (Fin m)}
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    (data : R324PaperOutgoingEndpointTerminal res)
    (hpred :
      r324WithinHalfPredecessorSlot data.endpoint.stop.state
          data.terminalData.terminal ≠ 0)
    (hactive : data.terminalPost.state.active.Nonempty)
    (coefficient :
      (data.terminalPost.SurvivingCoordinate → T4) → ℂ)
    (hcoefficient : ∀ (v : data.terminalPost.SurvivingCoordinate → T4)
        (a : T4), coefficient (fun i => v i + a) = coefficient v)
    (incomingMode : Z4) (x : T4)
    (v : data.terminalPost.SurvivingCoordinate → T4) (a : T4) :
    data.terminalSplitOuter coefficient incomingMode x
        (fun i => v i + a) =
      charT4 incomingMode a *
        data.terminalSplitOuter coefficient incomingMode x v := by
  unfold R324PaperOutgoingEndpointTerminal.terminalSplitOuter
  rw [hcoefficient,
    data.terminalPost.incomingPhaseAnchor_eq_terminalIncomingAnchor
      hactive,
    data.terminalPost.incomingPhaseAnchor_eq_terminalIncomingAnchor
      hactive,
    terminalIncomingAnchor_commonTranslate data.terminalPost hactive v a,
    charT4_add_argument,
    data.incomingErasedHeadOuterFactor_eq_terminalPost_endpointErasedSignedChain
      hpred hactive,
    data.incomingErasedHeadOuterFactor_eq_terminalPost_endpointErasedSignedChain
      hpred hactive,
    endpointErasedSignedChain_commonTranslate
      data.terminalPost hactive x 0 v a]
  ring

private theorem integral_outgoingEndpointDefectDensity_commonTranslate
    {pairing : PartialPairing (Fin m)}
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    (data : R324PaperOutgoingEndpointTerminal res)
    (hpred :
      r324WithinHalfPredecessorSlot data.endpoint.stop.state
          data.terminalData.terminal ≠ 0)
    (hactive : data.terminalPost.state.active.Nonempty)
    (coefficient :
      (data.terminalPost.SurvivingCoordinate → T4) → ℂ)
    (hcoefficient : ∀ (v : data.terminalPost.SurvivingCoordinate → T4)
        (a : T4), coefficient (fun i => v i + a) = coefficient v)
    (incomingMode outgoingMode : Z4) (x : T4)
    (v : data.terminalPost.SurvivingCoordinate → T4) (a : T4) :
    (∫ first : T4,
        data.outgoingEndpointDefectDensity coefficient incomingMode
          outgoingMode x (fun i => v i + a) first ∂paperMeasure) =
      charT4 (incomingMode + outgoingMode) a *
        ∫ first : T4,
          data.outgoingEndpointDefectDensity coefficient incomingMode
            outgoingMode x v first ∂paperMeasure := by
  let shift : T4 ≃ᵐ T4 := MeasurableEquiv.addRight a
  have hp : MeasurePreserving shift paperMeasure paperMeasure := by
    rw [paperMeasure_eq_volume]
    exact measurePreserving_add_right (volume : Measure T4) a
  calc
    (∫ first : T4,
        data.outgoingEndpointDefectDensity coefficient incomingMode
          outgoingMode x (fun i => v i + a) first ∂paperMeasure) =
        ∫ first : T4,
          data.outgoingEndpointDefectDensity coefficient incomingMode
            outgoingMode x (fun i => v i + a) (shift first)
          ∂paperMeasure := by
      symm
      exact hp.integral_comp'
        (fun first : T4 =>
          data.outgoingEndpointDefectDensity coefficient incomingMode
            outgoingMode x (fun i => v i + a) first)
    _ = charT4 (incomingMode + outgoingMode) a *
        ∫ first : T4,
          data.outgoingEndpointDefectDensity coefficient incomingMode
            outgoingMode x v first ∂paperMeasure := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with first
      unfold R324PaperOutgoingEndpointTerminal.outgoingEndpointDefectDensity
      change
        ((data.terminalContext.state.edges _
            (data.terminalPredecessorPoint x (fun i => v i + a) -
              (first + a)) : ℝ) : ℂ) * _ *
              charT4 outgoingMode (first + a) * _ *
              data.terminalSplitOuter coefficient incomingMode x
                (fun i => v i + a) = _
      rw [terminalPredecessorPoint_eq_terminalOutgoingAnchor
          data hpred hactive,
        terminalPredecessorPoint_eq_terminalOutgoingAnchor
          data hpred hactive,
        terminalOutgoingAnchor_commonTranslate
          data.terminalPost hactive v a,
        add_sub_add_right_eq_sub,
        charT4_add_argument,
        terminalSplitOuter_commonTranslate
          data hpred hactive coefficient hcoefficient incomingMode x v a,
        charT4_add]
      ring

/-- Common exact output of the four possible left endpoint routes. -/
structure R324PaperLeftRouteExactPackage
    (p : R324RefinedScheduleIndex m)
    (e0 : MomentContraction m)
    {routeProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) e0.1 alpha}
    (route : R324PaperHalfEndpointRoute routeProviders)
    (beta : Z4) where
  bound : R324PaperHalfEndpointUniformBound route.completedRoute
  transform : bound.ExactTransform
    (r324PaperLeftOuterParameterMeasure rho lam eps e0.2.1)
    (fun s v => r324PaperLeftCanonicalCoefficient
      bound.carrier alpha beta e0.2.2 s v)
    beta
  source_eq_physical :
    transform.source = r324RefinedPhysicalIntegral rho eps m alpha beta p
  target_integrable : Integrable
    (fun q : R324PaperLeftOuterParameter rho lam eps e0.2.1 ×
        (bound.carrier.SurvivingCoordinate → T4) =>
      bound.density
        (fun v => r324PaperLeftCanonicalCoefficient
          bound.carrier alpha beta e0.2.2 q.1 v)
        beta q.2)
    ((r324PaperLeftOuterParameterMeasure rho lam eps e0.2.1).prod
      (Measure.pi fun _ : bound.carrier.SurvivingCoordinate => paperMeasure))
  density_mul : ∀ (a : ℂ)
      (coefficient :
        (bound.carrier.SurvivingCoordinate → T4) → ℂ)
      (outgoingMode : Z4)
      (v : bound.carrier.SurvivingCoordinate → T4),
    bound.density (fun u => a * coefficient u) outgoingMode v =
      a * bound.density coefficient outgoingMode v
  density_congr_at : ∀
      (leftCoefficient rightCoefficient :
        (bound.carrier.SurvivingCoordinate → T4) → ℂ)
      (outgoingMode : Z4)
      (v : bound.carrier.SurvivingCoordinate → T4),
    leftCoefficient v = rightCoefficient v →
      bound.density leftCoefficient outgoingMode v =
        bound.density rightCoefficient outgoingMode v
  unit_commonTranslate : ∀ (a : T4)
      (v : bound.carrier.SurvivingCoordinate → T4),
    bound.density (fun _ => 1) beta (fun i => v i + a) =
      charT4 (alpha + beta) a *
        bound.density (fun _ => 1) beta v

namespace R324PaperLeftRouteExactPackage

/-- Literal four-case constructor.  Every branch is an already closed
producer; this theorem only forgets the branch witness after using it. -/
theorem exists_of_route
    (he0 : e0 ∈ momentRefinedContractionFiber m p.1.1 p.2.1)
    (hsingles : e0.1.singles.Nonempty)
    (route : R324PaperHalfEndpointRoute providers)
    (beta : Z4) :
    Nonempty (R324PaperLeftRouteExactPackage p e0 route beta) := by
  cases route with
  | directDirect hfirst houtgoing data =>
      obtain ⟨transform, hsource⟩ :=
        leftDirectDirect_exactTransform_and_source_eq_physical_closed
          p e0 he0 houtgoing data beta
      let bound :=
        R324PaperHalfEndpointUniformBound.ofDirectDirect houtgoing data
      have htarget :=
        integrable_leftDirectDirect_targetDensity
          (beta := beta) houtgoing data e0.2.2
      exact ⟨{
        bound := bound
        transform := transform
        source_eq_physical := hsource
        target_integrable := htarget
        density_mul := by
          intro a coefficient outgoingMode v
          exact R324PaperHalfEndpointUniformBound.density_mul_ofDirectDirect
            houtgoing data a coefficient outgoingMode v
        density_congr_at := by
          intro leftCoefficient rightCoefficient outgoingMode v h
          dsimp only [bound,
            R324PaperHalfEndpointUniformBound.ofDirectDirect]
          unfold R324PaperHalfDirectDirectRoute.transportEndpointDensity
            R324PaperHalfDirectDirectRoute.directIncomingCoefficient
          rw [h]
        unit_commonTranslate := by
          intro a v
          let hactive : data.transport.final.state.active.Nonempty :=
            data.transport.final.active_nonempty_of_directOutgoing
              providers.hm data.transport.final_processed_eq_schedule houtgoing
          dsimp only [bound,
            R324PaperHalfEndpointUniformBound.ofDirectDirect]
          unfold R324PaperHalfDirectDirectRoute.transportEndpointDensity
            R324PaperHalfDirectDirectRoute.directIncomingCoefficient
          rw [terminalIncomingAnchor_commonTranslate
              data.transport.final hactive v a,
            endpointErasedSignedChain_commonTranslate
              data.transport.final hactive 0 0 v a,
            terminalOutgoingAnchor_commonTranslate
              data.transport.final hactive v a,
            charT4_add_argument,
            translatedGreenMode_commonTranslate,
            charT4_add]
          ring }⟩
  | directExceptional hfirst houtgoing data =>
      obtain ⟨transform, hsource, htarget⟩ :=
        leftDirectExceptional_exactTransform_and_source_eq_physical_closed_with_targetIntegrable
          p e0 he0 data beta
      let bound :=
        R324PaperHalfEndpointUniformBound.ofDirectExceptional data
      exact ⟨{
        bound := bound
        transform := transform
        source_eq_physical := hsource
        target_integrable := htarget
        density_mul := by
          intro a coefficient outgoingMode v
          exact R324PaperHalfEndpointUniformBound.density_mul_ofDirectExceptional
            data a coefficient outgoingMode v
        density_congr_at := by
          intro leftCoefficient rightCoefficient outgoingMode v h
          dsimp only [bound,
            R324PaperHalfEndpointUniformBound.ofDirectExceptional] at leftCoefficient rightCoefficient v h ⊢
          unfold R324PaperHalfDirectExceptionalRoute.endpointDensity
          apply integral_congr_ae
          filter_upwards with first
          apply outgoingEndpointDefectDensity_congr_at
          unfold R324PaperHalfDirectExceptionalRoute.directIncomingEndpointCoefficient
          rw [h]
        unit_commonTranslate := by
          intro a v
          dsimp only [bound,
            R324PaperHalfEndpointUniformBound.ofDirectExceptional]
          unfold R324PaperHalfDirectExceptionalRoute.endpointDensity
          have hpred :
              r324WithinHalfPredecessorSlot
                  data.outgoing.endpoint.stop.state
                    data.outgoing.terminalData.terminal ≠ 0 := by
            rw [data.outgoing_eq]
            exact data.predecessor_ne_zero
          exact integral_outgoingEndpointDefectDensity_commonTranslate
            data.outgoing hpred data.terminalPost_active
            (data.directIncomingEndpointCoefficient (fun _ => 1))
            (by
              intro w b
              unfold R324PaperHalfDirectExceptionalRoute.directIncomingEndpointCoefficient
              rfl)
            alpha beta 0 v a }⟩
  | exceptionalDirect hfirst houtgoing data =>
      obtain ⟨transform, hsource⟩ :=
        leftExceptionalDirect_exactTransform_and_source_eq_physical
          p e0 he0 houtgoing data beta
      let bound :=
        R324PaperHalfEndpointUniformBound.ofExceptionalDirect houtgoing data
      have htarget :=
        integrable_leftExceptionalDirect_targetDensity
          (beta := beta) houtgoing data e0.2.2
      exact ⟨{
        bound := bound
        transform := transform
        source_eq_physical := hsource
        target_integrable := htarget
        density_mul := by
          intro a coefficient outgoingMode v
          exact R324PaperHalfEndpointUniformBound.density_mul_ofExceptionalDirect
            houtgoing data a coefficient outgoingMode v
        density_congr_at := by
          intro leftCoefficient rightCoefficient outgoingMode v h
          dsimp only [bound,
            R324PaperHalfEndpointUniformBound.ofExceptionalDirect]
          unfold R324PaperHalfExceptionalDirectRoute.endpointDensity
            R324PaperHalfExceptionalDirectRoute.incomingEndpointCoefficient
          rw [h]
        unit_commonTranslate := by
          intro a v
          let hactive : data.transport.final.state.active.Nonempty :=
            data.transport.final.active_nonempty_of_directOutgoing
              providers.hm data.transport.final_processed_eq_schedule houtgoing
          dsimp only [bound,
            R324PaperHalfEndpointUniformBound.ofExceptionalDirect]
          unfold R324PaperHalfExceptionalDirectRoute.endpointDensity
            R324PaperHalfExceptionalDirectRoute.incomingEndpointCoefficient
          rw [terminalIncomingAnchor_commonTranslate
              data.transport.final hactive v a,
            endpointErasedSignedChain_commonTranslate
              data.transport.final hactive 0 0 v a,
            terminalOutgoingAnchor_commonTranslate
              data.transport.final hactive v a,
            charT4_add_argument,
            translatedGreenMode_commonTranslate,
            charT4_add]
          ring }⟩
  | exceptionalExceptional hfirst houtgoing data =>
      obtain ⟨transform, hsource, htarget⟩ :=
        leftExceptionalExceptional_exactTransform_and_source_eq_physical_with_targetIntegrable
          p e0 he0 hsingles data beta
      let bound :=
        R324PaperHalfEndpointUniformBound.ofExceptionalExceptional
          hsingles data
      exact ⟨{
        bound := bound
        transform := transform
        source_eq_physical := hsource
        target_integrable := htarget
        density_mul := by
          intro a coefficient outgoingMode v
          exact R324PaperHalfEndpointUniformBound.density_mul_ofExceptionalExceptional
            hsingles data a coefficient outgoingMode v
        density_congr_at := by
          intro leftCoefficient rightCoefficient outgoingMode v h
          dsimp only [bound,
            R324PaperHalfEndpointUniformBound.ofExceptionalExceptional] at leftCoefficient rightCoefficient v h ⊢
          unfold R324PaperHalfExceptionalExceptionalRoute.endpointDensity
          apply integral_congr_ae
          filter_upwards with first
          apply outgoingEndpointDefectDensity_congr_at
          unfold R324PaperHalfExceptionalExceptionalRoute.incomingEndpointCoefficient
          rw [h]
        unit_commonTranslate := by
          intro a v
          let hactive := data.terminalPost_active_of_singles hsingles
          let hpred := data.predecessor_ne_zero_of_singles hsingles
          dsimp only [bound,
            R324PaperHalfEndpointUniformBound.ofExceptionalExceptional]
          unfold R324PaperHalfExceptionalExceptionalRoute.endpointDensity
          exact integral_outgoingEndpointDefectDensity_commonTranslate
            data.outgoing hpred hactive
            (data.incomingEndpointCoefficient (fun _ => 1))
            (by
              intro w b
              unfold R324PaperHalfExceptionalExceptionalRoute.incomingEndpointCoefficient
              rfl)
            alpha beta 0 v a }⟩

end R324PaperLeftRouteExactPackage
end R324WithinHalfResidualPrefix

end

end Anderson4D
