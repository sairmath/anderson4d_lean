import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingStopTraceAssembly

/-!
# Exact final-head geometry for a full R-324 pairing

After all proper within-half blocks have been collapsed, a full pairing
retains one terminal block.  This module identifies the complete sparse
geometry of that last head before any endpoint estimate is applied.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

namespace R324WithinHalfResidualPrefix

namespace R324FullPairingStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    {initialScale : Fin (2 * q + 1) → ℝ}

/-- The retained terminal block is exactly the active carrier at the
singleton stop. -/
theorem terminal_block_eq_active
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    data.terminalData.terminal.2 =
      data.trace.stopPrefix.state.active :=
  data.terminal_block_eq_stop_active

/-- At the singleton stop, the terminal head has no surviving internal
vertex strictly to its left.  Its sparse predecessor is therefore the
incoming external slot. -/
theorem terminal_predecessorSlot_eq_zero
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    r324WithinHalfPredecessorSlot
        data.trace.stopPrefix.state
        data.terminalData.terminal =
      0 := by
  let stop := data.trace.stopPrefix
  let terminal := data.terminalData.terminal
  have hremaining :
      stop.remaining = [terminal] :=
    data.stop_remaining_eq_singleton
  have hpred :=
    r324WithinHalfPredecessorSlot_mem
      stop.state terminal
  rw [r324WithinHalfPredecessorCandidates] at hpred
  rcases Finset.mem_union.mp hpred with hzero | hinter
  · simpa only [Finset.mem_singleton] using hzero
  · obtain ⟨i, hi, heq⟩ :=
      Finset.mem_image.mp hinter
    have hiActive := (Finset.mem_filter.mp hi).1
    have hiLt := (Finset.mem_filter.mp hi).2
    have hiBlock : i ∈ terminal.2 := by
      rw [data.terminal_block_eq_stop_active]
      exact hiActive
    have haligned :=
      r322AnalyticSchedule_forall_aligned
        κ terminal
        (stop.headContext terminal [] hremaining).step_mem_schedule
    exact
      ((not_lt_of_ge
        ((haligned.2.2 i hiBlock).1)) hiLt).elim

/-- The terminal head leaves through the last edge slot of the internal
chain. -/
theorem terminal_outgoingSlot_eq_last
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    (data.trace.stopPrefix.headContext
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).outgoingSlot =
      Fin.last (2 * q) := by
  apply Fin.ext
  change
    data.terminalData.terminal.1.2.val + 1 =
      2 * q
  have hright := data.terminal_right_eq_last
  have hlt :=
    data.terminalData.terminal.1.2.isLt
  omega

/-- The sparse successor after the terminal outgoing slot is the external
right endpoint. -/
theorem terminal_edgeSuccessor_outgoing_eq_last
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    data.trace.stopPrefix.edgeSuccessor
        (data.trace.stopPrefix.headContext
          data.terminalData.terminal []
          data.stop_remaining_eq_singleton).outgoingSlot =
      Fin.last (2 * q + 1) := by
  let stop := data.trace.stopPrefix
  let outgoing :=
    (stop.headContext
      data.terminalData.terminal []
      data.stop_remaining_eq_singleton).outgoingSlot
  have hout : outgoing = Fin.last (2 * q) :=
    data.terminal_outgoingSlot_eq_last
  have hlt := stop.edge_lt_edgeSuccessor outgoing
  have hltVal :
      outgoing.val <
        (stop.edgeSuccessor outgoing).val := by
    exact hlt
  have houtVal : outgoing.val = 2 * q := by
    have := congrArg Fin.val hout
    exact this
  have hbound := (stop.edgeSuccessor outgoing).isLt
  apply Fin.ext
  change (stop.edgeSuccessor outgoing).val = 2 * q + 1
  omega

/-- The predecessor point of the final local block is the external left
endpoint. -/
theorem terminal_headPredecessorPoint_eq_left
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (x y : T4)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).SurvivingCoordinate → T4) :
    data.trace.stopPrefix.headPredecessorPoint
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton x y v =
      x := by
  unfold headPredecessorPoint
  rw [data.terminal_predecessorSlot_eq_zero]
  exact assemble_zero x y _

/-- The successor point of the final local block is the external right
endpoint. -/
theorem terminal_headSuccessorPoint_eq_right
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (x y : T4)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).SurvivingCoordinate → T4) :
    data.trace.stopPrefix.headSuccessorPoint
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton x y v =
      y := by
  unfold headSuccessorPoint
  rw [data.terminal_edgeSuccessor_outgoing_eq_last]
  exact assemble_last x y _

/-- The named edge leaving the retained terminal head is still the free
Green kernel. -/
theorem terminal_outgoingEdge_eq_greenFn
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    data.trace.stopPrefix.state.edges
        (data.trace.stopPrefix.headContext
          data.terminalData.terminal []
          data.stop_remaining_eq_singleton).outgoingSlot =
      greenFn := by
  change
    data.trace.stopPrefix.state.edges
        (r324InternalVertexEdgeSlot
          data.terminalData.terminal.1.2) =
      greenFn
  exact
    data.trace.stopPrefix.state_edges_head_outgoing_eq_greenFn
      data.terminalData.terminal []
      data.stop_remaining_eq_singleton

/-- Once the retained terminal block is removed, no internal vertex
survives. -/
theorem terminal_afterHead_active_eq_empty
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    (data.trace.stopPrefix.afterHead
      data.terminalData.terminal []
      data.stop_remaining_eq_singleton).state.active =
      ∅ := by
  rw [
    data.trace.stopPrefix.afterHead_active
      data.terminalData.terminal []
      data.stop_remaining_eq_singleton,
    ← data.terminal_block_eq_stop_active,
    Finset.sdiff_self]

/-- After deleting the final block, the only active sparse edge slot is
the incoming external slot. -/
theorem terminal_afterHead_activeEdgeSlots_eq_singleton
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    (data.trace.stopPrefix.afterHead
      data.terminalData.terminal []
      data.stop_remaining_eq_singleton).activeEdgeSlots =
      {0} := by
  unfold activeEdgeSlots
  rw [data.terminal_afterHead_active_eq_empty]
  simp

/-- No ordinary outer sparse-chain factor remains outside the final local
head. -/
theorem terminal_headOuterChainProductAfter_eq_one
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (x y : T4)
    (v : Fin (2 * q) → T4) :
    data.trace.stopPrefix.headOuterChainProductAfter
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton x y v =
      1 := by
  unfold headOuterChainProductAfter
  apply Finset.prod_eq_one
  intro edge hedge
  have hedgeOutside :=
    (Finset.mem_sdiff.mp hedge).2
  have hzeroHead :
      (0 : Fin (2 * q + 1)) ∈
        data.trace.stopPrefix.headChainSlots
          data.terminalData.terminal []
          data.stop_remaining_eq_singleton := by
    unfold headChainSlots
    rw [data.terminal_predecessorSlot_eq_zero]
    simp
  have hedgeNeZero : edge ≠ 0 := by
    intro heq
    exact hedgeOutside (heq ▸ hzeroHead)
  unfold residualChainEdgeFactor
  rw [if_neg]
  rw [data.terminal_afterHead_activeEdgeSlots_eq_singleton]
  simpa only [Finset.mem_singleton] using hedgeNeZero

/-- At the terminal singleton stop, every factor outside the genuine final
local block is exactly one. -/
theorem terminal_headOuterFactor_eq_one
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (x y : T4)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).SurvivingCoordinate → T4) :
    data.trace.stopPrefix.headOuterFactor
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton ρ ε x y v =
      1 := by
  let post :=
    data.trace.stopPrefix.afterHead
      data.terminalData.terminal []
      data.stop_remaining_eq_singleton
  have hremaining : post.remaining = [] :=
    data.trace.stopPrefix.afterHead_remaining
      data.terminalData.terminal []
      data.stop_remaining_eq_singleton
  have hdifference :
      post.residualDifferenceProduct x y
          (post.reconstruct v) =
        1 := by
    unfold residualDifferenceProduct
    rw [hremaining]
    rfl
  have hprimitive :
      post.residualPrimitiveProduct ρ ε
          (post.reconstruct v) =
        1 := by
    unfold residualPrimitiveProduct
    simpa only [hremaining, Finset.prod_const_one]
  unfold headOuterFactor
  rw [data.terminal_headOuterChainProductAfter_eq_one]
  rw [hdifference, hprimitive]
  norm_num

/-- Exact final-head reduction: after all proper blocks have been consumed,
the whole singleton-stop residual integrand is the translated raw local
integrand joining the two external endpoints.  No absolute value or endpoint
estimate has been taken. -/
theorem terminal_residualIntegrand_reconstruct_split_eq_rawLocal
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (x y : T4)
    (t :
      Fin
          (2 * residualBlockOrder
            data.terminalData.terminal.2) →
        T4)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).SurvivingCoordinate → T4) :
    data.trace.stopPrefix.residualIntegrand ρ ε x y
        (data.trace.stopPrefix.reconstruct
          ((data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
            data.terminalData.terminal []
            data.stop_remaining_eq_singleton).symm (t, v))) =
      (data.trace.stopPrefix.headContext
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).rawLocalIntegrand
          ρ ε (x - y) (fun j => t j - y) := by
  rw [
    data.trace.stopPrefix.residualIntegrand_reconstruct_split
      data.terminalData.terminal []
      data.stop_remaining_eq_singleton,
    data.trace.stopPrefix.headLocalFactor_reconstruct_split
      data.terminalData.terminal []
      data.stop_remaining_eq_singleton,
    data.terminal_headOuterFactor_eq_one,
    data.terminal_headPredecessorPoint_eq_left,
    data.terminal_headSuccessorPoint_eq_right]
  ring

end R324FullPairingStopTraceAssembly

end R324WithinHalfResidualPrefix

end

end Anderson4D
