import Anderson4D.DetParametrix.Paper42_Moment.R324PaperIncomingEndpointReuse
import Anderson4D.DetParametrix.Paper42_Moment.R324OutgoingExceptionalTerminalBound

/-!
# Paper Step 4(A): reuse of the retained outgoing endpoint

After the paired incoming endpoint has been collapsed, the endpoint-stop
driver may start at an arbitrary reachable residual prefix.  The retained
outgoing shortcut is nevertheless the same last schedule block used in the
paper.  This file records only the thin geometric adapter needed to feed that
block to the already proved outgoing Fourier-defect identity.

In particular, the primitive-block and endpoint integrations below are exact
signed complex identities.  No norm, majorant, route, or scalar ledger is
introduced here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}

/-- A shortcut-terminal schedule whose endpoint-stop transport starts at an
arbitrary reachable residual prefix.  The dependent field makes the equality
between the stop terminal and the canonical outgoing terminal literal, so no
cast survives in the analytic statement. -/
structure R324PaperOutgoingEndpointTerminal
    (res : R324WithinHalfResidualPrefix rho lam eps pairing) where
  terminalData : R324ShortcutTerminalSchedule pairing
  endpoint :
    R324WithinHalfEndpointStopAtTerminal terminalData.terminal res

namespace R324PaperOutgoingEndpointTerminal

variable {res : R324WithinHalfResidualPrefix rho lam eps pairing}

/-- Package an endpoint indexed by an equal presentation of the canonical
outgoing terminal. -/
def of_eq
    {terminal : R322ExtractionStep m}
    (endpoint : R324WithinHalfEndpointStopAtTerminal terminal res)
    (terminalData : R324ShortcutTerminalSchedule pairing)
    (hterminal : terminal = terminalData.terminal) :
    R324PaperOutgoingEndpointTerminal res := by
  subst terminal
  exact { terminalData := terminalData, endpoint := endpoint }

/-- The retained outgoing terminal as the generic one-block context consumed
by the paper's exact Step 4(A) Fourier calculation. -/
def terminalContext
    (data : R324PaperOutgoingEndpointTerminal res) :
    R324WithinHalfStepContext pairing :=
  data.endpoint.stop.headContext
    data.terminalData.terminal [] data.endpoint.stop_remaining

/-- Reachability keeps the named edge leaving the unabsorbed terminal equal
to the free Green kernel. -/
theorem terminalContext_outgoing_eq_greenFn
    (data : R324PaperOutgoingEndpointTerminal res) :
    data.terminalContext.state.edges
        data.terminalContext.outgoingSlot =
      greenFn := by
  change
    data.endpoint.stop.state.edges
        (r324InternalVertexEdgeSlot data.terminalData.terminal.1.2) =
      greenFn
  exact
    data.endpoint.stop.state_edges_head_outgoing_eq_greenFn
      data.terminalData.terminal [] data.endpoint.stop_remaining

/-- The singleton retained suffix has exactly the perturbative order of the
outgoing terminal block. -/
theorem stop_remainingOrder_eq_terminal
    (data : R324PaperOutgoingEndpointTerminal res) :
    data.endpoint.stop.remainingOrder =
      residualBlockOrder data.terminalData.terminal.2 := by
  unfold R324WithinHalfResidualPrefix.remainingOrder
  rw [data.endpoint.stop_remaining]
  simp

/-- The endpoint stop has consumed precisely the proper prefix of the
canonical outgoing-shortcut schedule. -/
theorem stop_processed_eq_proper
    (data : R324PaperOutgoingEndpointTerminal res) :
    data.endpoint.stop.state.processed =
      data.terminalData.proper := by
  exact
    List.append_cancel_right
      (data.endpoint.stop_processed_append_terminal_eq_schedule.trans
        data.terminalData.schedule_eq)

/-- The retained terminal is the active part of its ambient interval.  This
is the schedule fact used in the paper before the final endpoint operation. -/
theorem terminal_block_eq_stop_active_inter_Icc
    (data : R324PaperOutgoingEndpointTerminal res) :
    data.terminalData.terminal.2 =
      data.endpoint.stop.state.active ∩
        Finset.Icc data.terminalData.terminal.1.1
          data.terminalData.terminal.1.2 := by
  have hblock :=
    r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
      pairing data.terminalData.proper []
      data.terminalData.terminal
      (by simpa using data.terminalData.schedule_eq)
  unfold R324WithinHalfEdgeState.active
  rw [data.stop_processed_eq_proper]
  exact hblock

/-- The canonical retained terminal ends at the last internal vertex. -/
theorem terminal_right_eq_last
    (data : R324PaperOutgoingEndpointTerminal res) :
    data.terminalData.terminal.1.2.val = m - 1 :=
  data.terminalData.terminal_right

/-- Hence its named outgoing edge is the final internal chain-edge slot. -/
theorem terminalContext_outgoingSlot_eq_last
    (data : R324PaperOutgoingEndpointTerminal res) :
    data.terminalContext.outgoingSlot = Fin.last m := by
  apply Fin.ext
  change data.terminalData.terminal.1.2.val + 1 = m
  have hright := data.terminal_right_eq_last
  have hlt := data.terminalData.terminal.1.2.isLt
  omega

/-- The sparse successor of the retained outgoing edge is the external right
endpoint. -/
theorem terminal_edgeSuccessor_outgoing_eq_last
    (data : R324PaperOutgoingEndpointTerminal res) :
    data.endpoint.stop.edgeSuccessor data.terminalContext.outgoingSlot =
      Fin.last (m + 1) := by
  let outgoing := data.terminalContext.outgoingSlot
  have hout : outgoing = Fin.last m :=
    data.terminalContext_outgoingSlot_eq_last
  have hlt :=
    data.endpoint.stop.edge_lt_edgeSuccessor
      outgoing
  have hltVal :
      outgoing.val <
        (data.endpoint.stop.edgeSuccessor outgoing).val := by
    exact hlt
  have houtVal : outgoing.val = m := by
    exact congrArg Fin.val hout
  have hbound :=
    (data.endpoint.stop.edgeSuccessor
      outgoing).isLt
  apply Fin.ext
  change
    (data.endpoint.stop.edgeSuccessor
      outgoing).val = m + 1
  omega

/-- In the terminal split, the local successor point is literally the
external outgoing variable. -/
theorem terminal_headSuccessorPoint_eq_right
    (data : R324PaperOutgoingEndpointTerminal res)
    (x y : T4)
    (v :
      (data.endpoint.stop.afterHead data.terminalData.terminal []
        data.endpoint.stop_remaining).SurvivingCoordinate → T4) :
    data.endpoint.stop.headSuccessorPoint
        data.terminalData.terminal [] data.endpoint.stop_remaining x y v =
      y := by
  unfold R324WithinHalfResidualPrefix.headSuccessorPoint
  change
    assemble x y
        (data.endpoint.stop.headOuterBase
          data.terminalData.terminal [] data.endpoint.stop_remaining v)
        (data.endpoint.stop.edgeSuccessor
          data.terminalContext.outgoingSlot) =
      y
  rw [data.terminal_edgeSuccessor_outgoing_eq_last]
  exact assemble_last x y _

/-- The terminal predecessor is an internal or incoming slot, never the
external-right slot; consequently it is independent of the outgoing
variable. -/
theorem terminal_headPredecessorPoint_right_independent
    (data : R324PaperOutgoingEndpointTerminal res)
    (x y : T4)
    (v :
      (data.endpoint.stop.afterHead data.terminalData.terminal []
        data.endpoint.stop_remaining).SurvivingCoordinate → T4) :
    data.endpoint.stop.headPredecessorPoint
        data.terminalData.terminal [] data.endpoint.stop_remaining x y v =
      data.endpoint.stop.headPredecessorPoint
        data.terminalData.terminal [] data.endpoint.stop_remaining x 0 v := by
  let predecessor :=
    r324WithinHalfPredecessorSlot data.endpoint.stop.state
      data.terminalData.terminal
  by_cases hp : predecessor = 0
  · unfold R324WithinHalfResidualPrefix.headPredecessorPoint
    change
      assemble x y _ predecessor.castSucc =
        assemble x 0 _ predecessor.castSucc
    rw [hp]
    simp
  · have hpval : predecessor.castSucc.val ≠ 0 := by
      change predecessor.val ≠ 0
      intro hval
      apply hp
      apply Fin.ext
      exact hval
    have hlast : predecessor.castSucc.val ≠ m + 1 := by
      change predecessor.val ≠ m + 1
      have hlt := predecessor.isLt
      omega
    unfold R324WithinHalfResidualPrefix.headPredecessorPoint assemble
    change
      (if _h0 : predecessor.castSucc.val = 0 then x
        else if _hm : predecessor.castSucc.val = m + 1 then y
        else _) =
      (if _h0 : predecessor.castSucc.val = 0 then x
        else if _hm : predecessor.castSucc.val = m + 1 then 0
        else _)
    rw [dif_neg hpval, dif_neg hlast, dif_neg hpval, dif_neg hlast]

/-- The post-coordinate predecessor point used as the fixed left input of
the outgoing terminal section. -/
def terminalPredecessorPoint
    (data : R324PaperOutgoingEndpointTerminal res)
    (x : T4)
    (v :
      (data.endpoint.stop.afterHead data.terminalData.terminal []
        data.endpoint.stop_remaining).SurvivingCoordinate → T4) : T4 :=
  data.endpoint.stop.headPredecessorPoint
    data.terminalData.terminal [] data.endpoint.stop_remaining x 0 v

/-- The literal ordinary branch produced by the singleton terminal split is
exactly the translated raw local section consumed by the existing outgoing
Fourier-defect theorem. -/
theorem headLocalFactor_reconstruct_split_eq_terminalRawLocal
    (data : R324PaperOutgoingEndpointTerminal res)
    (x y : T4)
    (t :
      Fin (2 * residualBlockOrder data.terminalData.terminal.2) → T4)
    (v :
      (data.endpoint.stop.afterHead data.terminalData.terminal []
        data.endpoint.stop_remaining).SurvivingCoordinate → T4) :
    data.endpoint.stop.headLocalFactor
        data.terminalData.terminal [] data.endpoint.stop_remaining
        rho eps x y
        (data.endpoint.stop.reconstruct
          ((data.endpoint.stop.splitSurvivingPiMeasurableEquiv
            data.terminalData.terminal [] data.endpoint.stop_remaining).symm
            (t, v))) =
      data.terminalContext.rawLocalIntegrand rho eps
        (data.terminalPredecessorPoint x v - y)
        (fun j => t j - y) := by
  rw [data.endpoint.stop.headLocalFactor_reconstruct_split]
  rw [data.terminal_headSuccessorPoint_eq_right]
  rw [data.terminal_headPredecessorPoint_right_independent]
  rfl

/-- Ordinary branch of the singleton terminal split, already rewritten in
the exact raw-local carrier required by the outgoing Fourier calculation.
This is the arbitrary-prefix analogue of the ordinary theorem in
`R324PaperEndpointTerminalSplit`; no analytic operation is repeated. -/
theorem incomingPhasedResidualDensity_terminal_split_of_ne_zero
    (data : R324PaperOutgoingEndpointTerminal res)
    (hpred :
      r324WithinHalfPredecessorSlot data.endpoint.stop.state
          data.terminalData.terminal ≠ 0)
    (coefficient : ℂ) (k : Z4) (x y : T4)
    (t :
      Fin (2 * residualBlockOrder data.terminalData.terminal.2) → T4)
    (v :
      (data.endpoint.stop.afterHead data.terminalData.terminal []
        data.endpoint.stop_remaining).SurvivingCoordinate → T4) :
    data.endpoint.stop.incomingPhasedResidualDensity
        coefficient k rho eps x y
        ((data.endpoint.stop.splitSurvivingPiMeasurableEquiv
          data.terminalData.terminal [] data.endpoint.stop_remaining).symm
          (t, v)) =
      coefficient *
        charT4 k
          ((data.endpoint.stop.afterHead data.terminalData.terminal []
            data.endpoint.stop_remaining).incomingPhaseAnchor x y v) *
        (data.terminalContext.rawLocalIntegrand rho eps
          (data.terminalPredecessorPoint x v - y)
          (fun j => t j - y) : ℂ) *
        (data.endpoint.stop.incomingErasedHeadOuterFactor
          data.terminalData.terminal [] data.endpoint.stop_remaining
          rho eps x y v : ℂ) := by
  rw [data.endpoint.stop
    |>.incomingPhasedResidualDensity_reconstruct_split_of_ne_zero
      data.terminalData.terminal [] data.endpoint.stop_remaining hpred
      coefficient k rho eps x y t v]
  rw [data.headLocalFactor_reconstruct_split_eq_terminalRawLocal]

/-- Exact signed outgoing-endpoint operation for a terminal retained after
an arbitrary endpoint-stop transport.  This is the paper's ordinary-`J`
defect identity; every endpoint and primitive coordinate is integrated
before the defect is exposed. -/
theorem integral_lamEps_pow_terminalOutgoingFourier_gap_eq_defect
    (data : R324PaperOutgoingEndpointTerminal res)
    (k : Z4) (x first : T4) (outer : ℂ)
    (hint :
      ∀ (gap : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder
                data.terminalData.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminalData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder
              data.terminalData.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder data.terminalData.terminal.2)
              κB.1 data.terminalContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder
                first (first - gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    (∫ gap : T4,
        (lamEps lam eps : ℂ) ^
            (2 * residualBlockOrder data.terminalData.terminal.2) *
          (∫ r : Fin (2 * residualBlockOrder
                data.terminalData.terminal.2 - 2) → T4,
            ∫ y : T4,
              charT4 k y *
                ((data.terminalContext.rawLocalIntegrand
                  rho eps (x - y)
                  (fun j =>
                    primitiveAssemble
                      (residualBlockOrder data.terminalData.terminal.2)
                      data.terminalContext.one_le_blockOrder
                      first (first - gap) r j - y) : ℂ) * outer)
              ∂paperMeasure
            ∂Measure.pi fun _ => paperMeasure)
        ∂paperMeasure) =
      ((data.terminalContext.state.edges
            (r324WithinHalfPredecessorSlot
              data.terminalContext.state data.terminalContext.step)
            (x - first) : Real) : ℂ) *
        (paperSecondOrderModeDecay k : ℂ) * charT4 k first *
        (∫ gap : T4,
          (primitiveKernelDiff rho lam eps
              (residualBlockOrder data.terminalData.terminal.2)
              data.terminalContext.one_le_blockOrder
              data.terminalContext.internalEdges gap : ℂ) *
            (charT4 (-k) gap - 1)
          ∂paperMeasure) * outer := by
  exact
    data.terminalContext
      |>.integral_lamEps_pow_terminalOutgoingFourier_gap_eq_defect
        rho lam eps data.terminalContext_outgoing_eq_greenFn
        k x first outer hint

/-- The local factor appearing literally in the ordinary singleton split is
fed, without a norm or domination, into the already proved outgoing
Fourier-defect identity.  The displayed `(gap, first, internal)` carrier is
the paper's Step 4(A) order after the standard primitive-tuple reindexing. -/
theorem integral_lamEps_pow_splitHeadLocal_terminalOutgoingFourier_gap_eq_defect
    (data : R324PaperOutgoingEndpointTerminal res)
    (k : Z4) (x first : T4)
    (v :
      (data.endpoint.stop.afterHead data.terminalData.terminal []
        data.endpoint.stop_remaining).SurvivingCoordinate → T4)
    (outer : ℂ)
    (hint :
      ∀ (gap : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder
                data.terminalData.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminalData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder
              data.terminalData.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder data.terminalData.terminal.2)
              κB.1 data.terminalContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder
                first (first - gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    (∫ gap : T4,
        (lamEps lam eps : ℂ) ^
            (2 * residualBlockOrder data.terminalData.terminal.2) *
          (∫ r : Fin (2 * residualBlockOrder
                data.terminalData.terminal.2 - 2) → T4,
            ∫ y : T4,
              charT4 k y *
                ((data.endpoint.stop.headLocalFactor
                  data.terminalData.terminal [] data.endpoint.stop_remaining
                  rho eps x y
                  (data.endpoint.stop.reconstruct
                    ((data.endpoint.stop.splitSurvivingPiMeasurableEquiv
                      data.terminalData.terminal []
                      data.endpoint.stop_remaining).symm
                      (primitiveAssemble
                        (residualBlockOrder
                          data.terminalData.terminal.2)
                        data.terminalContext.one_le_blockOrder
                        first (first - gap) r, v))) : ℂ) * outer)
              ∂paperMeasure
            ∂Measure.pi fun _ => paperMeasure)
        ∂paperMeasure) =
      ((data.terminalContext.state.edges
            (r324WithinHalfPredecessorSlot
              data.terminalContext.state data.terminalContext.step)
            (data.terminalPredecessorPoint x v - first) : Real) : ℂ) *
        (paperSecondOrderModeDecay k : ℂ) * charT4 k first *
        (∫ gap : T4,
          (primitiveKernelDiff rho lam eps
              (residualBlockOrder data.terminalData.terminal.2)
              data.terminalContext.one_le_blockOrder
              data.terminalContext.internalEdges gap : ℂ) *
            (charT4 (-k) gap - 1)
          ∂paperMeasure) * outer := by
  calc
    _ =
        ∫ gap : T4,
          (lamEps lam eps : ℂ) ^
              (2 * residualBlockOrder data.terminalData.terminal.2) *
            (∫ r : Fin (2 * residualBlockOrder
                  data.terminalData.terminal.2 - 2) → T4,
              ∫ y : T4,
                charT4 k y *
                  ((data.terminalContext.rawLocalIntegrand rho eps
                    (data.terminalPredecessorPoint x v - y)
                    (fun j =>
                      primitiveAssemble
                        (residualBlockOrder
                          data.terminalData.terminal.2)
                        data.terminalContext.one_le_blockOrder
                        first (first - gap) r j - y) : ℂ) * outer)
                ∂paperMeasure
              ∂Measure.pi fun _ => paperMeasure)
          ∂paperMeasure := by
            apply integral_congr_ae
            filter_upwards with gap
            apply congrArg
            apply integral_congr_ae
            filter_upwards with r
            apply integral_congr_ae
            filter_upwards with y
            rw [data.headLocalFactor_reconstruct_split_eq_terminalRawLocal]
    _ = _ :=
      data.integral_lamEps_pow_terminalOutgoingFourier_gap_eq_defect
        k (data.terminalPredecessorPoint x v) first outer hint

end R324PaperOutgoingEndpointTerminal

end R324WithinHalfResidualPrefix

end

end Anderson4D
