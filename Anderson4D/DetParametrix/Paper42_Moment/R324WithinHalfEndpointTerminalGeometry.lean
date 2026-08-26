import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfEndpointStopAtTerminal
import Anderson4D.DetParametrix.Paper42_Moment.R324ShortcutTerminalSchedule

/-!
# Geometry at the endpoint-stop terminal

This module identifies the stopped prefix produced by
`R324WithinHalfEndpointStopAtTerminal` with the canonical proper prefix of
an outgoing-shortcut terminal schedule.  It is the trace-free analogue of
`R324ShortcutStopTraceAssembly`: the terminal block remains visible, its
carrier and right endpoint are identified, and its outgoing edge is still
the free Green kernel.

Only schedule and edge-state geometry is recorded here.  No Fourier
integration, ordinary-J estimate, or numerical bound is used.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

namespace R324WithinHalfResidualPrefix

/-- A canonical outgoing-shortcut terminal schedule together with the
signed/phased endpoint-stop transport from the initial within-half state. -/
structure R324WithinHalfEndpointTerminalGeometry
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} (κ : PartialPairing (Fin m)) where
  terminalData : R324ShortcutTerminalSchedule κ
  transport :
    R324WithinHalfEndpointStopAtTerminal terminalData.terminal
      (R324WithinHalfResidualPrefix.initial ρ lam ε κ)

namespace R324WithinHalfEndpointTerminalGeometry

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κ : PartialPairing (Fin m)}

/-- Construct the canonical terminal geometry directly from the same local
block provider and initial edge certificate used by the complete within-half
driver.  The only change is that the final shortcut block is retained for
the endpoint Fourier operation required in paper Step 4. -/
theorem exists_of_localBlockProvider
    {C K : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider ρ C lam ε K κ)
    (scale : Fin (m + 1) → ℝ)
    (certificate :
      R324WithinHalfEdgeCertificate
        (R324WithinHalfResidualPrefix.initial ρ lam ε κ).state scale)
    (terminalData : R324ShortcutTerminalSchedule κ) :
    Nonempty
      (R324WithinHalfEndpointTerminalGeometry
        (ρ := ρ) (lam := lam) (ε := ε) κ) := by
  obtain ⟨transport⟩ :=
    R324WithinHalfEndpointStopAtTerminal.exists_r324WithinHalfEndpointStopAtTerminal
      hε hε1 provider
      (R324WithinHalfResidualPrefix.initial ρ lam ε κ)
      scale certificate terminalData.terminal terminalData.proper
      (by
        simpa only [R324WithinHalfResidualPrefix.initial] using
          terminalData.schedule_eq)
  exact ⟨{ terminalData := terminalData, transport := transport }⟩

/-- The endpoint-stop driver has consumed exactly the canonical proper
prefix before the shortcut terminal. -/
theorem stop_processed_eq_proper
    (data :
      R324WithinHalfEndpointTerminalGeometry
        (ρ := ρ) (lam := lam) (ε := ε) κ) :
    data.transport.stop.state.processed =
      data.terminalData.proper := by
  exact
    List.append_cancel_right
      (data.transport.stop_processed_append_terminal_eq_schedule.trans
        data.terminalData.schedule_eq)

/-- The stopped residual retains exactly the canonical shortcut terminal. -/
theorem stop_remaining_eq_singleton
    (data :
      R324WithinHalfEndpointTerminalGeometry
        (ρ := ρ) (lam := lam) (ε := ε) κ) :
    data.transport.stop.remaining =
      [data.terminalData.terminal] :=
  data.transport.stop_remaining

/-- At the stop, the terminal block is its ambient endpoint interval
intersected with the still-active carrier. -/
theorem terminal_block_eq_stop_active_inter_Icc
    (data :
      R324WithinHalfEndpointTerminalGeometry
        (ρ := ρ) (lam := lam) (ε := ε) κ) :
    data.terminalData.terminal.2 =
      data.transport.stop.state.active ∩
        Finset.Icc data.terminalData.terminal.1.1
          data.terminalData.terminal.1.2 := by
  have hblock :=
    r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
      κ data.terminalData.proper []
      data.terminalData.terminal
      (by simpa using data.terminalData.schedule_eq)
  unfold R324WithinHalfEdgeState.active
  rw [data.stop_processed_eq_proper]
  exact hblock

/-- The retained terminal ends at the final internal vertex. -/
theorem terminal_right_eq_last
    (data :
      R324WithinHalfEndpointTerminalGeometry
        (ρ := ρ) (lam := lam) (ε := ε) κ) :
    data.terminalData.terminal.1.2.val = m - 1 :=
  data.terminalData.terminal_right

/-- The retained terminal as a generic within-half step context. -/
def terminalContext
    (data :
      R324WithinHalfEndpointTerminalGeometry
        (ρ := ρ) (lam := lam) (ε := ε) κ) :
    R324WithinHalfStepContext κ :=
  data.transport.stop.headContext
    data.terminalData.terminal []
    data.stop_remaining_eq_singleton

/-- Reachability keeps the outgoing named edge of the unabsorbed terminal
equal to the free Green kernel. -/
theorem terminalContext_outgoing_eq_greenFn
    (data :
      R324WithinHalfEndpointTerminalGeometry
        (ρ := ρ) (lam := lam) (ε := ε) κ) :
    data.terminalContext.state.edges
        data.terminalContext.outgoingSlot =
      greenFn := by
  change
    data.transport.stop.state.edges
        (r324InternalVertexEdgeSlot
          data.terminalData.terminal.1.2) =
      greenFn
  exact
    data.transport.stop.state_edges_head_outgoing_eq_greenFn
      data.terminalData.terminal []
      data.stop_remaining_eq_singleton

/-- Exact processed/remaining perturbative-order ledger at the endpoint
stop. -/
theorem order_ledger
    (data :
      R324WithinHalfEndpointTerminalGeometry
        (ρ := ρ) (lam := lam) (ε := ε) κ) :
    (data.transport.stop.state.processed.map
        (fun step => residualBlockOrder step.2)).sum +
        data.transport.stop.remainingOrder =
      ((r322AnalyticSchedule κ).map
        (fun step => residualBlockOrder step.2)).sum := by
  simpa only [R324WithinHalfResidualPrefix.processedOrder] using
    data.transport.stop.processedOrder_add_remainingOrder

/-- Because the stopped remaining list is a singleton, its retained order
is exactly the order of the named terminal block. -/
theorem stop_remainingOrder_eq_terminal
    (data :
      R324WithinHalfEndpointTerminalGeometry
        (ρ := ρ) (lam := lam) (ε := ε) κ) :
    data.transport.stop.remainingOrder =
      residualBlockOrder data.terminalData.terminal.2 := by
  unfold R324WithinHalfResidualPrefix.remainingOrder
  rw [data.stop_remaining_eq_singleton]
  simp

end R324WithinHalfEndpointTerminalGeometry

end R324WithinHalfResidualPrefix

end

end Anderson4D
