import Anderson4D.DetParametrix.Paper42_Moment.R324ShortcutTerminalSchedule
import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfStopBeforeLastTrace

/-!
# Certified stop traces for the outgoing-shortcut branch

If the final chain edge is extracted, the analytic schedule has a canonical
last step even when the pairing has residual singles.  This module combines
that terminal schedule with the generic certified prefix iterator.  It
consumes exactly the proper prefix and leaves the terminal block visible.

Unlike the full-pairing assembly, the terminal block is only the part of the
stop active carrier lying in its endpoint interval.  No exhaustion of the
active carrier, trivial outer factor, or fullness property is asserted.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

namespace R324WithinHalfResidualPrefix

/-- A shortcut terminal schedule together with a certified trace through
exactly its proper prefix. -/
structure R324ShortcutStopTraceAssembly
    {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} (κ : PartialPairing (Fin m))
    (initialScale : Fin (m + 1) → ℝ) where
  terminalData : R324ShortcutTerminalSchedule κ
  trace :
    R324WithinHalfStopBeforeLastTrace
      terminalData.terminal
      (R324WithinHalfResidualPrefix.initial ρ lam ε κ)
      initialScale

namespace R324ShortcutStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- The trace consumes exactly the proper part of the canonical terminal
schedule. -/
theorem stop_processed_eq_proper
    (data :
      R324ShortcutStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    data.trace.stopPrefix.state.processed =
      data.terminalData.proper := by
  exact
    List.append_cancel_right
      (data.trace.stopPrefix_processed_append_terminal_eq_schedule.trans
        data.terminalData.schedule_eq)

/-- The trace retains exactly the canonical outgoing-shortcut step. -/
theorem stop_remaining_eq_singleton
    (data :
      R324ShortcutStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    data.trace.stopPrefix.remaining =
      [data.terminalData.terminal] :=
  data.trace.stopPrefix_remaining_eq_singleton

/-- For a residual pairing, the retained terminal block is the intersection
of the stop active carrier with its ambient endpoint interval. -/
theorem terminal_block_eq_stop_active_inter_Icc
    (data :
      R324ShortcutStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    data.terminalData.terminal.2 =
      data.trace.stopPrefix.state.active ∩
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

/-- The retained step ends at the final internal vertex. -/
theorem terminal_right_eq_last
    (data :
      R324ShortcutStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    data.terminalData.terminal.1.2.val = m - 1 :=
  data.terminalData.terminal_right

/-- The scale transported through all proper blocks. -/
def stopScale
    (data :
      R324ShortcutStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    Fin (m + 1) → ℝ :=
  data.trace.stopScale

/-- The edge certificate transported to the stop state. -/
theorem stopCertificate
    (data :
      R324ShortcutStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    R324WithinHalfEdgeCertificate
      data.trace.stopPrefix.state data.stopScale :=
  data.trace.stopCertificate

/-- Exact processed/remaining perturbative-order ledger at the stop. -/
theorem order_ledger
    (data :
      R324ShortcutStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    (data.trace.stopPrefix.state.processed.map
        (fun step => residualBlockOrder step.2)).sum +
        data.trace.stopPrefix.remainingOrder =
      ((r322AnalyticSchedule κ).map
        (fun step => residualBlockOrder step.2)).sum := by
  simpa only [R324WithinHalfResidualPrefix.processedOrder] using
    data.trace.stopPrefix.processedOrder_add_remainingOrder

/-- Construct the shortcut package from any certificate for the all-Green
initial state.  No fullness hypothesis is used. -/
theorem exists_of_initial_certificate
    (hshortcut : Fin.last m ∈ extractedRightEdges κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K κ)
    (initialCertificate :
      R324WithinHalfEdgeCertificate
        (r324InitialWithinHalfEdgeState m)
        initialScale) :
    Nonempty
      (R324ShortcutStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) := by
  obtain ⟨terminalData⟩ :=
    exists_r324ShortcutTerminalSchedule κ hshortcut
  let initial :
      R324WithinHalfResidualPrefix ρ lam ε κ :=
    R324WithinHalfResidualPrefix.initial ρ lam ε κ
  let trace :
      R324WithinHalfStopBeforeLastTrace
        terminalData.terminal initial initialScale :=
    R324WithinHalfStopBeforeLastTrace.of_localBlockProvider
      hε hε1 provider terminalData.terminal
      terminalData.proper initial initialScale
      initialCertificate (by
        change
          r322AnalyticSchedule κ =
            terminalData.proper ++ [terminalData.terminal]
        exact terminalData.schedule_eq)
  exact ⟨{ terminalData := terminalData, trace := trace }⟩

/-- Standard initialization with one positive uniform scale. -/
theorem exists_of_localBlockProvider
    (hshortcut : Fin.last m ∈ extractedRightEdges κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K κ) :
    ∃ A : ℝ, 0 < A ∧
      Nonempty
        (R324ShortcutStopTraceAssembly
          (ρ := ρ) (C := C) (lam := lam)
          (ε := ε) (K := K) κ (fun _ => A)) := by
  obtain ⟨A, hA, hcertificate⟩ :=
    exists_r324InitialWithinHalfEdgeCertificate m
  exact
    ⟨A, hA,
      exists_of_initial_certificate
        hshortcut hε hε1 provider hcertificate⟩

end R324ShortcutStopTraceAssembly

end R324WithinHalfResidualPrefix

end

end Anderson4D
