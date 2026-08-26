import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingTerminalSchedule
import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfStopBeforeLastTrace

/-!
# Certified full-pairing traces stopping at the terminal block

For a full pairing on an even carrier, the analytic schedule has a canonical
last block.  This module combines that terminal schedule with the generic
within-half prefix iterator: all proper blocks are consumed, while the last
block and its global right endpoint remain visible for the final Fourier
estimate.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

namespace R324WithinHalfResidualPrefix

/-- A full-pairing terminal schedule together with a certified analytic
trace through precisely its proper prefix. -/
structure R324FullPairingStopTraceAssembly
    {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {q : ℕ} (κ : PartialPairing (Fin (2 * q)))
    (initialScale : Fin (2 * q + 1) → ℝ) where
  terminalData : R324FullPairingTerminalSchedule κ
  trace :
    R324WithinHalfStopBeforeLastTrace
      terminalData.terminal
      (R324WithinHalfResidualPrefix.initial ρ lam ε κ)
      initialScale
  terminal_block_eq_stop_active :
    terminalData.terminal.2 = trace.stopPrefix.state.active
  order_ledger :
    (trace.stopPrefix.state.processed.map
        (fun step => residualBlockOrder step.2)).sum +
        trace.stopPrefix.remainingOrder =
      q

namespace R324FullPairingStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    {initialScale : Fin (2 * q + 1) → ℝ}

/-- The retained terminal block ends at the global right endpoint. -/
theorem terminal_right_eq_last
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    data.terminalData.terminal.1.2.val = 2 * q - 1 :=
  data.terminalData.terminal_right

/-- The scale transported through all proper within-half blocks. -/
def stopScale
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    Fin (2 * q + 1) → ℝ :=
  data.trace.stopScale

/-- The coordinate restriction transported through all proper blocks. -/
def stopProjection
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    ((R324WithinHalfResidualPrefix.initial
          ρ lam ε κ).SurvivingCoordinate → T4) →
      (data.trace.stopPrefix.SurvivingCoordinate → T4) :=
  data.trace.stopProjection

/-- The terminal edge certificate after all proper blocks have been
consumed. -/
theorem stopCertificate
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    R324WithinHalfEdgeCertificate
      data.trace.stopPrefix.state data.stopScale :=
  data.trace.stopCertificate

/-- The trace retains exactly the canonical terminal step. -/
theorem stop_remaining_eq_singleton
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    data.trace.stopPrefix.remaining =
      [data.terminalData.terminal] :=
  data.trace.stopPrefix_remaining_eq_singleton

/-- Construct the terminal package from any certificate for the standard
all-Green initial prefix. -/
theorem exists_of_initial_certificate
    (hq : 1 ≤ q)
    (hκ : κ.IsFull)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K κ)
    (initialCertificate :
      R324WithinHalfEdgeCertificate
        (r324InitialWithinHalfEdgeState (2 * q))
        initialScale) :
    Nonempty
      (R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) := by
  obtain ⟨terminalData⟩ :=
    exists_r324FullPairingTerminalSchedule
      (m := 2 * q) (by omega) κ hκ
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
  have hprocessed :
      trace.stopPrefix.state.processed =
        terminalData.proper := by
    exact
      List.append_cancel_right
        (trace.stopPrefix_processed_append_terminal_eq_schedule.trans
          terminalData.schedule_eq)
  have hterminalActive :
      terminalData.terminal.2 =
        trace.stopPrefix.state.active := by
    rw [terminalData.terminal_block]
    unfold R324WithinHalfEdgeState.active
    rw [hprocessed]
  have hledger :
      (trace.stopPrefix.state.processed.map
          (fun step => residualBlockOrder step.2)).sum +
          trace.stopPrefix.remainingOrder =
        q := by
    rw [hprocessed, trace.stopPrefix_remainingOrder_eq]
    exact
      terminalData.sum_properBlockOrders_add_terminal hκ
  exact
    ⟨{
      terminalData := terminalData
      trace := trace
      terminal_block_eq_stop_active := hterminalActive
      order_ledger := hledger
    }⟩

/-- Consumer-facing standard initialization: choose one positive uniform
all-Green scale, then stop the certified trace at the canonical last block. -/
theorem exists_of_localBlockProvider
    (hq : 1 ≤ q)
    (hκ : κ.IsFull)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K κ) :
    ∃ A : ℝ, 0 < A ∧
      Nonempty
        (R324FullPairingStopTraceAssembly
          (ρ := ρ) (C := C) (lam := lam)
          (ε := ε) (K := K) κ (fun _ => A)) := by
  obtain ⟨A, hA, hcertificate⟩ :=
    exists_r324InitialWithinHalfEdgeCertificate (2 * q)
  exact
    ⟨A, hA,
      exists_of_initial_certificate
        hq hκ hε hε1 provider hcertificate⟩

end R324FullPairingStopTraceAssembly

end R324WithinHalfResidualPrefix

end

end Anderson4D
