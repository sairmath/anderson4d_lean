import Anderson4D.DetParametrix.Paper42_Moment.R324StopBeforeStepTrace
import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalStop
import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingOuterIndependence

/-!
# Certified traces stopping before an exceptional incoming collapse

If the first internal vertex is removed by the within-half analytic
schedule, it belongs to an actual extraction block whose left endpoint is
zero.  This module constructs the certified residual trace directly from
the initial prefix to the state immediately before that block.  In
particular, the state underlying the incoming exceptional stop is
definitionally the state produced by the quantitative trace; no
reachability-uniqueness comparison is required.

The retained block and its complete suffix remain unintegrated.  This file
contains only schedule, certificate, order, and boundary geometry ledgers;
no endpoint Fubini exchange is performed.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

namespace R324WithinHalfResidualPrefix

/-- A certified trace from the all-Green initial prefix to immediately
before a schedule block beginning at the first internal vertex. -/
structure R324IncomingExceptionalStopTraceAssembly
    {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} (κ : PartialPairing (Fin m))
    (initialScale : Fin (m + 1) → ℝ) where
  pre : List (R322ExtractionStep m)
  suffix : List (R322ExtractionStep m)
  terminal : R322ExtractionStep m
  schedule_eq :
    r322AnalyticSchedule κ =
      pre ++ terminal :: suffix
  left_eq_zero :
    terminal.1.1.val = 0
  trace :
    R324WithinHalfStopBeforeStepTrace
      terminal suffix
      (R324WithinHalfResidualPrefix.initial ρ lam ε κ)
      initialScale

namespace R324IncomingExceptionalStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- The genuine residual context at the retained exceptional head. -/
def stopContext
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    R324WithinHalfStepContext κ :=
  data.trace.stopPrefix.headContext
    data.terminal data.suffix
    data.trace.stopPrefix_remaining_eq

/-- The trace stop, viewed through the local incoming-exceptional API.
The residual state is literally the trace's stopping state. -/
def incomingStop
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    R324IncomingExceptionalStop ρ lam ε κ where
  ctx := data.stopContext
  reachable := data.trace.stopPrefix.reachable
  left_eq_zero := data.left_eq_zero

/-- The trace consumes exactly the recorded proper prefix. -/
theorem stop_processed_eq_pre
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    data.trace.stopPrefix.state.processed =
      data.pre := by
  exact
    List.append_cancel_right
      (data.trace.stopPrefix_processed_append_eq_schedule.trans
        data.schedule_eq)

/-- The retained literal suffix begins with the exceptional block. -/
theorem stop_remaining_eq
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    data.trace.stopPrefix.remaining =
      data.terminal :: data.suffix :=
  data.trace.stopPrefix_remaining_eq

/-- Processed prefix followed by the exceptional block and its suffix is
the complete analytic schedule. -/
theorem stop_processed_append_eq_schedule
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    data.trace.stopPrefix.state.processed ++
        (data.terminal :: data.suffix) =
      r322AnalyticSchedule κ :=
  data.trace.stopPrefix_processed_append_eq_schedule

/-- The scale transported through exactly the recorded prefix. -/
def stopScale
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    Fin (m + 1) → ℝ :=
  data.trace.stopScale

/-- The edge certificate genuinely transported to the exceptional stop. -/
theorem stopCertificate
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    R324WithinHalfEdgeCertificate
      data.trace.stopPrefix.state data.stopScale :=
  data.trace.stopCertificate

/-- Exact order retained at the stop: the exceptional block plus every
later block, with neither part absorbed. -/
theorem stop_remainingOrder_eq
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    data.trace.stopPrefix.remainingOrder =
      residualBlockOrder data.terminal.2 +
        (data.suffix.map
          (fun step => residualBlockOrder step.2)).sum :=
  data.trace.stopPrefix_remainingOrder_eq

/-- Exact processed/remaining perturbative-order ledger at the stop. -/
theorem order_ledger
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    (data.trace.stopPrefix.state.processed.map
        (fun step => residualBlockOrder step.2)).sum +
        data.trace.stopPrefix.remainingOrder =
      ((r322AnalyticSchedule κ).map
        (fun step => residualBlockOrder step.2)).sum := by
  simpa only [R324WithinHalfResidualPrefix.processedOrder] using
    data.trace.stopPrefix.processedOrder_add_remainingOrder

/-- The retained exceptional head has incoming predecessor slot zero. -/
theorem stop_predecessorSlot_eq_zero
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    r324WithinHalfPredecessorSlot
        data.trace.stopPrefix.state data.terminal =
      0 := by
  exact
    data.trace.stopPrefix.predecessorSlot_eq_zero_of_head_left_eq_zero
      data.terminal data.left_eq_zero

/-- At positive order, the incoming external edge is still the untouched
free Green kernel immediately before the exceptional collapse. -/
theorem stop_incomingEdge_eq_greenFn
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (hm : 0 < m) :
    data.trace.stopPrefix.state.edges 0 =
      greenFn :=
  data.incomingStop.state_edge_zero_eq_greenFn hm

/-- The named predecessor edge at the exceptional stop is the free Green
kernel used by the incoming pre-collapse Fourier identity. -/
theorem stop_predecessorEdge_eq_greenFn
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (hm : 0 < m) :
    data.trace.stopPrefix.state.edges
        (r324WithinHalfPredecessorSlot
          data.trace.stopPrefix.state data.terminal) =
      greenFn :=
  data.incomingStop.state_edge_predecessor_eq_greenFn hm

/-- Construct the exceptional-stop package from any certificate for the
standard all-Green initial state.  The trace is built directly from the
same schedule decomposition that selects the exceptional block. -/
theorem exists_of_initial_certificate
    (hm : 0 < m)
    (hremoved :
      (⟨0, hm⟩ : Fin m) ∉ finalActive κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K κ)
    (initialCertificate :
      R324WithinHalfEdgeCertificate
        (r324InitialWithinHalfEdgeState m)
        initialScale) :
    Nonempty
      (R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) := by
  let first : Fin m := ⟨0, hm⟩
  have hcovered :
      first ∈ finsetUnionList (extractionBlocks κ) := by
    by_contra hnot
    apply hremoved
    rw [finalActive_eq_sdiff_extractionBlocks]
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ first, hnot⟩
  obtain ⟨B, hB, hfirstB⟩ :=
    (mem_finsetUnionList_iff (extractionBlocks κ)).mp hcovered
  have hBschedule :
      B ∈ (r322AnalyticSchedule κ).map Prod.snd :=
    (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).mem_iff.mpr hB
  obtain ⟨terminal, hterminal, hterminalBlock⟩ :=
    List.mem_map.mp hBschedule
  have hfirstTerminal : first ∈ terminal.2 := by
    rw [hterminalBlock]
    exact hfirstB
  have haligned :=
    r322AnalyticSchedule_forall_aligned κ terminal hterminal
  have hleftZero : terminal.1.1.val = 0 := by
    have hle := (haligned.2.2 first hfirstTerminal).1
    change terminal.1.1.val ≤ first.val at hle
    dsimp only [first] at hle
    omega
  obtain ⟨pre, suffix, hschedule⟩ :=
    List.mem_iff_append.mp hterminal
  let initial :
      R324WithinHalfResidualPrefix ρ lam ε κ :=
    R324WithinHalfResidualPrefix.initial ρ lam ε κ
  let trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix initial initialScale :=
    R324WithinHalfStopBeforeStepTrace.of_localBlockProvider
      hε hε1 provider terminal suffix pre
      initial initialScale initialCertificate
      (by
        change
          r322AnalyticSchedule κ =
            pre ++ terminal :: suffix
        exact hschedule)
  exact
    ⟨{
      pre := pre
      suffix := suffix
      terminal := terminal
      schedule_eq := hschedule
      left_eq_zero := hleftZero
      trace := trace
    }⟩

/-- Standard initialization with one positive uniform all-Green scale. -/
theorem exists_of_localBlockProvider
    (hm : 0 < m)
    (hremoved :
      (⟨0, hm⟩ : Fin m) ∉ finalActive κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K κ) :
    ∃ A : ℝ, 0 < A ∧
      Nonempty
        (R324IncomingExceptionalStopTraceAssembly
          (ρ := ρ) (C := C) (lam := lam)
          (ε := ε) (K := K) κ (fun _ => A)) := by
  obtain ⟨A, hA, hcertificate⟩ :=
    exists_r324InitialWithinHalfEdgeCertificate m
  exact
    ⟨A, hA,
      exists_of_initial_certificate
        hm hremoved hε hε1 provider hcertificate⟩

end R324IncomingExceptionalStopTraceAssembly

end R324WithinHalfResidualPrefix

end

end Anderson4D
