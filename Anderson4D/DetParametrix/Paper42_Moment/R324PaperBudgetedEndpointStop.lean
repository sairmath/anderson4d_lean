import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfCompletedRoute

/-!
# Budget-synchronized transport stopping before an outgoing terminal

This is the retained-terminal analogue of
`exists_budgetSynchronizedAlternatingTransport`.  It follows the same
literal paper schedule, alternates ordinary runs with exceptional incoming
heads, and stops immediately before one prescribed last block.  The exact
signed endpoint-stop witness and the complete numerical budget are built
together, so the multiplier bound lives on the actual stop carrier used by
the outgoing Fourier identity.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}

/-- Exact endpoint-stop transport together with the complete budget on the
same stop state. -/
structure R324BudgetedEndpointStopAtTerminal
    (terminal : R322ExtractionStep m)
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (initialBudgetScale : Fin (m + 1) -> Real)
    (mode : Z4) where
  endpoint : R324WithinHalfEndpointStopAtTerminal terminal res
  stopBudgetScale : Fin (m + 1) -> Real
  stopReachable :
    R324WithinHalfBudgetScaleReachable
      pairing rho C lam eps K A endpoint.stop.state stopBudgetScale
  stopCertificate :
    R324WithinHalfEdgeCertificate endpoint.stop.state stopBudgetScale
  multiplier_budget :
    ‖endpoint.multiplier mode‖ * initialBudgetScale 0 <= stopBudgetScale 0

namespace R324BudgetedEndpointStopAtTerminal

/-- Paper-order endpoint-stop budget recursion.  The named terminal itself
is not consumed. -/
theorem exists_of_providers
    {mode : Z4}
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hC : 0 <= C) (hlam : 0 <= lam) (hK : 0 <= K) (hA : 1 <= A)
    (analyticProvider :
      R324WithinHalfLocalBlockProvider rho C lam eps K pairing)
    (budgetProvider :
      R324WithinHalfBudgetLocalBlockProvider
        rho C lam eps K A pairing)
    (headBudget :
      R324WithinHalfInsertedExceptionalHeadBudget
        rho C lam eps K pairing mode)
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (analyticScale budgetScale : Fin (m + 1) -> Real)
    (analyticCertificate :
      R324WithinHalfEdgeCertificate res.state analyticScale)
    (budgetReachable :
      R324WithinHalfBudgetScaleReachable
        pairing rho C lam eps K A res.state budgetScale)
    (budgetCertificate :
      R324WithinHalfEdgeCertificate res.state budgetScale)
    (hscale : forall edge, analyticScale edge <= budgetScale edge)
    (terminal : R322ExtractionStep m)
    (pre : List (R322ExtractionStep m))
    (hremaining : res.remaining = pre ++ [terminal]) :
    Nonempty
      (R324BudgetedEndpointStopAtTerminal
        (rho := rho) (C := C) (lam := lam) (eps := eps)
        (K := K) (A := A) terminal res budgetScale mode) := by
  by_cases hrun :
      pre.length <=
        r324WithinHalfOrdinaryRunLength
          res.state.processed res.remaining
  · obtain ⟨trace, stopBudgetScale, stopReachable,
        stopCertificate, _stopScaleLe, hstopZeroIfOrdinary⟩ :=
      R324IncomingExceptionalStopTraceAssembly.R324IncomingExceptionalBudgetedStopTraceAssembly.exists_pairedStopBefore
        hC hlam hK hA heps heps1 analyticProvider budgetProvider
        terminal [] pre res analyticScale budgetScale
        analyticCertificate budgetReachable budgetCertificate hscale
        (by simpa using hremaining)
    have hord : trace.OrdinaryAlong :=
      trace.ordinaryAlong_of_le_ordinaryRunLength pre
        (by simpa using hremaining) hrun
    let endpoint :=
      R324WithinHalfEndpointStopAtTerminal.of_ordinaryTrace trace hord
    refine ⟨{
      endpoint := endpoint
      stopBudgetScale := stopBudgetScale
      stopReachable := by
        simpa only [endpoint,
          R324WithinHalfEndpointStopAtTerminal.of_ordinaryTrace] using
            stopReachable
      stopCertificate := by
        simpa only [endpoint,
          R324WithinHalfEndpointStopAtTerminal.of_ordinaryTrace] using
            stopCertificate
      multiplier_budget := ?_ }⟩
    change ‖(1 : Complex)‖ * budgetScale 0 <= stopBudgetScale 0
    rw [norm_one, one_mul, hstopZeroIfOrdinary hord]
  · have hbefore :
        r324WithinHalfOrdinaryRunLength
            res.state.processed res.remaining < pre.length :=
      Nat.lt_of_not_ge hrun
    have hlt :
        r324WithinHalfOrdinaryRunLength
            res.state.processed res.remaining < res.remaining.length := by
      exact hbefore.trans (by
        rw [hremaining]
        simp only [List.length_append, List.length_singleton]
        omega)
    obtain ⟨nextTerminal, suffix, hdrop, _hslot⟩ :=
      r324WithinHalfOrdinaryRunLength_drop_eq_slotZero
        res.state.processed res.remaining hlt
    let ordinaryPre := res.remaining.take
      (r324WithinHalfOrdinaryRunLength
        res.state.processed res.remaining)
    have hsplit :
        res.remaining = ordinaryPre ++ nextTerminal :: suffix := by
      conv_lhs =>
        rw [← List.take_append_drop
          (r324WithinHalfOrdinaryRunLength
            res.state.processed res.remaining) res.remaining]
      rw [hdrop]
    have hordinaryLength :
        ordinaryPre.length =
          r324WithinHalfOrdinaryRunLength
            res.state.processed res.remaining := by
      dsimp only [ordinaryPre]
      rw [List.length_take, min_eq_left hlt.le]
    obtain ⟨trace, stopBudgetScale, stopReachable,
        stopCertificate, hstopScale, hstopZeroIfOrdinary⟩ :=
      R324IncomingExceptionalStopTraceAssembly.R324IncomingExceptionalBudgetedStopTraceAssembly.exists_pairedStopBefore
        hC hlam hK hA heps heps1 analyticProvider budgetProvider
        nextTerminal suffix ordinaryPre res analyticScale budgetScale
        analyticCertificate budgetReachable budgetCertificate hscale hsplit
    have hord : trace.OrdinaryAlong :=
      trace.ordinaryAlong_of_le_ordinaryRunLength ordinaryPre hsplit
        (le_of_eq hordinaryLength)
    have hstopZero : stopBudgetScale 0 = budgetScale 0 :=
      hstopZeroIfOrdinary hord
    let data : R324WithinHalfNextExceptionalStop res analyticScale :=
      { pre := ordinaryPre
        terminal := nextTerminal
        suffix := suffix
        remaining_eq := hsplit
        pre_length_eq := hordinaryLength
        trace := trace
        ordinary := hord }
    have hdataBefore : data.pre.length < pre.length := by
      dsimp only [data]
      rw [hordinaryLength]
      exact hbefore
    obtain ⟨post, hsuffix, hpostlt⟩ :=
      data.exists_terminalPrefix_lt pre hremaining hdataBefore
    obtain ⟨_analyticBound, nextAnalyticCertificate⟩ :=
      analyticProvider trace.stopPrefix nextTerminal suffix
        trace.stopPrefix_remaining_eq trace.stopScale trace.stopCertificate
    obtain ⟨_budgetBound, nextBudgetReachable,
        nextBudgetCertificate⟩ :=
      budgetProvider trace.stopPrefix nextTerminal suffix
        trace.stopPrefix_remaining_eq stopBudgetScale
        stopReachable stopCertificate
    let nextAnalyticScale :=
      r324WithinHalfUpdatedEdgeScale
        (trace.stopPrefix.headContext
          nextTerminal suffix trace.stopPrefix_remaining_eq)
        trace.stopScale C lam K
    let nextBudgetScale :=
      trace.stopPrefix.budgetUpdatedEdgeScale
        nextTerminal suffix trace.stopPrefix_remaining_eq
        stopBudgetScale C lam K
    have hnextScale : forall edge,
        nextAnalyticScale edge <= nextBudgetScale edge :=
      R324IncomingExceptionalStopTraceAssembly.R324IncomingExceptionalBudgetedStopTraceAssembly.analyticUpdate_le_budgetUpdate
        trace.stopPrefix nextTerminal suffix trace.stopPrefix_remaining_eq
        trace.stopScale stopBudgetScale trace.stopCertificate
        stopCertificate stopReachable hstopScale hC hlam hK hA
    obtain ⟨sub⟩ :=
      exists_of_providers heps heps1 hC hlam hK hA
        analyticProvider budgetProvider headBudget
        (trace.stopPrefix.afterHead
          nextTerminal suffix trace.stopPrefix_remaining_eq)
        nextAnalyticScale nextBudgetScale nextAnalyticCertificate
        nextBudgetReachable nextBudgetCertificate hnextScale
        terminal post (by
          rw [R324WithinHalfResidualPrefix.afterHead_remaining]
          exact hsuffix)
    let endpoint :=
      R324WithinHalfEndpointStopAtTerminal.composeNextExceptionalStop
        data heps heps1 sub.endpoint
    refine ⟨{
      endpoint := endpoint
      stopBudgetScale := sub.stopBudgetScale
      stopReachable := by
        simpa only [endpoint, data,
          R324WithinHalfEndpointStopAtTerminal.composeNextExceptionalStop]
          using sub.stopReachable
      stopCertificate := by
        simpa only [endpoint, data,
          R324WithinHalfEndpointStopAtTerminal.composeNextExceptionalStop]
          using sub.stopCertificate
      multiplier_budget := ?_ }⟩
    have hfactor :=
      headBudget trace.stopPrefix nextTerminal suffix
        trace.stopPrefix_remaining_eq stopBudgetScale stopCertificate
    have hout :
        stopBudgetScale
            (trace.stopPrefix.headContext nextTerminal suffix
              trace.stopPrefix_remaining_eq).outgoingSlot = A :=
      stopReachable.outgoingScale_eq_base trace.stopPrefix rfl
        nextTerminal suffix trace.stopPrefix_remaining_eq
    have hpred :
        r324WithinHalfPredecessorSlot
            trace.stopPrefix.state nextTerminal = 0 :=
      data.predecessorSlot_eq_zero
    have hfactorUpdate :
        ‖trace.stopPrefix.incomingExceptionalHeadCollapseFactor
            nextTerminal suffix trace.stopPrefix_remaining_eq mode‖ *
            budgetScale 0 <= nextBudgetScale 0 := by
      rw [← hstopZero]
      calc
        _ <=
            (r324WithinHalfInternalEdgeScaleProduct
                (trace.stopPrefix.headContext nextTerminal suffix
                  trace.stopPrefix_remaining_eq) stopBudgetScale *
              (C * lam) ^ (2 * residualBlockOrder nextTerminal.2) * K) *
                stopBudgetScale 0 :=
          mul_le_mul_of_nonneg_right hfactor
            (stopCertificate.scale_pos 0).le
        _ <= nextBudgetScale 0 := by
          have hnextEq : nextBudgetScale 0 =
              stopBudgetScale 0 *
                (r324WithinHalfInternalEdgeScaleProduct
                  (trace.stopPrefix.headContext nextTerminal suffix
                    trace.stopPrefix_remaining_eq) stopBudgetScale * A) *
                (C * lam) ^ (2 * residualBlockOrder nextTerminal.2) * K := by
            dsimp only [nextBudgetScale]
            rw [← hpred,
              trace.stopPrefix.budgetUpdatedEdgeScale_predecessor,
              trace.stopPrefix.headBlockScaleProduct_eq_internal_mul_outgoing,
              hout, hpred]
          rw [hnextEq]
          have hcore : 0 <=
              stopBudgetScale 0 *
                r324WithinHalfInternalEdgeScaleProduct
                  (trace.stopPrefix.headContext nextTerminal suffix
                    trace.stopPrefix_remaining_eq) stopBudgetScale *
                (C * lam) ^ (2 * residualBlockOrder nextTerminal.2) * K := by
            exact mul_nonneg
              (mul_nonneg
                (mul_nonneg (stopCertificate.scale_pos 0).le
                  (stopCertificate.internalEdgeScaleProduct_pos
                    (ctx := trace.stopPrefix.headContext nextTerminal suffix
                      trace.stopPrefix_remaining_eq)).le)
                (pow_nonneg (mul_nonneg hC hlam) _)) hK
          calc
            _ = stopBudgetScale 0 *
                  r324WithinHalfInternalEdgeScaleProduct
                    (trace.stopPrefix.headContext nextTerminal suffix
                      trace.stopPrefix_remaining_eq) stopBudgetScale *
                  (C * lam) ^ (2 * residualBlockOrder nextTerminal.2) * K := by
                ring
            _ <=
                (stopBudgetScale 0 *
                  r324WithinHalfInternalEdgeScaleProduct
                    (trace.stopPrefix.headContext nextTerminal suffix
                      trace.stopPrefix_remaining_eq) stopBudgetScale *
                  (C * lam) ^ (2 * residualBlockOrder nextTerminal.2) * K) * A :=
              le_mul_of_one_le_right hcore hA
            _ = _ := by ring
    change
      ‖sub.endpoint.multiplier mode *
          trace.stopPrefix.incomingExceptionalHeadCollapseFactor
            nextTerminal suffix trace.stopPrefix_remaining_eq mode‖ *
          budgetScale 0 <= sub.stopBudgetScale 0
    rw [norm_mul]
    calc
      ‖sub.endpoint.multiplier mode‖ *
            ‖trace.stopPrefix.incomingExceptionalHeadCollapseFactor
              nextTerminal suffix trace.stopPrefix_remaining_eq mode‖ *
            budgetScale 0 =
          ‖sub.endpoint.multiplier mode‖ *
            (‖trace.stopPrefix.incomingExceptionalHeadCollapseFactor
                nextTerminal suffix trace.stopPrefix_remaining_eq mode‖ *
              budgetScale 0) := by ring
      _ <= ‖sub.endpoint.multiplier mode‖ * nextBudgetScale 0 :=
        mul_le_mul_of_nonneg_left hfactorUpdate (norm_nonneg _)
      _ <= sub.stopBudgetScale 0 := sub.multiplier_budget
termination_by pre.length
decreasing_by exact hpostlt

/-- Consume the retained outgoing terminal by one complete-budget update
after its exact signed Fourier/primitive operation.  Since the terminal
predecessor is nonzero in the residual branch, slot zero is unchanged; any
first-incoming charge already controlled by the stop budget therefore
survives verbatim on `terminalPost`. -/
theorem completedRoute_after_outgoingTerminal
    (budgetProvider :
      R324WithinHalfBudgetLocalBlockProvider
        rho C lam eps K A pairing)
    (terminalData : R324ShortcutTerminalSchedule pairing)
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    {initialBudgetScale : Fin (m + 1) -> Real}
    {mode : Z4}
    (data : R324BudgetedEndpointStopAtTerminal
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) terminalData.terminal res
      initialBudgetScale mode)
    (hpred :
      r324WithinHalfPredecessorSlot data.endpoint.stop.state
          terminalData.terminal ≠ 0)
    (cases : R324PaperHalfEndpointCases)
    (firstCharge : Real) (hfirstNonneg : 0 <= firstCharge)
    (hfirst : firstCharge <= initialBudgetScale 0) :
    let outgoing : R324PaperOutgoingEndpointTerminal res :=
      { terminalData := terminalData
        endpoint := data.endpoint }
    exists route : R324PaperHalfCompletedRoute
        (rho := rho) (C := C) (lam := lam) (eps := eps)
        (K := K) (A := A) pairing mode,
      route.cases = cases /\ route.final = outgoing.terminalPost := by
  dsimp only
  let outgoing : R324PaperOutgoingEndpointTerminal res :=
    { terminalData := terminalData
      endpoint := data.endpoint }
  let terminalScale :=
    data.endpoint.stop.budgetUpdatedEdgeScale
      terminalData.terminal [] data.endpoint.stop_remaining
      data.stopBudgetScale C lam K
  obtain ⟨_terminalBound, terminalReachable, terminalCertificate⟩ :=
    budgetProvider data.endpoint.stop terminalData.terminal []
      data.endpoint.stop_remaining data.stopBudgetScale
      data.stopReachable data.stopCertificate
  have hterminalZero : terminalScale 0 = data.stopBudgetScale 0 := by
    dsimp only [terminalScale]
    rw [data.endpoint.stop.budgetUpdatedEdgeScale_of_ne]
    exact Ne.symm hpred
  have hcharge :
      ‖data.endpoint.multiplier mode‖ * firstCharge <= terminalScale 0 := by
    calc
      _ <= ‖data.endpoint.multiplier mode‖ * initialBudgetScale 0 :=
        mul_le_mul_of_nonneg_left hfirst (norm_nonneg _)
      _ <= data.stopBudgetScale 0 := data.multiplier_budget
      _ = terminalScale 0 := hterminalZero.symm
  let route : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing mode :=
    R324PaperHalfCompletedRoute.ofOutgoingTerminalPost outgoing
      terminalScale
      (by simpa only [outgoing,
        R324PaperOutgoingEndpointTerminal.terminalPost] using
          terminalReachable)
      (by simpa only [outgoing,
        R324PaperOutgoingEndpointTerminal.terminalPost] using
          terminalCertificate)
      cases (data.endpoint.multiplier mode) firstCharge hfirstNonneg hcharge
  exact ⟨route, rfl, rfl⟩

end R324BudgetedEndpointStopAtTerminal

end R324WithinHalfResidualPrefix

end

end Anderson4D
