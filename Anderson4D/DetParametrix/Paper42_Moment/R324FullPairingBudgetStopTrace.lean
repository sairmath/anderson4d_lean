import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingStopTraceAssembly
import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfBudgetInvariant

/-!
# Quantitative full-pairing traces stopping before the terminal block

The light stop trace retains the exact analytic prefix iteration, but its
scale update intentionally omits the outgoing Green scale.  This module
builds the quantitative companion directly from the complete-budget local
provider.  It consumes the same literal proper prefix of the canonical
full-pairing schedule and leaves the last block untouched, while retaining
the budget-reachability witness needed by the exact active-scale product
ledger.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace R324WithinHalfResidualPrefix

/-! ## Literal budget iteration stopping before one specified block -/

/-- Consume exactly `pre` with the complete-budget provider and leave
`terminal` untouched.  Reachability is constructed at each literal head;
it is not inferred from an analytic stop trace. -/
private theorem exists_budgetStopBeforeLast_of_provider
    {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (provider :
      R324WithinHalfBudgetLocalBlockProvider
        ρ C lam ε K A pairing)
    (terminal : R322ExtractionStep m)
    (pre : List (R322ExtractionStep m))
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing)
    (scale : Fin (m + 1) → ℝ)
    (reachable :
      R324WithinHalfBudgetScaleReachable
        pairing ρ C lam ε K A res.state scale)
    (certificate :
      R324WithinHalfEdgeCertificate res.state scale)
    (hremaining :
      res.remaining = pre ++ [terminal]) :
    ∃ (stop :
        R324WithinHalfResidualPrefix ρ lam ε pairing)
      (stopScale : Fin (m + 1) → ℝ),
      stop.remaining = [terminal] ∧
        R324WithinHalfBudgetScaleReachable
          pairing ρ C lam ε K A
          stop.state stopScale ∧
        R324WithinHalfEdgeCertificate
          stop.state stopScale := by
  cases pre with
  | nil =>
      exact
        ⟨res, scale, by simpa using hremaining,
          reachable, certificate⟩
  | cons head rest =>
      let tail : List (R322ExtractionStep m) :=
        rest ++ [terminal]
      have hhead :
          res.remaining = head :: tail := by
        simpa only [tail, List.cons_append] using hremaining
      obtain ⟨_localBound, nextReachable,
          nextCertificate⟩ :=
        provider res head tail hhead scale
          reachable certificate
      exact
        exists_budgetStopBeforeLast_of_provider
          provider terminal rest
          (res.afterHead head tail hhead)
          (res.budgetUpdatedEdgeScale
            head tail hhead scale C lam K)
          nextReachable nextCertificate rfl
termination_by pre.length

/-! ## Full-pairing quantitative stop package -/

/-- A full-pairing schedule stopped immediately before its canonical last
block, with the complete numerical edge budget still attached.

The processed and remaining lists are recorded exactly, not merely up to a
permutation, so the product and perturbative-order ledgers can be consumed
without reconstructing the budget history. -/
structure R324FullPairingBudgetStopTrace
    {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {q : ℕ} (κ : PartialPairing (Fin (2 * q))) where
  base_one_le : 1 ≤ A
  terminalData : R324FullPairingTerminalSchedule κ
  stopPrefix :
    R324WithinHalfResidualPrefix ρ lam ε κ
  stopScale : Fin (2 * q + 1) → ℝ
  reachable :
    R324WithinHalfBudgetScaleReachable
      κ ρ C lam ε K A stopPrefix.state stopScale
  certificate :
    R324WithinHalfEdgeCertificate
      stopPrefix.state stopScale
  stop_processed_eq_proper :
    stopPrefix.state.processed = terminalData.proper
  stop_remaining_eq_singleton :
    stopPrefix.remaining = [terminalData.terminal]
  terminal_block_eq_stop_active :
    terminalData.terminal.2 = stopPrefix.state.active
  order_ledger :
    (stopPrefix.state.processed.map
        (fun step => residualBlockOrder step.2)).sum +
        stopPrefix.remainingOrder =
      q

namespace R324FullPairingBudgetStopTrace

variable {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}

/-- The retained block still has the global right endpoint. -/
theorem terminal_right_eq_last
    (data :
      R324FullPairingBudgetStopTrace
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) (A := A) κ) :
    data.terminalData.terminal.1.2.val = 2 * q - 1 :=
  data.terminalData.terminal_right

/-- The unprocessed perturbative order is exactly the retained block order. -/
theorem stop_remainingOrder_eq_terminal
    (data :
      R324FullPairingBudgetStopTrace
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) (A := A) κ) :
    data.stopPrefix.remainingOrder =
      residualBlockOrder data.terminalData.terminal.2 := by
  unfold R324WithinHalfResidualPrefix.remainingOrder
  rw [data.stop_remaining_eq_singleton]
  rfl

/-- The stopped processed prefix followed by the terminal block is the
complete analytic schedule. -/
theorem stop_processed_append_terminal_eq_schedule
    (data :
      R324FullPairingBudgetStopTrace
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) (A := A) κ) :
    data.stopPrefix.state.processed ++
        [data.terminalData.terminal] =
      r322AnalyticSchedule κ := by
  rw [data.stop_processed_eq_proper]
  exact data.terminalData.schedule_eq.symm

/-- Exact active-scale product after every proper block has been consumed.
This is the quantitative invariant at the point where the terminal Fourier
estimate starts. -/
theorem activeEdgeScaleProduct_eq
    (data :
      R324FullPairingBudgetStopTrace
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) (A := A) κ) :
    (∏ edge ∈
        ({0} ∪ data.stopPrefix.state.active.image
          r324InternalVertexEdgeSlot),
      data.stopScale edge) =
      (∏ _edge ∈
          ({0} ∪
            (r324InitialWithinHalfEdgeState
              (2 * q)).active.image
              r324InternalVertexEdgeSlot),
        A) *
        (C * lam) ^
          (2 *
            (data.terminalData.proper.map
              (fun step =>
                residualBlockOrder step.2)).sum) *
        K ^ data.terminalData.proper.length := by
  have hproduct :=
    data.reachable.activeEdgeScaleProduct_eq
  unfold r324WithinHalfProcessedOrder at hproduct
  rw [data.stop_processed_eq_proper] at hproduct
  exact hproduct

/-- Construct the quantitative stop package from a fixed uniform initial
certificate and the complete-budget local provider. -/
theorem exists_of_initial_certificate
    (hq : 1 ≤ q)
    (hκ : κ.IsFull)
    (hA : 1 ≤ A)
    (provider :
      R324WithinHalfBudgetLocalBlockProvider
        ρ C lam ε K A κ)
    (initialCertificate :
      R324WithinHalfEdgeCertificate
        (r324InitialWithinHalfEdgeState (2 * q))
        (fun _ => A)) :
    Nonempty
      (R324FullPairingBudgetStopTrace
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) (A := A) κ) := by
  obtain ⟨terminalData⟩ :=
    exists_r324FullPairingTerminalSchedule
      (m := 2 * q) (by omega) κ hκ
  let initial :
      R324WithinHalfResidualPrefix ρ lam ε κ :=
    R324WithinHalfResidualPrefix.initial ρ lam ε κ
  obtain ⟨stopPrefix, stopScale, hremaining,
      hreachable, hcertificate⟩ :=
    exists_budgetStopBeforeLast_of_provider
      provider terminalData.terminal terminalData.proper
      initial (fun _ => A)
      R324WithinHalfBudgetScaleReachable.initial
      initialCertificate (by
        change
          r322AnalyticSchedule κ =
            terminalData.proper ++ [terminalData.terminal]
        exact terminalData.schedule_eq)
  have hprocessed :
      stopPrefix.state.processed =
        terminalData.proper := by
    have hschedule := stopPrefix.schedule_eq
    rw [hremaining] at hschedule
    exact
      List.append_cancel_right
        (hschedule.symm.trans terminalData.schedule_eq)
  have hterminalActive :
      terminalData.terminal.2 =
        stopPrefix.state.active := by
    rw [terminalData.terminal_block]
    unfold R324WithinHalfEdgeState.active
    rw [hprocessed]
  have hledger :
      (stopPrefix.state.processed.map
          (fun step => residualBlockOrder step.2)).sum +
          stopPrefix.remainingOrder =
        q := by
    rw [hprocessed]
    unfold R324WithinHalfResidualPrefix.remainingOrder
    rw [hremaining]
    simpa using
      terminalData.sum_properBlockOrders_add_terminal hκ
  exact
    ⟨{
      base_one_le := hA
      terminalData := terminalData
      stopPrefix := stopPrefix
      stopScale := stopScale
      reachable := hreachable
      certificate := hcertificate
      stop_processed_eq_proper := hprocessed
      stop_remaining_eq_singleton := hremaining
      terminal_block_eq_stop_active := hterminalActive
      order_ledger := hledger
    }⟩

/-- Consumer-facing initialization: choose the repository-wide uniform
all-Green scale, then use the provider available at that scale. -/
theorem exists_with_uniform_initial_scale
    (hq : 1 ≤ q)
    (hκ : κ.IsFull)
    (provider :
      ∀ A : ℝ, 1 ≤ A →
        R324WithinHalfBudgetLocalBlockProvider
          ρ C lam ε K A κ) :
    ∃ A : ℝ, 1 ≤ A ∧
      Nonempty
        (R324FullPairingBudgetStopTrace
          (ρ := ρ) (C := C) (lam := lam)
          (ε := ε) (K := K) (A := A) κ) := by
  obtain ⟨A, hA, hinitial⟩ :=
    exists_r324InitialWithinHalfEdgeCertificate_one_le_uniform
  exact
    ⟨A, hA,
      exists_of_initial_certificate
        hq hκ hA (provider A hA) (hinitial (2 * q))⟩

/-- Proposition 4.1 supplies both numerical constants and the complete
budget stop package, uniformly before the perturbative order and pairing. -/
theorem exists_of_prop41
    {supportConstant : ℝ}
    (hsupport : 0 < supportConstant)
    (hq : 1 ≤ q)
    (hκ : κ.IsFull)
    (hC : 0 < C) (hlam : 0 < lam)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|)
    (hprop :
      R324WithinHalfProp41Provider
        ρ C lam ε supportConstant κ) :
    ∃ K : ℝ, 0 < K ∧
      ∃ A : ℝ, 1 ≤ A ∧
        Nonempty
          (R324FullPairingBudgetStopTrace
            (ρ := ρ) (C := C) (lam := lam)
            (ε := ε) (K := K) (A := A) κ) := by
  obtain ⟨K, hK, hprovider⟩ :=
    exists_r324WithinHalf_budgetLocalBlockProvider hsupport
  obtain ⟨A, hA, hinitial⟩ :=
    exists_r324InitialWithinHalfEdgeCertificate_one_le_uniform
  refine ⟨K, hK, A, hA, ?_⟩
  exact
    exists_of_initial_certificate
      hq hκ hA
      (hprovider ρ C lam ε A (2 * q) κ
        hA hC hlam hε hε1 hlog hprop)
      (hinitial (2 * q))

end R324FullPairingBudgetStopTrace

end R324WithinHalfResidualPrefix

end

end Anderson4D
