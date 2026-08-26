import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingBudgetStopTrace
import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingTerminalFourier

/-!
# One coherent budget and terminal-Fourier package for a full pairing

The numerical budget trace and the analytic terminal geometry are built
with different scale updates: the budget update also charges the outgoing
Green edge.  Their scale functions therefore must not be identified.
Nevertheless, their reached *residual state* is canonical, because both
have consumed the same literal proper prefix of the analytic schedule.

This module records that state identification explicitly.  Downstream
arguments can use the complete budget product and the exact terminal
Fourier identity from one package, without silently assuming that two
independently constructed stop states coincide.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfStateReachable

/-- Algebraic reachability is deterministic once the processed schedule
prefix is fixed. -/
theorem eq_of_processed_eq
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {left right : R324WithinHalfEdgeState m}
    (hleft :
      R324WithinHalfStateReachable pairing ρ lam ε left)
    (hright :
      R324WithinHalfStateReachable pairing ρ lam ε right)
    (hprocessed : left.processed = right.processed) :
    left = right := by
  induction hleft generalizing right with
  | initial =>
      cases hright with
      | initial =>
          rfl
      | absorb ctx hctx =>
          simp [r324InitialWithinHalfEdgeState,
            R324WithinHalfStepContext.absorb] at hprocessed
  | absorb ctx hctx ih =>
      cases hright with
      | initial =>
          simp [r324InitialWithinHalfEdgeState,
            R324WithinHalfStepContext.absorb] at hprocessed
      | absorb other hother =>
          have happend :
              ctx.state.processed ++ [ctx.step] =
                other.state.processed ++ [other.step] := by
            simpa only [R324WithinHalfStepContext.absorb] using hprocessed
          have hreverse :=
            congrArg List.reverse happend
          have hcons :
              ctx.step :: ctx.state.processed.reverse =
                other.step :: other.state.processed.reverse := by
            simpa only [List.reverse_append, List.reverse_singleton,
              List.singleton_append] using hreverse
          have hstep : ctx.step = other.step :=
            (List.cons.inj hcons).1
          have hprocessedBefore :
              ctx.state.processed =
                other.state.processed := by
            have htails :=
              (List.cons.inj hcons).2
            have hreversed :=
              congrArg List.reverse htails
            simpa only [List.reverse_reverse] using hreversed
          have hstate : ctx.state = other.state :=
            ih hother hprocessedBefore
          have hsuffix : ctx.suffix = other.suffix := by
            have hschedules :
                ctx.state.processed ++ ctx.step :: ctx.suffix =
                  other.state.processed ++
                    other.step :: other.suffix :=
              ctx.schedule_eq.symm.trans other.schedule_eq
            rw [hstate, hstep] at hschedules
            exact
              (List.cons.inj
                (List.append_cancel_left hschedules)).2
          have hctx : ctx = other := by
            cases ctx
            cases other
            simp_all
          subst other
          rfl

end R324WithinHalfStateReachable

namespace R324FullPairingTerminalSchedule

/-- The decomposition of a nonempty analytic schedule into its proper
prefix and singleton final step is unique. -/
theorem unique
    {m : ℕ} {κ : PartialPairing (Fin m)}
    (left right : R324FullPairingTerminalSchedule κ) :
    left = right := by
  have happend :
      left.proper ++ [left.terminal] =
        right.proper ++ [right.terminal] :=
    left.schedule_eq.symm.trans right.schedule_eq
  have hreverse := congrArg List.reverse happend
  have hcons :
      left.terminal :: left.proper.reverse =
        right.terminal :: right.proper.reverse := by
    simpa only [List.reverse_append, List.reverse_singleton,
      List.singleton_append] using hreverse
  have hterminal : left.terminal = right.terminal :=
    (List.cons.inj hcons).1
  have hproper : left.proper = right.proper := by
    have htails := (List.cons.inj hcons).2
    have hreversed := congrArg List.reverse htails
    simpa only [List.reverse_reverse] using hreversed
  cases left
  cases right
  simp_all

end R324FullPairingTerminalSchedule

namespace R324WithinHalfResidualPrefix

/-- Residual prefixes are determined by their algebraic state and literal
remaining suffix; the schedule and reachability fields are propositions. -/
theorem eq_of_state_eq_of_remaining_eq
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (left right :
      R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hstate : left.state = right.state)
    (hremaining : left.remaining = right.remaining) :
    left = right := by
  cases left
  cases right
  rw [Anderson4D.R324WithinHalfResidualPrefix.mk.injEq]
  exact ⟨hstate, hremaining⟩

/-- Two residual prefixes which have consumed the complete analytic
schedule are the same dependent carrier.  This is the reusable terminal
uniqueness form of `R324WithinHalfStateReachable.eq_of_processed_eq`: the
edge state is forced by reachability and the processed list, while both
remaining suffixes are empty. -/
theorem eq_of_processed_schedule_of_remaining_nil
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (left right : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hleftProcessed :
      left.state.processed = r322AnalyticSchedule pairing)
    (hrightProcessed :
      right.state.processed = r322AnalyticSchedule pairing)
    (hleftRemaining : left.remaining = [])
    (hrightRemaining : right.remaining = []) :
    left = right := by
  apply eq_of_state_eq_of_remaining_eq left right
  · exact R324WithinHalfStateReachable.eq_of_processed_eq
      left.reachable right.reachable
      (hleftProcessed.trans hrightProcessed.symm)
  · rw [hleftRemaining, hrightRemaining]

/-- One package carrying both the complete numerical budget and the exact
terminal analytic/Fourier view.

The scale functions are intentionally kept separate.  The equality field
identifies only the reached residual prefix, which is precisely the object
on which the terminal geometry depends. -/
structure R324FullPairingBudgetTerminalAdapter
    {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    (budget :
      R324FullPairingBudgetStopTrace
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) (A := A) κ) where
  initialScale : Fin (2 * q + 1) → ℝ
  geometry :
    R324FullPairingStopTraceAssembly
      (ρ := ρ) (C := C) (lam := lam)
      (ε := ε) (K := K) κ initialScale
  terminalData_eq :
    geometry.terminalData = budget.terminalData
  stopPrefix_eq :
    geometry.trace.stopPrefix = budget.stopPrefix

namespace R324FullPairingBudgetTerminalAdapter

variable {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    {budget :
      R324FullPairingBudgetStopTrace
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) (A := A) κ}

/-- Any analytic terminal assembly for the same pairing canonically
adapts to a quantitative budget stop: algebraic reachability and the
literal processed prefix force the two residual states to agree. -/
def ofAssembly
    {initialScale : Fin (2 * q + 1) → ℝ}
    (geometry :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    R324FullPairingBudgetTerminalAdapter budget := by
  have hterminal :
      geometry.terminalData = budget.terminalData :=
    R324FullPairingTerminalSchedule.unique _ _
  have hprocessed :
      geometry.trace.stopPrefix.state.processed =
        budget.stopPrefix.state.processed := by
    have hgeometry :
        geometry.trace.stopPrefix.state.processed ++
            [budget.terminalData.terminal] =
          r322AnalyticSchedule κ := by
      rw [← hterminal]
      exact
        geometry.trace.stopPrefix_processed_append_terminal_eq_schedule
    exact
      List.append_cancel_right
        (hgeometry.trans
          budget.stop_processed_append_terminal_eq_schedule.symm)
  have hstate :
      geometry.trace.stopPrefix.state =
        budget.stopPrefix.state :=
    R324WithinHalfStateReachable.eq_of_processed_eq
      geometry.trace.stopPrefix.reachable
      budget.stopPrefix.reachable hprocessed
  have hremaining :
      geometry.trace.stopPrefix.remaining =
        budget.stopPrefix.remaining := by
    rw [geometry.stop_remaining_eq_singleton,
      budget.stop_remaining_eq_singleton, hterminal]
  have hstop :
      geometry.trace.stopPrefix = budget.stopPrefix := by
    exact
      eq_of_state_eq_of_remaining_eq
        geometry.trace.stopPrefix budget.stopPrefix
        hstate hremaining
  exact
    {
      initialScale := initialScale
      geometry := geometry
      terminalData_eq := hterminal
      stopPrefix_eq := hstop
    }

/-- The complete budget reachability witness remains attached to the
same reached state used by `geometry`. -/
theorem reachable
    (data : R324FullPairingBudgetTerminalAdapter budget) :
    R324WithinHalfBudgetScaleReachable
      κ ρ C lam ε K A
      data.geometry.trace.stopPrefix.state
      budget.stopScale := by
  rw [data.stopPrefix_eq]
  exact budget.reachable

/-- The complete edge certificate remains attached to the same reached
state used by `geometry`. -/
theorem certificate
    (data : R324FullPairingBudgetTerminalAdapter budget) :
    R324WithinHalfEdgeCertificate
      data.geometry.trace.stopPrefix.state
      budget.stopScale := by
  rw [data.stopPrefix_eq]
  exact budget.certificate

/-- Exact complete active-scale product, written on the analytic geometry
state identified by this adapter. -/
theorem activeEdgeScaleProduct_eq
    (data : R324FullPairingBudgetTerminalAdapter budget) :
    (∏ edge ∈
        ({0} ∪
          data.geometry.trace.stopPrefix.state.active.image
            r324InternalVertexEdgeSlot),
      budget.stopScale edge) =
      (∏ _edge ∈
          ({0} ∪
            (r324InitialWithinHalfEdgeState
              (2 * q)).active.image
              r324InternalVertexEdgeSlot),
        A) *
        (C * lam) ^
          (2 *
            (budget.terminalData.proper.map
              (fun step =>
                residualBlockOrder step.2)).sum) *
        K ^ budget.terminalData.proper.length := by
  rw [data.stopPrefix_eq]
  exact budget.activeEdgeScaleProduct_eq

/-- Exact terminal endpoint-first Fourier identity on the residual state
which also carries the complete budget witness.  The primitive-pairing sum
remains grouped inside `terminalGroupedPrimitiveCore`. -/
theorem integral_char_mul_terminal_rawLocal_translated
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (β : Z4) (x : T4)
    (t :
      Fin
          (2 * residualBlockOrder
            data.geometry.terminalData.terminal.2) →
        T4) :
    (∫ y : T4,
        charT4 β y *
          ((data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).rawLocalIntegrand
              ρ ε (x - y) (fun j => t j - y) : ℂ)
        ∂paperMeasure) =
      (data.geometry.terminalGroupedPrimitiveCore x t : ℂ) *
        r324EndpointCoefficient β
          (t (primitiveLast
            (residualBlockOrder
              data.geometry.terminalData.terminal.2)
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).one_le_blockOrder))
          (t ⟨0, by
            have hn :=
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
            exact
              Nat.mul_pos (by decide)
                (Nat.zero_lt_of_lt hn)⟩)
          true :=
  data.geometry.integral_char_mul_terminal_rawLocal_translated β x t

end R324FullPairingBudgetTerminalAdapter

end R324WithinHalfResidualPrefix

end

end Anderson4D
