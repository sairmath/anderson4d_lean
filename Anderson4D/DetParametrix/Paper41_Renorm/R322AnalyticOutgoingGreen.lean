import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticProcessedIntegrandBridge

/-! # Free outgoing edges along the R-322 collapse schedule

The analytic schedule has strictly increasing right endpoints.  A proper
collapse only replaces its predecessor edge, which lies strictly to the left
of the collapsed block.  Consequently every edge strictly to the right of
all processed right endpoints is still the original Green kernel.  In
particular, the outgoing edge of the next scheduled block is free.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

namespace R322AnalyticEdgeState

variable {q : ℕ} {hq : 1 ≤ q}

/-- A proper update does not alter an edge lying strictly to the right of the
current block's right endpoint. -/
theorem updateProper_edges_eq_of_right_lt
    (state : R322AnalyticEdgeState q hq)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (suffix : List (R322ExtractionStep (2 * q)))
    (step : R322ExtractionStep (2 * q))
    (hschedule :
      r322AnalyticSchedule κ =
        state.processed ++ step :: suffix)
    (hproper : step.1 ≠ r322WholeEndpoint q hq)
    (J : T4 → ℝ)
    (edge : Fin (2 * q - 1))
    (hright :
      step.1.2 <
        r322AnalyticEdgeLeftVertex edge) :
    (state.updateProper κ hκ suffix step
        hschedule hproper J).edges edge =
      state.edges edge := by
  let hbounds :=
    r322AnalyticProperStep_endpoint_bounds
      hq κ hκ state.processed suffix step
      hschedule hproper
  have hstepMem :
      step ∈ r322AnalyticSchedule κ := by
    rw [hschedule]
    simp
  have hstepLt :
      step.1.1 < step.1.2 :=
    extract_mem_fst_lt_snd κ step.1
      (r322AnalyticSchedule_endpoint_mem_extract
        κ hstepMem)
  have hslotNe :
      edge ≠
        r322AnalyticPredecessorEdge
          state step hbounds.1 := by
    intro heq
    have hpreLt :
        r322AnalyticPredecessorVertex
            state step hbounds.1 <
          step.1.1 :=
      r322AnalyticPredecessorVertex_lt_left
        state step hbounds.1
    have hvalEq := congrArg Fin.val heq
    change edge.val =
      (r322AnalyticPredecessorVertex
        state step hbounds.1).val at hvalEq
    change step.1.2.val < edge.val at hright
    omega
  funext u
  unfold R322AnalyticEdgeState.updateProper
  exact
    r322ReplaceEdge_apply_ne
      state.edges
      (r322AnalyticPredecessorEdge
        state step hbounds.1)
      edge hslotNe
      (state.edges
        (r322AnalyticPredecessorEdge
          state step hbounds.1))
      J
      (state.edges
        (r322AnalyticOutgoingEdge step hbounds.2))
      u

end R322AnalyticEdgeState

namespace R322AnalyticAbsorbedState

variable {q : ℕ} {hq : 1 ≤ q}
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}

/-- Every edge whose left vertex is strictly beyond all processed right
endpoints is still the original Green kernel. -/
theorem edge_eq_greenFn_of_processed_right_lt
    {state : R322AnalyticEdgeState q hq}
    (hstate :
      R322AnalyticAbsorbedState ρ lam ε hq κ hκ state)
    (edge : Fin (2 * q - 1))
    (hfuture :
      ∀ earlier ∈ state.processed,
        earlier.1.2 <
          r322AnalyticEdgeLeftVertex edge) :
    state.edges edge = greenFn := by
  induction hstate with
  | initial =>
      rfl
  | update ctx hpairing previous ih =>
      have hcurrent :
          ctx.step.1.2 <
            r322AnalyticEdgeLeftVertex edge := by
        apply hfuture ctx.step
        simp [R322AnalyticProperStepContext.nextState]
      have hprevious :
          ∀ earlier ∈ ctx.state.processed,
            earlier.1.2 <
              r322AnalyticEdgeLeftVertex edge := by
        intro earlier hearlier
        apply hfuture earlier
        simp [R322AnalyticProperStepContext.nextState,
          hearlier]
      rw [R322AnalyticProperStepContext.nextState,
        R322AnalyticEdgeState.updateProper_edges_eq_of_right_lt
          ctx.state ctx.pairing ctx.pairing_mem ctx.suffix
          ctx.step ctx.schedule_eq ctx.proper
          (primitiveKernelDiff ρ lam ε
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder ctx.internalEdges)
          edge hcurrent]
      exact ih hprevious

/-- The outgoing edge of the next proper scheduled block has not yet been
updated, hence is exactly `greenFn`. -/
theorem outgoingEdge_eq_greenFn
    {state : R322AnalyticEdgeState q hq}
    (hstate :
      R322AnalyticAbsorbedState ρ lam ε hq κ hκ state)
    (ctx : R322AnalyticProperStepContext q hq)
    (hpairing : ctx.pairing = κ)
    (hstateEq : ctx.state = state) :
    ctx.state.edges ctx.outgoingEdge = greenFn := by
  subst state
  subst κ
  apply hstate.edge_eq_greenFn_of_processed_right_lt
  intro earlier hearlier
  have hp :=
    r322AnalyticSchedule_pairwise_right_lt ctx.pairing
  rw [ctx.schedule_eq, List.pairwise_append] at hp
  have hright :
      earlier.1.2 < ctx.step.1.2 :=
    hp.2.2 earlier hearlier ctx.step (by simp)
  simpa [R322AnalyticProperStepContext.outgoingEdge,
    r322AnalyticOutgoingEdge,
    r322AnalyticEdgeLeftVertex] using hright

end R322AnalyticAbsorbedState

end

end Anderson4D
