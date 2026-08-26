import Anderson4D.DetParametrix.Paper42_Moment.R324FirstLeftAnalyticPredecessorLast

/-! # Post-prefix state at the R-324 first-left block

This file combines the genuine analytic-schedule decomposition with the
heterogeneous edge-state iteration.  Its headline concerns the processed
state after integrating the prefix.  It does not identify that state
pointwise with the original unprocessed production integrand.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- If the production predecessor is extracted, the genuine analytic
prefix produces a reachable state in which the selected block reads the
three-kernel collapse stored by the last prefix step. -/
theorem exists_r324FirstLeft_postPrefixState_predecessor_read
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (hextracted :
      r324FirstLeftPredecessorEdge e₀ hleft ∈
        extractedRightEdges e₀.1) :
    ∃ (prior : List (R322ExtractionStep m))
        (step : R322ExtractionStep m)
        (post : List (R322ExtractionStep m))
        (ctx : R324WithinHalfStepContext e₀.1),
      r322AnalyticSchedule e₀.1 =
          (prior ++ [step]) ++
            r324FirstLeftSelectedStep e₀ hleft :: post ∧
        extractedRightEdge step.1 =
          r324FirstLeftPredecessorEdge e₀ hleft ∧
        ctx.state.processed = prior ∧
        ctx.step = step ∧
        ctx.suffix =
          r324FirstLeftSelectedStep e₀ hleft :: post ∧
        R324WithinHalfStateReachable e₀.1 ρ lam ε
          ctx.state ∧
        R324WithinHalfStateReachable e₀.1 ρ lam ε
          (ctx.absorb ρ lam ε) ∧
        (ctx.absorb ρ lam ε).processed =
          prior ++ [step] ∧
        r324WithinHalfPredecessorSlot
            (ctx.absorb ρ lam ε)
            (r324FirstLeftSelectedStep e₀ hleft) =
          r324WithinHalfPredecessorSlot
            ctx.state ctx.step ∧
        (ctx.absorb ρ lam ε).edges
            (r324WithinHalfPredecessorSlot
              (ctx.absorb ρ lam ε)
              (r324FirstLeftSelectedStep e₀ hleft)) =
          ctx.collapsedKernel ρ lam ε := by
  obtain
      ⟨prior, step, post, hschedule, hedge,
        hadjacent⟩ :=
    exists_r324FirstLeft_lastAnalyticPredecessor
      e₀ hleft hextracted
  obtain
      ⟨ctx, hbefore, hprocessed, hstep, hsuffix,
        hafter, hprocessedAfter, hread⟩ :=
    exists_r324WithinHalf_nonemptyPrefix_predecessor_read
      e₀.1 ρ lam ε prior step
      (r324FirstLeftSelectedStep e₀ hleft) post
      hschedule hadjacent
  have hadjacentCtx :
      ctx.step.1.2.val + 1 =
        (r324FirstLeftSelectedStep e₀ hleft).1.1.val := by
    rw [hstep]
    exact hadjacent
  have hslot :
      r324WithinHalfPredecessorSlot
          (ctx.absorb ρ lam ε)
          (r324FirstLeftSelectedStep e₀ hleft) =
        r324WithinHalfPredecessorSlot
          ctx.state ctx.step :=
    ctx.predecessorSlot_absorb_eq_of_adjacent
      (r324FirstLeftSelectedStep e₀ hleft)
      hadjacentCtx ρ lam ε
  exact
    ⟨prior, step, post, ctx, hschedule, hedge,
      hprocessed, hstep, hsuffix, hbefore, hafter,
      hprocessedAfter, hslot, hread⟩

end

end Anderson4D
