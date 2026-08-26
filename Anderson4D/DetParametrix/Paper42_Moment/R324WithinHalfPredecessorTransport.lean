import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfEdgeState

/-! # Transport of the R-324 within-half predecessor

After an adjacent analytic prefix block is collapsed, the predecessor of
the next block is the slot updated by that collapse.  The slot is recomputed
from the surviving active carrier; it is not the original production slot.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

theorem r324WithinHalfPredecessorSlot_mem
    {m : ℕ} (state : R324WithinHalfEdgeState m)
    (step : R322ExtractionStep m) :
    r324WithinHalfPredecessorSlot state step ∈
      r324WithinHalfPredecessorCandidates state step :=
  Finset.max'_mem _ _

theorem r324WithinHalfCandidate_le_predecessorSlot
    {m : ℕ} (state : R324WithinHalfEdgeState m)
    (step : R322ExtractionStep m)
    (edge : Fin (m + 1))
    (hedge :
      edge ∈ r324WithinHalfPredecessorCandidates
        state step) :
    edge ≤ r324WithinHalfPredecessorSlot state step :=
  Finset.le_max' _ _ hedge

namespace R324WithinHalfStepContext

variable {m : ℕ} {pairing : PartialPairing (Fin m)}
    (ctx : R324WithinHalfStepContext pairing)

/-- The slot updated by an analytic prefix step is exactly the surviving
predecessor slot of a block beginning immediately after it. -/
theorem predecessorSlot_absorb_eq_of_adjacent
    (selected : R322ExtractionStep m)
    (hadjacent :
      ctx.step.1.2.val + 1 = selected.1.1.val)
    (ρ : SmoothCutoff) (lam ε : ℝ) :
    r324WithinHalfPredecessorSlot
        (ctx.absorb ρ lam ε) selected =
      r324WithinHalfPredecessorSlot
        ctx.state ctx.step := by
  have hblock :
      ctx.step.2 =
        ctx.state.active ∩
          Finset.Icc ctx.step.1.1 ctx.step.1.2 := by
    simpa [R324WithinHalfEdgeState.active] using
      r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
        pairing ctx.state.processed ctx.suffix ctx.step
        ctx.schedule_eq
  have holdMem :=
    r324WithinHalfPredecessorSlot_mem
      ctx.state ctx.step
  have holdNew :
      r324WithinHalfPredecessorSlot ctx.state ctx.step ∈
        r324WithinHalfPredecessorCandidates
          (ctx.absorb ρ lam ε) selected := by
    rw [r324WithinHalfPredecessorCandidates] at holdMem ⊢
    rcases Finset.mem_union.mp holdMem with
      hzero | himage
    · exact Finset.mem_union.mpr (Or.inl hzero)
    · rcases Finset.mem_image.mp himage with
        ⟨i, hi, hedge⟩
      rcases Finset.mem_filter.mp hi with
        ⟨hiActive, hiLeft⟩
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨?_, ?_⟩, hedge⟩
      · rw [ctx.absorb_active]
        apply Finset.mem_sdiff.mpr
        refine ⟨hiActive, ?_⟩
        intro hiBlock
        rw [hblock] at hiBlock
        have hiBounds :=
          (Finset.mem_inter.mp hiBlock).2
        have hiLower := (Finset.mem_Icc.mp hiBounds).1
        exact (not_lt_of_ge hiLower) hiLeft
      · change i.val < selected.1.1.val
        have haligned :=
          r322AnalyticSchedule_forall_aligned
            pairing ctx.step ctx.step_mem_schedule
        have hleftLeRight :=
          (haligned.2.2 ctx.step.1.1 haligned.1).2
        change i.val < ctx.step.1.1.val at hiLeft
        change ctx.step.1.1.val ≤ ctx.step.1.2.val at hleftLeRight
        omega
  apply le_antisymm
  · have hnewMem :=
      r324WithinHalfPredecessorSlot_mem
        (ctx.absorb ρ lam ε) selected
    rw [r324WithinHalfPredecessorCandidates] at hnewMem
    rcases Finset.mem_union.mp hnewMem with
      hzero | himage
    · have hz :
          r324WithinHalfPredecessorSlot
              (ctx.absorb ρ lam ε) selected = 0 := by
          simpa using hzero
      rw [hz]
      exact Fin.zero_le _
    · rcases Finset.mem_image.mp himage with
        ⟨i, hi, hedge⟩
      rcases Finset.mem_filter.mp hi with
        ⟨hiActive, hiSelected⟩
      have hiDiff :
          i ∈ ctx.state.active \ ctx.step.2 := by
        simpa only [ctx.absorb_active] using hiActive
      have hiLeft : i < ctx.step.1.1 := by
        by_contra hnot
        have hleftLe : ctx.step.1.1 ≤ i :=
          le_of_not_gt hnot
        have hiRight : i ≤ ctx.step.1.2 := by
          change i.val ≤ ctx.step.1.2.val
          change i.val < selected.1.1.val at hiSelected
          omega
        have hiBlock : i ∈ ctx.step.2 := by
          rw [hblock]
          exact Finset.mem_inter.mpr
            ⟨(Finset.mem_sdiff.mp hiDiff).1,
              Finset.mem_Icc.mpr ⟨hleftLe, hiRight⟩⟩
        exact (Finset.mem_sdiff.mp hiDiff).2 hiBlock
      rw [← hedge]
      apply r324WithinHalfCandidate_le_predecessorSlot
      rw [r324WithinHalfPredecessorCandidates]
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr
          ⟨(Finset.mem_sdiff.mp hiDiff).1, hiLeft⟩, rfl⟩
  · exact r324WithinHalfCandidate_le_predecessorSlot
      (ctx.absorb ρ lam ε) selected _ holdNew

end R324WithinHalfStepContext

/-- Every genuine prefix of the analytic schedule generates a reachable
heterogeneous state.  This is an induction on the prefix itself, rather
than an arbitrary sequence of certified blocks. -/
theorem exists_r324WithinHalfState_of_schedule_prefix
    {m : ℕ} (pairing : PartialPairing (Fin m))
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (pre suffix : List (R322ExtractionStep m))
    (hschedule :
      r322AnalyticSchedule pairing = pre ++ suffix) :
    ∃ state : R324WithinHalfEdgeState m,
      R324WithinHalfStateReachable pairing ρ lam ε state ∧
        state.processed = pre := by
  induction pre using List.reverseRecOn generalizing suffix with
  | nil =>
      refine ⟨r324InitialWithinHalfEdgeState m,
        R324WithinHalfStateReachable.initial, rfl⟩
  | append_singleton pre step ih =>
      have hprefix :
          r322AnalyticSchedule pairing =
            pre ++ step :: suffix := by
        simpa [List.append_assoc] using hschedule
      obtain ⟨state, hstate, hprocessed⟩ :=
        ih (step :: suffix) hprefix
      let ctx : R324WithinHalfStepContext pairing :=
        { state := state
          step := step
          suffix := suffix
          schedule_eq := by
            rw [hprocessed]
            exact hprefix }
      refine ⟨ctx.absorb ρ lam ε,
        R324WithinHalfStateReachable.absorb ctx hstate, ?_⟩
      simp [R324WithinHalfStepContext.absorb, ctx,
        hprocessed]

/-- For a nonempty analytic prefix whose last block is adjacent to the
selected block, the selected predecessor reads the edge produced by the
last genuine collapse. -/
theorem exists_r324WithinHalf_nonemptyPrefix_predecessor_read
    {m : ℕ} (pairing : PartialPairing (Fin m))
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (prior : List (R322ExtractionStep m))
    (prefixStep selected : R322ExtractionStep m)
    (suffix : List (R322ExtractionStep m))
    (hschedule :
      r322AnalyticSchedule pairing =
        (prior ++ [prefixStep]) ++ selected :: suffix)
    (hadjacent :
      prefixStep.1.2.val + 1 = selected.1.1.val) :
    ∃ ctx : R324WithinHalfStepContext pairing,
      R324WithinHalfStateReachable pairing ρ lam ε ctx.state ∧
        ctx.state.processed = prior ∧
        ctx.step = prefixStep ∧
        ctx.suffix = selected :: suffix ∧
        R324WithinHalfStateReachable pairing ρ lam ε
          (ctx.absorb ρ lam ε) ∧
        (ctx.absorb ρ lam ε).processed =
          prior ++ [prefixStep] ∧
        (ctx.absorb ρ lam ε).edges
            (r324WithinHalfPredecessorSlot
              (ctx.absorb ρ lam ε) selected) =
          ctx.collapsedKernel ρ lam ε := by
  have hprior :
      r322AnalyticSchedule pairing =
        prior ++ prefixStep :: selected :: suffix := by
    simpa [List.append_assoc] using hschedule
  obtain ⟨state, hstate, hprocessed⟩ :=
    exists_r324WithinHalfState_of_schedule_prefix
      pairing ρ lam ε prior
        (prefixStep :: selected :: suffix)
      hprior
  let ctx : R324WithinHalfStepContext pairing :=
    { state := state
      step := prefixStep
      suffix := selected :: suffix
      schedule_eq := by
        rw [hprocessed]
        exact hprior }
  refine ⟨ctx, hstate, hprocessed, rfl, rfl,
    R324WithinHalfStateReachable.absorb ctx hstate, ?_, ?_⟩
  · simp [R324WithinHalfStepContext.absorb, ctx,
      hprocessed]
  · rw [ctx.predecessorSlot_absorb_eq_of_adjacent
      selected hadjacent]
    exact ctx.absorb_edges_predecessor ρ lam ε

end

end Anderson4D
