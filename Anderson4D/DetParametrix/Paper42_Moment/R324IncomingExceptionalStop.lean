import Anderson4D.DetParametrix.Paper42_Moment.R324DirectIncomingBoundaryGeometry
import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfPredecessorTransport

/-!
# The genuine stop before an exceptional incoming-boundary collapse

If the first internal vertex does not survive the complete within-half
schedule, one actual analytic step removes it.  This file constructs the
reachable heterogeneous state immediately before that step and proves the
two structural facts needed by the paper's endpoint-first Fourier argument:

* the step begins at internal vertex zero, so its predecessor slot is the
  incoming external slot; and
* before the step, that slot still carries the free Green kernel.

No block integration or endpoint Fubini exchange is performed here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

/-- A genuine reachable state stopped immediately before an analytic block
whose left endpoint is the first internal vertex. -/
structure R324IncomingExceptionalStop
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (κ : PartialPairing (Fin m)) where
  ctx : R324WithinHalfStepContext κ
  reachable :
    R324WithinHalfStateReachable κ ρ lam ε ctx.state
  left_eq_zero :
    ctx.step.1.1.val = 0

namespace R324IncomingExceptionalStop

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κ : PartialPairing (Fin m)}
    (stop : R324IncomingExceptionalStop ρ lam ε κ)

/-- The first internal vertex belongs to the block waiting at the stop. -/
theorem first_mem_step_block
    (hm : 0 < m) :
    (⟨0, hm⟩ : Fin m) ∈ stop.ctx.step.2 := by
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      κ stop.ctx.step stop.ctx.step_mem_schedule
  have hleft :
      stop.ctx.step.1.1 = (⟨0, hm⟩ : Fin m) := by
    apply Fin.ext
    exact stop.left_eq_zero
  exact hleft ▸ haligned.1

/-- A step beginning at the first internal vertex has the incoming external
slot as its sparse predecessor. -/
theorem predecessorSlot_eq_zero :
    r324WithinHalfPredecessorSlot
        stop.ctx.state stop.ctx.step =
      0 := by
  apply Fin.ext
  have hle :=
    r324WithinHalfPredecessorSlot_val_le_step_left
      stop.ctx.state stop.ctx.step
  have hleft := stop.left_eq_zero
  change
    (r324WithinHalfPredecessorSlot
      stop.ctx.state stop.ctx.step).val = 0
  omega

/-- The first internal vertex is active immediately before the exceptional
step. -/
theorem first_mem_state_active
    (hm : 0 < m) :
    (⟨0, hm⟩ : Fin m) ∈ stop.ctx.state.active := by
  have hblock :
      stop.ctx.step.2 =
        r322AnalyticActiveCarrier stop.ctx.state.processed ∩
          Finset.Icc stop.ctx.step.1.1 stop.ctx.step.1.2 := by
    exact
      r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
        κ stop.ctx.state.processed stop.ctx.suffix
        stop.ctx.step stop.ctx.schedule_eq
  have hfirst := stop.first_mem_step_block hm
  rw [hblock] at hfirst
  exact (Finset.mem_inter.mp hfirst).1

/-- Before the exceptional step is absorbed, its incoming predecessor is
still the untouched free Green edge. -/
theorem state_edge_zero_eq_greenFn
    (hm : 0 < m) :
    stop.ctx.state.edges 0 = greenFn := by
  exact
    stop.reachable.edge_zero_eq_greenFn_of_first_mem_active
      hm (stop.first_mem_state_active hm)

/-- The named predecessor edge used by the stopped step is literally the
free Green function. -/
theorem state_edge_predecessor_eq_greenFn
    (hm : 0 < m) :
    stop.ctx.state.edges
        (r324WithinHalfPredecessorSlot
          stop.ctx.state stop.ctx.step) =
      greenFn := by
  rw [stop.predecessorSlot_eq_zero]
  exact stop.state_edge_zero_eq_greenFn hm

end R324IncomingExceptionalStop

/-- If the first internal vertex is removed by the full analytic schedule,
there is a genuine reachable pre-step state of the preceding form. -/
theorem exists_r324IncomingExceptionalStop
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hm : 0 < m)
    (hremoved :
      (⟨0, hm⟩ : Fin m) ∉ finalActive κ) :
    Nonempty (R324IncomingExceptionalStop ρ lam ε κ) := by
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
  obtain ⟨step, hstep, hstepBlock⟩ :=
    List.mem_map.mp hBschedule
  have hfirstStep : first ∈ step.2 := by
    rw [hstepBlock]
    exact hfirstB
  have haligned :=
    r322AnalyticSchedule_forall_aligned κ step hstep
  have hleftZero : step.1.1.val = 0 := by
    have hle := (haligned.2.2 first hfirstStep).1
    change step.1.1.val ≤ first.val at hle
    dsimp only [first] at hle
    omega
  obtain ⟨pre, suffix, hschedule⟩ :=
    List.mem_iff_append.mp hstep
  obtain ⟨state, hstate, hprocessed⟩ :=
    exists_r324WithinHalfState_of_schedule_prefix
      κ ρ lam ε pre (step :: suffix) hschedule
  let ctx : R324WithinHalfStepContext κ :=
    {
      state := state
      step := step
      suffix := suffix
      schedule_eq := by
        rw [hprocessed]
        exact hschedule
    }
  exact
    ⟨{
      ctx := ctx
      reachable := hstate
      left_eq_zero := hleftZero
    }⟩

end

end Anderson4D
