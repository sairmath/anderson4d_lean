import Anderson4D.DetParametrix.Paper42_Moment.R324DirectOutgoingBoundaryGeometry

/-!
# Direct incoming boundary geometry for R-324

The incoming external edge is slot zero.  A collapse can overwrite that
slot only when its block has no surviving internal predecessor.  Therefore,
as long as the first internal vertex survives, slot zero is untouched and
still carries the free Green kernel.

This is deliberately only the direct incoming branch.  If the first
internal vertex is removed, the paper integrates the incoming Fourier
variable before the responsible collapse; the completed slot-zero kernel
is then generally not `greenFn`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

namespace R324WithinHalfStateReachable

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- If the first internal vertex is active in a reachable state, the
incoming external edge has never been updated. -/
theorem edge_zero_eq_greenFn_of_first_mem_active
    {state : R324WithinHalfEdgeState m}
    (hstate :
      R324WithinHalfStateReachable pairing ρ lam ε state)
    (hm : 0 < m)
    (hfirst :
      (⟨0, hm⟩ : Fin m) ∈ state.active) :
    state.edges 0 = greenFn := by
  let first : Fin m := ⟨0, hm⟩
  induction hstate with
  | initial =>
      rfl
  | absorb ctx hctx ih =>
      have hfirstPost :
          first ∈ (ctx.absorb ρ lam ε).active := by
        simpa only [first] using hfirst
      have hfirstOld : first ∈ ctx.state.active := by
        rw [ctx.absorb_active] at hfirstPost
        exact (Finset.mem_sdiff.mp hfirstPost).1
      have hfirstNotBlock : first ∉ ctx.step.2 := by
        rw [ctx.absorb_active] at hfirstPost
        exact (Finset.mem_sdiff.mp hfirstPost).2
      have hleftPos : 0 < ctx.step.1.1.val := by
        by_contra hnot
        have hleftZero : ctx.step.1.1 = first := by
          apply Fin.ext
          dsimp only [first]
          omega
        have haligned :=
          r322AnalyticSchedule_forall_aligned
            pairing ctx.step ctx.step_mem_schedule
        exact hfirstNotBlock (hleftZero ▸ haligned.1)
      have hcandidate :
          r324InternalVertexEdgeSlot first ∈
            r324WithinHalfPredecessorCandidates
              ctx.state ctx.step := by
        unfold r324WithinHalfPredecessorCandidates
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨first, ?_, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨hfirstOld, by
            change first.val < ctx.step.1.1.val
            simpa only [first] using hleftPos⟩
      have hle :
          r324InternalVertexEdgeSlot first ≤
            r324WithinHalfPredecessorSlot
              ctx.state ctx.step :=
        Finset.le_max'
          (r324WithinHalfPredecessorCandidates
            ctx.state ctx.step)
          (r324InternalVertexEdgeSlot first)
          hcandidate
      have hzeroNe :
          (0 : Fin (m + 1)) ≠
            r324WithinHalfPredecessorSlot
              ctx.state ctx.step := by
        intro heq
        have hval := Fin.mk_le_mk.mp hle
        have heqVal := congrArg Fin.val heq
        change first.val + 1 ≤
          (r324WithinHalfPredecessorSlot
            ctx.state ctx.step).val at hval
        dsimp only [first] at hval
        change 0 =
          (r324WithinHalfPredecessorSlot
            ctx.state ctx.step).val at heqVal
        omega
      rw [ctx.absorb_edges_of_ne ρ lam ε 0 hzeroNe]
      exact ih hfirstOld

end R324WithinHalfStateReachable

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- Completed-schedule form of the direct incoming boundary theorem. -/
theorem state_edges_zero_eq_greenFn_of_first_mem_finalActive
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hm : 0 < m)
    (hprocessed :
      res.state.processed = r322AnalyticSchedule pairing)
    (hfirst :
      (⟨0, hm⟩ : Fin m) ∈ finalActive pairing) :
    res.state.edges 0 = greenFn := by
  apply res.reachable.edge_zero_eq_greenFn_of_first_mem_active hm
  rw [res.active_eq_finalActive_of_processed_eq_schedule hprocessed]
  exact hfirst

/-- The same conclusion with the direct incoming branch expressed as
non-membership in the union of extracted primitive blocks. -/
theorem state_edges_zero_eq_greenFn_of_first_not_mem_extractionBlocks
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hm : 0 < m)
    (hprocessed :
      res.state.processed = r322AnalyticSchedule pairing)
    (hfirst :
      (⟨0, hm⟩ : Fin m) ∉
        finsetUnionList (extractionBlocks pairing)) :
    res.state.edges 0 = greenFn := by
  apply
    res.state_edges_zero_eq_greenFn_of_first_mem_finalActive
      hm hprocessed
  rw [finalActive_eq_sdiff_extractionBlocks]
  exact Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ _, hfirst⟩

end R324WithinHalfResidualPrefix

end

end Anderson4D
