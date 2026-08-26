import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticActiveCarrierGeometry

/-! # Evolving heterogeneous edges for R-322

A proper sparse-carrier step updates the greatest active predecessor slot. -/
set_option warningAsError true
set_option autoImplicit false
namespace Anderson4D
noncomputable section
/-- Bounds for any proper step, not only the first scheduled step. -/
theorem r322AnalyticProperStep_endpoint_bounds
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (pre suffix : List (R322ExtractionStep (2 * q)))
    (step : R322ExtractionStep (2 * q))
    (hschedule : r322AnalyticSchedule κ =
      pre ++ step :: suffix)
    (hproper : step.1 ≠ r322WholeEndpoint q hq) :
    0 < step.1.1.val ∧ step.1.2.val < 2 * q - 1 := by
  have hstepMem :
      step ∈ r322AnalyticSchedule κ := by
    rw [hschedule]
    simp
  have hendpointMem :
      step.1 ∈ extract κ :=
    r322AnalyticSchedule_endpoint_mem_extract
      κ hstepMem
  have hwholeIff :=
    extracted_meets_global_endpoint_iff_whole
      hq (mem_nonSplitPairings.mp hκ)
      step.1 hendpointMem
  have hnotMeet :
      ¬(step.1.1 =
            (⟨0, by omega⟩ :
              Fin (2 * q)) ∨
          step.1.2 =
            (⟨2 * q - 1, by omega⟩ :
              Fin (2 * q))) := by
    intro hmeet
    apply hproper
    have hwhole := hwholeIff.mp hmeet
    simpa only [r322WholeEndpoint] using hwhole
  constructor
  · have hne : step.1.1.val ≠ 0 := by
      intro hzero
      apply hnotMeet
      left
      apply Fin.ext
      exact hzero
    omega
  · have hne :
        step.1.2.val ≠ 2 * q - 1 := by
      intro hlast
      apply hnotMeet
      right
      apply Fin.ext
      exact hlast
    have hlt := step.1.2.isLt
    omega

/-- Processed prefix, heterogeneous edges, and surviving global endpoints. -/
structure R322AnalyticEdgeState (q : ℕ) (hq : 1 ≤ q) where
  processed : List (R322ExtractionStep (2 * q))
  edges : Fin (2 * q - 1) → T4 → ℝ
  zero_mem :
    (⟨0, by omega⟩ : Fin (2 * q)) ∈
      r322AnalyticActiveCarrier processed
  last_mem :
    (⟨2 * q - 1, by omega⟩ : Fin (2 * q)) ∈
      r322AnalyticActiveCarrier processed
/-- The active carrier derived from the processed prefix. -/
def R322AnalyticEdgeState.active
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq) :
    Finset (Fin (2 * q)) :=
  r322AnalyticActiveCarrier state.processed
/-- Initial all-free-Green state. -/
def r322InitialAnalyticEdgeState
    (q : ℕ) (hq : 1 ≤ q) :
    R322AnalyticEdgeState q hq where
  processed := []
  edges := fun _ => greenFn
  zero_mem := by simp
  last_mem := by simp
/-- Active vertices strictly before the next left endpoint. -/
def r322AnalyticPredecessorCandidates
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq)
    (step : R322ExtractionStep (2 * q)) :
    Finset (Fin (2 * q)) :=
  state.active.filter fun i => i < step.1.1
theorem r322AnalyticPredecessorCandidates_nonempty
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq)
    (step : R322ExtractionStep (2 * q))
    (hleft : 0 < step.1.1.val) :
    (r322AnalyticPredecessorCandidates
      state step).Nonempty := by
  let zero : Fin (2 * q) := ⟨0, by omega⟩
  refine ⟨zero, Finset.mem_filter.mpr
    ⟨state.zero_mem, ?_⟩⟩
  change 0 < step.1.1.val
  exact hleft
/-- Greatest active vertex before the next block. -/
def r322AnalyticPredecessorVertex
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq)
    (step : R322ExtractionStep (2 * q))
    (hleft : 0 < step.1.1.val) :
    Fin (2 * q) :=
  (r322AnalyticPredecessorCandidates state step).max'
    (r322AnalyticPredecessorCandidates_nonempty
      state step hleft)
theorem r322AnalyticPredecessorVertex_mem_active
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq)
    (step : R322ExtractionStep (2 * q))
    (hleft : 0 < step.1.1.val) :
    r322AnalyticPredecessorVertex state step hleft ∈
      state.active := by
  have hmem :=
    Finset.max'_mem
      (r322AnalyticPredecessorCandidates state step)
      (r322AnalyticPredecessorCandidates_nonempty
        state step hleft)
  exact (Finset.mem_filter.mp hmem).1
theorem r322AnalyticPredecessorVertex_lt_left
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq)
    (step : R322ExtractionStep (2 * q))
    (hleft : 0 < step.1.1.val) :
    r322AnalyticPredecessorVertex state step hleft <
      step.1.1 := by
  have hmem :=
    Finset.max'_mem
      (r322AnalyticPredecessorCandidates state step)
      (r322AnalyticPredecessorCandidates_nonempty
        state step hleft)
  exact (Finset.mem_filter.mp hmem).2
/-- No active vertex lies strictly between the chosen predecessor and the
left endpoint. -/
theorem r322AnalyticPredecessorVertex_maximal
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq)
    (step : R322ExtractionStep (2 * q))
    (hleft : 0 < step.1.1.val)
    (i : Fin (2 * q)) (hi : i ∈ state.active)
    (hil : i < step.1.1) :
    i ≤ r322AnalyticPredecessorVertex
      state step hleft := by
  change i ≤
    (r322AnalyticPredecessorCandidates
      state step).max' _
  exact Finset.le_max'
    (r322AnalyticPredecessorCandidates state step)
    i (Finset.mem_filter.mpr ⟨hi, hil⟩)
/-- Ambient left-edge slot carried by the sparse predecessor. -/
def r322AnalyticPredecessorEdge
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq)
    (step : R322ExtractionStep (2 * q))
    (hleft : 0 < step.1.1.val) :
    Fin (2 * q - 1) :=
  ⟨(r322AnalyticPredecessorVertex
      state step hleft).val, by
    have hp :=
      r322AnalyticPredecessorVertex_lt_left
        state step hleft
    have hl := step.1.1.isLt
    omega⟩
/-- Regard an ambient edge slot as its left vertex. -/
def r322AnalyticEdgeLeftVertex
    {q : ℕ} (edge : Fin (2 * q - 1)) :
    Fin (2 * q) :=
  ⟨edge.val, by
    have he := edge.isLt
    omega⟩
@[simp]
theorem r322AnalyticEdgeLeftVertex_predecessorEdge
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq)
    (step : R322ExtractionStep (2 * q))
    (hleft : 0 < step.1.1.val) :
    r322AnalyticEdgeLeftVertex
        (r322AnalyticPredecessorEdge
          state step hleft) =
      r322AnalyticPredecessorVertex
        state step hleft := by
  apply Fin.ext
  rfl
/-- The outgoing edge of a proper block is still indexed by its right
endpoint before that endpoint is deleted. -/
def r322AnalyticOutgoingEdge
    {q : ℕ} (step : R322ExtractionStep (2 * q))
    (hright : step.1.2.val < 2 * q - 1) :
    Fin (2 * q - 1) :=
  ⟨step.1.2.val, hright⟩
/-- One proper sparse-carrier update. -/
def R322AnalyticEdgeState.updateProper
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (suffix : List (R322ExtractionStep (2 * q)))
    (step : R322ExtractionStep (2 * q))
    (hschedule :
      r322AnalyticSchedule κ =
        state.processed ++ step :: suffix)
    (hproper :
      step.1 ≠ r322WholeEndpoint q hq)
    (J : T4 → ℝ) :
    R322AnalyticEdgeState q hq :=
  let hbounds :=
    r322AnalyticProperStep_endpoint_bounds
      hq κ hκ state.processed suffix step
      hschedule hproper
  { processed := state.processed ++ [step]
    edges :=
      r322ReplaceEdge state.edges
        (r322AnalyticPredecessorEdge
          state step hbounds.1)
        (state.edges
          (r322AnalyticPredecessorEdge
            state step hbounds.1))
        J
        (state.edges
          (r322AnalyticOutgoingEdge step hbounds.2))
    zero_mem := by
      rw [r322AnalyticActiveCarrier_append_singleton]
      apply Finset.mem_sdiff.mpr
      refine ⟨state.zero_mem, ?_⟩
      intro hzero
      have haligned :=
        r322AnalyticSchedule_forall_aligned κ step
          (by rw [hschedule]; simp)
      have hz := haligned.2.2 _ hzero
      have hzleft := hz.1
      change step.1.1.val ≤ 0 at hzleft
      omega
    last_mem := by
      rw [r322AnalyticActiveCarrier_append_singleton]
      apply Finset.mem_sdiff.mpr
      refine ⟨state.last_mem, ?_⟩
      intro hlast
      have haligned :=
        r322AnalyticSchedule_forall_aligned κ step
          (by rw [hschedule]; simp)
      have hz := haligned.2.2 _ hlast
      have hzright := hz.2
      change 2 * q - 1 ≤ step.1.2.val at hzright
      omega }
@[simp]
theorem R322AnalyticEdgeState.updateProper_processed
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (suffix : List (R322ExtractionStep (2 * q)))
    (step : R322ExtractionStep (2 * q))
    (hschedule :
      r322AnalyticSchedule κ =
        state.processed ++ step :: suffix)
    (hproper : step.1 ≠ r322WholeEndpoint q hq)
    (J : T4 → ℝ) :
    (state.updateProper κ hκ suffix step
      hschedule hproper J).processed =
      state.processed ++ [step] := by
  rfl
theorem R322AnalyticEdgeState.updateProper_active
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (suffix : List (R322ExtractionStep (2 * q)))
    (step : R322ExtractionStep (2 * q))
    (hschedule :
      r322AnalyticSchedule κ =
        state.processed ++ step :: suffix)
    (hproper : step.1 ≠ r322WholeEndpoint q hq)
    (J : T4 → ℝ) :
    (state.updateProper κ hκ suffix step
        hschedule hproper J).active =
      state.active \ step.2 := by
  rw [R322AnalyticEdgeState.active,
    R322AnalyticEdgeState.updateProper_processed,
    r322AnalyticActiveCarrier_append_singleton]
  rfl
end
end Anderson4D
