import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointErasedPhaseABoundary
import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointFiberClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfQuantitativeStep

/-!
# Direct outgoing boundary geometry for R-324

In the direct endpoint branch, the final internal vertex is not removed by
the within-half extraction schedule.  Thus it is the greatest terminal active
vertex, so its outgoing slot is the external slot `Fin.last m`.  Reachability
also shows that this external slot is never updated by an analytic collapse.
Consequently the completed outgoing boundary edge is exactly `greenFn`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

namespace R324WithinHalfStateReachable

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- The external outgoing slot lies strictly to the right of every analytic
step and therefore remains the free Green edge in every reachable state. -/
theorem edge_finLast_eq_greenFn
    {state : R324WithinHalfEdgeState m}
    (hstate :
      R324WithinHalfStateReachable pairing ρ lam ε state) :
    state.edges (Fin.last m) = greenFn := by
  apply hstate.edge_eq_greenFn_of_processed_right_lt
  intro earlier _hearlier
  change earlier.1.2.val < m
  exact earlier.1.2.isLt

end R324WithinHalfStateReachable

/-- If the external outgoing edge is not an extracted right edge, the last
internal vertex survives the complete reduction schedule. -/
theorem lastInternal_mem_finalActive_of_finLast_not_mem_extractedRightEdges
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hm : 0 < m)
    (hdirect : Fin.last m ∉ extractedRightEdges κ) :
    (⟨m - 1, by omega⟩ : Fin m) ∈ finalActive κ := by
  let lastInternal : Fin m := ⟨m - 1, by omega⟩
  rw [finalActive_eq_sdiff_extractionBlocks]
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ lastInternal, ?_⟩
  intro hremoved
  obtain ⟨B, hB, hlastB⟩ :=
    (mem_finsetUnionList_iff (extractionBlocks κ)).mp hremoved
  obtain ⟨p, hp, haligned⟩ :=
    exists_extractedPair_aligned_of_mem_extractionBlocks κ hB
  have hlastLe : lastInternal ≤ p.2 :=
    (haligned.2.2 lastInternal hlastB).2
  have hpRight : p.2 = lastInternal := by
    apply Fin.ext
    have hpLt := p.2.isLt
    change m - 1 ≤ p.2.val at hlastLe
    dsimp only [lastInternal]
    omega
  have hedge :
      extractedRightEdge p = Fin.last m := by
    apply Fin.ext
    simp only [extractedRightEdge_val, Fin.val_last]
    have hpLt := p.2.isLt
    have hpRightVal := congrArg Fin.val hpRight
    dsimp only [lastInternal] at hpRightVal
    omega
  apply hdirect
  rw [← hedge]
  exact extractedRightEdge_mem_extractedRightEdges κ p hp

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- In the direct outgoing branch, a completed within-half state has a
nonempty active carrier: the last internal vertex survives. -/
theorem active_nonempty_of_directOutgoing
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hm : 0 < m)
    (hprocessed :
      res.state.processed = r322AnalyticSchedule pairing)
    (hdirect : Fin.last m ∉ extractedRightEdges pairing) :
    res.state.active.Nonempty := by
  let lastInternal : Fin m := ⟨m - 1, by omega⟩
  refine ⟨lastInternal, ?_⟩
  rw [res.active_eq_finalActive_of_processed_eq_schedule hprocessed]
  exact
    lastInternal_mem_finalActive_of_finLast_not_mem_extractedRightEdges
      pairing hm hdirect

/-- In the direct outgoing branch, the terminal boundary slot is the
external final edge slot. -/
theorem terminalOutgoingEdgeSlot_eq_finLast_of_directOutgoing
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hm : 0 < m)
    (hprocessed :
      res.state.processed = r322AnalyticSchedule pairing)
    (hdirect : Fin.last m ∉ extractedRightEdges pairing)
    (hactive : res.state.active.Nonempty) :
    res.terminalOutgoingEdgeSlot hactive = Fin.last m := by
  let lastInternal : Fin m := ⟨m - 1, by omega⟩
  have hlastActive : lastInternal ∈ res.state.active := by
    rw [res.active_eq_finalActive_of_processed_eq_schedule hprocessed]
    exact
      lastInternal_mem_finalActive_of_finLast_not_mem_extractedRightEdges
        pairing hm hdirect
  have hmax :
      res.state.active.max' hactive = lastInternal := by
    apply Fin.ext
    have hle :=
      Finset.le_max' res.state.active lastInternal hlastActive
    have hmaxLt := (res.state.active.max' hactive).isLt
    change m - 1 ≤ (res.state.active.max' hactive).val at hle
    dsimp only [lastInternal]
    omega
  apply Fin.ext
  simp only [terminalOutgoingEdgeSlot, hmax,
    r324InternalVertexEdgeSlot, Fin.val_last]
  dsimp only [lastInternal]
  omega

/-- The completed direct outgoing boundary edge is exactly the free Green
function.  This is the structural input needed by the direct endpoint
Fourier transform. -/
theorem state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_directOutgoing
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hm : 0 < m)
    (hprocessed :
      res.state.processed = r322AnalyticSchedule pairing)
    (hdirect : Fin.last m ∉ extractedRightEdges pairing)
    (hactive : res.state.active.Nonempty) :
    res.state.edges (res.terminalOutgoingEdgeSlot hactive) =
      greenFn := by
  rw [res.terminalOutgoingEdgeSlot_eq_finLast_of_directOutgoing
    hm hprocessed hdirect hactive]
  exact res.reachable.edge_finLast_eq_greenFn

/-- Boolean-flag form of the direct outgoing boundary theorem. -/
theorem state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_not_shortcut
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hm : 0 < m)
    (hprocessed :
      res.state.processed = r322AnalyticSchedule pairing)
    (hdirect : r324OutgoingIsShortcut pairing = false)
    (hactive : res.state.active.Nonempty) :
    res.state.edges (res.terminalOutgoingEdgeSlot hactive) =
      greenFn := by
  apply
    res.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_directOutgoing
      hm hprocessed _ hactive
  simpa [r324OutgoingIsShortcut] using hdirect

end R324WithinHalfResidualPrefix

end

end Anderson4D
