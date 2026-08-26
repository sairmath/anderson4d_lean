import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointErasedPhaseABoundary

/-!
# Endpoint independence after the R-324 Phase-A boundary split

After the incoming and outgoing slots of a completed within-half chain
have been erased, both endpoints of every remaining production edge are
internal variables.  This file records that statement at the literal
sparse-chain level and deduces endpoint independence of the signed
interior product.

For the two terminal half states, the two endpoint-erased products are
then packaged as one signed, endpoint-free core.  The product of the two
full terminal chains is exactly the four external boundary factors times
that core.  No absolute value is taken and no nested-cross reduction is
started here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- An endpoint-erased slot is still an active production-chain slot. -/
theorem mem_activeEdgeSlots_of_mem_endpointErased
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    {edge : Fin (m + 1)}
    (hedge :
      edge ∈ res.endpointErasedActiveEdgeSlots hactive) :
    edge ∈ res.activeEdgeSlots :=
  (Finset.mem_erase.mp
    (Finset.mem_erase.mp hedge).2).2

/-- An endpoint-erased slot is not the incoming external slot. -/
theorem ne_zero_of_mem_endpointErased
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    {edge : Fin (m + 1)}
    (hedge :
      edge ∈ res.endpointErasedActiveEdgeSlots hactive) :
    edge ≠ 0 :=
  (Finset.mem_erase.mp
    (Finset.mem_erase.mp hedge).2).1

/-- An endpoint-erased slot is not the outgoing external slot. -/
theorem ne_terminalOutgoingEdgeSlot_of_mem_endpointErased
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    {edge : Fin (m + 1)}
    (hedge :
      edge ∈ res.endpointErasedActiveEdgeSlots hactive) :
    edge ≠ res.terminalOutgoingEdgeSlot hactive :=
  (Finset.mem_erase.mp hedge).1

/-- The source of every endpoint-erased edge is an internal assembled
coordinate. -/
theorem exists_sourceInternalIndex_of_mem_endpointErased
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    {edge : Fin (m + 1)}
    (hedge :
      edge ∈ res.endpointErasedActiveEdgeSlots hactive) :
    ∃ i : Fin m, edge.castSucc = varIdx i := by
  have hedgeZero :
      edge ≠ 0 :=
    res.ne_zero_of_mem_endpointErased hactive hedge
  have hedgeValPos : 0 < edge.val := by
    by_contra hnot
    have hedgeVal : edge.val = 0 :=
      Nat.eq_zero_of_not_pos hnot
    apply hedgeZero
    apply Fin.ext
    exact hedgeVal
  refine
    ⟨⟨edge.val - 1, by
        have hedgeLt := edge.isLt
        omega⟩, ?_⟩
  apply Fin.ext
  change edge.val = (edge.val - 1) + 1
  omega

/-- The target of every endpoint-erased edge is an internal assembled
coordinate.  Removing the maximal active slot is exactly what rules out
the terminal external vertex as the sparse successor. -/
theorem exists_targetInternalIndex_of_mem_endpointErased
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    {edge : Fin (m + 1)}
    (hedge :
      edge ∈ res.endpointErasedActiveEdgeSlots hactive) :
    ∃ i : Fin m, res.edgeSuccessor edge = varIdx i := by
  have hedgeZero :
      edge ≠ 0 :=
    res.ne_zero_of_mem_endpointErased hactive hedge
  have hedgeTerminal :
      edge ≠ res.terminalOutgoingEdgeSlot hactive :=
    res.ne_terminalOutgoingEdgeSlot_of_mem_endpointErased
      hactive hedge
  have hedgeActive :
      edge ∈ res.activeEdgeSlots :=
    res.mem_activeEdgeSlots_of_mem_endpointErased
      hactive hedge
  rw [activeEdgeSlots] at hedgeActive
  rcases Finset.mem_union.mp hedgeActive with
    hedgeIncoming | hedgeInternal
  · have hedgeEq : edge = 0 := by
      simpa only [Finset.mem_singleton] using hedgeIncoming
    exact (hedgeZero hedgeEq).elim
  · obtain ⟨i, hiActive, hiEdge⟩ :=
      Finset.mem_image.mp hedgeInternal
    have hiNeMax :
        i ≠ res.state.active.max' hactive := by
      intro hiMax
      apply hedgeTerminal
      simpa [terminalOutgoingEdgeSlot, hiMax] using hiEdge.symm
    have hiLtMax :
        i < res.state.active.max' hactive :=
      lt_of_le_of_ne
        (Finset.le_max' res.state.active i hiActive)
        hiNeMax
    have hmaxCandidate :
        varIdx (res.state.active.max' hactive) ∈
          res.edgeSuccessorCandidates edge := by
      rw [edgeSuccessorCandidates]
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine
        ⟨res.state.active.max' hactive,
          Finset.mem_filter.mpr
            ⟨Finset.max'_mem res.state.active hactive, ?_⟩,
          rfl⟩
      rw [← hiEdge]
      simp only [r324InternalVertexEdgeSlot, varIdx_val]
      exact Nat.add_lt_add_right hiLtMax 1
    have hsuccessorLe :
        res.edgeSuccessor edge ≤
          varIdx (res.state.active.max' hactive) := by
      unfold edgeSuccessor
      exact
        Finset.min'_le
          (res.edgeSuccessorCandidates edge)
          (varIdx (res.state.active.max' hactive))
          hmaxCandidate
    have hmaxInternalLtLast :
        varIdx (res.state.active.max' hactive) <
          Fin.last (m + 1) := by
      change
        (res.state.active.max' hactive).val + 1 <
          m + 1
      have hmaxLt :=
        (res.state.active.max' hactive).isLt
      omega
    have hsuccessorLtLast :
        res.edgeSuccessor edge < Fin.last (m + 1) :=
      hsuccessorLe.trans_lt hmaxInternalLtLast
    have hsuccessorMem :=
      res.edgeSuccessor_mem_candidates edge
    rw [edgeSuccessorCandidates] at hsuccessorMem
    rcases Finset.mem_union.mp hsuccessorMem with
      hterminal | hinternal
    · have hsuccessorNeLast :
          res.edgeSuccessor edge ≠ Fin.last (m + 1) :=
        ne_of_lt hsuccessorLtLast
      exact
        (hsuccessorNeLast
          (by
            simpa only [Finset.mem_singleton] using hterminal)).elim
    · obtain ⟨j, _hjActive, hjSuccessor⟩ :=
        Finset.mem_image.mp hinternal
      exact ⟨j, hjSuccessor.symm⟩

/-- Every endpoint-erased edge reads the same displacement after both
external endpoints are replaced by zero. -/
theorem edgeDisplacement_eq_zeroEndpoints_of_mem_endpointErased
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    (x y : T4) (v : Fin m → T4)
    {edge : Fin (m + 1)}
    (hedge :
      edge ∈ res.endpointErasedActiveEdgeSlots hactive) :
    res.edgeDisplacement x y v edge =
      res.edgeDisplacement 0 0 v edge := by
  obtain ⟨source, hsource⟩ :=
    res.exists_sourceInternalIndex_of_mem_endpointErased
      hactive hedge
  obtain ⟨target, htarget⟩ :=
    res.exists_targetInternalIndex_of_mem_endpointErased
      hactive hedge
  unfold edgeDisplacement
  rw [hsource, htarget]
  simp only [assemble_varIdx]

/-- Each signed chain factor on an endpoint-erased slot is independent of
the two external endpoints. -/
theorem residualChainEdgeFactor_eq_zeroEndpoints_of_mem_endpointErased
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    (x y : T4) (v : Fin m → T4)
    {edge : Fin (m + 1)}
    (hedge :
      edge ∈ res.endpointErasedActiveEdgeSlots hactive) :
    res.residualChainEdgeFactor x y v edge =
      res.residualChainEdgeFactor 0 0 v edge := by
  have hedgeActive :
      edge ∈ res.activeEdgeSlots :=
    res.mem_activeEdgeSlots_of_mem_endpointErased
      hactive hedge
  have hdisplacement :
      res.edgeDisplacement x y v edge =
        res.edgeDisplacement 0 0 v edge :=
    res.edgeDisplacement_eq_zeroEndpoints_of_mem_endpointErased
      hactive x y v hedge
  unfold residualChainEdgeFactor
  rw [if_pos hedgeActive, if_pos hedgeActive]
  by_cases hreserved :
      edge ∈ res.remainingOutgoingSlots
  · rw [if_pos hreserved, if_pos hreserved]
  · rw [if_neg hreserved, if_neg hreserved, hdisplacement]

/-- The complete signed endpoint-erased chain is independent of its two
external endpoint arguments. -/
theorem endpointErasedSignedChain_eq_zeroEndpoints
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    (x y : T4) (v : Fin m → T4) :
    res.endpointErasedSignedChain hactive x y v =
      res.endpointErasedSignedChain hactive 0 0 v := by
  unfold endpointErasedSignedChain
  apply Finset.prod_congr rfl
  intro edge hedge
  exact
    res.residualChainEdgeFactor_eq_zeroEndpoints_of_mem_endpointErased
      hactive x y v hedge

/-- Endpoint-erased chains agree for any two choices of external
endpoints. -/
theorem endpointErasedSignedChain_eq_of_endpoints
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    (x y x' y' : T4) (v : Fin m → T4) :
    res.endpointErasedSignedChain hactive x y v =
      res.endpointErasedSignedChain hactive x' y' v :=
  (res.endpointErasedSignedChain_eq_zeroEndpoints
    hactive x y v).trans
    (res.endpointErasedSignedChain_eq_zeroEndpoints
      hactive x' y' v).symm

end R324WithinHalfResidualPrefix

/-! ## The endpoint-free signed core of two terminal half states -/

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal :
      R324TwoHalfTerminalData ρ lam ε κp κm)

/-- The selected left single witnesses that the left certified terminal
half still has an active internal vertex. -/
theorem left_active_nonempty_of_selected
    (selected : R324ResidualCovarianceSlot κp) :
    terminal.left.state.active.Nonempty := by
  refine ⟨selected.1, ?_⟩
  rw [
    terminal.left.active_eq_finalActive_of_processed_eq_schedule
      terminal.left_processed]
  exact singles_subset_finalActive κp selected.2

/-- The matched right single witnesses that the right certified terminal
half still has an active internal vertex. -/
theorem right_active_nonempty_of_selected
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    terminal.right.state.active.Nonempty := by
  refine ⟨(π selected).1, ?_⟩
  rw [
    terminal.right.active_eq_finalActive_of_processed_eq_schedule
      terminal.right_processed]
  exact singles_subset_finalActive κm (π selected).2

/-- Product of the two signed terminal half-chain interiors, evaluated
with all four external endpoints erased.  In the certified route,
`terminal` is `ofCertifiedTraces leftTrace rightTrace`. -/
def endpointErasedSignedTerminalCore
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (vl : terminal.left.SurvivingCoordinate → T4)
    (vr : terminal.right.SurvivingCoordinate → T4) : ℝ :=
  terminal.left.endpointErasedSignedChain
      (terminal.left_active_nonempty_of_selected selected)
      0 0 (terminal.left.reconstruct vl) *
    terminal.right.endpointErasedSignedChain
      (terminal.right_active_nonempty_of_selected π selected)
      0 0 (terminal.right.reconstruct vr)

/-- Exact signed two-half terminal decomposition: the two full production
chains are the four external boundary factors times one endpoint-free
interior core. -/
theorem terminalChainProducts_eq_fourBoundary_mul_endpointErasedCore
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (x y z w : T4)
    (vl : terminal.left.SurvivingCoordinate → T4)
    (vr : terminal.right.SurvivingCoordinate → T4) :
    terminal.left.residualChainProduct
          x y (terminal.left.reconstruct vl) *
        terminal.right.residualChainProduct
          z w (terminal.right.reconstruct vr) =
      terminal.left.incomingBoundaryFactor
          x y (terminal.left.reconstruct vl) *
        terminal.left.outgoingBoundaryFactor
          (terminal.left_active_nonempty_of_selected selected)
          x y (terminal.left.reconstruct vl) *
        terminal.right.incomingBoundaryFactor
          z w (terminal.right.reconstruct vr) *
        terminal.right.outgoingBoundaryFactor
          (terminal.right_active_nonempty_of_selected π selected)
          z w (terminal.right.reconstruct vr) *
        terminal.endpointErasedSignedTerminalCore
          π selected vl vr := by
  rw [
    terminal.left.residualChainProduct_eq_boundary_mul_endpointErased
      (terminal.left_active_nonempty_of_selected selected),
    terminal.right.residualChainProduct_eq_boundary_mul_endpointErased
      (terminal.right_active_nonempty_of_selected π selected),
    terminal.left.endpointErasedSignedChain_eq_zeroEndpoints
      (terminal.left_active_nonempty_of_selected selected),
    terminal.right.endpointErasedSignedChain_eq_zeroEndpoints
      (terminal.right_active_nonempty_of_selected π selected)]
  unfold endpointErasedSignedTerminalCore
  ring

end R324TwoHalfTerminalData

end

end Anderson4D
