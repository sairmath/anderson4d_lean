import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointIntegratedResidualBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324DirectOutgoingBoundaryGeometry

/-!
# Fourier coefficients of direct terminal boundary legs

This file identifies a completed sparse half-chain boundary leg with one
translated Green kernel whenever its reachable edge state still stores the
free Green function at that boundary slot.  The result is exact and precedes
all norm estimates.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- The first surviving internal point of a nonempty completed half-chain,
written without choosing a new finite index. -/
def terminalIncomingAnchor
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (v : Fin m → T4) : T4 :=
  assemble 0 0 v (res.edgeSuccessor 0)

/-- The last surviving internal point of a nonempty completed half-chain. -/
def terminalOutgoingAnchor
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    (v : Fin m → T4) : T4 :=
  assemble 0 0 v
    (res.terminalOutgoingEdgeSlot hactive).castSucc

/-- With a nonempty active carrier, the successor of the incoming edge is
an internal vertex rather than the external right endpoint. -/
theorem edgeSuccessor_zero_ne_last_of_active
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty) :
    res.edgeSuccessor 0 ≠ Fin.last (m + 1) := by
  have hmaxCandidate :
      varIdx (res.state.active.max' hactive) ∈
        res.edgeSuccessorCandidates 0 := by
    rw [edgeSuccessorCandidates]
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine
      ⟨res.state.active.max' hactive,
        Finset.mem_filter.mpr
          ⟨Finset.max'_mem res.state.active hactive, ?_⟩,
        rfl⟩
    simp only [Fin.val_zero, varIdx_val]
    omega
  have hle :
      res.edgeSuccessor 0 ≤
        varIdx (res.state.active.max' hactive) := by
    unfold edgeSuccessor
    exact Finset.min'_le _ _ hmaxCandidate
  have hlt :
      varIdx (res.state.active.max' hactive) <
        Fin.last (m + 1) := by
    change
      (res.state.active.max' hactive).val + 1 < m + 1
    exact Nat.add_lt_add_right
      (res.state.active.max' hactive).isLt 1
  exact ne_of_lt (hle.trans_lt hlt)

/-- The incoming successor coordinate is independent of both external
endpoints whenever the completed half-chain is nonempty. -/
theorem assemble_edgeSuccessor_zero_eq_terminalIncomingAnchor
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    (x y : T4) (v : Fin m → T4) :
    assemble x y v (res.edgeSuccessor 0) =
      res.terminalIncomingAnchor v := by
  unfold terminalIncomingAnchor assemble
  have hpos :
      (res.edgeSuccessor 0).val ≠ 0 := by
    have hlt := res.edge_lt_edgeSuccessor 0
    intro hzero
    change (0 : ℕ) < (res.edgeSuccessor 0).val at hlt
    omega
  have hlast :
      (res.edgeSuccessor 0).val ≠ m + 1 := by
    intro hval
    apply res.edgeSuccessor_zero_ne_last_of_active hactive
    apply Fin.ext
    simpa using hval
  rw [dif_neg hpos, dif_neg hlast, dif_neg hpos, dif_neg hlast]

/-- The maximal active slot has no surviving internal successor. -/
theorem edgeSuccessor_terminalOutgoingEdgeSlot_eq_last
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty) :
    res.edgeSuccessor (res.terminalOutgoingEdgeSlot hactive) =
      Fin.last (m + 1) := by
  have hmem :=
    res.edgeSuccessor_mem_candidates
      (res.terminalOutgoingEdgeSlot hactive)
  rw [edgeSuccessorCandidates] at hmem
  rcases Finset.mem_union.mp hmem with hlast | hinter
  · simpa only [Finset.mem_singleton] using hlast
  · obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hinter
    have hgt := (Finset.mem_filter.mp hi).2
    have hmax :=
      Finset.le_max' res.state.active i
        (Finset.mem_filter.mp hi).1
    unfold terminalOutgoingEdgeSlot at hgt
    change
      (res.state.active.max' hactive).val + 1 <
        i.val + 1 at hgt
    omega

/-- The source coordinate of the outgoing terminal slot is independent of
both external endpoints. -/
theorem assemble_terminalOutgoing_castSucc_eq_terminalOutgoingAnchor
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    (x y : T4) (v : Fin m → T4) :
    assemble x y v
        (res.terminalOutgoingEdgeSlot hactive).castSucc =
      res.terminalOutgoingAnchor hactive v := by
  have hslot :
      (res.terminalOutgoingEdgeSlot hactive).castSucc =
        varIdx (res.state.active.max' hactive) := by
    apply Fin.ext
    rfl
  unfold terminalOutgoingAnchor
  rw [hslot, assemble_varIdx, assemble_varIdx]

/-- Exact direct incoming-boundary kernel identity. -/
theorem incomingBoundaryFactor_eq_incomingEndpointKernel
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hremaining : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (hedge : res.state.edges 0 = greenFn)
    (x y : T4) (v : Fin m → T4) :
    (res.incomingBoundaryFactor x y v : ℂ) =
      r324IncomingEndpointKernel
        (res.terminalIncomingAnchor v)
        (res.terminalIncomingAnchor v) false x := by
  unfold incomingBoundaryFactor residualChainEdgeFactor
  rw [if_pos res.zero_mem_activeEdgeSlots]
  have hnotReserved :
      (0 : Fin (m + 1)) ∉ res.remainingOutgoingSlots := by
    unfold remainingOutgoingSlots
    rw [hremaining]
    simp
  rw [if_neg hnotReserved, hedge]
  unfold edgeDisplacement r324IncomingEndpointKernel
  have hzeroCast :
      (0 : Fin (m + 1)).castSucc =
        (0 : Fin (m + 2)) := by
    rfl
  rw [hzeroCast, assemble_zero,
    res.assemble_edgeSuccessor_zero_eq_terminalIncomingAnchor
      hactive]
  simp

/-- Exact direct outgoing-boundary kernel identity. -/
theorem outgoingBoundaryFactor_eq_outgoingEndpointKernel
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hremaining : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (hedge :
      res.state.edges
          (res.terminalOutgoingEdgeSlot hactive) =
        greenFn)
    (x y : T4) (v : Fin m → T4) :
    (res.outgoingBoundaryFactor hactive x y v : ℂ) =
      r324OutgoingEndpointKernel
        (res.terminalOutgoingAnchor hactive v)
        (res.terminalOutgoingAnchor hactive v) false y := by
  unfold outgoingBoundaryFactor residualChainEdgeFactor
  rw [if_pos
    (res.terminalOutgoingEdgeSlot_mem_activeEdgeSlots hactive)]
  have hnotReserved :
      res.terminalOutgoingEdgeSlot hactive ∉
        res.remainingOutgoingSlots := by
    unfold remainingOutgoingSlots
    rw [hremaining]
    simp
  rw [if_neg hnotReserved, hedge]
  unfold edgeDisplacement r324OutgoingEndpointKernel
  rw [
    res.assemble_terminalOutgoing_castSucc_eq_terminalOutgoingAnchor
      hactive,
    res.edgeSuccessor_terminalOutgoingEdgeSlot_eq_last hactive,
    assemble_last]
  simp

/-- Fourier coefficient of a direct incoming terminal leg. -/
theorem integral_char_mul_incomingBoundaryFactor_eq
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hremaining : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (hedge : res.state.edges 0 = greenFn)
    (k : Z4) (y : T4) (v : Fin m → T4) :
    (∫ x : T4,
        charT4 k x *
          (res.incomingBoundaryFactor x y v : ℂ)
        ∂paperMeasure) =
      translatedGreenMode k
        (res.terminalIncomingAnchor v) := by
  simp_rw [
    res.incomingBoundaryFactor_eq_incomingEndpointKernel
      hremaining hactive hedge]
  rw [integral_char_mul_r324IncomingEndpointKernel]
  simp [r324EndpointCoefficient]

/-- Fourier coefficient of a direct outgoing terminal leg. -/
theorem integral_char_mul_outgoingBoundaryFactor_eq
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hremaining : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (hedge :
      res.state.edges
          (res.terminalOutgoingEdgeSlot hactive) =
        greenFn)
    (k : Z4) (x : T4) (v : Fin m → T4) :
    (∫ y : T4,
        charT4 k y *
          (res.outgoingBoundaryFactor hactive x y v : ℂ)
        ∂paperMeasure) =
      translatedGreenMode k
        (res.terminalOutgoingAnchor hactive v) := by
  simp_rw [
    res.outgoingBoundaryFactor_eq_outgoingEndpointKernel
      hremaining hactive hedge]
  rw [integral_char_mul_r324OutgoingEndpointKernel]
  simp [r324EndpointCoefficient]

/-- Consumer-facing direct-branch coefficient: schedule completion and
non-extraction of the last edge discharge the raw-Green premise. -/
theorem integral_char_mul_outgoingBoundaryFactor_eq_of_directOutgoing
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hremaining : res.remaining = [])
    (hm : 0 < m)
    (hprocessed :
      res.state.processed = r322AnalyticSchedule pairing)
    (hdirect : Fin.last m ∉ extractedRightEdges pairing)
    (hactive : res.state.active.Nonempty)
    (k : Z4) (x : T4) (v : Fin m → T4) :
    (∫ y : T4,
        charT4 k y *
          (res.outgoingBoundaryFactor hactive x y v : ℂ)
        ∂paperMeasure) =
      translatedGreenMode k
        (res.terminalOutgoingAnchor hactive v) := by
  exact
    res.integral_char_mul_outgoingBoundaryFactor_eq
      hremaining hactive
      (res.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_directOutgoing
        hm hprocessed hdirect hactive)
      k x v

/-- Boolean spelling of the preceding direct-branch coefficient. -/
theorem integral_char_mul_outgoingBoundaryFactor_eq_of_not_shortcut
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hremaining : res.remaining = [])
    (hm : 0 < m)
    (hprocessed :
      res.state.processed = r322AnalyticSchedule pairing)
    (hdirect : r324OutgoingIsShortcut pairing = false)
    (hactive : res.state.active.Nonempty)
    (k : Z4) (x : T4) (v : Fin m → T4) :
    (∫ y : T4,
        charT4 k y *
          (res.outgoingBoundaryFactor hactive x y v : ℂ)
        ∂paperMeasure) =
      translatedGreenMode k
        (res.terminalOutgoingAnchor hactive v) := by
  exact
    res.integral_char_mul_outgoingBoundaryFactor_eq
      hremaining hactive
      (res.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_not_shortcut
        hm hprocessed hdirect hactive)
      k x v

end R324WithinHalfResidualPrefix

end

end Anderson4D
