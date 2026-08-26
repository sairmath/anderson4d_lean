import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalPhysicalFubini

/-!
# Slot-zero phase anchors for the incoming R-324 Fourier branch

After the incoming endpoint is Fourier-integrated, its character is
anchored at the sparse successor of production slot zero.  This file records
the exact one-head geometry of that anchor.  A head whose predecessor is not
slot zero leaves the anchor in the post coordinates; a head whose
predecessor is slot zero moves it from the first head coordinate to the
post-collapse successor point.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- Spatial point carrying the incoming Fourier character at a reachable
within-half residual prefix. -/
def incomingPhaseAnchor
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (x y : T4)
    (v : res.SurvivingCoordinate → T4) : T4 :=
  assemble x y (res.reconstruct v) (res.edgeSuccessor 0)

/-- If the current head is fed by slot zero, the pre-collapse phase anchor
is its first standard block coordinate. -/
theorem incomingPhaseAnchor_reconstruct_split_eq_headFirst
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (hpred :
      r324WithinHalfPredecessorSlot res.state head = 0)
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    res.incomingPhaseAnchor x y
        ((res.splitSurvivingPiMeasurableEquiv
          head tail hremaining).symm (t, v)) =
      t ⟨0, by
        have hn :=
          (res.headContext
            head tail hremaining).one_le_blockOrder
        exact Nat.mul_pos (by decide) (Nat.zero_lt_of_lt hn)⟩ := by
  unfold incomingPhaseAnchor
  rw [← hpred,
    res.edgeSuccessor_predecessorSlot
      head tail hremaining]
  let ctx :=
    res.headContext head tail hremaining
  have hleft :
      head.1.1 =
        (ctx.blockOrderIso
          ⟨0, by
            have hn := ctx.one_le_blockOrder
            exact
              Nat.mul_pos
                (by decide) (Nat.zero_lt_of_lt hn)⟩).1 :=
    ctx.blockOrderIso_zero.symm
  rw [hleft, assemble_varIdx]
  exact
    res.reconstruct_split_symm_block
      head tail hremaining t v
      ⟨0, by
        have hn := ctx.one_le_blockOrder
        exact Nat.mul_pos (by decide) (Nat.zero_lt_of_lt hn)⟩

/-- When slot zero is absorbed, its post-collapse phase anchor is exactly
the successor point used by the local primitive kernel. -/
theorem incomingPhaseAnchor_afterHead_eq_headSuccessorPoint
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (hpred :
      r324WithinHalfPredecessorSlot res.state head = 0)
    (x y : T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    (res.afterHead head tail hremaining).incomingPhaseAnchor
        x y v =
      res.headSuccessorPoint
        head tail hremaining x y v := by
  unfold incomingPhaseAnchor
  rw [← hpred]
  exact
    res.assemble_afterHead_edgeSuccessor_predecessor_eq_headSuccessorPoint
      head tail hremaining x y v

/-- Production slot zero is neither an internal slot nor the outgoing slot
of a genuine internal head. -/
private theorem zero_is_outer_for_head
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail) :
    (0 : Fin (m + 1)) ∉
        res.headInternalSlots head tail hremaining ∧
      (0 : Fin (m + 1)) ≠
        (res.headContext head tail hremaining).outgoingSlot := by
  constructor
  · intro hzero
    unfold R324WithinHalfResidualPrefix.headInternalSlots at hzero
    obtain ⟨j, _hj, heq⟩ :=
      Finset.mem_image.mp hzero
    have hpos :
        (0 : Fin (m + 1)) <
          (res.headContext
            head tail hremaining).internalSlot j :=
      lt_of_le_of_lt (Fin.zero_le _)
        (res.predecessorSlot_lt_internalSlot
          head tail hremaining j)
    rw [heq] at hpos
    exact (lt_irrefl 0) hpos
  · exact
      ne_of_lt
        (lt_of_le_of_lt (Fin.zero_le _)
          (res.predecessorSlot_lt_outgoingSlot
            head tail hremaining))

/-- A head not fed by slot zero leaves the incoming phase anchor entirely
in the post-head coordinates. -/
theorem incomingPhaseAnchor_reconstruct_split_eq_afterHead
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (hpred :
      r324WithinHalfPredecessorSlot res.state head ≠ 0)
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    res.incomingPhaseAnchor x y
        ((res.splitSurvivingPiMeasurableEquiv
          head tail hremaining).symm (t, v)) =
      (res.afterHead head tail hremaining).incomingPhaseAnchor
        x y v := by
  have houter :=
    zero_is_outer_for_head res head tail hremaining
  have hsuccessor :=
    res.edgeSuccessor_afterHead_outer
      head tail hremaining
      (0 : Fin (m + 1))
      res.zero_mem_activeEdgeSlots
      hpred.symm houter.1 houter.2
  unfold incomingPhaseAnchor
  rw [← hsuccessor]
  exact
    res.assemble_split_afterHead_edgeSuccessor_eq
      head tail hremaining x y t v 0

end R324WithinHalfResidualPrefix

end

end Anderson4D
