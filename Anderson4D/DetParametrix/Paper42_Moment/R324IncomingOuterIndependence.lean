import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfResidualStep

/-!
# Incoming-endpoint independence at an R-324 head collapse

When the left endpoint of the current analytic head is the first internal
vertex, its sparse predecessor is the incoming external slot.  This file
records the concrete geometry needed to Fourier-integrate that external
variable before the head is absorbed:

* the named predecessor point is the incoming endpoint;
* the outgoing successor point is independent of that endpoint; and
* every factor outside the local head is independent of that endpoint.

All statements unfold the existing sparse residual integrand.  No analytic
collapse or Fubini hypothesis is introduced here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- An assembled coordinate other than slot zero is independent of the
incoming external endpoint. -/
private theorem assemble_eq_of_incoming_endpoint
    {m : ℕ} (x x' y : T4) (v : Fin m → T4)
    (j : Fin (m + 2)) (hj : j ≠ 0) :
    assemble x y v j = assemble x' y v j := by
  have hjval : j.val ≠ 0 := by
    intro hzero
    apply hj
    apply Fin.ext
    exact hzero
  unfold assemble
  rw [dif_neg hjval, dif_neg hjval]

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res :
      R324WithinHalfResidualPrefix
        ρ lam ε pairing)

/-- Every sparse edge whose source is not slot zero is independent of the
incoming external endpoint. -/
private theorem residualChainEdgeFactor_eq_of_incoming_endpoint
    (x x' y : T4) (v : Fin m → T4)
    (edge : Fin (m + 1)) (hedge : edge ≠ 0) :
    res.residualChainEdgeFactor x y v edge =
      res.residualChainEdgeFactor x' y v edge := by
  have hsource : edge.castSucc ≠ (0 : Fin (m + 2)) := by
    intro hzero
    apply hedge
    apply Fin.ext
    exact congrArg (fun j : Fin (m + 2) => j.val) hzero
  have htarget :
      res.edgeSuccessor edge ≠ (0 : Fin (m + 2)) := by
    have hlt := res.edge_lt_edgeSuccessor edge
    intro hzero
    rw [hzero] at hlt
    exact (not_lt_of_ge (Fin.zero_le _)) hlt
  have hdisplacement :
      res.edgeDisplacement x y v edge =
        res.edgeDisplacement x' y v edge := by
    unfold edgeDisplacement
    rw [
      assemble_eq_of_incoming_endpoint
        x x' y v edge.castSucc hsource,
      assemble_eq_of_incoming_endpoint
        x x' y v (res.edgeSuccessor edge) htarget]
  unfold residualChainEdgeFactor
  rw [hdisplacement]

/-- Every remaining signed step difference is independent of the incoming
external endpoint. -/
private theorem residualStepDifference_eq_of_incoming_endpoint
    (x x' y : T4) (v : Fin m → T4)
    (step : R322ExtractionStep m) :
    res.residualStepDifference x y v step =
      res.residualStepDifference x' y v step := by
  let edge : Fin (m + 1) :=
    r324InternalVertexEdgeSlot step.1.2
  have hvar (i : Fin m) :
      varIdx i ≠ (0 : Fin (m + 2)) := by
    intro hzero
    have hzeroVal := congrArg Fin.val hzero
    simp only [varIdx_val, Fin.val_zero] at hzeroVal
    omega
  have htarget :
      res.edgeSuccessor edge ≠ (0 : Fin (m + 2)) := by
    have hlt := res.edge_lt_edgeSuccessor edge
    intro hzero
    rw [hzero] at hlt
    exact (not_lt_of_ge (Fin.zero_le _)) hlt
  have hright :
      assemble x y v (varIdx step.1.2) =
        assemble x' y v (varIdx step.1.2) :=
    assemble_eq_of_incoming_endpoint
      x x' y v (varIdx step.1.2) (hvar step.1.2)
  have hleft :
      assemble x y v (varIdx step.1.1) =
        assemble x' y v (varIdx step.1.1) :=
    assemble_eq_of_incoming_endpoint
      x x' y v (varIdx step.1.1) (hvar step.1.1)
  have hsuccessor :
      assemble x y v (res.edgeSuccessor edge) =
        assemble x' y v (res.edgeSuccessor edge) :=
    assemble_eq_of_incoming_endpoint
      x x' y v (res.edgeSuccessor edge) htarget
  unfold residualStepDifference
  change
    res.state.edges edge
        (assemble x y v (varIdx step.1.2) -
          assemble x y v (res.edgeSuccessor edge)) -
      res.state.edges edge
        (assemble x y v (varIdx step.1.1) -
          assemble x y v (res.edgeSuccessor edge)) =
    res.state.edges edge
        (assemble x' y v (varIdx step.1.2) -
          assemble x' y v (res.edgeSuccessor edge)) -
      res.state.edges edge
        (assemble x' y v (varIdx step.1.1) -
          assemble x' y v (res.edgeSuccessor edge))
  rw [hright, hleft, hsuccessor]

/-- The complete product of remaining signed differences is independent of
the incoming external endpoint. -/
private theorem residualDifferenceProduct_eq_of_incoming_endpoint
    (x x' y : T4) (v : Fin m → T4) :
    res.residualDifferenceProduct x y v =
      res.residualDifferenceProduct x' y v := by
  unfold residualDifferenceProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro step _hstep
  exact
    res.residualStepDifference_eq_of_incoming_endpoint
      x x' y v step

section Head

variable
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)

include tail hremaining

omit tail hremaining in
/-- A head beginning at the first internal vertex necessarily has the
incoming external slot as sparse predecessor. -/
theorem predecessorSlot_eq_zero_of_head_left_eq_zero
    (hleft : head.1.1.val = 0) :
    r324WithinHalfPredecessorSlot res.state head = 0 := by
  apply Fin.ext
  have hle := res.predecessorSlot_val_le_left head
  change
    (r324WithinHalfPredecessorSlot
      res.state head).val = 0
  change
    (r324WithinHalfPredecessorSlot
      res.state head).val ≤ head.1.1.val at hle
  omega

/-- For a head beginning at internal vertex zero, the named predecessor
point is literally the incoming external endpoint. -/
theorem headPredecessorPoint_eq_incoming_of_head_left_eq_zero
    (hleft : head.1.1.val = 0)
    (x y : T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    res.headPredecessorPoint
        head tail hremaining x y v =
      x := by
  unfold headPredecessorPoint
  rw [
    res.predecessorSlot_eq_zero_of_head_left_eq_zero
      head hleft]
  exact assemble_zero x y _

/-- The outgoing successor point of any head is independent of the incoming
external endpoint.  This is stronger than the zero-left-endpoint case:
the sparse successor lies strictly after an internal outgoing slot. -/
theorem headSuccessorPoint_eq_of_incoming_endpoint
    (x x' y : T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    res.headSuccessorPoint
        head tail hremaining x y v =
      res.headSuccessorPoint
        head tail hremaining x' y v := by
  unfold headSuccessorPoint
  apply assemble_eq_of_incoming_endpoint
  let outgoing :=
    (res.headContext
      head tail hremaining).outgoingSlot
  have hlt := res.edge_lt_edgeSuccessor outgoing
  intro hzero
  rw [hzero] at hlt
  exact (not_lt_of_ge (Fin.zero_le _)) hlt

/-- Once the head predecessor is slot zero, every post-collapse ordinary
chain factor outside the local head is independent of the incoming
external endpoint. -/
theorem
    headOuterChainProductAfter_eq_of_incoming_endpoint_of_head_left_eq_zero
    (hleft : head.1.1.val = 0)
    (x x' y : T4) (v : Fin m → T4) :
    res.headOuterChainProductAfter
        head tail hremaining x y v =
      res.headOuterChainProductAfter
        head tail hremaining x' y v := by
  have hpred :
      r324WithinHalfPredecessorSlot res.state head = 0 :=
    res.predecessorSlot_eq_zero_of_head_left_eq_zero
      head hleft
  unfold headOuterChainProductAfter
  apply Finset.prod_congr rfl
  intro edge hedge
  apply
    (res.afterHead
      head tail hremaining).residualChainEdgeFactor_eq_of_incoming_endpoint
  intro hedgeZero
  have hnotHead :
      edge ∉ res.headChainSlots
        head tail hremaining :=
    (Finset.mem_sdiff.mp hedge).2
  apply hnotHead
  rw [headChainSlots, hpred, hedgeZero]
  simp

/-- Every factor outside a zero-left-endpoint local head is independent of
the incoming external endpoint.  In particular, the outer factor may be
held constant during the incoming Fourier integral. -/
theorem headOuterFactor_eq_of_incoming_endpoint_of_head_left_eq_zero
    (hleft : head.1.1.val = 0)
    (x x' y : T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    res.headOuterFactor
        head tail hremaining ρ ε x y v =
      res.headOuterFactor
        head tail hremaining ρ ε x' y v := by
  unfold headOuterFactor
  rw [
    res.headOuterChainProductAfter_eq_of_incoming_endpoint_of_head_left_eq_zero
      head tail hremaining hleft x x' y
      ((res.afterHead
        head tail hremaining).reconstruct v),
    (res.afterHead
      head tail hremaining).residualDifferenceProduct_eq_of_incoming_endpoint
        x x' y
        ((res.afterHead
          head tail hremaining).reconstruct v)]

end Head

end R324WithinHalfResidualPrefix

end

end Anderson4D
