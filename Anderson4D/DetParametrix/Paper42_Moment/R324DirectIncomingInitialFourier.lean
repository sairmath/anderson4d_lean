import Anderson4D.DetParametrix.Paper42_Moment.R324InitialTwoHalfRootIntegrability
import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingPhasedResidualCore
import Anderson4D.DetParametrix.Paper42_Moment.R324DifferenceRetainingCore

/-!
# Direct incoming Fourier evaluation at the initial R-324 root

At the all-Green initial state, production slot zero is the translated
incoming Green leg.  Every other factor in the slot-zero-erased residual is
independent of the incoming endpoint.  Hence its one-variable Fourier
integral is exactly the paper second-order mode decay times the phased
slot-zero-erased density.

This file deliberately proves only the pointwise one-variable identity.  It
does not change product coordinates or invoke a global Fubini theorem.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfResidualPrefix

/-! ## Incoming-endpoint independence away from slot zero -/

/-- Assembled coordinates other than the incoming endpoint do not inspect
that endpoint. -/
private theorem assemble_eq_of_incoming_endpoint
    {m : ℕ} (x x' y : T4) (v : Fin m → T4)
    (j : Fin (m + 2)) (hj : j.val ≠ 0) :
    assemble x y v j = assemble x' y v j := by
  simp only [assemble, dif_neg hj]

/-- The slot-zero-erased residual core is independent of the incoming
external endpoint. -/
private theorem incomingErasedResidualIntegrand_eq_of_incoming_endpoint
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x x' y : T4) (v : Fin m → T4) :
    res.incomingErasedResidualIntegrand ρ' ε' x y v =
      res.incomingErasedResidualIntegrand ρ' ε' x' y v := by
  have hchain :
      res.incomingErasedResidualChainProduct x y v =
        res.incomingErasedResidualChainProduct x' y v := by
    unfold incomingErasedResidualChainProduct
    apply Finset.prod_congr rfl
    intro edge hedge
    have hedgeNe : edge ≠ 0 :=
      (Finset.mem_erase.mp hedge).1
    have hsource :
        edge.castSucc.val ≠ 0 := by
      intro hzero
      apply hedgeNe
      apply Fin.ext
      exact hzero
    have htarget :
        (res.edgeSuccessor edge).val ≠ 0 := by
      have hlt := res.edge_lt_edgeSuccessor edge
      intro hzero
      have hedgeZero : edge.val = 0 := by omega
      exact hedgeNe (Fin.ext hedgeZero)
    have hdisplacement :
        res.edgeDisplacement x y v edge =
          res.edgeDisplacement x' y v edge := by
      unfold edgeDisplacement
      rw [assemble_eq_of_incoming_endpoint
          x x' y v edge.castSucc hsource,
        assemble_eq_of_incoming_endpoint
          x x' y v (res.edgeSuccessor edge) htarget]
    unfold residualChainEdgeFactor
    rw [hdisplacement]
  have hdifference :
      res.residualDifferenceProduct x y v =
        res.residualDifferenceProduct x' y v := by
    unfold residualDifferenceProduct
    apply congrArg List.prod
    apply List.map_congr_left
    intro step _hstep
    let edge : Fin (m + 1) :=
      r324InternalVertexEdgeSlot step.1.2
    have hvar (i : Fin m) :
        (varIdx i : Fin (m + 2)).val ≠ 0 := by
      simp only [varIdx_val]
      omega
    have htarget :
        (res.edgeSuccessor edge).val ≠ 0 := by
      have hlt := res.edge_lt_edgeSuccessor edge
      intro hzero
      change edge.val < (res.edgeSuccessor edge).val at hlt
      omega
    have hright :=
      assemble_eq_of_incoming_endpoint
        x x' y v (varIdx step.1.2) (hvar step.1.2)
    have hleft :=
      assemble_eq_of_incoming_endpoint
        x x' y v (varIdx step.1.1) (hvar step.1.1)
    have hsuccessor :=
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
  unfold incomingErasedResidualIntegrand
  rw [hchain, hdifference]

/-! ## Initial slot-zero Fourier evaluation -/

/-- Exact direct-incoming Fourier evaluation at the all-Green initial
residual.  The arbitrary scalar `coefficient` contains every factor that is
constant in the incoming endpoint; in root applications it carries the
other three endpoint characters, the opposite residual, and the cross
factor. -/
theorem integral_charT4_mul_initialResidual_mul_const_eq_incomingPhased
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m))
    (coefficient : ℂ) (k : Z4) (y : T4)
    (v :
      (R324WithinHalfResidualPrefix.initial
        ρ lam ε pairing).SurvivingCoordinate → T4) :
    (∫ x : T4,
        charT4 k x *
          (((R324WithinHalfResidualPrefix.initial
              ρ lam ε pairing).residualIntegrand
            ρ ε x y
            ((R324WithinHalfResidualPrefix.initial
              ρ lam ε pairing).reconstruct v) : ℂ) * coefficient)
        ∂paperMeasure) =
      (R324WithinHalfResidualPrefix.initial
        ρ lam ε pairing).incomingPhasedResidualDensity
          ((paperSecondOrderModeDecay k : ℂ) * coefficient)
          k ρ ε 0 y v := by
  let initial :=
    R324WithinHalfResidualPrefix.initial ρ lam ε pairing
  let anchor : T4 := initial.incomingPhaseAnchor 0 y v
  have hnotReserved :
      (0 : Fin (m + 1)) ∉ initial.remainingOutgoingSlots := by
    intro hmem
    unfold remainingOutgoingSlots at hmem
    obtain ⟨step, _hstep, hzero⟩ := List.mem_map.mp hmem
    exact
      (r324InternalVertexEdgeSlot_ne_zero step.1.2) hzero
  have hanchor (x : T4) :
      initial.incomingPhaseAnchor x y v = anchor := by
    unfold incomingPhaseAnchor anchor
    apply assemble_eq_of_incoming_endpoint
    have hlt := initial.edge_lt_edgeSuccessor (0 : Fin (m + 1))
    change 0 < (initial.edgeSuccessor (0 : Fin (m + 1))).val at hlt
    omega
  have hboundary (x : T4) :
      initial.residualChainEdgeFactor
          x y (initial.reconstruct v) 0 =
        greenFn (anchor - x) := by
    unfold residualChainEdgeFactor
    rw [if_pos initial.zero_mem_activeEdgeSlots,
      if_neg hnotReserved]
    change
      greenFn (initial.edgeDisplacement
        x y (initial.reconstruct v) 0) =
        greenFn (anchor - x)
    have hdisplacement :
        initial.edgeDisplacement
            x y (initial.reconstruct v) 0 =
          -(anchor - x) := by
      unfold edgeDisplacement
      rw [show (0 : Fin (m + 1)).castSucc =
          (0 : Fin (m + 2)) by rfl,
        assemble_zero]
      rw [show assemble x y (initial.reconstruct v)
          (initial.edgeSuccessor 0) = anchor by
        exact hanchor x]
      abel
    rw [hdisplacement, greenFn_memE.neg_invariant]
  have herased (x : T4) :
      initial.incomingErasedResidualIntegrand
          ρ ε x y (initial.reconstruct v) =
        initial.incomingErasedResidualIntegrand
          ρ ε 0 y (initial.reconstruct v) :=
    incomingErasedResidualIntegrand_eq_of_incoming_endpoint
      initial ρ ε x 0 y (initial.reconstruct v)
  have hpoint (x : T4) :
      charT4 k x *
          ((initial.residualIntegrand
            ρ ε x y (initial.reconstruct v) : ℂ) * coefficient) =
        (charT4 k x * ((greenFn (anchor - x) : ℝ) : ℂ)) *
          ((initial.incomingErasedResidualIntegrand
            ρ ε 0 y (initial.reconstruct v) : ℂ) * coefficient) := by
    rw [initial.residualIntegrand_eq_zero_mul_incomingErased,
      hboundary, herased]
    push_cast
    ring
  calc
    (∫ x : T4,
        charT4 k x *
          ((initial.residualIntegrand
            ρ ε x y (initial.reconstruct v) : ℂ) * coefficient)
        ∂paperMeasure) =
        ∫ x : T4,
          (charT4 k x * ((greenFn (anchor - x) : ℝ) : ℂ)) *
            ((initial.incomingErasedResidualIntegrand
              ρ ε 0 y (initial.reconstruct v) : ℂ) * coefficient)
          ∂paperMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ =
        (∫ x : T4,
          charT4 k x * ((greenFn (anchor - x) : ℝ) : ℂ)
          ∂paperMeasure) *
            ((initial.incomingErasedResidualIntegrand
              ρ ε 0 y (initial.reconstruct v) : ℂ) * coefficient) := by
      rw [integral_mul_const]
    _ = _ := by
      rw [integral_charT4_mul_greenFn_shift]
      unfold incomingPhasedResidualDensity
      dsimp only [initial, anchor]
      unfold paperSecondOrderModeDecay
      ring

end R324WithinHalfResidualPrefix

end

end Anderson4D
