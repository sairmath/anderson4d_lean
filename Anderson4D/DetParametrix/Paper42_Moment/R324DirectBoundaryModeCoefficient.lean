import Anderson4D.DetParametrix.Paper42_Moment.R324TerminalBoundaryLegFourier

/-!
# Direct two-leg Fourier coefficients at a completed R-324 half

When both boundary slots of one completed half-chain still carry the free
Green kernel, the two external Fourier integrations factor exactly into
two translated Green modes.  This supplies the direct/direct boundary case
without taking a norm of the endpoint-erased residual core.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal :
      R324TwoHalfTerminalData ρ lam ε κp κm)

/-- Exact two-leg coefficient on the left completed half when both actual
boundary slots are direct Green edges. -/
theorem leftBoundaryModeCoefficient_eq_translatedGreenModes_of_direct
    (hleft : terminal.left.state.active.Nonempty)
    (hincoming : terminal.left.state.edges 0 = greenFn)
    (houtgoing :
      terminal.left.state.edges
          (terminal.left.terminalOutgoingEdgeSlot hleft) =
        greenFn)
    (α β : Z4)
    (vl : terminal.left.SurvivingCoordinate → T4) :
    terminal.leftBoundaryModeCoefficient hleft α β vl =
      translatedGreenMode α
          (terminal.left.terminalIncomingAnchor
            (terminal.left.reconstruct vl)) *
        translatedGreenMode β
          (terminal.left.terminalOutgoingAnchor hleft
            (terminal.left.reconstruct vl)) := by
  let v := terminal.left.reconstruct vl
  have hy (x : T4) :
      (∫ y : T4,
          (charT4 α x *
              (terminal.left.incomingBoundaryFactor x y v : ℂ)) *
            (charT4 β y *
              (terminal.left.outgoingBoundaryFactor
                hleft x y v : ℂ))
          ∂paperMeasure) =
        (charT4 α x *
            (terminal.left.incomingBoundaryFactor x 0 v : ℂ)) *
          translatedGreenMode β
            (terminal.left.terminalOutgoingAnchor hleft v) := by
    have hinIndependent (y : T4) :
        terminal.left.incomingBoundaryFactor x y v =
          terminal.left.incomingBoundaryFactor x 0 v := by
      unfold R324WithinHalfResidualPrefix.incomingBoundaryFactor
        R324WithinHalfResidualPrefix.residualChainEdgeFactor
      rw [if_pos terminal.left.zero_mem_activeEdgeSlots,
        if_pos terminal.left.zero_mem_activeEdgeSlots]
      have hreserved :
          (0 : Fin (m + 1)) ∉
            terminal.left.remainingOutgoingSlots := by
        unfold R324WithinHalfResidualPrefix.remainingOutgoingSlots
        rw [terminal.left_remaining]
        simp
      rw [if_neg hreserved, if_neg hreserved]
      unfold R324WithinHalfResidualPrefix.edgeDisplacement
      have hzeroCast :
          (0 : Fin (m + 1)).castSucc =
            (0 : Fin (m + 2)) := by rfl
      rw [hzeroCast, assemble_zero, assemble_zero,
        terminal.left.assemble_edgeSuccessor_zero_eq_terminalIncomingAnchor
          hleft,
        terminal.left.assemble_edgeSuccessor_zero_eq_terminalIncomingAnchor
          hleft]
    simp_rw [hinIndependent]
    rw [integral_const_mul]
    rw [
      terminal.left.integral_char_mul_outgoingBoundaryFactor_eq
        terminal.left_remaining hleft houtgoing β x v]
  unfold leftBoundaryModeCoefficient leftBoundaryModeIntegrand
  change
    (∫ x : T4,
        ∫ y : T4,
          (charT4 α x *
              (terminal.left.incomingBoundaryFactor x y v : ℂ)) *
            (charT4 β y *
              (terminal.left.outgoingBoundaryFactor hleft x y v : ℂ))
          ∂paperMeasure
        ∂paperMeasure) = _
  simp_rw [hy]
  rw [integral_mul_const]
  rw [
    terminal.left.integral_char_mul_incomingBoundaryFactor_eq
      terminal.left_remaining hleft hincoming α 0 v]

/-- Norm of the preceding exact coefficient. -/
theorem norm_leftBoundaryModeCoefficient_eq_of_direct
    (hleft : terminal.left.state.active.Nonempty)
    (hincoming : terminal.left.state.edges 0 = greenFn)
    (houtgoing :
      terminal.left.state.edges
          (terminal.left.terminalOutgoingEdgeSlot hleft) =
        greenFn)
    (α β : Z4)
    (vl : terminal.left.SurvivingCoordinate → T4) :
    ‖terminal.leftBoundaryModeCoefficient hleft α β vl‖ =
      paperSecondOrderModeDecay α *
        paperSecondOrderModeDecay β := by
  rw [
    terminal.leftBoundaryModeCoefficient_eq_translatedGreenModes_of_direct
      hleft hincoming houtgoing α β vl,
    norm_mul, norm_translatedGreenMode, norm_translatedGreenMode]

/-- Exact two-leg coefficient on the right completed half.  Its modes are
the literal `(-α,-β)` modes from paper (4.18). -/
theorem rightBoundaryModeCoefficient_eq_translatedGreenModes_of_direct
    (hright : terminal.right.state.active.Nonempty)
    (hincoming : terminal.right.state.edges 0 = greenFn)
    (houtgoing :
      terminal.right.state.edges
          (terminal.right.terminalOutgoingEdgeSlot hright) =
        greenFn)
    (α β : Z4)
    (vr : terminal.right.SurvivingCoordinate → T4) :
    terminal.rightBoundaryModeCoefficient hright α β vr =
      translatedGreenMode (-α)
          (terminal.right.terminalIncomingAnchor
            (terminal.right.reconstruct vr)) *
        translatedGreenMode (-β)
          (terminal.right.terminalOutgoingAnchor hright
            (terminal.right.reconstruct vr)) := by
  let v := terminal.right.reconstruct vr
  have hw (z : T4) :
      (∫ w : T4,
          (charT4 (-α) z *
              (terminal.right.incomingBoundaryFactor z w v : ℂ)) *
            (charT4 (-β) w *
              (terminal.right.outgoingBoundaryFactor
                hright z w v : ℂ))
          ∂paperMeasure) =
        (charT4 (-α) z *
            (terminal.right.incomingBoundaryFactor z 0 v : ℂ)) *
          translatedGreenMode (-β)
            (terminal.right.terminalOutgoingAnchor hright v) := by
    have hinIndependent (w : T4) :
        terminal.right.incomingBoundaryFactor z w v =
          terminal.right.incomingBoundaryFactor z 0 v := by
      unfold R324WithinHalfResidualPrefix.incomingBoundaryFactor
        R324WithinHalfResidualPrefix.residualChainEdgeFactor
      rw [if_pos terminal.right.zero_mem_activeEdgeSlots,
        if_pos terminal.right.zero_mem_activeEdgeSlots]
      have hreserved :
          (0 : Fin (m + 1)) ∉
            terminal.right.remainingOutgoingSlots := by
        unfold R324WithinHalfResidualPrefix.remainingOutgoingSlots
        rw [terminal.right_remaining]
        simp
      rw [if_neg hreserved, if_neg hreserved]
      unfold R324WithinHalfResidualPrefix.edgeDisplacement
      have hzeroCast :
          (0 : Fin (m + 1)).castSucc =
            (0 : Fin (m + 2)) := by rfl
      rw [hzeroCast, assemble_zero, assemble_zero,
        terminal.right.assemble_edgeSuccessor_zero_eq_terminalIncomingAnchor
          hright,
        terminal.right.assemble_edgeSuccessor_zero_eq_terminalIncomingAnchor
          hright]
    simp_rw [hinIndependent]
    rw [integral_const_mul]
    rw [
      terminal.right.integral_char_mul_outgoingBoundaryFactor_eq
        terminal.right_remaining hright houtgoing (-β) z v]
  unfold rightBoundaryModeCoefficient rightBoundaryModeIntegrand
  change
    (∫ z : T4,
        ∫ w : T4,
          (charT4 (-α) z *
              (terminal.right.incomingBoundaryFactor z w v : ℂ)) *
            (charT4 (-β) w *
              (terminal.right.outgoingBoundaryFactor hright z w v : ℂ))
          ∂paperMeasure
        ∂paperMeasure) = _
  simp_rw [hw]
  rw [integral_mul_const]
  rw [
    terminal.right.integral_char_mul_incomingBoundaryFactor_eq
      terminal.right_remaining hright hincoming (-α) 0 v]

/-- Norm of the direct right-half coefficient, simplified using frequency
sign invariance of the Green multiplier. -/
theorem norm_rightBoundaryModeCoefficient_eq_of_direct
    (hright : terminal.right.state.active.Nonempty)
    (hincoming : terminal.right.state.edges 0 = greenFn)
    (houtgoing :
      terminal.right.state.edges
          (terminal.right.terminalOutgoingEdgeSlot hright) =
        greenFn)
    (α β : Z4)
    (vr : terminal.right.SurvivingCoordinate → T4) :
    ‖terminal.rightBoundaryModeCoefficient hright α β vr‖ =
      paperSecondOrderModeDecay α *
        paperSecondOrderModeDecay β := by
  rw [
    terminal.rightBoundaryModeCoefficient_eq_translatedGreenModes_of_direct
      hright hincoming houtgoing α β vr,
    norm_mul, norm_translatedGreenMode, norm_translatedGreenMode,
    paperSecondOrderModeDecay_neg,
    paperSecondOrderModeDecay_neg]

end R324TwoHalfTerminalData

end

end Anderson4D

