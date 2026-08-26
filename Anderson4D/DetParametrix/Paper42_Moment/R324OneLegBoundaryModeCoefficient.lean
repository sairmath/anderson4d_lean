import Anderson4D.DetParametrix.Paper42_Moment.R324TerminalBoundaryLegFourier

/-!
# One direct boundary leg at a completed R-324 half

When only the outgoing boundary slot is known to carry the free Green
kernel, the inner endpoint integral can still be evaluated exactly.  The
incoming boundary factor is kept literal and is integrated only in the
outer endpoint variable.  Thus no Fubini exchange and no Fourier claim
about the possibly updated incoming edge is used.
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

/-! ## Left half -/

/-- Exact left-half factorization with only the outgoing terminal edge
assumed to be a direct Green leg.  The incoming integral remains the
literal coefficient of the actual stored boundary kernel. -/
theorem leftBoundaryModeCoefficient_eq_incomingIntegral_mul_translatedGreenMode
    (hleft : terminal.left.state.active.Nonempty)
    (houtgoing :
      terminal.left.state.edges
          (terminal.left.terminalOutgoingEdgeSlot hleft) =
        greenFn)
    (α β : Z4)
    (vl : terminal.left.SurvivingCoordinate → T4) :
    terminal.leftBoundaryModeCoefficient hleft α β vl =
      (∫ x : T4,
          charT4 α x *
            (terminal.left.incomingBoundaryFactor
              x 0 (terminal.left.reconstruct vl) : ℂ)
          ∂paperMeasure) *
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
            (0 : Fin (m + 2)) := by
        rfl
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

/-- Exact norm ledger for the preceding one-direct-leg factorization. -/
theorem norm_leftBoundaryModeCoefficient_eq_incomingIntegral_mul_decay
    (hleft : terminal.left.state.active.Nonempty)
    (houtgoing :
      terminal.left.state.edges
          (terminal.left.terminalOutgoingEdgeSlot hleft) =
        greenFn)
    (α β : Z4)
    (vl : terminal.left.SurvivingCoordinate → T4) :
    ‖terminal.leftBoundaryModeCoefficient hleft α β vl‖ =
      ‖∫ x : T4,
          charT4 α x *
            (terminal.left.incomingBoundaryFactor
              x 0 (terminal.left.reconstruct vl) : ℂ)
          ∂paperMeasure‖ *
        paperSecondOrderModeDecay β := by
  rw [
    terminal.leftBoundaryModeCoefficient_eq_incomingIntegral_mul_translatedGreenMode
      hleft houtgoing α β vl,
    norm_mul, norm_translatedGreenMode]

/-- Any quantitative bound for the actual incoming boundary coefficient
combines monotonically with the direct outgoing Green decay. -/
theorem norm_leftBoundaryModeCoefficient_le_incomingBound_mul_decay
    (hleft : terminal.left.state.active.Nonempty)
    (houtgoing :
      terminal.left.state.edges
          (terminal.left.terminalOutgoingEdgeSlot hleft) =
        greenFn)
    (α β : Z4)
    (vl : terminal.left.SurvivingCoordinate → T4)
    (incomingBound : ℝ)
    (hincoming :
      ‖∫ x : T4,
          charT4 α x *
            (terminal.left.incomingBoundaryFactor
              x 0 (terminal.left.reconstruct vl) : ℂ)
          ∂paperMeasure‖ ≤
        incomingBound) :
    ‖terminal.leftBoundaryModeCoefficient hleft α β vl‖ ≤
      incomingBound * paperSecondOrderModeDecay β := by
  rw [
    terminal.norm_leftBoundaryModeCoefficient_eq_incomingIntegral_mul_decay
      hleft houtgoing α β vl]
  exact
    mul_le_mul_of_nonneg_right hincoming
      (paperSecondOrderModeDecay_nonneg β)

/-! ## Right half -/

/-- Exact right-half factorization with only the outgoing terminal edge
assumed to be a direct Green leg.  The literal right-half modes are
`(-α,-β)`. -/
theorem rightBoundaryModeCoefficient_eq_incomingIntegral_mul_translatedGreenMode
    (hright : terminal.right.state.active.Nonempty)
    (houtgoing :
      terminal.right.state.edges
          (terminal.right.terminalOutgoingEdgeSlot hright) =
        greenFn)
    (α β : Z4)
    (vr : terminal.right.SurvivingCoordinate → T4) :
    terminal.rightBoundaryModeCoefficient hright α β vr =
      (∫ z : T4,
          charT4 (-α) z *
            (terminal.right.incomingBoundaryFactor
              z 0 (terminal.right.reconstruct vr) : ℂ)
          ∂paperMeasure) *
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
            (0 : Fin (m + 2)) := by
        rfl
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

/-- Exact norm ledger for the right one-direct-leg factorization, with
sign invariance used only on the explicit outgoing Green mode. -/
theorem norm_rightBoundaryModeCoefficient_eq_incomingIntegral_mul_decay
    (hright : terminal.right.state.active.Nonempty)
    (houtgoing :
      terminal.right.state.edges
          (terminal.right.terminalOutgoingEdgeSlot hright) =
        greenFn)
    (α β : Z4)
    (vr : terminal.right.SurvivingCoordinate → T4) :
    ‖terminal.rightBoundaryModeCoefficient hright α β vr‖ =
      ‖∫ z : T4,
          charT4 (-α) z *
            (terminal.right.incomingBoundaryFactor
              z 0 (terminal.right.reconstruct vr) : ℂ)
          ∂paperMeasure‖ *
        paperSecondOrderModeDecay β := by
  rw [
    terminal.rightBoundaryModeCoefficient_eq_incomingIntegral_mul_translatedGreenMode
      hright houtgoing α β vr,
    norm_mul, norm_translatedGreenMode,
    paperSecondOrderModeDecay_neg]

/-- Any quantitative bound for the actual right incoming coefficient
combines monotonically with the direct outgoing Green decay. -/
theorem norm_rightBoundaryModeCoefficient_le_incomingBound_mul_decay
    (hright : terminal.right.state.active.Nonempty)
    (houtgoing :
      terminal.right.state.edges
          (terminal.right.terminalOutgoingEdgeSlot hright) =
        greenFn)
    (α β : Z4)
    (vr : terminal.right.SurvivingCoordinate → T4)
    (incomingBound : ℝ)
    (hincoming :
      ‖∫ z : T4,
          charT4 (-α) z *
            (terminal.right.incomingBoundaryFactor
              z 0 (terminal.right.reconstruct vr) : ℂ)
          ∂paperMeasure‖ ≤
        incomingBound) :
    ‖terminal.rightBoundaryModeCoefficient hright α β vr‖ ≤
      incomingBound * paperSecondOrderModeDecay β := by
  rw [
    terminal.norm_rightBoundaryModeCoefficient_eq_incomingIntegral_mul_decay
      hright houtgoing α β vr]
  exact
    mul_le_mul_of_nonneg_right hincoming
      (paperSecondOrderModeDecay_nonneg β)

end R324TwoHalfTerminalData

end

end Anderson4D
