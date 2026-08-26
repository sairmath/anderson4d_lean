import Anderson4D.DetParametrix.Paper42_Moment.R324DirectIncomingBoundaryGeometry
import Anderson4D.DetParametrix.Paper42_Moment.R324OneLegBoundaryModeCoefficient
import Anderson4D.DetParametrix.Paper42_Moment.R324DirectBoundaryModeCoefficient

/-!
# Structural consumers for direct R-324 boundary branches

The completed two-half package already records that each within-half
analytic schedule has been fully processed.  This file combines that
certificate with the structural direct-boundary geometry:

* a direct outgoing edge supplies a canonical nonempty terminal carrier
  and the one-leg coefficient factorization;
* if the first internal vertex also survives, the incoming edge is still
  the free Green kernel and the full direct/direct coefficient follows.

No raw-Green edge equality or active-carrier witness is added as an
interface hypothesis.
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

/-! ## Canonical active witnesses in the direct outgoing branches -/

/-- The left direct-outgoing condition canonically supplies the nonempty
terminal carrier required by the boundary-coefficient definitions. -/
theorem leftDirectOutgoingActive
    (hm : 0 < m)
    (hdirect : Fin.last m ∉ extractedRightEdges κp) :
    terminal.left.state.active.Nonempty :=
  terminal.left.active_nonempty_of_directOutgoing
    hm terminal.left_processed hdirect

/-- Right-copy counterpart of `leftDirectOutgoingActive`. -/
theorem rightDirectOutgoingActive
    (hm : 0 < m)
    (hdirect : Fin.last m ∉ extractedRightEdges κm) :
    terminal.right.state.active.Nonempty :=
  terminal.right.active_nonempty_of_directOutgoing
    hm terminal.right_processed hdirect

/-! ## Left half -/

/-- A completed left direct-outgoing branch automatically satisfies the
one-leg exact factorization.  The incoming boundary integral is retained
literally. -/
theorem leftBoundaryModeCoefficient_eq_oneLeg_of_directOutgoing
    (hm : 0 < m)
    (hdirect : Fin.last m ∉ extractedRightEdges κp)
    (α β : Z4)
    (vl : terminal.left.SurvivingCoordinate → T4) :
    terminal.leftBoundaryModeCoefficient
        (terminal.leftDirectOutgoingActive hm hdirect) α β vl =
      (∫ x : T4,
          charT4 α x *
            (terminal.left.incomingBoundaryFactor
              x 0 (terminal.left.reconstruct vl) : ℂ)
          ∂paperMeasure) *
        translatedGreenMode β
          (terminal.left.terminalOutgoingAnchor
            (terminal.leftDirectOutgoingActive hm hdirect)
            (terminal.left.reconstruct vl)) := by
  have houtgoing :
      terminal.left.state.edges
          (terminal.left.terminalOutgoingEdgeSlot
            (terminal.leftDirectOutgoingActive hm hdirect)) =
        greenFn :=
    terminal.left
      |>.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_directOutgoing
        hm terminal.left_processed hdirect
        (terminal.leftDirectOutgoingActive hm hdirect)
  exact
    terminal.leftBoundaryModeCoefficient_eq_incomingIntegral_mul_translatedGreenMode
      (terminal.leftDirectOutgoingActive hm hdirect)
      houtgoing α β vl

/-- Norm form of the structurally discharged left one-leg branch. -/
theorem norm_leftBoundaryModeCoefficient_eq_oneLeg_of_directOutgoing
    (hm : 0 < m)
    (hdirect : Fin.last m ∉ extractedRightEdges κp)
    (α β : Z4)
    (vl : terminal.left.SurvivingCoordinate → T4) :
    ‖terminal.leftBoundaryModeCoefficient
        (terminal.leftDirectOutgoingActive hm hdirect) α β vl‖ =
      ‖∫ x : T4,
          charT4 α x *
            (terminal.left.incomingBoundaryFactor
              x 0 (terminal.left.reconstruct vl) : ℂ)
          ∂paperMeasure‖ *
        paperSecondOrderModeDecay β := by
  have houtgoing :
      terminal.left.state.edges
          (terminal.left.terminalOutgoingEdgeSlot
            (terminal.leftDirectOutgoingActive hm hdirect)) =
        greenFn :=
    terminal.left
      |>.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_directOutgoing
        hm terminal.left_processed hdirect
        (terminal.leftDirectOutgoingActive hm hdirect)
  exact
    terminal.norm_leftBoundaryModeCoefficient_eq_incomingIntegral_mul_decay
      (terminal.leftDirectOutgoingActive hm hdirect)
      houtgoing α β vl

/-- If the first left internal vertex also survives the completed schedule,
both actual boundary slots are direct Green edges. -/
theorem leftBoundaryModeCoefficient_eq_of_directBoundary
    (hm : 0 < m)
    (hdirect : Fin.last m ∉ extractedRightEdges κp)
    (hfirst :
      (⟨0, hm⟩ : Fin m) ∈ finalActive κp)
    (α β : Z4)
    (vl : terminal.left.SurvivingCoordinate → T4) :
    terminal.leftBoundaryModeCoefficient
        (terminal.leftDirectOutgoingActive hm hdirect) α β vl =
      translatedGreenMode α
          (terminal.left.terminalIncomingAnchor
            (terminal.left.reconstruct vl)) *
        translatedGreenMode β
          (terminal.left.terminalOutgoingAnchor
            (terminal.leftDirectOutgoingActive hm hdirect)
            (terminal.left.reconstruct vl)) := by
  have hincoming :
      terminal.left.state.edges 0 = greenFn :=
    terminal.left.state_edges_zero_eq_greenFn_of_first_mem_finalActive
      hm terminal.left_processed hfirst
  have houtgoing :
      terminal.left.state.edges
          (terminal.left.terminalOutgoingEdgeSlot
            (terminal.leftDirectOutgoingActive hm hdirect)) =
        greenFn :=
    terminal.left
      |>.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_directOutgoing
        hm terminal.left_processed hdirect
        (terminal.leftDirectOutgoingActive hm hdirect)
  exact
    terminal.leftBoundaryModeCoefficient_eq_translatedGreenModes_of_direct
      (terminal.leftDirectOutgoingActive hm hdirect)
      hincoming houtgoing α β vl

/-- Norm form of the completed left direct/direct branch. -/
theorem norm_leftBoundaryModeCoefficient_eq_of_directBoundary
    (hm : 0 < m)
    (hdirect : Fin.last m ∉ extractedRightEdges κp)
    (hfirst :
      (⟨0, hm⟩ : Fin m) ∈ finalActive κp)
    (α β : Z4)
    (vl : terminal.left.SurvivingCoordinate → T4) :
    ‖terminal.leftBoundaryModeCoefficient
        (terminal.leftDirectOutgoingActive hm hdirect) α β vl‖ =
      paperSecondOrderModeDecay α *
        paperSecondOrderModeDecay β := by
  have hincoming :
      terminal.left.state.edges 0 = greenFn :=
    terminal.left.state_edges_zero_eq_greenFn_of_first_mem_finalActive
      hm terminal.left_processed hfirst
  have houtgoing :
      terminal.left.state.edges
          (terminal.left.terminalOutgoingEdgeSlot
            (terminal.leftDirectOutgoingActive hm hdirect)) =
        greenFn :=
    terminal.left
      |>.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_directOutgoing
        hm terminal.left_processed hdirect
        (terminal.leftDirectOutgoingActive hm hdirect)
  exact
    terminal.norm_leftBoundaryModeCoefficient_eq_of_direct
      (terminal.leftDirectOutgoingActive hm hdirect)
      hincoming houtgoing α β vl

/-! ## Right half -/

/-- A completed right direct-outgoing branch automatically satisfies the
one-leg exact factorization, with the literal `(-α,-β)` modes. -/
theorem rightBoundaryModeCoefficient_eq_oneLeg_of_directOutgoing
    (hm : 0 < m)
    (hdirect : Fin.last m ∉ extractedRightEdges κm)
    (α β : Z4)
    (vr : terminal.right.SurvivingCoordinate → T4) :
    terminal.rightBoundaryModeCoefficient
        (terminal.rightDirectOutgoingActive hm hdirect) α β vr =
      (∫ z : T4,
          charT4 (-α) z *
            (terminal.right.incomingBoundaryFactor
              z 0 (terminal.right.reconstruct vr) : ℂ)
          ∂paperMeasure) *
        translatedGreenMode (-β)
          (terminal.right.terminalOutgoingAnchor
            (terminal.rightDirectOutgoingActive hm hdirect)
            (terminal.right.reconstruct vr)) := by
  have houtgoing :
      terminal.right.state.edges
          (terminal.right.terminalOutgoingEdgeSlot
            (terminal.rightDirectOutgoingActive hm hdirect)) =
        greenFn :=
    terminal.right
      |>.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_directOutgoing
        hm terminal.right_processed hdirect
        (terminal.rightDirectOutgoingActive hm hdirect)
  exact
    terminal.rightBoundaryModeCoefficient_eq_incomingIntegral_mul_translatedGreenMode
      (terminal.rightDirectOutgoingActive hm hdirect)
      houtgoing α β vr

/-- Norm form of the structurally discharged right one-leg branch. -/
theorem norm_rightBoundaryModeCoefficient_eq_oneLeg_of_directOutgoing
    (hm : 0 < m)
    (hdirect : Fin.last m ∉ extractedRightEdges κm)
    (α β : Z4)
    (vr : terminal.right.SurvivingCoordinate → T4) :
    ‖terminal.rightBoundaryModeCoefficient
        (terminal.rightDirectOutgoingActive hm hdirect) α β vr‖ =
      ‖∫ z : T4,
          charT4 (-α) z *
            (terminal.right.incomingBoundaryFactor
              z 0 (terminal.right.reconstruct vr) : ℂ)
          ∂paperMeasure‖ *
        paperSecondOrderModeDecay β := by
  have houtgoing :
      terminal.right.state.edges
          (terminal.right.terminalOutgoingEdgeSlot
            (terminal.rightDirectOutgoingActive hm hdirect)) =
        greenFn :=
    terminal.right
      |>.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_directOutgoing
        hm terminal.right_processed hdirect
        (terminal.rightDirectOutgoingActive hm hdirect)
  exact
    terminal.norm_rightBoundaryModeCoefficient_eq_incomingIntegral_mul_decay
      (terminal.rightDirectOutgoingActive hm hdirect)
      houtgoing α β vr

/-- If the first right internal vertex also survives the completed
schedule, both actual boundary slots are direct Green edges. -/
theorem rightBoundaryModeCoefficient_eq_of_directBoundary
    (hm : 0 < m)
    (hdirect : Fin.last m ∉ extractedRightEdges κm)
    (hfirst :
      (⟨0, hm⟩ : Fin m) ∈ finalActive κm)
    (α β : Z4)
    (vr : terminal.right.SurvivingCoordinate → T4) :
    terminal.rightBoundaryModeCoefficient
        (terminal.rightDirectOutgoingActive hm hdirect) α β vr =
      translatedGreenMode (-α)
          (terminal.right.terminalIncomingAnchor
            (terminal.right.reconstruct vr)) *
        translatedGreenMode (-β)
          (terminal.right.terminalOutgoingAnchor
            (terminal.rightDirectOutgoingActive hm hdirect)
            (terminal.right.reconstruct vr)) := by
  have hincoming :
      terminal.right.state.edges 0 = greenFn :=
    terminal.right.state_edges_zero_eq_greenFn_of_first_mem_finalActive
      hm terminal.right_processed hfirst
  have houtgoing :
      terminal.right.state.edges
          (terminal.right.terminalOutgoingEdgeSlot
            (terminal.rightDirectOutgoingActive hm hdirect)) =
        greenFn :=
    terminal.right
      |>.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_directOutgoing
        hm terminal.right_processed hdirect
        (terminal.rightDirectOutgoingActive hm hdirect)
  exact
    terminal.rightBoundaryModeCoefficient_eq_translatedGreenModes_of_direct
      (terminal.rightDirectOutgoingActive hm hdirect)
      hincoming houtgoing α β vr

/-- Norm form of the completed right direct/direct branch. -/
theorem norm_rightBoundaryModeCoefficient_eq_of_directBoundary
    (hm : 0 < m)
    (hdirect : Fin.last m ∉ extractedRightEdges κm)
    (hfirst :
      (⟨0, hm⟩ : Fin m) ∈ finalActive κm)
    (α β : Z4)
    (vr : terminal.right.SurvivingCoordinate → T4) :
    ‖terminal.rightBoundaryModeCoefficient
        (terminal.rightDirectOutgoingActive hm hdirect) α β vr‖ =
      paperSecondOrderModeDecay α *
        paperSecondOrderModeDecay β := by
  have hincoming :
      terminal.right.state.edges 0 = greenFn :=
    terminal.right.state_edges_zero_eq_greenFn_of_first_mem_finalActive
      hm terminal.right_processed hfirst
  have houtgoing :
      terminal.right.state.edges
          (terminal.right.terminalOutgoingEdgeSlot
            (terminal.rightDirectOutgoingActive hm hdirect)) =
        greenFn :=
    terminal.right
      |>.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_directOutgoing
        hm terminal.right_processed hdirect
        (terminal.rightDirectOutgoingActive hm hdirect)
  exact
    terminal.norm_rightBoundaryModeCoefficient_eq_of_direct
      (terminal.rightDirectOutgoingActive hm hdirect)
      hincoming houtgoing α β vr

end R324TwoHalfTerminalData

end

end Anderson4D
