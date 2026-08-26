import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEEEEWeightedMajorant

/-!
# The exceptional/direct half after both endpoint operations

This is the literal paper Step 4(A) `ED` half.  The incoming exceptional
head is collapsed exactly, its signed coefficient is transported through
the remaining schedule, and the direct outgoing Fourier operation is then
performed on the completed carrier.  Norms are taken only after these two
operations.  No auxiliary mass or summation is introduced.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open SmoothCutoff
open scoped BigOperators

namespace R324WithinHalfResidualPrefix
namespace R324PaperHalfExceptionalDirectRoute

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}
    {incomingMode : Z4}
    {providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode}

/-- Exact scalar left after the exceptional incoming collapse and the
signed transport of its remaining suffix.  The first displayed decay is
the root Fourier decay; `incomingExceptionalHeadCollapseFactor` contains
the second decay and the primitive defect. -/
def incomingEndpointCoefficient
    (data : R324PaperHalfExceptionalDirectRoute providers)
    (coefficient :
      (data.transport.final.SurvivingCoordinate -> T4) -> Complex)
    (v : data.transport.final.SurvivingCoordinate -> T4) : Complex :=
  data.transport.multiplier incomingMode *
    (((paperSecondOrderModeDecay incomingMode : Complex) *
        data.pack.data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
          data.pack.data.terminal data.pack.data.suffix
          data.pack.data.trace.stopPrefix_remaining_eq incomingMode) *
      coefficient v)

/-- Literal `ED` density after the direct outgoing Fourier operation. -/
def endpointDensity
    (data : R324PaperHalfExceptionalDirectRoute providers)
    (hactive : data.transport.final.state.active.Nonempty)
    (coefficient :
      (data.transport.final.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4)
    (v : data.transport.final.SurvivingCoordinate -> T4) : Complex :=
  data.incomingEndpointCoefficient coefficient v *
    charT4 incomingMode
      (data.transport.final.terminalIncomingAnchor
        (data.transport.final.reconstruct v)) *
    ((data.transport.final.endpointErasedSignedChain
      hactive 0 0 (data.transport.final.reconstruct v) : Real) : Complex) *
    translatedGreenMode outgoingMode
      (data.transport.final.terminalOutgoingAnchor hactive
        (data.transport.final.reconstruct v))

/-- The already-existing complete after-head budget pays the transported
incoming exceptional coefficient. -/
theorem norm_incomingEndpointCoefficient_le
    (data : R324PaperHalfExceptionalDirectRoute providers)
    (coefficient :
      (data.transport.final.SurvivingCoordinate -> T4) -> Complex)
    (v : data.transport.final.SurvivingCoordinate -> T4) :
    ‖data.incomingEndpointCoefficient coefficient v‖ <=
      paperSecondOrderModeDecay incomingMode *
        data.route.terminalScale 0 * ‖coefficient v‖ := by
  have hhead :=
    providers.headBudget data.pack.data.trace.stopPrefix
      data.pack.data.terminal data.pack.data.suffix
      data.pack.data.trace.stopPrefix_remaining_eq
      data.pack.data.stopScale data.pack.data.trace.stopCertificate
  have hhead' :
      ‖data.pack.data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
          data.pack.data.terminal data.pack.data.suffix
          data.pack.data.trace.stopPrefix_remaining_eq incomingMode‖ <=
        data.pack.firstExceptionalScale * K := by
    simpa only [
      R324IncomingExceptionalStopTraceAssembly.R324IncomingExceptionalBudgetedStopTraceAssembly.firstExceptionalScale,
      R324IncomingExceptionalStopTraceAssembly.stopContext,
      R324WithinHalfResidualPrefix.headContext, mul_assoc] using hhead
  have hheadBudget :
      ‖data.pack.data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
          data.pack.data.terminal data.pack.data.suffix
          data.pack.data.trace.stopPrefix_remaining_eq incomingMode‖ <=
        data.pack.afterHeadBudgetScale 0 :=
    hhead'.trans
      (data.pack.firstExceptionalScale_mul_K_le_afterHeadBudgetScale
        providers.hC providers.hlam providers.hK_nonneg providers.hA)
  have hmultiplied :
      ‖data.transport.multiplier incomingMode‖ *
          ‖data.pack.data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
            data.pack.data.terminal data.pack.data.suffix
            data.pack.data.trace.stopPrefix_remaining_eq incomingMode‖ <=
        data.route.terminalScale 0 :=
    (mul_le_mul_of_nonneg_left hheadBudget (norm_nonneg _)).trans
      data.multiplier_mul_afterHeadBudgetScale_le_terminalScale_zero
  have hdecay := paperSecondOrderModeDecay_nonneg incomingMode
  unfold incomingEndpointCoefficient
  calc
    _ = paperSecondOrderModeDecay incomingMode *
          (‖data.transport.multiplier incomingMode‖ *
            ‖data.pack.data.trace.stopPrefix
                |>.incomingExceptionalHeadCollapseFactor
                  data.pack.data.terminal data.pack.data.suffix
                  data.pack.data.trace.stopPrefix_remaining_eq
                  incomingMode‖) *
          ‖coefficient v‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hdecay]
      ring
    _ <= paperSecondOrderModeDecay incomingMode *
          data.route.terminalScale 0 * ‖coefficient v‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmultiplied hdecay)
        (norm_nonneg _)

/-- A direct outgoing boundary retains the base scale `A`. -/
theorem terminalScale_outgoing_eq_base
    (data : R324PaperHalfExceptionalDirectRoute providers)
    (houtgoing : Fin.last m ∉ extractedRightEdges pairing)
    (hactive : data.transport.final.state.active.Nonempty) :
    data.route.terminalScale
        (data.transport.final.terminalOutgoingEdgeSlot hactive) = A := by
  rw [data.transport.final.terminalOutgoingEdgeSlot_eq_finLast_of_directOutgoing
    providers.hm data.transport.final_processed_eq_schedule houtgoing hactive]
  have hreachable := data.route.terminalReachable
  rw [data.route_final] at hreachable
  apply hreachable.edgeScale_eq_base_of_processed_right_lt
  intro earlier _
  exact earlier.1.2.isLt

/-- Slot zero and the erased interior scale product are contained in the
full completed active scale product. -/
theorem terminalScale_zero_mul_endpointErasedScaleProduct_le_activeProduct
    (data : R324PaperHalfExceptionalDirectRoute providers)
    (houtgoing : Fin.last m ∉ extractedRightEdges pairing)
    (hactive : data.transport.final.state.active.Nonempty) :
    data.route.terminalScale 0 *
        data.transport.final.endpointErasedScaleProduct
          hactive data.route.terminalScale <=
      ∏ edge ∈ data.transport.final.activeEdgeSlots,
        data.route.terminalScale edge := by
  have hcertificate := data.route.terminalCertificate
  rw [data.route_final] at hcertificate
  have herased :
      0 <= data.transport.final.endpointErasedScaleProduct
        hactive data.route.terminalScale := by
    unfold R324WithinHalfResidualPrefix.endpointErasedScaleProduct
    exact Finset.prod_nonneg fun edge _ =>
      (hcertificate.scale_pos edge).le
  have houtOne :
      1 <= data.route.terminalScale
        (data.transport.final.terminalOutgoingEdgeSlot hactive) := by
    rw [data.terminalScale_outgoing_eq_base houtgoing hactive]
    exact providers.hA
  have hzero := (hcertificate.scale_pos 0).le
  calc
    _ <= data.route.terminalScale 0 *
          data.route.terminalScale
            (data.transport.final.terminalOutgoingEdgeSlot hactive) *
        data.transport.final.endpointErasedScaleProduct
          hactive data.route.terminalScale := by
      calc
        _ = 1 *
            (data.route.terminalScale 0 *
              data.transport.final.endpointErasedScaleProduct
                hactive data.route.terminalScale) := by ring
        _ <= data.route.terminalScale
              (data.transport.final.terminalOutgoingEdgeSlot hactive) *
            (data.route.terminalScale 0 *
              data.transport.final.endpointErasedScaleProduct
                hactive data.route.terminalScale) :=
          mul_le_mul_of_nonneg_right houtOne (mul_nonneg hzero herased)
        _ = _ := by ring
    _ = _ := by
      rw [data.transport.final.activeEdgeScaleProduct_eq_boundary_mul_endpointErased
        hactive data.route.terminalScale]

/-- Pointwise bound before the harmless case-ledger enlargement for the
incoming inserted sacrifice. -/
theorem norm_endpointDensity_le_directCore
    (data : R324PaperHalfExceptionalDirectRoute providers)
    (houtgoing : Fin.last m ∉ extractedRightEdges pairing)
    (hactive : data.transport.final.state.active.Nonempty)
    (coefficient :
      (data.transport.final.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4)
    (v : data.transport.final.SurvivingCoordinate -> T4)
    (hne : ∀ edge ∈
        data.transport.final.endpointErasedActiveEdgeSlots hactive,
      data.transport.final.edgeDisplacement 0 0
        (data.transport.final.reconstruct v) edge ≠ 0) :
    ‖data.endpointDensity hactive coefficient outgoingMode v‖ <=
      (paperSecondOrderModeDecay incomingMode *
          paperSecondOrderModeDecay outgoingMode) *
        (∏ edge ∈ data.transport.final.activeEdgeSlots,
          data.route.terminalScale edge) *
        data.transport.final.endpointErasedInvSqChainProduct hactive v *
        ‖coefficient v‖ := by
  have hcertificate := data.route.terminalCertificate
  rw [data.route_final] at hcertificate
  have hchain := data.transport.final.abs_endpointErasedSignedChain_le
    hactive hcertificate data.transport.final_remaining
    0 0 (data.transport.final.reconstruct v) hne
  have hchain' :
      |data.transport.final.endpointErasedSignedChain hactive 0 0
          (data.transport.final.reconstruct v)| <=
        data.transport.final.endpointErasedScaleProduct
            hactive data.route.terminalScale *
          data.transport.final.endpointErasedInvSqChainProduct hactive v := by
    simpa only [R324WithinHalfResidualPrefix.endpointErasedInvSqChainProduct]
      using hchain
  have hincoming := data.norm_incomingEndpointCoefficient_le coefficient v
  have hscale :=
    data.terminalScale_zero_mul_endpointErasedScaleProduct_le_activeProduct
      houtgoing hactive
  have hdin := paperSecondOrderModeDecay_nonneg incomingMode
  have hdout := paperSecondOrderModeDecay_nonneg outgoingMode
  have hpath :=
    data.transport.final.endpointErasedInvSqChainProduct_nonneg hactive v
  have hcoef := norm_nonneg (coefficient v)
  have hscaleZero := (hcertificate.scale_pos 0).le
  have hincomingUpper :
      0 <= paperSecondOrderModeDecay incomingMode *
        data.route.terminalScale 0 * ‖coefficient v‖ :=
    mul_nonneg (mul_nonneg hdin hscaleZero) hcoef
  have hchainNonneg := abs_nonneg
    (data.transport.final.endpointErasedSignedChain hactive 0 0
      (data.transport.final.reconstruct v))
  unfold endpointDensity
  rw [norm_mul, norm_mul, norm_mul, norm_charT4, mul_one,
    Complex.norm_real, Real.norm_eq_abs, norm_translatedGreenMode]
  calc
    ‖data.incomingEndpointCoefficient coefficient v‖ *
          |data.transport.final.endpointErasedSignedChain hactive 0 0
            (data.transport.final.reconstruct v)| *
        paperSecondOrderModeDecay outgoingMode <=
      (paperSecondOrderModeDecay incomingMode *
          data.route.terminalScale 0 * ‖coefficient v‖) *
        (data.transport.final.endpointErasedScaleProduct
            hactive data.route.terminalScale *
          data.transport.final.endpointErasedInvSqChainProduct hactive v) *
        paperSecondOrderModeDecay outgoingMode := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hincoming hchain' hchainNonneg hincomingUpper) hdout
    _ =
      (paperSecondOrderModeDecay incomingMode *
          paperSecondOrderModeDecay outgoingMode) *
        (data.route.terminalScale 0 *
          data.transport.final.endpointErasedScaleProduct
            hactive data.route.terminalScale) *
        data.transport.final.endpointErasedInvSqChainProduct hactive v *
        ‖coefficient v‖ := by ring
    _ <= _ := by
      have hfront := mul_nonneg hdin hdout
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hscale hfront) hpath) hcoef

/-- Literal `ED` case-ledger estimate.  The inserted factor records the
already completed incoming exceptional operation; it is introduced only
after the signed density has been fully evaluated. -/
theorem norm_endpointDensity_le
    (data : R324PaperHalfExceptionalDirectRoute providers)
    (houtgoing : Fin.last m ∉ extractedRightEdges pairing)
    (hactive : data.transport.final.state.active.Nonempty)
    (coefficient :
      (data.transport.final.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4)
    (v : data.transport.final.SurvivingCoordinate -> T4)
    (hne : ∀ edge ∈
        data.transport.final.endpointErasedActiveEdgeSlots hactive,
      data.transport.final.edgeDisplacement 0 0
        (data.transport.final.reconstruct v) edge ≠ 0) :
    ‖data.endpointDensity hactive coefficient outgoingMode v‖ <=
      (paperSecondOrderModeDecay incomingMode *
          paperSecondOrderModeDecay outgoingMode) *
        r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
        (∏ edge ∈ data.transport.final.activeEdgeSlots,
          data.route.terminalScale edge) *
        data.transport.final.endpointErasedInvSqChainProduct hactive v *
        ‖coefficient v‖ := by
  have hcore := data.norm_endpointDensity_le_directCore
    houtgoing hactive coefficient outgoingMode v hne
  have hcertificate := data.route.terminalCertificate
  rw [data.route_final] at hcertificate
  have hactiveProduct :
      0 <= ∏ edge ∈ data.transport.final.activeEdgeSlots,
        data.route.terminalScale edge :=
    Finset.prod_nonneg fun edge _ => (hcertificate.scale_pos edge).le
  have hdin := paperSecondOrderModeDecay_nonneg incomingMode
  have hdout := paperSecondOrderModeDecay_nonneg outgoingMode
  have hpath :=
    data.transport.final.endpointErasedInvSqChainProduct_nonneg hactive v
  have hcoef := norm_nonneg (coefficient v)
  have hcoreNonneg :
      0 <= (paperSecondOrderModeDecay incomingMode *
          paperSecondOrderModeDecay outgoingMode) *
        (∏ edge ∈ data.transport.final.activeEdgeSlots,
          data.route.terminalScale edge) *
        data.transport.final.endpointErasedInvSqChainProduct hactive v *
        ‖coefficient v‖ := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hdin hdout) hactiveProduct) hpath)
      hcoef
  have hsac := one_le_r324EndpointPrimitiveSacrifice
    providers.heps providers.heps1
      R324EndpointReductionCase.insertedSacrifice
  refine hcore.trans ?_
  calc
    _ = 1 *
        ((paperSecondOrderModeDecay incomingMode *
            paperSecondOrderModeDecay outgoingMode) *
          (∏ edge ∈ data.transport.final.activeEdgeSlots,
            data.route.terminalScale edge) *
          data.transport.final.endpointErasedInvSqChainProduct hactive v *
          ‖coefficient v‖) := by ring
    _ <= r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
        ((paperSecondOrderModeDecay incomingMode *
            paperSecondOrderModeDecay outgoingMode) *
          (∏ edge ∈ data.transport.final.activeEdgeSlots,
            data.route.terminalScale edge) *
          data.transport.final.endpointErasedInvSqChainProduct hactive v *
          ‖coefficient v‖) :=
      mul_le_mul_of_nonneg_right hsac hcoreNonneg
    _ = _ := by ring

end R324PaperHalfExceptionalDirectRoute
end R324WithinHalfResidualPrefix

end

end Anderson4D
