import Anderson4D.DetParametrix.Paper42_Moment.R324PaperDEDDWeightedMajorant

/-!
# The direct/direct half after both endpoint Fourier operations

This is the literal paper Step 4(A) `DD` half.  The alternating transport is
kept signed to its terminal carrier; the two direct endpoint operations then
contribute their exact second-order Fourier multipliers.  Only after that
exact expression has been formed is its norm bounded by the completed route
scale product and the endpoint-erased inverse-square path.

No artificial inverse-square mass or new summation is introduced here.
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
namespace R324PaperHalfDirectDirectRoute

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}
    {incomingMode : Z4}
    {providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode}

/-- The exact direct incoming Fourier scalar, attached only after the
signed alternating transport has reached its final carrier. -/
def directIncomingCoefficient
    (data : R324PaperHalfDirectDirectRoute providers)
    (coefficient :
      (data.transport.final.SurvivingCoordinate -> T4) -> Complex)
    (v : data.transport.final.SurvivingCoordinate -> T4) : Complex :=
  data.transport.multiplier incomingMode *
    ((paperSecondOrderModeDecay incomingMode : Complex) * coefficient v)

/-- Complete literal `DD` half after both direct endpoint Fourier
operations. -/
def transportEndpointDensity
    (data : R324PaperHalfDirectDirectRoute providers)
    (hactive : data.transport.final.state.active.Nonempty)
    (coefficient :
      (data.transport.final.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4)
    (v : data.transport.final.SurvivingCoordinate -> T4) : Complex :=
  data.directIncomingCoefficient coefficient v *
    charT4 incomingMode
      (data.transport.final.terminalIncomingAnchor
        (data.transport.final.reconstruct v)) *
    ((data.transport.final.endpointErasedSignedChain
      hactive 0 0 (data.transport.final.reconstruct v) : Real) : Complex) *
    translatedGreenMode outgoingMode
      (data.transport.final.terminalOutgoingAnchor hactive
        (data.transport.final.reconstruct v))

/-- The transported multiplier, together with the direct incoming Fourier
decay, is paid by terminal slot zero. -/
theorem norm_directIncomingCoefficient_le
    (data : R324PaperHalfDirectDirectRoute providers)
    (coefficient :
      (data.transport.final.SurvivingCoordinate -> T4) -> Complex)
    (v : data.transport.final.SurvivingCoordinate -> T4) :
    ‖data.directIncomingCoefficient coefficient v‖ <=
      data.route.terminalScale 0 *
        paperSecondOrderModeDecay incomingMode * ‖coefficient v‖ := by
  have hcharge := data.route.multiplier_mul_firstCharge_le_terminal
  rw [data.route_transportedMultiplier, data.route_firstCharge] at hcharge
  have hmult :
      ‖data.transport.multiplier incomingMode‖ <=
        data.route.terminalScale 0 := by
    calc
      ‖data.transport.multiplier incomingMode‖ =
          ‖data.transport.multiplier incomingMode‖ * 1 := by ring
      _ <= ‖data.transport.multiplier incomingMode‖ * A :=
        mul_le_mul_of_nonneg_left providers.hA (norm_nonneg _)
      _ <= data.route.terminalScale 0 := hcharge
  have hdecay := paperSecondOrderModeDecay_nonneg incomingMode
  unfold directIncomingCoefficient
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hdecay]
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_right hmult
      (mul_nonneg hdecay (norm_nonneg (coefficient v))))

/-- In a direct outgoing branch the final boundary scale is still the
initial base `A`. -/
theorem terminalScale_outgoing_eq_base
    (data : R324PaperHalfDirectDirectRoute providers)
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

/-- Terminal slot zero and the endpoint-erased scale product are dominated
by the complete active scale product.  The direct incoming multiplier has
already been paid by slot zero in `norm_directIncomingCoefficient_le`. -/
theorem terminalScale_zero_mul_endpointErasedScaleProduct_le_activeProduct
    (data : R324PaperHalfDirectDirectRoute providers)
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

/-- Pointwise paper Step 4(A) estimate for a literal `DD` half.  Both
direct Fourier multipliers remain explicit; the spatial part is exactly
the completed route's active scale product times its endpoint-erased path.
-/
theorem norm_transportEndpointDensity_le
    (data : R324PaperHalfDirectDirectRoute providers)
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
    ‖data.transportEndpointDensity hactive coefficient outgoingMode v‖ <=
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
  have hcoefficient := data.norm_directIncomingCoefficient_le coefficient v
  have hscale :=
    data.terminalScale_zero_mul_endpointErasedScaleProduct_le_activeProduct
      houtgoing hactive
  have hdin := paperSecondOrderModeDecay_nonneg incomingMode
  have hdout := paperSecondOrderModeDecay_nonneg outgoingMode
  have hpath :=
    data.transport.final.endpointErasedInvSqChainProduct_nonneg hactive v
  have hcoef := norm_nonneg (coefficient v)
  have hscaleZero := (hcertificate.scale_pos 0).le
  have hcoefficientUpper :
      0 <= data.route.terminalScale 0 *
        paperSecondOrderModeDecay incomingMode * ‖coefficient v‖ :=
    mul_nonneg (mul_nonneg hscaleZero hdin) hcoef
  have hchain' :
      |data.transport.final.endpointErasedSignedChain hactive 0 0
          (data.transport.final.reconstruct v)| <=
        data.transport.final.endpointErasedScaleProduct
            hactive data.route.terminalScale *
          data.transport.final.endpointErasedInvSqChainProduct hactive v := by
    simpa only [R324WithinHalfResidualPrefix.endpointErasedInvSqChainProduct]
      using hchain
  unfold transportEndpointDensity
  rw [norm_mul, norm_mul, norm_mul, norm_charT4, mul_one,
    Complex.norm_real, Real.norm_eq_abs, norm_translatedGreenMode]
  have hchainNonneg := abs_nonneg
    (data.transport.final.endpointErasedSignedChain hactive 0 0
      (data.transport.final.reconstruct v))
  calc
    ‖data.directIncomingCoefficient coefficient v‖ *
          |data.transport.final.endpointErasedSignedChain hactive 0 0
            (data.transport.final.reconstruct v)| *
        paperSecondOrderModeDecay outgoingMode <=
      (data.route.terminalScale 0 *
          paperSecondOrderModeDecay incomingMode * ‖coefficient v‖) *
        (data.transport.final.endpointErasedScaleProduct
            hactive data.route.terminalScale *
          data.transport.final.endpointErasedInvSqChainProduct hactive v) *
        paperSecondOrderModeDecay outgoingMode := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hcoefficient hchain' hchainNonneg hcoefficientUpper)
        hdout
    _ =
      (paperSecondOrderModeDecay incomingMode *
          paperSecondOrderModeDecay outgoingMode) *
        (data.route.terminalScale 0 *
          data.transport.final.endpointErasedScaleProduct
            hactive data.route.terminalScale) *
        data.transport.final.endpointErasedInvSqChainProduct hactive v *
        ‖coefficient v‖ := by ring
    _ <=
      (paperSecondOrderModeDecay incomingMode *
          paperSecondOrderModeDecay outgoingMode) *
        (∏ edge ∈ data.transport.final.activeEdgeSlots,
          data.route.terminalScale edge) *
        data.transport.final.endpointErasedInvSqChainProduct hactive v *
        ‖coefficient v‖ := by
      gcongr

end R324PaperHalfDirectDirectRoute
end R324WithinHalfResidualPrefix

end

end Anderson4D
