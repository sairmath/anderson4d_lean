import Anderson4D.DetParametrix.Paper42_Moment.R324PaperDEDDExactCollapse
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperDirectDirectEndpointBound

/-!
# Literal `DE x DD` endpoint factorization and majorant

This file specializes the parameter carried by the exact `DE x DD`
collapse to the residual primitive cross factor from paper Step 3.  The
remaining endpoint density then factors exactly into one completed `DE`
half and one completed `DD` half.  The factorization is performed before
any norm is taken.
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

namespace R324PaperHalfDirectExceptionalRoute

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {alpha beta : Z4}
    {leftProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP alpha}
    {rightProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM (-alpha)}

/-- The untouched Step-3 primitive cross factor on the two completed
terminal carriers. -/
def deddCrossCoefficient
    (leftDE : R324PaperHalfDirectExceptionalRoute leftProviders)
    (rightDD : R324PaperHalfDirectDirectRoute rightProviders)
    (pi : kappaP.singles ≃ kappaM.singles)
    (leftPost : leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4)
    (rightPost : rightDD.transport.final.SurvivingCoordinate -> T4) :
    Complex :=
  (r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
    (r324TwoHalfRootDoubledReconstruct
      leftDE.outgoing.terminalPost rightDD.transport.final
      (leftPost, rightPost)) : Complex)

/-- Literal parameter supplied to the right `DD` collapse: the already
completed signed left `DE` density, the direct right incoming Fourier
scalar, and the still-grouped Step-3 cross factor. -/
def deddReducedCoefficient
    (leftDE : R324PaperHalfDirectExceptionalRoute leftProviders)
    (rightDD : R324PaperHalfDirectDirectRoute rightProviders)
    (outgoingMode : Z4)
    (pi : kappaP.singles ≃ kappaM.singles)
    (u :
      (leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) × T4)
    (rightPost : rightDD.transport.final.SurvivingCoordinate -> T4) :
    Complex :=
  leftDE.outgoing.outgoingEndpointDefectDensity
      (leftDE.directIncomingEndpointCoefficient (fun _ => 1))
      alpha outgoingMode 0 u.1 u.2 *
    (paperSecondOrderModeDecay (-alpha) : Complex) *
    deddCrossCoefficient leftDE rightDD pi u.1 rightPost

/-- Exact product factorization after the left outgoing exceptional
operation and both right direct endpoint operations. -/
theorem deddFinalRawEndpointDensity_eq_endpointFactors
    (leftDE : R324PaperHalfDirectExceptionalRoute leftProviders)
    (rightDD : R324PaperHalfDirectDirectRoute rightProviders)
    (pi : kappaP.singles ≃ kappaM.singles)
    (hactive : rightDD.transport.final.state.active.Nonempty)
    (leftPost : leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4)
    (firstLeft : T4)
    (rightPost : rightDD.transport.final.SurvivingCoordinate -> T4) :
    deddFinalRawEndpointDensity leftDE rightDD
        (deddReducedCoefficient leftDE rightDD beta pi) hactive
        (-alpha) (-beta) (leftPost, firstLeft) rightPost =
      leftDE.outgoing.outgoingEndpointDefectDensity
          (leftDE.directIncomingEndpointCoefficient (fun _ => 1))
          alpha beta 0 leftPost firstLeft *
        rightDD.transportEndpointDensity hactive
          (deddCrossCoefficient leftDE rightDD pi leftPost)
          (-beta) rightPost := by
  unfold deddFinalRawEndpointDensity deddReducedCoefficient
    R324PaperHalfDirectDirectRoute.transportEndpointDensity
    R324PaperHalfDirectDirectRoute.directIncomingCoefficient
  ring

/-- The specialized nested density produced by the exact `DE x DD`
collapse. -/
def deddPaperNestedEndpointDensity
    (leftDE : R324PaperHalfDirectExceptionalRoute leftProviders)
    (rightDD : R324PaperHalfDirectDirectRoute rightProviders)
    (outgoingMode : Z4)
    (hactive : rightDD.transport.final.state.active.Nonempty)
    (pi : kappaP.singles ≃ kappaM.singles)
    (v :
      (R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
        leftDE rightDD).NestedCoordinate pi -> T4) : Complex :=
  deddNestedEndpointDensity leftDE rightDD
    (deddReducedCoefficient leftDE rightDD outgoingMode pi) hactive
    (-alpha) (-outgoingMode) pi v

/-- Exact Fubini factorization on the common nested carrier.  This is the
last algebraic step before the first norm in the mixed endpoint branch. -/
theorem deddPaperNestedEndpointDensity_eq_endpointDensity_mul
    (leftDE : R324PaperHalfDirectExceptionalRoute leftProviders)
    (rightDD : R324PaperHalfDirectDirectRoute rightProviders)
    (hactive : rightDD.transport.final.state.active.Nonempty)
    (pi : kappaP.singles ≃ kappaM.singles)
    (v :
      (R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
        leftDE rightDD).NestedCoordinate pi -> T4) :
    let terminal :=
      R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
        leftDE rightDD
    let p := (terminal.terminalProductPiMeasurableEquivNested pi).symm v
    deddPaperNestedEndpointDensity leftDE rightDD beta hactive pi v =
      leftDE.endpointDensity (fun _ => 1) beta 0 p.1 *
        rightDD.transportEndpointDensity hactive
          (deddCrossCoefficient leftDE rightDD pi p.1)
          (-beta) p.2 := by
  dsimp only
  unfold deddPaperNestedEndpointDensity deddNestedEndpointDensity
    endpointDensity
  dsimp only
  calc
    (∫ firstLeft : T4,
        deddFinalRawEndpointDensity leftDE rightDD
          (deddReducedCoefficient leftDE rightDD beta pi) hactive
          (-alpha) (-beta)
          (((R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
              leftDE rightDD
              |>.terminalProductPiMeasurableEquivNested pi).symm v).1,
            firstLeft)
          ((R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
              leftDE rightDD
              |>.terminalProductPiMeasurableEquivNested pi).symm v).2
        ∂paperMeasure) =
      ∫ firstLeft : T4,
        leftDE.outgoing.outgoingEndpointDefectDensity
            (leftDE.directIncomingEndpointCoefficient (fun _ => 1))
            alpha beta 0
            ((R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
                leftDE rightDD
                |>.terminalProductPiMeasurableEquivNested pi).symm v).1
            firstLeft *
          rightDD.transportEndpointDensity hactive
            (deddCrossCoefficient leftDE rightDD pi
              ((R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
                  leftDE rightDD
                  |>.terminalProductPiMeasurableEquivNested pi).symm v).1)
            (-beta)
            ((R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
                leftDE rightDD
                |>.terminalProductPiMeasurableEquivNested pi).symm v).2
        ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with firstLeft
      exact deddFinalRawEndpointDensity_eq_endpointFactors
        leftDE rightDD pi hactive _ firstLeft _
    _ = _ := by rw [integral_mul_const]

/-- The exact positive carrier produced by the mixed `DE x DD` branch.
There is one inverse-square mass, from the retained exceptional outgoing
endpoint; all three direct Fourier operations are exact multipliers. -/
def deddMassOneGroupedMajorant
    (leftDE : R324PaperHalfDirectExceptionalRoute leftProviders)
    (rightDD : R324PaperHalfDirectDirectRoute rightProviders)
    (hright : rightDD.transport.final.state.active.Nonempty)
    (pi : kappaP.singles ≃ kappaM.singles)
    (leftPost : leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4)
    (rightPost : rightDD.transport.final.SurvivingCoordinate -> T4) : Real :=
  (((∏ edge ∈ leftDE.outgoing.terminalPost.activeEdgeSlots,
        leftDE.route.terminalScale edge) *
      (∏ edge ∈ rightDD.transport.final.activeEdgeSlots,
        rightDD.route.terminalScale edge)) * invSqKerMass) *
    leftDE.outgoing.terminalPost.endpointErasedInvSqChainProduct
      leftDE.terminalPost_active leftPost *
    rightDD.transport.final.endpointErasedInvSqChainProduct
      hright rightPost *
    r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
      (r324TwoHalfRootDoubledReconstruct
        leftDE.outgoing.terminalPost rightDD.transport.final
        (leftPost, rightPost))

/-- Fixed paper constant compensating the three artificial endpoint masses
present in the common uniform grouped carrier but absent from the literal
mixed calculation. -/
def deddEndpointMassCompensation : Real :=
  max 1 (invSqKerMass⁻¹ ^ (3 : Nat))

theorem one_le_deddEndpointMassCompensation :
    1 <= deddEndpointMassCompensation := by
  exact le_max_left _ _

theorem invSqKerMass_le_deddCompensation_mul_pow_four :
    invSqKerMass <=
      deddEndpointMassCompensation * invSqKerMass ^ (4 : Nat) := by
  have hinv :
      invSqKerMass⁻¹ ^ (3 : Nat) <= deddEndpointMassCompensation := by
    exact le_max_right _ _
  calc
    invSqKerMass =
        invSqKerMass⁻¹ ^ (3 : Nat) *
          invSqKerMass ^ (4 : Nat) := by
      field_simp [r324_invSqKerMass_pos.ne']
    _ <= deddEndpointMassCompensation * invSqKerMass ^ (4 : Nat) :=
      mul_le_mul_of_nonneg_right hinv (pow_nonneg invSqKerMass_nonneg _)

/-- Final complete-run base for the mixed branch.  Multiplying a fixed
positive base once absorbs the order-independent endpoint-mass constant at
every positive perturbative order. -/
def deddEndpointCompleteAbsorbedBase (A C K B : Real) : Real :=
  deddEndpointMassCompensation *
    r324TwoHalfCompleteAbsorbedBase A C K B

theorem deddEndpointMassCompensation_mul_primitiveInsertedMajorant_le
    (B lam eps supportConstant : Real) {n : Nat}
    (hn : 1 <= n) (z : T4) :
    deddEndpointMassCompensation *
        primitiveInsertedMajorant B lam eps supportConstant n z <=
      primitiveInsertedMajorant
        (deddEndpointMassCompensation * B)
        lam eps supportConstant n z := by
  have hqpow :
      deddEndpointMassCompensation <=
        deddEndpointMassCompensation ^ (2 * n) := by
    have h := pow_le_pow_right₀ one_le_deddEndpointMassCompensation
      (show 1 <= 2 * n by omega)
    simpa only [pow_one] using h
  have hcoefficient :
      deddEndpointMassCompensation * (B * lam) ^ (2 * n) <=
        ((deddEndpointMassCompensation * B) * lam) ^ (2 * n) := by
    calc
      _ <= deddEndpointMassCompensation ^ (2 * n) *
          (B * lam) ^ (2 * n) :=
        mul_le_mul_of_nonneg_right hqpow
          ((even_two_mul n).pow_nonneg _)
      _ = _ := by
        rw [show (deddEndpointMassCompensation * B) * lam =
          deddEndpointMassCompensation * (B * lam) by ring]
        exact
          (mul_pow deddEndpointMassCompensation (B * lam) (2 * n)).symm
  have hbracket :
      0 <= ((eps⁻¹) ^ 2 / |Real.log eps|) * invSqKer z *
          primitiveSupportIndicator supportConstant eps z +
        (1 / |Real.log eps| ^ 2) *
          (torusDistSq z + eps ^ 2)⁻¹ ^ 2 := by
    apply add_nonneg
    · exact mul_nonneg
        (mul_nonneg (div_nonneg (by positivity) (abs_nonneg _))
          (invSqKer_nonneg z))
        (primitiveSupportIndicator_nonneg supportConstant eps z)
    · exact mul_nonneg (div_nonneg zero_le_one (sq_nonneg _))
        (pow_nonneg
          (inv_nonneg.mpr
            (add_nonneg (torusDistSq_nonneg z) (sq_nonneg eps))) 2)
  unfold primitiveInsertedMajorant
  calc
    _ = (deddEndpointMassCompensation * (B * lam) ^ (2 * n)) *
        (((eps⁻¹) ^ 2 / |Real.log eps|) * invSqKer z *
            primitiveSupportIndicator supportConstant eps z +
          (1 / |Real.log eps| ^ 2) *
            (torusDistSq z + eps ^ 2)⁻¹ ^ 2) := by ring
    _ <= _ := mul_le_mul_of_nonneg_right hcoefficient hbracket

theorem deddEndpointMassCompensation_mul_integral_completeAbsorbed_le
    (A C K B lam : Real) {eps : Real} (heps : 0 < eps)
    (supportConstant : Real) {m : Nat} (hm : 1 <= m) :
    deddEndpointMassCompensation *
        (∫ z : T4,
          primitiveInsertedMajorant
            (r324TwoHalfCompleteAbsorbedBase A C K B)
            lam eps supportConstant m z
          ∂paperMeasure) <=
      ∫ z : T4,
        primitiveInsertedMajorant
          (deddEndpointCompleteAbsorbedBase A C K B)
          lam eps supportConstant m z
        ∂paperMeasure := by
  rw [← integral_const_mul]
  apply integral_mono_ae
  · exact (integrable_primitiveInsertedMajorant
      (r324TwoHalfCompleteAbsorbedBase A C K B)
      lam eps supportConstant m heps).const_mul _
  · exact integrable_primitiveInsertedMajorant
      (deddEndpointCompleteAbsorbedBase A C K B)
      lam eps supportConstant m heps
  · filter_upwards with z
    simpa only [deddEndpointCompleteAbsorbedBase] using
      deddEndpointMassCompensation_mul_primitiveInsertedMajorant_le
        (r324TwoHalfCompleteAbsorbedBase A C K B)
        lam eps supportConstant hm z

/-- Literal pointwise `DE x DD` estimate before replacing its one real
endpoint mass by the common four-mass grouped currency. -/
theorem norm_endpointDensity_mul_transportEndpointDensity_le_massOneGrouped
    (leftDE : R324PaperHalfDirectExceptionalRoute leftProviders)
    (rightDD : R324PaperHalfDirectDirectRoute rightProviders)
    (hrightOutgoing : Fin.last m ∉ extractedRightEdges kappaM)
    (hright : rightDD.transport.final.state.active.Nonempty)
    (pi : kappaP.singles ≃ kappaM.singles)
    (leftPost : leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4)
    (rightPost : rightDD.transport.final.SurvivingCoordinate -> T4)
    (hneLeft : ∀ edge ∈
        leftDE.outgoing.terminalPost.endpointErasedActiveEdgeSlots
          leftDE.terminalPost_active,
      leftDE.outgoing.terminalPost.edgeDisplacement 0 0
        (leftDE.outgoing.terminalPost.reconstruct leftPost) edge ≠ 0)
    (hneRight : ∀ edge ∈
        rightDD.transport.final.endpointErasedActiveEdgeSlots hright,
      rightDD.transport.final.edgeDisplacement 0 0
        (rightDD.transport.final.reconstruct rightPost) edge ≠ 0) :
    ‖leftDE.endpointDensity (fun _ => 1) beta 0 leftPost *
        rightDD.transportEndpointDensity hright
          (deddCrossCoefficient leftDE rightDD pi leftPost)
          (-beta) rightPost‖ <=
      ((paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        r324EndpointPrimitiveSacrificeProduct eps
          ![R324EndpointReductionCase.directFourier,
            R324EndpointReductionCase.insertedSacrifice,
            R324EndpointReductionCase.directFourier,
            R324EndpointReductionCase.directFourier]) *
        deddMassOneGroupedMajorant leftDE rightDD hright pi
          leftPost rightPost := by
  have hleftBound := leftDE.norm_endpointDensity_le
    (fun _ => 1) beta 0 leftPost hneLeft
  have hrightBound := rightDD.norm_transportEndpointDensity_le
    hrightOutgoing hright
    (deddCrossCoefficient leftDE rightDD pi leftPost)
    (-beta) rightPost hneRight
  have hleftUpperNonneg :=
    (norm_nonneg (leftDE.endpointDensity (fun _ => 1) beta 0 leftPost)).trans
      hleftBound
  have hmul := mul_le_mul hleftBound hrightBound
    (norm_nonneg
      (rightDD.transportEndpointDensity hright
        (deddCrossCoefficient leftDE rightDD pi leftPost)
        (-beta) rightPost))
    hleftUpperNonneg
  have hcrossNonneg :=
    r324ResidualPrimitiveSumProduct_nonneg
      rho eps kappaP kappaM pi
      (r324TwoHalfRootDoubledReconstruct
        leftDE.outgoing.terminalPost rightDD.transport.final
        (leftPost, rightPost))
  have hcrossNorm :
      ‖deddCrossCoefficient leftDE rightDD pi leftPost rightPost‖ =
        r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
          (r324TwoHalfRootDoubledReconstruct
            leftDE.outgoing.terminalPost rightDD.transport.final
            (leftPost, rightPost)) := by
    unfold deddCrossCoefficient
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hcrossNonneg]
  rw [← norm_mul] at hmul
  refine hmul.trans_eq ?_
  rw [paperSecondOrderModeDecay_neg alpha,
    paperSecondOrderModeDecay_neg beta,
    paperFourthOrderModeDecay_eq_sq alpha,
    paperFourthOrderModeDecay_eq_sq beta, hcrossNorm]
  unfold r324EndpointPrimitiveSacrificeProduct
    r324EndpointPrimitiveSacrifice deddMassOneGroupedMajorant
  rw [Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, norm_one, one_mul]
  ring

/-- The same mixed endpoint estimate in the common grouped Step-3
currency.  The sole enlargement is the fixed mass compensation. -/
theorem norm_endpointDensity_mul_transportEndpointDensity_le_compensatedGrouped
    (leftDE : R324PaperHalfDirectExceptionalRoute leftProviders)
    (rightDD : R324PaperHalfDirectDirectRoute rightProviders)
    (hrightOutgoing : Fin.last m ∉ extractedRightEdges kappaM)
    (hright : rightDD.transport.final.state.active.Nonempty)
    (pi : kappaP.singles ≃ kappaM.singles)
    (leftPost : leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4)
    (rightPost : rightDD.transport.final.SurvivingCoordinate -> T4)
    (hneLeft : ∀ edge ∈
        leftDE.outgoing.terminalPost.endpointErasedActiveEdgeSlots
          leftDE.terminalPost_active,
      leftDE.outgoing.terminalPost.edgeDisplacement 0 0
        (leftDE.outgoing.terminalPost.reconstruct leftPost) edge ≠ 0)
    (hneRight : ∀ edge ∈
        rightDD.transport.final.endpointErasedActiveEdgeSlots hright,
      rightDD.transport.final.edgeDisplacement 0 0
        (rightDD.transport.final.reconstruct rightPost) edge ≠ 0) :
    ‖leftDE.endpointDensity (fun _ => 1) beta 0 leftPost *
        rightDD.transportEndpointDensity hright
          (deddCrossCoefficient leftDE rightDD pi leftPost)
          (-beta) rightPost‖ <=
      (deddEndpointMassCompensation *
        ((paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          r324EndpointPrimitiveSacrificeProduct eps
            ![R324EndpointReductionCase.directFourier,
              R324EndpointReductionCase.insertedSacrifice,
              R324EndpointReductionCase.directFourier,
              R324EndpointReductionCase.directFourier])) *
        (R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
          leftDE rightDD
          |>.endpointIntegratedGroupedMajorant
            leftDE.route.terminalScale rightDD.route.terminalScale
            leftDE.terminalPost_active hright pi (leftPost, rightPost)) := by
  have hraw :=
    norm_endpointDensity_mul_transportEndpointDensity_le_massOneGrouped
      (beta := beta) leftDE rightDD hrightOutgoing hright pi leftPost rightPost
      hneLeft hneRight
  have hleftScale :
      0 <= ∏ edge ∈ leftDE.outgoing.terminalPost.activeEdgeSlots,
        leftDE.route.terminalScale edge := by
    exact Finset.prod_nonneg fun edge _ =>
      (leftDE.route.terminalCertificate.scale_pos edge).le
  have hrightCertificate := rightDD.route.terminalCertificate
  rw [rightDD.route_final] at hrightCertificate
  have hrightScale :
      0 <= ∏ edge ∈ rightDD.transport.final.activeEdgeSlots,
        rightDD.route.terminalScale edge := by
    exact Finset.prod_nonneg fun edge _ =>
      (hrightCertificate.scale_pos edge).le
  have hleftPath :=
    leftDE.outgoing.terminalPost.endpointErasedInvSqChainProduct_nonneg
      leftDE.terminalPost_active leftPost
  have hrightPath :=
    rightDD.transport.final.endpointErasedInvSqChainProduct_nonneg
      hright rightPost
  have hresidual :=
    r324ResidualPrimitiveSumProduct_nonneg rho eps kappaP kappaM pi
      (r324TwoHalfRootDoubledReconstruct
        leftDE.outgoing.terminalPost rightDD.transport.final
        (leftPost, rightPost))
  have hscalePair := mul_nonneg hleftScale hrightScale
  have hmassScaled := mul_le_mul_of_nonneg_left
    invSqKerMass_le_deddCompensation_mul_pow_four hscalePair
  have hleftScaled := mul_le_mul_of_nonneg_right hmassScaled hleftPath
  have hrightScaled := mul_le_mul_of_nonneg_right hleftScaled hrightPath
  have hspatial := mul_le_mul_of_nonneg_right hrightScaled hresidual
  have hweight :
      0 <= (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        r324EndpointPrimitiveSacrificeProduct eps
          ![R324EndpointReductionCase.directFourier,
            R324EndpointReductionCase.insertedSacrifice,
            R324EndpointReductionCase.directFourier,
            R324EndpointReductionCase.directFourier] :=
    mul_nonneg
      (mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
        (paperFourthOrderModeDecay_nonneg beta))
      (r324EndpointPrimitiveSacrificeProduct_nonneg eps _)
  have hreconstruct :
      r324TwoHalfRootDoubledReconstruct
          leftDE.outgoing.terminalPost rightDD.transport.final
          (leftPost, rightPost) =
        (R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
          leftDE rightDD).terminalDoubledReconstruct
            (leftPost, rightPost) := by
    funext k
    unfold r324TwoHalfRootDoubledReconstruct
      R324TwoHalfTerminalData.terminalDoubledReconstruct
      R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
    rfl
  have hweighted := mul_le_mul_of_nonneg_left hspatial hweight
  exact hraw.trans (hweighted.trans_eq (by
    unfold R324TwoHalfTerminalData.endpointIntegratedGroupedMajorant
    rw [← hreconstruct]
    unfold R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
    ring))

/-- Product-Haar and initial-nested form of the completed mixed endpoint
estimate. -/
theorem ae_norm_deddPaperNestedEndpointDensity_le_compensatedGrouped
    (leftDE : R324PaperHalfDirectExceptionalRoute leftProviders)
    (rightDD : R324PaperHalfDirectDirectRoute rightProviders)
    (hrightOutgoing : Fin.last m ∉ extractedRightEdges kappaM)
    (hright : rightDD.transport.final.state.active.Nonempty)
    (pi : kappaP.singles ≃ kappaM.singles) :
    let terminal :=
      R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
        leftDE rightDD
    (fun v =>
      ‖deddPaperNestedEndpointDensity leftDE rightDD beta hright pi v‖) ≤ᵐ[
      Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure]
      fun v =>
        (deddEndpointMassCompensation *
          ((paperFourthOrderModeDecay alpha *
              paperFourthOrderModeDecay beta) *
            r324EndpointPrimitiveSacrificeProduct eps
              ![R324EndpointReductionCase.directFourier,
                R324EndpointReductionCase.insertedSacrifice,
                R324EndpointReductionCase.directFourier,
                R324EndpointReductionCase.directFourier])) *
          terminal.initialNestedEndpointIntegratedGroupedMajorant
            leftDE.route.terminalScale rightDD.route.terminalScale
            leftDE.terminalPost_active hright pi v := by
  dsimp only
  let terminal :=
    R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
      leftDE rightDD
  let density :
      (leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) ×
        (rightDD.transport.final.SurvivingCoordinate -> T4) -> Complex :=
    fun p =>
      leftDE.endpointDensity (fun _ => 1) beta 0 p.1 *
        rightDD.transportEndpointDensity hright
          (deddCrossCoefficient leftDE rightDD pi p.1) (-beta) p.2
  let endpointWeight : Real :=
    deddEndpointMassCompensation *
      ((paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        r324EndpointPrimitiveSacrificeProduct eps
          ![R324EndpointReductionCase.directFourier,
            R324EndpointReductionCase.insertedSacrifice,
            R324EndpointReductionCase.directFourier,
            R324EndpointReductionCase.directFourier])
  let majorant :
      (leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) ×
        (rightDD.transport.final.SurvivingCoordinate -> T4) -> Real :=
    fun p => endpointWeight *
      terminal.endpointIntegratedGroupedMajorant
        leftDE.route.terminalScale rightDD.route.terminalScale
        leftDE.terminalPost_active hright pi p
  have hleftOff :=
    leftDE.outgoing.terminalPost
      |>.ae_endpointErased_edgeDisplacement_ne_zero
        leftDE.terminalPost_active
  have hrightOff :=
    rightDD.transport.final
      |>.ae_endpointErased_edgeDisplacement_ne_zero hright
  have hleftProduct :=
    (Measure.quasiMeasurePreserving_fst
      (μ := Measure.pi fun _ :
        leftDE.outgoing.terminalPost.SurvivingCoordinate => paperMeasure)
      (ν := Measure.pi fun _ :
        rightDD.transport.final.SurvivingCoordinate => paperMeasure))
      |>.tendsto_ae hleftOff
  have hrightProduct :=
    (Measure.quasiMeasurePreserving_snd
      (μ := Measure.pi fun _ :
        leftDE.outgoing.terminalPost.SurvivingCoordinate => paperMeasure)
      (ν := Measure.pi fun _ :
        rightDD.transport.final.SurvivingCoordinate => paperMeasure))
      |>.tendsto_ae hrightOff
  have hproduct :
      (fun p => ‖density p‖) ≤ᵐ[
        (Measure.pi fun _ :
          leftDE.outgoing.terminalPost.SurvivingCoordinate => paperMeasure).prod
        (Measure.pi fun _ :
          rightDD.transport.final.SurvivingCoordinate => paperMeasure)]
        majorant := by
    filter_upwards [hleftProduct, hrightProduct] with p hp hq
    simpa only [density, majorant, endpointWeight, terminal, Prod.eta] using
      norm_endpointDensity_mul_transportEndpointDensity_le_compensatedGrouped
        (beta := beta) leftDE rightDD hrightOutgoing hright pi p.1 p.2 hp hq
  have hpull := terminal.ae_norm_initialNestedPullback_le
    pi density majorant hproduct
  filter_upwards [hpull] with v hv
  rw [deddPaperNestedEndpointDensity_eq_endpointDensity_mul
    leftDE rightDD hright pi v]
  simpa only [R324TwoHalfTerminalData.initialNestedPullback,
    R324TwoHalfTerminalData.initialNestedEndpointIntegratedGroupedMajorant,
    density, majorant, endpointWeight, terminal] using hv

end R324PaperHalfDirectExceptionalRoute
end R324WithinHalfResidualPrefix

end

end Anderson4D
