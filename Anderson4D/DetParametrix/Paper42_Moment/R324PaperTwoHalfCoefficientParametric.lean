import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTwoHalfUniformMajorant

/-!
# Coefficient-parametric two-half endpoint exit

Paper Step 4 applies all four signed endpoint operations while the complete
signed-word coefficient is still untouched.  This file records that fact at
the common two-half carrier: the coefficient may be any function of the two
surviving half configurations.  In particular, no block-local factorization
of the coefficient is assumed.

The resulting estimate retains, as global factors, both fourth-order mode
decays and the four-route endpoint sacrifice.  The remaining spatial
majorant contains exactly the two terminal scale products, the two
endpoint-erased inverse-square paths, and the norm of the original complete
coefficient.
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
namespace R324PaperHalfEndpointUniformBound

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {alpha beta : Z4}
    {leftProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP alpha}
    {rightProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM (-alpha)}

/-- The ordered four-endpoint density with an arbitrary complete coefficient.
The right endpoint transform is applied only after the completed left density
has been formed, so the coefficient is never split between grouped blocks. -/
def endpointProductDensityWithCoefficient
    {routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders}
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (beta : Z4)
    (coefficient :
      (left.carrier.SurvivingCoordinate -> T4) ->
        (right.carrier.SurvivingCoordinate -> T4) -> Complex)
    (p :
      (left.carrier.SurvivingCoordinate -> T4) ×
        (right.carrier.SurvivingCoordinate -> T4)) : Complex :=
  right.density
    (fun rightPost =>
      left.density (fun _ => coefficient p.1 rightPost) beta p.1)
    (-beta) p.2

/-- The coefficient-parametric density on the literal initial nested-cross
carrier. -/
def nestedEndpointProductDensityWithCoefficient
    {routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders}
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (beta : Z4)
    (pi : kappaP.singles ≃ kappaM.singles)
    (coefficient :
      (left.carrier.SurvivingCoordinate -> T4) ->
        (right.carrier.SurvivingCoordinate -> T4) -> Complex)
    (v : (left.twoHalfTerminal right).NestedCoordinate pi -> T4) : Complex :=
  (left.twoHalfTerminal right).initialNestedPullback pi
    (left.endpointProductDensityWithCoefficient right beta coefficient) v

/-- The spatial part of the coefficient-parametric endpoint majorant.  The
mode decay and endpoint sacrifice deliberately do not occur here: they stay
outside the complete signed-word coefficient and outside every grouped run. -/
def coefficientEndpointGroupedMajorant
    {routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders}
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (coefficient :
      (left.carrier.SurvivingCoordinate -> T4) ->
        (right.carrier.SurvivingCoordinate -> T4) -> Complex)
    (p :
      (left.carrier.SurvivingCoordinate -> T4) ×
        (right.carrier.SurvivingCoordinate -> T4)) : Real :=
  ((∏ edge ∈ left.carrier.activeEdgeSlots,
        routes.left.completedRoute.terminalScale edge) *
      (∏ edge ∈ right.carrier.activeEdgeSlots,
        routes.right.completedRoute.terminalScale edge)) *
    invSqKerMass ^ (4 : Nat) *
    left.carrier.endpointErasedInvSqChainProduct left.active p.1 *
    right.carrier.endpointErasedInvSqChainProduct right.active p.2 *
    ‖coefficient p.1 p.2‖

/-- The preceding spatial majorant transported to the initial nested-cross
carrier. -/
def initialNestedCoefficientEndpointGroupedMajorant
    {routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders}
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (pi : kappaP.singles ≃ kappaM.singles)
    (coefficient :
      (left.carrier.SurvivingCoordinate -> T4) ->
        (right.carrier.SurvivingCoordinate -> T4) -> Complex)
    (v : (left.twoHalfTerminal right).NestedCoordinate pi -> T4) : Real :=
  coefficientEndpointGroupedMajorant left right coefficient
    (((left.twoHalfTerminal right).terminalProductPiMeasurableEquivNested pi).symm
      v)

private theorem r324PaperHalfOutgoingEndpointMass_le_cap_parametric
    (c : R324EndpointReductionCase) :
    r324PaperHalfOutgoingEndpointMass c <=
      twoHalfOutgoingEndpointMassCap := by
  cases c with
  | directFourier => exact le_max_left _ _
  | insertedSacrifice => exact le_max_right _ _

private theorem twoHalfOutgoingEndpointMass_le_compensated_parametric
    (routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders) :
    twoHalfOutgoingEndpointMass routes <=
      twoHalfEndpointMassCompensation *
        invSqKerMass ^ (4 : Nat) := by
  have hcapNonneg : 0 <= twoHalfOutgoingEndpointMassCap :=
    zero_le_one.trans (le_max_left _ _)
  have hmassCap :
      twoHalfOutgoingEndpointMass routes <=
        twoHalfOutgoingEndpointMassCap ^ (2 : Nat) := by
    unfold twoHalfOutgoingEndpointMass
    rw [pow_two]
    exact mul_le_mul
      (r324PaperHalfOutgoingEndpointMass_le_cap_parametric _)
      (r324PaperHalfOutgoingEndpointMass_le_cap_parametric _)
      (r324PaperHalfOutgoingEndpointMass_nonneg _) hcapNonneg
  have hinv :
      twoHalfOutgoingEndpointMassCap ^ (2 : Nat) *
          invSqKerMass⁻¹ ^ (4 : Nat) <=
        twoHalfEndpointMassCompensation := by
    exact le_max_right _ _
  calc
    twoHalfOutgoingEndpointMass routes <=
        twoHalfOutgoingEndpointMassCap ^ (2 : Nat) := hmassCap
    _ =
        (twoHalfOutgoingEndpointMassCap ^ (2 : Nat) *
            invSqKerMass⁻¹ ^ (4 : Nat)) *
          invSqKerMass ^ (4 : Nat) := by
      field_simp [r324_invSqKerMass_pos.ne']
    _ <= twoHalfEndpointMassCompensation *
          invSqKerMass ^ (4 : Nat) :=
      mul_le_mul_of_nonneg_right hinv
        (pow_nonneg invSqKerMass_nonneg _)

/-- Pointwise paper Step 4(A) estimate for an arbitrary complete two-half
coefficient.  The four signed endpoint operations occur before this theorem
takes a norm. -/
theorem norm_endpointProductDensityWithCoefficient_le_compensatedGrouped
    (routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders)
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (coefficient :
      (left.carrier.SurvivingCoordinate -> T4) ->
        (right.carrier.SurvivingCoordinate -> T4) -> Complex)
    (p :
      (left.carrier.SurvivingCoordinate -> T4) ×
        (right.carrier.SurvivingCoordinate -> T4))
    (hneLeft : ∀ edge ∈
        left.carrier.endpointErasedActiveEdgeSlots left.active,
      left.carrier.edgeDisplacement 0 0
        (left.carrier.reconstruct p.1) edge ≠ 0)
    (hneRight : ∀ edge ∈
        right.carrier.endpointErasedActiveEdgeSlots right.active,
      right.carrier.edgeDisplacement 0 0
        (right.carrier.reconstruct p.2) edge ≠ 0) :
    ‖left.endpointProductDensityWithCoefficient
        right beta coefficient p‖ <=
      (twoHalfEndpointMassCompensation *
        ((paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          r324EndpointPrimitiveSacrificeProduct eps routes.cases)) *
        coefficientEndpointGroupedMajorant left right coefficient p := by
  have hrightBound := right.norm_density_le
    (fun rightPost =>
      left.density (fun _ => coefficient p.1 rightPost) beta p.1)
    (-beta) p.2 hneRight
  have hleftBound := left.norm_density_le
    (fun _ => coefficient p.1 p.2) beta p.1 hneLeft
  have hrightScale :
      0 <= ∏ edge ∈ right.carrier.activeEdgeSlots,
        routes.right.completedRoute.terminalScale edge := by
    exact Finset.prod_nonneg fun edge _ =>
      (routes.right.completedRoute.terminalCertificate.scale_pos edge).le
  have hrightPrefix :
      0 <=
        (paperSecondOrderModeDecay (-alpha) *
            paperSecondOrderModeDecay (-beta)) *
          routes.right.completedRoute.endpointSacrifice *
          ((∏ edge ∈ right.carrier.activeEdgeSlots,
              routes.right.completedRoute.terminalScale edge) *
            r324PaperHalfOutgoingEndpointMass
              (routes.right.completedRoute.cases 1)) *
          right.carrier.endpointErasedInvSqChainProduct
            right.active p.2 := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (paperSecondOrderModeDecay_nonneg (-alpha))
            (paperSecondOrderModeDecay_nonneg (-beta)))
          routes.right.completedRoute.endpointSacrifice_nonneg)
        (mul_nonneg hrightScale
          (r324PaperHalfOutgoingEndpointMass_nonneg _)))
      (right.carrier.endpointErasedInvSqChainProduct_nonneg
        right.active p.2)
  have hsubstitute :=
    mul_le_mul_of_nonneg_left hleftBound hrightPrefix
  have hcoefficientNonneg : 0 <= ‖coefficient p.1 p.2‖ := norm_nonneg _
  have hexact :
      ‖left.endpointProductDensityWithCoefficient
          right beta coefficient p‖ <=
        ((paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          r324EndpointPrimitiveSacrificeProduct eps routes.cases) *
        (((∏ edge ∈ left.carrier.activeEdgeSlots,
              routes.left.completedRoute.terminalScale edge) *
            (∏ edge ∈ right.carrier.activeEdgeSlots,
              routes.right.completedRoute.terminalScale edge)) *
          twoHalfOutgoingEndpointMass routes) *
        left.carrier.endpointErasedInvSqChainProduct left.active p.1 *
        right.carrier.endpointErasedInvSqChainProduct right.active p.2 *
        ‖coefficient p.1 p.2‖ := by
    dsimp only [endpointProductDensityWithCoefficient]
    refine hrightBound.trans (hsubstitute.trans_eq ?_)
    rw [paperSecondOrderModeDecay_neg alpha,
      paperSecondOrderModeDecay_neg beta,
      paperFourthOrderModeDecay_eq_sq alpha,
      paperFourthOrderModeDecay_eq_sq beta,
      ← routes.endpointSacrifice_mul_eq_product]
    unfold twoHalfOutgoingEndpointMass
    ring
  have hleftScale :
      0 <= ∏ edge ∈ left.carrier.activeEdgeSlots,
        routes.left.completedRoute.terminalScale edge := by
    exact Finset.prod_nonneg fun edge _ =>
      (routes.left.completedRoute.terminalCertificate.scale_pos edge).le
  have hleftPath :=
    left.carrier.endpointErasedInvSqChainProduct_nonneg left.active p.1
  have hrightPath :=
    right.carrier.endpointErasedInvSqChainProduct_nonneg right.active p.2
  have hscalePair := mul_nonneg hleftScale hrightScale
  have hmassScaled := mul_le_mul_of_nonneg_left
    (twoHalfOutgoingEndpointMass_le_compensated_parametric routes) hscalePair
  have hleftScaled := mul_le_mul_of_nonneg_right hmassScaled hleftPath
  have hrightScaled := mul_le_mul_of_nonneg_right hleftScaled hrightPath
  have hspatial :=
    mul_le_mul_of_nonneg_right hrightScaled hcoefficientNonneg
  have hweight :
      0 <= (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        r324EndpointPrimitiveSacrificeProduct eps routes.cases :=
    mul_nonneg
      (mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
        (paperFourthOrderModeDecay_nonneg beta))
      (r324EndpointPrimitiveSacrificeProduct_nonneg eps routes.cases)
  have hweighted := mul_le_mul_of_nonneg_left hspatial hweight
  calc
    ‖left.endpointProductDensityWithCoefficient
        right beta coefficient p‖ <=
        ((paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          r324EndpointPrimitiveSacrificeProduct eps routes.cases) *
        (((∏ edge ∈ left.carrier.activeEdgeSlots,
              routes.left.completedRoute.terminalScale edge) *
            (∏ edge ∈ right.carrier.activeEdgeSlots,
              routes.right.completedRoute.terminalScale edge)) *
          twoHalfOutgoingEndpointMass routes) *
        left.carrier.endpointErasedInvSqChainProduct left.active p.1 *
        right.carrier.endpointErasedInvSqChainProduct right.active p.2 *
        ‖coefficient p.1 p.2‖ := hexact
    _ <=
        ((paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          r324EndpointPrimitiveSacrificeProduct eps routes.cases) *
        (((∏ edge ∈ left.carrier.activeEdgeSlots,
              routes.left.completedRoute.terminalScale edge) *
            (∏ edge ∈ right.carrier.activeEdgeSlots,
              routes.right.completedRoute.terminalScale edge)) *
          (twoHalfEndpointMassCompensation *
            invSqKerMass ^ (4 : Nat))) *
        left.carrier.endpointErasedInvSqChainProduct left.active p.1 *
        right.carrier.endpointErasedInvSqChainProduct right.active p.2 *
        ‖coefficient p.1 p.2‖ := by
      simpa only [mul_assoc] using hweighted
    _ = _ := by
      unfold coefficientEndpointGroupedMajorant
      ring

/-- The coefficient-parametric endpoint exit on the initial nested carrier. -/
theorem ae_norm_nestedEndpointProductDensityWithCoefficient_le_compensatedGrouped
    (routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders)
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (pi : kappaP.singles ≃ kappaM.singles)
    (coefficient :
      (left.carrier.SurvivingCoordinate -> T4) ->
        (right.carrier.SurvivingCoordinate -> T4) -> Complex) :
    (fun v =>
      ‖left.nestedEndpointProductDensityWithCoefficient
        right beta pi coefficient v‖) ≤ᵐ[
      Measure.pi fun _ :
        (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure]
      fun v =>
        (twoHalfEndpointMassCompensation *
          ((paperFourthOrderModeDecay alpha *
              paperFourthOrderModeDecay beta) *
            r324EndpointPrimitiveSacrificeProduct eps routes.cases)) *
          initialNestedCoefficientEndpointGroupedMajorant
            left right pi coefficient v := by
  let terminal := left.twoHalfTerminal right
  let density :=
    left.endpointProductDensityWithCoefficient right beta coefficient
  let endpointWeight : Real :=
    twoHalfEndpointMassCompensation *
      ((paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        r324EndpointPrimitiveSacrificeProduct eps routes.cases)
  let spatialMajorant :
      (left.carrier.SurvivingCoordinate -> T4) ×
        (right.carrier.SurvivingCoordinate -> T4) -> Real :=
    coefficientEndpointGroupedMajorant left right coefficient
  let majorant := fun p => endpointWeight * spatialMajorant p
  have hleftOff :=
    left.carrier.ae_endpointErased_edgeDisplacement_ne_zero left.active
  have hrightOff :=
    right.carrier.ae_endpointErased_edgeDisplacement_ne_zero right.active
  have hleftProduct :=
    (Measure.quasiMeasurePreserving_fst
      (μ := Measure.pi fun _ :
        left.carrier.SurvivingCoordinate => paperMeasure)
      (ν := Measure.pi fun _ :
        right.carrier.SurvivingCoordinate => paperMeasure))
      |>.tendsto_ae hleftOff
  have hrightProduct :=
    (Measure.quasiMeasurePreserving_snd
      (μ := Measure.pi fun _ :
        left.carrier.SurvivingCoordinate => paperMeasure)
      (ν := Measure.pi fun _ :
        right.carrier.SurvivingCoordinate => paperMeasure))
      |>.tendsto_ae hrightOff
  have hproduct :
      (fun p => ‖density p‖) ≤ᵐ[
        (Measure.pi fun _ :
          left.carrier.SurvivingCoordinate => paperMeasure).prod
        (Measure.pi fun _ :
          right.carrier.SurvivingCoordinate => paperMeasure)]
        majorant := by
    filter_upwards [hleftProduct, hrightProduct] with p hp hq
    simpa only [density, majorant, spatialMajorant, endpointWeight, Prod.eta]
      using norm_endpointProductDensityWithCoefficient_le_compensatedGrouped
        routes left right coefficient p hp hq
  have hpull := terminal.ae_norm_initialNestedPullback_le
    pi density majorant hproduct
  simpa only [nestedEndpointProductDensityWithCoefficient,
    initialNestedCoefficientEndpointGroupedMajorant,
    terminal, density, majorant, spatialMajorant, endpointWeight] using hpull

/-- The former residual-primitive endpoint density is the exact specialization
of the coefficient-parametric construction. -/
@[simp] theorem endpointProductDensityWithCoefficient_crossCoefficient
    (routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders)
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (pi : kappaP.singles ≃ kappaM.singles)
    (p :
      (left.carrier.SurvivingCoordinate -> T4) ×
        (right.carrier.SurvivingCoordinate -> T4)) :
    left.endpointProductDensityWithCoefficient right beta
        (left.crossCoefficient right pi) p =
      left.endpointProductDensity right beta pi p := by
  rfl

/-- The preceding specialization is also definitional after transport to the
initial nested carrier. -/
@[simp] theorem nestedEndpointProductDensityWithCoefficient_crossCoefficient
    (routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders)
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (pi : kappaP.singles ≃ kappaM.singles)
    (v : (left.twoHalfTerminal right).NestedCoordinate pi -> T4) :
    left.nestedEndpointProductDensityWithCoefficient right beta pi
        (left.crossCoefficient right pi) v =
      left.nestedEndpointProductDensity right beta pi v := by
  rfl

end R324PaperHalfEndpointUniformBound
end R324WithinHalfResidualPrefix

end

end Anderson4D
