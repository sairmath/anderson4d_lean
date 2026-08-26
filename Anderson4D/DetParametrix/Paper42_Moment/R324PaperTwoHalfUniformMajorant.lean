import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTwoHalfEndpointProduct

/-!
# Uniform two-half endpoint majorant

This is the numerical Step 4(A) seam for the common ordered endpoint
product.  The right uniform estimate is applied first.  Its coefficient is
the already completed left density; the left uniform estimate is then
applied to that coefficient with the untouched residual primitive factor.
Thus all four signed endpoint operations have already occurred before this
file takes a norm.

The proof keeps the two literal outgoing endpoint masses until the final
comparison with the four-mass grouped carrier.  That comparison uses only a
route-dependent, perturbative-order-independent scalar.  There is no case
split and no new residual sum or scale ledger.
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

/-- The exact product of the two literal outgoing endpoint masses. -/
def twoHalfOutgoingEndpointMass
    (routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders) : Real :=
  r324PaperHalfOutgoingEndpointMass
      (routes.left.completedRoute.cases 1) *
    r324PaperHalfOutgoingEndpointMass
      (routes.right.completedRoute.cases 1)

/-- A route-independent cap for either literal outgoing endpoint mass. -/
def twoHalfOutgoingEndpointMassCap : Real :=
  max 1 invSqKerMass

private theorem r324PaperHalfOutgoingEndpointMass_le_cap
    (c : R324EndpointReductionCase) :
    r324PaperHalfOutgoingEndpointMass c <=
      twoHalfOutgoingEndpointMassCap := by
  cases c with
  | directFourier => exact le_max_left _ _
  | insertedSacrifice => exact le_max_right _ _

/-- The sole enlargement needed to exchange either possible product of
literal outgoing masses for `invSqKerMass ^ 4`.  It is independent of both
the endpoint route and perturbative order. -/
def twoHalfEndpointMassCompensation : Real :=
  max 1
    (twoHalfOutgoingEndpointMassCap ^ (2 : Nat) *
      invSqKerMass⁻¹ ^ (4 : Nat))

theorem one_le_twoHalfEndpointMassCompensation :
    1 <= twoHalfEndpointMassCompensation := by
  exact le_max_left _ _

private theorem twoHalfOutgoingEndpointMass_le_compensated
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
      (r324PaperHalfOutgoingEndpointMass_le_cap _)
      (r324PaperHalfOutgoingEndpointMass_le_cap _)
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

private theorem norm_endpointProductDensity_le_compensatedGrouped
    (routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders)
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (pi : kappaP.singles ≃ kappaM.singles)
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
    ‖left.endpointProductDensity right beta pi p‖ <=
      (twoHalfEndpointMassCompensation *
        ((paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          r324EndpointPrimitiveSacrificeProduct eps routes.cases)) *
        (left.twoHalfTerminal right).endpointIntegratedGroupedMajorant
          routes.left.completedRoute.terminalScale
          routes.right.completedRoute.terminalScale
          left.active right.active pi p := by
  have hrightBound := right.norm_density_le
    (fun rightPost =>
      left.density
        (fun _ => left.crossCoefficient right pi p.1 rightPost)
        beta p.1)
    (-beta) p.2 hneRight
  have hleftBound := left.norm_density_le
    (fun _ => left.crossCoefficient right pi p.1 p.2)
    beta p.1 hneLeft
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
  have hcrossNonneg :=
    r324ResidualPrimitiveSumProduct_nonneg
      rho eps kappaP kappaM pi
      (r324TwoHalfRootDoubledReconstruct
        left.carrier right.carrier p)
  have hcrossNorm :
      ‖left.crossCoefficient right pi p.1 p.2‖ =
        r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
          (r324TwoHalfRootDoubledReconstruct
            left.carrier right.carrier p) := by
    unfold crossCoefficient
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hcrossNonneg]
  have hexact :
      ‖left.endpointProductDensity right beta pi p‖ <=
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
        r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
          (r324TwoHalfRootDoubledReconstruct
            left.carrier right.carrier p) := by
    refine hrightBound.trans (hsubstitute.trans_eq ?_)
    rw [paperSecondOrderModeDecay_neg alpha,
      paperSecondOrderModeDecay_neg beta,
      paperFourthOrderModeDecay_eq_sq alpha,
      paperFourthOrderModeDecay_eq_sq beta,
      ← routes.endpointSacrifice_mul_eq_product, hcrossNorm]
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
    (twoHalfOutgoingEndpointMass_le_compensated routes) hscalePair
  have hleftScaled := mul_le_mul_of_nonneg_right hmassScaled hleftPath
  have hrightScaled := mul_le_mul_of_nonneg_right hleftScaled hrightPath
  have hspatial := mul_le_mul_of_nonneg_right hrightScaled hcrossNonneg
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
    ‖left.endpointProductDensity right beta pi p‖ <=
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
        r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
          (r324TwoHalfRootDoubledReconstruct
            left.carrier right.carrier p) := hexact
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
        r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
          (r324TwoHalfRootDoubledReconstruct
            left.carrier right.carrier p) := by
      simpa only [mul_assoc] using hweighted
    _ = _ := by
      unfold R324TwoHalfTerminalData.endpointIntegratedGroupedMajorant
      simp only [twoHalfTerminal]
      unfold R324TwoHalfTerminalData.terminalDoubledReconstruct
        r324TwoHalfRootDoubledReconstruct
      ring_nf
      rfl

/-- The generic two-half endpoint exit.  It is the only theorem in this
file intended for the residual producer: the ordered signed endpoint
density is reindexed from product Haar to the common nested terminal and
dominated there by the existing
`initialNestedEndpointIntegratedGroupedMajorant`.  The producer may use
`twoHalfTerminal_eq_routes` once to identify this carrier with
`routes.terminal`. -/
theorem ae_norm_nestedEndpointProductDensity_le_compensatedGrouped
    (routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders)
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (pi : kappaP.singles ≃ kappaM.singles) :
    (fun v =>
      ‖left.nestedEndpointProductDensity right beta pi v‖) ≤ᵐ[
      Measure.pi fun _ :
        (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure]
      fun v =>
        (twoHalfEndpointMassCompensation *
          ((paperFourthOrderModeDecay alpha *
              paperFourthOrderModeDecay beta) *
            r324EndpointPrimitiveSacrificeProduct eps routes.cases)) *
          R324TwoHalfTerminalData.initialNestedEndpointIntegratedGroupedMajorant
            (left.twoHalfTerminal right)
            routes.left.completedRoute.terminalScale
            routes.right.completedRoute.terminalScale
            left.active right.active pi v := by
  let terminal := left.twoHalfTerminal right
  let density := left.endpointProductDensity right beta pi
  let endpointWeight : Real :=
    twoHalfEndpointMassCompensation *
      ((paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        r324EndpointPrimitiveSacrificeProduct eps routes.cases)
  let majorant :
      (left.carrier.SurvivingCoordinate -> T4) ×
        (right.carrier.SurvivingCoordinate -> T4) -> Real :=
    fun p => endpointWeight *
      terminal.endpointIntegratedGroupedMajorant
        routes.left.completedRoute.terminalScale
        routes.right.completedRoute.terminalScale
        left.active right.active pi p
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
    simpa only [density, majorant, endpointWeight, terminal, Prod.eta] using
      norm_endpointProductDensity_le_compensatedGrouped
        routes left right pi p hp hq
  have hpull := terminal.ae_norm_initialNestedPullback_le
    pi density majorant hproduct
  simpa only [nestedEndpointProductDensity,
    R324TwoHalfTerminalData.initialNestedEndpointIntegratedGroupedMajorant,
    terminal, density, majorant, endpointWeight] using hpull

end R324PaperHalfEndpointUniformBound
end R324WithinHalfResidualPrefix

end

end Anderson4D
