import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointAggregate
import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointErasedPhaseAIndependence
import Anderson4D.DetParametrix.Paper42_Moment.R324ResidualSumTerminalProjection

/-!
# Endpoint-integrated residual bridge for R-324

Paper §4.2 integrates the four external variables after the signed
within-half collapses and before the nested cross reductions.  At that
stage the four boundary legs are the actual kernels stored in the two
terminal edge states; in general they are no longer raw Green kernels.
Consequently the raw-Green coefficient formulas in
`R324EndpointAggregate` cannot be substituted pointwise here.

This file supplies the exact structural bridge needed by the paper order:

* the four-boundary split is parameterized by explicit nonempty terminal
  active carriers, with no selected primitive slot;
* the endpoint-free core retains the complete residual primitive-pairing
  product as one grouped factor;
* for each fixed terminal internal coordinate, the four genuine boundary
  legs are integrated against the external Fourier modes before any norm
  is taken;
* the resulting density is transported to the literal initial
  nested-cross carrier.

Two analytic interfaces are explicit.  First, the fixed moment
term integrates the internal coordinates inside the four endpoint integrals,
so a joint-integrability/Fubini theorem is still required before the
pointwise endpoint identity below can be substituted into that term.
Second, the present edge certificate records only measurability, symmetry,
and inverse-square domination; those data alone do not imply Fourier decay.
The required coefficient estimate must instead use the exact reachable
outer-Green structure (or a genuinely stronger Fourier certificate) together
with the endpoint cancellation of the paper.  Only after both steps may the
nested core be split into its two outer connectors and current complete
primitive head.
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

/-! ## A selected-slot-free endpoint-erased terminal core -/

/-- A nonempty left residual-single carrier gives a nonempty completed
left half, without choosing a distinguished primitive-sum term. -/
theorem left_active_nonempty_of_singles_nonempty
    (hsingles : κp.singles.Nonempty) :
    terminal.left.state.active.Nonempty := by
  obtain ⟨i, hi⟩ := hsingles
  refine ⟨i, ?_⟩
  rw [
    terminal.left.active_eq_finalActive_of_processed_eq_schedule
      terminal.left_processed]
  exact singles_subset_finalActive κp hi

/-- The residual-single equivalence transports nonemptiness to the
completed right half. -/
theorem right_active_nonempty_of_singles_nonempty
    (π : κp.singles ≃ κm.singles)
    (hsingles : κp.singles.Nonempty) :
    terminal.right.state.active.Nonempty := by
  obtain ⟨i, hi⟩ := hsingles
  let j : κm.singles := π ⟨i, hi⟩
  refine ⟨j.1, ?_⟩
  rw [
    terminal.right.active_eq_finalActive_of_processed_eq_schedule
      terminal.right_processed]
  exact singles_subset_finalActive κm j.2

/-- Product of the two signed endpoint-erased half chains, parameterized
only by explicit nonempty active-carrier witnesses.  These witnesses are
available in every nonempty residual-cross branch and do not select a
summand from the complete primitive covariance sum. -/
def endpointErasedSignedTerminalCoreOfActive
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (vl : terminal.left.SurvivingCoordinate → T4)
    (vr : terminal.right.SurvivingCoordinate → T4) : ℝ :=
  terminal.left.endpointErasedSignedChain
      hleft 0 0 (terminal.left.reconstruct vl) *
    terminal.right.endpointErasedSignedChain
      hright 0 0 (terminal.right.reconstruct vr)

/-- Exact signed four-boundary split without a distinguished residual
covariance slot. -/
theorem terminalChainProducts_eq_fourBoundary_mul_endpointErasedOfActive
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (x y z w : T4)
    (vl : terminal.left.SurvivingCoordinate → T4)
    (vr : terminal.right.SurvivingCoordinate → T4) :
    terminal.left.residualChainProduct
          x y (terminal.left.reconstruct vl) *
        terminal.right.residualChainProduct
          z w (terminal.right.reconstruct vr) =
      terminal.left.incomingBoundaryFactor
          x y (terminal.left.reconstruct vl) *
        terminal.left.outgoingBoundaryFactor
          hleft x y (terminal.left.reconstruct vl) *
        terminal.right.incomingBoundaryFactor
          z w (terminal.right.reconstruct vr) *
        terminal.right.outgoingBoundaryFactor
          hright z w (terminal.right.reconstruct vr) *
        terminal.endpointErasedSignedTerminalCoreOfActive
          hleft hright vl vr := by
  rw [
    terminal.left.residualChainProduct_eq_boundary_mul_endpointErased
      hleft,
    terminal.right.residualChainProduct_eq_boundary_mul_endpointErased
      hright,
    terminal.left.endpointErasedSignedChain_eq_zeroEndpoints hleft,
    terminal.right.endpointErasedSignedChain_eq_zeroEndpoints hright]
  unfold endpointErasedSignedTerminalCoreOfActive
  ring

/-- Endpoint-free two-half core with the complete residual primitive sum
still grouped.  No termwise absolute value is introduced. -/
def endpointErasedResidualSumTerminalCore
    (π : κp.singles ≃ κm.singles)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4)) : ℂ :=
  (terminal.endpointErasedSignedTerminalCoreOfActive
      hleft hright p.1 p.2 : ℂ) *
    terminal.residualSumCrossFactor π p.1 p.2

/-- The genuine terminal residual-sum density is exactly its four actual
signed boundary legs times the endpoint-free, complete primitive-sum
core. -/
theorem terminalResidualSumPhysicalCore_eq_fourBoundary_mul_endpointErased
    (π : κp.singles ≃ κm.singles)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (x y z w : T4)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4)) :
    terminal.terminalResidualSumPhysicalCore π x y z w p =
      (terminal.left.incomingBoundaryFactor
          x y (terminal.left.reconstruct p.1) : ℂ) *
        (terminal.left.outgoingBoundaryFactor
          hleft x y (terminal.left.reconstruct p.1) : ℂ) *
        (terminal.right.incomingBoundaryFactor
          z w (terminal.right.reconstruct p.2) : ℂ) *
        (terminal.right.outgoingBoundaryFactor
          hright z w (terminal.right.reconstruct p.2) : ℂ) *
        terminal.endpointErasedResidualSumTerminalCore
          π hleft hright p := by
  unfold terminalResidualSumPhysicalCore
  rw [
    terminal.left_residualIntegrand_eq_chain
      x y (terminal.left.reconstruct p.1),
    terminal.right_residualIntegrand_eq_chain
      z w (terminal.right.reconstruct p.2)]
  have hchain :=
    terminal.terminalChainProducts_eq_fourBoundary_mul_endpointErasedOfActive
      hleft hright x y z w p.1 p.2
  have hchainComplex :=
    congrArg (fun r : ℝ => (r : ℂ)) hchain
  push_cast at hchainComplex
  rw [hchainComplex]
  unfold endpointErasedResidualSumTerminalCore
  ring

/-! ## Exact integration of the genuine four boundary legs -/

/-- The two genuine left-half boundary legs with their external Fourier
characters.  The kernels are read from the terminal edge state rather
than replaced by raw Green kernels. -/
def leftBoundaryModeIntegrand
    (hleft : terminal.left.state.active.Nonempty)
    (α β : Z4)
    (vl : terminal.left.SurvivingCoordinate → T4)
    (x y : T4) : ℂ :=
  (charT4 α x *
      (terminal.left.incomingBoundaryFactor
        x y (terminal.left.reconstruct vl) : ℂ)) *
    (charT4 β y *
      (terminal.left.outgoingBoundaryFactor
        hleft x y (terminal.left.reconstruct vl) : ℂ))

/-- The two genuine right-half boundary legs in the mode order
`(-α,-β)` of paper (4.18). -/
def rightBoundaryModeIntegrand
    (hright : terminal.right.state.active.Nonempty)
    (α β : Z4)
    (vr : terminal.right.SurvivingCoordinate → T4)
    (z w : T4) : ℂ :=
  (charT4 (-α) z *
      (terminal.right.incomingBoundaryFactor
        z w (terminal.right.reconstruct vr) : ℂ)) *
    (charT4 (-β) w *
      (terminal.right.outgoingBoundaryFactor
        hright z w (terminal.right.reconstruct vr) : ℂ))

/-- Fourier coefficient of the two actual boundary legs of the completed
left half. -/
def leftBoundaryModeCoefficient
    (hleft : terminal.left.state.active.Nonempty)
    (α β : Z4)
    (vl : terminal.left.SurvivingCoordinate → T4) : ℂ :=
  ∫ x, ∫ y,
    terminal.leftBoundaryModeIntegrand hleft α β vl x y
    ∂paperMeasure ∂paperMeasure

/-- Fourier coefficient of the two actual boundary legs of the completed
right half. -/
def rightBoundaryModeCoefficient
    (hright : terminal.right.state.active.Nonempty)
    (α β : Z4)
    (vr : terminal.right.SurvivingCoordinate → T4) : ℂ :=
  ∫ z, ∫ w,
    terminal.rightBoundaryModeIntegrand hright α β vr z w
    ∂paperMeasure ∂paperMeasure

/-- The full external-mode terminal density before endpoint integration. -/
def externalModeResidualSumIntegrand
    (π : κp.singles ≃ κm.singles)
    (α β : Z4)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4))
    (x y z w : T4) : ℂ :=
  charT4 α x * charT4 β y *
    charT4 (-α) z * charT4 (-β) w *
    terminal.terminalResidualSumPhysicalCore
      π x y z w p

/-- Pointwise separation into the two genuine boundary-mode payloads and
one endpoint-free complete residual core. -/
theorem externalModeResidualSumIntegrand_eq_boundary_mul_core
    (π : κp.singles ≃ κm.singles)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (α β : Z4)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4))
    (x y z w : T4) :
    terminal.externalModeResidualSumIntegrand
        π α β p x y z w =
      terminal.leftBoundaryModeIntegrand
          hleft α β p.1 x y *
        terminal.rightBoundaryModeIntegrand
          hright α β p.2 z w *
        terminal.endpointErasedResidualSumTerminalCore
          π hleft hright p := by
  unfold externalModeResidualSumIntegrand
  rw [
    terminal.terminalResidualSumPhysicalCore_eq_fourBoundary_mul_endpointErased
      π hleft hright x y z w p]
  unfold leftBoundaryModeIntegrand rightBoundaryModeIntegrand
  ring

private theorem integral_fourVariables_separated
    (left right : T4 → T4 → ℂ) (core : ℂ) :
    (∫ x, ∫ y, ∫ z, ∫ w,
        left x y * right z w * core
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure) =
      (∫ x, ∫ y, left x y
        ∂paperMeasure ∂paperMeasure) *
      (∫ z, ∫ w, right z w
        ∂paperMeasure ∂paperMeasure) *
      core := by
  have hw (x y z : T4) :
      (∫ w, left x y * right z w * core ∂paperMeasure) =
        left x y * (∫ w, right z w ∂paperMeasure) * core := by
    rw [integral_mul_const, integral_const_mul]
  have hW :
      (∫ x, ∫ y, ∫ z, ∫ w,
          left x y * right z w * core
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure ∂paperMeasure) =
        ∫ x, ∫ y, ∫ z,
          left x y * (∫ w, right z w ∂paperMeasure) * core
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure := by
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with y
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (hw x y)
  rw [hW]
  have hz (x y : T4) :
      (∫ z,
          left x y * (∫ w, right z w ∂paperMeasure) * core
          ∂paperMeasure) =
        left x y *
          (∫ z, ∫ w, right z w
            ∂paperMeasure ∂paperMeasure) *
          core := by
    rw [integral_mul_const, integral_const_mul]
  have hZ :
      (∫ x, ∫ y, ∫ z,
          left x y * (∫ w, right z w ∂paperMeasure) * core
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure) =
        ∫ x, ∫ y,
          left x y *
            (∫ z, ∫ w, right z w
              ∂paperMeasure ∂paperMeasure) *
            core
          ∂paperMeasure ∂paperMeasure := by
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (hz x)
  rw [hZ]
  have hy (x : T4) :
      (∫ y,
          left x y *
            (∫ z, ∫ w, right z w
              ∂paperMeasure ∂paperMeasure) *
            core
          ∂paperMeasure) =
        (∫ y, left x y ∂paperMeasure) *
          (∫ z, ∫ w, right z w
            ∂paperMeasure ∂paperMeasure) *
          core := by
    rw [integral_mul_const, integral_mul_const]
  have hY :
      (∫ x, ∫ y,
          left x y *
            (∫ z, ∫ w, right z w
              ∂paperMeasure ∂paperMeasure) *
            core
          ∂paperMeasure ∂paperMeasure) =
        ∫ x,
          (∫ y, left x y ∂paperMeasure) *
            (∫ z, ∫ w, right z w
              ∂paperMeasure ∂paperMeasure) *
            core
          ∂paperMeasure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hy
  rw [hY, integral_mul_const, integral_mul_const]

/-- Density on the terminal product carrier after all four external
variables have been integrated.  This is the object that may enter the
nested two-connector reduction. -/
def endpointIntegratedResidualDensity
    (π : κp.singles ≃ κm.singles)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (α β : Z4)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4)) : ℂ :=
  terminal.leftBoundaryModeCoefficient hleft α β p.1 *
    terminal.rightBoundaryModeCoefficient hright α β p.2 *
    terminal.endpointErasedResidualSumTerminalCore
      π hleft hright p

/-- Exact endpoint-first identity at each fixed terminal internal
coordinate.  The complete primitive sum remains inside the last factor.
This theorem does not interchange the endpoint integrals with the internal
coordinate integral of the frozen moment term. -/
theorem integral_externalModeResidualSumIntegrand
    (π : κp.singles ≃ κm.singles)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (α β : Z4)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4)) :
    (∫ x, ∫ y, ∫ z, ∫ w,
        terminal.externalModeResidualSumIntegrand
          π α β p x y z w
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure) =
      terminal.endpointIntegratedResidualDensity
        π hleft hright α β p := by
  calc
    _ =
        ∫ x, ∫ y, ∫ z, ∫ w,
          terminal.leftBoundaryModeIntegrand
              hleft α β p.1 x y *
            terminal.rightBoundaryModeIntegrand
              hright α β p.2 z w *
            terminal.endpointErasedResidualSumTerminalCore
              π hleft hright p
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with x
      apply integral_congr_ae
      filter_upwards with y
      apply integral_congr_ae
      filter_upwards with z
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w =>
        terminal.externalModeResidualSumIntegrand_eq_boundary_mul_core
          π hleft hright α β p x y z w
    _ = _ := by
      unfold endpointIntegratedResidualDensity
      exact integral_fourVariables_separated
        (terminal.leftBoundaryModeIntegrand hleft α β p.1)
        (terminal.rightBoundaryModeIntegrand hright α β p.2)
        (terminal.endpointErasedResidualSumTerminalCore
          π hleft hright p)

/-- Exact norm ledger after endpoint integration.  No triangle inequality
has been applied to the complete primitive residual core. -/
theorem norm_endpointIntegratedResidualDensity
    (π : κp.singles ≃ κm.singles)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (α β : Z4)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4)) :
    ‖terminal.endpointIntegratedResidualDensity
        π hleft hright α β p‖ =
      ‖terminal.leftBoundaryModeCoefficient
          hleft α β p.1‖ *
        ‖terminal.rightBoundaryModeCoefficient
          hright α β p.2‖ *
        ‖terminal.endpointErasedResidualSumTerminalCore
          π hleft hright p‖ := by
  unfold endpointIntegratedResidualDensity
  simp only [norm_mul]

/-- Abstract majorant interface for the endpoint Fourier step.  It keeps
the complete residual core grouped and isolates the two coefficient
estimates which must be supplied from exact reachable outer-Green structure
or from a stronger Fourier certificate; the current inverse-square edge
certificate is not sufficient. -/
theorem norm_endpointIntegratedResidualDensity_le
    (π : κp.singles ≃ κm.singles)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (α β : Z4)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4))
    (leftMajorant rightMajorant : ℝ)
    (hleftMajorant :
      ‖terminal.leftBoundaryModeCoefficient
          hleft α β p.1‖ ≤ leftMajorant)
    (hrightMajorant :
      ‖terminal.rightBoundaryModeCoefficient
          hright α β p.2‖ ≤ rightMajorant) :
    ‖terminal.endpointIntegratedResidualDensity
        π hleft hright α β p‖ ≤
      leftMajorant * rightMajorant *
        ‖terminal.endpointErasedResidualSumTerminalCore
          π hleft hright p‖ := by
  rw [terminal.norm_endpointIntegratedResidualDensity
    π hleft hright α β p]
  have hleftNonneg : 0 ≤ leftMajorant :=
    (norm_nonneg _).trans hleftMajorant
  calc
    ‖terminal.leftBoundaryModeCoefficient hleft α β p.1‖ *
          ‖terminal.rightBoundaryModeCoefficient hright α β p.2‖ *
          ‖terminal.endpointErasedResidualSumTerminalCore
            π hleft hright p‖ ≤
        (leftMajorant * rightMajorant) *
          ‖terminal.endpointErasedResidualSumTerminalCore
            π hleft hright p‖ := by
      apply mul_le_mul_of_nonneg_right
      · calc
          ‖terminal.leftBoundaryModeCoefficient hleft α β p.1‖ *
                ‖terminal.rightBoundaryModeCoefficient hright α β p.2‖ ≤
              leftMajorant *
                ‖terminal.rightBoundaryModeCoefficient
                  hright α β p.2‖ :=
            mul_le_mul_of_nonneg_right hleftMajorant (norm_nonneg _)
          _ ≤ leftMajorant * rightMajorant :=
            mul_le_mul_of_nonneg_left
              hrightMajorant hleftNonneg
      · exact norm_nonneg _
    _ = _ := rfl

/-! ## Transport to the initial nested-cross carrier -/

/-- Endpoint-integrated density on the literal initial nested coordinate
carrier. -/
def initialNestedEndpointIntegratedResidualDensity
    (π : κp.singles ≃ κm.singles)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (α β : Z4)
    (v : terminal.NestedCoordinate π → T4) : ℂ :=
  terminal.endpointIntegratedResidualDensity
    π hleft hright α β
    ((terminal.terminalProductPiMeasurableEquivNested π).symm v)

@[simp]
theorem initialNestedEndpointIntegratedResidualDensity_reindex
    (π : κp.singles ≃ κm.singles)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (α β : Z4)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4)) :
    terminal.initialNestedEndpointIntegratedResidualDensity
        π hleft hright α β
        (terminal.terminalProductPiMeasurableEquivNested π p) =
      terminal.endpointIntegratedResidualDensity
        π hleft hright α β p := by
  unfold initialNestedEndpointIntegratedResidualDensity
  rw [MeasurableEquiv.symm_apply_apply]

/-- Measure-preserving transport of the endpoint-integrated density to
the exact carrier consumed by the nested-cross reduction. -/
theorem integral_endpointIntegratedResidualDensity_eq_initialNested
    (π : κp.singles ≃ κm.singles)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (α β : Z4) :
    (∫ p,
        terminal.endpointIntegratedResidualDensity
          π hleft hright α β p
        ∂((Measure.pi fun _ :
            terminal.left.SurvivingCoordinate => paperMeasure).prod
          (Measure.pi fun _ :
            terminal.right.SurvivingCoordinate => paperMeasure))) =
      ∫ v,
        terminal.initialNestedEndpointIntegratedResidualDensity
          π hleft hright α β v
        ∂(Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure) := by
  have hp :=
    terminal.measurePreserving_terminalProductPiMeasurableEquivNested π
  calc
    _ =
        ∫ p,
          terminal.initialNestedEndpointIntegratedResidualDensity
            π hleft hright α β
            (terminal.terminalProductPiMeasurableEquivNested π p)
          ∂((Measure.pi fun _ :
              terminal.left.SurvivingCoordinate => paperMeasure).prod
            (Measure.pi fun _ :
              terminal.right.SurvivingCoordinate => paperMeasure)) := by
      apply integral_congr_ae
      filter_upwards with p
      exact
        (terminal.initialNestedEndpointIntegratedResidualDensity_reindex
          π hleft hright α β p).symm
    _ = _ := by
      simpa only [Function.comp_apply] using
        hp.integral_comp'
          (fun v =>
            terminal.initialNestedEndpointIntegratedResidualDensity
              π hleft hright α β v)

end R324TwoHalfTerminalData

end

end Anderson4D
