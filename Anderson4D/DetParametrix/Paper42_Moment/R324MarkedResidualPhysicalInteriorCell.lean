import Anderson4D.DetParametrix.Paper42_Moment.R324MarkedResidualBlockProductClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324MarkedBlockModeMajorant
import Anderson4D.DetParametrix.Paper42_Moment.R324SelectedInteriorCellLedger

/-!
# A marked residual physical interior object before Fourier expansion

This module stays on the physical-covariance side of the R-324 argument.
It packages the two signed renormalized interior Green profiles with the
residual physical covariance product containing one projected cross edge,
then factors the genuine residual schedule without duplicating that marker.

This packaging is an interface object rather than a phase-A closure theorem;
no equality with the original pre-collapse physical core is asserted here.

This object is deliberately distinct from
`r324SelectedInteriorSkeletonCellMass`.  In that later object every
covariance has already been Fourier-expanded and its fixed coefficient
has been pulled outside the spatial integral.  A representation-order
bridge collapses first and then expands only the surviving marked edge; the
two cell masses are deliberately kept distinct here.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## A signed marked-residual interface object -/

/-- Candidate physical interior object at the residual-active interface.
No theorem here claims that phase A has already produced this object, and
no norm has yet been taken. -/
def r324MarkedResidualPhysicalInteriorCore
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) : ℂ :=
  r324RenormalizedInteriorCore κp
      (fun i => v (leftMomentIndex i)) *
    r324RenormalizedInteriorCore κm
      (fun i => v (rightMomentIndex i)) *
    ρ.r324MarkedPairingCovarianceProductOn ε L
      (momentCombinedPairing κp κm π)
      (r324ResidualMarkedLowerEndpoint selected)
      (momentResidualActive κp κm) v

/-- The same signed core after the exact residual schedule factorization.
The unique marked primitive block stays visible; every other residual
block carries its complete physical covariance product. -/
def r324ResidualFactoredMarkedPhysicalInteriorCore
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) : ℂ :=
  r324RenormalizedInteriorCore κp
      (fun i => v (leftMomentIndex i)) *
    r324RenormalizedInteriorCore κm
      (fun i => v (rightMomentIndex i)) *
    ρ.r324MarkedPairingCovarianceProductOn ε L
      (momentCombinedPairing κp κm π)
      (r324ResidualMarkedLowerEndpoint selected)
      (r324MarkedResidualBlock κp κm π selected) v *
    ρ.r324UnmarkedResidualBlockProduct
      ε κp κm π selected v

/-- Exact marker-preserving residual collapse while both Green profiles
remain signed. -/
theorem r324MarkedResidualPhysicalInteriorCore_eq_residualFactored
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    ρ.r324MarkedResidualPhysicalInteriorCore
        ε L κp κm π selected v =
      ρ.r324ResidualFactoredMarkedPhysicalInteriorCore
        ε L κp κm π selected v := by
  unfold r324MarkedResidualPhysicalInteriorCore
    r324ResidualFactoredMarkedPhysicalInteriorCore
  rw [
    ρ.r324MarkedResidualActiveProduct_eq_marked_mul_unmarked]
  ring

/-! ## Pointwise analytic ledger with one open block -/

/-- Exact norm ledger after the residual collapse.  This is the first
nonnegative form: the marked block is not estimated or replaced. -/
theorem norm_r324MarkedResidualPhysicalInteriorCore_eq_markedBlock
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    ‖ρ.r324MarkedResidualPhysicalInteriorCore
        ε L κp κm π selected v‖ =
      r324SelectedInteriorSkeletonNormDensity κp κm v *
        ‖ρ.r324MarkedPairingCovarianceProductOn ε L
          (momentCombinedPairing κp κm π)
          (r324ResidualMarkedLowerEndpoint selected)
          (r324MarkedResidualBlock κp κm π selected) v‖ *
        ‖ρ.r324UnmarkedResidualBlockProduct
          ε κp κm π selected v‖ := by
  rw [ρ.r324MarkedResidualPhysicalInteriorCore_eq_residualFactored]
  unfold r324ResidualFactoredMarkedPhysicalInteriorCore
    r324SelectedInteriorSkeletonNormDensity
  simp only [norm_mul]

/-- Expanding only the surviving marked block exposes precisely one
projected open edge and leaves every other covariance physical. -/
theorem norm_r324MarkedResidualPhysicalInteriorCore_eq_projectedEdge
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    ‖ρ.r324MarkedResidualPhysicalInteriorCore
        ε L κp κm π selected v‖ =
      r324SelectedInteriorSkeletonNormDensity κp κm v *
        ‖ρ.r324ProjectedCovarianceC ε L
          (v (r324ResidualMarkedLowerEndpoint selected) -
            v (r324ResidualMarkedUpperEndpoint π selected))‖ *
        ρ.r324MarkedResidualBlockUnselectedCovarianceMass
          ε κp κm π selected v *
        ‖ρ.r324UnmarkedResidualBlockProduct
          ε κp κm π selected v‖ := by
  have hblock :
      ‖ρ.r324MarkedPairingCovarianceProductOn ε L
          (momentCombinedPairing κp κm π)
          (r324ResidualMarkedLowerEndpoint selected)
          (r324MarkedResidualBlock κp κm π selected) v‖ =
        ‖ρ.r324ProjectedCovarianceC ε L
          (v (r324ResidualMarkedLowerEndpoint selected) -
            v (r324ResidualMarkedUpperEndpoint π selected))‖ *
          ρ.r324MarkedResidualBlockUnselectedCovarianceMass
            ε κp κm π selected v := by
    rw [ρ.r324MarkedResidualBlockProduct_eq, norm_mul]
    exact congrArg
      (fun x : ℝ =>
        ‖ρ.r324ProjectedCovarianceC ε L
          (v (r324ResidualMarkedLowerEndpoint selected) -
            v (r324ResidualMarkedUpperEndpoint π selected))‖ * x)
      (ρ.norm_r324MarkedResidualBlockUnselectedCovarianceProduct
        ε κp κm π selected v)
  rw [
    ρ.norm_r324MarkedResidualPhysicalInteriorCore_eq_markedBlock,
    hblock]
  ring

/-! ## The genuine selected internal cell -/

/-- Physical marked-residual interface mass on the same genuine open-edge
cell used by the endpoint-first representation. -/
def r324MarkedResidualPhysicalInteriorCellMass
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (hε : 0 < ε)
    (cell : Fin (2 * m) → Z4) : ℝ :=
  ∫ v in
      r324SelectedInternalCell
        κp κm π selected ε hε cell,
    ‖ρ.r324MarkedResidualPhysicalInteriorCore
      ε L κp κm π selected v‖
    ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)

theorem r324MarkedResidualPhysicalInteriorCellMass_nonneg
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (hε : 0 < ε)
    (cell : Fin (2 * m) → Z4) :
    0 ≤ ρ.r324MarkedResidualPhysicalInteriorCellMass
      ε L κp κm π selected hε cell :=
  integral_nonneg fun _ => norm_nonneg _

/-- Exact cellwise ledger after all unmarked residual factors have been
separated and only the projected edge remains distinguished. -/
theorem r324MarkedResidualPhysicalInteriorCellMass_eq_projectedEdge
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (hε : 0 < ε)
    (cell : Fin (2 * m) → Z4) :
    ρ.r324MarkedResidualPhysicalInteriorCellMass
        ε L κp κm π selected hε cell =
      ∫ v in
          r324SelectedInternalCell
            κp κm π selected ε hε cell,
        r324SelectedInteriorSkeletonNormDensity κp κm v *
          ‖ρ.r324ProjectedCovarianceC ε L
            (v (r324ResidualMarkedLowerEndpoint selected) -
              v (r324ResidualMarkedUpperEndpoint π selected))‖ *
          ρ.r324MarkedResidualBlockUnselectedCovarianceMass
            ε κp κm π selected v *
          ‖ρ.r324UnmarkedResidualBlockProduct
            ε κp κm π selected v‖
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  unfold r324MarkedResidualPhysicalInteriorCellMass
  apply setIntegral_congr_fun
    (measurableSet_r324SelectedInternalCell
      κp κm π selected ε hε cell)
  intro v _hv
  exact
    ρ.norm_r324MarkedResidualPhysicalInteriorCore_eq_projectedEdge
      ε L κp κm π selected v

end SmoothCutoff

end

end Anderson4D
