import Anderson4D.DetParametrix.Paper42_Moment.R324SelectedCellEndpointFactorization
import Anderson4D.DetParametrix.Paper42_Moment.R324SelectedCellNormFactorization

/-!
# Selected coefficient ledger after endpoint integration

After the four endpoint Fourier integrals have been evaluated, the
remaining selected core contains only the two interior Green profiles
and the fixed covariance configuration.  This file separates its
constant Fourier coefficient weight exactly.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- Bare norm of the two endpoint-independent Green profiles. -/
def r324SelectedInteriorSkeletonNormDensity
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (v : Fin (2 * m) → T4) : ℝ :=
  ‖r324RenormalizedInteriorCore κp
      (fun i => v (leftMomentIndex i))‖ *
    ‖r324RenormalizedInteriorCore κm
      (fun i => v (rightMomentIndex i))‖

theorem r324SelectedInteriorSkeletonNormDensity_nonneg
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (v : Fin (2 * m) → T4) :
    0 ≤ r324SelectedInteriorSkeletonNormDensity κp κm v :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Exact norm separation for the endpoint-independent selected core.
The canonical selector guarantee is used only to replace the guarded
high factor by the original fixed Fourier factor. -/
theorem norm_r324SelectedEndpointCore_eq_weight_mul_interior
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (ω :
      R324NonzeroCombinedFourierConfiguration
        ρ ε α β κp κm π)
    (v : Fin (2 * m) → T4) :
    ‖ρ.r324SelectedEndpointCore
        ε κp κm π ω.1
        (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
          ε α β κp κm π hexternal hε hε1 hmtrunc ω)
        ‖z4EuclideanFrequency (α + β)‖ v‖ =
      ‖ρ.covarianceModeCoeff ε
          (ω.1
            (r324CrossSlotPairIndex κp κm π
              (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
                ε α β κp κm π hexternal
                  hε hε1 hmtrunc ω)))‖ *
        ρ.r324SelectedUnselectedConfigurationWeight
          ε κp κm π ω.1
          (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
            ε α β κp κm π hexternal hε hε1 hmtrunc ω) *
        r324SelectedInteriorSkeletonNormDensity κp κm v := by
  unfold r324SelectedEndpointCore
    r324SelectedInteriorSkeletonNormDensity
  rw [
    ρ.r324SelectedHighCovarianceConfigurationTerm_eq
      ε α β κp κm π hexternal hε hε1 hmtrunc ω v,
    norm_mul, norm_mul,
    ρ.norm_r324CovarianceFourierConfigurationTerm,
    ρ.r324CovarianceConfigurationWeight_eq_selected_mul_unselected
      ε κp κm π ω.1
      (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
        ε α β κp κm π hexternal hε hε1 hmtrunc ω)]
  ring

/-- Bare interior-profile mass on one actual selected internal cell. -/
def r324SelectedInteriorSkeletonCellMass
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (ε : ℝ) (hε : 0 < ε)
    (cell : Fin (2 * m) → Z4) : ℝ :=
  ∫ v in
      r324SelectedInternalCell
        κp κm π selected ε hε cell,
    r324SelectedInteriorSkeletonNormDensity κp κm v
    ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)

theorem r324SelectedInteriorSkeletonCellMass_nonneg
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (ε : ℝ) (hε : 0 < ε)
    (cell : Fin (2 * m) → Z4) :
    0 ≤ r324SelectedInteriorSkeletonCellMass
      κp κm π selected ε hε cell :=
  integral_nonneg fun v =>
    r324SelectedInteriorSkeletonNormDensity_nonneg κp κm v

/-- Exact integral of the selected-core norm on one genuine internal
cell. -/
theorem integral_norm_r324SelectedEndpointCore_on_cell
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (ω :
      R324NonzeroCombinedFourierConfiguration
        ρ ε α β κp κm π)
    (cell : Fin (2 * m) → Z4) :
    (∫ v in
        r324SelectedInternalCell κp κm π
          (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
            ε α β κp κm π hexternal hε hε1 hmtrunc ω)
          ε hε cell,
      ‖ρ.r324SelectedEndpointCore
        ε κp κm π ω.1
        (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
          ε α β κp κm π hexternal hε hε1 hmtrunc ω)
        ‖z4EuclideanFrequency (α + β)‖ v‖
      ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) =
      ‖ρ.covarianceModeCoeff ε
          (ω.1
            (r324CrossSlotPairIndex κp κm π
              (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
                ε α β κp κm π hexternal
                  hε hε1 hmtrunc ω)))‖ *
        ρ.r324SelectedUnselectedConfigurationWeight
          ε κp κm π ω.1
          (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
            ε α β κp κm π hexternal hε hε1 hmtrunc ω) *
        r324SelectedInteriorSkeletonCellMass
          κp κm π
          (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
            ε α β κp κm π hexternal hε hε1 hmtrunc ω)
          ε hε cell := by
  unfold r324SelectedInteriorSkeletonCellMass
  rw [← integral_const_mul]
  apply setIntegral_congr_fun
    (measurableSet_r324SelectedInternalCell
      κp κm π
      (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
        ε α β κp κm π hexternal hε hε1 hmtrunc ω)
      ε hε cell)
  intro v _hv
  exact
    ρ.norm_r324SelectedEndpointCore_eq_weight_mul_interior
      ε α β κp κm π hexternal hε hε1 hmtrunc ω v

end SmoothCutoff

end

end Anderson4D
