import Anderson4D.DetParametrix.Paper42_Moment.R324SelectedCellEndpointFactorization
import Anderson4D.DetParametrix.Paper42_Moment.R324SelectedOpenEdgeIntegration
import Anderson4D.DetParametrix.Paper42_Moment.R324SingleProjectedMarkedPhysicalBridge

/-!
# Exact signed factorization on a canonical selector fibre

The canonical first-large-slot selector depends on every Fourier mode in a
configuration.  Consequently its fibre must not be replaced by an
unrestricted projected-covariance series.  This module keeps the existing
selector subtype literally in every declaration and performs only the
termwise signed factorization at the selected mode.

The resulting restricted `tsum` is exact.  Passing from it to the complete
physical complement is a later inequality, proved block by block; no such
enlargement is encoded here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- One signed interior mode on the genuine canonical-selector subtype.
The selected high mode is exposed, while the product of all other fixed
modes remains intact and inside the same signed term. -/
def r324SelectorRestrictedSignedInteriorMode
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (i : R324ResidualCovarianceSlot κp)
    (ω :
      R324SelectedCrossSlotConfigurationFiber
        ρ ε α β κp κm π hexternal
        hε hε1 hmtrunc i)
    (v : Fin (2 * m) → T4) : ℂ :=
  let selected :=
    ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
      ε α β κp κm π hexternal hε hε1 hmtrunc ω.1
  r324RenormalizedInteriorCore κp
      (fun j => v (leftMomentIndex j)) *
    r324RenormalizedInteriorCore κm
      (fun j => v (rightMomentIndex j)) *
    ρ.r324HighCovarianceModeTerm
      ε ‖z4EuclideanFrequency (α + β)‖
      (v (r324ResidualMarkedLowerEndpoint selected) -
        v (r324ResidualMarkedUpperEndpoint π selected))
      (ω.1.1
        (r324CrossSlotPairIndex κp κm π selected)) *
    ρ.r324SelectedHighUnselectedPairModeProduct
      ε ‖z4EuclideanFrequency (α + β)‖
      κp κm π ω.1.1 selected v

/-- Every member of the restricted selector fibre is exactly its signed
selected-mode factorization.  The subtype proof is neither discarded nor
weakened. -/
theorem r324SelectedEndpointCore_eq_selectorRestrictedSignedInteriorMode
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (i : R324ResidualCovarianceSlot κp)
    (ω :
      R324SelectedCrossSlotConfigurationFiber
        ρ ε α β κp κm π hexternal
        hε hε1 hmtrunc i)
    (v : Fin (2 * m) → T4) :
    let selected :=
      ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
        ε α β κp κm π hexternal hε hε1 hmtrunc ω.1
    ρ.r324SelectedEndpointCore
        ε κp κm π ω.1.1 selected
        ‖z4EuclideanFrequency (α + β)‖ v =
      ρ.r324SelectorRestrictedSignedInteriorMode
        ε α β κp κm π hexternal
        hε hε1 hmtrunc i ω v := by
  dsimp only
  unfold r324SelectedEndpointCore
    r324SelectorRestrictedSignedInteriorMode
  rw [
    ρ.r324SelectedHighCovarianceConfigurationTerm_eq_marked_mul_unselected]
  ring

/-- **Subtype-retaining exact series bridge.**  The restricted signed
selector series is unchanged by exposing its selected high mode termwise.
No summability hypothesis is needed for this termwise `tsum` identity. -/
theorem tsum_r324SelectedEndpointCore_eq_selectorRestrictedSigned
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (i : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    (∑' ω :
        R324SelectedCrossSlotConfigurationFiber
          ρ ε α β κp κm π hexternal
          hε hε1 hmtrunc i,
      let selected :=
        ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
          ε α β κp κm π hexternal hε hε1 hmtrunc ω.1
      ρ.r324SelectedEndpointCore
        ε κp κm π ω.1.1 selected
        ‖z4EuclideanFrequency (α + β)‖ v) =
      ∑' ω :
          R324SelectedCrossSlotConfigurationFiber
            ρ ε α β κp κm π hexternal
            hε hε1 hmtrunc i,
        ρ.r324SelectorRestrictedSignedInteriorMode
          ε α β κp κm π hexternal
          hε hε1 hmtrunc i ω v := by
  apply tsum_congr
  intro ω
  exact
    ρ.r324SelectedEndpointCore_eq_selectorRestrictedSignedInteriorMode
      ε α β κp κm π hexternal
      hε hε1 hmtrunc i ω v

end SmoothCutoff

end

end Anderson4D
