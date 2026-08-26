import Anderson4D.DetParametrix.Paper42_Moment.R324SelectedCellTreeCover

/-!
# Norm factorization on one selected R-324 physical cell

Before estimating a cell integral, its Fourier coefficient ledger can be
separated exactly from the two deterministic Green skeletons.  The
selected high coefficient is then split from all unselected coefficients.

This file proves those equalities and the resulting norm-of-integral
bound on the genuine physical cell fibre.  That last inequality takes a
norm before integrating the four endpoint phases, so it is only a
uniform-branch ledger: it must not be used for the decaying branch of
(3.24), where the endpoint-first route in
`R324SelectedCellEndpointFactorization` is mandatory.  No singular Green
estimate, cell-volume bound, tree-incidence denominator, or automorphism
factor is assumed or hidden here.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## The selected coefficient ledger -/

/-- Product of the absolute Fourier coefficients away from the selected
cross slot. -/
def r324SelectedUnselectedConfigurationWeight
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (selected : R324ResidualCovarianceSlot κp) : ℝ :=
  ∏ j ∈
      (Finset.univ.erase
        (r324CrossSlotPairIndex κp κm π selected)),
    ‖ρ.covarianceModeCoeff ε (q j)‖

theorem r324SelectedUnselectedConfigurationWeight_nonneg
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (selected : R324ResidualCovarianceSlot κp) :
    0 ≤ ρ.r324SelectedUnselectedConfigurationWeight
      ε κp κm π q selected :=
  Finset.prod_nonneg fun _ _ => norm_nonneg _

/-- Exact extraction of the canonical selected coefficient from the
complete configuration weight. -/
theorem r324CovarianceConfigurationWeight_eq_selected_mul_unselected
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (selected : R324ResidualCovarianceSlot κp) :
    ρ.r324CovarianceConfigurationWeight ε
        (momentCombinedPairing κp κm π) q =
      ‖ρ.covarianceModeCoeff ε
          (q
            (r324CrossSlotPairIndex
              κp κm π selected))‖ *
        ρ.r324SelectedUnselectedConfigurationWeight
          ε κp κm π q selected := by
  unfold r324CovarianceConfigurationWeight
    r324SelectedUnselectedConfigurationWeight
  exact
    (Finset.mul_prod_erase Finset.univ
      (fun j => ‖ρ.covarianceModeCoeff ε (q j)‖)
      (Finset.mem_univ
        (r324CrossSlotPairIndex
          κp κm π selected))).symm

/-! ## The genuine skeleton cell mass -/

/-- Nonnegative two-skeleton density after discarding the unit Fourier
phase and all configuration coefficients. -/
def r324SelectedSkeletonNormDensity
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (p : R324PhysicalPoint m) : ℝ :=
  let κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull} :=
    ⟨momentCombinedPairing κp κm π,
      momentCombinedPairing_isFull κp κm π⟩
  let e := (momentContractionEquivFullPairing m).symm κ
  ‖renormalizedGreenSkeleton e.1
      (assemble p.1 p.2.1
        fun i => p.2.2.2.2 (leftMomentIndex i))‖ *
    ‖renormalizedGreenSkeleton e.2.1
      (assemble p.2.2.1 p.2.2.2.1
        fun i => p.2.2.2.2 (rightMomentIndex i))‖

theorem r324SelectedSkeletonNormDensity_nonneg
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (p : R324PhysicalPoint m) :
    0 ≤ r324SelectedSkeletonNormDensity
      κp κm π p :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Integral of the bare two-skeleton norm on one genuine selected
physical cell. -/
def r324SelectedSkeletonCellMass
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (ε : ℝ) (hε : 0 < ε)
    (cell : Fin (2 * m) → Z4) : ℝ :=
  ∫ p in
      (r324SelectedPhysicalOpenEdgeCells
        κp κm π selected ε hε).index ⁻¹' {cell},
    r324SelectedSkeletonNormDensity
      κp κm π p
    ∂(r324PhysicalMeasure m)

theorem r324SelectedSkeletonCellMass_nonneg
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (ε : ℝ) (hε : 0 < ε)
    (cell : Fin (2 * m) → Z4) :
    0 ≤ r324SelectedSkeletonCellMass
      κp κm π selected ε hε cell := by
  exact integral_nonneg fun p =>
    r324SelectedSkeletonNormDensity_nonneg
      κp κm π p

/-! ## Exact cellwise factorization -/

/-- Pointwise norm of the selected physical integrand is the constant
configuration weight times the bare two-skeleton density. -/
theorem norm_r324SelectedHighFullPairingFourierIntegrand_eq_weight_mul_skeleton
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
    (p : R324PhysicalPoint m) :
    ‖r324Flatten
        (ρ.r324SelectedHighFullPairingFourierIntegrand
          ε α β κp κm π hexternal hε hε1 hmtrunc ω)
        p‖ =
      ρ.r324CovarianceConfigurationWeight ε
          (momentCombinedPairing κp κm π) ω.1 *
        r324SelectedSkeletonNormDensity
          κp κm π p := by
  unfold r324Flatten
  rw [ρ.r324SelectedHighFullPairingFourierIntegrand_eq
    ε α β κp κm π hexternal hε hε1 hmtrunc
    ω p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2]
  unfold r324FullPairingFourierIntegrand
    r324SelectedSkeletonNormDensity
  dsimp only
  rw [norm_mul, norm_mul, norm_mul]
  have hphase :
      ‖momentFourierPhase α β
        p.1 p.2.1 p.2.2.1 p.2.2.2.1‖ = 1 := by
    unfold momentFourierPhase
    simp only [norm_mul, norm_charT4, mul_one]
  rw [hphase, one_mul,
    ρ.norm_r324CovarianceFourierConfigurationTerm]
  ring

/-- Exact integral of the pointwise norm on one genuine selected cell. -/
theorem integral_norm_r324SelectedHighFullPairingFourierIntegrand_on_cell
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
    (∫ p in
        (r324SelectedPhysicalOpenEdgeCells
          κp κm π
          (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
            ε α β κp κm π hexternal
              hε hε1 hmtrunc ω)
          ε hε).index ⁻¹' {cell},
      ‖r324Flatten
        (ρ.r324SelectedHighFullPairingFourierIntegrand
          ε α β κp κm π hexternal hε hε1 hmtrunc ω)
        p‖
      ∂(r324PhysicalMeasure m)) =
      ρ.r324CovarianceConfigurationWeight ε
          (momentCombinedPairing κp κm π) ω.1 *
        r324SelectedSkeletonCellMass
          κp κm π
          (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
            ε α β κp κm π hexternal
              hε hε1 hmtrunc ω)
          ε hε cell := by
  unfold r324SelectedSkeletonCellMass
  rw [← integral_const_mul]
  apply setIntegral_congr_fun
  · exact
      (r324SelectedPhysicalOpenEdgeCells
        κp κm π
        (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
          ε α β κp κm π hexternal
            hε hε1 hmtrunc ω)
        ε hε).measurable_fiber cell
  · intro p _hp
    exact
      ρ.norm_r324SelectedHighFullPairingFourierIntegrand_eq_weight_mul_skeleton
        ε α β κp κm π hexternal hε hε1
        hmtrunc ω p

/-- The norm of one genuine selected cell integral is bounded by the
selected coefficient, the remaining coefficient ledger, and the exact
bare skeleton cell mass. -/
theorem norm_integral_r324SelectedHighFullPairingFourierIntegrand_on_cell_le
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
    ‖∫ p in
        (r324SelectedPhysicalOpenEdgeCells
          κp κm π
          (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
            ε α β κp κm π hexternal
              hε hε1 hmtrunc ω)
          ε hε).index ⁻¹' {cell},
      r324Flatten
        (ρ.r324SelectedHighFullPairingFourierIntegrand
          ε α β κp κm π hexternal hε hε1 hmtrunc ω)
        p
      ∂(r324PhysicalMeasure m)‖ ≤
      ‖ρ.covarianceModeCoeff ε
          (ω.1
            (r324CrossSlotPairIndex
              κp κm π
              (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
                ε α β κp κm π hexternal
                  hε hε1 hmtrunc ω)))‖ *
        ρ.r324SelectedUnselectedConfigurationWeight
          ε κp κm π ω.1
          (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
            ε α β κp κm π hexternal
              hε hε1 hmtrunc ω) *
        r324SelectedSkeletonCellMass
          κp κm π
          (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
            ε α β κp κm π hexternal
              hε hε1 hmtrunc ω)
          ε hε cell := by
  calc
    _ ≤
        ∫ p in
            (r324SelectedPhysicalOpenEdgeCells
              κp κm π
              (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
                ε α β κp κm π hexternal
                  hε hε1 hmtrunc ω)
              ε hε).index ⁻¹' {cell},
          ‖r324Flatten
            (ρ.r324SelectedHighFullPairingFourierIntegrand
              ε α β κp κm π hexternal
                hε hε1 hmtrunc ω) p‖
          ∂(r324PhysicalMeasure m) :=
      norm_integral_le_integral_norm _
    _ =
        ρ.r324CovarianceConfigurationWeight ε
            (momentCombinedPairing κp κm π) ω.1 *
          r324SelectedSkeletonCellMass
            κp κm π
            (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
              ε α β κp κm π hexternal
                hε hε1 hmtrunc ω)
            ε hε cell :=
      ρ.integral_norm_r324SelectedHighFullPairingFourierIntegrand_on_cell
        ε α β κp κm π hexternal hε hε1
        hmtrunc ω cell
    _ = _ := by
      rw [
        ρ.r324CovarianceConfigurationWeight_eq_selected_mul_unselected
          ε κp κm π ω.1
          (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
            ε α β κp κm π hexternal
              hε hε1 hmtrunc ω)]

end SmoothCutoff

end

end Anderson4D
