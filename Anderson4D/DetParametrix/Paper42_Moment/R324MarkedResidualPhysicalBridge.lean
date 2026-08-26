import Anderson4D.DetParametrix.Paper42_Moment.R324MarkedResidualPhysicalInteriorCell

/-!
# Fourier bridge for the marked residual physical core

The within-half phase of R-324 must be completed on the physical side,
before the central-frequency covariance is expanded.  This file records
the exact next representation-order step for the resulting marked
residual object:

* every unmarked residual block remains a complete physical covariance
  product;
* only the unique marked covariance is expanded into Fourier modes; and
* the signed left and right Green profiles remain outside that series.

No estimate for the original moment and no reduction-output hypothesis is
used here.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- One Fourier mode of the marked residual physical interior core.

All covariances outside the marked block, and every unselected covariance
inside the marked block, remain complete physical `etaEpsT4` factors. -/
def r324MarkedResidualPhysicalInteriorModeTerm
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) (k : Z4) : ℂ :=
  r324RenormalizedInteriorCore κp
      (fun i => v (leftMomentIndex i)) *
    r324RenormalizedInteriorCore κm
      (fun i => v (rightMomentIndex i)) *
    ρ.r324MarkedResidualBlockModeTerm
      ε L κp κm π selected v k *
    ρ.r324UnmarkedResidualBlockProduct
      ε κp κm π selected v

/-- The complete signed amplitude outside the one surviving Fourier mode.
It retains every unselected covariance as a physical factor. -/
def r324MarkedResidualPhysicalOpenEdgeAmplitude
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) : ℂ :=
  r324RenormalizedInteriorCore κp
      (fun i => v (leftMomentIndex i)) *
    r324RenormalizedInteriorCore κm
      (fun i => v (rightMomentIndex i)) *
    ρ.r324MarkedResidualBlockUnselectedCovarianceProduct
      ε κp κm π selected v *
    ρ.r324UnmarkedResidualBlockProduct
      ε κp κm π selected v

/-- Exact consumer-facing factorization: the sole expanded factor is the
high Fourier mode on the marked cross edge. -/
theorem r324MarkedResidualPhysicalInteriorModeTerm_eq_highMode_mul_amplitude
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) (k : Z4) :
    ρ.r324MarkedResidualPhysicalInteriorModeTerm
        ε L κp κm π selected v k =
      ρ.r324HighCovarianceModeTerm ε L
          (v (r324ResidualMarkedLowerEndpoint selected) -
            v (r324ResidualMarkedUpperEndpoint π selected)) k *
        ρ.r324MarkedResidualPhysicalOpenEdgeAmplitude
          ε κp κm π selected v := by
  unfold r324MarkedResidualPhysicalInteriorModeTerm
    r324MarkedResidualPhysicalOpenEdgeAmplitude
    r324MarkedResidualBlockModeTerm
  ring

/-- The one-marked-edge mode family is absolutely summable. -/
theorem summable_r324MarkedResidualPhysicalInteriorModeTerm
    {m : ℕ} {ε : ℝ} (hε : 0 < ε) (L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    Summable
      (ρ.r324MarkedResidualPhysicalInteriorModeTerm
        ε L κp κm π selected v) := by
  let amplitude : ℂ :=
    r324RenormalizedInteriorCore κp
        (fun i => v (leftMomentIndex i)) *
      r324RenormalizedInteriorCore κm
        (fun i => v (rightMomentIndex i))
  have hmode :=
    ρ.summable_r324MarkedResidualBlockModeTerm
      hε L κp κm π selected v
  have hscaled :=
    (hmode.mul_left amplitude).mul_right
      (ρ.r324UnmarkedResidualBlockProduct
        ε κp κm π selected v)
  exact hscaled.congr fun k => by
    unfold r324MarkedResidualPhysicalInteriorModeTerm
    dsimp only [amplitude]

/-- **Exact representation-order bridge.**

After the physical within-half collapse has produced the marked residual
core, expanding only the surviving marked covariance gives this `Z4`
series.  In particular, no covariance from an unmarked primitive block is
Fourier-expanded or separated from its Green skeleton. -/
theorem r324MarkedResidualPhysicalInteriorCore_eq_tsum_modes
    {m : ℕ} {ε : ℝ} (hε : 0 < ε) (L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    ρ.r324MarkedResidualPhysicalInteriorCore
        ε L κp κm π selected v =
      ∑' k : Z4,
        ρ.r324MarkedResidualPhysicalInteriorModeTerm
          ε L κp κm π selected v k := by
  rw [
    ρ.r324MarkedResidualPhysicalInteriorCore_eq_residualFactored]
  unfold r324ResidualFactoredMarkedPhysicalInteriorCore
  rw [
    ρ.r324MarkedPairingCovarianceProductOn_markedBlock_eq_tsum_modes
      hε L κp κm π selected v]
  unfold
    r324MarkedResidualPhysicalInteriorModeTerm
  rw [tsum_mul_right, tsum_mul_left]

/-- Absolute physical mass left after deleting only the selected projected
edge.  The unselected covariances are still grouped by their genuine
physical primitive blocks. -/
def r324MarkedResidualPhysicalComplementMass
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) : ℝ :=
  r324SelectedInteriorSkeletonNormDensity κp κm v *
    ρ.r324MarkedResidualBlockUnselectedCovarianceMass
      ε κp κm π selected v *
    ‖ρ.r324UnmarkedResidualBlockProduct
      ε κp κm π selected v‖

theorem r324MarkedResidualPhysicalComplementMass_nonneg
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    0 ≤ ρ.r324MarkedResidualPhysicalComplementMass
      ε κp κm π selected v := by
  unfold r324MarkedResidualPhysicalComplementMass
    r324SelectedInteriorSkeletonNormDensity
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (ρ.r324MarkedResidualBlockUnselectedCovarianceMass_nonneg
        ε κp κm π selected v))
    (norm_nonneg _)

/-- The exact single-mode physical term carries the paper's central
eighth-order decay.  Crucially, the remaining factor is the complete
physical complement mass, not a product of absolute Fourier coefficient
sums. -/
theorem
    exists_norm_r324MarkedResidualPhysicalInteriorModeTerm_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m : ℕ} {ε L : ℝ}
        {κp κm : PartialPairing (Fin m)}
        {π : κp.singles ≃ κm.singles}
        {selected : R324ResidualCovarianceSlot κp}
        {v : Fin (2 * m) → T4} {k : Z4},
        0 < ε →
        ε ≤ 1 / 4 →
        0 ≤ L →
        ‖ρ.r324MarkedResidualPhysicalInteriorModeTerm
            ε L κp κm π selected v k‖ ≤
          C * eighthOrderFrequencyDecay (ε ^ 2 * L) *
            ρ.r324MarkedResidualPhysicalComplementMass
              ε κp κm π selected v := by
  obtain ⟨C, hC, hmode⟩ :=
    ρ.exists_norm_mul_r324MarkedResidualBlockModeTerm_le
  refine ⟨C, hC, ?_⟩
  intro m ε L κp κm π selected v k hε hεsmall hL
  let amplitude : ℂ :=
    (r324RenormalizedInteriorCore κp
        (fun i => v (leftMomentIndex i)) *
      r324RenormalizedInteriorCore κm
        (fun i => v (rightMomentIndex i))) *
      ρ.r324UnmarkedResidualBlockProduct
        ε κp κm π selected v
  have h :=
    hmode (m := m) (ε := ε) (L := L)
      (κp := κp) (κm := κm) (π := π)
      (selected := selected) (v := v) (k := k)
      (amplitude := amplitude) hε hεsmall hL
  simpa only [
      r324MarkedResidualPhysicalInteriorModeTerm,
      r324MarkedResidualPhysicalComplementMass,
      r324SelectedInteriorSkeletonNormDensity,
      amplitude, norm_mul, mul_assoc, mul_left_comm, mul_comm] using h

end SmoothCutoff

end

end Anderson4D
