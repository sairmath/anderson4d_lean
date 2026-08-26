import Anderson4D.DetParametrix.Paper42_Moment.R324MarkedResidualPhysicalBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointMajorantClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324SelectedOpenEdgeIntegration

/-!
# Cell integration after expanding only the marked residual edge

This file integrates the one-mode estimate from
`R324MarkedResidualPhysicalBridge` on the genuine selected internal cell.
Every unmarked covariance stays in physical space.  The masses are stated
as nonnegative extended integrals, so this Tonelli-safe step keeps the
Proposition 4.1 block collapse explicit as a separate premise.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open PlaneTree
open scoped ENNReal

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## Measurability of the physical complement -/

theorem measurable_r324MarkedResidualBlockUnselectedCovarianceMass
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    Measurable fun v : Fin (2 * m) → T4 =>
      ρ.r324MarkedResidualBlockUnselectedCovarianceMass
        ε κp κm π selected v := by
  unfold r324MarkedResidualBlockUnselectedCovarianceMass
  apply Finset.measurable_prod
  intro i _hi
  exact
    ((ρ.measurable_etaEpsT4 ε).comp
      ((measurable_pi_apply i).sub
        (measurable_pi_apply
          (momentCombinedPairing κp κm π i)))).complex_ofReal.norm

theorem measurable_r324UnmarkedResidualBlockProduct
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    Measurable fun v : Fin (2 * m) → T4 =>
      ρ.r324UnmarkedResidualBlockProduct
        ε κp κm π selected v := by
  unfold r324UnmarkedResidualBlockProduct
  apply Finset.measurable_prod
  intro B _hB
  apply Measurable.complex_ofReal
  unfold pairingCovarianceProductOn
  apply Finset.measurable_prod
  intro i _hi
  exact
    (ρ.measurable_etaEpsT4 ε).comp
      ((measurable_pi_apply i).sub
        (measurable_pi_apply
          (momentCombinedPairing κp κm π i)))

theorem measurable_r324MarkedResidualPhysicalComplementMass
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    Measurable fun v : Fin (2 * m) → T4 =>
      ρ.r324MarkedResidualPhysicalComplementMass
        ε κp κm π selected v := by
  have hleft :
      Measurable fun v : Fin (2 * m) → T4 =>
        r324RenormalizedInteriorCore κp
          (fun i => v (leftMomentIndex i)) := by
    exact
      (measurable_r324RenormalizedInteriorCore κp).comp
        (measurable_pi_lambda _ fun i =>
          measurable_pi_apply (leftMomentIndex i))
  have hright :
      Measurable fun v : Fin (2 * m) → T4 =>
        r324RenormalizedInteriorCore κm
          (fun i => v (rightMomentIndex i)) := by
    exact
      (measurable_r324RenormalizedInteriorCore κm).comp
        (measurable_pi_lambda _ fun i =>
          measurable_pi_apply (rightMomentIndex i))
  unfold r324MarkedResidualPhysicalComplementMass
    r324SelectedInteriorSkeletonNormDensity
  exact
    (((hleft.norm.mul hright.norm).mul
      (ρ.measurable_r324MarkedResidualBlockUnselectedCovarianceMass
        ε κp κm π selected)).mul
      (ρ.measurable_r324UnmarkedResidualBlockProduct
        ε κp κm π selected).norm)

/-! ## Exact one-mode norm ledger -/

/-- Norm of one retained covariance coefficient.  Evaluating the spatial
mode at zero makes the coefficient nature explicit. -/
def r324MarkedResidualHighModeCoefficientNorm
    (ε L : ℝ) (k : Z4) : ℝ :=
  ‖ρ.r324HighCovarianceModeTerm ε L 0 k‖

theorem r324MarkedResidualHighModeCoefficientNorm_nonneg
    (ε L : ℝ) (k : Z4) :
    0 ≤ ρ.r324MarkedResidualHighModeCoefficientNorm ε L k :=
  norm_nonneg _

theorem r324MarkedResidualHighModeCoefficientNorm_eq_covarianceModeCoeff
    {ε L : ℝ} {k : Z4}
    (hk : k ∈ r324HighModeSet ε L) :
    ρ.r324MarkedResidualHighModeCoefficientNorm ε L k =
      ‖ρ.covarianceModeCoeff ε k‖ := by
  simp [r324MarkedResidualHighModeCoefficientNorm,
    r324HighCovarianceModeTerm, hk,
    r324CovarianceModeTerm, norm_charT4]

theorem summable_r324MarkedResidualHighModeCoefficientNorm
    {ε : ℝ} (hε : 0 < ε) (L : ℝ) :
    Summable
      (ρ.r324MarkedResidualHighModeCoefficientNorm ε L) := by
  exact
    (ρ.summable_r324HighCovarianceModeTerm hε L 0).norm

theorem norm_r324HighCovarianceModeTerm_eq_coefficientNorm
    (ε L : ℝ) (z : T4) (k : Z4) :
    ‖ρ.r324HighCovarianceModeTerm ε L z k‖ =
      ρ.r324MarkedResidualHighModeCoefficientNorm ε L k := by
  classical
  by_cases hk : k ∈ r324HighModeSet ε L
  · simp only [r324HighCovarianceModeTerm, Set.indicator_of_mem hk,
      r324MarkedResidualHighModeCoefficientNorm,
      ρ.norm_r324CovarianceModeTerm]
  · simp [r324HighCovarianceModeTerm,
      r324MarkedResidualHighModeCoefficientNorm, hk]

theorem norm_r324MarkedResidualPhysicalOpenEdgeAmplitude
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    ‖ρ.r324MarkedResidualPhysicalOpenEdgeAmplitude
        ε κp κm π selected v‖ =
      ρ.r324MarkedResidualPhysicalComplementMass
        ε κp κm π selected v := by
  unfold r324MarkedResidualPhysicalOpenEdgeAmplitude
    r324MarkedResidualPhysicalComplementMass
    r324SelectedInteriorSkeletonNormDensity
  simp only [norm_mul,
    ρ.norm_r324MarkedResidualBlockUnselectedCovarianceProduct]

theorem norm_r324MarkedResidualPhysicalInteriorModeTerm_eq
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) (k : Z4) :
    ‖ρ.r324MarkedResidualPhysicalInteriorModeTerm
        ε L κp κm π selected v k‖ =
      ρ.r324MarkedResidualHighModeCoefficientNorm ε L k *
        ρ.r324MarkedResidualPhysicalComplementMass
          ε κp κm π selected v := by
  rw [
    ρ.r324MarkedResidualPhysicalInteriorModeTerm_eq_highMode_mul_amplitude,
    norm_mul,
    ρ.norm_r324HighCovarianceModeTerm_eq_coefficientNorm,
    ρ.norm_r324MarkedResidualPhysicalOpenEdgeAmplitude]

theorem measurable_norm_r324MarkedResidualPhysicalInteriorModeTerm
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (k : Z4) :
    Measurable fun v : Fin (2 * m) → T4 =>
      ‖ρ.r324MarkedResidualPhysicalInteriorModeTerm
        ε L κp κm π selected v k‖ := by
  have hmeas :
      Measurable fun v : Fin (2 * m) → T4 =>
        ρ.r324MarkedResidualHighModeCoefficientNorm ε L k *
          ρ.r324MarkedResidualPhysicalComplementMass
            ε κp κm π selected v :=
    measurable_const.mul
      (ρ.measurable_r324MarkedResidualPhysicalComplementMass
        ε κp κm π selected)
  convert hmeas using 1
  funext v
  exact
    ρ.norm_r324MarkedResidualPhysicalInteriorModeTerm_eq
      ε L κp κm π selected v k

/-! ## Tonelli-safe cell masses -/

/-- Extended `L¹` mass of one marked Fourier mode on a genuine selected
internal cell. -/
def r324MarkedResidualPhysicalInteriorModeCellLIntegral
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (hε : 0 < ε)
    (cell : Fin (2 * m) → Z4)
    (k : Z4) : ℝ≥0∞ :=
  ∫⁻ v in
      r324SelectedInternalCell
        κp κm π selected ε hε cell,
    ENNReal.ofReal
      ‖ρ.r324MarkedResidualPhysicalInteriorModeTerm
        ε L κp κm π selected v k‖
    ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)

/-- Extended physical-complement mass on the same genuine selected cell.
Its finiteness is exactly the analytic input still supplied by the
within-half Proposition 4.1 collapse. -/
def r324MarkedResidualPhysicalComplementCellLIntegral
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (hε : 0 < ε)
    (cell : Fin (2 * m) → Z4) : ℝ≥0∞ :=
  ∫⁻ v in
      r324SelectedInternalCell
        κp κm π selected ε hε cell,
    ENNReal.ofReal
      (ρ.r324MarkedResidualPhysicalComplementMass
        ε κp κm π selected v)
    ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)

/-- Exact separation of the retained coefficient from the physical
complement on one selected cell. -/
theorem r324MarkedResidualPhysicalInteriorModeCellLIntegral_eq
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (hε : 0 < ε)
    (cell : Fin (2 * m) → Z4)
    (k : Z4) :
    ρ.r324MarkedResidualPhysicalInteriorModeCellLIntegral
        ε L κp κm π selected hε cell k =
      ENNReal.ofReal
          (ρ.r324MarkedResidualHighModeCoefficientNorm ε L k) *
        ρ.r324MarkedResidualPhysicalComplementCellLIntegral
          ε κp κm π selected hε cell := by
  unfold r324MarkedResidualPhysicalInteriorModeCellLIntegral
    r324MarkedResidualPhysicalComplementCellLIntegral
  calc
    (∫⁻ v in
        r324SelectedInternalCell
          κp κm π selected ε hε cell,
      ENNReal.ofReal
        ‖ρ.r324MarkedResidualPhysicalInteriorModeTerm
          ε L κp κm π selected v k‖
      ∂Measure.pi fun _ : Fin (2 * m) => paperMeasure) =
        ∫⁻ v in
          r324SelectedInternalCell
            κp κm π selected ε hε cell,
        ENNReal.ofReal
            (ρ.r324MarkedResidualHighModeCoefficientNorm ε L k) *
          ENNReal.ofReal
            (ρ.r324MarkedResidualPhysicalComplementMass
              ε κp κm π selected v)
        ∂Measure.pi fun _ : Fin (2 * m) => paperMeasure := by
      apply lintegral_congr
      intro v
      rw [
        ρ.norm_r324MarkedResidualPhysicalInteriorModeTerm_eq,
        ENNReal.ofReal_mul
          (ρ.r324MarkedResidualHighModeCoefficientNorm_nonneg
            ε L k)]
    _ =
        ENNReal.ofReal
            (ρ.r324MarkedResidualHighModeCoefficientNorm ε L k) *
          (∫⁻ v in
            r324SelectedInternalCell
              κp κm π selected ε hε cell,
            ENNReal.ofReal
              (ρ.r324MarkedResidualPhysicalComplementMass
                ε κp κm π selected v)
            ∂Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
      rw [lintegral_const_mul'']
      exact
        (ρ.measurable_r324MarkedResidualPhysicalComplementMass
          ε κp κm π selected).ennreal_ofReal.aemeasurable

/-! ## The integrated central-frequency payoff -/

/-- The paper's uniform eighth-order payoff survives integration over
every genuine selected internal cell, while the complete unmarked
physical covariance structure stays inside the complement mass. -/
theorem
    exists_r324MarkedResidualPhysicalInteriorModeCellLIntegral_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m : ℕ} {ε L : ℝ}
        {κp κm : PartialPairing (Fin m)}
        {π : κp.singles ≃ κm.singles}
        {selected : R324ResidualCovarianceSlot κp}
        {hε : 0 < ε}
        {cell : Fin (2 * m) → Z4}
        {k : Z4},
        ε ≤ 1 / 4 →
        0 ≤ L →
        ρ.r324MarkedResidualPhysicalInteriorModeCellLIntegral
            ε L κp κm π selected hε cell k ≤
          ENNReal.ofReal
              (C * eighthOrderFrequencyDecay (ε ^ 2 * L)) *
            ρ.r324MarkedResidualPhysicalComplementCellLIntegral
              ε κp κm π selected hε cell := by
  obtain ⟨C, hC, hpoint⟩ :=
    ρ.exists_norm_r324MarkedResidualPhysicalInteriorModeTerm_le
  refine ⟨C, hC, ?_⟩
  intro m ε L κp κm π selected hε cell k hεsmall hL
  unfold r324MarkedResidualPhysicalInteriorModeCellLIntegral
    r324MarkedResidualPhysicalComplementCellLIntegral
  calc
    (∫⁻ v in
        r324SelectedInternalCell
          κp κm π selected ε hε cell,
      ENNReal.ofReal
        ‖ρ.r324MarkedResidualPhysicalInteriorModeTerm
          ε L κp κm π selected v k‖
      ∂Measure.pi fun _ : Fin (2 * m) => paperMeasure) ≤
        ∫⁻ v in
          r324SelectedInternalCell
            κp κm π selected ε hε cell,
        ENNReal.ofReal
          ((C * eighthOrderFrequencyDecay (ε ^ 2 * L)) *
            ρ.r324MarkedResidualPhysicalComplementMass
              ε κp κm π selected v)
        ∂Measure.pi fun _ : Fin (2 * m) => paperMeasure := by
      apply lintegral_mono
      intro v
      exact ENNReal.ofReal_le_ofReal
        (hpoint hε hεsmall hL)
    _ =
        ENNReal.ofReal
            (C * eighthOrderFrequencyDecay (ε ^ 2 * L)) *
          (∫⁻ v in
            r324SelectedInternalCell
              κp κm π selected ε hε cell,
            ENNReal.ofReal
              (ρ.r324MarkedResidualPhysicalComplementMass
                ε κp κm π selected v)
            ∂Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
      have hscale :
          0 ≤ C * eighthOrderFrequencyDecay (ε ^ 2 * L) :=
        mul_nonneg hC.le (eighthOrderFrequencyDecay_nonneg _)
      simp_rw [ENNReal.ofReal_mul hscale]
      rw [lintegral_const_mul'']
      exact
        (ρ.measurable_r324MarkedResidualPhysicalComplementMass
          ε κp κm π selected).ennreal_ofReal.aemeasurable

/-! ## Absolute mode summation on the cell -/

/-- Tonelli exchange for the absolute one-marked-edge mode family.  It
is valid before the physical complement is known finite. -/
theorem lintegral_tsum_norm_r324MarkedResidualPhysicalInteriorModeTerm
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (hε : 0 < ε)
    (cell : Fin (2 * m) → Z4) :
    (∫⁻ v in
        r324SelectedInternalCell
          κp κm π selected ε hε cell,
      ∑' k : Z4,
        ENNReal.ofReal
          ‖ρ.r324MarkedResidualPhysicalInteriorModeTerm
            ε L κp κm π selected v k‖
      ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) =
      ∑' k : Z4,
        ρ.r324MarkedResidualPhysicalInteriorModeCellLIntegral
          ε L κp κm π selected hε cell k := by
  unfold r324MarkedResidualPhysicalInteriorModeCellLIntegral
  exact lintegral_tsum fun k =>
    (ρ.measurable_norm_r324MarkedResidualPhysicalInteriorModeTerm
      ε L κp κm π selected k).ennreal_ofReal.aemeasurable

/-- Exact factorization of the total absolute mode mass. -/
theorem tsum_r324MarkedResidualPhysicalInteriorModeCellLIntegral
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (hε : 0 < ε)
    (cell : Fin (2 * m) → Z4) :
    (∑' k : Z4,
      ρ.r324MarkedResidualPhysicalInteriorModeCellLIntegral
        ε L κp κm π selected hε cell k) =
      (∑' k : Z4,
        ENNReal.ofReal
          (ρ.r324MarkedResidualHighModeCoefficientNorm ε L k)) *
        ρ.r324MarkedResidualPhysicalComplementCellLIntegral
          ε κp κm π selected hε cell := by
  simp_rw [
    ρ.r324MarkedResidualPhysicalInteriorModeCellLIntegral_eq
      ε L κp κm π selected hε cell]
  exact ENNReal.tsum_mul_right

/-- The retained coefficient series has finite extended mass. -/
theorem tsum_ofReal_r324MarkedResidualHighModeCoefficientNorm_lt_top
    {ε : ℝ} (hε : 0 < ε) (L : ℝ) :
    (∑' k : Z4,
      ENNReal.ofReal
        (ρ.r324MarkedResidualHighModeCoefficientNorm ε L k)) < ∞ := by
  exact
    (ρ.summable_r324MarkedResidualHighModeCoefficientNorm hε L)
      |>.tsum_ofReal_lt_top

/-- Finite complement mass implies absolute summability of the integrated
marked-mode family. -/
theorem tsum_r324MarkedResidualPhysicalInteriorModeCellLIntegral_lt_top
    {m : ℕ} {ε L : ℝ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (hε : 0 < ε)
    (cell : Fin (2 * m) → Z4)
    (hcomplement :
      ρ.r324MarkedResidualPhysicalComplementCellLIntegral
        ε κp κm π selected hε cell < ∞) :
    (∑' k : Z4,
      ρ.r324MarkedResidualPhysicalInteriorModeCellLIntegral
        ε L κp κm π selected hε cell k) < ∞ := by
  rw [
    ρ.tsum_r324MarkedResidualPhysicalInteriorModeCellLIntegral
      ε L κp κm π selected hε cell]
  exact ENNReal.mul_lt_top
    (ρ.tsum_ofReal_r324MarkedResidualHighModeCoefficientNorm_lt_top
      hε L)
    hcomplement

/-! ## Interface to the existing primitive-word consumer -/

/-- The exact coefficient extracted by the physical marked-edge bridge
feeds the already proved one-open-edge primitive consumer. -/
theorem exists_r324MarkedResidualHighModePrimitiveConsumer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {t : PlaneTree} {m M : ℕ}
        {κ : PartialPairing (Fin m)}
        {a b : Fin m} {w : Fin m → HeppLeaf t}
        {Nm : HeppMarking t}
        {z : HeppLeaf t → Fin 4 → ℤ}
        {ε L : ℝ} {k : Z4},
        0 < m →
        κ a = b →
        a < b →
        κ.IsFull →
        IsPrimitive κ →
        (∀ i : Fin m, i ≠ a → i ≠ b →
          w i = w (κ i)) →
        IsAdmissible Nm M z →
        0 < ε →
        ε ≤ 1 / 4 →
        0 ≤ L →
        1 ≤ ε ^ 2 * L →
        k ∈ r324HighModeSet ε L →
        (M : ℝ) ≤ ε⁻¹ →
        NoProperLeafBlock
            (openEdgeAugmentedWord w a b) ∧
          ρ.r324MarkedResidualHighModeCoefficientNorm ε L k *
              heppChainWeight z w ≤
            C * eighthOrderFrequencyDecay (ε ^ 2 * L) *
              heppChainWeight z
                (openEdgeAugmentedWord w a b) := by
  obtain ⟨C, hC, hconsumer⟩ :=
    ρ.exists_selectedOpenEdgePrimitiveConsumer
  refine ⟨C, hC, ?_⟩
  intro t m M κ a b w Nm z ε L k hm hκab hab hfull
    hprimitive hrespect hadm hε hεsmall hL hlarge hk hM
  simpa only [
      ρ.r324MarkedResidualHighModeCoefficientNorm_eq_covarianceModeCoeff
        hk] using
    hconsumer hm hκab hab hfull hprimitive hrespect hadm hε
      hεsmall hL hlarge hk hM

end SmoothCutoff

end

end Anderson4D
