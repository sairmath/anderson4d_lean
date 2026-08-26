import Anderson4D.DetParametrix.Paper42_Moment.R324InternalCellFubini

/-!
# Endpoint-first factorization on a selected R-324 cell

The selected open-edge cells constrain only the internal doubled tuple.
We first move that restriction outside the four endpoint integrals, then
evaluate those Fourier integrals exactly.  Thus the two
`⟨α⟩⁻⁴ ⟨β⟩⁻⁴` endpoint factors are retained before any norm is taken.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- The contraction triple determined by the displayed left, right, and
cross pairing data. -/
def r324SelectedMomentContraction
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    MomentContraction m :=
  ⟨κp, ⟨κm, π⟩⟩

/-- Interior core of one genuine canonically selected Fourier
configuration. -/
def r324SelectedEndpointCore
    {m : ℕ}
    (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ)
    (v : Fin (2 * m) → T4) : ℂ :=
  r324RenormalizedInteriorCore κp
      (fun i => v (leftMomentIndex i)) *
    r324RenormalizedInteriorCore κm
      (fun i => v (rightMomentIndex i)) *
    ρ.r324SelectedHighCovarianceConfigurationTerm
      ε L κp κm π q selected v

/-- Pointwise endpoint-separated form of a selected fixed
configuration. -/
theorem r324SelectedHighFullPairingFourierIntegrand_eq_endpointSeparated
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (ω :
      R324NonzeroCombinedFourierConfiguration
        ρ ε α β κp κm π)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    ρ.r324SelectedHighFullPairingFourierIntegrand
        ε α β κp κm π hexternal hε hε1 hmtrunc
        ω x y z w v =
      r324EndpointSeparatedIntegrand α β
        (r324ContractionEndpointAnchors hm
          (r324SelectedMomentContraction κp κm π) v)
        (r324ContractionEndpointFlags
          (r324SelectedMomentContraction κp κm π))
        (ρ.r324SelectedEndpointCore
          ε κp κm π ω.1
          (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
            ε α β κp κm π hexternal hε hε1 hmtrunc ω)
          ‖z4EuclideanFrequency (α + β)‖ v)
        x y z w := by
  let e : MomentContraction m :=
    r324SelectedMomentContraction κp κm π
  have he :
      (momentContractionEquivFullPairing m).symm
          ⟨momentCombinedPairing κp κm π,
            momentCombinedPairing_isFull κp κm π⟩ =
        e := by
    change
      (momentContractionEquivFullPairing m).symm
          (momentContractionEquivFullPairing m e) = e
    exact Equiv.symm_apply_apply _ e
  unfold r324SelectedHighFullPairingFourierIntegrand
  dsimp only
  rw [he]
  dsimp only [e, r324SelectedMomentContraction]
  rw [
    renormalizedGreenSkeleton_eq_endpointKernels_mul_core
      hm κp x y (fun i => v (leftMomentIndex i)),
    renormalizedGreenSkeleton_eq_endpointKernels_mul_core
      hm κm z w (fun i => v (rightMomentIndex i))]
  unfold r324EndpointSeparatedIntegrand
    r324SelectedEndpointCore
    momentFourierPhase
  simp only [r324ContractionEndpointAnchors_zero,
    r324ContractionEndpointAnchors_one,
    r324ContractionEndpointAnchors_two,
    r324ContractionEndpointAnchors_three,
    r324ContractionEndpointFlags_zero,
    r324ContractionEndpointFlags_one,
    r324ContractionEndpointFlags_two,
    r324ContractionEndpointFlags_three]
  ring

/-- The genuine measurable internal cell selected by one open-edge word. -/
def r324SelectedInternalCell
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (ε : ℝ) (hε : 0 < ε)
    (cell : Fin (2 * m) → Z4) :
    Set (Fin (2 * m) → T4) :=
  (r324MarkedResidualOpenEdgeCells
    κp κm π selected ε hε).index ⁻¹' {cell}

theorem measurableSet_r324SelectedInternalCell
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (ε : ℝ) (hε : 0 < ε)
    (cell : Fin (2 * m) → Z4) :
    MeasurableSet
      (r324SelectedInternalCell
        κp κm π selected ε hε cell) :=
  (r324MarkedResidualOpenEdgeCells
    κp κm π selected ε hε).measurable_fiber cell

/-- The full physical cell fibre is literally the preimage of the
corresponding internal cell. -/
theorem r324SelectedPhysicalCell_eq_internal_preimage
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (ε : ℝ) (hε : 0 < ε)
    (cell : Fin (2 * m) → Z4) :
    (r324SelectedPhysicalOpenEdgeCells
        κp κm π selected ε hε).index ⁻¹' {cell} =
      r324InternalCoordinate ⁻¹'
        r324SelectedInternalCell
          κp κm π selected ε hε cell := by
  rfl

/-- Exact endpoint-first formula for one genuine selected cell integral. -/
theorem integral_r324SelectedHigh_on_cell_eq_endpointCoefficients
    {m : ℕ} (hm : 0 < m)
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
            ε α β κp κm π hexternal hε hε1 hmtrunc ω)
          ε hε).index ⁻¹' {cell},
      r324Flatten
        (ρ.r324SelectedHighFullPairingFourierIntegrand
          ε α β κp κm π hexternal hε hε1 hmtrunc ω) p
      ∂(r324PhysicalMeasure m)) =
      ∫ v in
        r324SelectedInternalCell κp κm π
          (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
            ε α β κp κm π hexternal hε hε1 hmtrunc ω)
          ε hε cell,
        r324EndpointCoefficient α
            ((r324ContractionEndpointAnchors hm
              (r324SelectedMomentContraction κp κm π) v) 0).1
            ((r324ContractionEndpointAnchors hm
              (r324SelectedMomentContraction κp κm π) v) 0).2
            ((r324ContractionEndpointFlags
              (r324SelectedMomentContraction κp κm π)) 0) *
          (r324EndpointCoefficient β
            ((r324ContractionEndpointAnchors hm
              (r324SelectedMomentContraction κp κm π) v) 1).1
            ((r324ContractionEndpointAnchors hm
              (r324SelectedMomentContraction κp κm π) v) 1).2
            ((r324ContractionEndpointFlags
              (r324SelectedMomentContraction κp κm π)) 1) *
          (r324EndpointCoefficient (-α)
            ((r324ContractionEndpointAnchors hm
              (r324SelectedMomentContraction κp κm π) v) 2).1
            ((r324ContractionEndpointAnchors hm
              (r324SelectedMomentContraction κp κm π) v) 2).2
            ((r324ContractionEndpointFlags
              (r324SelectedMomentContraction κp κm π)) 2) *
          (r324EndpointCoefficient (-β)
            ((r324ContractionEndpointAnchors hm
              (r324SelectedMomentContraction κp κm π) v) 3).1
            ((r324ContractionEndpointAnchors hm
              (r324SelectedMomentContraction κp κm π) v) 3).2
            ((r324ContractionEndpointFlags
              (r324SelectedMomentContraction κp κm π)) 3) *
            ρ.r324SelectedEndpointCore
              ε κp κm π ω.1
              (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
                ε α β κp κm π hexternal hε hε1 hmtrunc ω)
              ‖z4EuclideanFrequency (α + β)‖ v)))
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  let selected :=
    ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
      ε α β κp κm π hexternal hε hε1 hmtrunc ω
  let f :=
    ρ.r324SelectedHighFullPairingFourierIntegrand
      ε α β κp κm π hexternal hε hε1 hmtrunc ω
  have hf :
      Integrable (r324Flatten f)
        (r324PhysicalMeasure m) := by
    refine
      (ρ.integrable_r324Flatten_fullPairingFourierIntegrand
        ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩
        ω.1).congr (.of_forall fun p => ?_)
    exact
      (ρ.r324SelectedHighFullPairingFourierIntegrand_eq
        ε α β κp κm π hexternal hε hε1 hmtrunc
        ω p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2).symm
  rw [r324SelectedPhysicalCell_eq_internal_preimage]
  rw [r324_setIntegral_internal_eq_internal_first
    f
    (r324SelectedInternalCell
      κp κm π selected ε hε cell)
    (measurableSet_r324SelectedInternalCell
      κp κm π selected ε hε cell)
    hf]
  apply setIntegral_congr_fun
    (measurableSet_r324SelectedInternalCell
      κp κm π selected ε hε cell)
  intro v _hv
  dsimp only [f]
  simp_rw [
    ρ.r324SelectedHighFullPairingFourierIntegrand_eq_endpointSeparated
      hm ε α β κp κm π hexternal hε hε1 hmtrunc ω]
  exact
    integral_r324EndpointSeparatedIntegrand α β
      (r324ContractionEndpointAnchors hm
        (r324SelectedMomentContraction κp κm π) v)
      (r324ContractionEndpointFlags
        (r324SelectedMomentContraction κp κm π))
      (ρ.r324SelectedEndpointCore ε κp κm π ω.1 selected
        ‖z4EuclideanFrequency (α + β)‖ v)

end SmoothCutoff

end

end Anderson4D
