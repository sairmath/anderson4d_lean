import Anderson4D.Continuum.OpenEdgeDiscretization
import Anderson4D.DetParametrix.Paper42_Moment.R324SelectorFiberBridge

/-!
# Cell decomposition of the genuine selected configuration integral

Each member of the restricted canonical selector fibre is now decomposed
on the actual five-variable physical measure by the one-open-edge cell
partition.  This is an exact equality of complex integrals.  The selected
configuration is not replaced by an unrestricted projected series and
no norm is taken.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- Lift the marked-residual open-edge partition from the internal
physical coordinates to the complete `(x,y,z,w,v)` product. -/
def r324SelectedPhysicalOpenEdgeCells
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (ε : ℝ) (hε : 0 < ε) :
    FiniteMeasurableCells
      (R324PhysicalPoint m) (Fin (2 * m) → Z4) := by
  let P :=
    r324MarkedResidualOpenEdgeCells
      κp κm π selected ε hε
  let internal :
      R324PhysicalPoint m → (Fin (2 * m) → T4) :=
    fun p => p.2.2.2.2
  have hinternal : Measurable internal :=
    measurable_snd.comp
      (measurable_snd.comp
        (measurable_snd.comp measurable_snd))
  exact
    { indices := P.indices
      index := fun p => P.index (internal p)
      range_subset := fun p => P.range_subset (internal p)
      measurable_fiber := fun y =>
        (P.measurable_fiber y).preimage hinternal }

/-- Every physical point is indexed by an open word respecting all
unmarked covariance edges. -/
theorem r324SelectedPhysicalOpenEdgeCells_index_respects
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (ε : ℝ) (hε : 0 < ε)
    (p : R324PhysicalPoint m) :
    RespectsPairingExcept
      (momentCombinedPairing κp κm π)
      (r324ResidualMarkedLowerEndpoint selected)
      (r324ResidualMarkedUpperEndpoint π selected)
      ((r324SelectedPhysicalOpenEdgeCells
        κp κm π selected ε hε).index p) := by
  exact
    r324MarkedResidualOpenEdgeCells_index_respects
      κp κm π selected ε hε p.2.2.2.2

/-- One exact restricted selected-configuration integral is the finite
sum of its genuine open-edge physical cell integrals. -/
theorem r324SelectedHighFullPairingFourierIntegral_eq_openEdgeCells
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (ω :
      R324NonzeroCombinedFourierConfiguration
        ρ ε α β κp κm π) :
    ρ.r324SelectedHighFullPairingFourierIntegral
        ε α β κp κm π hexternal hε hε1 hmtrunc ω =
      ∑ y ∈
          (r324SelectedPhysicalOpenEdgeCells
            κp κm π
            (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
              ε α β κp κm π hexternal hε hε1 hmtrunc ω)
            ε hε).indices,
        ∫ p in
            (r324SelectedPhysicalOpenEdgeCells
              κp κm π
              (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
                ε α β κp κm π hexternal hε hε1 hmtrunc ω)
              ε hε).index ⁻¹' {y},
          r324Flatten
            (ρ.r324SelectedHighFullPairingFourierIntegrand
              ε α β κp κm π hexternal hε hε1 hmtrunc ω) p
          ∂(r324PhysicalMeasure m) := by
  let selected :=
    ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
      ε α β κp κm π hexternal hε hε1 hmtrunc ω
  let P :=
    r324SelectedPhysicalOpenEdgeCells
      κp κm π selected ε hε
  let f : R324PhysicalPoint m → ℂ :=
    r324Flatten
      (ρ.r324SelectedHighFullPairingFourierIntegrand
        ε α β κp κm π hexternal hε hε1 hmtrunc ω)
  let κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull} :=
    ⟨momentCombinedPairing κp κm π,
      momentCombinedPairing_isFull κp κm π⟩
  have hf : Integrable f (r324PhysicalMeasure m) := by
    refine
      (ρ.integrable_r324Flatten_fullPairingFourierIntegrand
        ε α β κ ω.1).congr (.of_forall fun p => ?_)
    unfold f r324Flatten
    exact
      (ρ.r324SelectedHighFullPairingFourierIntegrand_eq
        ε α β κp κm π hexternal hε hε1 hmtrunc
        ω p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2).symm
  unfold r324SelectedHighFullPairingFourierIntegral
  change (∫ p, f p ∂(r324PhysicalMeasure m)) = _
  rw [← setIntegral_univ, ← P.iUnion_fibers]
  exact integral_biUnion_finset P.indices
    (fun y _hy => P.measurable_fiber y)
    P.pairwiseDisjoint
    (fun _y _hy => hf.integrableOn)

end SmoothCutoff

end

end Anderson4D
