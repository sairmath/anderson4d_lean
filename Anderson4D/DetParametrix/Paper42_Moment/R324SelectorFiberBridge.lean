import Anderson4D.DetParametrix.Paper42_Moment.R324CrossSlotHighFrequencySelection

/-!
# Exact selector-fibre bridge for R-324 Fourier configurations

This module works at the exact full-pairing Fourier-series boundary.
Zero integrated configurations are deleted, the remaining configurations
are partitioned by their canonical first-large cross slot, and only the
selected covariance mode of each member is rewritten through its own
high-mode indicator.

The selector fibres remain restricted throughout.  They are not enlarged
to the unrestricted `r324ProjectedCovarianceC` series, and no norm is
taken before the exact partition.  Thus this file supplies an algebraic
bridge for a later primitive-fibre consumer; it does not claim a
termwise absolute-value reduction or an equality with the unrestricted
one-projected covariance product.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## Removing zero terms without changing a summable series -/

/-- A summable series is unchanged when it is restricted to the subtype
of indices carrying nonzero terms. -/
theorem tsum_eq_tsum_nonzero_subtype
    {Ω : Type*} (term : Ω → ℂ)
    (hterm : Summable term) :
    (∑' ω, term ω) =
      ∑' ω : {ω : Ω // term ω ≠ 0}, term ω.1 := by
  let S : Set Ω := {ω | term ω ≠ 0}
  have hsplit :=
    hterm.tsum_subtype_add_tsum_subtype_compl S
  have hzero :
      (∑' ω : ↥Sᶜ, term ω.1) = 0 := by
    calc
      (∑' ω : ↥Sᶜ, term ω.1) =
          ∑' _ω : ↥Sᶜ, (0 : ℂ) := by
        apply tsum_congr
        intro ω
        have hnot : ¬term ω.1 ≠ 0 := by
          simpa only [S, Set.mem_compl_iff, Set.mem_setOf_eq]
            using ω.2
        exact not_ne_iff.mp hnot
      _ = 0 := tsum_zero
  rw [hzero, add_zero] at hsplit
  exact hsplit.symm

/-! ## Replacing only the selected configuration factor -/

/-- One pair-mode factor in which precisely the selected genuine pair
index is passed through the high-mode indicator.  Every other pair mode
is left literally unchanged. -/
def r324SelectedHighPairModeFactor
    {m : ℕ}
    (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4)
    (j :
      Fin ((momentCombinedPairing κp κm π).pairSupport.filter
        (fun a => a < momentCombinedPairing κp κm π a)).card) :
    ℂ :=
  if j = r324CrossSlotPairIndex κp κm π selected then
    let a :=
      (r324PairFinEquiv
        (momentCombinedPairing κp κm π) j).1
    ρ.r324HighCovarianceModeTerm ε L
      (v a - v (momentCombinedPairing κp κm π a))
      (q j)
  else
    ρ.r324PairModeTerm ε
      (momentCombinedPairing κp κm π) v j (q j)

/-- Product of the actual fixed Fourier modes with only the selected
factor guarded by its high-mode indicator. -/
def r324SelectedHighCovarianceConfigurationTerm
    {m : ℕ}
    (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    ℂ :=
  ∏ j,
    ρ.r324SelectedHighPairModeFactor
      ε L κp κm π q selected v j

/-- On an actual nonzero configuration, every pair factor is unchanged
after guarding its own canonical selected pair by the high-mode
indicator. -/
theorem r324SelectedHighPairModeFactor_eq
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
    (v : Fin (2 * m) → T4)
    (j :
      Fin ((momentCombinedPairing κp κm π).pairSupport.filter
        (fun a => a < momentCombinedPairing κp κm π a)).card) :
    ρ.r324SelectedHighPairModeFactor
        ε ‖z4EuclideanFrequency (α + β)‖
        κp κm π ω.1
        (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
          ε α β κp κm π hexternal hε hε1 hmtrunc ω)
        v j =
      ρ.r324PairModeTerm ε
        (momentCombinedPairing κp κm π) v j (ω.1 j) := by
  let selected :=
    ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
      ε α β κp κm π hexternal hε hε1 hmtrunc ω
  by_cases hj :
      j = r324CrossSlotPairIndex κp κm π selected
  · subst j
    unfold r324SelectedHighPairModeFactor
    rw [if_pos rfl]
    unfold r324HighCovarianceModeTerm
    rw [Set.indicator_of_mem]
    · rfl
    · exact
        ρ.firstLargeCrossPairModeForNonzeroConfiguration_mem_highModeSet
          ε α β κp κm π hexternal hε hε1 hmtrunc ω
  · unfold r324SelectedHighPairModeFactor
    rw [if_neg hj]

/-- Hence the whole fixed-mode covariance product is unchanged. -/
theorem r324SelectedHighCovarianceConfigurationTerm_eq
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
    ρ.r324SelectedHighCovarianceConfigurationTerm
        ε ‖z4EuclideanFrequency (α + β)‖
        κp κm π ω.1
        (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
          ε α β κp κm π hexternal hε hε1 hmtrunc ω)
        v =
      ρ.r324CovarianceFourierConfigurationTerm ε
        (momentCombinedPairing κp κm π) v ω.1 := by
  unfold r324SelectedHighCovarianceConfigurationTerm
    r324CovarianceFourierConfigurationTerm
    finSeriesAssignmentTerm
  apply Finset.prod_congr rfl
  intro j _hj
  exact
    ρ.r324SelectedHighPairModeFactor_eq
      ε α β κp κm π hexternal hε hε1 hmtrunc ω v j

/-! ## Pointwise and integrated selected-indicator terms -/

/-- The full physical Fourier integrand with only its own canonical
selected pair factor guarded by the high-mode indicator. -/
def r324SelectedHighFullPairingFourierIntegrand
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
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  let κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull} :=
    ⟨momentCombinedPairing κp κm π,
      momentCombinedPairing_isFull κp κm π⟩
  let e := (momentContractionEquivFullPairing m).symm κ
  momentFourierPhase α β x y z w *
    renormalizedGreenSkeleton e.1
      (assemble x y fun i => v (leftMomentIndex i)) *
    renormalizedGreenSkeleton e.2.1
      (assemble z w fun i => v (rightMomentIndex i)) *
    ρ.r324SelectedHighCovarianceConfigurationTerm
      ε ‖z4EuclideanFrequency (α + β)‖
      κp κm π ω.1
      (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
        ε α β κp κm π hexternal hε hε1 hmtrunc ω)
      v

/-- Guarding the canonical selected mode does not change the original
full-pairing Fourier integrand. -/
theorem r324SelectedHighFullPairingFourierIntegrand_eq
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
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    ρ.r324SelectedHighFullPairingFourierIntegrand
        ε α β κp κm π hexternal hε hε1 hmtrunc
        ω x y z w v =
      ρ.r324FullPairingFourierIntegrand ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩
        ω.1 x y z w v := by
  unfold r324SelectedHighFullPairingFourierIntegrand
    r324FullPairingFourierIntegrand
  dsimp only
  rw [
    ρ.r324SelectedHighCovarianceConfigurationTerm_eq
      ε α β κp κm π hexternal hε hε1 hmtrunc ω v]

/-- Physical integral of one canonically selected high-indicator
configuration. -/
def r324SelectedHighFullPairingFourierIntegral
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (ω :
      R324NonzeroCombinedFourierConfiguration
        ρ ε α β κp κm π) : ℂ :=
  ∫ p,
    r324Flatten
      (ρ.r324SelectedHighFullPairingFourierIntegrand
        ε α β κp κm π hexternal hε hε1 hmtrunc ω) p
    ∂(r324PhysicalMeasure m)

/-- Every original nonzero integrated Fourier term is exactly its own
selected high-indicator term. -/
theorem r324SelectedHighFullPairingFourierIntegral_eq
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
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩
        ω.1 := by
  unfold r324SelectedHighFullPairingFourierIntegral
    r324FullPairingFourierIntegral
  apply integral_congr_ae
  filter_upwards with p
  exact
    ρ.r324SelectedHighFullPairingFourierIntegrand_eq
      ε α β κp κm π hexternal hε hε1 hmtrunc
      ω p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

/-! ## Exact zero deletion and selector-fibre partition -/

/-- Integrated full-pairing Fourier configurations form a summable
series. -/
theorem summable_r324FullPairingFourierIntegral
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    Summable fun q : R324CombinedFourierConfiguration κp κm π =>
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q := by
  apply Summable.of_norm
  exact
    (ρ.summable_integral_norm_r324FullPairingFourierIntegrand
      hε α β
      ⟨momentCombinedPairing κp κm π,
        momentCombinedPairing_isFull κp κm π⟩).of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (fun _ => norm_integral_le_integral_norm _)

/-- Zero integrated configurations may be deleted from the actual
full-pairing Fourier series. -/
theorem tsum_r324FullPairingFourierIntegral_eq_nonzero
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (∑' q : R324CombinedFourierConfiguration κp κm π,
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q) =
      ∑' ω :
          R324NonzeroCombinedFourierConfiguration
            ρ ε α β κp κm π,
        ρ.r324FullPairingFourierIntegral ε α β
          ⟨momentCombinedPairing κp κm π,
            momentCombinedPairing_isFull κp κm π⟩
          ω.1 := by
  exact
    tsum_eq_tsum_nonzero_subtype _
      (ρ.summable_r324FullPairingFourierIntegral
        hε α β κp κm π)

/-- The exact fibre of nonzero configurations whose canonical
first-large selector is the given cross slot. -/
abbrev R324SelectedCrossSlotConfigurationFiber
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (i : R324ResidualCovarianceSlot κp) :=
  ↥((ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
      ε α β κp κm π hexternal hε hε1 hmtrunc) ⁻¹'
    ({i} : Set (R324ResidualCovarianceSlot κp)))

/-- Nonzero configurations partition without overlap or omission into
the fibres of the canonical selected cross-slot function. -/
theorem tsum_nonzero_r324FullPairingFourierIntegral_eq_selectorFibres
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε) :
    (∑' ω :
        R324NonzeroCombinedFourierConfiguration
          ρ ε α β κp κm π,
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩
        ω.1) =
      ∑ i : R324ResidualCovarianceSlot κp,
        ∑' ω :
            R324SelectedCrossSlotConfigurationFiber
              ρ ε α β κp κm π hexternal
              hε hε1 hmtrunc i,
          ρ.r324FullPairingFourierIntegral ε α β
            ⟨momentCombinedPairing κp κm π,
              momentCombinedPairing_isFull κp κm π⟩
            ω.1.1 := by
  let term : R324CombinedFourierConfiguration κp κm π → ℂ :=
    fun q =>
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q
  let selected :
      R324NonzeroCombinedFourierConfiguration
          ρ ε α β κp κm π →
        R324ResidualCovarianceSlot κp :=
    ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
      ε α β κp κm π hexternal hε hε1 hmtrunc
  have hnonzero :
      Summable fun ω :
          R324NonzeroCombinedFourierConfiguration
            ρ ε α β κp κm π =>
        term ω.1 := by
    exact
      (ρ.summable_r324FullPairingFourierIntegral
        hε α β κp κm π).subtype _
  have hfibres :=
    hnonzero.hasSum.tsum_fiberwise selected
  calc
    (∑' ω :
        R324NonzeroCombinedFourierConfiguration
          ρ ε α β κp κm π,
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩
        ω.1) =
        ∑' i : R324ResidualCovarianceSlot κp,
          ∑' ω :
              R324SelectedCrossSlotConfigurationFiber
                ρ ε α β κp κm π hexternal
                hε hε1 hmtrunc i,
            ρ.r324FullPairingFourierIntegral ε α β
              ⟨momentCombinedPairing κp κm π,
                momentCombinedPairing_isFull κp κm π⟩
              ω.1.1 := by
      exact hfibres.tsum_eq.symm
    _ = ∑ i : R324ResidualCovarianceSlot κp,
          ∑' ω :
              R324SelectedCrossSlotConfigurationFiber
                ρ ε α β κp κm π hexternal
                hε hε1 hmtrunc i,
            ρ.r324FullPairingFourierIntegral ε α β
              ⟨momentCombinedPairing κp κm π,
                momentCombinedPairing_isFull κp κm π⟩
              ω.1.1 := by
      rw [tsum_fintype]

/-- Exact configuration-series bridge: after deleting zero terms and
partitioning by the canonical selector, each member is replaced only by
its own selected high-indicator integral. -/
theorem tsum_r324FullPairingFourierIntegral_eq_selectedHighFibres
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε) :
    (∑' q : R324CombinedFourierConfiguration κp κm π,
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q) =
      ∑ i : R324ResidualCovarianceSlot κp,
        ∑' ω :
            R324SelectedCrossSlotConfigurationFiber
              ρ ε α β κp κm π hexternal
              hε hε1 hmtrunc i,
          ρ.r324SelectedHighFullPairingFourierIntegral
            ε α β κp κm π hexternal hε hε1 hmtrunc
            ω.1 := by
  rw [
    ρ.tsum_r324FullPairingFourierIntegral_eq_nonzero
      hε α β κp κm π,
    ρ.tsum_nonzero_r324FullPairingFourierIntegral_eq_selectorFibres
      ε α β κp κm π hexternal hε hε1 hmtrunc]
  apply Finset.sum_congr rfl
  intro i _hi
  apply tsum_congr
  intro ω
  exact
    (ρ.r324SelectedHighFullPairingFourierIntegral_eq
      ε α β κp κm π hexternal hε hε1 hmtrunc
      ω.1).symm

/-- The real full-pairing physical integral, not an abstract routing
predicate, is exactly the finite sum of its restricted canonical
selected-slot high-indicator fibres. -/
theorem integral_momentFullPairingPhysicalIntegrand_eq_selectedHighFibres
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε) :
    (∫ p,
      r324Flatten
        (momentFullPairingPhysicalIntegrand
          ρ ε m α β
          ⟨momentCombinedPairing κp κm π,
            momentCombinedPairing_isFull κp κm π⟩) p
      ∂(r324PhysicalMeasure m)) =
      ∑ i : R324ResidualCovarianceSlot κp,
        ∑' ω :
            R324SelectedCrossSlotConfigurationFiber
              ρ ε α β κp κm π hexternal
              hε hε1 hmtrunc i,
          ρ.r324SelectedHighFullPairingFourierIntegral
            ε α β κp κm π hexternal hε hε1 hmtrunc
            ω.1 := by
  rw [
    ρ.integral_momentFullPairingPhysicalIntegrand_eq_configuration_tsum
      hε α β
      ⟨momentCombinedPairing κp κm π,
        momentCombinedPairing_isFull κp κm π⟩]
  exact
    ρ.tsum_r324FullPairingFourierIntegral_eq_selectedHighFibres
      ε α β κp κm π hexternal hε hε1 hmtrunc

end SmoothCutoff

end

end Anderson4D
