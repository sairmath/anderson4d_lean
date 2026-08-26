import Anderson4D.DetParametrix.Paper42_Moment.R324CrossSlotFrequencyConservation
import Anderson4D.DetParametrix.Paper42_Moment.R324SingleProjectedSlotClosure

/-!
# Selecting the high-frequency cross-contraction slot

This file connects the exact cross-slot conservation law for one actual
Fourier configuration to the first-large-increment selector.  The selected
left single is then mapped back to the genuine pair index of the doubled
pairing and to the existing one-projected-covariance construction.

The scope remains the Fourier-configuration layer.  In particular, no
declaration below identifies the original R-324 moment with a projected
configuration series, and no residual-block collapse is performed.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- Fourier assignments for the actual full doubled pairing attached to
one contraction triple. -/
abbrev R324CombinedFourierConfiguration
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :=
  Fin ((momentCombinedPairing κp κm π).pairSupport.filter
    (fun a => a < momentCombinedPairing κp κm π a)).card → Z4

/-- The actual Fourier configurations whose physical integral is
nonzero.  This is only a subtype of configurations, not a decomposition
of the original moment. -/
abbrev R324NonzeroCombinedFourierConfiguration
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :=
  {q : R324CombinedFourierConfiguration κp κm π //
    ρ.r324FullPairingFourierIntegral ε α β
      ⟨momentCombinedPairing κp κm π,
        momentCombinedPairing_isFull κp κm π⟩ q ≠ 0}

/-- Cross-slot increments enumerated by the standard `Fin card`
enumeration required by the first-large selector. -/
def r324EnumeratedCrossSlotIncrement
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (j : Fin κp.singles.card) :
    EuclideanSpace ℝ (Fin dim) :=
  r324CrossSlotIncrement κp κm π q
    (r324ResidualCovarianceSlotEquiv κp j)

/-- Reindexing by `Fin κp.singles.card` preserves the exact cross-slot
frequency sum. -/
theorem sum_r324EnumeratedCrossSlotIncrement_eq_external_of_integral_ne_zero
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (hne :
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q ≠ 0) :
    (∑ j : Fin κp.singles.card,
        r324EnumeratedCrossSlotIncrement κp κm π q j) =
      z4EuclideanFrequency (α + β) := by
  unfold r324EnumeratedCrossSlotIncrement
  rw [
    (r324ResidualCovarianceSlotEquiv κp).sum_comp
      (r324CrossSlotIncrement κp κm π q)]
  exact
    ρ.sum_r324CrossSlotIncrement_eq_external_of_integral_ne_zero
      ε α β κp κm π q hne

/-- At nonzero external shift, an actual nonzero configuration has a
positive number of cross slots. -/
theorem r324CrossSlot_card_pos_of_external_ne_zero_integral_ne_zero
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (q : R324CombinedFourierConfiguration κp κm π)
    (hne :
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q ≠ 0) :
    0 < κp.singles.card := by
  exact Finset.card_pos.mpr
    (ρ.singles_nonempty_of_external_add_ne_zero_integral_ne_zero
      ε α β κp κm π hexternal q hne)

/-- Average-size routing in the literal division-free form: one genuine
cross slot carries at least `1 / card` of the external shift. -/
theorem exists_r324CrossSlotIncrement_average
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (q : R324CombinedFourierConfiguration κp κm π)
    (hne :
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q ≠ 0) :
    ∃ i : R324ResidualCovarianceSlot κp,
      ‖z4EuclideanFrequency (α + β)‖ ≤
        (κp.singles.card : ℝ) *
          ‖r324CrossSlotIncrement κp κm π q i‖ := by
  let δ : Fin κp.singles.card →
      EuclideanSpace ℝ (Fin dim) :=
    r324EnumeratedCrossSlotIncrement κp κm π q
  have hcard :
      0 < κp.singles.card :=
    ρ.r324CrossSlot_card_pos_of_external_ne_zero_integral_ne_zero
      ε α β κp κm π hexternal q hne
  obtain ⟨j, hj⟩ :=
    exists_large_frequency_increment κp.singles.card hcard δ
  refine ⟨r324ResidualCovarianceSlotEquiv κp j, ?_⟩
  rw [
    ρ.sum_r324EnumeratedCrossSlotIncrement_eq_external_of_integral_ne_zero
      ε α β κp κm π q hne] at hj
  exact hj

/-- The same average-size conclusion in the explicit quotient form. -/
theorem exists_r324CrossSlotIncrement_norm_div_card_le
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (q : R324CombinedFourierConfiguration κp κm π)
    (hne :
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q ≠ 0) :
    ∃ i : R324ResidualCovarianceSlot κp,
      ‖z4EuclideanFrequency (α + β)‖ /
          (κp.singles.card : ℝ) ≤
        ‖r324CrossSlotIncrement κp κm π q i‖ := by
  obtain ⟨i, hi⟩ :=
    ρ.exists_r324CrossSlotIncrement_average
      ε α β κp κm π hexternal q hne
  refine ⟨i, ?_⟩
  have hcard :
      (0 : ℝ) < κp.singles.card := by
    exact_mod_cast
      ρ.r324CrossSlot_card_pos_of_external_ne_zero_integral_ne_zero
        ε α β κp κm π hexternal q hne
  exact (div_le_iff₀ hcard).2 (by
    simpa only [mul_comm] using hi)

/-- The number of cross slots is within the truncation order whenever
the moment order is. -/
theorem r324CrossSlot_card_le_truncOrder
    {m : ℕ} {ε : ℝ}
    (κp : PartialPairing (Fin m))
    (hmtrunc : m ≤ truncOrder ε) :
    κp.singles.card ≤ truncOrder ε := by
  have hcard : κp.singles.card ≤ m := by
    simpa using Finset.card_le_univ κp.singles
  exact hcard.trans hmtrunc

/-- The canonical first cross slot meeting the paper's
`sqrt ε / 2` routing threshold.  The positivity proof is explicit so
the definition itself does not pretend that every pairing has a cross
slot. -/
def r324FirstLargeCrossSlot
    {m : ℕ}
    (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (hcard : 0 < κp.singles.card)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε) :
    R324ResidualCovarianceSlot κp :=
  r324ResidualCovarianceSlotEquiv κp
    (r324FirstLargeResidualIncrementSlot
      hcard
      (r324EnumeratedCrossSlotIncrement κp κm π q)
      hε hε1
      (r324CrossSlot_card_le_truncOrder κp hmtrunc))

/-- The selected residual slot mapped to the actual pair index in the
combined full pairing. -/
def r324FirstLargeCrossPairIndex
    {m : ℕ}
    (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (hcard : 0 < κp.singles.card)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε) :
    Fin ((momentCombinedPairing κp κm π).pairSupport.filter
      (fun a => a < momentCombinedPairing κp κm π a)).card :=
  r324CrossSlotPairIndex κp κm π
    (r324FirstLargeCrossSlot
      ε κp κm π q hcard hε hε1 hmtrunc)

/-- The mapped selected pair index has precisely the left-single lower
endpoint in the actual combined pairing. -/
theorem r324PairFinEquiv_r324FirstLargeCrossPairIndex
    {m : ℕ}
    (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (hcard : 0 < κp.singles.card)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε) :
    (r324PairFinEquiv (momentCombinedPairing κp κm π)
      (r324FirstLargeCrossPairIndex
        ε κp κm π q hcard hε hε1 hmtrunc)).1 =
      leftMomentIndex
        (r324FirstLargeCrossSlot
          ε κp κm π q hcard hε hε1 hmtrunc).1 := by
  exact
    r324PairFinEquiv_r324CrossSlotPairIndex
      κp κm π
      (r324FirstLargeCrossSlot
        ε κp κm π q hcard hε hε1 hmtrunc)

/-- For a nonzero actual configuration, the canonical selected cross
slot satisfies the exact truncation-scale threshold. -/
theorem r324FirstLargeCrossSlot_spec_of_integral_ne_zero
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (hcard : 0 < κp.singles.card)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (hne :
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q ≠ 0) :
    (Real.sqrt ε / 2) *
        ‖z4EuclideanFrequency (α + β)‖ ≤
      ‖r324CrossSlotIncrement κp κm π q
        (r324FirstLargeCrossSlot
          ε κp κm π q hcard hε hε1 hmtrunc)‖ := by
  let δ : Fin κp.singles.card →
      EuclideanSpace ℝ (Fin dim) :=
    r324EnumeratedCrossSlotIncrement κp κm π q
  have hsum :
      (∑ j, δ j) = z4EuclideanFrequency (α + β) := by
    exact
      ρ.sum_r324EnumeratedCrossSlotIncrement_eq_external_of_integral_ne_zero
        ε α β κp κm π q hne
  have hspec :=
    r324FirstLargeResidualIncrementSlot_spec_of_sum
      hcard δ (z4EuclideanFrequency (α + β))
      hε hε1
      (r324CrossSlot_card_le_truncOrder κp hmtrunc)
      hsum
  exact hspec

/-- At nonzero external shift the positivity premise of the canonical
selector is supplied by the actual configuration itself. -/
theorem r324FirstLargeCrossSlot_spec_of_external_ne_zero
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (q : R324CombinedFourierConfiguration κp κm π)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (hne :
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q ≠ 0) :
    let hcard :=
      ρ.r324CrossSlot_card_pos_of_external_ne_zero_integral_ne_zero
        ε α β κp κm π hexternal q hne
    (Real.sqrt ε / 2) *
        ‖z4EuclideanFrequency (α + β)‖ ≤
      ‖r324CrossSlotIncrement κp κm π q
        (r324FirstLargeCrossSlot
          ε κp κm π q hcard hε hε1 hmtrunc)‖ := by
  dsimp only
  exact
    ρ.r324FirstLargeCrossSlot_spec_of_integral_ne_zero
      ε α β κp κm π q
      (ρ.r324CrossSlot_card_pos_of_external_ne_zero_integral_ne_zero
        ε α β κp κm π hexternal q hne)
      hε hε1 hmtrunc hne

/-- The norm of a cross-slot increment is exactly the norm of the
Fourier mode assigned to its genuine combined-pair index. -/
theorem norm_r324CrossSlotIncrement_eq_pairMode
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (i : R324ResidualCovarianceSlot κp) :
    ‖r324CrossSlotIncrement κp κm π q i‖ =
      ‖z4EuclideanFrequency
        (q (r324CrossSlotPairIndex κp κm π i))‖ := by
  change
    ‖z4EuclideanFrequencyAddHom
      (-q (r324CrossSlotPairIndex κp κm π i))‖ =
    ‖z4EuclideanFrequencyAddHom
      (q (r324CrossSlotPairIndex κp κm π i))‖
  rw [map_neg, norm_neg]

/-- The actual mode on the selected combined-pair index belongs to the
high-mode set used by `r324ProjectedCovarianceC`. -/
theorem r324FirstLargeCrossPairMode_mem_highModeSet
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (hcard : 0 < κp.singles.card)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (hne :
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q ≠ 0) :
    q (r324FirstLargeCrossPairIndex
        ε κp κm π q hcard hε hε1 hmtrunc) ∈
      r324HighModeSet ε
        ‖z4EuclideanFrequency (α + β)‖ := by
  change
    (Real.sqrt ε / 2) *
        ‖z4EuclideanFrequency (α + β)‖ ≤
      ‖z4EuclideanFrequency
        (q (r324FirstLargeCrossPairIndex
          ε κp κm π q hcard hε hε1 hmtrunc))‖
  unfold r324FirstLargeCrossPairIndex
  rw [← norm_r324CrossSlotIncrement_eq_pairMode
    κp κm π q
    (r324FirstLargeCrossSlot
      ε κp κm π q hcard hε hε1 hmtrunc)]
  exact
    ρ.r324FirstLargeCrossSlot_spec_of_integral_ne_zero
      ε α β κp κm π q hcard hε hε1 hmtrunc hne

/-- Consequently the selected actual Fourier mode is retained,
unchanged, by the high-covariance mode indicator. -/
theorem r324HighCovarianceModeTerm_firstLargeCrossPairMode
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (hcard : 0 < κp.singles.card)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (hne :
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q ≠ 0)
    (z : T4) :
    ρ.r324HighCovarianceModeTerm ε
        ‖z4EuclideanFrequency (α + β)‖ z
        (q (r324FirstLargeCrossPairIndex
          ε κp κm π q hcard hε hε1 hmtrunc)) =
      ρ.r324CovarianceModeTerm ε z
        (q (r324FirstLargeCrossPairIndex
          ε κp κm π q hcard hε hε1 hmtrunc)) := by
  unfold r324HighCovarianceModeTerm
  rw [Set.indicator_of_mem]
  exact
    ρ.r324FirstLargeCrossPairMode_mem_highModeSet
      ε α β κp κm π q hcard hε hε1 hmtrunc hne

/-- The concrete residual covariance product obtained by projecting
exactly the canonical selected cross slot. -/
def r324FirstLargeSingleProjectedResidualCovarianceProduct
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (hcard : 0 < κp.singles.card)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (v : Fin (2 * m) → T4) : ℂ :=
  ρ.r324SingleProjectedResidualCovarianceProduct
    ε ‖z4EuclideanFrequency (α + β)‖
    κp κm π v
    (r324FirstLargeCrossSlot
      ε κp κm π q hcard hε hε1 hmtrunc)

/-- Exact factorization of the selected product: one projected
covariance and complete `etaEpsT4` factors at every other cross slot. -/
theorem r324FirstLargeSingleProjectedResidualCovarianceProduct_eq
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (hcard : 0 < κp.singles.card)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (v : Fin (2 * m) → T4) :
    ρ.r324FirstLargeSingleProjectedResidualCovarianceProduct
        ε α β κp κm π q hcard hε hε1 hmtrunc v =
      ρ.r324ProjectedCovarianceC ε
          ‖z4EuclideanFrequency (α + β)‖
          (r324ResidualCovarianceDisplacement κp κm π v
            (r324FirstLargeCrossSlot
              ε κp κm π q hcard hε hε1 hmtrunc)) *
        ∏ i ∈
            (Finset.univ :
              Finset (R324ResidualCovarianceSlot κp)).erase
                (r324FirstLargeCrossSlot
                  ε κp κm π q hcard hε hε1 hmtrunc),
          (ρ.etaEpsT4 ε
            (r324ResidualCovarianceDisplacement
              κp κm π v i) : ℂ) := by
  unfold r324FirstLargeSingleProjectedResidualCovarianceProduct
  exact
    ρ.r324SingleProjectedResidualCovarianceProduct_eq
      ε ‖z4EuclideanFrequency (α + β)‖
      κp κm π v
      (r324FirstLargeCrossSlot
        ε κp κm π q hcard hε hε1 hmtrunc)

/-- Canonical selected slot as a function of an actual nonzero Fourier
configuration.  Nonzero external shift supplies the required nonempty
cross-slot proof for every member of the subtype. -/
def r324FirstLargeCrossSlotForNonzeroConfiguration
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
    R324ResidualCovarianceSlot κp :=
  r324FirstLargeCrossSlot
    ε κp κm π ω.1
    (ρ.r324CrossSlot_card_pos_of_external_ne_zero_integral_ne_zero
      ε α β κp κm π hexternal ω.1 ω.2)
    hε hε1 hmtrunc

/-- Every nonzero actual configuration is covered by its canonical
selected cross slot at the paper's high-mode threshold. -/
theorem r324FirstLargeCrossSlotForNonzeroConfiguration_spec
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
    (Real.sqrt ε / 2) *
        ‖z4EuclideanFrequency (α + β)‖ ≤
      ‖r324CrossSlotIncrement κp κm π ω.1
        (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
          ε α β κp κm π hexternal hε hε1 hmtrunc ω)‖ := by
  unfold r324FirstLargeCrossSlotForNonzeroConfiguration
  exact
    ρ.r324FirstLargeCrossSlot_spec_of_integral_ne_zero
      ε α β κp κm π ω.1
      (ρ.r324CrossSlot_card_pos_of_external_ne_zero_integral_ne_zero
        ε α β κp κm π hexternal ω.1 ω.2)
      hε hε1 hmtrunc ω.2

/-- The canonical selected slot of a nonzero configuration, mapped to
its genuine pair index in the combined full pairing. -/
def r324FirstLargeCrossPairIndexForNonzeroConfiguration
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
    Fin ((momentCombinedPairing κp κm π).pairSupport.filter
      (fun a => a < momentCombinedPairing κp κm π a)).card :=
  r324CrossSlotPairIndex κp κm π
    (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
      ε α β κp κm π hexternal hε hε1 hmtrunc ω)

/-- The actual selected pair index has the expected left-single lower
endpoint. -/
theorem r324PairFinEquiv_firstLargeCrossPairIndexForNonzeroConfiguration
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
    (r324PairFinEquiv (momentCombinedPairing κp κm π)
      (ρ.r324FirstLargeCrossPairIndexForNonzeroConfiguration
        ε α β κp κm π hexternal hε hε1 hmtrunc ω)).1 =
      leftMomentIndex
        (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
          ε α β κp κm π hexternal hε hε1 hmtrunc ω).1 := by
  exact
    r324PairFinEquiv_r324CrossSlotPairIndex
      κp κm π
      (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
        ε α β κp κm π hexternal hε hε1 hmtrunc ω)

/-- The actual Fourier mode carried by the selected genuine pair index
is retained by the one-slot high-frequency projection. -/
theorem firstLargeCrossPairModeForNonzeroConfiguration_mem_highModeSet
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
    ω.1
        (ρ.r324FirstLargeCrossPairIndexForNonzeroConfiguration
          ε α β κp κm π hexternal hε hε1 hmtrunc ω) ∈
      r324HighModeSet ε
        ‖z4EuclideanFrequency (α + β)‖ := by
  let hcard :=
    ρ.r324CrossSlot_card_pos_of_external_ne_zero_integral_ne_zero
      ε α β κp κm π hexternal ω.1 ω.2
  have hmem :=
    ρ.r324FirstLargeCrossPairMode_mem_highModeSet
      ε α β κp κm π ω.1 hcard hε hε1 hmtrunc ω.2
  exact hmem

/-- A concrete family over actual nonzero configurations in which the
canonical cross slot is projected and every other cross covariance is
left complete.  The amplitude and physical variables remain explicit:
no equality with the original moment is asserted. -/
def r324ActualCrossRoutedSingleProjectedTerm
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (v :
      R324NonzeroCombinedFourierConfiguration
          ρ ε α β κp κm π →
        Fin (2 * m) → T4)
    (amplitude :
      R324NonzeroCombinedFourierConfiguration
        ρ ε α β κp κm π → ℂ)
    (ω :
      R324NonzeroCombinedFourierConfiguration
        ρ ε α β κp κm π) : ℂ :=
  ρ.r324SingleProjectedResidualTerm
    ε κp κm π
    (fun _ => ‖z4EuclideanFrequency (α + β)‖)
    v amplitude
    (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
      ε α β κp κm π hexternal hε hε1 hmtrunc)
    ω

/-- Pointwise structure of the routed term: exactly one projected
covariance, multiplied by complete `etaEpsT4` factors at all remaining
cross slots. -/
theorem r324ActualCrossRoutedSingleProjectedTerm_eq
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (v :
      R324NonzeroCombinedFourierConfiguration
          ρ ε α β κp κm π →
        Fin (2 * m) → T4)
    (amplitude :
      R324NonzeroCombinedFourierConfiguration
        ρ ε α β κp κm π → ℂ)
    (ω :
      R324NonzeroCombinedFourierConfiguration
        ρ ε α β κp κm π) :
    ρ.r324ActualCrossRoutedSingleProjectedTerm
        ε α β κp κm π hexternal hε hε1 hmtrunc
        v amplitude ω =
      amplitude ω *
        (ρ.r324ProjectedCovarianceC ε
            ‖z4EuclideanFrequency (α + β)‖
            (r324ResidualCovarianceDisplacement
              κp κm π (v ω)
              (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
                ε α β κp κm π hexternal
                hε hε1 hmtrunc ω)) *
          ∏ i ∈
              (Finset.univ :
                Finset (R324ResidualCovarianceSlot κp)).erase
                  (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
                    ε α β κp κm π hexternal
                    hε hε1 hmtrunc ω),
            (ρ.etaEpsT4 ε
              (r324ResidualCovarianceDisplacement
                κp κm π (v ω) i) : ℂ)) := by
  unfold r324ActualCrossRoutedSingleProjectedTerm
  unfold r324SingleProjectedResidualTerm
  rw [
    ρ.r324SingleProjectedResidualCovarianceProduct_eq]

/-- Finite slot-fibre bound for the actual nonzero-configuration
family.  The selected-slot function is canonical, so the fibres are
disjoint; the finite index type has at most `m` elements. -/
theorem norm_tsum_r324ActualCrossRoutedSingleProjectedTerm_le
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (v :
      R324NonzeroCombinedFourierConfiguration
          ρ ε α β κp κm π →
        Fin (2 * m) → T4)
    (amplitude :
      R324NonzeroCombinedFourierConfiguration
        ρ ε α β κp κm π → ℂ)
    (hterm :
      Summable
        (ρ.r324ActualCrossRoutedSingleProjectedTerm
          ε α β κp κm π hexternal hε hε1 hmtrunc
          v amplitude)) :
    ‖∑' ω,
        ρ.r324ActualCrossRoutedSingleProjectedTerm
          ε α β κp κm π hexternal hε hε1 hmtrunc
          v amplitude ω‖ ≤
      ∑ i : R324ResidualCovarianceSlot κp,
        r324SingleProjectedSlotMass
          (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
            ε α β κp κm π hexternal hε hε1 hmtrunc)
          (ρ.r324ActualCrossRoutedSingleProjectedTerm
            ε α β κp κm π hexternal hε hε1 hmtrunc
            v amplitude)
          i := by
  exact
    norm_tsum_le_sum_singleProjectedSlotMass
      (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
        ε α β κp κm π hexternal hε hε1 hmtrunc)
      (ρ.r324ActualCrossRoutedSingleProjectedTerm
        ε α β κp κm π hexternal hε hε1 hmtrunc
        v amplitude)
      hterm

end SmoothCutoff

end

end Anderson4D
