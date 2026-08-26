import Anderson4D.DetParametrix.Paper42_Moment.R324MarkerPreservingResidualCollapse

/-!
# Per-mode majorant for the marked R-324 residual block

The marker-preserving residual decomposition leaves exactly one projected
cross covariance in one genuine residual block.  This file expands that
projected factor into its high Fourier modes while every other covariance
in the block remains the complete physical `etaEpsT4` factor.

The resulting pointwise estimate extracts the paper's central
`eighthOrderFrequencyDecay (ε ^ 2 * L)` payoff.  It is deliberately a
per-mode comparison with the covariance at the marked edge deleted.
Standard Proposition 4.1 estimates the complete primitive covariance sum;
it does not estimate this deleted-edge integrand.  Consequently this file
does not claim a projected primitive-kernel bound.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## Exact projected-mode expansion -/

/-- Product of all complete physical covariances in the marked block
except for the unique selected cross edge. -/
def r324MarkedResidualBlockUnselectedCovarianceProduct
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) : ℂ :=
  ∏ i ∈
      ((r324MarkedResidualBlock κp κm π selected).filter
        (fun i => i < momentCombinedPairing κp κm π i)).erase
        (r324ResidualMarkedLowerEndpoint selected),
    (ρ.etaEpsT4 ε
      (v i - v (momentCombinedPairing κp κm π i)) : ℂ)

/-- One high Fourier mode at the marked cross edge, multiplied by all
unselected complete covariance factors in its genuine residual block. -/
def r324MarkedResidualBlockModeTerm
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4)
    (k : Z4) : ℂ :=
  ρ.r324HighCovarianceModeTerm ε L
      (v (r324ResidualMarkedLowerEndpoint selected) -
        v (r324ResidualMarkedUpperEndpoint π selected)) k *
    ρ.r324MarkedResidualBlockUnselectedCovarianceProduct
      ε κp κm π selected v

/-- The ordinary complete covariance factor on the same physical block
is the selected full `etaEpsT4` covariance times the deleted-edge
product.  Together with
`pairingCovarianceProductOn_eq_residualPrimitiveBlock`, this identifies
the precise input controlled by Proposition 4.1. -/
theorem pairingCovarianceProductOn_markedBlock_eq_selected_mul_unselected
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    (pairingCovarianceProductOn ρ ε
        (momentCombinedPairing κp κm π)
        (r324MarkedResidualBlock κp κm π selected) v : ℂ) =
      (ρ.etaEpsT4 ε
        (v (r324ResidualMarkedLowerEndpoint selected) -
          v (r324ResidualMarkedUpperEndpoint π selected)) : ℂ) *
        ρ.r324MarkedResidualBlockUnselectedCovarianceProduct
          ε κp κm π selected v := by
  let marked :=
    r324ResidualMarkedLowerEndpoint selected
  let κ := momentCombinedPairing κp κm π
  let B := r324MarkedResidualBlock κp κm π selected
  let S := B.filter fun i => i < κ i
  have hmarkedS : marked ∈ S := by
    rw [Finset.mem_filter]
    refine
      ⟨r324ResidualMarkedLowerEndpoint_mem_markedBlock
          κp κm π selected, ?_⟩
    change
      r324ResidualMarkedLowerEndpoint selected <
        momentCombinedPairing κp κm π
          (r324ResidualMarkedLowerEndpoint selected)
    rw [
      momentCombinedPairing_r324ResidualMarkedLowerEndpoint
        κp κm π selected]
    exact r324ResidualMarkedLowerEndpoint_lt_upper
      κp κm π selected
  change
    ((∏ i ∈ S,
      ρ.etaEpsT4 ε (v i - v (κ i)) : ℝ) : ℂ) =
      (ρ.etaEpsT4 ε
        (v marked -
          v (r324ResidualMarkedUpperEndpoint π selected)) : ℂ) *
        ∏ i ∈ S.erase marked,
          (ρ.etaEpsT4 ε (v i - v (κ i)) : ℂ)
  push_cast
  rw [← Finset.mul_prod_erase S
    (fun i =>
      (ρ.etaEpsT4 ε (v i - v (κ i)) : ℂ)) hmarkedS]
  rw [
    momentCombinedPairing_r324ResidualMarkedLowerEndpoint
      κp κm π selected]

theorem summable_r324MarkedResidualBlockModeTerm
    {m : ℕ} {ε : ℝ} (hε : 0 < ε) (L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    Summable
      (ρ.r324MarkedResidualBlockModeTerm
        ε L κp κm π selected v) := by
  exact
    (ρ.summable_r324HighCovarianceModeTerm hε L
      (v (r324ResidualMarkedLowerEndpoint selected) -
        v (r324ResidualMarkedUpperEndpoint π selected))).mul_right _

/-- The actual marked-block covariance product is the absolutely
convergent sum of the one-mode marked terms.  No unselected covariance is
Fourier-expanded here. -/
theorem r324MarkedPairingCovarianceProductOn_markedBlock_eq_tsum_modes
    {m : ℕ} {ε : ℝ} (hε : 0 < ε) (L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    ρ.r324MarkedPairingCovarianceProductOn ε L
        (momentCombinedPairing κp κm π)
        (r324ResidualMarkedLowerEndpoint selected)
        (r324MarkedResidualBlock κp κm π selected) v =
      ∑' k : Z4,
        ρ.r324MarkedResidualBlockModeTerm
          ε L κp κm π selected v k := by
  rw [ρ.r324MarkedResidualBlockProduct_eq]
  unfold r324ProjectedCovarianceC
    r324MarkedResidualBlockModeTerm
    r324MarkedResidualBlockUnselectedCovarianceProduct
  exact
    (ρ.summable_r324HighCovarianceModeTerm hε L
      (v (r324ResidualMarkedLowerEndpoint selected) -
        v (r324ResidualMarkedUpperEndpoint π selected)))
      |>.tsum_mul_right _ |>.symm

/-! ## The central frequency payoff -/

/-- The high-mode indicator itself satisfies the same uniform central
frequency bound, including modes outside the retained set (where it
vanishes). -/
theorem exists_norm_r324HighCovarianceModeTerm_le_decay :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ε L : ℝ} {z : T4} {k : Z4},
        0 < ε →
        ε ≤ 1 / 4 →
        0 ≤ L →
        ‖ρ.r324HighCovarianceModeTerm ε L z k‖ ≤
          C * eighthOrderFrequencyDecay (ε ^ 2 * L) := by
  obtain ⟨C, hC, hmode⟩ :=
    ρ.exists_r324_highCovarianceModeTerm_bound
  refine ⟨C, hC, ?_⟩
  intro ε L z k hε hεsmall hL
  by_cases hk : k ∈ r324HighModeSet ε L
  · simpa [r324HighCovarianceModeTerm, hk] using
      hmode hε hεsmall hL hk
  · simp only [r324HighCovarianceModeTerm]
    simp [hk,
      mul_nonneg hC.le
        (eighthOrderFrequencyDecay_nonneg _)]

/-- The product of norms of the complete, unselected physical
covariances. -/
def r324MarkedResidualBlockUnselectedCovarianceMass
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) : ℝ :=
  ∏ i ∈
      ((r324MarkedResidualBlock κp κm π selected).filter
        (fun i => i < momentCombinedPairing κp κm π i)).erase
        (r324ResidualMarkedLowerEndpoint selected),
    ‖(ρ.etaEpsT4 ε
      (v i - v (momentCombinedPairing κp κm π i)) : ℂ)‖

theorem r324MarkedResidualBlockUnselectedCovarianceMass_nonneg
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    0 ≤ ρ.r324MarkedResidualBlockUnselectedCovarianceMass
      ε κp κm π selected v := by
  exact Finset.prod_nonneg fun _ _ => norm_nonneg _

theorem norm_r324MarkedResidualBlockUnselectedCovarianceProduct
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    ‖ρ.r324MarkedResidualBlockUnselectedCovarianceProduct
        ε κp κm π selected v‖ =
      ρ.r324MarkedResidualBlockUnselectedCovarianceMass
        ε κp κm π selected v := by
  unfold r324MarkedResidualBlockUnselectedCovarianceProduct
    r324MarkedResidualBlockUnselectedCovarianceMass
  rw [norm_prod]

/-- Honest per-mode marked-block comparison.

The selected projected covariance supplies the central decay.  The
remaining factor is exactly the product of norms of all unselected,
unexpanded `etaEpsT4` covariances in the same physical block. -/
theorem exists_norm_r324MarkedResidualBlockModeTerm_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m : ℕ} {ε L : ℝ}
        {κp κm : PartialPairing (Fin m)}
        {π : κp.singles ≃ κm.singles}
        {selected : R324ResidualCovarianceSlot κp}
        {v : Fin (2 * m) → T4} {k : Z4},
        0 < ε →
        ε ≤ 1 / 4 →
        0 ≤ L →
        ‖ρ.r324MarkedResidualBlockModeTerm
            ε L κp κm π selected v k‖ ≤
          C * eighthOrderFrequencyDecay (ε ^ 2 * L) *
            ρ.r324MarkedResidualBlockUnselectedCovarianceMass
              ε κp κm π selected v := by
  obtain ⟨C, hC, hmode⟩ :=
    ρ.exists_norm_r324HighCovarianceModeTerm_le_decay
  refine ⟨C, hC, ?_⟩
  intro m ε L κp κm π selected v k hε hεsmall hL
  unfold r324MarkedResidualBlockModeTerm
  rw [norm_mul,
    ρ.norm_r324MarkedResidualBlockUnselectedCovarianceProduct]
  exact
    mul_le_mul_of_nonneg_right
      (hmode hε hεsmall hL)
      (ρ.r324MarkedResidualBlockUnselectedCovarianceMass_nonneg
        ε κp κm π selected v)

/-- The same bound after multiplying by an arbitrary genuine Green-chain
or endpoint amplitude.  This is the pointwise consumer needed before
integrating a marked primitive coordinate. -/
theorem exists_norm_mul_r324MarkedResidualBlockModeTerm_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m : ℕ} {ε L : ℝ}
        {κp κm : PartialPairing (Fin m)}
        {π : κp.singles ≃ κm.singles}
        {selected : R324ResidualCovarianceSlot κp}
        {v : Fin (2 * m) → T4} {k : Z4} {amplitude : ℂ},
        0 < ε →
        ε ≤ 1 / 4 →
        0 ≤ L →
        ‖amplitude *
            ρ.r324MarkedResidualBlockModeTerm
              ε L κp κm π selected v k‖ ≤
          C * eighthOrderFrequencyDecay (ε ^ 2 * L) *
            (‖amplitude‖ *
              ρ.r324MarkedResidualBlockUnselectedCovarianceMass
                ε κp κm π selected v) := by
  obtain ⟨C, hC, hterm⟩ :=
    ρ.exists_norm_r324MarkedResidualBlockModeTerm_le
  refine ⟨C, hC, ?_⟩
  intro m ε L κp κm π selected v k amplitude
    hε hεsmall hL
  rw [norm_mul]
  have hbase :=
    hterm (m := m) (ε := ε) (L := L)
      (κp := κp) (κm := κm) (π := π)
      (selected := selected) (v := v) (k := k)
      hε hεsmall hL
  have h :=
    mul_le_mul_of_nonneg_left
      hbase
      (norm_nonneg amplitude)
  calc
    ‖amplitude‖ *
        ‖ρ.r324MarkedResidualBlockModeTerm
          ε L κp κm π selected v k‖ ≤
        ‖amplitude‖ *
          (C * eighthOrderFrequencyDecay (ε ^ 2 * L) *
            ρ.r324MarkedResidualBlockUnselectedCovarianceMass
              ε κp κm π selected v) := h
    _ =
        C * eighthOrderFrequencyDecay (ε ^ 2 * L) *
          (‖amplitude‖ *
            ρ.r324MarkedResidualBlockUnselectedCovarianceMass
              ε κp κm π selected v) := by ring

end SmoothCutoff

end

end Anderson4D
