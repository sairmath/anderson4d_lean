import Anderson4D.DetParametrix.Paper42_Moment.R324SelectorFiberBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324MarkerPreservingResidualCollapse
import Anderson4D.DetParametrix.Paper42_Moment.R324HighFrequencySlack
import Anderson4D.PermSum.OpenEdgeWeight

/-!
# Selected R-324 fibre to the one-open-edge consumer

This file joins four already exact boundaries without enlarging the
canonical selector fibre:

* its selected Fourier pair is the genuine marked residual cross edge;
* the selected fixed-mode product factors at precisely that edge;
* the spare `ε⁴` from the selected cutoff mode pays the two appended
  lattice-chain edges; and
* the augmented word is primitive and is therefore a genuine input to
  Proposition 5.7.

No unrestricted projected-covariance fibre and no diagnostic
pairing-dependent marker sum is introduced.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open PlaneTree
open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## The canonical selector is the genuine marked residual edge -/

/-- The selected pair-mode factor in the exact selector fibre is the
high-mode term on the endpoints of the unique marked residual edge. -/
theorem r324SelectedHighPairModeFactor_selected_eq_marked
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    ρ.r324SelectedHighPairModeFactor
        ε L κp κm π q selected v
        (r324CrossSlotPairIndex κp κm π selected) =
      ρ.r324HighCovarianceModeTerm ε L
        (v (r324ResidualMarkedLowerEndpoint selected) -
          v (r324ResidualMarkedUpperEndpoint π selected))
        (q (r324CrossSlotPairIndex κp κm π selected)) := by
  unfold r324SelectedHighPairModeFactor
  rw [if_pos rfl]
  dsimp only
  rw [r324PairFinEquiv_r324CrossSlotPairIndex]
  change
    ρ.r324HighCovarianceModeTerm ε L
        (v (r324ResidualMarkedLowerEndpoint selected) -
          v (momentCombinedPairing κp κm π
            (r324ResidualMarkedLowerEndpoint selected)))
        (q (r324CrossSlotPairIndex κp κm π selected)) =
      _
  rw [momentCombinedPairing_r324ResidualMarkedLowerEndpoint]

/-- Product of every fixed Fourier pair mode except the canonical
selected cross slot.  This retains the restricted configuration
coordinate verbatim. -/
def r324SelectedHighUnselectedPairModeProduct
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) : ℂ :=
  ∏ j ∈ (Finset.univ.erase
      (r324CrossSlotPairIndex κp κm π selected)),
    ρ.r324SelectedHighPairModeFactor
      ε L κp κm π q selected v j

/-- Exact factorization of the restricted fixed-mode covariance product
at its canonical selected slot. -/
theorem r324SelectedHighCovarianceConfigurationTerm_eq_marked_mul_unselected
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    ρ.r324SelectedHighCovarianceConfigurationTerm
        ε L κp κm π q selected v =
      ρ.r324HighCovarianceModeTerm ε L
        (v (r324ResidualMarkedLowerEndpoint selected) -
          v (r324ResidualMarkedUpperEndpoint π selected))
        (q (r324CrossSlotPairIndex κp κm π selected)) *
      ρ.r324SelectedHighUnselectedPairModeProduct
        ε L κp κm π q selected v := by
  unfold r324SelectedHighCovarianceConfigurationTerm
    r324SelectedHighUnselectedPairModeProduct
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j =>
      ρ.r324SelectedHighPairModeFactor
        ε L κp κm π q selected v j)
    (Finset.mem_univ _)]
  rw [ρ.r324SelectedHighPairModeFactor_selected_eq_marked]

/-! ## Paying the two appended chain edges -/

/-- If the cell box has the natural ultraviolet size `M ≤ ε⁻¹`, the
spare `ε⁴` pays both inverse lattice-edge factors with a uniform
constant. -/
theorem eps_four_mul_boxPenalty_sq_le
    {ε : ℝ} {M : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hM : (M : ℝ) ≤ ε⁻¹) :
    ε ^ 4 * (1 + (2 * (M : ℝ)) ^ 2) ^ 2 ≤ 25 := by
  have hMdiv : (M : ℝ) ≤ 1 / ε := by
    simpa [one_div] using hM
  have hMε : (M : ℝ) * ε ≤ 1 :=
    (le_div_iff₀ hε).mp hMdiv
  have hεM : ε * (M : ℝ) ≤ 1 := by
    simpa [mul_comm] using hMε
  have hε0 : 0 ≤ ε := hε.le
  have hM0 : 0 ≤ (M : ℝ) := by positivity
  have hεsq : ε ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (1 - ε)]
  have hεMsq : (ε * (M : ℝ)) ^ 2 ≤ 1 := by
    calc
      (ε * (M : ℝ)) ^ 2 ≤ (1 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hε0 hM0) hεM 2
      _ = 1 := by norm_num
  have hbase0 :
      0 ≤ ε ^ 2 * (1 + (2 * (M : ℝ)) ^ 2) := by
    positivity
  have hbase :
      ε ^ 2 * (1 + (2 * (M : ℝ)) ^ 2) ≤ 5 := by
    calc
      ε ^ 2 * (1 + (2 * (M : ℝ)) ^ 2) =
          ε ^ 2 + 4 * (ε * (M : ℝ)) ^ 2 := by ring
      _ ≤ 1 + 4 * 1 := by gcongr
      _ = 5 := by norm_num
  calc
    ε ^ 4 * (1 + (2 * (M : ℝ)) ^ 2) ^ 2 =
        (ε ^ 2 * (1 + (2 * (M : ℝ)) ^ 2)) ^ 2 := by
      ring
    _ ≤ 5 ^ 2 :=
      pow_le_pow_left₀ hbase0 hbase 2
    _ = 25 := by norm_num

/-- Covariance-coefficient form of the complete scalar ledger: the
canonical high mode times both box penalties is uniformly bounded by
the paper's eighth-order routed decay. -/
theorem exists_boxPenalty_sq_mul_covarianceModeCoeff_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ε L : ℝ} {M : ℕ} {k : Z4},
        0 < ε →
        ε ≤ 1 / 4 →
        0 ≤ L →
        1 ≤ ε ^ 2 * L →
        k ∈ r324HighModeSet ε L →
        (M : ℝ) ≤ ε⁻¹ →
        (1 + (2 * (M : ℝ)) ^ 2) ^ 2 *
            ‖ρ.covarianceModeCoeff ε k‖ ≤
          C * eighthOrderFrequencyDecay (ε ^ 2 * L) := by
  obtain ⟨C0, hC0, hcoeff⟩ :=
    ρ.exists_r324_covarianceModeCoeff_bound_with_eps_four
  refine ⟨25 * C0, mul_pos (by norm_num) hC0, ?_⟩
  intro ε L M k hε hεsmall hL hlarge hk hM
  have hε1 : ε ≤ 1 := by linarith
  have hpay :=
    eps_four_mul_boxPenalty_sq_le hε hε1 hM
  have hB :
      0 ≤ (1 + (2 * (M : ℝ)) ^ 2) ^ 2 := by positivity
  have hdecay :
      0 ≤ eighthOrderFrequencyDecay (ε ^ 2 * L) :=
    eighthOrderFrequencyDecay_nonneg _
  calc
    (1 + (2 * (M : ℝ)) ^ 2) ^ 2 *
          ‖ρ.covarianceModeCoeff ε k‖ ≤
        (1 + (2 * (M : ℝ)) ^ 2) ^ 2 *
          (C0 * ε ^ 4 *
            eighthOrderFrequencyDecay (ε ^ 2 * L)) :=
      mul_le_mul_of_nonneg_left
        (hcoeff hε hεsmall hL hlarge hk) hB
    _ =
        C0 * eighthOrderFrequencyDecay (ε ^ 2 * L) *
          (ε ^ 4 *
            (1 + (2 * (M : ℝ)) ^ 2) ^ 2) := by ring
    _ ≤
        C0 * eighthOrderFrequencyDecay (ε ^ 2 * L) * 25 := by
      exact mul_le_mul_of_nonneg_left hpay
        (mul_nonneg hC0.le hdecay)
    _ = (25 * C0) *
          eighthOrderFrequencyDecay (ε ^ 2 * L) := by ring

/-! ## Primitive-word consumer -/

/-- The concrete one-open-edge consumer used before Proposition 5.7.
It simultaneously certifies that the dummy-closed word is primitive and
that the selected high-frequency coefficient, including both appended
chain-edge costs, leaves exactly the routed eighth-order decay.

The pairing and marker are fixed inputs here; there is no
pairing-dependent arbitrary marker family. -/
theorem exists_selectedOpenEdgePrimitiveConsumer :
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
          ‖ρ.covarianceModeCoeff ε k‖ *
              heppChainWeight z w ≤
            C * eighthOrderFrequencyDecay (ε ^ 2 * L) *
              heppChainWeight z
                (openEdgeAugmentedWord w a b) := by
  obtain ⟨C, hC, hcoeff⟩ :=
    ρ.exists_boxPenalty_sq_mul_covarianceModeCoeff_bound
  refine ⟨C, hC, ?_⟩
  intro t m M κ a b w Nm z ε L k hm hκab hab
    hfull hprimitive hrespect hadm hε hεsmall hL hlarge
    hk hM
  refine
    ⟨noProperLeafBlock_openEdgeAugmentedWord
        κ a b hκab hab hfull hprimitive w hrespect, ?_⟩
  have hweight :=
    heppChainWeight_le_boxPenalty_sq_mul_openEdgeAugmented
      hm z hadm w a b
  have hnorm : 0 ≤ ‖ρ.covarianceModeCoeff ε k‖ :=
    norm_nonneg _
  have haug :
      0 ≤ heppChainWeight z
        (openEdgeAugmentedWord w a b) :=
    heppChainWeight_nonneg _ _
  have hcoeffB :=
    hcoeff hε hεsmall hL hlarge hk hM
  calc
    ‖ρ.covarianceModeCoeff ε k‖ *
          heppChainWeight z w ≤
        ‖ρ.covarianceModeCoeff ε k‖ *
          ((1 + (2 * (M : ℝ)) ^ 2) ^ 2 *
            heppChainWeight z
              (openEdgeAugmentedWord w a b)) :=
      mul_le_mul_of_nonneg_left hweight hnorm
    _ =
        ((1 + (2 * (M : ℝ)) ^ 2) ^ 2 *
          ‖ρ.covarianceModeCoeff ε k‖) *
            heppChainWeight z
              (openEdgeAugmentedWord w a b) := by ring
    _ ≤
        (C * eighthOrderFrequencyDecay (ε ^ 2 * L)) *
          heppChainWeight z
            (openEdgeAugmentedWord w a b) :=
      mul_le_mul_of_nonneg_right hcoeffB haug

end SmoothCutoff

end

end Anderson4D
