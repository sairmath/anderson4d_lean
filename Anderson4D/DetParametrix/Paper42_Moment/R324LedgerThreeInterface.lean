import Anderson4D.DetParametrix.Paper42_Moment.R324GeneralPeelClosure

/-!
# Case split of the residual general peel ledger (orders `m ≥ 3`)

The single remaining uniform-branch obligation
`R324GeneralPeelLedgerFromThree` demands, for every residual-refined
fibre at order `m ≥ 3`, the bound `K^m |log ε|^{m-1}` on the summed
fibre.  This file splits that obligation along the induction strategy
of paper Section 4.2:

* **pure-cross fibres**: every entity of the fibre carries no
  within-half pair (`κ⁺ = κ⁻ = id`); the fibre is a permutation sum of
  cross-covariance products handled by the multi-window estimate;
* **mixed fibres**: some entity retains a within-half pair, opening a
  parity/difference gain in that half.

The composition theorem proved here shows the two case ledgers exhaust
the residual obligation at one common constant.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## The two fibre classes -/

/-- An order-`m` contraction entity with no within-half pair at all:
both partial pairings are the identity, so all `m` covariance legs are
cross legs. -/
def R324LedgerThreeAllCrossEntity {m : ℕ}
    (e : MomentContraction m) : Prop :=
  e.1 = PartialPairing.id ∧ e.2.1 = PartialPairing.id

/-- A residual-refined fibre all of whose entities are pure-cross. -/
def R324LedgerThreeCrossFibre (m : ℕ)
    (s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))) : Prop :=
  ∀ e ∈ momentRefinedContractionFiber m s r,
    R324LedgerThreeAllCrossEntity e

/-! ## The two case ledgers -/

/-- **Cross-case ledger from order three**: the fibre logarithmic bound
restricted to pure-cross refined fibres. -/
def R324LedgerThreeCrossLedger
    (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 3 ≤ m →
      ∀ s ∈ momentContractionSignatures m,
        ∀ r ∈ momentResidualChainSignaturesAt m s,
          R324LedgerThreeCrossFibre m s r →
            ‖momentRefinedDeterministicTermSum ρ ε m α β s r‖ ≤
              K ^ m * |Real.log ε| ^ (m - 1)

/-- **Mixed-case ledger from order three**: the fibre logarithmic bound
restricted to fibres containing an entity with a within-half pair. -/
def R324LedgerThreeMixedLedger
    (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 3 ≤ m →
      ∀ s ∈ momentContractionSignatures m,
        ∀ r ∈ momentResidualChainSignaturesAt m s,
          ¬ R324LedgerThreeCrossFibre m s r →
            ‖momentRefinedDeterministicTermSum ρ ε m α β s r‖ ≤
              K ^ m * |Real.log ε| ^ (m - 1)

/-! ## The case ledgers exhaust the residual obligation -/

/-- **Composition of the two cases.**  Any pair of case ledgers merges
into the full residual general peel ledger at the common constant
`max K₁ K₂`. -/
theorem r324LedgerThree_generalPeelLedgerFromThree
    {ρ : SmoothCutoff} {K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hcross : R324LedgerThreeCrossLedger ρ K₁)
    (hmixed : R324LedgerThreeMixedLedger ρ K₂) :
    R324GeneralPeelLedgerFromThree ρ (max K₁ K₂) := by
  intro ε m α β hε hε1 hlog hm3 s hs r hr
  have hLpow : (0 : ℝ) ≤ |Real.log ε| ^ (m - 1) :=
    pow_nonneg (abs_nonneg _) _
  by_cases hfib : R324LedgerThreeCrossFibre m s r
  · exact (hcross m α β hε hε1 hlog hm3 s hs r hr hfib).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hK₁ (le_max_left _ _) m) hLpow)
  · exact (hmixed m α β hε hε1 hlog hm3 s hs r hr hfib).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hK₂ (le_max_right _ _) m) hLpow)

end

end Anderson4D
