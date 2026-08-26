import Anderson4D.DetParametrix.Paper42_Moment.R324MarkerPreservingResidualCollapse
import Anderson4D.DetParametrix.Paper42_Moment.R324ProjectedCovariance

/-!
# The Step 4 marking is trivial at a nonpositive threshold

Paper: R-324 — §4.2 — the Step 4 marking is inert at a nonpositive threshold

The proved two-half physical collapse
(`R324TwoHalfToNestedCrossBridge`, `R324CertifiedTwoHalfPhysicalCollapse`)
carries the cross-copy covariances in *marked* form
`r324MarkedPairingCovarianceProductOn ε L κ marked B`, in which one
distinguished lower endpoint has its covariance replaced by the Step 4(B)
high-frequency projection `r324ProjectedCovarianceC ε L`.  That marking
exists for the `⟨ε²(α+β)⟩⁻⁸` pigeonhole and is *not* part of the (4.18)
integrand of Steps 2--3.

This module shows the marking degenerates: the retained mode set is

    r324HighModeSet ε L = {k | (√ε/2)·L ≤ ‖k‖},

so at `L ≤ 0` it is all of `ℤ⁴`, the projection is the complete
covariance, and the marked product is literally the plain covariance
product of (4.18).  Steps 2--3 may therefore run the proved two-half
collapse at `L ≤ 0` and read off exactly the paper's (4.18) integrand,
with no marking to account for; Step 4(B) uses the same machinery at the
genuine threshold.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- At a nonpositive threshold the Step 4 pigeonhole retains every mode. -/
theorem r324HighModeSet_eq_univ {ε L : ℝ} (hL : L ≤ 0) :
    r324HighModeSet ε L = Set.univ := by
  ext k
  simp only [r324HighModeSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  have hsqrt : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have h1 : Real.sqrt ε / 2 * L ≤ 0 := by nlinarith
  exact h1.trans (norm_nonneg _)

/-- Hence every complementary low mode vanishes. -/
theorem r324LowCovarianceModeTerm_eq_zero {ε L : ℝ} (hL : L ≤ 0)
    (z : T4) (k : Z4) :
    ρ.r324LowCovarianceModeTerm ε L z k = 0 := by
  unfold r324LowCovarianceModeTerm
  rw [r324HighModeSet_eq_univ hL]
  simp

/-- The complementary low-mode covariance is zero at a nonpositive
threshold. -/
theorem r324LowCovarianceC_eq_zero {ε L : ℝ} (hL : L ≤ 0) (z : T4) :
    ρ.r324LowCovarianceC ε L z = 0 := by
  unfold r324LowCovarianceC
  rw [tsum_congr (ρ.r324LowCovarianceModeTerm_eq_zero hL z)]
  exact tsum_zero

/-- **The projection is trivial at a nonpositive threshold**: it is the
complete spatial covariance `η_ε` of (4.18). -/
theorem r324ProjectedCovarianceC_eq_etaEpsT4 {ε : ℝ} (hε : 0 < ε)
    {L : ℝ} (hL : L ≤ 0) (z : T4) :
    ρ.r324ProjectedCovarianceC ε L z = (ρ.etaEpsT4 ε z : ℂ) := by
  have hsplit := ρ.etaEpsT4_eq_low_add_projected hε L z
  rw [ρ.r324LowCovarianceC_eq_zero hL z, zero_add] at hsplit
  exact hsplit.symm

/-- **The marked covariance product is the plain one at a nonpositive
threshold**, for *any* distinguished endpoint — including one inside the
block, where `r324MarkedPairingCovarianceProductOn_eq_complete` does not
apply.

This is the identification Steps 2--3 need: the proved two-half
physical collapse, run at `L ≤ 0`, transports exactly the (4.18)
integrand, with the Step 4 marking inert. -/
theorem r324MarkedPairingCovarianceProductOn_eq_plain
    {n : ℕ} {ε : ℝ} (hε : 0 < ε) {L : ℝ} (hL : L ≤ 0)
    (κ : PartialPairing (Fin n)) (marked : Fin n)
    (B : Finset (Fin n)) (v : Fin n → T4) :
    ρ.r324MarkedPairingCovarianceProductOn ε L κ marked B v =
      (pairingCovarianceProductOn ρ ε κ B v : ℂ) := by
  unfold r324MarkedPairingCovarianceProductOn pairingCovarianceProductOn
  push_cast
  apply Finset.prod_congr rfl
  intro i _hi
  by_cases hmarked : i = marked
  · rw [if_pos hmarked]
    exact ρ.r324ProjectedCovarianceC_eq_etaEpsT4 hε hL _
  · rw [if_neg hmarked]

end SmoothCutoff

end

end Anderson4D
