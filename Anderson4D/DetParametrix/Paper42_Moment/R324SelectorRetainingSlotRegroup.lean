import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedQuadCovarianceReassembly
import Anderson4D.ForMathlib.FirstHighTelescope

/-!
# Selector-retaining regrouping by the paper's operator slot

Paper Section 4.2, Step 4(B) first chooses which factor in the operator
composition carries the large frequency shift.  The choice costs only the
finite number of operator factors.  It must happen before any norm is taken
and before the complete primitive-pairing sum is split.

The corrected endpoint-nonzero route label contains much more data than that
paper choice: it also fixes a contraction and a complete Fourier increment
key.  This file forgets those extra components *only as a fibre map*.  Thus
all contractions, increment keys and selector-restricted configurations with
the same underlying operator position remain in one signed series.

No route norm and no entity norm occurs below.  The sole triangle inequality
is the finite one over `Fin m`, matching the paper's choice of one factor in a
composition of length at most the truncation order.
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

/-! ## The complete signed term on one corrected route -/

/-- The contribution of one corrected route to the open covariance series.
The inner selector fibre is still summed before any norm is taken. -/
def r324RefinedQuadOpenCovarianceRouteTerm
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) : ℂ :=
  ∑' a :
      ρ.R324RefinedEndpointNonzeroRouteFiber
        hm ε α β hexternal hε hε1 hmtrunc p route,
    ρ.covarianceModeCoeff ε
        (ρ.r324RefinedRawSelectedCovarianceMode
          hm ε α β hexternal hε hε1 hmtrunc
          p a.1.1 a.1.2) *
      (∫ q,
        r324Flatten
          (ρ.r324RefinedRawOpenCovarianceIntegrand
            hm ε α β hexternal hε hε1 hmtrunc
            p a.1.1 a.1.2) q
        ∂(r324PhysicalMeasure m))

/-- Removing the selected covariance coefficient was an exact operation, so
one open route term is exactly the corresponding signed raw route fibre. -/
theorem r324RefinedQuadOpenCovarianceRouteTerm_eq_raw
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    ρ.r324RefinedQuadOpenCovarianceRouteTerm
        hm ε α β hexternal hε hε1 hmtrunc p route =
      ∑' a :
          ρ.R324RefinedEndpointNonzeroRouteFiber
            hm ε α β hexternal hε hε1 hmtrunc p route,
        ρ.r324RefinedRawFullPairingIntegral hm ε α β p a.1.1 := by
  apply tsum_congr
  intro a
  exact
    (ρ.r324RefinedRawFullPairingIntegral_eq_coeff_mul_openIntegral
      hm ε α β hexternal hε hε1 hmtrunc
      p a.1.1 a.1.2).symm

/-- The complete route family is absolutely summable.  This is inherited
from the original raw Fourier expansion through exact fibrewise regrouping;
it is not obtained by an analytic route budget. -/
theorem summable_r324RefinedQuadOpenCovarianceRouteTerm
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) :
    Summable fun route : R324NonzeroRouteLabel m =>
      ρ.r324RefinedQuadOpenCovarianceRouteTerm
        hm ε α β hexternal hε hε1 hmtrunc p route := by
  let raw :
      ρ.R324RefinedEndpointNonzeroRawConfiguration
          hm ε α β p → ℂ :=
    fun a =>
      ρ.r324RefinedRawFullPairingIntegral hm ε α β p a.1
  let selected :
      ρ.R324RefinedEndpointNonzeroRawConfiguration
          hm ε α β p →
        R324NonzeroRouteLabel m :=
    ρ.r324RefinedEndpointNonzeroRouteLabel
      hm ε α β hexternal hε hε1 hmtrunc p
  have hraw : Summable raw :=
    (ρ.summable_r324RefinedRawFullPairingIntegral
      hm hε α β p).subtype _
  have hfibres :
      Summable fun route : R324NonzeroRouteLabel m =>
        ∑' a :
            ρ.R324RefinedEndpointNonzeroRouteFiber
              hm ε α β hexternal hε hε1 hmtrunc p route,
          ρ.r324RefinedRawFullPairingIntegral
            hm ε α β p a.1.1 := by
    exact (hraw.hasSum.tsum_fiberwise selected).summable
  exact hfibres.congr fun route =>
    (ρ.r324RefinedQuadOpenCovarianceRouteTerm_eq_raw
      hm ε α β hexternal hε hε1 hmtrunc p route).symm

/-! ## Forget only to the operator position -/

/-- Endpoint-nonzero raw configurations whose canonical first-large cross
covariance has the same underlying position in the original `m`-factor
operator composition.  The contraction is deliberately *not* part of the
outer index. -/
abbrev R324RefinedQuadSelectedPositionRawFiber
    {m : ℕ} (ρ : SmoothCutoff) (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) (i : Fin m) :=
  ↥((fun a :
        ρ.R324RefinedEndpointNonzeroRawConfiguration hm ε α β p =>
      (ρ.r324RefinedRawSelectedResidualSlot
        hm ε α β hexternal hε hε1 hmtrunc p a.1 a.2).1) ⁻¹'
    ({i} : Set (Fin m)))

/-! ## What "first" means: the ordered singles enumeration -/

/-- Every slot strictly before the canonical first-large slot fails the
large-increment predicate.  The order here is the paper selector order on
`Fin N`; it is not an order on the ambient physical positions. -/
theorem r324FirstLargeResidualIncrementSlot_not_large_before
    {E : Type*} [SeminormedAddCommGroup E]
    {N : ℕ} (hN : 0 < N)
    (δ : Fin N → E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hNtrunc : N ≤ truncOrder ε)
    (j : Fin N)
    (hj : j < r324FirstLargeResidualIncrementSlot
      hN δ hε hε1 hNtrunc) :
    ¬((Real.sqrt ε / 2) * ‖∑ k, δ k‖ ≤ ‖δ j‖) := by
  intro hjlarge
  have hle := r324FirstLargeResidualIncrementSlot_le
    hN δ hε hε1 hNtrunc j hjlarge
  exact (not_le_of_gt hj) hle

/-- On every earlier slot in the ordered singles enumeration, the actual
cross-pair mode lies in the complementary low set.  This is the missing
"earlier factors low" half of the paper's first-large decomposition. -/
theorem r324CrossPairMode_not_mem_high_before_firstLarge
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (ω : R324NonzeroCombinedFourierConfiguration
      ρ ε α β κp κm π)
    (j : Fin κp.singles.card)
    (hj : j <
      r324FirstLargeResidualIncrementSlot
        (ρ.r324CrossSlot_card_pos_of_external_ne_zero_integral_ne_zero
          ε α β κp κm π hexternal ω.1 ω.2)
        (r324EnumeratedCrossSlotIncrement κp κm π ω.1)
        hε hε1
        (r324CrossSlot_card_le_truncOrder κp hmtrunc)) :
    ω.1 (r324CrossSlotPairIndex κp κm π
        (r324ResidualCovarianceSlotEquiv κp j)) ∉
      r324HighModeSet ε ‖z4EuclideanFrequency (α + β)‖ := by
  let hcard :=
    ρ.r324CrossSlot_card_pos_of_external_ne_zero_integral_ne_zero
      ε α β κp κm π hexternal ω.1 ω.2
  let δ : Fin κp.singles.card → EuclideanSpace ℝ (Fin dim) :=
    r324EnumeratedCrossSlotIncrement κp κm π ω.1
  have hnot := r324FirstLargeResidualIncrementSlot_not_large_before
    hcard δ hε hε1
      (r324CrossSlot_card_le_truncOrder κp hmtrunc) j hj
  have hsum :
      (∑ k, δ k) = z4EuclideanFrequency (α + β) :=
    ρ.sum_r324EnumeratedCrossSlotIncrement_eq_external_of_integral_ne_zero
      ε α β κp κm π ω.1 ω.2
  rw [hsum] at hnot
  change ¬((Real.sqrt ε / 2) *
      ‖z4EuclideanFrequency (α + β)‖ ≤
    ‖z4EuclideanFrequency
      (ω.1 (r324CrossSlotPairIndex κp κm π
        (r324ResidualCovarianceSlotEquiv κp j)))‖)
  rw [← norm_r324CrossSlotIncrement_eq_pairMode
    κp κm π ω.1 (r324ResidualCovarianceSlotEquiv κp j)]
  exact hnot

/-- Therefore every earlier cross-pair mode is retained, unchanged, by the
low-mode indicator. -/
theorem r324LowCovarianceModeTerm_before_firstLarge_eq
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (ω : R324NonzeroCombinedFourierConfiguration
      ρ ε α β κp κm π)
    (j : Fin κp.singles.card)
    (hj : j <
      r324FirstLargeResidualIncrementSlot
        (ρ.r324CrossSlot_card_pos_of_external_ne_zero_integral_ne_zero
          ε α β κp κm π hexternal ω.1 ω.2)
        (r324EnumeratedCrossSlotIncrement κp κm π ω.1)
        hε hε1
        (r324CrossSlot_card_le_truncOrder κp hmtrunc))
    (z : T4) :
    ρ.r324LowCovarianceModeTerm ε
        ‖z4EuclideanFrequency (α + β)‖ z
        (ω.1 (r324CrossSlotPairIndex κp κm π
          (r324ResidualCovarianceSlotEquiv κp j))) =
      ρ.r324CovarianceModeTerm ε z
        (ω.1 (r324CrossSlotPairIndex κp κm π
          (r324ResidualCovarianceSlotEquiv κp j))) := by
  unfold r324LowCovarianceModeTerm
  rw [Set.indicator_of_mem]
  exact
    ρ.r324CrossPairMode_not_mem_high_before_firstLarge
      ε α β κp κm π hexternal hε hε1 hmtrunc ω j hj

/-! ## Paper Step 4(B): the first-high telescope itself -/

/-- The full cross covariance in the canonical ordered-singles
enumeration. -/
def r324EnumeratedCrossFullCovariance
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4)
    (j : Fin κp.singles.card) : ℂ :=
  (ρ.etaEpsT4 ε
    (r324ResidualCovarianceDisplacement κp κm π v
      (r324ResidualCovarianceSlotEquiv κp j)) : ℂ)

/-- The low part of the same enumerated cross covariance. -/
def r324EnumeratedCrossLowCovariance
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4)
    (j : Fin κp.singles.card) : ℂ :=
  ρ.r324LowCovarianceC ε L
    (r324ResidualCovarianceDisplacement κp κm π v
      (r324ResidualCovarianceSlotEquiv κp j))

/-- The high part of the same enumerated cross covariance. -/
def r324EnumeratedCrossHighCovariance
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4)
    (j : Fin κp.singles.card) : ℂ :=
  ρ.r324ProjectedCovarianceC ε L
    (r324ResidualCovarianceDisplacement κp κm π v
      (r324ResidualCovarianceSlotEquiv κp j))

theorem r324EnumeratedCrossFullCovariance_eq_low_add_high
    {m : ℕ} {ε : ℝ} (hε : 0 < ε) (L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4)
    (j : Fin κp.singles.card) :
    ρ.r324EnumeratedCrossFullCovariance ε κp κm π v j =
      ρ.r324EnumeratedCrossLowCovariance ε L κp κm π v j +
        ρ.r324EnumeratedCrossHighCovariance ε L κp κm π v j := by
  exact ρ.etaEpsT4_eq_low_add_projected hε L
    (r324ResidualCovarianceDisplacement κp κm π v
      (r324ResidualCovarianceSlotEquiv κp j))

/-- The all-low term in the paper's exact telescope. -/
def r324AllLowCrossCovarianceProduct
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) : ℂ :=
  ∏ j,
    ρ.r324EnumeratedCrossLowCovariance ε L κp κm π v j

/-- The summand whose first high cross factor is `selectedOrder`: low
before it, high at it, and full after it. -/
def r324FirstHighCrossCovarianceProduct
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4)
    (selectedOrder : Fin κp.singles.card) : ℂ :=
  (∏ j ∈ Finset.univ with j < selectedOrder,
      ρ.r324EnumeratedCrossLowCovariance ε L κp κm π v j) *
    ρ.r324EnumeratedCrossHighCovariance
      ε L κp κm π v selectedOrder *
      ∏ j ∈ Finset.univ with selectedOrder < j,
        ρ.r324EnumeratedCrossFullCovariance ε κp κm π v j

/-- This is exactly the already-proved generic first-high telescope,
specialized to the paper's cross-covariance composition. -/
theorem prod_r324EnumeratedCrossFullCovariance_eq_allLow_add_firstHigh
    {m : ℕ} {ε : ℝ} (hε : 0 < ε) (L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) :
    (∏ j,
      ρ.r324EnumeratedCrossFullCovariance ε κp κm π v j) =
      ρ.r324AllLowCrossCovarianceProduct ε L κp κm π v +
        ∑ selectedOrder,
          ρ.r324FirstHighCrossCovarianceProduct
            ε L κp κm π v selectedOrder := by
  exact Fin.prod_firstHigh
    (ρ.r324EnumeratedCrossFullCovariance ε κp κm π v)
    (ρ.r324EnumeratedCrossLowCovariance ε L κp κm π v)
    (ρ.r324EnumeratedCrossHighCovariance ε L κp κm π v)
    (ρ.r324EnumeratedCrossFullCovariance_eq_low_add_high
      hε L κp κm π v)

/-- Reindexing by ordered singles identifies the paper telescope's full
product with the actual cross-covariance product in (4.18). -/
theorem coe_momentCrossCovarianceProduct_eq_enumerated
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) :
    (momentCrossCovarianceProduct ρ ε m κp κm π v : ℂ) =
      ∏ j,
        ρ.r324EnumeratedCrossFullCovariance ε κp κm π v j := by
  unfold momentCrossCovarianceProduct
    r324EnumeratedCrossFullCovariance
    r324ResidualCovarianceDisplacement
  push_cast
  exact (Equiv.prod_comp (r324ResidualCovarianceSlotEquiv κp)
    (fun i : R324ResidualCovarianceSlot κp =>
      (ρ.etaEpsT4 ε
        (v (leftMomentIndex i.1) -
          v (rightMomentIndex (π i).1)) : ℂ))).symm

/-- Literal paper Step 4(B) identity on the (4.18) cross product. -/
theorem coe_momentCrossCovarianceProduct_eq_allLow_add_firstHigh
    {m : ℕ} {ε : ℝ} (hε : 0 < ε) (L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) :
    (momentCrossCovarianceProduct ρ ε m κp κm π v : ℂ) =
      ρ.r324AllLowCrossCovarianceProduct ε L κp κm π v +
        ∑ selectedOrder,
          ρ.r324FirstHighCrossCovarianceProduct
            ε L κp κm π v selectedOrder := by
  rw [ρ.coe_momentCrossCovarianceProduct_eq_enumerated
    ε κp κm π v]
  exact
    ρ.prod_r324EnumeratedCrossFullCovariance_eq_allLow_add_firstHigh
      hε L κp κm π v

/-- The (4.18) integrand with every residual cross covariance projected
low.  Within-half renormalized factors and all four endpoint phases remain
untouched. -/
def r324AllLowDeterministicMomentIntegrand
    (ε L : ℝ) (m : ℕ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  momentFourierPhase α β x y z w *
    (detIntegrand ρ ε m κp
      (assemble x y fun i => v (leftMomentIndex i)) : ℂ) *
    (detIntegrand ρ ε m κm
      (assemble z w fun i => v (rightMomentIndex i)) : ℂ) *
    ρ.r324AllLowCrossCovarianceProduct ε L κp κm π v

/-- The (4.18) integrand whose first high residual cross covariance is the
displayed ordered-singles slot. -/
def r324FirstHighDeterministicMomentIntegrand
    (ε L : ℝ) (m : ℕ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selectedOrder : Fin κp.singles.card)
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  momentFourierPhase α β x y z w *
    (detIntegrand ρ ε m κp
      (assemble x y fun i => v (leftMomentIndex i)) : ℂ) *
    (detIntegrand ρ ε m κm
      (assemble z w fun i => v (rightMomentIndex i)) : ℂ) *
    ρ.r324FirstHighCrossCovarianceProduct
      ε L κp κm π v selectedOrder

/-- Pointwise paper Step 4(B) on the genuine (4.18) integrand.  The full
signed object is split only into the all-low term and the finite family of
first-high operator slots. -/
theorem deterministicMomentIntegrand_eq_allLow_add_firstHigh
    {ε : ℝ} (hε : 0 < ε) (L : ℝ) (m : ℕ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    deterministicMomentIntegrand ρ ε m α β
        κp κm π x y z w v =
      ρ.r324AllLowDeterministicMomentIntegrand
        ε L m α β κp κm π x y z w v +
        ∑ selectedOrder,
          ρ.r324FirstHighDeterministicMomentIntegrand
            ε L m α β κp κm π selectedOrder x y z w v := by
  let A : ℂ :=
    momentFourierPhase α β x y z w *
      (detIntegrand ρ ε m κp
        (assemble x y fun i => v (leftMomentIndex i)) : ℂ) *
      (detIntegrand ρ ε m κm
        (assemble z w fun i => v (rightMomentIndex i)) : ℂ)
  have hcross :=
    ρ.coe_momentCrossCovarianceProduct_eq_allLow_add_firstHigh
      hε L κp κm π v
  calc
    deterministicMomentIntegrand ρ ε m α β
        κp κm π x y z w v =
      A * (momentCrossCovarianceProduct ρ ε m κp κm π v : ℂ) := by
        unfold deterministicMomentIntegrand A momentFourierPhase
        push_cast
        ring
    _ = A *
        (ρ.r324AllLowCrossCovarianceProduct ε L κp κm π v +
          ∑ selectedOrder,
            ρ.r324FirstHighCrossCovarianceProduct
              ε L κp κm π v selectedOrder) := by
      rw [hcross]
    _ = A * ρ.r324AllLowCrossCovarianceProduct ε L κp κm π v +
        ∑ selectedOrder,
          A * ρ.r324FirstHighCrossCovarianceProduct
            ε L κp κm π v selectedOrder := by
      rw [mul_add, Finset.mul_sum]
    _ = ρ.r324AllLowDeterministicMomentIntegrand
          ε L m α β κp κm π x y z w v +
        ∑ selectedOrder,
          ρ.r324FirstHighDeterministicMomentIntegrand
            ε L m α β κp κm π selectedOrder x y z w v := by
      unfold r324AllLowDeterministicMomentIntegrand
        r324FirstHighDeterministicMomentIntegrand
      rfl

/-! ## The all-low Fourier coefficient vanishes off zero shift -/

/-- Fourier support condition for the all-low cross term. -/
def r324AllCrossPairModesLow
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π) : Prop :=
  ∀ j : Fin κp.singles.card,
    q (r324CrossSlotPairIndex κp κm π
      (r324ResidualCovarianceSlotEquiv κp j)) ∉
      r324HighModeSet ε L

/-- The all-low part of one integrated full-pairing Fourier coefficient.
This is the Fourier coefficient obtained after the spatial first-high
telescope, before summing configurations. -/
noncomputable def r324AllLowFullPairingFourierIntegral
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q : R324CombinedFourierConfiguration κp κm π) : ℂ := by
  classical
  exact if r324AllCrossPairModesLow ε
      ‖z4EuclideanFrequency (α + β)‖ κp κm π q then
    ρ.r324FullPairingFourierIntegral ε α β
      ⟨momentCombinedPairing κp κm π,
        momentCombinedPairing_isFull κp κm π⟩ q
  else 0

/-- A nonzero integrated Fourier configuration cannot be all-low.  This is
exactly the capped pigeonhole step used by the paper to delete the all-low
term; no pointwise spatial vanishing is asserted. -/
theorem not_r324AllCrossPairModesLow_of_integral_ne_zero
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (q : R324CombinedFourierConfiguration κp κm π)
    (hne :
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q ≠ 0) :
    ¬r324AllCrossPairModesLow ε
      ‖z4EuclideanFrequency (α + β)‖ κp κm π q := by
  intro hall
  let ω : R324NonzeroCombinedFourierConfiguration
      ρ ε α β κp κm π := ⟨q, hne⟩
  let selected :=
    ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
      ε α β κp κm π hexternal hε hε1 hmtrunc ω
  let selectedOrder : Fin κp.singles.card :=
    (r324ResidualCovarianceSlotEquiv κp).symm selected
  have hhigh :=
    ρ.firstLargeCrossPairModeForNonzeroConfiguration_mem_highModeSet
      ε α β κp κm π hexternal hε hε1 hmtrunc ω
  change q (r324CrossSlotPairIndex κp κm π selected) ∈
    r324HighModeSet ε ‖z4EuclideanFrequency (α + β)‖ at hhigh
  have hselected :
      r324ResidualCovarianceSlotEquiv κp selectedOrder = selected := by
    exact (r324ResidualCovarianceSlotEquiv κp).apply_symm_apply selected
  exact (hall selectedOrder) (by
    simpa only [hselected] using hhigh)

/-- Consequently every all-low integrated Fourier coefficient is zero at
nonzero external shift. -/
theorem r324AllLowFullPairingFourierIntegral_eq_zero
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (q : R324CombinedFourierConfiguration κp κm π) :
    ρ.r324AllLowFullPairingFourierIntegral
        ε α β κp κm π q = 0 := by
  classical
  unfold r324AllLowFullPairingFourierIntegral
  split_ifs with hall
  · by_cases hne :
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q = 0
    · exact hne
    · exact (ρ.not_r324AllCrossPairModesLow_of_integral_ne_zero
        ε α β κp κm π hexternal hε hε1 hmtrunc q hne hall).elim
  · rfl

/-- The complete all-low Fourier series therefore vanishes, while all
configuration and primitive-pairing sums remain signed. -/
theorem tsum_r324AllLowFullPairingFourierIntegral_eq_zero
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε) :
    (∑' q : R324CombinedFourierConfiguration κp κm π,
      ρ.r324AllLowFullPairingFourierIntegral
        ε α β κp κm π q) = 0 := by
  calc
    (∑' q : R324CombinedFourierConfiguration κp κm π,
      ρ.r324AllLowFullPairingFourierIntegral
        ε α β κp κm π q) =
        ∑' _q : R324CombinedFourierConfiguration κp κm π, (0 : ℂ) := by
      apply tsum_congr
      intro q
      exact ρ.r324AllLowFullPairingFourierIntegral_eq_zero
        ε α β κp κm π hexternal hε hε1 hmtrunc q
    _ = 0 := tsum_zero

/-! ## The exact low/high/full guarded configuration -/

/-- One pair-mode factor in the paper's first-large expansion.  Cross slots
before the selected slot (in the ordered-singles enumeration) are guarded
low, the selected slot is guarded high, and every other pair mode is left
full.  This remains a fixed Fourier-configuration term; no norm occurs. -/
def r324CanonicalFirstLargeGuardedPairModeFactor
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (ω : R324NonzeroCombinedFourierConfiguration
      ρ ε α β κp κm π)
    (v : Fin (2 * m) → T4)
    (r : Fin ((momentCombinedPairing κp κm π).pairSupport.filter
      (fun a => a < momentCombinedPairing κp κm π a)).card) : ℂ :=
  let hcard :=
    ρ.r324CrossSlot_card_pos_of_external_ne_zero_integral_ne_zero
      ε α β κp κm π hexternal ω.1 ω.2
  let selectedOrder :=
    r324FirstLargeResidualIncrementSlot hcard
      (r324EnumeratedCrossSlotIncrement κp κm π ω.1)
      hε hε1 (r324CrossSlot_card_le_truncOrder κp hmtrunc)
  if ∃ j : Fin κp.singles.card,
      j < selectedOrder ∧
        r = r324CrossSlotPairIndex κp κm π
          (r324ResidualCovarianceSlotEquiv κp j) then
    let a := (r324PairFinEquiv
      (momentCombinedPairing κp κm π) r).1
    ρ.r324LowCovarianceModeTerm ε
      ‖z4EuclideanFrequency (α + β)‖
      (v a - v (momentCombinedPairing κp κm π a))
      (ω.1 r)
  else
    ρ.r324SelectedHighPairModeFactor ε
      ‖z4EuclideanFrequency (α + β)‖
      κp κm π ω.1
      (r324ResidualCovarianceSlotEquiv κp selectedOrder) v r

/-- The guards are exact on the canonical nonzero configuration: all
earlier modes are genuinely low and the selected mode is genuinely high.
Thus the low/high/full factor equals the existing selected-high factor. -/
theorem r324CanonicalFirstLargeGuardedPairModeFactor_eq_selectedHigh
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (ω : R324NonzeroCombinedFourierConfiguration
      ρ ε α β κp κm π)
    (v : Fin (2 * m) → T4)
    (r : Fin ((momentCombinedPairing κp κm π).pairSupport.filter
      (fun a => a < momentCombinedPairing κp κm π a)).card) :
    ρ.r324CanonicalFirstLargeGuardedPairModeFactor
        ε α β κp κm π hexternal hε hε1 hmtrunc ω v r =
      ρ.r324SelectedHighPairModeFactor ε
        ‖z4EuclideanFrequency (α + β)‖
        κp κm π ω.1
        (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
          ε α β κp κm π hexternal hε hε1 hmtrunc ω) v r := by
  classical
  let hcard :=
    ρ.r324CrossSlot_card_pos_of_external_ne_zero_integral_ne_zero
      ε α β κp κm π hexternal ω.1 ω.2
  let δ : Fin κp.singles.card → EuclideanSpace ℝ (Fin dim) :=
    r324EnumeratedCrossSlotIncrement κp κm π ω.1
  let selectedOrder :=
    r324FirstLargeResidualIncrementSlot hcard δ hε hε1
      (r324CrossSlot_card_le_truncOrder κp hmtrunc)
  have hselected :
      ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
          ε α β κp κm π hexternal hε hε1 hmtrunc ω =
        r324ResidualCovarianceSlotEquiv κp selectedOrder := by
    rfl
  rw [hselected]
  unfold r324CanonicalFirstLargeGuardedPairModeFactor
  dsimp only
  split_ifs with hbefore
  · obtain ⟨j, hj, hr⟩ := hbefore
    have hjne :
        r324ResidualCovarianceSlotEquiv κp j ≠
          r324ResidualCovarianceSlotEquiv κp selectedOrder := by
      intro heq
      have hjeq := (r324ResidualCovarianceSlotEquiv κp).injective heq
      exact (ne_of_lt hj) hjeq
    have hrne :
        r ≠ r324CrossSlotPairIndex κp κm π
          (r324ResidualCovarianceSlotEquiv κp selectedOrder) := by
      intro heq
      apply hjne
      apply r324CrossSlotPairIndex_injective κp κm π
      exact hr.symm.trans heq
    unfold r324SelectedHighPairModeFactor
    rw [if_neg hrne]
    unfold r324PairModeTerm
    have hlow :=
      ρ.r324LowCovarianceModeTerm_before_firstLarge_eq
        ε α β κp κm π hexternal hε hε1 hmtrunc ω j hj
        (v (r324PairFinEquiv
              (momentCombinedPairing κp κm π) r).1 -
          v (momentCombinedPairing κp κm π
            (r324PairFinEquiv
              (momentCombinedPairing κp κm π) r).1))
    simpa only [hr] using hlow
  · rfl

/-- Product of the paper-ordered low/high/full factors for one complete
Fourier configuration. -/
def r324CanonicalFirstLargeGuardedCovarianceConfigurationTerm
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (ω : R324NonzeroCombinedFourierConfiguration
      ρ ε α β κp κm π)
    (v : Fin (2 * m) → T4) : ℂ :=
  ∏ r,
    ρ.r324CanonicalFirstLargeGuardedPairModeFactor
      ε α β κp κm π hexternal hε hε1 hmtrunc ω v r

/-- The complete guarded covariance product is exactly the existing
selected-high product, without splitting any primitive-pairing sum. -/
theorem r324CanonicalFirstLargeGuardedCovarianceConfigurationTerm_eq_selectedHigh
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (ω : R324NonzeroCombinedFourierConfiguration
      ρ ε α β κp κm π)
    (v : Fin (2 * m) → T4) :
    ρ.r324CanonicalFirstLargeGuardedCovarianceConfigurationTerm
        ε α β κp κm π hexternal hε hε1 hmtrunc ω v =
      ρ.r324SelectedHighCovarianceConfigurationTerm ε
        ‖z4EuclideanFrequency (α + β)‖
        κp κm π ω.1
        (ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
          ε α β κp κm π hexternal hε hε1 hmtrunc ω) v := by
  unfold r324CanonicalFirstLargeGuardedCovarianceConfigurationTerm
    r324SelectedHighCovarianceConfigurationTerm
  apply Finset.prod_congr rfl
  intro r _hr
  exact
    ρ.r324CanonicalFirstLargeGuardedPairModeFactor_eq_selectedHigh
      ε α β κp κm π hexternal hε hε1 hmtrunc ω v r

/-! ## Resumming one fixed selector slot -/

/-- The unrestricted mode factor for a *fixed* selector position in the
ordered-singles enumeration.  This is the literal operator-factor
low/high/full decomposition used in paper Step 4(B). -/
def r324FixedSelectorGuardedPairModeFactor
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selectedOrder : Fin κp.singles.card)
    (v : Fin (2 * m) → T4)
    (r : Fin ((momentCombinedPairing κp κm π).pairSupport.filter
      (fun a => a < momentCombinedPairing κp κm π a)).card)
    (k : Z4) : ℂ :=
  let a := (r324PairFinEquiv
    (momentCombinedPairing κp κm π) r).1
  if ∃ j : Fin κp.singles.card,
      j < selectedOrder ∧
        r = r324CrossSlotPairIndex κp κm π
          (r324ResidualCovarianceSlotEquiv κp j) then
    ρ.r324LowCovarianceModeTerm ε L
      (v a - v (momentCombinedPairing κp κm π a)) k
  else if r = r324CrossSlotPairIndex κp κm π
      (r324ResidualCovarianceSlotEquiv κp selectedOrder) then
    ρ.r324HighCovarianceModeTerm ε L
      (v a - v (momentCombinedPairing κp κm π a)) k
  else
    ρ.r324PairModeTerm ε
      (momentCombinedPairing κp κm π) v r k

/-- One unrestricted Fourier assignment for the fixed-selector guarded
covariance product. -/
def r324FixedSelectorGuardedCovarianceConfigurationTerm
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selectedOrder : Fin κp.singles.card)
    (v : Fin (2 * m) → T4)
    (q : R324CombinedFourierConfiguration κp κm π) : ℂ :=
  finSeriesAssignmentTerm
    ((momentCombinedPairing κp κm π).pairSupport.filter
      (fun a => a < momentCombinedPairing κp κm π a)).card
    (ρ.r324FixedSelectorGuardedPairModeFactor
      ε L κp κm π selectedOrder v) q

/-- The configuration-level meaning of the fixed selector: every earlier
cross mode is low and the chosen cross mode is high.  No condition is put
on later cross modes or on within-half pairs. -/
def r324FixedSelectorConfigurationCondition
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selectedOrder : Fin κp.singles.card)
    (q : R324CombinedFourierConfiguration κp κm π) : Prop :=
  (∀ j : Fin κp.singles.card, j < selectedOrder →
      q (r324CrossSlotPairIndex κp κm π
        (r324ResidualCovarianceSlotEquiv κp j)) ∉
        r324HighModeSet ε L) ∧
    q (r324CrossSlotPairIndex κp κm π
      (r324ResidualCovarianceSlotEquiv κp selectedOrder)) ∈
      r324HighModeSet ε L

/-- On an endpoint-nonzero configuration, the low-prefix/high-current
condition is equivalent to saying that the displayed slot is the canonical
first-large slot. -/
theorem r324FixedSelectorConfigurationCondition_iff_firstLargeOrder
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (ω : R324NonzeroCombinedFourierConfiguration
      ρ ε α β κp κm π)
    (selectedOrder : Fin κp.singles.card) :
    r324FixedSelectorConfigurationCondition ε
        ‖z4EuclideanFrequency (α + β)‖
        κp κm π selectedOrder ω.1 ↔
      r324FirstLargeResidualIncrementSlot
          (ρ.r324CrossSlot_card_pos_of_external_ne_zero_integral_ne_zero
            ε α β κp κm π hexternal ω.1 ω.2)
          (r324EnumeratedCrossSlotIncrement κp κm π ω.1)
          hε hε1
          (r324CrossSlot_card_le_truncOrder κp hmtrunc) =
        selectedOrder := by
  let hcard :=
    ρ.r324CrossSlot_card_pos_of_external_ne_zero_integral_ne_zero
      ε α β κp κm π hexternal ω.1 ω.2
  let δ : Fin κp.singles.card → EuclideanSpace ℝ (Fin dim) :=
    r324EnumeratedCrossSlotIncrement κp κm π ω.1
  let selected :=
    r324FirstLargeResidualIncrementSlot hcard δ hε hε1
      (r324CrossSlot_card_le_truncOrder κp hmtrunc)
  have hsum :
      (∑ j, δ j) = z4EuclideanFrequency (α + β) :=
    ρ.sum_r324EnumeratedCrossSlotIncrement_eq_external_of_integral_ne_zero
      ε α β κp κm π ω.1 ω.2
  have hselectedHigh :
      ω.1 (r324CrossSlotPairIndex κp κm π
          (r324ResidualCovarianceSlotEquiv κp selected)) ∈
        r324HighModeSet ε ‖z4EuclideanFrequency (α + β)‖ := by
    change (Real.sqrt ε / 2) *
        ‖z4EuclideanFrequency (α + β)‖ ≤
      ‖z4EuclideanFrequency
        (ω.1 (r324CrossSlotPairIndex κp κm π
          (r324ResidualCovarianceSlotEquiv κp selected)))‖
    rw [← norm_r324CrossSlotIncrement_eq_pairMode
      κp κm π ω.1 (r324ResidualCovarianceSlotEquiv κp selected)]
    change (Real.sqrt ε / 2) *
        ‖z4EuclideanFrequency (α + β)‖ ≤ ‖δ selected‖
    rw [← hsum]
    exact r324FirstLargeResidualIncrementSlot_spec
      hcard δ hε hε1
        (r324CrossSlot_card_le_truncOrder κp hmtrunc)
  constructor
  · intro hcondition
    have hselectedOrderLarge :
        (Real.sqrt ε / 2) * ‖∑ j, δ j‖ ≤
          ‖δ selectedOrder‖ := by
      rw [hsum]
      change (Real.sqrt ε / 2) *
          ‖z4EuclideanFrequency (α + β)‖ ≤
        ‖r324CrossSlotIncrement κp κm π ω.1
          (r324ResidualCovarianceSlotEquiv κp selectedOrder)‖
      rw [norm_r324CrossSlotIncrement_eq_pairMode]
      exact hcondition.2
    have hle : selected ≤ selectedOrder :=
      r324FirstLargeResidualIncrementSlot_le
        hcard δ hε hε1
          (r324CrossSlot_card_le_truncOrder κp hmtrunc)
        selectedOrder hselectedOrderLarge
    have hge : selectedOrder ≤ selected := by
      exact not_lt.mp fun hlt =>
        hcondition.1 selected hlt hselectedHigh
    exact le_antisymm hle hge
  · intro hselectedEq
    refine ⟨?_, ?_⟩
    · intro j hj
      apply ρ.r324CrossPairMode_not_mem_high_before_firstLarge
        ε α β κp κm π hexternal hε hε1 hmtrunc ω j
      simpa only [hselectedEq] using hj
    · simpa only [← hselectedEq] using hselectedHigh

/-- The original full configuration term restricted to the fixed-selector
condition. -/
noncomputable def r324FixedSelectorFilteredCovarianceConfigurationTerm
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selectedOrder : Fin κp.singles.card)
    (v : Fin (2 * m) → T4)
    (q : R324CombinedFourierConfiguration κp κm π) : ℂ := by
  classical
  exact if r324FixedSelectorConfigurationCondition
      ε L κp κm π selectedOrder q then
    ρ.r324CovarianceFourierConfigurationTerm ε
      (momentCombinedPairing κp κm π) v q
  else 0

/-- The factorized low/high/full configuration term is precisely the
indicator of the fixed-selector condition times the original full
configuration term. -/
theorem r324FixedSelectorGuardedCovarianceConfigurationTerm_eq_ite
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selectedOrder : Fin κp.singles.card)
    (v : Fin (2 * m) → T4)
    (q : R324CombinedFourierConfiguration κp κm π) :
    ρ.r324FixedSelectorGuardedCovarianceConfigurationTerm
        ε L κp κm π selectedOrder v q =
      ρ.r324FixedSelectorFilteredCovarianceConfigurationTerm
        ε L κp κm π selectedOrder v q := by
  classical
  unfold r324FixedSelectorFilteredCovarianceConfigurationTerm
  by_cases hcondition : r324FixedSelectorConfigurationCondition
      ε L κp κm π selectedOrder q
  · rw [if_pos hcondition]
    unfold r324FixedSelectorGuardedCovarianceConfigurationTerm
      r324CovarianceFourierConfigurationTerm
      finSeriesAssignmentTerm
    apply Finset.prod_congr rfl
    intro r _hr
    unfold r324FixedSelectorGuardedPairModeFactor
    dsimp only
    split_ifs with hbefore hselected
    · obtain ⟨j, hj, hr⟩ := hbefore
      have hlow :
          q (r324CrossSlotPairIndex κp κm π
            (r324ResidualCovarianceSlotEquiv κp j)) ∈
            (r324HighModeSet ε L)ᶜ :=
        hcondition.1 j hj
      have hlowr : q r ∈ (r324HighModeSet ε L)ᶜ := by
        simpa only [hr] using hlow
      unfold r324LowCovarianceModeTerm
      rw [Set.indicator_of_mem hlowr]
      unfold r324PairModeTerm
      rfl
    · have hhigh := hcondition.2
      have hhighr : q r ∈ r324HighModeSet ε L := by
        simpa only [hselected] using hhigh
      unfold r324HighCovarianceModeTerm
      rw [Set.indicator_of_mem hhighr]
      unfold r324PairModeTerm
      rfl
    · rfl
  · rw [if_neg hcondition]
    unfold r324FixedSelectorConfigurationCondition at hcondition
    by_cases hselected :
        q (r324CrossSlotPairIndex κp κm π
          (r324ResidualCovarianceSlotEquiv κp selectedOrder)) ∈
          r324HighModeSet ε L
    · have hbeforeExists : ∃ j : Fin κp.singles.card,
          j < selectedOrder ∧
            q (r324CrossSlotPairIndex κp κm π
              (r324ResidualCovarianceSlotEquiv κp j)) ∈
              r324HighModeSet ε L := by
        by_contra hnone
        apply hcondition
        refine ⟨?_, hselected⟩
        intro j hj
        by_contra hjhigh
        exact hnone ⟨j, hj, hjhigh⟩
      obtain ⟨j, hj, hjhigh⟩ := hbeforeExists
      unfold r324FixedSelectorGuardedCovarianceConfigurationTerm
        finSeriesAssignmentTerm
      apply Finset.prod_eq_zero (Finset.mem_univ
        (r324CrossSlotPairIndex κp κm π
          (r324ResidualCovarianceSlotEquiv κp j)))
      unfold r324FixedSelectorGuardedPairModeFactor
      dsimp only
      rw [if_pos ⟨j, hj, rfl⟩]
      unfold r324LowCovarianceModeTerm
      simp [hjhigh]
    · unfold r324FixedSelectorGuardedCovarianceConfigurationTerm
        finSeriesAssignmentTerm
      apply Finset.prod_eq_zero (Finset.mem_univ
        (r324CrossSlotPairIndex κp κm π
          (r324ResidualCovarianceSlotEquiv κp selectedOrder)))
      unfold r324FixedSelectorGuardedPairModeFactor
      dsimp only
      have hnotBefore : ¬∃ j : Fin κp.singles.card,
          j < selectedOrder ∧
            r324CrossSlotPairIndex κp κm π
                (r324ResidualCovarianceSlotEquiv κp selectedOrder) =
              r324CrossSlotPairIndex κp κm π
                (r324ResidualCovarianceSlotEquiv κp j) := by
        rintro ⟨j, hj, heq⟩
        have hslot := r324CrossSlotPairIndex_injective κp κm π heq
        have horder := (r324ResidualCovarianceSlotEquiv κp).injective hslot
        exact (ne_of_gt hj) horder
      rw [if_neg hnotBefore, if_pos rfl]
      unfold r324HighCovarianceModeTerm
      simp [hselected]

/-- The deterministic spatial product after resumming the fixed selector:
low covariances before it, the high projected covariance at it, and full
covariances at all other pair slots. -/
def r324FixedSelectorGuardedCovarianceProduct
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selectedOrder : Fin κp.singles.card)
    (v : Fin (2 * m) → T4) : ℂ :=
  ∏ r : Fin ((momentCombinedPairing κp κm π).pairSupport.filter
      (fun a => a < momentCombinedPairing κp κm π a)).card,
    let a := (r324PairFinEquiv
      (momentCombinedPairing κp κm π) r).1
    if ∃ j : Fin κp.singles.card,
        j < selectedOrder ∧
          r = r324CrossSlotPairIndex κp κm π
            (r324ResidualCovarianceSlotEquiv κp j) then
      ρ.r324LowCovarianceC ε L
        (v a - v (momentCombinedPairing κp κm π a))
    else if r = r324CrossSlotPairIndex κp κm π
        (r324ResidualCovarianceSlotEquiv κp selectedOrder) then
      ρ.r324ProjectedCovarianceC ε L
        (v a - v (momentCombinedPairing κp κm π a))
    else
      (ρ.etaEpsT4 ε
        (v a - v (momentCombinedPairing κp κm π a)) : ℂ)

/-- Exact finite-product Fubini: the unrestricted fixed-selector Fourier
series resums to the paper's low/high/full spatial product. -/
theorem tsum_r324FixedSelectorGuardedCovarianceConfigurationTerm
    {m : ℕ} {ε : ℝ} (hε : 0 < ε) (L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selectedOrder : Fin κp.singles.card)
    (v : Fin (2 * m) → T4) :
    (∑' q : R324CombinedFourierConfiguration κp κm π,
      ρ.r324FixedSelectorGuardedCovarianceConfigurationTerm
        ε L κp κm π selectedOrder v q) =
      ρ.r324FixedSelectorGuardedCovarianceProduct
        ε L κp κm π selectedOrder v := by
  let n := ((momentCombinedPairing κp κm π).pairSupport.filter
    (fun a => a < momentCombinedPairing κp κm π a)).card
  let f : Fin n → Z4 → ℂ :=
    ρ.r324FixedSelectorGuardedPairModeFactor
      ε L κp κm π selectedOrder v
  have hf : ∀ r, Summable fun k => ‖f r k‖ := by
    intro r
    unfold f r324FixedSelectorGuardedPairModeFactor
    dsimp only
    split_ifs
    · exact (ρ.summable_r324LowCovarianceModeTerm hε L
        (v (r324PairFinEquiv
              (momentCombinedPairing κp κm π) r).1 -
          v (momentCombinedPairing κp κm π
            (r324PairFinEquiv
              (momentCombinedPairing κp κm π) r).1))).norm
    · exact (ρ.summable_r324HighCovarianceModeTerm hε L
        (v (r324PairFinEquiv
              (momentCombinedPairing κp κm π) r).1 -
          v (momentCombinedPairing κp κm π
            (r324PairFinEquiv
              (momentCombinedPairing κp κm π) r).1))).norm
    · exact ρ.summable_norm_r324PairModeTerm hε
        (momentCombinedPairing κp κm π) v r
  calc
    (∑' q : R324CombinedFourierConfiguration κp κm π,
      ρ.r324FixedSelectorGuardedCovarianceConfigurationTerm
        ε L κp κm π selectedOrder v q) =
        ∏ r : Fin n, ∑' k : Z4, f r k := by
      exact tsum_finSeriesAssignmentTerm n f hf
    _ = ρ.r324FixedSelectorGuardedCovarianceProduct
        ε L κp κm π selectedOrder v := by
      unfold r324FixedSelectorGuardedCovarianceProduct
      apply Finset.prod_congr rfl
      intro r _hr
      unfold f r324FixedSelectorGuardedPairModeFactor
      dsimp only
      split_ifs
      · rfl
      · rfl
      · exact ρ.complexFourierCovarianceT4_eq_etaEpsT4 hε
          (v (r324PairFinEquiv
                (momentCombinedPairing κp κm π) r).1 -
            v (momentCombinedPairing κp κm π
              (r324PairFinEquiv
                (momentCombinedPairing κp κm π) r).1))

/-- The complete full-pairing Fourier integrand with the paper-order
low/high/full guards exposed.  All Green factors, endpoint phases, and the
complete covariance configuration remain in the same signed term. -/
def r324CanonicalFirstLargeGuardedFullPairingFourierIntegrand
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (ω : R324NonzeroCombinedFourierConfiguration
      ρ ε α β κp κm π)
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  let κ : R324FullPairingIndex m :=
    ⟨momentCombinedPairing κp κm π,
      momentCombinedPairing_isFull κp κm π⟩
  let e := (momentContractionEquivFullPairing m).symm κ
  momentFourierPhase α β x y z w *
    renormalizedGreenSkeleton e.1
      (assemble x y fun j => v (leftMomentIndex j)) *
    renormalizedGreenSkeleton e.2.1
      (assemble z w fun j => v (rightMomentIndex j)) *
    ρ.r324CanonicalFirstLargeGuardedCovarianceConfigurationTerm
      ε α β κp κm π hexternal hε hε1 hmtrunc ω v

/-- Exposing all first-large guards leaves the genuine selected-high
Fourier integrand unchanged pointwise. -/
theorem r324CanonicalFirstLargeGuardedFullPairingFourierIntegrand_eq_selectedHigh
    {m : ℕ}
    (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (ω : R324NonzeroCombinedFourierConfiguration
      ρ ε α β κp κm π)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    ρ.r324CanonicalFirstLargeGuardedFullPairingFourierIntegrand
        ε α β κp κm π hexternal hε hε1 hmtrunc
        ω x y z w v =
      ρ.r324SelectedHighFullPairingFourierIntegrand
        ε α β κp κm π hexternal hε hε1 hmtrunc
        ω x y z w v := by
  unfold r324CanonicalFirstLargeGuardedFullPairingFourierIntegrand
    r324SelectedHighFullPairingFourierIntegrand
  dsimp only
  rw [
    ρ.r324CanonicalFirstLargeGuardedCovarianceConfigurationTerm_eq_selectedHigh
      ε α β κp κm π hexternal hε hε1 hmtrunc ω v]

/-- The complete signed open series at one operator position.  In
particular, the contraction and increment-key components of the route are
summed *inside* this value. -/
def r324RefinedQuadOpenCovarianceSlotSeries
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (i : Fin m) : ℂ :=
  ∑' a : R324RefinedQuadSelectedPositionRawFiber
      ρ hm ε α β hexternal hε hε1 hmtrunc p i,
    ρ.r324RefinedRawFullPairingIntegral hm ε α β p a.1.1

/-- The genuine five-group physical carrier of one fixed operator slot.
The `tsum` still ranges simultaneously over all contractions and all
selector-restricted Fourier configurations in the refined schedule. -/
def r324RefinedQuadSelectedPositionPhysicalIntegrand
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (i : Fin m) (q : R324PhysicalPoint m) : ℂ :=
  ∑' a : R324RefinedQuadSelectedPositionRawFiber
      ρ hm ε α β hexternal hε hε1 hmtrunc p i,
    r324Flatten
      (ρ.r324RefinedRawEndpointIntegrand
        hm ε α β p a.1.1) q

/-- This fixed-slot physical carrier uses exactly the already-proved
canonical selected-high integrands.  In particular, no unrestricted
projected covariance is substituted for the selector subtype. -/
theorem r324RefinedQuadSelectedPositionPhysicalIntegrand_eq_selectedHigh
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (i : Fin m) (q : R324PhysicalPoint m) :
    ρ.r324RefinedQuadSelectedPositionPhysicalIntegrand
        hm ε α β hexternal hε hε1 hmtrunc p i q =
      ∑' a : R324RefinedQuadSelectedPositionRawFiber
          ρ hm ε α β hexternal hε hε1 hmtrunc p i,
        r324Flatten
          (ρ.r324SelectedHighFullPairingFourierIntegrand
            ε α β
            (r324RefinedRawMomentContraction p a.1.1).1
            (r324RefinedRawMomentContraction p a.1.1).2.1
            (r324RefinedRawMomentContraction p a.1.1).2.2
            hexternal hε hε1 hmtrunc
            (ρ.r324RefinedRawNonzeroCombinedConfiguration
              hm ε α β p a.1.1 a.1.2)) q := by
  unfold r324RefinedQuadSelectedPositionPhysicalIntegrand
  apply tsum_congr
  intro a
  exact ρ.r324RefinedRawEndpointIntegrand_eq_selectedHigh
    hm ε α β hexternal hε hε1 hmtrunc p a.1.1 a.1.2
    q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2

/-- The same fixed operator-position carrier, now written with the paper's
low-before/high-current/full-after guards exposed inside every complete
signed Fourier term. -/
theorem r324RefinedQuadSelectedPositionPhysicalIntegrand_eq_guarded
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (i : Fin m) (q : R324PhysicalPoint m) :
    ρ.r324RefinedQuadSelectedPositionPhysicalIntegrand
        hm ε α β hexternal hε hε1 hmtrunc p i q =
      ∑' a : R324RefinedQuadSelectedPositionRawFiber
          ρ hm ε α β hexternal hε hε1 hmtrunc p i,
        r324Flatten
          (ρ.r324CanonicalFirstLargeGuardedFullPairingFourierIntegrand
            ε α β
            (r324RefinedRawMomentContraction p a.1.1).1
            (r324RefinedRawMomentContraction p a.1.1).2.1
            (r324RefinedRawMomentContraction p a.1.1).2.2
            hexternal hε hε1 hmtrunc
            (ρ.r324RefinedRawNonzeroCombinedConfiguration
              hm ε α β p a.1.1 a.1.2)) q := by
  rw [ρ.r324RefinedQuadSelectedPositionPhysicalIntegrand_eq_selectedHigh
    hm ε α β hexternal hε hε1 hmtrunc p i q]
  apply tsum_congr
  intro a
  exact
    (ρ.r324CanonicalFirstLargeGuardedFullPairingFourierIntegrand_eq_selectedHigh
      ε α β
      (r324RefinedRawMomentContraction p a.1.1).1
      (r324RefinedRawMomentContraction p a.1.1).2.1
      (r324RefinedRawMomentContraction p a.1.1).2.2
      hexternal hε hε1 hmtrunc
      (ρ.r324RefinedRawNonzeroCombinedConfiguration
        hm ε α β p a.1.1 a.1.2)
      q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2).symm

/-- Exact Fubini boundary for one operator slot.  Absolute summability is
inherited from the original raw five-group expansion and is used only to
exchange the signed `tsum` with the physical integral. -/
theorem integral_r324RefinedQuadSelectedPositionPhysicalIntegrand_eq_slotSeries
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (i : Fin m) :
    (∫ q,
      ρ.r324RefinedQuadSelectedPositionPhysicalIntegrand
        hm ε α β hexternal hε hε1 hmtrunc p i q
      ∂(r324PhysicalMeasure m)) =
      ρ.r324RefinedQuadOpenCovarianceSlotSeries
        hm ε α β hexternal hε hε1 hmtrunc p i := by
  let S := R324RefinedQuadSelectedPositionRawFiber
    ρ hm ε α β hexternal hε hε1 hmtrunc p i
  let F : S → R324PhysicalPoint m → ℂ := fun a q =>
    r324Flatten
      (ρ.r324RefinedRawEndpointIntegrand
        hm ε α β p a.1.1) q
  have hFint : ∀ a : S,
      Integrable (F a) (r324PhysicalMeasure m) := by
    intro a
    exact ρ.integrable_r324Flatten_refinedRawEndpointIntegrand
      hm ε α β p a.1.1
  have hFnorm : Summable fun a : S =>
      ∫ q, ‖F a q‖ ∂(r324PhysicalMeasure m) := by
    have hnonzero : Summable fun a :
        ρ.R324RefinedEndpointNonzeroRawConfiguration
          hm ε α β p =>
        ρ.r324RefinedRawEndpointL1 hm ε α β p a.1 :=
      (ρ.summable_r324RefinedRawEndpointL1
        hm hε α β p).subtype _
    have hselected : Summable fun a : S =>
        ρ.r324RefinedRawEndpointL1 hm ε α β p a.1.1 :=
      hnonzero.subtype _
    simpa only [F, r324RefinedRawEndpointL1] using hselected
  rw [show
    ρ.r324RefinedQuadSelectedPositionPhysicalIntegrand
        hm ε α β hexternal hε hε1 hmtrunc p i =
      fun q => ∑' a : S, F a q by rfl]
  rw [← integral_tsum_of_summable_integral_norm hFint hFnorm]
  unfold r324RefinedQuadOpenCovarianceSlotSeries
  apply tsum_congr
  intro a
  exact ρ.integral_r324Flatten_refinedRawEndpointIntegrand_eq_rawFullPairingIntegral
    hm ε α β p a.1.1

/-- Exact paper-order regrouping: the whole open covariance series is a
finite sum over operator positions.  No norm occurs in this equality. -/
theorem r324RefinedQuadOpenCovarianceSeries_eq_sum_slotSeries
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) :
    ρ.r324RefinedQuadOpenCovarianceSeries
        hm ε α β hexternal hε hε1 hmtrunc p =
      ∑ i : Fin m,
        ρ.r324RefinedQuadOpenCovarianceSlotSeries
          hm ε α β hexternal hε hε1 hmtrunc p i := by
  let raw :
      ρ.R324RefinedEndpointNonzeroRawConfiguration hm ε α β p → ℂ :=
    fun a =>
      ρ.r324RefinedRawFullPairingIntegral hm ε α β p a.1
  let selected :
      ρ.R324RefinedEndpointNonzeroRawConfiguration hm ε α β p → Fin m :=
    fun a =>
      (ρ.r324RefinedRawSelectedResidualSlot
        hm ε α β hexternal hε hε1 hmtrunc p a.1 a.2).1
  have hraw : Summable raw :=
    (ρ.summable_r324RefinedRawFullPairingIntegral
      hm hε α β p).subtype _
  have hfibres := hraw.hasSum.tsum_fiberwise selected
  calc
    ρ.r324RefinedQuadOpenCovarianceSeries
        hm ε α β hexternal hε hε1 hmtrunc p =
        ∑' route : R324NonzeroRouteLabel m,
          ∑' a :
              ρ.R324RefinedEndpointNonzeroRouteFiber
                hm ε α β hexternal hε hε1 hmtrunc p route,
            ρ.r324RefinedRawFullPairingIntegral
              hm ε α β p a.1.1 := by
      unfold r324RefinedQuadOpenCovarianceSeries
      apply tsum_congr
      intro route
      exact ρ.r324RefinedQuadOpenCovarianceRouteTerm_eq_raw
        hm ε α β hexternal hε hε1 hmtrunc p route
    _ = ∑' a :
          ρ.R324RefinedEndpointNonzeroRawConfiguration hm ε α β p,
        raw a := by
      exact
        (ρ.tsum_r324RefinedEndpointNonzero_eq_routeFibres
          hm hε α β hexternal hε1 hmtrunc p).symm
    _ = ∑' i : Fin m,
          ∑' a : ↥(selected ⁻¹' ({i} : Set (Fin m))),
            raw a.1 := hfibres.tsum_eq.symm
    _ = ∑ i : Fin m,
          ρ.r324RefinedQuadOpenCovarianceSlotSeries
            hm ε α β hexternal hε hε1 hmtrunc p i := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro i _hi
      rfl

/-- The only triangle inequality introduced by the selector is the finite
one over the at most `m` operator positions.  Every primitive-pairing and
Fourier sum remains signed inside each summand. -/
theorem norm_r324RefinedQuadOpenCovarianceSeries_le_sum_slotSeries
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) :
    ‖ρ.r324RefinedQuadOpenCovarianceSeries
        hm ε α β hexternal hε hε1 hmtrunc p‖ ≤
      ∑ i : Fin m,
        ‖ρ.r324RefinedQuadOpenCovarianceSlotSeries
          hm ε α β hexternal hε hε1 hmtrunc p i‖ := by
  rw [ρ.r324RefinedQuadOpenCovarianceSeries_eq_sum_slotSeries
    hm ε α β hexternal hε hε1 hmtrunc p]
  exact norm_sum_le _ _

/-! ## The exact remaining physical consumer boundary -/

/-- Paper Step 4(B), after the finite choice of an operator factor and
before the final `Fin m` summation.  This is a bound on one *complete
signed* slot series: contractions, primitive pairings, routes and Fourier
configurations have not been normed separately.

The intended producer first identifies this series with the operator-slot
expansion having the chosen factor high-projected, all earlier factors
low-projected, and all later factors unprojected.  It then repeats the
already formalized complete Steps 2--3 collapse on that physical carrier. -/
def R324RefinedQuadOperatorSlotCollapseBound
    (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hlog : 1 ≤ |Real.log ε|) (hm2 : 2 ≤ m)
    (hmtrunc : m ≤ truncOrder ε) (hexternal : α + β ≠ 0)
    (hm : 0 < m) (p : R324RefinedScheduleIndex m) (i : Fin m),
      ‖ρ.r324RefinedQuadOpenCovarianceSlotSeries
          hm ε α β hexternal hε
            (hεsmall.trans (by norm_num)) hmtrunc p i‖ ≤
        (paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β) *
          ((m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
            ε⁻¹ ^ (8 : ℕ) *
              eighthOrderFrequencyDecay
                (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖))

/-- A uniform complete signed bound for one operator slot closes the whole
open covariance series.  The finite slot count costs only `m ≤ 2^m`, which
is absorbed into the geometric base. -/
theorem R324RefinedQuadOperatorSlotCollapseBound.toOpenCovarianceSeriesBound
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (h : R324RefinedQuadOperatorSlotCollapseBound ρ K) :
    R324RefinedQuadOpenCovarianceSeriesBound ρ (2 * K) := by
  intro ε m α β hε hεsmall hlog hm2 hmtrunc hexternal hm p
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  let D : ℝ :=
    paperFourthOrderModeDecay α *
      paperFourthOrderModeDecay β
  let A : ℝ :=
    (m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
      ε⁻¹ ^ (8 : ℕ) *
        eighthOrderFrequencyDecay
          (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖)
  have hD0 : 0 ≤ D := by
    exact mul_nonneg
      (paperFourthOrderModeDecay_nonneg α)
      (paperFourthOrderModeDecay_nonneg β)
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) (pow_nonneg hK m))
          (pow_nonneg (abs_nonneg _) _))
        (by positivity))
      (eighthOrderFrequencyDecay_nonneg _)
  have hmcast : (m : ℝ) ≤ (2 : ℝ) ^ m := by
    exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
  calc
    ‖ρ.r324RefinedQuadOpenCovarianceSeries
        hm ε α β hexternal hε hε1 hmtrunc p‖ ≤
      ∑ i : Fin m,
        ‖ρ.r324RefinedQuadOpenCovarianceSlotSeries
          hm ε α β hexternal hε hε1 hmtrunc p i‖ :=
      ρ.norm_r324RefinedQuadOpenCovarianceSeries_le_sum_slotSeries
        hm ε α β hexternal hε hε1 hmtrunc p
    _ ≤ ∑ _i : Fin m, D * A := by
      apply Finset.sum_le_sum
      intro i _hi
      dsimp only [D, A]
      exact h m α β hε hεsmall hlog hm2 hmtrunc
        hexternal hm p i
    _ = (m : ℝ) * (D * A) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [Finset.card_univ, Fintype.card_fin]
    _ ≤ (2 : ℝ) ^ m * (D * A) :=
      mul_le_mul_of_nonneg_right hmcast (mul_nonneg hD0 hA0)
    _ =
      (paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β) *
        ((m : ℝ) ^ 8 * (2 * K) ^ m *
          |Real.log ε| ^ (m - 1) * ε⁻¹ ^ (8 : ℕ) *
            eighthOrderFrequencyDecay
              (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖)) := by
      dsimp only [D, A]
      rw [mul_pow]
      ring

end SmoothCutoff

end

end Anderson4D
