import Anderson4D.DetParametrix.Paper42_Moment.R324CompatibleAnalyticBudgetTrace
import Anderson4D.DetParametrix.Paper42_Moment.R324CompleteOrderAbsorption
import Anderson4D.DetParametrix.Paper42_Moment.R324PhaseAOrderLedgerBridge

/-!
# Absorbing the two within-half scale ledgers and the complete cross run

This file is purely numerical.  It combines the two literal Phase-A scale
products with an inserted majorant at the remaining nested-cross order and
uses the exact three-schedule order identity to obtain one inserted
majorant at the ambient order.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- One explicit base large enough to absorb the two all-Green initial
scale products, the two Phase-A block costs, the complete nested-run base,
and the four endpoint inverse-square masses. -/
def r324TwoHalfCompleteAbsorbedBase
    (A C K B : ℝ) : ℝ :=
  max 1 A ^ 2 * max 1 C * max 1 K * max 1 B *
    max 1 invSqKerMass ^ 2

theorem r324TwoHalfCompleteAbsorbedBase_pos
    (A C K B : ℝ) :
    0 < r324TwoHalfCompleteAbsorbedBase A C K B := by
  unfold r324TwoHalfCompleteAbsorbedBase
  positivity

private theorem pow_le_absorbed_pow
    {a : ℝ} (ha : 0 ≤ a) {r s : ℕ}
    (hrs : r ≤ s) :
    a ^ r ≤ max 1 a ^ s := by
  calc
    a ^ r ≤ max 1 a ^ r :=
      pow_le_pow_left₀ ha (le_max_right _ _) _
    _ ≤ max 1 a ^ s :=
      pow_le_pow_right₀ (le_max_left _ _) hrs

/-- Pure coefficient absorption behind the final two-half/nested order
ledger.  The hypotheses `l₊ ≤ p₊`, `l₋ ≤ p₋` record that every processed
within-half block has positive perturbative order. -/
private theorem r324_twoHalf_complete_coefficient_le
    {A C K B lam : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hB : 0 ≤ B) (hlam : 0 ≤ lam)
    {m pleft pright cross leftLength rightLength : ℕ}
    (hm : 1 ≤ m)
    (horder : pleft + pright + cross = m)
    (hleftLength : leftLength ≤ pleft)
    (hrightLength : rightLength ≤ pright) :
    (A ^ (m + 1) * (C * lam) ^ (2 * pleft) * K ^ leftLength) *
        (A ^ (m + 1) * (C * lam) ^ (2 * pright) * K ^ rightLength) *
        invSqKerMass ^ 4 *
        (B * lam) ^ (2 * cross) ≤
      (r324TwoHalfCompleteAbsorbedBase A C K B * lam) ^ (2 * m) := by
  let dA := max 1 A
  let dC := max 1 C
  let dK := max 1 K
  let dB := max 1 B
  let dM := max 1 invSqKerMass
  have hM : 0 ≤ invSqKerMass := invSqKerMass_nonneg
  have hAexp : 2 * (m + 1) ≤ 4 * m := by omega
  have hCexp : 2 * (pleft + pright) ≤ 2 * m := by omega
  have hKexp : leftLength + rightLength ≤ 2 * m := by omega
  have hBexp : 2 * cross ≤ 2 * m := by omega
  have hMexp : 4 ≤ 4 * m := by omega
  have hApow :
      A ^ (2 * (m + 1)) ≤ dA ^ (4 * m) := by
    exact pow_le_absorbed_pow hA hAexp
  have hCpow :
      C ^ (2 * (pleft + pright)) ≤ dC ^ (2 * m) := by
    exact pow_le_absorbed_pow hC hCexp
  have hKpow :
      K ^ (leftLength + rightLength) ≤ dK ^ (2 * m) := by
    exact pow_le_absorbed_pow hK hKexp
  have hBpow :
      B ^ (2 * cross) ≤ dB ^ (2 * m) := by
    exact pow_le_absorbed_pow hB hBexp
  have hMpow :
      invSqKerMass ^ 4 ≤ dM ^ (4 * m) := by
    exact pow_le_absorbed_pow hM hMexp
  have hconstant :
      A ^ (2 * (m + 1)) *
          C ^ (2 * (pleft + pright)) *
          K ^ (leftLength + rightLength) *
          B ^ (2 * cross) * invSqKerMass ^ 4 ≤
        dA ^ (4 * m) * dC ^ (2 * m) * dK ^ (2 * m) *
          dB ^ (2 * m) * dM ^ (4 * m) := by
    exact mul_le_mul
      (mul_le_mul
        (mul_le_mul
          (mul_le_mul hApow hCpow
            (pow_nonneg hC _)
            (pow_nonneg (zero_le_one.trans (le_max_left 1 A)) _))
          hKpow (pow_nonneg hK _)
          (mul_nonneg
            (pow_nonneg (zero_le_one.trans (le_max_left 1 A)) _)
            (pow_nonneg (zero_le_one.trans (le_max_left 1 C)) _)))
        hBpow (pow_nonneg hB _)
        (mul_nonneg
          (mul_nonneg
            (pow_nonneg (zero_le_one.trans (le_max_left 1 A)) _)
            (pow_nonneg (zero_le_one.trans (le_max_left 1 C)) _))
          (pow_nonneg (zero_le_one.trans (le_max_left 1 K)) _)))
      hMpow (pow_nonneg hM _)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (pow_nonneg (zero_le_one.trans (le_max_left 1 A)) _)
            (pow_nonneg (zero_le_one.trans (le_max_left 1 C)) _))
          (pow_nonneg (zero_le_one.trans (le_max_left 1 K)) _))
        (pow_nonneg (zero_le_one.trans (le_max_left 1 B)) _))
  have hconstant' :
      A ^ (2 * (m + 1)) *
          C ^ (2 * (pleft + pright)) *
          K ^ (leftLength + rightLength) *
          B ^ (2 * cross) * invSqKerMass ^ 4 ≤
        r324TwoHalfCompleteAbsorbedBase A C K B ^ (2 * m) := by
    calc
      _ ≤ dA ^ (4 * m) * dC ^ (2 * m) * dK ^ (2 * m) *
            dB ^ (2 * m) * dM ^ (4 * m) := hconstant
      _ = r324TwoHalfCompleteAbsorbedBase A C K B ^ (2 * m) := by
        dsimp only [dA, dC, dK, dB, dM]
        unfold r324TwoHalfCompleteAbsorbedBase
        rw [mul_pow, mul_pow, mul_pow, mul_pow, pow_mul, pow_mul]
        ring
  have hlamPow : 0 ≤ lam ^ (2 * m) := pow_nonneg hlam _
  have hAcombine :
      A ^ (m + 1) * A ^ (m + 1) = A ^ (2 * (m + 1)) := by
    rw [← pow_add]
    congr 1
    omega
  have hCcombine :
      C ^ (2 * pleft) * C ^ (2 * pright) =
        C ^ (2 * (pleft + pright)) := by
    rw [← pow_add]
    congr 1
    omega
  have hKcombine :
      K ^ leftLength * K ^ rightLength =
        K ^ (leftLength + rightLength) := by
    rw [pow_add]
  have hlamOrder :
      lam ^ (2 * pleft) * lam ^ (2 * pright) *
          lam ^ (2 * cross) = lam ^ (2 * m) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  calc
    (A ^ (m + 1) * (C * lam) ^ (2 * pleft) * K ^ leftLength) *
          (A ^ (m + 1) * (C * lam) ^ (2 * pright) * K ^ rightLength) *
          invSqKerMass ^ 4 * (B * lam) ^ (2 * cross) =
        (A ^ (m + 1) * A ^ (m + 1)) *
          (C ^ (2 * pleft) * C ^ (2 * pright)) *
          (K ^ leftLength * K ^ rightLength) *
          B ^ (2 * cross) * invSqKerMass ^ 4 *
          (lam ^ (2 * pleft) * lam ^ (2 * pright) *
            lam ^ (2 * cross)) := by
      rw [mul_pow C lam, mul_pow C lam, mul_pow B lam]
      ring
    _ =
        (A ^ (2 * (m + 1)) *
          C ^ (2 * (pleft + pright)) *
          K ^ (leftLength + rightLength) *
          B ^ (2 * cross) * invSqKerMass ^ 4) *
          lam ^ (2 * m) := by
      rw [hAcombine, hCcombine, hKcombine, hlamOrder]
    _ ≤ r324TwoHalfCompleteAbsorbedBase A C K B ^ (2 * m) *
          lam ^ (2 * m) :=
      mul_le_mul_of_nonneg_right hconstant' hlamPow
    _ = (r324TwoHalfCompleteAbsorbedBase A C K B * lam) ^
          (2 * m) := by
      rw [mul_pow]

/-- Pointwise inserted-majorant form of the preceding coefficient ledger. -/
theorem r324_twoHalf_complete_majorant_le
    {A C K B lam ε supportConstant : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hB : 0 ≤ B) (hlam : 0 ≤ lam)
    {m pleft pright cross leftLength rightLength : ℕ}
    (hm : 1 ≤ m)
    (horder : pleft + pright + cross = m)
    (hleftLength : leftLength ≤ pleft)
    (hrightLength : rightLength ≤ pright)
    (z : T4) :
    (A ^ (m + 1) * (C * lam) ^ (2 * pleft) * K ^ leftLength) *
        (A ^ (m + 1) * (C * lam) ^ (2 * pright) * K ^ rightLength) *
        invSqKerMass ^ 4 *
        primitiveInsertedMajorant B lam ε supportConstant cross z ≤
      primitiveInsertedMajorant
        (r324TwoHalfCompleteAbsorbedBase A C K B)
        lam ε supportConstant m z := by
  let Q : ℝ :=
    (((ε⁻¹) ^ 2 / |Real.log ε|) * invSqKer z *
        primitiveSupportIndicator supportConstant ε z +
      (1 / |Real.log ε| ^ 2) *
        (torusDistSq z + ε ^ 2)⁻¹ ^ 2)
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    apply add_nonneg
    · exact mul_nonneg
        (mul_nonneg (div_nonneg (by positivity) (abs_nonneg _))
          (invSqKer_nonneg z))
        (primitiveSupportIndicator_nonneg supportConstant ε z)
    · exact mul_nonneg (div_nonneg zero_le_one (sq_nonneg _))
        (pow_nonneg
          (inv_nonneg.mpr
            (add_nonneg (torusDistSq_nonneg z) (sq_nonneg ε))) 2)
  have hcoef := r324_twoHalf_complete_coefficient_le
    hA hC hK hB hlam hm horder hleftLength hrightLength
  unfold primitiveInsertedMajorant
  have hmul := mul_le_mul_of_nonneg_right hcoef hQ
  simpa only [Q, mul_assoc] using hmul

end

end Anderson4D
