import Mathlib

/-!
# Numerical absorption of fixed-cutoff derivative losses

A fixed smooth cutoff may contribute an order-dependent loss of the form
`m⁸ Cderiv^m`.  This module records a deliberately coarse, purely numerical
ledger which absorbs that loss by enlarging both named constants in the
R-324 geometric amplitude.  It assumes no routing certificate and no
analytic estimate.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- The fixed base used to absorb an eighth-degree order loss together with
a cutoff-dependent geometric loss. -/
def r324DerivativeAbsorptionBase (Cderiv : ℝ) : ℝ :=
  256 * max 1 Cderiv

/-- The absorption base is at least one, with no sign assumption on the
cutoff-dependent input. -/
theorem one_le_r324DerivativeAbsorptionBase (Cderiv : ℝ) :
    1 ≤ r324DerivativeAbsorptionBase Cderiv := by
  unfold r324DerivativeAbsorptionBase
  calc
    (1 : ℝ) ≤ 256 := by norm_num
    _ = 256 * 1 := by ring
    _ ≤ 256 * max 1 Cderiv :=
      mul_le_mul_of_nonneg_left
        (le_max_left (1 : ℝ) Cderiv) (by norm_num)

/-- Elementary natural-number growth ledger:
`m⁸` costs at most the fixed geometric base `256^m` for `m ≥ 1`. -/
theorem r324_nat_pow_eight_le_256_pow
    (m : ℕ) (hm : 1 ≤ m) :
    m ^ (8 : ℕ) ≤ 256 ^ m := by
  induction m, hm using Nat.le_induction with
  | base =>
      norm_num
  | succ m hm ih =>
      have hdouble : m + 1 ≤ 2 * m := by
        omega
      calc
        (m + 1) ^ (8 : ℕ) ≤ (2 * m) ^ (8 : ℕ) :=
          Nat.pow_le_pow_left hdouble 8
        _ = 256 * m ^ (8 : ℕ) := by
          rw [mul_pow]
          norm_num
        _ ≤ 256 * 256 ^ m :=
          Nat.mul_le_mul_left 256 ih
        _ = 256 ^ (m + 1) := by
          rw [pow_succ]
          ring

/-- Real-cast form of `r324_nat_pow_eight_le_256_pow`. -/
theorem r324_real_natCast_pow_eight_le_256_pow
    (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) ^ (8 : ℕ) ≤ (256 : ℝ) ^ m := by
  exact_mod_cast r324_nat_pow_eight_le_256_pow m hm

/-- For a base at least one, the longer R-324 exponent `2m-2`, together
with one outer copy, absorbs a power with exponent `m`. -/
theorem r324_pow_le_self_mul_pow_double_sub_two
    {A : ℝ} {m : ℕ}
    (hA : 1 ≤ A) (hm : 1 ≤ m) :
    A ^ m ≤ A * A ^ (2 * m - 2) := by
  have hexponent :
      m ≤ 1 + (2 * m - 2) := by
    omega
  calc
    A ^ m ≤ A ^ (1 + (2 * m - 2)) :=
      pow_le_pow_right₀ hA hexponent
    _ = A * A ^ (2 * m - 2) := by
      rw [pow_add, pow_one]

/-- The raw fixed-cutoff loss is absorbed by one outer copy and the full
`2m-2` geometric power of `r324DerivativeAbsorptionBase Cderiv`. -/
theorem
    r324_derivative_order_loss_le_absorptionBase_mul_power
    {Cderiv : ℝ} {m : ℕ}
    (hCderiv : 0 ≤ Cderiv) (hm : 1 ≤ m) :
    (m : ℝ) ^ (8 : ℕ) * Cderiv ^ m ≤
      r324DerivativeAbsorptionBase Cderiv *
        r324DerivativeAbsorptionBase Cderiv ^ (2 * m - 2) := by
  have horder :=
    r324_real_natCast_pow_eight_le_256_pow m hm
  have hcutoff :
      Cderiv ^ m ≤ (max 1 Cderiv) ^ m :=
    pow_le_pow_left₀ hCderiv
      (le_max_right (1 : ℝ) Cderiv) m
  have hraw :
      (m : ℝ) ^ (8 : ℕ) * Cderiv ^ m ≤
        r324DerivativeAbsorptionBase Cderiv ^ m := by
    calc
      (m : ℝ) ^ (8 : ℕ) * Cderiv ^ m ≤
          (256 : ℝ) ^ m * (max 1 Cderiv) ^ m :=
        mul_le_mul horder hcutoff
          (pow_nonneg hCderiv _)
          (pow_nonneg (by norm_num) _)
      _ = r324DerivativeAbsorptionBase Cderiv ^ m := by
        rw [← mul_pow]
        rfl
  exact hraw.trans
    (r324_pow_le_self_mul_pow_double_sub_two
      (one_le_r324DerivativeAbsorptionBase Cderiv) hm)

/-- **Independent outer/power absorption ledger.**

If a derivative estimate contributes `m⁸ Cderiv^m` in front of the usual
geometric factor, it is enough to make the two independent replacements

* `outerConstant ↦ outerConstant * r324DerivativeAbsorptionBase Cderiv`;
* `powerConstant ↦ powerConstant * r324DerivativeAbsorptionBase Cderiv`.

This is the scalar inequality needed by a later analytic routing theorem. -/
theorem
    r324_derivative_order_loss_absorbed_by_outer_and_power
    {outerConstant powerConstant Cderiv lam : ℝ} {m : ℕ}
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hCderiv : 0 ≤ Cderiv)
    (hlam : 0 ≤ lam)
    (hm : 1 ≤ m) :
    outerConstant *
          ((m : ℝ) ^ (8 : ℕ) * Cderiv ^ m) *
        (powerConstant * lam) ^ (2 * m - 2) ≤
      (outerConstant * r324DerivativeAbsorptionBase Cderiv) *
        ((powerConstant * r324DerivativeAbsorptionBase Cderiv) * lam) ^
          (2 * m - 2) := by
  have hloss :=
    r324_derivative_order_loss_le_absorptionBase_mul_power
      hCderiv hm
  have hbase :
      0 ≤ powerConstant * lam :=
    mul_nonneg hpower hlam
  calc
    outerConstant *
          ((m : ℝ) ^ (8 : ℕ) * Cderiv ^ m) *
        (powerConstant * lam) ^ (2 * m - 2) ≤
      outerConstant *
          (r324DerivativeAbsorptionBase Cderiv *
            r324DerivativeAbsorptionBase Cderiv ^ (2 * m - 2)) *
        (powerConstant * lam) ^ (2 * m - 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hloss houter)
        (pow_nonneg hbase _)
    _ =
      (outerConstant * r324DerivativeAbsorptionBase Cderiv) *
        ((powerConstant * r324DerivativeAbsorptionBase Cderiv) * lam) ^
          (2 * m - 2) := by
      rw [show
        (powerConstant * r324DerivativeAbsorptionBase Cderiv) * lam =
          r324DerivativeAbsorptionBase Cderiv *
            (powerConstant * lam) by ring,
        mul_pow]
      ring

end

end Anderson4D
