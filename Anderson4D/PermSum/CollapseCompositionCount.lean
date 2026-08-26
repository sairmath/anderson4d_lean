import Anderson4D.Combinatorics.FactorialBounds
import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Composition-count losses in the collapse induction

The skipped-edge set is equivalently a positive composition of the inside
word.  This module records the two elementary exponential losses used after
the fixed-shape Fubini estimate.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open scoped BigOperators

/-- There are at most `2^n` positive compositions of `n`. -/
theorem card_composition_le_two_pow (n : ℕ) :
    Fintype.card (Composition n) ≤ 2 ^ n := by
  rw [composition_card]
  exact Nat.pow_le_pow_right (by omega) (Nat.sub_le n 1)

/-- A nonnegative summand uniformly bounded by `K` over compositions costs
at most the paper's coarse factor `2^n`. -/
theorem sum_composition_le_two_pow_mul
    {n : ℕ} (F : Composition n → ℝ) (K : ℝ)
    (hFK : ∀ c, F c ≤ K)
    (hK : 0 ≤ K) :
    (∑ c, F c) ≤ (2 : ℝ) ^ n * K := by
  calc
    (∑ c, F c) ≤ ∑ _c : Composition n, K :=
      Finset.sum_le_sum fun c _ => hFK c
    _ = (Fintype.card (Composition n) : ℝ) * K := by
      simp
    _ ≤ ((2 ^ n : ℕ) : ℝ) * K := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_composition_le_two_pow n) hK
    _ = (2 : ℝ) ^ n * K := by norm_num

/-- The polynomial loss in (5.47) is dominated by `2^n` for `n ≥ 4`. -/
theorem nat_sq_le_two_pow {n : ℕ} (hn : 4 ≤ n) :
    n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num
  | succ n hn ih =>
      calc
        (n + 1) ^ 2 ≤ 2 * n ^ 2 := by
          nlinarith
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by
          rw [pow_succ]
          omega

/-- Real-cast form used in the scalar factor audit. -/
theorem natCast_sq_le_two_pow {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := by
  exact_mod_cast nat_sq_le_two_pow hn

end Anderson4D
