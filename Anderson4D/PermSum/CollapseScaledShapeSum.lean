import Anderson4D.PermSum.CollapseCompositionCount

/-!
# Absorbing the outer collapse-shape sum

The number of admissible block-composition shapes is at most `2^n`.  In the
final scalar ledger that same factor has already been placed on the left of
each fixed-shape estimate.  The lemma below cancels these two occurrences
without introducing division.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open scoped BigOperators

/-- If there are at most `2^n` terms and every term multiplied by `2^n` is
bounded by the same nonnegative target, then their sum is bounded by that
target. -/
theorem sum_le_of_card_le_two_pow_of_two_pow_mul_le
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (F : ι → ℝ) (B : ℝ) (n : ℕ)
    (hcard : S.card ≤ 2 ^ n)
    (hB : 0 ≤ B)
    (hscaled : ∀ x ∈ S, (2 : ℝ) ^ n * F x ≤ B) :
    (∑ x ∈ S, F x) ≤ B := by
  have hp : 0 < (2 : ℝ) ^ n := by positivity
  have hmul :
      (2 : ℝ) ^ n * (∑ x ∈ S, F x) ≤
        (2 : ℝ) ^ n * B := by
    calc
      (2 : ℝ) ^ n * ∑ x ∈ S, F x =
          ∑ x ∈ S, (2 : ℝ) ^ n * F x := by
        rw [Finset.mul_sum]
      _ ≤ ∑ _x ∈ S, B :=
        Finset.sum_le_sum hscaled
      _ = (S.card : ℝ) * B := by simp
      _ ≤ ((2 ^ n : ℕ) : ℝ) * B := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast hcard) hB
      _ = (2 : ℝ) ^ n * B := by norm_num
  nlinarith

end Anderson4D
