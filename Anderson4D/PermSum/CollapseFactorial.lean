import Anderson4D.Combinatorics.FactorialBounds

/-!
# Factorial bookkeeping for the collapse induction

This file isolates equation (5.47) in the proof of Proposition 5.9.  The
paper distinguishes the case of one skipped edge, where the collapsed branch
is inserted into `W'`, from the case of at least two skipped edges.
-/

namespace Anderson4D

/-- Removing `k` factors from the first factorial costs at most `a^k`.

The sharper intermediate factor is `a.descFactorial k`; the remaining two
factorials form a binomial coefficient. -/
theorem factorial_mul_factorial_le_pow_mul_factorial_add_sub
    (a b k : ℕ) (hk : k ≤ a) :
    a.factorial * b.factorial ≤
      a ^ k * (a + b - k).factorial := by
  have hsplit :
      (a - k).factorial * a.descFactorial k = a.factorial :=
    Nat.factorial_mul_descFactorial hk
  have hfac :
      (a - k).factorial * b.factorial ≤
        ((a - k) + b).factorial := by
    exact Nat.le_of_dvd (Nat.factorial_pos _)
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  have hdesc : a.descFactorial k ≤ a ^ k :=
    Nat.descFactorial_le_pow _ _
  calc
    a.factorial * b.factorial =
        a.descFactorial k * ((a - k).factorial * b.factorial) := by
      rw [← hsplit]
      ring
    _ ≤ a.descFactorial k * ((a - k) + b).factorial :=
      Nat.mul_le_mul_left _ hfac
    _ ≤ a ^ k * ((a - k) + b).factorial :=
      Nat.mul_le_mul_right _ hdesc
    _ = a ^ k * (a + b - k).factorial := by
      congr 2
      omega

/-- Natural-number square of paper (5.47).

Here `w' = w + 1` when `s = 1`, and `w' = w` when `s > 1`.  Squaring
the printed inequality turns its factor `n²` into `n⁴`. -/
theorem collapse_factorial_sq_bound
    (n m s w : ℕ) (hs : 1 ≤ s) (hsn : s + 1 ≤ n)
    (hn : 4 ≤ n) (hw : 2 * w ≤ m) :
    (n - s).factorial * (m + s + 1 - 2 * w).factorial ≤
      n ^ 4 *
        (n + m - 2 * (if s = 1 then w + 1 else w)).factorial := by
  by_cases hs1 : s = 1
  · subst s
    have hk : 3 ≤ n - 1 := by omega
    have hbase :=
      factorial_mul_factorial_le_pow_mul_factorial_add_sub
        (n - 1) (m + 2 - 2 * w) 3 hk
    have harg :
        (n - 1) + (m + 2 - 2 * w) - 3 =
          n + m - 2 * (w + 1) := by omega
    rw [harg] at hbase
    calc
      (n - 1).factorial * (m + 1 + 1 - 2 * w).factorial =
          (n - 1).factorial * (m + 2 - 2 * w).factorial := by
        congr 2
      _ ≤ (n - 1) ^ 3 * (n + m - 2 * (w + 1)).factorial := hbase
      _ ≤ n ^ 4 * (n + m - 2 * (w + 1)).factorial := by
        apply Nat.mul_le_mul_right
        calc
          (n - 1) ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left (by omega) 3
          _ ≤ n ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  · have hs2 : 2 ≤ s := by omega
    simp only [if_neg hs1]
    have hk : 1 ≤ n - s := by omega
    have hbase :=
      factorial_mul_factorial_le_pow_mul_factorial_add_sub
        (n - s) (m + s + 1 - 2 * w) 1 hk
    have harg :
        (n - s) + (m + s + 1 - 2 * w) - 1 =
          n + m - 2 * w := by omega
    rw [harg, pow_one] at hbase
    calc
      (n - s).factorial * (m + s + 1 - 2 * w).factorial ≤
          (n - s) * (n + m - 2 * w).factorial := hbase
      _ ≤ n ^ 4 * (n + m - 2 * w).factorial := by
        apply Nat.mul_le_mul_right
        calc
          n - s ≤ n := Nat.sub_le ..
          _ = n ^ 1 := by simp
          _ ≤ n ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)

/-- Paper (5.47), with the two definitions of `W'` encoded by the conditional
in the target factorial. -/
theorem collapse_factorial_sqrt_bound
    (n m s w : ℕ) (hs : 1 ≤ s) (hsn : s + 1 ≤ n)
    (hn : 4 ≤ n) (hw : 2 * w ≤ m) :
    Real.sqrt ((n - s).factorial : ℝ) *
        Real.sqrt ((m + s + 1 - 2 * w).factorial : ℝ) ≤
      Real.sqrt
          ((n + m - 2 * (if s = 1 then w + 1 else w)).factorial : ℝ) *
        (n : ℝ) ^ 2 := by
  have hnat := collapse_factorial_sq_bound n m s w hs hsn hn hw
  have hreal :
      (((n - s).factorial * (m + s + 1 - 2 * w).factorial : ℕ) : ℝ) ≤
        ((n ^ 4 *
          (n + m - 2 * (if s = 1 then w + 1 else w)).factorial : ℕ) : ℝ) := by
    exact_mod_cast hnat
  calc
    Real.sqrt ((n - s).factorial : ℝ) *
          Real.sqrt ((m + s + 1 - 2 * w).factorial : ℝ) =
        Real.sqrt
          ((((n - s).factorial *
            (m + s + 1 - 2 * w).factorial : ℕ) : ℝ)) := by
      rw [Nat.cast_mul, Real.sqrt_mul (by positivity)]
    _ ≤ Real.sqrt
        ((n ^ 4 *
          (n + m - 2 * (if s = 1 then w + 1 else w)).factorial : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt hreal
    _ = Real.sqrt
          ((n + m - 2 * (if s = 1 then w + 1 else w)).factorial : ℝ) *
        (n : ℝ) ^ 2 := by
      push_cast
      rw [show (n : ℝ) ^ 4 = ((n : ℝ) ^ 2) ^ 2 by ring,
        Real.sqrt_mul (sq_nonneg ((n : ℝ) ^ 2)),
        Real.sqrt_sq (sq_nonneg (n : ℝ))]
      ring

end Anderson4D
