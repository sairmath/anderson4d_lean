import Anderson4D.Combinatorics.FactorialBounds
import Anderson4D.PermSum.Statements

/-!
# The factorial comparison after merging equal runs

This file isolates the factorial ledger in paper (5.37).  If the original
leaf multiplicities are `m_l`, the run-compressed multiplicities are `s_l`,
their sums are respectively `2n` and `m`, and `w = |W|`, then the factorial
factor produced by (5.35)--(5.36) is bounded by an absolute constant to the
power `n` times the factorial factor in (5.15).

We take the explicit absolute constant `4`.  Thus the conclusion below is
exactly of the paper's form `C^n`; increasing `C` only weakens the bound.
-/

namespace Anderson4D

open scoped BigOperators
noncomputable section

/-- The factorial factor on the left of (5.37), after fixing the partitions
and the set `W`. -/
def mergeFactorialBefore {α : Type*} (s : Finset α)
    (ml sl : α → ℕ) (m w : ℕ) : ℝ :=
  sqrtFactorial (m - 2 * w) *
    (∏ l ∈ s, sqrtFactorial (sl l)) *
    ∏ l ∈ s, ((ml l).factorial : ℝ) / ((sl l).factorial : ℝ)

/-- The factorial factor inherited from (5.15), with its exponential
constant omitted. -/
def mergeFactorialAfter {α : Type*} (s : Finset α)
    (ml : α → ℕ) (n w : ℕ) : ℝ :=
  ((n - w).factorial : ℝ) * ∏ l ∈ s, sqrtFactorial (ml l)

/-- The real factorial ratio is controlled by the binomial estimate used in
the first inequality of (5.37).  Positivity of the denominator is discharged
here rather than hidden in a later field simplification. -/
theorem factorial_ratio_le_two_pow_mul_deficit
    (ml sl : ℕ) (hsl : sl ≤ ml) :
    (ml.factorial : ℝ) / (sl.factorial : ℝ) ≤
      (2 : ℝ) ^ ml * ((ml - sl).factorial : ℝ) := by
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (sl.factorial : ℝ))]
  calc
    (ml.factorial : ℝ) ≤
        ((2 ^ ml * sl.factorial * (ml - sl).factorial : ℕ) : ℝ) := by
      exact_mod_cast
        factorial_le_two_pow_mul_factorial_mul_factorial_sub ml sl hsl
    _ = ((2 : ℝ) ^ ml * ((ml - sl).factorial : ℝ)) *
        (sl.factorial : ℝ) := by
      push_cast
      ring

/-- Product form of the preceding binomial estimate. -/
theorem prod_factorial_ratio_le
    {α : Type*} (s : Finset α) (ml sl : α → ℕ)
    (hsub : ∀ l ∈ s, sl l ≤ ml l) (n : ℕ)
    (hml : ∑ l ∈ s, ml l = 2 * n) :
    (∏ l ∈ s, ((ml l).factorial : ℝ) / ((sl l).factorial : ℝ)) ≤
      (2 : ℝ) ^ (2 * n) *
        ((∏ l ∈ s, (ml l - sl l).factorial : ℕ) : ℝ) := by
  calc
    (∏ l ∈ s, ((ml l).factorial : ℝ) / ((sl l).factorial : ℝ)) ≤
        ∏ l ∈ s,
          (2 : ℝ) ^ ml l * ((ml l - sl l).factorial : ℝ) := by
      apply Finset.prod_le_prod
      · intro l hl
        positivity
      · intro l hl
        exact factorial_ratio_le_two_pow_mul_deficit (ml l) (sl l) (hsub l hl)
    _ = (2 : ℝ) ^ (2 * n) *
        ((∏ l ∈ s, (ml l - sl l).factorial : ℕ) : ℝ) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hml]
      rw [Nat.cast_prod]

/-- Square-root form of the product ratio estimate.  Since
`∑ m_l = 2n`, the square root of the binomial loss is exactly `2^n`. -/
theorem sqrt_prod_factorial_ratio_le
    {α : Type*} (s : Finset α) (ml sl : α → ℕ)
    (hsub : ∀ l ∈ s, sl l ≤ ml l) (n : ℕ)
    (hml : ∑ l ∈ s, ml l = 2 * n) :
    Real.sqrt
        (∏ l ∈ s, ((ml l).factorial : ℝ) / ((sl l).factorial : ℝ)) ≤
      (2 : ℝ) ^ n *
        Real.sqrt ((∏ l ∈ s, (ml l - sl l).factorial : ℕ) : ℝ) := by
  calc
    Real.sqrt
        (∏ l ∈ s, ((ml l).factorial : ℝ) / ((sl l).factorial : ℝ)) ≤
        Real.sqrt
          ((2 : ℝ) ^ (2 * n) *
            ((∏ l ∈ s, (ml l - sl l).factorial : ℕ) : ℝ)) :=
      Real.sqrt_le_sqrt (prod_factorial_ratio_le s ml sl hsub n hml)
    _ = (2 : ℝ) ^ n *
        Real.sqrt ((∏ l ∈ s, (ml l - sl l).factorial : ℕ) : ℝ) := by
      rw [show 2 * n = n * 2 by omega,
        show (2 : ℝ) ^ (n * 2) = ((2 : ℝ) ^ n) ^ 2 by rw [pow_mul],
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- Multiplying by the residual factorial gives precisely the bracketed
deficit product in the middle line of (5.37). -/
theorem sqrt_deficit_product_le_shifted_factorial
    {α : Type*} (s : Finset α) (ml sl : α → ℕ)
    (hsub : ∀ l ∈ s, sl l ≤ ml l)
    (n m w : ℕ)
    (hml : ∑ l ∈ s, ml l = 2 * n)
    (hsl : ∑ l ∈ s, sl l = m)
    (hw : 2 * w ≤ m) :
    Real.sqrt ((m - 2 * w).factorial : ℝ) *
        Real.sqrt ((∏ l ∈ s, (ml l - sl l).factorial : ℕ) : ℝ) ≤
      Real.sqrt ((2 * n - 2 * w).factorial : ℝ) := by
  rw [← Real.sqrt_mul (by positivity :
    (0 : ℝ) ≤ ((m - 2 * w).factorial : ℝ))]
  apply Real.sqrt_le_sqrt
  exact_mod_cast
    (show
      (m - 2 * w).factorial *
          (∏ l ∈ s, (ml l - sl l).factorial) ≤
        (2 * n - 2 * w).factorial by
      rw [mul_comm]
      exact prod_factorial_sub_mul_factorial_sub_le
        s ml sl hsub n m w hml hsl hw)

/-- The denominator in the last quotient of (5.37) is strictly positive,
including when natural subtraction truncates. -/
theorem shifted_factorial_cast_pos (n w : ℕ) :
    (0 : ℝ) < ((2 * n - 2 * w).factorial : ℝ) := by
  positivity

/-- Literal form of the last parenthesized factor in (5.37): the square root
of the deficit-factorial quotient is at most one. -/
theorem sqrt_deficit_factorial_quotient_le_one
    {α : Type*} (s : Finset α) (ml sl : α → ℕ)
    (hsub : ∀ l ∈ s, sl l ≤ ml l)
    (n m w : ℕ)
    (hml : ∑ l ∈ s, ml l = 2 * n)
    (hsl : ∑ l ∈ s, sl l = m)
    (hw : 2 * w ≤ m) :
    Real.sqrt
        ((((∏ l ∈ s, (ml l - sl l).factorial : ℕ) : ℝ) *
            ((m - 2 * w).factorial : ℝ)) /
          ((2 * n - 2 * w).factorial : ℝ)) ≤ 1 := by
  rw [Real.sqrt_le_one, div_le_one (shifted_factorial_cast_pos n w)]
  exact_mod_cast
    prod_factorial_sub_mul_factorial_sub_le
      s ml sl hsub n m w hml hsl hw

/-- The exact one-leaf square-root identity used when factoring the first
line of (5.37). -/
theorem sqrtFactorial_mul_factorial_ratio
    (ml sl : ℕ) :
    sqrtFactorial sl * ((ml.factorial : ℝ) / (sl.factorial : ℝ)) =
      sqrtFactorial ml *
        Real.sqrt ((ml.factorial : ℝ) / (sl.factorial : ℝ)) := by
  have hden : (sl.factorial : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hratio :
      (0 : ℝ) ≤ (ml.factorial : ℝ) / (sl.factorial : ℝ) := by
    positivity
  have hfac :
      (ml.factorial : ℝ) =
        (sl.factorial : ℝ) *
          ((ml.factorial : ℝ) / (sl.factorial : ℝ)) := by
    exact (mul_div_cancel₀ (ml.factorial : ℝ) hden).symm
  have hsqrtfac :
      Real.sqrt (ml.factorial : ℝ) =
        Real.sqrt (sl.factorial : ℝ) *
          Real.sqrt ((ml.factorial : ℝ) / (sl.factorial : ℝ)) := by
    nth_rewrite 1 [hfac]
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (sl.factorial : ℝ))]
  rw [sqrtFactorial, sqrtFactorial, hsqrtfac, mul_assoc,
    Real.mul_self_sqrt hratio]

/-- Exact product factorization underlying the displayed equality in (5.37).
Every ratio is well-defined because factorials are strictly positive. -/
theorem mergeFactorialBefore_eq
    {α : Type*} (s : Finset α) (ml sl : α → ℕ) (m w : ℕ) :
    mergeFactorialBefore s ml sl m w =
      sqrtFactorial (m - 2 * w) *
        (∏ l ∈ s, sqrtFactorial (ml l)) *
        Real.sqrt
          (∏ l ∈ s,
            ((ml l).factorial : ℝ) / ((sl l).factorial : ℝ)) := by
  have hrat :
      ∀ l ∈ s,
        (0 : ℝ) ≤
          ((ml l).factorial : ℝ) / ((sl l).factorial : ℝ) := by
    intro l hl
    positivity
  have hmiddle :
      (∏ l ∈ s, sqrtFactorial (sl l)) *
        ∏ l ∈ s,
          ((ml l).factorial : ℝ) / ((sl l).factorial : ℝ) =
        Real.sqrt
          (∏ l ∈ s,
            ((ml l).factorial : ℝ) / ((sl l).factorial : ℝ)) *
          (∏ l ∈ s, sqrtFactorial (ml l)) := by
    calc
      (∏ l ∈ s, sqrtFactorial (sl l)) *
          ∏ l ∈ s,
            ((ml l).factorial : ℝ) / ((sl l).factorial : ℝ) =
          ∏ l ∈ s,
            (sqrtFactorial (sl l) *
              (((ml l).factorial : ℝ) / ((sl l).factorial : ℝ))) := by
        rw [Finset.prod_mul_distrib]
      _ = ∏ l ∈ s,
          (sqrtFactorial (ml l) *
            Real.sqrt
              (((ml l).factorial : ℝ) / ((sl l).factorial : ℝ))) := by
        apply Finset.prod_congr rfl
        intro l hl
        exact sqrtFactorial_mul_factorial_ratio (ml l) (sl l)
      _ = (∏ l ∈ s, sqrtFactorial (ml l)) *
          ∏ l ∈ s,
            Real.sqrt
              (((ml l).factorial : ℝ) / ((sl l).factorial : ℝ)) := by
        rw [Finset.prod_mul_distrib]
      _ = (∏ l ∈ s, sqrtFactorial (ml l)) *
          Real.sqrt
            (∏ l ∈ s,
              ((ml l).factorial : ℝ) / ((sl l).factorial : ℝ)) := by
        rw [Real.sqrt_prod s hrat]
      _ = Real.sqrt
          (∏ l ∈ s,
            ((ml l).factorial : ℝ) / ((sl l).factorial : ℝ)) *
          (∏ l ∈ s, sqrtFactorial (ml l)) := by ring
  rw [mergeFactorialBefore]
  calc
    sqrtFactorial (m - 2 * w) *
          (∏ l ∈ s, sqrtFactorial (sl l)) *
          ∏ l ∈ s,
            ((ml l).factorial : ℝ) / ((sl l).factorial : ℝ) =
        sqrtFactorial (m - 2 * w) *
          ((∏ l ∈ s, sqrtFactorial (sl l)) *
            ∏ l ∈ s,
              ((ml l).factorial : ℝ) / ((sl l).factorial : ℝ)) := by
      ring
    _ = sqrtFactorial (m - 2 * w) *
        (Real.sqrt
          (∏ l ∈ s,
            ((ml l).factorial : ℝ) / ((sl l).factorial : ℝ)) *
          (∏ l ∈ s, sqrtFactorial (ml l))) := by
      rw [hmiddle]
    _ = sqrtFactorial (m - 2 * w) *
        (∏ l ∈ s, sqrtFactorial (ml l)) *
        Real.sqrt
          (∏ l ∈ s,
            ((ml l).factorial : ℝ) / ((sl l).factorial : ℝ)) := by
      ring

/-- **Paper (5.37), with the explicit absolute constant `C = 4`.**

The hypotheses are exactly the numerical data available after merging equal
runs: `s_l ≤ m_l`, `∑m_l = 2n`, `∑s_l = m`, and `2w ≤ m`.  No factorial
comparison is assumed. -/
theorem mergeFactorialBefore_le_four_pow
    {α : Type*} (s : Finset α) (ml sl : α → ℕ)
    (hsub : ∀ l ∈ s, sl l ≤ ml l)
    (n m w : ℕ)
    (hml : ∑ l ∈ s, ml l = 2 * n)
    (hsl : ∑ l ∈ s, sl l = m)
    (hw : 2 * w ≤ m) :
    mergeFactorialBefore s ml sl m w ≤
      (4 : ℝ) ^ n * mergeFactorialAfter s ml n w := by
  have hmle : m ≤ 2 * n := by
    calc
      m = ∑ l ∈ s, sl l := hsl.symm
      _ ≤ ∑ l ∈ s, ml l :=
        Finset.sum_le_sum fun l hl => hsub l hl
      _ = 2 * n := hml
  have hwn : w ≤ n := by omega
  let A : ℝ := sqrtFactorial (m - 2 * w)
  let P : ℝ := ∏ l ∈ s, sqrtFactorial (ml l)
  let Q : ℝ :=
    Real.sqrt
      (∏ l ∈ s,
        ((ml l).factorial : ℝ) / ((sl l).factorial : ℝ))
  let D : ℝ :=
    Real.sqrt ((∏ l ∈ s, (ml l - sl l).factorial : ℕ) : ℝ)
  let T : ℝ := Real.sqrt ((2 * n - 2 * w).factorial : ℝ)
  let F : ℝ := ((n - w).factorial : ℝ)
  have hA : 0 ≤ A := by
    dsimp [A, sqrtFactorial]
    exact Real.sqrt_nonneg _
  have hP : 0 ≤ P := by
    dsimp [P, sqrtFactorial]
    positivity
  have hF : 0 ≤ F := by
    dsimp [F]
    positivity
  have hQ : Q ≤ (2 : ℝ) ^ n * D := by
    simpa [Q, D] using
      sqrt_prod_factorial_ratio_le s ml sl hsub n hml
  have hAD : A * D ≤ T := by
    simpa [A, D, T, sqrtFactorial] using
      sqrt_deficit_product_le_shifted_factorial
        s ml sl hsub n m w hml hsl hw
  have hT : T ≤ (2 : ℝ) ^ (n - w) * F := by
    simpa [T, F] using sqrt_factorial_two_mul_sub_le n w hwn
  have hconst :
      (2 : ℝ) ^ n * (2 : ℝ) ^ (n - w) ≤ (4 : ℝ) ^ n := by
    calc
      (2 : ℝ) ^ n * (2 : ℝ) ^ (n - w) ≤
          (2 : ℝ) ^ n * (2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num) (Nat.sub_le n w)) (by positivity)
      _ = (4 : ℝ) ^ n := by rw [← mul_pow]; norm_num
  rw [mergeFactorialBefore_eq]
  change A * P * Q ≤ (4 : ℝ) ^ n * (F * P)
  calc
    A * P * Q ≤ A * P * ((2 : ℝ) ^ n * D) :=
      mul_le_mul_of_nonneg_left hQ (mul_nonneg hA hP)
    _ = P * (2 : ℝ) ^ n * (A * D) := by ring
    _ ≤ P * (2 : ℝ) ^ n * T :=
      mul_le_mul_of_nonneg_left hAD (mul_nonneg hP (by positivity))
    _ ≤ P * (2 : ℝ) ^ n * ((2 : ℝ) ^ (n - w) * F) :=
      mul_le_mul_of_nonneg_left hT (mul_nonneg hP (by positivity))
    _ = ((2 : ℝ) ^ n * (2 : ℝ) ^ (n - w)) * (F * P) := by ring
    _ ≤ (4 : ℝ) ^ n * (F * P) :=
      mul_le_mul_of_nonneg_right hconst (mul_nonneg hF hP)

/-- Paper-style constant form of (5.37).  Any fixed `C ≥ 4` absorbs the
explicit loss, so the preceding theorem is exactly an absolute `C^n` bound. -/
theorem mergeFactorialBefore_le_const_pow
    {α : Type*} (s : Finset α) (ml sl : α → ℕ)
    (hsub : ∀ l ∈ s, sl l ≤ ml l)
    (C : ℝ) (hC : 4 ≤ C)
    (n m w : ℕ)
    (hml : ∑ l ∈ s, ml l = 2 * n)
    (hsl : ∑ l ∈ s, sl l = m)
    (hw : 2 * w ≤ m) :
    mergeFactorialBefore s ml sl m w ≤
      C ^ n * mergeFactorialAfter s ml n w := by
  calc
    mergeFactorialBefore s ml sl m w ≤
        (4 : ℝ) ^ n * mergeFactorialAfter s ml n w :=
      mergeFactorialBefore_le_four_pow
        s ml sl hsub n m w hml hsl hw
    _ ≤ C ^ n * mergeFactorialAfter s ml n w :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by norm_num) hC n) (by
          unfold mergeFactorialAfter sqrtFactorial
          positivity)

end
end Anderson4D
