import Mathlib

/-!
# Elementary exponential--factorial comparisons

The Hepp-tree volume iteration produces a factor `q ^ (q - 1)` from
parent-function codes at a branch with `q` children.  Paper (5.25) absorbs
this into `q!` at exponential cost.  This file records a kernel-checked,
fully explicit version of that absorption.
-/

namespace Anderson4D

open scoped BigOperators

/-- The elementary bound `n^n ≤ 4^n n!`.

We compare `n^n` with the descending factorial
`(2n)(2n-1)…(n+1)`, then bound the central binomial coefficient by its
row sum. -/
theorem pow_self_le_four_pow_mul_factorial (n : ℕ) :
    n ^ n ≤ 4 ^ n * n.factorial := by
  have hdesc : (n + 1) ^ n ≤ (2 * n).descFactorial n := by
    have h := Nat.pow_sub_le_descFactorial (2 * n) n
    have he : 2 * n + 1 - n = n + 1 := by omega
    rwa [he] at h
  have hsplit :
      (2 * n).descFactorial n = (2 * n).choose n * n.factorial := by
    have hle : n ≤ 2 * n := by omega
    have hchoose := Nat.choose_mul_factorial_mul_factorial hle
    have hfactorial := Nat.factorial_mul_descFactorial hle
    have he : 2 * n - n = n := by omega
    rw [he] at hchoose hfactorial
    apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos n)
    calc
      n.factorial * (2 * n).descFactorial n = (2 * n).factorial :=
        hfactorial
      _ = (2 * n).choose n * n.factorial * n.factorial :=
        hchoose.symm
      _ = n.factorial * ((2 * n).choose n * n.factorial) := by ring
  have hchoose : (2 * n).choose n ≤ 4 ^ n := by
    calc
      (2 * n).choose n
          ≤ ∑ i ∈ Finset.range (2 * n + 1), (2 * n).choose i :=
        Finset.single_le_sum
          (f := fun i => (2 * n).choose i)
          (fun i _ => Nat.zero_le _)
          (Finset.mem_range.mpr (by omega))
      _ = 2 ^ (2 * n) := Nat.sum_range_choose (2 * n)
      _ = 4 ^ n := by rw [pow_mul]; norm_num
  calc
    n ^ n ≤ (n + 1) ^ n := Nat.pow_le_pow_left (by omega) n
    _ ≤ (2 * n).descFactorial n := hdesc
    _ = (2 * n).choose n * n.factorial := hsplit
    _ ≤ 4 ^ n * n.factorial := Nat.mul_le_mul_right _ hchoose

/-- Central-binomial form of the even-factorial estimate:
`(2n)! ≤ 4^n (n!)²`. -/
theorem factorial_two_mul_le_four_pow_mul_factorial_sq (n : ℕ) :
    (2 * n).factorial ≤ 4 ^ n * n.factorial ^ 2 := by
  have hle : n ≤ 2 * n := by omega
  have hfac := Nat.choose_mul_factorial_mul_factorial hle
  have hsub : 2 * n - n = n := by omega
  rw [hsub] at hfac
  calc
    (2 * n).factorial =
        (2 * n).choose n * n.factorial * n.factorial := hfac.symm
    _ = Nat.centralBinom n * (n.factorial * n.factorial) := by
      rw [Nat.centralBinom_eq_two_mul_choose]
      ring
    _ ≤ 4 ^ n * (n.factorial * n.factorial) :=
      Nat.mul_le_mul_right _ (Nat.centralBinom_le_four_pow n)
    _ = 4 ^ n * n.factorial ^ 2 := by ring

/-- Square-root form used in paper (5.37):
`√((2n)!) ≤ 2^n n!`. -/
theorem sqrt_factorial_two_mul_le_two_pow_mul_factorial (n : ℕ) :
    Real.sqrt ((2 * n).factorial : ℝ) ≤
      (2 : ℝ) ^ n * (n.factorial : ℝ) := by
  have hnat := factorial_two_mul_le_four_pow_mul_factorial_sq n
  have hreal :
      ((2 * n).factorial : ℝ) ≤
        ((4 ^ n * n.factorial ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  calc
    Real.sqrt ((2 * n).factorial : ℝ) ≤
        Real.sqrt ((4 ^ n * n.factorial ^ 2 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt hreal
    _ = Real.sqrt (((2 : ℝ) ^ n * (n.factorial : ℝ)) ^ 2) := by
      congr 1
      push_cast
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, mul_pow,
        ← pow_mul]
      ring
    _ = (2 : ℝ) ^ n * (n.factorial : ℝ) :=
      Real.sqrt_sq (by positivity)

/-- Shifted version of the preceding bound, matching
`√((2n-2s)!)` in (5.37). -/
theorem sqrt_factorial_two_mul_sub_le (n s : ℕ) (hs : s ≤ n) :
    Real.sqrt ((2 * n - 2 * s).factorial : ℝ) ≤
      (2 : ℝ) ^ (n - s) * ((n - s).factorial : ℝ) := by
  have harg : 2 * n - 2 * s = 2 * (n - s) := by omega
  rw [harg]
  exact sqrt_factorial_two_mul_le_two_pow_mul_factorial (n - s)

/-! ### The factorial audit in paper (5.37) -/

/-- A product of factorials is bounded by the factorial of the sum.

This is the order-theoretic form of the multinomial divisibility lemma and is
the basic tool for the last square-root factor in (5.37). -/
theorem prod_factorial_le_factorial_sum
    {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∏ a ∈ s, (f a).factorial) ≤ (∑ a ∈ s, f a).factorial :=
  Nat.le_of_dvd (Nat.factorial_pos _)
    (Nat.prod_factorial_dvd_factorial_sum s f)

/-- The binomial estimate used in the first inequality of (5.37):
`m! ≤ 2^m s! (m-s)!`. -/
theorem factorial_le_two_pow_mul_factorial_mul_factorial_sub
    (m s : ℕ) (hs : s ≤ m) :
    m.factorial ≤ 2 ^ m * s.factorial * (m - s).factorial := by
  calc
    m.factorial = m.choose s * s.factorial * (m - s).factorial :=
      (Nat.choose_mul_factorial_mul_factorial hs).symm
    _ ≤ 2 ^ m * s.factorial * (m - s).factorial := by
      exact Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right _ (Nat.choose_le_two_pow m s))

/-- The bracketed factorial quotient in the last line of paper (5.37) is at
most one, before passing to `ℝ` and taking square roots.

If `M = ∑ m_l = 2n`, `S = ∑ s_l = m`, and `2w ≤ m`, then the deficits
`m_l-s_l`, together with the residual `m-2w`, have total
`2n-2w`.  Multinomial divisibility therefore gives the stated inequality. -/
theorem prod_factorial_sub_mul_factorial_sub_le
    {α : Type*} (s : Finset α) (ml sl : α → ℕ)
    (hsub : ∀ a ∈ s, sl a ≤ ml a)
    (n m w : ℕ)
    (hml : ∑ a ∈ s, ml a = 2 * n)
    (hsl : ∑ a ∈ s, sl a = m)
    (hw : 2 * w ≤ m) :
    (∏ a ∈ s, (ml a - sl a).factorial) * (m - 2 * w).factorial ≤
      (2 * n - 2 * w).factorial := by
  have hsumSub :
      ∑ a ∈ s, (ml a - sl a) = 2 * n - m := by
    rw [Finset.sum_tsub_distrib s hsub, hml, hsl]
  have hmle : m ≤ 2 * n := by
    calc
      m = ∑ a ∈ s, sl a := hsl.symm
      _ ≤ ∑ a ∈ s, ml a := Finset.sum_le_sum fun a ha => hsub a ha
      _ = 2 * n := hml
  have htarget :
      (∑ a ∈ s, (ml a - sl a)) + (m - 2 * w) =
        2 * n - 2 * w := by
    rw [hsumSub]
    omega
  have hprod :
      (∏ a ∈ s, (ml a - sl a).factorial) ∣
        (∑ a ∈ s, (ml a - sl a)).factorial :=
    Nat.prod_factorial_dvd_factorial_sum s fun a => ml a - sl a
  have hmul :
      (∏ a ∈ s, (ml a - sl a).factorial) * (m - 2 * w).factorial ∣
        (∑ a ∈ s, (ml a - sl a)).factorial * (m - 2 * w).factorial :=
    mul_dvd_mul_right hprod _
  have hadd :
      (∑ a ∈ s, (ml a - sl a)).factorial * (m - 2 * w).factorial ∣
        ((∑ a ∈ s, (ml a - sl a)) + (m - 2 * w)).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add _ _
  rw [← htarget]
  exact Nat.le_of_dvd (Nat.factorial_pos _) (hmul.trans hadd)

/-- The parent-code exponent `n - 1` is absorbed by the same bound. -/
theorem pow_pred_le_four_pow_mul_factorial (n : ℕ) :
    n ^ (n - 1) ≤ 4 ^ n * n.factorial := by
  by_cases hn : n = 0
  · simp [hn]
  · exact
      (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hn) (Nat.sub_le n 1)).trans
        (pow_self_le_four_pow_mul_factorial n)

/-- Product form used when one parent-code factor occurs at every branch. -/
theorem prod_pow_pred_le_prod_four_pow_factorial
    {α : Type*} (s : Finset α) (q : α → ℕ) :
    (∏ a ∈ s, q a ^ (q a - 1))
      ≤ ∏ a ∈ s, 4 ^ q a * (q a).factorial := by
  apply Finset.prod_le_prod
  · intro a ha
    exact Nat.zero_le _
  · intro a ha
    exact pow_pred_le_four_pow_mul_factorial (q a)

end Anderson4D
