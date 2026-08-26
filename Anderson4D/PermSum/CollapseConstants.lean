import Anderson4D.PermSum.Statements

/-!
# Constant absorption for the collapse induction

This file isolates the constant estimate following paper (5.46).  Taking
fourth powers turns the residual compound-leaf factor into one factorial
denominator, which is then controlled by the exponential series.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- The fourth power of `(n!)^(3/4)` is `(n!)^3`. -/
theorem factorialThreeQuarters_pow_four (n : ℕ) :
    factorialThreeQuarters n ^ (4 : ℕ) =
      (n.factorial : ℝ) ^ (3 : ℕ) := by
  unfold factorialThreeQuarters
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

/-- The factor in (5.46) involving the new compound leaf. -/
def collapseDLocalFactor (C0 D : ℝ) (n : ℕ) : ℝ :=
  D⁻¹ * C0 ^ n * (n.factorial : ℝ)⁻¹ *
    factorialThreeQuarters n

/-- The large constant `D = exp(C0^10)` absorbs the new compound-leaf
factor uniformly in its multiplicity. -/
theorem collapseDLocalFactor_le_one
    (C0 D : ℝ) (hC0 : 1000 < C0)
    (hD : D = Real.exp (C0 ^ (10 : ℕ))) (n : ℕ) :
    collapseDLocalFactor C0 D n ≤ 1 := by
  have hC0nonneg : 0 ≤ C0 := by linarith
  have hDone : 0 < D := by rw [hD]; positivity
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  have hseries :
      (C0 ^ (4 : ℕ)) ^ n ≤
        Real.exp (C0 ^ (4 : ℕ)) * (n.factorial : ℝ) := by
    have h :=
      Real.pow_div_factorial_le_exp
        (x := C0 ^ (4 : ℕ)) (by positivity) n
    rwa [div_le_iff₀ hfac] at h
  have hpowMonotone :
      C0 ^ (4 : ℕ) ≤ C0 ^ (10 : ℕ) :=
    pow_le_pow_right₀ (by linarith : 1 ≤ C0) (by omega)
  have hexp :
      Real.exp (C0 ^ (4 : ℕ)) ≤ D ^ (4 : ℕ) := by
    rw [hD, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hten : 0 ≤ C0 ^ (10 : ℕ) := by positivity
    norm_num
    linarith
  have hseriesD :
      (C0 ^ (4 : ℕ)) ^ n ≤
        D ^ (4 : ℕ) * (n.factorial : ℝ) :=
    hseries.trans
      (mul_le_mul_of_nonneg_right hexp hfac.le)
  have hfactorNonneg :
      0 ≤ collapseDLocalFactor C0 D n := by
    unfold collapseDLocalFactor factorialThreeQuarters
    positivity
  apply
    (pow_le_one_iff_of_nonneg hfactorNonneg
      (by norm_num : (4 : ℕ) ≠ 0)).mp
  have hpowIdentity :
      collapseDLocalFactor C0 D n ^ (4 : ℕ) =
        (D ^ (4 : ℕ))⁻¹ *
          ((C0 ^ (4 : ℕ)) ^ n *
            (n.factorial : ℝ)⁻¹) := by
    unfold collapseDLocalFactor
    rw [mul_pow, mul_pow, mul_pow,
      factorialThreeQuarters_pow_four, inv_pow, inv_pow]
    rw [show (C0 ^ n) ^ (4 : ℕ) =
      (C0 ^ (4 : ℕ)) ^ n by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega]
    field_simp
  rw [hpowIdentity]
  have hDpow : 0 < D ^ (4 : ℕ) := pow_pos hDone _
  rw [inv_mul_le_one₀ hDpow]
  calc
    (C0 ^ (4 : ℕ)) ^ n * (n.factorial : ℝ)⁻¹ ≤
        (D ^ (4 : ℕ) * (n.factorial : ℝ)) *
          (n.factorial : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hseriesD (inv_nonneg.mpr hfac.le)
    _ = D ^ (4 : ℕ) := by field_simp

/-!
## Final exponential absorption

After (5.47), the two independent `4^n` ledgers combine with the
single-scale half-power to give

`16^n * C0^(n/2)`.

The paper assumes `C0 > 1000`, which is already more than enough to absorb
this expression into `C0^n`.  Keeping this scalar step separate prevents the
collapse proof from silently spending the same geometric loss twice.
-/

/-- For the paper's range `C0 > 1000`, one copy of `16 * sqrt C0` is
absorbed by `C0`. -/
theorem sixteen_mul_sqrt_le_self
    (C0 : ℝ) (hC0 : 1000 < C0) :
    16 * Real.sqrt C0 ≤ C0 := by
  have hC0nonneg : 0 ≤ C0 := by linarith
  have h256 : (256 : ℝ) ≤ C0 := by linarith
  have hsqrt : (16 : ℝ) ≤ Real.sqrt C0 := by
    have h := Real.sqrt_le_sqrt h256
    norm_num at h ⊢
    exact h
  calc
    16 * Real.sqrt C0 ≤ Real.sqrt C0 * Real.sqrt C0 :=
      mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg C0)
    _ = C0 := Real.mul_self_sqrt hC0nonneg

/-- The complete post-collapse exponential ledger:
`16^n * C0^(n/2) ≤ C0^n`. -/
theorem sixteen_pow_mul_halfPower_le_natPower
    (C0 : ℝ) (hC0 : 1000 < C0) (n : ℕ) :
    (16 : ℝ) ^ n * C0 ^ ((n : ℝ) / 2) ≤ C0 ^ n := by
  have hC0nonneg : 0 ≤ C0 := by linarith
  rw [Real.rpow_div_two_eq_sqrt (n : ℝ) hC0nonneg,
    Real.rpow_natCast, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity)
    (sixteen_mul_sqrt_le_self C0 hC0) n

/-- A strict saving in a natural exponent extracts one inverse factor.  This
is the scalar form of the branch-cardinality saving in (5.45). -/
theorem pow_le_pow_mul_inv_of_succ_le
    (D : ℝ) (hD : 1 ≤ D) (a b : ℕ)
    (hab : a + 1 ≤ b) :
    D ^ a ≤ D ^ b * D⁻¹ := by
  cases b with
  | zero =>
      omega
  | succ b =>
      have hab' : a ≤ b := by omega
      have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
      calc
        D ^ a ≤ D ^ b := pow_le_pow_right₀ hD hab'
        _ = D ^ (b + 1) * D⁻¹ := by
          rw [pow_succ]
          field_simp

end

end Anderson4D
