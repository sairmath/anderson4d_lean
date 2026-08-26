import Anderson4D.PermSum.Statements

/-!
# Universal-constant absorption for the single-scale estimate

The proof of Proposition 5.10 repeatedly produces factors `C^m`, and a
bounded number of rough local operations additionally costs a fixed
polynomial such as `m^20`.  The statement uses the half-power
`C₀^(m/2)`.  This file proves once and for all that these losses can be
absorbed by choosing one `C₀ > 1000` depending only on the fixed inputs
`C,d`, uniformly in `m`.
-/

namespace Anderson4D

noncomputable section

/-- The elementary uniform bound `m^d ≤ (2^d)^m`. -/
theorem nat_pow_fixed_le_two_pow_fixed_pow (m d : ℕ) :
    m ^ d ≤ (2 ^ d) ^ m := by
  calc
    m ^ d ≤ (2 ^ m) ^ d :=
      Nat.pow_le_pow_left (Nat.le_of_lt m.lt_two_pow_self) d
    _ = (2 ^ d) ^ m := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]

/-- Real-cast form of the fixed-polynomial exponential bound. -/
theorem real_natCast_pow_fixed_le_two_pow_fixed_pow (m d : ℕ) :
    (m : ℝ) ^ d ≤ ((2 : ℝ) ^ d) ^ m := by
  exact_mod_cast nat_pow_fixed_le_two_pow_fixed_pow m d

/--
Every nonnegative exponential loss `C^m` is dominated by the paper's
half-power format after choosing one `C₀ > 1000`.
-/
theorem exists_large_halfPower_dominates_natPower
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ C₀ : ℝ, 1000 < C₀ ∧
      ∀ m : ℕ, C ^ m ≤ C₀ ^ ((m : ℝ) / 2) := by
  let B := max 1001 C
  have hB1001 : (1001 : ℝ) ≤ B := le_max_left _ _
  have hCB : C ≤ B := le_max_right _ _
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB1001
  refine ⟨B ^ 2, ?_, ?_⟩
  · nlinarith [sq_nonneg B]
  · intro m
    calc
      C ^ m ≤ B ^ m := pow_le_pow_left₀ hC hCB m
      _ = (B ^ 2) ^ ((m : ℝ) / 2) := by
        rw [Real.rpow_div_two_eq_sqrt (m : ℝ) (sq_nonneg B),
          Real.sqrt_sq hBpos.le, Real.rpow_natCast]

/--
The form needed after the rough-block audit following (5.92): a fixed
polynomial `m^d` times an exponential is still absorbed by one
`C₀^(m/2)`.
-/
theorem exists_large_halfPower_dominates_polynomial
    (C : ℝ) (hC : 0 ≤ C) (d : ℕ) :
    ∃ C₀ : ℝ, 1000 < C₀ ∧
      ∀ m : ℕ,
        C ^ m * (m : ℝ) ^ d ≤ C₀ ^ ((m : ℝ) / 2) := by
  let A : ℝ := C * (2 : ℝ) ^ d
  have hA : 0 ≤ A := mul_nonneg hC (by positivity)
  obtain ⟨C₀, hC₀, hdom⟩ :=
    exists_large_halfPower_dominates_natPower A hA
  refine ⟨C₀, hC₀, ?_⟩
  intro m
  calc
    C ^ m * (m : ℝ) ^ d ≤
        C ^ m * (((2 : ℝ) ^ d) ^ m) :=
      mul_le_mul_of_nonneg_left
        (real_natCast_pow_fixed_le_two_pow_fixed_pow m d)
        (pow_nonneg hC m)
    _ = A ^ m := by
      unfold A
      rw [mul_pow]
    _ ≤ C₀ ^ ((m : ℝ) / 2) := hdom m

/-- Specialized polynomial absorption for the paper's `m^20` loss. -/
theorem exists_large_halfPower_dominates_twenty
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ C₀ : ℝ, 1000 < C₀ ∧
      ∀ m : ℕ,
        C ^ m * (m : ℝ) ^ 20 ≤ C₀ ^ ((m : ℝ) / 2) :=
  exists_large_halfPower_dominates_polynomial C hC 20

end

end Anderson4D
