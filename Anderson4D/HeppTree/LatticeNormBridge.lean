import Anderson4D.HeppTree.VolumeEstimate

/-!
# Sup-norm to Euclidean-norm bridge on the four-dimensional lattice

The discrete Hepp-tree estimates use `znorm`, mathlib's sup norm on
`Fin 4 → ℝ`, while the paper's unqualified lattice norm may be read as the
Euclidean norm.  This file makes the finite-dimensional equivalence explicit.
In particular, the Euclidean fourth-order bracket is bounded by the sup-norm
bracket used in Proposition 5.6, and conversely with the sharp dimension-four
loss `16`.
-/

namespace Anderson4D

open scoped BigOperators

/-- Squared Euclidean norm of an integer four-vector. -/
def zEuclideanNormSq (x : LatticePoint) : ℝ :=
  ∑ i, (x i : ℝ) ^ 2

theorem zEuclideanNormSq_nonneg (x : LatticePoint) :
    0 ≤ zEuclideanNormSq x := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i : ℝ)

/-- The sup norm squared is no larger than the Euclidean norm squared. -/
theorem znorm_sq_le_zEuclideanNormSq (x : LatticePoint) :
    znorm x ^ 2 ≤ zEuclideanNormSq x := by
  have hnorm : znorm x ≤ Real.sqrt (zEuclideanNormSq x) := by
    rw [znorm, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    simp only [Real.norm_eq_abs]
    have hi : (x i : ℝ) ^ 2 ≤ zEuclideanNormSq x := by
      unfold zEuclideanNormSq
      exact Finset.single_le_sum
        (fun j _ => sq_nonneg (x j : ℝ)) (Finset.mem_univ i)
    have hsqrt := Real.sq_sqrt (zEuclideanNormSq_nonneg x)
    nlinarith [sq_abs (x i : ℝ), abs_nonneg (x i : ℝ),
      Real.sqrt_nonneg (zEuclideanNormSq x)]
  calc
    znorm x ^ 2 ≤ (Real.sqrt (zEuclideanNormSq x)) ^ 2 :=
      pow_le_pow_left₀ (znorm_nonneg x) hnorm 2
    _ = zEuclideanNormSq x :=
      Real.sq_sqrt (zEuclideanNormSq_nonneg x)

/-- In four dimensions the Euclidean norm squared is at most four times the
sup norm squared. -/
theorem zEuclideanNormSq_le_four_mul_znorm_sq (x : LatticePoint) :
    zEuclideanNormSq x ≤ 4 * znorm x ^ 2 := by
  calc
    zEuclideanNormSq x ≤ ∑ _i : Fin 4, znorm x ^ 2 := by
      unfold zEuclideanNormSq
      apply Finset.sum_le_sum
      intro i _
      have hi := znorm_coord_le x i
      simpa only [sq_abs] using
        (pow_le_pow_left₀ (abs_nonneg (x i : ℝ)) hi 2)
    _ = 4 * znorm x ^ 2 := by simp

/-- Euclidean norm of an integer four-vector. -/
noncomputable def zEuclideanNorm (x : LatticePoint) : ℝ :=
  Real.sqrt (zEuclideanNormSq x)

theorem znorm_le_zEuclideanNorm (x : LatticePoint) :
    znorm x ≤ zEuclideanNorm x := by
  unfold zEuclideanNorm
  have h := znorm_sq_le_zEuclideanNormSq x
  have hsqrt := Real.sq_sqrt (zEuclideanNormSq_nonneg x)
  nlinarith [znorm_nonneg x, Real.sqrt_nonneg (zEuclideanNormSq x)]

theorem zEuclideanNorm_le_two_mul_znorm (x : LatticePoint) :
    zEuclideanNorm x ≤ 2 * znorm x := by
  unfold zEuclideanNorm
  have h := zEuclideanNormSq_le_four_mul_znorm_sq x
  have hsqrt := Real.sq_sqrt (zEuclideanNormSq_nonneg x)
  nlinarith [znorm_nonneg x, Real.sqrt_nonneg (zEuclideanNormSq x)]

/-- Euclidean reading of the fourth-order bracket in paper (5.14). -/
noncomputable def latticeEuclideanBracketInvFourth
    (x₀ x₁ : LatticePoint) : ℝ :=
  ((1 + zEuclideanNormSq (x₀ - x₁)) ^ 2)⁻¹

theorem latticeEuclideanBracketInvFourth_nonneg
    (x₀ x₁ : LatticePoint) :
    0 ≤ latticeEuclideanBracketInvFourth x₀ x₁ := by
  unfold latticeEuclideanBracketInvFourth
  positivity

/-- The Euclidean bracket is pointwise no larger than the sup-norm bracket
already controlled by Proposition 5.6. -/
theorem latticeEuclideanBracketInvFourth_le_latticeBracketInvFourth
    (x₀ x₁ : LatticePoint) :
    latticeEuclideanBracketInvFourth x₀ x₁ ≤
      latticeBracketInvFourth x₀ x₁ := by
  unfold latticeEuclideanBracketInvFourth latticeBracketInvFourth
  apply inv_anti₀
  · positivity
  · gcongr
    exact znorm_sq_le_zEuclideanNormSq (x₀ - x₁)

/-- Reverse bracket comparison.  The factor is
`2⁴ = 16`, exactly the dimension-four norm-equivalence loss. -/
theorem latticeBracketInvFourth_le_sixteen_mul_euclidean
    (x₀ x₁ : LatticePoint) :
    latticeBracketInvFourth x₀ x₁ ≤
      16 * latticeEuclideanBracketInvFourth x₀ x₁ := by
  let A := 1 + znorm (x₀ - x₁) ^ 2
  let B := 1 + zEuclideanNormSq (x₀ - x₁)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    have := zEuclideanNormSq_nonneg (x₀ - x₁)
    linarith
  have hBA : B ≤ 4 * A := by
    dsimp [A, B]
    have h := zEuclideanNormSq_le_four_mul_znorm_sq (x₀ - x₁)
    nlinarith [sq_nonneg (znorm (x₀ - x₁))]
  have hsq : B ^ 2 ≤ 16 * A ^ 2 := by
    calc
      B ^ 2 ≤ (4 * A) ^ 2 := pow_le_pow_left₀ hB.le hBA 2
      _ = 16 * A ^ 2 := by ring
  have hinv : (16 * A ^ 2)⁻¹ ≤ (B ^ 2)⁻¹ := by
    exact inv_anti₀ (pow_pos hB 2) hsq
  change (A ^ 2)⁻¹ ≤ 16 * (B ^ 2)⁻¹
  calc
    (A ^ 2)⁻¹ = 16 * (16 * A ^ 2)⁻¹ := by
      field_simp
    _ ≤ 16 * (B ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)

end Anderson4D
