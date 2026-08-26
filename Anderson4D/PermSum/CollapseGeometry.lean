import Anderson4D.HeppTree.VolumeEstimate
import Anderson4D.PermSum.Statements

/-!
# Geometric replacement bounds for the collapse induction

The proof of Proposition 5.9 replaces every point in a collapsed subtree
by one distinguished leaf.  The paper prints the weaker comparability
(5.41), but the preceding argument gives a quarter-distance perturbation.
Retaining that stronger form makes each changed edge cost at most `2`;
with at most `2n` boundary edges this is the stated `4^n` loss in (5.43).
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

/-- A perturbation by at most one quarter of the original distance changes
the new distance by at most a factor `5/4`, in division-free form. -/
theorem four_mul_znorm_replacement_le_five_mul
    (y x x' : Fin 4 → ℤ)
    (hsmall : 4 * znorm (x - x') ≤ znorm (y - x)) :
    4 * znorm (y - x') ≤ 5 * znorm (y - x) := by
  have htri := znorm_triangle y x x'
  linarith

/-- The displayed lower half of paper (5.41). -/
theorem znorm_le_two_mul_replacement
    (y x x' : Fin 4 → ℤ)
    (hsmall : 4 * znorm (x - x') ≤ znorm (y - x)) :
    znorm (y - x) ≤ 2 * znorm (y - x') := by
  have htri := znorm_triangle y x' x
  rw [znorm_sub_comm x' x] at htri
  linarith [znorm_nonneg (y - x')]

/-- Paper (5.41), kept in division-free form. -/
theorem collapse_distance_comparable
    (y x x' : Fin 4 → ℤ)
    (hsmall : 4 * znorm (x - x') ≤ znorm (y - x)) :
    znorm (y - x) ≤ 2 * znorm (y - x') ∧
      znorm (y - x') ≤ 2 * znorm (y - x) := by
  refine ⟨znorm_le_two_mul_replacement y x x' hsmall, ?_⟩
  have hstrong :=
    four_mul_znorm_replacement_le_five_mul y x x' hsmall
  linarith [znorm_nonneg (y - x)]

/-- Scalar inverse-bracket comparison used for one boundary edge. -/
theorem inv_one_add_sq_le_two_mul_inv_one_add_sq
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hba : 4 * b ≤ 5 * a) :
    (1 + a ^ 2)⁻¹ ≤ 2 * (1 + b ^ 2)⁻¹ := by
  have hratio : b ≤ (5 / 4 : ℝ) * a := by linarith
  have hratioNonneg : 0 ≤ (5 / 4 : ℝ) * a := by positivity
  have hsq :
      b ^ 2 ≤ 2 * a ^ 2 := by
    calc
      b ^ 2 ≤ ((5 / 4 : ℝ) * a) ^ 2 :=
        (sq_le_sq₀ hb hratioNonneg).2 hratio
      _ ≤ 2 * a ^ 2 := by nlinarith [sq_nonneg a]
  calc
    (1 + a ^ 2)⁻¹ = 1 / (1 + a ^ 2) := by simp only [one_div]
    _ ≤ 2 / (1 + b ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    _ = 2 * (1 + b ^ 2)⁻¹ := by rw [div_eq_mul_inv]

/-- Replacing one endpoint by a point within a quarter of the original
edge length costs at most a factor `2` in `latticeEdgeWeight`. -/
theorem latticeEdgeWeight_le_two_mul_of_quarter_replacement
    (y x x' : Fin 4 → ℤ)
    (hsmall : 4 * znorm (x - x') ≤ znorm (y - x)) :
    latticeEdgeWeight y x ≤ 2 * latticeEdgeWeight y x' := by
  have hdist :=
    four_mul_znorm_replacement_le_five_mul y x x' hsmall
  unfold latticeEdgeWeight
  exact inv_one_add_sq_le_two_mul_inv_one_add_sq
    (znorm (y - x)) (znorm (y - x'))
    (znorm_nonneg _) (znorm_nonneg _) hdist

/-- Symmetric endpoint version of the same replacement estimate. -/
theorem latticeEdgeWeight_le_two_mul_of_quarter_replacement_left
    (y x x' : Fin 4 → ℤ)
    (hsmall : 4 * znorm (x - x') ≤ znorm (y - x)) :
    latticeEdgeWeight x y ≤ 2 * latticeEdgeWeight x' y := by
  simpa only [latticeEdgeWeight, znorm_sub_comm x y,
    znorm_sub_comm x' y] using
    latticeEdgeWeight_le_two_mul_of_quarter_replacement y x x' hsmall

/-- At most `2n` replacement edges, each costing at most `2`, give the
`4^n` loss printed in (5.43). -/
theorem prod_le_four_pow_mul_prod_of_card_le_two_mul
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f g : ι → ℝ) (n : ℕ)
    (hf : ∀ i ∈ S, 0 ≤ f i)
    (hg : ∀ i ∈ S, 0 ≤ g i)
    (hfg : ∀ i ∈ S, f i ≤ 2 * g i)
    (hcard : S.card ≤ 2 * n) :
    (∏ i ∈ S, f i) ≤
      (4 : ℝ) ^ n * ∏ i ∈ S, g i := by
  calc
    (∏ i ∈ S, f i) ≤ ∏ i ∈ S, 2 * g i :=
      Finset.prod_le_prod hf hfg
    _ = (2 : ℝ) ^ S.card * ∏ i ∈ S, g i := by
      rw [Finset.prod_mul_distrib]
      simp
    _ ≤ (2 : ℝ) ^ (2 * n) * ∏ i ∈ S, g i :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) hcard)
        (Finset.prod_nonneg hg)
    _ = (4 : ℝ) ^ n * ∏ i ∈ S, g i := by
      rw [pow_mul]
      norm_num

end Anderson4D
