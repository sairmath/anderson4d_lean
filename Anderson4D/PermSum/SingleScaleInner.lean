import Anderson4D.PermSum.LocalRefined

/-! Carrier-free analytic core of paper §5.4.3, (5.90)--(5.92). -/
namespace Anderson4D
open scoped BigOperators
noncomputable section
structure XYCluster where
  points : Finset (Fin 4 → ℤ)
  X : ℝ
  N : ℝ
  X_nonneg : 0 ≤ X
  one_le_N : 1 ≤ N
  separated : ∀ x ∈ points, ∀ y ∈ points, x ≠ y → N ≤ znorm (x - y)
namespace XYCluster
def Y (c : XYCluster) : ℝ := c.points.card
def P (c : XYCluster) : ℝ := c.Y * c.N ^ 4
def lambda (c : XYCluster) (R : ℝ) (skipped : Bool)
    (u x : Fin 4 → ℤ) : ℝ :=
  if skipped then R⁻¹ ^ 2
  else if c.N ≤ znorm (u - x) then (znorm (u - x))⁻¹ ^ 2 else 0
def singleInner (c : XYCluster) (R : ℝ) (skipped : Bool)
    (u : Fin 4 → ℤ) : ℝ :=
  c.X * ∑ x ∈ c.points, c.lambda R skipped u x
def pairInner (a b : XYCluster) (R : ℝ) (skipA skipB : Bool)
    (u : Fin 4 → ℤ) : ℝ :=
  a.X * b.X * ∑ x ∈ a.points, a.lambda R skipA u x *
    ∑ y ∈ b.points, b.lambda R skipB x y
private theorem lambda_le (c : XYCluster) (R : ℝ) (skipped : Bool)
    (u x : Fin 4 → ℤ) :
    c.lambda R skipped u x ≤ if skipped then R⁻¹ ^ 2 else c.N⁻¹ ^ 2 := by
  cases skipped with
  | false =>
      simp only [lambda, Bool.false_eq_true, if_false]
      split_ifs with h
      · have hN : 0 < c.N := lt_of_lt_of_le one_pos c.one_le_N
        have hd : 0 < znorm (u - x) := lt_of_lt_of_le hN h
        exact pow_le_pow_left₀ (inv_nonneg.mpr hd.le) (inv_anti₀ hN h) 2
      · positivity
  | true => simp [lambda]
private theorem lambda_nonneg (c : XYCluster) (R : ℝ) (skipped : Bool)
    (u x : Fin 4 → ℤ) : 0 ≤ c.lambda R skipped u x := by
  unfold lambda
  split_ifs <;> positivity
/-- Paper (5.92), in the stronger form `X_j Y_j · (N_j⁻² or R⁻²)`. -/
theorem singleInner_le_5_92 (c : XYCluster) (R : ℝ)
    (skipped : Bool) (u : Fin 4 → ℤ) :
    c.singleInner R skipped u ≤
      c.X * c.Y * (if skipped then R⁻¹ ^ 2 else c.N⁻¹ ^ 2) := by
  unfold singleInner Y
  calc
    c.X * ∑ x ∈ c.points, c.lambda R skipped u x
        ≤ c.X * ∑ _x ∈ c.points,
            (if skipped then R⁻¹ ^ 2 else c.N⁻¹ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ c.X_nonneg
          exact Finset.sum_le_sum fun x _ => lambda_le c R skipped u x
    _ = c.X * c.points.card *
          (if skipped then R⁻¹ ^ 2 else c.N⁻¹ ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
/-- Paper (5.90), with the printed square-root factors multiplied out. -/
theorem pairInner_le_5_90 (a b : XYCluster) (R : ℝ)
    (skipA skipB : Bool) (u : Fin 4 → ℤ) :
    a.pairInner b R skipA skipB u ≤
      (a.X * a.Y * (if skipA then R⁻¹ ^ 2 else a.N⁻¹ ^ 2)) *
      (b.X * b.Y * (if skipB then R⁻¹ ^ 2 else b.N⁻¹ ^ 2)) := by
  unfold pairInner
  let qa := if skipA then R⁻¹ ^ 2 else a.N⁻¹ ^ 2
  let qb := if skipB then R⁻¹ ^ 2 else b.N⁻¹ ^ 2
  calc
    a.X * b.X * ∑ x ∈ a.points, a.lambda R skipA u x *
        ∑ y ∈ b.points, b.lambda R skipB x y
        ≤ a.X * b.X * ∑ _x ∈ a.points, qa *
            ∑ _y ∈ b.points, qb := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg a.X_nonneg b.X_nonneg)
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul
      · exact lambda_le a R skipA u x
      · exact Finset.sum_le_sum fun y _ => lambda_le b R skipB x y
      · exact Finset.sum_nonneg fun y _ => lambda_nonneg b R skipB x y
      · dsimp [qa]
        split_ifs <;> positivity
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, qa, qb, Y]
      ring
private theorem min_quarter_le_eighth (r : ℝ) (hr : 0 ≤ r) :
    min 1 (r ^ (1 / 4 : ℝ)) ≤ min 1 (r ^ (1 / 8 : ℝ)) := by
  rcases le_total r 1 with h | h
  · exact min_le_min le_rfl
      (Real.rpow_le_rpow_of_exponent_ge' hr h (by norm_num) (by norm_num))
  · rw [min_eq_left (Real.one_le_rpow h (by norm_num)),
      min_eq_left (Real.one_le_rpow h (by norm_num))]
private theorem P_nonneg (c : XYCluster) : 0 ≤ c.P := by
  exact mul_nonneg (by simp [Y]) (by positivity)
/-- Unskipped (5.91); Lemma 5.14's `1/4` gain implies the required `1/8`. -/
theorem pairInner_le_5_91_unskipped :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : XYCluster) (u : Fin 4 → ℤ),
      a.X * b.X *
        (∑ x ∈ a.points.filter (fun x => a.N ≤ znorm (u - x)),
          ∑ y ∈ b.points.filter (fun y => max a.N b.N ≤ znorm (x - y)),
            (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2) ≤
      C * a.X * Real.sqrt a.Y * a.N⁻¹ ^ 2 *
        b.X * Real.sqrt b.Y * b.N⁻¹ ^ 2 *
        min 1 ((b.P / a.P) ^ (1 / 8 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := bilinear_cluster_bound
  refine ⟨C, hC, fun a b u => ?_⟩
  have hb := h a.points b.points a.N b.N a.one_le_N b.one_le_N
    a.separated b.separated u
  have hb' :
      (∑ x ∈ a.points.filter (fun x => a.N ≤ znorm (u - x)),
        ∑ y ∈ b.points.filter (fun y => max a.N b.N ≤ znorm (x - y)),
          (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2) ≤
        C * Real.sqrt a.Y * a.N⁻¹ ^ 2 * Real.sqrt b.Y * b.N⁻¹ ^ 2 *
          min 1 ((b.P / a.P) ^ (1 / 4 : ℝ)) := by
    simpa [Y, P] using hb
  have hgain : min 1 ((b.P / a.P) ^ (1 / 4 : ℝ)) ≤
      min 1 ((b.P / a.P) ^ (1 / 8 : ℝ)) :=
    min_quarter_le_eighth _ (div_nonneg (P_nonneg b) (P_nonneg a))
  calc
    _ ≤ a.X * b.X * (C * Real.sqrt a.Y * a.N⁻¹ ^ 2 *
        Real.sqrt b.Y * b.N⁻¹ ^ 2 * min 1 ((b.P / a.P) ^ (1 / 4 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hb' (mul_nonneg a.X_nonneg b.X_nonneg)
    _ ≤ a.X * b.X * (C * Real.sqrt a.Y * a.N⁻¹ ^ 2 *
        Real.sqrt b.Y * b.N⁻¹ ^ 2 * min 1 ((b.P / a.P) ^ (1 / 8 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg a.X_nonneg b.X_nonneg)
      exact mul_le_mul_of_nonneg_left hgain (by positivity)
    _ = _ := by ring
/-- One-parity product assembly with at most twenty discarded (5.87) gains. -/
theorem innerPi_parity_assembly {ι : Type*} [DecidableEq ι]
    (blocks skipped : Finset ι) (_hsub : skipped ⊆ blocks)
    (_h20 : skipped.card ≤ 20) (term base gain : ι → ℝ)
    (hlocal0 : ∀ i ∈ blocks, 0 ≤ term i)
    (hlocal : ∀ i ∈ blocks,
      term i ≤ base i * if i ∈ skipped then 1 else gain i) :
    (∏ i ∈ blocks, term i) ≤
      (∏ i ∈ blocks, base i) *
        ∏ i ∈ blocks, if i ∈ skipped then 1 else gain i := by
  calc
    (∏ i ∈ blocks, term i) ≤
        ∏ i ∈ blocks, base i * if i ∈ skipped then 1 else gain i := by
      exact Finset.prod_le_prod hlocal0 hlocal
    _ = _ := Finset.prod_mul_distrib
end XYCluster
end
end Anderson4D
