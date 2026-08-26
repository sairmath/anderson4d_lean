import Anderson4D.Combinatorics.OpenEdgeAugmentation
import Anderson4D.PermSum.CollapsePredicates
import Anderson4D.PermSum.WeightFilters

/-!
# Chain-weight ledger for one opened edge

The primitive-pairing augmentation appends copies of the two marked endpoint
labels.  This introduces exactly two final chain edges.  The equality
below exposes those factors; later R-324 estimates pay their inverse
with the extra `ε⁴` available from the strengthened high-frequency
symbol bound.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open PlaneTree
open scoped BigOperators

/-- Rewrite the project's adjacency-index product as the equivalent
product over predecessor indices. -/
theorem heppChainWeight_eq_finPred
    {t : PlaneTree} {m : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ)
    (w : Fin m → HeppLeaf t) :
    heppChainWeight z w =
      ∏ i : Fin (m - 1),
        latticeEdgeWeight
          (z (w ⟨i.val, by omega⟩))
          (z (w ⟨i.val + 1, by omega⟩)) := by
  unfold heppChainWeight
  symm
  apply Fintype.prod_equiv
    (finPredEquivAdjacentIndex m)
  intro i
  rfl

/-- Peel the final edge from a nontrivial chain. -/
theorem heppChainWeight_snoc
    {t : PlaneTree} (k : ℕ)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (u : Fin (k + 2) → HeppLeaf t) :
    heppChainWeight z u =
      heppChainWeight z (Fin.init u) *
        latticeEdgeWeight
          (z (u ⟨k, by omega⟩))
          (z (u ⟨k + 1, by omega⟩)) := by
  rw [heppChainWeight_eq_finPred,
    heppChainWeight_eq_finPred]
  change
    (∏ i : Fin (k + 1),
      latticeEdgeWeight
        (z (u ⟨i.val, by omega⟩))
        (z (u ⟨i.val + 1, by omega⟩))) =
      (∏ i : Fin k,
        latticeEdgeWeight
          (z (Fin.init u ⟨i.val, by omega⟩))
          (z (Fin.init u ⟨i.val + 1, by omega⟩))) *
        latticeEdgeWeight
          (z (u ⟨k, by omega⟩))
          (z (u ⟨k + 1, by omega⟩))
  rw [Fin.prod_univ_castSucc]
  rfl

/-- Appending the two dummy copies introduces exactly the final edges
`last → a` and `a → b`. -/
theorem heppChainWeight_openEdgeAugmentedWord
    {t : PlaneTree} {m : ℕ} (hm : 0 < m)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (w : Fin m → HeppLeaf t)
    (a b : Fin m) :
    heppChainWeight z
        (openEdgeAugmentedWord w a b) =
      heppChainWeight z w *
        latticeEdgeWeight
          (z (w ⟨m - 1, by omega⟩))
          (z (w a)) *
        latticeEdgeWeight (z (w a)) (z (w b)) := by
  obtain ⟨k, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hinitinit :
      Fin.init (Fin.init
        (openEdgeAugmentedWord w a b)) = w := by
    funext i
    change
      openEdgeAugmentedWord w a b
          (Fin.castAdd 2 i) = w i
    exact openEdgeAugmentedWord_old w a b i
  have hlast :
      Fin.init (openEdgeAugmentedWord w a b)
          ⟨k, by omega⟩ =
        w ⟨k, by omega⟩ := by
    change
      openEdgeAugmentedWord w a b
          (Fin.castAdd 2 ⟨k, by omega⟩) =
        w ⟨k, by omega⟩
    exact openEdgeAugmentedWord_old w a b _
  have hfirstInit :
      Fin.init (openEdgeAugmentedWord w a b)
          ⟨k + 1, by omega⟩ = w a := by
    change
      openEdgeAugmentedWord w a b
          (openEdgeFirstNew (k + 1)) = w a
    exact openEdgeAugmentedWord_firstNew w a b
  have hfirst :
      openEdgeAugmentedWord w a b
          ⟨k + 1, by omega⟩ = w a := by
    change
      openEdgeAugmentedWord w a b
          (openEdgeFirstNew (k + 1)) = w a
    exact openEdgeAugmentedWord_firstNew w a b
  have hsecond :
      openEdgeAugmentedWord w a b
          ⟨k + 2, by omega⟩ = w b := by
    change
      openEdgeAugmentedWord w a b
          (openEdgeSecondNew (k + 1)) = w b
    exact openEdgeAugmentedWord_secondNew w a b
  rw [heppChainWeight_snoc (k + 1),
    heppChainWeight_snoc k,
    hinitinit, hlast, hfirstInit, hfirst, hsecond]
  congr 2

/-- Two points of the admissible lattice box are at sup distance at most
`2M`. -/
theorem znorm_sub_le_two_mul_of_box
    {M : ℕ} {x y : Fin 4 → ℤ}
    (hx : ∀ i, |x i| ≤ (M : ℤ))
    (hy : ∀ i, |y i| ≤ (M : ℤ)) :
    znorm (x - y) ≤ 2 * (M : ℝ) := by
  have hpos : (0 : ℝ) ≤ 2 * (M : ℝ) := by positivity
  rw [znorm, pi_norm_le_iff_of_nonneg hpos]
  intro i
  have hZ : |x i - y i| ≤ (2 * M : ℤ) := by
    calc
      |x i - y i| ≤ |x i| + |y i| := by
        simpa [sub_eq_add_neg, abs_neg] using
          abs_add_le (x i) (-(y i))
      _ ≤ (M : ℤ) + (M : ℤ) :=
        add_le_add (hx i) (hy i)
      _ = (2 * M : ℤ) := by ring
  have hcast :
      |(x i : ℝ) - (y i : ℝ)| ≤
        ((2 * M : ℕ) : ℝ) := by
    have := (Int.cast_le (R := ℝ)).mpr hZ
    push_cast at this ⊢
    simpa using this
  calc
    ‖((x - y) i : ℝ)‖ =
        |(x i : ℝ) - (y i : ℝ)| := by
      rw [Real.norm_eq_abs]
      norm_num [Pi.sub_apply]
    _ ≤ ((2 * M : ℕ) : ℝ) := hcast
    _ = 2 * (M : ℝ) := by norm_num

/-- One lattice-box penalty reverses one of the two extra appended edge
weights. -/
theorem one_le_boxPenalty_mul_latticeEdgeWeight
    {M : ℕ} {x y : Fin 4 → ℤ}
    (hx : ∀ i, |x i| ≤ (M : ℤ))
    (hy : ∀ i, |y i| ≤ (M : ℤ)) :
    1 ≤ (1 + (2 * (M : ℝ)) ^ 2) *
      latticeEdgeWeight x y := by
  have hdist :=
    znorm_sub_le_two_mul_of_box hx hy
  have hD : 0 ≤ znorm (x - y) := znorm_nonneg _
  have h2M : 0 ≤ 2 * (M : ℝ) := by positivity
  have hsquare :
      znorm (x - y) ^ 2 ≤
        (2 * (M : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hD hdist 2
  have hden :
      0 < 1 + znorm (x - y) ^ 2 := by positivity
  unfold latticeEdgeWeight
  rw [show (1 + (2 * (M : ℝ)) ^ 2) *
      (1 + znorm (x - y) ^ 2)⁻¹ =
      (1 + (2 * (M : ℝ)) ^ 2) /
        (1 + znorm (x - y) ^ 2) by
      rw [div_eq_mul_inv]]
  exact (le_div_iff₀ hden).mpr (by linarith)

/-- The original open-edge chain is controlled by the augmented
primitive chain with the explicit square box penalty. -/
theorem heppChainWeight_le_boxPenalty_sq_mul_openEdgeAugmented
    {t : PlaneTree} {m : ℕ} (hm : 0 < m)
    {Nm : HeppMarking t} {M : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ)
    (hadm : IsAdmissible Nm M z)
    (w : Fin m → HeppLeaf t)
    (a b : Fin m) :
    heppChainWeight z w ≤
      (1 + (2 * (M : ℝ)) ^ 2) ^ 2 *
        heppChainWeight z
          (openEdgeAugmentedWord w a b) := by
  let last : Fin m := ⟨m - 1, by omega⟩
  let B : ℝ := 1 + (2 * (M : ℝ)) ^ 2
  have h₁ :
      1 ≤ B *
        latticeEdgeWeight
          (z (w last)) (z (w a)) :=
    one_le_boxPenalty_mul_latticeEdgeWeight
      (hadm.bounded (w last))
      (hadm.bounded (w a))
  have h₂ :
      1 ≤ B *
        latticeEdgeWeight
          (z (w a)) (z (w b)) :=
    one_le_boxPenalty_mul_latticeEdgeWeight
      (hadm.bounded (w a))
      (hadm.bounded (w b))
  have hchain : 0 ≤ heppChainWeight z w :=
    heppChainWeight_nonneg z w
  rw [heppChainWeight_openEdgeAugmentedWord hm]
  dsimp only [B, last] at h₁ h₂ ⊢
  calc
    heppChainWeight z w =
        heppChainWeight z w * 1 * 1 := by ring
    _ ≤
        heppChainWeight z w *
          ((1 + (2 * (M : ℝ)) ^ 2) *
            latticeEdgeWeight
              (z (w ⟨m - 1, by omega⟩))
              (z (w a))) *
          ((1 + (2 * (M : ℝ)) ^ 2) *
            latticeEdgeWeight (z (w a)) (z (w b))) := by
      gcongr
    _ =
        (1 + (2 * (M : ℝ)) ^ 2) ^ 2 *
          (heppChainWeight z w *
            latticeEdgeWeight
              (z (w ⟨m - 1, by omega⟩))
              (z (w a)) *
            latticeEdgeWeight (z (w a)) (z (w b))) := by
      ring

end

end Anderson4D
