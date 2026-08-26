import Anderson4D.PermSum.CollapseRHS
import Anderson4D.PermSum.CollapseFactorial
import Anderson4D.PermSum.CollapseConstants
import Anderson4D.PermSum.CollapseCompositionCount
import Anderson4D.PermSum.CollapseBranchLedger

/-!
# Final scalar ledger for the collapse induction

This file closes the numerical estimates (5.46)--(5.48).  The strict
branch-count saving supplies the inverse `D`, the new compound-leaf factor is
absorbed locally, and the remaining factorial and exponential losses fit the
original-tree induction coefficient.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## Positivity of the unchanged induction tail -/

theorem paperLeafProduct_nonneg {t : PlaneTree}
    (mu : Multiplicities t) (compound : Finset (VPos t)) :
    0 ≤ paperLeafProduct mu compound := by
  unfold paperLeafProduct paperLeafFactor sqrtFactorial
    factorialThreeQuarters
  positivity

theorem singleScaleBranchPower_nonneg {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) :
    0 ≤ singleScaleBranchPower Nm mu compound := by
  unfold singleScaleBranchPower
  positivity

theorem originalParentRatioFactor_nonneg {t : PlaneTree}
    (Nm : HeppMarking t) (W : Finset (VPos t)) :
    0 ≤ originalParentRatioFactor Nm W := by
  unfold originalParentRatioFactor parentScaleRatio
  positivity

/-! ## The strict `D` saving and local compound-leaf factor -/

/-- A one-unit branch-exponent saving pays for the entire new compound-leaf
factor. -/
theorem collapseDLocal_power_le
    (C0 D : ℝ) (hC0 : 1000 < C0)
    (hD : D = Real.exp (C0 ^ (10 : ℕ)))
    (a b k : ℕ) (hab : a + 1 ≤ b) :
    D ^ a * C0 ^ k * (k.factorial : ℝ)⁻¹ *
        factorialThreeQuarters k ≤
      D ^ b := by
  have hC0nonneg : 0 ≤ C0 := by
    linarith
  have hDge : 1 ≤ D := by
    rw [hD]
    exact Real.one_le_exp (by positivity)
  have hpow : D ^ a ≤ D ^ b * D⁻¹ :=
    pow_le_pow_mul_inv_of_succ_le D hDge a b hab
  have hrest :
      0 ≤ C0 ^ k * (k.factorial : ℝ)⁻¹ *
        factorialThreeQuarters k := by
    unfold factorialThreeQuarters
    positivity
  calc
    D ^ a * C0 ^ k * (k.factorial : ℝ)⁻¹ *
          factorialThreeQuarters k =
        D ^ a *
          (C0 ^ k * (k.factorial : ℝ)⁻¹ *
            factorialThreeQuarters k) := by
      ring
    _ ≤ (D ^ b * D⁻¹) *
          (C0 ^ k * (k.factorial : ℝ)⁻¹ *
            factorialThreeQuarters k) :=
      mul_le_mul_of_nonneg_right hpow hrest
    _ = D ^ b * collapseDLocalFactor C0 D k := by
      unfold collapseDLocalFactor
      ring
    _ ≤ D ^ b * 1 := by
      exact mul_le_mul_of_nonneg_left
        (collapseDLocalFactor_le_one C0 D hC0 hD k)
        (by positivity)
    _ = D ^ b := by
      ring

/-! ## Factorial and skipped-branch cardinality ledger -/

/-- Paper (5.47), with the cardinality of `W'` substituted and its polynomial
loss enlarged to `2^n`. -/
theorem collapse_factorial_card_bound
    {t : PlaneTree} (r : VPos t)
    (n m s : ℕ) (hn : 4 ≤ n) (hs : 1 ≤ s)
    (hsn : s + 1 ≤ n)
    (W : Finset (VPos (contractAt t r.1)))
    (hW : W ⊆ nonrootBranches (contractAt t r.1))
    (hw : 2 * W.card ≤ m) :
    sqrtFactorial (n - s) *
        sqrtFactorial (m + s + 1 - 2 * W.card) ≤
      sqrtFactorial
          (n + m - 2 * (liftWPrime r s W).card) *
        (2 : ℝ) ^ n := by
  have hfac :
      sqrtFactorial (n - s) *
          sqrtFactorial (m + s + 1 - 2 * W.card) ≤
        sqrtFactorial
            (n + m - 2 * (liftWPrime r s W).card) *
          (n : ℝ) ^ 2 := by
    simpa only [sqrtFactorial, card_liftWPrime r s W hW] using
      collapse_factorial_sqrt_bound n m s W.card hs hsn hn hw
  calc
    sqrtFactorial (n - s) *
          sqrtFactorial (m + s + 1 - 2 * W.card) ≤
        sqrtFactorial
            (n + m - 2 * (liftWPrime r s W).card) *
          (n : ℝ) ^ 2 := hfac
    _ ≤ sqrtFactorial
          (n + m - 2 * (liftWPrime r s W).card) *
        (2 : ℝ) ^ n := by
      exact mul_le_mul_of_nonneg_left
        (natCast_sq_le_two_pow hn)
        (by unfold sqrtFactorial; positivity)

/-! ## Complete scalar coefficient -/

/-- The complete scalar inequality in (5.46)--(5.48), before multiplying by
the unchanged leaf/branch/ratio tail.  The leading `2^n` is the outer
composition-count loss. -/
theorem collapse_scalar_coefficient_le
    (C0 D : ℝ) (hC0 : 1000 < C0)
    (hD : D = Real.exp (C0 ^ (10 : ℕ)))
    (n m s : ℕ) (hn : 4 ≤ n) (hs : 1 ≤ s)
    (hsn : s + 1 ≤ n)
    {t : PlaneTree} (r : VPos t)
    (hr : r ∈ nonrootBranches t)
    (W : Finset (VPos (contractAt t r.1)))
    (hW : W ⊆ nonrootBranches (contractAt t r.1))
    (hw : 2 * W.card ≤ m) :
    (2 : ℝ) ^ n *
        ((4 : ℝ) ^ n *
          C0 ^ ((n : ℝ) / 2) *
          C0 ^ (m + s + 1) *
          D ^ (BranchNodes (contractAt t r.1)).card *
          ((s + 1).factorial : ℝ)⁻¹ *
          factorialThreeQuarters (s + 1) *
          sqrtFactorial (n - s) *
          sqrtFactorial (m + s + 1 - 2 * W.card)) ≤
      C0 ^ (n + m) * D ^ (BranchNodes t).card *
        sqrtFactorial
          (n + m - 2 * (liftWPrime r s W).card) := by
  have hC0nonneg : 0 ≤ C0 := by
    linarith
  have hDpos : 0 < D := by
    rw [hD]
    positivity
  have hrBranch : r ∈ BranchNodes t :=
    (Finset.mem_erase.mp hr).2
  have hlocal :
      D ^ (BranchNodes (contractAt t r.1)).card *
          C0 ^ (s + 1) *
          ((s + 1).factorial : ℝ)⁻¹ *
          factorialThreeQuarters (s + 1) ≤
        D ^ (BranchNodes t).card := by
    exact collapseDLocal_power_le C0 D hC0 hD
      (BranchNodes (contractAt t r.1)).card
      (BranchNodes t).card (s + 1)
      (card_BranchNodes_contractAt_add_one_le hrBranch)
  have hfac :=
    collapse_factorial_card_bound r n m s hn hs hsn W hW hw
  have hexp :=
    sixteen_pow_mul_halfPower_le_natPower C0 hC0 n
  have h24 :
      (2 : ℝ) ^ n * (4 : ℝ) ^ n = (8 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  have h82 :
      (8 : ℝ) ^ n * (2 : ℝ) ^ n = (16 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  have hA :
      0 ≤ (8 : ℝ) ^ n * C0 ^ ((n : ℝ) / 2) * C0 ^ m := by
    positivity
  have hfactorials :
      0 ≤ sqrtFactorial (n - s) *
        sqrtFactorial (m + s + 1 - 2 * W.card) := by
    unfold sqrtFactorial
    positivity
  have hAD :
      0 ≤ (8 : ℝ) ^ n * C0 ^ ((n : ℝ) / 2) *
        C0 ^ m * D ^ (BranchNodes t).card := by
    positivity
  have htail :
      0 ≤ C0 ^ m * D ^ (BranchNodes t).card *
        sqrtFactorial
          (n + m - 2 * (liftWPrime r s W).card) := by
    unfold sqrtFactorial
    positivity
  calc
    (2 : ℝ) ^ n *
          ((4 : ℝ) ^ n *
            C0 ^ ((n : ℝ) / 2) *
            C0 ^ (m + s + 1) *
            D ^ (BranchNodes (contractAt t r.1)).card *
            ((s + 1).factorial : ℝ)⁻¹ *
            factorialThreeQuarters (s + 1) *
            sqrtFactorial (n - s) *
            sqrtFactorial (m + s + 1 - 2 * W.card)) =
        ((8 : ℝ) ^ n * C0 ^ ((n : ℝ) / 2) * C0 ^ m) *
          (D ^ (BranchNodes (contractAt t r.1)).card *
            C0 ^ (s + 1) *
            ((s + 1).factorial : ℝ)⁻¹ *
            factorialThreeQuarters (s + 1)) *
          (sqrtFactorial (n - s) *
            sqrtFactorial (m + s + 1 - 2 * W.card)) := by
      rw [← h24, show m + s + 1 = m + (s + 1) by omega, pow_add]
      ring
    _ ≤
        ((8 : ℝ) ^ n * C0 ^ ((n : ℝ) / 2) * C0 ^ m) *
          D ^ (BranchNodes t).card *
          (sqrtFactorial (n - s) *
            sqrtFactorial (m + s + 1 - 2 * W.card)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlocal hA) hfactorials
    _ ≤
        ((8 : ℝ) ^ n * C0 ^ ((n : ℝ) / 2) * C0 ^ m) *
          D ^ (BranchNodes t).card *
          (sqrtFactorial
              (n + m - 2 * (liftWPrime r s W).card) *
            (2 : ℝ) ^ n) := by
      exact mul_le_mul_of_nonneg_left hfac hAD
    _ =
        ((16 : ℝ) ^ n * C0 ^ ((n : ℝ) / 2)) *
          (C0 ^ m * D ^ (BranchNodes t).card *
            sqrtFactorial
              (n + m - 2 * (liftWPrime r s W).card)) := by
      rw [← h82]
      ring
    _ ≤
        C0 ^ n *
          (C0 ^ m * D ^ (BranchNodes t).card *
            sqrtFactorial
              (n + m - 2 * (liftWPrime r s W).card)) :=
      mul_le_mul_of_nonneg_right hexp htail
    _ =
        C0 ^ (n + m) * D ^ (BranchNodes t).card *
          sqrtFactorial
            (n + m - 2 * (liftWPrime r s W).card) := by
      rw [pow_add]
      ring

/-! ## Final (5.46)--(5.48) interface -/

/-- Paper (5.46)--(5.48): after the outer composition count, one factored
collapse term is bounded by the corresponding original-tree induction
summand. -/
theorem two_pow_mul_combinedCollapseFactored_le_inductiveRHSSummand
    (C0 D : ℝ) (hC0 : 1000 < C0)
    (hD : D = Real.exp (C0 ^ (10 : ℕ)))
    (n mOutside s : ℕ) (hn : 4 ≤ n) (hs : 1 ≤ s)
    (hsn : s + 1 ≤ n)
    {t : PlaneTree} (_ : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t))
    (r : VPos t) (hr : r ∈ nonrootBranches t)
    (W : Finset (VPos (contractAt t r.1)))
    (hW : W ⊆ nonrootBranches (contractAt t r.1))
    (hWcard : 2 * W.card ≤ mOutside) :
    (2 : ℝ) ^ n *
        combinedCollapseFactored C0 D n s (mOutside + s + 1)
          Nm mu compound r W ≤
      C0 ^ (n + mOutside) * D ^ (BranchNodes t).card *
        inductiveRHSSummand (n + mOutside) t Nm mu compound
          (liftWPrime r s W) := by
  have hscalar :=
    collapse_scalar_coefficient_le C0 D hC0 hD
      n mOutside s hn hs hsn r hr W hW hWcard
  have htail :
      0 ≤ paperLeafProduct mu compound *
        singleScaleBranchPower Nm mu compound *
        originalParentRatioFactor Nm (liftWPrime r s W) := by
    exact mul_nonneg
      (mul_nonneg
        (paperLeafProduct_nonneg mu compound)
        (singleScaleBranchPower_nonneg Nm mu compound))
      (originalParentRatioFactor_nonneg Nm (liftWPrime r s W))
  calc
    (2 : ℝ) ^ n *
          combinedCollapseFactored C0 D n s (mOutside + s + 1)
            Nm mu compound r W =
        ((2 : ℝ) ^ n *
          ((4 : ℝ) ^ n *
            C0 ^ ((n : ℝ) / 2) *
            C0 ^ (mOutside + s + 1) *
            D ^ (BranchNodes (contractAt t r.1)).card *
            ((s + 1).factorial : ℝ)⁻¹ *
            factorialThreeQuarters (s + 1) *
            sqrtFactorial (n - s) *
            sqrtFactorial
              (mOutside + s + 1 - 2 * W.card))) *
          (paperLeafProduct mu compound *
            singleScaleBranchPower Nm mu compound *
            originalParentRatioFactor Nm (liftWPrime r s W)) := by
      unfold combinedCollapseFactored
      ring
    _ ≤
        (C0 ^ (n + mOutside) * D ^ (BranchNodes t).card *
          sqrtFactorial
            (n + mOutside -
              2 * (liftWPrime r s W).card)) *
          (paperLeafProduct mu compound *
            singleScaleBranchPower Nm mu compound *
            originalParentRatioFactor Nm (liftWPrime r s W)) :=
      mul_le_mul_of_nonneg_right hscalar htail
    _ =
        C0 ^ (n + mOutside) * D ^ (BranchNodes t).card *
          inductiveRHSSummand (n + mOutside) t Nm mu compound
            (liftWPrime r s W) := by
      unfold inductiveRHSSummand
      ring

end
end Anderson4D
