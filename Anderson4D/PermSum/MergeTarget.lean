import Anderson4D.PermSum.MergeScaleLedger

/-!
# Factored target for Proposition 5.7

The final run-compression argument uses the same factorial/leaf/scale
summand repeatedly.  Naming it keeps the profile, factorial, and constant
ledgers independent while preserving the frozen statement definitionally.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- One summand of the Proposition 5.7 right-hand side, without its global
constant power. -/
def permSumSummand
    (n : ℕ) {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (W : Finset (VPos t)) : ℝ :=
  ((n - W.card).factorial : ℝ) *
    (∏ l : HeppLeaf t,
      sqrtFactorial (leafMultiplicity mu l)) *
    permSumScaleTail Nm W

theorem permSumSummand_nonneg
    (n : ℕ) {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (W : Finset (VPos t)) :
    0 ≤ permSumSummand n Nm mu W := by
  have hbranch :
      0 ≤
        ∏ v ∈ BranchNodes t,
          (scaleN Nm v : ℝ) ^
            ((-4 : ℤ) *
              (((childrenOf v).card : ℤ) - 1)) := by
    exact Finset.prod_nonneg fun v _ =>
      (zpow_pos
        (by exact_mod_cast scaleN_pos Nm v) _).le
  have hroot :
      0 ≤ (scaleN Nm (rootV t) : ℝ) ^ (-2 : ℤ) :=
    (zpow_pos
      (by exact_mod_cast scaleN_pos Nm (rootV t)) _).le
  have hratio :
      0 ≤
        ∏ v ∈ nonrootBranches t \ W,
          parentScaleRatio Nm v := by
    exact Finset.prod_nonneg fun v _ => by
      unfold parentScaleRatio
      positivity
  unfold permSumSummand permSumScaleTail sqrtFactorial
  positivity

/-- The frozen right-hand side is the global power times the named
nonnegative `W`-sum. -/
theorem permSumRHS_eq_factored
    (C : ℝ) (n : ℕ) (t : PlaneTree)
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    permSumRHS C n t Nm mu =
      C ^ n *
        ∑ W ∈ (nonrootBranches t).powerset,
          permSumSummand n Nm mu W := by
  unfold permSumRHS permSumSummand permSumScaleTail
  congr 1
  apply Finset.sum_congr rfl
  intro W _
  ring

/-- The target sum without its global constant is nonnegative. -/
theorem sum_permSumSummand_nonneg
    (n : ℕ) {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) :
    0 ≤
      ∑ W ∈ (nonrootBranches t).powerset,
        permSumSummand n Nm mu W :=
  Finset.sum_nonneg fun W _ =>
    permSumSummand_nonneg n Nm mu W

end

end Anderson4D
