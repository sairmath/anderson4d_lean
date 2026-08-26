import Anderson4D.PermSum.Inductive
import Anderson4D.PermSum.MergeFactorialApplication
import Anderson4D.PermSum.MergeLedger
import Anderson4D.PermSum.MergeTarget

/-!
# Applying the inductive estimate after run compression

This module combines the compressed P-5.9 right-hand side with the
factorial comparison (5.37).  The result is expressed in the fixed
P-5.7 `W`-sum; profile and expansion counting are deliberately left to
the final finite-sum assembly.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- Pointwise conversion of a compressed P-5.9 summand into the P-5.7
factorial/leaf/scale summand. -/
theorem mergeLedgerRatio_mul_inductiveRHSSummand_le
    {t : PlaneTree} {M n : ℕ}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t)
    (mu : Multiplicities t)
    (w : Fin M → HeppLeaf t)
    (hvalid : w ∈ validWords (leafMultiplicity mu))
    (hprimitive : NoProperLeafBlock w)
    (htotal : totalMultiplicity mu = 2 * n)
    (W : Finset (VPos t))
    (hW : W ⊆ nonrootBranches t) :
    mergeLedgerRatio
          (leafMultiplicity mu)
          (leafMultiplicity
            (mergedMultiplicities
              hroot mu w hvalid hprimitive)) *
        inductiveRHSSummand
          (mergedWordList w).length t Nm
          (mergedMultiplicities
            hroot mu w hvalid hprimitive) ∅ W ≤
      (4 : ℝ) ^ n * permSumSummand n Nm mu W := by
  let mu' : Multiplicities t :=
    mergedMultiplicities hroot mu w hvalid hprimitive
  have hfactorial :=
    merged_factorial_leaf_product_le_four_pow
      ht hroot mu w hvalid hprimitive htotal W hW
  have htail : 0 ≤ permSumScaleTail Nm W := by
    unfold permSumScaleTail parentScaleRatio
    have hbranch :
        0 ≤
          ∏ v ∈ BranchNodes t,
            (scaleN Nm v : ℝ) ^
              ((-4 : ℤ) *
                (((childrenOf v).card : ℤ) - 1)) := by
      exact Finset.prod_nonneg fun v _ =>
        (zpow_pos
          (by exact_mod_cast scaleN_pos Nm v) _).le
    have hrootScale :
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
    positivity
  rw [inductiveRHSSummand_empty_eq_permSumScaleTail
    (mergedWordList w).length ht hroot Nm
      (mergedMultiplicities hroot mu w hvalid hprimitive) W]
  unfold mergeLedgerRatio permSumSummand
  calc
    (∏ l : HeppLeaf t,
          ((leafMultiplicity mu l).factorial : ℝ) /
            ((leafMultiplicity
              (mergedMultiplicities
                hroot mu w hvalid hprimitive) l).factorial : ℝ)) *
        (sqrtFactorial
            ((mergedWordList w).length - 2 * W.card) *
          (∏ l : HeppLeaf t,
            sqrtFactorial
              (leafMultiplicity
                (mergedMultiplicities
                  hroot mu w hvalid hprimitive) l)) *
          permSumScaleTail Nm W) =
        (sqrtFactorial
            ((mergedWordList w).length - 2 * W.card) *
          (∏ l : HeppLeaf t,
            sqrtFactorial
              (leafMultiplicity
                (mergedMultiplicities
                  hroot mu w hvalid hprimitive) l)) *
          (∏ l : HeppLeaf t,
            ((leafMultiplicity mu l).factorial : ℝ) /
              ((leafMultiplicity
                (mergedMultiplicities
                  hroot mu w hvalid hprimitive) l).factorial : ℝ))) *
          permSumScaleTail Nm W := by ring
    _ ≤
        ((4 : ℝ) ^ n *
          ((n - W.card).factorial : ℝ) *
          ∏ l : HeppLeaf t,
            sqrtFactorial (leafMultiplicity mu l)) *
          permSumScaleTail Nm W :=
      mul_le_mul_of_nonneg_right hfactorial htail
    _ =
        (4 : ℝ) ^ n *
          (((n - W.card).factorial : ℝ) *
            (∏ l : HeppLeaf t,
              sqrtFactorial (leafMultiplicity mu l)) *
            permSumScaleTail Nm W) := by ring

/-- The full compressed P-5.9 right-hand side, restored to the original
factorial normalization, is bounded by the P-5.7 target sum with the
explicit `(5.37)` loss. -/
theorem mergeLedgerRatio_mul_inductiveRHS_le
    {C0 D : ℝ} {t : PlaneTree} {M n : ℕ}
    (hC0 : 0 ≤ C0) (hD : 0 ≤ D)
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t)
    (mu : Multiplicities t)
    (w : Fin M → HeppLeaf t)
    (hvalid : w ∈ validWords (leafMultiplicity mu))
    (hprimitive : NoProperLeafBlock w)
    (htotal : totalMultiplicity mu = 2 * n) :
    mergeLedgerRatio
          (leafMultiplicity mu)
          (leafMultiplicity
            (mergedMultiplicities
              hroot mu w hvalid hprimitive)) *
        inductiveRHS C0 D (mergedWordList w).length
          t Nm
          (mergedMultiplicities
            hroot mu w hvalid hprimitive) ∅ ≤
      C0 ^ (mergedWordList w).length *
        D ^ (BranchNodes t).card *
        (4 : ℝ) ^ n *
        ∑ W ∈ (nonrootBranches t).powerset,
          permSumSummand n Nm mu W := by
  rw [inductiveRHS_eq_factored]
  calc
    mergeLedgerRatio
          (leafMultiplicity mu)
          (leafMultiplicity
            (mergedMultiplicities
              hroot mu w hvalid hprimitive)) *
        (C0 ^ (mergedWordList w).length *
          D ^ (BranchNodes t).card *
          ∑ W ∈ (nonrootBranches t).powerset,
            inductiveRHSSummand
              (mergedWordList w).length t Nm
              (mergedMultiplicities
                hroot mu w hvalid hprimitive) ∅ W) =
        C0 ^ (mergedWordList w).length *
          D ^ (BranchNodes t).card *
          ∑ W ∈ (nonrootBranches t).powerset,
            (mergeLedgerRatio
              (leafMultiplicity mu)
              (leafMultiplicity
                (mergedMultiplicities
                  hroot mu w hvalid hprimitive)) *
              inductiveRHSSummand
                (mergedWordList w).length t Nm
                (mergedMultiplicities
                  hroot mu w hvalid hprimitive) ∅ W) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤
        C0 ^ (mergedWordList w).length *
          D ^ (BranchNodes t).card *
          ∑ W ∈ (nonrootBranches t).powerset,
            ((4 : ℝ) ^ n *
              permSumSummand n Nm mu W) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun W hW =>
          mergeLedgerRatio_mul_inductiveRHSSummand_le
            ht hroot Nm mu w hvalid hprimitive htotal W
            (Finset.mem_powerset.mp hW)
      · exact mul_nonneg
          (pow_nonneg hC0 _)
          (pow_nonneg hD _)
    _ =
        C0 ^ (mergedWordList w).length *
          D ^ (BranchNodes t).card *
          (4 : ℝ) ^ n *
          ∑ W ∈ (nonrootBranches t).powerset,
            permSumSummand n Nm mu W := by
      rw [← Finset.mul_sum]
      ring

end

end Anderson4D
