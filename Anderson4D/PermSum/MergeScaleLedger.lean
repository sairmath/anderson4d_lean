import Anderson4D.HeppTree.Leaves
import Anderson4D.PermSum.CollapseRHS

/-!
# Scale-tail ledger for the P-5.9 to P-5.7 merge

At `compound = ∅`, paper (5.31) identifies the squared parent-ratio part
of the P-5.9 branch power with the branch/root scale power in P-5.7.  The
remaining `W`-complement ratio is unchanged.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- The scale and parent-ratio tail printed in P-5.7, equation (5.15). -/
def permSumScaleTail {t : PlaneTree}
    (Nm : HeppMarking t) (W : Finset (VPos t)) : ℝ :=
  (∏ v ∈ BranchNodes t,
      (scaleN Nm v : ℝ) ^
        ((-4 : ℤ) * (((childrenOf v).card : ℤ) - 1))) *
    (scaleN Nm (rootV t) : ℝ) ^ (-2 : ℤ) *
    ∏ v ∈ nonrootBranches t \ W, parentScaleRatio Nm v

/-- Paper (5.31), specialized to a Hepp marking.  No incidence or parity
hypothesis is needed: validity and the root-branch condition are precisely
the assumptions of the existing combinatorial identity, while positivity of
all branch scales follows from the marking. -/
theorem allSimple_scale_ratio_tail_eq_permSumScaleTail
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (W : Finset (VPos t)) :
    singleScaleBranchPower Nm mu ∅ *
        originalParentRatioFactor Nm W =
      permSumScaleTail Nm W := by
  have hscale :
      ∀ v ∈ BranchNodes t, 0 < (scaleN Nm v : ℝ) := by
    intro v _
    exact_mod_cast scaleN_pos Nm v
  have h531 :=
    allSimple_direct_product_identity ht hroot mu
      (fun v => (scaleN Nm v : ℝ)) hscale
  have hbranch :
      (∏ v ∈ BranchNodes t,
          (scaleN Nm v : ℝ) ^
            ((-2 : ℤ) * ((gamma2 mu ∅ v : ℤ) - 1))) =
        singleScaleBranchPower Nm mu ∅ := by
    rfl
  have hratio :
      (∏ v ∈ (BranchNodes t).erase (rootV t),
          ((scaleN Nm v : ℝ) /
            (scaleN Nm (parentV v) : ℝ)) ^ (2 : ℤ)) =
        ∏ v ∈ nonrootBranches t,
          (parentScaleRatio Nm v) ^ 2 := by
    unfold nonrootBranches parentScaleRatio
    apply Finset.prod_congr rfl
    intro v _
    change
      ((scaleN Nm v : ℝ) /
          (scaleN Nm (parentV v) : ℝ)) ^ ((2 : ℕ) : ℤ) =
        ((scaleN Nm v : ℝ) /
          (scaleN Nm (parentV v) : ℝ)) ^ (2 : ℕ)
    rw [zpow_natCast]
  have h531' :
      (∏ v ∈ BranchNodes t,
          (scaleN Nm v : ℝ) ^
            ((-4 : ℤ) * (((childrenOf v).card : ℤ) - 1))) *
          (scaleN Nm (rootV t) : ℝ) ^ (-2 : ℤ) =
        singleScaleBranchPower Nm mu ∅ *
          ∏ v ∈ nonrootBranches t,
            (parentScaleRatio Nm v) ^ 2 := by
    calc
      _ =
          (∏ v ∈ BranchNodes t,
              (scaleN Nm v : ℝ) ^
                ((-2 : ℤ) * ((gamma2 mu ∅ v : ℤ) - 1))) *
            ∏ v ∈ (BranchNodes t).erase (rootV t),
              ((scaleN Nm v : ℝ) /
                (scaleN Nm (parentV v) : ℝ)) ^ (2 : ℤ) :=
        h531
      _ = _ := by rw [hbranch, hratio]
  unfold originalParentRatioFactor permSumScaleTail
  calc
    singleScaleBranchPower Nm mu ∅ *
          ((∏ v ∈ nonrootBranches t,
              parentScaleRatio Nm v ^ 2) *
            ∏ v ∈ nonrootBranches t \ W,
              parentScaleRatio Nm v) =
        (singleScaleBranchPower Nm mu ∅ *
          ∏ v ∈ nonrootBranches t,
            parentScaleRatio Nm v ^ 2) *
          ∏ v ∈ nonrootBranches t \ W,
            parentScaleRatio Nm v := by
      ring
    _ =
        ((∏ v ∈ BranchNodes t,
            (scaleN Nm v : ℝ) ^
              ((-4 : ℤ) * (((childrenOf v).card : ℤ) - 1))) *
          (scaleN Nm (rootV t) : ℝ) ^ (-2 : ℤ)) *
          ∏ v ∈ nonrootBranches t \ W,
            parentScaleRatio Nm v := by
      rw [← h531']

/-- With no compound leaves, the named leaf product is the P-5.7 product of
square-root factorials over all leaves. -/
@[simp]
theorem paperLeafProduct_empty
    {t : PlaneTree} (mu : Multiplicities t) :
    paperLeafProduct mu ∅ =
      ∏ l : HeppLeaf t, sqrtFactorial (leafMultiplicity mu l) := by
  unfold paperLeafProduct paperLeafFactor
  simp

/-- A P-5.9 summand at `compound = ∅` is exactly the factorial/leaf factor
and scale tail appearing in P-5.7. -/
theorem inductiveRHSSummand_empty_eq_permSumScaleTail
    (m : ℕ) {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (W : Finset (VPos t)) :
    inductiveRHSSummand m t Nm mu ∅ W =
      sqrtFactorial (m - 2 * W.card) *
        (∏ l : HeppLeaf t,
          sqrtFactorial (leafMultiplicity mu l)) *
        permSumScaleTail Nm W := by
  unfold inductiveRHSSummand
  rw [paperLeafProduct_empty]
  calc
    sqrtFactorial (m - 2 * W.card) *
          (∏ l : HeppLeaf t,
            sqrtFactorial (leafMultiplicity mu l)) *
          singleScaleBranchPower Nm mu ∅ *
          originalParentRatioFactor Nm W =
        (sqrtFactorial (m - 2 * W.card) *
          (∏ l : HeppLeaf t,
            sqrtFactorial (leafMultiplicity mu l))) *
          (singleScaleBranchPower Nm mu ∅ *
            originalParentRatioFactor Nm W) := by
      ring
    _ =
        (sqrtFactorial (m - 2 * W.card) *
          (∏ l : HeppLeaf t,
            sqrtFactorial (leafMultiplicity mu l))) *
          permSumScaleTail Nm W := by
      rw [allSimple_scale_ratio_tail_eq_permSumScaleTail
        ht hroot Nm mu W]
    _ = _ := by
      ring

end
end Anderson4D
