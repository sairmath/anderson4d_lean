import Anderson4D.PermSum.CollapseBranchPower
import Anderson4D.PermSum.CollapseLeafLedger
import Anderson4D.PermSum.CollapseRatioLedger

/-!
# Factored right-hand sides for the Proposition 5.9 collapse

The frozen statements intentionally display all paper factors.  This module
rewrites them into the named leaf, branch-power, and parent-ratio ledgers used
by the collapse audit.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## The P-5.9 summand -/

/-- One `W`-summand of the factored right side of Proposition 5.9, without
the global `C0^m D^|B|` coefficient. -/
def inductiveRHSSummand
    (m : ℕ) (t : PlaneTree) (Nm : HeppMarking t)
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (W : Finset (VPos t)) : ℝ :=
  sqrtFactorial (m - 2 * W.card) *
    paperLeafProduct mu compound *
    singleScaleBranchPower Nm mu compound *
    originalParentRatioFactor Nm W

/-- The frozen P-5.9 right side is the sum of the named factored summands. -/
theorem inductiveRHS_eq_factored
    (C0 D : ℝ) (m : ℕ) (t : PlaneTree)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) :
    inductiveRHS C0 D m t Nm mu compound =
      C0 ^ m * D ^ (BranchNodes t).card *
        ∑ W ∈ (nonrootBranches t).powerset,
          inductiveRHSSummand m t Nm mu compound W := by
  unfold inductiveRHS inductiveRHSSummand
  rw [paperLeafProduct_eq_simple_mul_compound]
  apply congrArg
  apply Finset.sum_congr rfl
  intro W _
  unfold singleScaleBranchPower originalParentRatioFactor
  ring

/-- One full contracted-tree induction term, including its global powers. -/
def contractedInductiveTerm
    (C0 D : ℝ) (m : ℕ) (t : PlaneTree)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (W : Finset (VPos t)) : ℝ :=
  C0 ^ m * D ^ (BranchNodes t).card *
    inductiveRHSSummand m t Nm mu compound W

/-- Distribute the global P-5.9 coefficient into the finite `W`-sum. -/
theorem inductiveRHS_eq_sum_contractedInductiveTerm
    (C0 D : ℝ) (m : ℕ) (t : PlaneTree)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) :
    inductiveRHS C0 D m t Nm mu compound =
      ∑ W ∈ (nonrootBranches t).powerset,
        contractedInductiveTerm C0 D m t Nm mu compound W := by
  rw [inductiveRHS_eq_factored]
  unfold contractedInductiveTerm
  rw [Finset.mul_sum]

/-! ## The restricted P-5.10 right side -/

/-- P-5.10 on the selected subtree, written with the named leaf and branch
factors and with its root-ratio contribution joined to the subtree cube
product. -/
def restrictedSingleScaleTerm
    (C0 : ℝ) (m s : ℕ)
    {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (r : VPos t) : ℝ :=
  C0 ^ ((m : ℝ) / 2) *
    sqrtFactorial (m - s) *
    paperLeafProduct (restrictMultiplicities mu r)
      (restrictCompound r compound) *
    singleScaleBranchPower (restrictMarking Nm r)
      (restrictMultiplicities mu r) (restrictCompound r compound) *
    (scaleN Nm (parentV r) : ℝ) ^ (2 * s) *
    restrictionParentRatioFactor Nm r s

/-- Exact specialized rewrite of the P-5.10 right side used in the collapse
induction. -/
theorem singleScaleRHS_restrict_eq
    (C0 : ℝ) (m s : ℕ)
    {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (r : VPos t) :
    singleScaleRHS C0 m s
        (scaleN Nm (parentV r))
        (subtreeAt t r.1)
        (restrictMarking Nm r)
        (restrictMultiplicities mu r)
        (restrictCompound r compound) =
      restrictedSingleScaleTerm C0 m s Nm mu compound r := by
  unfold singleScaleRHS restrictedSingleScaleTerm
    restrictionParentRatioFactor singleScaleBranchPower
  rw [paperLeafProduct_eq_simple_mul_compound,
    scaleN_restrictMarking_root]
  unfold parentScaleRatio
  ring

/-! ## The contracted P-5.9 term -/

/-- A contracted-tree induction term rewritten back to the original marking
for its parent-ratio factor. -/
def contractedCollapseTerm
    (C0 D : ℝ) (m : ℕ)
    {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (r : VPos t) (s : ℕ) (hs : 1 ≤ s)
    (W : Finset (VPos (contractAt t r.1))) : ℝ :=
  C0 ^ m * D ^ (BranchNodes (contractAt t r.1)).card *
    sqrtFactorial (m - 2 * W.card) *
    paperLeafProduct (contractMultiplicities mu r s hs)
      (contractCompound r compound) *
    singleScaleBranchPower (contractMarking Nm r)
      (contractMultiplicities mu r s hs)
      (contractCompound r compound) *
    contractionParentRatioFactor Nm r W

/-- Exact rewrite of one contracted induction summand. -/
theorem contractedInductiveTerm_eq_collapseTerm
    (C0 D : ℝ) (m : ℕ)
    {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (r : VPos t) (s : ℕ) (hs : 1 ≤ s)
    (W : Finset (VPos (contractAt t r.1))) :
    contractedInductiveTerm C0 D m
        (contractAt t r.1)
        (contractMarking Nm r)
        (contractMultiplicities mu r s hs)
        (contractCompound r compound) W =
      contractedCollapseTerm C0 D m Nm mu compound r s hs W := by
  unfold contractedInductiveTerm inductiveRHSSummand
    contractedCollapseTerm contractionParentRatioFactor
    originalParentRatioFactor
  ring

/-! ## Exact product audit -/

/-- The `R^(2s)` from P-5.10 cancels the `R^(-2s)` created by the
contracted `γ²` ledger. -/
theorem natScale_pow_cancel (R s : ℕ) (hR : 0 < R) :
    (R : ℝ) ^ (2 * s) *
        (R : ℝ) ^ ((-2 : ℤ) * (s : ℤ)) =
      1 := by
  have hR0 : (R : ℝ) ≠ 0 := by
    exact_mod_cast hR.ne'
  rw [← zpow_natCast, ← zpow_add₀ hR0]
  convert zpow_zero (R : ℝ) using 2
  push_cast
  ring

/-- The product appearing after the geometric pointwise estimate and the two
analytic calls, before the remaining scalar inequalities. -/
def combinedCollapseTerm
    (C0 D : ℝ) (n s m : ℕ)
    {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (r : VPos t) (hs : 1 ≤ s)
    (W : Finset (VPos (contractAt t r.1))) : ℝ :=
  (4 : ℝ) ^ n * ((s + 1).factorial : ℝ)⁻¹ *
    restrictedSingleScaleTerm C0 n s Nm mu compound r *
    contractedCollapseTerm C0 D m Nm mu compound r s hs W

/-- The same product after all exact tree ledgers and scale cancellation. -/
def combinedCollapseFactored
    (C0 D : ℝ) (n s m : ℕ)
    {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (r : VPos t)
    (W : Finset (VPos (contractAt t r.1))) : ℝ :=
  (4 : ℝ) ^ n *
    C0 ^ ((n : ℝ) / 2) *
    C0 ^ m *
    D ^ (BranchNodes (contractAt t r.1)).card *
    ((s + 1).factorial : ℝ)⁻¹ *
    factorialThreeQuarters (s + 1) *
    sqrtFactorial (n - s) *
    sqrtFactorial (m - 2 * W.card) *
    paperLeafProduct mu compound *
    singleScaleBranchPower Nm mu compound *
    originalParentRatioFactor Nm (liftWPrime r s W)

/-- Exact paper (5.45)--(5.46) factor audit before inequalities.

This is where the leaf ledger, `γ²` ledger, parent-ratio ledger, and the
dyadic-scale cancellation meet. -/
theorem combinedCollapseTerm_eq_factored
    (C0 D : ℝ) (n s m : ℕ)
    {t : PlaneTree} (ht : t.isValid = true)
    (Nm : HeppMarking t)
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (r : VPos t) (hr : r ∈ nonrootBranches t)
    (hs : 1 ≤ s)
    (W : Finset (VPos (contractAt t r.1)))
    (hW : W ⊆ nonrootBranches (contractAt t r.1)) :
    combinedCollapseTerm C0 D n s m Nm mu compound r hs W =
      combinedCollapseFactored C0 D n s m Nm mu compound r W := by
  have hrData := Finset.mem_erase.mp hr
  have hleaf :=
    paperLeafProduct_restrict_mul_contract
      mu compound r s hs
  have hbranch :=
    singleScaleBranchPower_restrict_mul_contract
      ht Nm mu compound r hrData.1 hrData.2 s hs
  have hratio :=
    restriction_mul_contraction_parentRatioFactor
      Nm r hr s (Nat.lt_of_lt_of_le Nat.zero_lt_one hs) W hW
  have hcancel :=
    natScale_pow_cancel (scaleN Nm (parentV r)) s
      (scaleN_pos Nm (parentV r))
  unfold combinedCollapseTerm combinedCollapseFactored
    restrictedSingleScaleTerm contractedCollapseTerm
  calc
    _ =
        (4 : ℝ) ^ n *
          C0 ^ ((n : ℝ) / 2) *
          C0 ^ m *
          D ^ (BranchNodes (contractAt t r.1)).card *
          ((s + 1).factorial : ℝ)⁻¹ *
          sqrtFactorial (n - s) *
          sqrtFactorial (m - 2 * W.card) *
          (paperLeafProduct (restrictMultiplicities mu r)
              (restrictCompound r compound) *
            paperLeafProduct (contractMultiplicities mu r s hs)
              (contractCompound r compound)) *
          (singleScaleBranchPower (restrictMarking Nm r)
              (restrictMultiplicities mu r)
              (restrictCompound r compound) *
            singleScaleBranchPower (contractMarking Nm r)
              (contractMultiplicities mu r s hs)
              (contractCompound r compound)) *
          (scaleN Nm (parentV r) : ℝ) ^ (2 * s) *
          (restrictionParentRatioFactor Nm r s *
            contractionParentRatioFactor Nm r W) := by
      ring
    _ =
        (4 : ℝ) ^ n *
          C0 ^ ((n : ℝ) / 2) *
          C0 ^ m *
          D ^ (BranchNodes (contractAt t r.1)).card *
          ((s + 1).factorial : ℝ)⁻¹ *
          sqrtFactorial (n - s) *
          sqrtFactorial (m - 2 * W.card) *
          (paperLeafProduct mu compound *
            factorialThreeQuarters (s + 1)) *
          singleScaleBranchPower Nm mu compound *
          ((scaleN Nm (parentV r) : ℝ) ^ (2 * s) *
            (scaleN Nm (parentV r) : ℝ) ^
              ((-2 : ℤ) * (s : ℤ))) *
          originalParentRatioFactor Nm (liftWPrime r s W) := by
      rw [hleaf, hbranch, hratio]
      ring
    _ =
        (4 : ℝ) ^ n *
          C0 ^ ((n : ℝ) / 2) *
          C0 ^ m *
          D ^ (BranchNodes (contractAt t r.1)).card *
          ((s + 1).factorial : ℝ)⁻¹ *
          sqrtFactorial (n - s) *
          sqrtFactorial (m - 2 * W.card) *
          (paperLeafProduct mu compound *
            factorialThreeQuarters (s + 1)) *
          singleScaleBranchPower Nm mu compound *
          originalParentRatioFactor Nm (liftWPrime r s W) := by
      rw [hcancel]
      ring
    _ = _ := by ring

end

end Anderson4D
