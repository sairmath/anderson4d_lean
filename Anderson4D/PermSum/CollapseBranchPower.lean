import Anderson4D.PermSum.CollapseGammaRestriction
import Anderson4D.PermSum.CollapseGamma
import Anderson4D.PermSum.CollapseBranchLedger
import Anderson4D.PermSum.SingleScalePowerReverse

/-!
# Exact branch-power ledger under subtree collapse

This module packages the `γ²` contribution to paper (5.45).  Restriction
contributes exactly the original branches below the collapse root, while
contraction contributes exactly the retained branches and one additional
`-2s` power at the original parent of the collapse root.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

set_option warningAsError true
set_option autoImplicit false

noncomputable section

/-! ## Original branch factors and their partition -/

/-- The individual `γ²` factor occurring in `singleScaleBranchPower`. -/
def gamma2BranchFactor {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (v : VPos t) : ℝ :=
  (scaleN Nm v : ℝ) ^
    ((-2 : ℤ) * ((gamma2 mu compound v : ℤ) - 1))

/-- Original branch power over the branches weakly below `r`. -/
def insideGamma2BranchPower {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (r : VPos t) : ℝ :=
  ∏ v : DescendantBranches r,
    gamma2BranchFactor Nm mu compound v.1.1

/-- Original branch power over the branches retained by contraction at `r`. -/
def retainedGamma2BranchPower {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (r : VPos t) : ℝ :=
  ∏ v : BranchesOutside t r.1,
    gamma2BranchFactor Nm mu compound v.1.1

/-- Original branches split into those weakly below `r` and those retained
by contraction. -/
def branchInsideOutsideEquiv {t : PlaneTree} (r : VPos t) :
    {v : VPos t // v ∈ BranchNodes t} ≃
      DescendantBranches r ⊕ BranchesOutside t r.1 where
  toFun v :=
    if h : r.1 <+: v.1.1 then
      Sum.inl ⟨⟨v.1, h⟩, v.2⟩
    else
      Sum.inr ⟨v, h⟩
  invFun
    | Sum.inl v => ⟨v.1.1, v.2⟩
    | Sum.inr v => v.1
  left_inv v := by
    by_cases h : r.1 <+: v.1.1 <;> simp [h]
  right_inv v := by
    cases v with
    | inl v => simp [v.1.2]
    | inr v => simp [v.2]

/-- Exact partition of the original `γ²` branch power. -/
theorem singleScaleBranchPower_eq_inside_mul_retained
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (r : VPos t) :
    singleScaleBranchPower Nm mu compound =
      insideGamma2BranchPower Nm mu compound r *
        retainedGamma2BranchPower Nm mu compound r := by
  let e := branchInsideOutsideEquiv r
  let f : DescendantBranches r ⊕ BranchesOutside t r.1 → ℝ :=
    Sum.elim
      (fun v : DescendantBranches r =>
        gamma2BranchFactor Nm mu compound v.1.1)
      (fun v : BranchesOutside t r.1 =>
        gamma2BranchFactor Nm mu compound v.1.1)
  calc
    singleScaleBranchPower Nm mu compound =
        ∏ v : {v : VPos t // v ∈ BranchNodes t},
          gamma2BranchFactor Nm mu compound v.1 := by
      unfold singleScaleBranchPower gamma2BranchFactor
      exact
        (Finset.prod_coe_sort
          (BranchNodes t)
          (fun v : VPos t =>
            (scaleN Nm v : ℝ) ^
              ((-2 : ℤ) * ((gamma2 mu compound v : ℤ) - 1)))).symm
    _ = ∏ v : {v : VPos t // v ∈ BranchNodes t}, f (e v) := by
      apply Fintype.prod_congr
      intro v
      by_cases h : r.1 <+: v.1.1
      · simp [e, f, branchInsideOutsideEquiv, h]
      · simp [e, f, branchInsideOutsideEquiv, h]
    _ = ∏ v : DescendantBranches r ⊕ BranchesOutside t r.1, f v :=
      Equiv.prod_comp e f
    _ = insideGamma2BranchPower Nm mu compound r *
        retainedGamma2BranchPower Nm mu compound r := by
      rw [Fintype.prod_sum_type]
      rfl

/-! ## Restricted branch power -/

/-- Restriction contributes exactly the original branch factors below `r`. -/
theorem singleScaleBranchPower_restrict
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (r : VPos t) :
    singleScaleBranchPower (restrictMarking Nm r)
        (restrictMultiplicities mu r) (restrictCompound r compound) =
      insideGamma2BranchPower Nm mu compound r := by
  calc
    singleScaleBranchPower (restrictMarking Nm r)
          (restrictMultiplicities mu r) (restrictCompound r compound) =
        ∏ v :
            {v : VPos (subtreeAt t r.1) //
              v ∈ BranchNodes (subtreeAt t r.1)},
          gamma2BranchFactor (restrictMarking Nm r)
            (restrictMultiplicities mu r) (restrictCompound r compound)
            v.1 := by
      unfold singleScaleBranchPower gamma2BranchFactor
      exact
        (Finset.prod_coe_sort
          (BranchNodes (subtreeAt t r.1))
          (fun v : VPos (subtreeAt t r.1) =>
            (scaleN (restrictMarking Nm r) v : ℝ) ^
              ((-2 : ℤ) *
                ((gamma2 (restrictMultiplicities mu r)
                  (restrictCompound r compound) v : ℤ) - 1)))).symm
    _ = ∏ v :
          {v : VPos (subtreeAt t r.1) //
            v ∈ BranchNodes (subtreeAt t r.1)},
          gamma2BranchFactor Nm mu compound (subtreeVertex r v.1) := by
      apply Fintype.prod_congr
      intro v
      unfold gamma2BranchFactor
      rw [scaleN_restrictMarking, gamma2_restrictMultiplicities]
    _ = insideGamma2BranchPower Nm mu compound r := by
      exact
        Equiv.prod_comp (subtreeBranchEquiv r)
          (fun v : DescendantBranches r =>
            gamma2BranchFactor Nm mu compound v.1.1)

/-! ## Contracted branch power -/

/-- Pointwise `γ²` ledger at every contracted branch. -/
theorem gamma2_contract_branch_formula {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (hr0 : r ≠ rootV t) (hrBranch : r ∈ BranchNodes t)
    (compound : Finset (VPos t)) (s : ℕ) (hs : 1 ≤ s)
    (v : VPos (contractAt t r.1))
    (hvBranch : v ∈ BranchNodes (contractAt t r.1)) :
    gamma2 (contractMultiplicities mu r s hs)
        (contractCompound r compound) v =
      gamma2 mu compound (contractVertex r.2 v) +
        if contractVertex r.2 v = parentV r then s else 0 := by
  have hvNotPrefix :
      ¬r.1 <+: v.1 :=
    not_prefix_of_mem_BranchNodes_contractAt r.2 v hvBranch
  have hvNe : v.1 ≠ r.1 := by
    intro h
    apply hvNotPrefix
    rw [h]
  by_cases hparent : contractVertex r.2 v = parentV r
  · have hvEq : v = contractParentVertex r hr0 := by
      apply Subtype.ext
      have hval := congrArg (fun u : VPos t => u.1) hparent
      exact hval
    subst v
    simp [gamma2_contract_parent
      mu r hr0 hrBranch compound s hs]
  · rw [gamma2_contract_of_ne_parent
      mu r v hvNe hparent compound s hs]
    simp [hparent]

/-- The contracted pointwise factor is the retained original factor, with
an additional `-2s` parent-scale power exactly at `parent(r)`. -/
theorem gamma2BranchFactor_contract {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (r : VPos t)
    (hr0 : r ≠ rootV t) (hrBranch : r ∈ BranchNodes t)
    (s : ℕ) (hs : 1 ≤ s)
    (v : VPos (contractAt t r.1))
    (hvBranch : v ∈ BranchNodes (contractAt t r.1)) :
    gamma2BranchFactor (contractMarking Nm r)
        (contractMultiplicities mu r s hs)
        (contractCompound r compound) v =
      gamma2BranchFactor Nm mu compound (contractVertex r.2 v) *
        if contractVertex r.2 v = parentV r then
          (scaleN Nm (parentV r) : ℝ) ^
            ((-2 : ℤ) * (s : ℤ))
        else 1 := by
  unfold gamma2BranchFactor
  rw [scaleN_contractMarking,
    gamma2_contract_branch_formula
      mu r hr0 hrBranch compound s hs v hvBranch]
  by_cases hparent : contractVertex r.2 v = parentV r
  · rw [if_pos hparent, if_pos hparent, hparent]
    push_cast
    rw [show
      (-2 : ℤ) *
          ((gamma2 mu compound (parentV r) : ℤ) + (s : ℤ) - 1) =
        (-2 : ℤ) *
            ((gamma2 mu compound (parentV r) : ℤ) - 1) +
          (-2 : ℤ) * (s : ℤ) by ring]
    have hscale :
        (scaleN Nm (parentV r) : ℝ) ≠ 0 := by
      exact_mod_cast (scaleN_pos Nm (parentV r)).ne'
    rw [zpow_add₀ hscale]
  · rw [if_neg hparent, if_neg hparent]
    simp

/-- The parent of a non-root branch is retained by contraction. -/
def collapseParentOutsideBranch {t : PlaneTree}
    (ht : t.isValid = true) (r : VPos t)
    (hr0 : r ≠ rootV t) (hrBranch : r ∈ BranchNodes t) :
    BranchesOutside t r.1 :=
  ⟨⟨parentV r, parentV_mem_BranchNodes_of_branch ht hrBranch hr0⟩, by
    intro hprefix
    have hle := hprefix.length_le
    change r.1.length ≤ r.1.dropLast.length at hle
    rw [List.length_dropLast] at hle
    have hpos : 0 < r.1.length :=
      List.length_pos_iff.mpr (ne_root_iff.mp hr0)
    omega⟩

/-- The extra parent factor is a one-point product over retained branches. -/
theorem prod_parentScaleBonus {t : PlaneTree}
    (ht : t.isValid = true) (Nm : HeppMarking t)
    (r : VPos t) (hr0 : r ≠ rootV t)
    (hrBranch : r ∈ BranchNodes t) (s : ℕ) :
    (∏ v : BranchesOutside t r.1,
        if v.1.1 = parentV r then
          (scaleN Nm (parentV r) : ℝ) ^
            ((-2 : ℤ) * (s : ℤ))
        else 1) =
      (scaleN Nm (parentV r) : ℝ) ^
        ((-2 : ℤ) * (s : ℤ)) := by
  let p := collapseParentOutsideBranch ht r hr0 hrBranch
  let q : ℝ :=
    (scaleN Nm (parentV r) : ℝ) ^
      ((-2 : ℤ) * (s : ℤ))
  calc
    (∏ v : BranchesOutside t r.1,
        if v.1.1 = parentV r then
          (scaleN Nm (parentV r) : ℝ) ^
            ((-2 : ℤ) * (s : ℤ))
        else 1) =
        ∏ v : BranchesOutside t r.1,
          if p = v then q else 1 := by
      apply Fintype.prod_congr
      intro v
      have hv : v.1.1 = parentV r ↔ v = p := by
        constructor
        · intro h
          apply Subtype.ext
          apply Subtype.ext
          exact h
        · intro h
          rw [h]
          rfl
      simp [hv, q, eq_comm]
    _ = q := Fintype.prod_ite_eq p (fun _ => q)
    _ = (scaleN Nm (parentV r) : ℝ) ^
        ((-2 : ℤ) * (s : ℤ)) := rfl

/-- Contraction contributes the retained original branch power and precisely
one extra `-2s` power at the parent of `r`. -/
theorem singleScaleBranchPower_contract
    {t : PlaneTree} (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (r : VPos t)
    (hr0 : r ≠ rootV t) (hrBranch : r ∈ BranchNodes t)
    (s : ℕ) (hs : 1 ≤ s) :
    singleScaleBranchPower (contractMarking Nm r)
        (contractMultiplicities mu r s hs) (contractCompound r compound) =
      retainedGamma2BranchPower Nm mu compound r *
        (scaleN Nm (parentV r) : ℝ) ^
          ((-2 : ℤ) * (s : ℤ)) := by
  let e := contractBranchEquiv r.2
  let f : BranchesOutside t r.1 → ℝ := fun v =>
    gamma2BranchFactor Nm mu compound v.1.1 *
      if v.1.1 = parentV r then
        (scaleN Nm (parentV r) : ℝ) ^
          ((-2 : ℤ) * (s : ℤ))
      else 1
  calc
    singleScaleBranchPower (contractMarking Nm r)
          (contractMultiplicities mu r s hs)
          (contractCompound r compound) =
        ∏ v :
            {v : VPos (contractAt t r.1) //
              v ∈ BranchNodes (contractAt t r.1)},
          gamma2BranchFactor (contractMarking Nm r)
            (contractMultiplicities mu r s hs)
            (contractCompound r compound) v.1 := by
      unfold singleScaleBranchPower gamma2BranchFactor
      exact
        (Finset.prod_coe_sort
          (BranchNodes (contractAt t r.1))
          (fun v : VPos (contractAt t r.1) =>
            (scaleN (contractMarking Nm r) v : ℝ) ^
              ((-2 : ℤ) *
                ((gamma2 (contractMultiplicities mu r s hs)
                  (contractCompound r compound) v : ℤ) - 1)))).symm
    _ = ∏ v :
          {v : VPos (contractAt t r.1) //
            v ∈ BranchNodes (contractAt t r.1)},
          f (e v) := by
      apply Fintype.prod_congr
      intro v
      exact gamma2BranchFactor_contract
        Nm mu compound r hr0 hrBranch s hs v.1 v.2
    _ = ∏ v : BranchesOutside t r.1, f v :=
      Equiv.prod_comp e f
    _ = retainedGamma2BranchPower Nm mu compound r *
        (∏ v : BranchesOutside t r.1,
          if v.1.1 = parentV r then
            (scaleN Nm (parentV r) : ℝ) ^
              ((-2 : ℤ) * (s : ℤ))
          else 1) := by
      unfold f retainedGamma2BranchPower
      rw [Finset.prod_mul_distrib]
    _ = retainedGamma2BranchPower Nm mu compound r *
        (scaleN Nm (parentV r) : ℝ) ^
          ((-2 : ℤ) * (s : ℤ)) := by
      rw [prod_parentScaleBonus ht Nm r hr0 hrBranch s]

/-! ## Complete `(5.45)` branch-power identity -/

/-- Exact `γ²` branch-power ledger used in the collapse induction. -/
theorem singleScaleBranchPower_restrict_mul_contract
    {t : PlaneTree} (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (r : VPos t)
    (hr0 : r ≠ rootV t) (hrBranch : r ∈ BranchNodes t)
    (s : ℕ) (hs : 1 ≤ s) :
    singleScaleBranchPower (restrictMarking Nm r)
          (restrictMultiplicities mu r) (restrictCompound r compound) *
        singleScaleBranchPower (contractMarking Nm r)
          (contractMultiplicities mu r s hs)
          (contractCompound r compound) =
      singleScaleBranchPower Nm mu compound *
        (scaleN Nm (parentV r) : ℝ) ^
          ((-2 : ℤ) * (s : ℤ)) := by
  rw [singleScaleBranchPower_restrict,
    singleScaleBranchPower_contract
      ht Nm mu compound r hr0 hrBranch s hs,
    singleScaleBranchPower_eq_inside_mul_retained]
  ring

end

end Anderson4D
