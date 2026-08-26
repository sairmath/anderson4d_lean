import Anderson4D.PermSum.CollapseMassLedger
import Anderson4D.PermSum.CollapseScalar
import Anderson4D.PermSum.CollapseWRegroup

/-!
# Fixed-datum scalar and skipped-set assembly

For one raw collapse datum, this file combines the exact factor audit, the
final scalar inequality, and the injective `W ↦ W'` regrouping.  The result
has exactly the global coefficient and `W'`-sum of the original-tree
induction right-hand side.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- Every named summand of the factored induction right-hand side is
nonnegative. -/
theorem inductiveRHSSummand_nonneg
    (m : ℕ) (t : PlaneTree) (Nm : HeppMarking t)
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (W : Finset (VPos t)) :
    0 ≤ inductiveRHSSummand m t Nm mu compound W := by
  have hsqrt : 0 ≤ sqrtFactorial (m - 2 * W.card) := by
    unfold sqrtFactorial
    positivity
  have hleaf := paperLeafProduct_nonneg mu compound
  have hbranch := singleScaleBranchPower_nonneg Nm mu compound
  have hratio := originalParentRatioFactor_nonneg Nm W
  unfold inductiveRHSSummand
  positivity

/-- Final fixed-datum scalar and `W`-sum bound. -/
theorem two_pow_mul_sum_combinedCollapseTerm_le_inductiveRHSSum
    (C0 D : ℝ) (hC0 : 1000 < C0)
    (hD : D = Real.exp (C0 ^ (10 : ℕ)))
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t))
    (r : VPos t) (hr : r ∈ nonrootBranches t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hSpec : CollapseMultiplicitySpec
      (splitLeafMultiplicity mu r) d)
    (hblocks : 2 ≤ d.blocks.length) :
    (2 : ℝ) ^ d.insideLength *
        (∑ W ∈
            (nonrootBranches (contractAt t r.1)).powerset,
          combinedCollapseTerm C0 D d.insideLength
            (collapseCutCount d) d.collapsed.length
            Nm mu compound r
            (one_le_collapseCutCount d hblocks) W) ≤
      C0 ^ (totalMultiplicity mu) *
        D ^ (BranchNodes t).card *
        ∑ W' ∈ (nonrootBranches t).powerset,
          inductiveRHSSummand (totalMultiplicity mu)
            t Nm mu compound W' := by
  let n := d.insideLength
  let s := collapseCutCount d
  let hs : 1 ≤ s := one_le_collapseCutCount d hblocks
  let mOutside := outsideMultiplicityTotal mu r
  have hnMass :
      n = totalMultiplicity (restrictMultiplicities mu r) := by
    exact
      (totalMultiplicity_restrict_eq_insideLength
        mu r d hSpec).symm
  have hn : 4 ≤ n := by
    rw [hnMass]
    exact four_le_totalMultiplicity_restrict mu r
      (Finset.mem_erase.mp hr).2
  have hsAddOne :
      s + 1 = d.blocks.length := by
    exact collapseCutCount_add_one d hblocks
  have hsn : s + 1 ≤ n := by
    calc
      s + 1 = d.blocks.length := hsAddOne
      _ = d.blockComposition.length :=
        d.blockComposition_length.symm
      _ ≤ d.insideLength := d.blockComposition.length_le
      _ = n := rfl
  have htotal :
      totalMultiplicity mu = n + mOutside := by
    calc
      totalMultiplicity mu =
          totalMultiplicity (restrictMultiplicities mu r) +
            outsideMultiplicityTotal mu r :=
        totalMultiplicity_eq_restrict_add_outside mu r
      _ = n + mOutside := by
        rw [← hnMass]
  have hcollapsed :
      d.collapsed.length = mOutside + s + 1 := by
    have hcontractLength :=
      totalMultiplicity_contract_eq_collapsedLength
        mu r d hSpec hblocks
    have hcontractMass :=
      totalMultiplicity_contractMultiplicities mu r s hs
    calc
      d.collapsed.length =
          totalMultiplicity
            (contractMultiplicities mu r s hs) :=
        hcontractLength.symm
      _ = (s + 1) + outsideMultiplicityTotal mu r :=
        hcontractMass
      _ = mOutside + s + 1 := by
        omega
  have hterm :
      ∀ W ∈ (nonrootBranches (contractAt t r.1)).powerset,
        (2 : ℝ) ^ n *
            combinedCollapseTerm C0 D n s d.collapsed.length
              Nm mu compound r hs W ≤
          C0 ^ (n + mOutside) * D ^ (BranchNodes t).card *
            inductiveRHSSummand (n + mOutside)
              t Nm mu compound (liftWPrime r s W) := by
    intro W hW
    have hWsub :
        W ⊆ nonrootBranches (contractAt t r.1) :=
      Finset.mem_powerset.mp hW
    have hWcard :
        2 * W.card ≤ mOutside := by
      exact two_mul_card_contractW_le_outsideMultiplicityTotal
        ht hroot mu r hr s hs W hWsub
    calc
      (2 : ℝ) ^ n *
            combinedCollapseTerm C0 D n s d.collapsed.length
              Nm mu compound r hs W =
          (2 : ℝ) ^ n *
            combinedCollapseFactored C0 D n s d.collapsed.length
              Nm mu compound r W := by
        rw [combinedCollapseTerm_eq_factored
          C0 D n s d.collapsed.length ht Nm mu compound
          r hr hs W hWsub]
      _ =
          (2 : ℝ) ^ n *
            combinedCollapseFactored C0 D n s
              (mOutside + s + 1) Nm mu compound r W := by
        rw [hcollapsed]
      _ ≤
          C0 ^ (n + mOutside) * D ^ (BranchNodes t).card *
            inductiveRHSSummand (n + mOutside)
              t Nm mu compound (liftWPrime r s W) :=
        two_pow_mul_combinedCollapseFactored_le_inductiveRHSSummand
          C0 D hC0 hD n mOutside s hn hs hsn ht
          Nm mu compound r hr W hWsub hWcard
  have htargetNonneg :
      ∀ W' ∈ (nonrootBranches t).powerset,
        0 ≤
          C0 ^ (n + mOutside) * D ^ (BranchNodes t).card *
            inductiveRHSSummand (n + mOutside)
              t Nm mu compound W' := by
    intro W' _
    have hDpos : 0 < D := by
      rw [hD]
      positivity
    exact mul_nonneg
      (mul_nonneg (by positivity) (by positivity))
      (inductiveRHSSummand_nonneg
        (n + mOutside) t Nm mu compound W')
  have hregroup :=
    sum_contracted_powerset_le_sum_original_powerset
      r hr s
      (fun W =>
        (2 : ℝ) ^ n *
          combinedCollapseTerm C0 D n s d.collapsed.length
            Nm mu compound r hs W)
      (fun W' =>
        C0 ^ (n + mOutside) * D ^ (BranchNodes t).card *
          inductiveRHSSummand (n + mOutside)
            t Nm mu compound W')
      hterm htargetNonneg
  rw [htotal]
  calc
    (2 : ℝ) ^ d.insideLength *
          (∑ W ∈
              (nonrootBranches (contractAt t r.1)).powerset,
            combinedCollapseTerm C0 D d.insideLength
              (collapseCutCount d) d.collapsed.length
              Nm mu compound r
              (one_le_collapseCutCount d hblocks) W) =
        ∑ W ∈
            (nonrootBranches (contractAt t r.1)).powerset,
          (2 : ℝ) ^ n *
            combinedCollapseTerm C0 D n s d.collapsed.length
              Nm mu compound r hs W := by
      rw [Finset.mul_sum]
    _ ≤
        ∑ W' ∈ (nonrootBranches t).powerset,
          C0 ^ (n + mOutside) * D ^ (BranchNodes t).card *
            inductiveRHSSummand (n + mOutside)
              t Nm mu compound W' :=
      hregroup
    _ =
        C0 ^ (n + mOutside) * D ^ (BranchNodes t).card *
          ∑ W' ∈ (nonrootBranches t).powerset,
            inductiveRHSSummand (n + mOutside)
              t Nm mu compound W' := by
      rw [Finset.mul_sum]

end
end Anderson4D
