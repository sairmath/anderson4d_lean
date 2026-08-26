import Anderson4D.PermSum.Statements
import Anderson4D.HeppTree.BranchExcess
import Anderson4D.HeppTree.LeafCard

/-!
# Branch count away from a distinguished leaf

The factorial ledger in the collapse step of Proposition 5.9 needs the
off-marker inequality `2 |W| ≤ m`, where `W` is a set of non-root branch
vertices and `m` is the total multiplicity of all leaves except the newly
created marker leaf.

For a valid tree, the branch-excess Euler identity bounds the number of
branch vertices by the number of leaves minus one.  Erasing the root from the
branch set and the marker from the leaf set, together with the lower bound two
on every leaf multiplicity, gives the required estimate.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

/--
Twice the number of non-root branch vertices is bounded by the total
multiplicity away from any distinguished leaf.
-/
theorem two_mul_card_nonrootBranches_le_sum_leafMultiplicity_erase
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t) (mu : Multiplicities t)
    (marker : HeppLeaf t) :
    2 * (nonrootBranches t).card ≤
      ∑ l ∈ (Finset.univ.erase marker), leafMultiplicity mu l := by
  have hnonroot :
      (nonrootBranches t).card + 1 = (BranchNodes t).card := by
    simpa [nonrootBranches] using Finset.card_erase_add_one hroot
  have hbranch :
      (BranchNodes t).card ≤ branchExcess t := by
    rw [← sum_branchNodes_childCount_sub_one_eq_branchExcess,
      Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun v hv => by
      have htwo : 2 ≤ childCount t v.1 := by
        simpa [BranchNodes] using hv
      omega
  have hexcess : branchExcess t + 1 = t.leafCount :=
    branchExcess_add_one_eq_leafCount t ht
  have hleafErase :
      ((Finset.univ : Finset (HeppLeaf t)).erase marker).card + 1 =
        t.leafCount := by
    rw [Finset.card_erase_add_one (Finset.mem_univ marker),
      Finset.card_univ, Fintype.card_coe, card_Leaves_eq_leafCount]
  have hcard :
      (nonrootBranches t).card ≤
        ((Finset.univ : Finset (HeppLeaf t)).erase marker).card := by
    omega
  calc
    2 * (nonrootBranches t).card ≤
        2 * ((Finset.univ : Finset (HeppLeaf t)).erase marker).card :=
      Nat.mul_le_mul_left 2 hcard
    _ = ∑ _l ∈ (Finset.univ.erase marker : Finset (HeppLeaf t)), 2 := by
      simp [Nat.mul_comm]
    _ ≤ ∑ l ∈ (Finset.univ.erase marker), leafMultiplicity mu l := by
      exact Finset.sum_le_sum fun l _ => mu.two_le l.1 l.2

/--
Off-marker branch bound for an arbitrary subset of the non-root branch
vertices.  This is the form used by the factorial estimate (5.47).
-/
theorem two_mul_card_le_sum_leafMultiplicity_erase_of_subset_nonrootBranches
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t) (mu : Multiplicities t)
    (marker : HeppLeaf t) (W : Finset (VPos t))
    (hW : W ⊆ nonrootBranches t) :
    2 * W.card ≤
      ∑ l ∈ (Finset.univ.erase marker), leafMultiplicity mu l := by
  exact le_trans
    (Nat.mul_le_mul_left 2 (Finset.card_le_card hW))
    (two_mul_card_nonrootBranches_le_sum_leafMultiplicity_erase
      ht hroot mu marker)

end Anderson4D
