import Anderson4D.HeppTree.SubtreeCollapse
import Anderson4D.PermSum.Statements

/-!
# Branch-cardinality ledger for subtree contraction

The branch set of the original tree is partitioned exactly into branches
inside the collapsed subtree and branches retained by the contracted tree.
This supplies the strict `D`-power saving in (5.45).
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree

/-- Branch vertices outside the subtree, as an ordinary filtered subtype. -/
def branchesOutsideEquivFilter {t : PlaneTree} (r : VPos t) :
    BranchesOutside t r.1 ≃
      ↥((BranchNodes t).filter fun u => ¬r.1 <+: u.1) where
  toFun v :=
    ⟨v.1.1, Finset.mem_filter.mpr ⟨v.1.2, v.2⟩⟩
  invFun v :=
    ⟨⟨v.1, (Finset.mem_filter.mp v.2).1⟩,
      (Finset.mem_filter.mp v.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Descendant branches, as the subtype of `branchNodesUnder r`. -/
def descendantBranchesEquivBranchNodesUnder {t : PlaneTree} (r : VPos t) :
    DescendantBranches r ≃
      ↥(branchNodesUnder r) where
  toFun v :=
    ⟨v.1.1, Finset.mem_filter.mpr ⟨v.2, v.1.2⟩⟩
  invFun v :=
    ⟨⟨v.1, (Finset.mem_filter.mp v.2).2⟩,
      (Finset.mem_filter.mp v.2).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_branchesOutside_eq_filter {t : PlaneTree} (r : VPos t) :
    Fintype.card (BranchesOutside t r.1) =
      ((BranchNodes t).filter fun u => ¬r.1 <+: u.1).card := by
  calc
    Fintype.card (BranchesOutside t r.1) =
        Fintype.card
          ↥((BranchNodes t).filter fun u => ¬r.1 <+: u.1) :=
      Fintype.card_congr (branchesOutsideEquivFilter r)
    _ = ((BranchNodes t).filter fun u => ¬r.1 <+: u.1).card :=
      Fintype.card_coe _

theorem card_descendantBranches_eq_branchNodesUnder
    {t : PlaneTree} (r : VPos t) :
    Fintype.card (DescendantBranches r) =
      (branchNodesUnder r).card := by
  calc
    Fintype.card (DescendantBranches r) =
        Fintype.card ↥(branchNodesUnder r) :=
      Fintype.card_congr (descendantBranchesEquivBranchNodesUnder r)
    _ = (branchNodesUnder r).card := Fintype.card_coe _

/-- Exact branch partition under contraction. -/
theorem card_BranchNodes_contractAt_add_card_BranchNodes_subtreeAt
    {t : PlaneTree} (r : VPos t) :
    (BranchNodes (contractAt t r.1)).card +
        (BranchNodes (subtreeAt t r.1)).card =
      (BranchNodes t).card := by
  rw [card_BranchNodes_contractAt_eq_card_branchesOutside r.2,
    card_branchesOutside_eq_filter]
  have hsub :
      (BranchNodes (subtreeAt t r.1)).card =
        (branchNodesUnder r).card := by
    calc
      (BranchNodes (subtreeAt t r.1)).card =
          Fintype.card
            {v : VPos (subtreeAt t r.1) //
              v ∈ BranchNodes (subtreeAt t r.1)} :=
        (Fintype.card_coe _).symm
      _ = Fintype.card (DescendantBranches r) :=
        Fintype.card_congr (subtreeBranchEquiv r)
      _ = (branchNodesUnder r).card :=
        card_descendantBranches_eq_branchNodesUnder r
  rw [hsub]
  unfold branchNodesUnder
  simpa [Nat.add_comm] using
    (Finset.card_filter_add_card_filter_not
      (s := BranchNodes t) fun u : VPos t => r.1 <+: u.1)

/-- Contracting a branch removes at least that branch from the branch count.
This is the exponent inequality used to extract one factor `D⁻¹`. -/
theorem card_BranchNodes_contractAt_add_one_le
    {t : PlaneTree} {r : VPos t}
    (hr : r ∈ BranchNodes t) :
    (BranchNodes (contractAt t r.1)).card + 1 ≤
      (BranchNodes t).card := by
  have hrootBranch :
      rootV (subtreeAt t r.1) ∈
        BranchNodes (subtreeAt t r.1) := by
    rw [mem_BranchNodes_subtreeVertex_iff r]
    simpa using hr
  have hone :
      1 ≤ (BranchNodes (subtreeAt t r.1)).card :=
    Finset.one_le_card.mpr ⟨_, hrootBranch⟩
  have hledger :=
    card_BranchNodes_contractAt_add_card_BranchNodes_subtreeAt r
  omega

/-- Subtractive form of the same strict branch saving. -/
theorem card_BranchNodes_contractAt_le_sub_one
    {t : PlaneTree} {r : VPos t}
    (hr : r ∈ BranchNodes t) :
    (BranchNodes (contractAt t r.1)).card ≤
      (BranchNodes t).card - 1 := by
  have := card_BranchNodes_contractAt_add_one_le hr
  omega

end Anderson4D
