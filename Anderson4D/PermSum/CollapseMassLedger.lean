import Anderson4D.PermSum.CollapseLeafExistence
import Anderson4D.PermSum.CollapseOffMarker
import Anderson4D.PermSum.CollapseTreeCoordinates

/-!
# Multiplicity ledgers for the collapse induction

This module records the three elementary mass facts used in the final
assembly of Proposition 5.9: a branching subtree carries at least four
copies, the original mass splits into its inside and outside parts, and a
skipped branch set in the contracted tree is paid for by the multiplicity
away from the new marker leaf.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- A tree whose root branches carries at least four copies: it has at least
two leaves and every leaf multiplicity is at least two. -/
theorem four_le_totalMultiplicity_of_root_mem_BranchNodes
    {t : PlaneTree} (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t) :
    4 ≤ totalMultiplicity mu := by
  have hcard :
      2 ≤ Fintype.card (HeppLeaf t) := by
    rw [Fintype.card_coe, card_Leaves_eq_leafCount]
    exact two_le_leafCount_of_root_mem_BranchNodes t hroot
  unfold totalMultiplicity
  calc
    4 ≤ 2 * Fintype.card (HeppLeaf t) := by omega
    _ = ∑ _l : HeppLeaf t, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ l : HeppLeaf t, leafMultiplicity mu l := by
      exact Finset.sum_le_sum fun l _ => mu.two_le l.1 l.2

/-- The inside mass of a selected branch is at least four. -/
theorem four_le_totalMultiplicity_restrict
    {t : PlaneTree} (mu : Multiplicities t) (r : VPos t)
    (hr : r ∈ BranchNodes t) :
    4 ≤ totalMultiplicity (restrictMultiplicities mu r) := by
  have hroot :
      rootV (subtreeAt t r.1) ∈ BranchNodes (subtreeAt t r.1) := by
    rw [mem_BranchNodes_subtreeVertex_iff r]
    simpa using hr
  exact
    four_le_totalMultiplicity_of_root_mem_BranchNodes
      hroot (restrictMultiplicities mu r)

/-- Original mass is the restricted mass plus the unchanged outside mass. -/
theorem totalMultiplicity_eq_restrict_add_outside
    {t : PlaneTree} (mu : Multiplicities t) (r : VPos t) :
    totalMultiplicity mu =
      totalMultiplicity (restrictMultiplicities mu r) +
        outsideMultiplicityTotal mu r := by
  rw [totalMultiplicity_restrictMultiplicities,
    totalMultiplicity_eq_inside_add_outside]

/-- The sum of contracted multiplicities away from the marker is exactly the
original outside mass. -/
theorem sum_contractMultiplicity_erase_marker
    {t : PlaneTree} (mu : Multiplicities t) (r : VPos t)
    (s : ℕ) (hs : 1 ≤ s) :
    (∑ l ∈
        (Finset.univ : Finset (HeppLeaf (contractAt t r.1))).erase
          (contractMarkerLeaf r),
        leafMultiplicity (contractMultiplicities mu r s hs) l) =
      outsideMultiplicityTotal mu r := by
  have hsum :
      (∑ l ∈
          (Finset.univ : Finset (HeppLeaf (contractAt t r.1))).erase
            (contractMarkerLeaf r),
          leafMultiplicity (contractMultiplicities mu r s hs) l) +
        leafMultiplicity (contractMultiplicities mu r s hs)
          (contractMarkerLeaf r) =
      totalMultiplicity (contractMultiplicities mu r s hs) := by
    unfold totalMultiplicity
    simpa using
      (Finset.sum_erase_add
        (s :=
          (Finset.univ : Finset (HeppLeaf (contractAt t r.1))))
        (f :=
          fun l => leafMultiplicity (contractMultiplicities mu r s hs) l)
        (show contractMarkerLeaf r ∈
            (Finset.univ :
              Finset (HeppLeaf (contractAt t r.1))) from
          Finset.mem_univ _))
  rw [contractMultiplicities_marker,
    totalMultiplicity_contractMultiplicities] at hsum
  omega

/-- Every skipped set in the contracted tree satisfies the off-marker
cardinality hypothesis used in the factorial comparison (5.47). -/
theorem two_mul_card_contractW_le_outsideMultiplicityTotal
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t) (r : VPos t)
    (hr : r ∈ nonrootBranches t)
    (s : ℕ) (hs : 1 ≤ s)
    (W : Finset (VPos (contractAt t r.1)))
    (hW : W ⊆ nonrootBranches (contractAt t r.1)) :
    2 * W.card ≤ outsideMultiplicityTotal mu r := by
  have hrData := Finset.mem_erase.mp hr
  have hcontract :=
    two_mul_card_le_sum_leafMultiplicity_erase_of_subset_nonrootBranches
      (isValid_contractAt ht r.2)
      (root_mem_BranchNodes_contractAt_of_ne r hrData.1 hroot)
      (contractMultiplicities mu r s hs)
      (contractMarkerLeaf r) W hW
  rw [sum_contractMultiplicity_erase_marker mu r s hs] at hcontract
  exact hcontract

end

end Anderson4D
