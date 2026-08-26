import Anderson4D.PermSum.CollapseEmbedding
import Anderson4D.PermSum.CollapseGamma
import Anderson4D.PermSum.CollapseLeafExistence
import Anderson4D.PermSum.CollapsePredicates
import Anderson4D.PermSum.CollapseTreeCoordinates

/-!
# Ready-to-use analytic calls in the Proposition 5.9 collapse

This file discharges the structural and geometric side conditions needed for
the two analytic estimates used after a collapse: Proposition 5.10 on the
selected rooted subtree, and the induction hypothesis on the contracted tree.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree

noncomputable section

/-! ## Proposition 5.10 on the restricted subtree -/

/-- A lowest eligible branch supplies every hypothesis of Proposition 5.10
on the restricted tree.  The scale parameter is exactly the original parent
scale and the skipped set is the canonical composition-cut set. -/
theorem singleScaleEstimate_restrict
    {C0 : ℝ} (hsingle : SingleScaleEstimate C0)
    {t : PlaneTree} (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t))
    (hcompound : compound ⊆ Leaves t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (hsep : IsSeparatedEmbedding Nm z)
    {r : VPos t} (hr : IsLowestCollapseEligible Nm mu r)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hSpec : CollapseMultiplicitySpec
      (splitLeafMultiplicity mu r) d) :
    paperSum (M := d.insideLength)
        (leafMultiplicity (restrictMultiplicities mu r))
        (singleScaleChainWeight
          (restrictEmbedding z r) d.adjacentCutIndices) ≤
      singleScaleRHS C0 d.insideLength
        d.adjacentCutIndices.card
        (scaleN Nm (parentV r))
        (subtreeAt t r.1)
        (restrictMarking Nm r)
        (restrictMultiplicities mu r)
        (restrictCompound r compound) := by
  have hrData := Finset.mem_erase.mp hr.1.1
  have hroot :
      rootV (subtreeAt t r.1) ∈
        BranchNodes (subtreeAt t r.1) := by
    rw [mem_BranchNodes_subtreeVertex_iff r]
    simpa using hrData.2
  have hparameters :=
    eligible_restrict_p5Parameters Nm mu hr.1
  exact hsingle.2
    d.insideLength d.adjacentCutIndices.card
    (scaleN Nm (parentV r))
    (subtreeAt t r.1)
    (restrictMarking Nm r)
    (restrictMultiplicities mu r)
    (restrictCompound r compound)
    (restrictEmbedding z r)
    d.adjacentCutIndices
    (isValid_subtreeAt ht r.2)
    hroot
    (restrictCompound_subset_leaves r hcompound)
    (totalMultiplicity_restrict_eq_insideLength mu r d hSpec)
    (isSeparatedEmbedding_restrict Nm z r hsep)
    (lowestEligible_restrict_singleScale Nm mu hr)
    hparameters.1
    hparameters.2
    rfl

/-! ## Contracted induction data -/

/-- All non-recursive hypotheses needed to apply Proposition 5.9 to the
contracted tree, including strict decrease of the induction measure. -/
theorem contracted_induction_hypotheses
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t))
    (hcompound : compound ⊆ Leaves t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (hsep : IsSeparatedEmbedding Nm z)
    (hdiam : SatisfiesSubtreeDiameter Nm mu z)
    {r : VPos t} (hr : CollapseEligible Nm mu r)
    (lstar : InsideLeaf r)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hSpec : CollapseMultiplicitySpec
      (splitLeafMultiplicity mu r) d)
    (hblocks : 2 ≤ d.blocks.length) :
    let s := collapseCutCount d
    let hs := one_le_collapseCutCount d hblocks
    (contractAt t r.1).isValid = true ∧
      rootV (contractAt t r.1) ∈
        BranchNodes (contractAt t r.1) ∧
      contractCompound r compound ⊆ Leaves (contractAt t r.1) ∧
      totalMultiplicity
          (contractMultiplicities mu r s hs) =
        d.collapsed.length ∧
      IsSeparatedEmbedding (contractMarking Nm r)
        (contractEmbedding z r lstar) ∧
      SatisfiesSubtreeDiameter
        (contractMarking Nm r)
        (contractMultiplicities mu r s hs)
        (contractEmbedding z r lstar) ∧
      (contractAt t r.1).size < t.size := by
  dsimp only
  have hrData := Finset.mem_erase.mp hr.1
  refine ⟨isValid_contractAt ht r.2,
    root_mem_BranchNodes_contractAt_of_ne r hrData.1 hroot,
    contractCompound_subset_leaves r hcompound,
    totalMultiplicity_contract_eq_collapsedLength
      mu r d hSpec hblocks,
    isSeparatedEmbedding_contract Nm z r lstar hsep,
    satisfiesSubtreeDiameter_contract_of_eligible
      ht Nm mu z r hr lstar
        (collapseCutCount d)
        (one_le_collapseCutCount d hblocks) hdiam,
    contractAt_size_lt_of_branch hrData.2⟩

end

end Anderson4D
