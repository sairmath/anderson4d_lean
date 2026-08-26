import Anderson4D.PermSum.CollapseRegroup
import Anderson4D.PermSum.CollapseAnalyticProduct

/-!
# Analytic bound for one collapse-shape fiber

This module joins the validity-preserving fixed-shape Fubini bound to the
two analytic calls in the eligible-collapse step.  The witness datum fixes
the actual cut set, cut count, inside length, and contracted word length
used by both sides of the estimate.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- A single multiplicity-valid collapse-shape fiber is bounded by the
contracted-tree `W`-sum of `combinedCollapseTerm`.

The first inequality is the concrete valid-word Fubini regrouping; the
second is exactly the product of Proposition 5.10 on the restricted tree
and the P-5.9 induction hypothesis on the contracted tree. -/
theorem sum_filter_witnessShape_collapseRawFixedWordSummand_le_sum_combinedCollapseTerm
    {C0 D : ℝ} (hsingle : SingleScaleEstimate C0)
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t))
    (hcompound : compound ⊆ Leaves t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (hsep : IsSeparatedEmbedding Nm z)
    (hdiam : SatisfiesSubtreeDiameter Nm mu z)
    {r : VPos t} (hr : IsLowestCollapseEligible Nm mu r)
    (lstar : InsideLeaf r)
    {M : ℕ}
    (d₀ : FixedRawCollapseData
      (InsideLeaf r) (OutsideLeaf r) M)
    (hSpec₀ : CollapseMultiplicitySpec
      (splitLeafMultiplicity mu r) d₀.1)
    (hblocks : 2 ≤ d₀.1.blocks.length)
    (hIH : InductiveConclusion C0 D (contractAt t r.1)) :
    (∑ d ∈ Finset.univ.filter
        (fun d : FixedRawCollapseData
            (InsideLeaf r) (OutsideLeaf r) M =>
          CollapseMultiplicitySpec
              (splitLeafMultiplicity mu r) d.1 ∧
            d.1.collapseShape = d₀.1.collapseShape),
        collapseRawFixedWordSummand mu r z lstar d.1) ≤
      ∑ W ∈
          (nonrootBranches (contractAt t r.1)).powerset,
        combinedCollapseTerm C0 D d₀.1.insideLength
          (collapseCutCount d₀.1) d₀.1.collapsed.length
          Nm mu compound r
          (one_le_collapseCutCount d₀.1 hblocks) W := by
  exact le_trans
    (sum_filter_witnessShape_collapseRawFixedWordSummand_le_paperSums
      mu z r lstar M d₀ hSpec₀ hblocks)
    (collapse_analytic_product_le_sum_combinedCollapseTerm
      hsingle ht hroot Nm mu compound hcompound z hsep hdiam
      hr lstar d₀.1 hSpec₀ hblocks hIH)

end

end Anderson4D
