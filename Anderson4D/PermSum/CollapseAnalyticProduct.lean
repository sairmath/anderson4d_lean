import Anderson4D.PermSum.CollapseApplications
import Anderson4D.PermSum.CollapseInduction
import Anderson4D.PermSum.CollapseRHS
import Anderson4D.PermSum.WeightFilters

/-!
# Product of the two analytic collapse calls

This file combines Proposition 5.10 on the restricted subtree with the
Proposition 5.9 induction hypothesis on the contracted tree.  The contracted
right-hand side is expanded into its `W`-sum, so each summand is exactly
`combinedCollapseTerm`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

private theorem paperSum_nonneg_of_pointwise
    {α : Type*} [Fintype α] [DecidableEq α]
    {M : ℕ} (mult : α → ℕ)
    (F : (Fin M → α) → ℝ)
    (hF : ∀ w, 0 ≤ F w) :
    0 ≤ paperSum mult F := by
  unfold paperSum wordSum
  exact mul_nonneg
    (Finset.prod_nonneg fun _ _ => by positivity)
    (Finset.sum_nonneg fun w _ => hF w)

private theorem restrictedSingleScaleTerm_nonneg
    (C0 : ℝ) (hC0 : 0 ≤ C0) (m s : ℕ)
    {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (r : VPos t) :
    0 ≤ restrictedSingleScaleTerm C0 m s Nm mu compound r := by
  unfold restrictedSingleScaleTerm paperLeafProduct paperLeafFactor
    singleScaleBranchPower restrictionParentRatioFactor
    parentScaleRatio sqrtFactorial factorialThreeQuarters
  positivity

/-! ## The combined analytic estimate -/

/-- The two analytic calls in the eligible-collapse step, multiplied and
expanded into the contracted-tree `W`-sum. -/
theorem collapse_analytic_product_le_sum_combinedCollapseTerm
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
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hSpec : CollapseMultiplicitySpec
      (splitLeafMultiplicity mu r) d)
    (hblocks : 2 ≤ d.blocks.length)
    (hIH : InductiveConclusion C0 D (contractAt t r.1)) :
    (4 : ℝ) ^ d.insideLength *
        (((collapseCutCount d + 1).factorial : ℝ)⁻¹) *
        paperSum (M := d.insideLength)
          (leafMultiplicity (restrictMultiplicities mu r))
          (singleScaleChainWeight
            (restrictEmbedding z r) d.adjacentCutIndices) *
        paperSum (M := d.collapsed.length)
          (leafMultiplicity
            (contractMultiplicities mu r (collapseCutCount d)
              (one_le_collapseCutCount d hblocks)))
          (primitiveSeparatedChainWeight
            (contractEmbedding z r lstar)) ≤
      ∑ W ∈
          (nonrootBranches (contractAt t r.1)).powerset,
        combinedCollapseTerm C0 D d.insideLength
          (collapseCutCount d) d.collapsed.length
          Nm mu compound r
          (one_le_collapseCutCount d hblocks) W := by
  let s := collapseCutCount d
  let hs : 1 ≤ s := one_le_collapseCutCount d hblocks
  have hinsideRaw :=
    singleScaleEstimate_restrict hsingle ht Nm mu compound hcompound
      z hsep hr d hSpec
  rw [singleScaleRHS_restrict_eq] at hinsideRaw
  have hinside :
      paperSum (M := d.insideLength)
          (leafMultiplicity (restrictMultiplicities mu r))
          (singleScaleChainWeight
            (restrictEmbedding z r) d.adjacentCutIndices) ≤
        restrictedSingleScaleTerm C0 d.insideLength s
          Nm mu compound r := by
    simpa [s, collapseCutCount] using hinsideRaw
  have hcontractData :=
    contracted_induction_hypotheses ht hroot Nm mu compound hcompound
      z hsep hdiam hr.1 lstar d hSpec hblocks
  dsimp only at hcontractData
  rcases hcontractData with
    ⟨htContract, hrootContract, hcompoundContract,
      htotalContract, hsepContract, hdiamContract, _⟩
  have hcontractRaw :=
    hIH d.collapsed.length
      (contractMarking Nm r)
      (contractMultiplicities mu r s hs)
      (contractCompound r compound)
      (contractEmbedding z r lstar)
      htContract hrootContract hcompoundContract htotalContract
      hsepContract hdiamContract
  rw [inductiveRHS_eq_sum_contractedInductiveTerm] at hcontractRaw
  have hcontract :
      paperSum (M := d.collapsed.length)
          (leafMultiplicity
            (contractMultiplicities mu r s hs))
          (primitiveSeparatedChainWeight
            (contractEmbedding z r lstar)) ≤
        ∑ W ∈
            (nonrootBranches (contractAt t r.1)).powerset,
          contractedCollapseTerm C0 D d.collapsed.length
            Nm mu compound r s hs W := by
    simpa only [contractedInductiveTerm_eq_collapseTerm] using
      hcontractRaw
  have hcontractPaperNonneg :
      0 ≤ paperSum (M := d.collapsed.length)
        (leafMultiplicity
          (contractMultiplicities mu r s hs))
        (primitiveSeparatedChainWeight
          (contractEmbedding z r lstar)) :=
    paperSum_nonneg_of_pointwise _ _ fun w =>
      primitiveSeparatedChainWeight_nonneg
        (contractEmbedding z r lstar) w
  have hrestrictedNonneg :
      0 ≤ restrictedSingleScaleTerm C0 d.insideLength s
        Nm mu compound r :=
    restrictedSingleScaleTerm_nonneg C0 (by linarith [hsingle.1])
      d.insideLength s Nm mu compound r
  have hproduct :
      paperSum (M := d.insideLength)
          (leafMultiplicity (restrictMultiplicities mu r))
          (singleScaleChainWeight
            (restrictEmbedding z r) d.adjacentCutIndices) *
        paperSum (M := d.collapsed.length)
          (leafMultiplicity
            (contractMultiplicities mu r s hs))
          (primitiveSeparatedChainWeight
            (contractEmbedding z r lstar)) ≤
        restrictedSingleScaleTerm C0 d.insideLength s
            Nm mu compound r *
          (∑ W ∈
              (nonrootBranches (contractAt t r.1)).powerset,
            contractedCollapseTerm C0 D d.collapsed.length
              Nm mu compound r s hs W) :=
    mul_le_mul hinside hcontract hcontractPaperNonneg
      hrestrictedNonneg
  have hcoefficient :
      0 ≤ (4 : ℝ) ^ d.insideLength *
        (((s + 1).factorial : ℝ)⁻¹) := by
    positivity
  calc
    (4 : ℝ) ^ d.insideLength *
          (((collapseCutCount d + 1).factorial : ℝ)⁻¹) *
          paperSum (M := d.insideLength)
            (leafMultiplicity (restrictMultiplicities mu r))
            (singleScaleChainWeight
              (restrictEmbedding z r) d.adjacentCutIndices) *
          paperSum (M := d.collapsed.length)
            (leafMultiplicity
              (contractMultiplicities mu r (collapseCutCount d)
                (one_le_collapseCutCount d hblocks)))
            (primitiveSeparatedChainWeight
              (contractEmbedding z r lstar)) ≤
        ((4 : ℝ) ^ d.insideLength *
          (((s + 1).factorial : ℝ)⁻¹)) *
          (restrictedSingleScaleTerm C0 d.insideLength s
              Nm mu compound r *
            (∑ W ∈
                (nonrootBranches (contractAt t r.1)).powerset,
              contractedCollapseTerm C0 D d.collapsed.length
                Nm mu compound r s hs W)) := by
      simpa only [s, hs, mul_assoc] using
        mul_le_mul_of_nonneg_left hproduct hcoefficient
    _ =
        ∑ W ∈
            (nonrootBranches (contractAt t r.1)).powerset,
          combinedCollapseTerm C0 D d.insideLength s
            d.collapsed.length Nm mu compound r hs W := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro W _
      unfold combinedCollapseTerm
      ring
    _ =
        ∑ W ∈
            (nonrootBranches (contractAt t r.1)).powerset,
          combinedCollapseTerm C0 D d.insideLength
            (collapseCutCount d) d.collapsed.length
            Nm mu compound r
            (one_le_collapseCutCount d hblocks) W := by
      rfl

end
end Anderson4D
