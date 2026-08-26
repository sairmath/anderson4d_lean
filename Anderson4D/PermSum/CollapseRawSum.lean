import Anderson4D.PermSum.CollapseFixedWord

/-!
# Raw-collapse finite-sum bound

This module combines the exact raw-data reindexing of the P-5.9 paper sum
with the fixed-word `(5.43)` estimate.  The named summands below expose the
finite family that the subsequent Fubini regrouping consumes.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

set_option warningAsError true
set_option autoImplicit false

noncomputable section

/-! ## Named raw-data summands -/

/-- Factorial coefficient attached to a raw collapse datum by the exact
marker-fiber ledger. -/
def collapseRawLedgerCoefficient {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r)) : ℝ :=
  (d.blocks.length.factorial : ℝ)⁻¹ *
    ((∏ a : InsideLeaf r,
        ((insideMultiplicity
          (splitLeafMultiplicity mu r) a).factorial : ℝ)) *
      ∏ x : Unit ⊕ OutsideLeaf r,
        ((collapsedMultiplicity
          (splitLeafMultiplicity mu r) d x).factorial : ℝ))

/-- The factorial ledger is nonnegative, as required to multiply a
pointwise chain-weight inequality. -/
theorem collapseRawLedgerCoefficient_nonneg {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r)) :
    0 ≤ collapseRawLedgerCoefficient mu r d := by
  unfold collapseRawLedgerCoefficient
  positivity

/-- Named summand in the exact raw-data reindexing, before applying
`(5.43)`. -/
def collapseRawReindexedSummand {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r)) : ℝ :=
  if CollapseMultiplicitySpec
      (splitLeafMultiplicity mu r) d then
    collapseRawLedgerCoefficient mu r d *
      rawPrimitiveSeparatedChainWeight
        (splitLeafPosition r z) d
  else
    0

/-- Explicit active fixed-word summand prepared for Fubini regrouping.  Its
indicator displays all three conditions that make the raw contribution
nonzero and admissible for the two recursive subproblems. -/
def collapseRawFixedWordSummand {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (z : HeppLeaf t → Fin 4 → ℤ) (lstar : InsideLeaf r)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r)) : ℝ :=
  if CollapseMultiplicitySpec (splitLeafMultiplicity mu r) d ∧
      NoProperLeafBlock d.expandedWord ∧
      NoAdjacentEqual d.expandedWord then
    collapseRawLedgerCoefficient mu r d *
      (4 : ℝ) ^ d.insideLength *
      singleScaleChainWeight (restrictEmbedding z r)
        d.adjacentCutIndices (restrictedInsideWord r d) *
      primitiveSeparatedChainWeight (contractEmbedding z r lstar)
        (contractedCollapsedWord r d)
  else
    0

/-! ## Exact reindexed sum -/

/-- The exact P-5.9 collapse reindexing expressed using the named raw
summand. -/
theorem paperSum_primitiveSeparated_eq_sum_collapseRawReindexedSummand
    {t : PlaneTree} {M : ℕ}
    (mu : Multiplicities t) (r : VPos t)
    (z : HeppLeaf t → Fin 4 → ℤ) :
    paperSum (M := M) (leafMultiplicity mu)
        (primitiveSeparatedChainWeight z) =
      ∑ d : FixedRawCollapseData
          (InsideLeaf r) (OutsideLeaf r) M,
        collapseRawReindexedSummand mu r z d.1 := by
  rw [paperSum_primitiveSeparated_eq_sum_collapseData]
  apply Finset.sum_congr rfl
  intro d _
  rfl

/-! ## Pointwise and finite-sum bounds -/

/-- Every reindexed raw summand is bounded by its explicit active
fixed-word summand.  Inactive data vanish on both sides; in the active case
the nonnegative factorial coefficient multiplies the fixed-word `(5.43)`
estimate. -/
theorem collapseRawReindexedSummand_le_fixedWordSummand
    {t : PlaneTree}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (hsep : IsSeparatedEmbedding Nm z)
    (hdiam : SatisfiesSubtreeDiameter Nm mu z)
    {r : VPos t} (hr : CollapseEligible Nm mu r)
    (lstar : InsideLeaf r)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r)) :
    collapseRawReindexedSummand mu r z d ≤
      collapseRawFixedWordSummand mu r z lstar d := by
  by_cases hspec :
      CollapseMultiplicitySpec (splitLeafMultiplicity mu r) d
  · by_cases hprimitive : NoProperLeafBlock d.expandedWord
    · by_cases hadjacent : NoAdjacentEqual d.expandedWord
      · have hweight :=
          d.rawPrimitiveSeparatedChainWeight_le_fixedWordFactors
            ht Nm mu z hsep hdiam hr lstar hprimitive hadjacent
        have hcoeff :=
          collapseRawLedgerCoefficient_nonneg mu r d
        unfold collapseRawReindexedSummand
        unfold collapseRawFixedWordSummand
        rw [if_pos hspec,
          if_pos ⟨hspec, hprimitive, hadjacent⟩]
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hweight hcoeff
      · simp [collapseRawReindexedSummand,
          collapseRawFixedWordSummand,
          rawPrimitiveSeparatedChainWeight,
          hspec, hprimitive, hadjacent]
    · simp [collapseRawReindexedSummand,
        collapseRawFixedWordSummand,
        rawPrimitiveSeparatedChainWeight,
        hspec, hprimitive]
  · simp [collapseRawReindexedSummand,
      collapseRawFixedWordSummand, hspec]

/-- Tree-facing raw-data finite-sum upper bound.  The `compound` argument is
carried explicitly for the subsequent collapse assembly, although this
chain-only stage does not inspect it. -/
theorem paperSum_primitiveSeparated_le_sum_collapseRawFixedWord
    {t : PlaneTree} {M : ℕ}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (_compound : Finset (VPos t))
    (z : HeppLeaf t → Fin 4 → ℤ)
    (hsep : IsSeparatedEmbedding Nm z)
    (hdiam : SatisfiesSubtreeDiameter Nm mu z)
    {r : VPos t} (hr : IsLowestCollapseEligible Nm mu r)
    (lstar : InsideLeaf r) :
    paperSum (M := M) (leafMultiplicity mu)
        (primitiveSeparatedChainWeight z) ≤
      ∑ d : FixedRawCollapseData
          (InsideLeaf r) (OutsideLeaf r) M,
        collapseRawFixedWordSummand mu r z lstar d.1 := by
  rw [
    paperSum_primitiveSeparated_eq_sum_collapseRawReindexedSummand
      mu r z]
  apply Finset.sum_le_sum
  intro d _
  exact collapseRawReindexedSummand_le_fixedWordSummand
    ht Nm mu z hsep hdiam hr.1 lstar d.1

/-- Fully expanded form of the raw-data bound, matching the summand that is
regrouped in the next Fubini step. -/
theorem paperSum_primitiveSeparated_le_sum_collapseRawFixedWord_explicit
    {t : PlaneTree} {M : ℕ}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t))
    (z : HeppLeaf t → Fin 4 → ℤ)
    (hsep : IsSeparatedEmbedding Nm z)
    (hdiam : SatisfiesSubtreeDiameter Nm mu z)
    {r : VPos t} (hr : IsLowestCollapseEligible Nm mu r)
    (lstar : InsideLeaf r) :
    paperSum (M := M) (leafMultiplicity mu)
        (primitiveSeparatedChainWeight z) ≤
      ∑ d : FixedRawCollapseData
          (InsideLeaf r) (OutsideLeaf r) M,
        if CollapseMultiplicitySpec
              (splitLeafMultiplicity mu r) d.1 ∧
            NoProperLeafBlock d.1.expandedWord ∧
            NoAdjacentEqual d.1.expandedWord then
          collapseRawLedgerCoefficient mu r d.1 *
            (4 : ℝ) ^ d.1.insideLength *
            singleScaleChainWeight (restrictEmbedding z r)
              d.1.adjacentCutIndices (restrictedInsideWord r d.1) *
            primitiveSeparatedChainWeight
              (contractEmbedding z r lstar)
              (contractedCollapsedWord r d.1)
        else
          0 := by
  simpa only [collapseRawFixedWordSummand] using
    paperSum_primitiveSeparated_le_sum_collapseRawFixedWord
      ht Nm mu compound z hsep hdiam hr lstar

end

end Anderson4D
