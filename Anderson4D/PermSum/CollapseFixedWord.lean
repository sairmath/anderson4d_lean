import Anderson4D.PermSum.CollapseBoundaryChain
import Anderson4D.PermSum.CollapseInsideChain
import Anderson4D.PermSum.CollapsePrimitivity
import Anderson4D.PermSum.CollapseReindexTree
import Anderson4D.PermSum.CollapseTreeCoordinates

/-!
# Fixed-word connector for the collapse induction

This module transports the two word predicates and the chain products from
raw collapse coordinates to the actual restricted and contracted Hepp-tree
alphabets.  It is the pointwise connector between the raw summand and the two
subproblems in paper (5.43).
-/

namespace Anderson4D

open PlaneTree

set_option warningAsError true
set_option autoImplicit false

noncomputable section

/-! ## Predicate transport through alphabet renaming -/

/-- `NoAdjacentOutside` is invariant under an alphabet equivalence. -/
theorem noAdjacentOutside_wordRename_iff
    {α β : Type*} {m : ℕ}
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (O : Finset (AdjacentIndex m))
    (w : Fin m → α) :
    NoAdjacentOutside O (wordRenameEquiv e m w) ↔
      NoAdjacentOutside O w := by
  constructor
  · intro h j hj heq
    exact h j hj (congrArg e heq)
  · intro h j hj heq
    exact h j hj (e.injective heq)

/-- The original finite-word adjacency condition supplies the exact
restricted-tree predicate required by Proposition 5.10. -/
theorem RawCollapseData.restrictedInsideWord_noAdjacentOutside
    {t : PlaneTree} {r : VPos t}
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hadjacent : NoAdjacentEqual d.expandedWord) :
    NoAdjacentOutside d.adjacentCutIndices
      (restrictedInsideWord r d) := by
  have hchain : d.expandWord.IsChain (· ≠ ·) := by
    have h :=
      (noAdjacentEqual_iff_isChain_ofFn d.expandedWord).mp hadjacent
    simpa only [d.ofFn_expandedWord] using h
  have hraw :
      NoAdjacentOutside d.adjacentCutIndices d.insideWord :=
    d.insideWord_noAdjacentOutside hchain
  change
    NoAdjacentOutside d.adjacentCutIndices
      (wordRenameEquiv (restrictInsideAlphabetEquiv r)
        d.insideLength d.insideWord)
  exact
    (noAdjacentOutside_wordRename_iff
      (restrictInsideAlphabetEquiv r)
      d.adjacentCutIndices d.insideWord).mpr hraw

/-- The collapsed word on the actual contracted-tree alphabet inherits
unequal neighbours. -/
theorem RawCollapseData.contractedCollapsedWord_noAdjacentEqual
    {t : PlaneTree} {r : VPos t}
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hadjacent : NoAdjacentEqual d.expandedWord) :
    NoAdjacentEqual (contractedCollapsedWord r d) := by
  have hchain : d.expandWord.IsChain (· ≠ ·) := by
    have h :=
      (noAdjacentEqual_iff_isChain_ofFn d.expandedWord).mp hadjacent
    simpa only [d.ofFn_expandedWord] using h
  have hraw : NoAdjacentEqual d.collapsedWord :=
    d.collapsedWord_noAdjacentEqual hchain
  change
    NoAdjacentEqual
      (wordRenameEquiv (contractCollapsedAlphabetEquiv r)
        d.collapsed.length d.collapsedWord)
  exact
    (noAdjacentEqual_wordRename_iff
      (contractCollapsedAlphabetEquiv r) d.collapsedWord).mpr hraw

/-- The collapsed word on the actual contracted-tree alphabet inherits the
paper's proper-leaf-block condition. -/
theorem RawCollapseData.contractedCollapsedWord_noProperLeafBlock
    {t : PlaneTree} {r : VPos t}
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hprimitive : NoProperLeafBlock d.expandedWord) :
    NoProperLeafBlock (contractedCollapsedWord r d) := by
  letI : Nonempty (InsideLeaf r) := nonempty_insideLeaf r
  have hraw : NoProperLeafBlock d.collapsedWord :=
    d.collapsedWord_noProperLeafBlock hprimitive
  change
    NoProperLeafBlock
      (wordRenameEquiv (contractCollapsedAlphabetEquiv r)
        d.collapsed.length d.collapsedWord)
  exact noProperLeafBlock_wordRename
    (contractCollapsedAlphabetEquiv r) d.collapsedWord hraw

/-- Both predicates required by the contracted primitive-separated
subproblem. -/
theorem RawCollapseData.contractedCollapsedWord_primitiveSeparated
    {t : PlaneTree} {r : VPos t}
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hprimitive : NoProperLeafBlock d.expandedWord)
    (hadjacent : NoAdjacentEqual d.expandedWord) :
    NoProperLeafBlock (contractedCollapsedWord r d) ∧
      NoAdjacentEqual (contractedCollapsedWord r d) :=
  ⟨d.contractedCollapsedWord_noProperLeafBlock hprimitive,
    d.contractedCollapsedWord_noAdjacentEqual hadjacent⟩

/-! ## Collapsed-chain exact connector -/

/-- Pulling the contracted embedding back to the raw marker/outside alphabet
is exactly `collapsedCollapsePoint`. -/
theorem collapsedCollapsePoint_contractCollapsedAlphabetEquiv_symm
    {t : PlaneTree} (z : HeppLeaf t → Fin 4 → ℤ)
    (r : VPos t) (lstar : InsideLeaf r) :
    (fun l : HeppLeaf (contractAt t r.1) =>
      collapsedCollapsePoint z r lstar
        ((contractCollapsedAlphabetEquiv r).symm l)) =
      contractEmbedding z r lstar := by
  funext l
  cases h : contractLeafSumEquiv r l with
  | inl u =>
      cases u
      have hl : l = contractMarkerLeaf r := by
        apply (contractLeafSumEquiv r).injective
        rw [h, contractLeafSumEquiv_marker]
      subst l
      simp [contractCollapsedAlphabetEquiv,
        collapsedCollapsePoint]
  | inr lout =>
      have hl : l = contractOutsideLeaf r lout := by
        apply (contractLeafSumEquiv r).injective
        rw [h, contractLeafSumEquiv_contractOutsideLeaf]
      subst l
      simp [contractCollapsedAlphabetEquiv,
        collapsedCollapsePoint]

/-- The raw collapsed list chain is exactly the chain weight of the renamed
word on the actual contracted tree. -/
theorem RawCollapseData.collapsedChainProduct_eq_heppChainWeight
    {t : PlaneTree} (z : HeppLeaf t → Fin 4 → ℤ)
    {r : VPos t} (lstar : InsideLeaf r)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r)) :
    listChainProduct (collapsedCollapseEdge z r lstar) d.collapsed =
      heppChainWeight (contractEmbedding z r lstar)
        (contractedCollapsedWord r d) := by
  let e := contractCollapsedAlphabetEquiv r
  let p := collapsedCollapsePoint z r lstar
  calc
    listChainProduct (collapsedCollapseEdge z r lstar) d.collapsed =
        alphabetChainWeight p d.collapsedWord := by
      rw [alphabetChainWeight_eq_listChainProduct,
        d.ofFn_collapsedWord]
      rfl
    _ = alphabetChainWeight (fun l => p (e.symm l))
        (wordRenameEquiv e d.collapsed.length d.collapsedWord) := by
      exact (alphabetChainWeight_wordRename e p d.collapsedWord).symm
    _ = heppChainWeight (contractEmbedding z r lstar)
        (contractedCollapsedWord r d) := by
      have hp :
          (fun l : HeppLeaf (contractAt t r.1) => p (e.symm l)) =
            contractEmbedding z r lstar := by
        exact
          collapsedCollapsePoint_contractCollapsedAlphabetEquiv_symm
            z r lstar
      rw [hp]
      rfl

/-- Under the transported predicates, the raw collapsed chain is the actual
contracted primitive-separated summand. -/
theorem RawCollapseData.collapsedChainProduct_eq_primitiveSeparatedChainWeight
    {t : PlaneTree} (z : HeppLeaf t → Fin 4 → ℤ)
    {r : VPos t} (lstar : InsideLeaf r)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hprimitive : NoProperLeafBlock d.expandedWord)
    (hadjacent : NoAdjacentEqual d.expandedWord) :
    listChainProduct (collapsedCollapseEdge z r lstar) d.collapsed =
      primitiveSeparatedChainWeight (contractEmbedding z r lstar)
        (contractedCollapsedWord r d) := by
  rw [primitiveSeparatedChainWeight,
    if_pos (d.contractedCollapsedWord_primitiveSeparated
      hprimitive hadjacent)]
  exact d.collapsedChainProduct_eq_heppChainWeight z lstar

/-! ## Active raw summand -/

/-- The split-alphabet position from the exact reindexing is the position
used by the geometric collapse estimate. -/
theorem splitLeafPosition_eq_originalCollapsePoint
    {t : PlaneTree} (z : HeppLeaf t → Fin 4 → ℤ)
    (r : VPos t) :
    splitLeafPosition r z = originalCollapsePoint z := by
  funext x
  cases x <;> rfl

/-- On an active raw datum, the raw statistic is exactly the original
split-alphabet list chain used by the geometric `(5.43)` estimate. -/
theorem RawCollapseData.rawPrimitiveSeparatedChainWeight_eq_originalChain
    {t : PlaneTree} (z : HeppLeaf t → Fin 4 → ℤ)
    {r : VPos t}
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hprimitive : NoProperLeafBlock d.expandedWord)
    (hadjacent : NoAdjacentEqual d.expandedWord) :
    rawPrimitiveSeparatedChainWeight (splitLeafPosition r z) d =
      listChainProduct (originalCollapseEdge z) d.expandWord := by
  rw [rawPrimitiveSeparatedChainWeight,
    if_pos ⟨hprimitive, hadjacent⟩]
  rw [splitLeafPosition_eq_originalCollapsePoint z r]
  rfl

/-! ## Fixed-word `(5.43)` -/

/-- Pointwise connector from an active raw primitive-separated summand to
the actual restricted single-scale and contracted primitive-separated
subproblems. -/
theorem RawCollapseData.rawPrimitiveSeparatedChainWeight_le_fixedWordFactors
    {t : PlaneTree}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (hsep : IsSeparatedEmbedding Nm z)
    (hdiam : SatisfiesSubtreeDiameter Nm mu z)
    {r : VPos t} (hr : CollapseEligible Nm mu r)
    (lstar : InsideLeaf r)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hprimitive : NoProperLeafBlock d.expandedWord)
    (hadjacent : NoAdjacentEqual d.expandedWord) :
    rawPrimitiveSeparatedChainWeight (splitLeafPosition r z) d ≤
      (4 : ℝ) ^ d.insideLength *
        singleScaleChainWeight (restrictEmbedding z r)
          d.adjacentCutIndices (restrictedInsideWord r d) *
        primitiveSeparatedChainWeight (contractEmbedding z r lstar)
          (contractedCollapsedWord r d) := by
  have hrestricted :
      NoAdjacentOutside d.adjacentCutIndices
        (restrictedInsideWord r d) :=
    d.restrictedInsideWord_noAdjacentOutside hadjacent
  have hcontracted :
      NoProperLeafBlock (contractedCollapsedWord r d) ∧
        NoAdjacentEqual (contractedCollapsedWord r d) :=
    d.contractedCollapsedWord_primitiveSeparated hprimitive hadjacent
  rw [d.rawPrimitiveSeparatedChainWeight_eq_originalChain
    z hprimitive hadjacent]
  rw [singleScaleChainWeight, if_pos hrestricted]
  rw [primitiveSeparatedChainWeight, if_pos hcontracted]
  calc
    listChainProduct (originalCollapseEdge z) d.expandWord ≤
        (4 : ℝ) ^ d.insideLength *
          d.insideBlockChainProduct (originalCollapseEdge z) *
          listChainProduct (collapsedCollapseEdge z r lstar)
            d.collapsed :=
      d.expandWord_latticeChain_le_four_pow
        ht Nm mu z hsep hdiam hr lstar
    _ = (4 : ℝ) ^ d.insideLength *
        heppChainWeightExcept (restrictEmbedding z r)
          d.adjacentCutIndices (restrictedInsideWord r d) *
        heppChainWeight (contractEmbedding z r lstar)
          (contractedCollapsedWord r d) := by
      rw [
        d.insideBlockChainProduct_originalCollapseEdge_eq_heppChainWeightExcept
          z r,
        d.collapsedChainProduct_eq_heppChainWeight z lstar]

end

end Anderson4D
