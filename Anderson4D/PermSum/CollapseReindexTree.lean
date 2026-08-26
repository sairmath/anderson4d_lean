import Anderson4D.PermSum.CollapsePrimitivity
import Anderson4D.PermSum.CollapseRename
import Anderson4D.PermSum.MergeWeights

/-!
# Tree-facing exact reindexing for the Proposition 5.9 collapse

This file packages the word-collapse equivalence in the precise form used by
the induction.  The original primitive separated paper sum becomes a sum over
raw collapse data, with the marker inverse factorial inserted by the
factorial ledger.  No fiber cardinality is introduced.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open scoped BigOperators

noncomputable section

variable {A B : Type*}

/-! ## Finite and list chain weights -/

/-- The alphabet-valued chain weight is the corresponding consecutive-edge
product on the underlying list. -/
theorem alphabetChainWeight_eq_listChainProduct
    {α : Type*} {m : ℕ}
    (z : α → Fin 4 → ℤ) (w : Fin m → α) :
    alphabetChainWeight z w =
      listChainProduct
        (fun x y => latticeEdgeWeight (z x) (z y))
        (List.ofFn w) := by
  unfold alphabetChainWeight
  let e := adjacentIndexEquiv m
  let edge : α → α → ℝ :=
    fun x y => latticeEdgeWeight (z x) (z y)
  let g : Fin m.pred → ℝ := fun i =>
    edge (w (chainLeftIndex i)) (w (chainRightIndex i))
  calc
    (∏ j : AdjacentIndex m,
        latticeEdgeWeight (z (w j.1))
          (z (w (adjacentSucc j)))) =
        ∏ j : AdjacentIndex m, g (e j) := by
      apply Finset.prod_congr rfl
      intro j _
      rfl
    _ = ∏ i : Fin m.pred, g i := Equiv.prod_comp e g
    _ = indexedChainProduct edge w := by
      rfl
    _ = listChainProduct edge (List.ofFn w) := by
      exact (listChainProduct_ofFn edge w).symm

/-! ## The inverse collapse word -/

/-- Re-expanding inverse finite collapse coordinates recovers their stored
expanded list exactly. -/
@[simp] theorem ofFn_finWordRawCollapseEquiv_symm
    [DecidableEq A] [DecidableEq B] {n : ℕ}
    (d : FixedRawCollapseData A B n) :
    List.ofFn ((finWordRawCollapseEquiv A B n).symm d) =
      d.1.expandWord := by
  have h :=
    finWordRawCollapseEquiv_expandWord
      (A := A) (B := B)
      ((finWordRawCollapseEquiv A B n).symm d)
  simpa using h.symm

/-- Primitive separated chain statistic written directly on raw collapse
coordinates. -/
def rawPrimitiveSeparatedChainWeight
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (z : A ⊕ B → Fin 4 → ℤ) (d : RawCollapseData A B) : ℝ :=
  if NoProperLeafBlock d.expandedWord ∧
      NoAdjacentEqual d.expandedWord then
    listChainProduct
      (fun x y => latticeEdgeWeight (z x) (z y))
      d.expandWord
  else
    0

/-- Pointwise compatibility of the raw statistic with the inverse finite
collapse equivalence. -/
theorem primitiveSeparatedAlphabetChainWeight_collapse_symm
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (z : A ⊕ B → Fin 4 → ℤ)
    (d : FixedRawCollapseData A B n) :
    primitiveSeparatedAlphabetChainWeight z
        ((finWordRawCollapseEquiv A B n).symm d) =
      rawPrimitiveSeparatedChainWeight z d.1 := by
  rcases d with ⟨d, hd⟩
  subst n
  have hword :
      (finWordRawCollapseEquiv A B d.expandedLength).symm
          ⟨d, rfl⟩ =
        d.expandedWord := by
    apply List.ofFn_injective
    rw [ofFn_finWordRawCollapseEquiv_symm, d.ofFn_expandedWord]
  rw [hword]
  unfold primitiveSeparatedAlphabetChainWeight
  unfold rawPrimitiveSeparatedChainWeight
  rw [alphabetChainWeight_eq_listChainProduct,
    d.ofFn_expandedWord]

/-! ## Exact tree-facing sum formula -/

open PlaneTree

/-- Exact collapse reindexing of the left side of Proposition 5.9.

The factor `(blocks.length !)⁻¹` is the marker factorial ledger.  The theorem
is an equality, so later estimates may work pointwise on a raw collapse datum
without assuming uniqueness or introducing a quotient argument. -/
theorem paperSum_primitiveSeparated_eq_sum_collapseData
    {t : PlaneTree} {m : ℕ}
    (mu : Multiplicities t) (r : VPos t)
    (z : HeppLeaf t → Fin 4 → ℤ) :
    paperSum (M := m) (leafMultiplicity mu)
        (primitiveSeparatedChainWeight z) =
      ∑ d : FixedRawCollapseData
          (InsideLeaf r) (OutsideLeaf r) m,
        if CollapseMultiplicitySpec
            (splitLeafMultiplicity mu r) d.1 then
          (d.1.blocks.length.factorial : ℝ)⁻¹ *
            ((∏ a : InsideLeaf r,
                ((insideMultiplicity
                    (splitLeafMultiplicity mu r) a).factorial : ℝ)) *
              ∏ x : Unit ⊕ OutsideLeaf r,
                ((collapsedMultiplicity
                    (splitLeafMultiplicity mu r) d.1 x).factorial : ℝ)) *
            rawPrimitiveSeparatedChainWeight
              (splitLeafPosition r z) d.1
        else
          0 := by
  rw [paperSum_primitiveSeparated_eq_splitLeafAlphabet]
  rw [paperSum_eq_sum_fixedRawCollapseData]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hspec :
      CollapseMultiplicitySpec (splitLeafMultiplicity mu r) d.1
  · simp only [hspec, if_true]
    rw [primitiveSeparatedAlphabetChainWeight_collapse_symm]
  · simp [hspec]

end

end Anderson4D
