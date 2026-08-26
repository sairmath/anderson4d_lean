import Anderson4D.PermSum.MergeExpansionCount
import Anderson4D.PermSum.MergeWeights
import Anderson4D.PermSum.WeightFilters

/-!
# Run compression preserves the filtered chain weight

Equal-letter edges have lattice weight one.  Consequently the Hepp-chain
weight is unchanged by run compression; primitivity transport and the
destutter chain condition identify the two filtered weights used in
Propositions 5.7 and 5.9.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree

noncomputable section

/-- Exact Hepp-chain-weight invariance under run compression. -/
theorem heppChainWeight_mergedWord
    {t : PlaneTree} {M : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ)
    (w : Fin M → HeppLeaf t) :
    heppChainWeight z (mergedWord w) =
      heppChainWeight z w := by
  rw [heppChainWeight_eq_listChainProduct,
    heppChainWeight_eq_listChainProduct]
  rw [List.ofFn_comp' (mergedWord w) z,
    show List.ofFn (mergedWord w) = mergedWordList w by
      exact List.ofFn_get (mergedWordList w),
    List.ofFn_comp' w z]
  exact latticeChainProduct_mergeLetterRuns z (List.ofFn w)

/-- List-facing form used by the profile regrouping: evaluating the
compressed representative list has the original chain weight. -/
theorem heppChainWeight_listWord_mergedWordList
    {t : PlaneTree} {M : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ)
    (w : Fin M → HeppLeaf t) :
    heppChainWeight z (listWord (mergedWordList w)) =
      heppChainWeight z w := by
  have hword :
      listWord (mergedWordList w) = mergedWord w := by
    apply List.ofFn_injective
    rw [ofFn_listWord]
    exact (List.ofFn_get (mergedWordList w)).symm
  rw [hword, heppChainWeight_mergedWord]

/-- On a primitive original word, the P-5.7 weight is exactly the P-5.9
primitive-and-separated weight of its run compression. -/
theorem primitiveSeparatedChainWeight_mergedWord_of_primitive
    {t : PlaneTree} {M : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ)
    (w : Fin M → HeppLeaf t)
    (hprimitive : NoProperLeafBlock w) :
    primitiveSeparatedChainWeight z (mergedWord w) =
      primitiveChainWeight z w := by
  unfold primitiveSeparatedChainWeight primitiveChainWeight
  rw [if_pos hprimitive,
    if_pos
      ⟨mergedWord_noProperLeafBlock w hprimitive,
        mergedWord_noAdjacentEqual w⟩,
    heppChainWeight_mergedWord]

end

end Anderson4D
