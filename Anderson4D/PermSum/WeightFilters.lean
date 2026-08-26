import Anderson4D.PermSum.Statements

/-!
# Filtered-sum forms of the paper weights

The paper-facing statements package side conditions into `if`-weighted
summands.  Internal permutation-sum proofs instead use `paperSumFiltered`.
This file supplies the exact conversion and nonnegativity lemmas at that
boundary.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators
noncomputable section

theorem latticeEdgeWeight_nonneg (x y : Fin 4 → ℤ) :
    0 ≤ latticeEdgeWeight x y := by
  unfold latticeEdgeWeight
  positivity

theorem heppChainWeight_nonneg {t : PlaneTree} {m : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ) (w : Fin m → HeppLeaf t) :
    0 ≤ heppChainWeight z w :=
  Finset.prod_nonneg fun j _ =>
    latticeEdgeWeight_nonneg (z (w j.1)) (z (w (adjacentSucc j)))

theorem heppChainWeightExcept_nonneg {t : PlaneTree} {m : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ) (O : Finset (AdjacentIndex m))
    (w : Fin m → HeppLeaf t) :
    0 ≤ heppChainWeightExcept z O w := by
  apply Finset.prod_nonneg
  intro j _
  split_ifs
  · positivity
  · exact latticeEdgeWeight_nonneg _ _

theorem primitiveChainWeight_nonneg {t : PlaneTree} {m : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ) (w : Fin m → HeppLeaf t) :
    0 ≤ primitiveChainWeight z w := by
  unfold primitiveChainWeight
  split_ifs
  · exact heppChainWeight_nonneg z w
  · exact le_rfl

theorem primitiveSeparatedChainWeight_nonneg {t : PlaneTree} {m : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ) (w : Fin m → HeppLeaf t) :
    0 ≤ primitiveSeparatedChainWeight z w := by
  unfold primitiveSeparatedChainWeight
  split_ifs
  · exact heppChainWeight_nonneg z w
  · exact le_rfl

theorem singleScaleChainWeight_nonneg {t : PlaneTree} {m : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ) (O : Finset (AdjacentIndex m))
    (w : Fin m → HeppLeaf t) :
    0 ≤ singleScaleChainWeight z O w := by
  unfold singleScaleChainWeight
  split_ifs
  · exact heppChainWeightExcept_nonneg z O w
  · exact le_rfl

/-- The left side of Proposition 5.7 as a filtered `paperSum`. -/
theorem paperSum_primitiveChainWeight {t : PlaneTree} {m : ℕ}
    (mu : Multiplicities t) (z : HeppLeaf t → Fin 4 → ℤ) :
    paperSum (M := m) (leafMultiplicity mu)
        (primitiveChainWeight (m := m) z) =
      paperSumFiltered (M := m) (leafMultiplicity mu)
        NoProperLeafBlock (heppChainWeight z) := by
  unfold paperSum paperSumFiltered wordSum wordSumFiltered
  congr 1
  rw [Finset.sum_filter]
  rfl

/-- The left side of Proposition 5.9 as a doubly filtered `paperSum`. -/
theorem paperSum_primitiveSeparatedChainWeight {t : PlaneTree} {m : ℕ}
    (mu : Multiplicities t) (z : HeppLeaf t → Fin 4 → ℤ) :
    paperSum (M := m) (leafMultiplicity mu)
        (primitiveSeparatedChainWeight (m := m) z) =
      paperSumFiltered (M := m) (leafMultiplicity mu)
        (fun w => NoProperLeafBlock w ∧ NoAdjacentEqual w)
        (heppChainWeight z) := by
  unfold paperSum paperSumFiltered wordSum wordSumFiltered
  congr 1
  rw [Finset.sum_filter]
  rfl

/-- The left side of Proposition 5.10 as a filtered `paperSum`. -/
theorem paperSum_singleScaleChainWeight {t : PlaneTree} {m : ℕ}
    (mu : Multiplicities t) (z : HeppLeaf t → Fin 4 → ℤ)
    (O : Finset (AdjacentIndex m)) :
    paperSum (M := m) (leafMultiplicity mu)
        (singleScaleChainWeight (m := m) z O) =
      paperSumFiltered (M := m) (leafMultiplicity mu)
        (NoAdjacentOutside O) (heppChainWeightExcept z O) := by
  unfold paperSum paperSumFiltered wordSum wordSumFiltered
  congr 1
  rw [Finset.sum_filter]
  rfl

end
end Anderson4D
