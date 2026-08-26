import Anderson4D.PermSum.MergeRuns
import Anderson4D.PermSum.Statements

/-!
# Run merging and the paper's chain weight

This file connects the list-level run-merging API to the exact adjacent-index
product used in Propositions 5.7 and 5.9.  It verifies the observation before
paper (5.35): merging a constant run does not change the inverse-square chain
weight, because every removed internal edge has weight one.
-/

namespace Anderson4D

open scoped BigOperators
noncomputable section

section Indexed

variable {α R : Type*}

/-- The left endpoint associated with an index in a chain of length `m`. -/
def chainLeftIndex {m : ℕ} (i : Fin m.pred) : Fin m :=
  ⟨i.1, lt_of_lt_of_le i.2 (Nat.pred_le m)⟩

/-- The right endpoint associated with an index in a chain of length `m`. -/
def chainRightIndex {m : ℕ} (i : Fin m.pred) : Fin m :=
  have hm : m ≠ 0 := by
    intro hm
    subst m
    exact Fin.elim0 i
  ⟨i.1 + 1, lt_of_le_of_lt (Nat.succ_le_of_lt i.2) (Nat.pred_lt hm)⟩

/-- Fin-indexed form of a consecutive-edge product. -/
def indexedChainProduct [CommMonoid R] {m : ℕ}
    (edge : α → α → R) (w : Fin m → α) : R :=
  ∏ i : Fin m.pred, edge (w (chainLeftIndex i)) (w (chainRightIndex i))

/-- List and Fin-indexed consecutive-edge products agree. -/
theorem listChainProduct_ofFn [CommMonoid R] :
    ∀ {m : ℕ} (edge : α → α → R) (w : Fin m → α),
      listChainProduct edge (List.ofFn w) = indexedChainProduct edge w
  | 0, edge, w => by simp [listChainProduct, indexedChainProduct]
  | 1, edge, w => by simp [listChainProduct, indexedChainProduct]
  | m + 2, edge, w => by
      simp only [List.ofFn_succ, listChainProduct]
      change _ = ∏ i : Fin (m + 1),
        edge (w ⟨i.1, by omega⟩) (w ⟨i.1 + 1, by omega⟩)
      rw [Fin.prod_univ_succ]
      have ih := listChainProduct_ofFn edge (fun i : Fin (m + 1) => w i.succ)
      simp only [List.ofFn_succ] at ih
      rw [ih]
      simp only [indexedChainProduct]
      congr 1

/-- The paper's adjacency-index carrier is canonically `Fin (m-1)`. -/
def adjacentIndexEquiv (m : ℕ) : AdjacentIndex m ≃ Fin m.pred where
  toFun j :=
    ⟨j.1.1, Nat.lt_of_succ_le (Nat.le_pred_of_lt j.2)⟩
  invFun i :=
    have hi : i.1 + 1 < m := by
      simpa [Nat.pred_eq_sub_one] using Nat.lt_sub_iff_add_lt.mp i.2
    ⟨⟨i.1, lt_trans (Nat.lt_succ_self _) hi⟩, hi⟩
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    rfl
  right_inv i := by
    apply Fin.ext
    rfl

theorem heppChainWeight_eq_indexed {t : PlaneTree} {m : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ) (w : Fin m → HeppLeaf t) :
    heppChainWeight z w =
      indexedChainProduct latticeEdgeWeight (fun i => z (w i)) := by
  unfold heppChainWeight indexedChainProduct
  let e := adjacentIndexEquiv m
  let g : Fin m.pred → ℝ := fun i =>
    latticeEdgeWeight (z (w (chainLeftIndex i)))
      (z (w (chainRightIndex i)))
  calc
    (∏ j : AdjacentIndex m,
        latticeEdgeWeight (z (w j.1)) (z (w (adjacentSucc j)))) =
        ∏ j : AdjacentIndex m, g (e j) := by
      apply Finset.prod_congr rfl
      intro j _
      rfl
    _ = ∏ i : Fin m.pred, g i := Equiv.prod_comp e g

theorem heppChainWeight_eq_listChainProduct {t : PlaneTree} {m : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ) (w : Fin m → HeppLeaf t) :
    heppChainWeight z w =
      listChainProduct latticeEdgeWeight (List.ofFn fun i => z (w i)) := by
  rw [heppChainWeight_eq_indexed, listChainProduct_ofFn]

end Indexed

@[simp]
theorem latticeEdgeWeight_self (x : Fin 4 → ℤ) :
    latticeEdgeWeight x x = 1 := by
  simp [latticeEdgeWeight, znorm]

/-- Exact weight invariance under merging all adjacent equal leaves. -/
theorem latticePointChainProduct_mergeEqualRuns {α : Type*} [DecidableEq α]
    (z : α → Fin 4 → ℤ) (l : List α) :
    listChainProduct latticeEdgeWeight (mergeEqualRuns (l.map z)) =
      listChainProduct latticeEdgeWeight (l.map z) := by
  rw [listChainProduct_mergeEqualRuns]
  intro x
  exact latticeEdgeWeight_self x

/-- Paper (5.35): merge equal *leaf letters* first, then evaluate their
lattice locations.  The inverse-square chain weight is unchanged. -/
theorem latticeChainProduct_mergeLetterRuns {α : Type*} [DecidableEq α]
    (z : α → Fin 4 → ℤ) (l : List α) :
    listChainProduct latticeEdgeWeight ((mergeEqualRuns l).map z) =
      listChainProduct latticeEdgeWeight (l.map z) := by
  calc
    listChainProduct latticeEdgeWeight ((mergeEqualRuns l).map z) =
        listChainProduct (fun a b => latticeEdgeWeight (z a) (z b))
          (mergeEqualRuns l) :=
      listChainProduct_map latticeEdgeWeight z (mergeEqualRuns l)
    _ = listChainProduct (fun a b => latticeEdgeWeight (z a) (z b)) l := by
      apply listChainProduct_mergeEqualRuns
      intro a
      exact latticeEdgeWeight_self (z a)
    _ = listChainProduct latticeEdgeWeight (l.map z) :=
      (listChainProduct_map latticeEdgeWeight z l).symm

end
end Anderson4D
