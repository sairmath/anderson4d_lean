import Anderson4D.HeppTree.Admissible

/-!
# Cardinality of the leaf carrier

`PlaneTree.leafCount` is the recursive paper-facing number of leaves, while
`PlaneTree.Leaves` is the finite subtype used by the Lean implementation.
This file proves that the two notions agree for every plane tree, including
invalid trees with unary vertices.
-/

namespace Anderson4D

open scoped BigOperators

namespace PlaneTree

private theorem leafCard_childCount_childV {cs : List PlaneTree}
    (i : Fin cs.length) (v : VPos (cs.get i)) :
    childCount (node cs) (childV i v).1 =
      childCount (cs.get i) v.1 := by
  rw [childV_val]
  simp [childCount, i.2, List.get_eq_getElem]

private theorem card_Leaves_eq_indicator_sum (t : PlaneTree) :
    (Leaves t).card =
      ∑ v : VPos t, if childCount t v.1 = 0 then 1 else 0 := by
  classical
  rw [Leaves, Finset.card_eq_sum_ones]
  simp

private theorem one_le_leafCount (t : PlaneTree) :
    1 ≤ t.leafCount := by
  obtain ⟨cs⟩ := t
  exact le_max_left 1 (leafCountList cs)

/-- The sum of the recursive leaf counts of the children is the forest leaf
count. -/
private theorem sum_leafCount_get_eq_leafCountList (cs : List PlaneTree) :
    (∑ i : Fin cs.length, (cs.get i).leafCount) = leafCountList cs := by
  rw [leafCountList_eq_map, map_eq_ofFn, List.sum_ofFn]

/-- The finite leaf carrier has exactly the recursive paper-facing leaf
count.  No Hepp-validity assumption is needed. -/
theorem card_Leaves_eq_leafCount :
    ∀ t : PlaneTree, (Leaves t).card = t.leafCount
  | node cs => by
      let f : VPos (node cs) → ℕ :=
        fun v => if childCount (node cs) v.1 = 0 then 1 else 0
      let g : Option ((i : Fin cs.length) × VPos (cs.get i)) → ℕ
        | none => if cs.length = 0 then 1 else 0
        | some ⟨i, v⟩ =>
            if childCount (cs.get i) v.1 = 0 then 1 else 0
      have hfg (v : VPos (node cs)) :
          f v = g (vposNodeEquiv cs v) := by
        rcases vpos_node_cases_or v with rfl | ⟨i, w, rfl⟩
        · rfl
        · simpa [f, g] using congrArg
            (fun n => if n = 0 then 1 else 0)
            (leafCard_childCount_childV i w)
      rw [card_Leaves_eq_indicator_sum]
      change (∑ v : VPos (node cs), f v) =
        max 1 (leafCountList cs)
      rw [show (∑ v : VPos (node cs), f v) = ∑ x, g x by
        exact Fintype.sum_equiv (vposNodeEquiv cs) f g hfg]
      rw [Fintype.sum_option]
      change (if cs.length = 0 then 1 else 0) +
          (∑ x : (i : Fin cs.length) × VPos (cs.get i),
            if childCount (cs.get x.1) x.2.1 = 0 then 1 else 0) =
        max 1 (leafCountList cs)
      rw [Fintype.sum_sigma]
      have hchildren :
          (∑ i : Fin cs.length,
              ∑ v : VPos (cs.get i),
                if childCount (cs.get i) v.1 = 0 then 1 else 0) =
            ∑ i : Fin cs.length, (cs.get i).leafCount := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← card_Leaves_eq_indicator_sum]
        exact card_Leaves_eq_leafCount (cs.get i)
      rw [hchildren, sum_leafCount_get_eq_leafCountList]
      cases cs with
      | nil =>
          simp [leafCountList]
      | cons c cs =>
          simp only [List.length_cons, Nat.succ_ne_zero, if_false,
            zero_add, leafCountList]
          rw [max_eq_right]
          exact le_trans (one_le_leafCount c)
            (Nat.le_add_right (leafCount c) (leafCountList cs))
termination_by t => sizeOf t
decreasing_by
  have hmem := List.sizeOf_lt_of_mem (List.get_mem cs i)
  simp only [node.sizeOf_spec]
  omega

/-- Lower-case compatibility spelling used by the Hepp-tree cardinality lemmas. -/
theorem card_leaves_eq_leafCount (t : PlaneTree) :
    (Leaves t).card = t.leafCount :=
  card_Leaves_eq_leafCount t

/-! ## The root-subtree bridge -/

/-- Every leaf lies under the root. -/
@[simp]
theorem leavesUnder_root_eq_univ (t : PlaneTree) :
    leavesUnder (rootV t) =
      (Finset.univ : Finset {w // w ∈ Leaves t}) := by
  ext l
  simp [leavesUnder, rootV]

/-- The leaves below the root are all paper leaves. -/
@[simp]
theorem card_leavesUnder_root (t : PlaneTree) :
    (leavesUnder (rootV t)).card = t.leafCount := by
  rw [leavesUnder_root_eq_univ, Finset.card_univ]
  change Fintype.card ↥(Leaves t) = t.leafCount
  rw [Fintype.card_coe]
  exact card_Leaves_eq_leafCount t

end PlaneTree

end Anderson4D
