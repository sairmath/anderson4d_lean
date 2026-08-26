import Anderson4D.HeppTree.ScaleGeometric

/-!
# Branch excess and the final geometric exponent bound

For a valid Hepp tree, the sum of `childCount - 1` over branching vertices is
exactly `leafCount - 1`.  Since a branching vertex has at least two children,
its child count is at most twice this excess.  Combined with the ancestor-scale
geometric sum from `ScaleGeometric`, this proves the combinatorial part of
paper equation (5.27).
-/

namespace Anderson4D

open scoped BigOperators

namespace PlaneTree

mutual

/-- Recursive sum of `childCount - 1` over a tree. -/
def branchExcess : PlaneTree → ℕ
  | node cs => cs.length - 1 + branchExcessList cs

/-- Forest companion of `branchExcess`. -/
def branchExcessList : List PlaneTree → ℕ
  | [] => 0
  | c :: cs => branchExcess c + branchExcessList cs

end

private theorem branchExcess_childCount_childV {cs : List PlaneTree}
    (i : Fin cs.length) (v : VPos (cs.get i)) :
    childCount (node cs) (childV i v).1 =
      childCount (cs.get i) v.1 := by
  rw [childV_val]
  simp [childCount, i.2, List.get_eq_getElem]

mutual

/-- Euler identity for a valid rooted tree, in subtraction-free form. -/
theorem branchExcess_add_one_eq_leafCount :
    ∀ t : PlaneTree, t.isValid = true →
      branchExcess t + 1 = t.leafCount
  | node cs, ht => by
      simp only [isValid, Bool.and_eq_true, bne_iff_ne, ne_eq] at ht
      obtain ⟨hlen, hvalid⟩ := ht
      cases cs with
      | nil =>
          simp [branchExcess, branchExcessList, leafCount, leafCountList]
      | cons c cs =>
          have hforest :=
            branchExcessList_add_length_eq_leafCountList (c :: cs) hvalid
          have hlen2 : 2 ≤ (c :: cs).length := by
            simp only [List.length_cons] at hlen ⊢
            omega
          simp only [branchExcess, leafCount]
          have hleaf :
              max 1 (leafCountList (c :: cs)) =
                leafCountList (c :: cs) := by
            rw [max_eq_right]
            omega
          rw [hleaf]
          omega

/-- Forest form of the Euler identity. -/
theorem branchExcessList_add_length_eq_leafCountList :
    ∀ cs : List PlaneTree, isValidList cs = true →
      branchExcessList cs + cs.length = leafCountList cs
  | [], _ => rfl
  | c :: cs, ht => by
      simp only [isValidList, Bool.and_eq_true] at ht
      obtain ⟨hc, hcs⟩ := ht
      have hc' := branchExcess_add_one_eq_leafCount c hc
      have hcs' :=
        branchExcessList_add_length_eq_leafCountList cs hcs
      simp only [branchExcessList, leafCountList, List.length_cons]
      omega

end

/-- The subtraction form of the valid-tree Euler identity. -/
theorem branchExcess_eq_leafCount_sub_one (t : PlaneTree)
    (ht : t.isValid = true) :
    branchExcess t = t.leafCount - 1 := by
  have h := branchExcess_add_one_eq_leafCount t ht
  omega

mutual

/-- The recursive excess is the sum of `childCount - 1` over all vertices. -/
theorem sum_childCount_sub_one_eq_branchExcess :
    ∀ t : PlaneTree,
      (∑ v : VPos t, (childCount t v.1 - 1)) = branchExcess t
  | node cs => by
      let f : VPos (node cs) → ℕ :=
        fun v => childCount (node cs) v.1 - 1
      let g : Option ((i : Fin cs.length) × VPos (cs.get i)) → ℕ
        | none => cs.length - 1
        | some ⟨i, v⟩ => childCount (cs.get i) v.1 - 1
      have hfg (v : VPos (node cs)) :
          f v = g (vposNodeEquiv cs v) := by
        rcases vpos_node_cases_or v with rfl | ⟨i, w, rfl⟩
        · rfl
        · simpa [f, g] using congrArg (fun n => n - 1)
            (branchExcess_childCount_childV i w)
      change (∑ v : VPos (node cs),
          (childCount (node cs) v.1 - 1)) =
        cs.length - 1 + branchExcessList cs
      rw [show (∑ v : VPos (node cs),
          (childCount (node cs) v.1 - 1)) =
            ∑ x, g x by
          simpa only [f] using
            Fintype.sum_equiv (vposNodeEquiv cs) f g hfg]
      rw [Fintype.sum_option]
      change cs.length - 1 +
          (∑ x : (i : Fin cs.length) × VPos (cs.get i),
            (childCount (cs.get x.1) x.2.1 - 1)) =
        cs.length - 1 + branchExcessList cs
      rw [sum_childCount_sub_one_sigma_eq_branchExcessList cs]

/-- Forest companion of `sum_childCount_sub_one_eq_branchExcess`. -/
theorem sum_childCount_sub_one_sigma_eq_branchExcessList :
    ∀ cs : List PlaneTree,
      (∑ x : (i : Fin cs.length) × VPos (cs.get i),
        (childCount (cs.get x.1) x.2.1 - 1)) =
          branchExcessList cs
  | [] => by simp [branchExcessList]
  | c :: cs => by
      rw [Fintype.sum_sigma]
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      change
        (∑ v : VPos c, (childCount c v.1 - 1)) +
          (∑ i : Fin cs.length, ∑ v : VPos (cs.get i),
            (childCount (cs.get i) v.1 - 1)) =
          branchExcess c + branchExcessList cs
      rw [sum_childCount_sub_one_eq_branchExcess c]
      have ih :=
        sum_childCount_sub_one_sigma_eq_branchExcessList cs
      rw [Fintype.sum_sigma] at ih
      rw [ih]

end

/-- Non-branching vertices contribute zero to the excess sum. -/
theorem sum_branchNodes_childCount_sub_one_eq_branchExcess (t : PlaneTree) :
    (∑ v ∈ BranchNodes t, (childCount t v.1 - 1)) = branchExcess t := by
  rw [← sum_childCount_sub_one_eq_branchExcess t]
  rw [BranchNodes]
  have hsub :
      (Finset.univ.filter fun v : VPos t => 2 ≤ childCount t v.1) ⊆
        (Finset.univ : Finset (VPos t)) :=
    Finset.filter_subset _ _
  exact Finset.sum_subset hsub (by
    intro v _ hv
    have hlt : childCount t v.1 < 2 := by
      simpa using hv
    omega)

/-- In a valid tree, the sum of branch child counts is at most twice the
total branch excess. -/
theorem sum_branchNodes_childCount_le_two_mul_excess (t : PlaneTree) :
    (∑ v ∈ BranchNodes t, childCount t v.1) ≤
      2 * branchExcess t := by
  calc
    (∑ v ∈ BranchNodes t, childCount t v.1) ≤
        ∑ v ∈ BranchNodes t, 2 * (childCount t v.1 - 1) := by
          apply Finset.sum_le_sum
          intro v hv
          have htwo : 2 ≤ childCount t v.1 := by
            simpa [BranchNodes] using hv
          omega
    _ = 2 * (∑ v ∈ BranchNodes t, (childCount t v.1 - 1)) := by
      simp only [Finset.mul_sum]
    _ = 2 * branchExcess t := by
      rw [sum_branchNodes_childCount_sub_one_eq_branchExcess]

/-- Valid-tree form of the branching-count estimate in paper (5.27). -/
theorem sum_branchNodes_childCount_le_two_mul_leafCount_sub_one
    (t : PlaneTree) (ht : t.isValid = true) :
    (∑ v ∈ BranchNodes t, childCount t v.1) ≤
      2 * (t.leafCount - 1) := by
  rw [← branchExcess_eq_leafCount_sub_one t ht]
  exact sum_branchNodes_childCount_le_two_mul_excess t

/-- Paper (5.27): after reordering by the lower branch vertex, the ancestor
scale ratios cost at most `2 * leafCount` in total. -/
theorem sum_childCount_mul_ancestor_ratio_le_two_mul_leafCount
    (t : PlaneTree) (ht : t.isValid = true) (Nm : HeppMarking t) :
    (∑ v ∈ BranchNodes t,
        (childCount t v.1 : ℝ) *
          (∑ u ∈ strictBranchAncestors v,
            (scaleN Nm v : ℝ) / scaleN Nm u))
      ≤ 2 * (t.leafCount : ℝ) := by
  calc
    (∑ v ∈ BranchNodes t,
        (childCount t v.1 : ℝ) *
          (∑ u ∈ strictBranchAncestors v,
            (scaleN Nm v : ℝ) / scaleN Nm u))
      ≤ ∑ v ∈ BranchNodes t, (childCount t v.1 : ℝ) :=
        Anderson4D.sum_childCount_mul_ancestor_ratio_le ht Nm
    _ ≤ 2 * (t.leafCount : ℝ) := by
      exact_mod_cast
        (le_trans
          (sum_branchNodes_childCount_le_two_mul_leafCount_sub_one t ht)
          (Nat.mul_le_mul_left 2 (Nat.sub_le t.leafCount 1)))

end PlaneTree

end Anderson4D
