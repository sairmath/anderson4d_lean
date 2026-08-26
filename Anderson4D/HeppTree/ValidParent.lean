import Anderson4D.HeppTree.Basic

/-!
# Parents in valid Hepp trees

In a valid `PlaneTree`, every internal vertex is branching: unary vertices
are excluded by `PlaneTree.isValid`.  Consequently the parent of every
non-root vertex is a branching vertex.
-/

namespace Anderson4D

open PlaneTree

private theorem vp_isValid_get {cs : List PlaneTree}
    (hcs : isValidList cs = true) (i : Fin cs.length) :
    (cs.get i).isValid = true := by
  rw [isValidList_eq_map] at hcs
  simp only [List.all_eq_true, id_eq] at hcs
  exact hcs _ (List.mem_map.mpr ⟨cs.get i, List.get_mem cs i, rfl⟩)

private theorem vp_isValidList_of_node {cs : List PlaneTree}
    (h : (node cs).isValid = true) :
    isValidList cs = true := by
  simp only [isValid, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact h.2

private theorem vp_root_childCount_ne_one {cs : List PlaneTree}
    (h : (node cs).isValid = true) :
    childCount (node cs) [] ≠ 1 := by
  simp only [isValid, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  simpa [childCount] using h.1

/-- Every valid position of a valid tree has either zero or at least two
children. -/
private theorem vp_childCount_ne_one {t : PlaneTree} {p : Pos}
    (ht : t.isValid = true) (hp : IsPos t p) :
    childCount t p ≠ 1 := by
  induction p generalizing t with
  | nil =>
      obtain ⟨cs⟩ := t
      exact vp_root_childCount_ne_one ht
  | cons i p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨hi, hp'⟩ := isPos_cons_iff.mp hp
      have hchild : (cs.get ⟨i, hi⟩).isValid = true :=
        vp_isValid_get (vp_isValidList_of_node ht) ⟨i, hi⟩
      have hne := ih hchild hp'
      simpa [childCount, hi] using hne

/-- If appending child index `i` to a position gives a valid position, then
`i` is below the child count at the original position. -/
private theorem vp_lt_childCount_of_isPos_append {t : PlaneTree}
    {p : Pos} {i : ℕ} (h : IsPos t (p ++ [i])) :
    i < childCount t p := by
  induction p generalizing t with
  | nil =>
      obtain ⟨cs⟩ := t
      have h' : IsPos (node cs) [i] := by simpa using h
      simpa [childCount] using isPos_cons_lt h'
  | cons a p ih =>
      obtain ⟨cs⟩ := t
      have h' : IsPos (node cs) (a :: (p ++ [i])) := by simpa using h
      obtain ⟨ha, hp⟩ := isPos_cons_iff.mp h'
      have hi := ih hp
      simpa [childCount, ha] using hi

private theorem vp_parent_childCount_pos {t : PlaneTree} (v : VPos t)
    (hne : v ≠ rootV t) :
    0 < childCount t (parentV v).1 := by
  have hpne : v.1 ≠ [] := by
    intro hp
    apply hne
    exact Subtype.ext hp
  have hpath : v.1.dropLast ++ [v.1.getLast hpne] = v.1 :=
    List.dropLast_append_getLast hpne
  have hpos : IsPos t (v.1.dropLast ++ [v.1.getLast hpne]) := by
    rw [hpath]
    exact v.2
  have hi := vp_lt_childCount_of_isPos_append hpos
  change 0 < childCount t v.1.dropLast
  omega

/-- In a valid Hepp tree, the parent of every non-root vertex is branching.
This is the general form used by marking monotonicity and automorphism
arguments. -/
theorem parentV_mem_BranchNodes_of_isValid {t : PlaneTree}
    (ht : t.isValid = true) {v : VPos t} (hne : v ≠ rootV t) :
    parentV v ∈ BranchNodes t := by
  rw [BranchNodes, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hpos := vp_parent_childCount_pos v hne
  have hne_one := vp_childCount_ne_one ht (parentV v).2
  omega

/-- Paper-facing specialization: the parent of a non-root branching vertex
in a valid Hepp tree is branching. -/
theorem parentV_mem_BranchNodes_of_branch {t : PlaneTree}
    (ht : t.isValid = true) {v : VPos t} (_hv : v ∈ BranchNodes t)
    (hne : v ≠ rootV t) :
    parentV v ∈ BranchNodes t :=
  parentV_mem_BranchNodes_of_isValid ht hne

end Anderson4D
