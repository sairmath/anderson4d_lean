import Anderson4D.PermSum.CollapseData

/-!
# Nonempty leaf carriers in the subtree-collapse step

The collapse coordinates use the sum alphabet
`InsideLeaf r ⊕ OutsideLeaf r`.  For a proper subtree of a tree whose root
branches, both summands are inhabited.  This file proves that structural fact
and records the elementary occurrence consequence of membership in
`validWords`.
-/

namespace Anderson4D

open PlaneTree

set_option warningAsError true
set_option autoImplicit false

private theorem one_le_leafCount_collapseExistence (t : PlaneTree) :
    1 ≤ t.leafCount := by
  obtain ⟨cs⟩ := t
  exact le_max_left 1 (leafCountList cs)

private theorem length_le_leafCountList :
    ∀ cs : List PlaneTree, cs.length ≤ leafCountList cs
  | [] => by simp [leafCountList]
  | c :: cs => by
      have hc := one_le_leafCount_collapseExistence c
      have hcs := length_le_leafCountList cs
      simp only [List.length_cons, leafCountList]
      omega

/-- A tree whose root is a branch node has at least two leaves. -/
theorem two_le_leafCount_of_root_mem_BranchNodes
    (t : PlaneTree) (hroot : rootV t ∈ BranchNodes t) :
    2 ≤ t.leafCount := by
  obtain ⟨cs⟩ := t
  have hchildren : 2 ≤ cs.length := by
    simpa [rootV, childCount] using (mem_BranchNodes_iff.mp hroot)
  have hle : cs.length ≤ leafCountList cs :=
    length_le_leafCountList cs
  simp only [leafCount]
  omega

/-- Contracting a proper rooted subtree preserves the branching root of the
ambient tree. -/
theorem root_mem_BranchNodes_contractAt_of_ne
    {t : PlaneTree} (r : VPos t)
    (hr : r ≠ rootV t) (hroot : rootV t ∈ BranchNodes t) :
    rootV (contractAt t r.1) ∈ BranchNodes (contractAt t r.1) := by
  rw [mem_BranchNodes_iff]
  have hpath : ([] : Pos) ≠ r.1 := by
    intro h
    apply hr
    apply Subtype.ext
    simpa [rootV] using h.symm
  rw [childCount_contractAt_eq_of_ne r.2 (rootV (contractAt t r.1)).2 hpath]
  exact mem_BranchNodes_iff.mp hroot

/-- Every rooted subtree contains an original leaf below its root. -/
theorem nonempty_insideLeaf {t : PlaneTree} (r : VPos t) :
    Nonempty (InsideLeaf r) := by
  have hcard :
      0 < Fintype.card (HeppLeaf (subtreeAt t r.1)) := by
    rw [Fintype.card_coe, card_Leaves_eq_leafCount]
    exact one_le_leafCount_collapseExistence _
  exact Nonempty.map (restrictLeafEquiv r)
    (Fintype.card_pos_iff.mp hcard)

/-- A proper rooted subtree of a tree whose root branches leaves at least one
original leaf outside it. -/
theorem nonempty_outsideLeaf_of_ne_root
    {t : PlaneTree} (r : VPos t)
    (hr : r ≠ rootV t) (hroot : rootV t ∈ BranchNodes t) :
    Nonempty (OutsideLeaf r) := by
  have hroot' :
      rootV (contractAt t r.1) ∈ BranchNodes (contractAt t r.1) :=
    root_mem_BranchNodes_contractAt_of_ne r hr hroot
  have htwo :
      2 ≤ Fintype.card (HeppLeaf (contractAt t r.1)) := by
    rw [Fintype.card_coe, card_Leaves_eq_leafCount]
    exact two_le_leafCount_of_root_mem_BranchNodes _ hroot'
  have hcard :
      Fintype.card (HeppLeaf (contractAt t r.1)) =
        1 + Fintype.card (OutsideLeaf r) := by
    rw [Fintype.card_congr (contractLeafSumEquiv r)]
    simp
  have hout : 0 < Fintype.card (OutsideLeaf r) := by
    omega
  exact Fintype.card_pos_iff.mp hout

/-- A positive prescribed multiplicity forces the corresponding letter to
occur in every valid word. -/
theorem exists_eq_of_mem_validWords_of_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    {M : ℕ} (mult : α → ℕ) (w : Fin M → α)
    (hw : w ∈ validWords mult) (a : α) (ha : 0 < mult a) :
    ∃ i, w i = a := by
  have hfiber :
      (Finset.univ.filter fun i => w i = a).card = mult a :=
    (Finset.mem_filter.mp hw).2 a
  have hpos :
      0 < (Finset.univ.filter fun i => w i = a).card := by
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  exact ⟨i, (Finset.mem_filter.mp hi).2⟩

end Anderson4D
