import Anderson4D.PermSum.CollapseData

/-!
# Scale-ratio transport through restriction and contraction

The markings constructed in `CollapseData` preserve branch scales.  This
module records the corresponding parent-ratio identities used in the
factor audit (5.45)--(5.46).
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree

/-- The root scale of the restricted subtree is the original scale at the
selected branch. -/
@[simp] theorem scaleN_restrictMarking_root
    {t : PlaneTree} (Nm : HeppMarking t) (r : VPos t) :
    scaleN (restrictMarking Nm r) (rootV (subtreeAt t r.1)) =
      scaleN Nm r := by
  rw [scaleN_restrictMarking, subtreeVertex_root]

/-- Parent ratios of non-root subtree branches are unchanged. -/
theorem parentScaleRatio_restrictMarking
    {t : PlaneTree} (Nm : HeppMarking t) (r : VPos t)
    (v : VPos (subtreeAt t r.1))
    (hv : v ∈ nonrootBranches (subtreeAt t r.1)) :
    parentScaleRatio (restrictMarking Nm r) v =
      parentScaleRatio Nm (subtreeVertex r v) := by
  have hvne :
      v ≠ rootV (subtreeAt t r.1) :=
    (Finset.mem_erase.mp hv).1
  unfold parentScaleRatio
  rw [scaleN_restrictMarking, scaleN_restrictMarking,
    parentV_subtreeVertex r v hvne]

/-- Parent ratios of all contracted vertices are unchanged.  Mathematical
uses specialize this to contracted non-root branches. -/
@[simp] theorem parentScaleRatio_contractMarking
    {t : PlaneTree} (Nm : HeppMarking t) (r : VPos t)
    (v : VPos (contractAt t r.1)) :
    parentScaleRatio (contractMarking Nm r) v =
      parentScaleRatio Nm (contractVertex r.2 v) := by
  unfold parentScaleRatio
  rw [scaleN_contractMarking, scaleN_contractMarking,
    parentV_contractVertex]

/-- A non-root branch in the restricted subtree maps to an original non-root
branch. -/
theorem subtreeVertex_mem_nonrootBranches
    {t : PlaneTree} (r : VPos t)
    {v : VPos (subtreeAt t r.1)}
    (hv : v ∈ nonrootBranches (subtreeAt t r.1)) :
    subtreeVertex r v ∈ nonrootBranches t := by
  have hvdata := Finset.mem_erase.mp hv
  have hvbranch :
      subtreeVertex r v ∈ BranchNodes t :=
    (mem_BranchNodes_subtreeVertex_iff r v).mp hvdata.2
  apply Finset.mem_erase.mpr
  refine ⟨?_, hvbranch⟩
  intro hroot
  apply hvdata.1
  apply Subtype.ext
  have hval := congrArg Subtype.val hroot
  have happ : r.1 ++ v.1 = [] := by
    simpa [subtreeVertex, rootV] using hval
  exact (List.append_eq_nil_iff.mp happ).2

/-- The restricted subtree's non-root branches embed in the original branch
set, preserving address order and scale ratios. -/
def subtreeNonrootBranchEmbedding
    {t : PlaneTree} (r : VPos t) :
    ↥(nonrootBranches (subtreeAt t r.1)) ↪
      ↥(nonrootBranches t) where
  toFun v :=
    ⟨subtreeVertex r v.1,
      subtreeVertex_mem_nonrootBranches r v.2⟩
  inj' := by
    intro v w h
    apply Subtype.ext
    apply subtreeVertex_injective r
    exact congrArg Subtype.val h

end Anderson4D
