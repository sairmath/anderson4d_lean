import Anderson4D.HeppTree.SubtreeCollapse
import Anderson4D.PermSum.Statements

/-!
# Transport of skipped branch sets through contraction

The induction hypothesis on the contracted tree sums over its non-root branch
sets `W`.  Equation (5.46) lifts such a set back to the original tree and,
only when `s = 1`, inserts the collapsed branch `r`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree

/-- The retained-vertex inclusion as an embedding. -/
def contractVertexEmbedding {t : PlaneTree} {p : Pos}
    (hp : IsPos t p) :
    VPos (contractAt t p) ↪ VPos t where
  toFun := contractVertex hp
  inj' := by
    intro v w h
    apply Subtype.ext
    change (contractVertex hp v).1 = (contractVertex hp w).1
    exact congrArg Subtype.val h

/-- Lift a finite vertex set from the contracted tree to the original tree. -/
def liftContractFinset {t : PlaneTree} {p : Pos}
    (hp : IsPos t p) (W : Finset (VPos (contractAt t p))) :
    Finset (VPos t) :=
  W.map (contractVertexEmbedding hp)

@[simp] theorem card_liftContractFinset
    {t : PlaneTree} {p : Pos} (hp : IsPos t p)
    (W : Finset (VPos (contractAt t p))) :
    (liftContractFinset hp W).card = W.card := by
  simp [liftContractFinset]

@[simp] theorem mem_liftContractFinset_iff
    {t : PlaneTree} {p : Pos} (hp : IsPos t p)
    (W : Finset (VPos (contractAt t p))) (v : VPos t) :
    v ∈ liftContractFinset hp W ↔
      ∃ w ∈ W, contractVertex hp w = v := by
  simp [liftContractFinset, contractVertexEmbedding]

/-- A contracted non-root branch lifts to an original non-root branch. -/
theorem contractVertex_mem_nonrootBranches
    {t : PlaneTree} {p : Pos} (hp : IsPos t p)
    {v : VPos (contractAt t p)}
    (hv : v ∈ nonrootBranches (contractAt t p)) :
    contractVertex hp v ∈ nonrootBranches t := by
  have hvdata := Finset.mem_erase.mp hv
  have hvroot : v ≠ rootV (contractAt t p) := hvdata.1
  have hvbranch : v ∈ BranchNodes (contractAt t p) := hvdata.2
  have hvp : v.1 ≠ p := by
    intro h
    have hprefix :
        p <+: v.1 := by
      rw [h]
    exact
      (not_prefix_of_mem_BranchNodes_contractAt hp v hvbranch)
        hprefix
  have hbranch :
      contractVertex hp v ∈ BranchNodes t :=
    (mem_BranchNodes_contractVertex_iff_of_ne hp v hvp).mp
      hvbranch
  apply Finset.mem_erase.mpr
  refine ⟨?_, hbranch⟩
  intro hroot
  apply hvroot
  apply Subtype.ext
  have hval := congrArg Subtype.val hroot
  simpa [contractVertex, rootV] using hval

/-- Lifting preserves the non-root-branch subset condition. -/
theorem liftContractFinset_subset_nonrootBranches
    {t : PlaneTree} {p : Pos} (hp : IsPos t p)
    {W : Finset (VPos (contractAt t p))}
    (hW : W ⊆ nonrootBranches (contractAt t p)) :
    liftContractFinset hp W ⊆ nonrootBranches t := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ :=
    (mem_liftContractFinset_iff hp W v).mp hv
  exact contractVertex_mem_nonrootBranches hp (hW hw)

/-- The collapsed root is not among the lifted contracted branches. -/
theorem not_mem_liftContractFinset_of_subset_nonrootBranches
    {t : PlaneTree} (r : VPos t)
    {W : Finset (VPos (contractAt t r.1))}
    (hW : W ⊆ nonrootBranches (contractAt t r.1)) :
    r ∉ liftContractFinset r.2 W := by
  intro hr
  obtain ⟨w, hw, hwr⟩ :=
    (mem_liftContractFinset_iff r.2 W r).mp hr
  have hwbranch :
      w ∈ BranchNodes (contractAt t r.1) :=
    (Finset.mem_erase.mp (hW hw)).2
  have houtside :=
    not_prefix_of_mem_BranchNodes_contractAt r.2 w hwbranch
  apply houtside
  have hval := congrArg Subtype.val hwr
  change w.1 = r.1 at hval
  rw [hval]

/-- Paper's set `W'`: insert `r` exactly in the one-cut case. -/
def liftWPrime {t : PlaneTree} (r : VPos t) (s : ℕ)
    (W : Finset (VPos (contractAt t r.1))) :
    Finset (VPos t) :=
  if s = 1 then insert r (liftContractFinset r.2 W)
  else liftContractFinset r.2 W

/-- Exact cardinality ledger for `W ↦ W'`. -/
theorem card_liftWPrime
    {t : PlaneTree} (r : VPos t) (s : ℕ)
    (W : Finset (VPos (contractAt t r.1)))
    (hW : W ⊆ nonrootBranches (contractAt t r.1)) :
    (liftWPrime r s W).card =
      if s = 1 then W.card + 1 else W.card := by
  by_cases hs : s = 1
  · simp [liftWPrime, hs,
      not_mem_liftContractFinset_of_subset_nonrootBranches r hW,
      Nat.add_comm]
  · simp [liftWPrime, hs]

/-- The lifted set is a valid original non-root branch set whenever the
collapsed root itself is non-root. -/
theorem liftWPrime_subset_nonrootBranches
    {t : PlaneTree} (r : VPos t)
    (hr : r ∈ nonrootBranches t) (s : ℕ)
    {W : Finset (VPos (contractAt t r.1))}
    (hW : W ⊆ nonrootBranches (contractAt t r.1)) :
    liftWPrime r s W ⊆ nonrootBranches t := by
  by_cases hs : s = 1
  · simp only [liftWPrime, hs, if_pos, Finset.insert_subset_iff]
    exact ⟨hr, liftContractFinset_subset_nonrootBranches r.2 hW⟩
  · simp only [liftWPrime, hs]
    exact liftContractFinset_subset_nonrootBranches r.2 hW

end Anderson4D
