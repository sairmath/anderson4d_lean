import Anderson4D.PermSum.CollapseRatios
import Anderson4D.PermSum.CollapseSkippedBranches

/-!
# Parent-scale-ratio ledger for the collapse induction

This file isolates the exact product bookkeeping in paper (5.45)--(5.46).
The original non-root branches split into the selected branch, its strict
branch descendants, and the branches retained by contraction.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## The exact branch partition -/

/-- Inclusion of every subtree vertex into the original tree. -/
def ratioSubtreeVertexEmbedding {t : PlaneTree} (r : VPos t) :
    VPos (subtreeAt t r.1) ↪ VPos t where
  toFun := subtreeVertex r
  inj' := subtreeVertex_injective r

/-- Original branches strictly below `r`, represented as a finset in the
original vertex type. -/
def liftSubtreeNonrootBranches {t : PlaneTree} (r : VPos t) :
    Finset (VPos t) :=
  (nonrootBranches (subtreeAt t r.1)).map (ratioSubtreeVertexEmbedding r)

@[simp] theorem mem_liftSubtreeNonrootBranches_iff
    {t : PlaneTree} (r : VPos t) (v : VPos t) :
    v ∈ liftSubtreeNonrootBranches r ↔
      ∃ u ∈ nonrootBranches (subtreeAt t r.1),
        subtreeVertex r u = v := by
  simp [liftSubtreeNonrootBranches, ratioSubtreeVertexEmbedding]

/-- Every lifted strict descendant branch is an original non-root branch. -/
theorem liftSubtreeNonrootBranches_subset
    {t : PlaneTree} (r : VPos t) :
    liftSubtreeNonrootBranches r ⊆ nonrootBranches t := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ :=
    (mem_liftSubtreeNonrootBranches_iff r v).mp hv
  exact subtreeVertex_mem_nonrootBranches r hu

/-- The selected root itself is not among its strict branch descendants. -/
theorem not_mem_liftSubtreeNonrootBranches
    {t : PlaneTree} (r : VPos t) :
    r ∉ liftSubtreeNonrootBranches r := by
  intro hr
  obtain ⟨u, hu, hur⟩ :=
    (mem_liftSubtreeNonrootBranches_iff r r).mp hr
  have huRoot : u = rootV (subtreeAt t r.1) := by
    apply subtreeVertex_injective r
    rw [hur, subtreeVertex_root]
  exact (Finset.mem_erase.mp hu).1 huRoot

/-- Lifted strict descendants really are weakly below `r`. -/
theorem prefix_of_mem_liftSubtreeNonrootBranches
    {t : PlaneTree} (r : VPos t) {v : VPos t}
    (hv : v ∈ liftSubtreeNonrootBranches r) :
    r.1 <+: v.1 := by
  obtain ⟨u, _hu, rfl⟩ :=
    (mem_liftSubtreeNonrootBranches_iff r v).mp hv
  exact List.prefix_append r.1 u.1

/-- A strict descendant original branch belongs to the lifted subtree
branch set. -/
theorem mem_liftSubtreeNonrootBranches_of_prefix
    {t : PlaneTree} (r : VPos t) {v : VPos t}
    (hv : v ∈ nonrootBranches t)
    (hprefix : r.1 <+: v.1) (hne : v ≠ r) :
    v ∈ liftSubtreeNonrootBranches r := by
  let d : Descendants r := ⟨v, hprefix⟩
  let u : VPos (subtreeAt t r.1) :=
    (subtreeVertexEquiv r).symm d
  have huImage : subtreeVertex r u = v := by
    change (subtreeVertexEquiv r u).1 = d.1
    exact congrArg Subtype.val
      ((subtreeVertexEquiv r).apply_symm_apply d)
  have huBranch :
      u ∈ BranchNodes (subtreeAt t r.1) := by
    apply (mem_BranchNodes_subtreeVertex_iff r u).mpr
    rw [huImage]
    exact (Finset.mem_erase.mp hv).2
  have huNeRoot : u ≠ rootV (subtreeAt t r.1) := by
    intro hu
    apply hne
    rw [← huImage, hu, subtreeVertex_root]
  apply (mem_liftSubtreeNonrootBranches_iff r v).mpr
  exact ⟨u, Finset.mem_erase.mpr ⟨huNeRoot, huBranch⟩, huImage⟩

/-- An original non-root branch outside the selected subtree is retained as
a contracted non-root branch. -/
theorem mem_liftContract_nonrootBranches_of_not_prefix
    {t : PlaneTree} (r : VPos t) {v : VPos t}
    (hv : v ∈ nonrootBranches t)
    (hprefix : ¬r.1 <+: v.1) :
    v ∈ liftContractFinset r.2
      (nonrootBranches (contractAt t r.1)) := by
  let retained : RetainedVertices t r.1 :=
    ⟨v, fun hstrict => hprefix hstrict.1⟩
  let u : VPos (contractAt t r.1) :=
    (contractVertexEquiv r.2).symm retained
  have huImage : contractVertex r.2 u = v := by
    change (contractVertexEquiv r.2 u).1 = retained.1
    exact congrArg Subtype.val
      ((contractVertexEquiv r.2).apply_symm_apply retained)
  have huNeMarker : u.1 ≠ r.1 := by
    intro hu
    apply hprefix
    rw [← huImage]
    change r.1 <+: u.1
    rw [hu]
  have huBranch :
      u ∈ BranchNodes (contractAt t r.1) := by
    exact (mem_BranchNodes_contractVertex_iff_of_ne r.2 u
      huNeMarker).mpr (Finset.mem_erase.mp hv).2
  have huNeRoot : u ≠ rootV (contractAt t r.1) := by
    intro hu
    apply (Finset.mem_erase.mp hv).1
    rw [← huImage, hu]
    apply Subtype.ext
    rfl
  apply (mem_liftContractFinset_iff r.2
    (nonrootBranches (contractAt t r.1)) v).mpr
  exact ⟨u, Finset.mem_erase.mpr ⟨huNeRoot, huBranch⟩, huImage⟩

/-- Contracted branch images cannot lie below the selected subtree root. -/
theorem not_prefix_of_mem_liftContract_nonrootBranches
    {t : PlaneTree} (r : VPos t) {v : VPos t}
    (hv : v ∈ liftContractFinset r.2
      (nonrootBranches (contractAt t r.1))) :
    ¬r.1 <+: v.1 := by
  obtain ⟨u, hu, rfl⟩ :=
    (mem_liftContractFinset_iff r.2
      (nonrootBranches (contractAt t r.1)) v).mp hv
  exact not_prefix_of_mem_BranchNodes_contractAt r.2 u
    (Finset.mem_erase.mp hu).2

/-- The strict-descendant and contraction pieces are disjoint. -/
theorem disjoint_liftSubtree_liftContract_nonrootBranches
    {t : PlaneTree} (r : VPos t) :
    Disjoint (liftSubtreeNonrootBranches r)
      (liftContractFinset r.2
        (nonrootBranches (contractAt t r.1))) := by
  rw [Finset.disjoint_left]
  intro v hvSub hvContract
  exact
    (not_prefix_of_mem_liftContract_nonrootBranches r hvContract)
      (prefix_of_mem_liftSubtreeNonrootBranches r hvSub)

/-- Exact trichotomy of original non-root branches: `r`, strict descendants
of `r`, and branches surviving contraction. -/
theorem nonrootBranches_eq_collapse_partition
    {t : PlaneTree} (r : VPos t)
    (hr : r ∈ nonrootBranches t) :
    nonrootBranches t =
      insert r (liftSubtreeNonrootBranches r) ∪
        liftContractFinset r.2
          (nonrootBranches (contractAt t r.1)) := by
  ext v
  constructor
  · intro hv
    by_cases hvr : v = r
    · simp [hvr]
    · by_cases hprefix : r.1 <+: v.1
      · exact Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_insert.mpr <| Or.inr <|
            mem_liftSubtreeNonrootBranches_of_prefix
              r hv hprefix hvr
      · exact Finset.mem_union.mpr <| Or.inr <|
          mem_liftContract_nonrootBranches_of_not_prefix
            r hv hprefix
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hr
      · exact liftSubtreeNonrootBranches_subset r hv
    · exact liftContractFinset_subset_nonrootBranches r.2
        (fun _ h => h) hv

/-! ## Finset and product reindexing -/

theorem liftContractFinset_sdiff
    {t : PlaneTree} {p : Pos} (hp : IsPos t p)
    (S W : Finset (VPos (contractAt t p))) :
    liftContractFinset hp (S \ W) =
      liftContractFinset hp S \ liftContractFinset hp W := by
  exact Finset.map_sdiff S W

theorem liftContractFinset_mono
    {t : PlaneTree} {p : Pos} (hp : IsPos t p)
    {S W : Finset (VPos (contractAt t p))}
    (h : W ⊆ S) :
    liftContractFinset hp W ⊆ liftContractFinset hp S := by
  exact Finset.map_subset_map.mpr h

/-- Reindex a product over lifted strict-descendant branches. -/
theorem prod_liftSubtreeNonrootBranches
    {t : PlaneTree} {M : Type*} [CommMonoid M]
    (r : VPos t) (f : VPos t → M) :
    (∏ v ∈ liftSubtreeNonrootBranches r, f v) =
      ∏ u ∈ nonrootBranches (subtreeAt t r.1),
        f (subtreeVertex r u) := by
  simp [liftSubtreeNonrootBranches, ratioSubtreeVertexEmbedding]

/-- Reindex a product over any lifted contracted vertex set. -/
theorem prod_liftContractFinset
    {t : PlaneTree} {p : Pos} {M : Type*} [CommMonoid M]
    (hp : IsPos t p) (W : Finset (VPos (contractAt t p)))
    (f : VPos t → M) :
    (∏ v ∈ liftContractFinset hp W, f v) =
      ∏ u ∈ W, f (contractVertex hp u) := by
  simp [liftContractFinset, contractVertexEmbedding]

/-- Exact complement partition underlying `W ↦ W'`.  If `s = 1`, the
selected branch is removed from the complement; otherwise it remains. -/
theorem nonrootBranches_sdiff_liftWPrime
    {t : PlaneTree} (r : VPos t)
    (hr : r ∈ nonrootBranches t) (s : ℕ)
    {W : Finset (VPos (contractAt t r.1))}
    (hW : W ⊆ nonrootBranches (contractAt t r.1)) :
    nonrootBranches t \ liftWPrime r s W =
      (if s = 1 then liftSubtreeNonrootBranches r
        else insert r (liftSubtreeNonrootBranches r)) ∪
      liftContractFinset r.2
        (nonrootBranches (contractAt t r.1) \ W) := by
  have hpartition :=
    nonrootBranches_eq_collapse_partition r hr
  have hsubContract :=
    disjoint_liftSubtree_liftContract_nonrootBranches r
  have hWlift :
      liftContractFinset r.2 W ⊆
        liftContractFinset r.2
          (nonrootBranches (contractAt t r.1)) :=
    liftContractFinset_mono r.2 hW
  have hrContract :
      r ∉ liftContractFinset r.2
        (nonrootBranches (contractAt t r.1)) :=
    not_mem_liftContractFinset_of_subset_nonrootBranches r
      (fun _ h => h)
  rw [hpartition, liftContractFinset_sdiff]
  by_cases hs : s = 1
  · simp only [liftWPrime, hs, if_pos]
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert]
    have hsubW :
        v ∈ liftSubtreeNonrootBranches r →
          v ∉ liftContractFinset r.2 W := by
      intro hvSub hvW
      exact (Finset.disjoint_left.mp hsubContract)
        hvSub (hWlift hvW)
    have hrW : r ∉ liftContractFinset r.2 W :=
      fun h => hrContract (hWlift h)
    constructor
    · rintro ⟨(hvr | hvSub) | hvContract, hvNot⟩
      · exact (hvNot (Or.inl hvr)).elim
      · exact Or.inl hvSub
      · exact Or.inr ⟨hvContract, fun hvW =>
          hvNot (Or.inr hvW)⟩
    · rintro (hvSub | ⟨hvContract, hvNotW⟩)
      · exact ⟨Or.inl (Or.inr hvSub), fun hvInsert =>
          hvInsert.elim
            (fun hvr => not_mem_liftSubtreeNonrootBranches r
              (hvr.symm ▸ hvSub))
            (hsubW hvSub)⟩
      · exact ⟨Or.inr hvContract, fun hvInsert =>
          hvInsert.elim
            (fun hvr => hrContract (hvr.symm ▸ hvContract))
            hvNotW⟩
  · simp only [liftWPrime, hs, if_false]
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert]
    have hsubW :
        v ∈ liftSubtreeNonrootBranches r →
          v ∉ liftContractFinset r.2 W := by
      intro hvSub hvW
      exact (Finset.disjoint_left.mp hsubContract)
        hvSub (hWlift hvW)
    have hrW : r ∉ liftContractFinset r.2 W :=
      fun h => hrContract (hWlift h)
    constructor
    · rintro ⟨(hvr | hvSub) | hvContract, hvNotW⟩
      · exact Or.inl (Or.inl hvr)
      · exact Or.inl (Or.inr hvSub)
      · exact Or.inr ⟨hvContract, hvNotW⟩
    · rintro ((hvr | hvSub) | ⟨hvContract, hvNotW⟩)
      · exact ⟨Or.inl (Or.inl hvr), hvr ▸ hrW⟩
      · exact ⟨Or.inl (Or.inr hvSub), hsubW hvSub⟩
      · exact ⟨Or.inr hvContract, hvNotW⟩

/-! ## Exact product ledgers -/

/-- Product form of the branch trichotomy. -/
theorem prod_nonrootBranches_eq_collapse_partition
    {t : PlaneTree} {M : Type*} [CommMonoid M]
    (r : VPos t) (hr : r ∈ nonrootBranches t)
    (f : VPos t → M) :
    (∏ v ∈ nonrootBranches t, f v) =
      f r *
        (∏ v ∈ liftSubtreeNonrootBranches r, f v) *
        ∏ v ∈ liftContractFinset r.2
          (nonrootBranches (contractAt t r.1)), f v := by
  have hdisjoint :
      Disjoint (insert r (liftSubtreeNonrootBranches r))
        (liftContractFinset r.2
          (nonrootBranches (contractAt t r.1))) := by
    rw [Finset.disjoint_left]
    intro v hvLeft hvRight
    rcases Finset.mem_insert.mp hvLeft with hvr | hvSub
    · exact
        (not_mem_liftContractFinset_of_subset_nonrootBranches r
          (fun _ h => h)) (by simpa [hvr] using hvRight)
    · exact
        (Finset.disjoint_left.mp
          (disjoint_liftSubtree_liftContract_nonrootBranches r))
          hvSub hvRight
  rw [nonrootBranches_eq_collapse_partition r hr,
    Finset.prod_union hdisjoint,
    Finset.prod_insert (not_mem_liftSubtreeNonrootBranches r)]

/-- Product form of the complement partition, already reindexed back to the
contracted tree on the final factor. -/
theorem prod_nonrootBranches_sdiff_liftWPrime
    {t : PlaneTree} {M : Type*} [CommMonoid M]
    (r : VPos t) (hr : r ∈ nonrootBranches t) (s : ℕ)
    {W : Finset (VPos (contractAt t r.1))}
    (hW : W ⊆ nonrootBranches (contractAt t r.1))
    (f : VPos t → M) :
    (∏ v ∈ nonrootBranches t \ liftWPrime r s W, f v) =
      (if s = 1 then
          ∏ v ∈ liftSubtreeNonrootBranches r, f v
        else
          f r * ∏ v ∈ liftSubtreeNonrootBranches r, f v) *
      ∏ u ∈ nonrootBranches (contractAt t r.1) \ W,
        f (contractVertex r.2 u) := by
  rw [nonrootBranches_sdiff_liftWPrime r hr s hW]
  have hcontractSubset :
      liftContractFinset r.2
          (nonrootBranches (contractAt t r.1) \ W) ⊆
        liftContractFinset r.2
          (nonrootBranches (contractAt t r.1)) :=
    liftContractFinset_mono r.2 Finset.sdiff_subset
  by_cases hs : s = 1
  · simp only [hs, if_pos]
    have hdisjoint :
        Disjoint (liftSubtreeNonrootBranches r)
          (liftContractFinset r.2
            (nonrootBranches (contractAt t r.1) \ W)) :=
      (disjoint_liftSubtree_liftContract_nonrootBranches r).mono_right
        hcontractSubset
    rw [Finset.prod_union hdisjoint,
      prod_liftContractFinset]
  · simp only [hs, if_false]
    have hdisjoint :
        Disjoint (insert r (liftSubtreeNonrootBranches r))
          (liftContractFinset r.2
            (nonrootBranches (contractAt t r.1) \ W)) := by
      rw [Finset.disjoint_left]
      intro v hvLeft hvRight
      have hvContract := hcontractSubset hvRight
      rcases Finset.mem_insert.mp hvLeft with hvr | hvSub
      · exact
          (not_mem_liftContractFinset_of_subset_nonrootBranches r
            (fun _ h => h)) (by simpa [hvr] using hvContract)
      · exact
          (Finset.disjoint_left.mp
            (disjoint_liftSubtree_liftContract_nonrootBranches r))
            hvSub hvContract
    rw [Finset.prod_union hdisjoint,
      Finset.prod_insert (not_mem_liftSubtreeNonrootBranches r),
      prod_liftContractFinset]

/-- Restriction transports the entire cube product to the strict-descendant
piece of the original tree. -/
theorem prod_parentScaleRatio_restrictMarking_cube
    {t : PlaneTree} (Nm : HeppMarking t) (r : VPos t) :
    (∏ u ∈ nonrootBranches (subtreeAt t r.1),
        (parentScaleRatio (restrictMarking Nm r) u) ^ 3) =
      ∏ v ∈ liftSubtreeNonrootBranches r,
        (parentScaleRatio Nm v) ^ 3 := by
  calc
    (∏ u ∈ nonrootBranches (subtreeAt t r.1),
        (parentScaleRatio (restrictMarking Nm r) u) ^ 3) =
        ∏ u ∈ nonrootBranches (subtreeAt t r.1),
          (parentScaleRatio Nm (subtreeVertex r u)) ^ 3 := by
      apply Finset.prod_congr rfl
      intro u hu
      rw [parentScaleRatio_restrictMarking Nm r u hu]
    _ = ∏ v ∈ liftSubtreeNonrootBranches r,
          (parentScaleRatio Nm v) ^ 3 :=
      (prod_liftSubtreeNonrootBranches r
        (fun v => (parentScaleRatio Nm v) ^ 3)).symm

/-- Contraction transports the square product to the retained branch piece
of the original tree. -/
theorem prod_parentScaleRatio_contractMarking_sq
    {t : PlaneTree} (Nm : HeppMarking t) (r : VPos t) :
    (∏ u ∈ nonrootBranches (contractAt t r.1),
        (parentScaleRatio (contractMarking Nm r) u) ^ 2) =
      ∏ v ∈ liftContractFinset r.2
          (nonrootBranches (contractAt t r.1)),
        (parentScaleRatio Nm v) ^ 2 := by
  calc
    (∏ u ∈ nonrootBranches (contractAt t r.1),
        (parentScaleRatio (contractMarking Nm r) u) ^ 2) =
        ∏ u ∈ nonrootBranches (contractAt t r.1),
          (parentScaleRatio Nm (contractVertex r.2 u)) ^ 2 := by
      apply Finset.prod_congr rfl
      intro u _hu
      rw [parentScaleRatio_contractMarking]
    _ = ∏ v ∈ liftContractFinset r.2
          (nonrootBranches (contractAt t r.1)),
          (parentScaleRatio Nm v) ^ 2 :=
      (prod_liftContractFinset r.2
        (nonrootBranches (contractAt t r.1))
        (fun v => (parentScaleRatio Nm v) ^ 2)).symm

/-- The contracted complement factor reindexes to the lifted complement. -/
theorem prod_parentScaleRatio_contractMarking_sdiff
    {t : PlaneTree} (Nm : HeppMarking t) (r : VPos t)
    (W : Finset (VPos (contractAt t r.1))) :
    (∏ u ∈ nonrootBranches (contractAt t r.1) \ W,
        parentScaleRatio (contractMarking Nm r) u) =
      ∏ v ∈ liftContractFinset r.2
          (nonrootBranches (contractAt t r.1) \ W),
        parentScaleRatio Nm v := by
  calc
    (∏ u ∈ nonrootBranches (contractAt t r.1) \ W,
        parentScaleRatio (contractMarking Nm r) u) =
        ∏ u ∈ nonrootBranches (contractAt t r.1) \ W,
          parentScaleRatio Nm (contractVertex r.2 u) := by
      apply Finset.prod_congr rfl
      intro u _hu
      rw [parentScaleRatio_contractMarking]
    _ = ∏ v ∈ liftContractFinset r.2
          (nonrootBranches (contractAt t r.1) \ W),
          parentScaleRatio Nm v :=
      (prod_liftContractFinset r.2
        (nonrootBranches (contractAt t r.1) \ W)
        (parentScaleRatio Nm)).symm

/-- A cube product is the square product times one complement copy. -/
theorem prod_cube_eq_prod_sq_mul_prod
    {α : Type*} (S : Finset α) (f : α → ℝ) :
    (∏ x ∈ S, (f x) ^ 3) =
      (∏ x ∈ S, (f x) ^ 2) * ∏ x ∈ S, f x := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro x _hx
  ring

/-- For positive `s`, the root exponent is two in the one-cut case and
three in every multi-cut case. -/
theorem min_two_mul_eq_root_ratio_exponent
    {s : ℕ} (hs : 0 < s) :
    min (2 * s) 3 = if s = 1 then 2 else 3 := by
  by_cases hs1 : s = 1
  · simp [hs1]
  · simp only [hs1, if_false]
    omega

/-- Restriction contribution in (5.45): the selected-root gain and all
strict-descendant cubes. -/
def restrictionParentRatioFactor
    {t : PlaneTree} (Nm : HeppMarking t) (r : VPos t)
    (s : ℕ) : ℝ :=
  (parentScaleRatio Nm r) ^ min (2 * s) 3 *
    ∏ u ∈ nonrootBranches (subtreeAt t r.1),
      (parentScaleRatio (restrictMarking Nm r) u) ^ 3

/-- Contraction/IH contribution in (5.45): retained squares and the
complement of `W`. -/
def contractionParentRatioFactor
    {t : PlaneTree} (Nm : HeppMarking t) (r : VPos t)
    (W : Finset (VPos (contractAt t r.1))) : ℝ :=
  (∏ u ∈ nonrootBranches (contractAt t r.1),
      (parentScaleRatio (contractMarking Nm r) u) ^ 2) *
    ∏ u ∈ nonrootBranches (contractAt t r.1) \ W,
      parentScaleRatio (contractMarking Nm r) u

/-- The target ratio ledger in the original-tree P-5.9 summand. -/
def originalParentRatioFactor
    {t : PlaneTree} (Nm : HeppMarking t)
    (W : Finset (VPos t)) : ℝ :=
  (∏ v ∈ nonrootBranches t, (parentScaleRatio Nm v) ^ 2) *
    ∏ v ∈ nonrootBranches t \ W, parentScaleRatio Nm v

/-- **Paper (5.45)--(5.46), exact parent-ratio ledger.**

When `s = 1`, `r ∈ W'`, so its root exponent is two.  When `s ≥ 2`,
`r ∉ W'`, so the exponent is three.  All strict descendants contribute a
cube, while retained contracted branches contribute the IH square and its
`W`-complement copy. -/
theorem restriction_mul_contraction_parentRatioFactor
    {t : PlaneTree} (Nm : HeppMarking t) (r : VPos t)
    (hr : r ∈ nonrootBranches t) (s : ℕ) (hs : 0 < s)
    (W : Finset (VPos (contractAt t r.1)))
    (hW : W ⊆ nonrootBranches (contractAt t r.1)) :
    restrictionParentRatioFactor Nm r s *
        contractionParentRatioFactor Nm r W =
      originalParentRatioFactor Nm (liftWPrime r s W) := by
  unfold restrictionParentRatioFactor contractionParentRatioFactor
    originalParentRatioFactor
  rw [prod_parentScaleRatio_restrictMarking_cube,
    prod_parentScaleRatio_contractMarking_sq,
    prod_parentScaleRatio_contractMarking_sdiff,
    min_two_mul_eq_root_ratio_exponent hs,
    prod_nonrootBranches_eq_collapse_partition r hr
      (fun v => (parentScaleRatio Nm v) ^ 2),
    prod_nonrootBranches_sdiff_liftWPrime r hr s hW
      (parentScaleRatio Nm),
    prod_cube_eq_prod_sq_mul_prod,
    prod_liftContractFinset r.2
      (nonrootBranches (contractAt t r.1) \ W)
      (parentScaleRatio Nm)]
  by_cases hs1 : s = 1
  · simp only [hs1, if_pos]
    ring
  · simp only [hs1, if_false]
    ring

end

end Anderson4D
