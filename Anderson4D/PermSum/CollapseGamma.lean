import Anderson4D.PermSum.CollapseEmbedding
import Anderson4D.HeppTree.ClusterDiameter

/-!
# Gamma and accumulated-scale transport through subtree collapse

This file records the exact contraction ledgers used in paper §5.4.1.
Restriction and geometric transport live in `CollapseEmbedding`; here the
marker contribution is isolated from the unchanged retained branches.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

set_option warningAsError true
set_option autoImplicit false

noncomputable section

/-! ## Children at a contracted branch -/

/-- Inclusion of all vertices retained by contraction. -/
def collapseContractVertexEmbedding {t : PlaneTree} (r : VPos t) :
    VPos (contractAt t r.1) ↪ VPos t where
  toFun := contractVertex r.2
  inj' := by
    intro v w h
    apply Subtype.ext
    exact congrArg (fun x : VPos t => x.1) h

/-- At a retained vertex distinct from the marker, the child finset maps
exactly to the original child finset.  The proof uses preservation of child
counts to obtain surjectivity from the evident inclusion. -/
theorem map_childrenOf_contractVertex_of_ne {t : PlaneTree} (r : VPos t)
    (v : VPos (contractAt t r.1)) (hv : v.1 ≠ r.1) :
    (childrenOf v).map (collapseContractVertexEmbedding r) =
      childrenOf (contractVertex r.2 v) := by
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    rw [Finset.mem_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    simpa [collapseContractVertexEmbedding] using hu
  · rw [Finset.card_map, card_childrenOf, card_childrenOf]
    have hcount :=
      childCount_contractAt_eq_of_ne r.2 v.2 hv
    exact Nat.le_of_eq (by
      simpa [contractVertex] using hcount.symm)

/-- A canonical retained copy of the original parent of a non-root
contraction vertex. -/
def contractParentVertex {t : PlaneTree} (r : VPos t)
    (hr0 : r ≠ rootV t) : VPos (contractAt t r.1) :=
  ⟨(parentV r).1, (isPos_contractAt_iff r.2).mpr
    ⟨(parentV r).2, by
      rintro ⟨hprefix, _hne⟩
      have hle := hprefix.length_le
      change r.1.length ≤ r.1.dropLast.length at hle
      rw [List.length_dropLast] at hle
      have hpos : 0 < r.1.length :=
        List.length_pos_iff.mpr (ne_root_iff.mp hr0)
      omega⟩⟩

@[simp]
theorem contractVertex_contractParentVertex {t : PlaneTree}
    (r : VPos t) (hr0 : r ≠ rootV t) :
    contractVertex r.2 (contractParentVertex r hr0) = parentV r :=
  rfl

/-- The contracted parent is not the marker. -/
theorem contractParentVertex_ne_marker {t : PlaneTree}
    (r : VPos t) (hr0 : r ≠ rootV t) :
    (contractParentVertex r hr0).1 ≠ r.1 := by
  intro h
  have hlen := congrArg List.length h
  change r.1.dropLast.length = r.1.length at hlen
  rw [List.length_dropLast] at hlen
  have hpos : 0 < r.1.length :=
    List.length_pos_iff.mpr (ne_root_iff.mp hr0)
  omega

/-- The marker leaf is a child of the canonical contracted parent. -/
theorem contractMarker_mem_childrenOf_parent {t : PlaneTree}
    (r : VPos t) (hr0 : r ≠ rootV t) :
    (contractMarker t r.1 r.2) ∈
      childrenOf (contractParentVertex r hr0) := by
  rw [mem_childrenOf_iff_ne_root_and_parentV_eq]
  constructor
  · intro hroot
    apply hr0
    apply Subtype.ext
    have hval := congrArg Subtype.val hroot
    simpa [contractMarker, rootV] using hval
  · apply Subtype.ext
    rfl

/-- The original subtree root is a child of its original parent. -/
theorem self_mem_childrenOf_parent {t : PlaneTree}
    (r : VPos t) (hr0 : r ≠ rootV t) :
    r ∈ childrenOf (parentV r) :=
  mem_childrenOf_iff_ne_root_and_parentV_eq.mpr ⟨hr0, rfl⟩

private theorem not_mem_Leaves_of_mem_BranchNodes {t : PlaneTree}
    (v : VPos t) (hv : v ∈ BranchNodes t) :
    v ∉ Leaves t := by
  rw [mem_BranchNodes_iff] at hv
  rw [mem_Leaves_iff]
  omega

/-- At the parent of the collapsed subtree, the contracted leaf children are
the old leaf children together with the new marker (viewed at the original
subtree-root position). -/
theorem map_leafChildren_contractParent {t : PlaneTree}
    (r : VPos t) (hr0 : r ≠ rootV t) (hrBranch : r ∈ BranchNodes t) :
    (leafChildren (contractParentVertex r hr0)).map
        (collapseContractVertexEmbedding r) =
      insert r (leafChildren (parentV r)) := by
  have hparentMap :=
    map_childrenOf_contractVertex_of_ne r (contractParentVertex r hr0)
      (contractParentVertex_ne_marker r hr0)
  ext w
  constructor
  · intro hw
    rw [Finset.mem_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    rcases Finset.mem_inter.mp hu with ⟨huChild, huLeaf⟩
    rw [Finset.mem_insert]
    by_cases hum : u.1 = r.1
    · left
      apply Subtype.ext
      exact hum
    · right
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · rw [← contractVertex_contractParentVertex r hr0, ← hparentMap]
        exact Finset.mem_map.mpr ⟨u, huChild, rfl⟩
      · exact (mem_Leaves_contractVertex_iff_of_ne r.2 u hum).mp huLeaf
  · intro hw
    rw [Finset.mem_insert] at hw
    rcases hw with hwr | hw
    · rw [Finset.mem_map]
      refine ⟨contractMarker t r.1 r.2, ?_, ?_⟩
      · exact Finset.mem_inter.mpr
          ⟨contractMarker_mem_childrenOf_parent r hr0,
            contractMarker_mem_Leaves t r.1 r.2⟩
      · exact hwr.symm
    · rcases Finset.mem_inter.mp hw with ⟨hwChild, hwLeaf⟩
      have hwMapped :
          w ∈ (childrenOf (contractParentVertex r hr0)).map
            (collapseContractVertexEmbedding r) := by
        rw [hparentMap, contractVertex_contractParentVertex]
        exact hwChild
      rw [Finset.mem_map] at hwMapped
      obtain ⟨u, huChild, huEq⟩ := hwMapped
      change contractVertex r.2 u = w at huEq
      have hum : u.1 ≠ r.1 := by
        intro hum
        have hwr : w = r := by
          rw [← huEq]
          apply Subtype.ext
          exact hum
        exact (not_mem_Leaves_of_mem_BranchNodes r hrBranch)
          (hwr ▸ hwLeaf)
      rw [Finset.mem_map]
      refine ⟨u, Finset.mem_inter.mpr ⟨huChild, ?_⟩, huEq⟩
      exact (mem_Leaves_contractVertex_iff_of_ne r.2 u hum).mpr
        (by rw [huEq]; exact hwLeaf)

/-- At the contracted parent, simple leaf children are precisely the
unchanged original simple leaf children; the marker is compound. -/
theorem map_simpleChildren_contractParent {t : PlaneTree}
    (r : VPos t) (hr0 : r ≠ rootV t) (hrBranch : r ∈ BranchNodes t)
    (compound : Finset (VPos t)) :
    (childrenOf (contractParentVertex r hr0) ∩
        simpleLeaves (contractAt t r.1) (contractCompound r compound)).map
        (collapseContractVertexEmbedding r) =
      childrenOf (parentV r) ∩ simpleLeaves t compound := by
  have hparentMap :=
    map_childrenOf_contractVertex_of_ne r (contractParentVertex r hr0)
      (contractParentVertex_ne_marker r hr0)
  ext w
  constructor
  · intro hw
    rw [Finset.mem_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    rcases Finset.mem_inter.mp hu with ⟨huChild, huSimple⟩
    rcases Finset.mem_sdiff.mp huSimple with ⟨huLeaf, huNotCompound⟩
    have hum : u.1 ≠ r.1 := by
      intro hum
      exact huNotCompound
        ((mem_contractCompound r compound u).mpr (Or.inl hum))
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · rw [← contractVertex_contractParentVertex r hr0, ← hparentMap]
      exact Finset.mem_map.mpr ⟨u, huChild, rfl⟩
    · refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · exact (mem_Leaves_contractVertex_iff_of_ne r.2 u hum).mp huLeaf
      · intro huCompound
        exact huNotCompound
          ((mem_contractCompound r compound u).mpr
            (Or.inr huCompound))
  · intro hw
    rcases Finset.mem_inter.mp hw with ⟨hwChild, hwSimple⟩
    rcases Finset.mem_sdiff.mp hwSimple with ⟨hwLeaf, hwNotCompound⟩
    have hwMapped :
        w ∈ (childrenOf (contractParentVertex r hr0)).map
          (collapseContractVertexEmbedding r) := by
      rw [hparentMap, contractVertex_contractParentVertex]
      exact hwChild
    rw [Finset.mem_map] at hwMapped
    obtain ⟨u, huChild, huEq⟩ := hwMapped
    change contractVertex r.2 u = w at huEq
    have hum : u.1 ≠ r.1 := by
      intro hum
      have hwr : w = r := by
        rw [← huEq]
        apply Subtype.ext
        exact hum
      exact (not_mem_Leaves_of_mem_BranchNodes r hrBranch)
        (hwr ▸ hwLeaf)
    rw [Finset.mem_map]
    refine ⟨u, Finset.mem_inter.mpr ⟨huChild, ?_⟩, huEq⟩
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact (mem_Leaves_contractVertex_iff_of_ne r.2 u hum).mpr
        (by rw [huEq]; exact hwLeaf)
    · intro huContractCompound
      rcases (mem_contractCompound r compound u).mp huContractCompound with
        huMarker | huCompound
      · exact hum huMarker
      · exact hwNotCompound (by rw [← huEq]; exact huCompound)

/-- At the contracted parent, compound leaf children are the original
compound leaf children together with the new marker. -/
theorem map_compoundChildren_contractParent {t : PlaneTree}
    (r : VPos t) (hr0 : r ≠ rootV t) (hrBranch : r ∈ BranchNodes t)
    (compound : Finset (VPos t)) :
    (childrenOf (contractParentVertex r hr0) ∩
        compoundLeaves (contractAt t r.1)
          (contractCompound r compound)).map
        (collapseContractVertexEmbedding r) =
      insert r
        (childrenOf (parentV r) ∩ compoundLeaves t compound) := by
  have hparentMap :=
    map_childrenOf_contractVertex_of_ne r (contractParentVertex r hr0)
      (contractParentVertex_ne_marker r hr0)
  ext w
  constructor
  · intro hw
    rw [Finset.mem_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    rcases Finset.mem_inter.mp hu with ⟨huChild, huCompound⟩
    rcases Finset.mem_inter.mp huCompound with ⟨huLeaf, huMem⟩
    rw [Finset.mem_insert]
    by_cases hum : u.1 = r.1
    · left
      apply Subtype.ext
      exact hum
    · right
      have huOriginal : contractVertex r.2 u ∈ compound := by
        rcases (mem_contractCompound r compound u).mp huMem with
          huMarker | huOriginal
        · exact (hum huMarker).elim
        · exact huOriginal
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · rw [← contractVertex_contractParentVertex r hr0, ← hparentMap]
        exact Finset.mem_map.mpr ⟨u, huChild, rfl⟩
      · exact Finset.mem_inter.mpr
          ⟨(mem_Leaves_contractVertex_iff_of_ne r.2 u hum).mp huLeaf,
            huOriginal⟩
  · intro hw
    rw [Finset.mem_insert] at hw
    rcases hw with hwr | hw
    · rw [Finset.mem_map]
      refine ⟨contractMarker t r.1 r.2, ?_, ?_⟩
      · exact Finset.mem_inter.mpr
          ⟨contractMarker_mem_childrenOf_parent r hr0,
            Finset.mem_inter.mpr
              ⟨contractMarker_mem_Leaves t r.1 r.2,
                contractMarker_mem_contractCompound r compound⟩⟩
      · exact hwr.symm
    · rcases Finset.mem_inter.mp hw with ⟨hwChild, hwCompound⟩
      rcases Finset.mem_inter.mp hwCompound with ⟨hwLeaf, hwMem⟩
      have hwMapped :
          w ∈ (childrenOf (contractParentVertex r hr0)).map
            (collapseContractVertexEmbedding r) := by
        rw [hparentMap, contractVertex_contractParentVertex]
        exact hwChild
      rw [Finset.mem_map] at hwMapped
      obtain ⟨u, huChild, huEq⟩ := hwMapped
      change contractVertex r.2 u = w at huEq
      have hum : u.1 ≠ r.1 := by
        intro hum
        have hwr : w = r := by
          rw [← huEq]
          apply Subtype.ext
          exact hum
        exact (not_mem_Leaves_of_mem_BranchNodes r hrBranch)
          (hwr ▸ hwLeaf)
      rw [Finset.mem_map]
      refine ⟨u, Finset.mem_inter.mpr ⟨huChild, ?_⟩, huEq⟩
      exact Finset.mem_inter.mpr
        ⟨(mem_Leaves_contractVertex_iff_of_ne r.2 u hum).mpr
            (by rw [huEq]; exact hwLeaf),
          (mem_contractCompound r compound u).mpr
            (Or.inr (by rw [huEq]; exact hwMem))⟩

/-! ## The parent-node gamma increment -/

/-- Reindex a contracted multiplicity-minus-one sum along the retained
vertex embedding.  The marker contributes exactly `s`; every other vertex
keeps its original multiplicity. -/
theorem sum_contractMultiplicities_sub_one_map {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t) (s : ℕ) (hs : 1 ≤ s)
    (S : Finset (VPos (contractAt t r.1))) :
    (∑ u ∈ S, ((contractMultiplicities mu r s hs).m u - 1)) =
      ∑ w ∈ S.map (collapseContractVertexEmbedding r),
        (if w = r then s else mu.m w - 1) := by
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro u _hu
  change (contractMultiplicities mu r s hs).m u - 1 =
    if contractVertex r.2 u = r then s
    else mu.m (contractVertex r.2 u) - 1
  by_cases hum : u.1 = r.1
  · have huEq : contractVertex r.2 u = r := by
      apply Subtype.ext
      exact hum
    simp [contractMultiplicities, hum, huEq]
  · have huNe : contractVertex r.2 u ≠ r := by
      intro h
      exact hum (congrArg (fun v : VPos t => v.1) h)
    simp [contractMultiplicities, hum, huNe]

/-- The leaf-child multiplicity sum at the contracted parent is the original
sum plus the marker contribution `s`. -/
theorem sum_leafChildren_contractParent {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (hr0 : r ≠ rootV t) (hrBranch : r ∈ BranchNodes t)
    (s : ℕ) (hs : 1 ≤ s) :
    (∑ l ∈ leafChildren (contractParentVertex r hr0),
        ((contractMultiplicities mu r s hs).m l - 1)) =
      s + ∑ l ∈ leafChildren (parentV r), (mu.m l - 1) := by
  rw [sum_contractMultiplicities_sub_one_map,
    map_leafChildren_contractParent r hr0 hrBranch]
  have hrNot : r ∉ leafChildren (parentV r) := by
    intro hr
    exact (not_mem_Leaves_of_mem_BranchNodes r hrBranch)
      (Finset.mem_inter.mp hr).2
  rw [Finset.sum_insert hrNot]
  simp only [if_pos]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  have hlne : l ≠ r := by
    intro hlr
    exact hrNot (hlr ▸ hl)
  simp [hlne]

/-- The compound-child multiplicity sum at the contracted parent is the
original sum plus the marker contribution `s`. -/
theorem sum_compoundChildren_contractParent {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (hr0 : r ≠ rootV t) (hrBranch : r ∈ BranchNodes t)
    (compound : Finset (VPos t)) (s : ℕ) (hs : 1 ≤ s) :
    (∑ l ∈ childrenOf (contractParentVertex r hr0) ∩
        compoundLeaves (contractAt t r.1) (contractCompound r compound),
        ((contractMultiplicities mu r s hs).m l - 1)) =
      s + ∑ l ∈ childrenOf (parentV r) ∩ compoundLeaves t compound,
        (mu.m l - 1) := by
  rw [sum_contractMultiplicities_sub_one_map,
    map_compoundChildren_contractParent r hr0 hrBranch compound]
  have hrNot :
      r ∉ childrenOf (parentV r) ∩ compoundLeaves t compound := by
    intro hr
    exact (not_mem_Leaves_of_mem_BranchNodes r hrBranch)
      (Finset.mem_inter.mp (Finset.mem_inter.mp hr).2).1
  rw [Finset.sum_insert hrNot]
  simp only [if_pos]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  have hlne : l ≠ r := by
    intro hlr
    exact hrNot (hlr ▸ hl)
  simp [hlne]

/-- **Paper (5.45)(iii), `γ^∞` form.**  Replacing the branch child `r` by
a compound marker of multiplicity `s+1` increases the parent's exponent by
exactly `s`. -/
theorem gammaInf_contract_parent {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (hr0 : r ≠ rootV t) (hrBranch : r ∈ BranchNodes t)
    (s : ℕ) (hs : 1 ≤ s) :
    gammaInf (contractMultiplicities mu r s hs)
        (contractParentVertex r hr0) =
      gammaInf mu (parentV r) + s := by
  have hchildren := congrArg Finset.card
    (map_childrenOf_contractVertex_of_ne r (contractParentVertex r hr0)
      (contractParentVertex_ne_marker r hr0))
  simp only [Finset.card_map, contractVertex_contractParentVertex] at hchildren
  unfold gammaInf
  rw [hchildren, sum_leafChildren_contractParent mu r hr0 hrBranch s hs]
  omega

/-- **Paper (5.45)(iii), `γ²` form.**  The contracted parent's `γ²`
exponent is the original exponent plus exactly `s`. -/
theorem gamma2_contract_parent {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (hr0 : r ≠ rootV t) (hrBranch : r ∈ BranchNodes t)
    (compound : Finset (VPos t)) (s : ℕ) (hs : 1 ≤ s) :
    gamma2 (contractMultiplicities mu r s hs)
        (contractCompound r compound) (contractParentVertex r hr0) =
      gamma2 mu compound (parentV r) + s := by
  have hchildren := congrArg Finset.card
    (map_childrenOf_contractVertex_of_ne r (contractParentVertex r hr0)
      (contractParentVertex_ne_marker r hr0))
  simp only [Finset.card_map, contractVertex_contractParentVertex] at hchildren
  have hsimple := congrArg Finset.card
    (map_simpleChildren_contractParent r hr0 hrBranch compound)
  simp only [Finset.card_map] at hsimple
  unfold gamma2
  rw [hchildren, hsimple,
    sum_compoundChildren_contractParent mu r hr0 hrBranch compound s hs]
  omega

/-! ## Gamma exponents at all other retained branches -/

/-- Away from the original parent of `r`, the marker is not a child. -/
theorem contractMarker_not_mem_childrenOf_of_ne_parent {t : PlaneTree}
    (r : VPos t) (v : VPos (contractAt t r.1))
    (hparent : contractVertex r.2 v ≠ parentV r) :
    contractMarker t r.1 r.2 ∉ childrenOf v := by
  intro hmarker
  have horiginal :
      r ∈ childrenOf (contractVertex r.2 v) := by
    simpa [contractVertex, contractMarker] using hmarker
  have hp :=
    (mem_childrenOf_iff_ne_root_and_parentV_eq.mp horiginal).2
  exact hparent hp.symm

/-- At a retained vertex other than the collapsed subtree's parent, leaf
children map exactly to the original leaf children. -/
theorem map_leafChildren_contractVertex_of_ne_parent {t : PlaneTree}
    (r : VPos t) (v : VPos (contractAt t r.1))
    (hv : v.1 ≠ r.1)
    (hparent : contractVertex r.2 v ≠ parentV r) :
    (leafChildren v).map (collapseContractVertexEmbedding r) =
      leafChildren (contractVertex r.2 v) := by
  have hchildren := map_childrenOf_contractVertex_of_ne r v hv
  have hmarker :=
    contractMarker_not_mem_childrenOf_of_ne_parent r v hparent
  ext w
  constructor
  · intro hw
    rw [Finset.mem_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    rcases Finset.mem_inter.mp hu with ⟨huChild, huLeaf⟩
    have hum : u.1 ≠ r.1 := by
      intro hum
      apply hmarker
      have huEq : u = contractMarker t r.1 r.2 := by
        apply Subtype.ext
        exact hum
      exact huEq ▸ huChild
    exact Finset.mem_inter.mpr
      ⟨by
        rw [← hchildren]
        exact Finset.mem_map.mpr ⟨u, huChild, rfl⟩,
        (mem_Leaves_contractVertex_iff_of_ne r.2 u hum).mp huLeaf⟩
  · intro hw
    rcases Finset.mem_inter.mp hw with ⟨hwChild, hwLeaf⟩
    have hwMapped :
        w ∈ (childrenOf v).map (collapseContractVertexEmbedding r) := by
      rw [hchildren]
      exact hwChild
    rw [Finset.mem_map] at hwMapped
    obtain ⟨u, huChild, huEq⟩ := hwMapped
    change contractVertex r.2 u = w at huEq
    have hum : u.1 ≠ r.1 := by
      intro hum
      apply hmarker
      have huMarker : u = contractMarker t r.1 r.2 := by
        apply Subtype.ext
        exact hum
      exact huMarker ▸ huChild
    rw [Finset.mem_map]
    refine ⟨u, Finset.mem_inter.mpr ⟨huChild, ?_⟩, huEq⟩
    exact (mem_Leaves_contractVertex_iff_of_ne r.2 u hum).mpr
      (by rw [huEq]; exact hwLeaf)

/-- Simple leaf children are unchanged away from the collapsed subtree's
parent. -/
theorem map_simpleChildren_contractVertex_of_ne_parent {t : PlaneTree}
    (r : VPos t) (v : VPos (contractAt t r.1))
    (hv : v.1 ≠ r.1)
    (hparent : contractVertex r.2 v ≠ parentV r)
    (compound : Finset (VPos t)) :
    (childrenOf v ∩
        simpleLeaves (contractAt t r.1) (contractCompound r compound)).map
        (collapseContractVertexEmbedding r) =
      childrenOf (contractVertex r.2 v) ∩ simpleLeaves t compound := by
  have hchildren := map_childrenOf_contractVertex_of_ne r v hv
  have hmarker :=
    contractMarker_not_mem_childrenOf_of_ne_parent r v hparent
  ext w
  constructor
  · intro hw
    rw [Finset.mem_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    rcases Finset.mem_inter.mp hu with ⟨huChild, huSimple⟩
    rcases Finset.mem_sdiff.mp huSimple with ⟨huLeaf, huNotCompound⟩
    have hum : u.1 ≠ r.1 := by
      intro hum
      apply hmarker
      have huMarker : u = contractMarker t r.1 r.2 := by
        apply Subtype.ext
        exact hum
      exact huMarker ▸ huChild
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · rw [← hchildren]
      exact Finset.mem_map.mpr ⟨u, huChild, rfl⟩
    · refine Finset.mem_sdiff.mpr
        ⟨(mem_Leaves_contractVertex_iff_of_ne r.2 u hum).mp huLeaf, ?_⟩
      intro huCompound
      exact huNotCompound
        ((mem_contractCompound r compound u).mpr (Or.inr huCompound))
  · intro hw
    rcases Finset.mem_inter.mp hw with ⟨hwChild, hwSimple⟩
    rcases Finset.mem_sdiff.mp hwSimple with ⟨hwLeaf, hwNotCompound⟩
    have hwMapped :
        w ∈ (childrenOf v).map (collapseContractVertexEmbedding r) := by
      rw [hchildren]
      exact hwChild
    rw [Finset.mem_map] at hwMapped
    obtain ⟨u, huChild, huEq⟩ := hwMapped
    change contractVertex r.2 u = w at huEq
    have hum : u.1 ≠ r.1 := by
      intro hum
      apply hmarker
      have huMarker : u = contractMarker t r.1 r.2 := by
        apply Subtype.ext
        exact hum
      exact huMarker ▸ huChild
    rw [Finset.mem_map]
    refine ⟨u, Finset.mem_inter.mpr ⟨huChild, ?_⟩, huEq⟩
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact (mem_Leaves_contractVertex_iff_of_ne r.2 u hum).mpr
        (by rw [huEq]; exact hwLeaf)
    · intro huContract
      rcases (mem_contractCompound r compound u).mp huContract with
        huMarker | huCompound
      · exact hum huMarker
      · exact hwNotCompound (by rw [← huEq]; exact huCompound)

/-- Compound leaf children are unchanged away from the collapsed subtree's
parent. -/
theorem map_compoundChildren_contractVertex_of_ne_parent {t : PlaneTree}
    (r : VPos t) (v : VPos (contractAt t r.1))
    (hv : v.1 ≠ r.1)
    (hparent : contractVertex r.2 v ≠ parentV r)
    (compound : Finset (VPos t)) :
    (childrenOf v ∩
        compoundLeaves (contractAt t r.1)
          (contractCompound r compound)).map
        (collapseContractVertexEmbedding r) =
      childrenOf (contractVertex r.2 v) ∩ compoundLeaves t compound := by
  have hchildren := map_childrenOf_contractVertex_of_ne r v hv
  have hmarker :=
    contractMarker_not_mem_childrenOf_of_ne_parent r v hparent
  ext w
  constructor
  · intro hw
    rw [Finset.mem_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    rcases Finset.mem_inter.mp hu with ⟨huChild, huCompound⟩
    rcases Finset.mem_inter.mp huCompound with ⟨huLeaf, huMem⟩
    have hum : u.1 ≠ r.1 := by
      intro hum
      apply hmarker
      have huMarker : u = contractMarker t r.1 r.2 := by
        apply Subtype.ext
        exact hum
      exact huMarker ▸ huChild
    have huOriginal : contractVertex r.2 u ∈ compound := by
      rcases (mem_contractCompound r compound u).mp huMem with
        huMarker | huOriginal
      · exact (hum huMarker).elim
      · exact huOriginal
    exact Finset.mem_inter.mpr
      ⟨by
        rw [← hchildren]
        exact Finset.mem_map.mpr ⟨u, huChild, rfl⟩,
        Finset.mem_inter.mpr
          ⟨(mem_Leaves_contractVertex_iff_of_ne r.2 u hum).mp huLeaf,
            huOriginal⟩⟩
  · intro hw
    rcases Finset.mem_inter.mp hw with ⟨hwChild, hwCompound⟩
    rcases Finset.mem_inter.mp hwCompound with ⟨hwLeaf, hwMem⟩
    have hwMapped :
        w ∈ (childrenOf v).map (collapseContractVertexEmbedding r) := by
      rw [hchildren]
      exact hwChild
    rw [Finset.mem_map] at hwMapped
    obtain ⟨u, huChild, huEq⟩ := hwMapped
    change contractVertex r.2 u = w at huEq
    have hum : u.1 ≠ r.1 := by
      intro hum
      apply hmarker
      have huMarker : u = contractMarker t r.1 r.2 := by
        apply Subtype.ext
        exact hum
      exact huMarker ▸ huChild
    rw [Finset.mem_map]
    refine ⟨u, Finset.mem_inter.mpr ⟨huChild, ?_⟩, huEq⟩
    exact Finset.mem_inter.mpr
      ⟨(mem_Leaves_contractVertex_iff_of_ne r.2 u hum).mpr
          (by rw [huEq]; exact hwLeaf),
        (mem_contractCompound r compound u).mpr
          (Or.inr (by rw [huEq]; exact hwMem))⟩

/-- The leaf-child multiplicity sum is unchanged at every retained branch
other than the collapsed subtree's parent. -/
theorem sum_leafChildren_contractVertex_of_ne_parent {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (v : VPos (contractAt t r.1)) (hv : v.1 ≠ r.1)
    (hparent : contractVertex r.2 v ≠ parentV r)
    (s : ℕ) (hs : 1 ≤ s) :
    (∑ l ∈ leafChildren v,
        ((contractMultiplicities mu r s hs).m l - 1)) =
      ∑ l ∈ leafChildren (contractVertex r.2 v), (mu.m l - 1) := by
  rw [sum_contractMultiplicities_sub_one_map,
    map_leafChildren_contractVertex_of_ne_parent r v hv hparent]
  apply Finset.sum_congr rfl
  intro l hl
  have hlne : l ≠ r := by
    intro hlr
    have hp :=
      (mem_childrenOf_iff_ne_root_and_parentV_eq.mp
        (Finset.mem_inter.mp (hlr ▸ hl)).1).2
    exact hparent hp.symm
  simp [hlne]

/-- The compound-child multiplicity sum is likewise unchanged away from the
collapsed subtree's parent. -/
theorem sum_compoundChildren_contractVertex_of_ne_parent {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (v : VPos (contractAt t r.1)) (hv : v.1 ≠ r.1)
    (hparent : contractVertex r.2 v ≠ parentV r)
    (compound : Finset (VPos t)) (s : ℕ) (hs : 1 ≤ s) :
    (∑ l ∈ childrenOf v ∩
        compoundLeaves (contractAt t r.1) (contractCompound r compound),
        ((contractMultiplicities mu r s hs).m l - 1)) =
      ∑ l ∈ childrenOf (contractVertex r.2 v) ∩
        compoundLeaves t compound, (mu.m l - 1) := by
  rw [sum_contractMultiplicities_sub_one_map,
    map_compoundChildren_contractVertex_of_ne_parent
      r v hv hparent compound]
  apply Finset.sum_congr rfl
  intro l hl
  have hlne : l ≠ r := by
    intro hlr
    have hp :=
      (mem_childrenOf_iff_ne_root_and_parentV_eq.mp
        (Finset.mem_inter.mp (hlr ▸ hl)).1).2
    exact hparent hp.symm
  simp [hlne]

/-- `γ^∞` is unchanged at every retained branch other than the parent of the
collapsed subtree. -/
theorem gammaInf_contract_of_ne_parent {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (v : VPos (contractAt t r.1)) (hv : v.1 ≠ r.1)
    (hparent : contractVertex r.2 v ≠ parentV r)
    (s : ℕ) (hs : 1 ≤ s) :
    gammaInf (contractMultiplicities mu r s hs) v =
      gammaInf mu (contractVertex r.2 v) := by
  have hchildren := congrArg Finset.card
    (map_childrenOf_contractVertex_of_ne r v hv)
  simp only [Finset.card_map] at hchildren
  unfold gammaInf
  rw [hchildren,
    sum_leafChildren_contractVertex_of_ne_parent
      mu r v hv hparent s hs]

/-- `γ²` is unchanged at every retained branch other than the parent of the
collapsed subtree. -/
theorem gamma2_contract_of_ne_parent {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (v : VPos (contractAt t r.1)) (hv : v.1 ≠ r.1)
    (hparent : contractVertex r.2 v ≠ parentV r)
    (compound : Finset (VPos t)) (s : ℕ) (hs : 1 ≤ s) :
    gamma2 (contractMultiplicities mu r s hs)
        (contractCompound r compound) v =
      gamma2 mu compound (contractVertex r.2 v) := by
  have hchildren := congrArg Finset.card
    (map_childrenOf_contractVertex_of_ne r v hv)
  simp only [Finset.card_map] at hchildren
  have hsimple := congrArg Finset.card
    (map_simpleChildren_contractVertex_of_ne_parent
      r v hv hparent compound)
  simp only [Finset.card_map] at hsimple
  unfold gamma2
  rw [hchildren, hsimple,
    sum_compoundChildren_contractVertex_of_ne_parent
      mu r v hv hparent compound s hs]

/-! ## Accumulated-scale ledger under contraction -/

/-- Descendant branches of the contracted tree are exactly the descendant
branches of the original tree that do not lie in the removed rooted
subtree. -/
theorem map_branchNodesUnder_contractVertex {t : PlaneTree}
    (r : VPos t) (v : VPos (contractAt t r.1)) :
    (branchNodesUnder v).map (collapseContractVertexEmbedding r) =
      (branchNodesUnder (contractVertex r.2 v)).filter
        (fun u => ¬r.1 <+: u.1) := by
  ext w
  constructor
  · intro hw
    rw [Finset.mem_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    rcases Finset.mem_filter.mp hu with ⟨huBranch, huPrefix⟩
    have huNotPrefix :
        ¬r.1 <+: u.1 :=
      not_prefix_of_mem_BranchNodes_contractAt r.2 u huBranch
    have huNe : u.1 ≠ r.1 := by
      intro h
      apply huNotPrefix
      rw [h]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨(mem_BranchNodes_contractVertex_iff_of_ne r.2 u huNe).mp
            huBranch,
          by
            change (contractVertex r.2 v).1 <+:
              (contractVertex r.2 u).1
            exact huPrefix⟩,
        by
          change ¬r.1 <+: (contractVertex r.2 u).1
          exact huNotPrefix⟩
  · intro hw
    rcases Finset.mem_filter.mp hw with ⟨hwUnder, hwNotPrefix⟩
    rcases Finset.mem_filter.mp hwUnder with ⟨hwBranch, hwPrefix⟩
    let u : VPos (contractAt t r.1) :=
      ⟨w.1, (isPos_contractAt_iff r.2).mpr
        ⟨w.2, by
          rintro ⟨hrw, _hne⟩
          exact hwNotPrefix hrw⟩⟩
    have huNe : u.1 ≠ r.1 := by
      intro h
      apply hwNotPrefix
      rw [← h]
    have huBranch : u ∈ BranchNodes (contractAt t r.1) :=
      (mem_BranchNodes_contractVertex_iff_of_ne r.2 u huNe).mpr
        (by simpa [u, contractVertex] using hwBranch)
    rw [Finset.mem_map]
    refine ⟨u, Finset.mem_filter.mpr ⟨huBranch, ?_⟩, ?_⟩
    · simpa [u, contractVertex] using hwPrefix
    · rfl

/-- Unified pointwise contraction ledger on branch nodes: the original
exponent is retained, with one extra `s` exactly at the parent of the
collapsed subtree. -/
theorem gammaInf_contract_branch_formula {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (hr0 : r ≠ rootV t) (hrBranch : r ∈ BranchNodes t)
    (s : ℕ) (hs : 1 ≤ s)
    (v : VPos (contractAt t r.1))
    (hvBranch : v ∈ BranchNodes (contractAt t r.1)) :
    gammaInf (contractMultiplicities mu r s hs) v =
      gammaInf mu (contractVertex r.2 v) +
        if contractVertex r.2 v = parentV r then s else 0 := by
  have hvNotPrefix :
      ¬r.1 <+: v.1 :=
    not_prefix_of_mem_BranchNodes_contractAt r.2 v hvBranch
  have hvNe : v.1 ≠ r.1 := by
    intro h
    apply hvNotPrefix
    rw [h]
  by_cases hparent : contractVertex r.2 v = parentV r
  · have hvEq : v = contractParentVertex r hr0 := by
      apply Subtype.ext
      have hval := congrArg (fun u : VPos t => u.1) hparent
      exact hval
    subst v
    simp [gammaInf_contract_parent mu r hr0 hrBranch s hs]
  · rw [gammaInf_contract_of_ne_parent mu r v hvNe hparent s hs]
    simp [hparent]

/-- Exact retained-branch form of the contracted accumulated scale.  It
exhibits explicitly that the sole local change is the extra parent mass
`s * N_{parent(r)}`; the removed subtree branches are absent from the
filtered index set. -/
theorem accumulatedScale_contract_eq_retained_sum {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (r : VPos t)
    (hr0 : r ≠ rootV t) (hrBranch : r ∈ BranchNodes t)
    (s : ℕ) (hs : 1 ≤ s)
    (v : VPos (contractAt t r.1)) :
    accumulatedScale (contractMarking Nm r)
        (contractMultiplicities mu r s hs) v =
      ∑ u ∈
          (branchNodesUnder (contractVertex r.2 v)).filter
            (fun u => ¬r.1 <+: u.1),
        (gammaInf mu u + if u = parentV r then s else 0) *
          scaleN Nm u := by
  unfold accumulatedScale
  rw [← map_branchNodesUnder_contractVertex r v, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro u hu
  have huBranch : u ∈ BranchNodes (contractAt t r.1) :=
    (Finset.mem_filter.mp hu).1
  rw [gammaInf_contract_branch_formula
    mu r hr0 hrBranch s hs u huBranch]
  rfl

private theorem listPrefixes_comparable {p q z : List ℕ}
    (hp : p <+: z) (hq : q <+: z) :
    p <+: q ∨ q <+: p := by
  induction z generalizing p q with
  | nil =>
      have hp0 : p = [] := by
        obtain ⟨tail, htail⟩ := hp
        exact (List.append_eq_nil_iff.mp htail).1
      have hq0 : q = [] := by
        obtain ⟨tail, htail⟩ := hq
        exact (List.append_eq_nil_iff.mp htail).1
      simp [hp0, hq0]
  | cons a z ih =>
      cases p with
      | nil => exact Or.inl List.nil_prefix
      | cons b p =>
          cases q with
          | nil => exact Or.inr List.nil_prefix
          | cons c q =>
              obtain ⟨hba, hp'⟩ := List.cons_prefix_cons.mp hp
              obtain ⟨hca, hq'⟩ := List.cons_prefix_cons.mp hq
              subst b
              subst c
              rcases ih hp' hq' with hpq | hqp
              · exact Or.inl
                  (List.cons_prefix_cons.mpr ⟨rfl, hpq⟩)
              · exact Or.inr
                  (List.cons_prefix_cons.mpr ⟨rfl, hqp⟩)

/-- If a retained vertex is above the contraction root, its original
descendant branches split into the retained branches and exactly the
branches of the removed rooted subtree. -/
theorem retainedBranches_union_removed {t : PlaneTree}
    (r : VPos t) (v : VPos (contractAt t r.1))
    (hvr : (contractVertex r.2 v).1 <+: r.1) :
    ((branchNodesUnder (contractVertex r.2 v)).filter
        (fun u => ¬r.1 <+: u.1)) ∪ branchNodesUnder r =
      branchNodesUnder (contractVertex r.2 v) := by
  ext u
  simp only [Finset.mem_union, branchNodesUnder, Finset.mem_filter]
  constructor
  · rintro (⟨⟨huBranch, hvu⟩, _hru⟩ | ⟨huBranch, hru⟩)
    · exact ⟨huBranch, hvu⟩
    · exact ⟨huBranch, hvr.trans hru⟩
  · rintro ⟨huBranch, hvu⟩
    by_cases hru : r.1 <+: u.1
    · exact Or.inr ⟨huBranch, hru⟩
    · exact Or.inl ⟨⟨huBranch, hvu⟩, hru⟩

/-- The retained and removed branch pieces are disjoint. -/
theorem retainedBranches_disjoint_removed {t : PlaneTree}
    (r : VPos t) (v : VPos (contractAt t r.1)) :
    Disjoint
      ((branchNodesUnder (contractVertex r.2 v)).filter
        (fun u => ¬r.1 <+: u.1))
      (branchNodesUnder r) := by
  exact Finset.disjoint_left.mpr fun u huRetained huRemoved =>
    (Finset.mem_filter.mp huRetained).2
      (Finset.mem_filter.mp huRemoved).2

/-- If the retained vertex and contraction root are incomparable, no branch
below the retained vertex is removed. -/
theorem retainedBranches_eq_all_of_incomparable {t : PlaneTree}
    (r : VPos t) (v : VPos (contractAt t r.1))
    (hvr : ¬(contractVertex r.2 v).1 <+: r.1)
    (hrv : ¬r.1 <+: (contractVertex r.2 v).1) :
    (branchNodesUnder (contractVertex r.2 v)).filter
        (fun u => ¬r.1 <+: u.1) =
      branchNodesUnder (contractVertex r.2 v) := by
  apply Finset.filter_eq_self.mpr
  intro u hu hru
  have hvu := (Finset.mem_filter.mp hu).2
  rcases listPrefixes_comparable hvu hru with hvr' | hrv'
  · exact hvr hvr'
  · exact hrv hrv'

/-- When the retained branch is above `r`, the original parent of `r`
belongs to the retained descendant-branch set. -/
theorem parent_mem_retainedBranches {t : PlaneTree}
    (ht : t.isValid = true) (r : VPos t)
    (hr0 : r ≠ rootV t) (hrBranch : r ∈ BranchNodes t)
    (v : VPos (contractAt t r.1))
    (hvBranch : v ∈ BranchNodes (contractAt t r.1))
    (hvr : (contractVertex r.2 v).1 <+: r.1) :
    parentV r ∈
      (branchNodesUnder (contractVertex r.2 v)).filter
        (fun u => ¬r.1 <+: u.1) := by
  have hrv :
      ¬r.1 <+: (contractVertex r.2 v).1 :=
    not_prefix_of_mem_BranchNodes_contractAt r.2 v hvBranch
  have hvNeR : (contractVertex r.2 v).1 ≠ r.1 := by
    intro h
    apply hrv
    rw [h]
  have hvParent :
      (contractVertex r.2 v).1 <+: (parentV r).1 :=
    prefix_dropLast_of_prefix_ne hvr hvNeR
  have hrNotParent : ¬r.1 <+: (parentV r).1 := by
    intro h
    have hle := h.length_le
    change r.1.length ≤ r.1.dropLast.length at hle
    rw [List.length_dropLast] at hle
    have hpos : 0 < r.1.length :=
      List.length_pos_iff.mpr (ne_root_iff.mp hr0)
    omega
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr
      ⟨parentV_mem_BranchNodes_of_branch ht hrBranch hr0, hvParent⟩,
      hrNotParent⟩

/-- **Accumulated-scale absorption for contraction.**  If the marker's extra
parent mass absorbs the removed subtree's accumulated scale, then every
contracted branch has at least the accumulated scale of its original
representative.  This is the arithmetic input expected by
`satisfiesSubtreeDiameter_contract_of_accumulatedScale`. -/
theorem accumulatedScale_le_contract {t : PlaneTree}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t) (r : VPos t)
    (hr0 : r ≠ rootV t) (hrBranch : r ∈ BranchNodes t)
    (s : ℕ) (hs : 1 ≤ s)
    (habsorb :
      accumulatedScale Nm mu r ≤ s * scaleN Nm (parentV r))
    (v : VPos (contractAt t r.1))
    (hvBranch : v ∈ BranchNodes (contractAt t r.1)) :
    accumulatedScale Nm mu (contractVertex r.2 v) ≤
      accumulatedScale (contractMarking Nm r)
        (contractMultiplicities mu r s hs) v := by
  rw [accumulatedScale_contract_eq_retained_sum
    Nm mu r hr0 hrBranch s hs v]
  unfold accumulatedScale
  have hrv :
      ¬r.1 <+: (contractVertex r.2 v).1 :=
    not_prefix_of_mem_BranchNodes_contractAt r.2 v hvBranch
  by_cases hvr : (contractVertex r.2 v).1 <+: r.1
  · have hunion :=
      retainedBranches_union_removed r v hvr
    have hdisjoint :=
      retainedBranches_disjoint_removed r v
    have hpMem :=
      parent_mem_retainedBranches ht r hr0 hrBranch v hvBranch hvr
    have horiginal :
        (∑ u ∈ branchNodesUnder (contractVertex r.2 v),
            gammaInf mu u * scaleN Nm u) =
          (∑ u ∈
              (branchNodesUnder (contractVertex r.2 v)).filter
                (fun u => ¬r.1 <+: u.1),
              gammaInf mu u * scaleN Nm u) +
            ∑ u ∈ branchNodesUnder r,
              gammaInf mu u * scaleN Nm u := by
      conv_lhs =>
        rw [← hunion, Finset.sum_union hdisjoint]
    have hbonus :
        (∑ u ∈
            (branchNodesUnder (contractVertex r.2 v)).filter
              (fun u => ¬r.1 <+: u.1),
            (gammaInf mu u + if u = parentV r then s else 0) *
              scaleN Nm u) =
          (∑ u ∈
              (branchNodesUnder (contractVertex r.2 v)).filter
                (fun u => ¬r.1 <+: u.1),
              gammaInf mu u * scaleN Nm u) +
            s * scaleN Nm (parentV r) := by
      simp_rw [Nat.add_mul]
      rw [Finset.sum_add_distrib]
      congr 1
      simp [hpMem]
    rw [horiginal, hbonus]
    exact Nat.add_le_add_left
      (by simpa [accumulatedScale] using habsorb) _
  · rw [retainedBranches_eq_all_of_incomparable r v hvr hrv]
    apply Finset.sum_le_sum
    intro u _hu
    exact Nat.mul_le_mul_right _
      (Nat.le_add_right (gammaInf mu u)
        (if u = parentV r then s else 0))

/-- Direct diameter-transport interface with the corrected absorption
hypothesis. -/
theorem satisfiesSubtreeDiameter_contract {t : PlaneTree}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (r : VPos t) (hr0 : r ≠ rootV t)
    (hrBranch : r ∈ BranchNodes t)
    (lstar : InsideLeaf r)
    (s : ℕ) (hs : 1 ≤ s)
    (hz : SatisfiesSubtreeDiameter Nm mu z)
    (habsorb :
      accumulatedScale Nm mu r ≤ s * scaleN Nm (parentV r)) :
    SatisfiesSubtreeDiameter (contractMarking Nm r)
      (contractMultiplicities mu r s hs)
      (contractEmbedding z r lstar) := by
  apply satisfiesSubtreeDiameter_contract_of_accumulatedScale
    Nm mu z r lstar s hs hz
  intro v hv
  exact accumulatedScale_le_contract ht Nm mu r hr0 hrBranch
    s hs habsorb v hv

/-- Eligibility supplies the absorption hypothesis automatically (already
with factor eight to spare). -/
theorem accumulatedScale_le_contract_of_eligible {t : PlaneTree}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t) (r : VPos t)
    (hr : CollapseEligible Nm mu r)
    (s : ℕ) (hs : 1 ≤ s)
    (v : VPos (contractAt t r.1))
    (hvBranch : v ∈ BranchNodes (contractAt t r.1)) :
    accumulatedScale Nm mu (contractVertex r.2 v) ≤
      accumulatedScale (contractMarking Nm r)
        (contractMultiplicities mu r s hs) v := by
  have hrData := Finset.mem_erase.mp hr.1
  have habsorb :
      accumulatedScale Nm mu r ≤ s * scaleN Nm (parentV r) := by
    calc
      accumulatedScale Nm mu r ≤ scaleN Nm (parentV r) :=
        eligible_accumulated_le_parent hr
      _ = 1 * scaleN Nm (parentV r) := by simp
      _ ≤ s * scaleN Nm (parentV r) :=
        Nat.mul_le_mul_right _ hs
  exact accumulatedScale_le_contract ht Nm mu r hrData.1 hrData.2
    s hs habsorb v hvBranch

/-- Paper-facing eligible form of contracted diameter transport. -/
theorem satisfiesSubtreeDiameter_contract_of_eligible {t : PlaneTree}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (r : VPos t) (hr : CollapseEligible Nm mu r)
    (lstar : InsideLeaf r)
    (s : ℕ) (hs : 1 ≤ s)
    (hz : SatisfiesSubtreeDiameter Nm mu z) :
    SatisfiesSubtreeDiameter (contractMarking Nm r)
      (contractMultiplicities mu r s hs)
      (contractEmbedding z r lstar) := by
  apply satisfiesSubtreeDiameter_contract_of_accumulatedScale
    Nm mu z r lstar s hs hz
  intro v hv
  exact accumulatedScale_le_contract_of_eligible
    ht Nm mu r hr s hs v hv

end

end Anderson4D
