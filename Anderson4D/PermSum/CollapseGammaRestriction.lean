import Anderson4D.PermSum.CollapseEmbedding

/-!
# Gamma-two transport under subtree restriction

Restriction preserves the child, simple-leaf, and compound-leaf terms in
`γ²` exactly.  This is the branch-power input for the restricted
Proposition 5.10 call in the collapse induction.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

set_option warningAsError true
set_option autoImplicit false

noncomputable section

/-- Simple leaf children map exactly under restriction of the compound set. -/
theorem map_simpleChildren_restrict {t : PlaneTree} (r : VPos t)
    (compound : Finset (VPos t))
    (v : VPos (subtreeAt t r.1)) :
    (childrenOf v ∩
        simpleLeaves (subtreeAt t r.1)
          (restrictCompound r compound)).map
        (subtreeVertexEmbedding r) =
      childrenOf (subtreeVertex r v) ∩ simpleLeaves t compound := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hx
    rcases Finset.mem_inter.mp hw with ⟨hwChild, hwSimple⟩
    rcases Finset.mem_sdiff.mp hwSimple with
      ⟨hwLeaf, hwNotCompound⟩
    exact Finset.mem_inter.mpr
      ⟨(mem_childrenOf_subtreeVertex_iff r v w).mp hwChild,
        Finset.mem_sdiff.mpr
          ⟨(mem_Leaves_subtreeVertex_iff r w).mp hwLeaf,
            fun hcompound =>
              hwNotCompound
                ((mem_restrictCompound r compound w).mpr hcompound)⟩⟩
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxChild, hxSimple⟩
    have hxMapped :
        x ∈ (childrenOf v).map (subtreeVertexEmbedding r) := by
      rw [map_childrenOf_subtreeVertex]
      exact hxChild
    obtain ⟨w, hwChild, hwEq⟩ := Finset.mem_map.mp hxMapped
    apply Finset.mem_map.mpr
    refine ⟨w, Finset.mem_inter.mpr ⟨hwChild, ?_⟩, hwEq⟩
    rcases Finset.mem_sdiff.mp hxSimple with
      ⟨hxLeaf, hxNotCompound⟩
    have hwEq' : subtreeVertex r w = x := hwEq
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact (mem_Leaves_subtreeVertex_iff r w).mpr (by
        rw [hwEq']
        exact hxLeaf)
    · intro hwCompound
      apply hxNotCompound
      rw [← hwEq']
      exact (mem_restrictCompound r compound w).mp hwCompound

/-- Compound leaf children map exactly under restriction. -/
theorem map_compoundChildren_restrict {t : PlaneTree} (r : VPos t)
    (compound : Finset (VPos t))
    (v : VPos (subtreeAt t r.1)) :
    (childrenOf v ∩
        compoundLeaves (subtreeAt t r.1)
          (restrictCompound r compound)).map
        (subtreeVertexEmbedding r) =
      childrenOf (subtreeVertex r v) ∩ compoundLeaves t compound := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hx
    rcases Finset.mem_inter.mp hw with ⟨hwChild, hwCompound⟩
    rcases Finset.mem_inter.mp hwCompound with
      ⟨hwLeaf, hwMem⟩
    exact Finset.mem_inter.mpr
      ⟨(mem_childrenOf_subtreeVertex_iff r v w).mp hwChild,
        Finset.mem_inter.mpr
          ⟨(mem_Leaves_subtreeVertex_iff r w).mp hwLeaf,
            (mem_restrictCompound r compound w).mp hwMem⟩⟩
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxChild, hxCompound⟩
    rcases Finset.mem_inter.mp hxCompound with ⟨hxLeaf, hxMem⟩
    have hxMapped :
        x ∈ (childrenOf v).map (subtreeVertexEmbedding r) := by
      rw [map_childrenOf_subtreeVertex]
      exact hxChild
    obtain ⟨w, hwChild, hwEq⟩ := Finset.mem_map.mp hxMapped
    have hwEq' : subtreeVertex r w = x := hwEq
    apply Finset.mem_map.mpr
    refine ⟨w, Finset.mem_inter.mpr ⟨hwChild, ?_⟩, hwEq⟩
    exact Finset.mem_inter.mpr
      ⟨(mem_Leaves_subtreeVertex_iff r w).mpr (by
          rw [hwEq']
          exact hxLeaf),
        (mem_restrictCompound r compound w).mpr (by
          rw [hwEq']
          exact hxMem)⟩

/-- `γ²` is unchanged at every branch of the restricted subtree. -/
@[simp]
theorem gamma2_restrictMultiplicities {t : PlaneTree}
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (r : VPos t) (v : VPos (subtreeAt t r.1)) :
    gamma2 (restrictMultiplicities mu r)
        (restrictCompound r compound) v =
      gamma2 mu compound (subtreeVertex r v) := by
  have hchildren := congrArg Finset.card
    (map_childrenOf_subtreeVertex r v)
  simp only [Finset.card_map] at hchildren
  have hsimple := congrArg Finset.card
    (map_simpleChildren_restrict r compound v)
  simp only [Finset.card_map] at hsimple
  have hsum :
      (∑ l ∈ childrenOf v ∩
          compoundLeaves (subtreeAt t r.1)
            (restrictCompound r compound),
          ((restrictMultiplicities mu r).m l - 1)) =
        ∑ l ∈ childrenOf (subtreeVertex r v) ∩
            compoundLeaves t compound,
          (mu.m l - 1) := by
    calc
      (∑ l ∈ childrenOf v ∩
          compoundLeaves (subtreeAt t r.1)
            (restrictCompound r compound),
          ((restrictMultiplicities mu r).m l - 1)) =
        ∑ l ∈
            (childrenOf v ∩
              compoundLeaves (subtreeAt t r.1)
                (restrictCompound r compound)).map
              (subtreeVertexEmbedding r),
          (mu.m l - 1) := by
        rw [Finset.sum_map]
        rfl
      _ = ∑ l ∈ childrenOf (subtreeVertex r v) ∩
            compoundLeaves t compound,
          (mu.m l - 1) := by
        rw [map_compoundChildren_restrict]
  unfold gamma2
  rw [hchildren, hsimple, hsum]

end

end Anderson4D
