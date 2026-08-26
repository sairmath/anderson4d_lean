import Anderson4D.DetParametrix.Core.ResidualPrimitiveRouting

/-!
# Complete primitive closed partitions

The block collapses in paper Sections 4.1--4.2 use the same finite
combinatorial object: a list of nonempty, pairwise-disjoint, closed primitive
blocks which covers the ambient carrier.  This file packages exactly those
properties, independently of any particular R-322 or R-324 construction.

The package is the input to the multiplicity-free product reindexing of a
fixed pairing fibre.  Its elementary consequences below make the two
bookkeeping points explicit: the ambient pairing is full, and the sum of the
half-cardinalities of the blocks is exactly half the ambient cardinality.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- A complete primitive closed block partition for one ambient pairing. -/
structure PrimitiveBlockPartition
    {n : ℕ} (κ : PartialPairing (Fin n)) where
  blocks : List (Finset (Fin n))
  pairwise_disjoint : blocks.Pairwise Disjoint
  cover : finsetUnionList blocks = Finset.univ
  nonempty : blocks.Forall Finset.Nonempty
  fullyPaired : blocks.Forall (IsFullyPairedOn κ)
  primitive : blocks.Forall (IsRelPrimitiveOn κ)

namespace PrimitiveBlockPartition

variable {n : ℕ} {κ : PartialPairing (Fin n)}

theorem block_nonempty
    (P : PrimitiveBlockPartition κ)
    {B : Finset (Fin n)} (hB : B ∈ P.blocks) :
    B.Nonempty :=
  List.forall_iff_forall_mem.mp P.nonempty B hB

theorem block_fullyPaired
    (P : PrimitiveBlockPartition κ)
    {B : Finset (Fin n)} (hB : B ∈ P.blocks) :
    IsFullyPairedOn κ B :=
  List.forall_iff_forall_mem.mp P.fullyPaired B hB

theorem block_primitive
    (P : PrimitiveBlockPartition κ)
    {B : Finset (Fin n)} (hB : B ∈ P.blocks) :
    IsRelPrimitiveOn κ B :=
  List.forall_iff_forall_mem.mp P.primitive B hB

/-- Every ambient index belongs to at least one scheduled block. -/
theorem exists_block_mem
    (P : PrimitiveBlockPartition κ) (i : Fin n) :
    ∃ B ∈ P.blocks, i ∈ B := by
  have hi :
      i ∈ finsetUnionList P.blocks := by
    rw [P.cover]
    exact Finset.mem_univ i
  exact (mem_finsetUnionList_iff P.blocks).mp hi

/-- Pairwise disjointness makes the scheduled block containing an index
unique. -/
theorem block_eq_of_mem
    (P : PrimitiveBlockPartition κ)
    {B C : Finset (Fin n)}
    (hB : B ∈ P.blocks) (hC : C ∈ P.blocks)
    {i : Fin n} (hiB : i ∈ B) (hiC : i ∈ C) :
    B = C := by
  by_contra hBC
  have hdisjoint : Disjoint B C :=
    P.pairwise_disjoint.forall hB hC hBC
  exact (Finset.disjoint_left.mp hdisjoint hiB) hiC

/-- A complete partition by fully paired blocks contains no fixed point. -/
theorem isFull
    (P : PrimitiveBlockPartition κ) :
    κ.IsFull := by
  intro i hiFix
  obtain ⟨B, hB, hiB⟩ := P.exists_block_mem i
  exact (P.block_fullyPaired hB).ne_of_mem hiB hiFix

/-- Every scheduled block has positive primitive order. -/
theorem one_le_blockOrder
    (P : PrimitiveBlockPartition κ)
    {B : Finset (Fin n)} (hB : B ∈ P.blocks) :
    1 ≤ residualBlockOrder B := by
  have heven :
      Even B.card :=
    residualBlock_card_even κ B (P.block_fullyPaired hB)
  have hcard : 0 < B.card :=
    Finset.card_pos.mpr (P.block_nonempty hB)
  obtain ⟨q, hq⟩ := heven
  unfold residualBlockOrder
  rw [hq]
  omega

/-- The block cardinalities add to the complete ambient cardinality. -/
theorem sum_blockCards
    (P : PrimitiveBlockPartition κ) :
    (P.blocks.map Finset.card).sum = n := by
  calc
    (P.blocks.map Finset.card).sum =
        (finsetUnionList P.blocks).card :=
      (card_finsetUnionList_eq_sum_card
        P.blocks P.pairwise_disjoint).symm
    _ = (Finset.univ : Finset (Fin n)).card := by
      rw [P.cover]
    _ = n := by simp

/-- Exact global order ledger.  This is the generic no-hidden-power form
used by both R-322 and R-324. -/
theorem two_mul_sum_blockOrders
    (P : PrimitiveBlockPartition κ) :
    2 * (P.blocks.map residualBlockOrder).sum = n := by
  have heven :
      P.blocks.Forall fun B => Even B.card :=
    P.fullyPaired.imp fun B hB =>
      residualBlock_card_even κ B hB
  exact
    (two_mul_sum_residualBlockOrder_eq_sum_card
      P.blocks heven).trans P.sum_blockCards

end PrimitiveBlockPartition

end

end Anderson4D
