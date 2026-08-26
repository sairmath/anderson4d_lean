import Anderson4D.DetParametrix.Paper41_Renorm.R322ReductionClosure

/-!
# Multi-block endpoint fibres for R-322

This file continues the all-order closure after the partition and terminal
primitive identities.  A member of a fixed endpoint-signature fibre is
recorded by its increasingly ordered primitive restriction on every concrete
Definition 3.1 extraction block.  The first result below is the exact
faithfulness statement: those block coordinates determine the ambient pairing
with no quotient and no multiplicity.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The complete primitive coordinate family -/

/-- The concrete blocks in the Definition 3.1 schedule, retaining their
membership proofs so that dependent primitive orders can be used. -/
abbrev ExtractionBlockIndex
    {m : ℕ} (κ : PartialPairing (Fin m)) :=
  {B : Finset (Fin m) // B ∈ extractionBlocks κ}

/-- One standard primitive pairing coordinate on every concrete extraction
block. -/
abbrev ExtractionPrimitiveCoordinates
    {m : ℕ} (κ : PartialPairing (Fin m)) :=
  ∀ B : ExtractionBlockIndex κ,
    {τ : PartialPairing
        (Fin (2 * residualBlockOrder B.1)) //
      τ ∈ primitiveFullPairings
        (residualBlockOrder B.1)}

/-- A signature-fibre member is fully paired on every reference extraction
block. -/
theorem endpointFiber_isFullyPairedOn_extractionBlock
    {m : ℕ} (κ : PartialPairing (Fin m))
    (τ : ReductionEndpointFiberAt κ)
    (B : ExtractionBlockIndex κ) :
    IsFullyPairedOn τ.1 B.1 := by
  apply extractionBlock_isFullyPairedOn_of_mem
  rw [extractionBlocks_eq_of_reductionEndpointSignature_eq
    τ.1 κ τ.2]
  exact B.2

/-- A signature-fibre member is relatively primitive on every reference
extraction block. -/
theorem endpointFiber_isRelPrimitiveOn_extractionBlock
    {m : ℕ} (κ : PartialPairing (Fin m))
    (τ : ReductionEndpointFiberAt κ)
    (B : ExtractionBlockIndex κ) :
    IsRelPrimitiveOn τ.1 B.1 := by
  apply extractionBlock_isRelPrimitiveOn_of_mem
  rw [extractionBlocks_eq_of_reductionEndpointSignature_eq
    τ.1 κ τ.2]
  exact B.2

/-- Increasing standardization of one reference block of a
signature-fibre member. -/
def endpointFiberPrimitiveCoordinate
    {m : ℕ} (κ : PartialPairing (Fin m))
    (τ : ReductionEndpointFiberAt κ)
    (B : ExtractionBlockIndex κ) :
    {σ : PartialPairing
        (Fin (2 * residualBlockOrder B.1)) //
      σ ∈ primitiveFullPairings
        (residualBlockOrder B.1)} := by
  let hκB :
      IsFullyPairedOn κ B.1 :=
    extractionBlock_isFullyPairedOn_of_mem
      κ B.1 B.2
  let hτB :
      IsFullyPairedOn τ.1 B.1 :=
    endpointFiber_isFullyPairedOn_extractionBlock
      κ τ B
  let e :=
    residualPrimitiveBlockOrderIso
      κ B.1 hκB
  refine
    ⟨orderedBlockPairing τ.1 B.1 hτB e, ?_⟩
  rw [mem_primitiveFullPairings]
  exact
    ⟨orderedBlockPairing_isFull
        τ.1 B.1 hτB e,
      orderedBlockPairing_isPrimitive
        τ.1 B.1 hτB
        (endpointFiber_isRelPrimitiveOn_extractionBlock
          κ τ B) e⟩

/-- All primitive block coordinates of one endpoint-fibre member. -/
def endpointFiberPrimitiveCoordinates
    {m : ℕ} (κ : PartialPairing (Fin m))
    (τ : ReductionEndpointFiberAt κ) :
    ExtractionPrimitiveCoordinates κ :=
  fun B => endpointFiberPrimitiveCoordinate κ τ B

/-- Evaluation of a standardized block coordinate recovers the ambient
pairing on that block. -/
theorem endpointFiberPrimitiveCoordinate_apply
    {m : ℕ} (κ : PartialPairing (Fin m))
    (τ : ReductionEndpointFiberAt κ)
    (B : ExtractionBlockIndex κ)
    (j : Fin (2 * residualBlockOrder B.1)) :
    ((residualPrimitiveBlockOrderIso κ B.1
        (extractionBlock_isFullyPairedOn_of_mem
          κ B.1 B.2))
      ((endpointFiberPrimitiveCoordinate κ τ B).1 j)).1 =
      τ.1
        ((residualPrimitiveBlockOrderIso κ B.1
          (extractionBlock_isFullyPairedOn_of_mem
            κ B.1 B.2)) j).1 := by
  exact orderedBlockPairing_apply
    τ.1 B.1
      (endpointFiber_isFullyPairedOn_extractionBlock
        κ τ B)
      (residualPrimitiveBlockOrderIso κ B.1
        (extractionBlock_isFullyPairedOn_of_mem
          κ B.1 B.2)) j

/-- The complete family of primitive block coordinates is faithful.  This is
the multiplicity-free component of the multi-block product equivalence. -/
theorem endpointFiberPrimitiveCoordinates_injective
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull) :
    Function.Injective
      (endpointFiberPrimitiveCoordinates κ) := by
  intro τ υ hcoordinates
  apply Subtype.ext
  apply PartialPairing.ext
  intro i
  obtain ⟨B, hB, hiB⟩ :=
    mem_extractionBlock_of_full κ hκ i
  let BI : ExtractionBlockIndex κ := ⟨B, hB⟩
  let e :=
    residualPrimitiveBlockOrderIso κ B
      (extractionBlock_isFullyPairedOn_of_mem
        κ B hB)
  let j : Fin (2 * residualBlockOrder B) :=
    e.symm ⟨i, hiB⟩
  have hej : e j = ⟨i, hiB⟩ :=
    e.apply_symm_apply ⟨i, hiB⟩
  have hcoordinate :
      endpointFiberPrimitiveCoordinate κ τ BI =
        endpointFiberPrimitiveCoordinate κ υ BI :=
    congrFun hcoordinates BI
  have happly :
      (endpointFiberPrimitiveCoordinate κ τ BI).1 j =
        (endpointFiberPrimitiveCoordinate κ υ BI).1 j :=
    congrArg (fun σ =>
      σ.1 j) hcoordinate
  have hτeval :
      (e
        ((endpointFiberPrimitiveCoordinate
          κ τ BI).1 j)).1 =
        τ.1 (e j).1 := by
    simpa only [e, BI] using
      endpointFiberPrimitiveCoordinate_apply
        κ τ BI j
  have hυeval :
      (e
        ((endpointFiberPrimitiveCoordinate
          κ υ BI).1 j)).1 =
        υ.1 (e j).1 := by
    simpa only [e, BI] using
      endpointFiberPrimitiveCoordinate_apply
        κ υ BI j
  calc
    τ.1 i = τ.1 (e j).1 := by
      exact congrArg τ.1
        (congrArg Subtype.val hej).symm
    _ =
        (e
          ((endpointFiberPrimitiveCoordinate
            κ τ BI).1 j)).1 := by
      exact hτeval.symm
    _ =
        (e
          ((endpointFiberPrimitiveCoordinate
            κ υ BI).1 j)).1 := by
      rw [happly]
    _ = υ.1 (e j).1 := hυeval
    _ = υ.1 i := by
      exact congrArg υ.1
        (congrArg Subtype.val hej)

/-! ## Reassembling a coordinate family -/

/-- In a pairwise-disjoint list, two members which meet are equal. -/
theorem eq_of_mem_of_mem_of_pairwise_disjoint
    {α : Type*} [DecidableEq α]
    {blocks : List (Finset α)}
    (hpairwise : blocks.Pairwise Disjoint)
    {B C : Finset α}
    (hB : B ∈ blocks) (hC : C ∈ blocks)
    {i : α} (hiB : i ∈ B) (hiC : i ∈ C) :
    B = C := by
  induction blocks generalizing B C with
  | nil =>
      simp at hB
  | cons A blocks ih =>
      rw [List.pairwise_cons] at hpairwise
      simp only [List.mem_cons] at hB hC
      rcases hB with hBA | hB
      · subst B
        rcases hC with hCA | hC
        · exact hCA.symm
        · exfalso
          exact
            (Finset.disjoint_left.mp
              (hpairwise.1 C hC)) hiB hiC
      · rcases hC with hCA | hC
        · subst C
          exfalso
          exact
            (Finset.disjoint_left.mp
              (hpairwise.1 B hB)) hiC hiB
        · exact ih hpairwise.2 hB hC hiB hiC

/-- The unique concrete extraction block containing an index of a full
pairing. -/
def extractionBlockAt
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull) (i : Fin m) :
    ExtractionBlockIndex κ :=
  let h :=
    mem_extractionBlock_of_full κ hκ i
  ⟨Classical.choose h,
    (Classical.choose_spec h).1⟩

theorem extractionBlockAt_contains
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull) (i : Fin m) :
    i ∈ (extractionBlockAt κ hκ i).1 := by
  unfold extractionBlockAt
  exact
    (Classical.choose_spec
      (mem_extractionBlock_of_full κ hκ i)).2

/-- Characterization of the chosen block by membership. -/
theorem extractionBlockAt_eq
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull) (i : Fin m)
    (B : ExtractionBlockIndex κ)
    (hiB : i ∈ B.1) :
    extractionBlockAt κ hκ i = B := by
  apply Subtype.ext
  exact eq_of_mem_of_mem_of_pairwise_disjoint
    (extractionBlocks_pairwise_disjoint κ)
    (extractionBlockAt κ hκ i).2 B.2
    (extractionBlockAt_contains κ hκ i) hiB

/-- Apply a complete coordinate family on the unique extraction block
containing the input index. -/
def extractionPrimitiveCoordinatesApply
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (coordinates : ExtractionPrimitiveCoordinates κ)
    (i : Fin m) : Fin m :=
  let B := extractionBlockAt κ hκ i
  let e :=
    residualPrimitiveBlockOrderIso κ B.1
      (extractionBlock_isFullyPairedOn_of_mem
        κ B.1 B.2)
  (e ((coordinates B).1
    (e.symm
      ⟨i, extractionBlockAt_contains κ hκ i⟩))).1

/-- Controlled unfolding equation for blockwise coordinate application. -/
theorem extractionPrimitiveCoordinatesApply_eq
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (coordinates : ExtractionPrimitiveCoordinates κ)
    (i : Fin m) :
    extractionPrimitiveCoordinatesApply κ hκ coordinates i =
      let B := extractionBlockAt κ hκ i
      let e :=
        residualPrimitiveBlockOrderIso κ B.1
          (extractionBlock_isFullyPairedOn_of_mem
            κ B.1 B.2)
      (e ((coordinates B).1
        (e.symm
          ⟨i, extractionBlockAt_contains κ hκ i⟩))).1 :=
  rfl

/-- Applying a coordinate stays in the same concrete extraction block. -/
theorem extractionPrimitiveCoordinatesApply_mem
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (coordinates : ExtractionPrimitiveCoordinates κ)
    (i : Fin m) :
    extractionPrimitiveCoordinatesApply κ hκ
        coordinates i ∈
      (extractionBlockAt κ hκ i).1 := by
  unfold extractionPrimitiveCoordinatesApply
  exact
    (residualPrimitiveBlockOrderIso κ
      (extractionBlockAt κ hκ i).1
      (extractionBlock_isFullyPairedOn_of_mem
        κ (extractionBlockAt κ hκ i).1
        (extractionBlockAt κ hκ i).2)
      ((coordinates
        (extractionBlockAt κ hκ i)).1
        _)).2

/-- The block lookup is stable under coordinate application. -/
theorem extractionBlockAt_apply
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (coordinates : ExtractionPrimitiveCoordinates κ)
    (i : Fin m) :
    extractionBlockAt κ hκ
        (extractionPrimitiveCoordinatesApply
          κ hκ coordinates i) =
      extractionBlockAt κ hκ i :=
  extractionBlockAt_eq κ hκ _ _
    (extractionPrimitiveCoordinatesApply_mem
      κ hκ coordinates i)

/-- Coordinate application written using any certified block containing the
input, rather than the noncomputable block lookup. -/
theorem extractionPrimitiveCoordinatesApply_of_mem
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (coordinates : ExtractionPrimitiveCoordinates κ)
    (i : Fin m) (B : ExtractionBlockIndex κ)
    (hiB : i ∈ B.1) :
    extractionPrimitiveCoordinatesApply κ hκ coordinates i =
      let e :=
        residualPrimitiveBlockOrderIso κ B.1
          (extractionBlock_isFullyPairedOn_of_mem
            κ B.1 B.2)
      (e ((coordinates B).1
        (e.symm ⟨i, hiB⟩))).1 := by
  rw [extractionPrimitiveCoordinatesApply_eq]
  dsimp only
  have hAB :
      extractionBlockAt κ hκ i = B :=
    extractionBlockAt_eq κ hκ i B hiB
  subst B
  rfl

/-- The blockwise application is an involution because every primitive
coordinate is an involution and its image stays in the same block. -/
theorem extractionPrimitiveCoordinatesApply_involutive
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (coordinates : ExtractionPrimitiveCoordinates κ) :
    Function.Involutive
      (extractionPrimitiveCoordinatesApply
        κ hκ coordinates) := by
  intro i
  let B := extractionBlockAt κ hκ i
  let e :=
    residualPrimitiveBlockOrderIso κ B.1
      (extractionBlock_isFullyPairedOn_of_mem
        κ B.1 B.2)
  let j : Fin (2 * residualBlockOrder B.1) :=
    e.symm ⟨i, extractionBlockAt_contains κ hκ i⟩
  have hej : e j =
      ⟨i, extractionBlockAt_contains κ hκ i⟩ :=
    e.apply_symm_apply _
  have hfirst :
      extractionPrimitiveCoordinatesApply
          κ hκ coordinates i =
        (e ((coordinates B).1 j)).1 := by
    exact extractionPrimitiveCoordinatesApply_of_mem
      κ hκ coordinates i B
        (extractionBlockAt_contains κ hκ i)
  have hout :
      extractionPrimitiveCoordinatesApply
          κ hκ coordinates i ∈ B.1 :=
    extractionPrimitiveCoordinatesApply_mem
      κ hκ coordinates i
  rw [extractionPrimitiveCoordinatesApply_of_mem
    κ hκ coordinates
      (extractionPrimitiveCoordinatesApply
        κ hκ coordinates i) B
      hout]
  dsimp only
  have hinside :
      (⟨extractionPrimitiveCoordinatesApply
          κ hκ coordinates i, hout⟩ : B.1) =
        e ((coordinates B).1 j) := by
    apply Subtype.ext
    exact hfirst
  rw [hinside, e.symm_apply_apply,
    (coordinates B).1.apply_apply]
  exact congrArg Subtype.val hej

/-- Ambient pairing obtained by independently installing every primitive
coordinate on the complete extraction-block partition. -/
def partialPairingOfExtractionPrimitiveCoordinates
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (coordinates : ExtractionPrimitiveCoordinates κ) :
    PartialPairing (Fin m) where
  toFun :=
    extractionPrimitiveCoordinatesApply
      κ hκ coordinates
  involutive :=
    extractionPrimitiveCoordinatesApply_involutive
      κ hκ coordinates

theorem partialPairingOfExtractionPrimitiveCoordinates_apply_of_mem
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (coordinates : ExtractionPrimitiveCoordinates κ)
    (i : Fin m) (B : ExtractionBlockIndex κ)
    (hiB : i ∈ B.1) :
    partialPairingOfExtractionPrimitiveCoordinates
        κ hκ coordinates i =
      let e :=
        residualPrimitiveBlockOrderIso κ B.1
          (extractionBlock_isFullyPairedOn_of_mem
            κ B.1 B.2)
      (e ((coordinates B).1
        (e.symm ⟨i, hiB⟩))).1 :=
  extractionPrimitiveCoordinatesApply_of_mem
    κ hκ coordinates i B hiB

/-- The assembled ambient pairing is closed on every reference block. -/
theorem partialPairingOfExtractionPrimitiveCoordinates_closedOn
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (coordinates : ExtractionPrimitiveCoordinates κ)
    (B : ExtractionBlockIndex κ) :
    ∀ i ∈ B.1,
      partialPairingOfExtractionPrimitiveCoordinates
          κ hκ coordinates i ∈ B.1 := by
  intro i hi
  rw [partialPairingOfExtractionPrimitiveCoordinates_apply_of_mem
    κ hκ coordinates i B hi]
  exact
    (residualPrimitiveBlockOrderIso κ B.1
      (extractionBlock_isFullyPairedOn_of_mem
        κ B.1 B.2)
      ((coordinates B).1 _)).2

/-- Increasing restriction of the assembled pairing is the prescribed
primitive coordinate. -/
theorem orderedBlockPairing_partialPairingOfExtractionPrimitiveCoordinates
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (coordinates : ExtractionPrimitiveCoordinates κ)
    (B : ExtractionBlockIndex κ) :
    orderedClosedBlockPairing B.1
        (residualPrimitiveBlockOrderIso κ B.1
          (extractionBlock_isFullyPairedOn_of_mem
            κ B.1 B.2))
        ⟨partialPairingOfExtractionPrimitiveCoordinates
            κ hκ coordinates,
          partialPairingOfExtractionPrimitiveCoordinates_closedOn
            κ hκ coordinates B⟩ =
      (coordinates B).1 := by
  apply PartialPairing.ext
  intro j
  let e :=
    residualPrimitiveBlockOrderIso κ B.1
      (extractionBlock_isFullyPairedOn_of_mem
        κ B.1 B.2)
  apply e.injective
  apply Subtype.ext
  have hordered :
      (e
        (orderedClosedBlockPairing B.1 e
          ⟨partialPairingOfExtractionPrimitiveCoordinates
              κ hκ coordinates,
            partialPairingOfExtractionPrimitiveCoordinates_closedOn
              κ hκ coordinates B⟩ j)).1 =
        partialPairingOfExtractionPrimitiveCoordinates
          κ hκ coordinates (e j).1 := by
    unfold orderedClosedBlockPairing
    rw [PartialPairing.congr_apply_apply]
    change
      (e
        (e.symm
          (PartialPairing.restrictTo
            (partialPairingOfExtractionPrimitiveCoordinates
              κ hκ coordinates)
            (partialPairingOfExtractionPrimitiveCoordinates_closedOn
              κ hκ coordinates B)
            (e j)))).1 =
        partialPairingOfExtractionPrimitiveCoordinates
          κ hκ coordinates (e j).1
    rw [e.apply_symm_apply]
    rfl
  calc
    (e
      (orderedClosedBlockPairing B.1 e
        ⟨partialPairingOfExtractionPrimitiveCoordinates
              κ hκ coordinates,
            partialPairingOfExtractionPrimitiveCoordinates_closedOn
              κ hκ coordinates B⟩ j)).val =
        partialPairingOfExtractionPrimitiveCoordinates
          κ hκ coordinates (e j).1 := hordered
    _ = (e ((coordinates B).1 j)).1 := by
      rw [
        partialPairingOfExtractionPrimitiveCoordinates_apply_of_mem
          κ hκ coordinates (e j).1 B (e j).2]
      change
        (e ((coordinates B).1
          (e.symm (e j)))).1 =
            (e ((coordinates B).1 j)).1
      rw [e.symm_apply_apply]

/-- The assembled ambient pairing, certified as primitive on one concrete
reference block. -/
def partialPairingOfExtractionPrimitiveCoordinates_primitiveClosedOn
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (coordinates : ExtractionPrimitiveCoordinates κ)
    (B : ExtractionBlockIndex κ) :
    PrimitiveClosedOn (residualBlockOrder B.1) B.1
      (residualPrimitiveBlockOrderIso κ B.1
        (extractionBlock_isFullyPairedOn_of_mem
          κ B.1 B.2)) :=
  ⟨⟨partialPairingOfExtractionPrimitiveCoordinates
        κ hκ coordinates,
      partialPairingOfExtractionPrimitiveCoordinates_closedOn
        κ hκ coordinates B⟩,
    by
      rw [
        orderedBlockPairing_partialPairingOfExtractionPrimitiveCoordinates
          κ hκ coordinates B]
      exact (coordinates B).2⟩

theorem partialPairingOfExtractionPrimitiveCoordinates_isFullyPairedOn
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (coordinates : ExtractionPrimitiveCoordinates κ)
    (B : ExtractionBlockIndex κ) :
    IsFullyPairedOn
      (partialPairingOfExtractionPrimitiveCoordinates
        κ hκ coordinates) B.1 :=
  (partialPairingOfExtractionPrimitiveCoordinates_primitiveClosedOn
    κ hκ coordinates B).isFullyPairedOn

theorem partialPairingOfExtractionPrimitiveCoordinates_isRelPrimitiveOn
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (coordinates : ExtractionPrimitiveCoordinates κ)
    (B : ExtractionBlockIndex κ) :
    IsRelPrimitiveOn
      (partialPairingOfExtractionPrimitiveCoordinates
        κ hκ coordinates) B.1 :=
  (partialPairingOfExtractionPrimitiveCoordinates_primitiveClosedOn
    κ hκ coordinates B).isRelPrimitiveOn

/-! ## Carrier-generic primitive-partition product equivalence -/

/-- Blocks of an arbitrary complete primitive partition. -/
abbrev PrimitivePartitionBlockIndex
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ) :=
  {B : Finset (Fin n) // B ∈ P.blocks}

/-- Independent standard primitive pairing coordinates on all blocks of an
arbitrary complete primitive partition. -/
abbrev PrimitivePartitionCoordinates
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ) :=
  ∀ B : PrimitivePartitionBlockIndex P,
    {τ : PartialPairing
        (Fin (2 * residualBlockOrder B.1)) //
      τ ∈ primitiveFullPairings
        (residualBlockOrder B.1)}

/-- Ambient pairings which are closed, full, and relatively primitive on
every block of a fixed complete primitive partition. -/
abbrev PrimitivePartitionFiber
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ) :=
  {τ : PartialPairing (Fin n) //
    ∀ B ∈ P.blocks,
      IsFullyPairedOn τ B ∧
        IsRelPrimitiveOn τ B}

/-- Standard primitive coordinates of a generic fixed-block fibre member. -/
def primitivePartitionFiberCoordinates
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ)
    (τ : PrimitivePartitionFiber P) :
    PrimitivePartitionCoordinates P :=
  fun B => by
    let hτB := (τ.2 B.1 B.2).1
    let e :=
      residualPrimitiveBlockOrderIso κ B.1
        (P.block_fullyPaired B.2)
    refine
      ⟨orderedBlockPairing τ.1 B.1 hτB e, ?_⟩
    rw [mem_primitiveFullPairings]
    exact
      ⟨orderedBlockPairing_isFull
          τ.1 B.1 hτB e,
        orderedBlockPairing_isPrimitive
          τ.1 B.1 hτB
          (τ.2 B.1 B.2).2 e⟩

/-- The unique block of a complete primitive partition containing an
ambient index. -/
def primitivePartitionBlockAt
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ) (i : Fin n) :
    PrimitivePartitionBlockIndex P :=
  let h := P.exists_block_mem i
  ⟨Classical.choose h,
    (Classical.choose_spec h).1⟩

theorem primitivePartitionBlockAt_contains
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ) (i : Fin n) :
    i ∈ (primitivePartitionBlockAt P i).1 := by
  unfold primitivePartitionBlockAt
  exact (Classical.choose_spec
    (P.exists_block_mem i)).2

theorem primitivePartitionBlockAt_eq
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ) (i : Fin n)
    (B : PrimitivePartitionBlockIndex P)
    (hiB : i ∈ B.1) :
    primitivePartitionBlockAt P i = B := by
  apply Subtype.ext
  exact P.block_eq_of_mem
    (primitivePartitionBlockAt P i).2 B.2
    (primitivePartitionBlockAt_contains P i) hiB

/-- Blockwise application for a generic primitive partition. -/
def primitivePartitionCoordinatesApply
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ)
    (coordinates : PrimitivePartitionCoordinates P)
    (i : Fin n) : Fin n :=
  let B := primitivePartitionBlockAt P i
  let e :=
    residualPrimitiveBlockOrderIso κ B.1
      (P.block_fullyPaired B.2)
  (e ((coordinates B).1
    (e.symm
      ⟨i, primitivePartitionBlockAt_contains P i⟩))).1

theorem primitivePartitionCoordinatesApply_eq
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ)
    (coordinates : PrimitivePartitionCoordinates P)
    (i : Fin n) :
    primitivePartitionCoordinatesApply P coordinates i =
      let B := primitivePartitionBlockAt P i
      let e :=
        residualPrimitiveBlockOrderIso κ B.1
          (P.block_fullyPaired B.2)
      (e ((coordinates B).1
        (e.symm
          ⟨i, primitivePartitionBlockAt_contains P i⟩))).1 :=
  rfl

theorem primitivePartitionCoordinatesApply_of_mem
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ)
    (coordinates : PrimitivePartitionCoordinates P)
    (i : Fin n) (B : PrimitivePartitionBlockIndex P)
    (hiB : i ∈ B.1) :
    primitivePartitionCoordinatesApply P coordinates i =
      let e :=
        residualPrimitiveBlockOrderIso κ B.1
          (P.block_fullyPaired B.2)
      (e ((coordinates B).1
        (e.symm ⟨i, hiB⟩))).1 := by
  rw [primitivePartitionCoordinatesApply_eq]
  dsimp only
  have hAB :
      primitivePartitionBlockAt P i = B :=
    primitivePartitionBlockAt_eq P i B hiB
  subst B
  rfl

theorem primitivePartitionCoordinatesApply_mem
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ)
    (coordinates : PrimitivePartitionCoordinates P)
    (i : Fin n) :
    primitivePartitionCoordinatesApply P coordinates i ∈
      (primitivePartitionBlockAt P i).1 := by
  unfold primitivePartitionCoordinatesApply
  exact
    (residualPrimitiveBlockOrderIso κ
      (primitivePartitionBlockAt P i).1
      (P.block_fullyPaired
        (primitivePartitionBlockAt P i).2)
      ((coordinates
        (primitivePartitionBlockAt P i)).1 _)).2

theorem primitivePartitionCoordinatesApply_involutive
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ)
    (coordinates : PrimitivePartitionCoordinates P) :
    Function.Involutive
      (primitivePartitionCoordinatesApply
        P coordinates) := by
  intro i
  let B := primitivePartitionBlockAt P i
  let e :=
    residualPrimitiveBlockOrderIso κ B.1
      (P.block_fullyPaired B.2)
  let j : Fin (2 * residualBlockOrder B.1) :=
    e.symm
      ⟨i, primitivePartitionBlockAt_contains P i⟩
  have hej :
      e j =
        ⟨i, primitivePartitionBlockAt_contains P i⟩ :=
    e.apply_symm_apply _
  have hfirst :
      primitivePartitionCoordinatesApply
          P coordinates i =
        (e ((coordinates B).1 j)).1 :=
    primitivePartitionCoordinatesApply_of_mem
      P coordinates i B
        (primitivePartitionBlockAt_contains P i)
  have hout :
      primitivePartitionCoordinatesApply
          P coordinates i ∈ B.1 := by
    rw [hfirst]
    exact (e ((coordinates B).1 j)).2
  rw [primitivePartitionCoordinatesApply_of_mem
    P coordinates
      (primitivePartitionCoordinatesApply
        P coordinates i) B hout]
  dsimp only
  have hinside :
      (⟨primitivePartitionCoordinatesApply
          P coordinates i, hout⟩ : B.1) =
        e ((coordinates B).1 j) := by
    apply Subtype.ext
    exact hfirst
  rw [hinside, e.symm_apply_apply,
    (coordinates B).1.apply_apply]
  exact congrArg Subtype.val hej

/-- Reassemble independent primitive coordinates on a generic complete
partition. -/
def partialPairingOfPrimitivePartitionCoordinates
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ)
    (coordinates : PrimitivePartitionCoordinates P) :
    PartialPairing (Fin n) where
  toFun :=
    primitivePartitionCoordinatesApply P coordinates
  involutive :=
    primitivePartitionCoordinatesApply_involutive
      P coordinates

theorem partialPairingOfPrimitivePartitionCoordinates_apply_of_mem
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ)
    (coordinates : PrimitivePartitionCoordinates P)
    (i : Fin n) (B : PrimitivePartitionBlockIndex P)
    (hiB : i ∈ B.1) :
    partialPairingOfPrimitivePartitionCoordinates
        P coordinates i =
      let e :=
        residualPrimitiveBlockOrderIso κ B.1
          (P.block_fullyPaired B.2)
      (e ((coordinates B).1
        (e.symm ⟨i, hiB⟩))).1 :=
  primitivePartitionCoordinatesApply_of_mem
    P coordinates i B hiB

theorem partialPairingOfPrimitivePartitionCoordinates_closedOn
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ)
    (coordinates : PrimitivePartitionCoordinates P)
    (B : PrimitivePartitionBlockIndex P) :
    ∀ i ∈ B.1,
      partialPairingOfPrimitivePartitionCoordinates
          P coordinates i ∈ B.1 := by
  intro i hi
  rw [partialPairingOfPrimitivePartitionCoordinates_apply_of_mem
    P coordinates i B hi]
  exact
    (residualPrimitiveBlockOrderIso κ B.1
      (P.block_fullyPaired B.2)
      ((coordinates B).1 _)).2

theorem orderedBlockPairing_partialPairingOfPrimitivePartitionCoordinates
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ)
    (coordinates : PrimitivePartitionCoordinates P)
    (B : PrimitivePartitionBlockIndex P) :
    orderedClosedBlockPairing B.1
        (residualPrimitiveBlockOrderIso κ B.1
          (P.block_fullyPaired B.2))
        ⟨partialPairingOfPrimitivePartitionCoordinates
            P coordinates,
          partialPairingOfPrimitivePartitionCoordinates_closedOn
            P coordinates B⟩ =
      (coordinates B).1 := by
  apply PartialPairing.ext
  intro j
  let e :=
    residualPrimitiveBlockOrderIso κ B.1
      (P.block_fullyPaired B.2)
  apply e.injective
  apply Subtype.ext
  have hordered :
      (e
        (orderedClosedBlockPairing B.1 e
          ⟨partialPairingOfPrimitivePartitionCoordinates
              P coordinates,
            partialPairingOfPrimitivePartitionCoordinates_closedOn
              P coordinates B⟩ j)).1 =
        partialPairingOfPrimitivePartitionCoordinates
          P coordinates (e j).1 := by
    unfold orderedClosedBlockPairing
    rw [PartialPairing.congr_apply_apply]
    change
      (e
        (e.symm
          (PartialPairing.restrictTo
            (partialPairingOfPrimitivePartitionCoordinates
              P coordinates)
            (partialPairingOfPrimitivePartitionCoordinates_closedOn
              P coordinates B)
            (e j)))).1 =
        partialPairingOfPrimitivePartitionCoordinates
          P coordinates (e j).1
    rw [e.apply_symm_apply]
    rfl
  calc
    (e
      (orderedClosedBlockPairing B.1 e
        ⟨partialPairingOfPrimitivePartitionCoordinates
              P coordinates,
            partialPairingOfPrimitivePartitionCoordinates_closedOn
              P coordinates B⟩ j)).val =
        partialPairingOfPrimitivePartitionCoordinates
          P coordinates (e j).1 := hordered
    _ = (e ((coordinates B).1 j)).1 := by
      rw [
        partialPairingOfPrimitivePartitionCoordinates_apply_of_mem
          P coordinates (e j).1 B (e j).2]
      change
        (e ((coordinates B).1
          (e.symm (e j)))).1 =
            (e ((coordinates B).1 j)).1
      rw [e.symm_apply_apply]

/-- Generic reassembly belongs to the fixed primitive-block fibre. -/
def primitivePartitionFiberOfCoordinates
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ)
    (coordinates : PrimitivePartitionCoordinates P) :
    PrimitivePartitionFiber P :=
  ⟨partialPairingOfPrimitivePartitionCoordinates
      P coordinates,
    by
      intro B hB
      let BI : PrimitivePartitionBlockIndex P :=
        ⟨B, hB⟩
      let closed :
          PrimitiveClosedOn
            (residualBlockOrder B) B
            (residualPrimitiveBlockOrderIso κ B
              (P.block_fullyPaired hB)) :=
        ⟨⟨partialPairingOfPrimitivePartitionCoordinates
              P coordinates,
            partialPairingOfPrimitivePartitionCoordinates_closedOn
              P coordinates BI⟩,
          by
            rw [
              orderedBlockPairing_partialPairingOfPrimitivePartitionCoordinates
                P coordinates BI]
            exact (coordinates BI).2⟩
      exact
        ⟨closed.isFullyPairedOn,
          closed.isRelPrimitiveOn⟩⟩

/-- Exact carrier-generic product equivalence: a fixed primitive-block fibre
has one independent complete primitive pairing coordinate per block, with no
quotient and no multiplicity. -/
def primitivePartitionFiberEquivCoordinates
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ) :
    PrimitivePartitionFiber P ≃
      PrimitivePartitionCoordinates P where
  toFun :=
    primitivePartitionFiberCoordinates P
  invFun :=
    primitivePartitionFiberOfCoordinates P
  left_inv τ := by
    apply Subtype.ext
    apply PartialPairing.ext
    intro i
    obtain ⟨B, hB, hiB⟩ :=
      P.exists_block_mem i
    let BI : PrimitivePartitionBlockIndex P :=
      ⟨B, hB⟩
    let e :=
      residualPrimitiveBlockOrderIso κ B
        (P.block_fullyPaired hB)
    let j : Fin (2 * residualBlockOrder B) :=
      e.symm ⟨i, hiB⟩
    have hej : e j = ⟨i, hiB⟩ :=
      e.apply_symm_apply _
    have hτapply :
        (e
          ((primitivePartitionFiberCoordinates
            P τ BI).1 j)).1 =
          τ.1 (e j).1 := by
      exact orderedBlockPairing_apply
        τ.1 B (τ.2 B hB).1 e j
    change
      partialPairingOfPrimitivePartitionCoordinates
          P (primitivePartitionFiberCoordinates P τ) i =
        τ.1 i
    rw [
      partialPairingOfPrimitivePartitionCoordinates_apply_of_mem
        P (primitivePartitionFiberCoordinates P τ)
        i BI hiB]
    dsimp only
    calc
      (e
        ((primitivePartitionFiberCoordinates
          P τ BI).1
          (e.symm ⟨i, hiB⟩))).1 =
          (e
            ((primitivePartitionFiberCoordinates
              P τ BI).1 j)).1 := rfl
      _ = τ.1 (e j).1 := hτapply
      _ = τ.1 i := by
        exact congrArg τ.1
          (congrArg Subtype.val hej)
  right_inv coordinates := by
    funext B
    apply Subtype.ext
    exact
      orderedBlockPairing_partialPairingOfPrimitivePartitionCoordinates
        P coordinates B

noncomputable instance instFintypePrimitivePartitionFiber
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ) :
    Fintype (PrimitivePartitionFiber P) :=
  Fintype.ofEquiv
    (PrimitivePartitionCoordinates P)
    (primitivePartitionFiberEquivCoordinates P).symm

/-- Reindex any finite sum over a fixed primitive-block fibre as the exact
dependent product of primitive coordinates. -/
theorem sum_primitivePartitionFiber_eq_sum_coordinates
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ)
    {M : Type*} [AddCommMonoid M]
    (F : PrimitivePartitionFiber P → M) :
    (∑ τ : PrimitivePartitionFiber P, F τ) =
      ∑ coordinates : PrimitivePartitionCoordinates P,
        F ((primitivePartitionFiberEquivCoordinates
          P).symm coordinates) := by
  exact
    ((primitivePartitionFiberEquivCoordinates
      P).symm.sum_comp F).symm

end

end Anderson4D
