import Anderson4D.DetParametrix.Paper41_Renorm.R322FiberIterationClosure

/-!
# Endpoint-signature recovery from primitive block coordinates

The carrier-generic product equivalence only records that every scheduled
block is closed and primitive.  For the concrete Definition 3.1 schedule we
must additionally prove that such a reassembled pairing runs through exactly
the same selected relative intervals.  This file supplies that selector
rigidity and then upgrades the R-322 endpoint fibre to the exact dependent
product of primitive coordinates.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Fully paired relative intervals depend only on primitive blocks -/

/-- A block in a finite block cover lies in the covered active carrier. -/
theorem block_subset_of_finsetUnionList_eq
    {α : Type*} [DecidableEq α]
    {blocks : List (Finset α)} {active B : Finset α}
    (hcover : finsetUnionList blocks = active)
    (hB : B ∈ blocks) :
    B ⊆ active := by
  intro i hi
  rw [← hcover]
  exact (mem_finsetUnionList_iff blocks).mpr
    ⟨B, hB, hi⟩

/-- If two pairings are full on the same block cover and the source pairing
is relatively primitive on every block, every source-fully-paired relative
interval is also fully paired for the target pairing. -/
theorem isFullyPairedOn_relIcc_of_primitive_block_cover
    {m : ℕ} (source target : PartialPairing (Fin m))
    (blocks : List (Finset (Fin m)))
    (active : Finset (Fin m))
    (hcover : finsetUnionList blocks = active)
    (hsourceFull :
      blocks.Forall (IsFullyPairedOn source))
    (hsourcePrimitive :
      blocks.Forall (IsRelPrimitiveOn source))
    (htargetFull :
      blocks.Forall (IsFullyPairedOn target))
    (a b : Fin m)
    (hR :
      IsFullyPairedOn source
        (relIcc active a b)) :
    IsFullyPairedOn target
      (relIcc active a b) := by
  have hblockSubset :
      ∀ B ∈ blocks, B ⊆ active :=
    fun B hB =>
      block_subset_of_finsetUnionList_eq
        hcover hB
  have hblockSubsetR :
      ∀ B ∈ blocks,
        (B ∩ relIcc active a b).Nonempty →
          B ⊆ relIcc active a b := by
    intro B hB hmeet
    have hBsource :
        IsFullyPairedOn source B :=
      List.forall_iff_forall_mem.mp
        hsourceFull B hB
    have hBprimitive :
        IsRelPrimitiveOn source B :=
      List.forall_iff_forall_mem.mp
        hsourcePrimitive B hB
    have hinterEq :
        B ∩ relIcc active a b =
          B ∩ Finset.Icc a b := by
      ext i
      simp only [Finset.mem_inter, mem_relIcc,
        Finset.mem_Icc]
      constructor
      · rintro ⟨hiB, _hiActive, hai, hib⟩
        exact ⟨hiB, hai, hib⟩
      · rintro ⟨hiB, hai, hib⟩
        exact
          ⟨hiB, hblockSubset B hB hiB,
            hai, hib⟩
    have hmeetIcc :
        (B ∩ Finset.Icc a b).Nonempty := by
      rw [← hinterEq]
      exact hmeet
    let c : Fin m :=
      (B ∩ Finset.Icc a b).min' hmeetIcc
    let d : Fin m :=
      (B ∩ Finset.Icc a b).max' hmeetIcc
    have hc :
        c ∈ B ∩ Finset.Icc a b :=
      Finset.min'_mem _ hmeetIcc
    have hd :
        d ∈ B ∩ Finset.Icc a b :=
      Finset.max'_mem _ hmeetIcc
    have hinterFull :
        IsFullyPairedOn source
          (B ∩ Finset.Icc a b) := by
      rw [← hinterEq]
      exact hBsource.inter hR
    have hrelative :
        IsRelFullyPaired source B c d := by
      refine
        ⟨(Finset.mem_inter.mp hc).1,
          (Finset.mem_inter.mp hd).1,
          Finset.min'_le _ d hd, ?_⟩
      rw [
        relIcc_min'_max'_eq_inter_Icc
          B a b hmeetIcc]
      exact hinterFull
    have hwhole :=
      hBprimitive c d hrelative
    rw [
      relIcc_min'_max'_eq_inter_Icc
        B a b hmeetIcc] at hwhole
    intro i hiB
    have hiInter :
        i ∈ B ∩ Finset.Icc a b := by
      rw [hwhole]
      exact hiB
    have hiIcc :=
      (Finset.mem_inter.mp hiInter).2
    exact mem_relIcc.mpr
      ⟨hblockSubset B hB hiB,
        (Finset.mem_Icc.mp hiIcc).1,
        (Finset.mem_Icc.mp hiIcc).2⟩
  constructor
  · intro i hiR hfix
    have hiActive :=
      (mem_relIcc.mp hiR).1
    have hiUnion :
        i ∈ finsetUnionList blocks := by
      rw [hcover]
      exact hiActive
    obtain ⟨B, hB, hiB⟩ :=
      (mem_finsetUnionList_iff blocks).mp
        hiUnion
    have hBsub :=
      hblockSubsetR B hB
        ⟨i, Finset.mem_inter.mpr
          ⟨hiB, hiR⟩⟩
    exact
      (List.forall_iff_forall_mem.mp
        htargetFull B hB).ne_of_mem hiB
        hfix
  · intro i hiR
    have hiActive :=
      (mem_relIcc.mp hiR).1
    have hiUnion :
        i ∈ finsetUnionList blocks := by
      rw [hcover]
      exact hiActive
    obtain ⟨B, hB, hiB⟩ :=
      (mem_finsetUnionList_iff blocks).mp
        hiUnion
    have hBsub :=
      hblockSubsetR B hB
        ⟨i, Finset.mem_inter.mpr
          ⟨hiB, hiR⟩⟩
    exact hBsub
      ((List.forall_iff_forall_mem.mp
        htargetFull B hB).apply_mem hiB)

/-- Under a common complete primitive block cover, the two pairings have
exactly the same relative fully-paired candidates. -/
theorem isRelFullyPaired_iff_of_common_primitive_block_cover
    {m : ℕ} (κ τ : PartialPairing (Fin m))
    (blocks : List (Finset (Fin m)))
    (active : Finset (Fin m))
    (hcover : finsetUnionList blocks = active)
    (hκFull : blocks.Forall (IsFullyPairedOn κ))
    (hκPrimitive :
      blocks.Forall (IsRelPrimitiveOn κ))
    (hτFull : blocks.Forall (IsFullyPairedOn τ))
    (hτPrimitive :
      blocks.Forall (IsRelPrimitiveOn τ))
    (a b : Fin m) :
    IsRelFullyPaired κ active a b ↔
      IsRelFullyPaired τ active a b := by
  constructor
  · intro h
    exact
      ⟨h.left_mem, h.right_mem, h.le,
        isFullyPairedOn_relIcc_of_primitive_block_cover
          κ τ blocks active hcover hκFull
          hκPrimitive hτFull a b
          h.isFullyPairedOn⟩
  · intro h
    exact
      ⟨h.left_mem, h.right_mem, h.le,
        isFullyPairedOn_relIcc_of_primitive_block_cover
          τ κ blocks active hcover hτFull
          hτPrimitive hκFull a b
          h.isFullyPairedOn⟩

/-! ## Selector recursion from the common block cover -/

/-- A fully paired active carrier is exhausted whenever the standard
two-indices-per-step fuel bound holds. -/
theorem extractAuxS_final_eq_empty_of_fullyPaired
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (hactive : IsFullyPairedOn κ active)
    (hcard : active.card ≤ 2 * fuel + 1) :
    (extractAuxS κ fuel active).2 = ∅ := by
  have hfinalFull :
      IsFullyPairedOn κ
        (extractAuxS κ fuel active).2 :=
    extractAuxS_final_fullyPaired
      κ fuel active hactive
  have hterminal :
      ¬∃ a b,
        IsRelFullyPaired κ
          (extractAuxS κ fuel active).2 a b :=
    extractAuxS_no_candidate κ fuel active hcard
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  let final :=
    (extractAuxS κ fuel active).2
  let a : Fin m := final.min' hne
  let b : Fin m := final.max' hne
  have ha : a ∈ final :=
    Finset.min'_mem final hne
  have hb : b ∈ final :=
    Finset.max'_mem final hne
  have hab : a ≤ b :=
    Finset.min'_le final b hb
  have hrel :
      relIcc final a b = final := by
    ext i
    rw [mem_relIcc]
    constructor
    · exact fun hi => hi.1
    · intro hi
      exact
        ⟨hi, Finset.min'_le final i hi,
          Finset.le_max' final i hi⟩
  apply hterminal
  refine ⟨a, b, ha, hb, hab, ?_⟩
  rw [hrel]
  exact hfinalFull

/-- For a fully paired state with sufficient fuel, its concrete extraction
blocks cover the active carrier exactly. -/
theorem finsetUnionList_extractionBlocksAux_eq_active
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (hactive : IsFullyPairedOn κ active)
    (hcard : active.card ≤ 2 * fuel + 1) :
    finsetUnionList
        (extractionBlocksAux κ fuel active) =
      active := by
  have hcover :=
    finsetUnionList_extractionBlocksAux_union_final
      κ fuel active
  rw [
    extractAuxS_final_eq_empty_of_fullyPaired
      κ fuel active hactive hcard,
    Finset.union_empty] at hcover
  exact hcover

/-- Two pairings which are full and primitive on every block of one concrete
Definition 3.1 schedule execute the same endpoint selector recursion. -/
theorem extractAux_eq_of_common_extraction_block_structure
    {m : ℕ} (κ τ : PartialPairing (Fin m))
    (fuel : ℕ) :
    ∀ (active : Finset (Fin m)),
      IsFullyPairedOn κ active →
      active.card ≤ 2 * fuel + 1 →
      (extractionBlocksAux κ fuel active).Forall
        (IsFullyPairedOn τ) →
      (extractionBlocksAux κ fuel active).Forall
        (IsRelPrimitiveOn τ) →
      extractAux τ fuel active =
        extractAux κ fuel active := by
  induction fuel with
  | zero =>
      intro active _hactive _hcard _hfull _hprimitive
      rfl
  | succ fuel ih =>
      intro active hactive hcard hτfull hτprimitive
      let blocks :=
        extractionBlocksAux κ (fuel + 1) active
      have hcover :
          finsetUnionList blocks = active :=
        finsetUnionList_extractionBlocksAux_eq_active
          κ (fuel + 1) active hactive hcard
      have hκfull :
          blocks.Forall (IsFullyPairedOn κ) :=
        extractionBlocksAux_forall_isFullyPairedOn
          κ (fuel + 1) active
      have hκprimitive :
          blocks.Forall (IsRelPrimitiveOn κ) :=
        extractionBlocksAux_forall_isRelPrimitiveOn
          κ (fuel + 1) active
      have hcandidates :
          ∀ a b,
            IsRelFullyPaired κ active a b ↔
              IsRelFullyPaired τ active a b :=
        fun a b =>
          isRelFullyPaired_iff_of_common_primitive_block_cover
            κ τ blocks active hcover
            hκfull hκprimitive
            hτfull hτprimitive a b
      by_cases hκ :
          ∃ a b, IsRelFullyPaired κ active a b
      · have hτ :
            ∃ a b,
              IsRelFullyPaired τ active a b := by
          obtain ⟨a, b, hab⟩ := hκ
          exact ⟨a, b, (hcandidates a b).mp hab⟩
        have hselect :
            selectRel κ active hκ =
              selectRel τ active hτ :=
          selectRel_eq_of_candidates_iff
            hcandidates hκ hτ
        rw [extractAux_succ_pos fuel hτ,
          extractAux_succ_pos fuel hκ,
          ← hselect]
        congr 1
        let B :=
          relIcc active
            (selectRel κ active hκ).1
            (selectRel κ active hκ).2
        let active' := active \ B
        have hactive' :
            IsFullyPairedOn κ active' :=
          hactive.sdiff
            (selectRel_isRelFullyPaired
              κ active hκ).isFullyPairedOn
        have hcard' :
            active'.card ≤ 2 * fuel + 1 := by
          have hshrink :=
            card_sdiff_relIcc_add_two_le
              (selectRel_isRelFullyPaired
                κ active hκ)
          dsimp only [active', B]
          omega
        have hτfull' :
            (extractionBlocksAux κ fuel active').Forall
              (IsFullyPairedOn τ) := by
          have hcons := hτfull
          rw [extractionBlocksAux_succ_pos
            fuel hκ, List.forall_cons] at hcons
          simpa only [active', B] using
            hcons.2
        have hτprimitive' :
            (extractionBlocksAux κ fuel active').Forall
              (IsRelPrimitiveOn τ) := by
          have hcons := hτprimitive
          rw [extractionBlocksAux_succ_pos
            fuel hκ, List.forall_cons] at hcons
          simpa only [active', B] using
            hcons.2
        exact ih active' hactive' hcard'
          hτfull' hτprimitive'
      · have hτ :
            ¬∃ a b,
              IsRelFullyPaired τ active a b := by
          rintro ⟨a, b, hab⟩
          exact hκ
            ⟨a, b, (hcandidates a b).mpr hab⟩
        rw [extractAux_succ_neg fuel hτ,
          extractAux_succ_neg fuel hκ]

/-! ## The exact R-322 endpoint fibre product -/

/-- Every pairing which is full and primitive on the concrete extraction
blocks of a full reference pairing has exactly the same ordered extraction
list. -/
theorem extract_eq_of_extractionPrimitivePartitionFiber
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (τ :
      PrimitivePartitionFiber
        (extractionPrimitiveBlockPartition κ hκ)) :
    extract τ.1 = extract κ := by
  apply extractAux_eq_of_common_extraction_block_structure
    κ τ.1 m Finset.univ
  · exact isFullyPairedOn_univ_iff.mpr hκ
  · simpa using
      (show m ≤ 2 * m + 1 by omega)
  · change
      (extractionBlocks κ).Forall
        (IsFullyPairedOn τ.1)
    exact
      List.forall_iff_forall_mem.mpr
        (fun B hB =>
          (τ.2 B hB).1)
  · change
      (extractionBlocks κ).Forall
        (IsRelPrimitiveOn τ.1)
    exact
      List.forall_iff_forall_mem.mpr
        (fun B hB =>
          (τ.2 B hB).2)

/-- Generic primitive-partition fibres for the concrete extraction schedule
are exactly the complete endpoint-signature fibre. -/
def reductionEndpointFiberEquivPrimitivePartitionFiber
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull) :
    ReductionEndpointFiberAt κ ≃
      PrimitivePartitionFiber
        (extractionPrimitiveBlockPartition κ hκ) where
  toFun τ :=
    ⟨τ.1, by
      intro B hB
      have hB' :
          B ∈ extractionBlocks κ := by
        simpa only [
          extractionPrimitiveBlockPartition_blocks] using hB
      exact
        ⟨endpointFiber_isFullyPairedOn_extractionBlock
            κ τ ⟨B, hB'⟩,
          endpointFiber_isRelPrimitiveOn_extractionBlock
            κ τ ⟨B, hB'⟩⟩⟩
  invFun τ :=
    ⟨τ.1,
      reductionEndpointSignature_eq_of_extract_eq
        τ.1 κ
          (extract_eq_of_extractionPrimitivePartitionFiber
            κ hκ τ)⟩
  left_inv τ := by
    apply Subtype.ext
    rfl
  right_inv τ := by
    apply Subtype.ext
    rfl

/-- **Exact multi-block product for an R-322 endpoint fibre.**  Every
realized endpoint-signature fibre has one independent primitive full pairing
coordinate on each concrete Definition 3.1 block, with no quotient,
multiplicity, or cardinality factor. -/
def endpointFiberEquivPrimitiveCoordinates
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull) :
    ReductionEndpointFiberAt κ ≃
      ExtractionPrimitiveCoordinates κ :=
  (reductionEndpointFiberEquivPrimitivePartitionFiber
    κ hκ).trans
      (primitivePartitionFiberEquivCoordinates
        (extractionPrimitiveBlockPartition κ hκ))

/-- The public product equivalence uses the previously frozen coordinate
map on its forward direction. -/
theorem endpointFiberEquivPrimitiveCoordinates_apply
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (τ : ReductionEndpointFiberAt κ) :
    endpointFiberEquivPrimitiveCoordinates κ hκ τ =
      endpointFiberPrimitiveCoordinates κ τ := by
  funext B
  apply Subtype.ext
  apply PartialPairing.ext
  intro j
  rfl

/-- Exact finite-sum reindexing of an endpoint fibre by all primitive block
coordinates. -/
theorem sum_endpointFiber_eq_sum_primitiveCoordinates
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    {M : Type*} [AddCommMonoid M]
    (F : ReductionEndpointFiberAt κ → M) :
    (∑ τ : ReductionEndpointFiberAt κ, F τ) =
      ∑ coordinates : ExtractionPrimitiveCoordinates κ,
        F ((endpointFiberEquivPrimitiveCoordinates
          κ hκ).symm coordinates) := by
  exact
    ((endpointFiberEquivPrimitiveCoordinates
      κ hκ).symm.sum_comp F).symm

end

end Anderson4D
