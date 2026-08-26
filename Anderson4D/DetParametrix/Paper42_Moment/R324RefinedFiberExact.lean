import Anderson4D.DetParametrix.Paper42_Moment.R324IntegratedMultiBlockCoordinates
import Anderson4D.DetParametrix.Paper41_Renorm.R322EndpointProductClosure

/-!
# Exact primitive coordinates of one refined R-324 fibre

The common primitive-block schedule of a residual-refined contraction
fibre does not merely give an embedding into the generic block fibre:
fullness and relative primitivity on every scheduled block recover the
two within-half extraction signatures and the residual interval chain.
Consequently the embedding is an equivalence.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## One-half active carriers inside the doubled order -/

/-- Keep an active subset of the left copy and all of the right copy. -/
def momentLeftAugmentedActive
    (m : ℕ) (active : Finset (Fin m)) :
    Finset (Fin (2 * m)) :=
  active.image leftMomentIndex ∪
    (Finset.univ : Finset (Fin m)).image rightMomentIndex

/-- Keep all of the left copy and an active subset of the right copy. -/
def momentRightAugmentedActive
    (m : ℕ) (active : Finset (Fin m)) :
    Finset (Fin (2 * m)) :=
  (Finset.univ : Finset (Fin m)).image leftMomentIndex ∪
    active.image rightMomentIndex

@[simp]
theorem leftMomentIndex_mem_momentLeftAugmentedActive
    {m : ℕ} (active : Finset (Fin m)) (i : Fin m) :
    leftMomentIndex i ∈ momentLeftAugmentedActive m active ↔
      i ∈ active := by
  simp only [momentLeftAugmentedActive, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro (⟨j, hj, hji⟩ | ⟨j, _hj, hji⟩)
    · exact (leftMomentIndex_injective hji) ▸ hj
    · have hval := congrArg Fin.val hji
      simp only [leftMomentIndex, rightMomentIndex] at hval
      omega
  · intro hi
    exact Or.inl ⟨i, hi, rfl⟩

@[simp]
theorem rightMomentIndex_mem_momentRightAugmentedActive
    {m : ℕ} (active : Finset (Fin m)) (i : Fin m) :
    rightMomentIndex i ∈ momentRightAugmentedActive m active ↔
      i ∈ active := by
  simp only [momentRightAugmentedActive, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro (⟨j, _hj, hji⟩ | ⟨j, hj, hji⟩)
    · have hval := congrArg Fin.val hji
      simp only [leftMomentIndex, rightMomentIndex] at hval
      omega
    · exact (rightMomentIndex_injective hji) ▸ hj
  · intro hi
    exact Or.inr ⟨i, hi, rfl⟩

theorem relIcc_momentLeftAugmentedActive
    {m : ℕ} (active : Finset (Fin m)) (a b : Fin m) :
    relIcc (momentLeftAugmentedActive m active)
        (leftMomentIndex a) (leftMomentIndex b) =
      (relIcc active a b).image leftMomentIndex := by
  ext i
  constructor
  · intro hi
    obtain ⟨hiD, hai, hib⟩ := mem_relIcc.mp hi
    rcases Finset.mem_union.mp hiD with hiLeft | hiRight
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hiLeft
      apply Finset.mem_image.mpr
      refine ⟨j, mem_relIcc.mpr ⟨hj, ?_, ?_⟩, rfl⟩
      · exact hai
      · exact hib
    · obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hiRight
      have hab : m + j.val ≤ b.val := hib
      have hb := b.isLt
      omega
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hjActive, haj, hjb⟩ := mem_relIcc.mp hj
    exact mem_relIcc.mpr
      ⟨Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨j, hjActive, rfl⟩),
        haj, hjb⟩

theorem relIcc_momentRightAugmentedActive
    {m : ℕ} (active : Finset (Fin m)) (a b : Fin m) :
    relIcc (momentRightAugmentedActive m active)
        (rightMomentIndex a) (rightMomentIndex b) =
      (relIcc active a b).image rightMomentIndex := by
  ext i
  constructor
  · intro hi
    obtain ⟨hiD, hai, hib⟩ := mem_relIcc.mp hi
    rcases Finset.mem_union.mp hiD with hiLeft | hiRight
    · obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hiLeft
      have hai' : m + a.val ≤ j.val := hai
      have hj := j.isLt
      omega
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hiRight
      apply Finset.mem_image.mpr
      refine ⟨j, mem_relIcc.mpr ⟨hj, ?_, ?_⟩, rfl⟩
      · change a.val ≤ j.val
        change m + a.val ≤ m + j.val at hai
        omega
      · change j.val ≤ b.val
        change m + j.val ≤ m + b.val at hib
        omega
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hjActive, haj, hjb⟩ := mem_relIcc.mp hj
    exact mem_relIcc.mpr
      ⟨Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨j, hjActive, rfl⟩),
        by
          change m + a.val ≤ m + j.val
          omega,
        by
          change m + j.val ≤ m + b.val
          omega⟩

@[simp]
theorem momentLeftAugmentedActive_univ
    (m : ℕ) :
    momentLeftAugmentedActive m Finset.univ =
      (Finset.univ : Finset (Fin (2 * m))) := by
  ext i
  constructor
  · exact fun _ => Finset.mem_univ i
  · intro _hi
    obtain ⟨s, rfl⟩ :=
      (momentDoubleFinEquiv m).surjective i
    cases s with
    | inl j =>
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr
            ⟨j, Finset.mem_univ j, rfl⟩)
    | inr j =>
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr
            ⟨j, Finset.mem_univ j, rfl⟩)

@[simp]
theorem momentRightAugmentedActive_univ
    (m : ℕ) :
    momentRightAugmentedActive m Finset.univ =
      (Finset.univ : Finset (Fin (2 * m))) := by
  ext i
  constructor
  · exact fun _ => Finset.mem_univ i
  · intro _hi
    obtain ⟨s, rfl⟩ :=
      (momentDoubleFinEquiv m).surjective i
    cases s with
    | inl j =>
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr
            ⟨j, Finset.mem_univ j, rfl⟩)
    | inr j =>
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr
            ⟨j, Finset.mem_univ j, rfl⟩)

theorem momentLeftAugmentedActive_sdiff_image
    {m : ℕ} (active I : Finset (Fin m)) :
    momentLeftAugmentedActive m (active \ I) =
      momentLeftAugmentedActive m active \
        I.image leftMomentIndex := by
  ext i
  constructor
  · intro hi
    apply Finset.mem_sdiff.mpr
    rcases Finset.mem_union.mp hi with hiLeft | hiRight
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hiLeft
      have hj' := Finset.mem_sdiff.mp hj
      exact
        ⟨Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨j, hj'.1, rfl⟩),
          by
            intro h
            obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp h
            exact hj'.2 ((leftMomentIndex_injective hkj) ▸ hk)⟩
    · exact
        ⟨Finset.mem_union_right _ hiRight,
          by
            intro h
            obtain ⟨j, _hj, hji⟩ := Finset.mem_image.mp h
            obtain ⟨k, _hk, hki⟩ := Finset.mem_image.mp hiRight
            have hval :=
              congrArg Fin.val (hji.trans hki.symm)
            simp only [leftMomentIndex, rightMomentIndex] at hval
            omega⟩
  · intro hi
    obtain ⟨hiD, hiI⟩ := Finset.mem_sdiff.mp hi
    rcases Finset.mem_union.mp hiD with hiLeft | hiRight
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hiLeft
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_sdiff.mpr ⟨hj, ?_⟩, rfl⟩
      intro hjI
      exact hiI (Finset.mem_image.mpr ⟨j, hjI, rfl⟩)
    · exact Finset.mem_union_right _ hiRight

theorem momentRightAugmentedActive_sdiff_image
    {m : ℕ} (active I : Finset (Fin m)) :
    momentRightAugmentedActive m (active \ I) =
      momentRightAugmentedActive m active \
        I.image rightMomentIndex := by
  ext i
  constructor
  · intro hi
    apply Finset.mem_sdiff.mpr
    rcases Finset.mem_union.mp hi with hiLeft | hiRight
    · exact
        ⟨Finset.mem_union_left _ hiLeft,
          by
            intro h
            obtain ⟨j, _hj, hji⟩ := Finset.mem_image.mp h
            obtain ⟨k, _hk, hki⟩ := Finset.mem_image.mp hiLeft
            have hval :=
              congrArg Fin.val (hji.trans hki.symm)
            simp only [leftMomentIndex, rightMomentIndex] at hval
            omega⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hiRight
      have hj' := Finset.mem_sdiff.mp hj
      exact
        ⟨Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨j, hj'.1, rfl⟩),
          by
            intro h
            obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp h
            exact hj'.2 ((rightMomentIndex_injective hkj) ▸ hk)⟩
  · intro hi
    obtain ⟨hiD, hiI⟩ := Finset.mem_sdiff.mp hi
    rcases Finset.mem_union.mp hiD with hiLeft | hiRight
    · exact Finset.mem_union_left _ hiLeft
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hiRight
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_sdiff.mpr ⟨hj, ?_⟩, rfl⟩
      intro hjI
      exact hiI (Finset.mem_image.mpr ⟨j, hjI, rfl⟩)

/-! ## Saturated subcovers of a primitive partition -/

/-- Blocks of a list which lie wholly in a current active carrier. -/
def primitiveBlocksInside
    {n : ℕ} (blocks : List (Finset (Fin n)))
    (active : Finset (Fin n)) :
    List (Finset (Fin n)) :=
  blocks.filter fun B => B ⊆ active

/-- If a current carrier is saturated by a complete block partition,
filtering to the blocks contained in that carrier still covers it exactly. -/
theorem finsetUnionList_primitiveBlocksInside_eq
    {n : ℕ} (blocks : List (Finset (Fin n)))
    (active : Finset (Fin n))
    (hcover :
      finsetUnionList blocks =
        (Finset.univ : Finset (Fin n)))
    (hsaturated :
      ∀ B ∈ blocks,
        (B ∩ active).Nonempty → B ⊆ active) :
    finsetUnionList
        (primitiveBlocksInside blocks active) =
      active := by
  apply Finset.Subset.antisymm
  · intro i hi
    obtain ⟨B, hB, hiB⟩ :=
      (mem_finsetUnionList_iff
        (primitiveBlocksInside blocks active)).mp hi
    have hB' :
        B ∈ blocks ∧ decide (B ⊆ active) = true := by
      simpa only [primitiveBlocksInside,
        List.mem_filter] using hB
    exact (of_decide_eq_true hB'.2) hiB
  · intro i hi
    have hiUniv :
        i ∈ finsetUnionList blocks := by
      rw [hcover]
      exact Finset.mem_univ i
    obtain ⟨B, hB, hiB⟩ :=
      (mem_finsetUnionList_iff blocks).mp hiUniv
    have hBsub :
        B ⊆ active :=
      hsaturated B hB
        ⟨i, Finset.mem_inter.mpr ⟨hiB, hi⟩⟩
    exact
      (mem_finsetUnionList_iff
        (primitiveBlocksInside blocks active)).mpr
          ⟨B, by
            rw [primitiveBlocksInside, List.mem_filter]
            exact ⟨hB, decide_eq_true hBsub⟩,
            hiB⟩

theorem primitiveBlocksInside_forall
    {n : ℕ} (blocks : List (Finset (Fin n)))
    (active : Finset (Fin n))
    (P : Finset (Fin n) → Prop)
    (hP : blocks.Forall P) :
    (primitiveBlocksInside blocks active).Forall P := by
  apply List.forall_iff_forall_mem.mpr
  intro B hB
  exact
    List.forall_iff_forall_mem.mp hP B
      (List.mem_of_mem_filter hB)

/-- Removing one whole member of a pairwise-disjoint saturated partition
preserves saturation. -/
theorem blockPartitionSaturated_sdiff
    {n : ℕ} (blocks : List (Finset (Fin n)))
    (hpairwise : blocks.Pairwise Disjoint)
    (active S : Finset (Fin n))
    (hS : S ∈ blocks)
    (hsaturated :
      ∀ B ∈ blocks,
        (B ∩ active).Nonempty → B ⊆ active) :
    ∀ B ∈ blocks,
      (B ∩ (active \ S)).Nonempty →
        B ⊆ active \ S := by
  intro B hB hmeet
  have hBsub :
      B ⊆ active := by
    apply hsaturated B hB
    obtain ⟨i, hi⟩ := hmeet
    exact
      ⟨i, Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hi).1,
          (Finset.mem_sdiff.mp
            (Finset.mem_inter.mp hi).2).1⟩⟩
  have hBS : B ≠ S := by
    intro hEq
    subst B
    obtain ⟨i, hi⟩ := hmeet
    exact
      (Finset.mem_sdiff.mp
        (Finset.mem_inter.mp hi).2).2
        (Finset.mem_inter.mp hi).1
  have hdisjoint :
      Disjoint B S :=
    hpairwise.forall hB hS hBS
  intro i hiB
  exact Finset.mem_sdiff.mpr
    ⟨hBsub hiB,
      fun hiS =>
        (Finset.disjoint_left.mp hdisjoint) hiB hiS⟩

/-! ## Candidate reflection through the augmented carriers -/

theorem isRelFullyPaired_momentLeftAugmentedActive_iff
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (active : Finset (Fin m)) (a b : Fin m) :
    IsRelFullyPaired
        (momentCombinedPairing κp κm π)
        (momentLeftAugmentedActive m active)
        (leftMomentIndex a) (leftMomentIndex b) ↔
      IsRelFullyPaired κp active a b := by
  constructor
  · intro h
    have himage :
        IsRelFullyPaired
          (momentCombinedPairing κp κm π)
          (active.image leftMomentIndex)
          (leftMomentIndex a) (leftMomentIndex b) := by
      refine
      ⟨Finset.mem_image.mpr
          ⟨a,
            (leftMomentIndex_mem_momentLeftAugmentedActive
              active a).mp h.left_mem,
            rfl⟩,
        Finset.mem_image.mpr
          ⟨b,
            (leftMomentIndex_mem_momentLeftAugmentedActive
              active b).mp h.right_mem,
            rfl⟩,
        h.le, ?_⟩
      rw [← image_leftMomentIndex_relIcc,
        ← relIcc_momentLeftAugmentedActive]
      exact h.isFullyPairedOn
    exact isRelFullyPaired_image_leftMomentIndex_iff.mp
      himage
  · intro h
    have h' :
        IsRelFullyPaired
          (momentCombinedPairing κp κm π)
          (active.image leftMomentIndex)
          (leftMomentIndex a) (leftMomentIndex b) :=
      IsRelFullyPaired.image_leftMomentIndex
        (κm := κm) (π := π) h
    refine
      ⟨(leftMomentIndex_mem_momentLeftAugmentedActive
          active a).mpr h.left_mem,
        (leftMomentIndex_mem_momentLeftAugmentedActive
          active b).mpr h.right_mem,
        h'.le, ?_⟩
    rw [relIcc_momentLeftAugmentedActive,
      image_leftMomentIndex_relIcc]
    exact h'.isFullyPairedOn

theorem isRelFullyPaired_momentRightAugmentedActive_iff
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (active : Finset (Fin m)) (a b : Fin m) :
    IsRelFullyPaired
        (momentCombinedPairing κp κm π)
        (momentRightAugmentedActive m active)
        (rightMomentIndex a) (rightMomentIndex b) ↔
      IsRelFullyPaired κm active a b := by
  constructor
  · intro h
    have himage :
        IsRelFullyPaired
          (momentCombinedPairing κp κm π)
          (active.image rightMomentIndex)
          (rightMomentIndex a) (rightMomentIndex b) := by
      refine
      ⟨Finset.mem_image.mpr
          ⟨a,
            (rightMomentIndex_mem_momentRightAugmentedActive
              active a).mp h.left_mem,
            rfl⟩,
        Finset.mem_image.mpr
          ⟨b,
            (rightMomentIndex_mem_momentRightAugmentedActive
              active b).mp h.right_mem,
            rfl⟩,
        h.le, ?_⟩
      rw [← image_rightMomentIndex_relIcc,
        ← relIcc_momentRightAugmentedActive]
      exact h.isFullyPairedOn
    exact isRelFullyPaired_image_rightMomentIndex_iff.mp
      himage
  · intro h
    have h' :
        IsRelFullyPaired
          (momentCombinedPairing κp κm π)
          (active.image rightMomentIndex)
          (rightMomentIndex a) (rightMomentIndex b) :=
      IsRelFullyPaired.image_rightMomentIndex
        (κp := κp) (π := π) h
    refine
      ⟨(rightMomentIndex_mem_momentRightAugmentedActive
          active a).mpr h.left_mem,
        (rightMomentIndex_mem_momentRightAugmentedActive
          active b).mpr h.right_mem,
        h'.le, ?_⟩
    rw [relIcc_momentRightAugmentedActive,
      image_rightMomentIndex_relIcc]
    exact h'.isFullyPairedOn

/-! ## Recovery of the two within-half extraction recursions -/

theorem extractAux_eq_of_common_momentPrimitivePartition_left
    {m : ℕ} (e₀ e : MomentContraction m)
    (htarget :
      ∀ B ∈
          (momentPrimitiveBlockPartition
            e₀.1 e₀.2.1 e₀.2.2).blocks,
        IsFullyPairedOn
            (momentCombinedPairing e.1 e.2.1 e.2.2) B ∧
          IsRelPrimitiveOn
            (momentCombinedPairing e.1 e.2.1 e.2.2) B)
    (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      (∀ B ∈
          (momentPrimitiveBlockPartition
            e₀.1 e₀.2.1 e₀.2.2).blocks,
        (B ∩ momentLeftAugmentedActive m active).Nonempty →
          B ⊆ momentLeftAugmentedActive m active) →
      (∀ B ∈ extractionBlocksAux e₀.1 fuel active,
        B.image leftMomentIndex ∈
          (momentPrimitiveBlockPartition
            e₀.1 e₀.2.1 e₀.2.2).blocks) →
      extractAux e.1 fuel active =
        extractAux e₀.1 fuel active := by
  induction fuel with
  | zero =>
      intro active _hsaturated _hblocks
      rfl
  | succ fuel ih =>
      intro active hsaturated hblocks
      let P :=
        momentPrimitiveBlockPartition
          e₀.1 e₀.2.1 e₀.2.2
      let doubledActive :=
        momentLeftAugmentedActive m active
      let blocks :=
        primitiveBlocksInside P.blocks doubledActive
      have hcover :
          finsetUnionList blocks = doubledActive := by
        exact finsetUnionList_primitiveBlocksInside_eq
          P.blocks doubledActive P.cover hsaturated
      have hsourceFull :
          blocks.Forall
            (IsFullyPairedOn
              (momentCombinedPairing
                e₀.1 e₀.2.1 e₀.2.2)) :=
        primitiveBlocksInside_forall
          P.blocks doubledActive _ P.fullyPaired
      have hsourcePrimitive :
          blocks.Forall
            (IsRelPrimitiveOn
              (momentCombinedPairing
                e₀.1 e₀.2.1 e₀.2.2)) :=
        primitiveBlocksInside_forall
          P.blocks doubledActive _ P.primitive
      have htargetFull :
          blocks.Forall
            (IsFullyPairedOn
              (momentCombinedPairing
                e.1 e.2.1 e.2.2)) := by
        apply List.forall_iff_forall_mem.mpr
        intro B hB
        exact
          (htarget B
            (List.mem_of_mem_filter hB)).1
      have htargetPrimitive :
          blocks.Forall
            (IsRelPrimitiveOn
              (momentCombinedPairing
                e.1 e.2.1 e.2.2)) := by
        apply List.forall_iff_forall_mem.mpr
        intro B hB
        exact
          (htarget B
            (List.mem_of_mem_filter hB)).2
      have hcombinedCandidates :
          ∀ a b : Fin (2 * m),
            IsRelFullyPaired
                (momentCombinedPairing
                  e₀.1 e₀.2.1 e₀.2.2)
                doubledActive a b ↔
              IsRelFullyPaired
                (momentCombinedPairing
                  e.1 e.2.1 e.2.2)
                doubledActive a b :=
        fun a b =>
          isRelFullyPaired_iff_of_common_primitive_block_cover
            (momentCombinedPairing
              e₀.1 e₀.2.1 e₀.2.2)
            (momentCombinedPairing
              e.1 e.2.1 e.2.2)
            blocks doubledActive hcover
            hsourceFull hsourcePrimitive
            htargetFull htargetPrimitive a b
      have hcandidates :
          ∀ a b : Fin m,
            IsRelFullyPaired e₀.1 active a b ↔
              IsRelFullyPaired e.1 active a b := by
        intro a b
        rw [←
          isRelFullyPaired_momentLeftAugmentedActive_iff
            (κm := e₀.2.1) (π := e₀.2.2)
            active a b]
        rw [hcombinedCandidates
          (leftMomentIndex a) (leftMomentIndex b)]
        exact
          isRelFullyPaired_momentLeftAugmentedActive_iff
            (κm := e.2.1) (π := e.2.2)
            active a b
      by_cases hsource :
          ∃ a b, IsRelFullyPaired e₀.1 active a b
      · have htarget' :
            ∃ a b, IsRelFullyPaired e.1 active a b := by
          obtain ⟨a, b, hab⟩ := hsource
          exact ⟨a, b, (hcandidates a b).mp hab⟩
        have hselect :
            selectRel e₀.1 active hsource =
              selectRel e.1 active htarget' :=
          selectRel_eq_of_candidates_iff
            hcandidates hsource htarget'
        let I :=
          relIcc active
            (selectRel e₀.1 active hsource).1
            (selectRel e₀.1 active hsource).2
        let S := I.image leftMomentIndex
        have hS :
            S ∈ P.blocks := by
          apply hblocks I
          rw [extractionBlocksAux_succ_pos fuel hsource]
          exact List.mem_cons_self
        have hsaturated' :
            ∀ B ∈ P.blocks,
              (B ∩
                momentLeftAugmentedActive
                  m (active \ I)).Nonempty →
                B ⊆
                  momentLeftAugmentedActive
                    m (active \ I) := by
          rw [momentLeftAugmentedActive_sdiff_image]
          exact blockPartitionSaturated_sdiff
            P.blocks P.pairwise_disjoint doubledActive S
            hS hsaturated
        have hblocks' :
            ∀ B ∈
                extractionBlocksAux
                  e₀.1 fuel (active \ I),
              B.image leftMomentIndex ∈ P.blocks := by
          intro B hB
          apply hblocks B
          rw [extractionBlocksAux_succ_pos fuel hsource]
          exact List.mem_cons_of_mem _ hB
        rw [extractAux_succ_pos fuel htarget',
          extractAux_succ_pos fuel hsource, ← hselect]
        congr 1
        exact ih (active \ I)
          hsaturated' hblocks'
      · have htarget' :
            ¬∃ a b, IsRelFullyPaired e.1 active a b := by
          rintro ⟨a, b, hab⟩
          exact hsource
            ⟨a, b, (hcandidates a b).mpr hab⟩
        rw [extractAux_succ_neg fuel htarget',
          extractAux_succ_neg fuel hsource]

theorem extract_left_eq_of_common_momentPrimitivePartition
    {m : ℕ} (e₀ e : MomentContraction m)
    (htarget :
      ∀ B ∈
          (momentPrimitiveBlockPartition
            e₀.1 e₀.2.1 e₀.2.2).blocks,
        IsFullyPairedOn
            (momentCombinedPairing e.1 e.2.1 e.2.2) B ∧
          IsRelPrimitiveOn
            (momentCombinedPairing e.1 e.2.1 e.2.2) B) :
    extract e.1 = extract e₀.1 := by
  unfold extract
  apply extractAux_eq_of_common_momentPrimitivePartition_left
    e₀ e htarget m Finset.univ
  · intro B _hB _hmeet
    rw [momentLeftAugmentedActive_univ]
    exact Finset.subset_univ B
  · intro B hB
    have hB' :
        B ∈ extractionBlocks e₀.1 := hB
    have hBne :
        B.Nonempty :=
      List.forall_iff_forall_mem.mp
        (extractionBlocks_forall_nonempty e₀.1)
        B hB'
    rw [momentPrimitiveBlockPartition_blocks,
      mem_momentNonemptyPrimitiveBlocks]
    constructor
    · left
      exact List.mem_map.mpr ⟨B, hB', rfl⟩
    · obtain ⟨i, hi⟩ := hBne
      exact
        ⟨leftMomentIndex i,
          Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩

theorem extractAux_eq_of_common_momentPrimitivePartition_right
    {m : ℕ} (e₀ e : MomentContraction m)
    (htarget :
      ∀ B ∈
          (momentPrimitiveBlockPartition
            e₀.1 e₀.2.1 e₀.2.2).blocks,
        IsFullyPairedOn
            (momentCombinedPairing e.1 e.2.1 e.2.2) B ∧
          IsRelPrimitiveOn
            (momentCombinedPairing e.1 e.2.1 e.2.2) B)
    (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      (∀ B ∈
          (momentPrimitiveBlockPartition
            e₀.1 e₀.2.1 e₀.2.2).blocks,
        (B ∩ momentRightAugmentedActive m active).Nonempty →
          B ⊆ momentRightAugmentedActive m active) →
      (∀ B ∈ extractionBlocksAux e₀.2.1 fuel active,
        B.image rightMomentIndex ∈
          (momentPrimitiveBlockPartition
            e₀.1 e₀.2.1 e₀.2.2).blocks) →
      extractAux e.2.1 fuel active =
        extractAux e₀.2.1 fuel active := by
  induction fuel with
  | zero =>
      intro active _hsaturated _hblocks
      rfl
  | succ fuel ih =>
      intro active hsaturated hblocks
      let P :=
        momentPrimitiveBlockPartition
          e₀.1 e₀.2.1 e₀.2.2
      let doubledActive :=
        momentRightAugmentedActive m active
      let blocks :=
        primitiveBlocksInside P.blocks doubledActive
      have hcover :
          finsetUnionList blocks = doubledActive := by
        exact finsetUnionList_primitiveBlocksInside_eq
          P.blocks doubledActive P.cover hsaturated
      have hsourceFull :
          blocks.Forall
            (IsFullyPairedOn
              (momentCombinedPairing
                e₀.1 e₀.2.1 e₀.2.2)) :=
        primitiveBlocksInside_forall
          P.blocks doubledActive _ P.fullyPaired
      have hsourcePrimitive :
          blocks.Forall
            (IsRelPrimitiveOn
              (momentCombinedPairing
                e₀.1 e₀.2.1 e₀.2.2)) :=
        primitiveBlocksInside_forall
          P.blocks doubledActive _ P.primitive
      have htargetFull :
          blocks.Forall
            (IsFullyPairedOn
              (momentCombinedPairing
                e.1 e.2.1 e.2.2)) := by
        apply List.forall_iff_forall_mem.mpr
        intro B hB
        exact
          (htarget B
            (List.mem_of_mem_filter hB)).1
      have htargetPrimitive :
          blocks.Forall
            (IsRelPrimitiveOn
              (momentCombinedPairing
                e.1 e.2.1 e.2.2)) := by
        apply List.forall_iff_forall_mem.mpr
        intro B hB
        exact
          (htarget B
            (List.mem_of_mem_filter hB)).2
      have hcombinedCandidates :
          ∀ a b : Fin (2 * m),
            IsRelFullyPaired
                (momentCombinedPairing
                  e₀.1 e₀.2.1 e₀.2.2)
                doubledActive a b ↔
              IsRelFullyPaired
                (momentCombinedPairing
                  e.1 e.2.1 e.2.2)
                doubledActive a b :=
        fun a b =>
          isRelFullyPaired_iff_of_common_primitive_block_cover
            (momentCombinedPairing
              e₀.1 e₀.2.1 e₀.2.2)
            (momentCombinedPairing
              e.1 e.2.1 e.2.2)
            blocks doubledActive hcover
            hsourceFull hsourcePrimitive
            htargetFull htargetPrimitive a b
      have hcandidates :
          ∀ a b : Fin m,
            IsRelFullyPaired e₀.2.1 active a b ↔
              IsRelFullyPaired e.2.1 active a b := by
        intro a b
        rw [←
          isRelFullyPaired_momentRightAugmentedActive_iff
            (κp := e₀.1) (π := e₀.2.2)
            active a b]
        rw [hcombinedCandidates
          (rightMomentIndex a) (rightMomentIndex b)]
        exact
          isRelFullyPaired_momentRightAugmentedActive_iff
            (κp := e.1) (π := e.2.2)
            active a b
      by_cases hsource :
          ∃ a b, IsRelFullyPaired e₀.2.1 active a b
      · have htarget' :
            ∃ a b, IsRelFullyPaired e.2.1 active a b := by
          obtain ⟨a, b, hab⟩ := hsource
          exact ⟨a, b, (hcandidates a b).mp hab⟩
        have hselect :
            selectRel e₀.2.1 active hsource =
              selectRel e.2.1 active htarget' :=
          selectRel_eq_of_candidates_iff
            hcandidates hsource htarget'
        let I :=
          relIcc active
            (selectRel e₀.2.1 active hsource).1
            (selectRel e₀.2.1 active hsource).2
        let S := I.image rightMomentIndex
        have hS :
            S ∈ P.blocks := by
          apply hblocks I
          rw [extractionBlocksAux_succ_pos fuel hsource]
          exact List.mem_cons_self
        have hsaturated' :
            ∀ B ∈ P.blocks,
              (B ∩
                momentRightAugmentedActive
                  m (active \ I)).Nonempty →
                B ⊆
                  momentRightAugmentedActive
                    m (active \ I) := by
          rw [momentRightAugmentedActive_sdiff_image]
          exact blockPartitionSaturated_sdiff
            P.blocks P.pairwise_disjoint doubledActive S
            hS hsaturated
        have hblocks' :
            ∀ B ∈
                extractionBlocksAux
                  e₀.2.1 fuel (active \ I),
              B.image rightMomentIndex ∈ P.blocks := by
          intro B hB
          apply hblocks B
          rw [extractionBlocksAux_succ_pos fuel hsource]
          exact List.mem_cons_of_mem _ hB
        rw [extractAux_succ_pos fuel htarget',
          extractAux_succ_pos fuel hsource, ← hselect]
        congr 1
        exact ih (active \ I)
          hsaturated' hblocks'
      · have htarget' :
            ¬∃ a b, IsRelFullyPaired e.2.1 active a b := by
          rintro ⟨a, b, hab⟩
          exact hsource
            ⟨a, b, (hcandidates a b).mpr hab⟩
        rw [extractAux_succ_neg fuel htarget',
          extractAux_succ_neg fuel hsource]

theorem extract_right_eq_of_common_momentPrimitivePartition
    {m : ℕ} (e₀ e : MomentContraction m)
    (htarget :
      ∀ B ∈
          (momentPrimitiveBlockPartition
            e₀.1 e₀.2.1 e₀.2.2).blocks,
        IsFullyPairedOn
            (momentCombinedPairing e.1 e.2.1 e.2.2) B ∧
          IsRelPrimitiveOn
            (momentCombinedPairing e.1 e.2.1 e.2.2) B) :
    extract e.2.1 = extract e₀.2.1 := by
  unfold extract
  apply extractAux_eq_of_common_momentPrimitivePartition_right
    e₀ e htarget m Finset.univ
  · intro B _hB _hmeet
    rw [momentRightAugmentedActive_univ]
    exact Finset.subset_univ B
  · intro B hB
    have hB' :
        B ∈ extractionBlocks e₀.2.1 := hB
    have hBne :
        B.Nonempty :=
      List.forall_iff_forall_mem.mp
        (extractionBlocks_forall_nonempty e₀.2.1)
        B hB'
    rw [momentPrimitiveBlockPartition_blocks,
      mem_momentNonemptyPrimitiveBlocks]
    constructor
    · right
      left
      exact List.mem_map.mpr ⟨B, hB', rfl⟩
    · obtain ⟨i, hi⟩ := hBne
      exact
        ⟨rightMomentIndex i,
          Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩

theorem momentContractionSignature_eq_of_commonPrimitivePartition
    {m : ℕ} (e₀ e : MomentContraction m)
    (htarget :
      ∀ B ∈
          (momentPrimitiveBlockPartition
            e₀.1 e₀.2.1 e₀.2.2).blocks,
        IsFullyPairedOn
            (momentCombinedPairing e.1 e.2.1 e.2.2) B ∧
          IsRelPrimitiveOn
            (momentCombinedPairing e.1 e.2.1 e.2.2) B) :
    momentContractionSignature e =
      momentContractionSignature e₀ := by
  have hleftExtract :
      extract e.1 = extract e₀.1 :=
    extract_left_eq_of_common_momentPrimitivePartition
      e₀ e htarget
  have hrightExtract :
      extract e.2.1 = extract e₀.2.1 :=
    extract_right_eq_of_common_momentPrimitivePartition
      e₀ e htarget
  have hleftSignature :
      reductionEndpointSignature e.1 =
        reductionEndpointSignature e₀.1 :=
    reductionEndpointSignature_eq_of_extract_eq
      e.1 e₀.1 hleftExtract
  have hrightSignature :
      reductionEndpointSignature e.2.1 =
        reductionEndpointSignature e₀.2.1 :=
    reductionEndpointSignature_eq_of_extract_eq
      e.2.1 e₀.2.1 hrightExtract
  have hleftLeft :
      leftEndpoints e.1 =
        leftEndpoints e₀.1 :=
    congrArg Prod.fst hleftSignature
  have hleftRight :
      rightEndpoints e.1 =
        rightEndpoints e₀.1 :=
    congrArg Prod.snd hleftSignature
  have hrightLeft :
      leftEndpoints e.2.1 =
        leftEndpoints e₀.2.1 :=
    congrArg Prod.fst hrightSignature
  have hrightRight :
      rightEndpoints e.2.1 =
        rightEndpoints e₀.2.1 :=
    congrArg Prod.snd hrightSignature
  unfold momentContractionSignature
    momentWithinHalfEndpointSignature
  rw [hleftLeft, hleftRight,
    hrightLeft, hrightRight]

theorem momentResidualIntervalChain_eq_of_commonPrimitivePartition
    {m : ℕ} (e₀ e : MomentContraction m)
    (htarget :
      ∀ B ∈
          (momentPrimitiveBlockPartition
            e₀.1 e₀.2.1 e₀.2.2).blocks,
        IsFullyPairedOn
            (momentCombinedPairing e.1 e.2.1 e.2.2) B ∧
          IsRelPrimitiveOn
            (momentCombinedPairing e.1 e.2.1 e.2.2) B) :
    momentResidualIntervalChain e.1 e.2.1 e.2.2 =
      momentResidualIntervalChain
        e₀.1 e₀.2.1 e₀.2.2 := by
  have hmoment :
      momentContractionSignature e =
        momentContractionSignature e₀ :=
    momentContractionSignature_eq_of_commonPrimitivePartition
      e₀ e htarget
  have hfinal :=
    momentFinalActive_eq_of_momentContractionSignature_eq
      e e₀ hmoment
  have hactive :
      momentResidualActive e.1 e.2.1 =
        momentResidualActive e₀.1 e₀.2.1 := by
    unfold momentResidualActive
    rw [hfinal.1, hfinal.2]
  let active :=
    momentResidualActive e₀.1 e₀.2.1
  let blocks :=
    nonemptyMomentResidualCollapseBlocks
      e₀.1 e₀.2.1 e₀.2.2
  have hcover :
      finsetUnionList blocks = active := by
    unfold blocks active
    unfold nonemptyMomentResidualCollapseBlocks
    rw [finsetUnionList_filter_nonempty,
      finsetUnionList_momentResidualCollapseBlocks]
  have hsourceFull :
      blocks.Forall
        (IsFullyPairedOn
          (momentCombinedPairing
            e₀.1 e₀.2.1 e₀.2.2)) := by
    apply List.forall_iff_forall_mem.mpr
    intro B hB
    exact
      List.forall_iff_forall_mem.mp
        (momentResidualCollapseBlocks_forall_isFullyPairedOn
          e₀.1 e₀.2.1 e₀.2.2)
        B (List.mem_of_mem_filter hB)
  have hsourcePrimitive :
      blocks.Forall
        (IsRelPrimitiveOn
          (momentCombinedPairing
            e₀.1 e₀.2.1 e₀.2.2)) := by
    apply List.forall_iff_forall_mem.mpr
    intro B hB
    exact
      List.forall_iff_forall_mem.mp
        (momentResidualCollapseBlocks_forall_isRelPrimitiveOn
          e₀.1 e₀.2.1 e₀.2.2)
        B (List.mem_of_mem_filter hB)
  have htargetFull :
      blocks.Forall
        (IsFullyPairedOn
          (momentCombinedPairing
            e.1 e.2.1 e.2.2)) := by
    apply List.forall_iff_forall_mem.mpr
    intro B hB
    have hB' :=
      mem_nonemptyMomentResidualCollapseBlocks.mp hB
    apply
      (htarget B ?_).1
    rw [momentPrimitiveBlockPartition_blocks,
      mem_momentNonemptyPrimitiveBlocks]
    exact ⟨Or.inr (Or.inr hB'.1), hB'.2⟩
  have htargetPrimitive :
      blocks.Forall
        (IsRelPrimitiveOn
          (momentCombinedPairing
            e.1 e.2.1 e.2.2)) := by
    apply List.forall_iff_forall_mem.mpr
    intro B hB
    have hB' :=
      mem_nonemptyMomentResidualCollapseBlocks.mp hB
    apply
      (htarget B ?_).2
    rw [momentPrimitiveBlockPartition_blocks,
      mem_momentNonemptyPrimitiveBlocks]
    exact ⟨Or.inr (Or.inr hB'.1), hB'.2⟩
  have hcandidates :
      ∀ a b : Fin (2 * m),
        IsRelFullyPaired
            (momentCombinedPairing
              e₀.1 e₀.2.1 e₀.2.2)
            active a b ↔
          IsRelFullyPaired
            (momentCombinedPairing
              e.1 e.2.1 e.2.2)
            active a b :=
    fun a b =>
      isRelFullyPaired_iff_of_common_primitive_block_cover
        (momentCombinedPairing
          e₀.1 e₀.2.1 e₀.2.2)
        (momentCombinedPairing
          e.1 e.2.1 e.2.2)
        blocks active hcover
        hsourceFull hsourcePrimitive
        htargetFull htargetPrimitive a b
  have hproper :
      momentResidualProperIntervals
          e.1 e.2.1 e.2.2 =
        momentResidualProperIntervals
          e₀.1 e₀.2.1 e₀.2.2 := by
    ext p
    rw [mem_momentResidualProperIntervals,
      mem_momentResidualProperIntervals, hactive]
    exact and_congr
      (hcandidates p.1 p.2).symm Iff.rfl
  unfold momentResidualIntervalChain
  rw [hproper]

theorem momentResidualChainSignature_eq_of_commonPrimitivePartition
    {m : ℕ} (e₀ e : MomentContraction m)
    (htarget :
      ∀ B ∈
          (momentPrimitiveBlockPartition
            e₀.1 e₀.2.1 e₀.2.2).blocks,
        IsFullyPairedOn
            (momentCombinedPairing e.1 e.2.1 e.2.2) B ∧
          IsRelPrimitiveOn
            (momentCombinedPairing e.1 e.2.1 e.2.2) B) :
    momentResidualChainSignature e.1 e.2.1 e.2.2 =
      momentResidualChainSignature
        e₀.1 e₀.2.1 e₀.2.2 := by
  have hchain :=
    momentResidualIntervalChain_eq_of_commonPrimitivePartition
      e₀ e htarget
  unfold momentResidualChainSignature
  rw [hchain]

/-! ## Exact refined-fibre equivalence -/

theorem momentRefinedFiberToPrimitivePartitionFiber_surjective
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r) :
    Function.Surjective
      (momentRefinedFiberToPrimitivePartitionFiber
        e₀ he₀) := by
  intro τ
  let P :=
    momentPrimitiveBlockPartition
      e₀.1 e₀.2.1 e₀.2.2
  have hfull : τ.1.IsFull := by
    intro i hiFix
    obtain ⟨B, hB, hiB⟩ :=
      P.exists_block_mem i
    exact (τ.2 B hB).1.ne_of_mem hiB hiFix
  let κfull :
      {κ : PartialPairing (Fin (2 * m)) //
        κ.IsFull} :=
    ⟨τ.1, hfull⟩
  let e : MomentContraction m :=
    (momentContractionEquivFullPairing m).symm κfull
  have hcombined :
      momentCombinedPairing e.1 e.2.1 e.2.2 =
        τ.1 := by
    change
      ((momentContractionEquivFullPairing m e).1) =
        κfull.1
    exact congrArg Subtype.val
      ((momentContractionEquivFullPairing m).apply_symm_apply
        κfull)
  have htarget :
      ∀ B ∈ P.blocks,
        IsFullyPairedOn
            (momentCombinedPairing e.1 e.2.1 e.2.2) B ∧
          IsRelPrimitiveOn
            (momentCombinedPairing e.1 e.2.1 e.2.2) B := by
    intro B hB
    rw [hcombined]
    exact τ.2 B hB
  have hmoment :
      momentContractionSignature e =
        momentContractionSignature e₀ :=
    momentContractionSignature_eq_of_commonPrimitivePartition
      e₀ e htarget
  have hresidual :
      momentResidualChainSignature e.1 e.2.1 e.2.2 =
        momentResidualChainSignature
          e₀.1 e₀.2.1 e₀.2.2 :=
    momentResidualChainSignature_eq_of_commonPrimitivePartition
      e₀ e htarget
  have he₀Signatures :=
    mem_momentRefinedContractionFiber.mp he₀
  have he :
      e ∈ momentRefinedContractionFiber m s r := by
    rw [mem_momentRefinedContractionFiber]
    exact
      ⟨hmoment.trans he₀Signatures.1,
        hresidual.trans he₀Signatures.2⟩
  let eFiber :
      MomentRefinedContractionFiberAt m s r :=
    ⟨e, he⟩
  refine ⟨eFiber, ?_⟩
  apply Subtype.ext
  exact hcombined

/-- The realized refined contraction fibre is exactly, rather than merely
embedded in, the generic fibre of pairings full and primitive on every
block of its common schedule. -/
def momentRefinedFiberEquivPrimitivePartitionFiber
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r) :
    MomentRefinedContractionFiberAt m s r ≃
      PrimitivePartitionFiber
        (momentPrimitiveBlockPartition
          e₀.1 e₀.2.1 e₀.2.2) :=
  Equiv.ofBijective
    (momentRefinedFiberToPrimitivePartitionFiber e₀ he₀)
    ⟨momentRefinedFiberToPrimitivePartitionFiber_injective
        e₀ he₀,
      momentRefinedFiberToPrimitivePartitionFiber_surjective
        e₀ he₀⟩

@[simp]
theorem momentRefinedFiberEquivPrimitivePartitionFiber_apply
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (e : MomentRefinedContractionFiberAt m s r) :
    momentRefinedFiberEquivPrimitivePartitionFiber
        e₀ he₀ e =
      momentRefinedFiberToPrimitivePartitionFiber
        e₀ he₀ e :=
  rfl

/-- Exact finite-sum reindexing of a residual-refined covariance fibre by
the complete primitive-partition fibre. -/
theorem sum_refinedCovariance_eq_sum_primitivePartitionFiber
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (v : Fin (2 * m) → T4) :
    (∑ e ∈ momentRefinedContractionFiber m s r,
        primitiveCovarianceProduct ρ ε m
          (momentCombinedPairing
            e.1 e.2.1 e.2.2) v) =
      ∑ τ : PrimitivePartitionFiber
          (momentPrimitiveBlockPartition
            e₀.1 e₀.2.1 e₀.2.2),
        primitiveCovarianceProduct ρ ε m τ.1 v := by
  let E :=
    momentRefinedFiberEquivPrimitivePartitionFiber
      e₀ he₀
  calc
    (∑ e ∈ momentRefinedContractionFiber m s r,
        primitiveCovarianceProduct ρ ε m
          (momentCombinedPairing
            e.1 e.2.1 e.2.2) v) =
        ∑ e : MomentRefinedContractionFiberAt m s r,
          primitiveCovarianceProduct ρ ε m
            (momentCombinedPairing
              e.1.1 e.1.2.1 e.1.2.2) v := by
      rw [← Finset.sum_attach]
      rw [Finset.attach_eq_univ]
    _ =
        ∑ e : MomentRefinedContractionFiberAt m s r,
          primitiveCovarianceProduct ρ ε m
            (E e).1 v := by
      apply Finset.sum_congr rfl
      intro e _he
      rfl
    _ =
        ∑ τ : PrimitivePartitionFiber
            (momentPrimitiveBlockPartition
              e₀.1 e₀.2.1 e₀.2.2),
          primitiveCovarianceProduct ρ ε m τ.1 v :=
      E.sum_comp fun τ =>
        primitiveCovarianceProduct ρ ε m τ.1 v

end

end Anderson4D
