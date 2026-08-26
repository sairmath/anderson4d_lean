import Anderson4D.DetParametrix.Paper42_Moment.R324PaperNestedHalfChainGlue
import Anderson4D.DetParametrix.Paper42_Moment.R324CompleteTerminalHeadBound
import Anderson4D.DetParametrix.Paper42_Moment.R324CompleteOrderAbsorption

/-!
# The literal complete nested run of paper Step 3

This module closes the last exact seam between the two terminal half
chains and the complete grouped primitive head used in (4.20).  It keeps
the primitive-pairing sum intact.  The one artificial edge across the
central cut is inserted only inside `normalizedInput` and is cancelled
exactly, almost everywhere, by the moving `torusDistSq` numerator.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324NestedCrossProperStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- On the untouched suffix, the current reconstruction is literally the
next-step reconstruction of the post tuple. -/
theorem reconstruct_eq_nextContext_reconstruct
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (v : ctx.step.SurvivingCoordinate → T4)
    (i : ctx.step.PostCoordinate) :
    ctx.step.reconstruct v i.1 =
      ctx.nextContext.reconstruct
        (ctx.step.splitSurvivingPiMeasurableEquiv v).2 i.1 := by
  let iNext : ctx.nextContext.SurvivingCoordinate := ⟨i.1, i.2⟩
  calc
    ctx.step.reconstruct v i.1 =
        v (ctx.step.postSurvivingCoordinate i) := by
      rw [← ctx.step.reconstruct_surviving v
        (ctx.step.postSurvivingCoordinate i)]
      rfl
    _ = (ctx.step.splitSurvivingPiMeasurableEquiv v).2 i := by
      symm
      exact ctx.step.splitSurvivingPiMeasurableEquiv_apply_snd v i
    _ = ctx.nextContext.reconstruct
          (ctx.step.splitSurvivingPiMeasurableEquiv v).2 i.1 := by
      symm
      calc
        ctx.nextContext.reconstruct
            (ctx.step.splitSurvivingPiMeasurableEquiv v).2 i.1 =
            (ctx.step.splitSurvivingPiMeasurableEquiv v).2 iNext := by
          exact ctx.nextContext.reconstruct_surviving _ iNext
        _ = (ctx.step.splitSurvivingPiMeasurableEquiv v).2 i := by
          congr 1

/-- The grouped covariance product on the untouched suffix is insensitive
to replacing the current reconstruction by the next-step reconstruction. -/
theorem nestedResidualPrimitiveSumProduct_next_reconstruct_eq
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (v : ctx.step.SurvivingCoordinate → T4) :
    r324NestedResidualPrimitiveSumProduct
        ρ ε κp κm π ctx.step.next (ctx.step.reconstruct v) =
      r324NestedResidualPrimitiveSumProduct
        ρ ε κp κm π ctx.step.next
          (ctx.nextContext.reconstruct
            (ctx.step.splitSurvivingPiMeasurableEquiv v).2) := by
  unfold r324NestedResidualPrimitiveSumProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro block hblock
  apply r324PrimitivePartitionBlockSum_congr_on
  intro i hi
  have hiActive : i ∈ ctx.step.next.activeCarrier := by
    unfold R324NestedCrossResidualPrefix.activeCarrier
    exact (mem_finsetUnionList_iff _).mpr
      ⟨block.carrier,
        List.mem_map.mpr ⟨block, hblock, rfl⟩, hi⟩
  exact ctx.reconstruct_eq_nextContext_reconstruct v ⟨i, hiActive⟩

/-- Standard primitive edges wholly contained in the left half of the
current cross shell. -/
def leftPrimitiveEdgeIndices
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    Finset (Fin (2 * ctx.step.order - 1)) :=
  Finset.univ.filter fun j => j.val < ctx.step.leftGapIndex.val

/-- Standard primitive edges wholly contained in the right half. -/
def rightPrimitiveEdgeIndices
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    Finset (Fin (2 * ctx.step.order - 1)) :=
  Finset.univ.filter fun j => ctx.step.rightGapIndex.val ≤ j.val

/-- The unique standard edge crossing the doubled cut. -/
def centralPrimitiveEdgeIndex
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    Fin (2 * ctx.step.order - 1) :=
  ⟨ctx.step.leftGapIndex.val, by
    have hgap := ctx.leftGapIndex_add_one_eq_rightGapIndex
    have hright := ctx.step.rightGapIndex.isLt
    omega⟩

/-- Standard primitive edge sourced at a nonterminal left-half vertex of
the current shell. -/
def leftHeadPrimitiveEdgeIndex
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324LeftHalfPullback ctx.step.head.carrier)
    (hne : i ≠
      (r324LeftHalfPullback ctx.step.head.carrier).max'
        ctx.leftHead_nonempty) :
    Fin (2 * ctx.step.order - 1) :=
  let j0 := ctx.step.blockOrderIso.symm
    ⟨leftMomentIndex i, mem_r324LeftHalfPullback.mp hi⟩
  ⟨j0.val, by
    have hiLe := Finset.le_max'
      (r324LeftHalfPullback ctx.step.head.carrier) i hi
    have hiLt : i <
        (r324LeftHalfPullback ctx.step.head.carrier).max'
          ctx.leftHead_nonempty :=
      lt_of_le_of_ne hiLe hne
    have hmapLt : leftMomentIndex i < ctx.step.head.leftGap := by
      rw [← leftMomentIndex_max'_r324LeftHalfPullback ctx.step.head]
      exact Fin.mk_lt_mk.mpr hiLt
    have hjLt : j0 < ctx.step.leftGapIndex := by
      apply ctx.step.blockOrderIso.lt_iff_lt.mp
      rw [ctx.step.blockOrderIso.apply_symm_apply,
        ctx.step.blockOrderIso_leftGapIndex]
      exact hmapLt
    have hgap := ctx.leftGapIndex_add_one_eq_rightGapIndex
    have hright := ctx.step.rightGapIndex.isLt
    omega⟩

@[simp]
theorem leftHeadPrimitiveEdgeIndex_val
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324LeftHalfPullback ctx.step.head.carrier)
    (hne : i ≠
      (r324LeftHalfPullback ctx.step.head.carrier).max'
        ctx.leftHead_nonempty) :
    (ctx.leftHeadPrimitiveEdgeIndex i hi hne).val =
      (ctx.step.blockOrderIso.symm
        ⟨leftMomentIndex i, mem_r324LeftHalfPullback.mp hi⟩).val :=
  rfl

theorem leftHeadPrimitiveEdgeIndex_mem
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324LeftHalfPullback ctx.step.head.carrier)
    (hne : i ≠
      (r324LeftHalfPullback ctx.step.head.carrier).max'
        ctx.leftHead_nonempty) :
    ctx.leftHeadPrimitiveEdgeIndex i hi hne ∈
      ctx.leftPrimitiveEdgeIndices := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hiLe := Finset.le_max'
    (r324LeftHalfPullback ctx.step.head.carrier) i hi
  have hiLt : i <
      (r324LeftHalfPullback ctx.step.head.carrier).max'
        ctx.leftHead_nonempty :=
    lt_of_le_of_ne hiLe hne
  have hmapLt : leftMomentIndex i < ctx.step.head.leftGap := by
    rw [← leftMomentIndex_max'_r324LeftHalfPullback ctx.step.head]
    exact Fin.mk_lt_mk.mpr hiLt
  have hjLt :
      (ctx.step.blockOrderIso.symm
        ⟨leftMomentIndex i,
          mem_r324LeftHalfPullback.mp hi⟩) <
        ctx.step.leftGapIndex := by
    apply ctx.step.blockOrderIso.lt_iff_lt.mp
    rw [ctx.step.blockOrderIso.apply_symm_apply,
      ctx.step.blockOrderIso_leftGapIndex]
    exact hmapLt
  exact hjLt

/-- Standard primitive edge sourced at a nonterminal right-half vertex. -/
def rightHeadPrimitiveEdgeIndex
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324RightHalfPullback ctx.step.head.carrier)
    (hne : i ≠
      (r324RightHalfPullback ctx.step.head.carrier).max'
        ctx.rightHead_nonempty) :
    Fin (2 * ctx.step.order - 1) :=
  let j0 := ctx.step.blockOrderIso.symm
    ⟨rightMomentIndex i, mem_r324RightHalfPullback.mp hi⟩
  ⟨j0.val, by
    have hiLe := Finset.le_max'
      (r324RightHalfPullback ctx.step.head.carrier) i hi
    have hiLt : i <
        (r324RightHalfPullback ctx.step.head.carrier).max'
          ctx.rightHead_nonempty :=
      lt_of_le_of_ne hiLe hne
    have hmapLt : rightMomentIndex i <
        (ctx.step.blockOrderIso
          (primitiveLast ctx.step.order ctx.step.one_le_order)).1 := by
      rw [← ctx.rightMomentIndex_rightHead_max']
      exact Fin.mk_lt_mk.mpr
        (Nat.add_lt_add_left hiLt m)
    have hjLt : j0 <
        primitiveLast ctx.step.order ctx.step.one_le_order := by
      apply ctx.step.blockOrderIso.lt_iff_lt.mp
      rw [ctx.step.blockOrderIso.apply_symm_apply]
      exact hmapLt
    omega⟩

@[simp]
theorem rightHeadPrimitiveEdgeIndex_val
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324RightHalfPullback ctx.step.head.carrier)
    (hne : i ≠
      (r324RightHalfPullback ctx.step.head.carrier).max'
        ctx.rightHead_nonempty) :
    (ctx.rightHeadPrimitiveEdgeIndex i hi hne).val =
      (ctx.step.blockOrderIso.symm
        ⟨rightMomentIndex i, mem_r324RightHalfPullback.mp hi⟩).val :=
  rfl

theorem rightHeadPrimitiveEdgeIndex_mem
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324RightHalfPullback ctx.step.head.carrier)
    (hne : i ≠
      (r324RightHalfPullback ctx.step.head.carrier).max'
        ctx.rightHead_nonempty) :
    ctx.rightHeadPrimitiveEdgeIndex i hi hne ∈
      ctx.rightPrimitiveEdgeIndices := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hgapMap :
      (ctx.step.blockOrderIso ctx.step.rightGapIndex).1 =
        ctx.step.head.rightGap :=
    congrArg Subtype.val ctx.step.blockOrderIso_rightGapIndex
  have hrightMem := mem_r324RightHalfPullback.mp hi
  have hpart : rightMomentIndex i ∈
      r324CrossRightPart m ctx.step.head.carrier := by
    exact Finset.mem_filter.mpr
      ⟨hrightMem, by simp [rightMomentIndex]⟩
  have hgapLe : ctx.step.head.rightGap ≤ rightMomentIndex i :=
    Finset.min'_le (r324CrossRightPart m ctx.step.head.carrier)
      (rightMomentIndex i) hpart
  have hjLe : ctx.step.rightGapIndex ≤
      ctx.step.blockOrderIso.symm
        ⟨rightMomentIndex i, hrightMem⟩ := by
    apply ctx.step.blockOrderIso.le_iff_le.mp
    rw [ctx.step.blockOrderIso_rightGapIndex,
      ctx.step.blockOrderIso.apply_symm_apply]
    exact hgapLe
  exact hjLe

/-- The next terminal left vertex along a current-shell internal edge. -/
def leftHeadSuccessorVertex
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324LeftHalfPullback ctx.step.head.carrier)
    (hne : i ≠
      (r324LeftHalfPullback ctx.step.head.carrier).max'
        ctx.leftHead_nonempty) : Fin m :=
  let j := ctx.leftHeadPrimitiveEdgeIndex i hi hne
  let ambient :=
    (ctx.step.blockOrderIso
      (primitiveEdgeRight ctx.step.order ctx.step.one_le_order j)).1
  ⟨ambient.val, by
    have hjmem := ctx.leftHeadPrimitiveEdgeIndex_mem i hi hne
    have hjlt := (Finset.mem_filter.mp hjmem).2
    have hrightLe :
        (primitiveEdgeRight ctx.step.order ctx.step.one_le_order j) ≤
          ctx.step.leftGapIndex := by
      change j.val + 1 ≤ ctx.step.leftGapIndex.val
      omega
    have himageLe := ctx.step.blockOrderIso.monotone hrightLe
    rw [ctx.step.blockOrderIso_leftGapIndex] at himageLe
    exact lt_of_le_of_lt himageLe
      (r324CrossGapLeft_lt_cut
        ctx.step.head.carrier ctx.step.head.crossCut)⟩

theorem leftMomentIndex_leftHeadSource
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324LeftHalfPullback ctx.step.head.carrier)
    (hne : i ≠
      (r324LeftHalfPullback ctx.step.head.carrier).max'
        ctx.leftHead_nonempty) :
    leftMomentIndex i =
      (ctx.step.blockOrderIso
        (primitiveEdgeLeft ctx.step.order ctx.step.one_le_order
          (ctx.leftHeadPrimitiveEdgeIndex i hi hne))).1 := by
  have hidx :
      primitiveEdgeLeft ctx.step.order ctx.step.one_le_order
          (ctx.leftHeadPrimitiveEdgeIndex i hi hne) =
        ctx.step.blockOrderIso.symm
          ⟨leftMomentIndex i,
            mem_r324LeftHalfPullback.mp hi⟩ := by
    apply Fin.ext
    rfl
  rw [hidx, ctx.step.blockOrderIso.apply_symm_apply]

theorem leftMomentIndex_leftHeadSuccessorVertex
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324LeftHalfPullback ctx.step.head.carrier)
    (hne : i ≠
      (r324LeftHalfPullback ctx.step.head.carrier).max'
        ctx.leftHead_nonempty) :
    leftMomentIndex (ctx.leftHeadSuccessorVertex i hi hne) =
      (ctx.step.blockOrderIso
        (primitiveEdgeRight ctx.step.order ctx.step.one_le_order
          (ctx.leftHeadPrimitiveEdgeIndex i hi hne))).1 := by
  apply Fin.ext
  rfl

/-- The next terminal right vertex along a current-shell internal edge. -/
def rightHeadSuccessorVertex
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324RightHalfPullback ctx.step.head.carrier)
    (hne : i ≠
      (r324RightHalfPullback ctx.step.head.carrier).max'
        ctx.rightHead_nonempty) : Fin m :=
  let j := ctx.rightHeadPrimitiveEdgeIndex i hi hne
  let ambient :=
    (ctx.step.blockOrderIso
      (primitiveEdgeRight ctx.step.order ctx.step.one_le_order j)).1
  ⟨ambient.val - m, by
    have hlt := ambient.isLt
    omega⟩

theorem rightMomentIndex_rightHeadSource
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324RightHalfPullback ctx.step.head.carrier)
    (hne : i ≠
      (r324RightHalfPullback ctx.step.head.carrier).max'
        ctx.rightHead_nonempty) :
    rightMomentIndex i =
      (ctx.step.blockOrderIso
        (primitiveEdgeLeft ctx.step.order ctx.step.one_le_order
          (ctx.rightHeadPrimitiveEdgeIndex i hi hne))).1 := by
  have hidx :
      primitiveEdgeLeft ctx.step.order ctx.step.one_le_order
          (ctx.rightHeadPrimitiveEdgeIndex i hi hne) =
        ctx.step.blockOrderIso.symm
          ⟨rightMomentIndex i,
            mem_r324RightHalfPullback.mp hi⟩ := by
    apply Fin.ext
    rfl
  rw [hidx, ctx.step.blockOrderIso.apply_symm_apply]

theorem rightMomentIndex_rightHeadSuccessorVertex
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324RightHalfPullback ctx.step.head.carrier)
    (hne : i ≠
      (r324RightHalfPullback ctx.step.head.carrier).max'
        ctx.rightHead_nonempty) :
    rightMomentIndex (ctx.rightHeadSuccessorVertex i hi hne) =
      (ctx.step.blockOrderIso
        (primitiveEdgeRight ctx.step.order ctx.step.one_le_order
          (ctx.rightHeadPrimitiveEdgeIndex i hi hne))).1 := by
  apply Fin.ext
  dsimp only [rightHeadSuccessorVertex, rightMomentIndex]
  have hjmem := ctx.rightHeadPrimitiveEdgeIndex_mem i hi hne
  have hjge := (Finset.mem_filter.mp hjmem).2
  have hrightLe : ctx.step.rightGapIndex ≤
      primitiveEdgeRight ctx.step.order ctx.step.one_le_order
        (ctx.rightHeadPrimitiveEdgeIndex i hi hne) := by
    change ctx.step.rightGapIndex.val ≤
      (ctx.rightHeadPrimitiveEdgeIndex i hi hne).val + 1
    omega
  have himageLe := ctx.step.blockOrderIso.monotone hrightLe
  rw [ctx.step.blockOrderIso_rightGapIndex] at himageLe
  have hcut := r324CrossGapRight_ge_cut
    ctx.step.head.carrier ctx.step.head.crossCut
  have hambientGe : m ≤
      (ctx.step.blockOrderIso
        (primitiveEdgeRight ctx.step.order ctx.step.one_le_order
          (ctx.rightHeadPrimitiveEdgeIndex i hi hne))).1.val :=
    hcut.trans himageLe
  exact Nat.add_sub_of_le hambientGe

@[simp]
theorem primitiveEdgeLeft_centralPrimitiveEdgeIndex
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    primitiveEdgeLeft ctx.step.order ctx.step.one_le_order
        ctx.centralPrimitiveEdgeIndex =
      ctx.step.leftGapIndex := by
  apply Fin.ext
  rfl

@[simp]
theorem primitiveEdgeRight_centralPrimitiveEdgeIndex
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    primitiveEdgeRight ctx.step.order ctx.step.one_le_order
        ctx.centralPrimitiveEdgeIndex =
      ctx.step.rightGapIndex := by
  apply Fin.ext
  change ctx.step.leftGapIndex.val + 1 =
    ctx.step.rightGapIndex.val
  exact ctx.leftGapIndex_add_one_eq_rightGapIndex

/-- The primitive edge family is the disjoint union of left internal
edges, the phantom cut edge, and right internal edges. -/
theorem primitiveEdgeIndices_eq_left_central_right
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    (Finset.univ : Finset (Fin (2 * ctx.step.order - 1))) =
      (ctx.leftPrimitiveEdgeIndices ∪
        {ctx.centralPrimitiveEdgeIndex}) ∪
      ctx.rightPrimitiveEdgeIndices := by
  ext j
  simp only [Finset.mem_univ, true_iff, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_filter,
    leftPrimitiveEdgeIndices, rightPrimitiveEdgeIndices]
  by_cases hleft : j.val < ctx.step.leftGapIndex.val
  · exact Or.inl (Or.inl ⟨True.intro, hleft⟩)
  · by_cases hcentral : j = ctx.centralPrimitiveEdgeIndex
    · exact Or.inl (Or.inr hcentral)
    · apply Or.inr
      refine ⟨True.intro, ?_⟩
      have hgap := ctx.leftGapIndex_add_one_eq_rightGapIndex
      have hjne : j.val ≠ ctx.step.leftGapIndex.val := by
        intro heq
        apply hcentral
        apply Fin.ext
        exact heq
      omega

theorem leftPrimitiveEdgeIndices_disjoint_central
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    Disjoint ctx.leftPrimitiveEdgeIndices
      {ctx.centralPrimitiveEdgeIndex} := by
  rw [Finset.disjoint_left]
  intro j hj hcentral
  have hjlt := (Finset.mem_filter.mp hj).2
  have heq := Finset.mem_singleton.mp hcentral
  subst j
  exact (lt_irrefl _) hjlt

theorem leftCentral_disjoint_rightPrimitiveEdgeIndices
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    Disjoint
      (ctx.leftPrimitiveEdgeIndices ∪
        {ctx.centralPrimitiveEdgeIndex})
      ctx.rightPrimitiveEdgeIndices := by
  rw [Finset.disjoint_left]
  intro j hj hright
  have hrightGe := (Finset.mem_filter.mp hright).2
  rcases Finset.mem_union.mp hj with hleft | hcentral
  · have hleftLt := (Finset.mem_filter.mp hleft).2
    have hgap := ctx.leftGapIndex_add_one_eq_rightGapIndex
    omega
  · have heq := Finset.mem_singleton.mp hcentral
    subst j
    have hgap := ctx.leftGapIndex_add_one_eq_rightGapIndex
    dsimp only [centralPrimitiveEdgeIndex] at hrightGe
    omega

/-- Exact three-way product decomposition of the normalized primitive
chain. -/
theorem primitiveChainProduct_normalized_eq_left_central_right
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (t : Fin (2 * ctx.step.order) → T4) :
    primitiveChainProduct ctx.step.order ctx.step.one_le_order
        ctx.step.normalizedInput t =
      (∏ j ∈ ctx.leftPrimitiveEdgeIndices,
          invSqKer
            (t (primitiveEdgeLeft
                ctx.step.order ctx.step.one_le_order j) -
              t (primitiveEdgeRight
                ctx.step.order ctx.step.one_le_order j))) *
        invSqKer
          (t ctx.step.leftGapIndex - t ctx.step.rightGapIndex) *
      (∏ j ∈ ctx.rightPrimitiveEdgeIndices,
          invSqKer
            (t (primitiveEdgeLeft
                ctx.step.order ctx.step.one_le_order j) -
              t (primitiveEdgeRight
                ctx.step.order ctx.step.one_le_order j))) := by
  unfold primitiveChainProduct R324NestedCrossStepContext.normalizedInput
  rw [ctx.primitiveEdgeIndices_eq_left_central_right,
    Finset.prod_union ctx.leftCentral_disjoint_rightPrimitiveEdgeIndices,
    Finset.prod_union ctx.leftPrimitiveEdgeIndices_disjoint_central]
  simp only [Finset.prod_singleton,
    ctx.primitiveEdgeLeft_centralPrimitiveEdgeIndex,
    ctx.primitiveEdgeRight_centralPrimitiveEdgeIndex]

end R324NestedCrossProperStepContext

/-! ## Head-local geometry for the genuine final shell

The preceding declarations were originally stated on a proper step because
they were first needed to expose the two connector legs.  The final shell has
no next block.  The following head-local names record exactly the same sparse
primitive order without manufacturing a dummy proper step. -/

namespace R324NestedCrossStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

theorem finalLeftHeadNonempty
    (step : R324NestedCrossStepContext κp κm π) :
    (r324LeftHalfPullback step.head.carrier).Nonempty :=
  r324LeftHalfPullback_nonempty_of_crossCut step.head.crossCut

theorem finalRightHeadNonempty
    (step : R324NestedCrossStepContext κp κm π) :
    (r324RightHalfPullback step.head.carrier).Nonempty :=
  r324RightHalfPullback_nonempty_of_crossCut step.head.crossCut

/-- The two cut sites are consecutive in the standard increasing order of
the final shell. -/
theorem final_leftGapIndex_add_one_eq_rightGapIndex
    (step : R324NestedCrossStepContext κp κm π) :
    step.leftGapIndex.val + 1 = step.rightGapIndex.val := by
  have hlt := step.leftGapIndex_lt_rightGapIndex
  by_contra hne
  have hstrict :
      step.leftGapIndex.val + 1 < step.rightGapIndex.val := by
    change step.leftGapIndex.val < step.rightGapIndex.val at hlt
    omega
  let j : Fin (2 * step.order) :=
    ⟨step.leftGapIndex.val + 1,
      hstrict.trans step.rightGapIndex.isLt⟩
  have hleftJ : step.leftGapIndex < j := by
    change step.leftGapIndex.val < step.leftGapIndex.val + 1
    omega
  have hjRight : j < step.rightGapIndex := Fin.mk_lt_mk.mpr hstrict
  have himageLeft := step.blockOrderIso.strictMono hleftJ
  have himageRight := step.blockOrderIso.strictMono hjRight
  rw [step.blockOrderIso_leftGapIndex] at himageLeft
  rw [step.blockOrderIso_rightGapIndex] at himageRight
  by_cases hcut : (step.blockOrderIso j).1.val < m
  · have hpart : (step.blockOrderIso j).1 ∈
        r324CrossLeftPart m step.head.carrier :=
      Finset.mem_filter.mpr ⟨(step.blockOrderIso j).2, hcut⟩
    have hle := Finset.le_max'
      (r324CrossLeftPart m step.head.carrier)
      (step.blockOrderIso j).1 hpart
    exact (not_le_of_gt himageLeft) hle
  · have hge : m ≤ (step.blockOrderIso j).1.val := by omega
    have hpart : (step.blockOrderIso j).1 ∈
        r324CrossRightPart m step.head.carrier :=
      Finset.mem_filter.mpr ⟨(step.blockOrderIso j).2, hge⟩
    have hle := Finset.min'_le
      (r324CrossRightPart m step.head.carrier)
      (step.blockOrderIso j).1 hpart
    exact (not_le_of_gt himageRight) hle

def finalLeftPrimitiveEdgeIndices
    (step : R324NestedCrossStepContext κp κm π) :
    Finset (Fin (2 * step.order - 1)) :=
  Finset.univ.filter fun j => j.val < step.leftGapIndex.val

def finalRightPrimitiveEdgeIndices
    (step : R324NestedCrossStepContext κp κm π) :
    Finset (Fin (2 * step.order - 1)) :=
  Finset.univ.filter fun j => step.rightGapIndex.val ≤ j.val

def finalCentralPrimitiveEdgeIndex
    (step : R324NestedCrossStepContext κp κm π) :
    Fin (2 * step.order - 1) :=
  ⟨step.leftGapIndex.val, by
    have hgap := step.final_leftGapIndex_add_one_eq_rightGapIndex
    have hright := step.rightGapIndex.isLt
    omega⟩

def finalLeftHeadPrimitiveEdgeIndex
    (step : R324NestedCrossStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324LeftHalfPullback step.head.carrier)
    (hne : i ≠
      (r324LeftHalfPullback step.head.carrier).max'
        step.finalLeftHeadNonempty) :
    Fin (2 * step.order - 1) :=
  let j0 := step.blockOrderIso.symm
    ⟨leftMomentIndex i, mem_r324LeftHalfPullback.mp hi⟩
  ⟨j0.val, by
    have hiLe := Finset.le_max'
      (r324LeftHalfPullback step.head.carrier) i hi
    have hiLt : i <
        (r324LeftHalfPullback step.head.carrier).max'
          step.finalLeftHeadNonempty :=
      lt_of_le_of_ne hiLe hne
    have hmapLt : leftMomentIndex i < step.head.leftGap := by
      rw [← leftMomentIndex_max'_r324LeftHalfPullback step.head]
      exact Fin.mk_lt_mk.mpr hiLt
    have hjLt : j0 < step.leftGapIndex := by
      apply step.blockOrderIso.lt_iff_lt.mp
      rw [step.blockOrderIso.apply_symm_apply,
        step.blockOrderIso_leftGapIndex]
      exact hmapLt
    have hgap := step.final_leftGapIndex_add_one_eq_rightGapIndex
    have hright := step.rightGapIndex.isLt
    omega⟩

@[simp]
theorem finalLeftHeadPrimitiveEdgeIndex_val
    (step : R324NestedCrossStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324LeftHalfPullback step.head.carrier)
    (hne : i ≠
      (r324LeftHalfPullback step.head.carrier).max'
        step.finalLeftHeadNonempty) :
    (step.finalLeftHeadPrimitiveEdgeIndex i hi hne).val =
      (step.blockOrderIso.symm
        ⟨leftMomentIndex i, mem_r324LeftHalfPullback.mp hi⟩).val :=
  rfl

theorem finalLeftHeadPrimitiveEdgeIndex_mem
    (step : R324NestedCrossStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324LeftHalfPullback step.head.carrier)
    (hne : i ≠
      (r324LeftHalfPullback step.head.carrier).max'
        step.finalLeftHeadNonempty) :
    step.finalLeftHeadPrimitiveEdgeIndex i hi hne ∈
      step.finalLeftPrimitiveEdgeIndices := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hiLe := Finset.le_max'
    (r324LeftHalfPullback step.head.carrier) i hi
  have hiLt : i <
      (r324LeftHalfPullback step.head.carrier).max'
        step.finalLeftHeadNonempty :=
    lt_of_le_of_ne hiLe hne
  have hmapLt : leftMomentIndex i < step.head.leftGap := by
    rw [← leftMomentIndex_max'_r324LeftHalfPullback step.head]
    exact Fin.mk_lt_mk.mpr hiLt
  have hjLt :
      step.blockOrderIso.symm
          ⟨leftMomentIndex i, mem_r324LeftHalfPullback.mp hi⟩ <
        step.leftGapIndex := by
    apply step.blockOrderIso.lt_iff_lt.mp
    rw [step.blockOrderIso.apply_symm_apply,
      step.blockOrderIso_leftGapIndex]
    exact hmapLt
  exact hjLt

def finalRightHeadPrimitiveEdgeIndex
    (step : R324NestedCrossStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324RightHalfPullback step.head.carrier)
    (hne : i ≠
      (r324RightHalfPullback step.head.carrier).max'
        step.finalRightHeadNonempty) :
    Fin (2 * step.order - 1) :=
  let j0 := step.blockOrderIso.symm
    ⟨rightMomentIndex i, mem_r324RightHalfPullback.mp hi⟩
  ⟨j0.val, by
    have hiLe := Finset.le_max'
      (r324RightHalfPullback step.head.carrier) i hi
    have hiLt : i <
        (r324RightHalfPullback step.head.carrier).max'
          step.finalRightHeadNonempty :=
      lt_of_le_of_ne hiLe hne
    let carrierMax : step.head.carrier :=
      ⟨step.head.carrier.max'
          ⟨step.head.rightGap, step.head.rightGap_mem⟩,
        Finset.max'_mem _ _⟩
    obtain ⟨jMax, hjMax⟩ := step.blockOrderIso.surjective carrierMax
    have hjMaxLe :
        jMax ≤ primitiveLast step.order step.one_le_order := by
      change jMax.val ≤ 2 * step.order - 1
      exact Nat.le_pred_of_lt jMax.isLt
    have hiRightLtMax :
        rightMomentIndex i < carrierMax.1 := by
      have hmapLt :
          rightMomentIndex i <
            rightMomentIndex
              ((r324RightHalfPullback step.head.carrier).max'
                step.finalRightHeadNonempty) :=
        Fin.mk_lt_mk.mpr (Nat.add_lt_add_left hiLt m)
      have hmaxMem := Finset.max'_mem
        (r324RightHalfPullback step.head.carrier)
        step.finalRightHeadNonempty
      have hcarrierMem := mem_r324RightHalfPullback.mp hmaxMem
      have hmaxLe := Finset.le_max' step.head.carrier
        (rightMomentIndex
          ((r324RightHalfPullback step.head.carrier).max'
            step.finalRightHeadNonempty)) hcarrierMem
      exact hmapLt.trans_le hmaxLe
    have hj0LtMax : j0 < jMax := by
      apply step.blockOrderIso.lt_iff_lt.mp
      rw [step.blockOrderIso.apply_symm_apply, hjMax]
      exact hiRightLtMax
    have hj0LtLast := hj0LtMax.trans_le hjMaxLe
    change j0.val < 2 * step.order - 1 at hj0LtLast
    exact hj0LtLast⟩

@[simp]
theorem finalRightHeadPrimitiveEdgeIndex_val
    (step : R324NestedCrossStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324RightHalfPullback step.head.carrier)
    (hne : i ≠
      (r324RightHalfPullback step.head.carrier).max'
        step.finalRightHeadNonempty) :
    (step.finalRightHeadPrimitiveEdgeIndex i hi hne).val =
      (step.blockOrderIso.symm
        ⟨rightMomentIndex i, mem_r324RightHalfPullback.mp hi⟩).val :=
  rfl

theorem finalRightHeadPrimitiveEdgeIndex_mem
    (step : R324NestedCrossStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324RightHalfPullback step.head.carrier)
    (hne : i ≠
      (r324RightHalfPullback step.head.carrier).max'
        step.finalRightHeadNonempty) :
    step.finalRightHeadPrimitiveEdgeIndex i hi hne ∈
      step.finalRightPrimitiveEdgeIndices := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hrightMem := mem_r324RightHalfPullback.mp hi
  have hpart : rightMomentIndex i ∈
      r324CrossRightPart m step.head.carrier :=
    Finset.mem_filter.mpr
      ⟨hrightMem, by simp [rightMomentIndex]⟩
  have hgapLe : step.head.rightGap ≤ rightMomentIndex i :=
    Finset.min'_le (r324CrossRightPart m step.head.carrier)
      (rightMomentIndex i) hpart
  have hjLe : step.rightGapIndex ≤
      step.blockOrderIso.symm ⟨rightMomentIndex i, hrightMem⟩ := by
    apply step.blockOrderIso.le_iff_le.mp
    rw [step.blockOrderIso_rightGapIndex,
      step.blockOrderIso.apply_symm_apply]
    exact hgapLe
  exact hjLe

def finalLeftHeadSuccessorVertex
    (step : R324NestedCrossStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324LeftHalfPullback step.head.carrier)
    (hne : i ≠
      (r324LeftHalfPullback step.head.carrier).max'
        step.finalLeftHeadNonempty) : Fin m :=
  let j := step.finalLeftHeadPrimitiveEdgeIndex i hi hne
  let ambient :=
    (step.blockOrderIso
      (primitiveEdgeRight step.order step.one_le_order j)).1
  ⟨ambient.val, by
    have hjmem := step.finalLeftHeadPrimitiveEdgeIndex_mem i hi hne
    have hjlt := (Finset.mem_filter.mp hjmem).2
    have hrightLe :
        primitiveEdgeRight step.order step.one_le_order j ≤
          step.leftGapIndex := by
      change j.val + 1 ≤ step.leftGapIndex.val
      omega
    have himageLe := step.blockOrderIso.monotone hrightLe
    rw [step.blockOrderIso_leftGapIndex] at himageLe
    exact lt_of_le_of_lt himageLe
      (r324CrossGapLeft_lt_cut
        step.head.carrier step.head.crossCut)⟩

theorem final_leftMomentIndex_headSource
    (step : R324NestedCrossStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324LeftHalfPullback step.head.carrier)
    (hne : i ≠
      (r324LeftHalfPullback step.head.carrier).max'
        step.finalLeftHeadNonempty) :
    leftMomentIndex i =
      (step.blockOrderIso
        (primitiveEdgeLeft step.order step.one_le_order
          (step.finalLeftHeadPrimitiveEdgeIndex i hi hne))).1 := by
  have hidx :
      primitiveEdgeLeft step.order step.one_le_order
          (step.finalLeftHeadPrimitiveEdgeIndex i hi hne) =
        step.blockOrderIso.symm
          ⟨leftMomentIndex i,
            mem_r324LeftHalfPullback.mp hi⟩ := by
    apply Fin.ext
    rfl
  rw [hidx, step.blockOrderIso.apply_symm_apply]

theorem final_leftMomentIndex_headSuccessor
    (step : R324NestedCrossStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324LeftHalfPullback step.head.carrier)
    (hne : i ≠
      (r324LeftHalfPullback step.head.carrier).max'
        step.finalLeftHeadNonempty) :
    leftMomentIndex
        (step.finalLeftHeadSuccessorVertex i hi hne) =
      (step.blockOrderIso
        (primitiveEdgeRight step.order step.one_le_order
          (step.finalLeftHeadPrimitiveEdgeIndex i hi hne))).1 := by
  apply Fin.ext
  rfl

def finalRightHeadSuccessorVertex
    (step : R324NestedCrossStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324RightHalfPullback step.head.carrier)
    (hne : i ≠
      (r324RightHalfPullback step.head.carrier).max'
        step.finalRightHeadNonempty) : Fin m :=
  let j := step.finalRightHeadPrimitiveEdgeIndex i hi hne
  let ambient :=
    (step.blockOrderIso
      (primitiveEdgeRight step.order step.one_le_order j)).1
  ⟨ambient.val - m, by
    have hlt := ambient.isLt
    omega⟩

theorem final_rightMomentIndex_headSource
    (step : R324NestedCrossStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324RightHalfPullback step.head.carrier)
    (hne : i ≠
      (r324RightHalfPullback step.head.carrier).max'
        step.finalRightHeadNonempty) :
    rightMomentIndex i =
      (step.blockOrderIso
        (primitiveEdgeLeft step.order step.one_le_order
          (step.finalRightHeadPrimitiveEdgeIndex i hi hne))).1 := by
  have hidx :
      primitiveEdgeLeft step.order step.one_le_order
          (step.finalRightHeadPrimitiveEdgeIndex i hi hne) =
        step.blockOrderIso.symm
          ⟨rightMomentIndex i,
            mem_r324RightHalfPullback.mp hi⟩ := by
    apply Fin.ext
    rfl
  rw [hidx, step.blockOrderIso.apply_symm_apply]

theorem final_rightMomentIndex_headSuccessor
    (step : R324NestedCrossStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324RightHalfPullback step.head.carrier)
    (hne : i ≠
      (r324RightHalfPullback step.head.carrier).max'
        step.finalRightHeadNonempty) :
    rightMomentIndex
        (step.finalRightHeadSuccessorVertex i hi hne) =
      (step.blockOrderIso
        (primitiveEdgeRight step.order step.one_le_order
          (step.finalRightHeadPrimitiveEdgeIndex i hi hne))).1 := by
  apply Fin.ext
  dsimp only [finalRightHeadSuccessorVertex, rightMomentIndex]
  have hjmem := step.finalRightHeadPrimitiveEdgeIndex_mem i hi hne
  have hjge := (Finset.mem_filter.mp hjmem).2
  have hrightLe : step.rightGapIndex ≤
      primitiveEdgeRight step.order step.one_le_order
        (step.finalRightHeadPrimitiveEdgeIndex i hi hne) := by
    change step.rightGapIndex.val ≤
      (step.finalRightHeadPrimitiveEdgeIndex i hi hne).val + 1
    omega
  have himageLe := step.blockOrderIso.monotone hrightLe
  rw [step.blockOrderIso_rightGapIndex] at himageLe
  have hcut := r324CrossGapRight_ge_cut
    step.head.carrier step.head.crossCut
  have hambientGe : m ≤
      (step.blockOrderIso
        (primitiveEdgeRight step.order step.one_le_order
          (step.finalRightHeadPrimitiveEdgeIndex i hi hne))).1.val :=
    hcut.trans himageLe
  exact Nat.add_sub_of_le hambientGe

@[simp]
theorem primitiveEdgeLeft_finalCentralPrimitiveEdgeIndex
    (step : R324NestedCrossStepContext κp κm π) :
    primitiveEdgeLeft step.order step.one_le_order
        step.finalCentralPrimitiveEdgeIndex =
      step.leftGapIndex := by
  apply Fin.ext
  rfl

@[simp]
theorem primitiveEdgeRight_finalCentralPrimitiveEdgeIndex
    (step : R324NestedCrossStepContext κp κm π) :
    primitiveEdgeRight step.order step.one_le_order
        step.finalCentralPrimitiveEdgeIndex =
      step.rightGapIndex := by
  apply Fin.ext
  change step.leftGapIndex.val + 1 = step.rightGapIndex.val
  exact step.final_leftGapIndex_add_one_eq_rightGapIndex

theorem finalPrimitiveEdgeIndices_eq_left_central_right
    (step : R324NestedCrossStepContext κp κm π) :
    (Finset.univ : Finset (Fin (2 * step.order - 1))) =
      (step.finalLeftPrimitiveEdgeIndices ∪
        {step.finalCentralPrimitiveEdgeIndex}) ∪
      step.finalRightPrimitiveEdgeIndices := by
  ext j
  simp only [Finset.mem_univ, true_iff, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_filter,
    finalLeftPrimitiveEdgeIndices, finalRightPrimitiveEdgeIndices]
  by_cases hleft : j.val < step.leftGapIndex.val
  · exact Or.inl (Or.inl ⟨True.intro, hleft⟩)
  · by_cases hcentral : j = step.finalCentralPrimitiveEdgeIndex
    · exact Or.inl (Or.inr hcentral)
    · apply Or.inr
      refine ⟨True.intro, ?_⟩
      have hgap := step.final_leftGapIndex_add_one_eq_rightGapIndex
      have hjne : j.val ≠ step.leftGapIndex.val := by
        intro heq
        apply hcentral
        apply Fin.ext
        exact heq
      omega

theorem finalLeftPrimitiveEdgeIndices_disjoint_central
    (step : R324NestedCrossStepContext κp κm π) :
    Disjoint step.finalLeftPrimitiveEdgeIndices
      {step.finalCentralPrimitiveEdgeIndex} := by
  rw [Finset.disjoint_left]
  intro j hj hcentral
  have hjlt := (Finset.mem_filter.mp hj).2
  have heq := Finset.mem_singleton.mp hcentral
  subst j
  exact (lt_irrefl _) hjlt

theorem finalLeftCentral_disjoint_rightPrimitiveEdgeIndices
    (step : R324NestedCrossStepContext κp κm π) :
    Disjoint
      (step.finalLeftPrimitiveEdgeIndices ∪
        {step.finalCentralPrimitiveEdgeIndex})
      step.finalRightPrimitiveEdgeIndices := by
  rw [Finset.disjoint_left]
  intro j hj hright
  have hrightGe := (Finset.mem_filter.mp hright).2
  rcases Finset.mem_union.mp hj with hleft | hcentral
  · have hleftLt := (Finset.mem_filter.mp hleft).2
    have hgap := step.final_leftGapIndex_add_one_eq_rightGapIndex
    omega
  · have heq := Finset.mem_singleton.mp hcentral
    subst j
    have hgap := step.final_leftGapIndex_add_one_eq_rightGapIndex
    dsimp only [finalCentralPrimitiveEdgeIndex] at hrightGe
    omega

theorem primitiveChainProduct_normalized_eq_finalParts
    (step : R324NestedCrossStepContext κp κm π)
    (t : Fin (2 * step.order) → T4) :
    primitiveChainProduct step.order step.one_le_order
        step.normalizedInput t =
      (∏ j ∈ step.finalLeftPrimitiveEdgeIndices,
          invSqKer
            (t (primitiveEdgeLeft step.order step.one_le_order j) -
              t (primitiveEdgeRight step.order step.one_le_order j))) *
        invSqKer (t step.leftGapIndex - t step.rightGapIndex) *
      (∏ j ∈ step.finalRightPrimitiveEdgeIndices,
          invSqKer
            (t (primitiveEdgeLeft step.order step.one_le_order j) -
              t (primitiveEdgeRight step.order step.one_le_order j))) := by
  unfold primitiveChainProduct R324NestedCrossStepContext.normalizedInput
  rw [step.finalPrimitiveEdgeIndices_eq_left_central_right,
    Finset.prod_union
      step.finalLeftCentral_disjoint_rightPrimitiveEdgeIndices,
    Finset.prod_union
      step.finalLeftPrimitiveEdgeIndices_disjoint_central]
  simp only [Finset.prod_singleton,
    step.primitiveEdgeLeft_finalCentralPrimitiveEdgeIndex,
    step.primitiveEdgeRight_finalCentralPrimitiveEdgeIndex]

theorem final_blockOrderIso_last_eq_max
    (step : R324NestedCrossStepContext κp κm π) :
    (step.blockOrderIso
        (primitiveLast step.order step.one_le_order)).1 =
      step.head.carrier.max'
        ⟨step.head.rightGap, step.head.rightGap_mem⟩ := by
  let hne : step.head.carrier.Nonempty :=
    ⟨step.head.rightGap, step.head.rightGap_mem⟩
  let carrierMax : step.head.carrier :=
    ⟨step.head.carrier.max' hne, Finset.max'_mem _ hne⟩
  obtain ⟨j, hj⟩ := step.blockOrderIso.surjective carrierMax
  apply le_antisymm
  · exact Finset.le_max' _ _
      (step.blockOrderIso
        (primitiveLast step.order step.one_le_order)).2
  · have hjLast :
        j ≤ primitiveLast step.order step.one_le_order := by
      change j.val ≤ 2 * step.order - 1
      exact Nat.le_pred_of_lt j.isLt
    have hmono := step.blockOrderIso.monotone hjLast
    rw [hj] at hmono
    exact hmono

theorem final_rightMomentIndex_headMax_eq_last
    (step : R324NestedCrossStepContext κp κm π) :
    rightMomentIndex
        ((r324RightHalfPullback step.head.carrier).max'
          step.finalRightHeadNonempty) =
      (step.blockOrderIso
        (primitiveLast step.order step.one_le_order)).1 := by
  let B := step.head.carrier
  let hB : B.Nonempty :=
    ⟨step.head.rightGap, step.head.rightGap_mem⟩
  let carrierMax := B.max' hB
  have hcarrierMaxGe : m ≤ carrierMax.val := by
    have hle := Finset.le_max' B step.head.rightGap
      step.head.rightGap_mem
    have hcut := r324CrossGapRight_ge_cut
      step.head.carrier step.head.crossCut
    exact hcut.trans hle
  let maxHalf : Fin m :=
    ⟨carrierMax.val - m, by
      have hlt := carrierMax.isLt
      omega⟩
  have hmaxHalfMap : rightMomentIndex maxHalf = carrierMax := by
    apply Fin.ext
    dsimp only [maxHalf, rightMomentIndex]
    omega
  have hmaxHalfMem :
      maxHalf ∈ r324RightHalfPullback step.head.carrier := by
    apply mem_r324RightHalfPullback.mpr
    rw [hmaxHalfMap]
    exact Finset.max'_mem B hB
  have hpullMaxMem := Finset.max'_mem
    (r324RightHalfPullback step.head.carrier)
    step.finalRightHeadNonempty
  have hpullCarrier := mem_r324RightHalfPullback.mp hpullMaxMem
  have hpullLe := Finset.le_max' B
    (rightMomentIndex
      ((r324RightHalfPullback step.head.carrier).max'
        step.finalRightHeadNonempty)) hpullCarrier
  have hmaxHalfLe := Finset.le_max'
    (r324RightHalfPullback step.head.carrier)
    maxHalf hmaxHalfMem
  rw [step.final_blockOrderIso_last_eq_max]
  apply Fin.ext
  change
    m + ((r324RightHalfPullback step.head.carrier).max'
      step.finalRightHeadNonempty).val = carrierMax.val
  change
    m + ((r324RightHalfPullback step.head.carrier).max'
      step.finalRightHeadNonempty).val ≤ carrierMax.val at hpullLe
  change maxHalf.val ≤
    ((r324RightHalfPullback step.head.carrier).max'
      step.finalRightHeadNonempty).val at hmaxHalfLe
  dsimp only [maxHalf] at hmaxHalfLe
  omega

end R324NestedCrossStepContext

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)

private theorem left_mem_terminal_of_block_local
    {π : κp.singles ≃ κm.singles}
    (block : R324NestedCrossBlock κp κm π)
    (i : Fin m) (hi : leftMomentIndex i ∈ block.carrier) :
    i ∈ terminal.left.state.active := by
  rw [terminal.left.active_eq_finalActive_of_processed_eq_schedule
    terminal.left_processed]
  rw [← leftMomentIndex_mem_momentResidualActive_iff]
  exact momentResidualCollapseBlock_subset_active
    (mem_nonemptyMomentResidualCollapseBlocks.mp
      block.mem_schedule).1 hi

private theorem right_mem_terminal_of_block_local
    {π : κp.singles ≃ κm.singles}
    (block : R324NestedCrossBlock κp κm π)
    (i : Fin m) (hi : rightMomentIndex i ∈ block.carrier) :
    i ∈ terminal.right.state.active := by
  rw [terminal.right.active_eq_finalActive_of_processed_eq_schedule
    terminal.right_processed]
  rw [← rightMomentIndex_mem_momentResidualActive_iff]
  exact momentResidualCollapseBlock_subset_active
    (mem_nonemptyMomentResidualCollapseBlocks.mp
      block.mem_schedule).1 hi

private theorem left_terminal_mem_schedule_local
    {π : κp.singles ≃ κm.singles}
    (i : Fin m) (hi : i ∈ terminal.left.state.active) :
    ∃ block ∈ r324NestedCrossSchedule κp κm π,
      leftMomentIndex i ∈ block.carrier := by
  have hiMoment :
      leftMomentIndex i ∈ momentResidualActive κp κm := by
    rw [leftMomentIndex_mem_momentResidualActive_iff]
    rw [← terminal.left.active_eq_finalActive_of_processed_eq_schedule
      terminal.left_processed]
    exact hi
  rw [← R324NestedCrossResidualPrefix.initial_activeCarrier_eq_momentResidualActive
    κp κm π] at hiMoment
  unfold R324NestedCrossResidualPrefix.activeCarrier
    R324NestedCrossResidualPrefix.initial at hiMoment
  obtain ⟨carrier, hcarrier, hiCarrier⟩ :=
    (mem_finsetUnionList_iff _).mp hiMoment
  obtain ⟨block, hblock, rfl⟩ := List.mem_map.mp hcarrier
  exact ⟨block, hblock, hiCarrier⟩

private theorem right_terminal_mem_schedule_local
    {π : κp.singles ≃ κm.singles}
    (i : Fin m) (hi : i ∈ terminal.right.state.active) :
    ∃ block ∈ r324NestedCrossSchedule κp κm π,
      rightMomentIndex i ∈ block.carrier := by
  have hiMoment :
      rightMomentIndex i ∈ momentResidualActive κp κm := by
    rw [rightMomentIndex_mem_momentResidualActive_iff]
    rw [← terminal.right.active_eq_finalActive_of_processed_eq_schedule
      terminal.right_processed]
    exact hi
  rw [← R324NestedCrossResidualPrefix.initial_activeCarrier_eq_momentResidualActive
    κp κm π] at hiMoment
  unfold R324NestedCrossResidualPrefix.activeCarrier
    R324NestedCrossResidualPrefix.initial at hiMoment
  obtain ⟨carrier, hcarrier, hiCarrier⟩ :=
    (mem_finsetUnionList_iff _).mp hiMoment
  obtain ⟨block, hblock, rfl⟩ := List.mem_map.mp hcarrier
  exact ⟨block, hblock, hiCarrier⟩

/-- Internal successor geometry for the genuine last left shell.  The
`tail = []` hypothesis removes the connector case and leaves exactly the
next standard primitive coordinate. -/
theorem left_edgeSuccessor_finalHeadInternal
    {π : κp.singles ≃ κm.singles}
    (step : R324NestedCrossStepContext κp κm π)
    (htail : step.tail = [])
    (i : Fin m)
    (hi : i ∈ r324LeftHalfPullback step.head.carrier)
    (hne : i ≠
      (r324LeftHalfPullback step.head.carrier).max'
        step.finalLeftHeadNonempty) :
    terminal.left.edgeSuccessor (r324InternalVertexEdgeSlot i) =
      varIdx (step.finalLeftHeadSuccessorVertex i hi hne) := by
  let target := step.finalLeftHeadSuccessorVertex i hi hne
  have htargetCarrier : leftMomentIndex target ∈ step.head.carrier := by
    rw [step.final_leftMomentIndex_headSuccessor i hi hne]
    exact (step.blockOrderIso _).2
  have htargetActive : target ∈ terminal.left.state.active :=
    terminal.left_mem_terminal_of_block_local
      step.head target htargetCarrier
  have hlt : i < target := by
    have hedge :
        primitiveEdgeLeft step.order step.one_le_order
            (step.finalLeftHeadPrimitiveEdgeIndex i hi hne) <
          primitiveEdgeRight step.order step.one_le_order
            (step.finalLeftHeadPrimitiveEdgeIndex i hi hne) := by
      apply Fin.mk_lt_mk.mpr
      omega
    have hmapLt := step.blockOrderIso.strictMono hedge
    change
      (step.blockOrderIso
        (primitiveEdgeLeft step.order step.one_le_order
          (step.finalLeftHeadPrimitiveEdgeIndex i hi hne))).1 <
      (step.blockOrderIso
        (primitiveEdgeRight step.order step.one_le_order
          (step.finalLeftHeadPrimitiveEdgeIndex i hi hne))).1 at hmapLt
    rw [← step.final_leftMomentIndex_headSource i hi hne,
      ← step.final_leftMomentIndex_headSuccessor i hi hne] at hmapLt
    exact Fin.mk_lt_mk.mpr hmapLt
  apply terminal.left.edgeSuccessor_internalVertex_eq_varIdx_of_no_between
    i target htargetActive hlt
  intro k hk hki
  obtain ⟨block, hblockSchedule, hkCarrier⟩ :=
    terminal.left_terminal_mem_schedule_local k hk
  have hfull := r324NestedCrossSchedule_pairwise_halfOutward κp κm π
  rw [step.residual.schedule_eq, step.remaining_eq,
    List.pairwise_append] at hfull
  rw [step.residual.schedule_eq, step.remaining_eq] at hblockSchedule
  rcases List.mem_append.mp hblockSchedule with hprocessed | hremaining
  · have hrel := hfull.2.2 block hprocessed step.head (by simp)
    exact (hrel.1 target
      (mem_r324LeftHalfPullback.mpr htargetCarrier) k
      (mem_r324LeftHalfPullback.mpr hkCarrier)).le
  · rcases List.mem_cons.mp hremaining with rfl | htailMem
    · let kStd := step.blockOrderIso.symm
        ⟨leftMomentIndex k, hkCarrier⟩
      have hsourceStdLt :
          primitiveEdgeLeft step.order step.one_le_order
              (step.finalLeftHeadPrimitiveEdgeIndex i hi hne) < kStd := by
        apply step.blockOrderIso.lt_iff_lt.mp
        rw [step.blockOrderIso.apply_symm_apply]
        change
          (step.blockOrderIso
            (primitiveEdgeLeft step.order step.one_le_order
              (step.finalLeftHeadPrimitiveEdgeIndex i hi hne))).1 <
            leftMomentIndex k
        rw [← step.final_leftMomentIndex_headSource i hi hne]
        exact Fin.mk_lt_mk.mpr hki
      have htargetStdLe :
          primitiveEdgeRight step.order step.one_le_order
              (step.finalLeftHeadPrimitiveEdgeIndex i hi hne) ≤ kStd := by
        change
          (step.finalLeftHeadPrimitiveEdgeIndex i hi hne).val + 1 ≤
            kStd.val
        change
          (step.finalLeftHeadPrimitiveEdgeIndex i hi hne).val <
            kStd.val at hsourceStdLt
        omega
      have hmapLe := step.blockOrderIso.monotone htargetStdLe
      rw [step.blockOrderIso.apply_symm_apply] at hmapLe
      change
        (step.blockOrderIso
          (primitiveEdgeRight step.order step.one_le_order
            (step.finalLeftHeadPrimitiveEdgeIndex i hi hne))).1 ≤
          leftMomentIndex k at hmapLe
      rw [← step.final_leftMomentIndex_headSuccessor i hi hne]
        at hmapLe
      change target.val ≤ k.val at hmapLe
      exact Fin.mk_le_mk.mpr hmapLe
    · rw [htail] at htailMem
      simp at htailMem

/-- Right-half analogue of `left_edgeSuccessor_finalHeadInternal`. -/
theorem right_edgeSuccessor_finalHeadInternal
    {π : κp.singles ≃ κm.singles}
    (step : R324NestedCrossStepContext κp κm π)
    (htail : step.tail = [])
    (i : Fin m)
    (hi : i ∈ r324RightHalfPullback step.head.carrier)
    (hne : i ≠
      (r324RightHalfPullback step.head.carrier).max'
        step.finalRightHeadNonempty) :
    terminal.right.edgeSuccessor (r324InternalVertexEdgeSlot i) =
      varIdx (step.finalRightHeadSuccessorVertex i hi hne) := by
  let target := step.finalRightHeadSuccessorVertex i hi hne
  have htargetCarrier : rightMomentIndex target ∈ step.head.carrier := by
    rw [step.final_rightMomentIndex_headSuccessor i hi hne]
    exact (step.blockOrderIso _).2
  have htargetActive : target ∈ terminal.right.state.active :=
    terminal.right_mem_terminal_of_block_local
      step.head target htargetCarrier
  have hlt : i < target := by
    have hedge :
        primitiveEdgeLeft step.order step.one_le_order
            (step.finalRightHeadPrimitiveEdgeIndex i hi hne) <
          primitiveEdgeRight step.order step.one_le_order
            (step.finalRightHeadPrimitiveEdgeIndex i hi hne) := by
      apply Fin.mk_lt_mk.mpr
      omega
    have hmapLt := step.blockOrderIso.strictMono hedge
    change
      (step.blockOrderIso
        (primitiveEdgeLeft step.order step.one_le_order
          (step.finalRightHeadPrimitiveEdgeIndex i hi hne))).1 <
      (step.blockOrderIso
        (primitiveEdgeRight step.order step.one_le_order
          (step.finalRightHeadPrimitiveEdgeIndex i hi hne))).1 at hmapLt
    rw [← step.final_rightMomentIndex_headSource i hi hne,
      ← step.final_rightMomentIndex_headSuccessor i hi hne] at hmapLt
    apply Fin.mk_lt_mk.mpr
    change m + i.val < m + target.val at hmapLt
    exact Nat.add_lt_add_iff_left.mp hmapLt
  apply terminal.right.edgeSuccessor_internalVertex_eq_varIdx_of_no_between
    i target htargetActive hlt
  intro k hk hki
  obtain ⟨block, hblockSchedule, hkCarrier⟩ :=
    terminal.right_terminal_mem_schedule_local k hk
  have hfull := r324NestedCrossSchedule_pairwise_halfOutward κp κm π
  rw [step.residual.schedule_eq, step.remaining_eq,
    List.pairwise_append] at hfull
  rw [step.residual.schedule_eq, step.remaining_eq] at hblockSchedule
  rcases List.mem_append.mp hblockSchedule with hprocessed | hremaining
  · have hrel := hfull.2.2 block hprocessed step.head (by simp)
    have hkLt := hrel.2 k
      (mem_r324RightHalfPullback.mpr hkCarrier) i hi
    exact (not_lt_of_ge hki.le hkLt).elim
  · rcases List.mem_cons.mp hremaining with rfl | htailMem
    · let kStd := step.blockOrderIso.symm
        ⟨rightMomentIndex k, hkCarrier⟩
      have hsourceStdLt :
          primitiveEdgeLeft step.order step.one_le_order
              (step.finalRightHeadPrimitiveEdgeIndex i hi hne) < kStd := by
        apply step.blockOrderIso.lt_iff_lt.mp
        rw [step.blockOrderIso.apply_symm_apply]
        change
          (step.blockOrderIso
            (primitiveEdgeLeft step.order step.one_le_order
              (step.finalRightHeadPrimitiveEdgeIndex i hi hne))).1 <
            rightMomentIndex k
        rw [← step.final_rightMomentIndex_headSource i hi hne]
        exact Fin.mk_lt_mk.mpr (Nat.add_lt_add_left hki m)
      have htargetStdLe :
          primitiveEdgeRight step.order step.one_le_order
              (step.finalRightHeadPrimitiveEdgeIndex i hi hne) ≤ kStd := by
        change
          (step.finalRightHeadPrimitiveEdgeIndex i hi hne).val + 1 ≤
            kStd.val
        change
          (step.finalRightHeadPrimitiveEdgeIndex i hi hne).val <
            kStd.val at hsourceStdLt
        omega
      have hmapLe := step.blockOrderIso.monotone htargetStdLe
      rw [step.blockOrderIso.apply_symm_apply] at hmapLe
      change
        (step.blockOrderIso
          (primitiveEdgeRight step.order step.one_le_order
            (step.finalRightHeadPrimitiveEdgeIndex i hi hne))).1 ≤
          rightMomentIndex k at hmapLe
      rw [← step.final_rightMomentIndex_headSuccessor i hi hne]
        at hmapLe
      apply Fin.mk_le_mk.mpr
      change m + target.val ≤ m + k.val at hmapLe
      exact Nat.add_le_add_iff_left.mp hmapLe
    · rw [htail] at htailMem
      simp at htailMem

theorem left_finalHeadInternal_edgeDisplacement_eq
    {π : κp.singles ≃ κm.singles}
    (step : R324NestedCrossStepContext κp κm π)
    (htail : step.tail = [])
    (i : Fin m)
    (hi : i ∈ r324LeftHalfPullback step.head.carrier)
    (hne : i ≠
      (r324LeftHalfPullback step.head.carrier).max'
        step.finalLeftHeadNonempty)
    (v : step.SurvivingCoordinate → T4) :
    terminal.left.edgeDisplacement 0 0
        (terminal.left.reconstruct
          (terminal.leftTupleOfNestedStep step v))
        (r324InternalVertexEdgeSlot i) =
      (step.splitSurvivingPiMeasurableEquiv v).1
          (primitiveEdgeLeft step.order step.one_le_order
            (step.finalLeftHeadPrimitiveEdgeIndex i hi hne)) -
        (step.splitSurvivingPiMeasurableEquiv v).1
          (primitiveEdgeRight step.order step.one_le_order
            (step.finalLeftHeadPrimitiveEdgeIndex i hi hne)) := by
  let target := step.finalLeftHeadSuccessorVertex i hi hne
  have hsourceCarrier : leftMomentIndex i ∈ step.head.carrier :=
    mem_r324LeftHalfPullback.mp hi
  have htargetCarrier : leftMomentIndex target ∈ step.head.carrier := by
    rw [step.final_leftMomentIndex_headSuccessor i hi hne]
    exact (step.blockOrderIso _).2
  have hsourceActive : i ∈ terminal.left.state.active :=
    terminal.left_mem_terminal_of_block_local
      step.head i hsourceCarrier
  have htargetActive : target ∈ terminal.left.state.active :=
    terminal.left_mem_terminal_of_block_local
      step.head target htargetCarrier
  have hsourceSlot :
      (r324InternalVertexEdgeSlot i).castSucc = varIdx i := by
    apply Fin.ext
    rfl
  unfold R324WithinHalfResidualPrefix.edgeDisplacement
  rw [hsourceSlot, terminal.left_edgeSuccessor_finalHeadInternal
      step htail i hi hne,
    assemble_varIdx, assemble_varIdx,
    terminal.left.reconstruct_surviving
      (terminal.leftTupleOfNestedStep step v)
      ⟨i, hsourceActive⟩,
    terminal.left.reconstruct_surviving
      (terminal.leftTupleOfNestedStep step v)
      ⟨target, htargetActive⟩]
  change step.reconstruct v (leftMomentIndex i) -
      step.reconstruct v (leftMomentIndex target) = _
  rw [step.final_leftMomentIndex_headSource i hi hne,
    step.final_leftMomentIndex_headSuccessor i hi hne]
  rw [step.splitSurvivingPiMeasurableEquiv_apply_fst,
    step.splitSurvivingPiMeasurableEquiv_apply_fst]
  rw [← step.reconstruct_surviving v
      (step.headSurvivingCoordinate
        (primitiveEdgeLeft step.order step.one_le_order
          (step.finalLeftHeadPrimitiveEdgeIndex i hi hne))),
    ← step.reconstruct_surviving v
      (step.headSurvivingCoordinate
        (primitiveEdgeRight step.order step.one_le_order
          (step.finalLeftHeadPrimitiveEdgeIndex i hi hne)))]
  rfl

theorem right_finalHeadInternal_edgeDisplacement_eq
    {π : κp.singles ≃ κm.singles}
    (step : R324NestedCrossStepContext κp κm π)
    (htail : step.tail = [])
    (i : Fin m)
    (hi : i ∈ r324RightHalfPullback step.head.carrier)
    (hne : i ≠
      (r324RightHalfPullback step.head.carrier).max'
        step.finalRightHeadNonempty)
    (v : step.SurvivingCoordinate → T4) :
    terminal.right.edgeDisplacement 0 0
        (terminal.right.reconstruct
          (terminal.rightTupleOfNestedStep step v))
        (r324InternalVertexEdgeSlot i) =
      (step.splitSurvivingPiMeasurableEquiv v).1
          (primitiveEdgeLeft step.order step.one_le_order
            (step.finalRightHeadPrimitiveEdgeIndex i hi hne)) -
        (step.splitSurvivingPiMeasurableEquiv v).1
          (primitiveEdgeRight step.order step.one_le_order
            (step.finalRightHeadPrimitiveEdgeIndex i hi hne)) := by
  let target := step.finalRightHeadSuccessorVertex i hi hne
  have hsourceCarrier : rightMomentIndex i ∈ step.head.carrier :=
    mem_r324RightHalfPullback.mp hi
  have htargetCarrier : rightMomentIndex target ∈ step.head.carrier := by
    rw [step.final_rightMomentIndex_headSuccessor i hi hne]
    exact (step.blockOrderIso _).2
  have hsourceActive : i ∈ terminal.right.state.active :=
    terminal.right_mem_terminal_of_block_local
      step.head i hsourceCarrier
  have htargetActive : target ∈ terminal.right.state.active :=
    terminal.right_mem_terminal_of_block_local
      step.head target htargetCarrier
  have hsourceSlot :
      (r324InternalVertexEdgeSlot i).castSucc = varIdx i := by
    apply Fin.ext
    rfl
  unfold R324WithinHalfResidualPrefix.edgeDisplacement
  rw [hsourceSlot, terminal.right_edgeSuccessor_finalHeadInternal
      step htail i hi hne,
    assemble_varIdx, assemble_varIdx,
    terminal.right.reconstruct_surviving
      (terminal.rightTupleOfNestedStep step v)
      ⟨i, hsourceActive⟩,
    terminal.right.reconstruct_surviving
      (terminal.rightTupleOfNestedStep step v)
      ⟨target, htargetActive⟩]
  change step.reconstruct v (rightMomentIndex i) -
      step.reconstruct v (rightMomentIndex target) = _
  rw [step.final_rightMomentIndex_headSource i hi hne,
    step.final_rightMomentIndex_headSuccessor i hi hne]
  rw [step.splitSurvivingPiMeasurableEquiv_apply_fst,
    step.splitSurvivingPiMeasurableEquiv_apply_fst]
  rw [← step.reconstruct_surviving v
      (step.headSurvivingCoordinate
        (primitiveEdgeLeft step.order step.one_le_order
          (step.finalRightHeadPrimitiveEdgeIndex i hi hne))),
    ← step.reconstruct_surviving v
      (step.headSurvivingCoordinate
        (primitiveEdgeRight step.order step.one_le_order
          (step.finalRightHeadPrimitiveEdgeIndex i hi hne)))]
  rfl

/-- A nonterminal left source in the current shell points to the next
standard block coordinate in the full terminal sparse chain. -/
theorem left_edgeSuccessor_headInternal
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324LeftHalfPullback ctx.step.head.carrier)
    (hne : i ≠
      (r324LeftHalfPullback ctx.step.head.carrier).max'
        ctx.leftHead_nonempty) :
    terminal.left.edgeSuccessor (r324InternalVertexEdgeSlot i) =
      varIdx (ctx.leftHeadSuccessorVertex i hi hne) := by
  let target := ctx.leftHeadSuccessorVertex i hi hne
  have htargetCarrier :
      leftMomentIndex target ∈ ctx.step.head.carrier := by
    rw [ctx.leftMomentIndex_leftHeadSuccessorVertex i hi hne]
    exact (ctx.step.blockOrderIso _).2
  have htargetActive : target ∈ terminal.left.state.active :=
    terminal.left_mem_terminal_of_block_local
      ctx.step.head target htargetCarrier
  have hlt : i < target := by
    have hedge :
        primitiveEdgeLeft ctx.step.order ctx.step.one_le_order
            (ctx.leftHeadPrimitiveEdgeIndex i hi hne) <
          primitiveEdgeRight ctx.step.order ctx.step.one_le_order
            (ctx.leftHeadPrimitiveEdgeIndex i hi hne) := by
      apply Fin.mk_lt_mk.mpr
      omega
    have hmapLt := ctx.step.blockOrderIso.strictMono hedge
    change
      (ctx.step.blockOrderIso
        (primitiveEdgeLeft ctx.step.order ctx.step.one_le_order
          (ctx.leftHeadPrimitiveEdgeIndex i hi hne))).1 <
      (ctx.step.blockOrderIso
        (primitiveEdgeRight ctx.step.order ctx.step.one_le_order
          (ctx.leftHeadPrimitiveEdgeIndex i hi hne))).1 at hmapLt
    rw [← ctx.leftMomentIndex_leftHeadSource i hi hne,
      ← ctx.leftMomentIndex_leftHeadSuccessorVertex i hi hne] at hmapLt
    change i.val < target.val at hmapLt
    exact Fin.mk_lt_mk.mpr hmapLt
  apply terminal.left.edgeSuccessor_internalVertex_eq_varIdx_of_no_between
    i target htargetActive hlt
  intro k hk hki
  obtain ⟨block, hblockSchedule, hkCarrier⟩ :=
    terminal.left_terminal_mem_schedule_local k hk
  have hfull := r324NestedCrossSchedule_pairwise_halfOutward κp κm π
  rw [ctx.step.residual.schedule_eq, ctx.step.remaining_eq,
    List.pairwise_append] at hfull
  rw [ctx.step.residual.schedule_eq, ctx.step.remaining_eq] at hblockSchedule
  rcases List.mem_append.mp hblockSchedule with hprocessed | hremaining
  · have hrel := hfull.2.2 block hprocessed ctx.step.head (by simp)
    exact (hrel.1 target
      (mem_r324LeftHalfPullback.mpr htargetCarrier) k
      (mem_r324LeftHalfPullback.mpr hkCarrier)).le
  · rcases List.mem_cons.mp hremaining with rfl | htail
    · let kStd := ctx.step.blockOrderIso.symm
        ⟨leftMomentIndex k, hkCarrier⟩
      have hsourceStdLt :
          primitiveEdgeLeft ctx.step.order ctx.step.one_le_order
              (ctx.leftHeadPrimitiveEdgeIndex i hi hne) < kStd := by
        apply ctx.step.blockOrderIso.lt_iff_lt.mp
        rw [ctx.step.blockOrderIso.apply_symm_apply]
        change
          (ctx.step.blockOrderIso
            (primitiveEdgeLeft ctx.step.order ctx.step.one_le_order
              (ctx.leftHeadPrimitiveEdgeIndex i hi hne))).1 <
            leftMomentIndex k
        rw [← ctx.leftMomentIndex_leftHeadSource i hi hne]
        exact Fin.mk_lt_mk.mpr hki
      have htargetStdLe :
          primitiveEdgeRight ctx.step.order ctx.step.one_le_order
              (ctx.leftHeadPrimitiveEdgeIndex i hi hne) ≤ kStd := by
        change (ctx.leftHeadPrimitiveEdgeIndex i hi hne).val + 1 ≤
          kStd.val
        change (ctx.leftHeadPrimitiveEdgeIndex i hi hne).val <
          kStd.val at hsourceStdLt
        omega
      have hmapLe := ctx.step.blockOrderIso.monotone htargetStdLe
      rw [ctx.step.blockOrderIso.apply_symm_apply] at hmapLe
      change
        (ctx.step.blockOrderIso
          (primitiveEdgeRight ctx.step.order ctx.step.one_le_order
            (ctx.leftHeadPrimitiveEdgeIndex i hi hne))).1 ≤
          leftMomentIndex k at hmapLe
      rw [← ctx.leftMomentIndex_leftHeadSuccessorVertex i hi hne]
        at hmapLe
      change target.val ≤ k.val at hmapLe
      exact Fin.mk_le_mk.mpr hmapLe
    · have hrel :=
        (List.pairwise_cons.mp hfull.2.1).1 block htail
      have hkLt := hrel.1 k
        (mem_r324LeftHalfPullback.mpr hkCarrier) i hi
      exact (not_lt_of_ge hki.le hkLt).elim

/-- Right-half internal successor. -/
theorem right_edgeSuccessor_headInternal
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324RightHalfPullback ctx.step.head.carrier)
    (hne : i ≠
      (r324RightHalfPullback ctx.step.head.carrier).max'
        ctx.rightHead_nonempty) :
    terminal.right.edgeSuccessor (r324InternalVertexEdgeSlot i) =
      varIdx (ctx.rightHeadSuccessorVertex i hi hne) := by
  let target := ctx.rightHeadSuccessorVertex i hi hne
  have htargetCarrier :
      rightMomentIndex target ∈ ctx.step.head.carrier := by
    rw [ctx.rightMomentIndex_rightHeadSuccessorVertex i hi hne]
    exact (ctx.step.blockOrderIso _).2
  have htargetActive : target ∈ terminal.right.state.active :=
    terminal.right_mem_terminal_of_block_local
      ctx.step.head target htargetCarrier
  have hlt : i < target := by
    have hedge :
        primitiveEdgeLeft ctx.step.order ctx.step.one_le_order
            (ctx.rightHeadPrimitiveEdgeIndex i hi hne) <
          primitiveEdgeRight ctx.step.order ctx.step.one_le_order
            (ctx.rightHeadPrimitiveEdgeIndex i hi hne) := by
      apply Fin.mk_lt_mk.mpr
      omega
    have hmapLt := ctx.step.blockOrderIso.strictMono hedge
    change
      (ctx.step.blockOrderIso
        (primitiveEdgeLeft ctx.step.order ctx.step.one_le_order
          (ctx.rightHeadPrimitiveEdgeIndex i hi hne))).1 <
      (ctx.step.blockOrderIso
        (primitiveEdgeRight ctx.step.order ctx.step.one_le_order
          (ctx.rightHeadPrimitiveEdgeIndex i hi hne))).1 at hmapLt
    rw [← ctx.rightMomentIndex_rightHeadSource i hi hne,
      ← ctx.rightMomentIndex_rightHeadSuccessorVertex i hi hne] at hmapLt
    apply Fin.mk_lt_mk.mpr
    change m + i.val < m + target.val at hmapLt
    exact Nat.add_lt_add_iff_left.mp hmapLt
  apply terminal.right.edgeSuccessor_internalVertex_eq_varIdx_of_no_between
    i target htargetActive hlt
  intro k hk hki
  obtain ⟨block, hblockSchedule, hkCarrier⟩ :=
    terminal.right_terminal_mem_schedule_local k hk
  have hfull := r324NestedCrossSchedule_pairwise_halfOutward κp κm π
  rw [ctx.step.residual.schedule_eq, ctx.step.remaining_eq,
    List.pairwise_append] at hfull
  rw [ctx.step.residual.schedule_eq, ctx.step.remaining_eq] at hblockSchedule
  rcases List.mem_append.mp hblockSchedule with hprocessed | hremaining
  · have hrel := hfull.2.2 block hprocessed ctx.step.head (by simp)
    have hkLt := hrel.2 k
      (mem_r324RightHalfPullback.mpr hkCarrier) i hi
    exact (not_lt_of_ge hki.le hkLt).elim
  · rcases List.mem_cons.mp hremaining with rfl | htail
    · let kStd := ctx.step.blockOrderIso.symm
        ⟨rightMomentIndex k, hkCarrier⟩
      have hsourceStdLt :
          primitiveEdgeLeft ctx.step.order ctx.step.one_le_order
              (ctx.rightHeadPrimitiveEdgeIndex i hi hne) < kStd := by
        apply ctx.step.blockOrderIso.lt_iff_lt.mp
        rw [ctx.step.blockOrderIso.apply_symm_apply]
        change
          (ctx.step.blockOrderIso
            (primitiveEdgeLeft ctx.step.order ctx.step.one_le_order
              (ctx.rightHeadPrimitiveEdgeIndex i hi hne))).1 <
            rightMomentIndex k
        rw [← ctx.rightMomentIndex_rightHeadSource i hi hne]
        exact Fin.mk_lt_mk.mpr
          (Nat.add_lt_add_left hki m)
      have htargetStdLe :
          primitiveEdgeRight ctx.step.order ctx.step.one_le_order
              (ctx.rightHeadPrimitiveEdgeIndex i hi hne) ≤ kStd := by
        change (ctx.rightHeadPrimitiveEdgeIndex i hi hne).val + 1 ≤
          kStd.val
        change (ctx.rightHeadPrimitiveEdgeIndex i hi hne).val <
          kStd.val at hsourceStdLt
        omega
      have hmapLe := ctx.step.blockOrderIso.monotone htargetStdLe
      rw [ctx.step.blockOrderIso.apply_symm_apply] at hmapLe
      change
        (ctx.step.blockOrderIso
          (primitiveEdgeRight ctx.step.order ctx.step.one_le_order
            (ctx.rightHeadPrimitiveEdgeIndex i hi hne))).1 ≤
          rightMomentIndex k at hmapLe
      rw [← ctx.rightMomentIndex_rightHeadSuccessorVertex i hi hne]
        at hmapLe
      apply Fin.mk_le_mk.mpr
      change m + target.val ≤ m + k.val at hmapLe
      exact Nat.add_le_add_iff_left.mp hmapLe
    · have hrel :=
        (List.pairwise_cons.mp hfull.2.1).1 block htail
      exact (hrel.2 target
        (mem_r324RightHalfPullback.mpr htargetCarrier) k
        (mem_r324RightHalfPullback.mpr hkCarrier)).le

/-- A left internal half-chain slot reads exactly the corresponding
standard primitive edge of the current head coordinates. -/
theorem left_headInternal_edgeDisplacement_eq
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324LeftHalfPullback ctx.step.head.carrier)
    (hne : i ≠
      (r324LeftHalfPullback ctx.step.head.carrier).max'
        ctx.leftHead_nonempty)
    (v : ctx.step.SurvivingCoordinate → T4) :
    terminal.left.edgeDisplacement 0 0
        (terminal.left.reconstruct
          (terminal.leftTupleOfNestedStep ctx.step v))
        (r324InternalVertexEdgeSlot i) =
      (ctx.step.splitSurvivingPiMeasurableEquiv v).1
          (primitiveEdgeLeft ctx.step.order ctx.step.one_le_order
            (ctx.leftHeadPrimitiveEdgeIndex i hi hne)) -
        (ctx.step.splitSurvivingPiMeasurableEquiv v).1
          (primitiveEdgeRight ctx.step.order ctx.step.one_le_order
            (ctx.leftHeadPrimitiveEdgeIndex i hi hne)) := by
  let target := ctx.leftHeadSuccessorVertex i hi hne
  have hsourceCarrier :
      leftMomentIndex i ∈ ctx.step.head.carrier :=
    mem_r324LeftHalfPullback.mp hi
  have htargetCarrier :
      leftMomentIndex target ∈ ctx.step.head.carrier := by
    rw [ctx.leftMomentIndex_leftHeadSuccessorVertex i hi hne]
    exact (ctx.step.blockOrderIso _).2
  have hsourceActive : i ∈ terminal.left.state.active :=
    terminal.left_mem_terminal_of_block_local
      ctx.step.head i hsourceCarrier
  have htargetActive : target ∈ terminal.left.state.active :=
    terminal.left_mem_terminal_of_block_local
      ctx.step.head target htargetCarrier
  have hsourceSlot :
      (r324InternalVertexEdgeSlot i).castSucc = varIdx i := by
    apply Fin.ext
    rfl
  unfold R324WithinHalfResidualPrefix.edgeDisplacement
  rw [hsourceSlot, terminal.left_edgeSuccessor_headInternal
      ctx i hi hne,
    assemble_varIdx, assemble_varIdx,
    terminal.left.reconstruct_surviving
      (terminal.leftTupleOfNestedStep ctx.step v)
      ⟨i, hsourceActive⟩,
    terminal.left.reconstruct_surviving
      (terminal.leftTupleOfNestedStep ctx.step v)
      ⟨target, htargetActive⟩]
  change
    ctx.step.reconstruct v (leftMomentIndex i) -
        ctx.step.reconstruct v (leftMomentIndex target) = _
  rw [ctx.leftMomentIndex_leftHeadSource i hi hne,
    ctx.leftMomentIndex_leftHeadSuccessorVertex i hi hne]
  rw [ctx.step.splitSurvivingPiMeasurableEquiv_apply_fst,
    ctx.step.splitSurvivingPiMeasurableEquiv_apply_fst]
  rw [← ctx.step.reconstruct_surviving v
      (ctx.step.headSurvivingCoordinate
        (primitiveEdgeLeft ctx.step.order ctx.step.one_le_order
          (ctx.leftHeadPrimitiveEdgeIndex i hi hne))),
    ← ctx.step.reconstruct_surviving v
      (ctx.step.headSurvivingCoordinate
        (primitiveEdgeRight ctx.step.order ctx.step.one_le_order
          (ctx.leftHeadPrimitiveEdgeIndex i hi hne)))]
  rfl

/-- Right-half analogue of
`left_headInternal_edgeDisplacement_eq`. -/
theorem right_headInternal_edgeDisplacement_eq
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324RightHalfPullback ctx.step.head.carrier)
    (hne : i ≠
      (r324RightHalfPullback ctx.step.head.carrier).max'
        ctx.rightHead_nonempty)
    (v : ctx.step.SurvivingCoordinate → T4) :
    terminal.right.edgeDisplacement 0 0
        (terminal.right.reconstruct
          (terminal.rightTupleOfNestedStep ctx.step v))
        (r324InternalVertexEdgeSlot i) =
      (ctx.step.splitSurvivingPiMeasurableEquiv v).1
          (primitiveEdgeLeft ctx.step.order ctx.step.one_le_order
            (ctx.rightHeadPrimitiveEdgeIndex i hi hne)) -
        (ctx.step.splitSurvivingPiMeasurableEquiv v).1
          (primitiveEdgeRight ctx.step.order ctx.step.one_le_order
            (ctx.rightHeadPrimitiveEdgeIndex i hi hne)) := by
  let target := ctx.rightHeadSuccessorVertex i hi hne
  have hsourceCarrier :
      rightMomentIndex i ∈ ctx.step.head.carrier :=
    mem_r324RightHalfPullback.mp hi
  have htargetCarrier :
      rightMomentIndex target ∈ ctx.step.head.carrier := by
    rw [ctx.rightMomentIndex_rightHeadSuccessorVertex i hi hne]
    exact (ctx.step.blockOrderIso _).2
  have hsourceActive : i ∈ terminal.right.state.active :=
    terminal.right_mem_terminal_of_block_local
      ctx.step.head i hsourceCarrier
  have htargetActive : target ∈ terminal.right.state.active :=
    terminal.right_mem_terminal_of_block_local
      ctx.step.head target htargetCarrier
  have hsourceSlot :
      (r324InternalVertexEdgeSlot i).castSucc = varIdx i := by
    apply Fin.ext
    rfl
  unfold R324WithinHalfResidualPrefix.edgeDisplacement
  rw [hsourceSlot, terminal.right_edgeSuccessor_headInternal
      ctx i hi hne,
    assemble_varIdx, assemble_varIdx,
    terminal.right.reconstruct_surviving
      (terminal.rightTupleOfNestedStep ctx.step v)
      ⟨i, hsourceActive⟩,
    terminal.right.reconstruct_surviving
      (terminal.rightTupleOfNestedStep ctx.step v)
      ⟨target, htargetActive⟩]
  change
    ctx.step.reconstruct v (rightMomentIndex i) -
        ctx.step.reconstruct v (rightMomentIndex target) = _
  rw [ctx.rightMomentIndex_rightHeadSource i hi hne,
    ctx.rightMomentIndex_rightHeadSuccessorVertex i hi hne]
  rw [ctx.step.splitSurvivingPiMeasurableEquiv_apply_fst,
    ctx.step.splitSurvivingPiMeasurableEquiv_apply_fst]
  rw [← ctx.step.reconstruct_surviving v
      (ctx.step.headSurvivingCoordinate
        (primitiveEdgeLeft ctx.step.order ctx.step.one_le_order
          (ctx.rightHeadPrimitiveEdgeIndex i hi hne))),
    ← ctx.step.reconstruct_surviving v
      (ctx.step.headSurvivingCoordinate
        (primitiveEdgeRight ctx.step.order ctx.step.one_le_order
          (ctx.rightHeadPrimitiveEdgeIndex i hi hne)))]
  rfl

/-- On the genuine last shell, the restricted terminal left path is the
left internal part of the normalized primitive chain. -/
theorem nestedLeftHalfInvSqProduct_finalHead_eq_primitiveEdges
    {π : κp.singles ≃ κm.singles}
    (step : R324NestedCrossStepContext κp κm π)
    (htail : step.tail = [])
    (v : step.SurvivingCoordinate → T4) :
    terminal.nestedLeftHalfInvSqProduct step
        step.head.carrier step.finalLeftHeadNonempty v =
      ∏ j ∈ step.finalLeftPrimitiveEdgeIndices,
        invSqKer
          ((step.splitSurvivingPiMeasurableEquiv v).1
              (primitiveEdgeLeft step.order step.one_le_order j) -
            (step.splitSurvivingPiMeasurableEquiv v).1
              (primitiveEdgeRight step.order step.one_le_order j)) := by
  let carrier := r324LeftHalfPullback step.head.carrier
  let source := carrier.erase (carrier.max' step.finalLeftHeadNonempty)
  have hslotInj : Set.InjOn
      (r324InternalVertexEdgeSlot : Fin m → Fin (m + 1)) source := by
    intro i hi k hk hik
    apply Fin.ext
    have hval := congrArg Fin.val hik
    simp only [r324InternalVertexEdgeSlot] at hval
    omega
  unfold nestedLeftHalfInvSqProduct
    R324WithinHalfResidualPrefix.halfInvSqChainProduct
    R324WithinHalfResidualPrefix.halfChainEdgeSlots
  rw [Finset.prod_image hslotInj]
  apply Finset.prod_bij
      (fun i hi =>
        step.finalLeftHeadPrimitiveEdgeIndex i
          (Finset.mem_erase.mp hi).2
          (Finset.mem_erase.mp hi).1)
  · intro i hi
    exact step.finalLeftHeadPrimitiveEdgeIndex_mem i
      (Finset.mem_erase.mp hi).2
      (Finset.mem_erase.mp hi).1
  · intro i hi k hk hik
    apply leftMomentIndex_injective
    rw [step.final_leftMomentIndex_headSource i
        (Finset.mem_erase.mp hi).2
        (Finset.mem_erase.mp hi).1,
      step.final_leftMomentIndex_headSource k
        (Finset.mem_erase.mp hk).2
        (Finset.mem_erase.mp hk).1,
      hik]
  · intro j hj
    have hjLt :
        primitiveEdgeLeft step.order step.one_le_order j <
          step.leftGapIndex := by
      apply Fin.mk_lt_mk.mpr
      exact (Finset.mem_filter.mp hj).2
    let ambient : {i : Fin (2 * m) // i ∈ step.head.carrier} :=
      step.blockOrderIso
        (primitiveEdgeLeft step.order step.one_le_order j)
    have hambientLtGap : ambient.1 < step.head.leftGap := by
      have himage := step.blockOrderIso.strictMono hjLt
      rw [step.blockOrderIso_leftGapIndex] at himage
      exact himage
    have hambientCut : ambient.1.val < m := by
      change ambient.1.val < step.head.leftGap.val at hambientLtGap
      exact hambientLtGap.trans
        (r324CrossGapLeft_lt_cut step.head.carrier step.head.crossCut)
    let i : Fin m := ⟨ambient.1.val, hambientCut⟩
    have hiMap : leftMomentIndex i = ambient.1 := by
      apply Fin.ext
      rfl
    have hiCarrier : i ∈ carrier := by
      apply mem_r324LeftHalfPullback.mpr
      rw [hiMap]
      exact ambient.2
    have hiLtMax : i < carrier.max' step.finalLeftHeadNonempty := by
      dsimp only [carrier]
      apply Fin.mk_lt_mk.mpr
      have hgapMap :=
        leftMomentIndex_max'_r324LeftHalfPullback step.head
      have hgapVal :
          ((r324LeftHalfPullback step.head.carrier).max'
              step.finalLeftHeadNonempty).val =
            step.head.leftGap.val := by
        simpa [leftMomentIndex] using congrArg Fin.val hgapMap
      change ambient.1.val <
        (carrier.max' step.finalLeftHeadNonempty).val
      change ambient.1.val < step.head.leftGap.val at hambientLtGap
      rw [hgapVal]
      exact hambientLtGap
    have hiSource : i ∈ source :=
      Finset.mem_erase.mpr ⟨ne_of_lt hiLtMax, hiCarrier⟩
    refine ⟨i, hiSource, ?_⟩
    apply Fin.ext
    change
      (step.blockOrderIso.symm
        ⟨leftMomentIndex i,
          mem_r324LeftHalfPullback.mp
            (Finset.mem_erase.mp hiSource).2⟩).val = j.val
    have hsub :
        (⟨leftMomentIndex i,
          mem_r324LeftHalfPullback.mp
            (Finset.mem_erase.mp hiSource).2⟩ :
            {x : Fin (2 * m) // x ∈ step.head.carrier}) = ambient := by
      apply Subtype.ext
      exact hiMap
    rw [hsub]
    change
      (step.blockOrderIso.symm
          (step.blockOrderIso
            (primitiveEdgeLeft step.order step.one_le_order j))).val =
        j.val
    rw [step.blockOrderIso.symm_apply_apply]
    rfl
  · intro i hi
    rw [terminal.left_finalHeadInternal_edgeDisplacement_eq
      step htail i (Finset.mem_erase.mp hi).2
        (Finset.mem_erase.mp hi).1 v]

/-- Right-half analogue of
`nestedLeftHalfInvSqProduct_finalHead_eq_primitiveEdges`. -/
theorem nestedRightHalfInvSqProduct_finalHead_eq_primitiveEdges
    {π : κp.singles ≃ κm.singles}
    (step : R324NestedCrossStepContext κp κm π)
    (htail : step.tail = [])
    (v : step.SurvivingCoordinate → T4) :
    terminal.nestedRightHalfInvSqProduct step
        step.head.carrier step.finalRightHeadNonempty v =
      ∏ j ∈ step.finalRightPrimitiveEdgeIndices,
        invSqKer
          ((step.splitSurvivingPiMeasurableEquiv v).1
              (primitiveEdgeLeft step.order step.one_le_order j) -
            (step.splitSurvivingPiMeasurableEquiv v).1
              (primitiveEdgeRight step.order step.one_le_order j)) := by
  let carrier := r324RightHalfPullback step.head.carrier
  let source := carrier.erase (carrier.max' step.finalRightHeadNonempty)
  have hslotInj : Set.InjOn
      (r324InternalVertexEdgeSlot : Fin m → Fin (m + 1)) source := by
    intro i hi k hk hik
    apply Fin.ext
    have hval := congrArg Fin.val hik
    simp only [r324InternalVertexEdgeSlot] at hval
    omega
  unfold nestedRightHalfInvSqProduct
    R324WithinHalfResidualPrefix.halfInvSqChainProduct
    R324WithinHalfResidualPrefix.halfChainEdgeSlots
  rw [Finset.prod_image hslotInj]
  apply Finset.prod_bij
      (fun i hi =>
        step.finalRightHeadPrimitiveEdgeIndex i
          (Finset.mem_erase.mp hi).2
          (Finset.mem_erase.mp hi).1)
  · intro i hi
    exact step.finalRightHeadPrimitiveEdgeIndex_mem i
      (Finset.mem_erase.mp hi).2
      (Finset.mem_erase.mp hi).1
  · intro i hi k hk hik
    apply rightMomentIndex_injective
    rw [step.final_rightMomentIndex_headSource i
        (Finset.mem_erase.mp hi).2
        (Finset.mem_erase.mp hi).1,
      step.final_rightMomentIndex_headSource k
        (Finset.mem_erase.mp hk).2
        (Finset.mem_erase.mp hk).1,
      hik]
  · intro j hj
    have hjRight : step.rightGapIndex ≤
        primitiveEdgeLeft step.order step.one_le_order j := by
      apply Fin.mk_le_mk.mpr
      exact (Finset.mem_filter.mp hj).2
    let ambient : {i : Fin (2 * m) // i ∈ step.head.carrier} :=
      step.blockOrderIso
        (primitiveEdgeLeft step.order step.one_le_order j)
    have hgapLeAmbient : step.head.rightGap ≤ ambient.1 := by
      have himage := step.blockOrderIso.monotone hjRight
      rw [step.blockOrderIso_rightGapIndex] at himage
      exact himage
    have hambientCut : m ≤ ambient.1.val := by
      have hgapCut := r324CrossGapRight_ge_cut
        step.head.carrier step.head.crossCut
      change step.head.rightGap.val ≤ ambient.1.val at hgapLeAmbient
      exact hgapCut.trans hgapLeAmbient
    let i : Fin m :=
      ⟨ambient.1.val - m, by
        have hambientLt := ambient.1.isLt
        omega⟩
    have hiMap : rightMomentIndex i = ambient.1 := by
      apply Fin.ext
      dsimp only [i, rightMomentIndex]
      omega
    have hiCarrier : i ∈ carrier := by
      apply mem_r324RightHalfPullback.mpr
      rw [hiMap]
      exact ambient.2
    have hjLast :
        primitiveEdgeLeft step.order step.one_le_order j <
          primitiveLast step.order step.one_le_order := by
      apply Fin.mk_lt_mk.mpr
      exact j.isLt
    have hambientLtLast := step.blockOrderIso.strictMono hjLast
    have hiNeMax : i ≠ carrier.max' step.finalRightHeadNonempty := by
      intro heq
      have hmap := congrArg rightMomentIndex heq
      rw [hiMap, step.final_rightMomentIndex_headMax_eq_last] at hmap
      exact (ne_of_lt hambientLtLast) (Subtype.ext hmap)
    have hiSource : i ∈ source :=
      Finset.mem_erase.mpr ⟨hiNeMax, hiCarrier⟩
    refine ⟨i, hiSource, ?_⟩
    apply Fin.ext
    change
      (step.blockOrderIso.symm
        ⟨rightMomentIndex i,
          mem_r324RightHalfPullback.mp
            (Finset.mem_erase.mp hiSource).2⟩).val = j.val
    have hsub :
        (⟨rightMomentIndex i,
          mem_r324RightHalfPullback.mp
            (Finset.mem_erase.mp hiSource).2⟩ :
            {x : Fin (2 * m) // x ∈ step.head.carrier}) = ambient := by
      apply Subtype.ext
      exact hiMap
    rw [hsub]
    change
      (step.blockOrderIso.symm
          (step.blockOrderIso
            (primitiveEdgeLeft step.order step.one_le_order j))).val =
        j.val
    rw [step.blockOrderIso.symm_apply_apply]
    rfl
  · intro i hi
    rw [terminal.right_finalHeadInternal_edgeDisplacement_eq
      step htail i (Finset.mem_erase.mp hi).2
        (Finset.mem_erase.mp hi).1 v]

/-- The restricted terminal left path is exactly the left internal part
of the normalized primitive chain. -/
theorem nestedLeftHalfInvSqProduct_head_eq_primitiveEdges
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (v : ctx.step.SurvivingCoordinate → T4) :
    terminal.nestedLeftHalfInvSqProduct ctx.step
        ctx.step.head.carrier ctx.leftHead_nonempty v =
      ∏ j ∈ ctx.leftPrimitiveEdgeIndices,
        invSqKer
          ((ctx.step.splitSurvivingPiMeasurableEquiv v).1
              (primitiveEdgeLeft ctx.step.order ctx.step.one_le_order j) -
            (ctx.step.splitSurvivingPiMeasurableEquiv v).1
              (primitiveEdgeRight
                ctx.step.order ctx.step.one_le_order j)) := by
  let carrier := r324LeftHalfPullback ctx.step.head.carrier
  let source := carrier.erase (carrier.max' ctx.leftHead_nonempty)
  have hslotInj : Set.InjOn
      (r324InternalVertexEdgeSlot : Fin m → Fin (m + 1)) source := by
    intro i hi k hk hik
    apply Fin.ext
    have hval := congrArg Fin.val hik
    simp only [r324InternalVertexEdgeSlot] at hval
    omega
  unfold nestedLeftHalfInvSqProduct
    R324WithinHalfResidualPrefix.halfInvSqChainProduct
    R324WithinHalfResidualPrefix.halfChainEdgeSlots
  rw [Finset.prod_image hslotInj]
  apply Finset.prod_bij
      (fun i hi =>
        ctx.leftHeadPrimitiveEdgeIndex i
          (Finset.mem_erase.mp hi).2
          (Finset.mem_erase.mp hi).1)
  · intro i hi
    exact ctx.leftHeadPrimitiveEdgeIndex_mem i
      (Finset.mem_erase.mp hi).2
      (Finset.mem_erase.mp hi).1
  · intro i hi k hk hik
    apply leftMomentIndex_injective
    rw [ctx.leftMomentIndex_leftHeadSource i
        (Finset.mem_erase.mp hi).2
        (Finset.mem_erase.mp hi).1,
      ctx.leftMomentIndex_leftHeadSource k
        (Finset.mem_erase.mp hk).2
        (Finset.mem_erase.mp hk).1,
      hik]
  · intro j hj
    have hjLt :
        primitiveEdgeLeft ctx.step.order ctx.step.one_le_order j <
          ctx.step.leftGapIndex := by
      apply Fin.mk_lt_mk.mpr
      exact (Finset.mem_filter.mp hj).2
    let ambient : {i : Fin (2 * m) // i ∈ ctx.step.head.carrier} :=
      ctx.step.blockOrderIso
        (primitiveEdgeLeft ctx.step.order ctx.step.one_le_order j)
    have hambientLtGap : ambient.1 < ctx.step.head.leftGap := by
      have himage := ctx.step.blockOrderIso.strictMono hjLt
      rw [ctx.step.blockOrderIso_leftGapIndex] at himage
      exact himage
    have hambientCut : ambient.1.val < m := by
      change ambient.1.val < ctx.step.head.leftGap.val at hambientLtGap
      exact hambientLtGap.trans
        (r324CrossGapLeft_lt_cut
          ctx.step.head.carrier ctx.step.head.crossCut)
    let i : Fin m := ⟨ambient.1.val, hambientCut⟩
    have hiMap : leftMomentIndex i = ambient.1 := by
      apply Fin.ext
      rfl
    have hiCarrier : i ∈ carrier := by
      apply mem_r324LeftHalfPullback.mpr
      rw [hiMap]
      exact ambient.2
    have hiLtMax : i < carrier.max' ctx.leftHead_nonempty := by
      dsimp only [carrier]
      apply Fin.mk_lt_mk.mpr
      have hgapMap :=
        leftMomentIndex_max'_r324LeftHalfPullback ctx.step.head
      have hgapVal :
          ((r324LeftHalfPullback ctx.step.head.carrier).max'
              ctx.leftHead_nonempty).val =
            ctx.step.head.leftGap.val := by
        simpa [leftMomentIndex] using congrArg Fin.val hgapMap
      change ambient.1.val < (carrier.max' ctx.leftHead_nonempty).val
      change ambient.1.val < ctx.step.head.leftGap.val at hambientLtGap
      rw [hgapVal]
      exact hambientLtGap
    have hiSource : i ∈ source := by
      exact Finset.mem_erase.mpr ⟨ne_of_lt hiLtMax, hiCarrier⟩
    refine ⟨i, hiSource, ?_⟩
    apply Fin.ext
    change
      (ctx.step.blockOrderIso.symm
        ⟨leftMomentIndex i,
          mem_r324LeftHalfPullback.mp
            (Finset.mem_erase.mp hiSource).2⟩).val = j.val
    have hsub :
        (⟨leftMomentIndex i,
          mem_r324LeftHalfPullback.mp
            (Finset.mem_erase.mp hiSource).2⟩ :
            {x : Fin (2 * m) // x ∈ ctx.step.head.carrier}) =
          ambient := by
      apply Subtype.ext
      exact hiMap
    rw [hsub]
    change
      (ctx.step.blockOrderIso.symm
          (ctx.step.blockOrderIso
            (primitiveEdgeLeft
              ctx.step.order ctx.step.one_le_order j))).val = j.val
    rw [ctx.step.blockOrderIso.symm_apply_apply]
    rfl
  · intro i hi
    rw [terminal.left_headInternal_edgeDisplacement_eq
      ctx i (Finset.mem_erase.mp hi).2
        (Finset.mem_erase.mp hi).1 v]

/-- The restricted terminal right path is exactly the right internal part
of the normalized primitive chain. -/
theorem nestedRightHalfInvSqProduct_head_eq_primitiveEdges
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (v : ctx.step.SurvivingCoordinate → T4) :
    terminal.nestedRightHalfInvSqProduct ctx.step
        ctx.step.head.carrier ctx.rightHead_nonempty v =
      ∏ j ∈ ctx.rightPrimitiveEdgeIndices,
        invSqKer
          ((ctx.step.splitSurvivingPiMeasurableEquiv v).1
              (primitiveEdgeLeft ctx.step.order ctx.step.one_le_order j) -
            (ctx.step.splitSurvivingPiMeasurableEquiv v).1
              (primitiveEdgeRight
                ctx.step.order ctx.step.one_le_order j)) := by
  let carrier := r324RightHalfPullback ctx.step.head.carrier
  let source := carrier.erase (carrier.max' ctx.rightHead_nonempty)
  have hslotInj : Set.InjOn
      (r324InternalVertexEdgeSlot : Fin m → Fin (m + 1)) source := by
    intro i hi k hk hik
    apply Fin.ext
    have hval := congrArg Fin.val hik
    simp only [r324InternalVertexEdgeSlot] at hval
    omega
  unfold nestedRightHalfInvSqProduct
    R324WithinHalfResidualPrefix.halfInvSqChainProduct
    R324WithinHalfResidualPrefix.halfChainEdgeSlots
  rw [Finset.prod_image hslotInj]
  apply Finset.prod_bij
      (fun i hi =>
        ctx.rightHeadPrimitiveEdgeIndex i
          (Finset.mem_erase.mp hi).2
          (Finset.mem_erase.mp hi).1)
  · intro i hi
    exact ctx.rightHeadPrimitiveEdgeIndex_mem i
      (Finset.mem_erase.mp hi).2
      (Finset.mem_erase.mp hi).1
  · intro i hi k hk hik
    apply rightMomentIndex_injective
    rw [ctx.rightMomentIndex_rightHeadSource i
        (Finset.mem_erase.mp hi).2
        (Finset.mem_erase.mp hi).1,
      ctx.rightMomentIndex_rightHeadSource k
        (Finset.mem_erase.mp hk).2
        (Finset.mem_erase.mp hk).1,
      hik]
  · intro j hj
    have hjRight :
        ctx.step.rightGapIndex ≤
          primitiveEdgeLeft ctx.step.order ctx.step.one_le_order j := by
      apply Fin.mk_le_mk.mpr
      exact (Finset.mem_filter.mp hj).2
    let ambient : {i : Fin (2 * m) // i ∈ ctx.step.head.carrier} :=
      ctx.step.blockOrderIso
        (primitiveEdgeLeft ctx.step.order ctx.step.one_le_order j)
    have hgapLeAmbient : ctx.step.head.rightGap ≤ ambient.1 := by
      have himage := ctx.step.blockOrderIso.monotone hjRight
      rw [ctx.step.blockOrderIso_rightGapIndex] at himage
      exact himage
    have hambientCut : m ≤ ambient.1.val := by
      have hgapCut := r324CrossGapRight_ge_cut
        ctx.step.head.carrier ctx.step.head.crossCut
      change ctx.step.head.rightGap.val ≤ ambient.1.val at hgapLeAmbient
      exact hgapCut.trans hgapLeAmbient
    let i : Fin m :=
      ⟨ambient.1.val - m, by
        have hambientLt := ambient.1.isLt
        omega⟩
    have hiMap : rightMomentIndex i = ambient.1 := by
      apply Fin.ext
      dsimp only [i, rightMomentIndex]
      omega
    have hiCarrier : i ∈ carrier := by
      apply mem_r324RightHalfPullback.mpr
      rw [hiMap]
      exact ambient.2
    have hjLast :
        primitiveEdgeLeft ctx.step.order ctx.step.one_le_order j <
          primitiveLast ctx.step.order ctx.step.one_le_order := by
      apply Fin.mk_lt_mk.mpr
      exact j.isLt
    have hambientLtLast := ctx.step.blockOrderIso.strictMono hjLast
    have hiNeMax : i ≠ carrier.max' ctx.rightHead_nonempty := by
      intro heq
      have hmap := congrArg rightMomentIndex heq
      rw [hiMap, ctx.rightMomentIndex_rightHead_max'] at hmap
      exact (ne_of_lt hambientLtLast) (Subtype.ext hmap)
    have hiSource : i ∈ source := by
      exact Finset.mem_erase.mpr ⟨hiNeMax, hiCarrier⟩
    refine ⟨i, hiSource, ?_⟩
    apply Fin.ext
    change
      (ctx.step.blockOrderIso.symm
        ⟨rightMomentIndex i,
          mem_r324RightHalfPullback.mp
            (Finset.mem_erase.mp hiSource).2⟩).val = j.val
    have hsub :
        (⟨rightMomentIndex i,
          mem_r324RightHalfPullback.mp
            (Finset.mem_erase.mp hiSource).2⟩ :
            {x : Fin (2 * m) // x ∈ ctx.step.head.carrier}) =
          ambient := by
      apply Subtype.ext
      exact hiMap
    rw [hsub]
    change
      (ctx.step.blockOrderIso.symm
          (ctx.step.blockOrderIso
            (primitiveEdgeLeft
              ctx.step.order ctx.step.one_le_order j))).val = j.val
    rw [ctx.step.blockOrderIso.symm_apply_apply]
    rfl
  · intro i hi
    rw [terminal.right_headInternal_edgeDisplacement_eq
      ctx i (Finset.mem_erase.mp hi).2
        (Finset.mem_erase.mp hi).1 v]

/-- Paper Step 3's exact current-shell identity.  The two physical half
paths contain every normalized primitive edge except the cut edge; the
moving `torusDistSq` numerator cancels precisely that missing edge almost
everywhere.  The complete primitive-pairing covariance sum remains
grouped throughout. -/
theorem ae_headHalfPaths_mul_completeCrossGap_one_eq_completeNormalized
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    ∀ᵐ v : ctx.step.SurvivingCoordinate → T4
        ∂(Measure.pi fun _ => paperMeasure),
      lamEps lam ε ^ (2 * ctx.step.order) *
          ((terminal.nestedLeftHalfInvSqProduct ctx.step
                ctx.step.head.carrier ctx.leftHead_nonempty v *
              terminal.nestedRightHalfInvSqProduct ctx.step
                ctx.step.head.carrier ctx.rightHead_nonempty v) *
            (∑ κ ∈ primitiveFullPairings ctx.step.order,
              primitiveCovarianceProduct ρ ε ctx.step.order κ
                (ctx.step.splitSurvivingPiMeasurableEquiv v).1)) =
        ctx.step.completeNormalizedHeadDensity ρ lam ε
          (ctx.step.splitSurvivingPiMeasurableEquiv v).1 := by
  filter_upwards
      [ctx.step.ae_centralGapCancellation_reconstruct_eq_one]
    with v hcancel
  let t := (ctx.step.splitSurvivingPiMeasurableEquiv v).1
  have hleftCoordinate :
      ctx.step.reconstruct v ctx.step.head.leftGap =
        t ctx.step.leftGapIndex := by
    dsimp only [t]
    rw [ctx.step.splitSurvivingPiMeasurableEquiv_apply_fst]
    have hval :
        (ctx.step.headSurvivingCoordinate
          ctx.step.leftGapIndex).1 =
            ctx.step.head.leftGap :=
      congrArg Subtype.val ctx.step.blockOrderIso_leftGapIndex
    rw [← hval, ctx.step.reconstruct_surviving]
  have hrightCoordinate :
      ctx.step.reconstruct v ctx.step.head.rightGap =
        t ctx.step.rightGapIndex := by
    dsimp only [t]
    rw [ctx.step.splitSurvivingPiMeasurableEquiv_apply_fst]
    have hval :
        (ctx.step.headSurvivingCoordinate
          ctx.step.rightGapIndex).1 =
            ctx.step.head.rightGap :=
      congrArg Subtype.val ctx.step.blockOrderIso_rightGapIndex
    rw [← hval, ctx.step.reconstruct_surviving]
  have hgap :
      torusDistSq
          (t ctx.step.leftGapIndex - t ctx.step.rightGapIndex) *
        invSqKer
          (t ctx.step.leftGapIndex - t ctx.step.rightGapIndex) =
        1 := by
    unfold R324NestedCrossBlock.centralGapNumerator at hcancel
    rw [hleftCoordinate, hrightCoordinate] at hcancel
    exact hcancel
  rw [terminal.nestedLeftHalfInvSqProduct_head_eq_primitiveEdges
      ctx v,
    terminal.nestedRightHalfInvSqProduct_head_eq_primitiveEdges
      ctx v]
  unfold R324NestedCrossStepContext.completeNormalizedHeadDensity
  rw [ctx.step.completeCrossGapPrimitiveIntegrand_eq,
    ctx.primitiveChainProduct_normalized_eq_left_central_right]
  change
    lamEps lam ε ^ (2 * ctx.step.order) *
          (((∏ j ∈ ctx.leftPrimitiveEdgeIndices,
              invSqKer
                (t (primitiveEdgeLeft
                    ctx.step.order ctx.step.one_le_order j) -
                  t (primitiveEdgeRight
                    ctx.step.order ctx.step.one_le_order j))) *
            (∏ j ∈ ctx.rightPrimitiveEdgeIndices,
              invSqKer
                (t (primitiveEdgeLeft
                    ctx.step.order ctx.step.one_le_order j) -
                  t (primitiveEdgeRight
                    ctx.step.order ctx.step.one_le_order j)))) *
          (∑ κ ∈ primitiveFullPairings ctx.step.order,
            primitiveCovarianceProduct ρ ε ctx.step.order κ t)) = _
  calc
    _ = lamEps lam ε ^ (2 * ctx.step.order) *
        ((torusDistSq
              (t ctx.step.leftGapIndex - t ctx.step.rightGapIndex) *
            invSqKer
              (t ctx.step.leftGapIndex - t ctx.step.rightGapIndex)) *
          (((∏ j ∈ ctx.leftPrimitiveEdgeIndices,
                invSqKer
                  (t (primitiveEdgeLeft
                      ctx.step.order ctx.step.one_le_order j) -
                    t (primitiveEdgeRight
                      ctx.step.order ctx.step.one_le_order j))) *
              (∏ j ∈ ctx.rightPrimitiveEdgeIndices,
                invSqKer
                  (t (primitiveEdgeLeft
                      ctx.step.order ctx.step.one_le_order j) -
                    t (primitiveEdgeRight
                      ctx.step.order ctx.step.one_le_order j)))) *
            (∑ κ ∈ primitiveFullPairings ctx.step.order,
              primitiveCovarianceProduct ρ ε ctx.step.order κ t))) := by
          rw [hgap]
          ring
    _ = _ := by ring

/-- The last application of paper (4.4): on a genuine final shell the two
terminal half paths contain every normalized primitive edge except the cut
edge, which is cancelled a.e. by the moving gap numerator. -/
theorem ae_finalHeadHalfPaths_mul_completeCrossGap_one_eq_completeNormalized
    {π : κp.singles ≃ κm.singles}
    (step : R324NestedCrossStepContext κp κm π)
    (htail : step.tail = []) :
    ∀ᵐ v : step.SurvivingCoordinate → T4
        ∂(Measure.pi fun _ => paperMeasure),
      lamEps lam ε ^ (2 * step.order) *
          ((terminal.nestedLeftHalfInvSqProduct step
                step.head.carrier step.finalLeftHeadNonempty v *
              terminal.nestedRightHalfInvSqProduct step
                step.head.carrier step.finalRightHeadNonempty v) *
            (∑ κ ∈ primitiveFullPairings step.order,
              primitiveCovarianceProduct ρ ε step.order κ
                (step.splitSurvivingPiMeasurableEquiv v).1)) =
        step.completeNormalizedHeadDensity ρ lam ε
          (step.splitSurvivingPiMeasurableEquiv v).1 := by
  filter_upwards [step.ae_centralGapCancellation_reconstruct_eq_one]
    with v hcancel
  let t := (step.splitSurvivingPiMeasurableEquiv v).1
  have hleftCoordinate :
      step.reconstruct v step.head.leftGap =
        t step.leftGapIndex := by
    dsimp only [t]
    rw [step.splitSurvivingPiMeasurableEquiv_apply_fst]
    have hval :
        (step.headSurvivingCoordinate step.leftGapIndex).1 =
          step.head.leftGap :=
      congrArg Subtype.val step.blockOrderIso_leftGapIndex
    rw [← hval, step.reconstruct_surviving]
  have hrightCoordinate :
      step.reconstruct v step.head.rightGap =
        t step.rightGapIndex := by
    dsimp only [t]
    rw [step.splitSurvivingPiMeasurableEquiv_apply_fst]
    have hval :
        (step.headSurvivingCoordinate step.rightGapIndex).1 =
          step.head.rightGap :=
      congrArg Subtype.val step.blockOrderIso_rightGapIndex
    rw [← hval, step.reconstruct_surviving]
  have hgap :
      torusDistSq (t step.leftGapIndex - t step.rightGapIndex) *
        invSqKer (t step.leftGapIndex - t step.rightGapIndex) = 1 := by
    unfold R324NestedCrossBlock.centralGapNumerator at hcancel
    rw [hleftCoordinate, hrightCoordinate] at hcancel
    exact hcancel
  rw [terminal.nestedLeftHalfInvSqProduct_finalHead_eq_primitiveEdges
      step htail v,
    terminal.nestedRightHalfInvSqProduct_finalHead_eq_primitiveEdges
      step htail v]
  unfold R324NestedCrossStepContext.completeNormalizedHeadDensity
  rw [step.completeCrossGapPrimitiveIntegrand_eq,
    step.primitiveChainProduct_normalized_eq_finalParts]
  change
    lamEps lam ε ^ (2 * step.order) *
          (((∏ j ∈ step.finalLeftPrimitiveEdgeIndices,
              invSqKer
                (t (primitiveEdgeLeft step.order step.one_le_order j) -
                  t (primitiveEdgeRight step.order step.one_le_order j))) *
            (∏ j ∈ step.finalRightPrimitiveEdgeIndices,
              invSqKer
                (t (primitiveEdgeLeft step.order step.one_le_order j) -
                  t (primitiveEdgeRight step.order step.one_le_order j)))) *
          (∑ κ ∈ primitiveFullPairings step.order,
            primitiveCovarianceProduct ρ ε step.order κ t)) = _
  calc
    _ = lamEps lam ε ^ (2 * step.order) *
        ((torusDistSq
              (t step.leftGapIndex - t step.rightGapIndex) *
            invSqKer
              (t step.leftGapIndex - t step.rightGapIndex)) *
          (((∏ j ∈ step.finalLeftPrimitiveEdgeIndices,
                invSqKer
                  (t (primitiveEdgeLeft step.order step.one_le_order j) -
                    t (primitiveEdgeRight step.order step.one_le_order j))) *
              (∏ j ∈ step.finalRightPrimitiveEdgeIndices,
                invSqKer
                  (t (primitiveEdgeLeft step.order step.one_le_order j) -
                    t (primitiveEdgeRight step.order step.one_le_order j)))) *
            (∑ κ ∈ primitiveFullPairings step.order,
              primitiveCovarianceProduct ρ ε step.order κ t))) := by
          rw [hgap]
          ring
    _ = _ := by ring

private theorem left_post_mem_terminal
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324LeftHalfPullback ctx.step.next.activeCarrier) :
    i ∈ terminal.left.state.active := by
  have hiDoubled := mem_r324LeftHalfPullback.mp hi
  unfold R324NestedCrossResidualPrefix.activeCarrier at hiDoubled
  obtain ⟨carrier, hcarrier, hiCarrier⟩ :=
    (mem_finsetUnionList_iff _).mp hiDoubled
  obtain ⟨block, hblock, rfl⟩ := List.mem_map.mp hcarrier
  exact terminal.left_mem_terminal_of_block_local block i hiCarrier

private theorem right_post_mem_terminal
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m)
    (hi : i ∈ r324RightHalfPullback ctx.step.next.activeCarrier) :
    i ∈ terminal.right.state.active := by
  have hiDoubled := mem_r324RightHalfPullback.mp hi
  unfold R324NestedCrossResidualPrefix.activeCarrier at hiDoubled
  obtain ⟨carrier, hcarrier, hiCarrier⟩ :=
    (mem_finsetUnionList_iff _).mp hiDoubled
  obtain ⟨block, hblock, rfl⟩ := List.mem_map.mp hcarrier
  exact terminal.right_mem_terminal_of_block_local block i hiCarrier

/-- On the left half the untouched outer suffix is an initial segment of
the full terminal active order. -/
private theorem left_terminal_mem_post_of_le_max
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m) (hi : i ∈ terminal.left.state.active)
    (hle : i ≤
      (r324LeftHalfPullback ctx.step.next.activeCarrier).max'
        ctx.leftPost_nonempty) :
    i ∈ r324LeftHalfPullback ctx.step.next.activeCarrier := by
  obtain ⟨block, hblockSchedule, hiCarrier⟩ :=
    terminal.left_terminal_mem_schedule_local i hi
  have hfull := r324NestedCrossSchedule_pairwise_halfOutward κp κm π
  rw [ctx.step.residual.schedule_eq, ctx.step.remaining_eq,
    List.pairwise_append] at hfull
  rw [ctx.step.residual.schedule_eq, ctx.step.remaining_eq] at hblockSchedule
  rcases List.mem_append.mp hblockSchedule with hprocessed | hremaining
  · have hnextMem : ctx.nextHead ∈ ctx.step.head :: ctx.step.tail := by
      rw [ctx.tail_eq]
      simp
    have hrel := hfull.2.2 block hprocessed ctx.nextHead hnextMem
    have hmaxNext :
        (r324LeftHalfPullback ctx.step.next.activeCarrier).max'
            ctx.leftPost_nonempty ∈
          r324LeftHalfPullback ctx.nextHead.carrier := by
      apply mem_r324LeftHalfPullback.mpr
      rw [ctx.leftMomentIndex_leftPost_max']
      exact ctx.nextHead.leftGap_mem
    have hlt := hrel.1 _ hmaxNext i
      (mem_r324LeftHalfPullback.mpr hiCarrier)
    exact (not_lt_of_ge hle hlt).elim
  · rcases List.mem_cons.mp hremaining with rfl | htail
    · have hlt := ctx.leftPost_before_head
        ((r324LeftHalfPullback ctx.step.next.activeCarrier).max'
          ctx.leftPost_nonempty)
        (Finset.max'_mem _ ctx.leftPost_nonempty) i
        (mem_r324LeftHalfPullback.mpr hiCarrier)
      exact (not_lt_of_ge hle hlt).elim
    · apply mem_r324LeftHalfPullback.mpr
      unfold R324NestedCrossResidualPrefix.activeCarrier
      exact (mem_finsetUnionList_iff _).mpr
        ⟨block.carrier,
          List.mem_map.mpr ⟨block, htail, rfl⟩,
          hiCarrier⟩

/-- On the right half the untouched outer suffix is a final segment of
the full terminal active order. -/
private theorem right_terminal_mem_post_of_min_le
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (i : Fin m) (hi : i ∈ terminal.right.state.active)
    (hle :
      (r324RightHalfPullback ctx.step.next.activeCarrier).min'
          ctx.rightPost_nonempty ≤ i) :
    i ∈ r324RightHalfPullback ctx.step.next.activeCarrier := by
  obtain ⟨block, hblockSchedule, hiCarrier⟩ :=
    terminal.right_terminal_mem_schedule_local i hi
  have hfull := r324NestedCrossSchedule_pairwise_halfOutward κp κm π
  rw [ctx.step.residual.schedule_eq, ctx.step.remaining_eq,
    List.pairwise_append] at hfull
  rw [ctx.step.residual.schedule_eq, ctx.step.remaining_eq] at hblockSchedule
  rcases List.mem_append.mp hblockSchedule with hprocessed | hremaining
  · have hnextMem : ctx.nextHead ∈ ctx.step.head :: ctx.step.tail := by
      rw [ctx.tail_eq]
      simp
    have hrel := hfull.2.2 block hprocessed ctx.nextHead hnextMem
    have hminNext :
        (r324RightHalfPullback ctx.step.next.activeCarrier).min'
            ctx.rightPost_nonempty ∈
          r324RightHalfPullback ctx.nextHead.carrier := by
      apply mem_r324RightHalfPullback.mpr
      rw [ctx.rightMomentIndex_rightPost_min']
      exact ctx.nextHead.rightGap_mem
    have hlt := hrel.2 i
      (mem_r324RightHalfPullback.mpr hiCarrier) _ hminNext
    exact (not_lt_of_ge hle hlt).elim
  · rcases List.mem_cons.mp hremaining with rfl | htail
    · have hlt := ctx.rightHead_before_post i
        (mem_r324RightHalfPullback.mpr hiCarrier)
        ((r324RightHalfPullback ctx.step.next.activeCarrier).min'
          ctx.rightPost_nonempty)
        (Finset.min'_mem _ ctx.rightPost_nonempty)
      exact (not_lt_of_ge hle hlt).elim
    · apply mem_r324RightHalfPullback.mpr
      unfold R324NestedCrossResidualPrefix.activeCarrier
      exact (mem_finsetUnionList_iff _).mpr
        ⟨block.carrier,
          List.mem_map.mpr ⟨block, htail, rfl⟩,
          hiCarrier⟩

/-- The left post-path is unchanged when it is re-read as the current path
of the next literal shell. -/
theorem nestedLeftHalfInvSqProduct_post_eq_next
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (v : ctx.step.SurvivingCoordinate → T4) :
    terminal.nestedLeftHalfInvSqProduct ctx.step
        ctx.step.next.activeCarrier ctx.leftPost_nonempty v =
      terminal.nestedLeftHalfInvSqProduct ctx.nextContext
        ctx.step.next.activeCarrier ctx.leftPost_nonempty
        (fun i : ctx.nextContext.SurvivingCoordinate =>
          (ctx.step.splitSurvivingPiMeasurableEquiv v).2 ⟨i.1, i.2⟩) := by
  have hpostEq :
      (fun i : ctx.nextContext.SurvivingCoordinate =>
        (ctx.step.splitSurvivingPiMeasurableEquiv v).2 ⟨i.1, i.2⟩) =
        (ctx.step.splitSurvivingPiMeasurableEquiv v).2 := by
    funext i
    congr 1
  unfold nestedLeftHalfInvSqProduct
    R324WithinHalfResidualPrefix.halfInvSqChainProduct
  apply Finset.prod_congr rfl
  intro edge hedge
  obtain ⟨i, hiErase, rfl⟩ := Finset.mem_image.mp hedge
  have hiCarrier := (Finset.mem_erase.mp hiErase).2
  have hiNeMax := (Finset.mem_erase.mp hiErase).1
  let last :=
    (r324LeftHalfPullback ctx.step.next.activeCarrier).max'
      ctx.leftPost_nonempty
  have hiLtLast : i < last := by
    exact lt_of_le_of_ne
      (Finset.le_max' _ i hiCarrier) hiNeMax
  have hiTerminal := terminal.left_post_mem_terminal ctx i hiCarrier
  have hlastCarrier : last ∈
      r324LeftHalfPullback ctx.step.next.activeCarrier :=
    Finset.max'_mem _ ctx.leftPost_nonempty
  have hlastTerminal :=
    terminal.left_post_mem_terminal ctx last hlastCarrier
  have hlastCandidate : varIdx last ∈
      terminal.left.edgeSuccessorCandidates
        (r324InternalVertexEdgeSlot i) := by
    unfold R324WithinHalfResidualPrefix.edgeSuccessorCandidates
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨last, Finset.mem_filter.mpr ⟨hlastTerminal, ?_⟩, rfl⟩
    simp only [r324InternalVertexEdgeSlot, varIdx_val]
    omega
  have hsuccLe := Finset.min'_le
    (terminal.left.edgeSuccessorCandidates
      (r324InternalVertexEdgeSlot i))
    (varIdx last) hlastCandidate
  change terminal.left.edgeSuccessor
      (r324InternalVertexEdgeSlot i) ≤ varIdx last at hsuccLe
  have hsuccMem := terminal.left.edgeSuccessor_mem_candidates
    (r324InternalVertexEdgeSlot i)
  unfold R324WithinHalfResidualPrefix.edgeSuccessorCandidates at hsuccMem
  have hnotLast : terminal.left.edgeSuccessor
      (r324InternalVertexEdgeSlot i) ∉
        ({Fin.last (m + 1)} : Finset (Fin (m + 2))) := by
    intro hmem
    have heq := Finset.mem_singleton.mp hmem
    rw [heq] at hsuccLe
    change m + 1 ≤ last.val + 1 at hsuccLe
    omega
  have hinter := (Finset.mem_union.mp hsuccMem).resolve_left hnotLast
  obtain ⟨k, hkFilter, hsuccEq⟩ := Finset.mem_image.mp hinter
  have hkTerminal := (Finset.mem_filter.mp hkFilter).1
  have hsourceLt := (Finset.mem_filter.mp hkFilter).2
  have hkLeLast : k ≤ last := by
    have hvarLe : varIdx k ≤ varIdx last := hsuccEq.trans_le hsuccLe
    dsimp only [last] at hvarLe ⊢
    change k.val + 1 ≤
      ((r324LeftHalfPullback ctx.step.next.activeCarrier).max'
        ctx.leftPost_nonempty).val + 1 at hvarLe
    change k.val ≤
      ((r324LeftHalfPullback ctx.step.next.activeCarrier).max'
        ctx.leftPost_nonempty).val
    omega
  have hkCarrier := terminal.left_terminal_mem_post_of_le_max
    ctx k hkTerminal hkLeLast
  have hiAmbient := mem_r324LeftHalfPullback.mp hiCarrier
  have hkAmbient := mem_r324LeftHalfPullback.mp hkCarrier
  let iTerminal : terminal.left.SurvivingCoordinate := ⟨i, hiTerminal⟩
  let kTerminal : terminal.left.SurvivingCoordinate := ⟨k, hkTerminal⟩
  have hsourceCast :
      (r324InternalVertexEdgeSlot i).castSucc = varIdx i := by
    apply Fin.ext
    rfl
  unfold R324WithinHalfResidualPrefix.edgeDisplacement
  rw [hsourceCast, ← hsuccEq]
  simp only [assemble_varIdx]
  rw [terminal.left.reconstruct_surviving
      (terminal.leftTupleOfNestedStep ctx.step v) iTerminal,
    terminal.left.reconstruct_surviving
      (terminal.leftTupleOfNestedStep ctx.step v) kTerminal,
    terminal.left.reconstruct_surviving
      (terminal.leftTupleOfNestedStep ctx.nextContext
        (fun i : ctx.nextContext.SurvivingCoordinate =>
          (ctx.step.splitSurvivingPiMeasurableEquiv v).2 ⟨i.1, i.2⟩))
        iTerminal,
    terminal.left.reconstruct_surviving
      (terminal.leftTupleOfNestedStep ctx.nextContext
        (fun i : ctx.nextContext.SurvivingCoordinate =>
          (ctx.step.splitSurvivingPiMeasurableEquiv v).2 ⟨i.1, i.2⟩))
        kTerminal]
  unfold leftTupleOfNestedStep
  dsimp only [iTerminal, kTerminal]
  rw [ctx.reconstruct_eq_nextContext_reconstruct v ⟨leftMomentIndex i, hiAmbient⟩,
    ctx.reconstruct_eq_nextContext_reconstruct v ⟨leftMomentIndex k, hkAmbient⟩]
  rw [hpostEq]

/-- Right-half analogue of
`nestedLeftHalfInvSqProduct_post_eq_next`. -/
theorem nestedRightHalfInvSqProduct_post_eq_next
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (v : ctx.step.SurvivingCoordinate → T4) :
    terminal.nestedRightHalfInvSqProduct ctx.step
        ctx.step.next.activeCarrier ctx.rightPost_nonempty v =
      terminal.nestedRightHalfInvSqProduct ctx.nextContext
        ctx.step.next.activeCarrier ctx.rightPost_nonempty
        (fun i : ctx.nextContext.SurvivingCoordinate =>
          (ctx.step.splitSurvivingPiMeasurableEquiv v).2 ⟨i.1, i.2⟩) := by
  have hpostEq :
      (fun i : ctx.nextContext.SurvivingCoordinate =>
        (ctx.step.splitSurvivingPiMeasurableEquiv v).2 ⟨i.1, i.2⟩) =
        (ctx.step.splitSurvivingPiMeasurableEquiv v).2 := by
    funext i
    congr 1
  unfold nestedRightHalfInvSqProduct
    R324WithinHalfResidualPrefix.halfInvSqChainProduct
  apply Finset.prod_congr rfl
  intro edge hedge
  obtain ⟨i, hiErase, rfl⟩ := Finset.mem_image.mp hedge
  have hiCarrier := (Finset.mem_erase.mp hiErase).2
  have hiNeMax := (Finset.mem_erase.mp hiErase).1
  let last :=
    (r324RightHalfPullback ctx.step.next.activeCarrier).max'
      ctx.rightPost_nonempty
  have hiLtLast : i < last := by
    exact lt_of_le_of_ne
      (Finset.le_max' _ i hiCarrier) hiNeMax
  have hiTerminal := terminal.right_post_mem_terminal ctx i hiCarrier
  have hlastCarrier : last ∈
      r324RightHalfPullback ctx.step.next.activeCarrier :=
    Finset.max'_mem _ ctx.rightPost_nonempty
  have hlastTerminal :=
    terminal.right_post_mem_terminal ctx last hlastCarrier
  have hlastCandidate : varIdx last ∈
      terminal.right.edgeSuccessorCandidates
        (r324InternalVertexEdgeSlot i) := by
    unfold R324WithinHalfResidualPrefix.edgeSuccessorCandidates
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨last, Finset.mem_filter.mpr ⟨hlastTerminal, ?_⟩, rfl⟩
    simp only [r324InternalVertexEdgeSlot, varIdx_val]
    omega
  have hsuccLe := Finset.min'_le
    (terminal.right.edgeSuccessorCandidates
      (r324InternalVertexEdgeSlot i))
    (varIdx last) hlastCandidate
  change terminal.right.edgeSuccessor
      (r324InternalVertexEdgeSlot i) ≤ varIdx last at hsuccLe
  have hsuccMem := terminal.right.edgeSuccessor_mem_candidates
    (r324InternalVertexEdgeSlot i)
  unfold R324WithinHalfResidualPrefix.edgeSuccessorCandidates at hsuccMem
  have hnotLast : terminal.right.edgeSuccessor
      (r324InternalVertexEdgeSlot i) ∉
        ({Fin.last (m + 1)} : Finset (Fin (m + 2))) := by
    intro hmem
    have heq := Finset.mem_singleton.mp hmem
    rw [heq] at hsuccLe
    change m + 1 ≤ last.val + 1 at hsuccLe
    omega
  have hinter := (Finset.mem_union.mp hsuccMem).resolve_left hnotLast
  obtain ⟨k, hkFilter, hsuccEq⟩ := Finset.mem_image.mp hinter
  have hkTerminal := (Finset.mem_filter.mp hkFilter).1
  have hsourceLt := (Finset.mem_filter.mp hkFilter).2
  have hiLtK : i < k := by
    change i.val + 1 < k.val + 1 at hsourceLt
    exact Fin.mk_lt_mk.mpr (by omega)
  have hminLeI :
      (r324RightHalfPullback ctx.step.next.activeCarrier).min'
          ctx.rightPost_nonempty ≤ i :=
    Finset.min'_le _ i hiCarrier
  have hkCarrier := terminal.right_terminal_mem_post_of_min_le
    ctx k hkTerminal (hminLeI.trans hiLtK.le)
  have hiAmbient := mem_r324RightHalfPullback.mp hiCarrier
  have hkAmbient := mem_r324RightHalfPullback.mp hkCarrier
  let iTerminal : terminal.right.SurvivingCoordinate := ⟨i, hiTerminal⟩
  let kTerminal : terminal.right.SurvivingCoordinate := ⟨k, hkTerminal⟩
  have hsourceCast :
      (r324InternalVertexEdgeSlot i).castSucc = varIdx i := by
    apply Fin.ext
    rfl
  unfold R324WithinHalfResidualPrefix.edgeDisplacement
  rw [hsourceCast, ← hsuccEq]
  simp only [assemble_varIdx]
  rw [terminal.right.reconstruct_surviving
      (terminal.rightTupleOfNestedStep ctx.step v) iTerminal,
    terminal.right.reconstruct_surviving
      (terminal.rightTupleOfNestedStep ctx.step v) kTerminal,
    terminal.right.reconstruct_surviving
      (terminal.rightTupleOfNestedStep ctx.nextContext
        (fun i : ctx.nextContext.SurvivingCoordinate =>
          (ctx.step.splitSurvivingPiMeasurableEquiv v).2 ⟨i.1, i.2⟩))
        iTerminal,
    terminal.right.reconstruct_surviving
      (terminal.rightTupleOfNestedStep ctx.nextContext
        (fun i : ctx.nextContext.SurvivingCoordinate =>
          (ctx.step.splitSurvivingPiMeasurableEquiv v).2 ⟨i.1, i.2⟩))
        kTerminal]
  unfold rightTupleOfNestedStep
  dsimp only [iTerminal, kTerminal]
  rw [ctx.reconstruct_eq_nextContext_reconstruct v ⟨rightMomentIndex i, hiAmbient⟩,
    ctx.reconstruct_eq_nextContext_reconstruct v ⟨rightMomentIndex k, hkAmbient⟩]
  rw [hpostEq]

/-- The literal nonnegative Steps 2--3 density on one remaining nested
suffix: both terminal half paths and every residual block covariance are
kept as products/sums until the shell is removed. -/
def completeNestedRunDensity
    {π : κp.singles ≃ κm.singles}
    (step : R324NestedCrossStepContext κp κm π)
    (hleft : (r324LeftHalfPullback step.residual.activeCarrier).Nonempty)
    (hright : (r324RightHalfPullback step.residual.activeCarrier).Nonempty)
    (v : step.SurvivingCoordinate → T4) : ℝ :=
  lamEps lam ε ^ (2 * step.residual.remainingOrder) *
    ((terminal.nestedLeftHalfInvSqProduct step
          step.residual.activeCarrier hleft v *
        terminal.nestedRightHalfInvSqProduct step
          step.residual.activeCarrier hright v) *
      r324NestedResidualPrimitiveSumProduct
        ρ ε κp κm π step.residual (step.reconstruct v))

private theorem finalHeadBlockSum_reconstruct_eq_completePairingSum
    {π : κp.singles ≃ κm.singles}
    (step : R324NestedCrossStepContext κp κm π)
    (v : step.SurvivingCoordinate → T4) :
    r324PrimitivePartitionBlockSum
        ρ ε κp κm π step.head.carrier
        (step.reconstruct v) =
      ∑ κ ∈ primitiveFullPairings step.order,
        primitiveCovarianceProduct ρ ε step.order κ
          (step.splitSurvivingPiMeasurableEquiv v).1 := by
  let t := (step.splitSurvivingPiMeasurableEquiv v).1
  let post := (step.splitSurvivingPiMeasurableEquiv v).2
  have h := step.r324PrimitivePartitionBlockSum_head_reconstruct_split
    ρ ε t post
  have hv : step.splitSurvivingPiMeasurableEquiv.symm (t, post) = v :=
    step.splitSurvivingPiMeasurableEquiv.symm_apply_apply v
  rw [hv, step.sum_r324PrimitiveCoordinate_covariance_eq] at h
  exact h

private theorem headBlockSum_reconstruct_eq_completePairingSum
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (v : ctx.step.SurvivingCoordinate → T4) :
    r324PrimitivePartitionBlockSum
        ρ ε κp κm π ctx.step.head.carrier
        (ctx.step.reconstruct v) =
      ∑ κ ∈ primitiveFullPairings ctx.step.order,
        primitiveCovarianceProduct ρ ε ctx.step.order κ
          (ctx.step.splitSurvivingPiMeasurableEquiv v).1 := by
  let t := (ctx.step.splitSurvivingPiMeasurableEquiv v).1
  let post := (ctx.step.splitSurvivingPiMeasurableEquiv v).2
  have h := ctx.step.r324PrimitivePartitionBlockSum_head_reconstruct_split
    ρ ε t post
  have hv :
      ctx.step.splitSurvivingPiMeasurableEquiv.symm (t, post) = v := by
    exact ctx.step.splitSurvivingPiMeasurableEquiv.symm_apply_apply v
  rw [hv, ctx.step.sum_r324PrimitiveCoordinate_covariance_eq] at h
  exact h

/-- Literal one-shell recursion for paper Step 3.  The equality is a.e.
only because the compensating cut edge is cancelled off the diagonal; no
absolute value and no pairing-wise triangle inequality is used. -/
theorem ae_completeNestedRunDensity_eq_head_connector_next
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    terminal.completeNestedRunDensity ctx.step
        ctx.leftCurrent_nonempty ctx.rightCurrent_nonempty =ᵐ[
      Measure.pi fun _ : ctx.step.SurvivingCoordinate => paperMeasure]
      fun v =>
        ctx.step.completeNormalizedHeadDensity ρ lam ε
            (ctx.step.splitSurvivingPiMeasurableEquiv v).1 *
          ctx.connector
            (ctx.step.splitSurvivingPiMeasurableEquiv v).1
            (ctx.step.splitSurvivingPiMeasurableEquiv v).2 *
          terminal.completeNestedRunDensity ctx.nextContext
            ctx.leftPost_nonempty ctx.rightPost_nonempty
            (fun i : ctx.nextContext.SurvivingCoordinate =>
              (ctx.step.splitSurvivingPiMeasurableEquiv v).2 ⟨i.1, i.2⟩) := by
  filter_upwards
      [terminal.ae_headHalfPaths_mul_completeCrossGap_one_eq_completeNormalized
        ctx]
    with v hhead
  have hhalf :=
    terminal.nestedHalfInvSqProducts_current_eq_head_connector_post_named
      ctx v
  have hleftPost := terminal.nestedLeftHalfInvSqProduct_post_eq_next ctx v
  have hrightPost := terminal.nestedRightHalfInvSqProduct_post_eq_next ctx v
  have hcovHead := headBlockSum_reconstruct_eq_completePairingSum
    (ρ := ρ) (ε := ε) ctx v
  have hcovSplit := r324NestedResidualPrimitiveSumProduct_head
    ρ ε ctx.step (ctx.step.reconstruct v)
  have hcovPost := ctx.nestedResidualPrimitiveSumProduct_next_reconstruct_eq
    ρ ε v
  have horder := ctx.step.remainingOrder_eq_order_add_next
  have hpostEq :
      (fun i : ctx.nextContext.SurvivingCoordinate =>
        (ctx.step.splitSurvivingPiMeasurableEquiv v).2 ⟨i.1, i.2⟩) =
        (ctx.step.splitSurvivingPiMeasurableEquiv v).2 := by
    funext i
    congr 1
  unfold completeNestedRunDensity
  rw [hhalf, hcovSplit, hcovHead, hleftPost, hrightPost, hcovPost,
    horder]
  rw [show 2 * (ctx.step.order + ctx.step.next.remainingOrder) =
      2 * ctx.step.order + 2 * ctx.step.next.remainingOrder by omega,
    pow_add]
  rw [← hhead]
  rw [hpostEq]
  dsimp only [R324NestedCrossProperStepContext.nextContext]
  ring

end R324TwoHalfTerminalData

/-! ## Integrability certificates for the literal complete run -/

private theorem measurable_primitiveInsertedMajorant_completeRun
    (C lam ε supportConstant : ℝ) (n : ℕ) :
    Measurable (primitiveInsertedMajorant C lam ε supportConstant n) := by
  unfold primitiveInsertedMajorant
  apply Measurable.const_mul
  apply Measurable.add
  · exact
      ((measurable_invSqKer.const_mul _).mul
        (measurable_primitiveSupportIndicator supportConstant ε))
  · exact
      ((measurable_torusDistSq.add_const _).inv.pow_const 2).const_mul _

namespace R324NestedCrossStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- Proposition 4.1 supplies the genuine integrability certificate for
one complete normalized shell, uniformly over every shell below the
ambient truncation.  This is separated from the quantitative terminal
bound because the budget-run constructor needs the certificate itself. -/
theorem integrable_completeNormalizedHeadDensity_at_truncation
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε) :
    Integrable (ctx.completeNormalizedHeadDensity ρ lam ε)
      (Measure.pi fun _ : Fin (2 * ctx.order) => paperMeasure) := by
  obtain ⟨supportConstant, C, _hsupport, _hC, hprop⟩ :=
    proposition41_at_truncation ρ
  let J := primitiveInsertedMajorant
    C lam ε supportConstant ctx.order
  have hJint : Integrable J paperMeasure :=
    integrable_primitiveInsertedMajorant
      C lam ε supportConstant ctx.order hε
  have hJmeas : Measurable J :=
    measurable_primitiveInsertedMajorant_completeRun
      C lam ε supportConstant ctx.order
  have hntrunc : ctx.order ≤ truncOrder ε :=
    ctx.order_le_ambient.trans hmtrunc
  have hmiddle : ∀ z : T4,
      ctx.completeCrossGapPrimitiveTerm
          ρ lam ε ctx.normalizedInput z 0 ≤ J z := by
    intro z
    have hkernel :=
      ctx.completeCrossGapPrimitiveTerm_le_primitiveKernelInserted
        ρ lam hε hε1 ctx.normalizedInput
        ctx.normalizedInput_measurable
        ctx.normalizedInput_admissible
        ctx.normalizedInput_nonneg z 0
    have hmajor :=
      (hprop lam ε ctx.order ctx.one_le_order ctx.normalizedInput
        hlam hε hε1 hntrunc
        ctx.normalizedInput_admissible).2.2 z |>.2
    exact hkernel.trans ((le_abs_self _).trans hmajor)
  exact ctx.integrable_completeNormalizedHeadDensity_of_term_le
    ρ lam hε hε1 J hJint hJmeas hmiddle

end R324NestedCrossStepContext

namespace R324NestedCrossProperStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- A complete normalized proper shell remains integrable after the two
literal flanking edges are attached.  The proof first integrates only the
internal block variables, and compares the resulting endpoint density with
the already-established inserted-convolution majorant. -/
theorem integrable_completeNormalizedHeadDensity_mul_connector_at_truncation
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (post : ctx.step.PostCoordinate → T4) :
    Integrable
      (fun t : Fin (2 * ctx.step.order) → T4 =>
        ctx.step.completeNormalizedHeadDensity ρ lam ε t *
          ctx.connector t post)
      (Measure.pi fun _ => paperMeasure) := by
  obtain ⟨supportConstant, C, hsupport, hC, hprop⟩ :=
    proposition41_at_truncation ρ
  let e := r324PrimitiveBlockTupleMeasurableEquiv
    ctx.step.order ctx.step.one_le_order
  let μ := Measure.pi fun _ : Fin (2 * ctx.step.order) => paperMeasure
  let μint := Measure.pi fun _ : Fin (2 * ctx.step.order - 2) => paperMeasure
  let ν := (paperMeasure.prod paperMeasure).prod μint
  let head := ctx.step.completeNormalizedHeadDensity ρ lam ε
  let current := fun t : Fin (2 * ctx.step.order) → T4 =>
    head t * ctx.connector t post
  let endpoint := fun p : T4 × T4 =>
    invSqKer (post ctx.nextLeftPostCoordinate - p.1) *
      ctx.step.completeCrossGapPrimitiveTerm
        ρ lam ε ctx.step.normalizedInput p.1 p.2 *
      invSqKer (p.2 - post ctx.nextRightPostCoordinate)
  let inserted := r324ProperInsertedConvolutionIntegrand
    C lam ε supportConstant ctx.step.order
      (post ctx.nextLeftPostCoordinate)
      (post ctx.nextRightPostCoordinate)
  have hntrunc : ctx.step.order ≤ truncOrder ε :=
    ctx.step.order_le_ambient.trans hmtrunc
  have hmiddle : ∀ z : T4,
      ctx.step.completeCrossGapPrimitiveTerm
          ρ lam ε ctx.step.normalizedInput z 0 ≤
        primitiveInsertedMajorant
          C lam ε supportConstant ctx.step.order z := by
    intro z
    have hkernel :=
      ctx.step.completeCrossGapPrimitiveTerm_le_primitiveKernelInserted
        ρ lam hε hε1 ctx.step.normalizedInput
        ctx.step.normalizedInput_measurable
        ctx.step.normalizedInput_admissible
        ctx.step.normalizedInput_nonneg z 0
    have hmajor :=
      (hprop lam ε ctx.step.order ctx.step.one_le_order
        ctx.step.normalizedInput hlam hε hε1 hntrunc
        ctx.step.normalizedInput_admissible).2.2 z |>.2
    exact hkernel.trans ((le_abs_self _).trans hmajor)
  have hinserted : Integrable inserted (paperMeasure.prod paperMeasure) := by
    dsimp only [inserted]
    exact integrable_r324ProperInsertedConvolutionIntegrand
      C lam supportConstant ctx.step.order hε
      (post ctx.nextLeftPostCoordinate)
      (post ctx.nextRightPostCoordinate)
  have hendpointMeas : Measurable endpoint := by
    dsimp only [endpoint]
    apply Measurable.mul
    · apply Measurable.mul
      · exact measurable_invSqKer.comp
          (measurable_const.sub measurable_fst)
      · exact
          (ctx.step.measurable_completeCrossGapPrimitiveTerm_normalized
            ρ lam hε hε1)
    · exact measurable_invSqKer.comp
        (measurable_snd.sub measurable_const)
  have hendpointNonneg : ∀ p, 0 ≤ endpoint p := by
    intro p
    exact mul_nonneg
      (mul_nonneg (invSqKer_nonneg _)
        (ctx.step.completeCrossGapPrimitiveTerm_nonneg
          ρ lam ε ctx.step.normalizedInput
          ctx.step.normalizedInput_nonneg p.1 p.2))
      (invSqKer_nonneg _)
  have hendpointLe : ∀ p, endpoint p ≤ inserted p := by
    intro p
    dsimp only [endpoint, inserted,
      r324ProperInsertedConvolutionIntegrand]
    rw [ctx.step.completeCrossGapPrimitiveTerm_eq_diff
      ρ lam ε ctx.step.normalizedInput p.1 p.2]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hmiddle (p.1 - p.2))
        (invSqKer_nonneg _))
      (invSqKer_nonneg _)
  have hendpoint : Integrable endpoint (paperMeasure.prod paperMeasure) := by
    refine hinserted.mono' hendpointMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hendpointNonneg p)]
    exact hendpointLe p
  have hhead : Integrable head μ := by
    dsimp only [head, μ]
    exact ctx.step.integrable_completeNormalizedHeadDensity_at_truncation
      ρ lam ε hlam hε hε1 hmtrunc
  have hp := measurePreserving_r324PrimitiveBlockTupleMeasurableEquiv
    ctx.step.order ctx.step.one_le_order
  have hheadSplit :
      Integrable (fun q : (T4 × T4) ×
          (Fin (2 * ctx.step.order - 2) → T4) => head (e.symm q)) ν := by
    have hiff := hp.integrable_comp_emb e.measurableEmbedding
      (g := fun q : (T4 × T4) ×
          (Fin (2 * ctx.step.order - 2) → T4) => head (e.symm q))
    apply hiff.mp
    have hcomp :
        (fun q : (T4 × T4) ×
          (Fin (2 * ctx.step.order - 2) → T4) => head (e.symm q)) ∘ e =
          head := by
      funext t
      simp only [Function.comp_apply, e.symm_apply_apply]
    rw [hcomp]
    exact hhead
  have hcurrentMeas : Measurable current := by
    dsimp only [current, head]
    exact (ctx.step.completeNormalizedHeadDensity_measurable ρ lam ε).mul
      (ctx.connector_measurable post)
  have hfmeas : Measurable (fun q : (T4 × T4) ×
      (Fin (2 * ctx.step.order - 2) → T4) => current (e.symm q)) :=
    hcurrentMeas.comp e.symm.measurable
  have hsections :
      ∀ᵐ p : T4 × T4 ∂(paperMeasure.prod paperMeasure),
        Integrable (fun u => current (e.symm (p, u))) μint := by
    filter_upwards [hheadSplit.prod_right_ae] with p hpSection
    let c : ℝ :=
      invSqKer (post ctx.nextLeftPostCoordinate - p.1) *
        invSqKer (p.2 - post ctx.nextRightPostCoordinate)
    have hsectionEq :
        (fun u => current (e.symm (p, u))) =
          fun u => head (e.symm (p, u)) * c := by
      funext u
      dsimp only [current, c]
      congr 1
      dsimp only [e]
      simp only [r324PrimitiveBlockTupleMeasurableEquiv_symm_apply]
      unfold connector
      rw [primitiveAssemble_zero, primitiveAssemble_last]
    rw [hsectionEq]
    exact hpSection.mul_const c
  have houterEq :
      (fun p : T4 × T4 =>
        ∫ u, ‖current (e.symm (p, u))‖ ∂μint) = endpoint := by
    funext p
    have hnonneg : ∀ u, 0 ≤ current (e.symm (p, u)) := by
      intro u
      exact mul_nonneg
        (ctx.step.completeNormalizedHeadDensity_nonneg ρ lam ε _)
        (ctx.connector_nonneg _ post)
    calc
      (∫ u, ‖current (e.symm (p, u))‖ ∂μint) =
          ∫ u, current (e.symm (p, u)) ∂μint := by
        apply integral_congr_ae
        filter_upwards with u
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg u)]
      _ = endpoint p := by
        dsimp only [current, head, endpoint, e]
        simp_rw [r324PrimitiveBlockTupleMeasurableEquiv_symm_apply]
        have hconnector : ∀ u,
            ctx.connector
                (primitiveAssemble ctx.step.order ctx.step.one_le_order
                  p.1 p.2 u) post =
              invSqKer (post ctx.nextLeftPostCoordinate - p.1) *
                invSqKer (p.2 - post ctx.nextRightPostCoordinate) := by
          intro u
          unfold connector
          rw [primitiveAssemble_zero, primitiveAssemble_last]
        simp_rw [hconnector]
        rw [integral_mul_const]
        unfold R324NestedCrossStepContext.completeNormalizedHeadDensity
        rw [integral_const_mul]
        rw [← ctx.step.completeCrossGapPrimitiveTerm_eq_integral
          ρ lam hε hε1 ctx.step.normalizedInput
          ctx.step.normalizedInput_measurable
          ctx.step.normalizedInput_admissible p.1 p.2]
        ring
  have hsplit :
      Integrable (fun q : (T4 × T4) ×
          (Fin (2 * ctx.step.order - 2) → T4) => current (e.symm q)) ν := by
    apply (integrable_prod_iff hfmeas.aestronglyMeasurable).2
    refine ⟨hsections, ?_⟩
    rw [houterEq]
    exact hendpoint
  have hback :=
    (hp.integrable_comp_emb e.measurableEmbedding
      (g := fun q : (T4 × T4) ×
        (Fin (2 * ctx.step.order - 2) → T4) => current (e.symm q))).mpr hsplit
  have hcomp :
      (fun q : (T4 × T4) ×
        (Fin (2 * ctx.step.order - 2) → T4) => current (e.symm q)) ∘ e =
        current := by
    funext t
    simp only [Function.comp_apply, e.symm_apply_apply]
  rw [hcomp] at hback
  simpa only [current, head, μ] using hback

/-- If the untouched outer suffix is integrable, then adjoining one
complete proper shell gives the exact integrable density required by the
`proper` constructor of `R324CompleteNestedCrossBudgetRun`. -/
theorem integrable_completeProperDensity_at_truncation
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|)
    (hmtrunc : m ≤ truncOrder ε)
    (nextDensity : (ctx.step.PostCoordinate → T4) → ℝ)
    (hnext : Integrable nextDensity
      (Measure.pi fun _ : ctx.step.PostCoordinate => paperMeasure)) :
    Integrable
      (fun v : ctx.step.SurvivingCoordinate → T4 =>
        ctx.step.completeNormalizedHeadDensity ρ lam ε
            (fun j => v (ctx.step.headSurvivingCoordinate j)) *
          ctx.connector
            (fun j => v (ctx.step.headSurvivingCoordinate j))
            (fun i => v (ctx.step.postSurvivingCoordinate i)) *
          nextDensity
            (fun i => v (ctx.step.postSurvivingCoordinate i)))
      (Measure.pi fun _ : ctx.step.SurvivingCoordinate => paperMeasure) := by
  obtain ⟨D, hD, hprovider⟩ :=
    exists_r324CompleteProperHeadSharpProvider ρ
  have provider : R324CompleteProperHeadSharpProvider
      ρ lam ε D κp κm π :=
    hprovider lam ε π hlam hε hε1 hlog hmtrunc
  let e := ctx.step.splitSurvivingPiMeasurableEquiv
  let μ := Measure.pi fun _ : ctx.step.SurvivingCoordinate => paperMeasure
  let μhead := Measure.pi fun _ : Fin (2 * ctx.step.order) => paperMeasure
  let μpost := Measure.pi fun _ : ctx.step.PostCoordinate => paperMeasure
  let head := ctx.step.completeNormalizedHeadDensity ρ lam ε
  let f := fun p : (Fin (2 * ctx.step.order) → T4) ×
      (ctx.step.PostCoordinate → T4) =>
    (head p.1 * ctx.connector p.1 p.2) * nextDensity p.2
  have hheadConnector : ∀ post,
      Integrable (fun t => head t * ctx.connector t post) μhead := by
    intro post
    dsimp only [head, μhead]
    exact ctx.integrable_completeNormalizedHeadDensity_mul_connector_at_truncation
      ρ lam ε hlam hε hε1 hmtrunc post
  have hfAES : AEStronglyMeasurable f (μhead.prod μpost) := by
    have hheadMeas : Measurable
        (fun p : (Fin (2 * ctx.step.order) → T4) ×
            (ctx.step.PostCoordinate → T4) => head p.1) :=
      (ctx.step.completeNormalizedHeadDensity_measurable ρ lam ε).comp
        measurable_fst
    have hheadConnectorMeas : Measurable
        (fun p : (Fin (2 * ctx.step.order) → T4) ×
            (ctx.step.PostCoordinate → T4) =>
          head p.1 * ctx.connector p.1 p.2) :=
      hheadMeas.mul ctx.connector_joint_measurable
    exact hheadConnectorMeas.aestronglyMeasurable.mul
      hnext.aestronglyMeasurable.comp_snd
  have hsections : ∀ᵐ post ∂μpost,
      Integrable (fun t => f (t, post)) μhead :=
    Filter.Eventually.of_forall fun post => by
      dsimp only [f]
      exact (hheadConnector post).mul_const (nextDensity post)
  let A : ℝ := (D * lam) ^ (2 * ctx.step.order)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact (even_two_mul ctx.step.order).pow_nonneg _
  have houterNonneg : ∀ post,
      0 ≤ ∫ t, ‖f (t, post)‖ ∂μhead := by
    intro post
    exact integral_nonneg fun _ => norm_nonneg _
  have houterLe : ∀ post,
      (∫ t, ‖f (t, post)‖ ∂μhead) ≤ A * ‖nextDensity post‖ := by
    intro post
    have hbaseNonneg : ∀ t, 0 ≤ head t * ctx.connector t post := by
      intro t
      exact mul_nonneg
        (ctx.step.completeNormalizedHeadDensity_nonneg ρ lam ε t)
        (ctx.connector_nonneg t post)
    calc
      (∫ t, ‖f (t, post)‖ ∂μhead) =
          (∫ t, head t * ctx.connector t post ∂μhead) *
            ‖nextDensity post‖ := by
        dsimp only [f]
        have hnorm : ∀ t,
            ‖(head t * ctx.connector t post) * nextDensity post‖ =
              (head t * ctx.connector t post) * ‖nextDensity post‖ := by
          intro t
          rw [norm_mul, Real.norm_eq_abs,
            abs_of_nonneg (hbaseNonneg t)]
        simp_rw [hnorm]
        rw [integral_mul_const]
      _ = ctx.completeProperHeadIntegral ρ lam ε
            (post ctx.nextLeftPostCoordinate)
            (post ctx.nextRightPostCoordinate) *
          ‖nextDensity post‖ := by
        rw [ctx.integral_completeNormalizedHeadDensity_mul_connector
          ρ lam ε hε hε1 post (hheadConnector post)]
      _ ≤ A * ‖nextDensity post‖ :=
        mul_le_mul_of_nonneg_right
          (provider.headIntegral_le ctx
            (post ctx.nextLeftPostCoordinate)
            (post ctx.nextRightPostCoordinate))
          (norm_nonneg _)
  have htarget : Integrable (fun post => A * ‖nextDensity post‖) μpost :=
    hnext.norm.const_mul A
  have houterAES : AEStronglyMeasurable
      (fun post => ∫ t, ‖f (t, post)‖ ∂μhead) μpost := by
    simpa [Function.comp_def, Prod.swap] using
      hfAES.norm.prod_swap.integral_prod_right'
  have houter : Integrable
      (fun post => ∫ t, ‖f (t, post)‖ ∂μhead) μpost := by
    refine htarget.mono' houterAES
      (Filter.Eventually.of_forall fun post => ?_)
    have hleft :
        ‖∫ t, ‖f (t, post)‖ ∂μhead‖ =
          ∫ t, ‖f (t, post)‖ ∂μhead := by
      rw [Real.norm_eq_abs, abs_of_nonneg (houterNonneg post)]
    rw [hleft]
    exact houterLe post
  have hsplit : Integrable f (μhead.prod μpost) := by
    exact (integrable_prod_iff' hfAES).2 ⟨hsections, houter⟩
  have hp : MeasurePreserving e μ (μhead.prod μpost) :=
    ctx.step.measurePreserving_splitSurvivingPiMeasurableEquiv
  have hback :=
    (hp.integrable_comp_emb e.measurableEmbedding (g := f)).mpr hsplit
  have hcomp : f ∘ e =
      fun v : ctx.step.SurvivingCoordinate → T4 =>
        ctx.step.completeNormalizedHeadDensity ρ lam ε
            (fun j => v (ctx.step.headSurvivingCoordinate j)) *
          ctx.connector
            (fun j => v (ctx.step.headSurvivingCoordinate j))
            (fun i => v (ctx.step.postSurvivingCoordinate i)) *
          nextDensity
            (fun i => v (ctx.step.postSurvivingCoordinate i)) := by
    funext v
    have hfst : (e v).1 =
        fun j => v (ctx.step.headSurvivingCoordinate j) := by
      funext j
      exact ctx.step.splitSurvivingPiMeasurableEquiv_apply_fst v j
    have hsnd : (e v).2 =
        fun i => v (ctx.step.postSurvivingCoordinate i) := by
      funext i
      exact ctx.step.splitSurvivingPiMeasurableEquiv_apply_snd v i
    dsimp only [f, head, Function.comp_apply]
    rw [hfst, hsnd]
  rw [hcomp] at hback
  simpa only [μ] using hback

end R324NestedCrossProperStepContext

namespace R324NestedCrossStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- The complete head density read on the genuine surviving carrier.  At
the final shell the post coordinate is empty; retaining this uniform
definition lets the structural recursion use the same coordinate split at
every depth. -/
def completeHeadPullbackDensity
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (v : ctx.SurvivingCoordinate → T4) : ℝ :=
  ctx.completeNormalizedHeadDensity ρ lam ε
    (ctx.splitSurvivingPiMeasurableEquiv v).1

theorem completeHeadPullbackDensity_nonneg
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ) (v : ctx.SurvivingCoordinate → T4) :
    0 ≤ ctx.completeHeadPullbackDensity ρ lam ε v :=
  ctx.completeNormalizedHeadDensity_nonneg ρ lam ε _

theorem integrable_completeHeadPullbackDensity_at_truncation
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε) :
    Integrable (ctx.completeHeadPullbackDensity ρ lam ε)
      (Measure.pi fun _ : ctx.SurvivingCoordinate => paperMeasure) := by
  let e := ctx.splitSurvivingPiMeasurableEquiv
  let μ := Measure.pi fun _ : ctx.SurvivingCoordinate => paperMeasure
  let μhead := Measure.pi fun _ : Fin (2 * ctx.order) => paperMeasure
  let μpost := Measure.pi fun _ : ctx.PostCoordinate => paperMeasure
  let head := ctx.completeNormalizedHeadDensity ρ lam ε
  have hhead : Integrable head μhead := by
    dsimp only [head, μhead]
    exact ctx.integrable_completeNormalizedHeadDensity_at_truncation
      ρ lam ε hlam hε hε1 hmtrunc
  have hprod : Integrable (fun p :
      (Fin (2 * ctx.order) → T4) × (ctx.PostCoordinate → T4) => head p.1)
      (μhead.prod μpost) :=
    hhead.comp_fst μpost
  have hp : MeasurePreserving e μ (μhead.prod μpost) :=
    ctx.measurePreserving_splitSurvivingPiMeasurableEquiv
  have hback :=
    (hp.integrable_comp_emb e.measurableEmbedding
      (g := fun p : (Fin (2 * ctx.order) → T4) ×
        (ctx.PostCoordinate → T4) => head p.1)).mpr hprod
  have hcomp :
      (fun p : (Fin (2 * ctx.order) → T4) ×
        (ctx.PostCoordinate → T4) => head p.1) ∘ e =
        ctx.completeHeadPullbackDensity ρ lam ε := by
    rfl
  rw [hcomp] at hback
  simpa only [μ] using hback

/-- At the genuine final shell the post carrier is empty, so pulling the
complete head back to the surviving carrier does not create an additional
volume factor.  This is the terminal Fubini identity in paper Step 3. -/
theorem integral_completeHeadPullbackDensity_eq_of_tail_eq_nil
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (htail : ctx.tail = []) :
    (∫ v : ctx.SurvivingCoordinate → T4,
        ctx.completeHeadPullbackDensity ρ lam ε v
        ∂Measure.pi fun _ => paperMeasure) =
      ∫ t : Fin (2 * ctx.order) → T4,
        ctx.completeNormalizedHeadDensity ρ lam ε t
        ∂Measure.pi fun _ => paperMeasure := by
  let e := ctx.splitSurvivingPiMeasurableEquiv
  let μ := Measure.pi fun _ : ctx.SurvivingCoordinate => paperMeasure
  let μhead := Measure.pi fun _ : Fin (2 * ctx.order) => paperMeasure
  let μpost := Measure.pi fun _ : ctx.PostCoordinate => paperMeasure
  let head := ctx.completeNormalizedHeadDensity ρ lam ε
  have hpostActive : ctx.next.activeCarrier = ∅ := by
    unfold R324NestedCrossStepContext.next
      R324NestedCrossResidualPrefix.activeCarrier
    rw [R324NestedCrossResidualPrefix.afterHead_remaining, htail]
    rfl
  letI : IsEmpty ctx.PostCoordinate :=
    ⟨fun i => by
      have hi : i.val ∈ ctx.next.activeCarrier := i.property
      have hempty : i.val ∈ (∅ : Finset (Fin (2 * m))) :=
        hpostActive ▸ hi
      simp at hempty⟩
  have hp : MeasurePreserving e μ (μhead.prod μpost) :=
    ctx.measurePreserving_splitSurvivingPiMeasurableEquiv
  have htransport :
      (∫ v : ctx.SurvivingCoordinate → T4,
          ctx.completeHeadPullbackDensity ρ lam ε v ∂μ) =
        ∫ p : (Fin (2 * ctx.order) → T4) ×
            (ctx.PostCoordinate → T4),
          head p.1 ∂(μhead.prod μpost) := by
    simpa only [Function.comp_apply, e, head,
      completeHeadPullbackDensity] using
      hp.integral_comp'
        (fun p : (Fin (2 * ctx.order) → T4) ×
          (ctx.PostCoordinate → T4) => head p.1)
  rw [htransport]
  have hpostMass : μpost.real Set.univ = 1 := by
    rw [measureReal_def]
    dsimp only [μpost]
    rw [Measure.pi_empty_univ]
    simp
  calc
    (∫ p : (Fin (2 * ctx.order) → T4) ×
          (ctx.PostCoordinate → T4),
        head p.1 ∂(μhead.prod μpost)) =
        (∫ t, head t ∂μhead) *
          ∫ _ : ctx.PostCoordinate → T4, (1 : ℝ) ∂μpost := by
      simpa only [mul_one] using
        (integral_prod_mul head
          (fun _ : ctx.PostCoordinate → T4 => (1 : ℝ)))
    _ = (∫ t, head t ∂μhead) * 1 := by
      congr 1
      rw [integral_unique, hpostMass, one_smul]
    _ = _ := by
      simp only [mul_one, head, μhead]

end R324NestedCrossStepContext

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)

/-- Base case of the literal Step 3 recursion.  When no outer shell remains,
the grouped physical density is exactly the complete final primitive head,
almost everywhere. -/
theorem ae_completeNestedRunDensity_eq_completeHeadPullback_of_tail_eq_nil
    {π : κp.singles ≃ κm.singles}
    (step : R324NestedCrossStepContext κp κm π)
    (htail : step.tail = [])
    (hleft : (r324LeftHalfPullback
      step.residual.activeCarrier).Nonempty)
    (hright : (r324RightHalfPullback
      step.residual.activeCarrier).Nonempty) :
    terminal.completeNestedRunDensity step hleft hright =ᵐ[
      Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure]
      step.completeHeadPullbackDensity ρ lam ε := by
  have hremaining : step.residual.remaining = [step.head] := by
    rw [step.remaining_eq, htail]
  have hactive : step.residual.activeCarrier = step.head.carrier := by
    unfold R324NestedCrossResidualPrefix.activeCarrier
    rw [hremaining]
    simp [finsetUnionList]
  have horder : step.residual.remainingOrder = step.order := by
    unfold R324NestedCrossResidualPrefix.remainingOrder
      R324NestedCrossStepContext.order
    rw [hremaining]
    simp
  filter_upwards
      [terminal.ae_finalHeadHalfPaths_mul_completeCrossGap_one_eq_completeNormalized
        step htail]
    with v hhead
  have hcov :
      r324NestedResidualPrimitiveSumProduct
          ρ ε κp κm π step.residual (step.reconstruct v) =
        ∑ κ ∈ primitiveFullPairings step.order,
          primitiveCovarianceProduct ρ ε step.order κ
            (step.splitSurvivingPiMeasurableEquiv v).1 := by
    unfold r324NestedResidualPrimitiveSumProduct
    rw [hremaining]
    simp only [List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    exact finalHeadBlockSum_reconstruct_eq_completePairingSum
      (ρ := ρ) (ε := ε) step v
  unfold completeNestedRunDensity
    R324NestedCrossStepContext.completeHeadPullbackDensity
  rw [horder, hcov]
  have hleftPath :
      terminal.nestedLeftHalfInvSqProduct step
          step.residual.activeCarrier hleft v =
        terminal.nestedLeftHalfInvSqProduct step
          step.head.carrier step.finalLeftHeadNonempty v := by
    simp only [hactive]
  have hrightPath :
      terminal.nestedRightHalfInvSqProduct step
          step.residual.activeCarrier hright v =
        terminal.nestedRightHalfInvSqProduct step
          step.head.carrier step.finalRightHeadNonempty v := by
    simp only [hactive]
  rw [hleftPath, hrightPath]
  exact hhead

end R324TwoHalfTerminalData

namespace R324NestedCrossStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- Pull an a.e. identity on the untouched suffix back to the current
surviving carrier. -/
theorem ae_post_comp_eq
    (step : R324NestedCrossStepContext κp κm π)
    {f g : (step.PostCoordinate → T4) → ℝ}
    (hfg : f =ᵐ[
      Measure.pi fun _ : step.PostCoordinate => paperMeasure] g) :
    (fun v : step.SurvivingCoordinate → T4 =>
        f (fun i => v (step.postSurvivingCoordinate i))) =ᵐ[
      Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure]
      fun v => g (fun i => v (step.postSurvivingCoordinate i)) := by
  have hprod :
      ∀ᵐ p :
          (Fin (2 * step.order) → T4) ×
            (step.PostCoordinate → T4)
          ∂((Measure.pi fun _ : Fin (2 * step.order) => paperMeasure).prod
            (Measure.pi fun _ : step.PostCoordinate => paperMeasure)),
        f p.2 = g p.2 :=
    Measure.quasiMeasurePreserving_snd.tendsto_ae hfg
  have hpull :=
    step.measurePreserving_splitSurvivingPiMeasurableEquiv
      |>.quasiMeasurePreserving.tendsto_ae hprod
  filter_upwards [hpull] with v hv
  change
    f (step.splitSurvivingPiMeasurableEquiv v).2 =
      g (step.splitSurvivingPiMeasurableEquiv v).2 at hv
  have hsnd :
      (step.splitSurvivingPiMeasurableEquiv v).2 =
        fun i => v (step.postSurvivingCoordinate i) := by
    funext i
    exact step.splitSurvivingPiMeasurableEquiv_apply_snd v i
  simpa only [hsnd] using hv

end R324NestedCrossStepContext

/-! ## Structural producer for the existing complete budget run -/

/-- The literal grouped Step 3 density is identified a.e. with the density
of an existing complete budget run.  The accompanying equality of orders is
the exact inside-to-outside ledger of (4.20), not an auxiliary estimate. -/
theorem exists_r324CompleteNestedCrossBudgetRun_identified
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)
    (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|)
    (hmtrunc : m ≤ truncOrder ε)
    (step : R324NestedCrossStepContext κp κm π)
    (hleft : (r324LeftHalfPullback
      step.residual.activeCarrier).Nonempty)
    (hright : (r324RightHalfPullback
      step.residual.activeCarrier).Nonempty) :
    ∃ density : (step.SurvivingCoordinate → T4) → ℝ,
      ∃ prefixOrder terminalOrder : ℕ,
        R324CompleteNestedCrossBudgetRun
            ρ lam ε step.residual density prefixOrder terminalOrder ∧
        terminal.completeNestedRunDensity step hleft hright =ᵐ[
          Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure]
          density ∧
        step.residual.remainingOrder = prefixOrder + terminalOrder := by
  cases htail : step.tail with
  | nil =>
      let density := step.completeHeadPullbackDensity ρ lam ε
      have hrun : R324CompleteNestedCrossBudgetRun
          ρ lam ε step.residual density 0
            step.residual.remainingOrder :=
        R324CompleteNestedCrossBudgetRun.stop
          step.residual density
          (fun v => step.completeHeadPullbackDensity_nonneg ρ lam ε v)
          (step.integrable_completeHeadPullbackDensity_at_truncation
            ρ lam ε hlam hε hε1 hmtrunc)
      refine ⟨density, 0, step.residual.remainingOrder,
        hrun, ?_, ?_⟩
      · exact
          terminal.ae_completeNestedRunDensity_eq_completeHeadPullback_of_tail_eq_nil
            step htail hleft hright
      · exact hrun.remainingOrder_eq
  | cons nextHead rest =>
      let proper : R324NestedCrossProperStepContext κp κm π :=
        { step := step
          nextHead := nextHead
          rest := rest
          tail_eq := htail }
      obtain ⟨nextDensity, nextPrefixOrder, terminalOrder,
          hnextRun, hnextEq, _hnextOrder⟩ :=
        exists_r324CompleteNestedCrossBudgetRun_identified
          terminal hlam hε hε1 hlog hmtrunc proper.nextContext
            proper.leftPost_nonempty proper.rightPost_nonempty
      let density := fun v : step.SurvivingCoordinate → T4 =>
        step.completeNormalizedHeadDensity ρ lam ε
            (fun j => v (step.headSurvivingCoordinate j)) *
          proper.connector
            (fun j => v (step.headSurvivingCoordinate j))
            (fun i => v (step.postSurvivingCoordinate i)) *
          nextDensity (fun i => v (step.postSurvivingCoordinate i))
      have hdensity : Integrable density
          (Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) := by
        dsimp only [density]
        exact proper.integrable_completeProperDensity_at_truncation
          ρ lam ε hlam hε hε1 hlog hmtrunc nextDensity
            hnextRun.density_integrable
      have hrun : R324CompleteNestedCrossBudgetRun
          ρ lam ε step.residual density
            (step.order + nextPrefixOrder) terminalOrder :=
        R324CompleteNestedCrossBudgetRun.proper proper
          nextDensity nextPrefixOrder terminalOrder hnextRun hdensity
      have hlayer :=
        terminal.ae_completeNestedRunDensity_eq_head_connector_next proper
      have hnextPulled := step.ae_post_comp_eq hnextEq
      have hidentified :
          terminal.completeNestedRunDensity step hleft hright =ᵐ[
            Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure]
            density := by
        filter_upwards [hlayer, hnextPulled] with v hv hnextv
        have hheadTuple :
            (step.splitSurvivingPiMeasurableEquiv v).1 =
              fun j => v (step.headSurvivingCoordinate j) := by
          funext j
          exact step.splitSurvivingPiMeasurableEquiv_apply_fst v j
        have hpostTuple :
            (step.splitSurvivingPiMeasurableEquiv v).2 =
              fun i => v (step.postSurvivingCoordinate i) := by
          funext i
          exact step.splitSurvivingPiMeasurableEquiv_apply_snd v i
        have hchildTuple :
            (fun i : proper.nextContext.SurvivingCoordinate =>
              (step.splitSurvivingPiMeasurableEquiv v).2 ⟨i.1, i.2⟩) =
              (step.splitSurvivingPiMeasurableEquiv v).2 := by
          funext i
          congr 1
        rw [hv]
        dsimp only [density]
        rw [hchildTuple]
        dsimp only [R324NestedCrossProperStepContext.nextContext]
          at hnextv ⊢
        rw [hpostTuple, hnextv, hheadTuple]
        rfl
      exact ⟨density, step.order + nextPrefixOrder, terminalOrder,
        hrun, hidentified, hrun.remainingOrder_eq⟩
termination_by step.tail.length
decreasing_by
  rw [htail]
  simp [R324NestedCrossProperStepContext.nextContext]

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- The literal grouped Step 3 density is integrable throughout the paper's
truncation range.  This is only the public analytic consequence of the
identified complete budget run above. -/
theorem integrable_completeNestedRunDensity_at_truncation
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)
    (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|)
    (hmtrunc : m ≤ truncOrder ε)
    (step : R324NestedCrossStepContext κp κm π)
    (hleft : (r324LeftHalfPullback
      step.residual.activeCarrier).Nonempty)
    (hright : (r324RightHalfPullback
      step.residual.activeCarrier).Nonempty) :
    Integrable (terminal.completeNestedRunDensity step hleft hright)
      (Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) := by
  obtain ⟨density, prefixOrder, terminalOrder,
      run, hidentified, _horder⟩ :=
    exists_r324CompleteNestedCrossBudgetRun_identified
      terminal hlam hε hε1 hlog hmtrunc step hleft hright
  exact run.density_integrable.congr hidentified.symm

/-- Positivity of the literal grouped Step 3 density, in the a.e. form
needed by the proper-head integral comparison. -/
theorem ae_completeNestedRunDensity_nonneg_at_truncation
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)
    (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|)
    (hmtrunc : m ≤ truncOrder ε)
    (step : R324NestedCrossStepContext κp κm π)
    (hleft : (r324LeftHalfPullback
      step.residual.activeCarrier).Nonempty)
    (hright : (r324RightHalfPullback
      step.residual.activeCarrier).Nonempty) :
    ∀ᵐ v ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure,
      0 ≤ terminal.completeNestedRunDensity step hleft hright v := by
  obtain ⟨density, prefixOrder, terminalOrder,
      run, hidentified, _horder⟩ :=
    exists_r324CompleteNestedCrossBudgetRun_identified
      terminal hlam hε hε1 hlog hmtrunc step hleft hright
  filter_upwards [hidentified] with v hv
  rw [hv]
  exact run.density_nonneg v

/-- Paper Step 3, quantitatively: removing all proper nested shells leaves
one genuine final complete head.  `prefixOrder` is exactly the sum of the
removed proper-shell orders and `terminalOrder` is the order of that final
head.  This statement keeps the complete primitive-pairing sum grouped
through every Fubini transition. -/
theorem exists_prefix_terminal_integral_completeNestedRunDensity_le
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)
    {D : ℝ}
    (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|)
    (hmtrunc : m ≤ truncOrder ε)
    (provider : R324CompleteProperHeadSharpProvider
      ρ lam ε D κp κm π)
    (step : R324NestedCrossStepContext κp κm π)
    (hleft : (r324LeftHalfPullback
      step.residual.activeCarrier).Nonempty)
    (hright : (r324RightHalfPullback
      step.residual.activeCarrier).Nonempty) :
    ∃ prefixOrder terminalOrder : ℕ,
      ∃ finalStep : R324NestedCrossStepContext κp κm π,
        step.residual.remainingOrder = prefixOrder + terminalOrder ∧
        terminalOrder = finalStep.order ∧
        (∫ v, terminal.completeNestedRunDensity step hleft hright v
            ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) ≤
          (D * lam) ^ (2 * prefixOrder) *
            ∫ t, finalStep.completeNormalizedHeadDensity ρ lam ε t
              ∂Measure.pi fun _ : Fin (2 * finalStep.order) => paperMeasure := by
  cases htail : step.tail with
  | nil =>
      have hremaining : step.residual.remaining = [step.head] := by
        rw [step.remaining_eq, htail]
      have horder : step.residual.remainingOrder = step.order := by
        unfold R324NestedCrossResidualPrefix.remainingOrder
          R324NestedCrossStepContext.order
        rw [hremaining]
        simp
      refine ⟨0, step.order, step, ?_, rfl, ?_⟩
      · simpa only [zero_add] using horder
      · have hidentified :=
          terminal.ae_completeNestedRunDensity_eq_completeHeadPullback_of_tail_eq_nil
            step htail hleft hright
        calc
          (∫ v, terminal.completeNestedRunDensity step hleft hright v
              ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) =
              ∫ v, step.completeHeadPullbackDensity ρ lam ε v
                ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure :=
            integral_congr_ae hidentified
          _ = ∫ t, step.completeNormalizedHeadDensity ρ lam ε t
                ∂Measure.pi fun _ : Fin (2 * step.order) => paperMeasure :=
            step.integral_completeHeadPullbackDensity_eq_of_tail_eq_nil
              ρ lam ε htail
          _ = (D * lam) ^ (2 * 0) *
                ∫ t, step.completeNormalizedHeadDensity ρ lam ε t
                  ∂Measure.pi fun _ : Fin (2 * step.order) => paperMeasure := by
            simp only [Nat.mul_zero, pow_zero, one_mul]
          _ ≤ _ := le_rfl
  | cons nextHead rest =>
      let proper : R324NestedCrossProperStepContext κp κm π :=
        { step := step
          nextHead := nextHead
          rest := rest
          tail_eq := htail }
      have hnextIntegrable :=
        terminal.integrable_completeNestedRunDensity_at_truncation
          hlam hε hε1 hlog hmtrunc proper.nextContext
            proper.leftPost_nonempty proper.rightPost_nonempty
      have hnextNonneg :=
        terminal.ae_completeNestedRunDensity_nonneg_at_truncation
          hlam hε hε1 hlog hmtrunc proper.nextContext
            proper.leftPost_nonempty proper.rightPost_nonempty
      obtain ⟨nextPrefixOrder, terminalOrder, finalStep,
          hnextOrder, hterminalOrder, hnextBound⟩ :=
        exists_prefix_terminal_integral_completeNestedRunDensity_le
          terminal hlam hε hε1 hlog hmtrunc provider proper.nextContext
            proper.leftPost_nonempty proper.rightPost_nonempty
      let nextDensity := terminal.completeNestedRunDensity proper.nextContext
        proper.leftPost_nonempty proper.rightPost_nonempty
      let currentDensity := fun v : step.SurvivingCoordinate → T4 =>
        step.completeNormalizedHeadDensity ρ lam ε
              (fun j => v (step.headSurvivingCoordinate j)) *
            proper.connector
              (fun j => v (step.headSurvivingCoordinate j))
              (fun i => v (step.postSurvivingCoordinate i)) *
            nextDensity (fun i => v (step.postSurvivingCoordinate i))
      have hcurrentIntegrable : Integrable currentDensity
          (Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) := by
        dsimp only [currentDensity, nextDensity]
        exact proper.integrable_completeProperDensity_at_truncation
          ρ lam ε hlam hε hε1 hlog hmtrunc _ hnextIntegrable
      have hlayer :=
        terminal.ae_completeNestedRunDensity_eq_head_connector_next proper
      have hidentified :
          terminal.completeNestedRunDensity step hleft hright =ᵐ[
            Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure]
            currentDensity := by
        filter_upwards [hlayer] with v hv
        have hheadTuple :
            (step.splitSurvivingPiMeasurableEquiv v).1 =
              fun j => v (step.headSurvivingCoordinate j) := by
          funext j
          exact step.splitSurvivingPiMeasurableEquiv_apply_fst v j
        have hpostTuple :
            (step.splitSurvivingPiMeasurableEquiv v).2 =
              fun i => v (step.postSurvivingCoordinate i) := by
          funext i
          exact step.splitSurvivingPiMeasurableEquiv_apply_snd v i
        have hchildTuple :
            (fun i : proper.nextContext.SurvivingCoordinate =>
              (step.splitSurvivingPiMeasurableEquiv v).2 ⟨i.1, i.2⟩) =
              (step.splitSurvivingPiMeasurableEquiv v).2 := by
          funext i
          congr 1
        rw [hv]
        dsimp only [currentDensity, nextDensity]
        rw [hchildTuple, hpostTuple, hheadTuple]
        rfl
      have hexact :=
        R324CompleteNestedCrossBudgetRun.integral_completeProperDensity_of_current_integrable
          proper nextDensity hε hε1 hcurrentIntegrable
      let A : ℝ := (D * lam) ^ (2 * step.order)
      have hA : 0 ≤ A := by
        dsimp only [A]
        exact (even_two_mul step.order).pow_nonneg _
      have htargetIntegrable : Integrable
          (fun post : step.PostCoordinate → T4 => A * nextDensity post)
          (Measure.pi fun _ => paperMeasure) := by
        exact hnextIntegrable.const_mul A
      have houterNonneg :
          ∀ᵐ post ∂Measure.pi fun _ : step.PostCoordinate => paperMeasure,
            0 ≤ proper.completeProperHeadIntegral ρ lam ε
                (post proper.nextLeftPostCoordinate)
                (post proper.nextRightPostCoordinate) * nextDensity post := by
        filter_upwards [hnextNonneg] with post hpost
        exact mul_nonneg
          (proper.completeProperHeadIntegral_nonneg ρ lam ε _ _) hpost
      have houterLe :
          (∫ post : step.PostCoordinate → T4,
              proper.completeProperHeadIntegral ρ lam ε
                  (post proper.nextLeftPostCoordinate)
                  (post proper.nextRightPostCoordinate) * nextDensity post
              ∂Measure.pi fun _ => paperMeasure) ≤
            A * ∫ post : step.PostCoordinate → T4, nextDensity post
              ∂Measure.pi fun _ => paperMeasure := by
        calc
          _ ≤ ∫ post : step.PostCoordinate → T4, A * nextDensity post
                ∂Measure.pi fun _ => paperMeasure := by
              apply integral_mono_of_nonneg houterNonneg htargetIntegrable
              filter_upwards [hnextNonneg] with post hpost
              exact mul_le_mul_of_nonneg_right
                (provider.headIntegral_le proper
                  (post proper.nextLeftPostCoordinate)
                  (post proper.nextRightPostCoordinate)) hpost
          _ = A * ∫ post : step.PostCoordinate → T4, nextDensity post
                ∂Measure.pi fun _ => paperMeasure := by
              rw [integral_const_mul]
      have hnextOrder' :
          step.next.remainingOrder = nextPrefixOrder + terminalOrder := by
        simpa only [proper,
          R324NestedCrossProperStepContext.nextContext] using hnextOrder
      refine ⟨step.order + nextPrefixOrder, terminalOrder, finalStep,
        ?_, hterminalOrder, ?_⟩
      · rw [step.remainingOrder_eq_order_add_next, hnextOrder']
        omega
      · calc
          (∫ v, terminal.completeNestedRunDensity step hleft hright v
              ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) =
              ∫ v, currentDensity v
                ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure :=
            integral_congr_ae hidentified
          _ = ∫ post : step.PostCoordinate → T4,
                proper.completeProperHeadIntegral ρ lam ε
                    (post proper.nextLeftPostCoordinate)
                    (post proper.nextRightPostCoordinate) * nextDensity post
                ∂Measure.pi fun _ => paperMeasure := hexact
          _ ≤ A * ∫ post : step.PostCoordinate → T4, nextDensity post
                ∂Measure.pi fun _ => paperMeasure := houterLe
          _ ≤ A * ((D * lam) ^ (2 * nextPrefixOrder) *
                ∫ t, finalStep.completeNormalizedHeadDensity ρ lam ε t
                  ∂Measure.pi fun _ : Fin (2 * finalStep.order) =>
                    paperMeasure) :=
            mul_le_mul_of_nonneg_left hnextBound hA
          _ = (D * lam) ^ (2 * (step.order + nextPrefixOrder)) *
                ∫ t, finalStep.completeNormalizedHeadDensity ρ lam ε t
                  ∂Measure.pi fun _ : Fin (2 * finalStep.order) =>
                    paperMeasure := by
            dsimp only [A]
            rw [show 2 * (step.order + nextPrefixOrder) =
                2 * step.order + 2 * nextPrefixOrder by omega, pow_add]
            ring
termination_by step.tail.length
decreasing_by
  rw [htail]
  simp [R324NestedCrossProperStepContext.nextContext]

/-- Uniform integrated closure of paper Steps 2(f)--3, equations
(4.18)--(4.20).  The two constants are selected from the cutoff before
`lam`, `ε`, the pairings, the terminal half traces, or the nested schedule;
the complete primitive-pairing sum is never split by a triangle
inequality. -/
theorem exists_integral_completeNestedRunDensity_le_primitiveInsertedMajorant
    (ρ : SmoothCutoff) :
    ∃ supportConstant C : ℝ,
      0 < supportConstant ∧ 0 < C ∧
      ∀ {lam ε : ℝ} {m : ℕ}
        {κp κm : PartialPairing (Fin m)}
        {π : κp.singles ≃ κm.singles}
        (terminal : R324TwoHalfTerminalData ρ lam ε κp κm),
        0 < lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| → m ≤ truncOrder ε →
        ∀ (step : R324NestedCrossStepContext κp κm π)
          (hleft : (r324LeftHalfPullback
            step.residual.activeCarrier).Nonempty)
          (hright : (r324RightHalfPullback
            step.residual.activeCarrier).Nonempty),
          (∫ v, terminal.completeNestedRunDensity step hleft hright v
              ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) ≤
            ∫ z, primitiveInsertedMajorant
              C lam ε supportConstant step.residual.remainingOrder z
              ∂paperMeasure := by
  obtain ⟨D, hD, hprovider⟩ :=
    exists_r324CompleteProperHeadSharpProvider ρ
  obtain ⟨supportConstant, terminalC, hsupport, hterminalC,
      hterminal⟩ :=
    R324NestedCrossStepContext.exists_completeTerminalHead_bound_at_truncation ρ
  refine ⟨supportConstant, r324CompleteAbsorbedBase D terminalC,
    hsupport, r324CompleteAbsorbedBase_pos D terminalC, ?_⟩
  intro lam ε m κp κm π terminal hlam hε hε1 hlog hmtrunc
    step hleft hright
  have provider : R324CompleteProperHeadSharpProvider
      ρ lam ε D κp κm π :=
    hprovider lam ε π hlam hε hε1 hlog hmtrunc
  obtain ⟨prefixOrder, terminalOrder, finalStep,
      htotalOrder, hterminalOrder, hprefix⟩ :=
    terminal.exists_prefix_terminal_integral_completeNestedRunDensity_le
      hlam hε hε1 hlog hmtrunc provider step hleft hright
  have hfinal := hterminal κp κm π finalStep lam ε
    hlam hε hε1 hmtrunc
  have hfinal' :
      (∫ t, finalStep.completeNormalizedHeadDensity ρ lam ε t
          ∂Measure.pi fun _ : Fin (2 * finalStep.order) => paperMeasure) ≤
        (2 * Real.pi) ^ (dim : ℕ) *
          ∫ z, primitiveInsertedMajorant
            terminalC lam ε supportConstant terminalOrder z
            ∂paperMeasure := by
    simpa only [hterminalOrder] using hfinal
  have hprefixNonneg :
      0 ≤ (D * lam) ^ (2 * prefixOrder) :=
    (even_two_mul prefixOrder).pow_nonneg _
  have hone : 1 ≤ prefixOrder + terminalOrder := by
    have hstepOrder : 1 ≤ step.order := step.one_le_order
    rw [← htotalOrder, step.remainingOrder_eq_order_add_next]
    omega
  calc
    (∫ v, terminal.completeNestedRunDensity step hleft hright v
        ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) ≤
        (D * lam) ^ (2 * prefixOrder) *
          ∫ t, finalStep.completeNormalizedHeadDensity ρ lam ε t
            ∂Measure.pi fun _ : Fin (2 * finalStep.order) => paperMeasure :=
      hprefix
    _ ≤ (D * lam) ^ (2 * prefixOrder) *
          ((2 * Real.pi) ^ (dim : ℕ) *
            ∫ z, primitiveInsertedMajorant
              terminalC lam ε supportConstant terminalOrder z
              ∂paperMeasure) :=
      mul_le_mul_of_nonneg_left hfinal' hprefixNonneg
    _ ≤ ∫ z, primitiveInsertedMajorant
          (r324CompleteAbsorbedBase D terminalC) lam ε supportConstant
            (prefixOrder + terminalOrder) z ∂paperMeasure :=
      r324_complete_prefix_mul_terminalIntegral_le
        hD.le hterminalC.le hlam.le hε prefixOrder terminalOrder hone
    _ = ∫ z, primitiveInsertedMajorant
          (r324CompleteAbsorbedBase D terminalC) lam ε supportConstant
            step.residual.remainingOrder z ∂paperMeasure := by
      rw [htotalOrder]

end R324TwoHalfTerminalData

/-- Every nonempty literal nested suffix produces the already-defined
complete budget run.  The recursion stops at the genuine last shell and
uses `proper` at every preceding shell, so the accumulated prefix order is
the paper's exact inside-to-outside removal order. -/
theorem exists_r324CompleteNestedCrossBudgetRun_of_remaining_ne_nil
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|)
    (hmtrunc : m ≤ truncOrder ε)
    (res : R324NestedCrossResidualPrefix κp κm π)
    (hne : res.remaining ≠ []) :
    ∃ density :
        ({i : Fin (2 * m) // i ∈ res.activeCarrier} → T4) → ℝ,
      ∃ prefixOrder terminalOrder : ℕ,
        R324CompleteNestedCrossBudgetRun
          ρ lam ε res density prefixOrder terminalOrder := by
  cases hremaining : res.remaining with
  | nil => exact (hne hremaining).elim
  | cons head tail =>
      let step := res.headContext head tail hremaining
      cases htail : tail with
      | nil =>
          let density := step.completeHeadPullbackDensity ρ lam ε
          refine ⟨density, 0, step.residual.remainingOrder, ?_⟩
          exact R324CompleteNestedCrossBudgetRun.stop
            step.residual density
            (fun v => step.completeHeadPullbackDensity_nonneg ρ lam ε v)
            (step.integrable_completeHeadPullbackDensity_at_truncation
              ρ lam ε hlam hε hε1 hmtrunc)
      | cons nextHead rest =>
          let proper : R324NestedCrossProperStepContext κp κm π :=
            { step := step
              nextHead := nextHead
              rest := rest
              tail_eq := htail }
          have hnextNe : step.next.remaining ≠ [] := by
            rw [show step.next.remaining = tail by rfl, htail]
            simp
          obtain ⟨nextDensity, nextPrefixOrder, terminalOrder, hnext⟩ :=
            exists_r324CompleteNestedCrossBudgetRun_of_remaining_ne_nil
              ρ lam ε hlam hε hε1 hlog hmtrunc step.next hnextNe
          let density := fun v : step.SurvivingCoordinate → T4 =>
            step.completeNormalizedHeadDensity ρ lam ε
                (fun j => v (step.headSurvivingCoordinate j)) *
              proper.connector
                (fun j => v (step.headSurvivingCoordinate j))
                (fun i => v (step.postSurvivingCoordinate i)) *
              nextDensity
                (fun i => v (step.postSurvivingCoordinate i))
          have hdensity : Integrable density
              (Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) := by
            dsimp only [density]
            exact proper.integrable_completeProperDensity_at_truncation
              ρ lam ε hlam hε hε1 hlog hmtrunc nextDensity
              hnext.density_integrable
          refine ⟨density, step.order + nextPrefixOrder, terminalOrder, ?_⟩
          exact R324CompleteNestedCrossBudgetRun.proper
            proper nextDensity nextPrefixOrder terminalOrder hnext hdensity
termination_by res.remaining.length
decreasing_by
  simp [R324NestedCrossResidualPrefix.headContext,
    R324NestedCrossStepContext.next,
    R324NestedCrossResidualPrefix.afterHead, hremaining, htail]

end

end Anderson4D
