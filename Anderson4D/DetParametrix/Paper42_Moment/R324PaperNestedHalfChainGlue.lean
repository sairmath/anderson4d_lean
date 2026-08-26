import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfChainPartition
import Anderson4D.DetParametrix.Paper42_Moment.R324CompleteNestedCrossIteration
import Anderson4D.DetParametrix.Paper42_Moment.R324ResidualSumNestedHeadBridge

/-!
# Gluing the terminal half chains to a nested cross step

This module transports the literal inside-to-outside order of the doubled
residual schedule to the two terminal half chains.  On the left the later
carrier precedes the current head; on the right the current head precedes
the later carrier.  These are exactly the two orientations of the
three-way half-chain partition.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- Pull a doubled carrier back to the left terminal half. -/
def r324LeftHalfPullback
    {m : ℕ} (B : Finset (Fin (2 * m))) : Finset (Fin m) :=
  Finset.univ.filter fun i => leftMomentIndex i ∈ B

/-- Pull a doubled carrier back to the right terminal half. -/
def r324RightHalfPullback
    {m : ℕ} (B : Finset (Fin (2 * m))) : Finset (Fin m) :=
  Finset.univ.filter fun i => rightMomentIndex i ∈ B

@[simp]
theorem mem_r324LeftHalfPullback
    {m : ℕ} {B : Finset (Fin (2 * m))} {i : Fin m} :
    i ∈ r324LeftHalfPullback B ↔ leftMomentIndex i ∈ B := by
  simp [r324LeftHalfPullback]

@[simp]
theorem mem_r324RightHalfPullback
    {m : ℕ} {B : Finset (Fin (2 * m))} {i : Fin m} :
    i ∈ r324RightHalfPullback B ↔ rightMomentIndex i ∈ B := by
  simp [r324RightHalfPullback]

/-- `outer` lies outside `inner` in both halves of the doubled chain. -/
def R324HalfCarrierOutward
    {m : ℕ} (inner outer : Finset (Fin (2 * m))) : Prop :=
  R324WithinHalfResidualPrefix.HalfCarrierBefore
      (r324LeftHalfPullback outer)
      (r324LeftHalfPullback inner) ∧
    R324WithinHalfResidualPrefix.HalfCarrierBefore
      (r324RightHalfPullback inner)
      (r324RightHalfPullback outer)

private theorem halfCarrierOutward_of_trace_exterior
    {n cut : ℕ} (active inner outer : Finset (Fin n))
    (p : Fin n × Fin n)
    (hstraddle : IntervalStraddlesCut cut p)
    (hinner : inner ⊆ residualIntervalTrace active p)
    (houter : outer ⊆ residualIntervalExterior active p) :
    (∀ i ∈ outer, (i : ℕ) < cut →
        ∀ j ∈ inner, (j : ℕ) < cut → i < j) ∧
      (∀ i ∈ inner, cut ≤ (i : ℕ) →
        ∀ j ∈ outer, cut ≤ (j : ℕ) → i < j) := by
  constructor
  · intro i hiOuter hiCut j hjInner _hjCut
    have hiExt := Finset.mem_sdiff.mp (houter hiOuter)
    have hjTrace := mem_relIcc.mp (hinner hjInner)
    have hiLt : i < p.1 := by
      by_contra hnot
      apply hiExt.2
      exact mem_relIcc.mpr
        ⟨hiExt.1, le_of_not_gt hnot,
          by
            rw [Fin.le_def]
            exact hiCut.le.trans hstraddle.2⟩
    exact hiLt.trans_le hjTrace.2.1
  · intro i hiInner _hiCut j hjOuter hjCut
    have hiTrace := mem_relIcc.mp (hinner hiInner)
    have hjExt := Finset.mem_sdiff.mp (houter hjOuter)
    have hp2Lt : p.2 < j := by
      by_contra hnot
      apply hjExt.2
      exact mem_relIcc.mpr
        ⟨hjExt.1,
          by
            rw [Fin.le_def]
            exact hstraddle.1.le.trans hjCut,
          le_of_not_gt hnot⟩
    exact hiTrace.2.2.trans_lt hp2Lt

private theorem nestedResidualShells_pairwise_halfOutward
    {m : ℕ} (active : Finset (Fin (2 * m)))
    (previous : Fin (2 * m) × Fin (2 * m))
    (rest : List (Fin (2 * m) × Fin (2 * m)))
    (hpair :
      (previous :: rest).Pairwise LaterCrossCutIntervalContains)
    (hcross :
      ∀ p ∈ previous :: rest, IntervalStraddlesCut m p) :
    (nestedResidualShells active previous rest).Pairwise
      R324HalfCarrierOutward := by
  induction rest generalizing previous with
  | nil =>
      simp [nestedResidualShells]
  | cons next rest ih =>
      have hcons := List.pairwise_cons.mp hpair
      have hnext : LaterCrossCutIntervalContains previous next :=
        hcons.1 next (by simp)
      have htail :
          (next :: rest).Pairwise LaterCrossCutIntervalContains :=
        hcons.2
      have hcrossNext : IntervalStraddlesCut m next :=
        hcross next (by simp)
      have hcrossTail :
          ∀ p ∈ next :: rest, IntervalStraddlesCut m p := by
        intro p hp
        exact hcross p (by simp [hp])
      simp only [nestedResidualShells, List.pairwise_cons]
      refine ⟨?_, ih next htail hcrossTail⟩
      intro B hB
      have hBsubset :
          B ⊆ residualIntervalExterior active next := by
        intro i hi
        have hiUnion :
            i ∈ finsetUnionList
              (nestedResidualShells active next rest) :=
          (mem_finsetUnionList_iff _).mpr ⟨B, hB, hi⟩
        rw [finsetUnionList_nestedResidualShells_eq_exterior
          active next rest htail] at hiUnion
        exact hiUnion
      have hshellSubset :
          residualIntervalShell active previous next ⊆
            residualIntervalTrace active next :=
        Finset.sdiff_subset
      have hout := halfCarrierOutward_of_trace_exterior
        active (residualIntervalShell active previous next) B next
        hcrossNext hshellSubset hBsubset
      constructor
      · intro i hi Bidx hBidx
        have hiDoubled := mem_r324LeftHalfPullback.mp hi
        have hBDoubled := mem_r324LeftHalfPullback.mp hBidx
        exact Fin.mk_lt_mk.mpr
          (hout.1 (leftMomentIndex i) hiDoubled i.isLt
            (leftMomentIndex Bidx) hBDoubled Bidx.isLt)
      · intro i hi Bidx hBidx
        have hiDoubled := mem_r324RightHalfPullback.mp hi
        have hBDoubled := mem_r324RightHalfPullback.mp hBidx
        have hiCut : m ≤ (rightMomentIndex i).val := by
          simp [rightMomentIndex]
        have hBCut : m ≤ (rightMomentIndex Bidx).val := by
          simp [rightMomentIndex]
        have hlt := hout.2 (rightMomentIndex i) hiDoubled hiCut
          (rightMomentIndex Bidx) hBDoubled hBCut
        apply Fin.mk_lt_mk.mpr
        change m + i.val < m + Bidx.val at hlt
        omega

private theorem residualCollapseBlocks_pairwise_halfOutward
    {m : ℕ} (active : Finset (Fin (2 * m)))
    (chain : List (Fin (2 * m) × Fin (2 * m)))
    (hpair : chain.Pairwise LaterCrossCutIntervalContains)
    (hcross : ∀ p ∈ chain, IntervalStraddlesCut m p) :
    (residualCollapseBlocks active chain).Pairwise
      R324HalfCarrierOutward := by
  cases chain with
  | nil =>
      simp [residualCollapseBlocks]
  | cons first rest =>
      have hfirstCross := hcross first (by simp)
      have htailCross :
          ∀ p ∈ first :: rest, IntervalStraddlesCut m p := by
        intro p hp
        exact hcross p hp
      simp only [residualCollapseBlocks, List.pairwise_cons]
      refine ⟨?_, nestedResidualShells_pairwise_halfOutward
        active first rest hpair htailCross⟩
      intro B hB
      have hBsubset :
          B ⊆ residualIntervalExterior active first := by
        intro i hi
        have hiUnion :
            i ∈ finsetUnionList
              (nestedResidualShells active first rest) :=
          (mem_finsetUnionList_iff _).mpr ⟨B, hB, hi⟩
        rw [finsetUnionList_nestedResidualShells_eq_exterior
          active first rest hpair] at hiUnion
        exact hiUnion
      have hout := halfCarrierOutward_of_trace_exterior
        active (residualIntervalTrace active first) B first
        hfirstCross (fun _ h => h) hBsubset
      constructor
      · intro i hi Bidx hBidx
        have hiDoubled := mem_r324LeftHalfPullback.mp hi
        have hBDoubled := mem_r324LeftHalfPullback.mp hBidx
        exact Fin.mk_lt_mk.mpr
          (hout.1 (leftMomentIndex i) hiDoubled i.isLt
            (leftMomentIndex Bidx) hBDoubled Bidx.isLt)
      · intro i hi Bidx hBidx
        have hiDoubled := mem_r324RightHalfPullback.mp hi
        have hBDoubled := mem_r324RightHalfPullback.mp hBidx
        have hiCut : m ≤ (rightMomentIndex i).val := by
          simp [rightMomentIndex]
        have hBCut : m ≤ (rightMomentIndex Bidx).val := by
          simp [rightMomentIndex]
        have hlt := hout.2 (rightMomentIndex i) hiDoubled hiCut
          (rightMomentIndex Bidx) hBDoubled hBCut
        apply Fin.mk_lt_mk.mpr
        change m + i.val < m + Bidx.val at hlt
        omega

/-- The canonical nonempty residual blocks are ordered from the inner
cross block to the outer blocks in both terminal half chains. -/
theorem nonemptyMomentResidualCollapseBlocks_pairwise_halfOutward
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (nonemptyMomentResidualCollapseBlocks κp κm π).Pairwise
      R324HalfCarrierOutward := by
  unfold nonemptyMomentResidualCollapseBlocks
    momentResidualCollapseBlocks
  apply List.Pairwise.filter
  apply residualCollapseBlocks_pairwise_halfOutward
  · exact momentResidualIntervalChain_pairwise_laterContains κp κm π
  · intro p hp
    exact momentResidualProperInterval_straddlesCut
      (mem_momentResidualIntervalChain.mp hp)

/-- Enriched proof-relevant blocks retain the same outward half order. -/
theorem r324NestedCrossSchedule_pairwise_halfOutward
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (r324NestedCrossSchedule κp κm π).Pairwise
      (fun inner outer =>
        R324HalfCarrierOutward inner.carrier outer.carrier) := by
  rw [← List.pairwise_map]
  rw [r324NestedCrossSchedule_carriers]
  exact nonemptyMomentResidualCollapseBlocks_pairwise_halfOutward κp κm π

theorem r324LeftHalfPullback_union
    {m : ℕ} (A B : Finset (Fin (2 * m))) :
    r324LeftHalfPullback (A ∪ B) =
      r324LeftHalfPullback A ∪ r324LeftHalfPullback B := by
  ext i
  simp

theorem r324RightHalfPullback_union
    {m : ℕ} (A B : Finset (Fin (2 * m))) :
    r324RightHalfPullback (A ∪ B) =
      r324RightHalfPullback A ∪ r324RightHalfPullback B := by
  ext i
  simp

theorem r324LeftHalfPullback_nonempty_of_crossCut
    {m : ℕ} {B : Finset (Fin (2 * m))}
    (hcross : R324CrossCutCarrier m B) :
    (r324LeftHalfPullback B).Nonempty := by
  obtain ⟨left, hleft, _right, _hright, hleftCut, _⟩ := hcross
  let i : Fin m := ⟨left.val, hleftCut⟩
  refine ⟨i, mem_r324LeftHalfPullback.mpr ?_⟩
  have heq : leftMomentIndex i = left := by
    apply Fin.ext
    rfl
  simpa only [heq] using hleft

theorem r324RightHalfPullback_nonempty_of_crossCut
    {m : ℕ} {B : Finset (Fin (2 * m))}
    (hcross : R324CrossCutCarrier m B) :
    (r324RightHalfPullback B).Nonempty := by
  obtain ⟨_left, _hleft, right, hright, _hleftCut, hrightCut⟩ := hcross
  let j : Fin m :=
    ⟨right.val - m, by
      have hrightLt := right.isLt
      omega⟩
  refine ⟨j, mem_r324RightHalfPullback.mpr ?_⟩
  have heq : rightMomentIndex j = right := by
    apply Fin.ext
    dsimp only [j, rightMomentIndex]
    omega
  simpa only [heq] using hright

/-- The terminal left index of the canonical cross gap is the maximum of
the pulled-back left carrier. -/
theorem leftMomentIndex_max'_r324LeftHalfPullback
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (block : R324NestedCrossBlock κp κm π) :
    leftMomentIndex
        ((r324LeftHalfPullback block.carrier).max'
          (r324LeftHalfPullback_nonempty_of_crossCut block.crossCut)) =
      block.leftGap := by
  let A := r324LeftHalfPullback block.carrier
  let hA : A.Nonempty :=
    r324LeftHalfPullback_nonempty_of_crossCut block.crossCut
  let gapHalf : Fin m :=
    ⟨block.leftGap.val, r324CrossGapLeft_lt_cut
      block.carrier block.crossCut⟩
  have hgapHalf : gapHalf ∈ A := by
    apply mem_r324LeftHalfPullback.mpr
    have heq : leftMomentIndex gapHalf = block.leftGap := by
      apply Fin.ext
      rfl
    simpa only [heq] using block.leftGap_mem
  apply Fin.ext
  apply le_antisymm
  · have hmaxMem : A.max' hA ∈ A := Finset.max'_mem A hA
    have hcarrier := mem_r324LeftHalfPullback.mp hmaxMem
    have hpart : leftMomentIndex (A.max' hA) ∈
        r324CrossLeftPart m block.carrier := by
      exact Finset.mem_filter.mpr ⟨hcarrier, (A.max' hA).isLt⟩
    exact Fin.mk_le_mk.mpr
      (Finset.le_max' (r324CrossLeftPart m block.carrier)
        (leftMomentIndex (A.max' hA)) hpart)
  · have hle : gapHalf ≤ A.max' hA :=
      Finset.le_max' A gapHalf hgapHalf
    exact Fin.mk_le_mk.mpr hle

/-- The terminal right index of the canonical cross gap is the minimum of
the pulled-back right carrier. -/
theorem rightMomentIndex_min'_r324RightHalfPullback
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (block : R324NestedCrossBlock κp κm π) :
    rightMomentIndex
        ((r324RightHalfPullback block.carrier).min'
          (r324RightHalfPullback_nonempty_of_crossCut block.crossCut)) =
      block.rightGap := by
  let A := r324RightHalfPullback block.carrier
  let hA : A.Nonempty :=
    r324RightHalfPullback_nonempty_of_crossCut block.crossCut
  let gapHalf : Fin m :=
    ⟨block.rightGap.val - m, by
      have hlt := block.rightGap.isLt
      omega⟩
  have hgapHalf : gapHalf ∈ A := by
    apply mem_r324RightHalfPullback.mpr
    have heq : rightMomentIndex gapHalf = block.rightGap := by
      apply Fin.ext
      dsimp only [gapHalf, rightMomentIndex]
      have hge : m ≤ block.rightGap.val :=
        r324CrossGapRight_ge_cut block.carrier block.crossCut
      omega
    simpa only [heq] using block.rightGap_mem
  apply Fin.ext
  change m + (A.min' hA).val = block.rightGap.val
  have hle : A.min' hA ≤ gapHalf :=
    Finset.min'_le A gapHalf hgapHalf
  have hminMem : A.min' hA ∈ A := Finset.min'_mem A hA
  have hcarrier := mem_r324RightHalfPullback.mp hminMem
  have hpart : rightMomentIndex (A.min' hA) ∈
      r324CrossRightPart m block.carrier := by
    exact Finset.mem_filter.mpr
      ⟨hcarrier, by simp [rightMomentIndex]⟩
  have hmin := Finset.min'_le
    (r324CrossRightPart m block.carrier)
    (rightMomentIndex (A.min' hA)) hpart
  have hge : m ≤ block.rightGap.val :=
    r324CrossGapRight_ge_cut block.carrier block.crossCut
  change (A.min' hA).val ≤ gapHalf.val at hle
  change block.rightGap.val ≤ m + (A.min' hA).val at hmin
  dsimp only [gapHalf] at hle
  omega

namespace R324NestedCrossProperStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- The increasing block enumeration starts at the carrier minimum. -/
theorem blockOrderIso_zero_eq_min'
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    (ctx.step.blockOrderIso
        ⟨0, by
          have horder := ctx.step.one_le_order
          omega⟩).1 =
      ctx.step.head.carrier.min'
        ⟨ctx.step.head.leftGap, ctx.step.head.leftGap_mem⟩ := by
  let hne : ctx.step.head.carrier.Nonempty :=
    ⟨ctx.step.head.leftGap, ctx.step.head.leftGap_mem⟩
  let carrierMin : ctx.step.head.carrier :=
    ⟨ctx.step.head.carrier.min' hne,
      Finset.min'_mem _ hne⟩
  obtain ⟨j, hj⟩ := ctx.step.blockOrderIso.surjective carrierMin
  apply le_antisymm
  · have hzeroLe :
        (⟨0, by
          have horder := ctx.step.one_le_order
          omega⟩ : Fin (2 * ctx.step.order)) ≤ j := by
      change 0 ≤ j.val
      omega
    have hmono := ctx.step.blockOrderIso.monotone hzeroLe
    rw [hj] at hmono
    exact hmono
  · exact Finset.min'_le _ _
      (ctx.step.blockOrderIso
        ⟨0, by
          have horder := ctx.step.one_le_order
          omega⟩).2

/-- The increasing block enumeration ends at the carrier maximum. -/
theorem blockOrderIso_last_eq_max'
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    (ctx.step.blockOrderIso
        (primitiveLast ctx.step.order ctx.step.one_le_order)).1 =
      ctx.step.head.carrier.max'
        ⟨ctx.step.head.rightGap, ctx.step.head.rightGap_mem⟩ := by
  let hne : ctx.step.head.carrier.Nonempty :=
    ⟨ctx.step.head.rightGap, ctx.step.head.rightGap_mem⟩
  let carrierMax : ctx.step.head.carrier :=
    ⟨ctx.step.head.carrier.max' hne,
      Finset.max'_mem _ hne⟩
  obtain ⟨j, hj⟩ := ctx.step.blockOrderIso.surjective carrierMax
  apply le_antisymm
  · exact Finset.le_max' _ _
      (ctx.step.blockOrderIso
        (primitiveLast ctx.step.order ctx.step.one_le_order)).2
  · have hjLast :
        j ≤ primitiveLast ctx.step.order ctx.step.one_le_order := by
      change j.val ≤ 2 * ctx.step.order - 1
      have hjlt := j.isLt
      omega
    have hmono := ctx.step.blockOrderIso.monotone hjLast
    rw [hj] at hmono
    exact hmono

/-- In the increasing standard block order the two canonical gap sites
are adjacent. There is no shell vertex between the last left site and the
first right site. -/
theorem leftGapIndex_add_one_eq_rightGapIndex
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    ctx.step.leftGapIndex.val + 1 =
      ctx.step.rightGapIndex.val := by
  have hlt := ctx.step.leftGapIndex_lt_rightGapIndex
  by_contra hne
  have hstrict :
      ctx.step.leftGapIndex.val + 1 <
        ctx.step.rightGapIndex.val := by
    change ctx.step.leftGapIndex.val <
      ctx.step.rightGapIndex.val at hlt
    omega
  let j : Fin (2 * ctx.step.order) :=
    ⟨ctx.step.leftGapIndex.val + 1, by
      exact hstrict.trans ctx.step.rightGapIndex.isLt⟩
  have hleftJ : ctx.step.leftGapIndex < j := by
    change ctx.step.leftGapIndex.val <
      ctx.step.leftGapIndex.val + 1
    omega
  have hjRight : j < ctx.step.rightGapIndex := by
    exact Fin.mk_lt_mk.mpr hstrict
  have himageLeft := ctx.step.blockOrderIso.strictMono hleftJ
  have himageRight := ctx.step.blockOrderIso.strictMono hjRight
  rw [ctx.step.blockOrderIso_leftGapIndex] at himageLeft
  rw [ctx.step.blockOrderIso_rightGapIndex] at himageRight
  by_cases hcut : (ctx.step.blockOrderIso j).1.val < m
  · have hpart : (ctx.step.blockOrderIso j).1 ∈
        r324CrossLeftPart m ctx.step.head.carrier :=
      Finset.mem_filter.mpr
        ⟨(ctx.step.blockOrderIso j).2, hcut⟩
    have hle := Finset.le_max'
      (r324CrossLeftPart m ctx.step.head.carrier)
      (ctx.step.blockOrderIso j).1 hpart
    exact (not_le_of_gt himageLeft) hle
  · have hge : m ≤ (ctx.step.blockOrderIso j).1.val := by
      omega
    have hpart : (ctx.step.blockOrderIso j).1 ∈
        r324CrossRightPart m ctx.step.head.carrier :=
      Finset.mem_filter.mpr
        ⟨(ctx.step.blockOrderIso j).2, hge⟩
    have hle := Finset.min'_le
      (r324CrossRightPart m ctx.step.head.carrier)
      (ctx.step.blockOrderIso j).1 hpart
    exact (not_le_of_gt himageRight) hle

private theorem head_outward_of_mem_tail
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (block : R324NestedCrossBlock κp κm π)
    (hblock : block ∈ ctx.step.tail) :
    R324HalfCarrierOutward
      ctx.step.head.carrier block.carrier := by
  have hfull := r324NestedCrossSchedule_pairwise_halfOutward κp κm π
  rw [ctx.step.residual.schedule_eq, ctx.step.remaining_eq,
    List.pairwise_append] at hfull
  have hremaining :
      (ctx.step.head :: ctx.step.tail).Pairwise
        (fun inner outer =>
          R324HalfCarrierOutward inner.carrier outer.carrier) :=
    hfull.2.1
  exact (List.pairwise_cons.mp hremaining).1 block hblock

private theorem nextHead_outward_of_mem_rest
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (block : R324NestedCrossBlock κp κm π)
    (hblock : block ∈ ctx.rest) :
    R324HalfCarrierOutward
      ctx.nextHead.carrier block.carrier := by
  have hfull := r324NestedCrossSchedule_pairwise_halfOutward κp κm π
  rw [ctx.step.residual.schedule_eq, ctx.step.remaining_eq,
    ctx.tail_eq, List.pairwise_append] at hfull
  have hsuffix :
      (ctx.step.head :: ctx.nextHead :: ctx.rest).Pairwise
        (fun inner outer =>
          R324HalfCarrierOutward inner.carrier outer.carrier) :=
    hfull.2.1
  have hnext := (List.pairwise_cons.mp hsuffix).2
  exact (List.pairwise_cons.mp hnext).1 block hblock

/-- In the left terminal half, every post-head vertex precedes every
current-head vertex. -/
theorem leftPost_before_head
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    R324WithinHalfResidualPrefix.HalfCarrierBefore
      (r324LeftHalfPullback ctx.step.next.activeCarrier)
      (r324LeftHalfPullback ctx.step.head.carrier) := by
  intro i hi j hj
  have hiDoubled := mem_r324LeftHalfPullback.mp hi
  unfold R324NestedCrossResidualPrefix.activeCarrier at hiDoubled
  obtain ⟨carrier, hcarrier, hiCarrier⟩ :=
    (mem_finsetUnionList_iff _).mp hiDoubled
  obtain ⟨block, hblock, rfl⟩ := List.mem_map.mp hcarrier
  exact (ctx.head_outward_of_mem_tail block hblock).1 i
    (mem_r324LeftHalfPullback.mpr hiCarrier) j hj

/-- In the right terminal half, every current-head vertex precedes every
post-head vertex. -/
theorem rightHead_before_post
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    R324WithinHalfResidualPrefix.HalfCarrierBefore
      (r324RightHalfPullback ctx.step.head.carrier)
      (r324RightHalfPullback ctx.step.next.activeCarrier) := by
  intro i hi j hj
  have hjDoubled := mem_r324RightHalfPullback.mp hj
  unfold R324NestedCrossResidualPrefix.activeCarrier at hjDoubled
  obtain ⟨carrier, hcarrier, hjCarrier⟩ :=
    (mem_finsetUnionList_iff _).mp hjDoubled
  obtain ⟨block, hblock, rfl⟩ := List.mem_map.mp hcarrier
  exact (ctx.head_outward_of_mem_tail block hblock).2 i hi j
    (mem_r324RightHalfPullback.mpr hjCarrier)

theorem leftCurrent_eq_post_union_head
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    r324LeftHalfPullback ctx.step.residual.activeCarrier =
      r324LeftHalfPullback ctx.step.next.activeCarrier ∪
        r324LeftHalfPullback ctx.step.head.carrier := by
  rw [ctx.step.residual.activeCarrier_head
    ctx.step.head ctx.step.tail ctx.step.remaining_eq,
    r324LeftHalfPullback_union, Finset.union_comm]
  rfl

theorem rightCurrent_eq_head_union_post
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    r324RightHalfPullback ctx.step.residual.activeCarrier =
      r324RightHalfPullback ctx.step.head.carrier ∪
        r324RightHalfPullback ctx.step.next.activeCarrier := by
  rw [ctx.step.residual.activeCarrier_head
    ctx.step.head ctx.step.tail ctx.step.remaining_eq,
    r324RightHalfPullback_union]
  rfl

theorem leftHead_nonempty
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    (r324LeftHalfPullback ctx.step.head.carrier).Nonempty :=
  r324LeftHalfPullback_nonempty_of_crossCut ctx.step.head.crossCut

theorem rightHead_nonempty
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    (r324RightHalfPullback ctx.step.head.carrier).Nonempty :=
  r324RightHalfPullback_nonempty_of_crossCut ctx.step.head.crossCut

theorem leftPost_nonempty
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    (r324LeftHalfPullback ctx.step.next.activeCarrier).Nonempty := by
  have hnext :=
    r324LeftHalfPullback_nonempty_of_crossCut ctx.nextHead.crossCut
  exact hnext.mono fun i hi => by
    apply mem_r324LeftHalfPullback.mpr
    exact ctx.nextContext.head_subset_activeCarrier
      (mem_r324LeftHalfPullback.mp hi)

theorem rightPost_nonempty
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    (r324RightHalfPullback ctx.step.next.activeCarrier).Nonempty := by
  have hnext :=
    r324RightHalfPullback_nonempty_of_crossCut ctx.nextHead.crossCut
  exact hnext.mono fun i hi => by
    apply mem_r324RightHalfPullback.mpr
    exact ctx.nextContext.head_subset_activeCarrier
      (mem_r324RightHalfPullback.mp hi)

theorem leftCurrent_nonempty
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    (r324LeftHalfPullback ctx.step.residual.activeCarrier).Nonempty :=
  ctx.leftHead_nonempty.mono fun i hi => by
    apply mem_r324LeftHalfPullback.mpr
    exact ctx.step.head_subset_activeCarrier
      (mem_r324LeftHalfPullback.mp hi)

theorem rightCurrent_nonempty
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    (r324RightHalfPullback ctx.step.residual.activeCarrier).Nonempty :=
  ctx.rightHead_nonempty.mono fun i hi => by
    apply mem_r324RightHalfPullback.mpr
    exact ctx.step.head_subset_activeCarrier
      (mem_r324RightHalfPullback.mp hi)

/-- The first left-half vertex of the current shell is its standard
coordinate `0`. -/
theorem leftMomentIndex_leftHead_min'
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    leftMomentIndex
        ((r324LeftHalfPullback ctx.step.head.carrier).min'
          ctx.leftHead_nonempty) =
      (ctx.step.blockOrderIso
        ⟨0, by
          have horder := ctx.step.one_le_order
          omega⟩).1 := by
  let B := ctx.step.head.carrier
  let hB : B.Nonempty :=
    ⟨ctx.step.head.leftGap, ctx.step.head.leftGap_mem⟩
  let carrierMin := B.min' hB
  have hcarrierMinCut : carrierMin.val < m := by
    have hle := Finset.min'_le B ctx.step.head.leftGap
      ctx.step.head.leftGap_mem
    have hcut := r324CrossGapLeft_lt_cut
      ctx.step.head.carrier ctx.step.head.crossCut
    exact lt_of_le_of_lt hle hcut
  let minHalf : Fin m := ⟨carrierMin.val, hcarrierMinCut⟩
  have hminHalfMem :
      minHalf ∈ r324LeftHalfPullback ctx.step.head.carrier := by
    apply mem_r324LeftHalfPullback.mpr
    have heq : leftMomentIndex minHalf = carrierMin := by
      apply Fin.ext
      rfl
    rw [heq]
    exact Finset.min'_mem B hB
  have hpullMinMem := Finset.min'_mem
    (r324LeftHalfPullback ctx.step.head.carrier)
    ctx.leftHead_nonempty
  have hpullCarrier := mem_r324LeftHalfPullback.mp hpullMinMem
  have hcarrierLe := Finset.min'_le B
    (leftMomentIndex
      ((r324LeftHalfPullback ctx.step.head.carrier).min'
        ctx.leftHead_nonempty)) hpullCarrier
  have hpullLe := Finset.min'_le
    (r324LeftHalfPullback ctx.step.head.carrier)
    minHalf hminHalfMem
  rw [ctx.blockOrderIso_zero_eq_min']
  apply Fin.ext
  change
    ((r324LeftHalfPullback ctx.step.head.carrier).min'
      ctx.leftHead_nonempty).val = carrierMin.val
  change carrierMin.val ≤
    ((r324LeftHalfPullback ctx.step.head.carrier).min'
      ctx.leftHead_nonempty).val at hcarrierLe
  change
    ((r324LeftHalfPullback ctx.step.head.carrier).min'
      ctx.leftHead_nonempty).val ≤ minHalf.val at hpullLe
  exact le_antisymm hpullLe hcarrierLe

/-- The last right-half vertex of the current shell is its final standard
coordinate. -/
theorem rightMomentIndex_rightHead_max'
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    rightMomentIndex
        ((r324RightHalfPullback ctx.step.head.carrier).max'
          ctx.rightHead_nonempty) =
      (ctx.step.blockOrderIso
        (primitiveLast ctx.step.order ctx.step.one_le_order)).1 := by
  let B := ctx.step.head.carrier
  let hB : B.Nonempty :=
    ⟨ctx.step.head.rightGap, ctx.step.head.rightGap_mem⟩
  let carrierMax := B.max' hB
  have hcarrierMaxGe : m ≤ carrierMax.val := by
    have hle := Finset.le_max' B ctx.step.head.rightGap
      ctx.step.head.rightGap_mem
    have hcut := r324CrossGapRight_ge_cut
      ctx.step.head.carrier ctx.step.head.crossCut
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
      maxHalf ∈ r324RightHalfPullback ctx.step.head.carrier := by
    apply mem_r324RightHalfPullback.mpr
    rw [hmaxHalfMap]
    exact Finset.max'_mem B hB
  have hpullMaxMem := Finset.max'_mem
    (r324RightHalfPullback ctx.step.head.carrier)
    ctx.rightHead_nonempty
  have hpullCarrier := mem_r324RightHalfPullback.mp hpullMaxMem
  have hpullLe := Finset.le_max' B
    (rightMomentIndex
      ((r324RightHalfPullback ctx.step.head.carrier).max'
        ctx.rightHead_nonempty)) hpullCarrier
  have hmaxHalfLe := Finset.le_max'
    (r324RightHalfPullback ctx.step.head.carrier)
    maxHalf hmaxHalfMem
  rw [ctx.blockOrderIso_last_eq_max']
  apply Fin.ext
  change
    m + ((r324RightHalfPullback ctx.step.head.carrier).max'
      ctx.rightHead_nonempty).val = carrierMax.val
  change
    m + ((r324RightHalfPullback ctx.step.head.carrier).max'
      ctx.rightHead_nonempty).val ≤ carrierMax.val at hpullLe
  change maxHalf.val ≤
    ((r324RightHalfPullback ctx.step.head.carrier).max'
      ctx.rightHead_nonempty).val at hmaxHalfLe
  dsimp only [maxHalf] at hmaxHalfLe
  omega

/-- The outermost left vertex still present after the current head is the
left central-gap vertex of the next literal block. -/
theorem leftMomentIndex_leftPost_max'
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    leftMomentIndex
        ((r324LeftHalfPullback ctx.step.next.activeCarrier).max'
          ctx.leftPost_nonempty) =
      ctx.nextHead.leftGap := by
  let nextA := r324LeftHalfPullback ctx.nextHead.carrier
  let hnextA : nextA.Nonempty :=
    r324LeftHalfPullback_nonempty_of_crossCut ctx.nextHead.crossCut
  let gapHalf : Fin m := nextA.max' hnextA
  have hgapMap : leftMomentIndex gapHalf = ctx.nextHead.leftGap := by
    exact leftMomentIndex_max'_r324LeftHalfPullback ctx.nextHead
  have hgapPost :
      gapHalf ∈ r324LeftHalfPullback ctx.step.next.activeCarrier := by
    apply mem_r324LeftHalfPullback.mpr
    rw [hgapMap]
    exact ctx.nextContext.head_subset_activeCarrier
      ctx.nextHead.leftGap_mem
  have hupper :
      ∀ i ∈ r324LeftHalfPullback ctx.step.next.activeCarrier,
        i ≤ gapHalf := by
    intro i hi
    have hiDoubled := mem_r324LeftHalfPullback.mp hi
    unfold R324NestedCrossResidualPrefix.activeCarrier at hiDoubled
    obtain ⟨carrier, hcarrier, hiCarrier⟩ :=
      (mem_finsetUnionList_iff _).mp hiDoubled
    obtain ⟨block, hblock, rfl⟩ := List.mem_map.mp hcarrier
    change block ∈ ctx.step.tail at hblock
    rw [ctx.tail_eq] at hblock
    rcases List.mem_cons.mp hblock with rfl | hrest
    · exact Finset.le_max' nextA i
        (mem_r324LeftHalfPullback.mpr hiCarrier)
    · exact (ctx.nextHead_outward_of_mem_rest block hrest).1 i
        (mem_r324LeftHalfPullback.mpr hiCarrier) gapHalf
        (Finset.max'_mem nextA hnextA) |>.le
  have heq :
      (r324LeftHalfPullback ctx.step.next.activeCarrier).max'
          ctx.leftPost_nonempty = gapHalf := by
    apply le_antisymm
    · exact hupper _ (Finset.max'_mem _ ctx.leftPost_nonempty)
    · exact Finset.le_max' _ gapHalf hgapPost
  rw [heq, hgapMap]

/-- The innermost right vertex still present after the current head is the
right central-gap vertex of the next literal block. -/
theorem rightMomentIndex_rightPost_min'
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    rightMomentIndex
        ((r324RightHalfPullback ctx.step.next.activeCarrier).min'
          ctx.rightPost_nonempty) =
      ctx.nextHead.rightGap := by
  let nextA := r324RightHalfPullback ctx.nextHead.carrier
  let hnextA : nextA.Nonempty :=
    r324RightHalfPullback_nonempty_of_crossCut ctx.nextHead.crossCut
  let gapHalf : Fin m := nextA.min' hnextA
  have hgapMap : rightMomentIndex gapHalf = ctx.nextHead.rightGap := by
    exact rightMomentIndex_min'_r324RightHalfPullback ctx.nextHead
  have hgapPost :
      gapHalf ∈ r324RightHalfPullback ctx.step.next.activeCarrier := by
    apply mem_r324RightHalfPullback.mpr
    rw [hgapMap]
    exact ctx.nextContext.head_subset_activeCarrier
      ctx.nextHead.rightGap_mem
  have hlower :
      ∀ i ∈ r324RightHalfPullback ctx.step.next.activeCarrier,
        gapHalf ≤ i := by
    intro i hi
    have hiDoubled := mem_r324RightHalfPullback.mp hi
    unfold R324NestedCrossResidualPrefix.activeCarrier at hiDoubled
    obtain ⟨carrier, hcarrier, hiCarrier⟩ :=
      (mem_finsetUnionList_iff _).mp hiDoubled
    obtain ⟨block, hblock, rfl⟩ := List.mem_map.mp hcarrier
    change block ∈ ctx.step.tail at hblock
    rw [ctx.tail_eq] at hblock
    rcases List.mem_cons.mp hblock with rfl | hrest
    · exact Finset.min'_le nextA i
        (mem_r324RightHalfPullback.mpr hiCarrier)
    · exact (ctx.nextHead_outward_of_mem_rest block hrest).2 gapHalf
        (Finset.min'_mem nextA hnextA) i
        (mem_r324RightHalfPullback.mpr hiCarrier) |>.le
  have heq :
      (r324RightHalfPullback ctx.step.next.activeCarrier).min'
          ctx.rightPost_nonempty = gapHalf := by
    apply le_antisymm
    · exact Finset.min'_le _ gapHalf hgapPost
    · exact hlower _ (Finset.min'_mem _ ctx.rightPost_nonempty)
  rw [heq, hgapMap]

end R324NestedCrossProperStepContext

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- A local successor criterion inside the full sparse terminal chain.
Unlike `edgeSuccessor_connector_eq_varIdx_min'`, this version does not
require the two displayed carriers to exhaust the active state: it is
enough to certify that no active vertex lies strictly between the source
and target. -/
theorem edgeSuccessor_internalVertex_eq_varIdx_of_no_between
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (source target : Fin m)
    (htarget : target ∈ res.state.active)
    (hlt : source < target)
    (hnoBetween :
      ∀ k ∈ res.state.active, source < k → target ≤ k) :
    res.edgeSuccessor (r324InternalVertexEdgeSlot source) =
      varIdx target := by
  unfold edgeSuccessor
  rw [Finset.min'_eq_iff]
  constructor
  · rw [edgeSuccessorCandidates]
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨target, Finset.mem_filter.mpr ⟨htarget, ?_⟩, rfl⟩
    simp only [r324InternalVertexEdgeSlot, varIdx_val]
    exact Nat.add_lt_add_right hlt 1
  · intro candidate hcandidate
    rw [edgeSuccessorCandidates] at hcandidate
    rcases Finset.mem_union.mp hcandidate with hlast | hinter
    · have hc : candidate = Fin.last (m + 1) := by
        simpa only [Finset.mem_singleton] using hlast
      rw [hc]
      exact Fin.le_last _
    · obtain ⟨k, hk, hkcandidate⟩ := Finset.mem_image.mp hinter
      have hkActive := (Finset.mem_filter.mp hk).1
      have hkAfter := (Finset.mem_filter.mp hk).2
      have hsourceLt : source < k := by
        simp only [r324InternalVertexEdgeSlot, varIdx_val] at hkAfter
        exact Fin.mk_lt_mk.mpr (by omega)
      have htargetLe := hnoBetween k hkActive hsourceLt
      rw [← hkcandidate]
      exact Fin.mk_le_mk.mpr
        (Nat.succ_le_succ htargetLe)

end R324WithinHalfResidualPrefix

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)

private theorem left_mem_terminal_of_mem_nestedBlock
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

private theorem right_mem_terminal_of_mem_nestedBlock
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

private theorem left_terminal_active_mem_scheduleCarrier
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
  have hiInitial :
      leftMomentIndex i ∈
        (R324NestedCrossResidualPrefix.initial κp κm π).activeCarrier := by
    rw [R324NestedCrossResidualPrefix.initial_activeCarrier_eq_momentResidualActive]
    exact hiMoment
  unfold R324NestedCrossResidualPrefix.activeCarrier
    R324NestedCrossResidualPrefix.initial at hiInitial
  obtain ⟨carrier, hcarrier, hiCarrier⟩ :=
    (mem_finsetUnionList_iff _).mp hiInitial
  obtain ⟨block, hblock, rfl⟩ := List.mem_map.mp hcarrier
  exact ⟨block, hblock, hiCarrier⟩

private theorem right_terminal_active_mem_scheduleCarrier
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
  have hiInitial :
      rightMomentIndex i ∈
        (R324NestedCrossResidualPrefix.initial κp κm π).activeCarrier := by
    rw [R324NestedCrossResidualPrefix.initial_activeCarrier_eq_momentResidualActive]
    exact hiMoment
  unfold R324NestedCrossResidualPrefix.activeCarrier
    R324NestedCrossResidualPrefix.initial at hiInitial
  obtain ⟨carrier, hcarrier, hiCarrier⟩ :=
    (mem_finsetUnionList_iff _).mp hiInitial
  obtain ⟨block, hblock, rfl⟩ := List.mem_map.mp hcarrier
  exact ⟨block, hblock, hiCarrier⟩

private theorem leftConnector_no_terminal_active_between
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    ∀ k ∈ terminal.left.state.active,
      (r324LeftHalfPullback ctx.step.next.activeCarrier).max'
          ctx.leftPost_nonempty < k →
        (r324LeftHalfPullback ctx.step.head.carrier).min'
            ctx.leftHead_nonempty ≤ k := by
  intro k hk hsourceLt
  obtain ⟨block, hblockSchedule, hkCarrier⟩ :=
    terminal.left_terminal_active_mem_scheduleCarrier k hk
  have hfull := r324NestedCrossSchedule_pairwise_halfOutward κp κm π
  rw [ctx.step.residual.schedule_eq, ctx.step.remaining_eq,
    List.pairwise_append] at hfull
  rw [ctx.step.residual.schedule_eq, ctx.step.remaining_eq] at hblockSchedule
  rcases List.mem_append.mp hblockSchedule with hprocessed | hremaining
  · have hrel := hfull.2.2 block hprocessed ctx.step.head (by simp)
    exact (hrel.1
      ((r324LeftHalfPullback ctx.step.head.carrier).min'
        ctx.leftHead_nonempty)
      (Finset.min'_mem _ ctx.leftHead_nonempty) k
      (mem_r324LeftHalfPullback.mpr hkCarrier)).le
  · rcases List.mem_cons.mp hremaining with rfl | htail
    · exact Finset.min'_le _ k
        (mem_r324LeftHalfPullback.mpr hkCarrier)
    · have hkPost :
          k ∈ r324LeftHalfPullback ctx.step.next.activeCarrier := by
        apply mem_r324LeftHalfPullback.mpr
        unfold R324NestedCrossResidualPrefix.activeCarrier
        exact (mem_finsetUnionList_iff _).mpr
          ⟨block.carrier,
            List.mem_map.mpr ⟨block, htail, rfl⟩,
            hkCarrier⟩
      have hkLe := Finset.le_max'
        (r324LeftHalfPullback ctx.step.next.activeCarrier) k hkPost
      exact (not_lt_of_ge hkLe hsourceLt).elim

private theorem rightConnector_no_terminal_active_between
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    ∀ k ∈ terminal.right.state.active,
      (r324RightHalfPullback ctx.step.head.carrier).max'
          ctx.rightHead_nonempty < k →
        (r324RightHalfPullback ctx.step.next.activeCarrier).min'
            ctx.rightPost_nonempty ≤ k := by
  intro k hk hsourceLt
  obtain ⟨block, hblockSchedule, hkCarrier⟩ :=
    terminal.right_terminal_active_mem_scheduleCarrier k hk
  have hfull := r324NestedCrossSchedule_pairwise_halfOutward κp κm π
  rw [ctx.step.residual.schedule_eq, ctx.step.remaining_eq,
    List.pairwise_append] at hfull
  rw [ctx.step.residual.schedule_eq, ctx.step.remaining_eq] at hblockSchedule
  rcases List.mem_append.mp hblockSchedule with hprocessed | hremaining
  · have hrel := hfull.2.2 block hprocessed ctx.step.head (by simp)
    have hkLt := hrel.2 k
      (mem_r324RightHalfPullback.mpr hkCarrier)
      ((r324RightHalfPullback ctx.step.head.carrier).max'
        ctx.rightHead_nonempty)
      (Finset.max'_mem _ ctx.rightHead_nonempty)
    exact (not_lt_of_ge hsourceLt.le hkLt).elim
  · rcases List.mem_cons.mp hremaining with rfl | htail
    · have hkLe := Finset.le_max'
        (r324RightHalfPullback ctx.step.head.carrier) k
        (mem_r324RightHalfPullback.mpr hkCarrier)
      exact (not_lt_of_ge hkLe hsourceLt).elim
    · have hkPost :
          k ∈ r324RightHalfPullback ctx.step.next.activeCarrier := by
        apply mem_r324RightHalfPullback.mpr
        unfold R324NestedCrossResidualPrefix.activeCarrier
        exact (mem_finsetUnionList_iff _).mpr
          ⟨block.carrier,
            List.mem_map.mpr ⟨block, htail, rfl⟩,
            hkCarrier⟩
      exact Finset.min'_le _ k hkPost

/-- The terminal left-chain connector slot really targets the outermost
left coordinate of the current shell. -/
theorem left_edgeSuccessor_connector
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    terminal.left.edgeSuccessor
        (r324InternalVertexEdgeSlot
          ((r324LeftHalfPullback ctx.step.next.activeCarrier).max'
            ctx.leftPost_nonempty)) =
      varIdx
        ((r324LeftHalfPullback ctx.step.head.carrier).min'
          ctx.leftHead_nonempty) := by
  let source :=
    (r324LeftHalfPullback ctx.step.next.activeCarrier).max'
      ctx.leftPost_nonempty
  let target :=
    (r324LeftHalfPullback ctx.step.head.carrier).min'
      ctx.leftHead_nonempty
  have htargetCarrier :
      leftMomentIndex target ∈ ctx.step.head.carrier :=
    mem_r324LeftHalfPullback.mp
      (Finset.min'_mem _ ctx.leftHead_nonempty)
  have htargetActive : target ∈ terminal.left.state.active :=
    terminal.left_mem_terminal_of_mem_nestedBlock
      ctx.step.head target htargetCarrier
  have hlt : source < target :=
    ctx.leftPost_before_head source
      (Finset.max'_mem _ ctx.leftPost_nonempty)
      target (Finset.min'_mem _ ctx.leftHead_nonempty)
  exact terminal.left.edgeSuccessor_internalVertex_eq_varIdx_of_no_between
    source target htargetActive hlt
    (terminal.leftConnector_no_terminal_active_between ctx)

/-- Right-chain connector successor. -/
theorem right_edgeSuccessor_connector
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π) :
    terminal.right.edgeSuccessor
        (r324InternalVertexEdgeSlot
          ((r324RightHalfPullback ctx.step.head.carrier).max'
            ctx.rightHead_nonempty)) =
      varIdx
        ((r324RightHalfPullback ctx.step.next.activeCarrier).min'
          ctx.rightPost_nonempty) := by
  let source :=
    (r324RightHalfPullback ctx.step.head.carrier).max'
      ctx.rightHead_nonempty
  let target :=
    (r324RightHalfPullback ctx.step.next.activeCarrier).min'
      ctx.rightPost_nonempty
  have htargetCarrier :
      rightMomentIndex target ∈ ctx.nextHead.carrier := by
    rw [ctx.rightMomentIndex_rightPost_min']
    exact ctx.nextHead.rightGap_mem
  have htargetActive : target ∈ terminal.right.state.active :=
    terminal.right_mem_terminal_of_mem_nestedBlock
      ctx.nextHead target htargetCarrier
  have hlt : source < target :=
    ctx.rightHead_before_post source
      (Finset.max'_mem _ ctx.rightHead_nonempty)
      target (Finset.min'_mem _ ctx.rightPost_nonempty)
  exact terminal.right.edgeSuccessor_internalVertex_eq_varIdx_of_no_between
    source target htargetActive hlt
    (terminal.rightConnector_no_terminal_active_between ctx)

/-- Coordinate identity for the left flanking leg of paper Step 3. -/
theorem left_connector_edgeDisplacement_eq
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (v : ctx.step.SurvivingCoordinate → T4) :
    terminal.left.edgeDisplacement 0 0
        (terminal.left.reconstruct
          (fun i =>
            ctx.step.reconstruct v (leftMomentIndex i.1)))
        (r324InternalVertexEdgeSlot
          ((r324LeftHalfPullback ctx.step.next.activeCarrier).max'
            ctx.leftPost_nonempty)) =
      (ctx.step.splitSurvivingPiMeasurableEquiv v).2
          ctx.nextLeftPostCoordinate -
        (ctx.step.splitSurvivingPiMeasurableEquiv v).1
          ⟨0, by
            have horder := ctx.step.one_le_order
            omega⟩ := by
  let source :=
    (r324LeftHalfPullback ctx.step.next.activeCarrier).max'
      ctx.leftPost_nonempty
  let target :=
    (r324LeftHalfPullback ctx.step.head.carrier).min'
      ctx.leftHead_nonempty
  have hsourceCarrier :
      leftMomentIndex source ∈ ctx.nextHead.carrier := by
    rw [ctx.leftMomentIndex_leftPost_max']
    exact ctx.nextHead.leftGap_mem
  have htargetCarrier :
      leftMomentIndex target ∈ ctx.step.head.carrier :=
    mem_r324LeftHalfPullback.mp
      (Finset.min'_mem _ ctx.leftHead_nonempty)
  have hsourceActive : source ∈ terminal.left.state.active :=
    terminal.left_mem_terminal_of_mem_nestedBlock
      ctx.nextHead source hsourceCarrier
  have htargetActive : target ∈ terminal.left.state.active :=
    terminal.left_mem_terminal_of_mem_nestedBlock
      ctx.step.head target htargetCarrier
  have hsourceSlot :
      (r324InternalVertexEdgeSlot source).castSucc =
        varIdx source := by
    apply Fin.ext
    rfl
  unfold R324WithinHalfResidualPrefix.edgeDisplacement
  rw [hsourceSlot, terminal.left_edgeSuccessor_connector ctx,
    assemble_varIdx, assemble_varIdx,
    terminal.left.reconstruct_surviving
      (fun i =>
        ctx.step.reconstruct v (leftMomentIndex i.1))
      ⟨source, hsourceActive⟩,
    terminal.left.reconstruct_surviving
      (fun i =>
        ctx.step.reconstruct v (leftMomentIndex i.1))
      ⟨target, htargetActive⟩]
  change
    ctx.step.reconstruct v (leftMomentIndex source) -
        ctx.step.reconstruct v (leftMomentIndex target) = _
  rw [ctx.leftMomentIndex_leftPost_max',
    ctx.leftMomentIndex_leftHead_min']
  have hpost :
      ctx.step.reconstruct v ctx.nextHead.leftGap =
        (ctx.step.splitSurvivingPiMeasurableEquiv v).2
          ctx.nextLeftPostCoordinate := by
    rw [ctx.step.splitSurvivingPiMeasurableEquiv_apply_snd]
    rw [← ctx.step.reconstruct_surviving v
      (ctx.step.postSurvivingCoordinate
        ctx.nextLeftPostCoordinate)]
    rfl
  have hhead :
      ctx.step.reconstruct v
          (ctx.step.blockOrderIso
            ⟨0, by
              have horder := ctx.step.one_le_order
              omega⟩).1 =
        (ctx.step.splitSurvivingPiMeasurableEquiv v).1
          ⟨0, by
            have horder := ctx.step.one_le_order
            omega⟩ := by
    rw [ctx.step.splitSurvivingPiMeasurableEquiv_apply_fst]
    rw [← ctx.step.reconstruct_surviving v
      (ctx.step.headSurvivingCoordinate
        ⟨0, by
          have horder := ctx.step.one_le_order
          omega⟩)]
    rfl
  rw [hpost, hhead]

/-- Coordinate identity for the right flanking leg. -/
theorem right_connector_edgeDisplacement_eq
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (v : ctx.step.SurvivingCoordinate → T4) :
    terminal.right.edgeDisplacement 0 0
        (terminal.right.reconstruct
          (fun i =>
            ctx.step.reconstruct v (rightMomentIndex i.1)))
        (r324InternalVertexEdgeSlot
          ((r324RightHalfPullback ctx.step.head.carrier).max'
            ctx.rightHead_nonempty)) =
      (ctx.step.splitSurvivingPiMeasurableEquiv v).1
          (primitiveLast ctx.step.order ctx.step.one_le_order) -
        (ctx.step.splitSurvivingPiMeasurableEquiv v).2
          ctx.nextRightPostCoordinate := by
  let source :=
    (r324RightHalfPullback ctx.step.head.carrier).max'
      ctx.rightHead_nonempty
  let target :=
    (r324RightHalfPullback ctx.step.next.activeCarrier).min'
      ctx.rightPost_nonempty
  have hsourceCarrier :
      rightMomentIndex source ∈ ctx.step.head.carrier :=
    mem_r324RightHalfPullback.mp
      (Finset.max'_mem _ ctx.rightHead_nonempty)
  have htargetCarrier :
      rightMomentIndex target ∈ ctx.nextHead.carrier := by
    rw [ctx.rightMomentIndex_rightPost_min']
    exact ctx.nextHead.rightGap_mem
  have hsourceActive : source ∈ terminal.right.state.active :=
    terminal.right_mem_terminal_of_mem_nestedBlock
      ctx.step.head source hsourceCarrier
  have htargetActive : target ∈ terminal.right.state.active :=
    terminal.right_mem_terminal_of_mem_nestedBlock
      ctx.nextHead target htargetCarrier
  have hsourceSlot :
      (r324InternalVertexEdgeSlot source).castSucc =
        varIdx source := by
    apply Fin.ext
    rfl
  unfold R324WithinHalfResidualPrefix.edgeDisplacement
  rw [hsourceSlot, terminal.right_edgeSuccessor_connector ctx,
    assemble_varIdx, assemble_varIdx,
    terminal.right.reconstruct_surviving
      (fun i =>
        ctx.step.reconstruct v (rightMomentIndex i.1))
      ⟨source, hsourceActive⟩,
    terminal.right.reconstruct_surviving
      (fun i =>
        ctx.step.reconstruct v (rightMomentIndex i.1))
      ⟨target, htargetActive⟩]
  change
    ctx.step.reconstruct v (rightMomentIndex source) -
        ctx.step.reconstruct v (rightMomentIndex target) = _
  rw [ctx.rightMomentIndex_rightHead_max',
    ctx.rightMomentIndex_rightPost_min']
  have hhead :
      ctx.step.reconstruct v
          (ctx.step.blockOrderIso
            (primitiveLast ctx.step.order ctx.step.one_le_order)).1 =
        (ctx.step.splitSurvivingPiMeasurableEquiv v).1
          (primitiveLast ctx.step.order ctx.step.one_le_order) := by
    rw [ctx.step.splitSurvivingPiMeasurableEquiv_apply_fst]
    rw [← ctx.step.reconstruct_surviving v
      (ctx.step.headSurvivingCoordinate
        (primitiveLast ctx.step.order ctx.step.one_le_order))]
    rfl
  have hpost :
      ctx.step.reconstruct v ctx.nextHead.rightGap =
        (ctx.step.splitSurvivingPiMeasurableEquiv v).2
          ctx.nextRightPostCoordinate := by
    rw [ctx.step.splitSurvivingPiMeasurableEquiv_apply_snd]
    rw [← ctx.step.reconstruct_surviving v
      (ctx.step.postSurvivingCoordinate
        ctx.nextRightPostCoordinate)]
    rfl
  rw [hhead, hpost]

private theorem halfInvSqChainProduct_congr_carrier
    {pairing : PartialPairing (Fin m)}
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    {A B : Finset (Fin m)} (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : A = B) (v : res.SurvivingCoordinate → T4) :
    res.halfInvSqChainProduct A hA v =
      res.halfInvSqChainProduct B hB v := by
  subst B
  rfl

/-- Read a current nested tuple on the full terminal left carrier. Values
already removed by the nested suffix are filled by its canonical zero
reconstruction and never enter the current restricted slot product. -/
def leftTupleOfNestedStep
    {π : κp.singles ≃ κm.singles}
    (step : R324NestedCrossStepContext κp κm π)
    (v : step.SurvivingCoordinate → T4) :
    terminal.left.SurvivingCoordinate → T4 :=
  fun i => step.reconstruct v (leftMomentIndex i.1)

/-- Right-half analogue. -/
def rightTupleOfNestedStep
    {π : κp.singles ≃ κm.singles}
    (step : R324NestedCrossStepContext κp κm π)
    (v : step.SurvivingCoordinate → T4) :
    terminal.right.SurvivingCoordinate → T4 :=
  fun i => step.reconstruct v (rightMomentIndex i.1)

/-- Restricted terminal left path on a doubled nested carrier. -/
def nestedLeftHalfInvSqProduct
    {π : κp.singles ≃ κm.singles}
    (step : R324NestedCrossStepContext κp κm π)
    (carrier : Finset (Fin (2 * m)))
    (hne : (r324LeftHalfPullback carrier).Nonempty)
    (v : step.SurvivingCoordinate → T4) : ℝ :=
  terminal.left.halfInvSqChainProduct
    (r324LeftHalfPullback carrier) hne
    (terminal.leftTupleOfNestedStep step v)

/-- Restricted terminal right path. -/
def nestedRightHalfInvSqProduct
    {π : κp.singles ≃ κm.singles}
    (step : R324NestedCrossStepContext κp κm π)
    (carrier : Finset (Fin (2 * m)))
    (hne : (r324RightHalfPullback carrier).Nonempty)
    (v : step.SurvivingCoordinate → T4) : ℝ :=
  terminal.right.halfInvSqChainProduct
    (r324RightHalfPullback carrier) hne
    (terminal.rightTupleOfNestedStep step v)

/-- The exact left-half slot decomposition at an arbitrary proper nested
step. The displayed middle factor is the unique left connector leg. -/
theorem nestedLeftHalfInvSqProduct_current_eq
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (v : ctx.step.SurvivingCoordinate → T4) :
    terminal.nestedLeftHalfInvSqProduct ctx.step
        ctx.step.residual.activeCarrier ctx.leftCurrent_nonempty v =
      terminal.nestedLeftHalfInvSqProduct ctx.step
          ctx.step.next.activeCarrier ctx.leftPost_nonempty v *
        invSqKer
          (terminal.left.edgeDisplacement 0 0
            (terminal.left.reconstruct
              (terminal.leftTupleOfNestedStep ctx.step v))
            (r324InternalVertexEdgeSlot
              ((r324LeftHalfPullback
                ctx.step.next.activeCarrier).max'
                  ctx.leftPost_nonempty))) *
        terminal.nestedLeftHalfInvSqProduct ctx.step
          ctx.step.head.carrier ctx.leftHead_nonempty v := by
  unfold nestedLeftHalfInvSqProduct
  calc
    terminal.left.halfInvSqChainProduct
          (r324LeftHalfPullback ctx.step.residual.activeCarrier)
          ctx.leftCurrent_nonempty
          (terminal.leftTupleOfNestedStep ctx.step v) =
        terminal.left.halfInvSqChainProduct
          (r324LeftHalfPullback ctx.step.next.activeCarrier ∪
            r324LeftHalfPullback ctx.step.head.carrier)
          (ctx.leftPost_nonempty.mono Finset.subset_union_left)
          (terminal.leftTupleOfNestedStep ctx.step v) :=
      halfInvSqChainProduct_congr_carrier terminal.left
        ctx.leftCurrent_nonempty
        (ctx.leftPost_nonempty.mono Finset.subset_union_left)
        ctx.leftCurrent_eq_post_union_head
        (terminal.leftTupleOfNestedStep ctx.step v)
    _ = _ :=
      terminal.left.halfInvSqChainProduct_union_eq_threeWay_of_before
        (r324LeftHalfPullback ctx.step.next.activeCarrier)
        (r324LeftHalfPullback ctx.step.head.carrier)
        ctx.leftPost_nonempty ctx.leftHead_nonempty ctx.leftPost_before_head
        (terminal.leftTupleOfNestedStep ctx.step v)

/-- Exact right-half decomposition; here the current head precedes the
post carrier. -/
theorem nestedRightHalfInvSqProduct_current_eq
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (v : ctx.step.SurvivingCoordinate → T4) :
    terminal.nestedRightHalfInvSqProduct ctx.step
        ctx.step.residual.activeCarrier ctx.rightCurrent_nonempty v =
      terminal.nestedRightHalfInvSqProduct ctx.step
          ctx.step.head.carrier ctx.rightHead_nonempty v *
        invSqKer
          (terminal.right.edgeDisplacement 0 0
            (terminal.right.reconstruct
              (terminal.rightTupleOfNestedStep ctx.step v))
            (r324InternalVertexEdgeSlot
              ((r324RightHalfPullback
                ctx.step.head.carrier).max'
                  ctx.rightHead_nonempty))) *
        terminal.nestedRightHalfInvSqProduct ctx.step
          ctx.step.next.activeCarrier ctx.rightPost_nonempty v := by
  unfold nestedRightHalfInvSqProduct
  calc
    terminal.right.halfInvSqChainProduct
          (r324RightHalfPullback ctx.step.residual.activeCarrier)
          ctx.rightCurrent_nonempty
          (terminal.rightTupleOfNestedStep ctx.step v) =
        terminal.right.halfInvSqChainProduct
          (r324RightHalfPullback ctx.step.head.carrier ∪
            r324RightHalfPullback ctx.step.next.activeCarrier)
          (ctx.rightHead_nonempty.mono Finset.subset_union_left)
          (terminal.rightTupleOfNestedStep ctx.step v) :=
      halfInvSqChainProduct_congr_carrier terminal.right
        ctx.rightCurrent_nonempty
        (ctx.rightHead_nonempty.mono Finset.subset_union_left)
        ctx.rightCurrent_eq_head_union_post
        (terminal.rightTupleOfNestedStep ctx.step v)
    _ = _ :=
      terminal.right.halfInvSqChainProduct_union_eq_threeWay_of_before
        (r324RightHalfPullback ctx.step.head.carrier)
        (r324RightHalfPullback ctx.step.next.activeCarrier)
        ctx.rightHead_nonempty ctx.rightPost_nonempty ctx.rightHead_before_post
        (terminal.rightTupleOfNestedStep ctx.step v)

/-- The two half paths together split as head paths, the two connector
legs, and post paths. No covariance sum has been expanded. -/
theorem nestedHalfInvSqProducts_current_eq_head_connector_post
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (v : ctx.step.SurvivingCoordinate → T4) :
    terminal.nestedLeftHalfInvSqProduct ctx.step
          ctx.step.residual.activeCarrier ctx.leftCurrent_nonempty v *
        terminal.nestedRightHalfInvSqProduct ctx.step
          ctx.step.residual.activeCarrier ctx.rightCurrent_nonempty v =
      (terminal.nestedLeftHalfInvSqProduct ctx.step
          ctx.step.head.carrier ctx.leftHead_nonempty v *
        terminal.nestedRightHalfInvSqProduct ctx.step
          ctx.step.head.carrier ctx.rightHead_nonempty v) *
      (invSqKer
          (terminal.left.edgeDisplacement 0 0
            (terminal.left.reconstruct
              (terminal.leftTupleOfNestedStep ctx.step v))
            (r324InternalVertexEdgeSlot
              ((r324LeftHalfPullback
                ctx.step.next.activeCarrier).max'
                  ctx.leftPost_nonempty))) *
        invSqKer
          (terminal.right.edgeDisplacement 0 0
            (terminal.right.reconstruct
              (terminal.rightTupleOfNestedStep ctx.step v))
            (r324InternalVertexEdgeSlot
              ((r324RightHalfPullback
                ctx.step.head.carrier).max'
                  ctx.rightHead_nonempty)))) *
      (terminal.nestedLeftHalfInvSqProduct ctx.step
          ctx.step.next.activeCarrier ctx.leftPost_nonempty v *
        terminal.nestedRightHalfInvSqProduct ctx.step
          ctx.step.next.activeCarrier ctx.rightPost_nonempty v) := by
  rw [terminal.nestedLeftHalfInvSqProduct_current_eq ctx v,
    terminal.nestedRightHalfInvSqProduct_current_eq ctx v]
  ring

/-- Paper Step 3 chain geometry in its exact named form: the two current
terminal half paths split into the current shell paths, `ctx.connector`'s
two flanking legs, and the unchanged post-shell paths. -/
theorem nestedHalfInvSqProducts_current_eq_head_connector_post_named
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossProperStepContext κp κm π)
    (v : ctx.step.SurvivingCoordinate → T4) :
    terminal.nestedLeftHalfInvSqProduct ctx.step
          ctx.step.residual.activeCarrier ctx.leftCurrent_nonempty v *
        terminal.nestedRightHalfInvSqProduct ctx.step
          ctx.step.residual.activeCarrier ctx.rightCurrent_nonempty v =
      (terminal.nestedLeftHalfInvSqProduct ctx.step
          ctx.step.head.carrier ctx.leftHead_nonempty v *
        terminal.nestedRightHalfInvSqProduct ctx.step
          ctx.step.head.carrier ctx.rightHead_nonempty v) *
      ctx.connector
        (ctx.step.splitSurvivingPiMeasurableEquiv v).1
        (ctx.step.splitSurvivingPiMeasurableEquiv v).2 *
      (terminal.nestedLeftHalfInvSqProduct ctx.step
          ctx.step.next.activeCarrier ctx.leftPost_nonempty v *
        terminal.nestedRightHalfInvSqProduct ctx.step
          ctx.step.next.activeCarrier ctx.rightPost_nonempty v) := by
  rw [terminal.nestedHalfInvSqProducts_current_eq_head_connector_post
    ctx v]
  unfold leftTupleOfNestedStep rightTupleOfNestedStep
  rw [terminal.left_connector_edgeDisplacement_eq ctx v,
    terminal.right_connector_edgeDisplacement_eq ctx v]
  rfl

end R324TwoHalfTerminalData

end


end Anderson4D
