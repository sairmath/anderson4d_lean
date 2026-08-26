import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfBudgetInvariant
import Anderson4D.DetParametrix.Paper42_Moment.R324PrimitiveBlockLedger

/-!
# The canonical nested cross-residual state for R-324

After both signed within-half schedules have been removed, paper §4.2
Step 3 does not use an arbitrary block order.  Every remaining fully paired
proper interval crosses the central cut, and the literal reduction order is
the inside-to-outside chain

`[a₁,b₁] ⊂ ... ⊂ [aₜ,bₜ]`.

This module turns the already-proved trace/shell/exterior decomposition into
a proof-relevant cross-block schedule.  Every nonempty scheduled block
contains a left and a right coordinate, so it has a canonical central gap.
That gap is the location of the numerator in (4.20); after one inserted
collapse the gap moves to the next outer shell.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Cross-cut carriers and their canonical gap -/

/-- A sparse doubled carrier genuinely crosses the cut between the two
copies. -/
def R324CrossCutCarrier
    (m : ℕ) (B : Finset (Fin (2 * m))) : Prop :=
  ∃ left ∈ B, ∃ right ∈ B,
    left.val < m ∧ m ≤ right.val

/-- The left component of a doubled sparse carrier. -/
def r324CrossLeftPart
    (m : ℕ) (B : Finset (Fin (2 * m))) :
    Finset (Fin (2 * m)) :=
  B.filter fun i => i.val < m

/-- The right component of a doubled sparse carrier. -/
def r324CrossRightPart
    (m : ℕ) (B : Finset (Fin (2 * m))) :
    Finset (Fin (2 * m)) :=
  B.filter fun i => m ≤ i.val

theorem r324CrossCutCarrier_iff_parts_nonempty
    {m : ℕ} {B : Finset (Fin (2 * m))} :
    R324CrossCutCarrier m B ↔
      (r324CrossLeftPart m B).Nonempty ∧
        (r324CrossRightPart m B).Nonempty := by
  constructor
  · rintro ⟨left, hleft, right, hright,
      hleftCut, hrightCut⟩
    exact
      ⟨⟨left, Finset.mem_filter.mpr
          ⟨hleft, hleftCut⟩⟩,
        ⟨right, Finset.mem_filter.mpr
          ⟨hright, hrightCut⟩⟩⟩
  · rintro ⟨⟨left, hleft⟩, ⟨right, hright⟩⟩
    have hleft' := Finset.mem_filter.mp hleft
    have hright' := Finset.mem_filter.mp hright
    exact
      ⟨left, hleft'.1, right, hright'.1,
        hleft'.2, hright'.2⟩

/-- The last surviving coordinate on the left side of a cross carrier. -/
def r324CrossGapLeft
    {m : ℕ} (B : Finset (Fin (2 * m)))
    (hcross : R324CrossCutCarrier m B) :
    Fin (2 * m) :=
  (r324CrossLeftPart m B).max'
    ((r324CrossCutCarrier_iff_parts_nonempty.mp hcross).1)

/-- The first surviving coordinate on the right side of a cross carrier. -/
def r324CrossGapRight
    {m : ℕ} (B : Finset (Fin (2 * m)))
    (hcross : R324CrossCutCarrier m B) :
    Fin (2 * m) :=
  (r324CrossRightPart m B).min'
    ((r324CrossCutCarrier_iff_parts_nonempty.mp hcross).2)

theorem r324CrossGapLeft_mem
    {m : ℕ} (B : Finset (Fin (2 * m)))
    (hcross : R324CrossCutCarrier m B) :
    r324CrossGapLeft B hcross ∈ B := by
  exact
    (Finset.mem_filter.mp
      (Finset.max'_mem
        (r324CrossLeftPart m B)
        ((r324CrossCutCarrier_iff_parts_nonempty.mp
          hcross).1))).1

theorem r324CrossGapRight_mem
    {m : ℕ} (B : Finset (Fin (2 * m)))
    (hcross : R324CrossCutCarrier m B) :
    r324CrossGapRight B hcross ∈ B := by
  exact
    (Finset.mem_filter.mp
      (Finset.min'_mem
        (r324CrossRightPart m B)
        ((r324CrossCutCarrier_iff_parts_nonempty.mp
          hcross).2))).1

theorem r324CrossGapLeft_lt_cut
    {m : ℕ} (B : Finset (Fin (2 * m)))
    (hcross : R324CrossCutCarrier m B) :
    (r324CrossGapLeft B hcross).val < m := by
  exact
    (Finset.mem_filter.mp
      (Finset.max'_mem
        (r324CrossLeftPart m B)
        ((r324CrossCutCarrier_iff_parts_nonempty.mp
          hcross).1))).2

theorem r324CrossGapRight_ge_cut
    {m : ℕ} (B : Finset (Fin (2 * m)))
    (hcross : R324CrossCutCarrier m B) :
    m ≤ (r324CrossGapRight B hcross).val := by
  exact
    (Finset.mem_filter.mp
      (Finset.min'_mem
        (r324CrossRightPart m B)
        ((r324CrossCutCarrier_iff_parts_nonempty.mp
          hcross).2))).2

theorem r324CrossGapLeft_lt_right
    {m : ℕ} (B : Finset (Fin (2 * m)))
    (hcross : R324CrossCutCarrier m B) :
    r324CrossGapLeft B hcross <
      r324CrossGapRight B hcross := by
  apply Fin.mk_lt_mk.mpr
  exact
    (r324CrossGapLeft_lt_cut B hcross).trans_le
      (r324CrossGapRight_ge_cut B hcross)

/-! ## A generic min/max interval on a closed sparse carrier -/

/-- On a nonempty closed sparse carrier, its minimum and maximum expose the
whole carrier as one relative fully paired interval. -/
theorem isRelFullyPaired_min'_max'
    {n : ℕ} {κ : PartialPairing (Fin n)}
    {B : Finset (Fin n)}
    (hne : B.Nonempty)
    (hfull : IsFullyPairedOn κ B) :
    IsRelFullyPaired κ B (B.min' hne) (B.max' hne) := by
  have hmin : B.min' hne ∈ B :=
    Finset.min'_mem B hne
  have hmax : B.max' hne ∈ B :=
    Finset.max'_mem B hne
  refine
    ⟨hmin, hmax,
      Finset.min'_le B (B.max' hne) hmax, ?_⟩
  have htrace :
      relIcc B (B.min' hne) (B.max' hne) = B := by
    ext i
    constructor
    · exact fun hi => (mem_relIcc.mp hi).1
    · intro hi
      exact mem_relIcc.mpr
        ⟨hi, Finset.min'_le B i hi,
          Finset.le_max' B i hi⟩
  rw [htrace]
  exact hfull

/-! ## Every literal residual block crosses the cut -/

private theorem momentResidualActive_crossCut_of_nonempty
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hne : (momentResidualActive κp κm).Nonempty) :
    R324CrossCutCarrier m
      (momentResidualActive κp κm) := by
  let active := momentResidualActive κp κm
  have hrel :
      IsRelFullyPaired
        (momentCombinedPairing κp κm π)
        active (active.min' hne) (active.max' hne) :=
    isRelFullyPaired_min'_max' hne
      (momentResidualActive_isFullyPairedOn
        κp κm π)
  have hcut :=
    hrel.momentResidualActive_straddlesCut
  exact
    ⟨active.min' hne, Finset.min'_mem active hne,
      active.max' hne, Finset.max'_mem active hne,
      hcut.1, hcut.2⟩

private theorem residualTrace_crossCut
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (p : Fin (2 * m) × Fin (2 * m))
    (hp :
      p ∈ momentResidualIntervalChain κp κm π) :
    R324CrossCutCarrier m
      (residualIntervalTrace
        (momentResidualActive κp κm) p) := by
  have hpaired :=
    (mem_momentResidualProperIntervals.mp
      (mem_momentResidualIntervalChain.mp hp)).1
  have hcut :=
    momentResidualProperInterval_straddlesCut
      (mem_momentResidualIntervalChain.mp hp)
  exact
    ⟨p.1, hpaired.left_mem_relIcc,
      p.2, hpaired.right_mem_relIcc,
      hcut.1, hcut.2⟩

private theorem residualShell_crossCut
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (previous next : Fin (2 * m) × Fin (2 * m))
    (hnext :
      next ∈ momentResidualIntervalChain κp κm π)
    (hcontains :
      LaterCrossCutIntervalContains previous next) :
    R324CrossCutCarrier m
      (residualIntervalShell
        (momentResidualActive κp κm) previous next) := by
  have hnextPaired :=
    (mem_momentResidualProperIntervals.mp
      (mem_momentResidualIntervalChain.mp hnext)).1
  have hleft :
      next.1 ∈
        residualIntervalShell
          (momentResidualActive κp κm)
          previous next := by
    apply Finset.mem_sdiff.mpr
    refine ⟨hnextPaired.left_mem_relIcc, ?_⟩
    intro hmem
    exact
      (not_lt_of_ge (mem_relIcc.mp hmem).2.1)
        hcontains.1
  have hright :
      next.2 ∈
        residualIntervalShell
          (momentResidualActive κp κm)
          previous next := by
    apply Finset.mem_sdiff.mpr
    refine ⟨hnextPaired.right_mem_relIcc, ?_⟩
    intro hmem
    exact
      (not_lt_of_ge (mem_relIcc.mp hmem).2.2)
        hcontains.2
  have hcut :=
    momentResidualProperInterval_straddlesCut
      (mem_momentResidualIntervalChain.mp hnext)
  exact
    ⟨next.1, hleft, next.2, hright,
      hcut.1, hcut.2⟩

private theorem residualExterior_nonempty
    {n : ℕ} {active : Finset (Fin n)}
    {p : Fin n × Fin n}
    (hproper :
      residualIntervalTrace active p ≠ active) :
    (residualIntervalExterior active p).Nonempty := by
  by_contra hempty
  have heq :
      residualIntervalExterior active p = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  apply hproper
  apply Finset.Subset.antisymm
  · exact relIcc_subset_active active p.1 p.2
  · intro i hi
    by_contra hnot
    have hdiff :
        i ∈ residualIntervalExterior active p :=
      Finset.mem_sdiff.mpr ⟨hi, hnot⟩
    rw [heq] at hdiff
    exact Finset.notMem_empty i hdiff

private theorem residualExterior_crossCut
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (last : Fin (2 * m) × Fin (2 * m))
    (hlast :
      last ∈ momentResidualIntervalChain κp κm π) :
    R324CrossCutCarrier m
      (residualIntervalExterior
        (momentResidualActive κp κm) last) := by
  let active := momentResidualActive κp κm
  let exterior :=
    residualIntervalExterior active last
  have hlastData :=
    mem_momentResidualProperIntervals.mp
      (mem_momentResidualIntervalChain.mp hlast)
  have hne : exterior.Nonempty :=
    residualExterior_nonempty hlastData.2
  have hfull :
      IsFullyPairedOn
        (momentCombinedPairing κp κm π) exterior :=
    (momentResidualActive_isFullyPairedOn
      κp κm π).sdiff hlastData.1.isFullyPairedOn
  have hrel :
      IsRelFullyPaired
        (momentCombinedPairing κp κm π)
        exterior (exterior.min' hne) (exterior.max' hne) :=
    isRelFullyPaired_min'_max' hne hfull
  have hsides :=
    IsRelFullyPaired.momentResidualExterior_straddlesInner
      hlastData.1 hrel
  have hlastCut :=
    momentResidualProperInterval_straddlesCut
      (mem_momentResidualIntervalChain.mp hlast)
  exact
    ⟨exterior.min' hne, Finset.min'_mem exterior hne,
      exterior.max' hne, Finset.max'_mem exterior hne,
      (Fin.mk_lt_mk.mp hsides.1).trans hlastCut.1,
      hlastCut.2.trans
        (Nat.le_of_lt (Fin.mk_lt_mk.mp hsides.2))⟩

private theorem nestedResidualShells_forall_crossCut
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (pre : List (Fin (2 * m) × Fin (2 * m)))
    (previous : Fin (2 * m) × Fin (2 * m))
    (rest : List (Fin (2 * m) × Fin (2 * m)))
    (hchain :
      momentResidualIntervalChain κp κm π =
        pre ++ previous :: rest) :
    (nestedResidualShells
      (momentResidualActive κp κm) previous rest).Forall
        (R324CrossCutCarrier m) := by
  induction rest generalizing pre previous with
  | nil =>
      rw [nestedResidualShells, List.forall_cons]
      refine ⟨?_, by trivial⟩
      apply residualExterior_crossCut κp κm π previous
      rw [hchain]
      simp
  | cons next rest ih =>
      simp only [nestedResidualShells, List.forall_cons]
      have hpair :
          (previous :: next :: rest).Pairwise
            LaterCrossCutIntervalContains := by
        have hfull :=
          momentResidualIntervalChain_pairwise_laterContains
            κp κm π
        rw [hchain] at hfull
        have hdrop := hfull.drop (i := pre.length)
        simpa only [List.drop_left] using hdrop
      have hnext :
          next ∈
            momentResidualIntervalChain κp κm π := by
        rw [hchain]
        simp
      constructor
      · exact residualShell_crossCut
          κp κm π previous next hnext
          ((List.pairwise_cons.mp hpair).1 next (by simp))
      · apply ih (pre := pre ++ [previous])
          (previous := next)
        simpa only [List.append_assoc,
          List.singleton_append] using hchain

/-- Every nonempty member of the literal trace/shell/exterior schedule
crosses the central cut. -/
theorem
    momentResidualCollapseBlocks_forall_crossCut_of_nonempty
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (momentResidualCollapseBlocks κp κm π).Forall
      (fun B => B.Nonempty →
        R324CrossCutCarrier m B) := by
  unfold momentResidualCollapseBlocks
  cases hchain :
      momentResidualIntervalChain κp κm π with
  | nil =>
      rw [residualCollapseBlocks, List.forall_cons]
      refine ⟨?_, by trivial⟩
      exact
        momentResidualActive_crossCut_of_nonempty
          κp κm π
  | cons first rest =>
      simp only [residualCollapseBlocks, List.forall_cons]
      constructor
      · intro _hne
        apply residualTrace_crossCut κp κm π first
        rw [hchain]
        simp
      · exact
          (nestedResidualShells_forall_crossCut
            κp κm π [] first rest
              (by simpa using hchain)).imp
            (fun B hcross =>
              (fun _hne : B.Nonempty => hcross))

theorem
    crossCut_of_mem_nonemptyMomentResidualCollapseBlocks
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB :
      B ∈ nonemptyMomentResidualCollapseBlocks
        κp κm π) :
    R324CrossCutCarrier m B := by
  have hdata :=
    mem_nonemptyMomentResidualCollapseBlocks.mp hB
  exact
    List.forall_iff_forall_mem.mp
      (momentResidualCollapseBlocks_forall_crossCut_of_nonempty
        κp κm π)
      B hdata.1 hdata.2

/-! ## The proof-relevant canonical nested schedule -/

/-- One actual nonempty cross-residual block, with its literal schedule
membership and canonical central gap certificate. -/
structure R324NestedCrossBlock
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) where
  carrier : Finset (Fin (2 * m))
  mem_schedule :
    carrier ∈
      nonemptyMomentResidualCollapseBlocks κp κm π
  crossCut : R324CrossCutCarrier m carrier

namespace R324NestedCrossBlock

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

def leftGap
    (block : R324NestedCrossBlock κp κm π) :
    Fin (2 * m) :=
  r324CrossGapLeft block.carrier block.crossCut

def rightGap
    (block : R324NestedCrossBlock κp κm π) :
    Fin (2 * m) :=
  r324CrossGapRight block.carrier block.crossCut

theorem leftGap_mem
    (block : R324NestedCrossBlock κp κm π) :
    block.leftGap ∈ block.carrier :=
  r324CrossGapLeft_mem block.carrier block.crossCut

theorem rightGap_mem
    (block : R324NestedCrossBlock κp κm π) :
    block.rightGap ∈ block.carrier :=
  r324CrossGapRight_mem block.carrier block.crossCut

theorem leftGap_lt_rightGap
    (block : R324NestedCrossBlock κp κm π) :
    block.leftGap < block.rightGap :=
  r324CrossGapLeft_lt_right block.carrier block.crossCut

theorem one_le_order
    (block : R324NestedCrossBlock κp κm π) :
    1 ≤ residualBlockOrder block.carrier :=
  one_le_residualBlockOrder_of_mem_nonemptyMomentResidual
    κp κm π block.carrier block.mem_schedule

end R324NestedCrossBlock

/-- The literal inside-to-outside nonempty residual schedule, enriched by
its canonical central gap at every block. -/
def r324NestedCrossSchedule
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    List (R324NestedCrossBlock κp κm π) :=
  (nonemptyMomentResidualCollapseBlocks κp κm π).attach.map
    fun B =>
      { carrier := B.1
        mem_schedule := B.2
        crossCut :=
          crossCut_of_mem_nonemptyMomentResidualCollapseBlocks
            κp κm π B.1 B.2 }

@[simp]
theorem r324NestedCrossSchedule_carriers
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (r324NestedCrossSchedule κp κm π).map
        R324NestedCrossBlock.carrier =
      nonemptyMomentResidualCollapseBlocks κp κm π := by
  simp [r324NestedCrossSchedule]

/-- Enriching the residual schedule does not alter its exact perturbative
order ledger. -/
theorem r324NestedCrossSchedule_sum_orders
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    ((r324NestedCrossSchedule κp κm π).map
        (fun block =>
          residualBlockOrder block.carrier)).sum =
      ((nonemptyMomentResidualCollapseBlocks κp κm π).map
        residualBlockOrder).sum := by
  change
    ((r324NestedCrossSchedule κp κm π).map
      (residualBlockOrder ∘
        R324NestedCrossBlock.carrier)).sum =
      _
  have h :=
    congrArg
      (fun blocks =>
        (blocks.map residualBlockOrder).sum)
      (r324NestedCrossSchedule_carriers κp κm π)
  rw [List.map_map] at h
  exact h

theorem r324NestedCrossSchedule_pairwise_disjoint
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (r324NestedCrossSchedule κp κm π).Pairwise
      (fun left right =>
        Disjoint left.carrier right.carrier) := by
  rw [← List.pairwise_map]
  rw [r324NestedCrossSchedule_carriers]
  exact
    nonemptyMomentResidualCollapseBlocks_pairwise_disjoint
      κp κm π

/-! ## Genuine prefixes of the nested schedule -/

/-- A processed prefix and literal remaining suffix of the canonical
inside-to-outside cross schedule. -/
structure R324NestedCrossResidualPrefix
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) where
  processed : List (R324NestedCrossBlock κp κm π)
  remaining : List (R324NestedCrossBlock κp κm π)
  schedule_eq :
    r324NestedCrossSchedule κp κm π =
      processed ++ remaining

namespace R324NestedCrossResidualPrefix

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- The cross state before the innermost residual block is removed. -/
def initial
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    R324NestedCrossResidualPrefix κp κm π where
  processed := []
  remaining := r324NestedCrossSchedule κp κm π
  schedule_eq := by simp

/-- The union of all variables not yet removed. -/
def activeCarrier
    (res : R324NestedCrossResidualPrefix κp κm π) :
    Finset (Fin (2 * m)) :=
  finsetUnionList
    (res.remaining.map
      R324NestedCrossBlock.carrier)

/-- Total perturbative order already removed. -/
def processedOrder
    (res : R324NestedCrossResidualPrefix κp κm π) :
    ℕ :=
  (res.processed.map fun block =>
    residualBlockOrder block.carrier).sum

/-- Total perturbative order still carried by the cross suffix. -/
def remainingOrder
    (res : R324NestedCrossResidualPrefix κp κm π) :
    ℕ :=
  (res.remaining.map fun block =>
    residualBlockOrder block.carrier).sum

theorem processedOrder_add_remainingOrder
    (res : R324NestedCrossResidualPrefix κp κm π) :
    res.processedOrder + res.remainingOrder =
      ((nonemptyMomentResidualCollapseBlocks
          κp κm π).map residualBlockOrder).sum := by
  unfold processedOrder remainingOrder
  have hschedule :=
    congrArg
      (fun schedule =>
        (schedule.map fun block =>
          residualBlockOrder block.carrier).sum)
      res.schedule_eq
  simp only [List.map_append, List.sum_append] at hschedule
  rw [← hschedule]
  exact r324NestedCrossSchedule_sum_orders κp κm π

/-- Delete the literal innermost remaining block and expose the next outer
shell (or final exterior). -/
def afterHead
    (res : R324NestedCrossResidualPrefix κp κm π)
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining : res.remaining = head :: tail) :
    R324NestedCrossResidualPrefix κp κm π where
  processed := res.processed ++ [head]
  remaining := tail
  schedule_eq := by
    rw [res.schedule_eq, hremaining]
    simp only [List.append_assoc, List.singleton_append]

@[simp]
theorem afterHead_remaining
    (res : R324NestedCrossResidualPrefix κp κm π)
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining : res.remaining = head :: tail) :
    (res.afterHead head tail hremaining).remaining = tail :=
  rfl

theorem activeCarrier_head
    (res : R324NestedCrossResidualPrefix κp κm π)
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining : res.remaining = head :: tail) :
    res.activeCarrier =
      head.carrier ∪
        (res.afterHead head tail hremaining).activeCarrier := by
  unfold activeCarrier
  rw [hremaining]
  rfl

/-- The block removed at one step is disjoint from the whole later
cross-residual carrier. -/
theorem head_disjoint_afterHead_activeCarrier
    (res : R324NestedCrossResidualPrefix κp κm π)
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining : res.remaining = head :: tail) :
    Disjoint head.carrier
      (res.afterHead head tail hremaining).activeCarrier := by
  have hfull :=
    r324NestedCrossSchedule_pairwise_disjoint κp κm π
  rw [res.schedule_eq, hremaining,
    List.pairwise_append] at hfull
  have htail :
      (head :: tail).Pairwise
        (fun left right =>
          Disjoint left.carrier right.carrier) :=
    hfull.2.1
  have hhead :=
    (List.pairwise_cons.mp htail).1
  unfold activeCarrier
  apply disjoint_finsetUnionList_of_forall_mem
  intro carrier hcarrier
  obtain ⟨block, hblock, rfl⟩ :=
    List.mem_map.mp hcarrier
  exact hhead block hblock

theorem remainingOrder_head
    (res : R324NestedCrossResidualPrefix κp κm π)
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining : res.remaining = head :: tail) :
    res.remainingOrder =
      residualBlockOrder head.carrier +
        (res.afterHead
          head tail hremaining).remainingOrder := by
  unfold remainingOrder
  rw [hremaining]
  rfl

end R324NestedCrossResidualPrefix

/-! ## The moving (4.20) numerator -/

/-- The central numerator attached to the current cross block. -/
def R324NestedCrossBlock.centralGapNumerator
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (block : R324NestedCrossBlock κp κm π)
    (v : Fin (2 * m) → T4) : ℝ :=
  torusDistSq
    (v block.leftGap - v block.rightGap)

theorem R324NestedCrossBlock.centralGapNumerator_nonneg
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (block : R324NestedCrossBlock κp κm π)
    (v : Fin (2 * m) → T4) :
    0 ≤ block.centralGapNumerator v :=
  torusDistSq_nonneg _

/-- The paper's central gap cancellation is pointwise bounded by one.
Equality is intentionally not asserted at the totalized diagonal. -/
theorem R324NestedCrossBlock.centralGapCancellation_le_one
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (block : R324NestedCrossBlock κp κm π)
    (v : Fin (2 * m) → T4) :
    block.centralGapNumerator v *
        invSqKer
          (v block.leftGap - v block.rightGap) ≤
      1 := by
  exact torusDistSq_mul_invSqKer_le_one _

/-- Off the null diagonal, the central inverse-square factor and the
(4.20) numerator cancel exactly. -/
theorem R324NestedCrossBlock.centralGapCancellation_eq_one_of_ne
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (block : R324NestedCrossBlock κp κm π)
    (v : Fin (2 * m) → T4)
    (hne : v block.leftGap ≠ v block.rightGap) :
    block.centralGapNumerator v *
        invSqKer
          (v block.leftGap - v block.rightGap) =
      1 := by
  have hdist :
      torusDistSq
          (v block.leftGap - v block.rightGap) ≠
        0 := by
    intro hzero
    have hsub :
        v block.leftGap - v block.rightGap = 0 :=
      (torusDistSq_eq_zero_iff _).mp hzero
    exact hne (sub_eq_zero.mp hsub)
  unfold R324NestedCrossBlock.centralGapNumerator
    invSqKer
  exact mul_inv_cancel₀ hdist

/-- Under the genuine product measure, the paper's moving central gap
cancels exactly almost everywhere. -/
theorem
    R324NestedCrossBlock.ae_centralGapCancellation_eq_one
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (block : R324NestedCrossBlock κp κm π) :
    ∀ᵐ v : Fin (2 * m) → T4
        ∂(Measure.pi fun _ => paperMeasure),
      block.centralGapNumerator v *
          invSqKer
            (v block.leftGap - v block.rightGap) =
        1 := by
  have hm : 0 < 2 * m := by
    have hleft := block.leftGap.isLt
    omega
  have hne :
      block.leftGap ≠ block.rightGap :=
    ne_of_lt block.leftGap_lt_rightGap
  filter_upwards
      [ae_pi_eval_ne_eval_of_pos
        hm block.leftGap block.rightGap hne] with v hv
  exact block.centralGapCancellation_eq_one_of_ne v hv

end

end Anderson4D
