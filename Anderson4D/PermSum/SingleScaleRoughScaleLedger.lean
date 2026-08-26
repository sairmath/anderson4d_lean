import Anderson4D.PermSum.SingleScaleTargetLedger
import Anderson4D.HeppTree.VolumeEstimate

/-!
# The rough-scale payoff in the one-parity ledger

This file records, with multiplicity, the skipped incoming edges whose
rough estimates contribute the explicit `(N / R)²` factors in
(5.90)--(5.92).  It also isolates the two estimates needed to collapse
those local factors to the root scale:

* marking the first `fuel` eligible pairs retains at least the first
  `min skipped fuel` skipped occurrences;
* every active `N`-class lies below the root Hepp scale.

The occurrence list below is deliberately a `List`, rather than a
`Finset`: when both incoming edges of one rough pair are skipped, both
copies of the scale gain occur in the analytic target.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/-! ## Pure positional counting -/

/-- Number of skipped incoming edges carried by one positional block. -/
def positionExceptionSkippedCountBlock {m : ℕ} :
    PositionExceptionControlBlock m → ℕ
  | .single _ skipped => if skipped then 1 else 0
  | .pair _ _ skipLeft skipRight
  | .roughPair _ _ skipLeft skipRight =>
      (if skipLeft then 1 else 0) + (if skipRight then 1 else 0)

/-- Number of skipped incoming-edge occurrences in a positional ledger. -/
def positionExceptionSkippedCount {m : ℕ} :
    List (PositionExceptionControlBlock m) → ℕ
  | [] => 0
  | b :: bs =>
      positionExceptionSkippedCountBlock b +
        positionExceptionSkippedCount bs

/--
Number of rough scale factors retained by one positional block.
Singles are intrinsically rough; unmarked pairs contribute none.
-/
def positionExceptionRoughFactorCountBlock {m : ℕ} :
    PositionExceptionControlBlock m → ℕ
  | .single _ skipped => if skipped then 1 else 0
  | .pair _ _ _ _ => 0
  | .roughPair _ _ skipLeft skipRight =>
      (if skipLeft then 1 else 0) + (if skipRight then 1 else 0)

/-- Number of explicit `(N/R)²` occurrences retained by a ledger. -/
def positionExceptionRoughFactorCount {m : ℕ} :
    List (PositionExceptionControlBlock m) → ℕ
  | [] => 0
  | b :: bs =>
      positionExceptionRoughFactorCountBlock b +
        positionExceptionRoughFactorCount bs

@[simp] theorem positionExceptionSkippedCount_append
    {m : ℕ} (bs cs : List (PositionExceptionControlBlock m)) :
    positionExceptionSkippedCount (bs ++ cs) =
      positionExceptionSkippedCount bs +
        positionExceptionSkippedCount cs := by
  induction bs with
  | nil =>
      simp [positionExceptionSkippedCount]
  | cons b bs ih =>
      simp [positionExceptionSkippedCount, ih, Nat.add_assoc]

private theorem positionExceptionSkippedCountBlock_toControl
    {m : ℕ} (incomingSkipped : Fin m → Bool)
    (b : PositionBlock (Fin m)) :
    positionExceptionSkippedCountBlock
        (positionBlockToExceptionControl incomingSkipped b) =
      (b.entries.map
        (fun i => if incomingSkipped i then 1 else 0)).sum := by
  cases b with
  | single i =>
      cases h : incomingSkipped i <;>
        simp [positionBlockToExceptionControl,
          positionExceptionSkippedCountBlock,
          PositionBlock.entries, h]
  | pair i j =>
      cases hi : incomingSkipped i <;>
        cases hj : incomingSkipped j <;>
        simp [positionBlockToExceptionControl,
          positionExceptionSkippedCountBlock,
          PositionBlock.entries, hi, hj]

private theorem positionExceptionSkippedCount_map_toControl
    {m : ℕ} (incomingSkipped : Fin m → Bool)
    (bs : List (PositionBlock (Fin m))) :
    positionExceptionSkippedCount
        (bs.map (positionBlockToExceptionControl incomingSkipped)) =
      ((bs.flatMap PositionBlock.entries).map
        (fun i => if incomingSkipped i then 1 else 0)).sum := by
  induction bs with
  | nil =>
      simp [positionExceptionSkippedCount]
  | cons b bs ih =>
      simp only [List.map_cons, positionExceptionSkippedCount,
        List.flatMap_cons, List.map_append, List.sum_append]
      rw [positionExceptionSkippedCountBlock_toControl, ih]

/-- The raw skip count is the sum of the incoming-edge indicators on the
two outward position runs, independently of the pairing phases. -/
theorem positionExceptionSkippedCount_finAnchor_raw_eq_positionSums
    {m : ℕ} (leftPhase rightPhase : Bool) (anchor : Fin m)
    (O : Finset (AdjacentIndex m)) :
    positionExceptionSkippedCount
        (finAnchorPositionExceptionControlLedgerWithPhases
          leftPhase rightPhase anchor O) =
      ((leftAnchorPositions anchor).map
        (fun i =>
          if positionIncomingSkipped O .reverse i then 1 else 0)).sum +
      ((rightAnchorPositions anchor).map
        (fun i =>
          if positionIncomingSkipped O .forward i then 1 else 0)).sum := by
  rw [finAnchorPositionExceptionControlLedgerWithPhases,
    positionExceptionSkippedCount_append,
    positionExceptionSkippedCount_map_toControl,
    positionExceptionSkippedCount_map_toControl,
    flatten_pairPositionRun, flatten_pairPositionRun]

/-- Incoming-skip bit on the unique outward traversal determined by an
anchor.  The value at the anchor itself is irrelevant. -/
private def anchorIncomingSkipped {m : ℕ}
    (O : Finset (AdjacentIndex m)) (anchor i : Fin m) : Bool :=
  if i < anchor then
    positionIncomingSkipped O .reverse i
  else
    positionIncomingSkipped O .forward i

private theorem leftAnchor_skipIndicator_eq_anchorIncoming
    {m : ℕ} (O : Finset (AdjacentIndex m)) (anchor : Fin m) :
    (leftAnchorPositions anchor).map
        (fun i =>
          if positionIncomingSkipped O .reverse i then 1 else 0) =
      (leftAnchorPositions anchor).map
        (fun i => if anchorIncomingSkipped O anchor i then 1 else 0) := by
  apply List.map_congr_left
  intro i hi
  have hil := (mem_leftAnchorPositions_iff anchor i).mp hi
  change i < anchor at hil
  simp [anchorIncomingSkipped, hil]

private theorem rightAnchor_skipIndicator_eq_anchorIncoming
    {m : ℕ} (O : Finset (AdjacentIndex m)) (anchor : Fin m) :
    (rightAnchorPositions anchor).map
        (fun i =>
          if positionIncomingSkipped O .forward i then 1 else 0) =
      (rightAnchorPositions anchor).map
        (fun i => if anchorIncomingSkipped O anchor i then 1 else 0) := by
  apply List.map_congr_left
  intro i hi
  have hir := (mem_rightAnchorPositions_iff anchor i).mp hi
  have hnot : ¬i < anchor := by
    omega
  simp [anchorIncomingSkipped, hnot]

/-- The outward position list is a permutation of `succAbove`: both are
enumerations of every position except the anchor exactly once. -/
private theorem anchorPositions_perm_succAbove
    {n : ℕ} (anchor : Fin (n + 1)) :
    List.Perm
      (leftAnchorPositions anchor ++ rightAnchorPositions anchor)
      (List.ofFn (fun j : Fin n => anchor.succAbove j)) := by
  apply (List.perm_ext_iff_of_nodup
    (left_append_rightAnchorPositions_nodup anchor)
    (List.nodup_ofFn_ofInjective
      Fin.succAbove_right_injective)).2
  intro i
  rw [List.mem_append, mem_leftAnchorPositions_iff,
    mem_rightAnchorPositions_iff, List.mem_ofFn']
  change
    (i.1 < anchor.1 ∨ anchor.1 < i.1) ↔
      ∃ j : Fin n, anchor.succAbove j = i
  rw [Fin.exists_succAbove_eq_iff]
  omega

/-- `succAbove` sends an edge index to the position entered by that edge
in the outward traversal, on either side of the anchor. -/
private theorem anchorIncomingSkipped_succAbove
    {n : ℕ} (O : Finset (AdjacentIndex (n + 1)))
    (anchor : Fin (n + 1)) (j : Fin n) :
    anchorIncomingSkipped O anchor (anchor.succAbove j) =
      decide ((adjacentIndexSuccEquiv n).symm j ∈ O) := by
  by_cases hleft : j.castSucc < anchor
  · rw [Fin.succAbove_of_castSucc_lt _ _ hleft]
    have hreverse :
        reverseIncomingEdge j.castSucc =
          some ((adjacentIndexSuccEquiv n).symm j) := by
      unfold reverseIncomingEdge
      rw [dif_pos (by omega)]
      congr 2
    simp [anchorIncomingSkipped, hleft,
      positionIncomingSkipped, hreverse]
  · have hanchor :
        ¬j.succ < anchor := by
      have hstep : j.castSucc < j.succ := by
        simp
      exact not_lt_of_ge
        (le_of_lt (lt_of_le_of_lt (Fin.not_lt.mp hleft) hstep))
    rw [Fin.succAbove_of_le_castSucc _ _ (Fin.not_lt.mp hleft)]
    have hforward :
        forwardIncomingEdge j.succ =
          some ((adjacentIndexSuccEquiv n).symm j) := by
      unfold forwardIncomingEdge
      rw [dif_pos (by simp)]
      congr 2
    simp [anchorIncomingSkipped, hanchor,
      positionIncomingSkipped, hforward]

/--
Every original adjacency is the incoming edge of exactly one non-anchor
position.  Hence the raw Boolean ledger counts `O` with no loss and no
duplication.
-/
theorem positionExceptionSkippedCount_finAnchor_raw
    {n : ℕ} (leftPhase rightPhase : Bool)
    (anchor : Fin (n + 1))
    (O : Finset (AdjacentIndex (n + 1))) :
    positionExceptionSkippedCount
        (finAnchorPositionExceptionControlLedgerWithPhases
          leftPhase rightPhase anchor O) =
      O.card := by
  classical
  rw [positionExceptionSkippedCount_finAnchor_raw_eq_positionSums,
    leftAnchor_skipIndicator_eq_anchorIncoming,
    rightAnchor_skipIndicator_eq_anchorIncoming]
  let weight : Fin (n + 1) → ℕ :=
    fun i => if anchorIncomingSkipped O anchor i then 1 else 0
  calc
    ((leftAnchorPositions anchor).map weight).sum +
        ((rightAnchorPositions anchor).map weight).sum =
      ((leftAnchorPositions anchor ++
        rightAnchorPositions anchor).map weight).sum := by
          rw [List.map_append, List.sum_append]
    _ = ((List.ofFn (fun j : Fin n =>
          anchor.succAbove j)).map weight).sum :=
      List.Perm.sum_eq
        ((anchorPositions_perm_succAbove anchor).map weight)
    _ = ∑ j : Fin n, weight (anchor.succAbove j) := by
      simp [List.sum_ofFn]
    _ = ∑ j : Fin n,
        if decide ((adjacentIndexSuccEquiv n).symm j ∈ O)
          then 1 else 0 := by
      apply Fintype.sum_congr
      intro j
      dsimp [weight]
      rw [anchorIncomingSkipped_succAbove]
    _ = ∑ edge : AdjacentIndex (n + 1),
        if decide (edge ∈ O) then 1 else 0 := by
      exact Fintype.sum_equiv (adjacentIndexSuccEquiv n).symm
        (fun j : Fin n =>
          if decide ((adjacentIndexSuccEquiv n).symm j ∈ O)
            then 1 else 0)
        (fun edge : AdjacentIndex (n + 1) =>
          if decide (edge ∈ O) then 1 else 0)
        (fun _j => rfl)
    _ = O.card := by
      simpa only [decide_eq_true_eq] using
        (Finset.card_eq_sum_ite
          (Finset.subset_univ O)).symm

/--
Exact selection-count inequality for the first-skipped-pair algorithm.

The left side counts skipped incoming edges, not merely eligible blocks.
Consequently, a marked pair whose two incoming edges are both skipped
contributes two rough factors, exactly as its analytic target does.
-/
theorem min_positionExceptionSkippedCount_le_roughFactorCount_mark
    {m : ℕ} (fuel : ℕ)
    (bs : List (PositionExceptionControlBlock m)) :
    min (positionExceptionSkippedCount bs) fuel ≤
      positionExceptionRoughFactorCount
        (markFirstSkippedPositionExceptionRough fuel bs) := by
  induction bs generalizing fuel with
  | nil =>
      simp [positionExceptionSkippedCount,
        positionExceptionRoughFactorCount,
        markFirstSkippedPositionExceptionRough]
  | cons b bs ih =>
      cases fuel with
      | zero =>
          simp [positionExceptionSkippedCount,
            positionExceptionRoughFactorCount,
            markFirstSkippedPositionExceptionRough]
      | succ fuel =>
          cases b with
          | single i skipped =>
              have h := ih (fuel + 1)
              cases skipped <;>
                simp [positionExceptionSkippedCount,
                  positionExceptionSkippedCountBlock,
                  positionExceptionRoughFactorCount,
                  positionExceptionRoughFactorCountBlock,
                  markFirstSkippedPositionExceptionRough] at h ⊢ <;>
                omega
          | pair i j skipLeft skipRight =>
              have hsame := ih (fuel + 1)
              have hnext := ih fuel
              cases skipLeft <;> cases skipRight <;>
                simp [positionExceptionSkippedCount,
                  positionExceptionSkippedCountBlock,
                  positionExceptionRoughFactorCount,
                  positionExceptionRoughFactorCountBlock,
                  markFirstSkippedPositionExceptionRough] at hsame hnext ⊢ <;>
                omega
          | roughPair i j skipLeft skipRight =>
              have h := ih (fuel + 1)
              cases skipLeft <;> cases skipRight <;>
                simp [positionExceptionSkippedCount,
                  positionExceptionSkippedCountBlock,
                  positionExceptionRoughFactorCount,
                  positionExceptionRoughFactorCountBlock,
                  markFirstSkippedPositionExceptionRough] at h ⊢ <;>
                omega

/-! ## Occurrence-level analytic ledger -/

/--
The active dyadic scales whose explicit square factors occur in one
located block.  Both skipped sides of a rough pair are retained.
-/
def locatedBlockRoughScaleOccurrences
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t} :
    LocatedNXParityBlock (m := m) Nm mu →
      List (ActiveNXClass Nm mu)
  | .single _ a skipped =>
      if skipped then [a] else []
  | .pair _ _ _ => []
  | .roughPair _ _ p =>
      (if p.skipLeft then [p.left] else []) ++
        (if p.skipRight then [p.right] else [])

/-- All rough square-factor scales, retaining their multiplicities. -/
def locatedLedgerRoughScaleOccurrences
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    List (ActiveNXClass Nm mu) :=
  bs.flatMap locatedBlockRoughScaleOccurrences

@[simp] theorem length_locatedBlockRoughScaleOccurrences
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (b : LocatedNXParityBlock (m := m) Nm mu) :
    (locatedBlockRoughScaleOccurrences b).length =
      positionExceptionRoughFactorCountBlock b.exceptionControl := by
  cases b with
  | single i a skipped =>
      cases skipped <;>
        simp [locatedBlockRoughScaleOccurrences,
          positionExceptionRoughFactorCountBlock,
          LocatedNXParityBlock.exceptionControl]
  | pair i j p =>
      simp [locatedBlockRoughScaleOccurrences,
        positionExceptionRoughFactorCountBlock,
        LocatedNXParityBlock.exceptionControl]
  | roughPair i j p =>
      cases hleft : p.skipLeft <;>
        cases hright : p.skipRight <;>
        simp [locatedBlockRoughScaleOccurrences,
          positionExceptionRoughFactorCountBlock,
          LocatedNXParityBlock.exceptionControl, hleft, hright]

theorem length_locatedLedgerRoughScaleOccurrences
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    (locatedLedgerRoughScaleOccurrences bs).length =
      positionExceptionRoughFactorCount
        (bs.map LocatedNXParityBlock.exceptionControl) := by
  induction bs with
  | nil =>
      simp [locatedLedgerRoughScaleOccurrences,
        positionExceptionRoughFactorCount]
  | cons b bs ih =>
      change
        (locatedBlockRoughScaleOccurrences b ++
          locatedLedgerRoughScaleOccurrences bs).length =
        positionExceptionRoughFactorCountBlock b.exceptionControl +
          positionExceptionRoughFactorCount
            (bs.map LocatedNXParityBlock.exceptionControl)
      rw [List.length_append,
        length_locatedBlockRoughScaleOccurrences, ih]

/-- The rough-scale product is exactly the product over its occurrence list. -/
theorem locatedLedgerRoughScaleProduct_eq_occurrences
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (R : ℝ)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    locatedLedgerRoughScaleProduct R bs =
      ((locatedLedgerRoughScaleOccurrences bs).map
        fun a => ((a.1.1 : ℝ) / R) ^ 2).prod := by
  induction bs with
  | nil =>
      simp [locatedLedgerRoughScaleProduct,
        locatedLedgerRoughScaleOccurrences]
  | cons b bs ih =>
      change
        locatedBlockRoughScale R b *
            locatedLedgerRoughScaleProduct R bs =
          (((locatedBlockRoughScaleOccurrences b ++
              locatedLedgerRoughScaleOccurrences bs).map
            (fun a => ((a.1.1 : ℝ) / R) ^ 2))).prod
      rw [List.map_append, List.prod_append, ← ih]
      congr 1
      cases b with
      | single i a skipped =>
          cases skipped <;>
            simp [locatedBlockRoughScale,
              locatedBlockRoughScaleOccurrences,
              paperDyadicRoughScaleGain]
      | pair i j p =>
          simp [locatedBlockRoughScale,
            locatedBlockRoughScaleOccurrences]
      | roughPair i j p =>
          cases hleft : p.skipLeft <;>
            cases hright : p.skipRight <;>
            simp [locatedBlockRoughScale,
              locatedBlockRoughScaleOccurrences,
              paperDyadicRoughScaleGain, hleft, hright]

/--
Concrete first-three selection theorem.  Its left side is computed from
the raw, pre-marking flags, so it does not assume an abstract supply of
eligible blocks.
-/
theorem finAnchorNXLocatedCoarse_roughScaleOccurrences_count_from_raw
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    min
        (positionExceptionSkippedCount
          (finAnchorPositionExceptionControlLedgerWithPhases
            leftPhase rightPhase anchor O))
        3 ≤
      (locatedLedgerRoughScaleOccurrences
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O)).length := by
  rw [length_locatedLedgerRoughScaleOccurrences,
    map_exceptionControl_finAnchorNXLocatedCoarseLedgerWithPhases]
  exact min_positionExceptionSkippedCount_le_roughFactorCount_mark 3 _

/--
Concrete paper count: the selected schedule contains at least
`min |O| 3` explicit square factors.
-/
theorem finAnchorNXLocatedCoarse_roughScaleOccurrences_count
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1))
    (cls : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1))) :
    min O.card 3 ≤
      (locatedLedgerRoughScaleOccurrences
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O)).length := by
  rw [← positionExceptionSkippedCount_finAnchor_raw
    leftPhase rightPhase anchor O]
  exact
    finAnchorNXLocatedCoarse_roughScaleOccurrences_count_from_raw
      Nm mu leftPhase rightPhase anchor cls O

/-! ## Moving local scales to the root -/

/-- Every active `N`-class scale is bounded by the root Hepp scale. -/
theorem activeNXClass_scale_le_root
    {t : PlaneTree}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (a : ActiveNXClass Nm mu) :
    a.1.1 ≤ scaleN Nm (rootV t) := by
  obtain ⟨l, _hl, ha⟩ := Finset.mem_image.mp a.2
  have hlne : l.1 ≠ rootV t := by
    intro h
    have hzero := mem_Leaves_iff.mp (h ▸ l.2)
    have htwo := mem_BranchNodes_iff.mp hroot
    omega
  have hp : parentV l.1 ∈ BranchNodes t :=
    parentV_mem_BranchNodes_of_isValid ht hlne
  have hdesc : parentV l.1 ∈ branchDescendants (rootV t) := by
    simpa using hp
  have hscale :=
    scaleN_branchDescendant_le ht Nm hdesc
  simpa [singleScaleSigma1] using ha ▸ hscale

/-- The root dyadic scale is one summand of its accumulated scale. -/
theorem scaleN_root_le_accumulatedScale_root
    {t : PlaneTree}
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    scaleN Nm (rootV t) ≤
      accumulatedScale Nm mu (rootV t) := by
  have hgamma : 1 ≤ gammaInf mu (rootV t) := by
    rw [gammaInf, card_childrenOf]
    have htwo := mem_BranchNodes_iff.mp hroot
    omega
  rw [accumulatedScale, branchNodesUnder_root]
  calc
    scaleN Nm (rootV t) =
        1 * scaleN Nm (rootV t) := by simp
    _ ≤ gammaInf mu (rootV t) * scaleN Nm (rootV t) :=
      Nat.mul_le_mul_right _ hgamma
    _ ≤ ∑ u ∈ BranchNodes t, gammaInf mu u * scaleN Nm u :=
      Finset.single_le_sum
        (fun u _hu => Nat.zero_le
          (gammaInf mu u * scaleN Nm u)) hroot

/-- One selected local square factor is no larger than its root-scale copy. -/
theorem roughScaleOccurrence_le_root
    {t : PlaneTree}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (R : ℕ) (a : ActiveNXClass Nm mu) :
    ((a.1.1 : ℝ) / (R : ℝ)) ^ 2 ≤
      ((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^ 2 := by
  have hscale : (a.1.1 : ℝ) ≤ scaleN Nm (rootV t) := by
    exact_mod_cast activeNXClass_scale_le_root ht hroot Nm mu a
  have hratio :
      (a.1.1 : ℝ) / (R : ℝ) ≤
        (scaleN Nm (rootV t) : ℝ) / (R : ℝ) := by
    exact div_le_div_of_nonneg_right hscale (by positivity)
  exact pow_le_pow_left₀ (by positivity) hratio 2

/--
The product of `k` selected local square gains is bounded by the
`2k`-th power of the root ratio.
-/
theorem roughScaleOccurrences_product_le_root_pow
    {t : PlaneTree}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (R : ℕ) (as : List (ActiveNXClass Nm mu)) :
    (as.map (fun a => ((a.1.1 : ℝ) / (R : ℝ)) ^ 2)).prod ≤
      ((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
        (2 * as.length) := by
  induction as with
  | nil =>
      simp
  | cons a as ih =>
      rw [List.map_cons, List.prod_cons, List.length_cons]
      have hlocal := roughScaleOccurrence_le_root
        ht hroot Nm mu R a
      have htailNonneg :
          0 ≤
            (as.map
              (fun b => ((b.1.1 : ℝ) / (R : ℝ)) ^ 2)).prod :=
        by
          apply List.prod_nonneg
          intro x hx
          obtain ⟨b, _hb, rfl⟩ := List.mem_map.mp hx
          exact sq_nonneg _
      calc
        ((a.1.1 : ℝ) / (R : ℝ)) ^ 2 *
            (as.map
              (fun b => ((b.1.1 : ℝ) / (R : ℝ)) ^ 2)).prod ≤
          ((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^ 2 *
            ((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
              (2 * as.length) :=
            mul_le_mul hlocal ih htailNonneg (sq_nonneg _)
        _ =
          ((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
            (2 * (as.length + 1)) := by
              rw [← pow_add]
              congr 1
              omega

/-- Under the paper's root accumulated-scale hypothesis, the root ratio
lies in the unit interval. -/
theorem rootScaleRatio_mem_unitInterval
    {t : PlaneTree}
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (R : ℕ)
    (hR : accumulatedScale Nm mu (rootV t) ≤ R) :
    0 ≤ (scaleN Nm (rootV t) : ℝ) / (R : ℝ) ∧
      (scaleN Nm (rootV t) : ℝ) / (R : ℝ) ≤ 1 := by
  have hrootR :
      scaleN Nm (rootV t) ≤ R :=
    (scaleN_root_le_accumulatedScale_root hroot Nm mu).trans hR
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast
      (lt_of_lt_of_le (scaleN_pos Nm (rootV t)) hrootR)
  exact ⟨by positivity, (div_le_one hRpos).2 (by exact_mod_cast hrootR)⟩

/--
The numerical collapse used after (5.92).  Counting
`min s 3` selected square occurrences is enough for the (slightly weaker)
paper exponent `min (2s) 3`.
-/
theorem roughScaleOccurrences_product_le_paperRootGain
    {t : PlaneTree}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (R s : ℕ)
    (hR : accumulatedScale Nm mu (rootV t) ≤ R)
    (as : List (ActiveNXClass Nm mu))
    (hcount : min s 3 ≤ as.length) :
    (as.map (fun a => ((a.1.1 : ℝ) / (R : ℝ)) ^ 2)).prod ≤
      ((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
        min (2 * s) 3 := by
  obtain ⟨hq0, hq1⟩ :=
    rootScaleRatio_mem_unitInterval hroot Nm mu R hR
  have hexponent : min (2 * s) 3 ≤ 2 * as.length := by
    omega
  exact
    (roughScaleOccurrences_product_le_root_pow
      ht hroot Nm mu R as).trans
      (pow_le_pow_of_le_one hq0 hq1 hexponent)

/--
Ledger-facing collapse: only the exact selected-occurrence lower bound is
needed.  The following concrete section proves that lower bound from `O`.
-/
theorem locatedLedgerRoughScaleProduct_le_paperRootGain
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (R s : ℕ)
    (hR : accumulatedScale Nm mu (rootV t) ≤ R)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu))
    (hcount :
      min s 3 ≤ (locatedLedgerRoughScaleOccurrences bs).length) :
    locatedLedgerRoughScaleProduct (R : ℝ) bs ≤
      ((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
        min (2 * s) 3 := by
  rw [locatedLedgerRoughScaleProduct_eq_occurrences]
  exact roughScaleOccurrences_product_le_paperRootGain
    ht hroot Nm mu R s hR _ hcount

/--
Final concrete rough-scale ledger bound for one anchored parity schedule.
This is the explicit `(N_root/R)^(min (2|O|) 3)` payoff used after
(5.90)--(5.92).
-/
theorem finAnchorNXLocatedCoarse_roughScaleProduct_le
    {t : PlaneTree} {n : ℕ}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (R : ℕ)
    (hR : accumulatedScale Nm mu (rootV t) ≤ R)
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1))
    (cls : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1))) :
    locatedLedgerRoughScaleProduct (R : ℝ)
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) ≤
      ((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
        min (2 * O.card) 3 := by
  apply locatedLedgerRoughScaleProduct_le_paperRootGain
    ht hroot Nm mu R O.card hR
  exact finAnchorNXLocatedCoarse_roughScaleOccurrences_count
    Nm mu leftPhase rightPhase anchor cls O

end XYCluster

end

end Anderson4D
