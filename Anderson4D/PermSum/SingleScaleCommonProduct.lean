import Anderson4D.PermSum.SingleScalePhaseAssembly
import Anderson4D.PermSum.SingleScaleKernelSchedule

set_option warningAsError true

/-!
# Phase-independent common product

The common local target in the anchored elimination depends on the word,
the anchor, and the omitted-edge set, but not on the pairing phase.  This
file expands the located ledger to the product over all non-anchor
positions and records that independence as an exact equality.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/-- Whether the original edge entering a non-anchor position in the
outward traversal belongs to `O`.  The anchor value is harmless because
the anchor is erased from every product below. -/
def outwardPositionSkipped {m : ℕ}
    (O : Finset (AdjacentIndex m)) (anchor i : Fin m) : Bool :=
  (outwardPositionIncomingEdge anchor i).any fun edge =>
    decide (edge ∈ O)

@[simp] theorem outwardPositionSkipped_of_lt {m : ℕ}
    (O : Finset (AdjacentIndex m)) (anchor i : Fin m)
    (hi : i.1 < anchor.1) :
    outwardPositionSkipped O anchor i =
      positionIncomingSkipped O .reverse i := by
  simp [outwardPositionSkipped, outwardPositionIncomingEdge,
    positionIncomingSkipped, hi]

@[simp] theorem outwardPositionSkipped_of_gt {m : ℕ}
    (O : Finset (AdjacentIndex m)) (anchor i : Fin m)
    (hi : anchor.1 < i.1) :
    outwardPositionSkipped O anchor i =
      positionIncomingSkipped O .forward i := by
  simp [outwardPositionSkipped, outwardPositionIncomingEdge,
    positionIncomingSkipped, hi,
    not_lt_of_ge (Nat.le_of_lt hi)]

@[simp] theorem outwardPositionSkipped_target {m : ℕ}
    (O : Finset (AdjacentIndex m)) (anchor : Fin m)
    (edge : AdjacentIndex m) :
    outwardPositionSkipped O anchor
        (outwardEdgeTargetPosition anchor edge) =
      decide (edge ∈ O) := by
  simp [outwardPositionSkipped, outwardPositionIncomingEdge_target]

@[simp] theorem locatedBlockCommonTarget_locatePositionBlock
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (cls : Fin m → ActiveNXClass Nm mu)
    (incomingSkipped : Fin m → Bool)
    (b : PositionBlock (Fin m)) :
    locatedBlockCommonTarget Nm mu
        (locatePositionBlock Nm mu cls incomingSkipped b) =
      (b.entries.map fun i =>
        paperDyadicLocalTarget Nm mu
          (cls i).1 (incomingSkipped i)).prod := by
  cases b <;>
    simp [locatedBlockCommonTarget, locatePositionBlock,
      PositionBlock.entries]

/-- Turning selected precise pairs into rough pairs does not change their
common local factors. -/
theorem locatedCommonProduct_markFirstSkippedLocatedPairsRough
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (fuel : ℕ)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    ((markFirstSkippedLocatedPairsRough fuel bs).map
        (locatedBlockCommonTarget Nm mu)).prod =
      (bs.map (locatedBlockCommonTarget Nm mu)).prod := by
  induction bs generalizing fuel with
  | nil =>
      simp [markFirstSkippedLocatedPairsRough]
  | cons b bs ih =>
      cases fuel with
      | zero =>
          rfl
      | succ fuel =>
          cases b with
          | single i a skipped =>
              simp [markFirstSkippedLocatedPairsRough, ih]
          | pair i j p =>
              by_cases h : nxPairBlockTouchesSkip p
              · simp [markFirstSkippedLocatedPairsRough, h,
                  locatedBlockCommonTarget, ih]
              · simp [markFirstSkippedLocatedPairsRough, h,
                  locatedBlockCommonTarget, ih]
          | roughPair i j p =>
              simp [markFirstSkippedLocatedPairsRough,
                locatedBlockCommonTarget, ih]

private theorem locatedCommonProduct_map_locatePositionBlocks
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (cls : Fin m → ActiveNXClass Nm mu)
    (incomingSkipped : Fin m → Bool)
    (bs : List (PositionBlock (Fin m))) :
    (((bs.map
        (locatePositionBlock Nm mu cls incomingSkipped)).map
          (locatedBlockCommonTarget Nm mu)).prod) =
      (((bs.flatMap PositionBlock.entries).map fun i =>
        paperDyadicLocalTarget Nm mu
          (cls i).1 (incomingSkipped i)).prod) := by
  induction bs with
  | nil =>
      rfl
  | cons b bs ih =>
      rw [List.map_cons, List.map_cons, List.prod_cons,
        locatedBlockCommonTarget_locatePositionBlock,
        List.flatMap_cons, List.map_append, List.prod_append, ih]

private theorem outwardOrderProduct_eq_nonanchorProduct
    {m : ℕ} (leftPhase rightPhase : Bool) (anchor : Fin m)
    (f : Fin m → ℝ) :
    (((finAnchorPositionScheduleWithPhases
      leftPhase rightPhase anchor).flatMap
        PositionBlock.entries).map f).prod =
      ∏ i ∈ Finset.univ.erase anchor, f i := by
  classical
  let order :=
    (finAnchorPositionScheduleWithPhases
      leftPhase rightPhase anchor).flatMap PositionBlock.entries
  have hnodup : order.Nodup :=
    nodup_flatten_finAnchorPositionScheduleWithPhases
      leftPhase rightPhase anchor
  have hcarrier :
      order.toFinset = Finset.univ.erase anchor := by
    ext i
    simp only [List.mem_toFinset, Finset.mem_erase,
      Finset.mem_univ, and_true]
    exact mem_flatten_finAnchorPositionScheduleWithPhases_iff
      leftPhase rightPhase anchor i
  rw [← List.prod_toFinset f hnodup, hcarrier]

/-- Reindex a non-anchor position product by the unique original edge whose
outward target is that position. -/
theorem prod_nonanchor_eq_prod_outwardEdgeTarget
    {m : ℕ} (anchor : Fin m) (f : Fin m → ℝ) :
    (∏ i ∈ Finset.univ.erase anchor, f i) =
      ∏ edge : AdjacentIndex m,
        f (outwardEdgeTargetPosition anchor edge) := by
  classical
  symm
  refine Finset.prod_bij
    (fun edge _hedge => outwardEdgeTargetPosition anchor edge)
    ?_ ?_ ?_ ?_
  · intro edge _hedge
    simp [outwardEdgeTargetPosition_ne_anchor]
  · intro edge₁ _h₁ edge₂ _h₂ heq
    exact outwardEdgeTargetPosition_injective anchor heq
  · intro i hi
    have hne : i ≠ anchor := (Finset.mem_erase.mp hi).1
    have hval : i.1 ≠ anchor.1 := fun h => hne (Fin.ext h)
    by_cases hleft : i.1 < anchor.1
    · let edge : AdjacentIndex m := ⟨i, by omega⟩
      refine ⟨edge, Finset.mem_univ _, ?_⟩
      simp [outwardEdgeTargetPosition, edge, hleft]
    · have hright : anchor.1 < i.1 := by omega
      let lower : Fin m := ⟨i.1 - 1, by omega⟩
      let edge : AdjacentIndex m := ⟨lower, by
        dsimp [lower]
        omega⟩
      have hlower : ¬lower.1 < anchor.1 := by
        dsimp [lower]
        omega
      refine ⟨edge, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp [outwardEdgeTargetPosition, edge, lower, hlower,
        adjacentSucc]
      omega
  · intro edge _hedge
    rfl

/--
Exact phase-free normal form of the common located ledger: one local target
for every non-anchor word position, with the actual outward incoming edge.
-/
theorem locatedLedgerCommonProduct_finAnchor_eq_outward
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    locatedLedgerCommonProduct Nm mu
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) =
      ∏ i ∈ Finset.univ.erase anchor,
        paperDyadicLocalTarget Nm mu
          (cls i).1 (outwardPositionSkipped O anchor i) := by
  rw [locatedLedgerCommonProduct,
    finAnchorNXLocatedCoarseLedgerWithPhases,
    locatedCommonProduct_markFirstSkippedLocatedPairsRough]
  unfold finAnchorNXLocatedParityLedgerWithPhases
  rw [List.map_append, List.prod_append,
    locatedCommonProduct_map_locatePositionBlocks,
    locatedCommonProduct_map_locatePositionBlocks]
  rw [flatten_pairPositionRun, flatten_pairPositionRun]
  have hleft :
      ((leftAnchorPositions anchor).map fun i =>
        paperDyadicLocalTarget Nm mu (cls i).1
          (positionIncomingSkipped O .reverse i)) =
        (leftAnchorPositions anchor).map fun i =>
          paperDyadicLocalTarget Nm mu (cls i).1
            (outwardPositionSkipped O anchor i) := by
    apply List.map_congr_left
    intro i hi
    rw [outwardPositionSkipped_of_lt]
    exact (mem_leftAnchorPositions_iff anchor i).mp hi
  have hright :
      ((rightAnchorPositions anchor).map fun i =>
        paperDyadicLocalTarget Nm mu (cls i).1
          (positionIncomingSkipped O .forward i)) =
        (rightAnchorPositions anchor).map fun i =>
          paperDyadicLocalTarget Nm mu (cls i).1
            (outwardPositionSkipped O anchor i) := by
    apply List.map_congr_left
    intro i hi
    rw [outwardPositionSkipped_of_gt]
    exact (mem_rightAnchorPositions_iff anchor i).mp hi
  rw [hleft, hright, ← List.prod_append, ← List.map_append]
  simpa [flatten_finAnchorPositionScheduleWithPhases] using
    outwardOrderProduct_eq_nonanchorProduct
      leftPhase rightPhase anchor
      (fun i => paperDyadicLocalTarget Nm mu
        (cls i).1 (outwardPositionSkipped O anchor i))

/-- The common factor is exactly invariant under independent phase flips. -/
theorem locatedLedgerCommonProduct_finAnchor_phase_independent
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase leftPhase' rightPhase' : Bool)
    (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    locatedLedgerCommonProduct Nm mu
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) =
      locatedLedgerCommonProduct Nm mu
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase' rightPhase' anchor cls O) := by
  rw [
    locatedLedgerCommonProduct_finAnchor_eq_outward,
    locatedLedgerCommonProduct_finAnchor_eq_outward]

/-- Equivalent edge-indexed normal form.  This makes the skipped factors
line up definitionally with the outward occurrence ledger. -/
theorem locatedLedgerCommonProduct_finAnchor_eq_edgeProduct
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    locatedLedgerCommonProduct Nm mu
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) =
      ∏ edge : AdjacentIndex m,
        paperDyadicLocalTarget Nm mu
          (cls (outwardEdgeTargetPosition anchor edge)).1
          (decide (edge ∈ O)) := by
  rw [locatedLedgerCommonProduct_finAnchor_eq_outward,
    prod_nonanchor_eq_prod_outwardEdgeTarget]
  apply Finset.prod_congr rfl
  intro edge _hedge
  rw [outwardPositionSkipped_target]

end XYCluster

end

end Anderson4D
