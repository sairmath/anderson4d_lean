import Anderson4D.PermSum.SingleScaleOrientation
import Anderson4D.PermSum.SingleScaleWeightBridge
import Anderson4D.PermSum.SingleScaleSharedElimination
import Anderson4D.PermSum.SingleScalePosition
import Anderson4D.PermSum.SingleScaleAnchorGlue

set_option warningAsError true

/-!
# Original-edge kernels in the anchored outward schedule

This module records the deterministic kernel bookkeeping needed before the
arrangement finite-Fubini step.  Original edges are assigned to the unique
non-anchor endpoint farther from the anchor.  Consequently the anchor is
never enumerated twice and no edge is invented between the two outer
endpoints.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/-- The endpoint of an original edge farther from the anchor. -/
def outwardEdgeTargetPosition {m : ℕ}
    (anchor : Fin m) (edge : AdjacentIndex m) : Fin m :=
  if edge.1.1 < anchor.1 then edge.1 else adjacentSucc edge

theorem outwardEdgeTargetPosition_ne_anchor {m : ℕ}
    (anchor : Fin m) (edge : AdjacentIndex m) :
    outwardEdgeTargetPosition anchor edge ≠ anchor := by
  unfold outwardEdgeTargetPosition
  split_ifs with hleft
  · intro h
    have := congrArg Fin.val h
    omega
  · intro h
    have := congrArg Fin.val h
    simp only [adjacentSucc] at this
    omega

theorem outwardEdgeTargetPosition_injective {m : ℕ}
    (anchor : Fin m) :
    Function.Injective (outwardEdgeTargetPosition anchor) := by
  intro edge₁ edge₂ heq
  unfold outwardEdgeTargetPosition at heq
  by_cases h₁ : edge₁.1.1 < anchor.1 <;>
    by_cases h₂ : edge₂.1.1 < anchor.1
  · simp only [h₁, h₂, if_true] at heq
    exact Subtype.ext heq
  · simp only [h₁, if_true, h₂, if_false] at heq
    have hv := congrArg Fin.val heq
    simp only [adjacentSucc] at hv
    omega
  · simp only [h₁, if_false, h₂, if_true] at heq
    have hv := congrArg Fin.val heq
    simp only [adjacentSucc] at hv
    omega
  · simp only [h₁, h₂, if_false] at heq
    apply Subtype.ext
    apply Fin.ext
    have hv := congrArg Fin.val heq
    simp only [adjacentSucc] at hv
    omega

/--
The original edge entering a position while traversing outward.  It is
`none` exactly at the anchor.
-/
def outwardPositionIncomingEdge {m : ℕ}
    (anchor i : Fin m) : Option (AdjacentIndex m) :=
  if i.1 < anchor.1 then reverseIncomingEdge i
  else if anchor.1 < i.1 then forwardIncomingEdge i
  else none

@[simp] theorem outwardPositionIncomingEdge_anchor {m : ℕ}
    (anchor : Fin m) :
    outwardPositionIncomingEdge anchor anchor = none := by
  simp [outwardPositionIncomingEdge]

theorem outwardPositionIncomingEdge_target {m : ℕ}
    (anchor : Fin m) (edge : AdjacentIndex m) :
    outwardPositionIncomingEdge anchor
      (outwardEdgeTargetPosition anchor edge) = some edge := by
  by_cases hleft : edge.1.1 < anchor.1
  · have hrev : reverseIncomingEdge edge.1 = some edge := by
      unfold reverseIncomingEdge
      rw [dif_pos edge.2]
    simp [outwardEdgeTargetPosition, hleft,
      outwardPositionIncomingEdge, hrev]
  · have hright : anchor.1 < (adjacentSucc edge).1 := by
      simp only [adjacentSucc]
      omega
    have hfwd :
        forwardIncomingEdge (adjacentSucc edge) = some edge := by
      unfold forwardIncomingEdge
      rw [dif_pos (by
        simp only [adjacentSucc]
        omega)]
      congr 2
    have hnleft : ¬(adjacentSucc edge).1 < anchor.1 :=
      not_lt_of_ge (Nat.le_of_lt hright)
    simp [outwardEdgeTargetPosition, hleft,
      outwardPositionIncomingEdge, hright, hnleft, hfwd]

/-- Evaluate an original-edge kernel at the edge entering a position. -/
noncomputable def outwardPositionKernel
    {m : ℕ} (K : AdjacentIndex m → ℝ)
    (anchor i : Fin m) : ℝ :=
  (outwardPositionIncomingEdge anchor i).elim 1 K

@[simp] theorem outwardPositionKernel_target
    {m : ℕ} (K : AdjacentIndex m → ℝ)
    (anchor : Fin m) (edge : AdjacentIndex m) :
    outwardPositionKernel K anchor
      (outwardEdgeTargetPosition anchor edge) = K edge := by
  simp [outwardPositionKernel,
    outwardPositionIncomingEdge_target]

/-- Original edges are in bijection with non-anchor outward positions. -/
theorem edgeKernelProduct_eq_nonanchorPositionProduct
    {m : ℕ} (K : AdjacentIndex m → ℝ) (anchor : Fin m) :
    (∏ edge : AdjacentIndex m, K edge) =
      ∏ i ∈ (Finset.univ.erase anchor),
        outwardPositionKernel K anchor i := by
  classical
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
    exact (outwardPositionKernel_target K anchor edge).symm

private theorem scheduleProduct_eq_nonanchorPositionProduct
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

private theorem prod_map_flatMap_positionEntries
    {α : Type*} (f : α → ℝ)
    (bs : List (PositionBlock α)) :
    ((bs.flatMap PositionBlock.entries).map f).prod =
      (bs.map fun b => (b.entries.map f).prod).prod := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      simp [PositionBlock.entries, ih, List.prod_append]

/-- Kernel factors assigned to one concrete located block. -/
noncomputable def locatedBlockOriginalKernelProduct
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (K : AdjacentIndex m → ℝ) (anchor : Fin m)
    (b : LocatedNXParityBlock (m := m) Nm mu) : ℝ :=
  (b.positionBlock.entries.map
    (outwardPositionKernel K anchor)).prod

/-- Product of the original-edge factors carried by a located ledger. -/
noncomputable def locatedLedgerOriginalKernelProduct
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (K : AdjacentIndex m → ℝ) (anchor : Fin m)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) : ℝ :=
  (bs.map (locatedBlockOriginalKernelProduct Nm mu K anchor)).prod

/--
Exact original-edge decomposition through the concrete coarse schedule.
Every edge occurs once, and the anchor contributes no factor.
-/
theorem edgeKernelProduct_eq_finAnchorNXLocatedCoarse
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m))
    (K : AdjacentIndex m → ℝ) :
    (∏ edge : AdjacentIndex m, K edge) =
      locatedLedgerOriginalKernelProduct Nm mu K anchor
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) := by
  rw [edgeKernelProduct_eq_nonanchorPositionProduct]
  rw [← scheduleProduct_eq_nonanchorPositionProduct
    leftPhase rightPhase anchor]
  rw [prod_map_flatMap_positionEntries]
  unfold locatedLedgerOriginalKernelProduct
    locatedBlockOriginalKernelProduct
  have hmap :=
    map_positionBlock_finAnchorNXLocatedCoarseLedgerWithPhases
      Nm mu leftPhase rightPhase anchor cls O
  have hprod := congrArg
    (fun bs =>
      (bs.map fun b =>
        (b.entries.map (outwardPositionKernel K anchor)).prod).prod)
    hmap
  simpa only [List.map_map, Function.comp_def] using hprod.symm

/-! ## The canonical strong-edge schedule -/

/-- Original edges incident to a scheduled pair block. -/
noncomputable def positionPairAffectedEdges {m : ℕ}
    (bs : List (PositionBlock (Fin m))) :
    Finset (AdjacentIndex m) := by
  classical
  exact bs.toFinset.biUnion fun b =>
    match b with
    | .single _ => ∅
    | .pair i j => (PositionBlock.pair i j).affectedEdges

/--
The strong-kernel edges needed by the outward elimination.  Every original
left edge is strong, because its traversal direction is reversed.  On both
sides, every edge incident to a pair is also strong; in particular this
contains every precise-pair internal edge (and safely also rough-pair
internal edges).
-/
noncomputable def finAnchorNXKernelStrongEdges {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m) :
    Finset (AdjacentIndex m) :=
  (Finset.univ.filter fun edge => edge.1.1 < anchor.1) ∪
    positionPairAffectedEdges
      (finAnchorPositionScheduleWithPhases
        leftPhase rightPhase anchor)

theorem mem_finAnchorNXKernelStrongEdges_of_left {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (edge : AdjacentIndex m) (hleft : edge.1.1 < anchor.1) :
    edge ∈ finAnchorNXKernelStrongEdges
      leftPhase rightPhase anchor := by
  apply Finset.mem_union_left
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hleft⟩

private theorem internalEdge_mem_pair_affectedEdges
    {m : ℕ} (edge : AdjacentIndex m) (i j : Fin m)
    (horientation :
      (edge.1 = i ∧ i.1 + 1 = j.1) ∨
        (edge.1 = j ∧ j.1 + 1 = i.1)) :
    edge ∈ (PositionBlock.pair i j).affectedEdges := by
  rcases horientation with hforward | hreverse
  · rcases hforward with ⟨heq, _hadj⟩
    subst i
    simp [PositionBlock.affectedEdges, positionIncidentEdges,
      reverseIncomingEdge, edge.2]
  · rcases hreverse with ⟨heq, _hadj⟩
    subst j
    simp [PositionBlock.affectedEdges, positionIncidentEdges,
      reverseIncomingEdge, edge.2]

/-- Every concrete scheduled pair has a strong internal original edge. -/
theorem finAnchorNXKernelStrongEdges_pair_internal
    {m : ℕ} (leftPhase rightPhase : Bool) (anchor i j : Fin m)
    (hpair :
      PositionBlock.pair i j ∈
        finAnchorPositionScheduleWithPhases
          leftPhase rightPhase anchor) :
    ∃ edge : AdjacentIndex m,
      edge ∈ finAnchorNXKernelStrongEdges
          leftPhase rightPhase anchor ∧
        ((edge.1 = i ∧ i.1 + 1 = j.1) ∨
          (edge.1 = j ∧ j.1 + 1 = i.1)) := by
  obtain ⟨edge, _hcarrier, horientation⟩ :=
    finAnchorPositionSchedule_pair_internalEdge_mem_phaseCarrier
      leftPhase rightPhase anchor i j hpair
  refine ⟨edge, ?_, horientation⟩
  apply Finset.mem_union.mpr
  right
  unfold positionPairAffectedEdges
  apply Finset.mem_biUnion.mpr
  refine ⟨PositionBlock.pair i j, ?_, ?_⟩
  · exact List.mem_toFinset.mpr hpair
  · exact internalEdge_mem_pair_affectedEdges
      edge i j horientation

/-! ## Metadata retained by rough marking -/

private def scheduledPairPayload
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (cls : Fin m → ActiveNXClass Nm mu)
    (incomingSkipped : Fin m → Bool) (i j : Fin m) :
    NXPairBlock Nm mu where
  left := cls i
  right := cls j
  skipLeft := incomingSkipped i
  skipRight := incomingSkipped j

/--
Exact side, class, and skip metadata of a block in the anchored located
schedule.  Separate rough constructors make the effect of marking
explicit without weakening any payload equality.
-/
inductive FinAnchorLocatedBlockMetadata
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    LocatedNXParityBlock (m := m) Nm mu → Prop
  | leftSingle (i : Fin m)
      (hmem : PositionBlock.single i ∈
        pairPositionRun leftPhase (leftAnchorPositions anchor)) :
      FinAnchorLocatedBlockMetadata Nm mu leftPhase rightPhase anchor cls O
        (.single i (cls i) (positionIncomingSkipped O .reverse i))
  | rightSingle (i : Fin m)
      (hmem : PositionBlock.single i ∈
        pairPositionRun rightPhase (rightAnchorPositions anchor)) :
      FinAnchorLocatedBlockMetadata Nm mu leftPhase rightPhase anchor cls O
        (.single i (cls i) (positionIncomingSkipped O .forward i))
  | leftPair (i j : Fin m)
      (hmem : PositionBlock.pair i j ∈
        pairPositionRun leftPhase (leftAnchorPositions anchor)) :
      FinAnchorLocatedBlockMetadata Nm mu leftPhase rightPhase anchor cls O
        (.pair i j
          (scheduledPairPayload Nm mu cls
            (positionIncomingSkipped O .reverse) i j))
  | rightPair (i j : Fin m)
      (hmem : PositionBlock.pair i j ∈
        pairPositionRun rightPhase (rightAnchorPositions anchor)) :
      FinAnchorLocatedBlockMetadata Nm mu leftPhase rightPhase anchor cls O
        (.pair i j
          (scheduledPairPayload Nm mu cls
            (positionIncomingSkipped O .forward) i j))
  | leftRoughPair (i j : Fin m)
      (hmem : PositionBlock.pair i j ∈
        pairPositionRun leftPhase (leftAnchorPositions anchor)) :
      FinAnchorLocatedBlockMetadata Nm mu leftPhase rightPhase anchor cls O
        (.roughPair i j
          (scheduledPairPayload Nm mu cls
            (positionIncomingSkipped O .reverse) i j))
  | rightRoughPair (i j : Fin m)
      (hmem : PositionBlock.pair i j ∈
        pairPositionRun rightPhase (rightAnchorPositions anchor)) :
      FinAnchorLocatedBlockMetadata Nm mu leftPhase rightPhase anchor cls O
        (.roughPair i j
          (scheduledPairPayload Nm mu cls
            (positionIncomingSkipped O .forward) i j))

private theorem FinAnchorLocatedBlockMetadata.roughen
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    {leftPhase rightPhase : Bool} {anchor : Fin m}
    {cls : Fin m → ActiveNXClass Nm mu}
    {O : Finset (AdjacentIndex m)}
    {i j : Fin m} {p : NXPairBlock Nm mu}
    (hmeta :
      FinAnchorLocatedBlockMetadata Nm mu
        leftPhase rightPhase anchor cls O (.pair i j p)) :
    FinAnchorLocatedBlockMetadata Nm mu
      leftPhase rightPhase anchor cls O (.roughPair i j p) := by
  cases hmeta with
  | leftPair i j hmem =>
      exact .leftRoughPair i j hmem
  | rightPair i j hmem =>
      exact .rightRoughPair i j hmem

private theorem metadata_markFirstSkippedLocatedPairsRough
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    {leftPhase rightPhase : Bool} {anchor : Fin m}
    {cls : Fin m → ActiveNXClass Nm mu}
    {O : Finset (AdjacentIndex m)}
    (fuel : ℕ)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu))
    (hmeta : ∀ b ∈ bs,
      FinAnchorLocatedBlockMetadata Nm mu
        leftPhase rightPhase anchor cls O b)
    (b : LocatedNXParityBlock (m := m) Nm mu)
    (hb : b ∈ markFirstSkippedLocatedPairsRough fuel bs) :
    FinAnchorLocatedBlockMetadata Nm mu
      leftPhase rightPhase anchor cls O b := by
  induction bs generalizing fuel b with
  | nil =>
      simp [markFirstSkippedLocatedPairsRough] at hb
  | cons head tail ih =>
      cases fuel with
      | zero =>
          exact hmeta b hb
      | succ fuel =>
          cases head with
          | single i a skipped =>
              rw [markFirstSkippedLocatedPairsRough] at hb
              rcases List.mem_cons.mp hb with hhead | htail
              · cases hhead
                exact hmeta _ (by simp)
              · exact ih (fuel + 1)
                  (fun q hq => hmeta q
                    (List.mem_cons.mpr (Or.inr hq)))
                  b htail
          | pair i j p =>
              by_cases htouch : nxPairBlockTouchesSkip p
              · rw [markFirstSkippedLocatedPairsRough,
                  if_pos htouch] at hb
                rcases List.mem_cons.mp hb with hhead | htail
                · cases hhead
                  exact
                    (hmeta _ (by simp)).roughen
                · exact ih fuel
                    (fun q hq => hmeta q
                      (List.mem_cons.mpr (Or.inr hq)))
                    b htail
              · have hfalse :
                    nxPairBlockTouchesSkip p = false :=
                  Bool.eq_false_of_not_eq_true htouch
                rw [markFirstSkippedLocatedPairsRough,
                  hfalse] at hb
                rcases List.mem_cons.mp hb with hhead | htail
                · cases hhead
                  exact hmeta _ (by simp)
                · exact ih (fuel + 1)
                    (fun q hq => hmeta q
                      (List.mem_cons.mpr (Or.inr hq)))
                    b htail
          | roughPair i j p =>
              rw [markFirstSkippedLocatedPairsRough] at hb
              rcases List.mem_cons.mp hb with hhead | htail
              · cases hhead
                exact hmeta _ (by simp)
              · exact ih (fuel + 1)
                  (fun q hq => hmeta q
                    (List.mem_cons.mpr (Or.inr hq)))
                  b htail

private theorem rawLocatedLedger_metadata
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m))
    (b : LocatedNXParityBlock (m := m) Nm mu)
    (hb : b ∈ finAnchorNXLocatedParityLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O) :
    FinAnchorLocatedBlockMetadata Nm mu
      leftPhase rightPhase anchor cls O b := by
  rw [finAnchorNXLocatedParityLedgerWithPhases,
    List.mem_append] at hb
  rcases hb with hleft | hright
  · obtain ⟨pb, hpb, rfl⟩ := List.mem_map.mp hleft
    cases pb with
    | single i =>
        exact .leftSingle i hpb
    | pair i j =>
        exact .leftPair i j hpb
  · obtain ⟨pb, hpb, rfl⟩ := List.mem_map.mp hright
    cases pb with
    | single i =>
        exact .rightSingle i hpb
    | pair i j =>
        exact .rightPair i j hpb

/-- Every coarse located block retains its exact raw side and payload. -/
theorem finAnchorNXLocatedCoarse_block_metadata
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m))
    (b : LocatedNXParityBlock (m := m) Nm mu)
    (hb : b ∈ finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O) :
    FinAnchorLocatedBlockMetadata Nm mu
      leftPhase rightPhase anchor cls O b := by
  apply metadata_markFirstSkippedLocatedPairsRough
    3
    (finAnchorNXLocatedParityLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O)
    (fun q hq => rawLocatedLedger_metadata
      Nm mu leftPhase rightPhase anchor cls O q hq)
    b
  exact hb

/-! ## Pointwise local factors in CPS order -/

private theorem pairPositionRun_single_mem
    {α : Type*} (phase : Bool) (xs : List α) (i : α)
    (h : PositionBlock.single i ∈ pairPositionRun phase xs) :
    i ∈ xs := by
  rw [← flatten_pairPositionRun phase xs, List.mem_flatMap]
  exact ⟨PositionBlock.single i, h,
    by simp [PositionBlock.entries]⟩

private theorem pair_mem_pairPositionRun_range_step
    (phase : Bool) (start len x y : ℕ)
    (h : PositionBlock.pair x y ∈
      pairPositionRun phase (List.range' start len)) :
    y = x + 1 := by
  cases phase with
  | false =>
      induction len using Nat.twoStepInduction generalizing start x y with
      | zero =>
          simp [pairPositionRun] at h
      | one =>
          simp [List.range'_succ, pairPositionRun] at h
      | more n ih0 _ih1 =>
          have hrange :
              List.range' start (n + 2) =
                start :: (start + 1) ::
                  List.range' (start + 2) n := by
            rw [show n + 2 = (n + 1) + 1 by omega,
              List.range'_succ, List.range'_succ]
          rw [hrange] at h
          simp only [pairPositionRun, List.mem_cons] at h
          rcases h with hhead | htail
          · cases hhead
            omega
          · exact ih0 (start + 2) x y htail
  | true =>
      cases len with
      | zero =>
          simp [pairPositionRun] at h
      | succ len =>
          rw [List.range'_succ] at h
          simp only [pairPositionRun, List.mem_cons] at h
          rcases h with hbad | htail
          · cases hbad
          · exact pair_mem_pairPositionRun_range_step
              false (start + 1) len x y htail

private theorem leftPair_descends
    {m : ℕ} (phase : Bool) (anchor i j : Fin m)
    (hpair : PositionBlock.pair i j ∈
      pairPositionRun phase (leftAnchorPositions anchor)) :
    j.1 + 1 = i.1 := by
  have hendpoints :=
    pairPositionRun_pair_endpoints_mem
      phase (leftAnchorPositions anchor) i j hpair
  have hi : i.1 < anchor.1 :=
    (mem_leftAnchorPositions_iff anchor i).mp hendpoints.1
  have hj : j.1 < anchor.1 :=
    (mem_leftAnchorPositions_iff anchor j).mp hendpoints.2
  have hmapped :
      PositionBlock.pair
          (anchorPositionOutwardOffset anchor i)
          (anchorPositionOutwardOffset anchor j) ∈
        pairPositionRun phase (List.range anchor.1) := by
    rw [← map_anchorPositionOutwardOffset_left,
      ← pairPositionRun_map]
    exact List.mem_map_of_mem hpair
  rw [List.range_eq_range'] at hmapped
  have hstep :=
    pair_mem_pairPositionRun_range_step phase 0 anchor.1
      (anchorPositionOutwardOffset anchor i)
      (anchorPositionOutwardOffset anchor j) hmapped
  simp only [anchorPositionOutwardOffset,
    if_pos hi, if_pos hj] at hstep
  omega

private theorem rightPair_ascends
    {m : ℕ} (phase : Bool) (anchor i j : Fin m)
    (hpair : PositionBlock.pair i j ∈
      pairPositionRun phase (rightAnchorPositions anchor)) :
    i.1 + 1 = j.1 := by
  have hendpoints :=
    pairPositionRun_pair_endpoints_mem
      phase (rightAnchorPositions anchor) i j hpair
  have hi : anchor.1 < i.1 :=
    (mem_rightAnchorPositions_iff anchor i).mp hendpoints.1
  have hj : anchor.1 < j.1 :=
    (mem_rightAnchorPositions_iff anchor j).mp hendpoints.2
  have hmapped :
      PositionBlock.pair
          (anchorPositionOutwardOffset anchor i)
          (anchorPositionOutwardOffset anchor j) ∈
        pairPositionRun phase
          (List.range (m - (anchor.1 + 1))) := by
    rw [← map_anchorPositionOutwardOffset_right,
      ← pairPositionRun_map]
    exact List.mem_map_of_mem hpair
  rw [List.range_eq_range'] at hmapped
  have hstep :=
    pair_mem_pairPositionRun_range_step phase 0
      (m - (anchor.1 + 1))
      (anchorPositionOutwardOffset anchor i)
      (anchorPositionOutwardOffset anchor j) hmapped
  simp only [anchorPositionOutwardOffset,
    if_neg (not_lt_of_ge (Nat.le_of_lt hi)),
    if_neg (not_lt_of_ge (Nat.le_of_lt hj))] at hstep
  omega

/-- The position immediately closer to the anchor in the outward run. -/
def outwardPreviousPosition {m : ℕ}
    (anchor i : Fin m) : Fin m :=
  if hleft : i.1 < anchor.1 then
    ⟨i.1 + 1, by omega⟩
  else if hright : anchor.1 < i.1 then
    ⟨i.1 - 1, by omega⟩
  else anchor

/--
The local lambda/strongLambda monomial consumed by one CPS block at a
fixed arrangement.
-/
noncomputable def locatedBlockEliminationKernel
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (anchor : Fin m)
    (σ : Fin m → HeppLabeledCopy mu) :
    LocatedNXParityBlock (m := m) Nm mu → ℝ
  | .single i a skipped =>
      let ca := nxClassCluster ht hroot Nm mu z hz a.1 a.2
      ca.lambda R skipped
        (labeledCopyPoint z (σ (outwardPreviousPosition anchor i)))
        (labeledCopyPoint z (σ i))
  | .pair i j p | .roughPair i j p =>
      let ca :=
        nxClassCluster ht hroot Nm mu z hz p.left.1 p.left.2
      let cb :=
        nxClassCluster ht hroot Nm mu z hz p.right.1 p.right.2
      ca.lambda R p.skipLeft
          (labeledCopyPoint z
            (σ (outwardPreviousPosition anchor i)))
          (labeledCopyPoint z (σ i)) *
        strongLambda ca cb R p.skipRight
          (labeledCopyPoint z (σ i))
          (labeledCopyPoint z (σ j))

noncomputable def locatedLedgerEliminationKernelProduct
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (anchor : Fin m)
    (σ : Fin m → HeppLabeledCopy mu)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) : ℝ :=
  (bs.map
    (locatedBlockEliminationKernel
      ht hroot Nm mu z hz R anchor σ)).prod

/-- The fixed-arrangement original-edge kernel with the canonical schedule
of strong cutoffs. -/
noncomputable def finAnchorNXArrangementEdgeKernel
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (O : Finset (AdjacentIndex m))
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (σ : Fin m → HeppLabeledCopy mu)
    (edge : AdjacentIndex m) : ℝ :=
  nxClassEdgeKernel ht hroot Nm mu z hz R O
    (finAnchorNXKernelStrongEdges leftPhase rightPhase anchor)
    cls (fun i => (σ i).1) edge

private theorem leftIncomingKernel_le_lambda
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (O : Finset (AdjacentIndex m))
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (σ : Fin m → HeppLabeledCopy mu)
    (i : Fin m) (hi : i.1 < anchor.1) :
    outwardPositionKernel
        (finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls σ)
        anchor i ≤
      (nxClassCluster ht hroot Nm mu z hz
        (cls i).1 (cls i).2).lambda R
        (positionIncomingSkipped O .reverse i)
        (labeledCopyPoint z
          (σ (outwardPreviousPosition anchor i)))
        (labeledCopyPoint z (σ i)) := by
  let edge : AdjacentIndex m := ⟨i, by omega⟩
  have hrev : reverseIncomingEdge i = some edge := by
    unfold reverseIncomingEdge
    rw [dif_pos edge.2]
  have hincoming :
      outwardPositionIncomingEdge anchor i = some edge := by
    simp [outwardPositionIncomingEdge, hi, hrev]
  have hstrong :
      edge ∈ finAnchorNXKernelStrongEdges
        leftPhase rightPhase anchor :=
    mem_finAnchorNXKernelStrongEdges_of_left
      leftPhase rightPhase anchor edge hi
  have hprev :
      outwardPreviousPosition anchor i = adjacentSucc edge := by
    apply Fin.ext
    simp [outwardPreviousPosition, hi, adjacentSucc, edge]
  have hskip :
      positionIncomingSkipped O .reverse i =
        decide (edge ∈ O) := by
    simp [positionIncomingSkipped, hrev]
  let ci :=
    nxClassCluster ht hroot Nm mu z hz
      (cls i).1 (cls i).2
  let cp :=
    nxClassCluster ht hroot Nm mu z hz
      (cls (adjacentSucc edge)).1 (cls (adjacentSucc edge)).2
  calc
    outwardPositionKernel
        (finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls σ)
        anchor i =
      strongLambda ci cp R (decide (edge ∈ O))
        (labeledCopyPoint z (σ i))
        (labeledCopyPoint z (σ (adjacentSucc edge))) := by
          simp [outwardPositionKernel, hincoming,
            finAnchorNXArrangementEdgeKernel, nxClassEdgeKernel,
            hstrong, edge, ci, cp, labeledCopyPoint]
    _ ≤ ci.lambda R (decide (edge ∈ O))
        (labeledCopyPoint z (σ i))
        (labeledCopyPoint z (σ (adjacentSucc edge))) :=
      strongLambda_le_leftLambda _ _ _ _ _ _
    _ = (nxClassCluster ht hroot Nm mu z hz
          (cls i).1 (cls i).2).lambda R
        (positionIncomingSkipped O .reverse i)
        (labeledCopyPoint z
          (σ (outwardPreviousPosition anchor i)))
        (labeledCopyPoint z (σ i)) := by
      rw [hskip, hprev]
      exact lambda_comm ci R (decide (edge ∈ O))
        (labeledCopyPoint z (σ i))
        (labeledCopyPoint z (σ (adjacentSucc edge)))

private theorem rightIncomingKernel_le_lambda
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (O : Finset (AdjacentIndex m))
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (σ : Fin m → HeppLabeledCopy mu)
    (i : Fin m) (hi : anchor.1 < i.1) :
    outwardPositionKernel
        (finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls σ)
        anchor i ≤
      (nxClassCluster ht hroot Nm mu z hz
        (cls i).1 (cls i).2).lambda R
        (positionIncomingSkipped O .forward i)
        (labeledCopyPoint z
          (σ (outwardPreviousPosition anchor i)))
        (labeledCopyPoint z (σ i)) := by
  let lower : Fin m := ⟨i.1 - 1, by omega⟩
  let edge : AdjacentIndex m := ⟨lower, by
    dsimp [lower]
    omega⟩
  have hfwd : forwardIncomingEdge i = some edge := by
    unfold forwardIncomingEdge
    rw [dif_pos (by omega)]
  have hincoming :
      outwardPositionIncomingEdge anchor i = some edge := by
    simp [outwardPositionIncomingEdge,
      not_lt_of_ge (Nat.le_of_lt hi), hi, hfwd]
  have hprev :
      outwardPreviousPosition anchor i = edge.1 := by
    apply Fin.ext
    simp [outwardPreviousPosition,
      not_lt_of_ge (Nat.le_of_lt hi), hi, edge, lower]
  have hsucc : adjacentSucc edge = i := by
    apply Fin.ext
    simp [adjacentSucc, edge, lower]
    omega
  have hskip :
      positionIncomingSkipped O .forward i =
        decide (edge ∈ O) := by
    simp [positionIncomingSkipped, hfwd]
  let cp :=
    nxClassCluster ht hroot Nm mu z hz
      (cls edge.1).1 (cls edge.1).2
  let ci :=
    nxClassCluster ht hroot Nm mu z hz
      (cls i).1 (cls i).2
  by_cases hstrong :
      edge ∈ finAnchorNXKernelStrongEdges
        leftPhase rightPhase anchor
  · calc
      outwardPositionKernel
          (finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
            R O leftPhase rightPhase anchor cls σ)
          anchor i =
        strongLambda cp ci R (decide (edge ∈ O))
          (labeledCopyPoint z (σ edge.1))
          (labeledCopyPoint z (σ i)) := by
            simp [outwardPositionKernel, hincoming,
              finAnchorNXArrangementEdgeKernel, nxClassEdgeKernel,
              hstrong, hsucc, cp, ci, labeledCopyPoint]
      _ ≤ ci.lambda R (decide (edge ∈ O))
          (labeledCopyPoint z (σ edge.1))
          (labeledCopyPoint z (σ i)) :=
        strongLambda_le_rightLambda _ _ _ _ _ _
      _ = (nxClassCluster ht hroot Nm mu z hz
            (cls i).1 (cls i).2).lambda R
          (positionIncomingSkipped O .forward i)
          (labeledCopyPoint z
            (σ (outwardPreviousPosition anchor i)))
          (labeledCopyPoint z (σ i)) := by
        rw [hskip, hprev]
  · exact le_of_eq (by
      simp [outwardPositionKernel, hincoming,
        finAnchorNXArrangementEdgeKernel, nxClassEdgeKernel,
        hstrong, hsucc, hskip, hprev, labeledCopyPoint])

private theorem leftPairInternalKernel_eq_strongLambda
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (O : Finset (AdjacentIndex m))
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (σ : Fin m → HeppLabeledCopy mu)
    (i j : Fin m)
    (hpair : PositionBlock.pair i j ∈
      pairPositionRun leftPhase (leftAnchorPositions anchor)) :
    outwardPositionKernel
        (finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls σ)
        anchor j =
      strongLambda
        (nxClassCluster ht hroot Nm mu z hz
          (cls i).1 (cls i).2)
        (nxClassCluster ht hroot Nm mu z hz
          (cls j).1 (cls j).2)
        R (positionIncomingSkipped O .reverse j)
        (labeledCopyPoint z (σ i))
        (labeledCopyPoint z (σ j)) := by
  have hendpoints :=
    pairPositionRun_pair_endpoints_mem
      leftPhase (leftAnchorPositions anchor) i j hpair
  have hj : j.1 < anchor.1 :=
    (mem_leftAnchorPositions_iff anchor j).mp hendpoints.2
  have hadj : j.1 + 1 = i.1 :=
    leftPair_descends leftPhase anchor i j hpair
  let edge : AdjacentIndex m := ⟨j, by omega⟩
  have hrev : reverseIncomingEdge j = some edge := by
    unfold reverseIncomingEdge
    rw [dif_pos edge.2]
  have hincoming :
      outwardPositionIncomingEdge anchor j = some edge := by
    simp [outwardPositionIncomingEdge, hj, hrev]
  have hsucc : adjacentSucc edge = i := by
    apply Fin.ext
    simp [adjacentSucc, edge]
    omega
  have hfull :
      PositionBlock.pair i j ∈
        finAnchorPositionScheduleWithPhases
          leftPhase rightPhase anchor := by
    simpa [finAnchorPositionScheduleWithPhases,
      anchorPositionScheduleWithPhases] using
        (List.mem_append_left
          (pairPositionRun rightPhase
            (rightAnchorPositions anchor)) hpair)
  have hstrong :
      edge ∈ finAnchorNXKernelStrongEdges
        leftPhase rightPhase anchor := by
    apply Finset.mem_union_right
    unfold positionPairAffectedEdges
    apply Finset.mem_biUnion.mpr
    refine ⟨PositionBlock.pair i j,
      List.mem_toFinset.mpr hfull, ?_⟩
    exact internalEdge_mem_pair_affectedEdges
      edge i j (Or.inr ⟨rfl, hadj⟩)
  have hskip :
      positionIncomingSkipped O .reverse j =
        decide (edge ∈ O) := by
    simp [positionIncomingSkipped, hrev]
  let ci :=
    nxClassCluster ht hroot Nm mu z hz
      (cls i).1 (cls i).2
  let cj :=
    nxClassCluster ht hroot Nm mu z hz
      (cls j).1 (cls j).2
  calc
    outwardPositionKernel
        (finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls σ)
        anchor j =
      strongLambda cj ci R (decide (edge ∈ O))
        (labeledCopyPoint z (σ j))
        (labeledCopyPoint z (σ i)) := by
          simp [outwardPositionKernel, hincoming,
            finAnchorNXArrangementEdgeKernel, nxClassEdgeKernel,
            hstrong, hsucc, edge, ci, cj, labeledCopyPoint]
    _ = strongLambda ci cj R
        (positionIncomingSkipped O .reverse j)
        (labeledCopyPoint z (σ i))
        (labeledCopyPoint z (σ j)) := by
      rw [hskip]
      exact strongLambda_comm cj ci R (decide (edge ∈ O))
        (labeledCopyPoint z (σ j))
        (labeledCopyPoint z (σ i))

private theorem rightPairInternalKernel_eq_strongLambda
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (O : Finset (AdjacentIndex m))
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (σ : Fin m → HeppLabeledCopy mu)
    (i j : Fin m)
    (hpair : PositionBlock.pair i j ∈
      pairPositionRun rightPhase (rightAnchorPositions anchor)) :
    outwardPositionKernel
        (finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls σ)
        anchor j =
      strongLambda
        (nxClassCluster ht hroot Nm mu z hz
          (cls i).1 (cls i).2)
        (nxClassCluster ht hroot Nm mu z hz
          (cls j).1 (cls j).2)
        R (positionIncomingSkipped O .forward j)
        (labeledCopyPoint z (σ i))
        (labeledCopyPoint z (σ j)) := by
  have hendpoints :=
    pairPositionRun_pair_endpoints_mem
      rightPhase (rightAnchorPositions anchor) i j hpair
  have hj : anchor.1 < j.1 :=
    (mem_rightAnchorPositions_iff anchor j).mp hendpoints.2
  have hadj : i.1 + 1 = j.1 :=
    rightPair_ascends rightPhase anchor i j hpair
  let edge : AdjacentIndex m := ⟨i, by omega⟩
  have hfwd : forwardIncomingEdge j = some edge := by
    unfold forwardIncomingEdge
    rw [dif_pos (by omega)]
    congr 2
    apply Fin.ext
    simp
    omega
  have hincoming :
      outwardPositionIncomingEdge anchor j = some edge := by
    simp [outwardPositionIncomingEdge,
      not_lt_of_ge (Nat.le_of_lt hj), hj, hfwd]
  have hsucc : adjacentSucc edge = j := by
    apply Fin.ext
    simp [adjacentSucc, edge]
    omega
  have hfull :
      PositionBlock.pair i j ∈
        finAnchorPositionScheduleWithPhases
          leftPhase rightPhase anchor := by
    simpa [finAnchorPositionScheduleWithPhases,
      anchorPositionScheduleWithPhases] using
        (List.mem_append_right
          (pairPositionRun leftPhase
            (leftAnchorPositions anchor)) hpair)
  have hstrong :
      edge ∈ finAnchorNXKernelStrongEdges
        leftPhase rightPhase anchor := by
    apply Finset.mem_union_right
    unfold positionPairAffectedEdges
    apply Finset.mem_biUnion.mpr
    refine ⟨PositionBlock.pair i j,
      List.mem_toFinset.mpr hfull, ?_⟩
    exact internalEdge_mem_pair_affectedEdges
      edge i j (Or.inl ⟨rfl, hadj⟩)
  have hskip :
      positionIncomingSkipped O .forward j =
        decide (edge ∈ O) := by
    simp [positionIncomingSkipped, hfwd]
  let ci :=
    nxClassCluster ht hroot Nm mu z hz
      (cls i).1 (cls i).2
  let cj :=
    nxClassCluster ht hroot Nm mu z hz
      (cls j).1 (cls j).2
  simp [outwardPositionKernel, hincoming,
    finAnchorNXArrangementEdgeKernel, nxClassEdgeKernel,
    hstrong, hsucc, hskip, edge, labeledCopyPoint]

private theorem kernelLambda_nonneg
    (c : XYCluster) (R : ℝ) (skipped : Bool)
    (u x : Fin 4 → ℤ) :
    0 ≤ c.lambda R skipped u x := by
  unfold lambda
  split_ifs <;> positivity

private theorem kernelStrongLambda_nonneg
    (a b : XYCluster) (R : ℝ) (skipped : Bool)
    (x y : Fin 4 → ℤ) :
    0 ≤ strongLambda a b R skipped x y := by
  unfold strongLambda
  split_ifs <;> positivity

/--
For each concrete block in the marked anchored ledger, the original-edge
factors assigned to its positions are bounded by the lambda/strongLambda
monomial in the outward CPS order.
-/
theorem locatedBlockOriginalKernelProduct_le_eliminationKernel
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (O : Finset (AdjacentIndex m))
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (σ : Fin m → HeppLabeledCopy mu)
    (b : LocatedNXParityBlock (m := m) Nm mu)
    (hb : b ∈ finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O) :
    locatedBlockOriginalKernelProduct Nm mu
        (finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls σ)
        anchor b ≤
      locatedBlockEliminationKernel
        ht hroot Nm mu z hz R anchor σ b := by
  have hmeta :=
    finAnchorNXLocatedCoarse_block_metadata Nm mu
      leftPhase rightPhase anchor cls O b hb
  cases hmeta with
  | leftSingle i hmem =>
      have hi : i.1 < anchor.1 :=
        (mem_leftAnchorPositions_iff anchor i).mp
          (pairPositionRun_single_mem
            leftPhase (leftAnchorPositions anchor) i hmem)
      simpa [locatedBlockOriginalKernelProduct,
        LocatedNXParityBlock.positionBlock, PositionBlock.entries,
        locatedBlockEliminationKernel] using
          leftIncomingKernel_le_lambda ht hroot Nm mu z hz
            R O leftPhase rightPhase anchor cls σ i hi
  | rightSingle i hmem =>
      have hi : anchor.1 < i.1 :=
        (mem_rightAnchorPositions_iff anchor i).mp
          (pairPositionRun_single_mem
            rightPhase (rightAnchorPositions anchor) i hmem)
      simpa [locatedBlockOriginalKernelProduct,
        LocatedNXParityBlock.positionBlock, PositionBlock.entries,
        locatedBlockEliminationKernel] using
          rightIncomingKernel_le_lambda ht hroot Nm mu z hz
            R O leftPhase rightPhase anchor cls σ i hi
  | leftPair i j hmem =>
      have hendpoints :=
        pairPositionRun_pair_endpoints_mem
          leftPhase (leftAnchorPositions anchor) i j hmem
      have hi : i.1 < anchor.1 :=
        (mem_leftAnchorPositions_iff anchor i).mp hendpoints.1
      have hfirst :=
        leftIncomingKernel_le_lambda ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls σ i hi
      have hsecond :=
        leftPairInternalKernel_eq_strongLambda ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls σ i j hmem
      simp only [locatedBlockOriginalKernelProduct,
        LocatedNXParityBlock.positionBlock, PositionBlock.entries,
        locatedBlockEliminationKernel, scheduledPairPayload,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
      rw [hsecond]
      exact mul_le_mul_of_nonneg_right hfirst
        (kernelStrongLambda_nonneg
          (nxClassCluster ht hroot Nm mu z hz
            (cls i).1 (cls i).2)
          (nxClassCluster ht hroot Nm mu z hz
            (cls j).1 (cls j).2)
          R (positionIncomingSkipped O .reverse j)
          (labeledCopyPoint z (σ i))
          (labeledCopyPoint z (σ j)))
  | rightPair i j hmem =>
      have hendpoints :=
        pairPositionRun_pair_endpoints_mem
          rightPhase (rightAnchorPositions anchor) i j hmem
      have hi : anchor.1 < i.1 :=
        (mem_rightAnchorPositions_iff anchor i).mp hendpoints.1
      have hfirst :=
        rightIncomingKernel_le_lambda ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls σ i hi
      have hsecond :=
        rightPairInternalKernel_eq_strongLambda ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls σ i j hmem
      simp only [locatedBlockOriginalKernelProduct,
        LocatedNXParityBlock.positionBlock, PositionBlock.entries,
        locatedBlockEliminationKernel, scheduledPairPayload,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
      rw [hsecond]
      exact mul_le_mul_of_nonneg_right hfirst
        (kernelStrongLambda_nonneg
          (nxClassCluster ht hroot Nm mu z hz
            (cls i).1 (cls i).2)
          (nxClassCluster ht hroot Nm mu z hz
            (cls j).1 (cls j).2)
          R (positionIncomingSkipped O .forward j)
          (labeledCopyPoint z (σ i))
          (labeledCopyPoint z (σ j)))
  | leftRoughPair i j hmem =>
      have hendpoints :=
        pairPositionRun_pair_endpoints_mem
          leftPhase (leftAnchorPositions anchor) i j hmem
      have hi : i.1 < anchor.1 :=
        (mem_leftAnchorPositions_iff anchor i).mp hendpoints.1
      have hfirst :=
        leftIncomingKernel_le_lambda ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls σ i hi
      have hsecond :=
        leftPairInternalKernel_eq_strongLambda ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls σ i j hmem
      simp only [locatedBlockOriginalKernelProduct,
        LocatedNXParityBlock.positionBlock, PositionBlock.entries,
        locatedBlockEliminationKernel, scheduledPairPayload,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
      rw [hsecond]
      exact mul_le_mul_of_nonneg_right hfirst
        (kernelStrongLambda_nonneg
          (nxClassCluster ht hroot Nm mu z hz
            (cls i).1 (cls i).2)
          (nxClassCluster ht hroot Nm mu z hz
            (cls j).1 (cls j).2)
          R (positionIncomingSkipped O .reverse j)
          (labeledCopyPoint z (σ i))
          (labeledCopyPoint z (σ j)))
  | rightRoughPair i j hmem =>
      have hendpoints :=
        pairPositionRun_pair_endpoints_mem
          rightPhase (rightAnchorPositions anchor) i j hmem
      have hi : anchor.1 < i.1 :=
        (mem_rightAnchorPositions_iff anchor i).mp hendpoints.1
      have hfirst :=
        rightIncomingKernel_le_lambda ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls σ i hi
      have hsecond :=
        rightPairInternalKernel_eq_strongLambda ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls σ i j hmem
      simp only [locatedBlockOriginalKernelProduct,
        LocatedNXParityBlock.positionBlock, PositionBlock.entries,
        locatedBlockEliminationKernel, scheduledPairPayload,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
      rw [hsecond]
      exact mul_le_mul_of_nonneg_right hfirst
        (kernelStrongLambda_nonneg
          (nxClassCluster ht hroot Nm mu z hz
            (cls i).1 (cls i).2)
          (nxClassCluster ht hroot Nm mu z hz
            (cls j).1 (cls j).2)
          R (positionIncomingSkipped O .forward j)
          (labeledCopyPoint z (σ i))
          (labeledCopyPoint z (σ j)))

private theorem outwardPositionKernel_nonneg
    {m : ℕ} (K : AdjacentIndex m → ℝ)
    (hK : ∀ edge, 0 ≤ K edge)
    (anchor i : Fin m) :
    0 ≤ outwardPositionKernel K anchor i := by
  unfold outwardPositionKernel
  cases h :
      outwardPositionIncomingEdge anchor i with
  | none => simp
  | some edge => simpa [h] using hK edge

private theorem locatedBlockOriginalKernelProduct_nonneg
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (K : AdjacentIndex m → ℝ)
    (hK : ∀ edge, 0 ≤ K edge)
    (anchor : Fin m)
    (b : LocatedNXParityBlock (m := m) Nm mu) :
    0 ≤ locatedBlockOriginalKernelProduct Nm mu K anchor b := by
  unfold locatedBlockOriginalKernelProduct
  apply List.prod_nonneg
  intro q hq
  obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hq
  exact outwardPositionKernel_nonneg K hK anchor i

/--
The complete original-edge product of a fixed arrangement is bounded by
the product of the outward local elimination monomials.  The proof uses
the exact edge-to-position bijection, so there is no anchor factor and no
edge joining the two outward runs.
-/
theorem edgeKernelProduct_le_finAnchorNXLocatedEliminationProduct
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (O : Finset (AdjacentIndex m))
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (σ : Fin m → HeppLabeledCopy mu) :
    (∏ edge : AdjacentIndex m,
      finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
        R O leftPhase rightPhase anchor cls σ edge) ≤
      locatedLedgerEliminationKernelProduct
        ht hroot Nm mu z hz R anchor σ
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) := by
  rw [edgeKernelProduct_eq_finAnchorNXLocatedCoarse
    Nm mu leftPhase rightPhase anchor cls O
      (finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
        R O leftPhase rightPhase anchor cls σ)]
  unfold locatedLedgerOriginalKernelProduct
    locatedLedgerEliminationKernelProduct
  apply List.prod_map_le_prod_map₀
  · intro b _hb
    apply locatedBlockOriginalKernelProduct_nonneg
    intro edge
    exact nxClassEdgeKernel_nonneg ht hroot Nm mu z hz R O
      (finAnchorNXKernelStrongEdges leftPhase rightPhase anchor)
      cls (fun i => (σ i).1) edge
  · intro b hb
    exact locatedBlockOriginalKernelProduct_le_eliminationKernel
      ht hroot Nm mu z hz R O leftPhase rightPhase anchor cls σ b hb

/-! ## Split back into the two outward CPS runs -/

/--
The position-retaining counterpart of `AnchoredNXParityRuns`.  Its ledger
is bookkeeping only; the two lists remain distinct analytic runs.
-/
structure AnchoredLocatedNXParityRuns {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t) where
  left : List (LocatedNXParityBlock (m := m) Nm mu)
  right : List (LocatedNXParityBlock (m := m) Nm mu)

def AnchoredLocatedNXParityRuns.ledger
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (runs : AnchoredLocatedNXParityRuns (m := m) Nm mu) :
    List (LocatedNXParityBlock (m := m) Nm mu) :=
  runs.left ++ runs.right

/--
Split the concrete marked ledger at exactly the same raw-left length as
`finAnchorNXCoarseRunsWithPhases`.
-/
def finAnchorNXLocatedCoarseRunsWithPhases
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    AnchoredLocatedNXParityRuns (m := m) Nm mu :=
  let raw := finAnchorNXParityRunsWithPhases Nm mu
    leftPhase rightPhase anchor cls O
  let marked := finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
    leftPhase rightPhase anchor cls O
  { left := marked.take raw.left.length
    right := marked.drop raw.left.length }

theorem finAnchorNXLocatedCoarseRunsWithPhases_ledger
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
      leftPhase rightPhase anchor cls O).ledger =
      finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
        leftPhase rightPhase anchor cls O := by
  simp [finAnchorNXLocatedCoarseRunsWithPhases,
    AnchoredLocatedNXParityRuns.ledger, List.take_append_drop]

/--
After erasing positions, the concrete left split is definitionally the
left run consumed by `conditionedNXAnchoredRunsSum`.
-/
theorem map_analyticBlock_finAnchorNXLocatedCoarseRunsWithPhases_left
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
      leftPhase rightPhase anchor cls O).left.map
        LocatedNXParityBlock.analyticBlock =
      (finAnchorNXCoarseRunsWithPhases Nm mu
        leftPhase rightPhase anchor cls O).left := by
  simp only [finAnchorNXLocatedCoarseRunsWithPhases,
    finAnchorNXCoarseRunsWithPhases, List.map_take]
  rw [map_analyticBlock_finAnchorNXLocatedCoarseLedgerWithPhases]

/--
After erasing positions, the concrete right split is definitionally the
right run consumed by `conditionedNXAnchoredRunsSum`.
-/
theorem map_analyticBlock_finAnchorNXLocatedCoarseRunsWithPhases_right
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
      leftPhase rightPhase anchor cls O).right.map
        LocatedNXParityBlock.analyticBlock =
      (finAnchorNXCoarseRunsWithPhases Nm mu
        leftPhase rightPhase anchor cls O).right := by
  simp only [finAnchorNXLocatedCoarseRunsWithPhases,
    finAnchorNXCoarseRunsWithPhases, List.map_drop]
  rw [map_analyticBlock_finAnchorNXLocatedCoarseLedgerWithPhases]

/--
Fixed-arrangement kernel schedule in the exact two-run order: the left
monomial is completed first, then the right monomial restarts at the
anchor.  The right-hand side contains no cross-run factor.
-/
theorem edgeKernelProduct_le_finAnchorNXLocatedOutwardRunsProduct
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (O : Finset (AdjacentIndex m))
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (σ : Fin m → HeppLabeledCopy mu) :
    (∏ edge : AdjacentIndex m,
      finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
        R O leftPhase rightPhase anchor cls σ edge) ≤
      locatedLedgerEliminationKernelProduct
          ht hroot Nm mu z hz R anchor σ
          (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
            leftPhase rightPhase anchor cls O).left *
        locatedLedgerEliminationKernelProduct
          ht hroot Nm mu z hz R anchor σ
          (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
            leftPhase rightPhase anchor cls O).right := by
  have hbound :=
    edgeKernelProduct_le_finAnchorNXLocatedEliminationProduct
      ht hroot Nm mu z hz R O leftPhase rightPhase anchor cls σ
  rw [← finAnchorNXLocatedCoarseRunsWithPhases_ledger
    Nm mu leftPhase rightPhase anchor cls O] at hbound
  simpa [AnchoredLocatedNXParityRuns.ledger,
    locatedLedgerEliminationKernelProduct, List.map_append,
    List.prod_append] using hbound

/--
Assembly-facing certificate: the fixed-arrangement kernel bound and the
two exact erasures to the analytic runs expected by
`conditionedNXAnchoredRunsSum`.
-/
theorem finAnchorNXKernelSchedule_CPS_interface
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (O : Finset (AdjacentIndex m))
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (σ : Fin m → HeppLabeledCopy mu) :
    (∏ edge : AdjacentIndex m,
      finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
        R O leftPhase rightPhase anchor cls σ edge) ≤
        locatedLedgerEliminationKernelProduct
            ht hroot Nm mu z hz R anchor σ
            (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
              leftPhase rightPhase anchor cls O).left *
          locatedLedgerEliminationKernelProduct
            ht hroot Nm mu z hz R anchor σ
            (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
              leftPhase rightPhase anchor cls O).right ∧
      (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).left.map
          LocatedNXParityBlock.analyticBlock =
        (finAnchorNXCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).left ∧
      (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).right.map
          LocatedNXParityBlock.analyticBlock =
        (finAnchorNXCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).right := by
  exact ⟨
    edgeKernelProduct_le_finAnchorNXLocatedOutwardRunsProduct
      ht hroot Nm mu z hz R O leftPhase rightPhase anchor cls σ,
    map_analyticBlock_finAnchorNXLocatedCoarseRunsWithPhases_left
      Nm mu leftPhase rightPhase anchor cls O,
    map_analyticBlock_finAnchorNXLocatedCoarseRunsWithPhases_right
      Nm mu leftPhase rightPhase anchor cls O⟩

end XYCluster

end

end Anderson4D
