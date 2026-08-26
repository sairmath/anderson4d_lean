import Anderson4D.PermSum.SingleScaleFiberCPS

/-!
# Alignment of the located kernel ledger with the fiber CPS kernel

The kernel schedule keeps original positions, while the finite-Fubini/CPS
schedule keeps only analytic `(N,X)` blocks and consumes a finite tuple.
This file records the missing pointwise alignment.  The central certificate
`LocatedRunConsecutive` says exactly that a located run starts at a given
position and then visits consecutive positions away from the anchor.

Rough marking is harmless here: `.pair` and `.roughPair` retain the same
two positions and both kernel definitions use the same
`lambda * strongLambda` monomial.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/-! ## Assignment and consecutiveness certificates -/

/--
Read a fixed position assignment in the exact tuple order consumed by a
located ledger.
-/
def locatedScheduleAssignment
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (σ : Fin m → HeppLabeledCopy mu) :
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) →
      Fin (nxParityScheduleArity
        (bs.map LocatedNXParityBlock.analyticBlock)) →
        HeppLabeledCopy mu
  | [] => Fin.elim0
  | .single i _a _skipped :: bs =>
      @Fin.cons
        (nxParityScheduleArity
          (bs.map LocatedNXParityBlock.analyticBlock))
        (fun _ => HeppLabeledCopy mu) (σ i)
        (locatedScheduleAssignment σ bs)
  | .pair i j _p :: bs
  | .roughPair i j _p :: bs =>
      @Fin.cons
        (nxParityScheduleArity
          (bs.map LocatedNXParityBlock.analyticBlock) + 1)
        (fun _ => HeppLabeledCopy mu) (σ i)
        (@Fin.cons
          (nxParityScheduleArity
            (bs.map LocatedNXParityBlock.analyticBlock))
          (fun _ => HeppLabeledCopy mu) (σ j)
          (locatedScheduleAssignment σ bs))

/--
The analogous assignment for two outward runs.  It is defined in the same
recursion pattern as `nxAnchoredScheduleKernel`, so no dependent cast is
hidden at the run boundary.
-/
def locatedAnchoredScheduleAssignment
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (σ : Fin m → HeppLabeledCopy mu) :
    (left right : List (LocatedNXParityBlock (m := m) Nm mu)) →
      Fin (nxParityScheduleArity
        (left.map LocatedNXParityBlock.analyticBlock ++
          right.map LocatedNXParityBlock.analyticBlock)) →
        HeppLabeledCopy mu
  | [], right => locatedScheduleAssignment σ right
  | .single i _a _skipped :: left, right =>
      @Fin.cons
        (nxParityScheduleArity
          (left.map LocatedNXParityBlock.analyticBlock ++
            right.map LocatedNXParityBlock.analyticBlock))
        (fun _ => HeppLabeledCopy mu) (σ i)
        (locatedAnchoredScheduleAssignment σ left right)
  | .pair i j _p :: left, right
  | .roughPair i j _p :: left, right =>
      @Fin.cons
        (nxParityScheduleArity
          (left.map LocatedNXParityBlock.analyticBlock ++
            right.map LocatedNXParityBlock.analyticBlock) + 1)
        (fun _ => HeppLabeledCopy mu) (σ i)
        (@Fin.cons
          (nxParityScheduleArity
            (left.map LocatedNXParityBlock.analyticBlock ++
              right.map LocatedNXParityBlock.analyticBlock))
          (fun _ => HeppLabeledCopy mu) (σ j)
          (locatedAnchoredScheduleAssignment σ left right))

theorem ofFn_locatedScheduleAssignment
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (σ : Fin m → HeppLabeledCopy mu)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    List.ofFn (locatedScheduleAssignment σ bs) =
      (bs.flatMap fun b => b.positionBlock.entries).map σ := by
  induction bs with
  | nil =>
      rfl
  | cons b bs ih =>
      cases b with
      | single i a skipped =>
          dsimp only [locatedScheduleAssignment, List.map,
            LocatedNXParityBlock.analyticBlock,
            nxParityScheduleArity, List.flatMap,
            LocatedNXParityBlock.positionBlock,
            PositionBlock.entries]
          rw [List.ofFn_cons, ih]
          simp
          rw [List.map_flatMap]
          rfl
      | pair i j p =>
          dsimp only [locatedScheduleAssignment, List.map,
            LocatedNXParityBlock.analyticBlock,
            nxParityScheduleArity, List.flatMap,
            LocatedNXParityBlock.positionBlock,
            PositionBlock.entries]
          rw [List.ofFn_cons, List.ofFn_cons, ih]
          simp
          rw [List.map_flatMap]
          rfl
      | roughPair i j p =>
          dsimp only [locatedScheduleAssignment, List.map,
            LocatedNXParityBlock.analyticBlock,
            nxParityScheduleArity, List.flatMap,
            LocatedNXParityBlock.positionBlock,
            PositionBlock.entries]
          rw [List.ofFn_cons, List.ofFn_cons, ih]
          simp
          rw [List.map_flatMap]
          rfl

/--
The anchored assignment reads the two located ledgers in order.  The
explicit arity casts below isolate the otherwise fragile dependent
normalization at the `left ++ right` boundary.
-/
theorem ofFn_locatedAnchoredScheduleAssignment
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (σ : Fin m → HeppLabeledCopy mu)
    (left right : List (LocatedNXParityBlock (m := m) Nm mu)) :
    List.ofFn (locatedAnchoredScheduleAssignment σ left right) =
      ((left.flatMap fun b => b.positionBlock.entries) ++
        (right.flatMap fun b => b.positionBlock.entries)).map σ := by
  induction left with
  | nil =>
      have hfun :
          locatedAnchoredScheduleAssignment σ [] right =
            locatedScheduleAssignment σ right := by
        rfl
      rw [hfun]
      simpa using ofFn_locatedScheduleAssignment σ right
  | cons b left ih =>
      cases b with
      | single i a skipped =>
          let n :=
            nxParityScheduleArity
              (left.map LocatedNXParityBlock.analyticBlock ++
                right.map LocatedNXParityBlock.analyticBlock)
          let f : Fin (n + 1) → HeppLabeledCopy mu :=
            Fin.cons (σ i)
              (locatedAnchoredScheduleAssignment σ left right)
          have hArity :
              nxParityScheduleArity
                  ((LocatedNXParityBlock.single i a skipped :: left).map
                    LocatedNXParityBlock.analyticBlock ++
                    right.map LocatedNXParityBlock.analyticBlock) =
                n + 1 := by
            rfl
          have hfun :
              locatedAnchoredScheduleAssignment σ
                  (LocatedNXParityBlock.single i a skipped :: left) right =
                f ∘ Fin.cast hArity := by
            funext k
            rfl
          rw [hfun, ofFn_comp_finCast, List.ofFn_cons]
          change σ i ::
              List.ofFn
                  (locatedAnchoredScheduleAssignment σ left right) =
            _
          rw [ih]
          dsimp only [List.map, List.flatMap,
            LocatedNXParityBlock.positionBlock,
            PositionBlock.entries]
          simp
      | pair i j p =>
          let n :=
            nxParityScheduleArity
              (left.map LocatedNXParityBlock.analyticBlock ++
                right.map LocatedNXParityBlock.analyticBlock)
          let f : Fin (n + 2) → HeppLabeledCopy mu :=
            Fin.cons (σ i)
              (Fin.cons (σ j)
                (locatedAnchoredScheduleAssignment σ left right))
          have hArity :
              nxParityScheduleArity
                  ((LocatedNXParityBlock.pair i j p :: left).map
                    LocatedNXParityBlock.analyticBlock ++
                    right.map LocatedNXParityBlock.analyticBlock) =
                n + 2 := by
            rfl
          have hfun :
              locatedAnchoredScheduleAssignment σ
                  (LocatedNXParityBlock.pair i j p :: left) right =
                f ∘ Fin.cast hArity := by
            funext k
            rfl
          rw [hfun, ofFn_comp_finCast, List.ofFn_cons,
            List.ofFn_cons]
          change σ i :: σ j ::
              List.ofFn
                  (locatedAnchoredScheduleAssignment σ left right) =
            _
          rw [ih]
          dsimp only [List.map, List.flatMap,
            LocatedNXParityBlock.positionBlock,
            PositionBlock.entries]
          simp
      | roughPair i j p =>
          let n :=
            nxParityScheduleArity
              (left.map LocatedNXParityBlock.analyticBlock ++
                right.map LocatedNXParityBlock.analyticBlock)
          let f : Fin (n + 2) → HeppLabeledCopy mu :=
            Fin.cons (σ i)
              (Fin.cons (σ j)
                (locatedAnchoredScheduleAssignment σ left right))
          have hArity :
              nxParityScheduleArity
                  ((LocatedNXParityBlock.roughPair i j p :: left).map
                    LocatedNXParityBlock.analyticBlock ++
                    right.map LocatedNXParityBlock.analyticBlock) =
                n + 2 := by
            rfl
          have hfun :
              locatedAnchoredScheduleAssignment σ
                  (LocatedNXParityBlock.roughPair i j p :: left) right =
                f ∘ Fin.cast hArity := by
            funext k
            rfl
          rw [hfun, ofFn_comp_finCast, List.ofFn_cons,
            List.ofFn_cons]
          change σ i :: σ j ::
              List.ofFn
                  (locatedAnchoredScheduleAssignment σ left right) =
            _
          rw [ih]
          dsimp only [List.map, List.flatMap,
            LocatedNXParityBlock.positionBlock,
            PositionBlock.entries]
          simp

/--
A located run is consecutive away from `anchor`, beginning just outside
`previous`.  The endpoint of each block becomes the preceding position for
the next block.
-/
inductive LocatedRunConsecutive
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (anchor : Fin m) :
    Fin m → List (LocatedNXParityBlock (m := m) Nm mu) → Prop
  | nil (previous : Fin m) :
      LocatedRunConsecutive anchor previous []
  | single (previous i : Fin m) (a : ActiveNXClass Nm mu)
      (skipped : Bool)
      (bs : List (LocatedNXParityBlock (m := m) Nm mu))
      (hprevious : outwardPreviousPosition anchor i = previous)
      (hrest : LocatedRunConsecutive anchor i bs) :
      LocatedRunConsecutive anchor previous
        (.single i a skipped :: bs)
  | pair (previous i j : Fin m) (p : NXPairBlock Nm mu)
      (bs : List (LocatedNXParityBlock (m := m) Nm mu))
      (hprevious : outwardPreviousPosition anchor i = previous)
      (hinternal : outwardPreviousPosition anchor j = i)
      (hrest : LocatedRunConsecutive anchor j bs) :
      LocatedRunConsecutive anchor previous (.pair i j p :: bs)
  | roughPair (previous i j : Fin m) (p : NXPairBlock Nm mu)
      (bs : List (LocatedNXParityBlock (m := m) Nm mu))
      (hprevious : outwardPreviousPosition anchor i = previous)
      (hinternal : outwardPreviousPosition anchor j = i)
      (hrest : LocatedRunConsecutive anchor j bs) :
      LocatedRunConsecutive anchor previous (.roughPair i j p :: bs)

/-- Position-only version of the same consecutive-run condition. -/
def OutwardPositionChain {m : ℕ} (anchor : Fin m) :
    Fin m → List (Fin m) → Prop
  | _previous, [] => True
  | previous, i :: is =>
      outwardPreviousPosition anchor i = previous ∧
        OutwardPositionChain anchor i is

private theorem outwardPositionChain_iff_isChain
    {m : ℕ} (anchor previous : Fin m) (xs : List (Fin m)) :
    OutwardPositionChain anchor previous xs ↔
      (previous :: xs).IsChain
        (fun p i => outwardPreviousPosition anchor i = p) := by
  induction xs generalizing previous with
  | nil =>
      simp [OutwardPositionChain]
  | cons i is ih =>
      simp only [OutwardPositionChain, List.isChain_cons_cons]
      rw [ih]

private theorem outwardPreviousPosition_left_zero
    {m : ℕ} (anchor i : Fin m)
    (hi : i.1 < anchor.1)
    (hoff : anchorPositionOutwardOffset anchor i = 0) :
    outwardPreviousPosition anchor i = anchor := by
  have hv : i.1 + 1 = anchor.1 := by
    simp [anchorPositionOutwardOffset, hi] at hoff
    omega
  apply Fin.ext
  simp [outwardPreviousPosition, hi]
  exact hv

private theorem outwardPreviousPosition_left_succ
    {m : ℕ} (anchor i j : Fin m)
    (hi : i.1 < anchor.1) (hj : j.1 < anchor.1)
    (hoff : anchorPositionOutwardOffset anchor j =
      anchorPositionOutwardOffset anchor i + 1) :
    outwardPreviousPosition anchor j = i := by
  have hv : j.1 + 1 = i.1 := by
    simp [anchorPositionOutwardOffset, hi, hj] at hoff
    omega
  apply Fin.ext
  simp [outwardPreviousPosition, hj]
  exact hv

private theorem outwardPreviousPosition_right_zero
    {m : ℕ} (anchor i : Fin m)
    (hi : anchor.1 < i.1)
    (hoff : anchorPositionOutwardOffset anchor i = 0) :
    outwardPreviousPosition anchor i = anchor := by
  have hv : i.1 = anchor.1 + 1 := by
    simp [anchorPositionOutwardOffset,
      not_lt_of_ge (Nat.le_of_lt hi)] at hoff
    omega
  apply Fin.ext
  simp [outwardPreviousPosition,
    not_lt_of_ge (Nat.le_of_lt hi), hi]
  omega

private theorem outwardPreviousPosition_right_succ
    {m : ℕ} (anchor i j : Fin m)
    (hi : anchor.1 < i.1) (hj : anchor.1 < j.1)
    (hoff : anchorPositionOutwardOffset anchor j =
      anchorPositionOutwardOffset anchor i + 1) :
    outwardPreviousPosition anchor j = i := by
  have hv : j.1 = i.1 + 1 := by
    simp [anchorPositionOutwardOffset,
      not_lt_of_ge (Nat.le_of_lt hi),
      not_lt_of_ge (Nat.le_of_lt hj)] at hoff
    omega
  apply Fin.ext
  simp [outwardPreviousPosition,
    not_lt_of_ge (Nat.le_of_lt hj), hj]
  omega

private theorem leftAnchorPositions_outwardChain
    {m : ℕ} (anchor : Fin m) :
    OutwardPositionChain anchor anchor
      (leftAnchorPositions anchor) := by
  rw [outwardPositionChain_iff_isChain]
  let xs := leftAnchorPositions anchor
  let off := anchorPositionOutwardOffset anchor
  have hmap : xs.map off = List.range xs.length := by
    simpa [xs, off] using
      map_anchorPositionOutwardOffset_left anchor
  have hside : ∀ i ∈ xs, i.1 < anchor.1 := by
    intro i hi
    exact (mem_leftAnchorPositions_iff anchor i).mp
      (by simpa [xs] using hi)
  have hcOff :
      (xs.map off).IsChain (fun a b => b = a + 1) := by
    rw [hmap, List.isChain_range]
    intro k hk
    omega
  have hcRaw :
      xs.IsChain (fun a b => off b = off a + 1) :=
    (List.isChain_map off).mp hcOff
  have hc :
      xs.IsChain
        (fun prev i => outwardPreviousPosition anchor i = prev) :=
    hcRaw.imp_of_mem_imp (fun i j hi hj hij =>
      outwardPreviousPosition_left_succ anchor i j
        (hside i hi) (hside j hj) hij)
  change (anchor :: xs).IsChain
    (fun prev i => outwardPreviousPosition anchor i = prev)
  cases hxs : xs with
  | nil =>
      simp
  | cons i is =>
      have hi : i.1 < anchor.1 :=
        hside i (by simp [hxs])
      have hoff : off i = 0 := by
        have hh := congrArg List.head? hmap
        simp [hxs, List.range_succ_eq_map] at hh
        exact hh
      have hfirst :=
        outwardPreviousPosition_left_zero anchor i hi
          (by simpa [off] using hoff)
      rw [hxs] at hc
      rw [List.isChain_cons_cons]
      exact ⟨hfirst, hc⟩

private theorem rightAnchorPositions_outwardChain
    {m : ℕ} (anchor : Fin m) :
    OutwardPositionChain anchor anchor
      (rightAnchorPositions anchor) := by
  rw [outwardPositionChain_iff_isChain]
  let xs := rightAnchorPositions anchor
  let off := anchorPositionOutwardOffset anchor
  have hmap : xs.map off = List.range xs.length := by
    simpa [xs, off] using
      map_anchorPositionOutwardOffset_right anchor
  have hside : ∀ i ∈ xs, anchor.1 < i.1 := by
    intro i hi
    exact (mem_rightAnchorPositions_iff anchor i).mp
      (by simpa [xs] using hi)
  have hcOff :
      (xs.map off).IsChain (fun a b => b = a + 1) := by
    rw [hmap, List.isChain_range]
    intro k hk
    omega
  have hcRaw :
      xs.IsChain (fun a b => off b = off a + 1) :=
    (List.isChain_map off).mp hcOff
  have hc :
      xs.IsChain
        (fun prev i => outwardPreviousPosition anchor i = prev) :=
    hcRaw.imp_of_mem_imp (fun i j hi hj hij =>
      outwardPreviousPosition_right_succ anchor i j
        (hside i hi) (hside j hj) hij)
  change (anchor :: xs).IsChain
    (fun prev i => outwardPreviousPosition anchor i = prev)
  cases hxs : xs with
  | nil =>
      simp
  | cons i is =>
      have hi : anchor.1 < i.1 :=
        hside i (by simp [hxs])
      have hoff : off i = 0 := by
        have hh := congrArg List.head? hmap
        simp [hxs, List.range_succ_eq_map] at hh
        exact hh
      have hfirst :=
        outwardPreviousPosition_right_zero anchor i hi
          (by simpa [off] using hoff)
      rw [hxs] at hc
      rw [List.isChain_cons_cons]
      exact ⟨hfirst, hc⟩

/--
Any located block partition of a consecutive position list inherits the
kernel alignment certificate.  This is the reusable raw
`pairPositionRun` interface; it is insensitive to rough marking.
-/
theorem locatedRunConsecutive_of_flatten_positionBlocks
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (anchor previous : Fin m)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu))
    (xs : List (Fin m))
    (hflat :
      (bs.map LocatedNXParityBlock.positionBlock).flatMap
          PositionBlock.entries = xs)
    (hchain : OutwardPositionChain anchor previous xs) :
    LocatedRunConsecutive anchor previous bs := by
  induction bs generalizing previous xs with
  | nil =>
      have hxs : xs = [] := by
        simpa using hflat.symm
      subst xs
      exact .nil previous
  | cons b bs ih =>
      cases b with
      | single i a skipped =>
          rw [← hflat] at hchain
          change
            outwardPreviousPosition anchor i = previous ∧
              OutwardPositionChain anchor i
                ((bs.map LocatedNXParityBlock.positionBlock).flatMap
                  PositionBlock.entries) at hchain
          exact .single previous i a skipped bs hchain.1
            (ih i _ rfl hchain.2)
      | pair i j p =>
          rw [← hflat] at hchain
          change
            outwardPreviousPosition anchor i = previous ∧
              outwardPreviousPosition anchor j = i ∧
                OutwardPositionChain anchor j
                  ((bs.map LocatedNXParityBlock.positionBlock).flatMap
                    PositionBlock.entries) at hchain
          exact .pair previous i j p bs hchain.1 hchain.2.1
            (ih j _ rfl hchain.2.2)
      | roughPair i j p =>
          rw [← hflat] at hchain
          change
            outwardPreviousPosition anchor i = previous ∧
              outwardPreviousPosition anchor j = i ∧
                OutwardPositionChain anchor j
                  ((bs.map LocatedNXParityBlock.positionBlock).flatMap
                    PositionBlock.entries) at hchain
          exact .roughPair previous i j p bs hchain.1 hchain.2.1
            (ih j _ rfl hchain.2.2)

/--
Raw `pairPositionRun` wrapper.  A rough-marked located list aligns whenever
erasing its rough metadata recovers the raw pairing schedule.
-/
theorem locatedRunConsecutive_of_map_positionBlock_eq_pairPositionRun
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (anchor previous : Fin m)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu))
    (phase : Bool) (xs : List (Fin m))
    (hblocks :
      bs.map LocatedNXParityBlock.positionBlock =
        pairPositionRun phase xs)
    (hchain : OutwardPositionChain anchor previous xs) :
    LocatedRunConsecutive anchor previous bs := by
  apply locatedRunConsecutive_of_flatten_positionBlocks
    anchor previous bs xs
  · calc
      (bs.map LocatedNXParityBlock.positionBlock).flatMap
          PositionBlock.entries =
        (pairPositionRun phase xs).flatMap
          PositionBlock.entries := congrArg
            (List.flatMap PositionBlock.entries) hblocks
      _ = xs := flatten_pairPositionRun phase xs
  · exact hchain

/-- Rough marking and the canonical split retain the raw left position
pairing schedule exactly. -/
theorem map_positionBlock_finAnchorNXLocatedCoarseRunsWithPhases_left
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
      leftPhase rightPhase anchor cls O).left.map
        LocatedNXParityBlock.positionBlock =
      pairPositionRun leftPhase (leftAnchorPositions anchor) := by
  simp only [finAnchorNXLocatedCoarseRunsWithPhases, List.map_take]
  rw [map_positionBlock_finAnchorNXLocatedCoarseLedgerWithPhases]
  simp [finAnchorPositionScheduleWithPhases,
    anchorPositionScheduleWithPhases,
    finAnchorNXParityRunsWithPhases]

/-- Rough marking and the canonical split retain the raw right position
pairing schedule exactly. -/
theorem map_positionBlock_finAnchorNXLocatedCoarseRunsWithPhases_right
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
      leftPhase rightPhase anchor cls O).right.map
        LocatedNXParityBlock.positionBlock =
      pairPositionRun rightPhase (rightAnchorPositions anchor) := by
  simp only [finAnchorNXLocatedCoarseRunsWithPhases, List.map_drop]
  rw [map_positionBlock_finAnchorNXLocatedCoarseLedgerWithPhases]
  simp [finAnchorPositionScheduleWithPhases,
    anchorPositionScheduleWithPhases,
    finAnchorNXParityRunsWithPhases]

/--
The sole position-only condition still needed to instantiate the canonical
alignment.  It contains no classes, skip flags, rough marking, or kernels.
-/
def FinAnchorOutwardChainCondition {m : ℕ} (anchor : Fin m) : Prop :=
  OutwardPositionChain anchor anchor (leftAnchorPositions anchor) ∧
    OutwardPositionChain anchor anchor (rightAnchorPositions anchor)

/-- The canonical left/right position schedules really are consecutive
outward runs. -/
theorem finAnchorOutwardChainCondition
    {m : ℕ} (anchor : Fin m) :
    FinAnchorOutwardChainCondition anchor :=
  ⟨leftAnchorPositions_outwardChain anchor,
    rightAnchorPositions_outwardChain anchor⟩

/-- The position-only chain condition produces both actual coarse-run
certificates. -/
theorem finAnchorNXLocatedCoarseRuns_consecutive_of_chainCondition
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m))
    (hchain : FinAnchorOutwardChainCondition anchor) :
    LocatedRunConsecutive anchor anchor
        (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).left ∧
      LocatedRunConsecutive anchor anchor
        (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).right := by
  constructor
  · exact
      locatedRunConsecutive_of_map_positionBlock_eq_pairPositionRun
        anchor anchor
        (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).left
        leftPhase (leftAnchorPositions anchor)
        (map_positionBlock_finAnchorNXLocatedCoarseRunsWithPhases_left
          Nm mu leftPhase rightPhase anchor cls O)
        hchain.1
  · exact
      locatedRunConsecutive_of_map_positionBlock_eq_pairPositionRun
        anchor anchor
        (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).right
        rightPhase (rightAnchorPositions anchor)
        (map_positionBlock_finAnchorNXLocatedCoarseRunsWithPhases_right
          Nm mu leftPhase rightPhase anchor cls O)
        hchain.2

/-! ## Exact kernel equalities from the certificate -/

/--
For a consecutive located run, the product of located elimination
monomials is exactly the recursive CPS assignment monomial.
-/
theorem locatedLedgerEliminationKernelProduct_eq_scheduleKernel
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (anchor previous : Fin m)
    (σ : Fin m → HeppLabeledCopy mu)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu))
    (halign : LocatedRunConsecutive anchor previous bs) :
    locatedLedgerEliminationKernelProduct
        ht hroot Nm mu z hz R anchor σ bs =
      nxParityScheduleKernel ht hroot Nm mu z hz R
        (bs.map LocatedNXParityBlock.analyticBlock)
        (labeledCopyPoint z (σ previous))
        (locatedScheduleAssignment σ bs) := by
  induction halign with
  | nil previous =>
      rfl
  | single previous i a skipped bs hprevious hrest ih =>
      calc
        locatedLedgerEliminationKernelProduct
            ht hroot Nm mu z hz R anchor σ
              (.single i a skipped :: bs) =
          locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ
                (.single i a skipped) *
            locatedLedgerEliminationKernelProduct
              ht hroot Nm mu z hz R anchor σ bs := by
                rfl
        _ =
          locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ
                (.single i a skipped) *
            nxParityScheduleKernel ht hroot Nm mu z hz R
              (bs.map LocatedNXParityBlock.analyticBlock)
              (labeledCopyPoint z (σ i))
              (locatedScheduleAssignment σ bs) :=
          congrArg
            (locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ
                (.single i a skipped) * ·) ih
        _ = nxParityScheduleKernel ht hroot Nm mu z hz R
              ((.single i a skipped :: bs).map
                LocatedNXParityBlock.analyticBlock)
              (labeledCopyPoint z (σ previous))
              (locatedScheduleAssignment σ
                (.single i a skipped :: bs)) := by
          simp [locatedBlockEliminationKernel,
            LocatedNXParityBlock.analyticBlock,
            locatedScheduleAssignment, nxParityScheduleKernel,
            hprevious]
  | pair previous i j p bs hprevious hinternal hrest ih =>
      calc
        locatedLedgerEliminationKernelProduct
            ht hroot Nm mu z hz R anchor σ
              (.pair i j p :: bs) =
          locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ (.pair i j p) *
            locatedLedgerEliminationKernelProduct
              ht hroot Nm mu z hz R anchor σ bs := by
                rfl
        _ =
          locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ (.pair i j p) *
            nxParityScheduleKernel ht hroot Nm mu z hz R
              (bs.map LocatedNXParityBlock.analyticBlock)
              (labeledCopyPoint z (σ j))
              (locatedScheduleAssignment σ bs) :=
          congrArg
            (locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ (.pair i j p) * ·) ih
        _ = nxParityScheduleKernel ht hroot Nm mu z hz R
              ((.pair i j p :: bs).map
                LocatedNXParityBlock.analyticBlock)
              (labeledCopyPoint z (σ previous))
              (locatedScheduleAssignment σ (.pair i j p :: bs)) := by
          simp [locatedBlockEliminationKernel,
            LocatedNXParityBlock.analyticBlock,
            locatedScheduleAssignment, nxParityScheduleKernel,
            hprevious, mul_assoc]
  | roughPair previous i j p bs hprevious hinternal hrest ih =>
      calc
        locatedLedgerEliminationKernelProduct
            ht hroot Nm mu z hz R anchor σ
              (.roughPair i j p :: bs) =
          locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ (.roughPair i j p) *
            locatedLedgerEliminationKernelProduct
              ht hroot Nm mu z hz R anchor σ bs := by
                rfl
        _ =
          locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ (.roughPair i j p) *
            nxParityScheduleKernel ht hroot Nm mu z hz R
              (bs.map LocatedNXParityBlock.analyticBlock)
              (labeledCopyPoint z (σ j))
              (locatedScheduleAssignment σ bs) :=
          congrArg
            (locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ (.roughPair i j p) * ·) ih
        _ = nxParityScheduleKernel ht hroot Nm mu z hz R
              ((.roughPair i j p :: bs).map
                LocatedNXParityBlock.analyticBlock)
              (labeledCopyPoint z (σ previous))
              (locatedScheduleAssignment σ
                (.roughPair i j p :: bs)) := by
          simp [locatedBlockEliminationKernel,
            LocatedNXParityBlock.analyticBlock,
            locatedScheduleAssignment, nxParityScheduleKernel,
            hprevious, mul_assoc]

/--
Two consecutive outward runs give exactly `nxAnchoredScheduleKernel`: the
right run starts from the anchor point after the left tuple has been
consumed, with no cross-run factor.
-/
theorem locatedOutwardRunsEliminationKernelProduct_eq_anchoredScheduleKernel
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (anchor : Fin m)
    (σ : Fin m → HeppLabeledCopy mu)
    (left right : List (LocatedNXParityBlock (m := m) Nm mu))
    (previous : Fin m)
    (hleft : LocatedRunConsecutive anchor previous left)
    (hright : LocatedRunConsecutive anchor anchor right) :
    locatedLedgerEliminationKernelProduct
          ht hroot Nm mu z hz R anchor σ left *
        locatedLedgerEliminationKernelProduct
          ht hroot Nm mu z hz R anchor σ right =
      nxAnchoredScheduleKernel ht hroot Nm mu z hz R
        (left.map LocatedNXParityBlock.analyticBlock)
        (right.map LocatedNXParityBlock.analyticBlock)
        (labeledCopyPoint z (σ anchor))
        (labeledCopyPoint z (σ previous))
        (locatedAnchoredScheduleAssignment σ left right) := by
  induction hleft with
  | nil previous =>
      calc
        locatedLedgerEliminationKernelProduct
              ht hroot Nm mu z hz R anchor σ [] *
            locatedLedgerEliminationKernelProduct
              ht hroot Nm mu z hz R anchor σ right =
          locatedLedgerEliminationKernelProduct
              ht hroot Nm mu z hz R anchor σ right := by
                simp [locatedLedgerEliminationKernelProduct]
        _ = nxParityScheduleKernel ht hroot Nm mu z hz R
              (right.map LocatedNXParityBlock.analyticBlock)
              (labeledCopyPoint z (σ anchor))
              (locatedScheduleAssignment σ right) :=
          locatedLedgerEliminationKernelProduct_eq_scheduleKernel
            ht hroot Nm mu z hz R anchor anchor σ right hright
        _ = nxAnchoredScheduleKernel ht hroot Nm mu z hz R
              ([] : List (NXParityBlock Nm mu))
              (right.map LocatedNXParityBlock.analyticBlock)
              (labeledCopyPoint z (σ anchor))
              (labeledCopyPoint z (σ previous))
              (locatedAnchoredScheduleAssignment σ [] right) := by
                rfl
  | single previous i a skipped left hprevious hrest ih =>
      calc
        locatedLedgerEliminationKernelProduct
              ht hroot Nm mu z hz R anchor σ
                (.single i a skipped :: left) *
            locatedLedgerEliminationKernelProduct
              ht hroot Nm mu z hz R anchor σ right =
          locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ
                (.single i a skipped) *
            (locatedLedgerEliminationKernelProduct
                ht hroot Nm mu z hz R anchor σ left *
              locatedLedgerEliminationKernelProduct
                ht hroot Nm mu z hz R anchor σ right) := by
                  simp [locatedLedgerEliminationKernelProduct,
                    mul_assoc]
        _ = locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ
                (.single i a skipped) *
            nxAnchoredScheduleKernel ht hroot Nm mu z hz R
              (left.map LocatedNXParityBlock.analyticBlock)
              (right.map LocatedNXParityBlock.analyticBlock)
              (labeledCopyPoint z (σ anchor))
              (labeledCopyPoint z (σ i))
              (locatedAnchoredScheduleAssignment σ left right) :=
          congrArg
            (locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ
                (.single i a skipped) * ·) ih
        _ = nxAnchoredScheduleKernel ht hroot Nm mu z hz R
              ((.single i a skipped :: left).map
                LocatedNXParityBlock.analyticBlock)
              (right.map LocatedNXParityBlock.analyticBlock)
              (labeledCopyPoint z (σ anchor))
              (labeledCopyPoint z (σ previous))
              (locatedAnchoredScheduleAssignment σ
                (.single i a skipped :: left) right) := by
          simp [locatedBlockEliminationKernel,
            LocatedNXParityBlock.analyticBlock,
            locatedAnchoredScheduleAssignment,
            nxAnchoredScheduleKernel, hprevious]
  | pair previous i j p left hprevious hinternal hrest ih =>
      calc
        locatedLedgerEliminationKernelProduct
              ht hroot Nm mu z hz R anchor σ (.pair i j p :: left) *
            locatedLedgerEliminationKernelProduct
              ht hroot Nm mu z hz R anchor σ right =
          locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ (.pair i j p) *
            (locatedLedgerEliminationKernelProduct
                ht hroot Nm mu z hz R anchor σ left *
              locatedLedgerEliminationKernelProduct
                ht hroot Nm mu z hz R anchor σ right) := by
                  simp [locatedLedgerEliminationKernelProduct,
                    mul_assoc]
        _ = locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ (.pair i j p) *
            nxAnchoredScheduleKernel ht hroot Nm mu z hz R
              (left.map LocatedNXParityBlock.analyticBlock)
              (right.map LocatedNXParityBlock.analyticBlock)
              (labeledCopyPoint z (σ anchor))
              (labeledCopyPoint z (σ j))
              (locatedAnchoredScheduleAssignment σ left right) :=
          congrArg
            (locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ (.pair i j p) * ·) ih
        _ = nxAnchoredScheduleKernel ht hroot Nm mu z hz R
              ((.pair i j p :: left).map
                LocatedNXParityBlock.analyticBlock)
              (right.map LocatedNXParityBlock.analyticBlock)
              (labeledCopyPoint z (σ anchor))
              (labeledCopyPoint z (σ previous))
              (locatedAnchoredScheduleAssignment σ
                (.pair i j p :: left) right) := by
          simp [locatedBlockEliminationKernel,
            LocatedNXParityBlock.analyticBlock,
            locatedAnchoredScheduleAssignment,
            nxAnchoredScheduleKernel, hprevious,
            mul_assoc]
  | roughPair previous i j p left hprevious hinternal hrest ih =>
      calc
        locatedLedgerEliminationKernelProduct
              ht hroot Nm mu z hz R anchor σ
                (.roughPair i j p :: left) *
            locatedLedgerEliminationKernelProduct
              ht hroot Nm mu z hz R anchor σ right =
          locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ (.roughPair i j p) *
            (locatedLedgerEliminationKernelProduct
                ht hroot Nm mu z hz R anchor σ left *
              locatedLedgerEliminationKernelProduct
                ht hroot Nm mu z hz R anchor σ right) := by
                  simp [locatedLedgerEliminationKernelProduct,
                    mul_assoc]
        _ = locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ (.roughPair i j p) *
            nxAnchoredScheduleKernel ht hroot Nm mu z hz R
              (left.map LocatedNXParityBlock.analyticBlock)
              (right.map LocatedNXParityBlock.analyticBlock)
              (labeledCopyPoint z (σ anchor))
              (labeledCopyPoint z (σ j))
              (locatedAnchoredScheduleAssignment σ left right) :=
          congrArg
            (locatedBlockEliminationKernel
              ht hroot Nm mu z hz R anchor σ (.roughPair i j p) * ·) ih
        _ = nxAnchoredScheduleKernel ht hroot Nm mu z hz R
              ((.roughPair i j p :: left).map
                LocatedNXParityBlock.analyticBlock)
              (right.map LocatedNXParityBlock.analyticBlock)
              (labeledCopyPoint z (σ anchor))
              (labeledCopyPoint z (σ previous))
              (locatedAnchoredScheduleAssignment σ
                (.roughPair i j p :: left) right) := by
          simp [locatedBlockEliminationKernel,
            LocatedNXParityBlock.analyticBlock,
            locatedAnchoredScheduleAssignment,
            nxAnchoredScheduleKernel, hprevious,
            mul_assoc]

/--
Pointwise bridge ready for the finite-Fubini monotonicity theorem.  The only
structural inputs are the two consecutive-run certificates; all analytic
kernel comparison has already been discharged by `KernelSchedule`.
-/
theorem edgeKernelProduct_le_finAnchorNXAnchoredScheduleKernel_of_consecutive
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (O : Finset (AdjacentIndex m))
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (σ : Fin m → HeppLabeledCopy mu)
    (hleft :
      LocatedRunConsecutive anchor anchor
        (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).left)
    (hright :
      LocatedRunConsecutive anchor anchor
        (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).right) :
    (∏ edge : AdjacentIndex m,
        finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls σ edge) ≤
      nxAnchoredScheduleKernel ht hroot Nm mu z hz R
        ((finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).left.map
            LocatedNXParityBlock.analyticBlock)
        ((finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).right.map
            LocatedNXParityBlock.analyticBlock)
        (labeledCopyPoint z (σ anchor))
        (labeledCopyPoint z (σ anchor))
        (locatedAnchoredScheduleAssignment σ
          (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
            leftPhase rightPhase anchor cls O).left
          (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
            leftPhase rightPhase anchor cls O).right) := by
  calc
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
            leftPhase rightPhase anchor cls O).right :=
      edgeKernelProduct_le_finAnchorNXLocatedOutwardRunsProduct
        ht hroot Nm mu z hz R O leftPhase rightPhase anchor cls σ
    _ = _ :=
      locatedOutwardRunsEliminationKernelProduct_eq_anchoredScheduleKernel
        ht hroot Nm mu z hz R anchor σ
        (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).left
        (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).right
        anchor hleft hright

/-! ## Canonical finite-Fubini assignment -/

theorem flatMap_positionEntries_finAnchorNXLocatedCoarseRuns_left
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    ((finAnchorNXLocatedCoarseRunsWithPhases Nm mu
        leftPhase rightPhase anchor cls O).left.flatMap
      (fun b => b.positionBlock.entries)) =
      leftAnchorPositions anchor := by
  rw [← List.flatMap_map]
  rw [map_positionBlock_finAnchorNXLocatedCoarseRunsWithPhases_left]
  exact flatten_pairPositionRun leftPhase (leftAnchorPositions anchor)

theorem flatMap_positionEntries_finAnchorNXLocatedCoarseRuns_right
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    ((finAnchorNXLocatedCoarseRunsWithPhases Nm mu
        leftPhase rightPhase anchor cls O).right.flatMap
      (fun b => b.positionBlock.entries)) =
      rightAnchorPositions anchor := by
  rw [← List.flatMap_map]
  rw [map_positionBlock_finAnchorNXLocatedCoarseRunsWithPhases_right]
  exact flatten_pairPositionRun rightPhase (rightAnchorPositions anchor)

theorem append_flatMap_positionEntries_finAnchorNXLocatedCoarseRuns
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    ((finAnchorNXLocatedCoarseRunsWithPhases Nm mu
        leftPhase rightPhase anchor cls O).left.flatMap
          (fun b => b.positionBlock.entries)) ++
      ((finAnchorNXLocatedCoarseRunsWithPhases Nm mu
        leftPhase rightPhase anchor cls O).right.flatMap
          (fun b => b.positionBlock.entries)) =
      (finAnchorPositionScheduleWithPhases
        leftPhase rightPhase anchor).flatMap
          PositionBlock.entries := by
  rw [flatMap_positionEntries_finAnchorNXLocatedCoarseRuns_left,
    flatMap_positionEntries_finAnchorNXLocatedCoarseRuns_right]
  simp [finAnchorPositionScheduleWithPhases,
    anchorPositionScheduleWithPhases, flatten_pairPositionRun]

theorem nxParityScheduleArity_finAnchorNXLocatedCoarseRunsWithPhases
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (cls : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (totalMultiplicity mu))) :
    nxParityScheduleArity
        ((finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).left.map
            LocatedNXParityBlock.analyticBlock ++
        (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).right.map
            LocatedNXParityBlock.analyticBlock) =
      paperTailLength mu := by
  rw [map_analyticBlock_finAnchorNXLocatedCoarseRunsWithPhases_left,
    map_analyticBlock_finAnchorNXLocatedCoarseRunsWithPhases_right]
  exact
    nxParityScheduleArity_finAnchorNXCoarseRunsWithPhases
      Nm mu leftPhase rightPhase anchor cls O

theorem map_paperFinAnchorAssignmentFromTail_outwardOrder
    {t : PlaneTree} {mu : Multiplicities t}
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (b : HeppLabeledCopy mu)
    (tail : Fin (paperTailLength mu) → HeppLabeledCopy mu) :
    (paperFinAnchorOutwardOrderWithPhases
        leftPhase rightPhase anchor).map
      (paperFinAnchorAssignmentFromTail
        leftPhase rightPhase anchor b tail) =
      List.ofFn tail := by
  let order :=
    paperFinAnchorOutwardOrderWithPhases
      leftPhase rightPhase anchor
  let hlen :=
    length_paperFinAnchorOutwardOrderWithPhases
      leftPhase rightPhase anchor
  let σ :=
    paperFinAnchorAssignmentFromTail
      leftPhase rightPhase anchor b tail
  calc
    order.map σ =
        List.ofFn (σ ∘ scheduleTail order hlen) := by
      rw [← List.map_ofFn, ofFn_scheduleTail]
    _ = List.ofFn tail := by
      congr 1
      funext i
      change
        paperFinAnchorAssignmentFromTail
            leftPhase rightPhase anchor b tail
              (scheduleTail
                (paperFinAnchorOutwardOrderWithPhases
                  leftPhase rightPhase anchor)
                (length_paperFinAnchorOutwardOrderWithPhases
                  leftPhase rightPhase anchor) i) =
          tail i
      rw [←
        paperFinAnchorOutwardEquivWithPhases_succ
          leftPhase rightPhase anchor i]
      exact
        paperFinAnchorAssignmentFromTail_outward
          leftPhase rightPhase anchor b tail i

/--
The assignment reconstructed by finite Fubini is consumed by the located
left/right ledgers as exactly the supplied tail tuple.
-/
theorem locatedAnchoredScheduleAssignment_finAnchor_fromTail
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (cls : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (totalMultiplicity mu)))
    (b : HeppLabeledCopy mu)
    (tail : Fin (paperTailLength mu) → HeppLabeledCopy mu) :
    locatedAnchoredScheduleAssignment
        (paperFinAnchorAssignmentFromTail
          leftPhase rightPhase anchor b tail)
        (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).left
        (finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).right =
      tail ∘ Fin.cast
        (nxParityScheduleArity_finAnchorNXLocatedCoarseRunsWithPhases
          Nm mu leftPhase rightPhase anchor cls O) := by
  apply List.ofFn_injective
  rw [ofFn_locatedAnchoredScheduleAssignment]
  rw [append_flatMap_positionEntries_finAnchorNXLocatedCoarseRuns]
  change
    (paperFinAnchorOutwardOrderWithPhases
        leftPhase rightPhase anchor).map
        (paperFinAnchorAssignmentFromTail
          leftPhase rightPhase anchor b tail) =
      List.ofFn
        (tail ∘ Fin.cast
          (nxParityScheduleArity_finAnchorNXLocatedCoarseRunsWithPhases
            Nm mu leftPhase rightPhase anchor cls O))
  rw [ofFn_comp_finCast]
  exact
    map_paperFinAnchorAssignmentFromTail_outwardOrder
      leftPhase rightPhase anchor b tail

theorem nxAnchoredScheduleKernel_congr_cast
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ)
    (left right left' right' : List (NXParityBlock Nm mu))
    (hleft : left = left') (hright : right = right')
    (anchorPoint u : Fin 4 → ℤ)
    (n : ℕ)
    (hArity : nxParityScheduleArity (left ++ right) = n)
    (hArity' : nxParityScheduleArity (left' ++ right') = n)
    (f : Fin n → HeppLabeledCopy mu) :
    nxAnchoredScheduleKernel ht hroot Nm mu z hz R
        left right anchorPoint u
        (f ∘ Fin.cast hArity) =
      nxAnchoredScheduleKernel ht hroot Nm mu z hz R
        left' right' anchorPoint u
        (f ∘ Fin.cast hArity') := by
  subst left'
  subst right'
  rfl

/--
Canonical pointwise bound for the fixed-fiber CPS theorem.  Consecutiveness,
anchor reconstruction, analytic erasure, and the two arity casts are all
discharged internally.
-/
theorem edgeKernelProduct_le_finAnchorNXAnchoredScheduleKernel_fromTail
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ)
    (O : Finset (AdjacentIndex (totalMultiplicity mu)))
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (cls : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (b : HeppLabeledCopy mu)
    (tail : Fin (paperTailLength mu) → HeppLabeledCopy mu) :
    (∏ edge : AdjacentIndex (totalMultiplicity mu),
        finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls
            (paperFinAnchorAssignmentFromTail
              leftPhase rightPhase anchor b tail) edge) ≤
      nxAnchoredScheduleKernel ht hroot Nm mu z hz R
        (finAnchorNXCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).left
        (finAnchorNXCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).right
        (labeledCopyPoint z b)
        (labeledCopyPoint z b)
        (tail ∘ Fin.cast
          (nxParityScheduleArity_finAnchorNXCoarseRunsWithPhases
            Nm mu leftPhase rightPhase anchor cls O)) := by
  let σ :=
    paperFinAnchorAssignmentFromTail
      leftPhase rightPhase anchor b tail
  have hconsecutive :=
    finAnchorNXLocatedCoarseRuns_consecutive_of_chainCondition
      Nm mu leftPhase rightPhase anchor cls O
        (finAnchorOutwardChainCondition anchor)
  have hle :=
    edgeKernelProduct_le_finAnchorNXAnchoredScheduleKernel_of_consecutive
      ht hroot Nm mu z hz R O leftPhase rightPhase anchor cls σ
      hconsecutive.1 hconsecutive.2
  rw [locatedAnchoredScheduleAssignment_finAnchor_fromTail] at hle
  have hle' :
      (∏ edge : AdjacentIndex (totalMultiplicity mu),
          finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
            R O leftPhase rightPhase anchor cls
              (paperFinAnchorAssignmentFromTail
                leftPhase rightPhase anchor b tail) edge) ≤
        nxAnchoredScheduleKernel ht hroot Nm mu z hz R
          ((finAnchorNXLocatedCoarseRunsWithPhases Nm mu
            leftPhase rightPhase anchor cls O).left.map
              LocatedNXParityBlock.analyticBlock)
          ((finAnchorNXLocatedCoarseRunsWithPhases Nm mu
            leftPhase rightPhase anchor cls O).right.map
              LocatedNXParityBlock.analyticBlock)
          (labeledCopyPoint z b)
          (labeledCopyPoint z b)
          (tail ∘ Fin.cast
            (nxParityScheduleArity_finAnchorNXLocatedCoarseRunsWithPhases
              Nm mu leftPhase rightPhase anchor cls O)) := by
    simpa only [σ, paperFinAnchorAssignmentFromTail_anchor] using hle
  calc
    (∏ edge : AdjacentIndex (totalMultiplicity mu),
        finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor cls
            (paperFinAnchorAssignmentFromTail
              leftPhase rightPhase anchor b tail) edge) ≤
      nxAnchoredScheduleKernel ht hroot Nm mu z hz R
        ((finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).left.map
            LocatedNXParityBlock.analyticBlock)
        ((finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).right.map
            LocatedNXParityBlock.analyticBlock)
        (labeledCopyPoint z b)
        (labeledCopyPoint z b)
        (tail ∘ Fin.cast
          (nxParityScheduleArity_finAnchorNXLocatedCoarseRunsWithPhases
            Nm mu leftPhase rightPhase anchor cls O)) := hle'
    _ = _ :=
      nxAnchoredScheduleKernel_congr_cast
        ht hroot Nm mu z hz R
        ((finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).left.map
            LocatedNXParityBlock.analyticBlock)
        ((finAnchorNXLocatedCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).right.map
            LocatedNXParityBlock.analyticBlock)
        (finAnchorNXCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).left
        (finAnchorNXCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).right
        (map_analyticBlock_finAnchorNXLocatedCoarseRunsWithPhases_left
          Nm mu leftPhase rightPhase anchor cls O)
        (map_analyticBlock_finAnchorNXLocatedCoarseRunsWithPhases_right
          Nm mu leftPhase rightPhase anchor cls O)
        (labeledCopyPoint z b) (labeledCopyPoint z b)
        (paperTailLength mu)
        (nxParityScheduleArity_finAnchorNXLocatedCoarseRunsWithPhases
          Nm mu leftPhase rightPhase anchor cls O)
        (nxParityScheduleArity_finAnchorNXCoarseRunsWithPhases
          Nm mu leftPhase rightPhase anchor cls O)
        tail

end XYCluster

end

end Anderson4D
