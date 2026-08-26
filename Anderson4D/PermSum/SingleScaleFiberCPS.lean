import Anderson4D.PermSum.SingleScaleArrangementFubini
import Anderson4D.PermSum.SingleScaleKernelSchedule

/-!
# Fixed-fiber Fubini to the shared-state CPS eliminator

The arrangement fiber exposes the anchor and then a `Fin`-indexed outward
tail.  This file gives the analytic block schedule its own exact arity,
class word, and assignment monomial.  Repeated use of the exact
`classifiedTupleSum_succ` identity identifies the resulting finite sum with
the conditioned eliminator, including the shared used-copy state between
the left and right runs.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/-! ## Sequential class words and assignment monomials -/

/-- Number of labeled copies consumed by one analytic block. -/
def nxParityBlockArity {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t} :
    NXParityBlock Nm mu → ℕ
  | .single _ _ => 1
  | .pair _ | .roughPair _ => 2

/-- Total number of copies consumed by an analytic schedule. -/
def nxParityScheduleArity {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t} :
    List (NXParityBlock Nm mu) → ℕ
  | [] => 0
  | .single _ _ :: ps => nxParityScheduleArity ps + 1
  | .pair _ :: ps | .roughPair _ :: ps =>
      nxParityScheduleArity ps + 2

@[simp] theorem nxParityScheduleArity_append
    {t : PlaneTree} {Nm : HeppMarking t} {mu : Multiplicities t}
    (ps qs : List (NXParityBlock Nm mu)) :
    nxParityScheduleArity (ps ++ qs) =
      nxParityScheduleArity ps + nxParityScheduleArity qs := by
  induction ps with
  | nil =>
      simp [nxParityScheduleArity]
  | cons p ps ih =>
      cases p <;> simp [nxParityScheduleArity, ih] <;> omega

/-- Underlying `(N,X)` class word consumed by a schedule. -/
def nxParityScheduleClasses {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t} :
    (ps : List (NXParityBlock Nm mu)) →
      Fin (nxParityScheduleArity ps) → NXClass
  | [], i => Fin.elim0 i
  | .single a _ :: ps, i =>
      @Fin.cons (nxParityScheduleArity ps)
        (fun _ => NXClass) a.1 (nxParityScheduleClasses ps) i
  | .pair p :: ps, i | .roughPair p :: ps, i =>
      @Fin.cons (nxParityScheduleArity ps + 1)
        (fun _ => NXClass) p.left.1
        (@Fin.cons (nxParityScheduleArity ps)
          (fun _ => NXClass) p.right.1
          (nxParityScheduleClasses ps)) i

/-- The same class word as an ordinary list, useful for comparing the
analytic schedule with the flattened paper-position schedule. -/
def nxParityBlockClassList {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t} :
    NXParityBlock Nm mu → List NXClass
  | .single a _ => [a.1]
  | .pair p | .roughPair p => [p.left.1, p.right.1]

def nxParityScheduleClassList {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (ps : List (NXParityBlock Nm mu)) : List NXClass :=
  ps.flatMap nxParityBlockClassList

@[simp] theorem length_nxParityScheduleClassList
    {t : PlaneTree} {Nm : HeppMarking t} {mu : Multiplicities t}
    (ps : List (NXParityBlock Nm mu)) :
    (nxParityScheduleClassList ps).length =
      nxParityScheduleArity ps := by
  induction ps with
  | nil =>
      rfl
  | cons p ps ih =>
      cases p with
      | single a skipped =>
          change
            ([a.1] ++ nxParityScheduleClassList ps).length =
              nxParityScheduleArity ps + 1
          simp [ih]
      | pair p =>
          change
            ([p.left.1, p.right.1] ++
              nxParityScheduleClassList ps).length =
                nxParityScheduleArity ps + 2
          simp [ih]
      | roughPair p =>
          change
            ([p.left.1, p.right.1] ++
              nxParityScheduleClassList ps).length =
                nxParityScheduleArity ps + 2
          simp [ih]

@[simp] theorem ofFn_nxParityScheduleClasses
    {t : PlaneTree} {Nm : HeppMarking t} {mu : Multiplicities t}
    (ps : List (NXParityBlock Nm mu)) :
    List.ofFn (nxParityScheduleClasses ps) =
      nxParityScheduleClassList ps := by
  induction ps with
  | nil =>
      rfl
  | cons p ps ih =>
      cases p with
      | single a skipped =>
          change
            List.ofFn
                (Fin.cons a.1 (nxParityScheduleClasses ps)) =
              [a.1] ++ nxParityScheduleClassList ps
          rw [List.ofFn_cons, ih]
          rfl
      | pair p =>
          change
            List.ofFn
                (Fin.cons p.left.1
                  (Fin.cons p.right.1
                    (nxParityScheduleClasses ps))) =
              [p.left.1, p.right.1] ++
                nxParityScheduleClassList ps
          rw [List.ofFn_cons, List.ofFn_cons, ih]
          rfl
      | roughPair p =>
          change
            List.ofFn
                (Fin.cons p.left.1
                  (Fin.cons p.right.1
                    (nxParityScheduleClasses ps))) =
              [p.left.1, p.right.1] ++
                nxParityScheduleClassList ps
          rw [List.ofFn_cons, List.ofFn_cons, ih]
          rfl

/-- Attaching payloads to a position block records exactly the classes of
its entries, in traversal order. -/
@[simp] theorem nxParityBlockClassList_positionBlockToNXParityBlock
    {α : Type*} {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (cls : α → ActiveNXClass Nm mu)
    (incomingSkipped : α → Bool) (b : PositionBlock α) :
    nxParityBlockClassList
        (positionBlockToNXParityBlock Nm mu cls incomingSkipped b) =
      b.entries.map (fun i => (cls i).1) := by
  cases b <;>
    rfl

theorem nxParityScheduleClassList_map_positionBlocks
    {α : Type*} {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (cls : α → ActiveNXClass Nm mu)
    (incomingSkipped : α → Bool) (bs : List (PositionBlock α)) :
    nxParityScheduleClassList
        (bs.map
          (positionBlockToNXParityBlock Nm mu cls incomingSkipped)) =
      (bs.flatMap PositionBlock.entries).map
        (fun i => (cls i).1) := by
  induction bs with
  | nil =>
      rfl
  | cons b bs ih =>
      change
        nxParityBlockClassList
              (positionBlockToNXParityBlock
                Nm mu cls incomingSkipped b) ++
            nxParityScheduleClassList
              (bs.map
                (positionBlockToNXParityBlock
                  Nm mu cls incomingSkipped)) =
          (b.entries ++ bs.flatMap PositionBlock.entries).map
            (fun i => (cls i).1)
      rw [nxParityBlockClassList_positionBlockToNXParityBlock,
        ih, List.map_append]

/-- Rough-pair marking changes only the estimate selected for a pair, not
the ordered class word which is summed over. -/
theorem nxParityScheduleClassList_markFirstSkippedPairsRough
    {t : PlaneTree} {Nm : HeppMarking t} {mu : Multiplicities t}
    (fuel : ℕ) (ps : List (NXParityBlock Nm mu)) :
    nxParityScheduleClassList
        (markFirstSkippedPairsRough fuel ps) =
      nxParityScheduleClassList ps := by
  induction ps generalizing fuel with
  | nil =>
      simp [markFirstSkippedPairsRough, nxParityScheduleClassList]
  | cons p ps ih =>
      cases fuel with
      | zero =>
          rfl
      | succ fuel =>
          cases p with
          | single a skipped =>
              change
                [a.1] ++ nxParityScheduleClassList
                    (markFirstSkippedPairsRough (fuel + 1) ps) =
                  [a.1] ++ nxParityScheduleClassList ps
              rw [ih]
          | pair p =>
              by_cases h : nxPairBlockTouchesSkip p
              · simp only [markFirstSkippedPairsRough, h, if_true]
                change
                  [p.left.1, p.right.1] ++
                      nxParityScheduleClassList
                        (markFirstSkippedPairsRough fuel ps) =
                    [p.left.1, p.right.1] ++
                      nxParityScheduleClassList ps
                rw [ih]
              · simp only [markFirstSkippedPairsRough, h]
                change
                  [p.left.1, p.right.1] ++
                      nxParityScheduleClassList
                        (markFirstSkippedPairsRough (fuel + 1) ps) =
                    [p.left.1, p.right.1] ++
                      nxParityScheduleClassList ps
                rw [ih]
          | roughPair p =>
              change
                [p.left.1, p.right.1] ++
                    nxParityScheduleClassList
                      (markFirstSkippedPairsRough (fuel + 1) ps) =
                  [p.left.1, p.right.1] ++
                    nxParityScheduleClassList ps
              rw [ih]

/-- The analytic coarse ledger spells the paper's concrete outward class
word exactly; rough marking neither permutes nor duplicates a position. -/
theorem nxParityScheduleClassList_finAnchorNXCoarseLedgerWithPhases
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (cls : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (totalMultiplicity mu))) :
    nxParityScheduleClassList
        (finAnchorNXCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) =
      (paperFinAnchorOutwardOrderWithPhases
        leftPhase rightPhase anchor).map
          (fun i => (cls i).1) := by
  rw [finAnchorNXCoarseLedgerWithPhases,
    nxParityScheduleClassList_markFirstSkippedPairsRough]
  unfold finAnchorNXParityLedgerWithPhases
    finAnchorNXParityRunsWithPhases AnchoredNXParityRuns.ledger
  rw [show
    nxParityScheduleClassList
        ((pairPositionRun leftPhase
            (leftAnchorPositions anchor)).map
          (positionBlockToNXParityBlock Nm mu cls
            (positionIncomingSkipped O .reverse)) ++
        (pairPositionRun rightPhase
            (rightAnchorPositions anchor)).map
          (positionBlockToNXParityBlock Nm mu cls
            (positionIncomingSkipped O .forward))) =
      nxParityScheduleClassList
          ((pairPositionRun leftPhase
              (leftAnchorPositions anchor)).map
            (positionBlockToNXParityBlock Nm mu cls
              (positionIncomingSkipped O .reverse))) ++
        nxParityScheduleClassList
          ((pairPositionRun rightPhase
              (rightAnchorPositions anchor)).map
            (positionBlockToNXParityBlock Nm mu cls
              (positionIncomingSkipped O .forward))) by
      simp [nxParityScheduleClassList]]
  rw [nxParityScheduleClassList_map_positionBlocks,
    nxParityScheduleClassList_map_positionBlocks]
  simp [paperFinAnchorOutwardOrderWithPhases,
    finAnchorPositionScheduleWithPhases,
    anchorPositionScheduleWithPhases, flatten_pairPositionRun]

@[simp] theorem nxParityScheduleArity_finAnchorNXCoarseRunsWithPhases
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (cls : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (totalMultiplicity mu))) :
    nxParityScheduleArity
        (finAnchorNXCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).ledger =
      paperTailLength mu := by
  rw [finAnchorNXCoarseRunsWithPhases_ledger]
  calc
    nxParityScheduleArity
        (finAnchorNXCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) =
        (nxParityScheduleClassList
          (finAnchorNXCoarseLedgerWithPhases Nm mu
            leftPhase rightPhase anchor cls O)).length := by
          symm
          exact length_nxParityScheduleClassList _
    _ = ((paperFinAnchorOutwardOrderWithPhases
          leftPhase rightPhase anchor).map
            (fun i => (cls i).1)).length := by
          rw [
            nxParityScheduleClassList_finAnchorNXCoarseLedgerWithPhases]
    _ = paperTailLength mu := by
          simp

/-- Reading the list presentation of a schedule by its canonical finite
index recovers the recursive `Fin.cons` class function. -/
private theorem scheduleTail_eq_of_ofFn_eq
    {α : Type*} {n : ℕ} (f : Fin n → α) (xs : List α)
    (hxs : List.ofFn f = xs) (hlen : xs.length = n) :
    scheduleTail xs hlen = f := by
  subst xs
  funext i
  simp [scheduleTail]

@[simp] theorem scheduleTail_nxParityScheduleClassList
    {t : PlaneTree} {Nm : HeppMarking t} {mu : Multiplicities t}
    (ps : List (NXParityBlock Nm mu))
    (i : Fin (nxParityScheduleArity ps)) :
    scheduleTail (nxParityScheduleClassList ps)
        (length_nxParityScheduleClassList ps) i =
      nxParityScheduleClasses ps i := by
  exact congrFun
    (scheduleTail_eq_of_ofFn_eq
      (nxParityScheduleClasses ps)
      (nxParityScheduleClassList ps)
      (ofFn_nxParityScheduleClasses ps)
      (length_nxParityScheduleClassList ps)) i

/-- `scheduleTail` commutes with mapping an ordinary finite list. -/
theorem scheduleTail_map {α β : Type*} {n : ℕ}
    (f : α → β) (xs : List α) (hlen : xs.length = n)
    (i : Fin n) :
    scheduleTail (xs.map f) (by simpa using hlen) i =
      f (scheduleTail xs hlen i) := by
  simp [scheduleTail]

private theorem scheduleTail_congr
    {α : Type*} {n : ℕ} (xs ys : List α)
    (hxs : xs.length = n) (hys : ys.length = n)
    (h : xs = ys) :
    scheduleTail xs hxs = scheduleTail ys hys := by
  subst ys
  rfl

private theorem scheduleTail_cast
    {α : Type*} {n m : ℕ} (xs : List α)
    (hn : xs.length = n) (hm : xs.length = m)
    (i : Fin n) :
    scheduleTail xs hn i =
      scheduleTail xs hm (Fin.cast (hn.symm.trans hm) i) := by
  simp [scheduleTail]

@[simp] theorem nxParityScheduleArity_finAnchorNXCoarseLedgerWithPhases
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (cls : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (totalMultiplicity mu))) :
    nxParityScheduleArity
        (finAnchorNXCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) =
      paperTailLength mu := by
  rw [← length_nxParityScheduleClassList,
    nxParityScheduleClassList_finAnchorNXCoarseLedgerWithPhases]
  simp

/--
The recursive CPS class function is exactly the class word exposed by the
paper's concrete outward equivalence.
-/
theorem nxParityScheduleClasses_finAnchorNXCoarseLedgerWithPhases
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (cls : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (totalMultiplicity mu)))
    (i : Fin
      (nxParityScheduleArity
        (finAnchorNXCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O))) :
    nxParityScheduleClasses
        (finAnchorNXCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) i =
      (cls
        ((paperFinAnchorOutwardEquivWithPhases
          leftPhase rightPhase anchor)
            (Fin.cast
              (nxParityScheduleArity_finAnchorNXCoarseLedgerWithPhases
                Nm mu leftPhase rightPhase anchor cls O) i).succ)).1 := by
  let ps :=
    finAnchorNXCoarseLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O
  let order :=
    paperFinAnchorOutwardOrderWithPhases
      leftPhase rightPhase anchor
  let hArity : nxParityScheduleArity ps = paperTailLength mu :=
    nxParityScheduleArity_finAnchorNXCoarseLedgerWithPhases
      Nm mu leftPhase rightPhase anchor cls O
  let hOrderPaper : order.length = paperTailLength mu :=
    length_paperFinAnchorOutwardOrderWithPhases
      leftPhase rightPhase anchor
  let hOrderArity : order.length = nxParityScheduleArity ps :=
    hOrderPaper.trans hArity.symm
  let hMapped :
      (order.map (fun j => (cls j).1)).length =
        nxParityScheduleArity ps := by
    simpa using hOrderArity
  have hClassList :
      nxParityScheduleClassList ps =
        order.map (fun j => (cls j).1) := by
    exact
      nxParityScheduleClassList_finAnchorNXCoarseLedgerWithPhases
        Nm mu leftPhase rightPhase anchor cls O
  have hTailClass :
      scheduleTail (nxParityScheduleClassList ps)
          (length_nxParityScheduleClassList ps) =
        scheduleTail (order.map (fun j => (cls j).1))
          hMapped :=
    scheduleTail_congr _ _
      (length_nxParityScheduleClassList ps) hMapped hClassList
  calc
    nxParityScheduleClasses ps i =
        scheduleTail (nxParityScheduleClassList ps)
          (length_nxParityScheduleClassList ps) i := by
            symm
            exact scheduleTail_nxParityScheduleClassList ps i
    _ = scheduleTail (order.map (fun j => (cls j).1))
          hMapped i := congrFun hTailClass i
    _ = (cls (scheduleTail order hOrderArity i)).1 := by
          exact scheduleTail_map
            (fun j => (cls j).1) order hOrderArity i
    _ = (cls
          (scheduleTail order hOrderPaper
            (Fin.cast hArity i))).1 := by
          rw [scheduleTail_cast order hOrderArity hOrderPaper i]
    _ = (cls
        ((paperFinAnchorOutwardEquivWithPhases
          leftPhase rightPhase anchor)
            (Fin.cast hArity i).succ)).1 := by
          rw [
            paperFinAnchorOutwardEquivWithPhases_succ]

theorem nxParityScheduleClasses_finAnchorNXCoarseLedgerWithPhases_fun
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (cls : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (totalMultiplicity mu))) :
    nxParityScheduleClasses
        (finAnchorNXCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) =
      (fun i : Fin (paperTailLength mu) =>
        (cls
          ((paperFinAnchorOutwardEquivWithPhases
            leftPhase rightPhase anchor) i.succ)).1) ∘
        Fin.cast
          (nxParityScheduleArity_finAnchorNXCoarseLedgerWithPhases
            Nm mu leftPhase rightPhase anchor cls O) := by
  funext i
  exact
    nxParityScheduleClasses_finAnchorNXCoarseLedgerWithPhases
      Nm mu leftPhase rightPhase anchor cls O i

@[simp] theorem ofFn_scheduleTail {α : Type*} {n : ℕ}
    (order : List α) (hlen : order.length = n) :
    List.ofFn (scheduleTail order hlen) = order := by
  subst n
  change List.ofFn order.get = order
  exact List.ofFn_get order

theorem ofFn_comp_finCast {α : Type*} {m n : ℕ}
    (h : m = n) (f : Fin n → α) :
    List.ofFn (f ∘ Fin.cast h) = List.ofFn f := by
  subst n
  rfl

theorem ofFn_finAnchorOutward_tailClasses
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (cls : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu) :
    List.ofFn
        (fun i : Fin (paperTailLength mu) =>
          (cls
            ((paperFinAnchorOutwardEquivWithPhases
              leftPhase rightPhase anchor) i.succ)).1) =
      (paperFinAnchorOutwardOrderWithPhases
        leftPhase rightPhase anchor).map
          (fun i => (cls i).1) := by
  simp only [paperFinAnchorOutwardEquivWithPhases_succ]
  change
    List.ofFn
        ((fun i => (cls i).1) ∘
          scheduleTail
            (paperFinAnchorOutwardOrderWithPhases
              leftPhase rightPhase anchor)
            (length_paperFinAnchorOutwardOrderWithPhases
              leftPhase rightPhase anchor)) =
      _
  rw [← List.map_ofFn, ofFn_scheduleTail]

theorem nxParityScheduleClasses_finAnchorNXCoarseRunsWithPhases_fun
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (cls : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (totalMultiplicity mu))) :
    let runs :=
      finAnchorNXCoarseRunsWithPhases Nm mu
        leftPhase rightPhase anchor cls O
    nxParityScheduleClasses runs.ledger =
      (fun i : Fin (paperTailLength mu) =>
        (cls
          ((paperFinAnchorOutwardEquivWithPhases
            leftPhase rightPhase anchor) i.succ)).1) ∘
        Fin.cast
          (nxParityScheduleArity_finAnchorNXCoarseRunsWithPhases
            Nm mu leftPhase rightPhase anchor cls O) := by
  dsimp only
  apply List.ofFn_injective
  rw [ofFn_nxParityScheduleClasses]
  rw [show
    nxParityScheduleClassList
        (finAnchorNXCoarseRunsWithPhases Nm mu
          leftPhase rightPhase anchor cls O).ledger =
      (paperFinAnchorOutwardOrderWithPhases
        leftPhase rightPhase anchor).map
          (fun i => (cls i).1) by
      rw [finAnchorNXCoarseRunsWithPhases_ledger,
        nxParityScheduleClassList_finAnchorNXCoarseLedgerWithPhases]]
  rw [← ofFn_finAnchorOutward_tailClasses
    Nm mu leftPhase rightPhase anchor cls]
  exact
    (ofFn_comp_finCast
      (nxParityScheduleArity_finAnchorNXCoarseRunsWithPhases
        Nm mu leftPhase rightPhase anchor cls O) _).symm

/-! ## Reconstructing the full position assignment -/

/-- Insert the exposed anchor copy in front of an outward tail and transport
the result back to the original paper positions. -/
noncomputable def paperFinAnchorAssignmentFromTail
    {t : PlaneTree} {mu : Multiplicities t}
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (b : HeppLabeledCopy mu)
    (tail : Fin (paperTailLength mu) → HeppLabeledCopy mu) :
    Fin (totalMultiplicity mu) → HeppLabeledCopy mu :=
  fun j =>
    @Fin.cons (paperTailLength mu)
      (fun _ => HeppLabeledCopy mu) b tail
      ((paperFinAnchorOutwardEquivWithPhases
        leftPhase rightPhase anchor).symm j)

@[simp] theorem paperFinAnchorAssignmentFromTail_anchor
    {t : PlaneTree} {mu : Multiplicities t}
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (b : HeppLabeledCopy mu)
    (tail : Fin (paperTailLength mu) → HeppLabeledCopy mu) :
    paperFinAnchorAssignmentFromTail
      leftPhase rightPhase anchor b tail anchor = b := by
  unfold paperFinAnchorAssignmentFromTail
  have hzero :
      (paperFinAnchorOutwardEquivWithPhases
        leftPhase rightPhase anchor).symm anchor = 0 := by
    apply
      (paperFinAnchorOutwardEquivWithPhases
        leftPhase rightPhase anchor).injective
    simp
  rw [hzero]
  rfl

@[simp] theorem paperFinAnchorAssignmentFromTail_outward
    {t : PlaneTree} {mu : Multiplicities t}
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (b : HeppLabeledCopy mu)
    (tail : Fin (paperTailLength mu) → HeppLabeledCopy mu)
    (i : Fin (paperTailLength mu)) :
    paperFinAnchorAssignmentFromTail
      leftPhase rightPhase anchor b tail
        ((paperFinAnchorOutwardEquivWithPhases
          leftPhase rightPhase anchor) i.succ) =
      tail i := by
  unfold paperFinAnchorAssignmentFromTail
  have hsucc :
      (paperFinAnchorOutwardEquivWithPhases
        leftPhase rightPhase anchor).symm
          ((paperFinAnchorOutwardEquivWithPhases
            leftPhase rightPhase anchor) i.succ) =
        i.succ :=
    (paperFinAnchorOutwardEquivWithPhases
      leftPhase rightPhase anchor).symm_apply_apply i.succ
  rw [hsucc]
  rfl

/-- Head of a nonempty finite tuple, with a stable simplification rule. -/
def finTupleHead {β : Type*} {n : ℕ}
    (f : Fin (n + 1) → β) : β :=
  f 0

@[simp] theorem finTupleHead_cons {β : Type*} {n : ℕ}
    (b : β) (f : Fin n → β) :
    finTupleHead (Fin.cons b f) = b :=
  rfl

/--
Lambda/strongLambda monomial attached to a complete sequential assignment.
The endpoint of each block is the preceding point for the next block.
-/
noncomputable def nxParityScheduleKernel
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) :
    (ps : List (NXParityBlock Nm mu)) →
      (Fin 4 → ℤ) →
      (Fin (nxParityScheduleArity ps) → HeppLabeledCopy mu) → ℝ
  | [], _u, _f => 1
  | .single a skipped :: ps, u, f =>
      let ca := nxClassCluster ht hroot Nm mu z hz a.1 a.2
      ca.lambda R skipped u
          (labeledCopyPoint z (finTupleHead f)) *
        nxParityScheduleKernel ht hroot Nm mu z hz R ps
          (labeledCopyPoint z (finTupleHead f))
          (Fin.tail f)
  | .pair p :: ps, u, f | .roughPair p :: ps, u, f =>
      let ca :=
        nxClassCluster ht hroot Nm mu z hz p.left.1 p.left.2
      let cb :=
        nxClassCluster ht hroot Nm mu z hz p.right.1 p.right.2
      ca.lambda R p.skipLeft u
          (labeledCopyPoint z (finTupleHead f)) *
        strongLambda ca cb R p.skipRight
          (labeledCopyPoint z (finTupleHead f))
          (labeledCopyPoint z (finTupleHead (Fin.tail f))) *
        nxParityScheduleKernel ht hroot Nm mu z hz R ps
          (labeledCopyPoint z (finTupleHead (Fin.tail f)))
          (Fin.tail (Fin.tail f))

/--
Assignment monomial for two outward runs.  The right run starts only after
all left copies have been consumed, but its geometric starting point is
reset to the anchor.
-/
noncomputable def nxAnchoredScheduleKernel
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) :
    (left right : List (NXParityBlock Nm mu)) →
      (Fin 4 → ℤ) → (Fin 4 → ℤ) →
      (Fin (nxParityScheduleArity (left ++ right)) →
        HeppLabeledCopy mu) → ℝ
  | [], right, anchorPoint, _u, f =>
      nxParityScheduleKernel ht hroot Nm mu z hz R
        right anchorPoint f
  | .single a skipped :: left, right, anchorPoint, u, f =>
      let ca := nxClassCluster ht hroot Nm mu z hz a.1 a.2
      ca.lambda R skipped u
          (labeledCopyPoint z (finTupleHead f)) *
        nxAnchoredScheduleKernel ht hroot Nm mu z hz R
          left right anchorPoint
          (labeledCopyPoint z (finTupleHead f))
          (Fin.tail f)
  | .pair p :: left, right, anchorPoint, u, f
  | .roughPair p :: left, right, anchorPoint, u, f =>
      let ca :=
        nxClassCluster ht hroot Nm mu z hz p.left.1 p.left.2
      let cb :=
        nxClassCluster ht hroot Nm mu z hz p.right.1 p.right.2
      ca.lambda R p.skipLeft u
          (labeledCopyPoint z (finTupleHead f)) *
        strongLambda ca cb R p.skipRight
          (labeledCopyPoint z (finTupleHead f))
          (labeledCopyPoint z (finTupleHead (Fin.tail f))) *
        nxAnchoredScheduleKernel ht hroot Nm mu z hz R
          left right anchorPoint
          (labeledCopyPoint z (finTupleHead (Fin.tail f)))
          (Fin.tail (Fin.tail f))

/-! ## Exact tuple-sum recursion -/

theorem classifiedTupleSum_const_mul
    {β α : Type*} [Fintype β] [DecidableEq β] [DecidableEq α]
    {n : ℕ} (classify : β → α) (used : Finset β)
    (classes : Fin n → α) (c : ℝ)
    (F : (Fin n → β) → ℝ) :
    classifiedTupleSum classify used classes (fun f => c * F f) =
      c * classifiedTupleSum classify used classes F := by
  classical
  unfold classifiedTupleSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _hf
  by_cases h : ClassTupleAdmissible classify used classes f
  · simp [h]
  · simp [h]

theorem classifiedTupleSum_mono
    {β α : Type*} [Fintype β] [DecidableEq β] [DecidableEq α]
    {n : ℕ} (classify : β → α) (used : Finset β)
    (classes : Fin n → α) (F G : (Fin n → β) → ℝ)
    (hFG : ∀ f,
      ClassTupleAdmissible classify used classes f →
        F f ≤ G f) :
    classifiedTupleSum classify used classes F ≤
      classifiedTupleSum classify used classes G := by
  classical
  unfold classifiedTupleSum
  apply Finset.sum_le_sum
  intro f _hf
  by_cases h : ClassTupleAdmissible classify used classes f
  · simpa [h] using hFG f h
  · simp [h]

/-- Exact finite-Fubini identity for one analytic schedule. -/
theorem classifiedTupleSum_nxParityScheduleKernel
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (ps : List (NXParityBlock Nm mu))
    (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ) :
    classifiedTupleSum (labeledCopyNXClass Nm mu) used
        (nxParityScheduleClasses ps)
        (nxParityScheduleKernel ht hroot Nm mu z hz R ps u) =
      conditionedNXParityChainSum ht hroot Nm mu z hz R ps used u := by
  induction ps generalizing used u with
  | nil =>
      simp [nxParityScheduleArity, nxParityScheduleClasses,
        nxParityScheduleKernel, conditionedNXParityChainSum]
  | cons p ps ih =>
      cases p with
      | single a skipped =>
          simp only [nxParityScheduleArity,
            nxParityScheduleClasses]
          rw [classifiedTupleSum_succ]
          rw [classifiedAvailableValues_labeledCopyNXClass]
          simp only [nxParityScheduleKernel, finTupleHead_cons,
            Fin.cons_zero, Fin.tail_cons,
            conditionedNXParityChainSum]
          apply Finset.sum_congr rfl
          intro x _hx
          rw [classifiedTupleSum_const_mul]
          rw [ih]
      | pair p =>
          simp only [nxParityScheduleArity,
            nxParityScheduleClasses]
          rw [classifiedTupleSum_succ_succ]
          rw [classifiedAvailableValues_labeledCopyNXClass]
          simp only [nxParityScheduleKernel, finTupleHead_cons,
            Fin.cons_zero, Fin.tail_cons,
            conditionedNXParityChainSum]
          apply Finset.sum_congr rfl
          intro x _hx
          rw [classifiedAvailableValues_labeledCopyNXClass]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _hy
          rw [classifiedTupleSum_const_mul]
          rw [ih]
          ring
      | roughPair p =>
          simp only [nxParityScheduleArity,
            nxParityScheduleClasses]
          rw [classifiedTupleSum_succ_succ]
          rw [classifiedAvailableValues_labeledCopyNXClass]
          simp only [nxParityScheduleKernel, finTupleHead_cons,
            Fin.cons_zero, Fin.tail_cons,
            conditionedNXParityChainSum]
          apply Finset.sum_congr rfl
          intro x _hx
          rw [classifiedAvailableValues_labeledCopyNXClass]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _hy
          rw [classifiedTupleSum_const_mul]
          rw [ih]
          ring

/--
Exact two-run identity with one shared used-copy state and a geometric reset
at the anchor.  No concatenated analytic chain is introduced.
-/
theorem classifiedTupleSum_nxAnchoredScheduleKernel
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (left right : List (NXParityBlock Nm mu))
    (used : Finset (HeppLabeledCopy mu))
    (anchorPoint u : Fin 4 → ℤ) :
    classifiedTupleSum (labeledCopyNXClass Nm mu) used
        (nxParityScheduleClasses (left ++ right))
        (nxAnchoredScheduleKernel ht hroot Nm mu z hz R
          left right anchorPoint u) =
      conditionedNXParityChainSumThen ht hroot Nm mu z hz R
        left used u fun usedAfterLeft _leftEndpoint =>
          conditionedNXParityChainSum ht hroot Nm mu z hz R
            right usedAfterLeft anchorPoint := by
  induction left generalizing used u with
  | nil =>
      simp only [List.nil_append, nxAnchoredScheduleKernel,
        conditionedNXParityChainSumThen]
      exact classifiedTupleSum_nxParityScheduleKernel
        ht hroot Nm mu z hz R right used anchorPoint
  | cons p left ih =>
      cases p with
      | single a skipped =>
          simp only [List.cons_append, nxParityScheduleArity,
            nxParityScheduleClasses]
          rw [classifiedTupleSum_succ]
          rw [classifiedAvailableValues_labeledCopyNXClass]
          simp only [nxAnchoredScheduleKernel, finTupleHead_cons,
            Fin.cons_zero, Fin.tail_cons,
            conditionedNXParityChainSumThen]
          apply Finset.sum_congr rfl
          intro x _hx
          rw [classifiedTupleSum_const_mul]
          rw [ih]
      | pair p =>
          simp only [List.cons_append, nxParityScheduleArity,
            nxParityScheduleClasses]
          rw [classifiedTupleSum_succ_succ]
          rw [classifiedAvailableValues_labeledCopyNXClass]
          simp only [nxAnchoredScheduleKernel, finTupleHead_cons,
            Fin.cons_zero, Fin.tail_cons,
            conditionedNXParityChainSumThen]
          apply Finset.sum_congr rfl
          intro x _hx
          rw [classifiedAvailableValues_labeledCopyNXClass]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _hy
          rw [classifiedTupleSum_const_mul]
          rw [ih]
          ring
      | roughPair p =>
          simp only [List.cons_append, nxParityScheduleArity,
            nxParityScheduleClasses]
          rw [classifiedTupleSum_succ_succ]
          rw [classifiedAvailableValues_labeledCopyNXClass]
          simp only [nxAnchoredScheduleKernel, finTupleHead_cons,
            Fin.cons_zero, Fin.tail_cons,
            conditionedNXParityChainSumThen]
          apply Finset.sum_congr rfl
          intro x _hx
          rw [classifiedAvailableValues_labeledCopyNXClass]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _hy
          rw [classifiedTupleSum_const_mul]
          rw [ih]
          ring

/--
The exact two-run identity is invariant under casting the finite tuple
length.  This is the dependent transport used by the paper-length Fubini
formula.
-/
theorem classifiedTupleSum_nxAnchoredScheduleKernel_cast
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (left right : List (NXParityBlock Nm mu))
    (used : Finset (HeppLabeledCopy mu))
    (anchorPoint u : Fin 4 → ℤ)
    (n : ℕ)
    (hArity : nxParityScheduleArity (left ++ right) = n)
    (classes : Fin n → NXClass)
    (hClasses :
      nxParityScheduleClasses (left ++ right) =
        classes ∘ Fin.cast hArity) :
    classifiedTupleSum (labeledCopyNXClass Nm mu) used classes
        (fun f =>
          nxAnchoredScheduleKernel ht hroot Nm mu z hz R
            left right anchorPoint u (f ∘ Fin.cast hArity)) =
      conditionedNXParityChainSumThen ht hroot Nm mu z hz R
        left used u fun usedAfterLeft _leftEndpoint =>
          conditionedNXParityChainSum ht hroot Nm mu z hz R
            right usedAfterLeft anchorPoint := by
  subst n
  simp only [Fin.cast_refl, Function.comp_id] at hClasses ⊢
  rw [← hClasses]
  exact classifiedTupleSum_nxAnchoredScheduleKernel
    ht hroot Nm mu z hz R left right used anchorPoint u

/--
Abstract fixed-fiber bridge.  Once a pointwise scheduled-kernel bound is
supplied, the exact paper Fubini identity and the shared-state CPS recursion
sum it without an overcount or an extra factorial.
-/
theorem sum_arrangementsAtNXWord_le_conditionedNXAnchoredRunsSum
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (left right : List (NXParityBlock Nm mu))
    (hArity :
      nxParityScheduleArity (left ++ right) = paperTailLength mu)
    (hClasses :
      nxParityScheduleClasses (left ++ right) =
        (fun i : Fin (paperTailLength mu) =>
          (x ((paperFinAnchorOutwardEquivWithPhases
            leftPhase rightPhase anchor) i.succ)).1) ∘
          Fin.cast hArity)
    (F : (Fin (totalMultiplicity mu) →
      HeppLabeledCopy mu) → ℝ)
    (hF : ∀
      (b : HeppLabeledCopy mu),
      b ∈ conditionedCopiesAtNX Nm mu ∅ (x anchor).1 →
      ∀ (tail : Fin (paperTailLength mu) →
          HeppLabeledCopy mu),
        ClassTupleAdmissible
          (labeledCopyNXClass Nm mu) {b}
          (fun i : Fin (paperTailLength mu) =>
            (x ((paperFinAnchorOutwardEquivWithPhases
              leftPhase rightPhase anchor) i.succ)).1)
          tail →
        F (fun j =>
          @Fin.cons (paperTailLength mu)
            (fun _ => HeppLabeledCopy mu) b tail
            ((paperFinAnchorOutwardEquivWithPhases
              leftPhase rightPhase anchor).symm j)) ≤
          nxAnchoredScheduleKernel ht hroot Nm mu z hz R
            left right (labeledCopyPoint z b)
            (labeledCopyPoint z b)
            (tail ∘ Fin.cast hArity)) :
    (∑ σ ∈ arrangementsAtNXWord Nm mu x, F σ) ≤
      ∑ b ∈ conditionedCopiesAtNX Nm mu ∅ (x anchor).1,
        conditionedNXAnchoredRunsSum ht hroot Nm mu z hz R
          left right {b} (labeledCopyPoint z b) := by
  rw [
    sum_arrangementsAtNXWord_eq_finAnchorOutward_classifiedTuple
      Nm mu leftPhase rightPhase anchor x F]
  apply Finset.sum_le_sum
  intro b hb
  calc
    classifiedTupleSum
        (labeledCopyNXClass Nm mu) {b}
        (fun i : Fin (paperTailLength mu) =>
          (x ((paperFinAnchorOutwardEquivWithPhases
            leftPhase rightPhase anchor) i.succ)).1)
        (fun tail =>
          F (fun j =>
            @Fin.cons (paperTailLength mu)
              (fun _ => HeppLabeledCopy mu) b tail
              ((paperFinAnchorOutwardEquivWithPhases
                leftPhase rightPhase anchor).symm j))) ≤
      classifiedTupleSum
        (labeledCopyNXClass Nm mu) {b}
        (fun i : Fin (paperTailLength mu) =>
          (x ((paperFinAnchorOutwardEquivWithPhases
            leftPhase rightPhase anchor) i.succ)).1)
        (fun tail =>
          nxAnchoredScheduleKernel ht hroot Nm mu z hz R
            left right (labeledCopyPoint z b)
            (labeledCopyPoint z b)
            (tail ∘ Fin.cast hArity)) := by
      apply classifiedTupleSum_mono
      intro tail htail
      exact hF b hb tail htail
    _ = conditionedNXAnchoredRunsSum ht hroot Nm mu z hz R
          left right {b} (labeledCopyPoint z b) := by
      unfold conditionedNXAnchoredRunsSum
      exact classifiedTupleSum_nxAnchoredScheduleKernel_cast
        ht hroot Nm mu z hz R left right {b}
        (labeledCopyPoint z b) (labeledCopyPoint z b)
        (paperTailLength mu) hArity _ hClasses

/--
Canonical coarse-schedule specialization of the abstract fixed-fiber
bridge.  The caller now supplies only the pointwise kernel comparison; all
length and class-word transports are discharged here.
-/
theorem
    sum_arrangementsAtNXWord_le_finAnchorNXCoarseRunsSum_of_pointwise
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (totalMultiplicity mu)))
    (F : (Fin (totalMultiplicity mu) →
      HeppLabeledCopy mu) → ℝ)
    (hF : ∀
      (b : HeppLabeledCopy mu),
      b ∈ conditionedCopiesAtNX Nm mu ∅ (x anchor).1 →
      ∀ (tail : Fin (paperTailLength mu) →
          HeppLabeledCopy mu),
        ClassTupleAdmissible
          (labeledCopyNXClass Nm mu) {b}
          (fun i : Fin (paperTailLength mu) =>
            (x ((paperFinAnchorOutwardEquivWithPhases
              leftPhase rightPhase anchor) i.succ)).1)
          tail →
        F (paperFinAnchorAssignmentFromTail
          leftPhase rightPhase anchor b tail) ≤
          let runs :=
            finAnchorNXCoarseRunsWithPhases Nm mu
              leftPhase rightPhase anchor x O
          nxAnchoredScheduleKernel ht hroot Nm mu z hz R
            runs.left runs.right
            (labeledCopyPoint z b) (labeledCopyPoint z b)
            (tail ∘ Fin.cast
              (nxParityScheduleArity_finAnchorNXCoarseRunsWithPhases
                Nm mu leftPhase rightPhase anchor x O))) :
    let runs :=
      finAnchorNXCoarseRunsWithPhases Nm mu
        leftPhase rightPhase anchor x O
    (∑ σ ∈ arrangementsAtNXWord Nm mu x, F σ) ≤
      ∑ b ∈ conditionedCopiesAtNX Nm mu ∅ (x anchor).1,
        conditionedNXAnchoredRunsSum ht hroot Nm mu z hz R
          runs.left runs.right {b} (labeledCopyPoint z b) := by
  dsimp only
  let runs :=
    finAnchorNXCoarseRunsWithPhases Nm mu
      leftPhase rightPhase anchor x O
  let hArity :
      nxParityScheduleArity (runs.left ++ runs.right) =
        paperTailLength mu := by
    change nxParityScheduleArity runs.ledger = paperTailLength mu
    exact
      nxParityScheduleArity_finAnchorNXCoarseRunsWithPhases
        Nm mu leftPhase rightPhase anchor x O
  let hClasses :
      nxParityScheduleClasses (runs.left ++ runs.right) =
        (fun i : Fin (paperTailLength mu) =>
          (x ((paperFinAnchorOutwardEquivWithPhases
            leftPhase rightPhase anchor) i.succ)).1) ∘
          Fin.cast hArity := by
    change nxParityScheduleClasses runs.ledger = _
    exact
      nxParityScheduleClasses_finAnchorNXCoarseRunsWithPhases_fun
        Nm mu leftPhase rightPhase anchor x O
  apply sum_arrangementsAtNXWord_le_conditionedNXAnchoredRunsSum
    ht hroot Nm mu z hz R leftPhase rightPhase anchor x
    runs.left runs.right hArity hClasses F
  intro b hb tail htail
  change
    F (paperFinAnchorAssignmentFromTail
        leftPhase rightPhase anchor b tail) ≤
      nxAnchoredScheduleKernel ht hroot Nm mu z hz R
        runs.left runs.right
        (labeledCopyPoint z b) (labeledCopyPoint z b)
        (tail ∘ Fin.cast hArity)
  simpa only [runs] using hF b hb tail htail

end XYCluster

end

end Anderson4D
