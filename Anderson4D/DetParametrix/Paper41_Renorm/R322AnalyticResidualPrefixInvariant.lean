import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticResidualScheduleClosure
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticActiveEdgeLedger

/-!
# Global processed-prefix residual invariant for R-322

The one-step residual Fubini theorem carries an arbitrary outer factor.  To
iterate it honestly, that outer factor must be the complete surviving
integrand on the sparse active carrier, not an unconstrained placeholder.
This module defines that object.

After a processed prefix:

* coordinates range only over active non-endpoint vertices;
* every active left vertex reads its actual sparse successor;
* right-edge slots of the remaining proper extraction steps are replaced by
  their signed difference factors;
* every remaining extraction block carries its complete primitive covariance
  sum; and
* the coupling power is exactly the sum of the remaining block orders.

No unintegrated initial integrand is identified with a post-collapse state.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## A reachable processed prefix and its surviving coordinates -/

/-- Complete data at one genuine processed prefix of the production
schedule. -/
structure R322AnalyticResidualPrefix
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (q : ℕ) (hq : 1 ≤ q) where
  pairing : PartialPairing (Fin (2 * q))
  pairing_mem : pairing ∈ nonSplitPairings q
  state : R322AnalyticEdgeState q hq
  remaining : List (R322ExtractionStep (2 * q))
  schedule_eq :
    r322AnalyticSchedule pairing =
      state.processed ++ remaining
  absorbed :
    R322AnalyticAbsorbedState
      ρ lam ε hq pairing pairing_mem state

namespace R322AnalyticResidualPrefix

section GenericPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {q : ℕ} {hq : 1 ≤ q}
    (res : R322AnalyticResidualPrefix ρ lam ε q hq)

/-- Active vertices which remain genuine spatial variables.  The two global
endpoints are fixed separately to `z` and `0`. -/
def SurvivingCoordinate : Type :=
  {i : Fin (2 * q) //
    i ∈ res.state.active ∧
      0 < i.val ∧ i.val < 2 * q - 1}

noncomputable instance survivingCoordinateFintype :
    Fintype res.SurvivingCoordinate :=
  show
    Fintype
      {i : Fin (2 * q) //
        i ∈ res.state.active ∧
          0 < i.val ∧ i.val < 2 * q - 1}
    from inferInstance

/-- Canonical ambient tuple reconstructed from surviving coordinates.
Coordinates deleted by the processed prefix are set to zero; every residual
factor below is proved/defined to read only active coordinates. -/
def reconstruct
    (z : T4)
    (v : res.SurvivingCoordinate → T4) :
    Fin (2 * q) → T4 :=
  fun i =>
    if hzero : i.val = 0 then z
    else if hlast : i.val = 2 * q - 1 then 0
    else if hactive : i ∈ res.state.active then
      v ⟨i, hactive, by omega, by omega⟩
    else 0

@[simp]
theorem reconstruct_zero
    (z : T4) (v : res.SurvivingCoordinate → T4) :
    res.reconstruct z v
        (⟨0, by omega⟩ : Fin (2 * q)) =
      z := by
  simp [reconstruct]

@[simp]
theorem reconstruct_last
    (z : T4) (v : res.SurvivingCoordinate → T4) :
    res.reconstruct z v
        (⟨2 * q - 1, by omega⟩ : Fin (2 * q)) =
      0 := by
  have hne : 2 * q - 1 ≠ 0 := by
    omega
  simp [reconstruct, hne]

@[simp]
theorem reconstruct_surviving
    (z : T4) (v : res.SurvivingCoordinate → T4)
    (i : res.SurvivingCoordinate) :
    res.reconstruct z v i.1 = v i := by
  unfold reconstruct
  have hzero : i.1.val ≠ 0 :=
    ne_of_gt i.2.2.1
  have hlast : i.1.val ≠ 2 * q - 1 :=
    ne_of_lt i.2.2.2
  rw [dif_neg hzero, dif_neg hlast,
    dif_pos i.2.1]
  apply congrArg v
  apply Subtype.ext
  rfl

theorem reconstruct_eq_zero_of_internal_inactive
    (z : T4) (v : res.SurvivingCoordinate → T4)
    (i : Fin (2 * q))
    (hzero : i.val ≠ 0)
    (hlast : i.val ≠ 2 * q - 1)
    (hinactive : i ∉ res.state.active) :
    res.reconstruct z v i = 0 := by
  unfold reconstruct
  rw [dif_neg hzero, dif_neg hlast,
    dif_neg hinactive]

/-! ## The complete surviving suffix factor -/

/-- The next active vertex to the right of an ambient edge slot. -/
def edgeSuccessor
    (edge : Fin (2 * q - 1)) :
    Fin (2 * q) :=
  r322AnalyticSuccessorVertex
    res.state
    (r322AnalyticEdgeLeftVertex edge)
    (by
      change edge.val < 2 * q - 1
      exact edge.isLt)

/-- Right-endpoint values whose ordinary active edge is replaced by a
remaining signed extraction difference. -/
def remainingRightValues : List ℕ :=
  res.remaining.map fun step => step.1.2.val

/-- One surviving sparse chain factor.  Inactive slots contribute one, and
remaining extraction right edges are reserved for the signed difference
product below. -/
def residualChainEdgeFactor
    (x : Fin (2 * q) → T4)
    (edge : Fin (2 * q - 1)) : ℝ :=
  if r322AnalyticEdgeLeftVertex edge ∈ res.state.active then
    if edge.val ∈ res.remainingRightValues then
      1
    else
      res.state.edges edge
        (x (r322AnalyticEdgeLeftVertex edge) -
          x (res.edgeSuccessor edge))
  else 1

/-- Product of all ordinary sparse-carrier edges still present after the
processed prefix. -/
def residualChainProduct
    (x : Fin (2 * q) → T4) : ℝ :=
  ∏ edge : Fin (2 * q - 1),
    res.residualChainEdgeFactor x edge

/-- Signed difference belonging to one remaining extraction step, read on
the current sparse carrier.  The terminal whole-carrier step has no outgoing
edge and contributes one, exactly as in the closed `J` definition. -/
def residualStepDifference
    (x : Fin (2 * q) → T4)
    (step : R322ExtractionStep (2 * q)) : ℝ :=
  if hguard : step.1.2.val < 2 * q - 1 then
    let edge : Fin (2 * q - 1) :=
      ⟨step.1.2.val, hguard⟩
    let successor :=
      r322AnalyticSuccessorVertex
        res.state step.1.2 hguard
    res.state.edges edge
        (x step.1.2 - x successor) -
      res.state.edges edge
        (x step.1.1 - x successor)
  else 1

/-- Product of every remaining signed extraction difference. -/
def residualDifferenceProduct
    (x : Fin (2 * q) → T4) : ℝ :=
  (res.remaining.map
    (res.residualStepDifference x)).prod

/-- A remaining schedule block is an actual extraction block of the frozen
pairing. -/
def remainingBlockIndex
    (j : Fin res.remaining.length) :
    ExtractionBlockIndex res.pairing := by
  let step := res.remaining.get j
  refine ⟨step.2, ?_⟩
  apply
    (r322AnalyticSchedule_blocks_perm_extractionBlocks
      res.pairing).mem_iff.mp
  exact
    List.mem_map.mpr
      ⟨step,
        by
          rw [res.schedule_eq]
          exact List.mem_append_right _
            (res.remaining.get_mem j),
        rfl⟩

@[simp]
theorem remainingBlockIndex_val
    (j : Fin res.remaining.length) :
    (res.remainingBlockIndex j).1 =
      (res.remaining.get j).2 :=
  rfl

/-- Complete primitive covariance coordinate for every remaining block. -/
def residualPrimitiveProduct
    (ρ : SmoothCutoff) (ε : ℝ)
    (x : Fin (2 * q) → T4) : ℝ :=
  ∏ j : Fin res.remaining.length,
    r322ExtractionBlockPrimitiveSum ρ ε
      res.pairing (res.remainingBlockIndex j) x

/-- Complete post-prefix residual integrand on the sparse carrier. -/
def residualIntegrand
    (ρ : SmoothCutoff) (ε : ℝ)
    (x : Fin (2 * q) → T4) : ℝ :=
  res.residualChainProduct x *
    res.residualDifferenceProduct x *
    res.residualPrimitiveProduct ρ ε x

/-- Exact perturbative order which has not yet been integrated. -/
def remainingOrder : ℕ :=
  (res.remaining.map
    (fun step => residualBlockOrder step.2)).sum

/-- Complete scalar residual value after the processed prefix. -/
def residualValue
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (z : T4) : ℝ :=
  lamEps lam ε ^ (2 * res.remainingOrder) *
    ∫ v : res.SurvivingCoordinate → T4,
      res.residualIntegrand ρ ε
        (res.reconstruct z v)
      ∂Measure.pi fun _ => paperMeasure

/-! ## The exact order ledger -/

theorem processedOrder_add_remainingOrder :
    (res.state.processed.map
        (fun step => residualBlockOrder step.2)).sum +
      res.remainingOrder =
        q := by
  have hsum :=
    sum_r322AnalyticSchedule_blockOrders_of_full
      res.pairing
      (mem_nonSplitPairings.mp res.pairing_mem).1
  rw [res.schedule_eq, List.map_append,
    List.sum_append] at hsum
  exact hsum

/-! ## Proper and terminal transitions of the data object -/

/-- The genuine proper-step context at the head of a nonterminal residual
res. -/
def properStepContext
    (step : R322ExtractionStep (2 * q))
    (suffix : List (R322ExtractionStep (2 * q)))
    (hremaining : res.remaining = step :: suffix)
    (hproper :
      step.1 ≠ r322WholeEndpoint q hq) :
    R322AnalyticProperStepContext q hq where
  state := res.state
  pairing := res.pairing
  pairing_mem := res.pairing_mem
  suffix := suffix
  step := step
  schedule_eq := by
    rw [res.schedule_eq, hremaining]
  proper := hproper

/-- Residual-prefix data after one actual proper state update. -/
def afterProper
    (step : R322ExtractionStep (2 * q))
    (suffix : List (R322ExtractionStep (2 * q)))
    (hremaining : res.remaining = step :: suffix)
    (hproper :
      step.1 ≠ r322WholeEndpoint q hq) :
    R322AnalyticResidualPrefix ρ lam ε q hq :=
  let ctx :=
    res.properStepContext step suffix
      hremaining hproper
  { pairing := res.pairing
    pairing_mem := res.pairing_mem
    state := ctx.nextState ρ lam ε
    remaining := suffix
    schedule_eq := by
      change
        r322AnalyticSchedule res.pairing =
          (res.state.processed ++ [step]) ++ suffix
      simpa [hremaining, List.append_assoc] using
        res.schedule_eq
    absorbed :=
      R322AnalyticAbsorbedState.update
        ctx rfl res.absorbed }

@[simp]
theorem afterProper_remaining
    (step : R322ExtractionStep (2 * q))
    (suffix : List (R322ExtractionStep (2 * q)))
    (hremaining : res.remaining = step :: suffix)
    (hproper :
      step.1 ≠ r322WholeEndpoint q hq) :
    (res.afterProper step suffix
      hremaining hproper).remaining =
        suffix :=
  rfl

@[simp]
theorem afterProper_active
    (step : R322ExtractionStep (2 * q))
    (suffix : List (R322ExtractionStep (2 * q)))
    (hremaining : res.remaining = step :: suffix)
    (hproper :
      step.1 ≠ r322WholeEndpoint q hq) :
    (res.afterProper step suffix
        hremaining hproper).state.active =
      res.state.active \ step.2 := by
  change
    ((res.properStepContext
      step suffix hremaining hproper).nextState
        ρ lam ε).active =
      res.state.active \ step.2
  rw [R322AnalyticProperStepContext.nextState,
    R322AnalyticEdgeState.updateProper_active]
  rfl

/-- A singleton whole-carrier suffix produces the certified terminal context
on exactly the current heterogeneous state. -/
def terminalStepContext
    (terminal : R322ExtractionStep (2 * q))
    (hremaining : res.remaining = [terminal])
    (hterminal :
      terminal.1 = r322WholeEndpoint q hq) :
    R322AnalyticTerminalStepContext q hq where
  state := res.state
  pairing := res.pairing
  pairing_mem := res.pairing_mem
  terminal := terminal
  schedule_eq := by
    rw [res.schedule_eq, hremaining]
  terminal_endpoint := hterminal

end GenericPrefix

/-! ## The first production update in the global residual type -/

/-- The unprocessed production schedule as a residual-prefix object. -/
def initial
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q) :
    R322AnalyticResidualPrefix ρ lam ε q hq where
  pairing := κ
  pairing_mem := hκ
  state := r322InitialAnalyticEdgeState q hq
  remaining := r322AnalyticSchedule κ
  schedule_eq := by
    simp [r322InitialAnalyticEdgeState]
  absorbed := R322AnalyticAbsorbedState.initial

/-- The first proper production absorption, expressed in the global residual
data type. -/
def afterInitialProper
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    R322AnalyticResidualPrefix ρ lam ε q hq :=
  (initial ρ lam ε hq κ hκ).afterProper
    head tail hschedule hproper

@[simp]
theorem afterInitialProper_remaining
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    (afterInitialProper
      ρ lam ε hq κ hκ head tail hschedule hproper).remaining =
        tail :=
  rfl

@[simp]
theorem afterInitialProper_state
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    (afterInitialProper
      ρ lam ε hq κ hκ head tail hschedule hproper).state =
        (r322InitialProperStepContext
          hq κ hκ head tail hschedule hproper).nextState
            ρ lam ε :=
  rfl

/-- The surviving carrier after the first production absorption is exactly
the complement of the first concrete block. -/
theorem afterInitialProper_active
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    (afterInitialProper
        ρ lam ε hq κ hκ head tail hschedule hproper).state.active =
      Finset.univ \ head.2 := by
  let ctx :=
    r322InitialProperStepContext
      hq κ hκ head tail hschedule hproper
  change (ctx.nextState ρ lam ε).active =
    Finset.univ \ head.2
  rw [
    R322AnalyticProperStepContext.nextState,
    R322AnalyticEdgeState.updateProper_active]
  rfl

/-- Complementary ambient internal coordinates used by the first-step
Fubini theorem. -/
abbrev InitialComplementCoordinate
    {q : ℕ} (hq : 1 ≤ q)
    (head : R322ExtractionStep (2 * q)) : Type :=
  {i : Fin (2 * q - 2) //
    ¬r322SelectedFinPredicate
      (r322InternalCoordinatesOfBlock q hq head.2) i}

/-- Explicit carrier form used to keep the ambient order visible during the
dependent first-prefix reindex. -/
abbrev AfterInitialSurvivingCoordinate
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) : Type :=
  {i : Fin (2 * q) //
    i ∈
        (afterInitialProper
          ρ lam ε hq κ hκ head tail hschedule hproper).state.active ∧
      0 < i.val ∧ i.val < 2 * q - 1}

@[simp]
theorem primitiveInternalIdx_val_residual
    (q : ℕ) (hq : 1 ≤ q)
    (i : Fin (2 * q - 2)) :
    (primitiveInternalIdx q hq i).val = i.val + 1 := by
  rfl

/-- The first-step complementary coordinates are precisely the surviving
active internal vertices after the first block has been removed. -/
def initialComplementEquivSurviving
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    InitialComplementCoordinate hq head ≃
      AfterInitialSurvivingCoordinate
        ρ lam ε hq κ hκ head tail hschedule hproper where
  toFun j := by
    refine ⟨primitiveInternalIdx q hq j.1, ?_, ?_, ?_⟩
    · rw [afterInitialProper_active
        ρ lam ε hq κ hκ head tail hschedule hproper]
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hj
      apply j.2
      rw [r322SelectedFinPredicate_iff,
        mem_r322InternalCoordinatesOfBlock]
      exact hj
    · rw [primitiveInternalIdx_val_residual]
      omega
    · have hj := j.1.isLt
      rw [primitiveInternalIdx_val_residual]
      omega
  invFun i := by
    let j : Fin (2 * q - 2) :=
      ⟨i.1.val - 1, by
        have hi := i.2.2.2
        omega⟩
    refine ⟨j, ?_⟩
    intro hj
    have hjBlock :
        primitiveInternalIdx q hq j ∈ head.2 := by
      exact
        (mem_r322InternalCoordinatesOfBlock
          q hq head.2 j).mp
          ((r322SelectedFinPredicate_iff
            (r322InternalCoordinatesOfBlock
              q hq head.2) j).mp hj)
    have hji :
        primitiveInternalIdx q hq j = i.1 := by
      apply Fin.ext
      rw [primitiveInternalIdx_val_residual]
      dsimp only [j]
      omega
    rw [hji] at hjBlock
    have hiActive :
        i.1 ∈ Finset.univ \ head.2 := by
      rw [← afterInitialProper_active
        ρ lam ε hq κ hκ head tail hschedule hproper]
      exact i.2.1
    exact (Finset.mem_sdiff.mp hiActive).2 hjBlock
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    change
      (primitiveInternalIdx q hq j.1).val - 1 =
        j.1.val
    rw [primitiveInternalIdx_val_residual]
    omega
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    change
      (primitiveInternalIdx q hq
          ⟨i.1.val - 1, by
            have hi := i.2.2.2
            omega⟩).val =
        i.1.val
    rw [primitiveInternalIdx_val_residual]
    change (i.1.val - 1) + 1 = i.1.val
    omega

/-- Coordinate-function reindex induced by
`initialComplementEquivSurviving`. -/
def initialComplementPiMeasurableEquiv
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    (InitialComplementCoordinate hq head → T4) ≃ᵐ
      (AfterInitialSurvivingCoordinate
          ρ lam ε hq κ hκ head tail hschedule hproper →
        T4) :=
  MeasurableEquiv.piCongrLeft
    (fun _ :
      AfterInitialSurvivingCoordinate
        ρ lam ε hq κ hκ head tail hschedule hproper => T4)
    (initialComplementEquivSurviving
      ρ lam ε hq κ hκ head tail hschedule hproper)

/-- The concrete first-prefix reindex preserves the exact product Haar
measure. -/
theorem measurePreserving_initialComplementPiMeasurableEquiv
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    MeasurePreserving
      (initialComplementPiMeasurableEquiv
        ρ lam ε hq κ hκ head tail hschedule hproper)
      (Measure.pi fun _ :
        InitialComplementCoordinate hq head =>
          paperMeasure)
      (Measure.pi fun _ :
        AfterInitialSurvivingCoordinate
          ρ lam ε hq κ hκ head tail hschedule hproper =>
            paperMeasure) := by
  simpa only [initialComplementPiMeasurableEquiv] using
    (measurePreserving_piCongrLeft
      (fun _ :
        AfterInitialSurvivingCoordinate
          ρ lam ε hq κ hκ head tail hschedule hproper =>
            paperMeasure)
      (initialComplementEquivSurviving
        ρ lam ε hq κ hκ head tail hschedule hproper))

/-- The concrete first-prefix function reindex reads the same coordinate at
the corresponding surviving ambient vertex. -/
@[simp]
theorem initialComplementPiMeasurableEquiv_apply
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (vC : InitialComplementCoordinate hq head → T4)
    (j : InitialComplementCoordinate hq head) :
    initialComplementPiMeasurableEquiv
        ρ lam ε hq κ hκ head tail hschedule hproper vC
        (initialComplementEquivSurviving
          ρ lam ε hq κ hκ head tail hschedule hproper j) =
      vC j := by
  exact
    MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ :
        AfterInitialSurvivingCoordinate
          ρ lam ε hq κ hκ head tail hschedule hproper => T4)
      (initialComplementEquivSurviving
        ρ lam ε hq κ hκ head tail hschedule hproper)
      vC j

/-- The proper-head reference tuple reads a complementary internal
coordinate literally. -/
theorem properHeadReferenceTuple_internal_complement
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC : InitialComplementCoordinate hq head → T4)
    (j : InitialComplementCoordinate hq head) :
    r322AnalyticProperHeadReferenceTuple
        hq κ hκ head tail hschedule hproper z vC
        (primitiveInternalIdx q hq j.1) =
      vC j := by
  unfold r322AnalyticProperHeadReferenceTuple
    r322AnalyticProperHeadReconstruct
  rw [primitiveAssemble_internal]
  exact
    r322MergeSelectedFinCoordinates_apply_not_mem
      _ _ _ j.1 j.2

/-- Every deleted first-block coordinate is zero in the fixed proper-head
reference tuple. -/
theorem properHeadReferenceTuple_eq_zero_of_mem
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC : InitialComplementCoordinate hq head → T4)
    (i : Fin (2 * q)) (hi : i ∈ head.2) :
    r322AnalyticProperHeadReferenceTuple
        hq κ hκ head tail hschedule hproper z vC i =
      0 := by
  let ctx :=
    r322InitialProperStepContext
      hq κ hκ head tail hschedule hproper
  let base :=
    r322AnalyticProperHeadReferenceTuple
      hq κ hκ head tail hschedule hproper z vC
  have hreconstruct :=
    R322InitialProperStepContext.reconstructBlockTuple_reference_eq
      hq κ hκ head tail hschedule hproper z vC
      (fun _ => 0)
  have hiEq := congrFun hreconstruct i
  change ctx.reconstructBlockTuple base (fun _ => 0) i =
    base i at hiEq
  unfold R322AnalyticProperStepContext.reconstructBlockTuple at hiEq
  dsimp only [ctx, r322InitialProperStepContext] at hiEq
  rw [dif_pos hi] at hiEq
  exact hiEq.symm

/-- Under the concrete finite-coordinate reindex, the global residual
reconstruction is exactly the first-step reference tuple. -/
theorem afterInitialProper_reconstruct_reindex
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC : InitialComplementCoordinate hq head → T4) :
    (afterInitialProper
        ρ lam ε hq κ hκ head tail hschedule hproper).reconstruct z
        (initialComplementPiMeasurableEquiv
          ρ lam ε hq κ hκ head tail hschedule hproper vC) =
      r322AnalyticProperHeadReferenceTuple
        hq κ hκ head tail hschedule hproper z vC := by
  let post :=
    afterInitialProper
      ρ lam ε hq κ hκ head tail hschedule hproper
  let e :=
    initialComplementEquivSurviving
      ρ lam ε hq κ hκ head tail hschedule hproper
  let v :=
    initialComplementPiMeasurableEquiv
      ρ lam ε hq κ hκ head tail hschedule hproper vC
  funext i
  by_cases hzero : i.val = 0
  · have hi :
        i = (⟨0, by omega⟩ : Fin (2 * q)) :=
      Fin.ext hzero
    rw [hi]
    rw [post.reconstruct_zero]
    unfold r322AnalyticProperHeadReferenceTuple
      r322AnalyticProperHeadReconstruct
    rw [primitiveAssemble_zero]
  by_cases hlast : i.val = 2 * q - 1
  · have hi :
        i = (⟨2 * q - 1, by omega⟩ : Fin (2 * q)) :=
      Fin.ext hlast
    rw [hi]
    rw [post.reconstruct_last]
    unfold r322AnalyticProperHeadReferenceTuple
      r322AnalyticProperHeadReconstruct
    have hiLast :
        (⟨2 * q - 1, by omega⟩ : Fin (2 * q)) =
          primitiveLast q hq := by
      apply Fin.ext
      rfl
    rw [hiLast, primitiveAssemble_last]
  by_cases hactive : i ∈ post.state.active
  · let si : post.SurvivingCoordinate :=
      ⟨i, hactive, by omega, by omega⟩
    let j : InitialComplementCoordinate hq head :=
      e.symm si
    have hej : e j = si :=
      e.apply_symm_apply si
    have hambient :
        primitiveInternalIdx q hq j.1 = i := by
      exact congrArg Subtype.val hej
    unfold R322AnalyticResidualPrefix.reconstruct
    rw [dif_neg hzero, dif_neg hlast, dif_pos hactive]
    change v si =
      r322AnalyticProperHeadReferenceTuple
        hq κ hκ head tail hschedule hproper z vC i
    rw [← hambient]
    have hv :
        v (e j) = vC j :=
      initialComplementPiMeasurableEquiv_apply
        ρ lam ε hq κ hκ head tail hschedule hproper vC j
    rw [hej] at hv
    rw [hv]
    exact
      (properHeadReferenceTuple_internal_complement
        hq κ hκ head tail hschedule hproper z vC j).symm
  · have hiHead : i ∈ head.2 := by
      have hcarrier :
          post.state.active = Finset.univ \ head.2 :=
        afterInitialProper_active
          ρ lam ε hq κ hκ head tail hschedule hproper
      by_contra hi
      apply hactive
      rw [hcarrier]
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, hi⟩
    unfold R322AnalyticResidualPrefix.reconstruct
    rw [dif_neg hzero, dif_neg hlast, dif_neg hactive]
    exact
      (properHeadReferenceTuple_eq_zero_of_mem
        hq κ hκ head tail hschedule hproper z vC i hiHead).symm

/-! ## Exact first-prefix factor ledger -/

/-- If the ordinary adjacent right vertex is active, it is already the
least sparse successor. -/
theorem edgeSuccessor_eq_adjacent_of_right_mem_active
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {q : ℕ} {hq : 1 ≤ q}
    (res : R322AnalyticResidualPrefix ρ lam ε q hq)
    (edge : Fin (2 * q - 1))
    (hright :
      r322JChainEdgeRight edge ∈ res.state.active) :
    res.edgeSuccessor edge =
      r322JChainEdgeRight edge := by
  have hcandidate :
      r322JChainEdgeRight edge ∈
        r322AnalyticSuccessorCandidates
          res.state
          (r322AnalyticEdgeLeftVertex edge) := by
    apply Finset.mem_filter.mpr
    refine ⟨hright, ?_⟩
    change edge.val < edge.val + 1
    omega
  have hupper :
      res.edgeSuccessor edge ≤
        r322JChainEdgeRight edge := by
    unfold edgeSuccessor r322AnalyticSuccessorVertex
    exact Finset.min'_le _
      (r322JChainEdgeRight edge) hcandidate
  have hlower :
      r322AnalyticEdgeLeftVertex edge <
        res.edgeSuccessor edge :=
    r322AnalyticSuccessorVertex_gt
      res.state
      (r322AnalyticEdgeLeftVertex edge)
      (by
        change edge.val < 2 * q - 1
        exact edge.isLt)
  apply Fin.ext
  change (res.edgeSuccessor edge).val =
    edge.val + 1
  change (res.edgeSuccessor edge).val ≤
    edge.val + 1 at hupper
  change edge.val < (res.edgeSuccessor edge).val at hlower
  omega

/-- The updated predecessor slot skips exactly the deleted first block. -/
theorem afterInitialProper_predecessor_successor_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    let ctx :=
      r322InitialProperStepContext
        hq κ hκ head tail hschedule hproper
    let post :=
      afterInitialProper
        ρ lam ε hq κ hκ head tail hschedule hproper
    post.edgeSuccessor ctx.predecessorEdge =
      ctx.successorVertex := by
  dsimp only
  let ctx :=
    r322InitialProperStepContext
      hq κ hκ head tail hschedule hproper
  let post :=
    afterInitialProper
      ρ lam ε hq κ hκ head tail hschedule hproper
  have hheadMem :
      head ∈ r322AnalyticSchedule κ := by
    rw [hschedule]
    simp
  have hheadLt :
      head.1.1 < head.1.2 :=
    extract_mem_fst_lt_snd κ head.1
      (r322AnalyticSchedule_endpoint_mem_extract
        κ hheadMem)
  have htargetNot :
      ctx.successorVertex ∉ head.2 :=
    ctx.successorVertex_not_mem_step
  have htargetActive :
      ctx.successorVertex ∈ post.state.active := by
    rw [afterInitialProper_active
      ρ lam ε hq κ hκ head tail hschedule hproper]
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, htargetNot⟩
  have hpredLtTarget :
      r322AnalyticEdgeLeftVertex ctx.predecessorEdge <
        ctx.successorVertex := by
    rw [
      R322AnalyticProperStepContext.predecessorEdge,
      r322AnalyticEdgeLeftVertex_predecessorEdge]
    exact
      (r322AnalyticPredecessorVertex_lt_left
          ctx.state ctx.step ctx.bounds.1).trans
        (hheadLt.trans ctx.stepRight_lt_successorVertex)
  have hcandidate :
      ctx.successorVertex ∈
        r322AnalyticSuccessorCandidates
          post.state
          (r322AnalyticEdgeLeftVertex
            ctx.predecessorEdge) :=
    Finset.mem_filter.mpr
      ⟨htargetActive, hpredLtTarget⟩
  have hupper :
      post.edgeSuccessor ctx.predecessorEdge ≤
        ctx.successorVertex := by
    unfold edgeSuccessor r322AnalyticSuccessorVertex
    exact Finset.min'_le _ ctx.successorVertex hcandidate
  have hactualActive :
      post.edgeSuccessor ctx.predecessorEdge ∈
        post.state.active :=
    r322AnalyticSuccessorVertex_mem_active
      post.state
      (r322AnalyticEdgeLeftVertex
        ctx.predecessorEdge)
      (by
        change ctx.predecessorEdge.val < 2 * q - 1
        exact ctx.predecessorEdge.isLt)
  have hactualNot :
      post.edgeSuccessor ctx.predecessorEdge ∉ head.2 := by
    have hparts :
        post.edgeSuccessor ctx.predecessorEdge ∈
          Finset.univ \ head.2 := by
      rw [← afterInitialProper_active
        ρ lam ε hq κ hκ head tail hschedule hproper]
      exact hactualActive
    exact (Finset.mem_sdiff.mp hparts).2
  have hstrict :
      r322AnalyticEdgeLeftVertex ctx.predecessorEdge <
        post.edgeSuccessor ctx.predecessorEdge :=
    r322AnalyticSuccessorVertex_gt
      post.state
      (r322AnalyticEdgeLeftVertex
        ctx.predecessorEdge)
      (by
        change ctx.predecessorEdge.val < 2 * q - 1
        exact ctx.predecessorEdge.isLt)
  have hlower :
      ctx.successorVertex ≤
        post.edgeSuccessor ctx.predecessorEdge := by
    by_contra hnot
    apply hactualNot
    rw [
      r322AnalyticSchedule_head_block_eq_Icc
        κ head tail hschedule]
    apply Finset.mem_Icc.mpr
    have hpredEdgeEq :=
      R322InitialProperStepContext.predecessorEdge_eq
        hq κ hκ head tail hschedule hproper
    have hpredEdgeVal := congrArg Fin.val hpredEdgeEq
    have hsuccEq :=
      R322InitialProperStepContext.successorVertex_eq
        hq κ hκ head tail hschedule hproper
    have hsuccVal := congrArg Fin.val hsuccEq
    have hactualLt :
        post.edgeSuccessor ctx.predecessorEdge <
          ctx.successorVertex :=
      lt_of_not_ge hnot
    constructor
    · change head.1.1.val ≤
        (post.edgeSuccessor
          ctx.predecessorEdge).val
      change
        ctx.predecessorEdge.val <
            (post.edgeSuccessor
              ctx.predecessorEdge).val at hstrict
      change ctx.predecessorEdge.val =
        head.1.1.val - 1 at hpredEdgeVal
      omega
    · change
        (post.edgeSuccessor
          ctx.predecessorEdge).val ≤
            head.1.2.val
      change
        (post.edgeSuccessor
          ctx.predecessorEdge).val <
            ctx.successorVertex.val at hactualLt
      change ctx.successorVertex.val =
        head.1.2.val + 1 at hsuccVal
      omega
  exact le_antisymm hupper hlower

/-- The primitive-block part of the global residual is literally the tail
primitive product from the first-step pointwise factorization. -/
theorem afterInitialProper_residualPrimitiveProduct_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (x : Fin (2 * q) → T4) :
    (afterInitialProper
        ρ lam ε hq κ hκ head tail hschedule hproper).residualPrimitiveProduct
        ρ ε x =
      ∏ j : Fin tail.length,
        r322ExtractionBlockPrimitiveSum ρ ε κ
          (r322AnalyticTailBlockIndex κ hschedule j) x := by
  apply Finset.prod_congr rfl
  intro j _hj
  apply congrArg
    (fun B : ExtractionBlockIndex κ =>
      r322ExtractionBlockPrimitiveSum ρ ε κ B x)
  apply Subtype.ext
  change (tail.get j).2 =
    (r322AnalyticTailBlockIndex κ hschedule j).1
  exact (r322AnalyticTailBlockIndex_val κ hschedule j).symm

/-- Every later right endpoint lies strictly beyond the first one. -/
theorem afterInitialProper_headRight_lt_tailRight
    {q : ℕ}
    (κ : PartialPairing (Fin (2 * q)))
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (step : R322ExtractionStep (2 * q))
    (hstep : step ∈ tail) :
    head.1.2 < step.1.2 := by
  have hp :=
    r322AnalyticSchedule_pairwise_right_lt κ
  rw [hschedule] at hp
  exact (List.pairwise_cons.mp hp).1 step hstep

/-- After removing the first block, the sparse successor of every later
right endpoint is still its ordinary adjacent ambient vertex. -/
theorem afterInitialProper_tail_successor_eq_adjacent
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (step : R322ExtractionStep (2 * q))
    (hstep : step ∈ tail)
    (hguard : step.1.2.val < 2 * q - 1) :
    r322AnalyticSuccessorVertex
        (afterInitialProper
          ρ lam ε hq κ hκ head tail hschedule hproper).state
        step.1.2 hguard =
      (⟨step.1.2.val + 1, by omega⟩ : Fin (2 * q)) := by
  let post :=
    afterInitialProper
      ρ lam ε hq κ hκ head tail hschedule hproper
  let adjacent : Fin (2 * q) :=
    ⟨step.1.2.val + 1, by omega⟩
  have hright :
      head.1.2 < step.1.2 :=
    afterInitialProper_headRight_lt_tailRight
      κ head tail hschedule step hstep
  have hadjNot : adjacent ∉ head.2 := by
    rw [
      r322AnalyticSchedule_head_block_eq_Icc
        κ head tail hschedule]
    intro hadj
    have hu := (Finset.mem_Icc.mp hadj).2
    change adjacent.val ≤ head.1.2.val at hu
    change head.1.2.val < step.1.2.val at hright
    dsimp only [adjacent] at hu
    omega
  have hadjActive : adjacent ∈ post.state.active := by
    rw [afterInitialProper_active
      ρ lam ε hq κ hκ head tail hschedule hproper]
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, hadjNot⟩
  have hadjCandidate :
      adjacent ∈
        r322AnalyticSuccessorCandidates
          post.state step.1.2 := by
    apply Finset.mem_filter.mpr
    refine ⟨hadjActive, ?_⟩
    change step.1.2.val < adjacent.val
    dsimp only [adjacent]
    omega
  have hupper :
      r322AnalyticSuccessorVertex
          post.state step.1.2 hguard ≤ adjacent := by
    unfold r322AnalyticSuccessorVertex
    exact Finset.min'_le _ adjacent hadjCandidate
  have hlower :
      step.1.2 <
        r322AnalyticSuccessorVertex
          post.state step.1.2 hguard :=
    r322AnalyticSuccessorVertex_gt
      post.state step.1.2 hguard
  apply Fin.ext
  change
    (r322AnalyticSuccessorVertex
      post.state step.1.2 hguard).val =
      step.1.2.val + 1
  change
    (r322AnalyticSuccessorVertex
      post.state step.1.2 hguard).val ≤
      adjacent.val at hupper
  change
    step.1.2.val <
      (r322AnalyticSuccessorVertex
        post.state step.1.2 hguard).val at hlower
  dsimp only [adjacent] at hupper
  omega

/-- The outgoing edge of every tail step is untouched by the first update
and therefore remains the free Green kernel. -/
theorem afterInitialProper_tail_edge_eq_greenFn
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (step : R322ExtractionStep (2 * q))
    (hstep : step ∈ tail)
    (hguard : step.1.2.val < 2 * q - 1) :
    (afterInitialProper
        ρ lam ε hq κ hκ head tail hschedule hproper).state.edges
        ⟨step.1.2.val, hguard⟩ =
      greenFn := by
  let ctx :=
    r322InitialProperStepContext
      hq κ hκ head tail hschedule hproper
  let edge : Fin (2 * q - 1) :=
    ⟨step.1.2.val, hguard⟩
  have hright :
      head.1.2 <
        r322AnalyticEdgeLeftVertex edge := by
    change head.1.2.val < step.1.2.val
    exact
      afterInitialProper_headRight_lt_tailRight
        κ head tail hschedule step hstep
  change (ctx.nextState ρ lam ε).edges edge = greenFn
  rw [R322AnalyticProperStepContext.nextState,
    R322AnalyticEdgeState.updateProper_edges_eq_of_right_lt
      ctx.state ctx.pairing ctx.pairing_mem ctx.suffix
      ctx.step ctx.schedule_eq ctx.proper
      (primitiveKernelDiff ρ lam ε
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder ctx.internalEdges)
      edge hright]
  rfl

/-- The global sparse signed-difference product after the first update is
exactly the old all-Green tail difference product. -/
theorem afterInitialProper_residualDifferenceProduct_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (x : Fin (2 * q) → T4) :
    (afterInitialProper
        ρ lam ε hq κ hκ head tail hschedule hproper).residualDifferenceProduct
        x =
      r322AnalyticDiffProductWith
        (fun _ : Fin (2 * q - 1) => greenFn) tail x := by
  unfold residualDifferenceProduct
    r322AnalyticDiffProductWith
  apply congrArg List.prod
  apply List.map_congr_left
  intro step hstep
  change step ∈ tail at hstep
  unfold residualStepDifference diffFactorJWith
  by_cases hguard :
      step.1.2.val < 2 * q - 1
  · have hguard' :
        step.1.2.val + 1 < 2 * q := by
      omega
    simp only [hguard, dite_true, hguard']
    rw [
      afterInitialProper_tail_edge_eq_greenFn
        ρ lam ε hq κ hκ head tail hschedule hproper
        step hstep hguard,
      afterInitialProper_tail_successor_eq_adjacent
        ρ lam ε hq κ hκ head tail hschedule hproper
        step hstep hguard]
  · have hguard' :
        ¬step.1.2.val + 1 < 2 * q := by
      omega
    simp only [hguard, hguard', dite_false]

/-- The predecessor contribution in the first post-update sparse chain is
the newly collapsed heterogeneous edge, read against the actual sparse
successor. -/
theorem afterInitialProper_residualChainEdgeFactor_predecessor
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (x : Fin (2 * q) → T4) :
    let ctx :=
      r322InitialProperStepContext
        hq κ hκ head tail hschedule hproper
    let post :=
      afterInitialProper
        ρ lam ε hq κ hκ head tail hschedule hproper
    post.residualChainEdgeFactor x ctx.predecessorEdge =
      post.state.edges ctx.predecessorEdge
        (x (r322AnalyticEdgeLeftVertex
              ctx.predecessorEdge) -
          x ctx.successorVertex) := by
  dsimp only
  let ctx :=
    r322InitialProperStepContext
      hq κ hκ head tail hschedule hproper
  let post :=
    afterInitialProper
      ρ lam ε hq κ hκ head tail hschedule hproper
  have hleftActive :
      r322AnalyticEdgeLeftVertex ctx.predecessorEdge ∈
        post.state.active := by
    rw [afterInitialProper_active
      ρ lam ε hq κ hκ head tail hschedule hproper]
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [
      R322AnalyticProperStepContext.predecessorEdge,
      r322AnalyticEdgeLeftVertex_predecessorEdge]
    exact ctx.predecessorVertex_not_mem_step
  have hnotTail :
      ctx.predecessorEdge.val ∉
        post.remainingRightValues := by
    unfold remainingRightValues
    change
      ctx.predecessorEdge.val ∉
        tail.map (fun step => step.1.2.val)
    intro hmem
    rcases List.mem_map.mp hmem with
      ⟨step, hstep, hval⟩
    have hright :
        head.1.2 < step.1.2 :=
      afterInitialProper_headRight_lt_tailRight
        κ head tail hschedule step hstep
    have hpredEdgeEq :=
      R322InitialProperStepContext.predecessorEdge_eq
        hq κ hκ head tail hschedule hproper
    have hpredEdgeVal := congrArg Fin.val hpredEdgeEq
    change ctx.predecessorEdge.val =
      head.1.1.val - 1 at hpredEdgeVal
    change step.1.2.val =
      ctx.predecessorEdge.val at hval
    have hheadMem :
        head ∈ r322AnalyticSchedule κ := by
      rw [hschedule]
      simp
    have hheadLt :
        head.1.1 < head.1.2 :=
      extract_mem_fst_lt_snd κ head.1
        (r322AnalyticSchedule_endpoint_mem_extract
          κ hheadMem)
    omega
  unfold residualChainEdgeFactor
  rw [if_pos hleftActive, if_neg hnotTail,
    afterInitialProper_predecessor_successor_eq
      ρ lam ε hq κ hκ head tail hschedule hproper]

/-- Away from the collapsed predecessor slot, the post-update sparse-chain
factor is exactly the corresponding exterior factor from the old head
split. -/
theorem afterInitialProper_residualChainEdgeFactor_eq_of_ne
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (x : Fin (2 * q) → T4)
    (edge : Fin (2 * q - 1))
    (hne :
      edge ≠
        (r322InitialProperStepContext
          hq κ hκ head tail hschedule hproper).predecessorEdge) :
    let post :=
      afterInitialProper
        ρ lam ε hq κ hκ head tail hschedule hproper
    post.residualChainEdgeFactor x edge =
      if R322ChainEdgeOutside head.2 edge then
        r322AnalyticChainEdgeFactorWith
          (fun _ : Fin (2 * q - 1) => greenFn)
          κ x edge
      else 1 := by
  dsimp only
  let ctx :=
    r322InitialProperStepContext
      hq κ hκ head tail hschedule hproper
  let post :=
    afterInitialProper
      ρ lam ε hq κ hκ head tail hschedule hproper
  have hheadMem :
      head ∈ r322AnalyticSchedule κ := by
    rw [hschedule]
    simp
  have hheadLt :
      head.1.1 < head.1.2 :=
    extract_mem_fst_lt_snd κ head.1
      (r322AnalyticSchedule_endpoint_mem_extract
        κ hheadMem)
  by_cases hleft :
      r322AnalyticEdgeLeftVertex edge ∈
        post.state.active
  · by_cases htail :
        edge.val ∈ post.remainingRightValues
    · have htailList :
          edge.val ∈
            tail.map (fun step => step.1.2.val) := by
        have hremaining : post.remaining = tail := rfl
        simpa only [remainingRightValues,
          hremaining] using htail
      have hscheduleEdge :
          edge.val ∈
            (r322AnalyticSchedule κ).map
              (fun step => step.1.2.val) := by
        rw [hschedule]
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr htailList
      unfold residualChainEdgeFactor
      rw [if_pos hleft, if_pos htail]
      by_cases hout :
          R322ChainEdgeOutside head.2 edge
      · rw [if_pos hout]
        unfold r322AnalyticChainEdgeFactorWith
        rw [if_pos hscheduleEdge]
      · rw [if_neg hout]
    · have htailList :
          edge.val ∉
            tail.map (fun step => step.1.2.val) := by
        have hremaining : post.remaining = tail := rfl
        simpa only [remainingRightValues,
          hremaining] using htail
      have hleftNot :
          r322AnalyticEdgeLeftVertex edge ∉ head.2 := by
        have hparts :
            r322AnalyticEdgeLeftVertex edge ∈
              Finset.univ \ head.2 := by
          rw [← afterInitialProper_active
            ρ lam ε hq κ hκ head tail hschedule hproper]
          exact hleft
        exact (Finset.mem_sdiff.mp hparts).2
      have hrightNot :
          r322JChainEdgeRight edge ∉ head.2 := by
        intro hright
        have hrightBounds :
            head.1.1 ≤ r322JChainEdgeRight edge ∧
              r322JChainEdgeRight edge ≤ head.1.2 := by
          rw [← Finset.mem_Icc]
          rw [←
            r322AnalyticSchedule_head_block_eq_Icc
              κ head tail hschedule]
          exact hright
        have hleftNotBounds :
            ¬(head.1.1 ≤
                r322AnalyticEdgeLeftVertex edge ∧
              r322AnalyticEdgeLeftVertex edge ≤
                head.1.2) := by
          intro hb
          apply hleftNot
          rw [
            r322AnalyticSchedule_head_block_eq_Icc
              κ head tail hschedule]
          exact Finset.mem_Icc.mpr hb
        have hpredEdgeEq :=
          R322InitialProperStepContext.predecessorEdge_eq
            hq κ hκ head tail hschedule hproper
        have hpredEdgeVal :=
          congrArg Fin.val hpredEdgeEq
        have hedgeEq : edge = ctx.predecessorEdge := by
          apply Fin.ext
          change ctx.predecessorEdge.val =
            head.1.1.val - 1 at hpredEdgeVal
          change
            head.1.1.val ≤ edge.val + 1 ∧
              edge.val + 1 ≤ head.1.2.val at hrightBounds
          change
            ¬(head.1.1.val ≤ edge.val ∧
              edge.val ≤ head.1.2.val) at hleftNotBounds
          omega
        exact hne hedgeEq
      have hrightActive :
          r322JChainEdgeRight edge ∈
            post.state.active := by
        rw [afterInitialProper_active
          ρ lam ε hq κ hκ head tail hschedule hproper]
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, hrightNot⟩
      have hout :
          R322ChainEdgeOutside head.2 edge :=
        ⟨hleftNot, hrightNot⟩
      have hnotSchedule :
          edge.val ∉
            (r322AnalyticSchedule κ).map
              (fun step => step.1.2.val) := by
        rw [hschedule]
        simp only [List.map_cons, List.mem_cons]
        intro hmem
        rcases hmem with hhead | hlater
        · apply hleftNot
          rw [
            r322AnalyticSchedule_head_block_eq_Icc
              κ head tail hschedule]
          apply Finset.mem_Icc.mpr
          change
            head.1.1.val ≤ edge.val ∧
              edge.val ≤ head.1.2.val
          change edge.val = head.1.2.val at hhead
          omega
        · exact htailList hlater
      have hedgeGreen :
          post.state.edges edge = greenFn := by
        change
          (ctx.nextState ρ lam ε).edges edge =
            greenFn
        rw [ctx.nextState_edges_eq_of_ne
          ρ lam ε edge hne]
        rfl
      have hsuccessor :
          post.edgeSuccessor edge =
            r322JChainEdgeRight edge :=
        edgeSuccessor_eq_adjacent_of_right_mem_active
          post edge hrightActive
      unfold residualChainEdgeFactor
      rw [if_pos hleft, if_neg htail,
        hsuccessor, hedgeGreen, if_pos hout]
      unfold r322AnalyticChainEdgeFactorWith
        jChainEdgeWith
      rw [if_neg hnotSchedule]
      apply congrArg greenFn
      congr 1
  · have hleftHead :
        r322AnalyticEdgeLeftVertex edge ∈ head.2 := by
      by_contra hnot
      apply hleft
      rw [afterInitialProper_active
        ρ lam ε hq κ hκ head tail hschedule hproper]
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, hnot⟩
    have hout :
        ¬R322ChainEdgeOutside head.2 edge :=
      fun he => he.1 hleftHead
    unfold residualChainEdgeFactor
    rw [if_neg hleft, if_neg hout]

/-- Exact chain ledger after the first absorption: the new predecessor edge
is pulled out once, and every other slot is the old exterior head-chain
factor. -/
theorem afterInitialProper_residualChainProduct_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (x : Fin (2 * q) → T4) :
    let ctx :=
      r322InitialProperStepContext
        hq κ hκ head tail hschedule hproper
    let post :=
      afterInitialProper
        ρ lam ε hq κ hκ head tail hschedule hproper
    post.residualChainProduct x =
      post.state.edges ctx.predecessorEdge
          (x (r322AnalyticEdgeLeftVertex
                ctx.predecessorEdge) -
            x ctx.successorVertex) *
        r322AnalyticHeadOuterChainProductWith
          (fun _ : Fin (2 * q - 1) => greenFn)
          κ head x := by
  dsimp only
  let ctx :=
    r322InitialProperStepContext
      hq κ hκ head tail hschedule hproper
  let post :=
    afterInitialProper
      ρ lam ε hq κ hκ head tail hschedule hproper
  let oldFactor : Fin (2 * q - 1) → ℝ :=
    fun edge =>
      if R322ChainEdgeOutside head.2 edge then
        r322AnalyticChainEdgeFactorWith
          (fun _ : Fin (2 * q - 1) => greenFn)
          κ x edge
      else 1
  have hpredOld :
      oldFactor ctx.predecessorEdge = 1 := by
    unfold oldFactor
    rw [if_neg]
    intro hout
    apply hout.2
    have hright :
        r322JChainEdgeRight ctx.predecessorEdge =
          head.1.1 := by
      rw [
        R322InitialProperStepContext.predecessorEdge_eq
          hq κ hκ head tail hschedule hproper,
        r322AnalyticProperHeadPredecessorEdge_right
          hq κ hκ head tail hschedule hproper]
    rw [hright,
      r322AnalyticSchedule_head_block_eq_Icc
        κ head tail hschedule]
    have hheadMem :
        head ∈ r322AnalyticSchedule κ := by
      rw [hschedule]
      simp
    have hheadLt :
        head.1.1 < head.1.2 :=
      extract_mem_fst_lt_snd κ head.1
        (r322AnalyticSchedule_endpoint_mem_extract
          κ hheadMem)
    exact Finset.mem_Icc.mpr
      ⟨le_rfl, hheadLt.le⟩
  unfold residualChainProduct
    r322AnalyticHeadOuterChainProductWith
  rw [
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
      (Finset.mem_univ ctx.predecessorEdge),
    afterInitialProper_residualChainEdgeFactor_predecessor
      ρ lam ε hq κ hκ head tail hschedule hproper x]
  change
    _ * (∏ edge ∈ Finset.univ \ {ctx.predecessorEdge},
      post.residualChainEdgeFactor x edge) =
      _ * ∏ edge : Fin (2 * q - 1), oldFactor edge
  rw [
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
      (Finset.mem_univ ctx.predecessorEdge),
    hpredOld, one_mul]
  apply congrArg
    (fun value : ℝ =>
      post.state.edges ctx.predecessorEdge
          (x (r322AnalyticEdgeLeftVertex
                ctx.predecessorEdge) -
            x ctx.successorVertex) * value)
  apply Finset.prod_congr rfl
  intro edge hedge
  have hne : edge ≠ ctx.predecessorEdge := by
    simpa using (Finset.mem_sdiff.mp hedge).2
  exact
    afterInitialProper_residualChainEdgeFactor_eq_of_ne
      ρ lam ε hq κ hκ head tail hschedule hproper
      x edge hne

/-- Pointwise closure of the complete first post-prefix integrand.  This is
the missing compatibility statement between the global sparse residual and
the concrete outer factor produced by the first Fubini absorption. -/
theorem afterInitialProper_residualIntegrand_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (x : Fin (2 * q) → T4) :
    let ctx :=
      r322InitialProperStepContext
        hq κ hκ head tail hschedule hproper
    let post :=
      afterInitialProper
        ρ lam ε hq κ hκ head tail hschedule hproper
    post.residualIntegrand ρ ε x =
      post.state.edges ctx.predecessorEdge
          (ctx.predecessorPoint x -
            ctx.successorPoint x) *
        r322AnalyticHeadOuterIntegrandFactor
          ρ ε κ head tail hschedule x := by
  dsimp only
  let ctx :=
    r322InitialProperStepContext
      hq κ hκ head tail hschedule hproper
  let post :=
    afterInitialProper
      ρ lam ε hq κ hκ head tail hschedule hproper
  unfold residualIntegrand
    r322AnalyticHeadOuterIntegrandFactor
    r322AnalyticHeadOuterFactorWith
  rw [
    afterInitialProper_residualChainProduct_eq
      ρ lam ε hq κ hκ head tail hschedule hproper x,
    afterInitialProper_residualDifferenceProduct_eq
      ρ lam ε hq κ hκ head tail hschedule hproper x,
    afterInitialProper_residualPrimitiveProduct_eq
      ρ lam ε hq κ hκ head tail hschedule hproper x]
  unfold R322AnalyticProperStepContext.predecessorPoint
    R322AnalyticProperStepContext.successorPoint
  rw [
    R322AnalyticProperStepContext.predecessorEdge,
    r322AnalyticEdgeLeftVertex_predecessorEdge]
  ring

/-! ## Exact first residual-value transition -/

/-- The concrete first updated outer integral is exactly the value of the
global post-prefix residual object.  The proof uses the explicit finite
coordinate equivalence above; no identification of pre- and post-collapse
ambient integrands is made. -/
theorem r322InitialUpdatedOuterIntegral_eq_afterInitialProper_residualValue
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4) :
    r322InitialUpdatedOuterIntegral
        hq ρ lam ε κ hκ head tail hschedule hproper z =
      (afterInitialProper
        ρ lam ε hq κ hκ head tail hschedule hproper).residualValue
        ρ lam ε z := by
  let ctx :=
    r322InitialProperStepContext
      hq κ hκ head tail hschedule hproper
  let post :=
    afterInitialProper
      ρ lam ε hq κ hκ head tail hschedule hproper
  let μC : Measure
      (InitialComplementCoordinate hq head → T4) :=
    Measure.pi fun _ => paperMeasure
  let μS : Measure
      (post.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let e :
      (InitialComplementCoordinate hq head → T4) ≃ᵐ
        (post.SurvivingCoordinate → T4) :=
    initialComplementPiMeasurableEquiv
      ρ lam ε hq κ hκ head tail hschedule hproper
  let f : (post.SurvivingCoordinate → T4) → ℝ :=
    fun v =>
      post.residualIntegrand ρ ε
        (post.reconstruct z v)
  have hreindex :
      (∫ vC, f (e vC) ∂μC) =
        ∫ v, f v ∂μS := by
    exact
      (measurePreserving_initialComplementPiMeasurableEquiv
        ρ lam ε hq κ hκ head tail hschedule hproper).integral_comp' f
  have horder :
      post.remainingOrder =
        r322AnalyticSuffixOrder tail := by
    rfl
  calc
    r322InitialUpdatedOuterIntegral
        hq ρ lam ε κ hκ head tail hschedule hproper z =
      ∫ vC,
        lamEps lam ε ^
            (2 * r322AnalyticSuffixOrder tail) *
          f (e vC)
        ∂μC := by
      unfold r322InitialUpdatedOuterIntegral
        R322AnalyticProperStepContext.updatedResidualOuterIntegral
      apply integral_congr_ae
      filter_upwards with vC
      change
        (ctx.nextState ρ lam ε).edges ctx.predecessorEdge
              (ctx.predecessorPoint
                  (r322AnalyticProperHeadReferenceTuple
                    hq κ hκ head tail hschedule hproper z vC) -
                ctx.successorPoint
                  (r322AnalyticProperHeadReferenceTuple
                    hq κ hκ head tail hschedule hproper z vC)) *
            (lamEps lam ε ^
                (2 * r322AnalyticSuffixOrder tail) *
              r322AnalyticHeadOuterIntegrandFactor
                ρ ε κ head tail hschedule
                (r322AnalyticProperHeadReferenceTuple
                  hq κ hκ head tail hschedule hproper z vC)) =
          lamEps lam ε ^
              (2 * r322AnalyticSuffixOrder tail) *
            f (e vC)
      have hcoord :
          post.reconstruct z (e vC) =
            r322AnalyticProperHeadReferenceTuple
              hq κ hκ head tail hschedule hproper z vC := by
        exact
          afterInitialProper_reconstruct_reindex
            ρ lam ε hq κ hκ head tail hschedule hproper z vC
      unfold f
      rw [
        hcoord,
        afterInitialProper_residualIntegrand_eq
          ρ lam ε hq κ hκ head tail hschedule hproper
          (r322AnalyticProperHeadReferenceTuple
            hq κ hκ head tail hschedule hproper z vC)]
      have hstate :
          post.state = ctx.nextState ρ lam ε :=
        rfl
      rw [← hstate]
      ring
    _ =
      lamEps lam ε ^
          (2 * r322AnalyticSuffixOrder tail) *
        (∫ vC, f (e vC) ∂μC) := by
      rw [integral_const_mul]
    _ =
      lamEps lam ε ^
          (2 * r322AnalyticSuffixOrder tail) *
        (∫ v, f v ∂μS) := by
      rw [hreindex]
    _ =
      post.residualValue ρ lam ε z := by
      unfold residualValue
      rw [horder]

/-! ## Arbitrary proper-prefix coordinate decomposition -/

section ProperPrefixCoordinates

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {q : ℕ} {hq : 1 ≤ q}
    (res : R322AnalyticResidualPrefix ρ lam ε q hq)
    (step : R322ExtractionStep (2 * q))
    (suffix : List (R322ExtractionStep (2 * q)))
    (hremaining : res.remaining = step :: suffix)
    (hproper :
      step.1 ≠ r322WholeEndpoint q hq)

/-- Every vertex of the current concrete block is active before the current
proper update. -/
theorem properBlockVertex_mem_active
    (i : Fin (2 * q)) (hi : i ∈ step.2) :
    let _ctx :=
      res.properStepContext
        step suffix hremaining hproper
    i ∈ res.state.active := by
  dsimp only
  have hblock :=
    r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
      res.pairing res.state.processed suffix step
      (res.properStepContext
        step suffix hremaining hproper).schedule_eq
  rw [hblock] at hi
  exact (Finset.mem_inter.mp hi).1

/-- A proper block contains neither global endpoint, so each of its vertices
is represented in the pre-update surviving-coordinate type. -/
theorem properBlockVertex_internal
    (i : Fin (2 * q)) (hi : i ∈ step.2) :
    let _ctx :=
      res.properStepContext
        step suffix hremaining hproper
    0 < i.val ∧ i.val < 2 * q - 1 := by
  dsimp only
  have hblock :=
    r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
      res.pairing res.state.processed suffix step
      (res.properStepContext
        step suffix hremaining hproper).schedule_eq
  have hiBounds :
      step.1.1 ≤ i ∧ i ≤ step.1.2 := by
    rw [hblock] at hi
    exact Finset.mem_Icc.mp
      (Finset.mem_inter.mp hi).2
  have hbounds :=
    (res.properStepContext
      step suffix hremaining hproper).bounds
  dsimp only [properStepContext] at hbounds
  constructor <;> omega

/-- The updated active carrier is a subset of the old one. -/
theorem afterProper_vertex_mem_previous_active
    (i : Fin (2 * q))
    (hi :
      i ∈
        (res.afterProper step suffix
          hremaining hproper).state.active) :
    i ∈ res.state.active := by
  rw [res.afterProper_active
    step suffix hremaining hproper] at hi
  exact (Finset.mem_sdiff.mp hi).1

/-- The current context's canonical block order, with its definitionally
equal `step` field hidden behind a stable public type. -/
def properBlockOrderIso :
    Fin (2 * residualBlockOrder step.2) ≃
      {i : Fin (2 * q) // i ∈ step.2} := by
  simpa only [properStepContext] using
    (res.properStepContext
      step suffix hremaining hproper).blockOrderIso.toEquiv

/-- Exact index decomposition at an arbitrary reachable proper prefix:
current standard block vertices, followed by all post-update surviving
vertices. -/
def properCoordinateEquiv :
    (Fin (2 * residualBlockOrder step.2) ⊕
        (res.afterProper step suffix
          hremaining hproper).SurvivingCoordinate) ≃
      res.SurvivingCoordinate where
  toFun
    | Sum.inl j =>
        let i :=
          (properBlockOrderIso res
            step suffix hremaining hproper j).1
        ⟨i,
          res.properBlockVertex_mem_active
            step suffix hremaining hproper i
            (properBlockOrderIso res
              step suffix hremaining hproper j).2,
          (res.properBlockVertex_internal
            step suffix hremaining hproper i
            (properBlockOrderIso res
              step suffix hremaining hproper j).2).1,
          (res.properBlockVertex_internal
            step suffix hremaining hproper i
            (properBlockOrderIso res
              step suffix hremaining hproper j).2).2⟩
    | Sum.inr i =>
        ⟨i.1,
          res.afterProper_vertex_mem_previous_active
            step suffix hremaining hproper i.1 i.2.1,
          i.2.2.1, i.2.2.2⟩
  invFun i :=
    if hi : i.1 ∈ step.2 then
      Sum.inl
        ((properBlockOrderIso res
          step suffix hremaining hproper).symm
            ⟨i.1, hi⟩)
    else
      Sum.inr
        ⟨i.1,
          by
            rw [res.afterProper_active
              step suffix hremaining hproper]
            exact Finset.mem_sdiff.mpr
              ⟨i.2.1, hi⟩,
          i.2.2.1, i.2.2.2⟩
  left_inv value := by
    rcases value with j | i
    · simp only
      have hi :
          (properBlockOrderIso res
            step suffix hremaining hproper j).1 ∈
              step.2 :=
        (properBlockOrderIso res
          step suffix hremaining hproper j).2
      rw [dif_pos hi]
      apply congrArg Sum.inl
      exact
        (properBlockOrderIso res
          step suffix hremaining hproper).symm_apply_apply j
    · simp only
      have hi : i.1 ∉ step.2 := by
        have hparts :
            i.1 ∈ res.state.active \ step.2 := by
          rw [← res.afterProper_active
            step suffix hremaining hproper]
          exact i.2.1
        exact (Finset.mem_sdiff.mp hparts).2
      rw [dif_neg hi]
      apply congrArg Sum.inr
      apply Subtype.ext
      rfl
  right_inv i := by
    by_cases hi : i.1 ∈ step.2
    · simp only [hi, dite_true]
      apply Subtype.ext
      change
        ((properBlockOrderIso res
          step suffix hremaining hproper)
            ((properBlockOrderIso res
              step suffix hremaining hproper).symm
                ⟨i.1, hi⟩)).1 =
          i.1
      exact congrArg Subtype.val
        ((properBlockOrderIso res
          step suffix hremaining hproper).apply_symm_apply
            ⟨i.1, hi⟩)
    · simp only [hi, dite_false]
      apply Subtype.ext
      rfl

/-- Measurable splitting of all pre-update surviving coordinates into the
current standard block and the post-update surviving carrier. -/
def properCoordinatePiMeasurableEquiv :
    (res.SurvivingCoordinate → T4) ≃ᵐ
      ((Fin (2 * residualBlockOrder step.2) → T4) ×
        ((res.afterProper step suffix
          hremaining hproper).SurvivingCoordinate → T4)) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : res.SurvivingCoordinate => T4)
      (res.properCoordinateEquiv
        step suffix hremaining hproper)).symm |>.trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ :
        Fin (2 * residualBlockOrder step.2) ⊕
          (res.afterProper step suffix
            hremaining hproper).SurvivingCoordinate =>
        T4))

/-- The arbitrary-prefix split preserves the exact product Haar measure. -/
theorem measurePreserving_properCoordinatePiMeasurableEquiv :
    MeasurePreserving
      (res.properCoordinatePiMeasurableEquiv
        step suffix hremaining hproper)
      (Measure.pi fun _ : res.SurvivingCoordinate =>
        paperMeasure)
      ((Measure.pi fun _ :
          Fin (2 * residualBlockOrder step.2) =>
            paperMeasure).prod
        (Measure.pi fun _ :
          (res.afterProper step suffix
            hremaining hproper).SurvivingCoordinate =>
              paperMeasure)) := by
  let e :=
    res.properCoordinateEquiv
      step suffix hremaining hproper
  have hfirst :
      MeasurePreserving
        (MeasurableEquiv.piCongrLeft
          (fun _ : res.SurvivingCoordinate => T4) e).symm
        (Measure.pi fun _ : res.SurvivingCoordinate =>
          paperMeasure)
        (Measure.pi fun _ :
          Fin (2 * residualBlockOrder step.2) ⊕
            (res.afterProper step suffix
              hremaining hproper).SurvivingCoordinate =>
                paperMeasure) :=
    (measurePreserving_piCongrLeft
      (fun _ : res.SurvivingCoordinate =>
        paperMeasure) e).symm
  have hsecond :
      MeasurePreserving
        (MeasurableEquiv.sumPiEquivProdPi
          (fun _ :
            Fin (2 * residualBlockOrder step.2) ⊕
              (res.afterProper step suffix
                hremaining hproper).SurvivingCoordinate =>
            T4))
        (Measure.pi fun _ :
          Fin (2 * residualBlockOrder step.2) ⊕
            (res.afterProper step suffix
              hremaining hproper).SurvivingCoordinate =>
                paperMeasure)
        ((Measure.pi fun _ :
            Fin (2 * residualBlockOrder step.2) =>
              paperMeasure).prod
          (Measure.pi fun _ :
            (res.afterProper step suffix
              hremaining hproper).SurvivingCoordinate =>
                paperMeasure)) :=
    measurePreserving_sumPiEquivProdPi
      (fun _ :
        Fin (2 * residualBlockOrder step.2) ⊕
          (res.afterProper step suffix
            hremaining hproper).SurvivingCoordinate =>
        paperMeasure)
  exact hsecond.comp hfirst

@[simp]
theorem properCoordinatePiMeasurableEquiv_fst_apply
    (v : res.SurvivingCoordinate → T4)
    (j : Fin (2 * residualBlockOrder step.2)) :
    (res.properCoordinatePiMeasurableEquiv
        step suffix hremaining hproper v).1 j =
      v (res.properCoordinateEquiv
        step suffix hremaining hproper (Sum.inl j)) := by
  rfl

@[simp]
theorem properCoordinatePiMeasurableEquiv_snd_apply
    (v : res.SurvivingCoordinate → T4)
    (i :
      (res.afterProper step suffix
        hremaining hproper).SurvivingCoordinate) :
    (res.properCoordinatePiMeasurableEquiv
        step suffix hremaining hproper v).2 i =
      v (res.properCoordinateEquiv
        step suffix hremaining hproper (Sum.inr i)) := by
  rfl

/-- Stable, step-typed wrapper around the context's ambient block
reconstruction. -/
def properReconstructBlockTuple
    (base : Fin (2 * q) → T4)
    (t : Fin (2 * residualBlockOrder step.2) → T4) :
    Fin (2 * q) → T4 :=
  fun i =>
    if hi : i ∈ step.2 then
      t ((properBlockOrderIso res
        step suffix hremaining hproper).symm ⟨i, hi⟩)
    else base i

/-- The stable wrapper is the actual context reconstruction. -/
theorem properReconstructBlockTuple_eq_context
    (base : Fin (2 * q) → T4)
    (t : Fin (2 * residualBlockOrder step.2) → T4) :
    res.properReconstructBlockTuple
        step suffix hremaining hproper base t =
      (res.properStepContext
        step suffix hremaining hproper).reconstructBlockTuple
          base t := by
  funext i
  unfold properReconstructBlockTuple
    R322AnalyticProperStepContext.reconstructBlockTuple
    properBlockOrderIso properStepContext
  rfl

/-- Reassembling the two components of the arbitrary-prefix coordinate
split reproduces the original ambient residual tuple exactly. -/
theorem reconstructBlockTuple_properCoordinateSplit
    (z : T4)
    (v : res.SurvivingCoordinate → T4) :
    res.properReconstructBlockTuple
        step suffix hremaining hproper
        ((res.afterProper step suffix
            hremaining hproper).reconstruct z
          (res.properCoordinatePiMeasurableEquiv
            step suffix hremaining hproper v).2)
        (res.properCoordinatePiMeasurableEquiv
          step suffix hremaining hproper v).1 =
      res.reconstruct z v := by
  let post :=
    res.afterProper step suffix hremaining hproper
  let split :=
    res.properCoordinatePiMeasurableEquiv
      step suffix hremaining hproper v
  funext i
  by_cases hiBlock : i ∈ step.2
  · have hinternal :=
      res.properBlockVertex_internal
        step suffix hremaining hproper i hiBlock
    have hactive :=
      res.properBlockVertex_mem_active
        step suffix hremaining hproper i hiBlock
    unfold properReconstructBlockTuple
    rw [dif_pos hiBlock]
    unfold reconstruct
    rw [
      dif_neg (ne_of_gt hinternal.1),
      dif_neg (ne_of_lt hinternal.2),
      dif_pos hactive]
    change
      split.1
          ((properBlockOrderIso res
            step suffix hremaining hproper).symm
              ⟨i, hiBlock⟩) =
        v ⟨i, hactive, hinternal.1, hinternal.2⟩
    rw [properCoordinatePiMeasurableEquiv_fst_apply]
    apply congrArg v
    apply Subtype.ext
    change
      ((properBlockOrderIso res
        step suffix hremaining hproper)
          ((properBlockOrderIso res
            step suffix hremaining hproper).symm
              ⟨i, hiBlock⟩)).1 =
        i
    exact congrArg Subtype.val
      ((properBlockOrderIso res
        step suffix hremaining hproper).apply_symm_apply
          ⟨i, hiBlock⟩)
  · unfold properReconstructBlockTuple
    rw [dif_neg hiBlock]
    by_cases hzero : i.val = 0
    · have hi :
          i = (⟨0, by omega⟩ : Fin (2 * q)) :=
        Fin.ext hzero
      rw [hi, post.reconstruct_zero,
        res.reconstruct_zero]
    by_cases hlast : i.val = 2 * q - 1
    · have hi :
          i =
            (⟨2 * q - 1, by omega⟩ :
              Fin (2 * q)) :=
        Fin.ext hlast
      rw [hi, post.reconstruct_last,
        res.reconstruct_last]
    by_cases hactive : i ∈ res.state.active
    · have hpostActive : i ∈ post.state.active := by
        rw [res.afterProper_active
          step suffix hremaining hproper]
        exact Finset.mem_sdiff.mpr
          ⟨hactive, hiBlock⟩
      let si : post.SurvivingCoordinate :=
        ⟨i, hpostActive, by omega, by omega⟩
      let ri : res.SurvivingCoordinate :=
        ⟨i, hactive, by omega, by omega⟩
      calc
        post.reconstruct z split.2 i =
            split.2 si := by
          exact post.reconstruct_surviving z split.2 si
        _ = v ri := by
          rw [properCoordinatePiMeasurableEquiv_snd_apply]
          apply congrArg v
          apply Subtype.ext
          rfl
        _ = res.reconstruct z v i := by
          exact (res.reconstruct_surviving z v ri).symm
    · have hpostInactive : i ∉ post.state.active := by
        intro hi
        exact hactive
          (res.afterProper_vertex_mem_previous_active
            step suffix hremaining hproper i hi)
      rw [
        post.reconstruct_eq_zero_of_internal_inactive
          z split.2 i hzero hlast hpostInactive,
        res.reconstruct_eq_zero_of_internal_inactive
          z v i hzero hlast hactive]

/-- Outer-first form of the proper coordinate split, matching the order of
integration in the one-step residual Fubini API. -/
def properOuterBlockPiMeasurableEquiv :
    (res.SurvivingCoordinate → T4) ≃ᵐ
      (((res.afterProper step suffix
          hremaining hproper).SurvivingCoordinate → T4) ×
        (Fin (2 * residualBlockOrder step.2) → T4)) :=
  (res.properCoordinatePiMeasurableEquiv
      step suffix hremaining hproper).trans
    MeasurableEquiv.prodComm

/-- The outer-first split preserves outer-product-block Haar measure. -/
theorem measurePreserving_properOuterBlockPiMeasurableEquiv :
    MeasurePreserving
      (res.properOuterBlockPiMeasurableEquiv
        step suffix hremaining hproper)
      (Measure.pi fun _ : res.SurvivingCoordinate =>
        paperMeasure)
      ((Measure.pi fun _ :
          (res.afterProper step suffix
            hremaining hproper).SurvivingCoordinate =>
              paperMeasure).prod
        (Measure.pi fun _ :
          Fin (2 * residualBlockOrder step.2) =>
            paperMeasure)) := by
  exact
    (Measure.measurePreserving_swap).comp
      (res.measurePreserving_properCoordinatePiMeasurableEquiv
        step suffix hremaining hproper)

@[simp]
theorem properOuterBlockPiMeasurableEquiv_fst_apply
    (v : res.SurvivingCoordinate → T4) :
    (res.properOuterBlockPiMeasurableEquiv
      step suffix hremaining hproper v).1 =
      (res.properCoordinatePiMeasurableEquiv
        step suffix hremaining hproper v).2 :=
  rfl

@[simp]
theorem properOuterBlockPiMeasurableEquiv_snd_apply
    (v : res.SurvivingCoordinate → T4) :
    (res.properOuterBlockPiMeasurableEquiv
      step suffix hremaining hproper v).2 =
      (res.properCoordinatePiMeasurableEquiv
        step suffix hremaining hproper v).1 :=
  rfl

/-- Reassembly stated directly for the outer-first measurable split. -/
theorem reconstructBlockTuple_properOuterBlockSplit
    (z : T4)
    (v : res.SurvivingCoordinate → T4) :
    res.properReconstructBlockTuple
        step suffix hremaining hproper
        ((res.afterProper step suffix
            hremaining hproper).reconstruct z
          (res.properOuterBlockPiMeasurableEquiv
            step suffix hremaining hproper v).1)
        (res.properOuterBlockPiMeasurableEquiv
          step suffix hremaining hproper v).2 =
      res.reconstruct z v := by
  exact
    res.reconstructBlockTuple_properCoordinateSplit
      step suffix hremaining hproper z v

/-- Exact outer-then-block Fubini form of an arbitrary proper-prefix
residual value.  The sole premise is genuine joint integrability of the
current residual integrand; no equality or estimate is assumed. -/
theorem residualValue_eq_iteratedProperRaw
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (z : T4)
    (hint :
      Integrable
        (fun v : res.SurvivingCoordinate → T4 =>
          res.residualIntegrand ρ ε
            (res.reconstruct z v))
        (Measure.pi fun _ => paperMeasure)) :
    res.residualValue ρ lam ε z =
      lamEps lam ε ^ (2 * res.remainingOrder) *
        ∫ outer :
            (res.afterProper step suffix
              hremaining hproper).SurvivingCoordinate → T4,
          ∫ t :
              Fin (2 * residualBlockOrder step.2) → T4,
            res.residualIntegrand ρ ε
              (res.properReconstructBlockTuple
                step suffix hremaining hproper
                ((res.afterProper step suffix
                    hremaining hproper).reconstruct z outer)
                t)
            ∂Measure.pi fun _ => paperMeasure
          ∂Measure.pi fun _ => paperMeasure := by
  let μPre : Measure (res.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μOuter : Measure
      ((res.afterProper step suffix
        hremaining hproper).SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μBlock : Measure
      (Fin (2 * residualBlockOrder step.2) → T4) :=
    Measure.pi fun _ => paperMeasure
  let e :=
    res.properOuterBlockPiMeasurableEquiv
      step suffix hremaining hproper
  let g :
      (((res.afterProper step suffix
          hremaining hproper).SurvivingCoordinate → T4) ×
        (Fin (2 * residualBlockOrder step.2) → T4)) → ℝ :=
    fun p =>
      res.residualIntegrand ρ ε
        (res.properReconstructBlockTuple
          step suffix hremaining hproper
          ((res.afterProper step suffix
            hremaining hproper).reconstruct z p.1)
          p.2)
  have hcomp :
      Integrable (g ∘ e) μPre := by
    apply hint.congr
    filter_upwards with v
    change
      res.residualIntegrand ρ ε
          (res.reconstruct z v) =
        g (e v)
    unfold g e
    rw [
      res.reconstructBlockTuple_properOuterBlockSplit
        step suffix hremaining hproper z v]
  have hg : Integrable g (μOuter.prod μBlock) :=
    (res.measurePreserving_properOuterBlockPiMeasurableEquiv
      step suffix hremaining hproper).integrable_comp_emb
        e.measurableEmbedding |>.mp hcomp
  have hmap :
      (∫ v, g (e v) ∂μPre) =
        ∫ p, g p ∂μOuter.prod μBlock :=
    (res.measurePreserving_properOuterBlockPiMeasurableEquiv
      step suffix hremaining hproper).integral_comp' g
  unfold residualValue
  apply congrArg
    (fun value : ℝ =>
      lamEps lam ε ^ (2 * res.remainingOrder) * value)
  calc
    (∫ v : res.SurvivingCoordinate → T4,
        res.residualIntegrand ρ ε
          (res.reconstruct z v)
        ∂Measure.pi fun _ => paperMeasure) =
      ∫ v, g (e v) ∂μPre := by
        apply integral_congr_ae
        filter_upwards with v
        unfold g e
        rw [
          res.reconstructBlockTuple_properOuterBlockSplit
            step suffix hremaining hproper z v]
    _ = ∫ p, g p ∂μOuter.prod μBlock :=
      hmap
    _ = ∫ outer, ∫ t, g (outer, t) ∂μBlock
        ∂μOuter :=
      integral_prod g hg
    _ = _ := rfl

/-! ## Arbitrary proper-prefix factor ledgers -/

/-- The coupling order splits exactly into the current block order and the
post-update suffix order. -/
theorem remainingOrder_eq_current_add_afterProper :
    res.remainingOrder =
      residualBlockOrder step.2 +
        (res.afterProper step suffix
          hremaining hproper).remainingOrder := by
  unfold remainingOrder
  rw [hremaining]
  simp

/-- The primitive covariance product splits at the current schedule head;
the suffix is exactly the post-update primitive product. -/
theorem residualPrimitiveProduct_eq_current_mul_afterProper
    (ρ : SmoothCutoff) (ε : ℝ)
    (x : Fin (2 * q) → T4) :
    res.residualPrimitiveProduct ρ ε x =
      r322ExtractionBlockPrimitiveSum ρ ε
          res.pairing
          (res.remainingBlockIndex
            ⟨0, by
              rw [hremaining]
              simp⟩) x *
        (res.afterProper step suffix
          hremaining hproper).residualPrimitiveProduct
            ρ ε x := by
  have hlength :
      res.remaining.length = suffix.length + 1 := by
    rw [hremaining]
    simp
  let e :
      Fin res.remaining.length ≃
        Fin (suffix.length + 1) :=
    finCongr hlength
  let f : Fin res.remaining.length → ℝ :=
    fun j =>
      r322ExtractionBlockPrimitiveSum ρ ε
        res.pairing (res.remainingBlockIndex j) x
  let jzero : Fin res.remaining.length :=
    ⟨0, by
      rw [hremaining]
      simp⟩
  have hezero :
      e.symm (0 : Fin (suffix.length + 1)) =
        jzero := by
    apply Fin.ext
    rfl
  unfold residualPrimitiveProduct
  calc
    (∏ j : Fin res.remaining.length, f j) =
        ∏ k : Fin (suffix.length + 1),
          f (e.symm k) :=
      (Equiv.prod_comp e.symm f).symm
    _ =
        f (e.symm 0) *
          ∏ j : Fin suffix.length,
            f (e.symm j.succ) := by
      rw [Fin.prod_univ_succ]
    _ =
        f jzero *
          (res.afterProper step suffix
            hremaining hproper).residualPrimitiveProduct
              ρ ε x := by
      rw [hezero]
      apply congrArg (fun value : ℝ => f jzero * value)
      unfold residualPrimitiveProduct
      apply Finset.prod_congr rfl
      intro j _hj
      apply congrArg
        (fun B : ExtractionBlockIndex res.pairing =>
          r322ExtractionBlockPrimitiveSum
            ρ ε res.pairing B x)
      apply Subtype.ext
      rw [
        (res.afterProper step suffix
          hremaining hproper).remainingBlockIndex_val,
        res.remainingBlockIndex_val]
      have hget :=
        List.get_of_eq hremaining (e.symm j.succ)
      have hval :
          (e.symm j.succ).val = j.val + 1 := by
        rfl
      change
        (res.remaining.get (e.symm j.succ)).2 =
          (suffix.get j).2
      simpa only [List.get_cons_succ,
        hval] using congrArg Prod.snd hget
    _ = _ := rfl

/-- The current residual block index is the actual block stored at the
displayed proper head. -/
theorem remainingBlockIndex_zero_val :
    (res.remainingBlockIndex
      ⟨0, by
        rw [hremaining]
        simp⟩).1 =
      step.2 := by
  rw [res.remainingBlockIndex_val]
  have hget :=
    List.get_of_eq hremaining
      (⟨0, by
        rw [hremaining]
        simp⟩ : Fin res.remaining.length)
  simpa using congrArg Prod.snd hget

/-- Every suffix step has a strictly larger right endpoint than the current
proper head. -/
theorem properStep_right_lt_suffix_right
    (later : R322ExtractionStep (2 * q))
    (hlater : later ∈ suffix) :
    let _ctx :=
      res.properStepContext
        step suffix hremaining hproper
    step.1.2 < later.1.2 := by
  dsimp only
  have hp :=
    r322AnalyticSchedule_pairwise_right_lt res.pairing
  rw [res.schedule_eq, hremaining,
    List.pairwise_append] at hp
  exact (List.pairwise_cons.mp hp.2.1).1
    later hlater

/-- Removing the current block does not alter the active-successor set
strictly to the right of any suffix endpoint. -/
theorem successorCandidates_afterProper_eq_of_mem_suffix
    (later : R322ExtractionStep (2 * q))
    (hlater : later ∈ suffix) :
    r322AnalyticSuccessorCandidates
        (res.afterProper step suffix
          hremaining hproper).state later.1.2 =
      r322AnalyticSuccessorCandidates
        res.state later.1.2 := by
  ext i
  simp only [r322AnalyticSuccessorCandidates,
    Finset.mem_filter]
  rw [res.afterProper_active
    step suffix hremaining hproper]
  simp only [Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hactive, _hnotBlock⟩, hright⟩
    exact ⟨hactive, hright⟩
  · rintro ⟨hactive, hright⟩
    refine ⟨⟨hactive, ?_⟩, hright⟩
    intro hiBlock
    have hblock :=
      r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
        res.pairing res.state.processed suffix step
        (res.properStepContext
          step suffix hremaining hproper).schedule_eq
    have hiUpper : i ≤ step.1.2 := by
      rw [hblock] at hiBlock
      exact
        (Finset.mem_Icc.mp
          (Finset.mem_inter.mp hiBlock).2).2
    have hstepLater :=
      res.properStep_right_lt_suffix_right
        step suffix hremaining hproper later hlater
    exact (not_lt_of_ge
      (hiUpper.trans hstepLater.le)) hright

/-- Consequently every suffix endpoint has exactly the same sparse
successor before and after the current proper update. -/
theorem successorVertex_afterProper_eq_of_mem_suffix
    (later : R322ExtractionStep (2 * q))
    (hlater : later ∈ suffix)
    (hguard : later.1.2.val < 2 * q - 1) :
    r322AnalyticSuccessorVertex
        (res.afterProper step suffix
          hremaining hproper).state
        later.1.2 hguard =
      r322AnalyticSuccessorVertex
        res.state later.1.2 hguard := by
  have hcandidates :=
    res.successorCandidates_afterProper_eq_of_mem_suffix
      step suffix hremaining hproper later hlater
  unfold r322AnalyticSuccessorVertex
  apply le_antisymm
  · apply Finset.min'_le
    rw [hcandidates]
    exact Finset.min'_mem _ _
  · apply Finset.min'_le
    rw [← hcandidates]
    exact Finset.min'_mem _ _

/-- The edge stored at a suffix right endpoint is untouched by the current
proper update. -/
theorem afterProper_suffix_edge_eq
    (later : R322ExtractionStep (2 * q))
    (hlater : later ∈ suffix)
    (hguard : later.1.2.val < 2 * q - 1) :
    (res.afterProper step suffix
        hremaining hproper).state.edges
        ⟨later.1.2.val, hguard⟩ =
      res.state.edges ⟨later.1.2.val, hguard⟩ := by
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  let edge : Fin (2 * q - 1) :=
    ⟨later.1.2.val, hguard⟩
  have hright :
      step.1.2 <
        r322AnalyticEdgeLeftVertex edge := by
    change step.1.2.val < later.1.2.val
    exact
      res.properStep_right_lt_suffix_right
        step suffix hremaining hproper later hlater
  change (ctx.nextState ρ lam ε).edges edge =
    ctx.state.edges edge
  rw [R322AnalyticProperStepContext.nextState,
    R322AnalyticEdgeState.updateProper_edges_eq_of_right_lt
      ctx.state ctx.pairing ctx.pairing_mem ctx.suffix
      ctx.step ctx.schedule_eq ctx.proper
      (primitiveKernelDiff ρ lam ε
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder ctx.internalEdges)
      edge hright]

/-- Every signed suffix difference is pointwise unchanged by the current
proper update. -/
theorem residualStepDifference_afterProper_eq_of_mem_suffix
    (x : Fin (2 * q) → T4)
    (later : R322ExtractionStep (2 * q))
    (hlater : later ∈ suffix) :
    (res.afterProper step suffix
        hremaining hproper).residualStepDifference x later =
      res.residualStepDifference x later := by
  by_cases hguard :
      later.1.2.val < 2 * q - 1
  · have hpost :
        (res.afterProper step suffix
            hremaining hproper).residualStepDifference x later =
          (res.afterProper step suffix
              hremaining hproper).state.edges
              ⟨later.1.2.val, hguard⟩
              (x later.1.2 -
                x (r322AnalyticSuccessorVertex
                  (res.afterProper step suffix
                    hremaining hproper).state
                  later.1.2 hguard)) -
            (res.afterProper step suffix
              hremaining hproper).state.edges
              ⟨later.1.2.val, hguard⟩
              (x later.1.1 -
                x (r322AnalyticSuccessorVertex
                  (res.afterProper step suffix
                    hremaining hproper).state
                  later.1.2 hguard)) := by
      unfold residualStepDifference
      split
      · rfl
      · contradiction
    have hpre :
        res.residualStepDifference x later =
          res.state.edges
              ⟨later.1.2.val, hguard⟩
              (x later.1.2 -
                x (r322AnalyticSuccessorVertex
                  res.state later.1.2 hguard)) -
            res.state.edges
              ⟨later.1.2.val, hguard⟩
              (x later.1.1 -
                x (r322AnalyticSuccessorVertex
                  res.state later.1.2 hguard)) := by
      unfold residualStepDifference
      split
      · rfl
      · contradiction
    rw [hpost, hpre,
      res.afterProper_suffix_edge_eq
        step suffix hremaining hproper
        later hlater hguard,
      res.successorVertex_afterProper_eq_of_mem_suffix
        step suffix hremaining hproper
        later hlater hguard]
  · have hpost :
        (res.afterProper step suffix
            hremaining hproper).residualStepDifference x later = 1 := by
      unfold residualStepDifference
      split
      · contradiction
      · rfl
    have hpre :
        res.residualStepDifference x later = 1 := by
      unfold residualStepDifference
      split
      · contradiction
      · rfl
    rw [hpost, hpre]

/-- The complete difference product splits into the current signed
difference and the unchanged post-update suffix product. -/
theorem residualDifferenceProduct_eq_current_mul_afterProper
    (x : Fin (2 * q) → T4) :
    res.residualDifferenceProduct x =
      res.residualStepDifference x step *
        (res.afterProper step suffix
          hremaining hproper).residualDifferenceProduct x := by
  unfold residualDifferenceProduct
  rw [hremaining]
  simp only [List.map_cons, List.prod_cons]
  apply congrArg
    (fun value : ℝ =>
      res.residualStepDifference x step * value)
  apply congrArg List.prod
  apply List.map_congr_left
  intro later hlater
  exact
    (res.residualStepDifference_afterProper_eq_of_mem_suffix
      step suffix hremaining hproper x later hlater).symm

/-- The current residual difference is the context's actual sparse
outgoing difference. -/
theorem residualStepDifference_current_eq
    (x : Fin (2 * q) → T4) :
    res.residualStepDifference x step =
      res.state.edges
          (res.properStepContext
            step suffix hremaining hproper).outgoingEdge
          (x step.1.2 -
            x (res.properStepContext
              step suffix hremaining hproper).successorVertex) -
        res.state.edges
          (res.properStepContext
            step suffix hremaining hproper).outgoingEdge
          (x step.1.1 -
            x (res.properStepContext
              step suffix hremaining hproper).successorVertex) := by
  have hguard :
      step.1.2.val < 2 * q - 1 :=
    (res.properStepContext
      step suffix hremaining hproper).bounds.2
  unfold residualStepDifference
  split
  · rfl
  · contradiction

/-! ## Arbitrary proper-prefix chain ledgers -/

/-- After deleting the current proper block, the predecessor slot skips
exactly that block and lands at the old sparse successor of the current
right endpoint. -/
theorem afterProper_predecessor_successor_eq :
    (res.afterProper step suffix
        hremaining hproper).edgeSuccessor
        (res.properStepContext
          step suffix hremaining hproper).predecessorEdge =
      (res.properStepContext
        step suffix hremaining hproper).successorVertex := by
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  let post :=
    res.afterProper
      step suffix hremaining hproper
  have hstepLt :
      ctx.step.1.1 < ctx.step.1.2 :=
    extract_mem_fst_lt_snd
      ctx.pairing ctx.step.1
      (r322AnalyticSchedule_endpoint_mem_extract
        ctx.pairing ctx.step_mem_schedule)
  have htargetActive :
      ctx.successorVertex ∈ post.state.active := by
    rw [res.afterProper_active
      step suffix hremaining hproper]
    exact Finset.mem_sdiff.mpr
      ⟨ctx.successorVertex_mem_active,
        ctx.successorVertex_not_mem_step⟩
  have hpredLtTarget :
      r322AnalyticEdgeLeftVertex ctx.predecessorEdge <
        ctx.successorVertex := by
    rw [R322AnalyticProperStepContext.predecessorEdge,
      r322AnalyticEdgeLeftVertex_predecessorEdge]
    exact
      (r322AnalyticPredecessorVertex_lt_left
          ctx.state ctx.step ctx.bounds.1).trans
        (hstepLt.trans ctx.stepRight_lt_successorVertex)
  have htargetCandidate :
      ctx.successorVertex ∈
        r322AnalyticSuccessorCandidates
          post.state
          (r322AnalyticEdgeLeftVertex
            ctx.predecessorEdge) :=
    Finset.mem_filter.mpr
      ⟨htargetActive, hpredLtTarget⟩
  have hupper :
      post.edgeSuccessor ctx.predecessorEdge ≤
        ctx.successorVertex := by
    unfold edgeSuccessor r322AnalyticSuccessorVertex
    exact Finset.min'_le _
      ctx.successorVertex htargetCandidate
  have hactualActive :
      post.edgeSuccessor ctx.predecessorEdge ∈
        post.state.active :=
    r322AnalyticSuccessorVertex_mem_active
      post.state
      (r322AnalyticEdgeLeftVertex
        ctx.predecessorEdge)
      (by
        change ctx.predecessorEdge.val < 2 * q - 1
        exact ctx.predecessorEdge.isLt)
  have hactualParts :
      post.edgeSuccessor ctx.predecessorEdge ∈
        res.state.active \ step.2 := by
    rw [← res.afterProper_active
      step suffix hremaining hproper]
    exact hactualActive
  have hactualPreActive :
      post.edgeSuccessor ctx.predecessorEdge ∈
        res.state.active :=
    (Finset.mem_sdiff.mp hactualParts).1
  have hactualNotBlock :
      post.edgeSuccessor ctx.predecessorEdge ∉ step.2 :=
    (Finset.mem_sdiff.mp hactualParts).2
  have hstrict :
      r322AnalyticEdgeLeftVertex ctx.predecessorEdge <
        post.edgeSuccessor ctx.predecessorEdge :=
    r322AnalyticSuccessorVertex_gt
      post.state
      (r322AnalyticEdgeLeftVertex
        ctx.predecessorEdge)
      (by
        change ctx.predecessorEdge.val < 2 * q - 1
        exact ctx.predecessorEdge.isLt)
  have hlower :
      ctx.successorVertex ≤
        post.edgeSuccessor ctx.predecessorEdge := by
    by_contra hnot
    have hactualLtTarget :
        post.edgeSuccessor ctx.predecessorEdge <
          ctx.successorVertex :=
      lt_of_not_ge hnot
    by_cases hbefore :
        post.edgeSuccessor ctx.predecessorEdge <
          ctx.step.1.1
    · have hlePred :=
        r322AnalyticPredecessorVertex_maximal
          ctx.state ctx.step ctx.bounds.1
          (post.edgeSuccessor ctx.predecessorEdge)
          hactualPreActive hbefore
      rw [R322AnalyticProperStepContext.predecessorEdge,
        r322AnalyticEdgeLeftVertex_predecessorEdge] at hstrict
      exact (not_lt_of_ge hlePred) hstrict
    · have hleftLe :
          ctx.step.1.1 ≤
            post.edgeSuccessor ctx.predecessorEdge :=
        le_of_not_gt hbefore
      by_cases hright :
          post.edgeSuccessor ctx.predecessorEdge ≤
            ctx.step.1.2
      · apply hactualNotBlock
        change
          post.edgeSuccessor ctx.predecessorEdge ∈
            ctx.step.2
        rw [
          r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
            ctx.pairing ctx.state.processed ctx.suffix
            ctx.step ctx.schedule_eq]
        exact Finset.mem_inter.mpr
          ⟨hactualPreActive,
            Finset.mem_Icc.mpr ⟨hleftLe, hright⟩⟩
      · have hrightLt :
            ctx.step.1.2 <
              post.edgeSuccessor ctx.predecessorEdge :=
          lt_of_not_ge hright
        have hactualCandidate :
            post.edgeSuccessor ctx.predecessorEdge ∈
              r322AnalyticSuccessorCandidates
                ctx.state ctx.step.1.2 :=
          Finset.mem_filter.mpr
            ⟨hactualPreActive, hrightLt⟩
        have htargetLe :
            ctx.successorVertex ≤
              post.edgeSuccessor ctx.predecessorEdge := by
          unfold R322AnalyticProperStepContext.successorVertex
            r322AnalyticSuccessorVertex
          exact Finset.min'_le _
            (post.edgeSuccessor ctx.predecessorEdge)
            hactualCandidate
        exact (not_lt_of_ge htargetLe) hactualLtTarget
  exact le_antisymm hupper hlower

/-- The updated predecessor is active in the post-state and is not reserved
for a later signed-difference slot. -/
theorem afterProper_predecessor_chain_factor
    (x : Fin (2 * q) → T4) :
    (res.afterProper step suffix
        hremaining hproper).residualChainEdgeFactor x
        (res.properStepContext
          step suffix hremaining hproper).predecessorEdge =
      (res.afterProper step suffix
        hremaining hproper).state.edges
          (res.properStepContext
            step suffix hremaining hproper).predecessorEdge
          (x (r322AnalyticEdgeLeftVertex
              (res.properStepContext
                step suffix hremaining hproper).predecessorEdge) -
            x (res.properStepContext
              step suffix hremaining hproper).successorVertex) := by
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  let post :=
    res.afterProper
      step suffix hremaining hproper
  have hpredActive :
      r322AnalyticEdgeLeftVertex ctx.predecessorEdge ∈
        post.state.active := by
    rw [res.afterProper_active
      step suffix hremaining hproper]
    apply Finset.mem_sdiff.mpr
    constructor
    · rw [R322AnalyticProperStepContext.predecessorEdge,
        r322AnalyticEdgeLeftVertex_predecessorEdge]
      exact
        r322AnalyticPredecessorVertex_mem_active
          ctx.state ctx.step ctx.bounds.1
    · rw [R322AnalyticProperStepContext.predecessorEdge,
        r322AnalyticEdgeLeftVertex_predecessorEdge]
      exact ctx.predecessorVertex_not_mem_step
  have hpredLtLeft :
      r322AnalyticEdgeLeftVertex ctx.predecessorEdge <
        ctx.step.1.1 := by
    rw [R322AnalyticProperStepContext.predecessorEdge,
      r322AnalyticEdgeLeftVertex_predecessorEdge]
    exact
      r322AnalyticPredecessorVertex_lt_left
        ctx.state ctx.step ctx.bounds.1
  have hstepLt :
      ctx.step.1.1 < ctx.step.1.2 :=
    extract_mem_fst_lt_snd
      ctx.pairing ctx.step.1
      (r322AnalyticSchedule_endpoint_mem_extract
        ctx.pairing ctx.step_mem_schedule)
  have hnotSuffix :
      ctx.predecessorEdge.val ∉
        post.remainingRightValues := by
    unfold remainingRightValues
    change
      ctx.predecessorEdge.val ∉
        suffix.map (fun later => later.1.2.val)
    intro hmem
    rcases List.mem_map.mp hmem with
      ⟨later, hlater, hval⟩
    have hcurrentLater :
        ctx.step.1.2 < later.1.2 :=
      res.properStep_right_lt_suffix_right
        step suffix hremaining hproper later hlater
    change later.1.2.val =
      ctx.predecessorEdge.val at hval
    change ctx.predecessorEdge.val <
      ctx.step.1.1.val at hpredLtLeft
    change ctx.step.1.1.val <
      ctx.step.1.2.val at hstepLt
    change ctx.step.1.2.val <
      later.1.2.val at hcurrentLater
    omega
  unfold residualChainEdgeFactor
  rw [if_pos hpredActive, if_neg hnotSuffix,
    res.afterProper_predecessor_successor_eq
      step suffix hremaining hproper]

/-- The first coordinate in the increasing current-block enumeration is
the selected left endpoint. -/
theorem properStep_blockOrderIso_zero :
    ((res.properStepContext
        step suffix hremaining hproper).blockOrderIso
      ⟨0, by
        have hn :=
          (res.properStepContext
            step suffix hremaining hproper).one_le_blockOrder
        omega⟩).1 =
      step.1.1 := by
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      ctx.pairing ctx.step ctx.step_mem_schedule
  let leftInBlock : ctx.step.2 :=
    ⟨ctx.step.1.1, haligned.1⟩
  obtain ⟨j, hj⟩ :=
    ctx.blockOrderIso.surjective leftInBlock
  have hzeroLe :
      (⟨0, by
        have hn := ctx.one_le_blockOrder
        omega⟩ :
        Fin (2 * residualBlockOrder ctx.step.2)) ≤ j := by
    change 0 ≤ j.val
    omega
  have hfirstLe :
      (ctx.blockOrderIso
        ⟨0, by
          have hn := ctx.one_le_blockOrder
          omega⟩).1 ≤
        ctx.step.1.1 := by
    have hmono :=
      ctx.blockOrderIso.monotone hzeroLe
    rw [hj] at hmono
    exact hmono
  have hleftLe :
      ctx.step.1.1 ≤
        (ctx.blockOrderIso
          ⟨0, by
            have hn := ctx.one_le_blockOrder
            omega⟩).1 :=
    (haligned.2.2 _
      (ctx.blockOrderIso
        ⟨0, by
          have hn := ctx.one_le_blockOrder
          omega⟩).2).1
  exact le_antisymm hfirstLe hleftLe

/-- Before deletion, the sparse successor of the predecessor slot is the
first coordinate of the current block. -/
theorem edgeSuccessor_predecessor_eq_step_left :
    res.edgeSuccessor
        (res.properStepContext
          step suffix hremaining hproper).predecessorEdge =
      step.1.1 := by
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      ctx.pairing ctx.step ctx.step_mem_schedule
  have hleftActive :
      ctx.step.1.1 ∈ ctx.state.active := by
    have hblock :
        ctx.step.1.1 ∈ ctx.step.2 :=
      haligned.1
    rw [
      r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
        ctx.pairing ctx.state.processed ctx.suffix
        ctx.step ctx.schedule_eq] at hblock
    exact (Finset.mem_inter.mp hblock).1
  have hpredLt :
      r322AnalyticEdgeLeftVertex ctx.predecessorEdge <
        ctx.step.1.1 := by
    rw [R322AnalyticProperStepContext.predecessorEdge,
      r322AnalyticEdgeLeftVertex_predecessorEdge]
    exact
      r322AnalyticPredecessorVertex_lt_left
        ctx.state ctx.step ctx.bounds.1
  unfold edgeSuccessor r322AnalyticSuccessorVertex
  rw [Finset.min'_eq_iff]
  constructor
  · exact Finset.mem_filter.mpr
      ⟨hleftActive, hpredLt⟩
  · intro candidate hcand
    have hactive :=
      (Finset.mem_filter.mp hcand).1
    have hpredCandidate :=
      (Finset.mem_filter.mp hcand).2
    by_contra hnot
    have hcandLeft :
        candidate < ctx.step.1.1 :=
      lt_of_not_ge hnot
    have hlePred :=
      r322AnalyticPredecessorVertex_maximal
        ctx.state ctx.step ctx.bounds.1
        candidate hactive hcandLeft
    rw [R322AnalyticProperStepContext.predecessorEdge,
      r322AnalyticEdgeLeftVertex_predecessorEdge] at hpredCandidate
    exact (not_lt_of_ge hlePred) hpredCandidate

/-- The pre-update predecessor factor is the incoming edge of the actual
ambient local integrand. -/
theorem residualChainEdgeFactor_predecessor_eq
    (x : Fin (2 * q) → T4) :
    res.residualChainEdgeFactor x
        (res.properStepContext
          step suffix hremaining hproper).predecessorEdge =
      res.state.edges
          (res.properStepContext
            step suffix hremaining hproper).predecessorEdge
          ((res.properStepContext
              step suffix hremaining hproper).predecessorPoint x -
            (res.properStepContext
              step suffix hremaining hproper).standardBlockTuple x
              ⟨0, by
                have hn :=
                  (res.properStepContext
                    step suffix hremaining hproper).one_le_blockOrder
                omega⟩) := by
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  have hctxStep : ctx.step = step := rfl
  have hpredActive :
      r322AnalyticEdgeLeftVertex ctx.predecessorEdge ∈
        res.state.active := by
    rw [R322AnalyticProperStepContext.predecessorEdge,
      r322AnalyticEdgeLeftVertex_predecessorEdge]
    exact
      r322AnalyticPredecessorVertex_mem_active
        ctx.state ctx.step ctx.bounds.1
  have hpredLt :
      r322AnalyticEdgeLeftVertex ctx.predecessorEdge <
        ctx.step.1.1 := by
    rw [R322AnalyticProperStepContext.predecessorEdge,
      r322AnalyticEdgeLeftVertex_predecessorEdge]
    exact
      r322AnalyticPredecessorVertex_lt_left
        ctx.state ctx.step ctx.bounds.1
  have hstepLt :
      ctx.step.1.1 < ctx.step.1.2 :=
    extract_mem_fst_lt_snd
      ctx.pairing ctx.step.1
      (r322AnalyticSchedule_endpoint_mem_extract
        ctx.pairing ctx.step_mem_schedule)
  have hnotRemaining :
      ctx.predecessorEdge.val ∉
        res.remainingRightValues := by
    unfold remainingRightValues
    rw [hremaining]
    simp only [List.map_cons, List.mem_cons]
    intro hmem
    rcases hmem with hcurrent | hlater
    · have hcurrent' :
          ctx.predecessorEdge.val =
            ctx.step.1.2.val := by
        simpa only [ctx, properStepContext] using hcurrent
      change ctx.predecessorEdge.val <
        ctx.step.1.1.val at hpredLt
      change ctx.step.1.1.val <
        ctx.step.1.2.val at hstepLt
      omega
    · obtain ⟨later, hlaterMem, hval⟩ :=
        List.mem_map.mp hlater
      have hright :=
        res.properStep_right_lt_suffix_right
          step suffix hremaining hproper
          later hlaterMem
      change later.1.2.val =
        ctx.predecessorEdge.val at hval
      change ctx.predecessorEdge.val <
        ctx.step.1.1.val at hpredLt
      change ctx.step.1.1.val <
        ctx.step.1.2.val at hstepLt
      change ctx.step.1.2.val <
        later.1.2.val at hright
      omega
  unfold residualChainEdgeFactor
  rw [if_pos hpredActive, if_neg hnotRemaining,
    res.edgeSuccessor_predecessor_eq_step_left
      step suffix hremaining hproper]
  unfold R322AnalyticProperStepContext.predecessorPoint
    R322AnalyticProperStepContext.standardBlockTuple
  rw [res.properStep_blockOrderIso_zero
    step suffix hremaining hproper]
  rw [R322AnalyticProperStepContext.predecessorEdge,
    r322AnalyticEdgeLeftVertex_predecessorEdge]

/-- On an internal current-block edge, the sparse successor is the next
coordinate in the increasing block enumeration. -/
theorem edgeSuccessor_internalEdge_eq
    (j : Fin
      (2 * residualBlockOrder step.2 - 1)) :
    let ctx :=
      res.properStepContext
        step suffix hremaining hproper
    let jnext :
        Fin (2 * residualBlockOrder step.2) :=
      ⟨j.val + 1, by
        have hj := j.isLt
        omega⟩
    res.edgeSuccessor (ctx.internalEdge j) =
      (ctx.blockOrderIso jnext).1 := by
  dsimp only
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  have hjbound :
      j.val <
        2 * residualBlockOrder ctx.step.2 - 1 := by
    simpa only [ctx, properStepContext] using j.isLt
  let jleft :
      Fin (2 * residualBlockOrder ctx.step.2) :=
    ⟨j.val, by
      have hn := ctx.one_le_blockOrder
      exact lt_trans hjbound (by omega)⟩
  let jnext :
      Fin (2 * residualBlockOrder ctx.step.2) :=
    ⟨j.val + 1, by
      have hn := ctx.one_le_blockOrder
      omega⟩
  have hjlt : jleft < jnext := by
    change j.val < j.val + 1
    omega
  have hcoordLt :
      (ctx.blockOrderIso jleft).1 <
        (ctx.blockOrderIso jnext).1 :=
    ctx.blockOrderIso.strictMono hjlt
  have hblock :
      ctx.step.2 =
        ctx.state.active ∩
          Finset.Icc ctx.step.1.1 ctx.step.1.2 :=
    r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
      ctx.pairing ctx.state.processed ctx.suffix
      ctx.step ctx.schedule_eq
  have htargetActive :
      (ctx.blockOrderIso jnext).1 ∈
        ctx.state.active := by
    let target : Fin (2 * q) :=
      (ctx.blockOrderIso jnext).1
    have hmem : target ∈ ctx.step.2 :=
      (ctx.blockOrderIso jnext).2
    have hinter :
        target ∈
          ctx.state.active ∩
            Finset.Icc ctx.step.1.1 ctx.step.1.2 := by
      exact hblock ▸ hmem
    exact (Finset.mem_inter.mp hinter).1
  have hleftVertex :
      r322AnalyticEdgeLeftVertex
          (ctx.internalEdge j) =
        (ctx.blockOrderIso jleft).1 := by
    apply Fin.ext
    rfl
  unfold edgeSuccessor r322AnalyticSuccessorVertex
  rw [Finset.min'_eq_iff]
  constructor
  · apply Finset.mem_filter.mpr
    rw [hleftVertex]
    exact ⟨htargetActive, hcoordLt⟩
  · intro candidate hcand
    have hactive :=
      (Finset.mem_filter.mp hcand).1
    have hedgeLt :=
      (Finset.mem_filter.mp hcand).2
    rw [hleftVertex] at hedgeLt
    by_cases hiright :
        candidate ≤ ctx.step.1.2
    · have hleftLe :
          ctx.step.1.1 ≤ candidate := by
        have hblockLeft :=
          (r322AnalyticSchedule_forall_aligned
            ctx.pairing ctx.step ctx.step_mem_schedule).2.2
              (ctx.blockOrderIso jleft).1
              (ctx.blockOrderIso jleft).2 |>.1
        exact hblockLeft.trans hedgeLt.le
      have hiBlock : candidate ∈ ctx.step.2 := by
        rw [hblock]
        exact Finset.mem_inter.mpr
          ⟨hactive,
            Finset.mem_Icc.mpr
              ⟨hleftLe, hiright⟩⟩
      let ji :=
        ctx.blockOrderIso.symm ⟨candidate, hiBlock⟩
      have hjleftLtJi : jleft < ji := by
        apply ctx.blockOrderIso.lt_iff_lt.mp
        rw [ctx.blockOrderIso.apply_symm_apply
          ⟨candidate, hiBlock⟩]
        exact hedgeLt
      have hjnextLeJi : jnext ≤ ji := by
        change j.val + 1 ≤ ji.val
        change j.val < ji.val at hjleftLtJi
        omega
      have hmono :=
        ctx.blockOrderIso.monotone hjnextLeJi
      rw [ctx.blockOrderIso.apply_symm_apply
        ⟨candidate, hiBlock⟩] at hmono
      exact hmono
    · have hrightLt :
          ctx.step.1.2 < candidate :=
        lt_of_not_ge hiright
      have htargetLeRight :
          (ctx.blockOrderIso jnext).1 ≤
            ctx.step.1.2 :=
        (r322AnalyticSchedule_forall_aligned
          ctx.pairing ctx.step ctx.step_mem_schedule).2.2
            (ctx.blockOrderIso jnext).1
            (ctx.blockOrderIso jnext).2 |>.2
      exact htargetLeRight.trans hrightLt.le

/-- Every current internal ordinary chain factor is exactly the
corresponding primitive-chain factor in standard block coordinates. -/
theorem residualChainEdgeFactor_internal_eq
    (x : Fin (2 * q) → T4)
    (j : Fin
      (2 * residualBlockOrder step.2 - 1)) :
    let ctx :=
      res.properStepContext
        step suffix hremaining hproper
    res.residualChainEdgeFactor x
        (ctx.internalEdge j) =
      ctx.internalEdges j
        (ctx.standardBlockTuple x
            (primitiveEdgeLeft
              (residualBlockOrder step.2)
              ctx.one_le_blockOrder j) -
          ctx.standardBlockTuple x
            (primitiveEdgeRight
              (residualBlockOrder step.2)
              ctx.one_le_blockOrder j)) := by
  dsimp only
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  have hjbound :
      j.val <
        2 * residualBlockOrder ctx.step.2 - 1 := by
    simpa only [ctx, properStepContext] using j.isLt
  have hactive :
      r322AnalyticEdgeLeftVertex
          (ctx.internalEdge j) ∈
        res.state.active := by
    change ctx.internalLeftVertex j ∈
      ctx.state.active
    exact ctx.internalLeftVertex_mem_active j
  have hinternalLt :
      (ctx.internalEdge j).val <
        ctx.outgoingEdge.val := by
    change
      (ctx.blockOrderIso
        ⟨j.val, by
          have hn := ctx.one_le_blockOrder
          exact lt_trans hjbound (by omega)⟩).1.val <
        ctx.step.1.2.val
    have hjlast :
        (⟨j.val, by
          have hn := ctx.one_le_blockOrder
          exact lt_trans hjbound (by omega)⟩ :
          Fin (2 * residualBlockOrder ctx.step.2)) <
        primitiveLast
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder := by
      change j.val <
        2 * residualBlockOrder ctx.step.2 - 1
      exact hjbound
    have hmono :=
      ctx.blockOrderIso.strictMono hjlast
    change
      (ctx.blockOrderIso
        ⟨j.val, by
          have hn := ctx.one_le_blockOrder
          exact lt_trans hjbound (by omega)⟩).1 <
        (ctx.blockOrderIso
          (primitiveLast
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder)).1 at hmono
    rw [ctx.blockOrderIso_last] at hmono
    exact hmono
  have hnotRemaining :
      (ctx.internalEdge j).val ∉
        res.remainingRightValues := by
    unfold remainingRightValues
    rw [hremaining]
    simp only [List.map_cons, List.mem_cons]
    intro hmem
    rcases hmem with hcurrent | hlater
    · have hcurrent' :
          (ctx.internalEdge j).val =
            ctx.step.1.2.val := by
        simpa only [ctx, properStepContext] using hcurrent
      change
        (ctx.internalEdge j).val <
          ctx.step.1.2.val at hinternalLt
      omega
    · obtain ⟨later, hlaterMem, hval⟩ :=
        List.mem_map.mp hlater
      have hright :=
        res.properStep_right_lt_suffix_right
          step suffix hremaining hproper
          later hlaterMem
      change later.1.2.val =
        (ctx.internalEdge j).val at hval
      change
        (ctx.internalEdge j).val <
          ctx.step.1.2.val at hinternalLt
      change ctx.step.1.2.val <
        later.1.2.val at hright
      omega
  unfold residualChainEdgeFactor
  rw [if_pos hactive, if_neg hnotRemaining,
    res.edgeSuccessor_internalEdge_eq
      step suffix hremaining hproper j]
  unfold R322AnalyticProperStepContext.internalEdges
    R322AnalyticProperStepContext.standardBlockTuple
  rfl

/-- The current outgoing slot is reserved for the signed difference product
and contributes one to the ordinary chain. -/
theorem residualChainEdgeFactor_outgoing_eq
    (x : Fin (2 * q) → T4) :
    res.residualChainEdgeFactor x
        (res.properStepContext
          step suffix hremaining hproper).outgoingEdge =
      1 := by
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  have hctxStep : ctx.step = step := rfl
  have hactive :
      r322AnalyticEdgeLeftVertex ctx.outgoingEdge ∈
        res.state.active := by
    change ctx.step.1.2 ∈
      res.state.active
    have haligned :=
      r322AnalyticSchedule_forall_aligned
        ctx.pairing ctx.step ctx.step_mem_schedule
    have hblock : ctx.step.1.2 ∈ ctx.step.2 :=
      haligned.2.1
    rw [
      r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
        ctx.pairing ctx.state.processed ctx.suffix
        ctx.step ctx.schedule_eq] at hblock
    exact (Finset.mem_inter.mp hblock).1
  have hremainingRight :
      ctx.outgoingEdge.val ∈
        res.remainingRightValues := by
    unfold remainingRightValues
    rw [hremaining]
    simp only [List.map_cons, List.mem_cons]
    left
    unfold R322AnalyticProperStepContext.outgoingEdge
      r322AnalyticOutgoingEdge
    exact congrArg (fun s => s.1.2.val) hctxStep
  unfold residualChainEdgeFactor
  rw [if_pos hactive, if_pos hremainingRight]

/-- Ordinary chain slots which remain genuinely exterior to the current
proper block and its incoming predecessor slot. -/
def properOuterChainProduct
    (x : Fin (2 * q) → T4) : ℝ :=
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  ∏ edge ∈
      Finset.univ \
        ({ctx.predecessorEdge} ∪ ctx.blockEdges),
    res.residualChainEdgeFactor x edge

/-- The complete exterior factor carried unchanged through the current
proper block integration. -/
def properOuterIntegrand
    (ρ : SmoothCutoff) (ε : ℝ)
    (x : Fin (2 * q) → T4) : ℝ :=
  res.properOuterChainProduct
      step suffix hremaining hproper x *
    (res.afterProper step suffix
      hremaining hproper).residualDifferenceProduct x *
    (res.afterProper step suffix
      hremaining hproper).residualPrimitiveProduct
        ρ ε x

/-- The product over the actual internal ambient slots is exactly the
primitive chain product in standard current-block coordinates. -/
theorem prod_internalEdgesFinset_residualChainEdgeFactor
    (x : Fin (2 * q) → T4) :
    let ctx :=
      res.properStepContext
        step suffix hremaining hproper
    (∏ edge ∈ ctx.internalEdgesFinset,
        res.residualChainEdgeFactor x edge) =
      primitiveChainProduct
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder ctx.internalEdges
        (ctx.standardBlockTuple x) := by
  dsimp only
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  unfold R322AnalyticProperStepContext.internalEdgesFinset
    primitiveChainProduct
  rw [Finset.prod_image
    ctx.internalEdge_injective.injOn]
  apply Finset.prod_congr rfl
  intro j _hj
  exact
    res.residualChainEdgeFactor_internal_eq
      step suffix hremaining hproper x j

/-- Exact ordinary-chain factorization at an arbitrary reachable proper
prefix: incoming edge, current internal primitive chain, and the complete
exterior chain. -/
theorem residualChainProduct_eq_local_mul_outer
    (x : Fin (2 * q) → T4) :
    let ctx :=
      res.properStepContext
        step suffix hremaining hproper
    res.residualChainProduct x =
      (res.state.edges ctx.predecessorEdge
          (ctx.predecessorPoint x -
            ctx.standardBlockTuple x
              ⟨0, by
                have hn := ctx.one_le_blockOrder
                omega⟩) *
        primitiveChainProduct
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder ctx.internalEdges
          (ctx.standardBlockTuple x)) *
        res.properOuterChainProduct
          step suffix hremaining hproper x := by
  dsimp only
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  let localSlots : Finset (Fin (2 * q - 1)) :=
    {ctx.predecessorEdge} ∪ ctx.blockEdges
  let outerSlots : Finset (Fin (2 * q - 1)) :=
    Finset.univ \ localSlots
  let f : Fin (2 * q - 1) → ℝ :=
    res.residualChainEdgeFactor x
  have hpartition :=
    Finset.prod_sdiff
      (show localSlots ⊆
        (Finset.univ : Finset (Fin (2 * q - 1))) by
          exact Finset.subset_univ localSlots)
      (f := f)
  have hlocal :
      (∏ edge ∈ localSlots, f edge) =
        res.state.edges ctx.predecessorEdge
            (ctx.predecessorPoint x -
              ctx.standardBlockTuple x
                ⟨0, by
                  have hn := ctx.one_le_blockOrder
                  omega⟩) *
          primitiveChainProduct
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder ctx.internalEdges
            (ctx.standardBlockTuple x) := by
    have hpredDisjoint :
        Disjoint ({ctx.predecessorEdge} :
          Finset (Fin (2 * q - 1))) ctx.blockEdges :=
      Finset.disjoint_singleton_left.mpr
        ctx.predecessorEdge_not_mem_blockEdges
    have hinternalDisjoint :
        Disjoint ctx.internalEdgesFinset
          ({ctx.outgoingEdge} :
            Finset (Fin (2 * q - 1))) :=
      Finset.disjoint_singleton_right.mpr
        ctx.outgoingEdge_not_mem_internalEdgesFinset
    unfold localSlots f
    rw [Finset.prod_union hpredDisjoint,
      Finset.prod_singleton,
      ← ctx.internalEdgesFinset_union_outgoing,
      Finset.prod_union hinternalDisjoint,
      Finset.prod_singleton,
      res.residualChainEdgeFactor_predecessor_eq
        step suffix hremaining hproper x,
      res.prod_internalEdgesFinset_residualChainEdgeFactor
        step suffix hremaining hproper x,
      res.residualChainEdgeFactor_outgoing_eq
        step suffix hremaining hproper x,
      mul_one]
  unfold residualChainProduct
  change
    (∏ edge : Fin (2 * q - 1), f edge) =
      _ * res.properOuterChainProduct
        step suffix hremaining hproper x
  unfold properOuterChainProduct
  change
    (∏ edge : Fin (2 * q - 1), f edge) =
      _ * ∏ edge ∈ outerSlots, f edge
  rw [← hlocal]
  have hpartition' :
      (∏ edge ∈ outerSlots, f edge) *
          (∏ edge ∈ localSlots, f edge) =
        ∏ edge : Fin (2 * q - 1), f edge := by
    simpa only [outerSlots] using hpartition
  rw [← hpartition']
  ring

/-- Away from the deleted block and its predecessor slot, removing the
current block does not alter the least sparse successor of an active left
vertex. -/
theorem afterProper_edgeSuccessor_eq_of_outer
    (edge : Fin (2 * q - 1))
    (hedge :
      edge ∈
        Finset.univ \
          ({(res.properStepContext
              step suffix hremaining hproper).predecessorEdge} ∪
            (res.properStepContext
              step suffix hremaining hproper).blockEdges))
    (hactive :
      r322AnalyticEdgeLeftVertex edge ∈
        res.state.active) :
    (res.afterProper step suffix
        hremaining hproper).edgeSuccessor edge =
      res.edgeSuccessor edge := by
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  let post :=
    res.afterProper
      step suffix hremaining hproper
  have hnotLocal :=
    (Finset.mem_sdiff.mp hedge).2
  have hnePred : edge ≠ ctx.predecessorEdge := by
    intro heq
    apply hnotLocal
    rw [heq]
    exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
  have hnotBlockEdge : edge ∉ ctx.blockEdges := by
    intro hmem
    apply hnotLocal
    exact Finset.mem_union_right _ hmem
  have hleftNotBlock :
      r322AnalyticEdgeLeftVertex edge ∉
        ctx.step.2 := by
    simpa only [ctx.mem_blockEdges_iff] using hnotBlockEdge
  have hpostLeftActive :
      r322AnalyticEdgeLeftVertex edge ∈
        post.state.active := by
    rw [res.afterProper_active
      step suffix hremaining hproper]
    exact Finset.mem_sdiff.mpr
      ⟨hactive, hleftNotBlock⟩
  have hpostSuccessorActive :
      post.edgeSuccessor edge ∈
        post.state.active :=
    r322AnalyticSuccessorVertex_mem_active
      post.state
      (r322AnalyticEdgeLeftVertex edge)
      (by
        change edge.val < 2 * q - 1
        exact edge.isLt)
  have hpostSuccessorParts :
      post.edgeSuccessor edge ∈
        res.state.active \ ctx.step.2 := by
    have hparts :
        post.edgeSuccessor edge ∈
          res.state.active \ step.2 := by
      rw [← res.afterProper_active
        step suffix hremaining hproper]
      exact hpostSuccessorActive
    simpa only [ctx, properStepContext] using hparts
  have hpostCandidatePre :
      post.edgeSuccessor edge ∈
        r322AnalyticSuccessorCandidates
          res.state
          (r322AnalyticEdgeLeftVertex edge) := by
    apply Finset.mem_filter.mpr
    refine
      ⟨(Finset.mem_sdiff.mp hpostSuccessorParts).1, ?_⟩
    exact
      r322AnalyticSuccessorVertex_gt
        post.state
        (r322AnalyticEdgeLeftVertex edge)
        (by
          change edge.val < 2 * q - 1
          exact edge.isLt)
  have hpreLePost :
      res.edgeSuccessor edge ≤
        post.edgeSuccessor edge := by
    unfold edgeSuccessor r322AnalyticSuccessorVertex
    exact Finset.min'_le _
      (post.edgeSuccessor edge) hpostCandidatePre
  have hpreSuccessorActive :
      res.edgeSuccessor edge ∈
        res.state.active :=
    r322AnalyticSuccessorVertex_mem_active
      res.state
      (r322AnalyticEdgeLeftVertex edge)
      (by
        change edge.val < 2 * q - 1
        exact edge.isLt)
  have hpreSuccessorGt :
      r322AnalyticEdgeLeftVertex edge <
        res.edgeSuccessor edge :=
    r322AnalyticSuccessorVertex_gt
      res.state
      (r322AnalyticEdgeLeftVertex edge)
      (by
        change edge.val < 2 * q - 1
        exact edge.isLt)
  have hblockEq :
      ctx.step.2 =
        res.state.active ∩
          Finset.Icc ctx.step.1.1 ctx.step.1.2 :=
    r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
      ctx.pairing ctx.state.processed ctx.suffix
      ctx.step ctx.schedule_eq
  have hleftOutside :
      r322AnalyticEdgeLeftVertex edge <
          ctx.step.1.1 ∨
        ctx.step.1.2 <
          r322AnalyticEdgeLeftVertex edge := by
    have hnotIcc :
        r322AnalyticEdgeLeftVertex edge ∉
          Finset.Icc ctx.step.1.1 ctx.step.1.2 := by
      intro hi
      apply hleftNotBlock
      rw [hblockEq]
      exact Finset.mem_inter.mpr ⟨hactive, hi⟩
    rw [Finset.mem_Icc] at hnotIcc
    omega
  have hpreSuccessorNotBlock :
      res.edgeSuccessor edge ∉ ctx.step.2 := by
    rcases hleftOutside with hbefore | hafter
    · have hleftLePred :=
        r322AnalyticPredecessorVertex_maximal
          ctx.state ctx.step ctx.bounds.1
          (r322AnalyticEdgeLeftVertex edge)
          hactive hbefore
      have hleftNePred :
          r322AnalyticEdgeLeftVertex edge ≠
            r322AnalyticEdgeLeftVertex
              ctx.predecessorEdge := by
        intro heq
        apply hnePred
        apply Fin.ext
        have hval :=
          congrArg
            (fun i : Fin (2 * q) => i.val) heq
        exact hval
      have hleftLtPred :
          r322AnalyticEdgeLeftVertex edge <
            r322AnalyticEdgeLeftVertex
              ctx.predecessorEdge :=
        lt_of_le_of_ne hleftLePred
          (by
            rw [R322AnalyticProperStepContext.predecessorEdge,
              r322AnalyticEdgeLeftVertex_predecessorEdge]
            exact hleftNePred)
      have hpredActive :
          r322AnalyticEdgeLeftVertex ctx.predecessorEdge ∈
            res.state.active := by
        rw [R322AnalyticProperStepContext.predecessorEdge,
          r322AnalyticEdgeLeftVertex_predecessorEdge]
        exact
          r322AnalyticPredecessorVertex_mem_active
            ctx.state ctx.step ctx.bounds.1
      have hpredCandidate :
          r322AnalyticEdgeLeftVertex ctx.predecessorEdge ∈
            r322AnalyticSuccessorCandidates
              res.state
              (r322AnalyticEdgeLeftVertex edge) :=
        Finset.mem_filter.mpr
          ⟨hpredActive, hleftLtPred⟩
      have hsuccLePred :
          res.edgeSuccessor edge ≤
            r322AnalyticEdgeLeftVertex
              ctx.predecessorEdge := by
        unfold edgeSuccessor r322AnalyticSuccessorVertex
        exact Finset.min'_le _
          (r322AnalyticEdgeLeftVertex
            ctx.predecessorEdge) hpredCandidate
      have hsuccLtLeft :
          res.edgeSuccessor edge < ctx.step.1.1 := by
        exact hsuccLePred.trans_lt
          (by
            rw [R322AnalyticProperStepContext.predecessorEdge,
              r322AnalyticEdgeLeftVertex_predecessorEdge]
            exact
              r322AnalyticPredecessorVertex_lt_left
                ctx.state ctx.step ctx.bounds.1)
      intro hmem
      rw [hblockEq] at hmem
      have hleftLe :=
        (Finset.mem_Icc.mp
          (Finset.mem_inter.mp hmem).2).1
      exact (not_lt_of_ge hleftLe) hsuccLtLeft
    · have hsuccRight :
          ctx.step.1.2 <
            res.edgeSuccessor edge :=
        hafter.trans hpreSuccessorGt
      intro hmem
      rw [hblockEq] at hmem
      have hrightLe :=
        (Finset.mem_Icc.mp
          (Finset.mem_inter.mp hmem).2).2
      exact (not_lt_of_ge hrightLe) hsuccRight
  have hpreSuccessorPostActive :
      res.edgeSuccessor edge ∈ post.state.active := by
    rw [res.afterProper_active
      step suffix hremaining hproper]
    exact Finset.mem_sdiff.mpr
      ⟨hpreSuccessorActive,
        hpreSuccessorNotBlock⟩
  have hpreCandidatePost :
      res.edgeSuccessor edge ∈
        r322AnalyticSuccessorCandidates
          post.state
          (r322AnalyticEdgeLeftVertex edge) :=
    Finset.mem_filter.mpr
      ⟨hpreSuccessorPostActive, hpreSuccessorGt⟩
  have hpostLePre :
      post.edgeSuccessor edge ≤
        res.edgeSuccessor edge := by
    unfold edgeSuccessor r322AnalyticSuccessorVertex
    exact Finset.min'_le _
      (res.edgeSuccessor edge) hpreCandidatePost
  exact le_antisymm hpostLePre hpreLePost

/-- Exterior slots see the same reserved suffix-right values before and
after removal of the current head; the only deleted value is the outgoing
slot, which is not exterior. -/
theorem outerEdge_remainingRightValues_iff
    (edge : Fin (2 * q - 1))
    (hedge :
      edge ∈
        Finset.univ \
          ({(res.properStepContext
              step suffix hremaining hproper).predecessorEdge} ∪
            (res.properStepContext
              step suffix hremaining hproper).blockEdges)) :
    edge.val ∈ res.remainingRightValues ↔
      edge.val ∈
        (res.afterProper step suffix
          hremaining hproper).remainingRightValues := by
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  have hnotLocal :=
    (Finset.mem_sdiff.mp hedge).2
  have hnotOutgoing :
      edge ≠ ctx.outgoingEdge := by
    intro heq
    apply hnotLocal
    rw [heq]
    exact Finset.mem_union_right _
      ctx.outgoingEdge_mem_blockEdges
  unfold remainingRightValues
  rw [hremaining]
  change
    edge.val ∈
        (step :: suffix).map
          (fun later => later.1.2.val) ↔
      edge.val ∈
        suffix.map
          (fun later => later.1.2.val)
  simp only [List.map_cons, List.mem_cons]
  constructor
  · intro hmem
    rcases hmem with hcurrent | hlater
    · exfalso
      apply hnotOutgoing
      apply Fin.ext
      unfold R322AnalyticProperStepContext.outgoingEdge
        r322AnalyticOutgoingEdge
      exact hcurrent
    · exact hlater
  · exact Or.inr

/-- Every exterior ordinary chain factor is pointwise unchanged by the
current proper state update. -/
theorem afterProper_residualChainEdgeFactor_eq_of_outer
    (x : Fin (2 * q) → T4)
    (edge : Fin (2 * q - 1))
    (hedge :
      edge ∈
        Finset.univ \
          ({(res.properStepContext
              step suffix hremaining hproper).predecessorEdge} ∪
            (res.properStepContext
              step suffix hremaining hproper).blockEdges)) :
    (res.afterProper step suffix
        hremaining hproper).residualChainEdgeFactor x edge =
      res.residualChainEdgeFactor x edge := by
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  let post :=
    res.afterProper
      step suffix hremaining hproper
  have hnotLocal :=
    (Finset.mem_sdiff.mp hedge).2
  have hnePred : edge ≠ ctx.predecessorEdge := by
    intro heq
    apply hnotLocal
    rw [heq]
    exact Finset.mem_union_left _
      (Finset.mem_singleton_self _)
  have hnotBlockEdge : edge ∉ ctx.blockEdges := by
    intro hmem
    apply hnotLocal
    exact Finset.mem_union_right _ hmem
  have hleftNotBlock :
      r322AnalyticEdgeLeftVertex edge ∉
        ctx.step.2 := by
    simpa only [ctx.mem_blockEdges_iff] using hnotBlockEdge
  by_cases hactive :
      r322AnalyticEdgeLeftVertex edge ∈
        res.state.active
  · have hpostActive :
        r322AnalyticEdgeLeftVertex edge ∈
          post.state.active := by
      rw [res.afterProper_active
        step suffix hremaining hproper]
      exact Finset.mem_sdiff.mpr
        ⟨hactive, hleftNotBlock⟩
    have hreserved :=
      res.outerEdge_remainingRightValues_iff
        step suffix hremaining hproper edge hedge
    by_cases hpreReserved :
        edge.val ∈ res.remainingRightValues
    · have hpostReserved :=
        hreserved.mp hpreReserved
      unfold residualChainEdgeFactor
      rw [if_pos hpostActive,
        if_pos hpostReserved,
        if_pos hactive,
        if_pos hpreReserved]
    · have hpostReserved :
          edge.val ∉ post.remainingRightValues :=
        fun hmem => hpreReserved (hreserved.mpr hmem)
      have hedgeEq :
          post.state.edges edge =
            res.state.edges edge := by
        change
          (ctx.nextState ρ lam ε).edges edge =
            ctx.state.edges edge
        exact ctx.nextState_edges_eq_of_ne
          ρ lam ε edge hnePred
      unfold residualChainEdgeFactor
      rw [if_pos hpostActive,
        if_neg hpostReserved,
        if_pos hactive,
        if_neg hpreReserved,
        hedgeEq,
        res.afterProper_edgeSuccessor_eq_of_outer
          step suffix hremaining hproper
          edge hedge hactive]
  · have hpostInactive :
        r322AnalyticEdgeLeftVertex edge ∉
          post.state.active := by
      intro hmem
      rw [res.afterProper_active
        step suffix hremaining hproper] at hmem
      exact hactive (Finset.mem_sdiff.mp hmem).1
    unfold residualChainEdgeFactor
    rw [if_neg hpostInactive, if_neg hactive]

/-- Slots based in the deleted current block are inactive in the post-state,
so their ordinary post-chain factor is one. -/
theorem afterProper_residualChainEdgeFactor_eq_one_of_mem_blockEdges
    (x : Fin (2 * q) → T4)
    (edge : Fin (2 * q - 1))
    (hedge :
      edge ∈
        (res.properStepContext
          step suffix hremaining hproper).blockEdges) :
    (res.afterProper step suffix
        hremaining hproper).residualChainEdgeFactor x edge =
      1 := by
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  let post :=
    res.afterProper
      step suffix hremaining hproper
  have hleftBlock :
      r322AnalyticEdgeLeftVertex edge ∈
        ctx.step.2 :=
    ctx.mem_blockEdges_iff.mp hedge
  have hpostInactive :
      r322AnalyticEdgeLeftVertex edge ∉
        post.state.active := by
    rw [res.afterProper_active
      step suffix hremaining hproper]
    exact fun hmem =>
      (Finset.mem_sdiff.mp hmem).2 hleftBlock
  unfold residualChainEdgeFactor
  rw [if_neg hpostInactive]

/-- Exact post-update ordinary-chain ledger: the newly collapsed
predecessor edge is pulled out once, and the exterior chain is literally the
same product as before the update. -/
theorem afterProper_residualChainProduct_eq_updated_mul_outer
    (x : Fin (2 * q) → T4) :
    let ctx :=
      res.properStepContext
        step suffix hremaining hproper
    let post :=
      res.afterProper
        step suffix hremaining hproper
    post.residualChainProduct x =
      post.state.edges ctx.predecessorEdge
          (x (r322AnalyticEdgeLeftVertex
                ctx.predecessorEdge) -
            x ctx.successorVertex) *
        res.properOuterChainProduct
          step suffix hremaining hproper x := by
  dsimp only
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  let post :=
    res.afterProper
      step suffix hremaining hproper
  let localSlots : Finset (Fin (2 * q - 1)) :=
    {ctx.predecessorEdge} ∪ ctx.blockEdges
  let outerSlots : Finset (Fin (2 * q - 1)) :=
    Finset.univ \ localSlots
  let fPost : Fin (2 * q - 1) → ℝ :=
    post.residualChainEdgeFactor x
  let fPre : Fin (2 * q - 1) → ℝ :=
    res.residualChainEdgeFactor x
  have hpartition :=
    Finset.prod_sdiff
      (show localSlots ⊆
        (Finset.univ : Finset (Fin (2 * q - 1))) by
          exact Finset.subset_univ localSlots)
      (f := fPost)
  have hblockProduct :
      (∏ edge ∈ ctx.blockEdges, fPost edge) = 1 := by
    apply Finset.prod_eq_one
    intro edge hedge
    exact
      res.afterProper_residualChainEdgeFactor_eq_one_of_mem_blockEdges
        step suffix hremaining hproper x edge hedge
  have hlocal :
      (∏ edge ∈ localSlots, fPost edge) =
        post.state.edges ctx.predecessorEdge
          (x (r322AnalyticEdgeLeftVertex
                ctx.predecessorEdge) -
            x ctx.successorVertex) := by
    have hpredDisjoint :
        Disjoint ({ctx.predecessorEdge} :
          Finset (Fin (2 * q - 1))) ctx.blockEdges :=
      Finset.disjoint_singleton_left.mpr
        ctx.predecessorEdge_not_mem_blockEdges
    unfold localSlots
    rw [Finset.prod_union hpredDisjoint,
      Finset.prod_singleton, hblockProduct,
      mul_one]
    exact
      res.afterProper_predecessor_chain_factor
        step suffix hremaining hproper x
  have houter :
      (∏ edge ∈ outerSlots, fPost edge) =
        ∏ edge ∈ outerSlots, fPre edge := by
    apply Finset.prod_congr rfl
    intro edge hedge
    exact
      res.afterProper_residualChainEdgeFactor_eq_of_outer
        step suffix hremaining hproper x edge
        (by
          simpa only [outerSlots, localSlots] using hedge)
  unfold residualChainProduct
  change
    (∏ edge : Fin (2 * q - 1), fPost edge) =
      _ * res.properOuterChainProduct
        step suffix hremaining hproper x
  unfold properOuterChainProduct
  change
    (∏ edge : Fin (2 * q - 1), fPost edge) =
      _ * ∏ edge ∈ outerSlots, fPre edge
  rw [← houter, ← hlocal]
  have hpartition' :
      (∏ edge ∈ outerSlots, fPost edge) *
          (∏ edge ∈ localSlots, fPost edge) =
        ∏ edge : Fin (2 * q - 1), fPost edge := by
    simpa only [outerSlots] using hpartition
  rw [← hpartition']
  ring

/-- The current residual head index is the actual block index used by the
proper-step context. -/
theorem remainingBlockIndex_zero_eq_contextBlockIndex :
    res.remainingBlockIndex
        ⟨0, by
          rw [hremaining]
          simp⟩ =
      (res.properStepContext
        step suffix hremaining hproper).blockIndex := by
  apply Subtype.ext
  rw [res.remainingBlockIndex_zero_val
    step suffix hremaining]
  dsimp only [properStepContext,
    R322AnalyticProperStepContext.blockIndex]

/-- The current primitive coordinate in the residual product is exactly the
standard-block covariance sum in the ambient local factor. -/
theorem currentPrimitiveSum_eq_standardBlock
    (ρ : SmoothCutoff) (ε : ℝ)
    (x : Fin (2 * q) → T4) :
    r322ExtractionBlockPrimitiveSum ρ ε
        res.pairing
        (res.remainingBlockIndex
          ⟨0, by
            rw [hremaining]
            simp⟩) x =
      let ctx :=
        res.properStepContext
          step suffix hremaining hproper
      ∑ κB :
          {κ : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κ ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)},
        primitiveCovarianceProduct ρ ε
          (residualBlockOrder ctx.step.2) κB.1
          (ctx.standardBlockTuple x) := by
  dsimp only
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  rw [res.remainingBlockIndex_zero_eq_contextBlockIndex
    step suffix hremaining hproper]
  exact ctx.extractionBlockPrimitiveSum_eq_standardBlock
    ρ ε x

/-- The current signed residual difference is the outgoing term in standard
current-block coordinates. -/
theorem residualStepDifference_current_eq_standardBlock
    (x : Fin (2 * q) → T4) :
    let ctx :=
      res.properStepContext
        step suffix hremaining hproper
    res.residualStepDifference x step =
      ctx.state.edges ctx.outgoingEdge
          (ctx.standardBlockTuple x
              (primitiveLast
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder) -
            ctx.successorPoint x) -
        ctx.state.edges ctx.outgoingEdge
          (ctx.standardBlockTuple x
              ⟨0, by
                have hn := ctx.one_le_blockOrder
                omega⟩ -
            ctx.successorPoint x) := by
  dsimp only
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  have hlast :
      (ctx.blockOrderIso
        (primitiveLast
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder)).1 =
        step.1.2 := by
    simpa only [ctx, properStepContext] using
      ctx.blockOrderIso_last
  have hzero :
      (ctx.blockOrderIso
        ⟨0, by
          have hn := ctx.one_le_blockOrder
          omega⟩).1 =
        step.1.1 :=
    res.properStep_blockOrderIso_zero
      step suffix hremaining hproper
  rw [res.residualStepDifference_current_eq
    step suffix hremaining hproper x]
  unfold R322AnalyticProperStepContext.standardBlockTuple
    R322AnalyticProperStepContext.successorPoint
  rw [hlast, hzero]
  rfl

/-- Pointwise local-times-outer factorization of the complete pre-update
residual integrand at an arbitrary reachable proper prefix. -/
theorem residualIntegrand_eq_ambientLocal_mul_outer
    (ρ : SmoothCutoff) (ε : ℝ)
    (x : Fin (2 * q) → T4) :
    let ctx :=
      res.properStepContext
        step suffix hremaining hproper
    res.residualIntegrand ρ ε x =
      ctx.ambientLocalIntegrand ρ ε x *
        res.properOuterIntegrand
          step suffix hremaining hproper ρ ε x := by
  dsimp only
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  unfold residualIntegrand properOuterIntegrand
    R322AnalyticProperStepContext.ambientLocalIntegrand
  rw [
    res.residualChainProduct_eq_local_mul_outer
      step suffix hremaining hproper x,
    res.residualDifferenceProduct_eq_current_mul_afterProper
      step suffix hremaining hproper x,
    res.residualPrimitiveProduct_eq_current_mul_afterProper
      step suffix hremaining hproper ρ ε x,
    res.residualStepDifference_current_eq_standardBlock
      step suffix hremaining hproper x,
    res.currentPrimitiveSum_eq_standardBlock
      step suffix hremaining hproper ρ ε x]
  let incoming : ℝ :=
    ctx.state.edges ctx.predecessorEdge
      (ctx.predecessorPoint x -
        ctx.standardBlockTuple x
          ⟨0, by
            have hn := ctx.one_le_blockOrder
            omega⟩)
  let internal : ℝ :=
    primitiveChainProduct
      (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges
      (ctx.standardBlockTuple x)
  let exterior : ℝ :=
    res.properOuterChainProduct
      step suffix hremaining hproper x
  let outgoingLast : ℝ :=
    ctx.state.edges ctx.outgoingEdge
      (ctx.standardBlockTuple x
          (primitiveLast
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder) -
        ctx.successorPoint x)
  let outgoingFirst : ℝ :=
    ctx.state.edges ctx.outgoingEdge
      (ctx.standardBlockTuple x
          ⟨0, by
            have hn := ctx.one_le_blockOrder
            omega⟩ -
        ctx.successorPoint x)
  let laterDiff : ℝ :=
    (res.afterProper step suffix
      hremaining hproper).residualDifferenceProduct x
  let currentCov : ℝ :=
    ∑ κB :
        {κ : PartialPairing
            (Fin (2 * residualBlockOrder ctx.step.2)) //
          κ ∈ primitiveFullPairings
            (residualBlockOrder ctx.step.2)},
      primitiveCovarianceProduct ρ ε
        (residualBlockOrder ctx.step.2) κB.1
        (ctx.standardBlockTuple x)
  let laterCov : ℝ :=
    (res.afterProper step suffix
      hremaining hproper).residualPrimitiveProduct
        ρ ε x
  change
    ((incoming * internal) * exterior) *
          ((outgoingLast - outgoingFirst) * laterDiff) *
        (currentCov * laterCov) =
      (incoming * internal *
            (outgoingLast - outgoingFirst) *
          currentCov) *
        (exterior * laterDiff * laterCov)
  ring

/-- Pointwise updated-edge-times-outer factorization of the complete
post-update residual integrand. -/
theorem afterProper_residualIntegrand_eq_updated_mul_outer
    (ρ : SmoothCutoff) (ε : ℝ)
    (x : Fin (2 * q) → T4) :
    let ctx :=
      res.properStepContext
        step suffix hremaining hproper
    let post :=
      res.afterProper
        step suffix hremaining hproper
    post.residualIntegrand ρ ε x =
      post.state.edges ctx.predecessorEdge
          (ctx.predecessorPoint x -
            ctx.successorPoint x) *
        res.properOuterIntegrand
          step suffix hremaining hproper ρ ε x := by
  dsimp only
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  let post :=
    res.afterProper
      step suffix hremaining hproper
  unfold residualIntegrand properOuterIntegrand
  rw [
    res.afterProper_residualChainProduct_eq_updated_mul_outer
      step suffix hremaining hproper x]
  unfold R322AnalyticProperStepContext.predecessorPoint
    R322AnalyticProperStepContext.successorPoint
  rw [R322AnalyticProperStepContext.predecessorEdge,
    r322AnalyticEdgeLeftVertex_predecessorEdge]
  ring

/-! ## Exterior-factor independence of current block coordinates -/

/-- The stable current-block reconstruction leaves every complementary
ambient coordinate unchanged. -/
theorem properReconstructBlockTuple_eq_of_not_mem
    (base : Fin (2 * q) → T4)
    (t : Fin (2 * residualBlockOrder step.2) → T4)
    (i : Fin (2 * q))
    (hi : i ∉ step.2) :
    res.properReconstructBlockTuple
        step suffix hremaining hproper base t i =
      base i := by
  unfold properReconstructBlockTuple
  rw [dif_neg hi]

/-- A post-update ordinary chain factor depends only on post-active
coordinates, hence is insensitive to changes inside the deleted block. -/
theorem afterProper_residualChainEdgeFactor_eq_of_eq_outside_step
    (x y : Fin (2 * q) → T4)
    (hxy : ∀ i, i ∉ step.2 → x i = y i)
    (edge : Fin (2 * q - 1)) :
    (res.afterProper step suffix
        hremaining hproper).residualChainEdgeFactor x edge =
      (res.afterProper step suffix
        hremaining hproper).residualChainEdgeFactor y edge := by
  let post :=
    res.afterProper
      step suffix hremaining hproper
  by_cases hactive :
      r322AnalyticEdgeLeftVertex edge ∈
        post.state.active
  · have hleftNot :
        r322AnalyticEdgeLeftVertex edge ∉ step.2 := by
      rw [res.afterProper_active
        step suffix hremaining hproper] at hactive
      exact (Finset.mem_sdiff.mp hactive).2
    by_cases hreserved :
        edge.val ∈ post.remainingRightValues
    · unfold residualChainEdgeFactor
      rw [if_pos hactive, if_pos hreserved,
        if_pos hactive, if_pos hreserved]
    · have hsuccessorActive :
          post.edgeSuccessor edge ∈
            post.state.active :=
        r322AnalyticSuccessorVertex_mem_active
          post.state
          (r322AnalyticEdgeLeftVertex edge)
          (by
            change edge.val < 2 * q - 1
            exact edge.isLt)
      have hsuccessorNot :
          post.edgeSuccessor edge ∉ step.2 := by
        rw [res.afterProper_active
          step suffix hremaining hproper] at hsuccessorActive
        exact (Finset.mem_sdiff.mp
          hsuccessorActive).2
      unfold residualChainEdgeFactor
      rw [if_pos hactive, if_neg hreserved,
        if_pos hactive, if_neg hreserved,
        hxy _ hleftNot,
        hxy _ hsuccessorNot]
  · unfold residualChainEdgeFactor
    rw [if_neg hactive, if_neg hactive]

/-- The exterior ordinary-chain product is independent of every current
block coordinate. -/
theorem properOuterChainProduct_eq_of_eq_outside_step
    (x y : Fin (2 * q) → T4)
    (hxy : ∀ i, i ∉ step.2 → x i = y i) :
    res.properOuterChainProduct
        step suffix hremaining hproper x =
      res.properOuterChainProduct
        step suffix hremaining hproper y := by
  unfold properOuterChainProduct
  apply Finset.prod_congr rfl
  intro edge hedge
  calc
    res.residualChainEdgeFactor x edge =
        (res.afterProper step suffix
          hremaining hproper).residualChainEdgeFactor x edge := by
      exact
        (res.afterProper_residualChainEdgeFactor_eq_of_outer
          step suffix hremaining hproper x edge hedge).symm
    _ =
        (res.afterProper step suffix
          hremaining hproper).residualChainEdgeFactor y edge :=
      res.afterProper_residualChainEdgeFactor_eq_of_eq_outside_step
        step suffix hremaining hproper x y hxy edge
    _ = res.residualChainEdgeFactor y edge :=
      res.afterProper_residualChainEdgeFactor_eq_of_outer
        step suffix hremaining hproper y edge hedge

/-- Every displayed suffix step has the paper's disjoint-right-or-containing
relation to the current head. -/
theorem properStep_later_right_or_contains
    (later : R322ExtractionStep (2 * q))
    (hlater : later ∈ suffix) :
    let _ctx :=
      res.properStepContext
        step suffix hremaining hproper
    step.1.2 < later.1.1 ∨
      (later.1.1 < step.1.1 ∧
        step.1.2 < later.1.2) := by
  dsimp only
  have hp :=
    r322AnalyticSchedule_pairwise_paperEarlier
      res.pairing
  rw [res.schedule_eq, hremaining,
    List.pairwise_append] at hp
  exact
    (List.pairwise_cons.mp hp.2.1).1
      later hlater

/-- Every remaining signed post-update difference is insensitive to current
block coordinates. -/
theorem afterProper_residualStepDifference_eq_of_eq_outside_step
    (x y : Fin (2 * q) → T4)
    (hxy : ∀ i, i ∉ step.2 → x i = y i)
    (later : R322ExtractionStep (2 * q))
    (hlater : later ∈ suffix) :
    (res.afterProper step suffix
        hremaining hproper).residualStepDifference x later =
      (res.afterProper step suffix
        hremaining hproper).residualStepDifference y later := by
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  let post :=
    res.afterProper
      step suffix hremaining hproper
  have hstepAligned :=
    r322AnalyticSchedule_forall_aligned
      res.pairing step
      (by
        rw [res.schedule_eq, hremaining]
        simp)
  have hlaterAligned :=
    r322AnalyticSchedule_forall_aligned
      res.pairing later
      (by
        rw [res.schedule_eq, hremaining]
        exact List.mem_append_right _
          (List.mem_cons_of_mem step hlater))
  have hrelation :=
    res.properStep_later_right_or_contains
      step suffix hremaining hproper later hlater
  obtain ⟨hleftNot, hrightNot, _hadjacentNot⟩ :=
    r322AnalyticLater_diffCoordinates_not_mem_headBlock
      step later hstepAligned hlaterAligned hrelation
  by_cases hguard :
      later.1.2.val < 2 * q - 1
  · have hsuccessorActive :
        r322AnalyticSuccessorVertex
            post.state later.1.2 hguard ∈
          post.state.active :=
      r322AnalyticSuccessorVertex_mem_active
        post.state later.1.2 hguard
    have hsuccessorNot :
        r322AnalyticSuccessorVertex
            post.state later.1.2 hguard ∉
          step.2 := by
      rw [res.afterProper_active
        step suffix hremaining hproper] at hsuccessorActive
      exact (Finset.mem_sdiff.mp
        hsuccessorActive).2
    have hx :
        post.residualStepDifference x later =
          post.state.edges
              ⟨later.1.2.val, hguard⟩
              (x later.1.2 -
                x (r322AnalyticSuccessorVertex
                  post.state later.1.2 hguard)) -
            post.state.edges
              ⟨later.1.2.val, hguard⟩
              (x later.1.1 -
                x (r322AnalyticSuccessorVertex
                  post.state later.1.2 hguard)) := by
      unfold residualStepDifference
      split
      · rfl
      · contradiction
    have hy :
        post.residualStepDifference y later =
          post.state.edges
              ⟨later.1.2.val, hguard⟩
              (y later.1.2 -
                y (r322AnalyticSuccessorVertex
                  post.state later.1.2 hguard)) -
            post.state.edges
              ⟨later.1.2.val, hguard⟩
              (y later.1.1 -
                y (r322AnalyticSuccessorVertex
                  post.state later.1.2 hguard)) := by
      unfold residualStepDifference
      split
      · rfl
      · contradiction
    rw [hx, hy,
      hxy later.1.2 hrightNot,
      hxy later.1.1 hleftNot,
      hxy _ hsuccessorNot]
  · have hx :
        post.residualStepDifference x later = 1 := by
      unfold residualStepDifference
      split
      · contradiction
      · rfl
    have hy :
        post.residualStepDifference y later = 1 := by
      unfold residualStepDifference
      split
      · contradiction
      · rfl
    rw [hx, hy]

/-- The complete remaining signed-difference product is independent of the
current block coordinates. -/
theorem afterProper_residualDifferenceProduct_eq_of_eq_outside_step
    (x y : Fin (2 * q) → T4)
    (hxy : ∀ i, i ∉ step.2 → x i = y i) :
    (res.afterProper step suffix
        hremaining hproper).residualDifferenceProduct x =
      (res.afterProper step suffix
        hremaining hproper).residualDifferenceProduct y := by
  unfold residualDifferenceProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro later hlater
  exact
    res.afterProper_residualStepDifference_eq_of_eq_outside_step
      step suffix hremaining hproper
      x y hxy later hlater

/-- The complete remaining primitive covariance product is independent of
the current block, using the schedule's exact pairwise block disjointness. -/
theorem afterProper_residualPrimitiveProduct_eq_of_eq_outside_step
    (ρ : SmoothCutoff) (ε : ℝ)
    (x y : Fin (2 * q) → T4)
    (hxy : ∀ i, i ∉ step.2 → x i = y i) :
    (res.afterProper step suffix
        hremaining hproper).residualPrimitiveProduct ρ ε x =
      (res.afterProper step suffix
        hremaining hproper).residualPrimitiveProduct ρ ε y := by
  let post :=
    res.afterProper
      step suffix hremaining hproper
  have hp :=
    r322AnalyticSchedule_blocks_pairwise_disjoint
      res.pairing
  rw [res.schedule_eq, hremaining,
    List.map_append, List.map_cons,
    List.pairwise_append] at hp
  have hstepDisjoint :
      ∀ later : R322ExtractionStep (2 * q),
        later ∈ suffix →
          Disjoint step.2 later.2 := by
    intro later hlater
    exact
      (List.pairwise_cons.mp hp.2.1).1
        later.2
        (List.mem_map.mpr
          ⟨later, hlater, rfl⟩)
  unfold residualPrimitiveProduct
  apply Finset.prod_congr rfl
  intro j _hj
  apply r322ExtractionBlockPrimitiveSum_eq_of_eq_on
  intro i hi
  apply hxy i
  have hlater :
      post.remaining.get j ∈ suffix := by
    have hmem :=
      post.remaining.get_mem j
    simpa only [post, afterProper] using hmem
  have hdisjoint :=
    hstepDisjoint
      (post.remaining.get j) hlater
  have hiLater :
      i ∈ (post.remaining.get j).2 := by
    simpa only [remainingBlockIndex_val] using hi
  intro hiStep
  exact
    (Finset.disjoint_left.mp hdisjoint)
      hiStep hiLater

/-- The complete exterior factor is constant along every current-block
coordinate fibre. -/
theorem properOuterIntegrand_eq_of_eq_outside_step
    (ρ : SmoothCutoff) (ε : ℝ)
    (x y : Fin (2 * q) → T4)
    (hxy : ∀ i, i ∉ step.2 → x i = y i) :
    res.properOuterIntegrand
        step suffix hremaining hproper ρ ε x =
      res.properOuterIntegrand
        step suffix hremaining hproper ρ ε y := by
  unfold properOuterIntegrand
  rw [
    res.properOuterChainProduct_eq_of_eq_outside_step
      step suffix hremaining hproper x y hxy,
    res.afterProper_residualDifferenceProduct_eq_of_eq_outside_step
      step suffix hremaining hproper x y hxy,
    res.afterProper_residualPrimitiveProduct_eq_of_eq_outside_step
      step suffix hremaining hproper ρ ε x y hxy]

/-- Concrete fibre form: evaluating the exterior factor on a reconstructed
current block gives exactly its value on the outer base tuple. -/
theorem properOuterIntegrand_properReconstructBlockTuple
    (ρ : SmoothCutoff) (ε : ℝ)
    (base : Fin (2 * q) → T4)
    (t : Fin (2 * residualBlockOrder step.2) → T4) :
    res.properOuterIntegrand
        step suffix hremaining hproper ρ ε
        (res.properReconstructBlockTuple
          step suffix hremaining hproper base t) =
      res.properOuterIntegrand
        step suffix hremaining hproper ρ ε base := by
  apply
    res.properOuterIntegrand_eq_of_eq_outside_step
      step suffix hremaining hproper
  intro i hi
  exact
    res.properReconstructBlockTuple_eq_of_not_mem
      step suffix hremaining hproper base t i hi

/-! ## Exact arbitrary-prefix value transition -/

/-- One actual proper schedule step preserves the complete residual value.

The only analytic premises are genuine integrability of the current full
residual (for the coordinate Fubini split) and the native almost-everywhere
section premises consumed by the local collapse theorem.  No equality or
estimate interface is assumed. -/
theorem residualValue_eq_afterProper
    (z : T4)
    (hint :
      Integrable
        (fun v : res.SurvivingCoordinate → T4 =>
          res.residualIntegrand ρ ε
            (res.reconstruct z v))
        (Measure.pi fun _ => paperMeasure))
    (hstandard :
      ∀ᵐ outer ∂(Measure.pi fun _ :
          (res.afterProper step suffix
            hremaining hproper).SurvivingCoordinate =>
            paperMeasure),
        Integrable
          ((res.properStepContext
              step suffix hremaining hproper).localIntegrand
            ρ ε
            ((res.properStepContext
                step suffix hremaining hproper).predecessorPoint
                ((res.afterProper step suffix
                  hremaining hproper).reconstruct z outer) -
              (res.properStepContext
                step suffix hremaining hproper).successorPoint
                ((res.afterProper step suffix
                  hremaining hproper).reconstruct z outer)))
          (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin
                  (2 * residualBlockOrder step.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder step.2)},
          Integrable
            (fun v :
                Fin
                  (2 * residualBlockOrder step.2 - 2) →
                    T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder step.2)
                κB.1
                (res.properStepContext
                  step suffix hremaining hproper).internalEdges
                (primitiveAssemble
                  (residualBlockOrder step.2)
                  (res.properStepContext
                    step suffix hremaining hproper).one_le_blockOrder
                  p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    res.residualValue ρ lam ε z =
      (res.afterProper step suffix
        hremaining hproper).residualValue
          ρ lam ε z := by
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  let post :=
    res.afterProper
      step suffix hremaining hproper
  let ν :
      Measure (post.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let base :
      (post.SurvivingCoordinate → T4) →
        Fin (2 * q) → T4 :=
    fun outer => post.reconstruct z outer
  let outerFactor :
      (post.SurvivingCoordinate → T4) → ℝ :=
    fun outer =>
      res.properOuterIntegrand
        step suffix hremaining hproper
        ρ ε (base outer)
  have hinner :
      ∀ outer,
        (∫ t :
            Fin (2 * residualBlockOrder step.2) → T4,
          res.residualIntegrand ρ ε
            (res.properReconstructBlockTuple
              step suffix hremaining hproper
              (base outer) t)
          ∂Measure.pi fun _ => paperMeasure) =
          ∫ t :
              Fin (2 * residualBlockOrder step.2) → T4,
            ctx.ambientLocalIntegrand ρ ε
                (ctx.reconstructRelativeBlockTuple
                  (base outer) t) *
              outerFactor outer
            ∂Measure.pi fun _ => paperMeasure := by
    intro outer
    calc
      (∫ t :
          Fin (2 * residualBlockOrder step.2) → T4,
        res.residualIntegrand ρ ε
          (res.properReconstructBlockTuple
            step suffix hremaining hproper
            (base outer) t)
        ∂Measure.pi fun _ => paperMeasure) =
        ∫ t :
            Fin (2 * residualBlockOrder step.2) → T4,
          ctx.ambientLocalIntegrand ρ ε
              (ctx.reconstructBlockTuple
                (base outer) t) *
            outerFactor outer
          ∂Measure.pi fun _ => paperMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        rw [
          res.residualIntegrand_eq_ambientLocal_mul_outer
            step suffix hremaining hproper ρ ε,
          res.properOuterIntegrand_properReconstructBlockTuple
            step suffix hremaining hproper
            ρ ε (base outer) t,
          res.properReconstructBlockTuple_eq_context
            step suffix hremaining hproper
            (base outer) t]
      _ = _ :=
        ctx.integral_actualBlock_eq_relativeBlock
          ρ ε (base outer) (outerFactor outer)
  let laterPower :=
    lamEps lam ε ^
      (2 * post.remainingOrder)
  calc
    res.residualValue ρ lam ε z =
        lamEps lam ε ^ (2 * res.remainingOrder) *
          ∫ outer : post.SurvivingCoordinate → T4,
            ∫ t :
                Fin (2 * residualBlockOrder step.2) → T4,
              res.residualIntegrand ρ ε
                (res.properReconstructBlockTuple
                  step suffix hremaining hproper
                  (base outer) t)
              ∂Measure.pi fun _ => paperMeasure
            ∂ν := by
      exact
        res.residualValue_eq_iteratedProperRaw
          step suffix hremaining hproper
          ρ lam ε z hint
    _ =
        laterPower *
          ctx.processedResidualOuterIntegral
            ν ρ lam ε base outerFactor := by
      unfold R322AnalyticProperStepContext.processedResidualOuterIntegral
        R322AnalyticProperStepContext.processedResidualIntegrand
      rw [res.remainingOrder_eq_current_add_afterProper
        step suffix hremaining hproper]
      rw [← integral_const_mul]
      conv_rhs => rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with outer
      rw [hinner outer]
      dsimp only [laterPower, ctx, post, properStepContext]
      rw [← mul_assoc]
      rw [← pow_add]
      congr 2
      omega
    _ =
        laterPower *
          ctx.updatedResidualOuterIntegral
            ν ρ lam ε base outerFactor := by
      apply congrArg (fun value : ℝ =>
        laterPower * value)
      exact
        ctx.processedResidualOuterIntegral_eq_updated
          ν ρ lam ε base outerFactor
          hstandard hinternal
    _ = post.residualValue ρ lam ε z := by
      unfold R322AnalyticProperStepContext.updatedResidualOuterIntegral
        residualValue
      dsimp only [laterPower, ν]
      apply congrArg (fun value : ℝ =>
        lamEps lam ε ^ (2 * post.remainingOrder) * value)
      apply integral_congr_ae
      filter_upwards with outer
      have hstate :
          post.state = ctx.nextState ρ lam ε :=
        by
          dsimp only [post, ctx, afterProper, properStepContext]
      rw [← hstate]
      simpa only [ctx, post, base, outerFactor] using
        (res.afterProper_residualIntegrand_eq_updated_mul_outer
          step suffix hremaining hproper
          ρ ε (base outer)).symm

end ProperPrefixCoordinates

end R322AnalyticResidualPrefix

end

end Anderson4D
