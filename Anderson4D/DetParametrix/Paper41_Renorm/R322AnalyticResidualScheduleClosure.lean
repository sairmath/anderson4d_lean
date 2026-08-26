import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticResidualFubini
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticProperPrefixReachability
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticPrimitiveCertificate

/-! # Schedule closure for the R-322 residual integral

This module starts by identifying the general sparse-carrier residual step
with the actual first step of `endpointFiberDetJSum`.  The preceding module
already proves the ambient successor translation and the one-step Fubini
update; here the all-Green initial context is connected to that interface
before the schedule induction is assembled.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The first schedule step as a genuine edge-state context -/

/-- Proper-step context carried by the all-Green initial state. -/
def r322InitialProperStepContext
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    R322AnalyticProperStepContext q hq where
  state := r322InitialAnalyticEdgeState q hq
  pairing := κ
  pairing_mem := hκ
  suffix := tail
  step := head
  schedule_eq := by
    simpa [r322InitialAnalyticEdgeState] using hschedule
  proper := hproper

namespace R322InitialProperStepContext

variable {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)

local notation "ctx₀" =>
  r322InitialProperStepContext
    hq κ hκ head tail hschedule hproper

@[simp]
theorem state :
    (ctx₀).state = r322InitialAnalyticEdgeState q hq :=
  rfl

@[simp]
theorem state_edges
    (edge : Fin (2 * q - 1)) :
    (ctx₀).state.edges edge = greenFn :=
  rfl

theorem one_le_blockOrder :
    (ctx₀).one_le_blockOrder =
      r322AnalyticHead_one_le_residualBlockOrder
        κ hκ head tail hschedule := by
  apply Subsingleton.elim

/-- The generic sparse block enumeration specializes to the production
proper-head enumeration. -/
theorem standardBlockTuple_eq
    (x : Fin (2 * q) → T4) :
    (ctx₀).standardBlockTuple x =
      r322AnalyticProperHeadStandardTuple
        hq κ hκ head tail hschedule hproper x := by
  funext j
  unfold R322AnalyticProperStepContext.standardBlockTuple
    R322AnalyticProperStepContext.blockOrderIso
  change
    x ((residualPrimitiveBlockOrderIso κ head.2
      (ctx₀).blockFullyPaired j).1) =
      x (r322AnalyticProperHeadVertex
        hq κ hκ head tail hschedule hproper j)
  apply congrArg x
  exact
    r322AnalyticProperHead_residualOrderIso_apply
      hq κ hκ head tail hschedule hproper j

/-- Initially the greatest active predecessor is the literal ambient vertex
`head.left - 1`. -/
theorem predecessorVertex_eq :
    r322AnalyticPredecessorVertex
        (ctx₀).state (ctx₀).step (ctx₀).bounds.1 =
      (⟨head.1.1.val - 1, by
        have hl := head.1.1.isLt
        omega⟩ : Fin (2 * q)) := by
  let before : Fin (2 * q) :=
    ⟨head.1.1.val - 1, by
      have hb := (ctx₀).bounds.1
      have hl := head.1.1.isLt
      omega⟩
  have hbeforeActive : before ∈ (ctx₀).state.active := by
    simp [before, r322InitialProperStepContext,
      r322InitialAnalyticEdgeState,
      R322AnalyticEdgeState.active]
  have hbeforeLeft : before < (ctx₀).step.1.1 := by
    change head.1.1.val - 1 < head.1.1.val
    exact Nat.sub_lt (ctx₀).bounds.1 Nat.zero_lt_one
  have hlower :
      before ≤
        r322AnalyticPredecessorVertex
          (ctx₀).state (ctx₀).step (ctx₀).bounds.1 :=
    r322AnalyticPredecessorVertex_maximal
      (ctx₀).state (ctx₀).step (ctx₀).bounds.1
      before hbeforeActive hbeforeLeft
  have hupper :
      r322AnalyticPredecessorVertex
          (ctx₀).state (ctx₀).step (ctx₀).bounds.1 <
        (ctx₀).step.1.1 :=
    r322AnalyticPredecessorVertex_lt_left
      (ctx₀).state (ctx₀).step (ctx₀).bounds.1
  apply Fin.ext
  change
    (r322AnalyticPredecessorVertex
        (ctx₀).state (ctx₀).step (ctx₀).bounds.1).val =
      head.1.1.val - 1
  change before.val ≤ _ at hlower
  change _ < head.1.1.val at hupper
  dsimp only [before] at hlower
  omega

theorem predecessorEdge_eq :
    (ctx₀).predecessorEdge =
      r322AnalyticProperHeadPredecessorEdge
        hq κ hκ head tail hschedule hproper := by
  apply Fin.ext
  change
    (r322AnalyticPredecessorVertex
      (ctx₀).state (ctx₀).step (ctx₀).bounds.1).val =
      head.1.1.val - 1
  exact congrArg Fin.val
    (predecessorVertex_eq
      hq κ hκ head tail hschedule hproper)

/-- Initially the least active successor is the literal ambient vertex
`head.right + 1`. -/
theorem successorVertex_eq :
    (ctx₀).successorVertex =
      (⟨head.1.2.val + 1, by
        have hb := (ctx₀).bounds.2
        change head.1.2.val < 2 * q - 1 at hb
        omega⟩ : Fin (2 * q)) := by
  let after : Fin (2 * q) :=
    ⟨head.1.2.val + 1, by
      have hb := (ctx₀).bounds.2
      change head.1.2.val < 2 * q - 1 at hb
      omega⟩
  have hafterCandidate :
      after ∈
        r322AnalyticSuccessorCandidates
          (ctx₀).state (ctx₀).step.1.2 := by
    apply Finset.mem_filter.mpr
    constructor
    · simp [after, r322InitialProperStepContext,
        r322InitialAnalyticEdgeState,
        R322AnalyticEdgeState.active]
    · change head.1.2.val < head.1.2.val + 1
      omega
  have hupper :
      (ctx₀).successorVertex ≤ after := by
    unfold R322AnalyticProperStepContext.successorVertex
      r322AnalyticSuccessorVertex
    exact Finset.min'_le _ after hafterCandidate
  have hlower :
      (ctx₀).step.1.2 < (ctx₀).successorVertex :=
    (ctx₀).stepRight_lt_successorVertex
  apply Fin.ext
  change (ctx₀).successorVertex.val = head.1.2.val + 1
  change head.1.2.val < (ctx₀).successorVertex.val at hlower
  change (ctx₀).successorVertex.val ≤ after.val at hupper
  dsimp only [after] at hupper
  omega

theorem outgoingEdge_eq :
    (ctx₀).outgoingEdge =
      ⟨head.1.2.val, by
        have hb := (ctx₀).bounds.2
        exact hb⟩ := by
  rfl

/-- Every initial internal sparse edge is the corresponding affine
proper-head edge. -/
theorem internalEdge_eq
    (j : Fin (2 * residualBlockOrder head.2 - 1)) :
    (ctx₀).internalEdge j =
      r322AnalyticProperHeadInternalEdge
        hq κ hκ head tail hschedule hproper j := by
  apply Fin.ext
  unfold R322AnalyticProperStepContext.internalEdge
    R322AnalyticProperStepContext.internalLeftVertex
    R322AnalyticProperStepContext.blockOrderIso
  change
    ((residualPrimitiveBlockOrderIso κ head.2
      (ctx₀).blockFullyPaired
      ⟨j.val, by
        have hj := j.isLt
        have hn := (ctx₀).one_le_blockOrder
        omega⟩).1).val =
      head.1.1.val + j.val
  exact
    r322AnalyticProperHead_residualOrderIso_apply_val
      hq κ hκ head tail hschedule hproper
      ⟨j.val, by
        have hj := j.isLt
        have hn := (ctx₀).one_le_blockOrder
        omega⟩

theorem internalEdges_eq :
    (ctx₀).internalEdges =
      fun _ : Fin (2 * residualBlockOrder head.2 - 1) =>
        greenFn := by
  funext j
  unfold R322AnalyticProperStepContext.internalEdges
  rfl

theorem predecessorPoint_eq
    (x : Fin (2 * q) → T4) :
    (ctx₀).predecessorPoint x =
      x (r322JChainEdgeLeft
        (r322AnalyticProperHeadPredecessorEdge
          hq κ hκ head tail hschedule hproper)) := by
  unfold R322AnalyticProperStepContext.predecessorPoint
  rw [predecessorVertex_eq
    hq κ hκ head tail hschedule hproper]
  apply congrArg x
  apply Fin.ext
  rfl

theorem successorPoint_eq
    (x : Fin (2 * q) → T4) :
    (ctx₀).successorPoint x =
      x ⟨head.1.2.val + 1, by
        have hb := (ctx₀).bounds.2
        change head.1.2.val < 2 * q - 1 at hb
        omega⟩ := by
  unfold R322AnalyticProperStepContext.successorPoint
  rw [successorVertex_eq
    hq κ hκ head tail hschedule hproper]

/-- Reconstructing the initial head block through the generic sparse-state
API is literally the production proper-head reconstruction. -/
theorem reconstructBlockTuple_reference_eq
    (z : T4)
    (vC :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock q hq head.2) i} → T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4) :
    (ctx₀).reconstructBlockTuple
        (r322AnalyticProperHeadReferenceTuple
          hq κ hκ head tail hschedule hproper z vC) t =
      r322AnalyticProperHeadReconstruct
        hq κ hκ head tail hschedule hproper z vC t := by
  let base :=
    r322AnalyticProperHeadReferenceTuple
      hq κ hκ head tail hschedule hproper z vC
  let x :=
    r322AnalyticProperHeadReconstruct
      hq κ hκ head tail hschedule hproper z vC t
  have hread : (ctx₀).standardBlockTuple x = t := by
    rw [
      standardBlockTuple_eq
        hq κ hκ head tail hschedule hproper]
    exact
      r322AnalyticProperHeadStandardTuple_reconstruct
        hq κ hκ head tail hschedule hproper z vC t
  funext i
  dsimp only [r322InitialProperStepContext]
  by_cases hi : i ∈ head.2
  · unfold R322AnalyticProperStepContext.reconstructBlockTuple
    rw [dif_pos hi]
    let j : Fin (2 * residualBlockOrder head.2) :=
      (ctx₀).blockOrderIso.symm ⟨i, hi⟩
    have hj := congrFun hread j
    change x ((ctx₀).blockOrderIso j).1 = t j at hj
    have hjimage :
        ((ctx₀).blockOrderIso j).1 = i := by
      exact congrArg Subtype.val
        ((ctx₀).blockOrderIso.apply_symm_apply ⟨i, hi⟩)
    rw [hjimage] at hj
    exact hj.symm
  · unfold R322AnalyticProperStepContext.reconstructBlockTuple
    rw [dif_neg hi]
    change base i = x i
    exact
      (r322AnalyticProperHeadReconstruct_eq_of_not_mem
        hq κ hκ head tail hschedule hproper z vC
        (fun _ => 0) t i hi)

/-- The state-based ambient local factor is exactly the production
analytic-head factor at the all-Green initial state. -/
theorem ambientLocalIntegrand_eq_headLocal
    (ρ : SmoothCutoff) (ε : ℝ)
    (x : Fin (2 * q) → T4) :
    (ctx₀).ambientLocalIntegrand ρ ε x =
      r322AnalyticHeadLocalIntegrandFactor
        ρ ε κ head tail hschedule x := by
  have haligned :
      ExtractionPairBlockAligned head.1 head.2 :=
    r322AnalyticSchedule_forall_aligned κ head
      (by rw [hschedule]; simp)
  have hguard : head.1.2.val + 1 < 2 * q := by
    have hb := (ctx₀).bounds.2
    change head.1.2.val < 2 * q - 1 at hb
    omega
  have hdiff :=
    (r322AnalyticHead_diffFactorJWith_eq
      (fun _ : Fin (2 * q - 1) => greenFn)
      x head haligned hguard).2
  have hincoming :
      greenFn
          (x (r322JChainEdgeLeft
              (r322AnalyticProperHeadPredecessorEdge
                hq κ hκ head tail hschedule hproper)) -
            x head.1.1) =
        jChainEdgeWith
          (fun _ : Fin (2 * q - 1) => greenFn) x
          (r322AnalyticProperHeadPredecessorEdge
            hq κ hκ head tail hschedule hproper) := by
    change
      greenFn
          (x (r322JChainEdgeLeft
              (r322AnalyticProperHeadPredecessorEdge
                hq κ hκ head tail hschedule hproper)) -
            x head.1.1) =
        greenFn
          (x (r322JChainEdgeLeft
              (r322AnalyticProperHeadPredecessorEdge
                hq κ hκ head tail hschedule hproper)) -
            x (r322JChainEdgeRight
              (r322AnalyticProperHeadPredecessorEdge
                hq κ hκ head tail hschedule hproper)))
    rw [
      r322AnalyticProperHeadPredecessorEdge_right
        hq κ hκ head tail hschedule hproper]
  have hzero :
      r322AnalyticProperHeadStandardTuple
          hq κ hκ head tail hschedule hproper x
          ⟨0, by
            have hn :=
              r322AnalyticHead_one_le_residualBlockOrder
                κ hκ head tail hschedule
            omega⟩ =
        x head.1.1 := by
    unfold r322AnalyticProperHeadStandardTuple
    rw [r322AnalyticProperHeadVertex_zero
      hq κ hκ head tail hschedule hproper]
  have hlast :
      r322AnalyticProperHeadStandardTuple
          hq κ hκ head tail hschedule hproper x
          (primitiveLast
            (residualBlockOrder head.2)
            (r322AnalyticHead_one_le_residualBlockOrder
              κ hκ head tail hschedule)) =
        x head.1.2 := by
    unfold r322AnalyticProperHeadStandardTuple
    rw [r322AnalyticProperHeadVertex_last
      hq κ hκ head tail hschedule hproper]
  have hzeroCtx :
      (ctx₀).standardBlockTuple x
          ⟨0, by
            have hn := (ctx₀).one_le_blockOrder
            omega⟩ =
        x head.1.1 := by
    rw [
      standardBlockTuple_eq
        hq κ hκ head tail hschedule hproper]
    exact hzero
  have hlastCtx :
      (ctx₀).standardBlockTuple x
          (primitiveLast
            (residualBlockOrder (ctx₀).step.2)
            (ctx₀).one_le_blockOrder) =
        x head.1.2 := by
    rw [
      standardBlockTuple_eq
        hq κ hκ head tail hschedule hproper]
    exact hlast
  unfold R322AnalyticProperStepContext.ambientLocalIntegrand
    r322AnalyticHeadLocalIntegrandFactor
    r322AnalyticHeadLocalFactorWith
  rw [
    r322AnalyticProperHeadLocalChainProductWith_eq
      hq κ hκ head tail hschedule hproper
      (fun _ : Fin (2 * q - 1) => greenFn) x,
    r322AnalyticHeadPrimitiveSum_eq_standardTuple
      hq ρ ε κ hκ head tail hschedule hproper x,
    hdiff]
  rw [
    predecessorPoint_eq
      hq κ hκ head tail hschedule hproper,
    successorPoint_eq
      hq κ hκ head tail hschedule hproper,
    predecessorEdge_eq
      hq κ hκ head tail hschedule hproper,
    outgoingEdge_eq
      hq κ hκ head tail hschedule hproper,
    hzeroCtx, hlastCtx,
    standardBlockTuple_eq
      hq κ hκ head tail hschedule hproper,
    internalEdges_eq
      hq κ hκ head tail hschedule hproper]
  simp only [
    state_edges
      hq κ hκ head tail hschedule hproper]
  dsimp only [r322InitialProperStepContext]
  rw [
    one_le_blockOrder
      hq κ hκ head tail hschedule hproper]
  rw [hincoming]
  rfl

end R322InitialProperStepContext

/-! ## The actual initial residual as the first processed state -/

/-- Exact order still carried by the suffix after the first analytic
schedule block. -/
def r322AnalyticSuffixOrder
    {q : ℕ}
    (tail : List (R322ExtractionStep (2 * q))) : ℕ :=
  (tail.map fun step => residualBlockOrder step.2).sum

theorem residualBlockOrder_head_add_suffixOrder
    {q : ℕ}
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail) :
    residualBlockOrder head.2 +
        r322AnalyticSuffixOrder tail =
      q := by
  have hsum :=
    sum_r322AnalyticSchedule_blockOrders_of_full
      κ (mem_nonSplitPairings.mp hκ).1
  rw [hschedule] at hsum
  simpa [r322AnalyticSuffixOrder] using hsum

/-- At the first block, the exact production residual integrand agrees with
the generic sparse-state local factor times the unchanged suffix factor. -/
theorem r322InitialResidualIntegrand_reconstruct_eq
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock q hq head.2) i} → T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4) :
    r322InitialResidualIntegrand
        ρ ε κ head tail hschedule
        (r322AnalyticProperHeadReconstruct
          hq κ hκ head tail hschedule hproper z vC t) =
      (r322InitialProperStepContext
          hq κ hκ head tail hschedule hproper).ambientLocalIntegrand
          ρ ε
          ((r322InitialProperStepContext
              hq κ hκ head tail hschedule hproper).reconstructBlockTuple
            (r322AnalyticProperHeadReferenceTuple
              hq κ hκ head tail hschedule hproper z vC) t) *
        r322AnalyticHeadOuterIntegrandFactor
          ρ ε κ head tail hschedule
          (r322AnalyticProperHeadReferenceTuple
            hq κ hκ head tail hschedule hproper z vC) := by
  let x :=
    r322AnalyticProperHeadReconstruct
      hq κ hκ head tail hschedule hproper z vC t
  let xRef :=
    r322AnalyticProperHeadReferenceTuple
      hq κ hκ head tail hschedule hproper z vC
  have houter :
      r322AnalyticHeadOuterIntegrandFactor
          ρ ε κ head tail hschedule x =
        r322AnalyticHeadOuterIntegrandFactor
          ρ ε κ head tail hschedule xRef := by
    exact
      r322AnalyticHeadOuterIntegrandFactor_eq
        ρ ε κ x xRef head tail hschedule
        (fun i hi =>
          r322AnalyticProperHeadReconstruct_eq_of_not_mem
            hq κ hκ head tail hschedule hproper z vC
            t (fun _ => 0) i hi)
  unfold r322InitialResidualIntegrand
  change
    r322AnalyticHeadLocalIntegrandFactor
          ρ ε κ head tail hschedule x *
        r322AnalyticHeadOuterIntegrandFactor
          ρ ε κ head tail hschedule x =
      _
  rw [
    R322InitialProperStepContext.reconstructBlockTuple_reference_eq
      hq κ hκ head tail hschedule hproper z vC t,
    R322InitialProperStepContext.ambientLocalIntegrand_eq_headLocal
      hq κ hκ head tail hschedule hproper ρ ε x,
    houter]

/-- The actual first-block integral is exactly the relative-coordinate
processed residual integral; the translation is genuine Haar invariance. -/
theorem integral_r322InitialResidualIntegrand_eq_processed
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock q hq head.2) i} → T4) :
    (∫ t : Fin (2 * residualBlockOrder head.2) → T4,
        r322InitialResidualIntegrand
          ρ ε κ head tail hschedule
          (r322AnalyticProperHeadReconstruct
            hq κ hκ head tail hschedule hproper z vC t)
        ∂Measure.pi fun _ => paperMeasure) =
      ∫ t : Fin (2 * residualBlockOrder head.2) → T4,
        (r322InitialProperStepContext
            hq κ hκ head tail hschedule hproper).processedResidualIntegrand
          ρ ε
          (r322AnalyticProperHeadReferenceTuple
            hq κ hκ head tail hschedule hproper z vC)
          (r322AnalyticHeadOuterIntegrandFactor
            ρ ε κ head tail hschedule
            (r322AnalyticProperHeadReferenceTuple
              hq κ hκ head tail hschedule hproper z vC))
          t
        ∂Measure.pi fun _ => paperMeasure := by
  let ctx :=
    r322InitialProperStepContext
      hq κ hκ head tail hschedule hproper
  let base :=
    r322AnalyticProperHeadReferenceTuple
      hq κ hκ head tail hschedule hproper z vC
  let outer :=
    r322AnalyticHeadOuterIntegrandFactor
      ρ ε κ head tail hschedule base
  calc
    (∫ t : Fin (2 * residualBlockOrder head.2) → T4,
        r322InitialResidualIntegrand
          ρ ε κ head tail hschedule
          (r322AnalyticProperHeadReconstruct
            hq κ hκ head tail hschedule hproper z vC t)
        ∂Measure.pi fun _ => paperMeasure) =
      ∫ t : Fin (2 * residualBlockOrder head.2) → T4,
        ctx.ambientLocalIntegrand ρ ε
            (ctx.reconstructBlockTuple base t) * outer
        ∂Measure.pi fun _ => paperMeasure := by
      apply integral_congr_ae
      filter_upwards with t
      exact
        r322InitialResidualIntegrand_reconstruct_eq
          hq ρ ε κ hκ head tail hschedule hproper z vC t
    _ =
      ∫ t : Fin (2 * residualBlockOrder head.2) → T4,
        ctx.ambientLocalIntegrand ρ ε
            (ctx.reconstructRelativeBlockTuple base t) * outer
        ∂Measure.pi fun _ => paperMeasure :=
      ctx.integral_actualBlock_eq_relativeBlock ρ ε base outer
    _ = _ := by
      rfl

/-- The exact first processed residual, including the perturbative power
carried by every later schedule block. -/
def r322InitialProcessedOuterIntegral
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4) : ℝ :=
  (r322InitialProperStepContext
      hq κ hκ head tail hschedule hproper).processedResidualOuterIntegral
    (Measure.pi fun _ :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock q hq head.2) i} =>
        paperMeasure)
    ρ lam ε
    (fun vC =>
      r322AnalyticProperHeadReferenceTuple
        hq κ hκ head tail hschedule hproper z vC)
    (fun vC =>
      lamEps lam ε ^ (2 * r322AnalyticSuffixOrder tail) *
        r322AnalyticHeadOuterIntegrandFactor
          ρ ε κ head tail hschedule
          (r322AnalyticProperHeadReferenceTuple
            hq κ hκ head tail hschedule hproper z vC))

/-- The initial residual object from the actual endpoint fibre is exactly
the first generic processed-prefix residual object.  In particular, the
global `2q` coupling power is neither dropped nor duplicated: it splits
between the head order and the suffix-order ledger. -/
theorem r322InitialResidualOuterIntegral_eq_processed
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4) :
    r322InitialResidualOuterIntegral
        hq ρ lam ε κ hκ head tail hschedule hproper z =
      r322InitialProcessedOuterIntegral
        hq ρ lam ε κ hκ head tail hschedule hproper z := by
  let ctx :=
    r322InitialProperStepContext
      hq κ hκ head tail hschedule hproper
  let ν : Measure
      ({i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock q hq head.2) i} → T4) :=
    Measure.pi fun _ => paperMeasure
  have horder :
      residualBlockOrder head.2 +
          r322AnalyticSuffixOrder tail =
        q :=
    residualBlockOrder_head_add_suffixOrder
      κ hκ head tail hschedule
  unfold r322InitialResidualOuterIntegral
    r322InitialProcessedOuterIntegral
    R322AnalyticProperStepContext.processedResidualOuterIntegral
  calc
    lamEps lam ε ^ (2 * q) *
        (∫ vC,
          ∫ t : Fin (2 * residualBlockOrder head.2) → T4,
            r322InitialResidualIntegrand
              ρ ε κ head tail hschedule
              (r322AnalyticProperHeadReconstruct
                hq κ hκ head tail hschedule hproper z vC t)
            ∂Measure.pi fun _ => paperMeasure
          ∂ν) =
      ∫ vC,
        lamEps lam ε ^ (2 * q) *
          (∫ t : Fin (2 * residualBlockOrder head.2) → T4,
            r322InitialResidualIntegrand
              ρ ε κ head tail hschedule
              (r322AnalyticProperHeadReconstruct
                hq κ hκ head tail hschedule hproper z vC t)
            ∂Measure.pi fun _ => paperMeasure)
        ∂ν := by
      rw [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with vC
      let base :=
        r322AnalyticProperHeadReferenceTuple
          hq κ hκ head tail hschedule hproper z vC
      let outer :=
        r322AnalyticHeadOuterIntegrandFactor
          ρ ε κ head tail hschedule base
      have hinner :=
        integral_r322InitialResidualIntegrand_eq_processed
          hq ρ ε κ hκ head tail hschedule hproper z vC
      change
        lamEps lam ε ^ (2 * q) *
            (∫ t : Fin (2 * residualBlockOrder head.2) → T4,
              r322InitialResidualIntegrand
                ρ ε κ head tail hschedule
                (r322AnalyticProperHeadReconstruct
                  hq κ hκ head tail hschedule hproper z vC t)
              ∂Measure.pi fun _ => paperMeasure) =
          lamEps lam ε ^ (2 * residualBlockOrder head.2) *
            (∫ t : Fin (2 * residualBlockOrder head.2) → T4,
              ctx.ambientLocalIntegrand ρ ε
                    (ctx.reconstructRelativeBlockTuple base t) *
                  (lamEps lam ε ^
                      (2 * r322AnalyticSuffixOrder tail) *
                    outer)
              ∂Measure.pi fun _ => paperMeasure)
      rw [hinner]
      have hscaled :
          (∫ t : Fin (2 * residualBlockOrder head.2) → T4,
              ctx.ambientLocalIntegrand ρ ε
                    (ctx.reconstructRelativeBlockTuple base t) *
                  (lamEps lam ε ^
                      (2 * r322AnalyticSuffixOrder tail) *
                    outer)
              ∂Measure.pi fun _ => paperMeasure) =
            lamEps lam ε ^
                (2 * r322AnalyticSuffixOrder tail) *
              (∫ t : Fin (2 * residualBlockOrder head.2) → T4,
                ctx.ambientLocalIntegrand ρ ε
                    (ctx.reconstructRelativeBlockTuple base t) *
                  outer
                ∂Measure.pi fun _ => paperMeasure) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        ring
      rw [hscaled, ← mul_assoc, ← pow_add]
      congr 2
      omega

/-- The endpoint-fibre sum is now connected to the production processed
residual API without any model-integrand interface. -/
theorem endpointFiberDetJSum_eq_initialProcessedOuterIntegral
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (hint :
      ∀ τ : ReductionEndpointFiberAt κ,
        Integrable
          (fun v : Fin (2 * q - 2) → T4 =>
            detJintegrand ρ ε q τ.1
              (primitiveAssemble q hq z 0 v))
          (Measure.pi fun _ => paperMeasure)) :
    endpointFiberDetJSum ρ lam ε q
        (reductionEndpointSignature κ) z =
      r322InitialProcessedOuterIntegral
        hq ρ lam ε κ hκ head tail hschedule hproper z := by
  rw [
    endpointFiberDetJSum_eq_initialResidualOuterIntegral
      hq ρ lam ε κ hκ head tail hschedule hproper z hint,
    r322InitialResidualOuterIntegral_eq_processed
      hq ρ lam ε κ hκ head tail hschedule hproper z]

/-- The exact residual integral immediately after the first schedule block
has been absorbed into its predecessor edge. -/
def r322InitialUpdatedOuterIntegral
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4) : ℝ :=
  (r322InitialProperStepContext
      hq κ hκ head tail hschedule hproper).updatedResidualOuterIntegral
    (Measure.pi fun _ :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock q hq head.2) i} =>
        paperMeasure)
    ρ lam ε
    (fun vC =>
      r322AnalyticProperHeadReferenceTuple
        hq κ hκ head tail hschedule hproper z vC)
    (fun vC =>
      lamEps lam ε ^ (2 * r322AnalyticSuffixOrder tail) *
        r322AnalyticHeadOuterIntegrandFactor
          ρ ε κ head tail hschedule
          (r322AnalyticProperHeadReferenceTuple
            hq κ hκ head tail hschedule hproper z vC))

/-- **Actual first-step schedule closure.**

Starting from `endpointFiberDetJSum`, the first genuine proper schedule
block is integrated and absorbed into the heterogeneous predecessor edge.
The only premises are the section-integrability statements required by
Fubini; the primitive-endpoint premise is product-Haar almost everywhere,
which is the exact strength supplied by joint integrability. -/
theorem endpointFiberDetJSum_eq_initialUpdatedOuterIntegral
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (hint :
      ∀ τ : ReductionEndpointFiberAt κ,
        Integrable
          (fun v : Fin (2 * q - 2) → T4 =>
            detJintegrand ρ ε q τ.1
              (primitiveAssemble q hq z 0 v))
          (Measure.pi fun _ => paperMeasure))
    (hstandard :
      ∀ᵐ vC ∂(Measure.pi fun _ :
          {i : Fin (2 * q - 2) //
            ¬r322SelectedFinPredicate
              (r322InternalCoordinatesOfBlock q hq head.2) i} =>
            paperMeasure),
        Integrable
          ((r322InitialProperStepContext
              hq κ hκ head tail hschedule hproper).localIntegrand
            ρ ε
            ((r322InitialProperStepContext
                hq κ hκ head tail hschedule hproper).predecessorPoint
                (r322AnalyticProperHeadReferenceTuple
                  hq κ hκ head tail hschedule hproper z vC) -
              (r322InitialProperStepContext
                hq κ hκ head tail hschedule hproper).successorPoint
                (r322AnalyticProperHeadReferenceTuple
                  hq κ hκ head tail hschedule hproper z vC)))
          (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder head.2)) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder head.2)},
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder head.2)
                κB.1
                (r322InitialProperStepContext
                  hq κ hκ head tail hschedule hproper).internalEdges
                (primitiveAssemble
                  (residualBlockOrder head.2)
                  (r322InitialProperStepContext
                    hq κ hκ head tail hschedule hproper).one_le_blockOrder
                  p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    endpointFiberDetJSum ρ lam ε q
        (reductionEndpointSignature κ) z =
      r322InitialUpdatedOuterIntegral
        hq ρ lam ε κ hκ head tail hschedule hproper z := by
  rw [
    endpointFiberDetJSum_eq_initialProcessedOuterIntegral
      hq ρ lam ε κ hκ head tail hschedule hproper z hint]
  exact
    (r322InitialProperStepContext
      hq κ hκ head tail hschedule hproper)
      |>.processedResidualOuterIntegral_eq_updated
        (Measure.pi fun _ :
          {i : Fin (2 * q - 2) //
            ¬r322SelectedFinPredicate
              (r322InternalCoordinatesOfBlock q hq head.2) i} =>
            paperMeasure)
        ρ lam ε
        (fun vC =>
          r322AnalyticProperHeadReferenceTuple
            hq κ hκ head tail hschedule hproper z vC)
        (fun vC =>
          lamEps lam ε ^ (2 * r322AnalyticSuffixOrder tail) *
            r322AnalyticHeadOuterIntegrandFactor
              ρ ε κ head tail hschedule
              (r322AnalyticProperHeadReferenceTuple
                hq κ hκ head tail hschedule hproper z vC))
        hstandard hinternal

/-! ## Continuity with the genuine absorbed-state induction -/

/-- The state produced by the exact first residual update is the first
reachable heterogeneous state of the production schedule. -/
theorem r322InitialNextState_absorbed
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    R322AnalyticAbsorbedState ρ lam ε hq κ hκ
      ((r322InitialProperStepContext
          hq κ hκ head tail hschedule hproper).nextState
        ρ lam ε) := by
  exact
    R322AnalyticAbsorbedState.update
      (r322InitialProperStepContext
        hq κ hκ head tail hschedule hproper)
      rfl R322AnalyticAbsorbedState.initial

@[simp]
theorem r322InitialNextState_processed
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    ((r322InitialProperStepContext
          hq κ hκ head tail hschedule hproper).nextState
        ρ lam ε).processed =
      [head] := by
  rfl

namespace R322AnalyticProperStepContext

variable {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticProperStepContext q hq)

/-- Advance a proper-step context to the next proper schedule step using
the exact heterogeneous state produced by the current absorption. -/
def nextProperStep
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (next : R322ExtractionStep (2 * q))
    (rest : List (R322ExtractionStep (2 * q)))
    (hsuffix : ctx.suffix = next :: rest)
    (hproper :
      next.1 ≠ r322WholeEndpoint q hq) :
    R322AnalyticProperStepContext q hq where
  state := ctx.nextState ρ lam ε
  pairing := ctx.pairing
  pairing_mem := ctx.pairing_mem
  suffix := rest
  step := next
  schedule_eq := by
    rw [nextState, R322AnalyticEdgeState.updateProper_processed]
    rw [List.append_assoc]
    simpa [hsuffix] using ctx.schedule_eq
  proper := hproper

@[simp]
theorem nextProperStep_state
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (next : R322ExtractionStep (2 * q))
    (rest : List (R322ExtractionStep (2 * q)))
    (hsuffix : ctx.suffix = next :: rest)
    (hproper :
      next.1 ≠ r322WholeEndpoint q hq) :
    (ctx.nextProperStep ρ lam ε next rest hsuffix hproper).state =
      ctx.nextState ρ lam ε :=
  rfl

/-- If only the whole-carrier step remains, the current proper absorption
produces the certified terminal context consumed by Proposition 4.1. -/
def nextTerminalStep
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (terminal : R322ExtractionStep (2 * q))
    (hsuffix : ctx.suffix = [terminal])
    (hterminal :
      terminal.1 = r322WholeEndpoint q hq) :
    R322AnalyticTerminalStepContext q hq where
  state := ctx.nextState ρ lam ε
  pairing := ctx.pairing
  pairing_mem := ctx.pairing_mem
  terminal := terminal
  schedule_eq := by
    rw [nextState, R322AnalyticEdgeState.updateProper_processed]
    rw [List.append_assoc]
    simpa [hsuffix] using ctx.schedule_eq
  terminal_endpoint := hterminal

@[simp]
theorem nextTerminalStep_state
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (terminal : R322ExtractionStep (2 * q))
    (hsuffix : ctx.suffix = [terminal])
    (hterminal :
      terminal.1 = r322WholeEndpoint q hq) :
    (ctx.nextTerminalStep
        ρ lam ε terminal hsuffix hterminal).state =
      ctx.nextState ρ lam ε :=
  rfl

end R322AnalyticProperStepContext

end

end Anderson4D
