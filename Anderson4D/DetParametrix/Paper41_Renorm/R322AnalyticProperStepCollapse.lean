import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticEdgeState
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticScheduleLedger

/-! # One carrier-relative proper collapse for R-322

The standard block coordinates are read from the next concrete block in the
sparse active carrier.  Every chain kernel is taken from the current
heterogeneous edge state, and the signed spatial integral is identified with
the predecessor edge of the updated state.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- Certified data for one proper step of the current schedule suffix. -/
structure R322AnalyticProperStepContext
    (q : ℕ) (hq : 1 ≤ q) where
  state : R322AnalyticEdgeState q hq
  pairing : PartialPairing (Fin (2 * q))
  pairing_mem : pairing ∈ nonSplitPairings q
  suffix : List (R322ExtractionStep (2 * q))
  step : R322ExtractionStep (2 * q)
  schedule_eq :
    r322AnalyticSchedule pairing =
      state.processed ++ step :: suffix
  proper : step.1 ≠ r322WholeEndpoint q hq

namespace R322AnalyticProperStepContext

variable {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticProperStepContext q hq)

theorem bounds :
    0 < ctx.step.1.1.val ∧
      ctx.step.1.2.val < 2 * q - 1 :=
  r322AnalyticProperStep_endpoint_bounds
    hq ctx.pairing ctx.pairing_mem
    ctx.state.processed ctx.suffix ctx.step
    ctx.schedule_eq ctx.proper

theorem step_mem_schedule :
    ctx.step ∈ r322AnalyticSchedule ctx.pairing := by
  rw [ctx.schedule_eq]
  simp

theorem block_mem_extractionBlocks :
    ctx.step.2 ∈ extractionBlocks ctx.pairing := by
  apply
    (r322AnalyticSchedule_blocks_perm_extractionBlocks
      ctx.pairing).mem_iff.mp
  exact List.mem_map.mpr
    ⟨ctx.step, ctx.step_mem_schedule, rfl⟩

theorem blockFullyPaired :
    IsFullyPairedOn ctx.pairing ctx.step.2 :=
  extractionBlock_isFullyPairedOn_of_mem
    ctx.pairing ctx.step.2
    ctx.block_mem_extractionBlocks

theorem one_le_blockOrder :
    1 ≤ residualBlockOrder ctx.step.2 :=
  r322AnalyticSchedule_blockOrder_pos
    ctx.pairing
    (mem_nonSplitPairings.mp ctx.pairing_mem).1
    ctx.step ctx.step_mem_schedule

/-- Increasing enumeration of the current sparse concrete block. -/
def blockOrderIso :
    Fin (2 * residualBlockOrder ctx.step.2) ≃o
      ctx.step.2 :=
  residualPrimitiveBlockOrderIso
    ctx.pairing ctx.step.2 ctx.blockFullyPaired

theorem blockVertex_bounds
    (i : Fin (2 * q)) (hi : i ∈ ctx.step.2) :
    0 < i.val ∧ i.val < 2 * q - 1 := by
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      ctx.pairing ctx.step ctx.step_mem_schedule
  have hiBounds := haligned.2.2 i hi
  have hend := ctx.bounds
  omega

/-- Ambient vertex at the left of the `j`th internal active edge. -/
def internalLeftVertex
    (j : Fin (2 * residualBlockOrder ctx.step.2 - 1)) :
    Fin (2 * q) :=
  (ctx.blockOrderIso
    ⟨j.val, by
      have hj := j.isLt
      have hn := ctx.one_le_blockOrder
      omega⟩).1

theorem internalLeftVertex_mem_active
    (j : Fin (2 * residualBlockOrder ctx.step.2 - 1)) :
    ctx.internalLeftVertex j ∈ ctx.state.active := by
  have hj :
      ctx.internalLeftVertex j ∈ ctx.step.2 :=
    (ctx.blockOrderIso
      ⟨j.val, by
        have hj := j.isLt
        have hn := ctx.one_le_blockOrder
        omega⟩).2
  rw [
    r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
      ctx.pairing ctx.state.processed ctx.suffix
      ctx.step ctx.schedule_eq] at hj
  exact (Finset.mem_inter.mp hj).1

/-- Ambient edge slot at the `j`th internal active adjacency. -/
def internalEdge
    (j : Fin (2 * residualBlockOrder ctx.step.2 - 1)) :
    Fin (2 * q - 1) :=
  ⟨(ctx.internalLeftVertex j).val,
    (ctx.blockVertex_bounds
      (ctx.internalLeftVertex j)
      (ctx.blockOrderIso
        ⟨j.val, by
          have hj := j.isLt
          have hn := ctx.one_le_blockOrder
          omega⟩).2).2⟩

/-- The primitive block sees the current heterogeneous internal edges. -/
def internalEdges :
    Fin (2 * residualBlockOrder ctx.step.2 - 1) →
      T4 → ℝ :=
  fun j => ctx.state.edges (ctx.internalEdge j)

def predecessorEdge : Fin (2 * q - 1) :=
  r322AnalyticPredecessorEdge
    ctx.state ctx.step ctx.bounds.1

def outgoingEdge : Fin (2 * q - 1) :=
  r322AnalyticOutgoingEdge ctx.step ctx.bounds.2

/-- Standard-coordinate signed integrand for this sparse proper block. -/
def localIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (u : T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ℝ :=
  ctx.state.edges ctx.predecessorEdge
      (u - t ⟨0, by
        have hn := ctx.one_le_blockOrder
        omega⟩) *
    (∑ κB :
        {κ : PartialPairing
            (Fin (2 * residualBlockOrder ctx.step.2)) //
          κ ∈ primitiveFullPairings
            (residualBlockOrder ctx.step.2)},
      detJclosedIntegrandWith ρ ε
        (2 * residualBlockOrder ctx.step.2)
        κB.1 ctx.internalEdges t) *
    (ctx.state.edges ctx.outgoingEdge
        (t (primitiveLast
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder)) -
      ctx.state.edges ctx.outgoingEdge
        (t ⟨0, by
          have hn := ctx.one_le_blockOrder
          omega⟩))

/-- The actual signed spatial integral paid by this step. -/
def localSpatialIntegral
    (ρ : SmoothCutoff) (lam ε : ℝ) (u : T4) : ℝ :=
  lamEps lam ε ^
      (2 * residualBlockOrder ctx.step.2) *
    ∫ t : Fin (2 * residualBlockOrder ctx.step.2) → T4,
      ctx.localIntegrand ρ ε u t
      ∂Measure.pi fun _ => paperMeasure

/-- State after inserting the primitive difference kernel at the sparse
predecessor slot. -/
def nextState
    (ρ : SmoothCutoff) (lam ε : ℝ) :
    R322AnalyticEdgeState q hq :=
  ctx.state.updateProper ctx.pairing ctx.pairing_mem
    ctx.suffix ctx.step ctx.schedule_eq ctx.proper
    (primitiveKernelDiff ρ lam ε
      (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges)

/-- One signed proper-block spatial integral is exactly the new
heterogeneous predecessor edge. -/
theorem localSpatialIntegral_eq_nextState_predecessor
    (ρ : SmoothCutoff) (lam ε : ℝ) (u : T4)
    (hstandard :
      Integrable (ctx.localIntegrand ρ ε u)
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder ctx.step.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder ctx.step.2)},
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder ctx.step.2)
                κB.1 ctx.internalEdges
                (primitiveAssemble
                  (residualBlockOrder ctx.step.2)
                  ctx.one_le_blockOrder p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    ctx.localSpatialIntegral ρ lam ε u =
      (ctx.nextState ρ lam ε).edges
        ctx.predecessorEdge u := by
  simpa [localSpatialIntegral, localIntegrand,
    nextState, R322AnalyticEdgeState.updateProper,
    predecessorEdge, outgoingEdge] using
    (lamEps_pow_integral_standardCompletePrimitive_eq_replacementEdge
      ctx.state.edges ctx.predecessorEdge
      ρ lam ε (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges
      (ctx.state.edges ctx.predecessorEdge)
      (ctx.state.edges ctx.outgoingEdge) u
      hstandard hinternal)

/-- A.e. wrapper used by the outer Fubini induction.  No global
`∀ u` section-integrability claim is introduced. -/
theorem eventually_localSpatialIntegral_eq_nextState_predecessor
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (hstandard :
      ∀ᵐ u ∂paperMeasure,
        Integrable (ctx.localIntegrand ρ ε u)
          (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder ctx.step.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder ctx.step.2)},
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder ctx.step.2)
                κB.1 ctx.internalEdges
                (primitiveAssemble
                  (residualBlockOrder ctx.step.2)
                  ctx.one_le_blockOrder p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    ∀ᵐ u ∂paperMeasure,
      ctx.localSpatialIntegral ρ lam ε u =
        (ctx.nextState ρ lam ε).edges
          ctx.predecessorEdge u := by
  filter_upwards [hstandard] with u hu
  exact ctx.localSpatialIntegral_eq_nextState_predecessor
    ρ lam ε u hu hinternal

end R322AnalyticProperStepContext

end

end Anderson4D
