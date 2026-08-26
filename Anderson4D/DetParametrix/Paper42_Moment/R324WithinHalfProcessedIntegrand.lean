import Anderson4D.DetParametrix.Paper42_Moment.R324FirstLeftPostPrefixState
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticProperStepFubini

/-! # Honest processed integrands for an R-324 within-half step

The current heterogeneous edge state represents blocks already integrated
from the analytic prefix.  The next block remains an actual local spatial
integral, multiplied by an arbitrary fixed outer factor.  No statement here
identifies an unprocessed production integrand pointwise with this state.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfStepContext

variable {m : ℕ} {pairing : PartialPairing (Fin m)}
    (ctx : R324WithinHalfStepContext pairing)

/-- The current concrete block as a genuine extraction-block coordinate. -/
def blockIndex : ExtractionBlockIndex pairing :=
  ⟨ctx.step.2, ctx.block_mem_extractionBlocks⟩

/-- Restriction of an ambient within-half tuple to the current sparse block. -/
def standardBlockTuple (x : Fin m → T4) :
    Fin (2 * residualBlockOrder ctx.step.2) → T4 :=
  fun i => x (ctx.blockOrderIso i).1

theorem extractionBlockPrimitiveSum_eq_standardBlock
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin m → T4) :
    r322ExtractionBlockPrimitiveSum ρ ε
        pairing ctx.blockIndex x =
      ∑ κB :
          {κ : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κ ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)},
        primitiveCovarianceProduct ρ ε
          (residualBlockOrder ctx.step.2)
          κB.1 (ctx.standardBlockTuple x) := by
  rfl

/-- The unintegrated local factor in standard block coordinates. -/
def rawLocalIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (u : T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ℝ :=
  ctx.state.edges
      (r324WithinHalfPredecessorSlot ctx.state ctx.step)
      (u - t ⟨0, by
        have hn := ctx.one_le_blockOrder
        omega⟩) *
    primitiveChainProduct
      (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges t *
    (ctx.state.edges ctx.outgoingSlot
        (t (primitiveLast
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder)) -
      ctx.state.edges ctx.outgoingSlot
        (t ⟨0, by
          have hn := ctx.one_le_blockOrder
          omega⟩)) *
    ∑ κB :
        {κ : PartialPairing
            (Fin (2 * residualBlockOrder ctx.step.2)) //
          κ ∈ primitiveFullPairings
            (residualBlockOrder ctx.step.2)},
      primitiveCovarianceProduct ρ ε
        (residualBlockOrder ctx.step.2) κB.1 t

/-- Closed-`J` form consumed by the signed three-kernel collapse. -/
def localIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (u : T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ℝ :=
  ctx.state.edges
      (r324WithinHalfPredecessorSlot ctx.state ctx.step)
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
    (ctx.state.edges ctx.outgoingSlot
        (t (primitiveLast
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder)) -
      ctx.state.edges ctx.outgoingSlot
        (t ⟨0, by
          have hn := ctx.one_le_blockOrder
          omega⟩))

theorem rawLocalIntegrand_eq_localIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (u : T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ctx.rawLocalIntegrand ρ ε u t =
      ctx.localIntegrand ρ ε u t := by
  have hclosed :
      primitiveChainProduct
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder ctx.internalEdges t *
          (∑ κB :
              {κ : PartialPairing
                  (Fin (2 * residualBlockOrder ctx.step.2)) //
                κ ∈ primitiveFullPairings
                  (residualBlockOrder ctx.step.2)},
            primitiveCovarianceProduct ρ ε
              (residualBlockOrder ctx.step.2) κB.1 t) =
        ∑ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder ctx.step.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder ctx.step.2)},
          detJclosedIntegrandWith ρ ε
            (2 * residualBlockOrder ctx.step.2)
            κB.1 ctx.internalEdges t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro κB _hκB
    obtain ⟨hfull, hprimitive⟩ :=
      mem_primitiveFullPairings.mp κB.2
    rw [
      detJclosedIntegrandWith_eq_primitiveIntegrand_of_full_primitive
        ρ ε (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder ctx.internalEdges
        κB.1 hfull hprimitive t]
    rfl
  unfold rawLocalIntegrand localIntegrand
  rw [← hclosed]
  ring

/-- Ambient processed factor for the current block and a fixed outer
factor.  Earlier blocks enter only through `ctx.state.edges`. -/
def processedIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (u : T4)
    (x : Fin m → T4) (outer : ℝ) : ℝ :=
  ctx.state.edges
      (r324WithinHalfPredecessorSlot ctx.state ctx.step)
      (u - ctx.standardBlockTuple x
        ⟨0, by
          have hn := ctx.one_le_blockOrder
          omega⟩) *
    primitiveChainProduct
      (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges
      (ctx.standardBlockTuple x) *
    (ctx.state.edges ctx.outgoingSlot
        (ctx.standardBlockTuple x
          (primitiveLast
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder)) -
      ctx.state.edges ctx.outgoingSlot
        (ctx.standardBlockTuple x
          ⟨0, by
            have hn := ctx.one_le_blockOrder
            omega⟩)) *
    r322ExtractionBlockPrimitiveSum ρ ε
      pairing ctx.blockIndex x *
    outer

/-- Exact pointwise local-times-outer factorization of the processed state. -/
theorem processedIntegrand_eq_local_mul_outer
    (ρ : SmoothCutoff) (ε : ℝ) (u : T4)
    (x : Fin m → T4) (outer : ℝ) :
    ctx.processedIntegrand ρ ε u x outer =
      ctx.localIntegrand ρ ε u
        (ctx.standardBlockTuple x) * outer := by
  unfold processedIntegrand
  rw [ctx.extractionBlockPrimitiveSum_eq_standardBlock]
  change
    ctx.rawLocalIntegrand ρ ε u
        (ctx.standardBlockTuple x) * outer =
      ctx.localIntegrand ρ ε u
        (ctx.standardBlockTuple x) * outer
  rw [ctx.rawLocalIntegrand_eq_localIntegrand]

/-- Signed spatial integral of the current processed local factor. -/
def localSpatialIntegral
    (ρ : SmoothCutoff) (lam ε : ℝ) (u : T4) : ℝ :=
  lamEps lam ε ^
      (2 * residualBlockOrder ctx.step.2) *
    ∫ t : Fin (2 * residualBlockOrder ctx.step.2) → T4,
      ctx.localIntegrand ρ ε u t
      ∂Measure.pi fun _ => paperMeasure

/-- One honest processed spatial section is exactly the predecessor edge
of the absorbed state. -/
theorem localSpatialIntegral_eq_absorb_predecessor
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
      (ctx.absorb ρ lam ε).edges
        (r324WithinHalfPredecessorSlot
          ctx.state ctx.step) u := by
  rw [ctx.absorb_edges_predecessor]
  simpa [localSpatialIntegral, localIntegrand,
    collapsedKernel, primitiveKernel] using
    (lamEps_pow_integral_standardCompletePrimitive_eq_replacementEdge
      ctx.state.edges
      (r324WithinHalfPredecessorSlot ctx.state ctx.step)
      ρ lam ε (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges
      (ctx.state.edges
        (r324WithinHalfPredecessorSlot ctx.state ctx.step))
      (ctx.state.edges ctx.outgoingSlot) u
      hstandard hinternal)

end R324WithinHalfStepContext

end

end Anderson4D
