import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticProperStepCollapse

/-! # Reconstructed outer Fubini for one R-322 proper step

This file exposes the pre-collapse local factor in the same
`primitiveChainProduct × primitiveCovarianceProduct` form obtained from the
actual endpoint-fibre block coordinate.  It then carries an arbitrary outer
coordinate and outer factor through the signed block integral.

The one remaining global identification is pointwise: the processed
endpoint-fibre skeleton on a reconstructed ambient tuple must equal
`rawLocalIntegrand * outer`.  No analytic estimate or new integrability claim
is needed after that identity; `integral_outer_rawLocalIntegrand_eq_nextState`
below performs the exact Fubini substitution.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R322AnalyticProperStepContext

variable {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticProperStepContext q hq)

/-- The current concrete block as an actual extraction-block coordinate. -/
def blockIndex : ExtractionBlockIndex ctx.pairing :=
  ⟨ctx.step.2, ctx.block_mem_extractionBlocks⟩

/-- An ambient tuple restricted to the current sparse block in increasing
active order. -/
def standardBlockTuple (x : Fin (2 * q) → T4) :
    Fin (2 * residualBlockOrder ctx.step.2) → T4 :=
  fun i => x (ctx.blockOrderIso i).1

/-- The primitive covariance sum in the actual endpoint-fibre block product
is literally the standard covariance sum on the sparse block tuple. -/
theorem extractionBlockPrimitiveSum_eq_standardBlock
    (ρ : SmoothCutoff) (ε : ℝ)
    (x : Fin (2 * q) → T4) :
    r322ExtractionBlockPrimitiveSum ρ ε
        ctx.pairing ctx.blockIndex x =
      ∑ κB :
          {κ : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κ ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)},
        primitiveCovarianceProduct ρ ε
          (residualBlockOrder ctx.step.2)
          κB.1 (ctx.standardBlockTuple x) := by
  rfl

/-- Local factor before recognizing the generalized closed `J` integrand.
This is the exact chain-times-covariance form produced by the actual
endpoint-fibre pointwise factorization. -/
def rawLocalIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (u : T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ℝ :=
  ctx.state.edges ctx.predecessorEdge
      (u - t ⟨0, by
        have hn := ctx.one_le_blockOrder
        omega⟩) *
    primitiveChainProduct
      (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges t *
    (ctx.state.edges ctx.outgoingEdge
        (t (primitiveLast
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder)) -
      ctx.state.edges ctx.outgoingEdge
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

/-- Exact pointwise recognition of the true primitive chain and covariance
sum as the generalized closed-`J` local integrand. -/
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

/-- One reconstructed inner integral may carry any fixed outer factor. -/
theorem rawLocalSpatialIntegral_mul_outer_eq_nextState
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (u : T4) (outer : ℝ)
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
    lamEps lam ε ^
          (2 * residualBlockOrder ctx.step.2) *
        (∫ t : Fin (2 * residualBlockOrder ctx.step.2) → T4,
          ctx.rawLocalIntegrand ρ ε u t * outer
          ∂Measure.pi fun _ => paperMeasure) =
      (ctx.nextState ρ lam ε).edges
          ctx.predecessorEdge u * outer := by
  simp_rw [ctx.rawLocalIntegrand_eq_localIntegrand]
  rw [integral_mul_const]
  rw [← mul_assoc]
  change ctx.localSpatialIntegral ρ lam ε u * outer =
    (ctx.nextState ρ lam ε).edges
      ctx.predecessorEdge u * outer
  rw [ctx.localSpatialIntegral_eq_nextState_predecessor
    ρ lam ε u hstandard hinternal]

/-- Exact outer-Fubini substitution.  The section-integrability premise is
only almost everywhere in the genuine outer coordinate. -/
theorem integral_outer_rawLocalIntegrand_eq_nextState
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (u : Ω → T4) (outer : Ω → ℝ)
    (hstandard :
      ∀ᵐ ω ∂ν,
        Integrable (ctx.localIntegrand ρ ε (u ω))
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
    (∫ ω,
        lamEps lam ε ^
            (2 * residualBlockOrder ctx.step.2) *
          (∫ t :
              Fin (2 * residualBlockOrder ctx.step.2) → T4,
            ctx.rawLocalIntegrand ρ ε (u ω) t *
              outer ω
            ∂Measure.pi fun _ => paperMeasure)
        ∂ν) =
      ∫ ω,
        (ctx.nextState ρ lam ε).edges
            ctx.predecessorEdge (u ω) *
          outer ω
        ∂ν := by
  apply integral_congr_ae
  filter_upwards [hstandard] with ω hω
  exact ctx.rawLocalSpatialIntegral_mul_outer_eq_nextState
    ρ lam ε (u ω) (outer ω) hω hinternal

end R322AnalyticProperStepContext

end

end Anderson4D
