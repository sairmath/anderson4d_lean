import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticProperStepFubini

/-! # Processed-integrand invariant for R-322

An unintegrated original endpoint-fibre integrand is not pointwise equal to a
state in which earlier blocks have already been integrated.  The honest
invariant is therefore inductive: the initial state is reachable, and one
certified proper spatial collapse produces the next reachable state.  Its
processed list remains a prefix of the production analytic schedule.

For the current step, `processedLocalFactor` uses the production
`r322ExtractionBlockPrimitiveSum`.  The pointwise theorem below identifies
that pre-integration factor with the exact generalized closed-`J` integrand
consumed by the one-step Fubini theorem.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- States obtained from the all-Green production state by the exact proper
updates of `R322AnalyticProperStepContext`.  This records absorption history,
not a pointwise equality with the unintegrated original integrand. -/
inductive R322AnalyticAbsorbedState
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q) :
    R322AnalyticEdgeState q hq → Prop
  | initial :
      R322AnalyticAbsorbedState ρ lam ε hq κ hκ
        (r322InitialAnalyticEdgeState q hq)
  | update
      (ctx : R322AnalyticProperStepContext q hq)
      (hpairing : ctx.pairing = κ)
      (previous :
        R322AnalyticAbsorbedState ρ lam ε hq κ hκ
          ctx.state) :
      R322AnalyticAbsorbedState ρ lam ε hq κ hκ
        (ctx.nextState ρ lam ε)

namespace R322AnalyticAbsorbedState

variable {q : ℕ} {hq : 1 ≤ q}
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}

/-- Reachability always carries an actual processed prefix of the fixed
production schedule. -/
theorem processed_prefix
    {state : R322AnalyticEdgeState q hq}
    (hstate :
      R322AnalyticAbsorbedState ρ lam ε hq κ hκ state) :
    ∃ remaining,
      r322AnalyticSchedule κ =
        state.processed ++ remaining := by
  induction hstate with
  | initial =>
      exact
        ⟨r322AnalyticSchedule κ, by
          simp [r322InitialAnalyticEdgeState]⟩
  | update ctx hpairing previous ih =>
      refine ⟨ctx.suffix, ?_⟩
      rw [R322AnalyticProperStepContext.nextState,
        R322AnalyticEdgeState.updateProper_processed]
      rw [← hpairing]
      simpa [List.append_assoc] using ctx.schedule_eq

/-- The induction constructor preserves the exact one-step integral
identity whenever its genuine section-integrability premises hold. -/
theorem localSpatialIntegral_eq_updatedEdge
    (ctx : R322AnalyticProperStepContext q hq)
    (hpairing : ctx.pairing = κ)
    (_hstate :
      R322AnalyticAbsorbedState ρ lam ε hq κ hκ
        ctx.state)
    (u : T4)
    (hstandard :
      Integrable (ctx.localIntegrand ρ ε u)
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {σ : PartialPairing
                (Fin (2 * residualBlockOrder ctx.step.2)) //
              σ ∈ primitiveFullPairings
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
  have _ := hpairing
  exact ctx.localSpatialIntegral_eq_nextState_predecessor
    ρ lam ε u hstandard hinternal

end R322AnalyticAbsorbedState

namespace R322AnalyticProperStepContext

variable {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticProperStepContext q hq)

/-- Translation-normalized local factor before the current block is
integrated.  The covariance coordinate is the actual extraction-block
factor, while the external successor has been placed at zero.  A separate
translated-tuple bridge is required before this is used in the ambient
endpoint-fibre integrand. -/
def processedLocalFactor
    (ρ : SmoothCutoff) (ε : ℝ) (u : T4)
    (x : Fin (2 * q) → T4) : ℝ :=
  ctx.state.edges ctx.predecessorEdge
      (u - ctx.standardBlockTuple x
        ⟨0, by
          have hn := ctx.one_le_blockOrder
          omega⟩) *
    primitiveChainProduct
      (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges
      (ctx.standardBlockTuple x) *
    (ctx.state.edges ctx.outgoingEdge
        (ctx.standardBlockTuple x
          (primitiveLast
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder)) -
      ctx.state.edges ctx.outgoingEdge
        (ctx.standardBlockTuple x
          ⟨0, by
            have hn := ctx.one_le_blockOrder
            omega⟩)) *
    r322ExtractionBlockPrimitiveSum ρ ε
      ctx.pairing ctx.blockIndex x

/-- Exact pointwise reconstruction of the zero-successor current-block
factor as the raw local integrand on its canonical sparse tuple. -/
theorem processedLocalFactor_eq_rawLocalIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (u : T4)
    (x : Fin (2 * q) → T4) :
    ctx.processedLocalFactor ρ ε u x =
      ctx.rawLocalIntegrand ρ ε u
        (ctx.standardBlockTuple x) := by
  unfold processedLocalFactor rawLocalIntegrand
  rw [ctx.extractionBlockPrimitiveSum_eq_standardBlock]

/-- Hence the zero-successor current-block factor is exactly the closed-`J`
integrand already consumed by the signed spatial collapse. -/
theorem processedLocalFactor_eq_localIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (u : T4)
    (x : Fin (2 * q) → T4) :
    ctx.processedLocalFactor ρ ε u x =
      ctx.localIntegrand ρ ε u
        (ctx.standardBlockTuple x) := by
  rw [ctx.processedLocalFactor_eq_rawLocalIntegrand]
  exact ctx.rawLocalIntegrand_eq_localIntegrand
    ρ ε u (ctx.standardBlockTuple x)

/-- Pointwise local-times-outer form used immediately below the outer
integral.  The outer factor is not constrained or smuggled in as a target
equality. -/
theorem processedLocalFactor_mul_outer
    (ρ : SmoothCutoff) (ε : ℝ) (u : T4)
    (x : Fin (2 * q) → T4) (outer : ℝ) :
    ctx.processedLocalFactor ρ ε u x * outer =
      ctx.localIntegrand ρ ε u
          (ctx.standardBlockTuple x) * outer := by
  rw [ctx.processedLocalFactor_eq_localIntegrand]

/-- Replace exactly the ambient vertices of the current concrete block by a
standard sparse tuple; all complementary ambient coordinates are retained. -/
def reconstructBlockTuple
    (base : Fin (2 * q) → T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    Fin (2 * q) → T4 :=
  fun i =>
    if hi : i ∈ ctx.step.2 then
      t (ctx.blockOrderIso.symm ⟨i, hi⟩)
    else
      base i

/-- Reading the reconstructed ambient tuple on the production block returns
the supplied standard tuple literally. -/
@[simp]
theorem standardBlockTuple_reconstructBlockTuple
    (base : Fin (2 * q) → T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ctx.standardBlockTuple
        (ctx.reconstructBlockTuple base t) =
      t := by
  funext j
  unfold standardBlockTuple reconstructBlockTuple
  simp

/-- Zero-successor coordinate reconstruction.  This is not by itself the
ambient production bridge: there the supplied block tuple and incoming
coordinate must first be translated by the active successor. -/
theorem processedLocalFactor_reconstructBlockTuple
    (ρ : SmoothCutoff) (ε : ℝ) (u : T4)
    (base : Fin (2 * q) → T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ctx.processedLocalFactor ρ ε u
        (ctx.reconstructBlockTuple base t) =
      ctx.localIntegrand ρ ε u t := by
  rw [ctx.processedLocalFactor_eq_localIntegrand,
    ctx.standardBlockTuple_reconstructBlockTuple]

end R322AnalyticProperStepContext

end

end Anderson4D
