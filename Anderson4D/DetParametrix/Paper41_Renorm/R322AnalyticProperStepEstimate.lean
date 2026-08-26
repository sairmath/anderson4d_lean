import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticOutgoingGreen

/-! # Quantitative carrier-relative R-322 update

This file connects the production heterogeneous-edge state transition with
the analytic one-block estimate.  The outgoing-edge invariant removes the
last apparent mismatch: the quantitative collapse theorem is stated with a
free right Green kernel, and the next production edge is proved to have
exactly that kernel.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R322AnalyticProperStepContext

variable {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticProperStepContext q hq)

/-- At the predecessor slot, the state update is definitionally the
three-kernel collapse with the current heterogeneous incoming, primitive,
and outgoing kernels. -/
theorem nextState_predecessor_eq_r322Collapse
    (ρ : SmoothCutoff) (lam ε : ℝ) (u : T4) :
    (ctx.nextState ρ lam ε).edges ctx.predecessorEdge u =
      r322Collapse
        (ctx.state.edges ctx.predecessorEdge)
        (primitiveKernelDiff ρ lam ε
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder ctx.internalEdges)
        (ctx.state.edges ctx.outgoingEdge) u := by
  simp [nextState, R322AnalyticEdgeState.updateProper,
    predecessorEdge, outgoingEdge]

/-- For an actually reachable state, the same update is the precise
free-right-Green collapse required by the quantitative one-block theorem. -/
theorem nextState_predecessor_eq_r322Collapse_greenFn
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    (hstate :
      R322AnalyticAbsorbedState ρ lam ε hq κ hκ
        ctx.state)
    (hpairing : ctx.pairing = κ)
    (u : T4) :
    (ctx.nextState ρ lam ε).edges ctx.predecessorEdge u =
      r322Collapse
        (ctx.state.edges ctx.predecessorEdge)
        (primitiveKernelDiff ρ lam ε
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder ctx.internalEdges)
        greenFn u := by
  rw [ctx.nextState_predecessor_eq_r322Collapse]
  rw [
    hstate.outgoingEdge_eq_greenFn
      ctx hpairing rfl]

end R322AnalyticProperStepContext

/-- A production proper step inherits the exact inverse-square estimate of
`exists_r322Collapse_le`.  The constant is chosen before every scale,
coupling, block order, state, and endpoint. -/
theorem exists_r322AnalyticNextState_predecessor_le
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ρ : SmoothCutoff) (C lam ε A : ℝ)
        (q : ℕ) (hq : 1 ≤ q)
        (κ : PartialPairing (Fin (2 * q)))
        (hκ : κ ∈ nonSplitPairings q)
        (ctx : R322AnalyticProperStepContext q hq)
        (_hstate :
          R322AnalyticAbsorbedState
            ρ lam ε hq κ hκ ctx.state),
        ctx.pairing = κ →
        0 ≤ C → 0 ≤ lam → 0 ≤ A →
        0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| →
        Measurable
          (primitiveKernelDiff ρ lam ε
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder ctx.internalEdges) →
        MemEClassT4
          (primitiveKernelDiff ρ lam ε
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder ctx.internalEdges) →
        (∀ u,
          |primitiveKernelDiff ρ lam ε
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder ctx.internalEdges u| ≤
            primitiveKernelMajorant C lam ε
              supportConstant
              (residualBlockOrder ctx.step.2) u) →
        (∀ z, z ≠ 0 →
          |ctx.state.edges ctx.predecessorEdge z| ≤
            A * invSqKer z) →
        (∀ x, x ≠ 0 →
          Integrable
            (r322CollapseIntegrand
              (ctx.state.edges ctx.predecessorEdge)
              (primitiveKernelDiff ρ lam ε
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder ctx.internalEdges)
              greenFn x)
            (paperMeasure.prod paperMeasure)) →
        ∀ x : T4, x ≠ 0 →
          |(ctx.nextState ρ lam ε).edges
              ctx.predecessorEdge x| ≤
            A * (C * lam) ^
                (2 * residualBlockOrder ctx.step.2) *
              K * invSqKer x := by
  obtain ⟨K, hK, hcollapse⟩ :=
    exists_r322Collapse_le hsupport
  refine ⟨K, hK, ?_⟩
  intro ρ C lam ε A q hq κ hκ ctx _hstate
    hpairing hC hlam hA hε hε1 hlog hJmeas
    hJmem hJbound hGpBound hint x hx
  rw [
    ctx.nextState_predecessor_eq_r322Collapse_greenFn
      _hstate hpairing x]
  exact
    hcollapse C lam ε A
      (residualBlockOrder ctx.step.2)
      (ctx.state.edges ctx.predecessorEdge)
      (primitiveKernelDiff ρ lam ε
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder ctx.internalEdges)
      x hC hlam hA hε hε1 hlog hx
      hJmeas hJmem hJbound hGpBound (hint x hx)

end

end Anderson4D
