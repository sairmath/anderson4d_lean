import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticReachableIntegrability
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticTerminalStepCollapse

/-!
# Fixed-endpoint integrability at the R-322 terminal step

The final carrier collapse is a generalized primitive kernel whose edge
family is the current heterogeneous edge state.  Reachability supplies
measurability of every such edge, while the quantitative edge certificate
supplies its class-`E` membership and off-diagonal inverse-square bound.
The scaled off-diagonal primitive-integrability theorem can therefore be
applied directly at each fixed pair of endpoints.

In particular, no exceptional endpoint is selected from a joint Fubini
statement: the result below holds pointwise in both endpoints.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R322AnalyticAbsorbedState

/-- Every closed primitive summand in a reachable terminal carrier has an
absolutely integrable internal section, pointwise in both fixed endpoints. -/
theorem integrable_terminalClosedIntegrand_section
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {q : ℕ} {hq : 1 ≤ q}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    {scale : Fin (2 * q - 1) → ℝ}
    (ctx : R322AnalyticTerminalStepContext q hq)
    (hstate :
      R322AnalyticAbsorbedState
        ρ lam ε hq κ hκ ctx.state)
    (hcert : R322AnalyticEdgeCertificate ctx.state scale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (κB :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder ctx.terminal.2)) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder ctx.terminal.2)})
    (z w : T4) :
    Integrable
      (fun v :
          Fin (2 * residualBlockOrder ctx.terminal.2 - 2) → T4 =>
        detJclosedIntegrandWith ρ ε
          (2 * residualBlockOrder ctx.terminal.2)
          κB.1 ctx.internalEdges
          (primitiveAssemble
            (residualBlockOrder ctx.terminal.2)
            ctx.one_le_blockOrder z w v))
      (Measure.pi fun _ => paperMeasure) := by
  obtain ⟨hfull, hprimitive⟩ :=
    mem_primitiveFullPairings.mp κB.2
  have hraw :
      Integrable
        (fun v :
            Fin (2 * residualBlockOrder ctx.terminal.2 - 2) → T4 =>
          primitiveIntegrand ρ ε
            (residualBlockOrder ctx.terminal.2)
            ctx.one_le_blockOrder ctx.internalEdges κB.1
            (primitiveAssemble
              (residualBlockOrder ctx.terminal.2)
              ctx.one_le_blockOrder z w v))
        (Measure.pi fun _ => paperMeasure) :=
    integrable_primitiveIntegrand_assemble_of_scaled_offDiagonal
      ρ hε hε1 ctx.one_le_blockOrder
      ctx.internalEdges
      (fun j => scale (ctx.internalEdge j))
      (fun j => hstate.measurable_edges (ctx.internalEdge j))
      (fun j => hcert.scale_pos (ctx.internalEdge j))
      (fun j => hcert.memE (ctx.internalEdge j))
      (fun j u hu => hcert.bound (ctx.internalEdge j) u hu)
      κB z w
  apply hraw.congr
  filter_upwards with v
  exact
    (detJclosedIntegrandWith_eq_primitiveIntegrand_of_full_primitive
      ρ ε (residualBlockOrder ctx.terminal.2)
      ctx.one_le_blockOrder ctx.internalEdges
      κB.1 hfull hprimitive
      (primitiveAssemble
        (residualBlockOrder ctx.terminal.2)
        ctx.one_le_blockOrder z w v)).symm

/-- The exact fixed-endpoint package consumed by the terminal-collapse
identity.  The nonzero endpoint assumption belongs to the subsequent
Proposition 4.1 estimate; integrability itself also holds on the diagonal. -/
theorem terminalClosedIntegrand_hint
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {q : ℕ} {hq : 1 ≤ q}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    {scale : Fin (2 * q - 1) → ℝ}
    (ctx : R322AnalyticTerminalStepContext q hq)
    (hstate :
      R322AnalyticAbsorbedState
        ρ lam ε hq κ hκ ctx.state)
    (hcert : R322AnalyticEdgeCertificate ctx.state scale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (z : T4) (_hz : z ≠ 0) :
    ∀ κB :
        {τ : PartialPairing
            (Fin (2 * residualBlockOrder ctx.terminal.2)) //
          τ ∈ primitiveFullPairings
            (residualBlockOrder ctx.terminal.2)},
      Integrable
        (fun v :
            Fin (2 * residualBlockOrder ctx.terminal.2 - 2) → T4 =>
          detJclosedIntegrandWith ρ ε
            (2 * residualBlockOrder ctx.terminal.2)
            κB.1 ctx.internalEdges
            (primitiveAssemble
              (residualBlockOrder ctx.terminal.2)
              ctx.one_le_blockOrder z 0 v))
        (Measure.pi fun _ => paperMeasure) := by
  intro κB
  exact hstate.integrable_terminalClosedIntegrand_section
    ctx hcert hε hε1 κB z 0

end R322AnalyticAbsorbedState

end

end Anderson4D
