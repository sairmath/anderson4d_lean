import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticBudgetScaleInvariant
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticScheduleLedger
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticTerminalActiveEdges

/-!
# Exact product invariant for the quantitative R-322 schedule

The slotwise budget update has an exact active-edge product recurrence.  This
module iterates that recurrence over a genuinely reachable scale history and
then combines it with the schedule's exact perturbative-order ledger.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- Total perturbative order already absorbed into a sparse edge state. -/
def r322AnalyticProcessedOrder
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq) : ℕ :=
  (state.processed.map
    (fun step => residualBlockOrder step.2)).sum

theorem r322AnalyticActiveEdges_initial
    (q : ℕ) (hq : 1 ≤ q) :
    r322AnalyticActiveEdges
        (r322InitialAnalyticEdgeState q hq) =
      Finset.univ := by
  ext edge
  simp [r322AnalyticActiveEdges,
    r322InitialAnalyticEdgeState,
    R322AnalyticEdgeState.active,
    r322AnalyticActiveCarrier_nil]

namespace R322AnalyticBudgetScaleReachable

variable {q : ℕ} {hq : 1 ≤ q}
    {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    {state : R322AnalyticEdgeState q hq}
    {scale : Fin (2 * q - 1) → ℝ}

/-- Exact active-edge product after any quantitatively reachable proper
prefix.  Every proper block contributes its order power and one collapse
constant exactly once. -/
theorem activeEdgeScaleProduct_eq
    (hreach :
      R322AnalyticBudgetScaleReachable
        hq ρ C lam ε K A κ hκ state scale) :
    (∏ edge ∈ r322AnalyticActiveEdges state, scale edge) =
      A ^ (2 * q - 1) *
        (C * lam) ^ (2 * r322AnalyticProcessedOrder state) *
          K ^ state.processed.length := by
  induction hreach with
  | initial =>
      rw [r322AnalyticActiveEdges_initial]
      change
        (∏ _edge : Fin (2 * q - 1), A) =
          A ^ (2 * q - 1) * (C * lam) ^ 0 * K ^ 0
      simp
  | @update oldScale ctx hpairing previous ih =>
      rw [ctx.activeEdgeScaleProduct_budgetUpdate
        ρ ε C lam K oldScale]
      unfold R322AnalyticProperStepContext.activeEdgeScaleProduct
      rw [ih]
      simp only [R322AnalyticProperStepContext.nextState,
        R322AnalyticEdgeState.updateProper_processed,
        r322AnalyticProcessedOrder, List.map_append,
        List.map_singleton, List.sum_append,
        List.sum_singleton, List.length_append,
        List.length_singleton]
      rw [show
          2 *
              ((ctx.state.processed.map
                (fun step =>
                  residualBlockOrder step.2)).sum +
                residualBlockOrder ctx.step.2) =
            2 *
                (ctx.state.processed.map
                  (fun step =>
                    residualBlockOrder step.2)).sum +
              2 * residualBlockOrder ctx.step.2 by omega,
        pow_add, pow_succ]
      ring

end R322AnalyticBudgetScaleReachable

namespace R322AnalyticTerminalStepContext

variable {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticTerminalStepContext q hq)

/-- After adding the final primitive block, the coupling power is exactly
the ambient perturbative order `2q`; no block order is lost or duplicated. -/
theorem activeEdgeScaleProduct_mul_terminalPower
    {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    {scale : Fin (2 * q - 1) → ℝ}
    (hpairing : ctx.pairing = κ)
    (hreach :
      R322AnalyticBudgetScaleReachable
        hq ρ C lam ε K A κ hκ ctx.state scale) :
    (∏ edge ∈ r322AnalyticActiveEdges ctx.state, scale edge) *
        (C * lam) ^
          (2 * residualBlockOrder ctx.terminal.2) =
      A ^ (2 * q - 1) *
        (C * lam) ^ (2 * q) *
          K ^ ctx.state.processed.length := by
  have hfull : ctx.pairing.IsFull :=
    (mem_nonSplitPairings.mp ctx.pairing_mem).1
  have horder :
      (ctx.state.processed.map
          (fun step => residualBlockOrder step.2)).sum +
        residualBlockOrder ctx.terminal.2 = q :=
    sum_r322AnalyticSchedule_proper_add_terminal
      hfull ctx.state.processed ctx.terminal ctx.schedule_eq
  have hproduct := hreach.activeEdgeScaleProduct_eq
  subst κ
  rw [hproduct]
  unfold r322AnalyticProcessedOrder
  have hexponent :
      2 *
          (ctx.state.processed.map
            (fun step =>
              residualBlockOrder step.2)).sum +
        2 * residualBlockOrder ctx.terminal.2 =
      2 * q := by
    omega
  have hpower :
      (C * lam) ^
          (2 *
            (ctx.state.processed.map
              (fun step =>
                residualBlockOrder step.2)).sum) *
          (C * lam) ^
            (2 * residualBlockOrder ctx.terminal.2) =
        (C * lam) ^ (2 * q) := by
    rw [← pow_add, hexponent]
  calc
    A ^ (2 * q - 1) *
          (C * lam) ^
            (2 *
              (ctx.state.processed.map
                (fun step =>
                  residualBlockOrder step.2)).sum) *
          K ^ ctx.state.processed.length *
          (C * lam) ^
            (2 * residualBlockOrder ctx.terminal.2) =
        A ^ (2 * q - 1) *
          ((C * lam) ^
              (2 *
                (ctx.state.processed.map
                  (fun step =>
                    residualBlockOrder step.2)).sum) *
            (C * lam) ^
              (2 * residualBlockOrder ctx.terminal.2)) *
          K ^ ctx.state.processed.length := by ring
    _ = A ^ (2 * q - 1) *
          (C * lam) ^ (2 * q) *
          K ^ ctx.state.processed.length := by
      rw [hpower]

/-- The initial Green scales and the one constant per proper collapse can
be absorbed into a single base raised to the final even order. -/
theorem budgetMultiplier_le_finalEvenPower
    {K A : ℝ}
    (hA : 1 ≤ A) (hK : 0 < K) :
    A ^ (2 * q - 1) * K ^ ctx.state.processed.length ≤
      (A * max 1 K) ^ (2 * q) := by
  have hfull : ctx.pairing.IsFull :=
    (mem_nonSplitPairings.mp ctx.pairing_mem).1
  have hscheduleLength :
      (r322AnalyticSchedule ctx.pairing).length ≤ q :=
    length_r322AnalyticSchedule_le_of_full ctx.pairing hfull
  rw [ctx.schedule_eq, List.length_append] at hscheduleLength
  have hprocessedLe :
      ctx.state.processed.length ≤ 2 * q := by
    simp only [List.length_singleton] at hscheduleLength
    omega
  have hApow :
      A ^ (2 * q - 1) ≤ A ^ (2 * q) :=
    pow_le_pow_right₀ hA (by omega)
  have hKpowBase :
      K ^ ctx.state.processed.length ≤
        (max 1 K) ^ ctx.state.processed.length :=
    pow_le_pow_left₀ hK.le (le_max_right 1 K) _
  have hKpowExponent :
      (max 1 K) ^ ctx.state.processed.length ≤
        (max 1 K) ^ (2 * q) :=
    pow_le_pow_right₀ (le_max_left 1 K) hprocessedLe
  calc
    A ^ (2 * q - 1) * K ^ ctx.state.processed.length ≤
        A ^ (2 * q) *
          (max 1 K) ^ (2 * q) :=
      mul_le_mul hApow (hKpowBase.trans hKpowExponent)
        (pow_nonneg hK.le _)
        (pow_nonneg (zero_le_one.trans hA) _)
    _ = (A * max 1 K) ^ (2 * q) := by
      rw [mul_pow]

/-- Exact terminal-order accounting plus the preceding numerical absorption
turn the residual-block majorant into one ambient-order majorant. -/
theorem activeEdgeScaleProduct_mul_terminalMajorant_le
    {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    {scale : Fin (2 * q - 1) → ℝ}
    (hpairing : ctx.pairing = κ)
    (hreach :
      R322AnalyticBudgetScaleReachable
        hq ρ C lam ε K A κ hκ ctx.state scale)
    (hA : 1 ≤ A) (hK : 0 < K)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (supportConstant : ℝ) (z : T4) :
    (∏ edge ∈ r322AnalyticActiveEdges ctx.state, scale edge) *
        primitiveKernelMajorant C lam ε supportConstant
          (residualBlockOrder ctx.terminal.2) z ≤
      primitiveKernelMajorant
        (A * max 1 K * C) lam ε supportConstant q z := by
  let E : ℝ :=
    ((ε⁻¹) ^ 4 / |Real.log ε|) * invSqKer z *
        primitiveSupportIndicator supportConstant ε z +
      (1 / |Real.log ε| ^ 2) *
        (torusDistSq z + ε ^ 2)⁻¹ ^ 3
  have hE : 0 ≤ E := by
    have hnonneg :=
      primitiveKernelMajorant_nonneg
        (C := (1 : ℝ)) (lam := (1 : ℝ))
        (ε := ε) (supportConstant := supportConstant)
        (n := residualBlockOrder ctx.terminal.2) (z := z)
        zero_le_one zero_le_one
    simpa only [primitiveKernelMajorant, one_mul, one_pow, E]
      using hnonneg
  have hterminal :=
    ctx.activeEdgeScaleProduct_mul_terminalPower
      hpairing hreach
  have hmultiplier :=
    ctx.budgetMultiplier_le_finalEvenPower hA hK
  unfold primitiveKernelMajorant
  change
    (∏ edge ∈ r322AnalyticActiveEdges ctx.state, scale edge) *
        ((C * lam) ^
          (2 * residualBlockOrder ctx.terminal.2) * E) ≤
      ((A * max 1 K * C) * lam) ^ (2 * q) * E
  calc
    (∏ edge ∈ r322AnalyticActiveEdges ctx.state, scale edge) *
          ((C * lam) ^
            (2 * residualBlockOrder ctx.terminal.2) * E) =
        ((∏ edge ∈ r322AnalyticActiveEdges ctx.state, scale edge) *
          (C * lam) ^
            (2 * residualBlockOrder ctx.terminal.2)) * E := by
      ring
    _ =
        (A ^ (2 * q - 1) *
          (C * lam) ^ (2 * q) *
          K ^ ctx.state.processed.length) * E := by
      rw [hterminal]
    _ ≤
        ((A * max 1 K) ^ (2 * q) *
          (C * lam) ^ (2 * q)) * E := by
      apply mul_le_mul_of_nonneg_right _ hE
      calc
        A ^ (2 * q - 1) *
              (C * lam) ^ (2 * q) *
              K ^ ctx.state.processed.length =
            (A ^ (2 * q - 1) *
              K ^ ctx.state.processed.length) *
              (C * lam) ^ (2 * q) := by ring
        _ ≤ (A * max 1 K) ^ (2 * q) *
              (C * lam) ^ (2 * q) :=
          mul_le_mul_of_nonneg_right hmultiplier
            (pow_nonneg (mul_nonneg hC hlam) _)
    _ = ((A * max 1 K * C) * lam) ^ (2 * q) * E := by
      rw [show
          (A * max 1 K * C) * lam =
            (A * max 1 K) * (C * lam) by ring,
        mul_pow, mul_pow]
      ring

/-- Fully quantitative terminal Proposition 4.1 estimate in the final
ambient-order normalization.  The remaining R-322 work is to identify each
fixed endpoint fibre with this terminal spatial integral. -/
theorem abs_terminalSpatialIntegral_le_finalMajorant
    {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    {scale : Fin (2 * q - 1) → ℝ}
    (hpairing : ctx.pairing = κ)
    (hreach :
      R322AnalyticBudgetScaleReachable
        hq ρ C lam ε K A κ hκ ctx.state scale)
    (hA : 1 ≤ A) (hK : 0 < K)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (supportConstant : ℝ)
    (hcert : R322AnalyticEdgeCertificate ctx.state scale)
    (hprop :
      ∀ H : Fin
          (2 * residualBlockOrder ctx.terminal.2 - 1) →
            T4 → ℝ,
        IsAdmissiblePrimitiveInput
            (residualBlockOrder ctx.terminal.2) H →
          MemEClassT4
              (primitiveKernelDiff ρ lam ε
                (residualBlockOrder ctx.terminal.2)
                ctx.one_le_blockOrder H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff ρ lam ε
                (residualBlockOrder ctx.terminal.2)
                ctx.one_le_blockOrder H) ∧
              PrimitiveKernelBounds ρ lam ε
                (residualBlockOrder ctx.terminal.2)
                ctx.one_le_blockOrder H supportConstant C)
    (z : T4) (hz : z ≠ 0)
    (hint :
      ∀ κB :
          {κ' : PartialPairing
              (Fin (2 * residualBlockOrder ctx.terminal.2)) //
            κ' ∈ primitiveFullPairings
              (residualBlockOrder ctx.terminal.2)},
        MeasureTheory.Integrable
          (fun u :
              Fin (2 * residualBlockOrder
                ctx.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder ctx.terminal.2)
              κB.1 ctx.internalEdges
              (primitiveAssemble
                (residualBlockOrder ctx.terminal.2)
                ctx.one_le_blockOrder z 0 u))
          (Measure.pi fun _ => paperMeasure)) :
    |ctx.terminalSpatialIntegral ρ lam ε z 0| ≤
      primitiveKernelMajorant
        (A * max 1 K * C) lam ε supportConstant q z := by
  exact
    (ctx.abs_terminalSpatialIntegral_le_activeEdgeScaleProduct_mul_majorant
      ρ lam ε C supportConstant scale hcert hprop z hz hint).trans
      (ctx.activeEdgeScaleProduct_mul_terminalMajorant_le
        hpairing hreach hA hK hC hlam supportConstant z)

end R322AnalyticTerminalStepContext

end

end Anderson4D
