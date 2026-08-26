import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticActiveEdgeLedger
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticOutgoingGreen

/-!
# Future-edge invariance of the R-322 budget scales

The analytic schedule has strictly increasing right endpoints.  Its
quantitative scale update changes only the predecessor slot, strictly to the
left of the current block.  Hence every slot to the right of all processed
blocks still carries the initial Green scale.  In particular, the outgoing
slot of the next block has exactly that scale.

This closes the numerical premise exposed by the complete active-edge ledger:
choosing the initial Green scale at least one gives
`1 ≤ scale outgoingEdge` at every production step without discarding any
coupling power.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- Reachability of a quantitative budget scale along the same genuine
proper-step history as the analytic edge state. -/
inductive R322AnalyticBudgetScaleReachable
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (C lam ε K A : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q) :
    R322AnalyticEdgeState q hq →
      (Fin (2 * q - 1) → ℝ) → Prop
  | initial :
      R322AnalyticBudgetScaleReachable
        hq ρ C lam ε K A κ hκ
        (r322InitialAnalyticEdgeState q hq)
        (fun _ => A)
  | update
      {scale : Fin (2 * q - 1) → ℝ}
      (ctx : R322AnalyticProperStepContext q hq)
      (hpairing : ctx.pairing = κ)
      (previous :
        R322AnalyticBudgetScaleReachable
          hq ρ C lam ε K A κ hκ
          ctx.state scale) :
      R322AnalyticBudgetScaleReachable
        hq ρ C lam ε K A κ hκ
        (ctx.nextState ρ lam ε)
        (ctx.budgetUpdatedEdgeScale scale C lam K)

namespace R322AnalyticProperStepContext

variable {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticProperStepContext q hq)

/-- A budget update leaves every edge strictly to the right of the current
block unchanged. -/
theorem budgetUpdatedEdgeScale_eq_of_right_lt
    (scale : Fin (2 * q - 1) → ℝ)
    (C lam K : ℝ)
    (edge : Fin (2 * q - 1))
    (hright :
      ctx.step.1.2 <
        r322AnalyticEdgeLeftVertex edge) :
    ctx.budgetUpdatedEdgeScale scale C lam K edge =
      scale edge := by
  apply ctx.budgetUpdatedEdgeScale_of_ne
  intro hedge
  have hpreLt :
      r322AnalyticPredecessorVertex
          ctx.state ctx.step ctx.bounds.1 <
        ctx.step.1.1 :=
    r322AnalyticPredecessorVertex_lt_left
      ctx.state ctx.step ctx.bounds.1
  have hstepMem :
      ctx.step ∈ r322AnalyticSchedule ctx.pairing := by
    rw [ctx.schedule_eq]
    simp
  have hstepLt :
      ctx.step.1.1 < ctx.step.1.2 :=
    extract_mem_fst_lt_snd ctx.pairing ctx.step.1
      (r322AnalyticSchedule_endpoint_mem_extract
        ctx.pairing hstepMem)
  have hval := congrArg Fin.val hedge
  change ctx.step.1.2.val < edge.val at hright
  change edge.val =
    (r322AnalyticPredecessorVertex
      ctx.state ctx.step ctx.bounds.1).val at hval
  omega

end R322AnalyticProperStepContext

namespace R322AnalyticBudgetScaleReachable

variable {q : ℕ} {hq : 1 ≤ q}
    {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    {state : R322AnalyticEdgeState q hq}
    {scale : Fin (2 * q - 1) → ℝ}

/-- Every scale slot strictly beyond all processed right endpoints still
equals the initial Green scale. -/
theorem edgeScale_eq_base_of_processed_right_lt
    (hreach :
      R322AnalyticBudgetScaleReachable
        hq ρ C lam ε K A κ hκ state scale)
    (edge : Fin (2 * q - 1))
    (hfuture :
      ∀ earlier ∈ state.processed,
        earlier.1.2 <
          r322AnalyticEdgeLeftVertex edge) :
    scale edge = A := by
  induction hreach with
  | initial =>
      rfl
  | @update oldScale ctx hpairing previous ih =>
      have hcurrent :
          ctx.step.1.2 <
            r322AnalyticEdgeLeftVertex edge := by
        apply hfuture ctx.step
        simp [R322AnalyticProperStepContext.nextState]
      have hprevious :
          ∀ earlier ∈ ctx.state.processed,
            earlier.1.2 <
              r322AnalyticEdgeLeftVertex edge := by
        intro earlier hearlier
        apply hfuture earlier
        simp [R322AnalyticProperStepContext.nextState,
          hearlier]
      rw [
        ctx.budgetUpdatedEdgeScale_eq_of_right_lt
          oldScale C lam K edge hcurrent]
      exact ih hprevious

/-- The outgoing scale of the next genuine proper step is exactly the
initial Green scale. -/
theorem outgoingEdgeScale_eq_base
    (hreach :
      R322AnalyticBudgetScaleReachable
        hq ρ C lam ε K A κ hκ state scale)
    (ctx : R322AnalyticProperStepContext q hq)
    (hpairing : ctx.pairing = κ)
    (hstateEq : ctx.state = state) :
    scale ctx.outgoingEdge = A := by
  subst state
  subst κ
  apply hreach.edgeScale_eq_base_of_processed_right_lt
  intro earlier hearlier
  have hp :=
    r322AnalyticSchedule_pairwise_right_lt ctx.pairing
  rw [ctx.schedule_eq, List.pairwise_append] at hp
  have hright :
      earlier.1.2 < ctx.step.1.2 :=
    hp.2.2 earlier hearlier ctx.step (by simp)
  simpa [R322AnalyticProperStepContext.outgoingEdge,
    r322AnalyticOutgoingEdge,
    r322AnalyticEdgeLeftVertex] using hright

/-- A base scale at least one discharges the outgoing normalization premise
of the complete budget-certificate update. -/
theorem edgeCertificate_to_budgetUpdatedEdgeScale
    (hreach :
      R322AnalyticBudgetScaleReachable
        hq ρ C lam ε K A κ hκ state scale)
    (ctx : R322AnalyticProperStepContext q hq)
    (hpairing : ctx.pairing = κ)
    (hstateEq : ctx.state = state)
    (hA : 1 ≤ A)
    (hcert :
      R322AnalyticEdgeCertificate
        (ctx.nextState ρ lam ε)
        (r322AnalyticUpdatedEdgeScale ctx scale
          (r322AnalyticInternalEdgeScaleProduct ctx scale)
          C lam K)) :
    R322AnalyticEdgeCertificate
      (ctx.nextState ρ lam ε)
      (ctx.budgetUpdatedEdgeScale scale C lam K) := by
  apply
    ctx.edgeCertificate_to_budgetUpdatedEdgeScale
      ρ lam ε C K scale hcert
  rw [hreach.outgoingEdgeScale_eq_base
    ctx hpairing hstateEq]
  exact hA

end R322AnalyticBudgetScaleReachable

/-! ## Initial normalization -/

/-- The all-Green initial certificate may be chosen with a scale at least
one. -/
theorem exists_r322InitialAnalyticEdgeCertificate_one_le
    (q : ℕ) (hq : 1 ≤ q) :
    ∃ A : ℝ, 1 ≤ A ∧
      R322AnalyticEdgeCertificate
        (r322InitialAnalyticEdgeState q hq)
        (fun _ => A) := by
  obtain ⟨A₀, hA₀, hcert⟩ :=
    exists_r322InitialAnalyticEdgeCertificate q hq
  let A : ℝ := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  have hA₀A : A₀ ≤ A := le_max_right _ _
  refine ⟨A, hA, ?_⟩
  apply
    R322AnalyticProperStepContext.edgeCertificate_of_pointwise_scale_le
      hcert
  intro _edge
  exact hA₀A

/-- One initial Green scale works simultaneously at every perturbative
order.  This quantifier order is needed when the final P-3.5a constant is
chosen before `q`. -/
theorem exists_r322InitialAnalyticEdgeCertificate_one_le_uniform :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (q : ℕ) (hq : 1 ≤ q),
        R322AnalyticEdgeCertificate
          (r322InitialAnalyticEdgeState q hq)
          (fun _ => A) := by
  obtain ⟨A₀, hA₀, hgreen⟩ := greenFn_le
  let A : ℝ := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  have hA₀A : A₀ ≤ A := le_max_right _ _
  refine ⟨A, hA, ?_⟩
  intro q hq
  let hcert :
      R322AnalyticEdgeCertificate
        (r322InitialAnalyticEdgeState q hq)
        (fun _ => A₀) :=
    { scale_pos := fun _ => hA₀
      memE := by
        intro edge
        simpa [r322InitialAnalyticEdgeState] using greenFn_memE
      bound := by
        intro edge z hz
        change |greenFn z| ≤ A₀ * invSqKer z
        exact greenFn_abs_le_mul_invSqKer hgreen z hz }
  apply
    R322AnalyticProperStepContext.edgeCertificate_of_pointwise_scale_le
      hcert
  intro _edge
  exact hA₀A

end

end Anderson4D
