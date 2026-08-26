import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticProcessedIntegrandBridge
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticTerminalStepCollapse

/-!
# Reachability along the genuine R-322 proper prefix

Every proper prefix of the paper-ordered analytic schedule generates an
actual heterogeneous edge state.  The construction iterates the signed
three-kernel update recorded by `R322AnalyticAbsorbedState`; it does not
identify an unintegrated production integrand pointwise with the resulting
state.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- A genuine proper prefix of the analytic schedule produces a reachable
heterogeneous state whose processed history is exactly that prefix. -/
theorem exists_r322AnalyticAbsorbedState_of_properPrefix
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (pre suffix : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = pre ++ suffix)
    (hproper :
      ∀ step ∈ pre,
        step.1 ≠ r322WholeEndpoint q hq) :
    ∃ state : R322AnalyticEdgeState q hq,
      R322AnalyticAbsorbedState ρ lam ε hq κ hκ state ∧
        state.processed = pre := by
  induction pre using List.reverseRecOn generalizing suffix with
  | nil =>
      refine ⟨r322InitialAnalyticEdgeState q hq,
        R322AnalyticAbsorbedState.initial, rfl⟩
  | append_singleton pre step ih =>
      have hprefix :
          r322AnalyticSchedule κ =
            pre ++ step :: suffix := by
        simpa [List.append_assoc] using hschedule
      have hproperPre :
          ∀ s ∈ pre,
            s.1 ≠ r322WholeEndpoint q hq := by
        intro s hs
        exact hproper s (by
          simp only [List.mem_append, List.mem_singleton]
          exact Or.inl hs)
      obtain ⟨state, hstate, hprocessed⟩ :=
        ih (step :: suffix) hprefix hproperPre
      let ctx : R322AnalyticProperStepContext q hq :=
        { state := state
          pairing := κ
          pairing_mem := hκ
          suffix := suffix
          step := step
          schedule_eq := by
            rw [hprocessed]
            exact hprefix
          proper := hproper step (by simp) }
      refine ⟨ctx.nextState ρ lam ε,
        R322AnalyticAbsorbedState.update ctx rfl hstate, ?_⟩
      simp [R322AnalyticProperStepContext.nextState, ctx,
        hprocessed]

/-- The proper-prefix/terminal decomposition therefore reaches a certified
terminal context on the actual heterogeneous edge state. -/
theorem exists_r322AnalyticReachableTerminalContext
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q) :
    ∃ ctx : R322AnalyticTerminalStepContext q hq,
      R322AnalyticAbsorbedState ρ lam ε hq κ hκ ctx.state := by
  obtain ⟨proper, terminal, hschedule, hterminal, hproper⟩ :=
    r322AnalyticSchedule_eq_proper_append_terminal_of_isNonSplit
      hq (mem_nonSplitPairings.mp hκ)
  obtain ⟨state, hstate, hprocessed⟩ :=
    exists_r322AnalyticAbsorbedState_of_properPrefix
      hq ρ lam ε κ hκ proper [terminal]
      hschedule hproper
  let ctx : R322AnalyticTerminalStepContext q hq :=
    { state := state
      pairing := κ
      pairing_mem := hκ
      terminal := terminal
      schedule_eq := by
        rw [hprocessed]
        exact hschedule
      terminal_endpoint := hterminal }
  exact ⟨ctx, hstate⟩

end

end Anderson4D
