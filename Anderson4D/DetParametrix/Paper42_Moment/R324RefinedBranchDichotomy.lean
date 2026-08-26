import Anderson4D.DetParametrix.Paper41_Renorm.R322EndpointFiber
import Anderson4D.DetParametrix.Paper42_Moment.R324CertifiedTwoHalfPhysicalCollapse
import Anderson4D.DetParametrix.Paper42_Moment.R324ConcreteRoutingClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointIntegratedResidualBridge

/-!
# The refined full/full versus residual branch dichotomy for R-324

For a realized refined schedule, the two within-half partial pairings have
equivalent single carriers.  Hence either the representative has a residual
single, or both halves are full.  Fullness in the second branch depends only
on the fixed within-half endpoint signature and therefore propagates to every
contraction in the refined fibre.

In the residual branch, the same single witness supplies nonempty active
carriers in both completed certified traces.  This file records only these
exact structural facts; it introduces no analytic estimate.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-! ## The representative dichotomy and fibrewise propagation -/

/-- A refined representative either has a residual single in its left half,
or both of its within-half pairings are full. -/
theorem r324RefinedScheduleRepresentative_singles_nonempty_or_isFull
    {m : ℕ} (p : R324RefinedScheduleIndex m) :
    let e₀ := r324RefinedScheduleRepresentative p
    e₀.1.singles.Nonempty ∨
      (e₀.1.IsFull ∧ e₀.2.1.IsFull) := by
  classical
  dsimp only
  let e₀ := r324RefinedScheduleRepresentative p
  by_cases hsingles : e₀.1.singles.Nonempty
  · exact Or.inl hsingles
  · right
    have hpempty : e₀.1.singles = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hsingles
    have hmempty : e₀.2.1.singles = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hmnonempty
      obtain ⟨j, hj⟩ := hmnonempty
      let i : e₀.1.singles := e₀.2.2.symm ⟨j, hj⟩
      exact hsingles ⟨i.1, i.2⟩
    exact
      ⟨PartialPairing.isFull_iff_singles_eq_empty.mpr hpempty,
        PartialPairing.isFull_iff_singles_eq_empty.mpr hmempty⟩

/-- If the canonical representative of a refined schedule is full in both
halves, then every contraction in that refined fibre is full in both halves.
This uses only equality of the fixed within-half endpoint signature. -/
theorem r324RefinedContractionFiber_isFull_of_representative_isFull
    {m : ℕ} (p : R324RefinedScheduleIndex m)
    (hfull :
      (r324RefinedScheduleRepresentative p).1.IsFull ∧
        (r324RefinedScheduleRepresentative p).2.1.IsFull)
    {e : MomentContraction m}
    (he :
      e ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1) :
    e.1.IsFull ∧ e.2.1.IsFull := by
  let e₀ := r324RefinedScheduleRepresentative p
  have heSignature :
      momentContractionSignature e = p.1.1 :=
    (mem_momentRefinedContractionFiber.mp he).1
  have he₀Signature :
      momentContractionSignature e₀ = p.1.1 :=
    mem_momentContractionFiber.mp
      (r324RefinedScheduleRepresentative_mem p)
  obtain ⟨hleftSignature, hrightSignature⟩ :=
    reductionEndpointSignatures_eq_of_momentContractionSignature_eq
      e e₀ (heSignature.trans he₀Signature.symm)
  exact
    ⟨isFull_of_reductionEndpointSignature_eq
        e₀.1 e.1 hfull.1 hleftSignature,
      isFull_of_reductionEndpointSignature_eq
        e₀.2.1 e.2.1 hfull.2 hrightSignature⟩

/-- Fibrewise form of the refined branch split used downstream: either the
representative has a residual single, or the whole refined fibre is
full/full. -/
theorem r324RefinedSchedule_branchDichotomy
    {m : ℕ} (p : R324RefinedScheduleIndex m) :
    (r324RefinedScheduleRepresentative p).1.singles.Nonempty ∨
      ∀ e ∈ momentRefinedContractionFiber m p.1.1 p.2.1,
        e.1.IsFull ∧ e.2.1.IsFull := by
  rcases
      r324RefinedScheduleRepresentative_singles_nonempty_or_isFull p with
    hsingles | hfull
  · exact Or.inl hsingles
  · exact Or.inr fun e he =>
      r324RefinedContractionFiber_isFull_of_representative_isFull
        p hfull he

/-! ## Active-carrier witnesses in the residual branch -/

namespace R324TwoHalfTerminalData

/-- A residual single in the refined representative supplies nonempty active
carriers in both completed half traces. -/
theorem active_nonempty_of_refinedScheduleRepresentative_singles_nonempty
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    (p : R324RefinedScheduleIndex m)
    (terminal :
      R324TwoHalfTerminalData ρ lam ε
        (r324RefinedScheduleRepresentative p).1
        (r324RefinedScheduleRepresentative p).2.1)
    (hsingles :
      (r324RefinedScheduleRepresentative p).1.singles.Nonempty) :
    terminal.left.state.active.Nonempty ∧
      terminal.right.state.active.Nonempty :=
  ⟨terminal.left_active_nonempty_of_singles_nonempty hsingles,
    terminal.right_active_nonempty_of_singles_nonempty
      (r324RefinedScheduleRepresentative p).2.2 hsingles⟩

/-- Specialization of the active-carrier witnesses to the terminal datum
packaged by two certified within-half traces. -/
theorem certifiedTraces_active_nonempty_of_refinedScheduleRepresentative
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    (p : R324RefinedScheduleIndex m)
    {leftRes :
      R324WithinHalfResidualPrefix ρ lam ε
        (r324RefinedScheduleRepresentative p).1}
    {rightRes :
      R324WithinHalfResidualPrefix ρ lam ε
        (r324RefinedScheduleRepresentative p).2.1}
    {leftScale rightScale : Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        leftRes leftScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        rightRes rightScale)
    (hsingles :
      (r324RefinedScheduleRepresentative p).1.singles.Nonempty) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces
        leftTrace rightTrace
    terminal.left.state.active.Nonempty ∧
      terminal.right.state.active.Nonempty := by
  exact
    active_nonempty_of_refinedScheduleRepresentative_singles_nonempty
      p
      (R324TwoHalfTerminalData.ofCertifiedTraces
        leftTrace rightTrace)
      hsingles

end R324TwoHalfTerminalData

end

end Anderson4D
