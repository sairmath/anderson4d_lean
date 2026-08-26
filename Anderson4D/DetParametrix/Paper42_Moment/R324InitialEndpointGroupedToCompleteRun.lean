import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointIntegratedGroupedMajorant
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperCompleteNestedRun

/-!
# Initial endpoint-grouped majorant to the complete nested run

This file closes the pointwise seam between the grouped majorant obtained
after the four external endpoint integrations and the literal initial
Steps 2--3 density.  It only reindexes the two endpoint-erased terminal
half paths and the still-grouped residual primitive sum.  No nested-shell
iteration is performed here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}

/-- On the initial nested carrier, the left-half pullback is exactly the
completed left terminal carrier.  This carrier identity is also used by the
endpoint-pattern splice, so it is intentionally public. -/
theorem initial_leftHalfPullback_eq_terminalActive
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)
    (π : κp.singles ≃ κm.singles) :
    r324LeftHalfPullback
        (R324NestedCrossResidualPrefix.initial κp κm π).activeCarrier =
      terminal.left.state.active := by
  ext i
  rw [mem_r324LeftHalfPullback,
    R324NestedCrossResidualPrefix.initial_activeCarrier_eq_momentResidualActive,
    leftMomentIndex_mem_momentResidualActive_iff,
    ← terminal.left.active_eq_finalActive_of_processed_eq_schedule
      terminal.left_processed]

/-- On the initial nested carrier, the right-half pullback is exactly the
completed right terminal carrier.  This carrier identity is also used by the
endpoint-pattern splice, so it is intentionally public. -/
theorem initial_rightHalfPullback_eq_terminalActive
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)
    (π : κp.singles ≃ κm.singles) :
    r324RightHalfPullback
        (R324NestedCrossResidualPrefix.initial κp κm π).activeCarrier =
      terminal.right.state.active := by
  ext i
  rw [mem_r324RightHalfPullback,
    R324NestedCrossResidualPrefix.initial_activeCarrier_eq_momentResidualActive,
    rightMomentIndex_mem_momentResidualActive_iff,
    ← terminal.right.active_eq_finalActive_of_processed_eq_schedule
      terminal.right_processed]

private theorem terminalProduct_left_eq_initialLeftTuple
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)
    (π : κp.singles ≃ κm.singles)
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial κp κm π).remaining =
        head :: tail)
    (v : terminal.NestedCoordinate π → T4) :
    ((terminal.terminalProductPiMeasurableEquivNested π).symm v).1 =
      terminal.leftTupleOfNestedStep
        (r324InitialNestedCrossStepContext
          κp κm π head tail hremaining) v := by
  funext i
  let e := terminal.terminalProductPiMeasurableEquivNested π
  let step :=
    r324InitialNestedCrossStepContext κp κm π head tail hremaining
  have hiNested :
      leftMomentIndex i.1 ∈
        (R324NestedCrossResidualPrefix.initial κp κm π).activeCarrier := by
    rw [R324NestedCrossResidualPrefix.initial_activeCarrier_eq_momentResidualActive,
      leftMomentIndex_mem_momentResidualActive_iff,
      ← terminal.left.active_eq_finalActive_of_processed_eq_schedule
        terminal.left_processed]
    exact i.2
  let nestedI : terminal.NestedCoordinate π :=
    ⟨leftMomentIndex i.1, hiNested⟩
  have hcoord :
      nestedI = terminal.survivingSumEquivNested π (Sum.inl i) := by
    apply Subtype.ext
    rfl
  calc
    (e.symm v).1 i =
        e (e.symm v)
          (terminal.survivingSumEquivNested π (Sum.inl i)) := by
      symm
      exact terminal.terminalProductPiMeasurableEquivNested_apply_left
        π (e.symm v).1 (e.symm v).2 i
    _ = v nestedI := by
      rw [e.apply_symm_apply, hcoord]
    _ = step.reconstruct v (leftMomentIndex i.1) := by
      symm
      exact step.reconstruct_surviving v ⟨leftMomentIndex i.1, hiNested⟩
    _ = terminal.leftTupleOfNestedStep step v i := rfl

private theorem terminalProduct_right_eq_initialRightTuple
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)
    (π : κp.singles ≃ κm.singles)
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial κp κm π).remaining =
        head :: tail)
    (v : terminal.NestedCoordinate π → T4) :
    ((terminal.terminalProductPiMeasurableEquivNested π).symm v).2 =
      terminal.rightTupleOfNestedStep
        (r324InitialNestedCrossStepContext
          κp κm π head tail hremaining) v := by
  funext i
  let e := terminal.terminalProductPiMeasurableEquivNested π
  let step :=
    r324InitialNestedCrossStepContext κp κm π head tail hremaining
  have hiNested :
      rightMomentIndex i.1 ∈
        (R324NestedCrossResidualPrefix.initial κp κm π).activeCarrier := by
    rw [R324NestedCrossResidualPrefix.initial_activeCarrier_eq_momentResidualActive,
      rightMomentIndex_mem_momentResidualActive_iff,
      ← terminal.right.active_eq_finalActive_of_processed_eq_schedule
        terminal.right_processed]
    exact i.2
  let nestedI : terminal.NestedCoordinate π :=
    ⟨rightMomentIndex i.1, hiNested⟩
  have hcoord :
      nestedI = terminal.survivingSumEquivNested π (Sum.inr i) := by
    apply Subtype.ext
    rfl
  calc
    (e.symm v).2 i =
        e (e.symm v)
          (terminal.survivingSumEquivNested π (Sum.inr i)) := by
      symm
      exact terminal.terminalProductPiMeasurableEquivNested_apply_right
        π (e.symm v).1 (e.symm v).2 i
    _ = v nestedI := by
      rw [e.apply_symm_apply, hcoord]
    _ = step.reconstruct v (rightMomentIndex i.1) := by
      symm
      exact step.reconstruct_surviving v ⟨rightMomentIndex i.1, hiNested⟩
    _ = terminal.rightTupleOfNestedStep step v i := rfl

private theorem terminalDoubledReconstruct_symm_eq_initialStepReconstruct
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)
    (π : κp.singles ≃ κm.singles)
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial κp κm π).remaining =
        head :: tail)
    (v : terminal.NestedCoordinate π → T4) :
    terminal.terminalDoubledReconstruct
        ((terminal.terminalProductPiMeasurableEquivNested π).symm v) =
      (r324InitialNestedCrossStepContext
        κp κm π head tail hremaining).reconstruct v := by
  let e := terminal.terminalProductPiMeasurableEquivNested π
  calc
    terminal.terminalDoubledReconstruct (e.symm v) =
        terminal.nestedReconstruct π (e (e.symm v)) :=
      terminal.terminalDoubledReconstruct_eq_nestedReconstruct π (e.symm v)
    _ = terminal.nestedReconstruct π v := by rw [e.apply_symm_apply]
    _ = (r324InitialNestedCrossStepContext
          κp κm π head tail hremaining).reconstruct v := by
      rfl

/-! ## Public initial-carrier transport package

The three lemmas above are the coordinate calculation used by the complete
run.  The marked-word run needs exactly the same calculation, with the
marked payload left untouched.  These wrappers deliberately expose only
the resulting equalities; no implementation detail of the initial endpoint
majorant is exported. -/

/-- The completed left terminal tuple is the left tuple read by the initial
nested step. -/
theorem initialTerminalProduct_left_eq_initialLeftTuple
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)
    (π : κp.singles ≃ κm.singles)
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial κp κm π).remaining =
        head :: tail)
    (v : terminal.NestedCoordinate π → T4) :
    ((terminal.terminalProductPiMeasurableEquivNested π).symm v).1 =
      terminal.leftTupleOfNestedStep
        (r324InitialNestedCrossStepContext
          κp κm π head tail hremaining) v := by
  exact terminalProduct_left_eq_initialLeftTuple
    terminal π head tail hremaining v

/-- The completed right terminal tuple is the right tuple read by the
initial nested step. -/
theorem initialTerminalProduct_right_eq_initialRightTuple
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)
    (π : κp.singles ≃ κm.singles)
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial κp κm π).remaining =
        head :: tail)
    (v : terminal.NestedCoordinate π → T4) :
    ((terminal.terminalProductPiMeasurableEquivNested π).symm v).2 =
      terminal.rightTupleOfNestedStep
        (r324InitialNestedCrossStepContext
          κp κm π head tail hremaining) v := by
  exact terminalProduct_right_eq_initialRightTuple
    terminal π head tail hremaining v

/-- Reconstructing the completed terminal pair agrees with reconstructing
the initial nested step. -/
theorem initialTerminalDoubledReconstruct_symm_eq_stepReconstruct
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)
    (π : κp.singles ≃ κm.singles)
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial κp κm π).remaining =
        head :: tail)
    (v : terminal.NestedCoordinate π → T4) :
    terminal.terminalDoubledReconstruct
        ((terminal.terminalProductPiMeasurableEquivNested π).symm v) =
      (r324InitialNestedCrossStepContext
        κp κm π head tail hremaining).reconstruct v := by
  exact terminalDoubledReconstruct_symm_eq_initialStepReconstruct
    terminal π head tail hremaining v

theorem initialNestedEndpointIntegratedGroupedMajorant_mul_coupling_eq
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)
    (leftScale rightScale : Fin (m + 1) → ℝ)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (π : κp.singles ≃ κm.singles)
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial κp κm π).remaining =
        head :: tail)
    (v : terminal.NestedCoordinate π → T4) :
    let step :=
      r324InitialNestedCrossStepContext κp κm π head tail hremaining
    let hleftInitial :
        (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
      change (r324LeftHalfPullback
        (R324NestedCrossResidualPrefix.initial κp κm π).activeCarrier).Nonempty
      rw [initial_leftHalfPullback_eq_terminalActive terminal π]
      exact hleft
    let hrightInitial :
        (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
      change (r324RightHalfPullback
        (R324NestedCrossResidualPrefix.initial κp κm π).activeCarrier).Nonempty
      rw [initial_rightHalfPullback_eq_terminalActive terminal π]
      exact hright
    lamEps lam ε ^ (2 * step.residual.remainingOrder) *
        terminal.initialNestedEndpointIntegratedGroupedMajorant
          leftScale rightScale hleft hright π v =
      (((∏ edge ∈ terminal.left.activeEdgeSlots, leftScale edge) *
          (∏ edge ∈ terminal.right.activeEdgeSlots, rightScale edge)) *
        invSqKerMass ^ 4) *
        terminal.completeNestedRunDensity
          step hleftInitial hrightInitial v := by
  dsimp only
  let step :=
    r324InitialNestedCrossStepContext κp κm π head tail hremaining
  change step.SurvivingCoordinate → T4 at v
  have hleftCarrier :=
    initial_leftHalfPullback_eq_terminalActive terminal π
  have hrightCarrier :=
    initial_rightHalfPullback_eq_terminalActive terminal π
  have hleftInitial :
      (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
    change (r324LeftHalfPullback
      (R324NestedCrossResidualPrefix.initial κp κm π).activeCarrier).Nonempty
    rw [hleftCarrier]
    exact hleft
  have hrightInitial :
      (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
    change (r324RightHalfPullback
      (R324NestedCrossResidualPrefix.initial κp κm π).activeCarrier).Nonempty
    rw [hrightCarrier]
    exact hright
  have hleftTuple :=
    terminalProduct_left_eq_initialLeftTuple
      terminal π head tail hremaining v
  have hrightTuple :=
    terminalProduct_right_eq_initialRightTuple
      terminal π head tail hremaining v
  have hreconstruct :=
    terminalDoubledReconstruct_symm_eq_initialStepReconstruct
      terminal π head tail hremaining v
  have hleftPath :
      terminal.left.endpointErasedInvSqChainProduct hleft
          ((terminal.terminalProductPiMeasurableEquivNested π).symm v).1 =
        terminal.nestedLeftHalfInvSqProduct step
          step.residual.activeCarrier hleftInitial v := by
    rw [terminal.left.endpointErasedInvSqChainProduct_eq_halfInvSqChainProduct,
      hleftTuple]
    unfold nestedLeftHalfInvSqProduct
    dsimp only [step, r324InitialNestedCrossStepContext]
    simp only [hleftCarrier]
  have hrightPath :
      terminal.right.endpointErasedInvSqChainProduct hright
          ((terminal.terminalProductPiMeasurableEquivNested π).symm v).2 =
        terminal.nestedRightHalfInvSqProduct step
          step.residual.activeCarrier hrightInitial v := by
    rw [terminal.right.endpointErasedInvSqChainProduct_eq_halfInvSqChainProduct,
      hrightTuple]
    unfold nestedRightHalfInvSqProduct
    dsimp only [step, r324InitialNestedCrossStepContext]
    simp only [hrightCarrier]
  have hresidual :
      r324ResidualPrimitiveSumProduct ρ ε κp κm π
          (terminal.terminalDoubledReconstruct
            ((terminal.terminalProductPiMeasurableEquivNested π).symm v)) =
        r324NestedResidualPrimitiveSumProduct
          ρ ε κp κm π step.residual (step.reconstruct v) := by
    rw [hreconstruct]
    dsimp only [step, r324InitialNestedCrossStepContext]
    rw [r324NestedResidualPrimitiveSumProduct_initial]
  unfold initialNestedEndpointIntegratedGroupedMajorant
    endpointIntegratedGroupedMajorant completeNestedRunDensity
  rw [hleftPath, hrightPath, hresidual]
  ring

/-- The initial endpoint-integrated grouped bound is exactly the literal
initial Steps 2--3 complete-run density, up to the two stored terminal
scale products and the four endpoint inverse-square masses.  The residual
primitive covariance sum remains grouped and the coupling is inserted only
after the endpoint norm bound has been established. -/
theorem ae_coupling_mul_norm_initialNestedEndpointIntegratedResidualDensity_le_completeNestedRun
    {leftRes : R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes : R324WithinHalfResidualPrefix ρ lam ε κm}
    {leftInitialScale rightInitialScale : Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        leftRes leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        rightRes rightInitialScale)
    (π : κp.singles ≃ κm.singles)
    (hleft : leftTrace.terminalPrefix.state.active.Nonempty)
    (hright : rightTrace.terminalPrefix.state.active.Nonempty)
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial κp κm π).remaining =
        head :: tail)
    (α β : Z4) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
    let step :=
      r324InitialNestedCrossStepContext κp κm π head tail hremaining
    let hleftInitial :
        (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
      change (r324LeftHalfPullback
        (R324NestedCrossResidualPrefix.initial κp κm π).activeCarrier).Nonempty
      rw [initial_leftHalfPullback_eq_terminalActive terminal π]
      exact hleft
    let hrightInitial :
        (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
      change (r324RightHalfPullback
        (R324NestedCrossResidualPrefix.initial κp κm π).activeCarrier).Nonempty
      rw [initial_rightHalfPullback_eq_terminalActive terminal π]
      exact hright
    (fun v =>
      lamEps lam ε ^ (2 * step.residual.remainingOrder) *
        ‖terminal.initialNestedEndpointIntegratedResidualDensity
          π hleft hright α β v‖) ≤ᵐ[
      Measure.pi fun _ : terminal.NestedCoordinate π => paperMeasure]
      fun v =>
        (((∏ edge ∈ terminal.left.activeEdgeSlots,
              leftTrace.terminalScale edge) *
            (∏ edge ∈ terminal.right.activeEdgeSlots,
              rightTrace.terminalScale edge)) *
          invSqKerMass ^ 4) *
          terminal.completeNestedRunDensity
            step hleftInitial hrightInitial v := by
  dsimp only
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
  let step :=
    r324InitialNestedCrossStepContext κp κm π head tail hremaining
  have hmajorant :=
    ae_norm_initialNestedEndpointIntegratedResidualDensity_le_groupedMajorant
      leftTrace rightTrace π hleft hright α β
  filter_upwards [hmajorant] with v hv
  calc
    lamEps lam ε ^ (2 * step.residual.remainingOrder) *
        ‖terminal.initialNestedEndpointIntegratedResidualDensity
          π hleft hright α β v‖ ≤
      lamEps lam ε ^ (2 * step.residual.remainingOrder) *
        terminal.initialNestedEndpointIntegratedGroupedMajorant
          leftTrace.terminalScale rightTrace.terminalScale
          hleft hright π v :=
      mul_le_mul_of_nonneg_left hv
        ((even_two_mul step.residual.remainingOrder).pow_nonneg _)
    _ = _ :=
      initialNestedEndpointIntegratedGroupedMajorant_mul_coupling_eq
        terminal leftTrace.terminalScale rightTrace.terminalScale
        hleft hright π head tail hremaining v

end R324TwoHalfTerminalData

end

end Anderson4D
