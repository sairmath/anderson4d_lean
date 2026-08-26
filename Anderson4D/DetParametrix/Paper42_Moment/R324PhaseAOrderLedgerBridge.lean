import Anderson4D.DetParametrix.Paper42_Moment.R324NestedCrossBudgetIteration
import Anderson4D.DetParametrix.Paper42_Moment.R324ConcreteRoutingClosure

/-!
# Exact Phase-A-to-terminal order ledger for R-324

This module records the missing numeric bridge between the three literal
primitive schedules used in the physical construction and the unified
primitive-block partition.  The bridge is derived from the actual schedule
permutations, the two doubled-coordinate embeddings, and the residual
inside-to-outside schedule.  It does not assume an order decomposition.

The resulting equality splits the ambient perturbative order into the left
within-half suffix, the right within-half suffix, the consumed nested-cross
prefix, and the terminal marked/suffix payload.  The final section also
records the structural data that survive at that payload and the exact
identification of the corrected refined-fibre sum with its physical integral.
No analytic estimate or target-shaped final bound is introduced here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## The two Phase-A schedules inside the doubled carrier -/

@[simp]
theorem residualBlockOrder_image_leftMomentIndex
    {m : ℕ} (B : Finset (Fin m)) :
    residualBlockOrder (B.image leftMomentIndex) =
      residualBlockOrder B := by
  unfold residualBlockOrder
  rw [Finset.card_image_of_injective _
    leftMomentIndex_injective]

@[simp]
theorem residualBlockOrder_image_rightMomentIndex
    {m : ℕ} (B : Finset (Fin m)) :
    residualBlockOrder (B.image rightMomentIndex) =
      residualBlockOrder B := by
  unfold residualBlockOrder
  rw [Finset.card_image_of_injective _
    rightMomentIndex_injective]

/-- The literal left within-half initial suffix has the same exact order as
the left-copy block family in the unified doubled schedule. -/
theorem r324LeftWithinHalfInitial_remainingOrder_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (κp : PartialPairing (Fin m)) :
    (R324WithinHalfResidualPrefix.initial
        ρ lam ε κp).remainingOrder =
      ((momentLeftExtractionBlocks κp).map
        residualBlockOrder).sum := by
  have hperm :=
    (r322AnalyticSchedule_blocks_perm_extractionBlocks κp).map
      residualBlockOrder
  have hsum := hperm.sum_eq
  calc
    (R324WithinHalfResidualPrefix.initial
        ρ lam ε κp).remainingOrder =
        ((extractionBlocks κp).map
          residualBlockOrder).sum := by
      simpa only [
        R324WithinHalfResidualPrefix.remainingOrder,
        R324WithinHalfResidualPrefix.initial,
        List.map_map,
        Function.comp_def] using hsum
    _ =
        ((momentLeftExtractionBlocks κp).map
          residualBlockOrder).sum := by
      simp only [
        momentLeftExtractionBlocks,
        List.map_map,
        Function.comp_def,
        residualBlockOrder_image_leftMomentIndex]

/-- The literal right within-half initial suffix has the same exact order as
the right-copy block family in the unified doubled schedule. -/
theorem r324RightWithinHalfInitial_remainingOrder_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (κm : PartialPairing (Fin m)) :
    (R324WithinHalfResidualPrefix.initial
        ρ lam ε κm).remainingOrder =
      ((momentRightExtractionBlocks κm).map
        residualBlockOrder).sum := by
  have hperm :=
    (r322AnalyticSchedule_blocks_perm_extractionBlocks κm).map
      residualBlockOrder
  have hsum := hperm.sum_eq
  calc
    (R324WithinHalfResidualPrefix.initial
        ρ lam ε κm).remainingOrder =
        ((extractionBlocks κm).map
          residualBlockOrder).sum := by
      simpa only [
        R324WithinHalfResidualPrefix.remainingOrder,
        R324WithinHalfResidualPrefix.initial,
        List.map_map,
        Function.comp_def] using hsum
    _ =
        ((momentRightExtractionBlocks κm).map
          residualBlockOrder).sum := by
      simp only [
        momentRightExtractionBlocks,
        List.map_map,
        Function.comp_def,
        residualBlockOrder_image_rightMomentIndex]

/-- The literal initial nested-cross suffix has the exact order of the
nonempty residual block family in the unified doubled schedule. -/
theorem r324NestedCrossInitial_remainingOrder_eq
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (R324NestedCrossResidualPrefix.initial
        κp κm π).remainingOrder =
      ((nonemptyMomentResidualCollapseBlocks
          κp κm π).map residualBlockOrder).sum := by
  simpa only [
      R324NestedCrossResidualPrefix.initial,
      R324NestedCrossResidualPrefix.remainingOrder] using
    r324NestedCrossSchedule_sum_orders κp κm π

/-! ## Ambient order conservation -/

/-- The two actual Phase-A initial suffixes and the actual initial
nested-cross suffix partition the full ambient perturbative order.

This is a derived schedule theorem: its proof passes through the unified
nonempty primitive-block ledger and does not take the desired equality as
an input. -/
theorem r324InitialSchedules_remainingOrders_eq_ambient
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (R324WithinHalfResidualPrefix.initial
        ρ lam ε κp).remainingOrder +
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κm).remainingOrder +
        (R324NestedCrossResidualPrefix.initial
          κp κm π).remainingOrder =
      m := by
  have htotal :=
    sum_momentNonemptyPrimitiveBlockOrders κp κm π
  unfold momentNonemptyPrimitiveBlocks at htotal
  rw [sum_residualBlockOrder_filter_nonempty] at htotal
  unfold momentAllPrimitiveBlocks at htotal
  simp only [List.map_append, List.sum_append] at htotal
  have hresidual :
      ((nonemptyMomentResidualCollapseBlocks
          κp κm π).map residualBlockOrder).sum =
        ((momentResidualCollapseBlocks
          κp κm π).map residualBlockOrder).sum := by
    simpa only [nonemptyMomentResidualCollapseBlocks] using
      sum_residualBlockOrder_filter_nonempty
        (momentResidualCollapseBlocks κp κm π)
  have hleft :=
    r324LeftWithinHalfInitial_remainingOrder_eq
      ρ lam ε κp
  have hright :=
    r324RightWithinHalfInitial_remainingOrder_eq
      ρ lam ε κm
  have hcross :=
    r324NestedCrossInitial_remainingOrder_eq
      κp κm π
  omega

namespace R324InitialNestedContextFactorization

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {selected : R324ResidualCovarianceSlot κp}
    {terminal :
      R324TwoHalfTerminalData ρ lam ε κp κm}
    {L : ℝ} {x y z w : T4}

/-- Replacing the initial cross order by the actual proper-prefix and
terminal orders gives a genuine four-part partition of ambient order. -/
theorem left_add_right_add_prefix_add_terminal_eq_ambient
    (factorization :
      R324InitialNestedContextFactorization
        ρ lam ε κp κm π selected terminal L x y z w) :
    (R324WithinHalfResidualPrefix.initial
        ρ lam ε κp).remainingOrder +
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κm).remainingOrder +
        factorization.prefixOrder +
        factorization.terminalOrder =
      m := by
  have hschedules :=
    r324InitialSchedules_remainingOrders_eq_ambient
      ρ lam ε κp κm π
  have hcross :=
    factorization.prefixOrder_add_terminalOrder
  omega

/-- The exact four-part multiplicative ledger, valid in every monoid. -/
theorem pow_ambient_eq_four_part
    (factorization :
      R324InitialNestedContextFactorization
        ρ lam ε κp κm π selected terminal L x y z w)
    {A : Type*} [Monoid A] (a : A) :
    a ^ (2 * m) =
      a ^ (2 *
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κp).remainingOrder) *
        (a ^ (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).remainingOrder) *
          (a ^ (2 * factorization.prefixOrder) *
            a ^ (2 * factorization.terminalOrder))) := by
  have horder :=
    left_add_right_add_prefix_add_terminal_eq_ambient
      factorization
  have hexponent :
      2 * m =
        2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κp).remainingOrder +
          (2 *
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).remainingOrder +
            (2 * factorization.prefixOrder +
              2 * factorization.terminalOrder)) := by
    omega
  rw [hexponent, pow_add, pow_add, pow_add]

/-- Real coupling-power specialization of the exact four-part ledger. -/
theorem lamEps_pow_ambient_eq_four_part
    (factorization :
      R324InitialNestedContextFactorization
        ρ lam ε κp κm π selected terminal L x y z w) :
    lamEps lam ε ^ (2 * m) =
      lamEps lam ε ^ (2 *
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κp).remainingOrder) *
        (lamEps lam ε ^ (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).remainingOrder) *
          (lamEps lam ε ^
              (2 * factorization.prefixOrder) *
            lamEps lam ε ^
              (2 * factorization.terminalOrder))) :=
  factorization.pow_ambient_eq_four_part (lamEps lam ε)

/-- Complex coupling-power specialization used before taking the physical
norm. -/
theorem complex_lamEps_pow_ambient_eq_four_part
    (factorization :
      R324InitialNestedContextFactorization
        ρ lam ε κp κm π selected terminal L x y z w) :
    (lamEps lam ε : ℂ) ^ (2 * m) =
      (lamEps lam ε : ℂ) ^ (2 *
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κp).remainingOrder) *
        ((lamEps lam ε : ℂ) ^ (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).remainingOrder) *
          ((lamEps lam ε : ℂ) ^
              (2 * factorization.prefixOrder) *
            (lamEps lam ε : ℂ) ^
              (2 * factorization.terminalOrder))) :=
  factorization.pow_ambient_eq_four_part
    (lamEps lam ε : ℂ)

/-- Absolute-value specialization matching the corrected integrated
reduction boundary. -/
theorem abs_lamEps_pow_ambient_eq_four_part
    (factorization :
      R324InitialNestedContextFactorization
        ρ lam ε κp κm π selected terminal L x y z w) :
    |lamEps lam ε| ^ (2 * m) =
      |lamEps lam ε| ^ (2 *
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κp).remainingOrder) *
        (|lamEps lam ε| ^ (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).remainingOrder) *
          (|lamEps lam ε| ^
              (2 * factorization.prefixOrder) *
            |lamEps lam ε| ^
              (2 * factorization.terminalOrder))) :=
  factorization.pow_ambient_eq_four_part |lamEps lam ε|

end R324InitialNestedContextFactorization

/-! ## Structural data retained at the terminal payload -/

/-- The four endpoint cases recoverable from the indexed left/right
partial pairings at every terminal nested-cross payload. -/
def r324RecoveredEndpointFlags
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    R324EndpointFlags :=
  ![
    false,
    r324OutgoingIsShortcut κp,
    false,
    r324OutgoingIsShortcut κm
  ]

@[simp]
theorem r324RecoveredEndpointFlags_zero
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    r324RecoveredEndpointFlags κp κm 0 = false :=
  rfl

@[simp]
theorem r324RecoveredEndpointFlags_one
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    r324RecoveredEndpointFlags κp κm 1 =
      r324OutgoingIsShortcut κp :=
  rfl

@[simp]
theorem r324RecoveredEndpointFlags_two
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    r324RecoveredEndpointFlags κp κm 2 = false :=
  rfl

@[simp]
theorem r324RecoveredEndpointFlags_three
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    r324RecoveredEndpointFlags κp κm 3 =
      r324OutgoingIsShortcut κm :=
  rfl

/-- The recovered cases are definitionally the cases attached to the
corresponding complete contraction. -/
@[simp]
theorem r324RecoveredEndpointFlags_eq_contraction
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    r324RecoveredEndpointFlags κp κm =
      r324ContractionEndpointFlags
        (⟨κp, ⟨κm, π⟩⟩ : MomentContraction m) :=
  rfl

namespace R324NestedCrossTerminalPayload

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {lam ε : ℝ}
    {step : R324NestedCrossStepContext κp κm π}

/-- The payload's indexed pairing data recover all four endpoint cases;
the payload need not duplicate them as mutable fields. -/
def recoveredEndpointFlags
    (_payload :
      R324NestedCrossTerminalPayload lam ε step) :
    R324EndpointFlags :=
  r324RecoveredEndpointFlags κp κm

@[simp]
theorem recoveredEndpointFlags_eq_contraction
    (payload :
      R324NestedCrossTerminalPayload lam ε step) :
    payload.recoveredEndpointFlags =
      r324ContractionEndpointFlags
        (⟨κp, ⟨κm, π⟩⟩ : MomentContraction m) :=
  r324RecoveredEndpointFlags_eq_contraction κp κm π

end R324NestedCrossTerminalPayload

/-- Exact structural ledger at the stop of the proper-prefix run.

It records the genuine marked carrier, the literal unprocessed suffix,
both endpoints of the selected covariance, the four endpoint cases
recovered from the payload indices, and the unchanged four-endpoint
context represented by `unscaledDensity`. -/
structure R324TerminalPayloadStructuralLedger
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (selected : R324ResidualCovarianceSlot κp)
    {lam ε : ℝ}
    (step : R324NestedCrossStepContext κp κm π)
    (payload :
      R324NestedCrossTerminalPayload lam ε step) : Prop where
  head_carrier_eq :
    step.head.carrier =
      r324MarkedResidualBlock κp κm π selected
  literal_suffix :
    step.residual.remaining = step.head :: step.tail
  marked_lower_mem :
    r324ResidualMarkedLowerEndpoint selected ∈
      step.head.carrier
  marked_upper_mem :
    r324ResidualMarkedUpperEndpoint π selected ∈
      step.head.carrier
  recovered_flags :
    payload.recoveredEndpointFlags =
      r324ContractionEndpointFlags
        (⟨κp, ⟨κm, π⟩⟩ : MomentContraction m)
  unscaledDensity_eq :
    payload.unscaledDensity =
      payload.context
        payload.x payload.y payload.z payload.w

/-- Every actual stop witness returned by the quantitative proper-prefix
iteration supplies the complete terminal structural ledger. -/
theorem R324NestedCrossTerminalPayload.structuralLedger_of_stop
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (selected : R324ResidualCovarianceSlot κp)
    {lam ε : ℝ}
    {step : R324NestedCrossStepContext κp κm π}
    (payload :
      R324NestedCrossTerminalPayload lam ε step)
    (hstop :
      step.head.carrier =
        r324MarkedResidualBlock κp κm π selected) :
    R324TerminalPayloadStructuralLedger
      selected step payload := by
  refine
    { head_carrier_eq := hstop
      literal_suffix := step.remaining_eq
      marked_lower_mem := ?_
      marked_upper_mem := ?_
      recovered_flags := payload.recoveredEndpointFlags_eq_contraction
      unscaledDensity_eq := rfl }
  · rw [hstop]
    exact
      r324ResidualMarkedLowerEndpoint_mem_markedBlock
        κp κm π selected
  · rw [hstop]
    exact
      r324ResidualMarkedUpperEndpoint_mem_markedBlock
        κp κm π selected

/-! ## Exact corrected-output / physical-integral boundary -/

/-- The scalar refined-fibre term appearing in
`MomentRefinedIntegratedReductionData.refined_bound` is exactly the
corresponding genuine refined physical integral.  This is an equality,
not an estimate or a replacement reduction hypothesis. -/
theorem
    momentRefinedDeterministicTermSum_eq_r324RefinedPhysicalIntegral
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (α β : Z4)
    (s :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hs : s ∈ momentContractionSignatures m)
    (r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hr : r ∈ momentResidualChainSignaturesAt m s) :
    momentRefinedDeterministicTermSum
        ρ ε m α β s r =
      r324RefinedPhysicalIntegral ρ ε m α β
        (⟨⟨s, hs⟩, ⟨r, hr⟩⟩ :
          R324RefinedScheduleIndex m) := by
  simpa only [momentRefinedDeterministicTermSum] using
    (r324RefinedPhysicalIntegral_eq_sum_contractionTerms
      ρ hε hε1 α β
      (⟨⟨s, hs⟩, ⟨r, hr⟩⟩ :
        R324RefinedScheduleIndex m)).symm

end

end Anderson4D
