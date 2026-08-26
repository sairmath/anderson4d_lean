import Anderson4D.DetParametrix.Paper42_Moment.R324TerminalJointIntegrability
import Anderson4D.DetParametrix.Paper42_Moment.R324SignedFinalClosure

/-!
# Final assembly of the R-324 deterministic moment bound

This file assembles the R-324 deterministic estimate:

* the driver mode-decay bounds of `R324DriverClosure` are restated with
  the joint-integrability premise *discharged* for the canonical
  transport `afterHeadAlternatingTransport`, using
  `R324TerminalJointIntegrability`);
* the uniform-branch middle estimate is isolated as the named Prop
  `R324RefinedInsertedMajorantBound` and wired into
  `MomentRefinedIntegratedReductionOutputAt`;
* the deterministic-moment paper bound (the P-3.5b-det shape) is
  produced from these inputs through the signed routed collapse.

The routed branch is consumed in countable-series form. Its production is
packaged by `SignedRoutedPrimitiveSlotCollapseData`, which derives
`CountableCentralRoutedMomentReductionOutput` at the endpoint-weighted
budget.

## The complementary incoming branch

The remaining middle estimate `R324RefinedInsertedMajorantBound` is a
per-schedule-index bound, and the incoming-endpoint case split
`(⟨0, hm⟩ ∈ finalActive e₀.1)` versus `(∉)` lives *inside* it, per
contraction entity: the driver assemblies
(`R324IncomingExceptionalStopTraceAssembly.exists_of_localBlockProvider`)
exist exactly on the `∉` branch, while on the `∈` branch the incoming
endpoint's vertex survives the whole schedule and the state keeps the
direct Green factor at slot zero
(`state_edges_zero_eq_greenFn_of_first_mem_finalActive`), selecting the
`.directFourier` case of `r324IncomingEndpointReductionCase` — the
branch with one more raw Green leg and fewer collapsed heads.  On the
outgoing side the analogous split is the boolean
`r324OutgoingIsShortcut`; the non-shortcut branch is closed below with
gap (a) discharged.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

namespace R324IncomingExceptionalStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {initialScale : Fin (m + 1) → ℝ}

/-- **Gap (a) consumed: the outgoing mode-decay upgrade holds
unconditionally for the canonical driver transport.**  Both the joint
integrability premise and the nonempty-active premise of
`norm_lamEps_pow_mul_r324RefinedPhysicalIntegral_le_modeDecay_of_not_shortcut`
are discharged: the first by the terminal certificate extracted from the
driver recursion, the second because the non-shortcut outgoing frozen
pairing keeps the last internal vertex active. -/
theorem norm_lamEps_pow_mul_r324RefinedPhysicalIntegral_le_modeDecay_of_provider
    (p : R324RefinedScheduleIndex m)
    (e₀ : MomentContraction m)
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) e₀.1 initialScale)
    (hm : 0 < m)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K e₀.1)
    (hG :
      ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder data.terminal.2)
              κB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (α β : Z4)
    (hdirect : r324OutgoingIsShortcut e₀.1 = false) :
    ‖(lamEps lam ε : ℂ) ^
          (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).remainingOrder) *
        r324RefinedPhysicalIntegral
          ρ ε m α β p‖ ≤
      paperSecondOrderModeDecay β *
        (∫ z : T4, |greenFn z| ∂paperMeasure)⁻¹ *
        ∫ q :
            R324IncomingExceptionalRootParameter
                ρ lam ε e₀.2.1 ×
              ((data.afterHeadAlternatingTransport
                hε hε1 provider).final.SurvivingCoordinate → T4),
          ‖(data.afterHeadAlternatingTransport
              hε hε1 provider).final.incomingPhasedResidualDensity
            ((data.afterHeadAlternatingTransport
              hε hε1 provider).multiplier α *
              data.incomingExceptionalRefinedRootDriverCoefficient
                (data.afterHeadAlternatingTransport
                  hε hε1 provider)
                α β e₀.2.2 q.1 q.2)
            α ρ ε 0 q.1.1.1 q.2‖
          ∂((r324IncomingExceptionalRootParameterMeasure
              ρ lam ε e₀.2.1).prod
            (Measure.pi fun _ => paperMeasure)) := by
  have hnotmem :
      Fin.last m ∉ extractedRightEdges e₀.1 := by
    simpa [r324OutgoingIsShortcut] using hdirect
  have hactive :
      (data.afterHeadAlternatingTransport
        hε hε1 provider).final.state.active.Nonempty := by
    refine ⟨⟨m - 1, by omega⟩, ?_⟩
    rw [(data.afterHeadAlternatingTransport
        hε hε1 provider).final.active_eq_finalActive_of_processed_eq_schedule
      (data.afterHeadAlternatingTransport
        hε hε1 provider).final_processed_eq_schedule]
    exact
      lastInternal_mem_finalActive_of_finLast_not_mem_extractedRightEdges
        e₀.1 hm hnotmem
  exact
    data.norm_lamEps_pow_mul_r324RefinedPhysicalIntegral_le_modeDecay_of_not_shortcut
      p e₀ he₀
      (data.afterHeadAlternatingTransport hε hε1 provider)
      hm hε hε1 hG hint α β
      (data.driverTerminalJointIntegrable_afterHeadAlternatingTransport
        hε hε1 provider α β e₀.2.2)
      hactive hdirect

/-- **Gaps (a)+(b) combined, unconditional form:** the full-ambient-weight
mode-decay bound for the canonical driver transport, with the joint
integrability and active-carrier premises discharged. -/
theorem norm_lamEps_pow_ambient_mul_r324RefinedPhysicalIntegral_le_modeDecay_of_provider
    (p : R324RefinedScheduleIndex m)
    (e₀ : MomentContraction m)
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) e₀.1 initialScale)
    (hm : 0 < m)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K e₀.1)
    (hG :
      ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder data.terminal.2)
              κB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (α β : Z4)
    (hdirect : r324OutgoingIsShortcut e₀.1 = false) :
    |lamEps lam ε| ^ (2 * m) *
        ‖r324RefinedPhysicalIntegral ρ ε m α β p‖ ≤
      paperSecondOrderModeDecay β *
        (∫ z : T4, |greenFn z| ∂paperMeasure)⁻¹ *
        ∫ q :
            R324IncomingExceptionalRootParameter
                ρ lam ε e₀.2.1 ×
              ((data.afterHeadAlternatingTransport
                hε hε1 provider).final.SurvivingCoordinate → T4),
          |lamEps lam ε| ^
              (2 *
                  (R324WithinHalfResidualPrefix.initial
                    ρ lam ε e₀.2.1).remainingOrder +
                2 *
                  (R324NestedCrossResidualPrefix.initial
                    e₀.1 e₀.2.1 e₀.2.2).remainingOrder) *
            ‖(data.afterHeadAlternatingTransport
                hε hε1 provider).final.incomingPhasedResidualDensity
              ((data.afterHeadAlternatingTransport
                hε hε1 provider).multiplier α *
                data.incomingExceptionalRefinedRootDriverCoefficient
                  (data.afterHeadAlternatingTransport
                    hε hε1 provider)
                  α β e₀.2.2 q.1 q.2)
              α ρ ε 0 q.1.1.1 q.2‖
          ∂((r324IncomingExceptionalRootParameterMeasure
              ρ lam ε e₀.2.1).prod
            (Measure.pi fun _ => paperMeasure)) := by
  have hnotmem :
      Fin.last m ∉ extractedRightEdges e₀.1 := by
    simpa [r324OutgoingIsShortcut] using hdirect
  have hactive :
      (data.afterHeadAlternatingTransport
        hε hε1 provider).final.state.active.Nonempty := by
    refine ⟨⟨m - 1, by omega⟩, ?_⟩
    rw [(data.afterHeadAlternatingTransport
        hε hε1 provider).final.active_eq_finalActive_of_processed_eq_schedule
      (data.afterHeadAlternatingTransport
        hε hε1 provider).final_processed_eq_schedule]
    exact
      lastInternal_mem_finalActive_of_finLast_not_mem_extractedRightEdges
        e₀.1 hm hnotmem
  exact
    data.norm_lamEps_pow_ambient_mul_r324RefinedPhysicalIntegral_le_modeDecay
      p e₀ he₀
      (data.afterHeadAlternatingTransport hε hε1 provider)
      hm hε hε1 hG hint α β
      (data.driverTerminalJointIntegrable_afterHeadAlternatingTransport
        hε hε1 provider α β e₀.2.2)
      hactive
      ((data.afterHeadAlternatingTransport
        hε hε1 provider).final.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_not_shortcut
        hm
        (data.afterHeadAlternatingTransport
          hε hε1 provider).final_processed_eq_schedule
        hdirect hactive)

end R324IncomingExceptionalStopTraceAssembly

end R324WithinHalfResidualPrefix

/-! ## The remaining middle estimate, as a named interface -/

/-- **Gap (b), the middle estimate (open).**  The `2m`-weighted refined
physical integral is bounded, uniformly over the refined schedule
index, by the integrated inserted majorant.  On the driver branch this
is the estimate connecting the mode-decay output of
`norm_lamEps_pow_ambient_mul_r324RefinedPhysicalIntegral_le_modeDecay_of_provider`
(with gap (a) discharged) to `∫ primitiveInsertedMajorant`; it contains
the per-contraction case splits `⟨0, hm⟩ ∈/∉ finalActive` (incoming)
and `r324OutgoingIsShortcut` (outgoing). -/
def R324RefinedInsertedMajorantBound
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4)
    (primitiveConstant supportConstant : ℝ) : Prop :=
  ∀ p : R324RefinedScheduleIndex m,
    |lamEps lam ε| ^ (2 * m) *
        ‖r324RefinedPhysicalIntegral ρ ε m α β p‖ ≤
      ∫ z,
        primitiveInsertedMajorant
          primitiveConstant lam ε supportConstant m z
        ∂paperMeasure

/-- The middle estimate discharges the integrated residual-refined
reduction interface `MomentRefinedIntegratedReductionOutputAt`. -/
theorem momentRefinedIntegratedReductionOutputAt_of_insertedMajorantBound
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {α β : Z4}
    {primitiveConstant supportConstant : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h :
      R324RefinedInsertedMajorantBound
        ρ lam ε m α β primitiveConstant supportConstant) :
    MomentRefinedIntegratedReductionOutputAt
      ρ lam ε m α β primitiveConstant supportConstant :=
  ⟨momentRefinedIntegratedReductionData_of_refinedPhysicalIntegral_bound
    hε hε1 h⟩

/-! ## The deterministic moment paper bound (P-3.5b-det shape) -/

/-- **The R-324 final assembly (P-3.5b-det shape).** Given the middle
estimate `R324RefinedInsertedMajorantBound` and the signed routed primitive slot
collapse data (the routing input, consumed through the countable
central interface), the deterministic moment pairing sum obeys the
paper bound of (3.24), including the
`⟨α⟩⁻⁴⟨β⟩⁻⁴⟨ε²(α+β)⟩⁻⁸` decay bracket carried by
`paperDeterministicMomentRHS`.

The realized P-3.5b-det shape is this bound on `deterministicMomentPairingSum`
against `paperDeterministicMomentRHS outerConstant
(16 * primitiveConstant)`, as in
`R324FinalDeterministicClosure` and `R324SignedFinalClosure`. -/
theorem exists_deterministicMoment_paper_bound_of_insertedMajorant_and_signedCollapse
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
        (hm : 0 < m) (α β : Z4),
        0 ≤ lam →
        0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        m ≤ truncOrder ε →
        R324RefinedInsertedMajorantBound
          ρ lam ε m α β primitiveConstant supportConstant →
        ρ.SignedRoutedPrimitiveSlotCollapseData
          lam ε m hm primitiveConstant supportConstant →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (16 * primitiveConstant) lam ε m α β := by
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_refinedIntegrated_and_signedCollapse
      hprimitive hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m hm α β hlam hε hε1 hlog hmtrunc
    hmajorant hsigned
  exact
    h ρ lam ε m hm α β hlam hε hε1 hlog hmtrunc
      (momentRefinedIntegratedReductionOutputAt_of_insertedMajorantBound
        hε (hε1.trans (by norm_num)) hmajorant)
      hsigned

/-- Variant of the final assembly consuming the countable central routed
interface directly, for callers that produce
`CountableCentralRoutedMomentReductionOutput` by other means (the
`_of_zeroShift` / `_of_nonzeroRoutes` branch producers of
`R324NonzeroRoutedDensity`). -/
theorem exists_deterministicMoment_paper_bound_of_insertedMajorant_and_countable
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4),
        0 ≤ lam →
        0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| → 1 ≤ m →
        R324RefinedInsertedMajorantBound
          ρ lam ε m α β primitiveConstant supportConstant →
        CountableCentralRoutedMomentReductionOutput
          ρ lam ε m α β
          ((lamEps lam ε ^ 2 * outerConstant *
              ((16 * primitiveConstant) * lam) ^ (2 * m - 2)) *
            r324EndpointLoss ε α β) →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (16 * primitiveConstant) lam ε m α β := by
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_refinedIntegrated_and_countable
      hprimitive hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m α β hlam hε hε1 hlog hm
    hmajorant hcountable
  exact
    h ρ lam ε m α β hlam hε hε1 hlog hm
      (momentRefinedIntegratedReductionOutputAt_of_insertedMajorantBound
        hε (hε1.trans (by norm_num)) hmajorant)
      hcountable

end

end Anderson4D
