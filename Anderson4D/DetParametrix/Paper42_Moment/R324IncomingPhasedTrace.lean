import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingPhasedOrdinarySeam
import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalSeam
import Anderson4D.DetParametrix.Paper42_Moment.R324ResidualSumTerminalProjection

/-!
# Phased trace: iterating the ordinary transport along the whole suffix

The one-head ordinary transport and its integrability seam advance the
incoming phased residual density across one non-slot-zero-fed head.  This
file iterates that step along a complete certified analytic trace, from an
arbitrary residual prefix down to the terminal prefix with empty remaining
list, and composes the result with the exceptional-head base case at the
genuine refined physical root.

The certified analytic trace already stores the per-head internal Fubini
evidence and edge certificates.  The single genuinely new hypothesis is
`OrdinaryAlong`: every head traversed by the trace must have a nonzero
sparse predecessor slot, so that the slot-zero-erased phase representation
is preserved.  This is not derivable from the stop certificate: a schedule
may contain a later block all of whose earlier vertices have already been
consumed, and such a block is fed by slot zero.  The hypothesis is
therefore taken pointwise along the trace and must be discharged by the
caller from the combinatorics of the concrete schedule.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

namespace R324WithinHalfCertifiedAnalyticTrace

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- Every head traversed by a certified analytic trace has a nonzero
sparse predecessor slot.  This is exactly the hypothesis under which the
ordinary phased one-head transport applies at every step. -/
def OrdinaryAlong
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale) : Prop :=
  match trace with
  | .terminal .. => True
  | @R324WithinHalfCertifiedAnalyticTrace.step
      _ _ _ _ _
      current head _tail _hremaining _ _ _ _ next =>
      r324WithinHalfPredecessorSlot current.state head ≠ 0 ∧
        next.OrdinaryAlong

/-- Ordinariness along a certified analytic trace follows from the purely
combinatorial statement that every prefix whose remaining list is a suffix
of the starting remaining list has a nonzero sparse predecessor slot at
its head.  The predecessor slot depends only on the processed schedule
prefix, so this hypothesis is a property of the schedule decomposition
alone, independent of the trace. -/
theorem ordinaryAlong_of_predecessorSlot_ne_zero
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale)
    (hpreds :
      ∀ (res' :
          R324WithinHalfResidualPrefix ρ lam ε pairing)
        (head : R322ExtractionStep m)
        (tail : List (R322ExtractionStep m)),
        res'.remaining = head :: tail →
        res'.remaining.IsSuffix res.remaining →
        r324WithinHalfPredecessorSlot res'.state head ≠ 0) :
    trace.OrdinaryAlong := by
  induction trace with
  | terminal terminal scale hremaining certificate =>
      trivial
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      refine
        ⟨hpreds current head tail hremaining
          (by rw [hremaining]), ?_⟩
      apply ih
      intro res' head' tail' hrem' hsuffix
      apply hpreds res' head' tail' hrem'
      have hstep :
          (current.afterHead
            head tail hremaining).remaining.IsSuffix
            current.remaining := by
        rw [current.afterHead_remaining
          head tail hremaining, hremaining]
        exact List.suffix_cons head tail
      exact hsuffix.trans hstep

/-- **Terminal integrability along an ordinary phased trace.**  Full
integrability of the phased density at the root of the trace transports to
the terminal prefix, with the coefficient read through the terminal
projection at every intermediate step. -/
theorem integrable_trace_end_incomingPhasedResidualDensity
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (x y : T4)
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale)
    (hordinary : trace.OrdinaryAlong)
    (coefficient :
      (trace.terminalPrefix.SurvivingCoordinate → T4) → ℂ)
    (k : Z4)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          res.incomingPhasedResidualDensity
            (coefficient (trace.terminalProjection w))
            k ρ ε x y w)
        (Measure.pi fun _ => paperMeasure)) :
    Integrable
      (fun v :
          trace.terminalPrefix.SurvivingCoordinate → T4 =>
        trace.terminalPrefix.incomingPhasedResidualDensity
          (coefficient v) k ρ ε x y v)
      (Measure.pi fun _ => paperMeasure) := by
  induction trace with
  | terminal terminal scale hremaining certificate =>
      exact hfull
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      obtain ⟨hpred, hnext⟩ := hordinary
      have hcurrent :
          Integrable
            (fun w : current.SurvivingCoordinate → T4 =>
              current.incomingPhasedResidualDensity
                ((fun v => coefficient (next.terminalProjection v))
                  ((current.splitSurvivingPiMeasurableEquiv
                    head tail hremaining w).2))
                k ρ ε x y w)
            (Measure.pi fun _ => paperMeasure) := hfull
      have hpost :=
        current.integrable_afterHead_incomingPhasedResidualDensity_of_ne_zero
          head tail hremaining hpred x y
          (fun v => coefficient (next.terminalProjection v))
          k hcurrent internal.internal
      exact ih hnext coefficient hpost

/-- **Phased trace recursion.**  Along a certified analytic trace all of
whose heads are ordinary, the weighted incoming phased residual integral
transports exactly to the terminal prefix: the perturbative power drops to
twice the terminal remaining order and the density becomes the terminal
phased density with the same coefficient, phase, and endpoints. -/
theorem lamEps_pow_integral_incomingPhasedResidualDensity_eq_trace_end
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (x y : T4)
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale)
    (hordinary : trace.OrdinaryAlong)
    (coefficient :
      (trace.terminalPrefix.SurvivingCoordinate → T4) → ℂ)
    (k : Z4)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          res.incomingPhasedResidualDensity
            (coefficient (trace.terminalProjection w))
            k ρ ε x y w)
        (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
        (∫ w : res.SurvivingCoordinate → T4,
          res.incomingPhasedResidualDensity
            (coefficient (trace.terminalProjection w))
            k ρ ε x y w
          ∂Measure.pi fun _ => paperMeasure) =
      (lamEps lam ε : ℂ) ^
          (2 * trace.terminalPrefix.remainingOrder) *
        (∫ v :
            trace.terminalPrefix.SurvivingCoordinate → T4,
          trace.terminalPrefix.incomingPhasedResidualDensity
            (coefficient v) k ρ ε x y v
          ∂Measure.pi fun _ => paperMeasure) := by
  induction trace with
  | terminal terminal scale hremaining certificate =>
      rfl
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      obtain ⟨hpred, hnext⟩ := hordinary
      have hcurrent :
          Integrable
            (fun w : current.SurvivingCoordinate → T4 =>
              current.incomingPhasedResidualDensity
                ((fun v => coefficient (next.terminalProjection v))
                  ((current.splitSurvivingPiMeasurableEquiv
                    head tail hremaining w).2))
                k ρ ε x y w)
            (Measure.pi fun _ => paperMeasure) := hfull
      have hpost :=
        current.integrable_afterHead_incomingPhasedResidualDensity_of_ne_zero
          head tail hremaining hpred x y
          (fun v => coefficient (next.terminalProjection v))
          k hcurrent internal.internal
      change
        (lamEps lam ε : ℂ) ^ (2 * current.remainingOrder) *
            (∫ w : current.SurvivingCoordinate → T4,
              current.incomingPhasedResidualDensity
                ((fun v => coefficient (next.terminalProjection v))
                  ((current.splitSurvivingPiMeasurableEquiv
                    head tail hremaining w).2))
                k ρ ε x y w
              ∂Measure.pi fun _ => paperMeasure) =
          (lamEps lam ε : ℂ) ^
              (2 * next.terminalPrefix.remainingOrder) *
            (∫ v :
                next.terminalPrefix.SurvivingCoordinate → T4,
              next.terminalPrefix.incomingPhasedResidualDensity
                (coefficient v) k ρ ε x y v
              ∂Measure.pi fun _ => paperMeasure)
      rw [
        current.lamEps_pow_integral_incomingPhasedResidualDensity_eq_afterHead_of_ne_zero
          head tail hremaining hpred x y
          (fun v => coefficient (next.terminalProjection v))
          k hcurrent internal.internal]
      exact ih hnext coefficient hpost

end R324WithinHalfCertifiedAnalyticTrace

namespace R324IncomingExceptionalStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-! ## The certified analytic trace of the after-head suffix -/

/-- The certified analytic trace of the complete after-head suffix, built
from the local block provider and the certificate transported to the
exceptional stop.  Only the ordinariness of the suffix heads is not
provided by this construction. -/
def afterHeadCertifiedAnalyticTrace
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K κp) :
    R324WithinHalfCertifiedAnalyticTrace
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq)
      (r324WithinHalfUpdatedEdgeScale
        data.stopContext data.stopScale C lam K) :=
  R324WithinHalfCertifiedAnalyticTrace.of_localBlockProvider
    hε hε1 provider
    (data.trace.stopPrefix.afterHead
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq)
    (r324WithinHalfUpdatedEdgeScale
      data.stopContext data.stopScale C lam K)
    (provider data.trace.stopPrefix
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
      data.stopScale data.stopCertificate).2

/-! ## The genuine root coefficient at the terminal carrier -/

/-- The untouched refined-root outer functional read on the terminal
carrier of a certified after-head trace: the retained endpoint characters,
the untouched right initial residual, and the cross-cut primitive factor
reconstructed from the terminal prefix. -/
def incomingExceptionalRefinedRootTerminalPostOuter
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq)
        scale)
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω :
      R324IncomingExceptionalRootParameter
        ρ lam ε κm)
    (u :
      trace.terminalPrefix.SurvivingCoordinate → T4) : ℂ :=
  charT4 β ω.1.1 *
    charT4 (-α) ω.1.2.1 *
    charT4 (-β) ω.1.2.2 *
    (((R324WithinHalfResidualPrefix.initial
        ρ lam ε κm).residualIntegrand
      ρ ε ω.1.2.1 ω.1.2.2
      ((R324WithinHalfResidualPrefix.initial
        ρ lam ε κm).reconstruct ω.2) : ℂ) *
      (r324ResidualPrimitiveSumProduct
        ρ ε κp κm π
        (r324TwoHalfRootDoubledReconstruct
          trace.terminalPrefix
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κm)
          (u, ω.2)) : ℂ))

/-- **Terminal factorization of the refined-root outer functional.**  The
cross-cut primitive factor reads only coordinates on the doubled residual
carrier, all of which survive to the terminal prefix; hence the whole
refined-root outer functional factors through the terminal projection of
any certified after-head trace. -/
theorem incomingExceptionalRefinedRootPostOuter_eq_terminalProjection
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq)
        scale)
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω :
      R324IncomingExceptionalRootParameter
        ρ lam ε κm)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
          T4) :
    data.incomingExceptionalRefinedRootPostOuter
        α β π ω v =
      data.incomingExceptionalRefinedRootTerminalPostOuter
        trace α β π ω (trace.terminalProjection v) := by
  have hsum :
      r324ResidualPrimitiveSumProduct
          ρ ε κp κm π
          (r324TwoHalfRootDoubledReconstruct
            (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq)
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm)
            (v, ω.2)) =
        r324ResidualPrimitiveSumProduct
          ρ ε κp κm π
          (r324TwoHalfRootDoubledReconstruct
            trace.terminalPrefix
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm)
            (trace.terminalProjection v, ω.2)) := by
    apply r324ResidualPrimitiveSumProduct_congr_on_active
    intro j hj
    by_cases hleft : j.val < m
    · obtain ⟨i, hi, hji⟩ :=
        exists_leftMomentIndex_of_mem_momentResidualActive
          hj hleft
      subst j
      let i' :
          trace.terminalPrefix.SurvivingCoordinate :=
        ⟨i, by
          rw [
            trace.terminalPrefix.active_eq_finalActive_of_processed_eq_schedule
              trace.terminalPrefix_processed_eq_schedule]
          exact hi⟩
      unfold r324TwoHalfRootDoubledReconstruct
      rw [momentDoubleFinEquiv_symm_leftMomentIndex]
      exact trace.reconstruct_terminalProjection v i'
    · obtain ⟨i, hi, hji⟩ :=
        exists_rightMomentIndex_of_mem_momentResidualActive
          hj (by omega)
      subst j
      unfold r324TwoHalfRootDoubledReconstruct
      rw [momentDoubleFinEquiv_symm_rightMomentIndex]
  unfold incomingExceptionalRefinedRootPostOuter
    incomingExceptionalRefinedRootTerminalPostOuter
  rw [hsum]

/-- The collapsed-head coefficient of the genuine refined root, read on
the terminal carrier: squared second-order decay, primitive Step-4 defect
of the exceptional head, and the terminal form of the untouched refined
outer functional. -/
def incomingExceptionalRefinedRootTerminalCoefficient
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq)
        scale)
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω :
      R324IncomingExceptionalRootParameter
        ρ lam ε κm)
    (u :
      trace.terminalPrefix.SurvivingCoordinate → T4) : ℂ :=
  (paperSecondOrderModeDecay α : ℂ) ^ 2 *
    incomingExceptionalPrimitiveDefect ρ lam ε
      (residualBlockOrder data.terminal.2)
      data.stopContext.one_le_blockOrder
      data.stopContext.internalEdges α *
    data.incomingExceptionalRefinedRootTerminalPostOuter
      trace α β π ω u

/-- The collapsed-head refined-root coefficient factors through the
terminal projection of any certified after-head trace. -/
theorem incomingExceptionalPostCoefficient_refinedRoot_eq_terminalProjection
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq)
        scale)
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω :
      R324IncomingExceptionalRootParameter
        ρ lam ε κm)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
          T4) :
    data.incomingExceptionalPostCoefficient
        α
        (data.incomingExceptionalRefinedRootPostOuter
          α β π)
        ω v =
      data.incomingExceptionalRefinedRootTerminalCoefficient
        trace α β π ω (trace.terminalProjection v) := by
  unfold incomingExceptionalPostCoefficient
    incomingExceptionalRefinedRootTerminalCoefficient
  rw [
    data.incomingExceptionalRefinedRootPostOuter_eq_terminalProjection
      trace α β π ω v]

/-- At a fixed root parameter, the after-head phased integrand of the
genuine refined root is the after-head phased density whose coefficient is
the terminal refined coefficient read through the terminal projection. -/
theorem incomingExceptionalAfterHeadPhasedIntegrand_refinedRoot_section_eq
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq)
        scale)
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω :
      R324IncomingExceptionalRootParameter
        ρ lam ε κm) :
    (fun v :
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4 =>
      data.incomingExceptionalAfterHeadPhasedIntegrand
        α
        (fun ω' :
            R324IncomingExceptionalRootParameter
              ρ lam ε κm =>
          ω'.1.1)
        (data.incomingExceptionalRefinedRootPostOuter
          α β π)
        (ω, v)) =
      fun v =>
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).incomingPhasedResidualDensity
          (data.incomingExceptionalRefinedRootTerminalCoefficient
            trace α β π ω
            (trace.terminalProjection v))
          α ρ ε 0 ω.1.1 v := by
  funext v
  show
    (data.trace.stopPrefix.afterHead
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq).incomingPhasedResidualDensity
        (data.incomingExceptionalPostCoefficient
          α
          (data.incomingExceptionalRefinedRootPostOuter
            α β π)
          ω v)
        α ρ ε 0 ω.1.1 v =
      _
  rw [
    data.incomingExceptionalPostCoefficient_refinedRoot_eq_terminalProjection
      trace α β π ω v]

/-- **Full phased trace of the genuine refined root.**  The weighted
single-fibre refined physical integral, with the exceptional head absorbed
by the base case and every later suffix head absorbed by the ordinary
phased iteration: the right-hand side integrates the terminal phased
density over the root parameter and the terminal coordinates, with the
collapsed-head refined coefficient read on the terminal carrier. -/
theorem lamEps_pow_r324RefinedPhysicalIntegral_eq_incomingExceptionalTraceEnd
    (p : R324RefinedScheduleIndex m)
    (e₀ : MomentContraction m)
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) e₀.1 initialScale)
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq)
        scale)
    (hordinary : trace.OrdinaryAlong)
    (hm : 0 < m)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
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
    (α β : Z4) :
    (lamEps lam ε : ℂ) ^
          (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).remainingOrder) *
        r324RefinedPhysicalIntegral
          ρ ε m α β p =
      (lamEps lam ε : ℂ) ^
          (2 * trace.terminalPrefix.remainingOrder) *
        (∫ ω :
            R324IncomingExceptionalRootParameter
              ρ lam ε e₀.2.1,
          (∫ u :
              trace.terminalPrefix.SurvivingCoordinate → T4,
            trace.terminalPrefix.incomingPhasedResidualDensity
              (data.incomingExceptionalRefinedRootTerminalCoefficient
                trace α β e₀.2.2 ω u)
              α ρ ε 0 ω.1.1 u
            ∂Measure.pi fun _ => paperMeasure)
          ∂r324IncomingExceptionalRootParameterMeasure
            ρ lam ε e₀.2.1) := by
  have hjoint :=
    data.integrable_incomingExceptionalRefinedRootAfterHeadPhasedIntegrand
      p e₀ he₀ hm hε hε1 hG hint α β
  refine
    (data.lamEps_pow_r324RefinedPhysicalIntegral_eq_incomingExceptionalAfterHead
      p e₀ he₀ hm hε hε1 hG hint α β).trans ?_
  rw [integral_prod _ hjoint, ← integral_const_mul,
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hjoint.prod_right_ae] with ω hω
  rw [data.incomingExceptionalAfterHeadPhasedIntegrand_refinedRoot_section_eq
    trace α β e₀.2.2 ω] at hω ⊢
  exact
    trace.lamEps_pow_integral_incomingPhasedResidualDensity_eq_trace_end
      0 ω.1.1 hordinary
      (fun u =>
        data.incomingExceptionalRefinedRootTerminalCoefficient
          trace α β e₀.2.2 ω u)
      α hω

/-- **Terminal integrability at the genuine refined root.**  For almost
every root parameter, the terminal phased density with the refined
terminal coefficient is integrable over the terminal coordinates.  This is
the endpoint form of the trace integrability seam, ready for the final
incoming Fourier evaluation and the branch summation. -/
theorem eventually_integrable_incomingExceptionalRefinedRootTraceEnd
    (p : R324RefinedScheduleIndex m)
    (e₀ : MomentContraction m)
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) e₀.1 initialScale)
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq)
        scale)
    (hordinary : trace.OrdinaryAlong)
    (hm : 0 < m)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
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
    (α β : Z4) :
    ∀ᵐ ω ∂(r324IncomingExceptionalRootParameterMeasure
        ρ lam ε e₀.2.1),
      Integrable
        (fun u :
            trace.terminalPrefix.SurvivingCoordinate → T4 =>
          trace.terminalPrefix.incomingPhasedResidualDensity
            (data.incomingExceptionalRefinedRootTerminalCoefficient
              trace α β e₀.2.2 ω u)
            α ρ ε 0 ω.1.1 u)
        (Measure.pi fun _ => paperMeasure) := by
  have hjoint :=
    data.integrable_incomingExceptionalRefinedRootAfterHeadPhasedIntegrand
      p e₀ he₀ hm hε hε1 hG hint α β
  filter_upwards [hjoint.prod_right_ae] with ω hω
  rw [data.incomingExceptionalAfterHeadPhasedIntegrand_refinedRoot_section_eq
    trace α β e₀.2.2 ω] at hω
  exact
    trace.integrable_trace_end_incomingPhasedResidualDensity
      0 ω.1.1 hordinary
      (fun u =>
        data.incomingExceptionalRefinedRootTerminalCoefficient
          trace α β e₀.2.2 ω u)
      α hω

end R324IncomingExceptionalStopTraceAssembly

end R324WithinHalfResidualPrefix

end

end Anderson4D
