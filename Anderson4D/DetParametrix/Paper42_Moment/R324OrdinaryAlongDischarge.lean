import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingPhasedTrace
import Anderson4D.DetParametrix.Paper42_Moment.R324StopBeforeStepProjection

/-!
# Discharging `OrdinaryAlong`: the longest ordinary run and the next stop

`OrdinaryAlong` is false for a general remaining suffix: a later block all
of whose earlier vertices have already been consumed is fed by slot zero.
This module provides the decomposition that the alternating trace needs:
every remaining list splits as the longest ordinary run followed either by
nothing or by a slot-zero-fed head.

The sparse predecessor slot depends only on the processed schedule prefix,
never on the named kernels.  The run is therefore a purely combinatorial
`takeWhile`-style recursion on the remaining list with an evolving
processed accumulator.  Its specifications discharge `OrdinaryAlong` both
for complete certified analytic traces (when the run covers the whole
remaining list) and for certified stop-before-step traces that stop at the
run boundary.  The phased one-head transport then iterates exactly up to
the next slot-zero-fed head, at arbitrary Fourier-evaluated endpoints, and
the packaged next-stop data exposes the boundary head with its literal
slot-zero certificate for the exceptional collapse.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## The predecessor slot is a function of the processed prefix -/

/-- The sparse predecessor slot reads only the active carrier, hence only
the processed schedule prefix; the named kernels are irrelevant. -/
theorem r324WithinHalfPredecessorSlot_congr_processed
    {m : ℕ} (s₁ s₂ : R324WithinHalfEdgeState m)
    (h : s₁.processed = s₂.processed)
    (step : R322ExtractionStep m) :
    r324WithinHalfPredecessorSlot s₁ step =
      r324WithinHalfPredecessorSlot s₂ step := by
  have hactive : s₁.active = s₂.active := by
    unfold R324WithinHalfEdgeState.active
    rw [h]
  unfold r324WithinHalfPredecessorSlot
    r324WithinHalfPredecessorCandidates
  simp only [hactive]

/-- The predecessor slot of a head over a bare processed prefix. -/
def r324WithinHalfListPredecessorSlot
    {m : ℕ} (processed : List (R322ExtractionStep m))
    (step : R322ExtractionStep m) : Fin (m + 1) :=
  r324WithinHalfPredecessorSlot
    { processed := processed, edges := fun _ => greenFn } step

/-- Any state computes its predecessor slots through its processed list. -/
theorem r324WithinHalfPredecessorSlot_eq_listPredecessorSlot
    {m : ℕ} (state : R324WithinHalfEdgeState m)
    (step : R322ExtractionStep m) :
    r324WithinHalfPredecessorSlot state step =
      r324WithinHalfListPredecessorSlot state.processed step :=
  r324WithinHalfPredecessorSlot_congr_processed
    state { processed := state.processed, edges := fun _ => greenFn }
    rfl step

/-! ## The longest ordinary run -/

/-- Length of the longest prefix of the remaining list along which every
head, read at its own evolved processed prefix, has a nonzero predecessor
slot.  The recursion consumes one head at a time, appending it to the
processed accumulator exactly as `absorb` does. -/
def r324WithinHalfOrdinaryRunLength {m : ℕ} :
    List (R322ExtractionStep m) →
      List (R322ExtractionStep m) → ℕ
  | _, [] => 0
  | processed, head :: tail =>
      if r324WithinHalfListPredecessorSlot processed head = 0 then 0
      else
        r324WithinHalfOrdinaryRunLength (processed ++ [head]) tail + 1

@[simp]
theorem r324WithinHalfOrdinaryRunLength_nil
    {m : ℕ} (processed : List (R322ExtractionStep m)) :
    r324WithinHalfOrdinaryRunLength processed [] = 0 :=
  rfl

theorem r324WithinHalfOrdinaryRunLength_cons
    {m : ℕ} (processed : List (R322ExtractionStep m))
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m)) :
    r324WithinHalfOrdinaryRunLength processed (head :: tail) =
      if r324WithinHalfListPredecessorSlot processed head = 0 then 0
      else
        r324WithinHalfOrdinaryRunLength
          (processed ++ [head]) tail + 1 :=
  rfl

theorem r324WithinHalfOrdinaryRunLength_le_length
    {m : ℕ} (processed l : List (R322ExtractionStep m)) :
    r324WithinHalfOrdinaryRunLength processed l ≤ l.length := by
  induction l generalizing processed with
  | nil => simp
  | cons head tail ih =>
      rw [r324WithinHalfOrdinaryRunLength_cons]
      split
      · simp
      · have := ih (processed ++ [head])
        simp only [List.length_cons]
        omega

/-- **Ordinariness inside the run.**  Every head whose position lies
strictly inside the ordinary run has a nonzero predecessor slot at its own
evolved processed prefix. -/
theorem r324WithinHalfListPredecessorSlot_ne_zero_of_lt_ordinaryRunLength
    {m : ℕ} (processed a b : List (R322ExtractionStep m))
    (head : R322ExtractionStep m)
    (hlt :
      a.length <
        r324WithinHalfOrdinaryRunLength processed
          (a ++ head :: b)) :
    r324WithinHalfListPredecessorSlot
      (processed ++ a) head ≠ 0 := by
  induction a generalizing processed with
  | nil =>
      rw [List.nil_append,
        r324WithinHalfOrdinaryRunLength_cons] at hlt
      rw [List.append_nil]
      intro h0
      rw [if_pos h0] at hlt
      exact absurd hlt (by omega)
  | cons a₀ a' ih =>
      rw [List.cons_append,
        r324WithinHalfOrdinaryRunLength_cons] at hlt
      by_cases h0 :
          r324WithinHalfListPredecessorSlot processed a₀ = 0
      · rw [if_pos h0] at hlt
        exact absurd hlt (by omega)
      · rw [if_neg h0] at hlt
        have hlt' :
            a'.length <
              r324WithinHalfOrdinaryRunLength
                (processed ++ [a₀]) (a' ++ head :: b) := by
          have :
              (a₀ :: a').length = a'.length + 1 :=
            List.length_cons
          omega
        have := ih (processed ++ [a₀]) hlt'
        rwa [List.append_assoc, List.singleton_append] at this

/-- **The head after the run is fed by slot zero.**  When the run does not
exhaust the list, the first head past the run has predecessor slot zero at
the processed prefix extended by the whole run. -/
theorem r324WithinHalfOrdinaryRunLength_drop_eq_slotZero
    {m : ℕ} (processed l : List (R322ExtractionStep m))
    (hlt :
      r324WithinHalfOrdinaryRunLength processed l < l.length) :
    ∃ (head : R322ExtractionStep m)
      (rest : List (R322ExtractionStep m)),
      l.drop (r324WithinHalfOrdinaryRunLength processed l) =
          head :: rest ∧
        r324WithinHalfListPredecessorSlot
          (processed ++
            l.take (r324WithinHalfOrdinaryRunLength processed l))
          head = 0 := by
  induction l generalizing processed with
  | nil => exact absurd hlt (by simp)
  | cons head tail ih =>
      by_cases h0 :
          r324WithinHalfListPredecessorSlot processed head = 0
      · refine ⟨head, tail, ?_, ?_⟩
        · rw [r324WithinHalfOrdinaryRunLength_cons, if_pos h0]
          rfl
        · rw [r324WithinHalfOrdinaryRunLength_cons, if_pos h0]
          simpa using h0
      · have hlt' :
            r324WithinHalfOrdinaryRunLength
                (processed ++ [head]) tail <
              tail.length := by
          rw [r324WithinHalfOrdinaryRunLength_cons,
            if_neg h0] at hlt
          simp only [List.length_cons] at hlt
          omega
        obtain ⟨hd, rest, hdrop, hslot⟩ :=
          ih (processed ++ [head]) hlt'
        refine ⟨hd, rest, ?_, ?_⟩
        · rw [r324WithinHalfOrdinaryRunLength_cons, if_neg h0]
          simpa [List.drop_succ_cons] using hdrop
        · rw [r324WithinHalfOrdinaryRunLength_cons, if_neg h0]
          rw [List.take_succ_cons, ← List.singleton_append,
            ← List.append_assoc]
          exact hslot

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-! ## Processed prefixes are determined by remaining suffixes -/

/-- Two residual prefixes of the same schedule with nested remaining lists
differ by an explicit consumed middle segment, appended to the processed
prefix. -/
theorem exists_processed_append_of_remaining_isSuffix
    (res res' : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hsuffix : res'.remaining.IsSuffix res.remaining) :
    ∃ c : List (R322ExtractionStep m),
      res.remaining = c ++ res'.remaining ∧
        res'.state.processed = res.state.processed ++ c := by
  obtain ⟨c, hc⟩ := hsuffix
  refine ⟨c, hc.symm, ?_⟩
  have h1 := res.schedule_eq
  rw [← hc, ← List.append_assoc] at h1
  exact
    List.append_cancel_right
      (res'.schedule_eq.symm.trans h1)

/-! ## Discharge for complete certified analytic traces -/

namespace R324WithinHalfCertifiedAnalyticTrace

/-- **All-ordinary discharge.**  If the ordinary run covers the whole
remaining list, every certified analytic trace from that residual prefix
is ordinary along all of its heads. -/
theorem ordinaryAlong_of_ordinaryRunLength_eq_length
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale)
    (hrun :
      r324WithinHalfOrdinaryRunLength
          res.state.processed res.remaining =
        res.remaining.length) :
    trace.OrdinaryAlong := by
  apply trace.ordinaryAlong_of_predecessorSlot_ne_zero
  intro res' head tail hrem' hsuffix
  obtain ⟨c, hc, hproc⟩ :=
    exists_processed_append_of_remaining_isSuffix
      res res' hsuffix
  rw [r324WithinHalfPredecessorSlot_eq_listPredecessorSlot,
    hproc]
  rw [hrem'] at hc
  apply
    r324WithinHalfListPredecessorSlot_ne_zero_of_lt_ordinaryRunLength
      res.state.processed c tail head
  rw [← hc, hrun, hc]
  simp only [List.length_append, List.length_cons]
  omega

end R324WithinHalfCertifiedAnalyticTrace

/-! ## Ordinariness along a stop-before-step trace -/

namespace R324WithinHalfStopBeforeStepTrace

variable {terminal : R322ExtractionStep m}
    {suffix : List (R322ExtractionStep m)}

/-- Every head genuinely consumed by a stop-before-step trace has a
nonzero sparse predecessor slot.  The retained stop step itself is not
constrained. -/
def OrdinaryAlong
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res scale) : Prop :=
  match trace with
  | .stop .. => True
  | @R324WithinHalfStopBeforeStepTrace.step
      _ _ _ _ _ _ _
      current head _tail _hremaining _ _ _ _ next =>
      r324WithinHalfPredecessorSlot current.state head ≠ 0 ∧
        next.OrdinaryAlong

/-- The retained named suffix is a suffix of every remaining list met by
the trace, in particular of the starting one. -/
theorem isSuffix_remaining
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res scale) :
    (terminal :: suffix).IsSuffix res.remaining := by
  induction trace with
  | stop stop scale hremaining certificate =>
      rw [hremaining]
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      rw [hremaining]
      exact ih.trans (List.suffix_cons head tail)

/-- Ordinariness along a stop-before-step trace follows from the purely
combinatorial statement for every strictly pre-stop head: the retained
named suffix must still lie inside the tail. -/
theorem ordinaryAlong_of_predecessorSlot_ne_zero
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res scale)
    (hpreds :
      ∀ (res' :
          R324WithinHalfResidualPrefix ρ lam ε pairing)
        (head : R322ExtractionStep m)
        (tail : List (R322ExtractionStep m)),
        res'.remaining = head :: tail →
        res'.remaining.IsSuffix res.remaining →
        (terminal :: suffix).IsSuffix tail →
        r324WithinHalfPredecessorSlot res'.state head ≠ 0) :
    trace.OrdinaryAlong := by
  induction trace with
  | stop stop scale hremaining certificate =>
      trivial
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      refine
        ⟨hpreds current head tail hremaining
          (by rw [hremaining])
          (by
            have := next.isSuffix_remaining
            rwa [current.afterHead_remaining
              head tail hremaining] at this), ?_⟩
      apply ih
      intro res' head' tail' hrem' hsuffix hterm
      apply hpreds res' head' tail' hrem' ?_ hterm
      have hstep :
          (current.afterHead
            head tail hremaining).remaining.IsSuffix
            current.remaining := by
        rw [current.afterHead_remaining
          head tail hremaining, hremaining]
        exact List.suffix_cons head tail
      exact hsuffix.trans hstep

/-- **Run discharge for stop traces.**  A stop-before-step trace whose
consumed prefix lies inside the ordinary run is ordinary along every
consumed head. -/
theorem ordinaryAlong_of_le_ordinaryRunLength
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res scale)
    (pre : List (R322ExtractionStep m))
    (hremaining :
      res.remaining = pre ++ terminal :: suffix)
    (hlen :
      pre.length ≤
        r324WithinHalfOrdinaryRunLength
          res.state.processed res.remaining) :
    trace.OrdinaryAlong := by
  apply trace.ordinaryAlong_of_predecessorSlot_ne_zero
  intro res' head tail hrem' hsuffix hterm
  obtain ⟨c, hc, hproc⟩ :=
    exists_processed_append_of_remaining_isSuffix
      res res' hsuffix
  rw [r324WithinHalfPredecessorSlot_eq_listPredecessorSlot,
    hproc]
  rw [hrem'] at hc
  apply
    r324WithinHalfListPredecessorSlot_ne_zero_of_lt_ordinaryRunLength
      res.state.processed c tail head
  rw [← hc]
  refine lt_of_lt_of_le ?_ hlen
  obtain ⟨d, hd⟩ := hterm
  have hlength :
      res.remaining.length =
        pre.length + (suffix.length + 1) := by
    rw [hremaining]
    simp only [List.length_append, List.length_cons]
  have hlength' :
      res.remaining.length =
        c.length + (d.length + (suffix.length + 1)) + 1 := by
    rw [hc, ← hd]
    simp only [List.length_append, List.length_cons]
    omega
  omega

/-! ## Phased transport up to the stop -/

/-- **Integrability transport to the stop.**  Full integrability of the
phased density at the root of an ordinary stop-before-step trace
transports to the stopping prefix, at arbitrary endpoints. -/
theorem integrable_stop_incomingPhasedResidualDensity
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (x y : T4)
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res scale)
    (hordinary : trace.OrdinaryAlong)
    (coefficient :
      (trace.stopPrefix.SurvivingCoordinate → T4) → ℂ)
    (k : Z4)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          res.incomingPhasedResidualDensity
            (coefficient (trace.stopProjection w))
            k ρ ε x y w)
        (Measure.pi fun _ => paperMeasure)) :
    Integrable
      (fun v :
          trace.stopPrefix.SurvivingCoordinate → T4 =>
        trace.stopPrefix.incomingPhasedResidualDensity
          (coefficient v) k ρ ε x y v)
      (Measure.pi fun _ => paperMeasure) := by
  induction trace with
  | stop stop scale hremaining certificate =>
      exact hfull
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      obtain ⟨hpred, hnext⟩ := hordinary
      have hcurrent :
          Integrable
            (fun w : current.SurvivingCoordinate → T4 =>
              current.incomingPhasedResidualDensity
                ((fun v => coefficient (next.stopProjection v))
                  ((current.splitSurvivingPiMeasurableEquiv
                    head tail hremaining w).2))
                k ρ ε x y w)
            (Measure.pi fun _ => paperMeasure) := hfull
      have hpost :=
        current.integrable_afterHead_incomingPhasedResidualDensity_of_ne_zero
          head tail hremaining hpred x y
          (fun v => coefficient (next.stopProjection v))
          k hcurrent internal.internal
      exact ih hnext coefficient hpost

/-- **Phased recursion to the stop.**  Along an ordinary stop-before-step
trace, the weighted incoming phased residual integral transports exactly
to the stopping prefix: the perturbative power drops to twice the retained
remaining order and the density becomes the stop phased density with the
same coefficient, phase mode, and endpoints. -/
theorem lamEps_pow_integral_incomingPhasedResidualDensity_eq_stop
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (x y : T4)
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res scale)
    (hordinary : trace.OrdinaryAlong)
    (coefficient :
      (trace.stopPrefix.SurvivingCoordinate → T4) → ℂ)
    (k : Z4)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          res.incomingPhasedResidualDensity
            (coefficient (trace.stopProjection w))
            k ρ ε x y w)
        (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
        (∫ w : res.SurvivingCoordinate → T4,
          res.incomingPhasedResidualDensity
            (coefficient (trace.stopProjection w))
            k ρ ε x y w
          ∂Measure.pi fun _ => paperMeasure) =
      (lamEps lam ε : ℂ) ^
          (2 * trace.stopPrefix.remainingOrder) *
        (∫ v :
            trace.stopPrefix.SurvivingCoordinate → T4,
          trace.stopPrefix.incomingPhasedResidualDensity
            (coefficient v) k ρ ε x y v
          ∂Measure.pi fun _ => paperMeasure) := by
  induction trace with
  | stop stop scale hremaining certificate =>
      rfl
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      obtain ⟨hpred, hnext⟩ := hordinary
      have hcurrent :
          Integrable
            (fun w : current.SurvivingCoordinate → T4 =>
              current.incomingPhasedResidualDensity
                ((fun v => coefficient (next.stopProjection v))
                  ((current.splitSurvivingPiMeasurableEquiv
                    head tail hremaining w).2))
                k ρ ε x y w)
            (Measure.pi fun _ => paperMeasure) := hfull
      have hpost :=
        current.integrable_afterHead_incomingPhasedResidualDensity_of_ne_zero
          head tail hremaining hpred x y
          (fun v => coefficient (next.stopProjection v))
          k hcurrent internal.internal
      change
        (lamEps lam ε : ℂ) ^ (2 * current.remainingOrder) *
            (∫ w : current.SurvivingCoordinate → T4,
              current.incomingPhasedResidualDensity
                ((fun v => coefficient (next.stopProjection v))
                  ((current.splitSurvivingPiMeasurableEquiv
                    head tail hremaining w).2))
                k ρ ε x y w
              ∂Measure.pi fun _ => paperMeasure) =
          (lamEps lam ε : ℂ) ^
              (2 * next.stopPrefix.remainingOrder) *
            (∫ v :
                next.stopPrefix.SurvivingCoordinate → T4,
              next.stopPrefix.incomingPhasedResidualDensity
                (coefficient v) k ρ ε x y v
              ∂Measure.pi fun _ => paperMeasure)
      rw [
        current.lamEps_pow_integral_incomingPhasedResidualDensity_eq_afterHead_of_ne_zero
          head tail hremaining hpred x y
          (fun v => coefficient (next.stopProjection v))
          k hcurrent internal.internal]
      exact ih hnext coefficient hpost

end R324WithinHalfStopBeforeStepTrace

/-! ## The exceptional entry at an arbitrary slot-zero-fed head

The proved exceptional collapse machinery is anchored at the refined
physical root.  The two identities below are its endpoint-agnostic core at
an arbitrary residual prefix: the transported outgoing Fourier mode of a
slot-zero-fed head re-anchors the phase at the post-head anchor with one
paper second-order decay, and the phased density splits pointwise into
the head character, the translated erased raw local core, and the
coefficient with the ordinary outer factor.  Both hold at every pair of
Fourier-evaluated endpoints, in particular at the endpoint `0` produced
by the first exceptional collapse. -/

section ExceptionalEntry

variable (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)

/-- The transported outgoing mode of a slot-zero-fed head at an arbitrary
residual prefix: one paper second-order decay times the incoming character
read at the post-head phase anchor.  Generalizes the root-anchored
assembly identity to every stop of the alternating trace. -/
theorem incomingExceptionalTransportedMode_eq_decay_mul_afterHead_anchor
    (hpred :
      r324WithinHalfPredecessorSlot res.state head = 0)
    (k : Z4) (x y : T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    incomingExceptionalTransportedMode k
        (res.headSuccessorPoint
          head tail hremaining x y v)
        (res.state.edges
          (res.headContext
            head tail hremaining).outgoingSlot) =
      (paperSecondOrderModeDecay k : ℂ) *
        charT4 k
          ((res.afterHead
            head tail hremaining).incomingPhaseAnchor
              x y v) := by
  have hout :
      res.state.edges
          (res.headContext
            head tail hremaining).outgoingSlot =
        greenFn :=
    res.state_edges_head_outgoing_eq_greenFn
      head tail hremaining
  have hmode :
      incomingExceptionalTransportedMode k
          (res.headSuccessorPoint
            head tail hremaining x y v)
          (res.state.edges
            (res.headContext
              head tail hremaining).outgoingSlot) =
        translatedGreenMode k
          (res.headSuccessorPoint
            head tail hremaining x y v) := by
    rw [hout]
    rfl
  rw [hmode, translatedGreenMode_eq]
  unfold paperSecondOrderModeDecay paperModeNormSq
  rw [
    res.incomingPhaseAnchor_afterHead_eq_headSuccessorPoint
      head tail hremaining hpred x y v]
  ring

/-- Consumer form of the re-anchoring identity at an arbitrary
slot-zero-fed head: together with the decay extracted by the incoming
Fourier evaluation, the collapse leaves a squared second-order decay and
the phase re-anchored after the head. -/
theorem paperDecay_mul_incomingExceptionalTransportedMode_mul_eq_afterHead_anchor
    (hpred :
      r324WithinHalfPredecessorSlot res.state head = 0)
    (k : Z4) (x y : T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4)
    (payload : ℂ) :
    (paperSecondOrderModeDecay k : ℂ) *
        incomingExceptionalTransportedMode k
          (res.headSuccessorPoint
            head tail hremaining x y v)
          (res.state.edges
            (res.headContext
              head tail hremaining).outgoingSlot) *
        payload =
      (paperSecondOrderModeDecay k : ℂ) ^ 2 *
        charT4 k
          ((res.afterHead
            head tail hremaining).incomingPhaseAnchor
              x y v) *
        payload := by
  rw [
    res.incomingExceptionalTransportedMode_eq_decay_mul_afterHead_anchor
      head tail hremaining hpred k x y v]
  ring

/-- **Pointwise exceptional entry for the phased density.**  At a
slot-zero-fed head the incoming phased density splits across the
head/post equivalence into the character read at the first head
coordinate, the translated erased raw local core, and the coefficient
carrying the ordinary head outer factor. -/
theorem incomingPhasedResidualDensity_reconstruct_split_of_eq_zero
    (hpred :
      r324WithinHalfPredecessorSlot res.state head = 0)
    (coefficient : ℂ) (k : Z4)
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    res.incomingPhasedResidualDensity
        coefficient k ρ' ε' x y
        ((res.splitSurvivingPiMeasurableEquiv
          head tail hremaining).symm (t, v)) =
      charT4 k
          (t ⟨0, by
            have hn :=
              (res.headContext
                head tail hremaining).one_le_blockOrder
            exact
              Nat.mul_pos (by decide)
                (Nat.zero_lt_of_lt hn)⟩) *
        (res.headContext
          head tail hremaining).incomingErasedTranslatedRawLocalCore
            ρ' ε'
            (res.headSuccessorPoint
              head tail hremaining x y v)
            t *
        (coefficient *
          (res.headOuterFactor
            head tail hremaining ρ' ε' x y v : ℂ)) := by
  unfold incomingPhasedResidualDensity
  rw [
    res.incomingErasedResidualIntegrand_reconstruct_split_of_eq_zero
      head tail hremaining hpred ρ' ε' x y t v,
    res.incomingPhaseAnchor_reconstruct_split_eq_headFirst
      head tail hremaining hpred x y t v]
  ring

end ExceptionalEntry

/-! ## The next exceptional stop of a residual prefix -/

/-- The certified decomposition of a remaining list at its next
slot-zero-fed head: the longest ordinary run is consumed by a certified
stop-before-step trace, ordinary along every consumed head, and the
retained named step is the first head past the run. -/
structure R324WithinHalfNextExceptionalStop
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (scale : Fin (m + 1) → ℝ) where
  pre : List (R322ExtractionStep m)
  terminal : R322ExtractionStep m
  suffix : List (R322ExtractionStep m)
  remaining_eq :
    res.remaining = pre ++ terminal :: suffix
  pre_length_eq :
    pre.length =
      r324WithinHalfOrdinaryRunLength
        res.state.processed res.remaining
  trace :
    R324WithinHalfStopBeforeStepTrace
      terminal suffix res scale
  ordinary : trace.OrdinaryAlong

namespace R324WithinHalfNextExceptionalStop

variable {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}

/-- The stopping state has consumed exactly the recorded ordinary run. -/
theorem stopPrefix_processed_eq
    (data : R324WithinHalfNextExceptionalStop res scale) :
    data.trace.stopPrefix.state.processed =
      res.state.processed ++ data.pre := by
  apply
    List.append_cancel_right
      (bs := data.terminal :: data.suffix)
  rw [data.trace.stopPrefix_processed_append_eq_schedule,
    res.schedule_eq, data.remaining_eq,
    List.append_assoc]

/-- **The retained head is genuinely exceptional**: at the stopping state
its sparse predecessor slot is literally zero. -/
theorem predecessorSlot_eq_zero
    (data : R324WithinHalfNextExceptionalStop res scale) :
    r324WithinHalfPredecessorSlot
        data.trace.stopPrefix.state data.terminal = 0 := by
  rw [r324WithinHalfPredecessorSlot_eq_listPredecessorSlot,
    data.stopPrefix_processed_eq]
  have hlt :
      r324WithinHalfOrdinaryRunLength
          res.state.processed res.remaining <
        res.remaining.length := by
    rw [← data.pre_length_eq, data.remaining_eq]
    simp only [List.length_append, List.length_cons]
    omega
  obtain ⟨head, rest, hdrop, hslot⟩ :=
    r324WithinHalfOrdinaryRunLength_drop_eq_slotZero
      res.state.processed res.remaining hlt
  rw [← data.pre_length_eq] at hdrop hslot
  rw [data.remaining_eq, List.drop_left] at hdrop
  rw [data.remaining_eq, List.take_left] at hslot
  injection hdrop with hhead _hrest
  rwa [hhead]

/-- Re-anchoring identity read at the packaged next stop: the transported
outgoing mode of the retained head collapses to a squared second-order
decay and the phase re-anchored after the head, at arbitrary endpoints. -/
theorem paperDecay_mul_incomingExceptionalTransportedMode_mul_eq_anchor
    (data : R324WithinHalfNextExceptionalStop res scale)
    (k : Z4) (x y : T4)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
          T4)
    (payload : ℂ) :
    (paperSecondOrderModeDecay k : ℂ) *
        incomingExceptionalTransportedMode k
          (data.trace.stopPrefix.headSuccessorPoint
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq x y v)
          (data.trace.stopPrefix.state.edges
            (data.trace.stopPrefix.headContext
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).outgoingSlot) *
        payload =
      (paperSecondOrderModeDecay k : ℂ) ^ 2 *
        charT4 k
          ((data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq).incomingPhaseAnchor
              x y v) *
        payload :=
  data.trace.stopPrefix.paperDecay_mul_incomingExceptionalTransportedMode_mul_eq_afterHead_anchor
    data.terminal data.suffix
    data.trace.stopPrefix_remaining_eq
    data.predecessorSlot_eq_zero k x y v payload

/-- Pointwise exceptional entry of the phased density at the packaged
next stop. -/
theorem incomingPhasedResidualDensity_reconstruct_split
    (data : R324WithinHalfNextExceptionalStop res scale)
    (coefficient : ℂ) (k : Z4)
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4)
    (t : Fin (2 * residualBlockOrder data.terminal.2) → T4)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
          T4) :
    data.trace.stopPrefix.incomingPhasedResidualDensity
        coefficient k ρ' ε' x y
        ((data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).symm (t, v)) =
      charT4 k
          (t ⟨0, by
            have hn :=
              (data.trace.stopPrefix.headContext
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq).one_le_blockOrder
            exact
              Nat.mul_pos (by decide)
                (Nat.zero_lt_of_lt hn)⟩) *
        (data.trace.stopPrefix.headContext
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).incomingErasedTranslatedRawLocalCore
            ρ' ε'
            (data.trace.stopPrefix.headSuccessorPoint
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq x y v)
            t *
        (coefficient *
          (data.trace.stopPrefix.headOuterFactor
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq
            ρ' ε' x y v : ℂ)) :=
  data.trace.stopPrefix.incomingPhasedResidualDensity_reconstruct_split_of_eq_zero
    data.terminal data.suffix
    data.trace.stopPrefix_remaining_eq
    data.predecessorSlot_eq_zero
    coefficient k ρ' ε' x y t v

end R324WithinHalfNextExceptionalStop

/-- **Existence of the next exceptional stop.**  Whenever the ordinary run
does not exhaust the remaining list, the local block provider builds the
certified stop-before-step trace to the run boundary, ordinary along every
consumed head. -/
theorem nonempty_r324WithinHalfNextExceptionalStop_of_lt_length
    {C K : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K pairing)
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (scale : Fin (m + 1) → ℝ)
    (certificate :
      R324WithinHalfEdgeCertificate res.state scale)
    (hlt :
      r324WithinHalfOrdinaryRunLength
          res.state.processed res.remaining <
        res.remaining.length) :
    Nonempty
      (R324WithinHalfNextExceptionalStop res scale) := by
  obtain ⟨head, rest, hdrop, _hslot⟩ :=
    r324WithinHalfOrdinaryRunLength_drop_eq_slotZero
      res.state.processed res.remaining hlt
  have hsplit :
      res.remaining =
        res.remaining.take
            (r324WithinHalfOrdinaryRunLength
              res.state.processed res.remaining) ++
          head :: rest := by
    conv_lhs =>
      rw [← List.take_append_drop
        (r324WithinHalfOrdinaryRunLength
          res.state.processed res.remaining)
        res.remaining]
    rw [hdrop]
  have hlen :
      (res.remaining.take
          (r324WithinHalfOrdinaryRunLength
            res.state.processed res.remaining)).length =
        r324WithinHalfOrdinaryRunLength
          res.state.processed res.remaining := by
    rw [List.length_take]
    exact min_eq_left hlt.le
  refine
    ⟨{ pre :=
        res.remaining.take
          (r324WithinHalfOrdinaryRunLength
            res.state.processed res.remaining)
       terminal := head
       suffix := rest
       remaining_eq := hsplit
       pre_length_eq := hlen
       trace :=
        R324WithinHalfStopBeforeStepTrace.of_localBlockProvider
          hε hε1 provider head rest _ res scale
          certificate hsplit
       ordinary := ?_ }⟩
  exact
    R324WithinHalfStopBeforeStepTrace.ordinaryAlong_of_le_ordinaryRunLength
      _ _ hsplit (le_of_eq hlen)

/-- **The alternative.**  Every residual prefix either is ordinary along
its whole remaining list, or admits a certified next exceptional stop. -/
theorem ordinaryRunLength_eq_length_or_nonempty_nextExceptionalStop
    {C K : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K pairing)
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (scale : Fin (m + 1) → ℝ)
    (certificate :
      R324WithinHalfEdgeCertificate res.state scale) :
    r324WithinHalfOrdinaryRunLength
        res.state.processed res.remaining =
      res.remaining.length ∨
      Nonempty
        (R324WithinHalfNextExceptionalStop res scale) := by
  rcases lt_or_eq_of_le
      (r324WithinHalfOrdinaryRunLength_le_length
        res.state.processed res.remaining) with hlt | heq
  · exact Or.inr
      (nonempty_r324WithinHalfNextExceptionalStop_of_lt_length
        hε hε1 provider res scale certificate hlt)
  · exact Or.inl heq

/-! ## Discharge at the proved exceptional stop assembly -/

namespace R324IncomingExceptionalStopTraceAssembly

variable {C K : ℝ} {κ : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- The `OrdinaryAlong` hypothesis of the proved phased endgame
theorems holds whenever the ordinary run of the after-head residual
covers the whole retained suffix.  When it does not, the after-head
residual instead admits a certified next exceptional stop by
`nonempty_r324WithinHalfNextExceptionalStop_of_lt_length`. -/
theorem afterHead_ordinaryAlong_of_ordinaryRunLength_eq_length
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq)
        scale)
    (hrun :
      r324WithinHalfOrdinaryRunLength
          (data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq).state.processed
          data.suffix =
        data.suffix.length) :
    trace.OrdinaryAlong :=
  trace.ordinaryAlong_of_ordinaryRunLength_eq_length hrun

end R324IncomingExceptionalStopTraceAssembly

end R324WithinHalfResidualPrefix

end

end Anderson4D
