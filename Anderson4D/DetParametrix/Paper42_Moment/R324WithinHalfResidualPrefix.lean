import Anderson4D.DetParametrix.Paper42_Moment.R324FirstLeftInitialPhysicalFubini
import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfPredecessorTransport

/-!
# Integral-level residual prefixes for one R-324 half

This module packages an arbitrary genuine prefix of the analytic schedule.
The state is generated only by prior `absorb` operations, and the remaining
list is the literal schedule suffix.  The one-step theorem below is therefore
an integral transition between two reachable prefix states.  It does not
identify an original unintegrated production integrand pointwise with either
state.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- A processed prefix and its exact analytic suffix. -/
structure R324WithinHalfResidualPrefix
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m)) where
  state : R324WithinHalfEdgeState m
  remaining : List (R322ExtractionStep m)
  schedule_eq :
    r322AnalyticSchedule pairing =
      state.processed ++ remaining
  reachable :
    R324WithinHalfStateReachable pairing ρ lam ε state

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res :
      R324WithinHalfResidualPrefix
        ρ lam ε pairing)

/-- The all-Green state before any analytic block has been integrated. -/
def initial
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m)) :
    R324WithinHalfResidualPrefix ρ lam ε pairing where
  state := r324InitialWithinHalfEdgeState m
  remaining := r322AnalyticSchedule pairing
  schedule_eq := by
    simp [r324InitialWithinHalfEdgeState]
  reachable := R324WithinHalfStateReachable.initial

/-- Exact perturbative order still present in the suffix. -/
def remainingOrder : ℕ :=
  (res.remaining.map
    (fun step => residualBlockOrder step.2)).sum

/-- Exact perturbative order already absorbed into named edges. -/
def processedOrder : ℕ :=
  (res.state.processed.map
    (fun step => residualBlockOrder step.2)).sum

/-- The prefix/suffix order ledger is just the fixed schedule order, with no
cardinality or asymptotic estimate. -/
theorem processedOrder_add_remainingOrder :
    res.processedOrder + res.remainingOrder =
      ((r322AnalyticSchedule pairing).map
        (fun step => residualBlockOrder step.2)).sum := by
  unfold processedOrder remainingOrder
  rw [res.schedule_eq, List.map_append, List.sum_append]

/-- Context for the literal head of an arbitrary remaining suffix. -/
def headContext
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining :
      res.remaining = head :: tail) :
    R324WithinHalfStepContext pairing where
  state := res.state
  step := head
  suffix := tail
  schedule_eq := by
    rw [res.schedule_eq, hremaining]

/-- Residual data after the literal head has been integrated and absorbed. -/
def afterHead
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining :
      res.remaining = head :: tail) :
    R324WithinHalfResidualPrefix ρ lam ε pairing :=
  let ctx := res.headContext head tail hremaining
  { state := ctx.absorb ρ lam ε
    remaining := tail
    schedule_eq := by
      change
        r322AnalyticSchedule pairing =
          (res.state.processed ++ [head]) ++ tail
      simpa [hremaining, List.append_assoc] using
        res.schedule_eq
    reachable :=
      R324WithinHalfStateReachable.absorb
        ctx res.reachable }

@[simp]
theorem afterHead_remaining
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining :
      res.remaining = head :: tail) :
    (res.afterHead head tail hremaining).remaining = tail :=
  rfl

@[simp]
theorem afterHead_state
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining :
      res.remaining = head :: tail) :
    (res.afterHead head tail hremaining).state =
      (res.headContext head tail hremaining).absorb
        ρ lam ε :=
  rfl

theorem remainingOrder_head
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining :
      res.remaining = head :: tail) :
    res.remainingOrder =
      residualBlockOrder head.2 +
        (res.afterHead head tail hremaining).remainingOrder := by
  unfold remainingOrder
  rw [hremaining]
  rfl

/-- **Arbitrary-prefix integral transition.**

For the actual head of a reachable schedule suffix, the honest raw local
spatial integral updates exactly the predecessor edge of `afterHead`.  The
outer complex factor is fixed during this local integral, and the state
change occurs only in the conclusion. -/
theorem
    lamEps_pow_integral_head_rawLocal_eq_afterHead
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining :
      res.remaining = head :: tail)
    (u : T4) (outer : ℂ)
    (hstandard :
      Integrable
        ((res.headContext head tail hremaining).localIntegrand
          ρ ε u)
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder head.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder head.2)},
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder head.2)
                κB.1
                (res.headContext
                  head tail hremaining).internalEdges
                (primitiveAssemble
                  (residualBlockOrder head.2)
                  (res.headContext
                    head tail hremaining).one_le_blockOrder
                  p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε ^
          (2 * residualBlockOrder head.2) : ℂ) *
        (∫ t : Fin (2 * residualBlockOrder head.2) → T4,
          ((res.headContext
            head tail hremaining).rawLocalIntegrand
              ρ ε u t : ℂ) * outer
          ∂Measure.pi fun _ => paperMeasure) =
      (((res.afterHead
          head tail hremaining).state.edges
          (r324WithinHalfPredecessorSlot
            res.state head) u : ℝ) : ℂ) * outer := by
  exact
    (res.headContext
      head tail hremaining).rawLocalSpatialIntegral_mul_complexOuter_eq_absorb
      ρ lam ε u outer hstandard hinternal

end R324WithinHalfResidualPrefix

/-! ## The genuine first-left selector after its arbitrary analytic prefix -/

/-- The analytic decomposition of the first-left selector produces an
actual reachable residual prefix whose literal head is that selector. -/
theorem exists_r324FirstLeftResidualPrefix
    {m : ℕ} (ρ : SmoothCutoff) (lam ε : ℝ)
    (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :
    ∃ (pre post : List (R322ExtractionStep m))
        (res :
          R324WithinHalfResidualPrefix
            ρ lam ε e₀.1),
      r322AnalyticSchedule e₀.1 =
          pre ++ r324FirstLeftSelectedStep e₀ hleft :: post ∧
        res.state.processed = pre ∧
        res.remaining =
          r324FirstLeftSelectedStep e₀ hleft :: post ∧
        (∀ earlier ∈ pre,
          Disjoint earlier.2
            (selectedExtractionBlock
              e₀.1 Finset.univ hleft)) := by
  obtain ⟨pre, post, hschedule, hdisjoint⟩ :=
    exists_r324FirstLeft_analytic_decomposition
      e₀ hleft
  obtain ⟨state, hreachable, hprocessed⟩ :=
    exists_r324WithinHalfState_of_schedule_prefix
      e₀.1 ρ lam ε pre
      (r324FirstLeftSelectedStep e₀ hleft :: post)
      hschedule
  let res :
      R324WithinHalfResidualPrefix
        ρ lam ε e₀.1 :=
    { state := state
      remaining :=
        r324FirstLeftSelectedStep e₀ hleft :: post
      schedule_eq := by
        rw [hprocessed]
        exact hschedule
      reachable := hreachable }
  exact
    ⟨pre, post, res, hschedule, hprocessed, rfl,
      hdisjoint⟩

end

end Anderson4D
