import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalStopTraceAssembly
import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfBudgetInvariant
import Anderson4D.DetParametrix.Paper42_Moment.R324OrdinaryAlongDischarge

/-!
# Complete budget at the paper's incoming exceptional stop

The analytic stop trace and the complete numerical budget follow the same
literal prefix of the Section 4.2 schedule.  This file synchronizes those
two already-established recursions.  It introduces no estimate: the budget
provider is simply called at each head genuinely consumed by the stop trace,
and the resulting reachability witness and edge certificate are retained at
the exact analytic stopping state.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

namespace R324WithinHalfResidualPrefix
namespace R324WithinHalfStopBeforeStepTrace

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}
    {terminal : R322ExtractionStep m}
    {suffix : List (R322ExtractionStep m)}

/-- Run the complete-budget provider along exactly the heads already
certified by an analytic stop-before-step trace.  In particular, neither
the retained terminal nor any part of its suffix is consumed. -/
theorem exists_budgetScale_at_stop
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    {analyticScale budgetScale : Fin (m + 1) -> Real}
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res analyticScale)
    (provider :
      R324WithinHalfBudgetLocalBlockProvider
        rho C lam eps K A pairing)
    (reachable :
      R324WithinHalfBudgetScaleReachable
        pairing rho C lam eps K A res.state budgetScale)
    (certificate :
      R324WithinHalfEdgeCertificate res.state budgetScale) :
    exists stopBudgetScale : Fin (m + 1) -> Real,
      R324WithinHalfBudgetScaleReachable
          pairing rho C lam eps K A
          trace.stopPrefix.state stopBudgetScale /\
        R324WithinHalfEdgeCertificate
          trace.stopPrefix.state stopBudgetScale := by
  induction trace generalizing budgetScale with
  | stop stop analyticScale hremaining analyticCertificate =>
      exact ⟨budgetScale, reachable, certificate⟩
  | step current head tail hremaining analyticScale internal
      nextAnalyticScale nextAnalyticCertificate next ih =>
      obtain ⟨_localBound, nextReachable, nextBudgetCertificate⟩ :=
        provider current head tail hremaining budgetScale
          reachable certificate
      exact ih nextReachable nextBudgetCertificate

end R324WithinHalfStopBeforeStepTrace

namespace R324IncomingExceptionalStopTraceAssembly

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) -> Real}

/-- Consumer form at the incoming exceptional package selected by the
paper: start from the uniform all-Green budget and synchronize it with the
already-built analytic prefix. -/
theorem exists_completeBudget_at_stop
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) pairing initialScale)
    (provider :
      R324WithinHalfBudgetLocalBlockProvider
        rho C lam eps K A pairing)
    (initialCertificate :
      R324WithinHalfEdgeCertificate
        (r324InitialWithinHalfEdgeState m) (fun _ => A)) :
    exists stopBudgetScale : Fin (m + 1) -> Real,
      R324WithinHalfBudgetScaleReachable
          pairing rho C lam eps K A
          data.trace.stopPrefix.state stopBudgetScale /\
        R324WithinHalfEdgeCertificate
          data.trace.stopPrefix.state stopBudgetScale :=
  data.trace.exists_budgetScale_at_stop provider
    R324WithinHalfBudgetScaleReachable.initial initialCertificate

/-! ## A synchronized, pointwise-dominating stop package

The light stop trace type intentionally permits an arbitrary certified
`nextScale`; consequently a pointwise comparison with the canonical complete
budget cannot be recovered from an already packaged trace.  The endpoint
argument needs that comparison, so the following package builds the analytic
and complete-budget prefixes synchronously from the same literal `pre` list.
This is the stopped-prefix analogue of
`R324CompatibleAnalyticBudgetTrace.exists_of_providers`.
-/

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}

/-- An incoming exceptional stop together with the canonical complete budget
on the same physical residual state. -/
structure R324IncomingExceptionalBudgetedStopTraceAssembly
    (pairing : PartialPairing (Fin m)) where
  data :
    R324IncomingExceptionalStopTraceAssembly
      (ρ := rho) (C := C) (lam := lam)
      (ε := eps) (K := K) pairing (fun _ => A)
  stopBudgetScale : Fin (m + 1) -> Real
  budgetReachable :
    R324WithinHalfBudgetScaleReachable
      pairing rho C lam eps K A
      data.trace.stopPrefix.state stopBudgetScale
  budgetCertificate :
    R324WithinHalfEdgeCertificate
      data.trace.stopPrefix.state stopBudgetScale
  stopScale_le : forall edge, data.stopScale edge <= stopBudgetScale edge
  stopBudget_zero_eq_base : stopBudgetScale 0 = A

namespace R324IncomingExceptionalBudgetedStopTraceAssembly

/-- Monotonicity of the signed analytic scale update. -/
theorem analyticUpdate_mono
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (small large : Fin (m + 1) -> Real)
    (hsmall : R324WithinHalfEdgeCertificate res.state small)
    (hlarge : R324WithinHalfEdgeCertificate res.state large)
    (hle : forall edge, small edge <= large edge)
    (hC : 0 <= C) (hlam : 0 <= lam) (hK : 0 <= K) :
    forall edge,
      r324WithinHalfUpdatedEdgeScale
          (res.headContext head tail hremaining)
          small C lam K edge <=
        r324WithinHalfUpdatedEdgeScale
          (res.headContext head tail hremaining)
          large C lam K edge := by
  intro edge
  by_cases hedge : edge = r324WithinHalfPredecessorSlot res.state head
  · subst edge
    simp only [r324WithinHalfUpdatedEdgeScale,
      R324WithinHalfResidualPrefix.headContext, Function.update_self]
    have hinternal :
        r324WithinHalfInternalEdgeScaleProduct
            (res.headContext head tail hremaining) small <=
          r324WithinHalfInternalEdgeScaleProduct
            (res.headContext head tail hremaining) large := by
      unfold r324WithinHalfInternalEdgeScaleProduct
      exact Finset.prod_le_prod
        (fun j _ =>
          (hsmall.scale_pos
            ((res.headContext head tail hremaining).internalSlot j)).le)
        (fun j _ =>
          hle ((res.headContext head tail hremaining).internalSlot j))
    apply mul_le_mul_of_nonneg_right _ hK
    apply mul_le_mul_of_nonneg_right _
      (pow_nonneg (mul_nonneg hC hlam) _)
    exact mul_le_mul
      (hle (r324WithinHalfPredecessorSlot res.state head))
      hinternal
      (hsmall.internalEdgeScaleProduct_pos
        (ctx := res.headContext head tail hremaining)).le
      (hlarge.scale_pos
        (r324WithinHalfPredecessorSlot res.state head)).le
  · rw [r324WithinHalfUpdatedEdgeScale_of_ne,
      r324WithinHalfUpdatedEdgeScale_of_ne]
    · exact hle edge
    · exact hedge
    · exact hedge

/-- One complete-budget update dominates the simultaneous signed update.
The only extra factor is the untouched outgoing Green scale, exactly `A`. -/
theorem analyticUpdate_le_budgetUpdate
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (analyticScale budgetScale : Fin (m + 1) -> Real)
    (analyticCertificate :
      R324WithinHalfEdgeCertificate res.state analyticScale)
    (budgetCertificate :
      R324WithinHalfEdgeCertificate res.state budgetScale)
    (budgetReachable :
      R324WithinHalfBudgetScaleReachable
        pairing rho C lam eps K A res.state budgetScale)
    (hle : forall edge, analyticScale edge <= budgetScale edge)
    (hC : 0 <= C) (hlam : 0 <= lam) (hK : 0 <= K)
    (hA : 1 <= A) :
    forall edge,
      r324WithinHalfUpdatedEdgeScale
          (res.headContext head tail hremaining)
          analyticScale C lam K edge <=
        res.budgetUpdatedEdgeScale
          head tail hremaining budgetScale C lam K edge := by
  intro edge
  by_cases hedge : edge = r324WithinHalfPredecessorSlot res.state head
  · subst edge
    rw [res.budgetUpdatedEdgeScale_predecessor_eq_analytic_mul_outgoing]
    have hmono := analyticUpdate_mono
      res head tail hremaining analyticScale budgetScale
      analyticCertificate budgetCertificate hle hC hlam hK
      (r324WithinHalfPredecessorSlot res.state head)
    have hout :
        budgetScale
            (res.headContext head tail hremaining).outgoingSlot = A :=
      budgetReachable.outgoingScale_eq_base
        res rfl head tail hremaining
    rw [hout]
    exact hmono.trans
      (le_mul_of_one_le_right
        (show
          0 <= r324WithinHalfUpdatedEdgeScale
            (res.headContext head tail hremaining)
            budgetScale C lam K
            (r324WithinHalfPredecessorSlot res.state head) by
          simp only [r324WithinHalfUpdatedEdgeScale,
            R324WithinHalfResidualPrefix.headContext,
            Function.update_self]
          apply mul_nonneg
          · apply mul_nonneg
            · exact mul_nonneg
                (budgetCertificate.scale_pos
                  (r324WithinHalfPredecessorSlot res.state head)).le
                (by
                  simpa only [R324WithinHalfResidualPrefix.headContext] using
                    (budgetCertificate.internalEdgeScaleProduct_pos
                      (ctx := res.headContext head tail hremaining)).le)
            · exact pow_nonneg (mul_nonneg hC hlam) _
          · exact hK)
        hA)
  · rw [r324WithinHalfUpdatedEdgeScale_of_ne,
      res.budgetUpdatedEdgeScale_of_ne]
    · exact hle edge
    · exact hedge
    · exact hedge

/-- Build both stopped prefixes along one literal proper-prefix list. -/
theorem exists_pairedStopBefore
    (hC : 0 <= C) (hlam : 0 <= lam) (hK : 0 <= K) (hA : 1 <= A)
    (hε : 0 < eps) (hε1 : eps <= 1)
    (analyticProvider :
      R324WithinHalfLocalBlockProvider rho C lam eps K pairing)
    (budgetProvider :
      R324WithinHalfBudgetLocalBlockProvider rho C lam eps K A pairing)
    (terminal : R322ExtractionStep m)
    (suffix pre : List (R322ExtractionStep m))
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (analyticScale budgetScale : Fin (m + 1) -> Real)
    (analyticCertificate :
      R324WithinHalfEdgeCertificate res.state analyticScale)
    (budgetReachable :
      R324WithinHalfBudgetScaleReachable
        pairing rho C lam eps K A res.state budgetScale)
    (budgetCertificate :
      R324WithinHalfEdgeCertificate res.state budgetScale)
    (hle : forall edge, analyticScale edge <= budgetScale edge)
    (hremaining : res.remaining = pre ++ terminal :: suffix) :
    exists trace :
        R324WithinHalfStopBeforeStepTrace
          terminal suffix res analyticScale,
      exists stopBudgetScale : Fin (m + 1) -> Real,
        R324WithinHalfBudgetScaleReachable
            pairing rho C lam eps K A
            trace.stopPrefix.state stopBudgetScale /\
          R324WithinHalfEdgeCertificate
            trace.stopPrefix.state stopBudgetScale /\
          (forall edge, trace.stopScale edge <= stopBudgetScale edge) /\
          (trace.OrdinaryAlong -> stopBudgetScale 0 = budgetScale 0) := by
  induction pre generalizing res analyticScale budgetScale with
  | nil =>
      let trace :=
        R324WithinHalfStopBeforeStepTrace.stop
          res analyticScale (by simpa using hremaining) analyticCertificate
      refine ⟨trace, budgetScale, ?_, ?_, ?_, ?_⟩
      · simpa [trace, R324WithinHalfStopBeforeStepTrace.stopPrefix] using
          budgetReachable
      · simpa [trace, R324WithinHalfStopBeforeStepTrace.stopPrefix] using
          budgetCertificate
      · intro edge
        simpa [trace, R324WithinHalfStopBeforeStepTrace.stopScale] using
          hle edge
      · intro _hordinary
        rfl
  | cons head rest ih =>
      let tail : List (R322ExtractionStep m) := rest ++ terminal :: suffix
      have hhead : res.remaining = head :: tail := by
        simpa only [tail, List.cons_append] using hremaining
      obtain ⟨_localBound, nextAnalyticCertificate⟩ :=
        analyticProvider res head tail hhead analyticScale analyticCertificate
      obtain ⟨_budgetBound, nextBudgetReachable,
          nextBudgetCertificate⟩ :=
        budgetProvider res head tail hhead budgetScale
          budgetReachable budgetCertificate
      let nextAnalyticScale :=
        r324WithinHalfUpdatedEdgeScale
          (res.headContext head tail hhead) analyticScale C lam K
      let nextBudgetScale :=
        res.budgetUpdatedEdgeScale
          head tail hhead budgetScale C lam K
      have hnextLe : forall edge,
          nextAnalyticScale edge <= nextBudgetScale edge :=
        analyticUpdate_le_budgetUpdate
          res head tail hhead analyticScale budgetScale
          analyticCertificate budgetCertificate budgetReachable hle
          hC hlam hK hA
      obtain ⟨nextTrace, stopBudgetScale,
          stopReachable, stopCertificate, hstopLe, hstopZero⟩ :=
        ih (res := res.afterHead head tail hhead)
          (analyticScale := nextAnalyticScale)
          (budgetScale := nextBudgetScale)
          nextAnalyticCertificate nextBudgetReachable
          nextBudgetCertificate hnextLe rfl
      let internal :
          R324WithinHalfResidualInternalReady res head tail hhead :=
        ⟨R324WithinHalfEdgeCertificate.eventually_integrable_stepClosedIntegrand_section
          (ctx := res.headContext head tail hhead)
          analyticCertificate hε hε1⟩
      let trace :=
        R324WithinHalfStopBeforeStepTrace.step
          res head tail hhead analyticScale internal
          nextAnalyticScale nextAnalyticCertificate nextTrace
      refine ⟨trace, stopBudgetScale, ?_, ?_, ?_, ?_⟩
      · simpa [trace, R324WithinHalfStopBeforeStepTrace.stopPrefix] using
          stopReachable
      · simpa [trace, R324WithinHalfStopBeforeStepTrace.stopPrefix] using
          stopCertificate
      · intro edge
        simpa [trace, R324WithinHalfStopBeforeStepTrace.stopScale] using
          hstopLe edge
      · intro hord
        have hord' :
            r324WithinHalfPredecessorSlot res.state head ≠ 0 /\
              nextTrace.OrdinaryAlong := by
          simpa [trace,
            R324WithinHalfStopBeforeStepTrace.OrdinaryAlong] using hord
        have hnextZero : nextBudgetScale 0 = budgetScale 0 := by
          dsimp only [nextBudgetScale]
          rw [res.budgetUpdatedEdgeScale_of_ne]
          exact Ne.symm hord'.1
        exact (hstopZero hord'.2).trans hnextZero

/-- A stop before a retained block whose left endpoint is vertex zero is
ordinary along every genuinely consumed head.  The retained zero vertex is
still active after the whole prefix; hence it was active before each earlier
head, while disjointness from that head forces the head to start strictly to
its right.  Its internal edge slot is therefore a nonzero predecessor
candidate. -/
theorem R324WithinHalfStopBeforeStepTrace.ordinaryAlong_of_terminal_left_eq_zero
    {terminal : R322ExtractionStep m}
    {suffix : List (R322ExtractionStep m)}
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    {scale : Fin (m + 1) -> Real}
    (trace :
      R324WithinHalfStopBeforeStepTrace terminal suffix res scale)
    (hleft : terminal.1.1.val = 0) :
    trace.OrdinaryAlong /\ terminal.1.1 ∈ res.state.active := by
  induction trace with
  | stop stop scale hremaining certificate =>
      refine ⟨trivial, ?_⟩
      have hactive :=
        r322AnalyticSchedule_step_endpoints_mem_activeCarrier
          pairing stop.state.processed suffix terminal (by
            rw [stop.schedule_eq, hremaining])
      simpa only [R324WithinHalfEdgeState.active] using hactive.1
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      obtain ⟨hordNext, hterminalPost⟩ := ih
      have hterminalCurrent : terminal.1.1 ∈ current.state.active := by
        rw [current.afterHead_active head tail hremaining] at hterminalPost
        exact (Finset.mem_sdiff.mp hterminalPost).1
      have hterminalNotHead : terminal.1.1 ∉ head.2 := by
        rw [current.afterHead_active head tail hremaining] at hterminalPost
        exact (Finset.mem_sdiff.mp hterminalPost).2
      have hheadSchedule : head ∈ r322AnalyticSchedule pairing := by
        rw [current.schedule_eq, hremaining]
        simp
      have hheadLeftMem : head.1.1 ∈ head.2 :=
        (r322AnalyticSchedule_forall_aligned
          pairing head hheadSchedule).1
      have hleftNe : head.1.1 ≠ terminal.1.1 := by
        intro heq
        exact hterminalNotHead (heq ▸ hheadLeftMem)
      have hvertexLt : terminal.1.1 < head.1.1 := by
        apply Fin.mk_lt_mk.mpr
        have hneVal : head.1.1.val ≠ 0 := by
          intro hz
          apply hleftNe
          apply Fin.ext
          omega
        rw [hleft]
        exact Nat.pos_of_ne_zero hneVal
      have hcandidate :
          r324InternalVertexEdgeSlot terminal.1.1 ∈
            r324WithinHalfPredecessorCandidates current.state head := by
        rw [r324WithinHalfPredecessorCandidates]
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr
          ⟨terminal.1.1,
            Finset.mem_filter.mpr ⟨hterminalCurrent, hvertexLt⟩, rfl⟩
      have hcandidateLe :=
        r324WithinHalfCandidate_le_predecessorSlot
          current.state head
          (r324InternalVertexEdgeSlot terminal.1.1) hcandidate
      have hpred :
          r324WithinHalfPredecessorSlot current.state head ≠ 0 := by
        intro hzero
        apply r324InternalVertexEdgeSlot_ne_zero terminal.1.1
        apply Fin.le_zero_iff.mp
        simpa only [hzero] using hcandidateLe
      exact ⟨⟨hpred, hordNext⟩, hterminalCurrent⟩

/-- Canonical construction of the incoming exceptional stop and its
pointwise-dominating complete budget. -/
theorem exists_of_initial_certificate
    (hm : 0 < m)
    (hremoved : (⟨0, hm⟩ : Fin m) ∉ finalActive pairing)
    (hε : 0 < eps) (hε1 : eps <= 1)
    (hC : 0 <= C) (hlam : 0 <= lam) (hK : 0 <= K) (hA : 1 <= A)
    (analyticProvider :
      R324WithinHalfLocalBlockProvider rho C lam eps K pairing)
    (budgetProvider :
      R324WithinHalfBudgetLocalBlockProvider rho C lam eps K A pairing)
    (initialCertificate :
      R324WithinHalfEdgeCertificate
        (r324InitialWithinHalfEdgeState m) (fun _ => A)) :
    Nonempty
      (R324IncomingExceptionalBudgetedStopTraceAssembly
        (rho := rho) (C := C) (lam := lam)
        (eps := eps) (K := K) (A := A) pairing) := by
  obtain ⟨seed⟩ :=
    R324IncomingExceptionalStopTraceAssembly.exists_of_initial_certificate
      hm hremoved hε hε1 analyticProvider initialCertificate
  let initial := R324WithinHalfResidualPrefix.initial rho lam eps pairing
  obtain ⟨trace, stopBudgetScale,
      stopReachable, stopCertificate, hstopLe, hstopZero⟩ :=
    exists_pairedStopBefore hC hlam hK hA hε hε1
      analyticProvider budgetProvider seed.terminal seed.suffix seed.pre
      initial (fun _ => A) (fun _ => A) initialCertificate
      R324WithinHalfBudgetScaleReachable.initial initialCertificate
      (fun _ => le_rfl) (by
        change r322AnalyticSchedule pairing =
          seed.pre ++ seed.terminal :: seed.suffix
        exact seed.schedule_eq)
  let data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) pairing (fun _ => A) :=
    { pre := seed.pre
      suffix := seed.suffix
      terminal := seed.terminal
      schedule_eq := seed.schedule_eq
      left_eq_zero := seed.left_eq_zero
      trace := trace }
  exact ⟨{
    data := data
    stopBudgetScale := stopBudgetScale
    budgetReachable := by
      simpa only [data] using stopReachable
    budgetCertificate := by
      simpa only [data] using stopCertificate
    stopScale_le := by
      intro edge
      simpa only [data,
        R324IncomingExceptionalStopTraceAssembly.stopScale] using
        hstopLe edge
    stopBudget_zero_eq_base := by
      apply hstopZero
      exact
        (R324WithinHalfStopBeforeStepTrace.ordinaryAlong_of_terminal_left_eq_zero
          trace seed.left_eq_zero).1
  }⟩

/-- The canonical complete-budget continuation after charging the retained
incoming head once. -/
def afterHeadBudgetScale
    (pack : R324IncomingExceptionalBudgetedStopTraceAssembly
      (rho := rho) (C := C) (lam := lam)
      (eps := eps) (K := K) (A := A) pairing) :
    Fin (m + 1) -> Real :=
  pack.data.trace.stopPrefix.budgetUpdatedEdgeScale
    pack.data.terminal pack.data.suffix
    pack.data.trace.stopPrefix_remaining_eq
    pack.stopBudgetScale C lam K

theorem afterHeadBudgetReachable
    (pack : R324IncomingExceptionalBudgetedStopTraceAssembly
      (rho := rho) (C := C) (lam := lam)
      (eps := eps) (K := K) (A := A) pairing) :
    R324WithinHalfBudgetScaleReachable
      pairing rho C lam eps K A
      (pack.data.trace.stopPrefix.afterHead
        pack.data.terminal pack.data.suffix
        pack.data.trace.stopPrefix_remaining_eq).state
      pack.afterHeadBudgetScale :=
  R324WithinHalfBudgetScaleReachable.afterHead
    pack.data.trace.stopPrefix pack.data.terminal pack.data.suffix
    pack.data.trace.stopPrefix_remaining_eq pack.budgetReachable

theorem afterHeadBudgetCertificate
    (pack : R324IncomingExceptionalBudgetedStopTraceAssembly
      (rho := rho) (C := C) (lam := lam)
      (eps := eps) (K := K) (A := A) pairing)
    (budgetProvider :
      R324WithinHalfBudgetLocalBlockProvider
        rho C lam eps K A pairing) :
    R324WithinHalfEdgeCertificate
      (pack.data.trace.stopPrefix.afterHead
        pack.data.terminal pack.data.suffix
        pack.data.trace.stopPrefix_remaining_eq).state
      pack.afterHeadBudgetScale := by
  exact
    (budgetProvider pack.data.trace.stopPrefix
      pack.data.terminal pack.data.suffix
      pack.data.trace.stopPrefix_remaining_eq
      pack.stopBudgetScale pack.budgetReachable
      pack.budgetCertificate).2.2

end R324IncomingExceptionalBudgetedStopTraceAssembly

end R324IncomingExceptionalStopTraceAssembly
end R324WithinHalfResidualPrefix

end

end Anderson4D
