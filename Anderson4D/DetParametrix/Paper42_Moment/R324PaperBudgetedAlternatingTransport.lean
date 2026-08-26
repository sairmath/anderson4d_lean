import Anderson4D.DetParametrix.Paper42_Moment.R324PaperIncomingStopBudgetAdapter
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperIncomingSuffixInsertedBudget

/-!
# Complete-budget control of the incoming alternating suffix

Paper Section 4.2 removes every ordinary interval before taking a norm.  A
slot-zero-fed head is then Fourier-collapsed and the literal suffix resumes.
The analytic driver already implements that alternation.  This file runs its
numerical complete budget along the same literal heads.

The useful invariant is deliberately small: the norm of the accumulated
exceptional multiplier, times the current slot-zero budget, is bounded by
the terminal slot-zero budget.  At an ordinary run slot zero is untouched;
at an exceptional head the inserted cosine estimate is exactly one complete
budget update after enlarging the universal one-block constant once.  Thus
no exceptional suffix block pays a second `eps^-2` endpoint loss.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}

/-! ## Enlarging the one-block constant -/

/-- A local analytic block provider remains valid after enlarging its
nonnegative universal one-block constant. -/
theorem R324WithinHalfLocalBlockProvider.mono_K
    {K' : Real} (hC : 0 <= C) (hlam : 0 <= lam)
    (hKK' : K <= K')
    (provider :
      R324WithinHalfLocalBlockProvider rho C lam eps K pairing) :
    R324WithinHalfLocalBlockProvider rho C lam eps K' pairing := by
  intro res head tail hremaining scale certificate
  obtain ⟨hbound, nextCertificate⟩ :=
    provider res head tail hremaining scale certificate
  let ctx := res.headContext head tail hremaining
  have hscale : forall edge,
      r324WithinHalfUpdatedEdgeScale ctx scale C lam K edge <=
        r324WithinHalfUpdatedEdgeScale ctx scale C lam K' edge := by
    intro edge
    by_cases hedge :
        edge = r324WithinHalfPredecessorSlot ctx.state ctx.step
    · subst edge
      rw [r324WithinHalfUpdatedEdgeScale_predecessor,
        r324WithinHalfUpdatedEdgeScale_predecessor]
      exact mul_le_mul_of_nonneg_left hKK'
        (mul_nonneg
          (mul_nonneg
            (certificate.scale_pos
              (r324WithinHalfPredecessorSlot ctx.state ctx.step)).le
            certificate.internalEdgeScaleProduct_pos.le)
          (pow_nonneg (mul_nonneg hC hlam) _))
    · rw [r324WithinHalfUpdatedEdgeScale_of_ne,
        r324WithinHalfUpdatedEdgeScale_of_ne]
      · exact hedge
      · exact hedge
  have enlargedCertificate :
      R324WithinHalfEdgeCertificate
        (res.afterHead head tail hremaining).state
        (r324WithinHalfUpdatedEdgeScale ctx scale C lam K') :=
    R324WithinHalfEdgeCertificate.of_pointwise_scale_le
      nextCertificate hscale
  refine ⟨?_, enlargedCertificate⟩
  intro x hx
  exact (hbound x hx).trans
    (mul_le_mul_of_nonneg_right
      (hscale (r324WithinHalfPredecessorSlot res.state head))
      (invSqKer_nonneg x))

/-! ## The sharp exceptional-head input -/

/-- Every exceptional head spends its inserted-cosine charge inside the
same complete-budget update used for an ordinary head. -/
def R324WithinHalfInsertedExceptionalHeadBudget
    (rho : SmoothCutoff) (C lam eps K : Real)
    {m : Nat} (pairing : PartialPairing (Fin m)) (k : Z4) : Prop :=
  forall (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (scale : Fin (m + 1) -> Real),
    R324WithinHalfEdgeCertificate res.state scale ->
      ‖res.incomingExceptionalHeadCollapseFactor
          head tail hremaining k‖ <=
        r324WithinHalfInternalEdgeScaleProduct
            (res.headContext head tail hremaining) scale *
          (C * lam) ^ (2 * residualBlockOrder head.2) * K

/-- Proposition 4.1's inserted estimate supplies the exceptional-head
budget once its scalar inserted integral is covered by `K`. -/
theorem r324WithinHalfInsertedExceptionalHeadBudget_of_prop41
    (hε : 0 < eps) (supportConstant primitiveConstant : Real)
    (hprimitive : 0 <= primitiveConstant) (hlam : 0 <= lam)
    (hprop :
      forall (res : R324WithinHalfResidualPrefix rho lam eps pairing)
        (head : R322ExtractionStep m)
        (tail : List (R322ExtractionStep m))
        (hremaining : res.remaining = head :: tail)
        (H : Fin (2 * residualBlockOrder head.2 - 1) -> T4 -> Real),
        IsAdmissiblePrimitiveInput (residualBlockOrder head.2) H ->
          MemEClassT4
              (primitiveKernelDiff rho lam eps
                (residualBlockOrder head.2)
                (res.headContext head tail hremaining).one_le_blockOrder H) /\
            MemEClassT4
              (primitiveKernelInsertedDiff rho lam eps
                (residualBlockOrder head.2)
                (res.headContext head tail hremaining).one_le_blockOrder H) /\
            PrimitiveKernelBounds rho lam eps
              (residualBlockOrder head.2)
              (res.headContext head tail hremaining).one_le_blockOrder
              H supportConstant primitiveConstant)
    (hcharge : forall n : Nat, 1 <= n ->
      (1 / 2 : Real) *
          (max 1 (supportConstant ^ 2) *
            ∫ z : T4,
              primitiveInsertedMajorant primitiveConstant lam eps
                supportConstant n z ∂paperMeasure) <=
        (C * lam) ^ (2 * n) * K)
    (k : Z4) :
    R324WithinHalfInsertedExceptionalHeadBudget
      rho C lam eps K pairing k := by
  intro res head tail hremaining scale certificate
  refine
    (res.norm_incomingExceptionalHeadCollapseFactor_le_scaled_inserted
      head tail hremaining scale certificate hε supportConstant
      primitiveConstant hprimitive hlam
      (fun H hH => hprop res head tail hremaining H hH) k).trans ?_
  have h := mul_le_mul_of_nonneg_left
    (hcharge (residualBlockOrder head.2)
      (res.headContext head tail hremaining).one_le_blockOrder)
    (certificate.internalEdgeScaleProduct_pos
      (ctx := res.headContext head tail hremaining)).le
  simpa only [mul_assoc] using h

/-! ## Slot-zero budget along an ordinary trace -/

/-- A complete budget run along an all-ordinary analytic trace leaves slot
zero unchanged.  No comparison of analytic and budget scales is needed in
this base case; they merely traverse the same literal residual states. -/
theorem R324WithinHalfCertifiedAnalyticTrace.exists_terminalBudget_zero_eq
    (budgetProvider :
      R324WithinHalfBudgetLocalBlockProvider
        rho C lam eps K A pairing)
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    {analyticScale budgetScale : Fin (m + 1) -> Real}
    (trace : R324WithinHalfCertifiedAnalyticTrace res analyticScale)
    (hordinary : trace.OrdinaryAlong)
    (budgetReachable :
      R324WithinHalfBudgetScaleReachable
        pairing rho C lam eps K A res.state budgetScale)
    (budgetCertificate :
      R324WithinHalfEdgeCertificate res.state budgetScale) :
    exists terminalBudgetScale : Fin (m + 1) -> Real,
      R324WithinHalfBudgetScaleReachable
          pairing rho C lam eps K A
          trace.terminalPrefix.state terminalBudgetScale /\
        R324WithinHalfEdgeCertificate
          trace.terminalPrefix.state terminalBudgetScale /\
        terminalBudgetScale 0 = budgetScale 0 := by
  induction trace generalizing budgetScale with
  | terminal terminal analyticScale hremaining analyticCertificate =>
      exact ⟨budgetScale, budgetReachable, budgetCertificate, rfl⟩
  | step current head tail hremaining analyticScale internal
      nextAnalyticScale nextAnalyticCertificate next ih =>
      have hord :
          r324WithinHalfPredecessorSlot current.state head ≠ 0 /\
            next.OrdinaryAlong := hordinary
      obtain ⟨_hbound, nextReachable, nextBudgetCertificate⟩ :=
        budgetProvider current head tail hremaining budgetScale
          budgetReachable budgetCertificate
      let nextBudgetScale :=
        current.budgetUpdatedEdgeScale
          head tail hremaining budgetScale C lam K
      obtain ⟨terminalBudgetScale,
          terminalReachable, terminalCertificate, hterminalZero⟩ :=
        ih hord.2 nextReachable nextBudgetCertificate
      refine ⟨terminalBudgetScale, ?_, ?_, ?_⟩
      · simpa only [R324WithinHalfCertifiedAnalyticTrace.terminalPrefix] using
          terminalReachable
      · simpa only [R324WithinHalfCertifiedAnalyticTrace.terminalPrefix] using
          terminalCertificate
      · have hnextZero : nextBudgetScale 0 = budgetScale 0 := by
          dsimp only [nextBudgetScale]
          rw [current.budgetUpdatedEdgeScale_of_ne]
          exact Ne.symm hord.1
        exact hterminalZero.trans hnextZero

/-! ## Budget-synchronized alternating transport -/

/-- **Paper-order alternating budget.**  There is an exact alternating
transport whose exceptional multiplier is paid by the complete numerical
budget on the same literal schedule.  The invariant is the telescoping
slot-zero inequality

`norm multiplier * currentBudget(0) <= terminalBudget(0)`.

Ordinary runs do not touch slot zero.  At a retained exceptional head the
predecessor is slot zero, and the head budget is dominated by the complete
update because the untouched outgoing scale is `A >= 1`. -/
theorem exists_budgetSynchronizedAlternatingTransport
    (hε : 0 < eps) (hε1 : eps <= 1)
    (hC : 0 <= C) (hlam : 0 <= lam) (hK : 0 <= K) (hA : 1 <= A)
    (analyticProvider :
      R324WithinHalfLocalBlockProvider rho C lam eps K pairing)
    (budgetProvider :
      R324WithinHalfBudgetLocalBlockProvider
        rho C lam eps K A pairing)
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (analyticScale budgetScale : Fin (m + 1) -> Real)
    (analyticCertificate :
      R324WithinHalfEdgeCertificate res.state analyticScale)
    (budgetReachable :
      R324WithinHalfBudgetScaleReachable
        pairing rho C lam eps K A res.state budgetScale)
    (budgetCertificate :
      R324WithinHalfEdgeCertificate res.state budgetScale)
    (hscale : forall edge, analyticScale edge <= budgetScale edge)
    (k : Z4)
    (headBudget :
      R324WithinHalfInsertedExceptionalHeadBudget
        rho C lam eps K pairing k) :
    exists transport : R324WithinHalfAlternatingTransport res,
      exists terminalBudgetScale : Fin (m + 1) -> Real,
        R324WithinHalfBudgetScaleReachable
            pairing rho C lam eps K A
            transport.final.state terminalBudgetScale /\
          R324WithinHalfEdgeCertificate
            transport.final.state terminalBudgetScale /\
          ‖transport.multiplier k‖ * budgetScale 0 <=
            terminalBudgetScale 0 := by
  by_cases hrun :
      r324WithinHalfOrdinaryRunLength
          res.state.processed res.remaining = res.remaining.length
  · let trace :=
      R324WithinHalfCertifiedAnalyticTrace.of_localBlockProvider
        hε hε1 analyticProvider res analyticScale analyticCertificate
    have hord : trace.OrdinaryAlong :=
      trace.ordinaryAlong_of_ordinaryRunLength_eq_length hrun
    obtain ⟨terminalBudgetScale,
        terminalReachable, terminalCertificate, hzero⟩ :=
      trace.exists_terminalBudget_zero_eq budgetProvider hord
        budgetReachable budgetCertificate
    let transport := trace.alternatingTransport hord
    refine ⟨transport, terminalBudgetScale, ?_, ?_, ?_⟩
    · simpa only [transport,
        R324WithinHalfCertifiedAnalyticTrace.alternatingTransport] using
        terminalReachable
    · simpa only [transport,
        R324WithinHalfCertifiedAnalyticTrace.alternatingTransport] using
        terminalCertificate
    · change ‖(1 : Complex)‖ * budgetScale 0 <= terminalBudgetScale 0
      rw [norm_one, one_mul, hzero]
  · have hlt :
        r324WithinHalfOrdinaryRunLength
            res.state.processed res.remaining < res.remaining.length :=
      lt_of_le_of_ne
        (r324WithinHalfOrdinaryRunLength_le_length
          res.state.processed res.remaining) hrun
    obtain ⟨terminal, suffix, hdrop, _hslot⟩ :=
      r324WithinHalfOrdinaryRunLength_drop_eq_slotZero
        res.state.processed res.remaining hlt
    let pre := res.remaining.take
      (r324WithinHalfOrdinaryRunLength
        res.state.processed res.remaining)
    have hsplit : res.remaining = pre ++ terminal :: suffix := by
      conv_lhs =>
        rw [← List.take_append_drop
          (r324WithinHalfOrdinaryRunLength
            res.state.processed res.remaining) res.remaining]
      rw [hdrop]
    have hlen : pre.length =
        r324WithinHalfOrdinaryRunLength
          res.state.processed res.remaining := by
      dsimp only [pre]
      rw [List.length_take, min_eq_left hlt.le]
    obtain ⟨trace, stopBudgetScale,
        stopReachable, stopCertificate, hstopScale, hstopZeroIfOrdinary⟩ :=
      R324IncomingExceptionalStopTraceAssembly.R324IncomingExceptionalBudgetedStopTraceAssembly.exists_pairedStopBefore
          hC hlam hK hA hε hε1 analyticProvider budgetProvider
          terminal suffix pre res analyticScale budgetScale
          analyticCertificate budgetReachable budgetCertificate hscale hsplit
    have hord : trace.OrdinaryAlong :=
      trace.ordinaryAlong_of_le_ordinaryRunLength
        pre hsplit (le_of_eq hlen)
    have hstopZero : stopBudgetScale 0 = budgetScale 0 :=
      hstopZeroIfOrdinary hord
    let data : R324WithinHalfNextExceptionalStop res analyticScale :=
      { pre := pre
        terminal := terminal
        suffix := suffix
        remaining_eq := hsplit
        pre_length_eq := hlen
        trace := trace
        ordinary := hord }
    obtain ⟨_analyticBound, nextAnalyticCertificate⟩ :=
      analyticProvider trace.stopPrefix terminal suffix
        trace.stopPrefix_remaining_eq trace.stopScale trace.stopCertificate
    obtain ⟨_budgetBound, nextBudgetReachable,
        nextBudgetCertificate⟩ :=
      budgetProvider trace.stopPrefix terminal suffix
        trace.stopPrefix_remaining_eq stopBudgetScale
        stopReachable stopCertificate
    let nextAnalyticScale :=
      r324WithinHalfUpdatedEdgeScale
        (trace.stopPrefix.headContext terminal suffix
          trace.stopPrefix_remaining_eq)
        trace.stopScale C lam K
    let nextBudgetScale :=
      trace.stopPrefix.budgetUpdatedEdgeScale
        terminal suffix trace.stopPrefix_remaining_eq
        stopBudgetScale C lam K
    have hnextScale : forall edge,
        nextAnalyticScale edge <= nextBudgetScale edge :=
      R324IncomingExceptionalStopTraceAssembly.R324IncomingExceptionalBudgetedStopTraceAssembly.analyticUpdate_le_budgetUpdate
            trace.stopPrefix terminal suffix trace.stopPrefix_remaining_eq
            trace.stopScale stopBudgetScale trace.stopCertificate
            stopCertificate stopReachable hstopScale hC hlam hK hA
    obtain ⟨sub, terminalBudgetScale,
        terminalReachable, terminalCertificate, hsub⟩ :=
      exists_budgetSynchronizedAlternatingTransport
        hε hε1 hC hlam hK hA analyticProvider budgetProvider
        (trace.stopPrefix.afterHead
          terminal suffix trace.stopPrefix_remaining_eq)
        nextAnalyticScale nextBudgetScale nextAnalyticCertificate
        nextBudgetReachable nextBudgetCertificate hnextScale k headBudget
    let transport := data.alternatingTransport hε hε1 sub
    refine ⟨transport, terminalBudgetScale, ?_, ?_, ?_⟩
    · simpa only [transport, data,
        R324WithinHalfNextExceptionalStop.alternatingTransport] using
        terminalReachable
    · simpa only [transport, data,
        R324WithinHalfNextExceptionalStop.alternatingTransport] using
        terminalCertificate
    · have hfactor :=
        headBudget trace.stopPrefix terminal suffix
          trace.stopPrefix_remaining_eq stopBudgetScale stopCertificate
      have hout :
          stopBudgetScale
              (trace.stopPrefix.headContext terminal suffix
                trace.stopPrefix_remaining_eq).outgoingSlot = A :=
        stopReachable.outgoingScale_eq_base trace.stopPrefix rfl
          terminal suffix trace.stopPrefix_remaining_eq
      have hpred :
          r324WithinHalfPredecessorSlot
              trace.stopPrefix.state terminal = 0 :=
        data.predecessorSlot_eq_zero
      have hfactorUpdate :
          ‖trace.stopPrefix.incomingExceptionalHeadCollapseFactor
              terminal suffix trace.stopPrefix_remaining_eq k‖ *
              budgetScale 0 <= nextBudgetScale 0 := by
        rw [← hstopZero]
        calc
          _ <=
              (r324WithinHalfInternalEdgeScaleProduct
                  (trace.stopPrefix.headContext terminal suffix
                    trace.stopPrefix_remaining_eq) stopBudgetScale *
                (C * lam) ^ (2 * residualBlockOrder terminal.2) * K) *
                  stopBudgetScale 0 :=
            mul_le_mul_of_nonneg_right hfactor
              (stopCertificate.scale_pos 0).le
          _ <= nextBudgetScale 0 := by
            have hnextEq : nextBudgetScale 0 =
                stopBudgetScale 0 *
                  (r324WithinHalfInternalEdgeScaleProduct
                    (trace.stopPrefix.headContext terminal suffix
                      trace.stopPrefix_remaining_eq) stopBudgetScale * A) *
                  (C * lam) ^ (2 * residualBlockOrder terminal.2) * K := by
              dsimp only [nextBudgetScale]
              rw [← hpred,
                trace.stopPrefix.budgetUpdatedEdgeScale_predecessor,
                trace.stopPrefix.headBlockScaleProduct_eq_internal_mul_outgoing,
                hout, hpred]
            rw [hnextEq]
            have hcore : 0 <=
                stopBudgetScale 0 *
                  r324WithinHalfInternalEdgeScaleProduct
                    (trace.stopPrefix.headContext terminal suffix
                      trace.stopPrefix_remaining_eq) stopBudgetScale *
                  (C * lam) ^ (2 * residualBlockOrder terminal.2) * K := by
              exact mul_nonneg
                (mul_nonneg
                  (mul_nonneg (stopCertificate.scale_pos 0).le
                    (stopCertificate.internalEdgeScaleProduct_pos
                      (ctx := trace.stopPrefix.headContext terminal suffix
                        trace.stopPrefix_remaining_eq)).le)
                  (pow_nonneg (mul_nonneg hC hlam) _)) hK
            calc
              _ = stopBudgetScale 0 *
                    r324WithinHalfInternalEdgeScaleProduct
                      (trace.stopPrefix.headContext terminal suffix
                        trace.stopPrefix_remaining_eq) stopBudgetScale *
                    (C * lam) ^ (2 * residualBlockOrder terminal.2) * K := by
                  ring
              _ <=
                  (stopBudgetScale 0 *
                    r324WithinHalfInternalEdgeScaleProduct
                      (trace.stopPrefix.headContext terminal suffix
                        trace.stopPrefix_remaining_eq) stopBudgetScale *
                    (C * lam) ^ (2 * residualBlockOrder terminal.2) * K) * A :=
                le_mul_of_one_le_right hcore hA
              _ = _ := by ring
      change
        ‖sub.multiplier k *
            trace.stopPrefix.incomingExceptionalHeadCollapseFactor
              terminal suffix trace.stopPrefix_remaining_eq k‖ *
            budgetScale 0 <= terminalBudgetScale 0
      rw [norm_mul]
      calc
        ‖sub.multiplier k‖ *
              ‖trace.stopPrefix.incomingExceptionalHeadCollapseFactor
                terminal suffix trace.stopPrefix_remaining_eq k‖ *
              budgetScale 0 =
            ‖sub.multiplier k‖ *
              (‖trace.stopPrefix.incomingExceptionalHeadCollapseFactor
                  terminal suffix trace.stopPrefix_remaining_eq k‖ *
                budgetScale 0) := by ring
        _ <= ‖sub.multiplier k‖ * nextBudgetScale 0 :=
          mul_le_mul_of_nonneg_left hfactorUpdate (norm_nonneg _)
        _ <= terminalBudgetScale 0 := hsub
termination_by res.remaining.length
decreasing_by
  simp only [R324WithinHalfResidualPrefix.afterHead_remaining]
  have hdata : data.suffix.length < res.remaining.length :=
    data.suffix_length_lt
  simpa only [data] using hdata

/-! ## Starting the alternating suffix at the paper's first incoming head -/

/-- Consumer form for the canonical incoming stop.  After the first
ordinary primitive defect has been exposed, the remaining literal suffix is
transported with the same complete budget.  This theorem introduces no new
estimate; it only connects the stopped package to the alternating theorem
above. -/
theorem R324IncomingExceptionalStopTraceAssembly.R324IncomingExceptionalBudgetedStopTraceAssembly.exists_budgetSynchronizedAlternatingTransport_afterHead
    (pack :
      R324IncomingExceptionalStopTraceAssembly.R324IncomingExceptionalBudgetedStopTraceAssembly
          (rho := rho) (C := C) (lam := lam)
          (eps := eps) (K := K) (A := A) pairing)
    (hε : 0 < eps) (hε1 : eps <= 1)
    (hC : 0 <= C) (hlam : 0 <= lam) (hK : 0 <= K) (hA : 1 <= A)
    (analyticProvider :
      R324WithinHalfLocalBlockProvider rho C lam eps K pairing)
    (budgetProvider :
      R324WithinHalfBudgetLocalBlockProvider
        rho C lam eps K A pairing)
    (k : Z4)
    (headBudget :
      R324WithinHalfInsertedExceptionalHeadBudget
        rho C lam eps K pairing k) :
    exists transport : R324WithinHalfAlternatingTransport
        (pack.data.trace.stopPrefix.afterHead
          pack.data.terminal pack.data.suffix
          pack.data.trace.stopPrefix_remaining_eq),
      exists terminalBudgetScale : Fin (m + 1) -> Real,
        R324WithinHalfBudgetScaleReachable
            pairing rho C lam eps K A
            transport.final.state terminalBudgetScale /\
          R324WithinHalfEdgeCertificate
            transport.final.state terminalBudgetScale /\
          ‖transport.multiplier k‖ * pack.afterHeadBudgetScale 0 <=
            terminalBudgetScale 0 := by
  let afterHead :=
    pack.data.trace.stopPrefix.afterHead
      pack.data.terminal pack.data.suffix
      pack.data.trace.stopPrefix_remaining_eq
  let analyticScale :=
    r324WithinHalfUpdatedEdgeScale
      (pack.data.trace.stopPrefix.headContext
        pack.data.terminal pack.data.suffix
        pack.data.trace.stopPrefix_remaining_eq)
      pack.data.stopScale C lam K
  obtain ⟨_headBound, analyticCertificate⟩ :=
    analyticProvider pack.data.trace.stopPrefix
      pack.data.terminal pack.data.suffix
      pack.data.trace.stopPrefix_remaining_eq
      pack.data.stopScale pack.data.trace.stopCertificate
  have hscale : forall edge,
      analyticScale edge <= pack.afterHeadBudgetScale edge := by
    intro edge
    exact
      R324IncomingExceptionalStopTraceAssembly.R324IncomingExceptionalBudgetedStopTraceAssembly.analyticUpdate_le_budgetUpdate
        pack.data.trace.stopPrefix pack.data.terminal pack.data.suffix
        pack.data.trace.stopPrefix_remaining_eq
        pack.data.stopScale pack.stopBudgetScale
        pack.data.trace.stopCertificate pack.budgetCertificate
        pack.budgetReachable pack.stopScale_le hC hlam hK hA edge
  simpa only [afterHead, analyticScale] using
    exists_budgetSynchronizedAlternatingTransport
      hε hε1 hC hlam hK hA analyticProvider budgetProvider
      afterHead analyticScale pack.afterHeadBudgetScale
      analyticCertificate pack.afterHeadBudgetReachable
      (pack.afterHeadBudgetCertificate budgetProvider) hscale k headBudget

end R324WithinHalfResidualPrefix

end

end Anderson4D
