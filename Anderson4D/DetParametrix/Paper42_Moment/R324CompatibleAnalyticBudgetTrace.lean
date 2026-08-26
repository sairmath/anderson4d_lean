import Anderson4D.DetParametrix.Paper42_Moment.R324Prop41ProviderAtTruncation
import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointErasedPhaseABoundary

/-!
# Compatible analytic and complete-budget traces for R-324

The signed Phase-A collapse and the numerical edge ledger use the same
literal within-half suffix, but intentionally update their scales in
different ways.  The numerical update also charges the outgoing Green edge.

This file constructs the two traces synchronously.  Starting from the same
uniform all-Green scale, the complete-budget scale dominates the analytic
scale slot by slot at every head.  Consequently the terminal active product
appearing after the signed collapse is controlled by the already proved
exact budget-product invariant.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- One signed analytic trace together with a complete numerical budget on
its actual terminal residual state. -/
structure R324CompatibleAnalyticBudgetTrace
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (initialScale : Fin (m + 1) → ℝ) where
  analytic : R324WithinHalfCertifiedAnalyticTrace res initialScale
  budgetScale : Fin (m + 1) → ℝ
  budgetReachable :
    R324WithinHalfBudgetScaleReachable
      pairing ρ C lam ε K A
      analytic.terminalPrefix.state budgetScale
  budgetCertificate :
    R324WithinHalfEdgeCertificate
      analytic.terminalPrefix.state budgetScale
  terminalScale_le : ∀ edge, analytic.terminalScale edge ≤ budgetScale edge

namespace R324CompatibleAnalyticBudgetTrace

/-- The analytic scale update is monotone in its input scales. -/
private theorem analyticUpdate_mono
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (small large : Fin (m + 1) → ℝ)
    (hsmall : R324WithinHalfEdgeCertificate res.state small)
    (hlarge : R324WithinHalfEdgeCertificate res.state large)
    (hle : ∀ edge, small edge ≤ large edge)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hK : 0 ≤ K) :
    ∀ edge,
      r324WithinHalfUpdatedEdgeScale
          (res.headContext head tail hremaining)
          small C lam K edge ≤
        r324WithinHalfUpdatedEdgeScale
          (res.headContext head tail hremaining)
          large C lam K edge := by
  intro edge
  by_cases hedge :
      edge = r324WithinHalfPredecessorSlot res.state head
  · subst edge
    simp only [r324WithinHalfUpdatedEdgeScale,
      R324WithinHalfResidualPrefix.headContext,
      Function.update_self]
    have hinternal :
        r324WithinHalfInternalEdgeScaleProduct
            (res.headContext head tail hremaining) small ≤
          r324WithinHalfInternalEdgeScaleProduct
            (res.headContext head tail hremaining) large := by
      unfold r324WithinHalfInternalEdgeScaleProduct
      exact Finset.prod_le_prod
        (fun j _ =>
          (hsmall.scale_pos
            ((res.headContext head tail hremaining).internalSlot j)).le)
        (fun j _ =>
          hle ((res.headContext head tail hremaining).internalSlot j))
    have hinternal' :
        r324WithinHalfInternalEdgeScaleProduct
            { state := res.state
              step := head
              suffix := tail
              schedule_eq := by
                rw [res.schedule_eq, hremaining] }
            small ≤
          r324WithinHalfInternalEdgeScaleProduct
            { state := res.state
              step := head
              suffix := tail
              schedule_eq := by
                rw [res.schedule_eq, hremaining] }
            large := by
      simpa only [R324WithinHalfResidualPrefix.headContext] using hinternal
    apply mul_le_mul_of_nonneg_right _ hK
    apply mul_le_mul_of_nonneg_right _
      (pow_nonneg (mul_nonneg hC hlam) _)
    exact mul_le_mul
      (hle (r324WithinHalfPredecessorSlot res.state head))
      hinternal'
      (by
        simpa only [R324WithinHalfResidualPrefix.headContext] using
          (hsmall.internalEdgeScaleProduct_pos
            (ctx := res.headContext head tail hremaining)).le)
      (hlarge.scale_pos
        (r324WithinHalfPredecessorSlot res.state head)).le
  · rw [r324WithinHalfUpdatedEdgeScale_of_ne,
      r324WithinHalfUpdatedEdgeScale_of_ne]
    · exact hle edge
    · exact hedge
    · exact hedge

/-- One complete-budget head dominates the corresponding analytic head.
The extra outgoing factor is harmless because budget reachability identifies
it with the uniform base scale `A`, which is at least one. -/
private theorem analyticUpdate_le_budgetUpdate
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (analyticScale budgetScale : Fin (m + 1) → ℝ)
    (analyticCertificate :
      R324WithinHalfEdgeCertificate res.state analyticScale)
    (budgetCertificate :
      R324WithinHalfEdgeCertificate res.state budgetScale)
    (budgetReachable :
      R324WithinHalfBudgetScaleReachable
        pairing ρ C lam ε K A res.state budgetScale)
    (hle : ∀ edge, analyticScale edge ≤ budgetScale edge)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hK : 0 ≤ K)
    (hA : 1 ≤ A) :
    ∀ edge,
      r324WithinHalfUpdatedEdgeScale
          (res.headContext head tail hremaining)
          analyticScale C lam K edge ≤
        res.budgetUpdatedEdgeScale
          head tail hremaining budgetScale C lam K edge := by
  intro edge
  by_cases hedge :
      edge = r324WithinHalfPredecessorSlot res.state head
  · subst edge
    rw [res.budgetUpdatedEdgeScale_predecessor_eq_analytic_mul_outgoing]
    have hmono :=
      analyticUpdate_mono res head tail hremaining
        analyticScale budgetScale analyticCertificate budgetCertificate
        hle hC hlam hK
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
          0 ≤ r324WithinHalfUpdatedEdgeScale
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

/-- Synchronous recursion through the literal suffix constructs the signed
analytic trace and a dominating complete numerical budget on the same
terminal residual prefix. -/
theorem exists_of_providers
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC : 0 < C) (hlam : 0 < lam) (hK : 0 < K)
    (hA : 1 ≤ A)
    (analyticProvider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K pairing)
    (budgetProvider :
      R324WithinHalfBudgetLocalBlockProvider
        ρ C lam ε K A pairing)
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (analyticScale budgetScale : Fin (m + 1) → ℝ)
    (analyticCertificate :
      R324WithinHalfEdgeCertificate res.state analyticScale)
    (budgetReachable :
      R324WithinHalfBudgetScaleReachable
        pairing ρ C lam ε K A res.state budgetScale)
    (budgetCertificate :
      R324WithinHalfEdgeCertificate res.state budgetScale)
    (hle : ∀ edge, analyticScale edge ≤ budgetScale edge) :
    Nonempty
      (R324CompatibleAnalyticBudgetTrace
        (C := C) (K := K) (A := A) res analyticScale) := by
  cases hremaining : res.remaining with
  | nil =>
      let trace :
          R324WithinHalfCertifiedAnalyticTrace res analyticScale :=
        R324WithinHalfCertifiedAnalyticTrace.terminal
          res analyticScale hremaining analyticCertificate
      exact ⟨{
        analytic := trace
        budgetScale := budgetScale
        budgetReachable := by
          simpa [trace,
            R324WithinHalfCertifiedAnalyticTrace.terminalPrefix] using
            budgetReachable
        budgetCertificate := by
          simpa [trace,
            R324WithinHalfCertifiedAnalyticTrace.terminalPrefix] using
            budgetCertificate
        terminalScale_le := by
          intro edge
          simpa [trace,
            R324WithinHalfCertifiedAnalyticTrace.terminalScale] using
            hle edge
      }⟩
  | cons head tail =>
      obtain ⟨_analyticBound, nextAnalyticCertificate⟩ :=
        analyticProvider res head tail hremaining
          analyticScale analyticCertificate
      obtain ⟨_budgetBound, nextBudgetReachable,
          nextBudgetCertificate⟩ :=
        budgetProvider res head tail hremaining
          budgetScale budgetReachable budgetCertificate
      let nextAnalyticScale :=
        r324WithinHalfUpdatedEdgeScale
          (res.headContext head tail hremaining)
          analyticScale C lam K
      let nextBudgetScale :=
        res.budgetUpdatedEdgeScale
          head tail hremaining budgetScale C lam K
      have hnextLe :
          ∀ edge, nextAnalyticScale edge ≤ nextBudgetScale edge := by
        intro edge
        exact analyticUpdate_le_budgetUpdate
          res head tail hremaining analyticScale budgetScale
          analyticCertificate budgetCertificate budgetReachable hle
          hC.le hlam.le hK.le hA edge
      obtain ⟨nextData⟩ :=
        exists_of_providers hε hε1 hC hlam hK hA
          analyticProvider budgetProvider
          (res.afterHead head tail hremaining)
          nextAnalyticScale nextBudgetScale
          nextAnalyticCertificate nextBudgetReachable
          nextBudgetCertificate hnextLe
      let internal :
          R324WithinHalfResidualInternalReady
            res head tail hremaining :=
        ⟨R324WithinHalfEdgeCertificate.eventually_integrable_stepClosedIntegrand_section
          (ctx := res.headContext head tail hremaining)
          analyticCertificate hε hε1⟩
      let trace :
          R324WithinHalfCertifiedAnalyticTrace res analyticScale :=
        R324WithinHalfCertifiedAnalyticTrace.step
          res head tail hremaining analyticScale internal
          nextAnalyticScale nextAnalyticCertificate nextData.analytic
      exact ⟨{
        analytic := trace
        budgetScale := nextData.budgetScale
        budgetReachable := by
          simpa [trace,
            R324WithinHalfCertifiedAnalyticTrace.terminalPrefix] using
            nextData.budgetReachable
        budgetCertificate := by
          simpa [trace,
            R324WithinHalfCertifiedAnalyticTrace.terminalPrefix] using
            nextData.budgetCertificate
        terminalScale_le := by
          intro edge
          simpa [trace,
            R324WithinHalfCertifiedAnalyticTrace.terminalScale] using
            nextData.terminalScale_le edge
      }⟩
termination_by res.remaining.length
decreasing_by simp [hremaining]

/-- The terminal analytic active-scale product is dominated by the exact
complete-budget product. -/
theorem analytic_activeEdgeScaleProduct_le
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {initialScale : Fin (m + 1) → ℝ}
    (data :
      R324CompatibleAnalyticBudgetTrace
        (C := C) (K := K) (A := A) res initialScale) :
    (∏ edge ∈ data.analytic.terminalPrefix.activeEdgeSlots,
        data.analytic.terminalScale edge) ≤
      ∏ edge ∈ data.analytic.terminalPrefix.activeEdgeSlots,
        data.budgetScale edge := by
  exact Finset.prod_le_prod
    (fun edge _ =>
      (data.analytic.terminalCertificate.scale_pos edge).le)
    (fun edge _ => data.terminalScale_le edge)

/-- Closed form of the complete numerical budget controlling the terminal
analytic active product. -/
theorem analytic_activeEdgeScaleProduct_le_closedForm
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {initialScale : Fin (m + 1) → ℝ}
    (data :
      R324CompatibleAnalyticBudgetTrace
        (C := C) (K := K) (A := A) res initialScale) :
    (∏ edge ∈ data.analytic.terminalPrefix.activeEdgeSlots,
        data.analytic.terminalScale edge) ≤
      (∏ _edge ∈
          ({0} ∪
            (r324InitialWithinHalfEdgeState m).active.image
              r324InternalVertexEdgeSlot), A) *
        (C * lam) ^
          (2 * r324WithinHalfProcessedOrder
            data.analytic.terminalPrefix.state) *
        K ^ data.analytic.terminalPrefix.state.processed.length := by
  calc
    _ ≤ ∏ edge ∈ data.analytic.terminalPrefix.activeEdgeSlots,
          data.budgetScale edge :=
      data.analytic_activeEdgeScaleProduct_le
    _ = _ := data.budgetReachable.activeEdgeScaleProduct_eq

end R324CompatibleAnalyticBudgetTrace

end R324WithinHalfResidualPrefix

/-! ## Uniform paper-truncation constructor -/

/-- Proposition 4.1 constructs a signed analytic trace and a compatible
complete numerical budget from the same all-Green root, uniformly in the
pairing and order allowed by the paper truncation. -/
theorem exists_r324InitialCompatibleAnalyticBudgetTrace_at_truncation
    (ρ : SmoothCutoff) :
    ∃ supportConstant C K A : ℝ,
      0 < supportConstant ∧ 0 < C ∧ 0 < K ∧ 1 ≤ A ∧
        ∀ (lam ε : ℝ) (m : ℕ)
          (pairing : PartialPairing (Fin m)),
          0 < lam → 0 < ε → ε ≤ 1 →
          1 ≤ |Real.log ε| →
          m ≤ truncOrder ε →
          Nonempty
            (R324WithinHalfResidualPrefix.R324CompatibleAnalyticBudgetTrace
              (C := C) (K := K) (A := A)
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε pairing) (fun _ => A)) := by
  obtain ⟨supportConstant, C, K,
      hsupport, hC, hK, hprovider⟩ :=
    exists_r324WithinHalfLocalBlockProvider_at_truncation ρ
  obtain ⟨A, hA, hinitial⟩ :=
    exists_r324InitialWithinHalfEdgeCertificate_one_le_uniform
  refine ⟨supportConstant, C, K, A,
    hsupport, hC, hK, hA, ?_⟩
  intro lam ε m pairing hlam hε hε1 hlog hm
  let provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K pairing :=
    hprovider lam ε m pairing hlam hε hε1 hlog hm
  let budgetProvider :
      R324WithinHalfBudgetLocalBlockProvider
        ρ C lam ε K A pairing :=
    r324WithinHalfBudgetLocalBlockProvider_of_localBlockProvider
      hA provider
  exact
    R324WithinHalfResidualPrefix.R324CompatibleAnalyticBudgetTrace.exists_of_providers
      hε hε1 hC hlam hK hA provider budgetProvider
      (R324WithinHalfResidualPrefix.initial ρ lam ε pairing)
      (fun _ => A) (fun _ => A) (hinitial m)
      R324WithinHalfBudgetScaleReachable.initial (hinitial m)
      (fun _ => le_rfl)

end

end Anderson4D
