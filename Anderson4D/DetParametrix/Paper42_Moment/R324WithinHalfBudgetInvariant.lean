import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfQuantitativeStep

/-!
# Complete edge-budget invariant for the R-324 within-half schedule

The analytic one-block estimate absorbs the predecessor and all internal
head-edge scales.  The outgoing head edge is a free Green factor, but its
slot is deleted from the sparse carrier.  This module inserts that one
outgoing scale into a numerical budget update and proves the exact active
product recurrence through the genuine suffix.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing)

section Head

variable
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)

include tail hremaining

private abbrev ctx :
    R324WithinHalfStepContext pairing :=
  res.headContext head tail hremaining

private abbrev post :
    R324WithinHalfResidualPrefix ρ lam ε pairing :=
  res.afterHead head tail hremaining

/-- All active edge slots deleted with the literal head: its standard
internal slots and its outgoing right-endpoint slot. -/
def headBlockSlots : Finset (Fin (m + 1)) :=
  res.headInternalSlots head tail hremaining ∪
    {(ctx res head tail hremaining).outgoingSlot}

theorem headBlockSlots_subset_activeEdgeSlots :
    res.headBlockSlots head tail hremaining ⊆
      res.activeEdgeSlots := by
  intro edge hedge
  rw [headBlockSlots] at hedge
  rcases Finset.mem_union.mp hedge with
      hinternal | houtgoing
  · obtain ⟨j, _hj, rfl⟩ :=
      Finset.mem_image.mp hinternal
    exact
      res.internalSlot_mem_activeEdgeSlots
        head tail hremaining j
  · have heq :
        edge =
          (ctx res head tail hremaining).outgoingSlot := by
      simpa using houtgoing
    rw [heq]
    exact
      res.outgoingSlot_mem_activeEdgeSlots
        head tail hremaining

theorem predecessorSlot_not_mem_headBlockSlots :
    r324WithinHalfPredecessorSlot res.state head ∉
      res.headBlockSlots head tail hremaining := by
  rw [headBlockSlots, Finset.mem_union,
    Finset.mem_singleton]
  push Not
  exact
    ⟨res.predecessorSlot_not_mem_headInternalSlots
        head tail hremaining,
      ne_of_lt
        (res.predecessorSlot_lt_outgoingSlot
          head tail hremaining)⟩

/-- Deleting one literal block removes exactly its internal and outgoing
edge slots from the active scale carrier. -/
theorem afterHead_activeEdgeSlots :
    (post res head tail hremaining).activeEdgeSlots =
      res.activeEdgeSlots \
        res.headBlockSlots head tail hremaining := by
  ext edge
  rw [Finset.mem_sdiff]
  constructor
  · intro hpost
    refine
      ⟨res.afterHead_activeEdgeSlots_subset
          head tail hremaining hpost, ?_⟩
    rw [headBlockSlots, Finset.mem_union,
      Finset.mem_singleton]
    push Not
    refine ⟨?_, ?_⟩
    · intro hinternal
      obtain ⟨j, _hj, heq⟩ :=
        Finset.mem_image.mp hinternal
      exact
        res.internalSlot_not_mem_afterHead_activeEdgeSlots
          head tail hremaining j (heq ▸ hpost)
    · intro heq
      exact
        res.outgoingSlot_not_mem_afterHead_activeEdgeSlots
          head tail hremaining (heq ▸ hpost)
  · rintro ⟨hold, hblock⟩
    have hinternal :
        edge ∉
          res.headInternalSlots head tail hremaining := by
      intro hmem
      apply hblock
      rw [headBlockSlots]
      exact Finset.mem_union_left _ hmem
    have hout :
        edge ≠
          (ctx res head tail hremaining).outgoingSlot := by
      intro heq
      apply hblock
      rw [headBlockSlots, heq]
      simp
    exact
      res.mem_afterHead_activeEdgeSlots_of_outer
        head tail hremaining edge hold hinternal hout

/-- Product of all numerical scales deleted with the head block. -/
def headBlockScaleProduct
    (scale : Fin (m + 1) → ℝ) : ℝ :=
  ∏ edge ∈ res.headBlockSlots head tail hremaining,
    scale edge

/-- The complete block budget is the analytic internal-edge product times
the outgoing free-Green scale. -/
theorem headBlockScaleProduct_eq_internal_mul_outgoing
    (scale : Fin (m + 1) → ℝ) :
    res.headBlockScaleProduct
        head tail hremaining scale =
      r324WithinHalfInternalEdgeScaleProduct
          (ctx res head tail hremaining) scale *
        scale (ctx res head tail hremaining).outgoingSlot := by
  unfold headBlockScaleProduct headBlockSlots
  rw [Finset.prod_union]
  · rw [res.prod_headInternalSlots
      head tail hremaining, Finset.prod_singleton]
    rfl
  · exact Finset.disjoint_singleton_right.mpr
      (by
        intro hmem
        obtain ⟨j, _hj, heq⟩ :=
          Finset.mem_image.mp hmem
        exact
          (ne_of_lt
            ((ctx res head tail hremaining).internalSlot_lt_outgoingSlot j))
            heq)

/-- Numerical update which absorbs every deleted block scale, including
the outgoing free-Green slot. -/
def budgetUpdatedEdgeScale
    (scale : Fin (m + 1) → ℝ)
    (C lam K : ℝ) :
    Fin (m + 1) → ℝ :=
  Function.update scale
    (r324WithinHalfPredecessorSlot res.state head)
    (scale (r324WithinHalfPredecessorSlot res.state head) *
      res.headBlockScaleProduct head tail hremaining scale *
      (C * lam) ^ (2 * residualBlockOrder head.2) * K)

@[simp]
theorem budgetUpdatedEdgeScale_predecessor
    (scale : Fin (m + 1) → ℝ)
    (C lam K : ℝ) :
    res.budgetUpdatedEdgeScale
        head tail hremaining scale C lam K
        (r324WithinHalfPredecessorSlot res.state head) =
      scale (r324WithinHalfPredecessorSlot res.state head) *
        res.headBlockScaleProduct
          head tail hremaining scale *
        (C * lam) ^ (2 * residualBlockOrder head.2) * K := by
  simp [budgetUpdatedEdgeScale]

theorem budgetUpdatedEdgeScale_of_ne
    (scale : Fin (m + 1) → ℝ)
    (C lam K : ℝ)
    (edge : Fin (m + 1))
    (hne :
      edge ≠
        r324WithinHalfPredecessorSlot res.state head) :
    res.budgetUpdatedEdgeScale
        head tail hremaining scale C lam K edge =
      scale edge := by
  simp [budgetUpdatedEdgeScale, hne]

/-- At the predecessor, the budget update is the analytic scale multiplied
by the one outgoing scale. -/
theorem
    budgetUpdatedEdgeScale_predecessor_eq_analytic_mul_outgoing
    (scale : Fin (m + 1) → ℝ)
    (C lam K : ℝ) :
    res.budgetUpdatedEdgeScale
        head tail hremaining scale C lam K
        (r324WithinHalfPredecessorSlot res.state head) =
      r324WithinHalfUpdatedEdgeScale
          (ctx res head tail hremaining)
          scale C lam K
          (r324WithinHalfPredecessorSlot res.state head) *
        scale (ctx res head tail hremaining).outgoingSlot := by
  rw [res.budgetUpdatedEdgeScale_predecessor
      head tail hremaining,
    res.headBlockScaleProduct_eq_internal_mul_outgoing
      head tail hremaining]
  change
    scale
          (r324WithinHalfPredecessorSlot
            (ctx res head tail hremaining).state
            (ctx res head tail hremaining).step) *
        (r324WithinHalfInternalEdgeScaleProduct
            (ctx res head tail hremaining) scale *
          scale (ctx res head tail hremaining).outgoingSlot) *
        (C * lam) ^
          (2 * residualBlockOrder
            (ctx res head tail hremaining).step.2) *
        K =
      r324WithinHalfUpdatedEdgeScale
          (ctx res head tail hremaining)
          scale C lam K
          (r324WithinHalfPredecessorSlot
            (ctx res head tail hremaining).state
            (ctx res head tail hremaining).step) *
        scale (ctx res head tail hremaining).outgoingSlot
  rw [r324WithinHalfUpdatedEdgeScale_predecessor]
  ring

/-- Exact active scale-product recurrence for one budget update. -/
theorem activeEdgeScaleProduct_budgetUpdate
    (scale : Fin (m + 1) → ℝ)
    (C lam K : ℝ) :
    (∏ edge ∈
        (post res head tail hremaining).activeEdgeSlots,
      res.budgetUpdatedEdgeScale
        head tail hremaining scale C lam K edge) =
      (∏ edge ∈ res.activeEdgeSlots, scale edge) *
        (C * lam) ^ (2 * residualBlockOrder head.2) * K := by
  let oldActive := res.activeEdgeSlots
  let block :=
    res.headBlockSlots head tail hremaining
  let newActive := oldActive \ block
  let pred :=
    r324WithinHalfPredecessorSlot res.state head
  have hpredNew : pred ∈ newActive := by
    exact Finset.mem_sdiff.mpr
      ⟨res.predecessorSlot_mem_activeEdgeSlots head,
        res.predecessorSlot_not_mem_headBlockSlots
          head tail hremaining⟩
  have hblock : block ⊆ oldActive :=
    res.headBlockSlots_subset_activeEdgeSlots
      head tail hremaining
  have hpartition :
      (∏ edge ∈ newActive, scale edge) *
          res.headBlockScaleProduct
            head tail hremaining scale =
        ∏ edge ∈ oldActive, scale edge := by
    simpa only [newActive, block, oldActive,
      headBlockScaleProduct, mul_comm] using
      (Finset.prod_sdiff hblock (f := scale))
  rw [res.afterHead_activeEdgeSlots
    head tail hremaining]
  change
    (∏ edge ∈ newActive,
      res.budgetUpdatedEdgeScale
        head tail hremaining scale C lam K edge) =
      (∏ edge ∈ oldActive, scale edge) *
        (C * lam) ^ (2 * residualBlockOrder head.2) * K
  simp only [budgetUpdatedEdgeScale]
  rw [Finset.prod_update_of_mem hpredNew]
  have hsplit :=
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
      hpredNew scale
  rw [← hpartition, hsplit]
  ring

end Head

end R324WithinHalfResidualPrefix

/-! ## Certificate enlargement -/

theorem R324WithinHalfEdgeCertificate.of_pointwise_scale_le
    {m : ℕ} {state : R324WithinHalfEdgeState m}
    {scale budget : Fin (m + 1) → ℝ}
    (hcert :
      R324WithinHalfEdgeCertificate state scale)
    (hle : ∀ edge, scale edge ≤ budget edge) :
    R324WithinHalfEdgeCertificate state budget := by
  refine
    ⟨fun edge =>
        lt_of_lt_of_le (hcert.scale_pos edge) (hle edge),
      hcert.measurable, hcert.memE, ?_⟩
  intro edge z hz
  exact
    (hcert.bound edge z hz).trans
      (mul_le_mul_of_nonneg_right
        (hle edge) (invSqKer_nonneg z))

/-! ## Uniform initial normalization -/

/-- A single scale at least one controls every all-Green initial state,
uniformly in the ambient perturbative order. -/
theorem
    exists_r324InitialWithinHalfEdgeCertificate_one_le_uniform :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ m : ℕ,
        R324WithinHalfEdgeCertificate
          (r324InitialWithinHalfEdgeState m)
          (fun _ => A) := by
  obtain ⟨A₀, hA₀, hgreen⟩ := greenFn_le
  let A : ℝ := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  have hA₀A : A₀ ≤ A := le_max_right _ _
  refine ⟨A, hA, ?_⟩
  intro m
  let initialCertificate :
      R324WithinHalfEdgeCertificate
        (r324InitialWithinHalfEdgeState m)
        (fun _ => A₀) :=
    { scale_pos := fun _ => hA₀
      measurable := by
        intro edge
        simpa [r324InitialWithinHalfEdgeState] using
          measurable_greenFn
      memE := by
        intro edge
        simpa [r324InitialWithinHalfEdgeState] using
          greenFn_memE
      bound := by
        intro edge z hz
        change |greenFn z| ≤ A₀ * invSqKer z
        exact greenFn_abs_le_mul_invSqKer hgreen z hz }
  apply
    R324WithinHalfEdgeCertificate.of_pointwise_scale_le
      initialCertificate
  intro _edge
  exact hA₀A

/-! ## Reachable budget histories -/

/-- Quantitative budget reachability follows the same literal schedule
heads as the analytic residual prefix. -/
inductive R324WithinHalfBudgetScaleReachable
    {m : ℕ} (pairing : PartialPairing (Fin m))
    (ρ : SmoothCutoff) (C lam ε K A : ℝ) :
    R324WithinHalfEdgeState m →
      (Fin (m + 1) → ℝ) → Prop
  | initial :
      R324WithinHalfBudgetScaleReachable
        pairing ρ C lam ε K A
        (r324InitialWithinHalfEdgeState m)
        (fun _ => A)
  | afterHead
      {scale : Fin (m + 1) → ℝ}
      (res :
        R324WithinHalfResidualPrefix ρ lam ε pairing)
      (head : R322ExtractionStep m)
      (tail : List (R322ExtractionStep m))
      (hremaining : res.remaining = head :: tail)
      (previous :
        R324WithinHalfBudgetScaleReachable
          pairing ρ C lam ε K A res.state scale) :
      R324WithinHalfBudgetScaleReachable
        pairing ρ C lam ε K A
        (res.afterHead head tail hremaining).state
        (res.budgetUpdatedEdgeScale
          head tail hremaining scale C lam K)

namespace R324WithinHalfBudgetScaleReachable

variable {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {state : R324WithinHalfEdgeState m}
    {scale : Fin (m + 1) → ℝ}

/-- Every future edge scale is still the initial Green budget. -/
theorem edgeScale_eq_base_of_processed_right_lt
    (hreach :
      R324WithinHalfBudgetScaleReachable
        pairing ρ C lam ε K A state scale)
    (edge : Fin (m + 1))
    (hfuture :
      ∀ earlier ∈ state.processed,
        earlier.1.2.val < edge.val) :
    scale edge = A := by
  induction hreach with
  | initial =>
      rfl
  | @afterHead oldScale res head tail
      hremaining previous ih =>
      have hcurrent :
          head.1.2.val < edge.val := by
        apply hfuture head
        change
          head ∈ res.state.processed ++ [head]
        simp
      have hprevious :
          ∀ earlier ∈ res.state.processed,
            earlier.1.2.val < edge.val := by
        intro earlier hearlier
        apply hfuture earlier
        change
          earlier ∈ res.state.processed ++ [head]
        simp [hearlier]
      have hleftRight :
          head.1.1.val ≤ head.1.2.val := by
        have haligned :=
          r322AnalyticSchedule_forall_aligned
            pairing head
            (res.headContext
              head tail hremaining).step_mem_schedule
        exact Fin.mk_le_mk.mp
          ((haligned.2.2 head.1.1 haligned.1).2)
      have hne :
          edge ≠
            r324WithinHalfPredecessorSlot
              res.state head := by
        intro heq
        have hp :=
          r324WithinHalfPredecessorSlot_val_le_step_left
            res.state head
        have hval := congrArg Fin.val heq
        omega
      rw [res.budgetUpdatedEdgeScale_of_ne
        head tail hremaining oldScale C lam K edge hne]
      exact ih hprevious

/-- The outgoing budget scale of the current literal head is exactly the
initial Green budget. -/
theorem outgoingScale_eq_base
    (hreach :
      R324WithinHalfBudgetScaleReachable
        pairing ρ C lam ε K A state scale)
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hstate : res.state = state)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail) :
    scale
        (res.headContext
          head tail hremaining).outgoingSlot =
      A := by
  subst state
  apply hreach.edgeScale_eq_base_of_processed_right_lt
  intro earlier hearlier
  have hp :=
    r322AnalyticSchedule_pairwise_right_lt pairing
  rw [res.schedule_eq, hremaining,
    List.pairwise_append] at hp
  have hright :
      earlier.1.2 < head.1.2 :=
    hp.2.2 earlier hearlier head (by simp)
  unfold R324WithinHalfStepContext.outgoingSlot
    r324InternalVertexEdgeSlot
  change earlier.1.2.val < head.1.2.val + 1
  omega

/-- The analytic one-block certificate promotes to the complete numerical
budget update once the unchanged outgoing Green scale is at least one. -/
theorem promote_afterHead_certificate
    (hreach :
      R324WithinHalfBudgetScaleReachable
        pairing ρ C lam ε K A state scale)
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hstate : res.state = state)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (hA : 1 ≤ A)
    (rawCertificate :
      R324WithinHalfEdgeCertificate
        (res.afterHead head tail hremaining).state
        (r324WithinHalfUpdatedEdgeScale
          (res.headContext head tail hremaining)
          scale C lam K)) :
    R324WithinHalfEdgeCertificate
      (res.afterHead head tail hremaining).state
      (res.budgetUpdatedEdgeScale
        head tail hremaining scale C lam K) := by
  apply
    R324WithinHalfEdgeCertificate.of_pointwise_scale_le
      rawCertificate
  intro edge
  by_cases hedge :
      edge =
        r324WithinHalfPredecessorSlot res.state head
  · subst edge
    rw [
      res.budgetUpdatedEdgeScale_predecessor_eq_analytic_mul_outgoing
        head tail hremaining]
    have hout :
        scale
            (res.headContext
              head tail hremaining).outgoingSlot =
          A :=
      hreach.outgoingScale_eq_base
        res hstate head tail hremaining
    rw [hout]
    simpa using
      (show
          r324WithinHalfUpdatedEdgeScale
              (res.headContext head tail hremaining)
              scale C lam K
              (r324WithinHalfPredecessorSlot res.state head) *
                1 ≤
            r324WithinHalfUpdatedEdgeScale
                (res.headContext head tail hremaining)
                scale C lam K
                (r324WithinHalfPredecessorSlot res.state head) *
              A from
        mul_le_mul_of_nonneg_left hA
          (rawCertificate.scale_pos
            (r324WithinHalfPredecessorSlot
              res.state head)).le)
  · rw [
      r324WithinHalfUpdatedEdgeScale_of_ne,
      res.budgetUpdatedEdgeScale_of_ne
        head tail hremaining scale C lam K edge hedge]
    exact hedge

end R324WithinHalfBudgetScaleReachable

/-! ## Exact active-product ledger -/

/-- Total perturbative order absorbed into a within-half edge state. -/
def r324WithinHalfProcessedOrder
    {m : ℕ} (state : R324WithinHalfEdgeState m) : ℕ :=
  (state.processed.map
    (fun step => residualBlockOrder step.2)).sum

/-- Every budget-reachable history satisfies the exact active-scale
product recurrence.  The initial active product is intentionally left
literal here; its uniform numerical absorption is a separate step. -/
theorem
    R324WithinHalfBudgetScaleReachable.activeEdgeScaleProduct_eq
    {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {state : R324WithinHalfEdgeState m}
    {scale : Fin (m + 1) → ℝ}
    (hreach :
      R324WithinHalfBudgetScaleReachable
        pairing ρ C lam ε K A state scale) :
    (∏ edge ∈
        ({0} ∪ state.active.image
          r324InternalVertexEdgeSlot),
      scale edge) =
      (∏ _edge ∈
          ({0} ∪
            (r324InitialWithinHalfEdgeState m).active.image
              r324InternalVertexEdgeSlot),
        A) *
        (C * lam) ^
          (2 * r324WithinHalfProcessedOrder state) *
        K ^ state.processed.length := by
  induction hreach with
  | initial =>
      simp [r324WithinHalfProcessedOrder,
        r324InitialWithinHalfEdgeState]
  | @afterHead oldScale res head tail
      hremaining previous ih =>
      have hstep :=
        res.activeEdgeScaleProduct_budgetUpdate
          head tail hremaining oldScale C lam K
      change
        (∏ edge ∈ res.activeEdgeSlots, oldScale edge) =
          _ at ih
      change
        (∏ edge ∈
            (res.afterHead
              head tail hremaining).activeEdgeSlots,
          res.budgetUpdatedEdgeScale
            head tail hremaining oldScale C lam K edge) =
          _
      rw [hstep]
      rw [ih]
      simp only [
        R324WithinHalfResidualPrefix.afterHead,
        R324WithinHalfStepContext.absorb,
        r324WithinHalfProcessedOrder,
        List.map_append, List.map_singleton,
        List.sum_append, List.sum_singleton,
        List.length_append, List.length_singleton]
      simp only [R324WithinHalfResidualPrefix.headContext]
      rw [show
          2 *
              ((res.state.processed.map
                (fun step =>
                  residualBlockOrder step.2)).sum +
                residualBlockOrder head.2) =
            2 *
                (res.state.processed.map
                  (fun step =>
                    residualBlockOrder step.2)).sum +
              2 * residualBlockOrder head.2 by omega,
        pow_add, pow_succ]
      ring

/-! ## Budget-certified local closure and literal suffix iteration -/

/-- A one-block provider for the complete numerical budget.  Besides the
actual local predecessor inequality, it transports both reachability and the
slotwise edge certificate to the literal suffix. -/
def R324WithinHalfBudgetLocalBlockProvider
    (ρ : SmoothCutoff) (C lam ε K A : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m)) : Prop :=
  ∀ (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (scale : Fin (m + 1) → ℝ),
    R324WithinHalfBudgetScaleReachable
        pairing ρ C lam ε K A res.state scale →
      R324WithinHalfEdgeCertificate res.state scale →
        (∀ x, x ≠ 0 →
          |(res.afterHead
              head tail hremaining).state.edges
              (r324WithinHalfPredecessorSlot
                res.state head) x| ≤
            res.budgetUpdatedEdgeScale
                head tail hremaining scale C lam K
                (r324WithinHalfPredecessorSlot
                  res.state head) *
              invSqKer x) ∧
          R324WithinHalfBudgetScaleReachable
            pairing ρ C lam ε K A
            (res.afterHead head tail hremaining).state
            (res.budgetUpdatedEdgeScale
              head tail hremaining scale C lam K) ∧
          R324WithinHalfEdgeCertificate
            (res.afterHead head tail hremaining).state
            (res.budgetUpdatedEdgeScale
              head tail hremaining scale C lam K)

/-- Proposition 4.1 supplies a genuine complete-budget provider at every
literal within-half head. -/
theorem exists_r324WithinHalf_budgetLocalBlockProvider
    {supportConstant : ℝ}
    (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ρ : SmoothCutoff) (C lam ε A : ℝ)
        (m : ℕ) (pairing : PartialPairing (Fin m)),
        1 ≤ A →
        0 < C → 0 < lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| →
        R324WithinHalfProp41Provider
          ρ C lam ε supportConstant pairing →
        R324WithinHalfBudgetLocalBlockProvider
          ρ C lam ε K A pairing := by
  obtain ⟨K, hK, hlocal⟩ :=
    exists_r324WithinHalf_localBlockClosure hsupport
  refine ⟨K, hK, ?_⟩
  intro ρ C lam ε A m pairing hA hC hlam hε hε1
    hlog hprop res head tail hremaining scale hreach hcert
  obtain ⟨_rawLocalBound, rawCertificate⟩ :=
    hlocal ρ C lam ε m pairing
      res head tail hremaining scale hcert
      hC hlam hε hε1 hlog
      (fun H hH =>
        hprop res head tail hremaining H hH)
  have budgetCertificate :
      R324WithinHalfEdgeCertificate
        (res.afterHead head tail hremaining).state
        (res.budgetUpdatedEdgeScale
          head tail hremaining scale C lam K) :=
    hreach.promote_afterHead_certificate
      res rfl head tail hremaining hA rawCertificate
  refine ⟨?_, ?_, budgetCertificate⟩
  · intro x hx
    exact
      budgetCertificate.bound
        (r324WithinHalfPredecessorSlot
          res.state head) x hx
  · exact
      R324WithinHalfBudgetScaleReachable.afterHead
        res head tail hremaining hreach

/-- Structural recursion through the literal remaining suffix reaches an
empty residual prefix while retaining the complete quantitative budget. -/
theorem exists_r324WithinHalf_terminalBudgetCertificate_of_provider
    {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (provider :
      R324WithinHalfBudgetLocalBlockProvider
        ρ C lam ε K A pairing)
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing)
    (scale : Fin (m + 1) → ℝ)
    (reachable :
      R324WithinHalfBudgetScaleReachable
        pairing ρ C lam ε K A res.state scale)
    (certificate :
      R324WithinHalfEdgeCertificate res.state scale) :
    ∃ (terminal :
        R324WithinHalfResidualPrefix ρ lam ε pairing)
      (terminalScale : Fin (m + 1) → ℝ),
      terminal.remaining = [] ∧
        terminal.state.processed =
          r322AnalyticSchedule pairing ∧
        R324WithinHalfBudgetScaleReachable
          pairing ρ C lam ε K A
          terminal.state terminalScale ∧
        R324WithinHalfEdgeCertificate
          terminal.state terminalScale := by
  cases hremaining : res.remaining with
  | nil =>
      refine
        ⟨res, scale, hremaining, ?_, reachable,
          certificate⟩
      have hschedule := res.schedule_eq
      rw [hremaining, List.append_nil] at hschedule
      exact hschedule.symm
  | cons head tail =>
      obtain ⟨_localBound, nextReachable,
          nextCertificate⟩ :=
        provider res head tail hremaining scale
          reachable certificate
      exact
        exists_r324WithinHalf_terminalBudgetCertificate_of_provider
          provider
          (res.afterHead head tail hremaining)
          (res.budgetUpdatedEdgeScale
            head tail hremaining scale C lam K)
          nextReachable nextCertificate
termination_by res.remaining.length
decreasing_by simp [hremaining]

/-- Uniform within-half terminal budget obtained by iterating the actual
Proposition 4.1 block estimate from the all-Green initial state.  Both
numerical constants are chosen before the order and pairing. -/
theorem exists_r324WithinHalf_uniformTerminalBudget_of_prop41
    {supportConstant : ℝ}
    (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∃ A : ℝ, 1 ≤ A ∧
        ∀ (ρ : SmoothCutoff) (C lam ε : ℝ)
          (m : ℕ) (pairing : PartialPairing (Fin m)),
          0 < C → 0 < lam → 0 < ε → ε ≤ 1 →
          1 ≤ |Real.log ε| →
          R324WithinHalfProp41Provider
            ρ C lam ε supportConstant pairing →
          ∃ (terminal :
              R324WithinHalfResidualPrefix
                ρ lam ε pairing)
            (terminalScale : Fin (m + 1) → ℝ),
            terminal.remaining = [] ∧
              terminal.state.processed =
                r322AnalyticSchedule pairing ∧
              R324WithinHalfBudgetScaleReachable
                pairing ρ C lam ε K A
                terminal.state terminalScale ∧
              R324WithinHalfEdgeCertificate
                terminal.state terminalScale := by
  obtain ⟨K, hK, hprovider⟩ :=
    exists_r324WithinHalf_budgetLocalBlockProvider hsupport
  obtain ⟨A, hA, hinitial⟩ :=
    exists_r324InitialWithinHalfEdgeCertificate_one_le_uniform
  refine ⟨K, hK, A, hA, ?_⟩
  intro ρ C lam ε m pairing hC hlam hε hε1 hlog hprop
  let initial :
      R324WithinHalfResidualPrefix ρ lam ε pairing :=
    R324WithinHalfResidualPrefix.initial
      ρ lam ε pairing
  exact
    exists_r324WithinHalf_terminalBudgetCertificate_of_provider
      (hprovider ρ C lam ε A m pairing hA hC hlam
        hε hε1 hlog hprop)
      initial (fun _ => A)
      R324WithinHalfBudgetScaleReachable.initial
      (hinitial m)

end

end Anderson4D
