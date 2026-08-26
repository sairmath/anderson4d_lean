import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfResidualCoordinates

/-!
# Complete surviving integrand of one R-324 within-half prefix

This module names the full sparse-chain integrand which survives a genuine
processed prefix.  Its coordinate carrier is the one proved
measure-preserving in `R324WithinHalfResidualCoordinates`.

The three factors are kept separate:

* ordinary heterogeneous edges on the sparse active chain;
* the signed outgoing-edge differences of every remaining schedule step;
* one complete primitive-pairing sum for every remaining block.

This is pre-collapse data.  No original unintegrated integrand is equated
with a post-collapse edge state.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfStepContext

variable {m : ℕ} {pairing : PartialPairing (Fin m)}
    (ctx : R324WithinHalfStepContext pairing)

/-- The first standard coordinate of a current within-half block is its
certified left endpoint. -/
theorem blockOrderIso_zero :
    (ctx.blockOrderIso
      ⟨0, by
        have hn := ctx.one_le_blockOrder
        omega⟩).1 =
      ctx.step.1.1 := by
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      pairing ctx.step ctx.step_mem_schedule
  let leftInBlock : ctx.step.2 :=
    ⟨ctx.step.1.1, haligned.1⟩
  obtain ⟨j, hj⟩ :=
    ctx.blockOrderIso.surjective leftInBlock
  have hzeroLe :
      (⟨0, by
        have hn := ctx.one_le_blockOrder
        omega⟩ :
        Fin (2 * residualBlockOrder ctx.step.2)) ≤ j :=
    by
      change 0 ≤ j.val
      omega
  have hfirstLe :
      (ctx.blockOrderIso
        ⟨0, by
          have hn := ctx.one_le_blockOrder
          omega⟩).1 ≤
        ctx.step.1.1 := by
    have hmono :=
      ctx.blockOrderIso.monotone hzeroLe
    rw [hj] at hmono
    exact hmono
  have hleftLe :
      ctx.step.1.1 ≤
        (ctx.blockOrderIso
          ⟨0, by
            have hn := ctx.one_le_blockOrder
            omega⟩).1 :=
    (haligned.2.2 _
      (ctx.blockOrderIso
        ⟨0, by
          have hn := ctx.one_le_blockOrder
          omega⟩).2).1
  exact le_antisymm hfirstLe hleftLe

/-- The last standard coordinate of a current within-half block is its
certified right endpoint. -/
theorem blockOrderIso_last :
    (ctx.blockOrderIso
      (primitiveLast
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder)).1 =
      ctx.step.1.2 := by
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      pairing ctx.step ctx.step_mem_schedule
  let rightInBlock : ctx.step.2 :=
    ⟨ctx.step.1.2, haligned.2.1⟩
  obtain ⟨j, hj⟩ :=
    ctx.blockOrderIso.surjective rightInBlock
  have hjlast :
      j ≤
        primitiveLast
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder := by
    change j.val ≤
      2 * residualBlockOrder ctx.step.2 - 1
    have hjlt := j.isLt
    omega
  have hrightLe :
      ctx.step.1.2 ≤
        (ctx.blockOrderIso
          (primitiveLast
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder)).1 := by
    have hmono :=
      ctx.blockOrderIso.monotone hjlast
    rw [hj] at hmono
    exact hmono
  have hlastLe :
      (ctx.blockOrderIso
        (primitiveLast
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder)).1 ≤
        ctx.step.1.2 :=
    (haligned.2.2 _
      (ctx.blockOrderIso
        (primitiveLast
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder)).2).2
  exact le_antisymm hlastLe hrightLe

/-- Every genuine internal standard edge precedes the outgoing slot of its
block. -/
theorem internalSlot_lt_outgoingSlot
    (j : Fin (2 * residualBlockOrder ctx.step.2 - 1)) :
    ctx.internalSlot j < ctx.outgoingSlot := by
  let j0 :
      Fin (2 * residualBlockOrder ctx.step.2) :=
    ⟨j.val, by
      have hj := j.isLt
      have hn := ctx.one_le_blockOrder
      omega⟩
  have hjlast :
      j0 <
        primitiveLast
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder := by
    change j.val <
      2 * residualBlockOrder ctx.step.2 - 1
    exact j.isLt
  have hmono :=
    ctx.blockOrderIso.strictMono hjlast
  change
    (ctx.blockOrderIso j0).1 <
      (ctx.blockOrderIso
        (primitiveLast
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder)).1 at hmono
  rw [ctx.blockOrderIso_last] at hmono
  unfold internalSlot outgoingSlot
  change
    (ctx.blockOrderIso j0).1.val + 1 <
      ctx.step.1.2.val + 1
  exact Nat.add_lt_add_right hmono 1

/-- Translating all local coordinates and the predecessor point by one
common torus point gives an explicit absolute-coordinate form of the raw
local integrand. -/
theorem rawLocalIntegrand_translated
    (ρ : SmoothCutoff) (ε : ℝ)
    (u a : T4)
    (t :
      Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ctx.rawLocalIntegrand ρ ε (u - a)
        (fun j => t j - a) =
      ctx.state.edges
          (r324WithinHalfPredecessorSlot
            ctx.state ctx.step)
          (u - t ⟨0, by
            have hn := ctx.one_le_blockOrder
            omega⟩) *
        primitiveChainProduct
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder ctx.internalEdges t *
        (ctx.state.edges ctx.outgoingSlot
            (t (primitiveLast
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder) - a) -
          ctx.state.edges ctx.outgoingSlot
            (t ⟨0, by
              have hn := ctx.one_le_blockOrder
              omega⟩ - a)) *
        ∑ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder ctx.step.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder ctx.step.2)},
          primitiveCovarianceProduct ρ ε
            (residualBlockOrder ctx.step.2) κB.1 t := by
  have hchain :
      primitiveChainProduct
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder ctx.internalEdges
          (fun j => t j - a) =
        primitiveChainProduct
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder ctx.internalEdges t := by
    unfold primitiveChainProduct
    apply Finset.prod_congr rfl
    intro j _hj
    apply congrArg (ctx.internalEdges j)
    change
      (t (primitiveEdgeLeft
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder j) - a) -
          (t (primitiveEdgeRight
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder j) - a) =
        t (primitiveEdgeLeft
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder j) -
          t (primitiveEdgeRight
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder j)
    abel
  have hcov :
      (∑ κB :
          {κ : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κ ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)},
        primitiveCovarianceProduct ρ ε
          (residualBlockOrder ctx.step.2) κB.1
          (fun j => t j - a)) =
        ∑ κB :
          {κ : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κ ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)},
        primitiveCovarianceProduct ρ ε
          (residualBlockOrder ctx.step.2) κB.1 t := by
    apply Finset.sum_congr rfl
    intro κB _hκB
    unfold primitiveCovarianceProduct
    apply Finset.prod_congr rfl
    intro i _hi
    apply congrArg (ρ.etaEpsT4 ε)
    change
      (t i - a) - (t (κB.1 i) - a) =
        t i - t (κB.1 i)
    abel
  have hincoming :
      (u - a) -
          (t ⟨0, by
            have hn := ctx.one_le_blockOrder
            omega⟩ - a) =
        u - t ⟨0, by
          have hn := ctx.one_le_blockOrder
          omega⟩ := by
    abel
  unfold rawLocalIntegrand
  rw [hchain, hcov, hincoming]

end R324WithinHalfStepContext

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res :
      R324WithinHalfResidualPrefix
        ρ lam ε pairing)

/-! ## Sparse production-chain geometry -/

/-- Edge slots whose left endpoint survives in the current production
chain.  Slot zero is the incoming external edge. -/
def activeEdgeSlots : Finset (Fin (m + 1)) :=
  {0} ∪ res.state.active.image r324InternalVertexEdgeSlot

@[simp]
theorem zero_mem_activeEdgeSlots :
    (0 : Fin (m + 1)) ∈ res.activeEdgeSlots := by
  simp [activeEdgeSlots]

theorem internalVertexEdgeSlot_mem_activeEdgeSlots
    (i : Fin m) (hi : i ∈ res.state.active) :
    r324InternalVertexEdgeSlot i ∈
      res.activeEdgeSlots := by
  rw [activeEdgeSlots]
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

/-- Active internal vertices strictly to the right of one production edge
slot, shifted into the `(m+2)` chain carrier.  The terminal external vertex
is always adjoined as a candidate. -/
def edgeSuccessorCandidates
    (edge : Fin (m + 1)) :
    Finset (Fin (m + 2)) :=
  {Fin.last (m + 1)} ∪
    (res.state.active.filter fun i =>
      edge.val < (varIdx i).val).image varIdx

theorem edgeSuccessorCandidates_nonempty
    (edge : Fin (m + 1)) :
    (res.edgeSuccessorCandidates edge).Nonempty := by
  refine ⟨Fin.last (m + 1), ?_⟩
  simp [edgeSuccessorCandidates]

/-- Least surviving production-chain vertex strictly after an edge slot. -/
def edgeSuccessor
    (edge : Fin (m + 1)) :
    Fin (m + 2) :=
  (res.edgeSuccessorCandidates edge).min'
    (res.edgeSuccessorCandidates_nonempty edge)

theorem edgeSuccessor_mem_candidates
    (edge : Fin (m + 1)) :
    res.edgeSuccessor edge ∈
      res.edgeSuccessorCandidates edge :=
  Finset.min'_mem _ _

theorem edge_lt_edgeSuccessor
    (edge : Fin (m + 1)) :
    edge.castSucc < res.edgeSuccessor edge := by
  have hmem := res.edgeSuccessor_mem_candidates edge
  rw [edgeSuccessorCandidates] at hmem
  rcases Finset.mem_union.mp hmem with hlast | hinter
  · have heq :
        res.edgeSuccessor edge =
          Fin.last (m + 1) := by
      simpa using hlast
    rw [heq]
    change edge.val < m + 1
    exact edge.isLt
  · obtain ⟨i, hi, heq⟩ :=
      Finset.mem_image.mp hinter
    have hlt := (Finset.mem_filter.mp hi).2
    rw [heq] at hlt
    exact hlt

/-- The spatial difference read by one current heterogeneous edge. -/
def edgeDisplacement
    (x y : T4) (v : Fin m → T4)
    (edge : Fin (m + 1)) : T4 :=
  assemble x y v edge.castSucc -
    assemble x y v (res.edgeSuccessor edge)

/-- Outgoing production slots reserved for the signed differences of the
analytic suffix. -/
def remainingOutgoingSlots : List (Fin (m + 1)) :=
  res.remaining.map fun step =>
    r324InternalVertexEdgeSlot step.1.2

/-- One ordinary sparse-chain factor.  Deleted left vertices and outgoing
slots reserved for remaining signed differences contribute one. -/
def residualChainEdgeFactor
    (x y : T4) (v : Fin m → T4)
    (edge : Fin (m + 1)) : ℝ :=
  if edge ∈ res.activeEdgeSlots then
    if edge ∈ res.remainingOutgoingSlots then
      1
    else
      res.state.edges edge
        (res.edgeDisplacement x y v edge)
  else 1

/-- Product of all ordinary sparse-chain factors. -/
def residualChainProduct
    (x y : T4) (v : Fin m → T4) : ℝ :=
  ∏ edge : Fin (m + 1),
    res.residualChainEdgeFactor x y v edge

/-- Signed outgoing-edge difference belonging to one remaining schedule
step, read against its actual sparse successor. -/
def residualStepDifference
    (x y : T4) (v : Fin m → T4)
    (step : R322ExtractionStep m) : ℝ :=
  let edge :=
    r324InternalVertexEdgeSlot step.1.2
  res.state.edges edge
      (assemble x y v (varIdx step.1.2) -
        assemble x y v (res.edgeSuccessor edge)) -
    res.state.edges edge
      (assemble x y v (varIdx step.1.1) -
        assemble x y v (res.edgeSuccessor edge))

/-- Product of all signed differences in the literal remaining schedule. -/
def residualDifferenceProduct
    (x y : T4) (v : Fin m → T4) : ℝ :=
  (res.remaining.map
    (res.residualStepDifference x y v)).prod

/-! ## Remaining primitive coordinates -/

/-- A remaining schedule block is a genuine extraction block of the frozen
within-half pairing. -/
def remainingBlockIndex
    (j : Fin res.remaining.length) :
    ExtractionBlockIndex pairing := by
  let step := res.remaining.get j
  refine ⟨step.2, ?_⟩
  apply
    (r322AnalyticSchedule_blocks_perm_extractionBlocks
      pairing).mem_iff.mp
  exact
    List.mem_map.mpr
      ⟨step,
        by
          rw [res.schedule_eq]
          exact List.mem_append_right _
            (res.remaining.get_mem j),
        rfl⟩

/-- Complete primitive covariance sum on every remaining block. -/
def residualPrimitiveProduct
    (ρ : SmoothCutoff) (ε : ℝ)
    (v : Fin m → T4) : ℝ :=
  ∏ j : Fin res.remaining.length,
    r322ExtractionBlockPrimitiveSum ρ ε
      pairing (res.remainingBlockIndex j) v

/-- The complete pre-collapse residual integrand on the sparse within-half
carrier. -/
def residualIntegrand
    (ρ : SmoothCutoff) (ε : ℝ)
    (x y : T4) (v : Fin m → T4) : ℝ :=
  res.residualChainProduct x y v *
    res.residualDifferenceProduct x y v *
    res.residualPrimitiveProduct ρ ε v

/-- Complete scalar residual value, with only genuinely surviving internal
coordinates integrated. -/
def residualValue
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (x y : T4) : ℝ :=
  lamEps lam ε ^ (2 * res.remainingOrder) *
    ∫ v : res.SurvivingCoordinate → T4,
      res.residualIntegrand ρ ε x y
        (res.reconstruct v)
      ∂Measure.pi fun _ => paperMeasure

/-! ## Literal head bookkeeping -/

section Head

variable
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)

include tail hremaining

/-- The literal head has positive primitive order, stated without exposing
the reducible `headContext.step` field. -/
theorem head_one_le_blockOrder :
    1 ≤ residualBlockOrder head.2 := by
  change
    1 ≤ residualBlockOrder
      (res.headContext
        head tail hremaining).step.2
  exact
    (res.headContext
      head tail hremaining).one_le_blockOrder

theorem head_right_lt_tail_right
    (later : R322ExtractionStep m)
    (hlater : later ∈ tail) :
    head.1.2 < later.1.2 := by
  have hp :=
    r322AnalyticSchedule_pairwise_right_lt pairing
  rw [res.schedule_eq, hremaining,
    List.pairwise_append] at hp
  exact
    (List.pairwise_cons.mp hp.2.1).1
      later hlater

omit tail hremaining in
theorem predecessorSlot_val_le_left :
    (r324WithinHalfPredecessorSlot
        res.state head).val ≤
      head.1.1.val := by
  have hp :=
    r324WithinHalfPredecessorSlot_mem
      res.state head
  rw [r324WithinHalfPredecessorCandidates] at hp
  rcases Finset.mem_union.mp hp with hzero | hinter
  · have heq :
        r324WithinHalfPredecessorSlot
            res.state head =
          0 := by
      simpa using hzero
    rw [heq]
    exact Nat.zero_le _
  · obtain ⟨i, hi, heq⟩ :=
      Finset.mem_image.mp hinter
    have hlt := (Finset.mem_filter.mp hi).2
    have hval := congrArg Fin.val heq
    simp only [r324InternalVertexEdgeSlot] at hval
    change i.val < head.1.1.val at hlt
    omega

theorem predecessorSlot_lt_outgoingSlot :
    r324WithinHalfPredecessorSlot res.state head <
      r324InternalVertexEdgeSlot head.1.2 := by
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      pairing head
      (by
        rw [res.schedule_eq, hremaining]
        simp)
  have hlr := (haligned.2.2 head.1.1 haligned.1).2
  have hp :=
    res.predecessorSlot_val_le_left
      head
  change
    (r324WithinHalfPredecessorSlot
      res.state head).val <
      head.1.2.val + 1
  change head.1.1.val ≤ head.1.2.val at hlr
  omega

omit tail hremaining in
theorem predecessorSlot_mem_activeEdgeSlots :
    r324WithinHalfPredecessorSlot res.state head ∈
      res.activeEdgeSlots := by
  have hp :=
    r324WithinHalfPredecessorSlot_mem
      res.state head
  rw [r324WithinHalfPredecessorCandidates] at hp
  rcases Finset.mem_union.mp hp with hzero | hinter
  · have heq :
        r324WithinHalfPredecessorSlot
            res.state head =
          0 := by
      simpa using hzero
    rw [heq]
    exact res.zero_mem_activeEdgeSlots
  · obtain ⟨i, hi, heq⟩ :=
      Finset.mem_image.mp hinter
    rw [← heq]
    exact
      res.internalVertexEdgeSlot_mem_activeEdgeSlots
        i (Finset.mem_filter.mp hi).1

theorem predecessorSlot_not_mem_remainingOutgoingSlots :
    r324WithinHalfPredecessorSlot res.state head ∉
      res.remainingOutgoingSlots := by
  intro hmem
  unfold remainingOutgoingSlots at hmem
  rw [hremaining] at hmem
  simp only [List.map_cons, List.mem_cons] at hmem
  rcases hmem with hhead | htail
  · exact
      (ne_of_lt
        (res.predecessorSlot_lt_outgoingSlot
          head tail hremaining)) hhead
  · obtain ⟨later, hlater, heq⟩ :=
      List.mem_map.mp htail
    have hright :=
      res.head_right_lt_tail_right
        head tail hremaining later hlater
    have hp :=
      res.predecessorSlot_val_le_left
        head
    have haligned :=
      r322AnalyticSchedule_forall_aligned
        pairing head
        (by
          rw [res.schedule_eq, hremaining]
          simp)
    have hlr := (haligned.2.2 head.1.1 haligned.1).2
    have hval := congrArg Fin.val heq
    simp only [r324InternalVertexEdgeSlot] at hval
    change head.1.1.val ≤ head.1.2.val at hlr
    change head.1.2.val < later.1.2.val at hright
    omega

/-- The sparse successor of the current predecessor slot is the first
standard vertex of the current block. -/
theorem edgeSuccessor_predecessorSlot :
    res.edgeSuccessor
        (r324WithinHalfPredecessorSlot
          res.state head) =
      varIdx head.1.1 := by
  let pred :=
    r324WithinHalfPredecessorSlot
      res.state head
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      pairing head
      (by
        rw [res.schedule_eq, hremaining]
        simp)
  have hleftActive :
      head.1.1 ∈ res.state.active :=
    res.head_block_subset_active
      head tail hremaining haligned.1
  unfold edgeSuccessor
  rw [Finset.min'_eq_iff]
  constructor
  · rw [edgeSuccessorCandidates]
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine
      ⟨head.1.1,
        Finset.mem_filter.mpr
          ⟨hleftActive, ?_⟩,
        rfl⟩
    have hp :=
      res.predecessorSlot_val_le_left head
    change pred.val < head.1.1.val + 1
    omega
  · intro candidate hcand
    rw [edgeSuccessorCandidates] at hcand
    rcases Finset.mem_union.mp hcand with
        hlast | hinter
    · have heq :
          candidate = Fin.last (m + 1) := by
        simpa using hlast
      rw [heq]
      exact Fin.le_last _
    · obtain ⟨i, hi, heq⟩ :=
        Finset.mem_image.mp hinter
      rw [← heq]
      have hiActive := (Finset.mem_filter.mp hi).1
      have hpredLt := (Finset.mem_filter.mp hi).2
      have hleftLe : head.1.1 ≤ i := by
        by_contra hnot
        have hiLeft : i < head.1.1 :=
          lt_of_not_ge hnot
        have hicandidate :
            r324InternalVertexEdgeSlot i ∈
              r324WithinHalfPredecessorCandidates
                res.state head := by
          rw [r324WithinHalfPredecessorCandidates]
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr
            ⟨i,
              Finset.mem_filter.mpr
                ⟨hiActive, hiLeft⟩,
              rfl⟩
        have hle :=
          r324WithinHalfCandidate_le_predecessorSlot
            res.state head
            (r324InternalVertexEdgeSlot i)
            hicandidate
        unfold r324InternalVertexEdgeSlot at hle
        simp only [varIdx_val] at hpredLt
        change pred.val < i.val + 1 at hpredLt
        exact (not_lt_of_ge hle) hpredLt
      change head.1.1.val + 1 ≤ i.val + 1
      omega

theorem internalSlot_mem_activeEdgeSlots
    (j : Fin (2 * residualBlockOrder head.2 - 1)) :
    (res.headContext
        head tail hremaining).internalSlot j ∈
      res.activeEdgeSlots := by
  unfold R324WithinHalfStepContext.internalSlot
  apply res.internalVertexEdgeSlot_mem_activeEdgeSlots
  apply res.head_block_subset_active
    head tail hremaining
  exact
    (res.headContext
      head tail hremaining).blockOrderIso
      ⟨j.val, by
        change
          j.val <
            2 * residualBlockOrder head.2
        have hj := j.isLt
        omega⟩ |>.2

theorem internalSlot_not_mem_remainingOutgoingSlots
    (j : Fin (2 * residualBlockOrder head.2 - 1)) :
    (res.headContext
        head tail hremaining).internalSlot j ∉
      res.remainingOutgoingSlots := by
  intro hmem
  unfold remainingOutgoingSlots at hmem
  rw [hremaining] at hmem
  simp only [List.map_cons, List.mem_cons] at hmem
  rcases hmem with hhead | htail
  · exact
      (ne_of_lt
        ((res.headContext
          head tail hremaining).internalSlot_lt_outgoingSlot j))
        hhead
  · obtain ⟨later, hlater, heq⟩ :=
      List.mem_map.mp htail
    have hinternal :=
      (res.headContext
        head tail hremaining).internalSlot_lt_outgoingSlot j
    have hright :=
      res.head_right_lt_tail_right
        head tail hremaining later hlater
    have hval := congrArg Fin.val heq
    change
      ((res.headContext
        head tail hremaining).internalSlot j).val <
        head.1.2.val + 1 at hinternal
    simp only [r324InternalVertexEdgeSlot] at hval
    change head.1.2.val < later.1.2.val at hright
    omega

/-- On an internal standard edge of the current block, the sparse
production successor is the next standard block coordinate. -/
theorem edgeSuccessor_internalSlot
    (j : Fin (2 * residualBlockOrder head.2 - 1)) :
    let jnext :
        Fin (2 * residualBlockOrder head.2) :=
      ⟨j.val + 1, by
        have hj := j.isLt
        omega⟩
    res.edgeSuccessor
        ((res.headContext
          head tail hremaining).internalSlot j) =
      varIdx
        ((res.headContext
          head tail hremaining).blockOrderIso jnext).1 := by
  dsimp only
  let ctx :=
    res.headContext head tail hremaining
  let jleft :
      Fin (2 * residualBlockOrder head.2) :=
    ⟨j.val, by
      have hj := j.isLt
      have hn := ctx.one_le_blockOrder
      omega⟩
  let jnext :
      Fin (2 * residualBlockOrder head.2) :=
    ⟨j.val + 1, by
      have hj := j.isLt
      have hn := ctx.one_le_blockOrder
      omega⟩
  have hjlt : jleft < jnext := by
    change j.val < j.val + 1
    omega
  have hcoordlt :
      (ctx.blockOrderIso jleft).1 <
        (ctx.blockOrderIso jnext).1 :=
    ctx.blockOrderIso.strictMono hjlt
  have hblock :
      head.2 =
        res.state.active ∩
          Finset.Icc head.1.1 head.1.2 := by
    simpa [R324WithinHalfEdgeState.active] using
      r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
        pairing res.state.processed tail head
        ctx.schedule_eq
  unfold edgeSuccessor
  rw [Finset.min'_eq_iff]
  constructor
  · rw [edgeSuccessorCandidates]
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine
      ⟨(ctx.blockOrderIso jnext).1,
        Finset.mem_filter.mpr ⟨
          res.head_block_subset_active
            head tail hremaining
            (ctx.blockOrderIso jnext).2, ?_⟩,
        rfl⟩
    unfold R324WithinHalfStepContext.internalSlot
      r324InternalVertexEdgeSlot
    simp only [varIdx_val]
    change
      (ctx.blockOrderIso jleft).1.val + 1 <
        (ctx.blockOrderIso jnext).1.val + 1
    omega
  · intro candidate hcand
    rw [edgeSuccessorCandidates] at hcand
    rcases Finset.mem_union.mp hcand with
        hlast | hinter
    · have heq :
          candidate = Fin.last (m + 1) := by
        simpa using hlast
      rw [heq]
      exact Fin.le_last _
    · obtain ⟨i, hi, heq⟩ :=
        Finset.mem_image.mp hinter
      rw [← heq]
      have hiActive := (Finset.mem_filter.mp hi).1
      have hedgeLt := (Finset.mem_filter.mp hi).2
      have hleftLt :
          (ctx.blockOrderIso jleft).1 < i := by
        unfold R324WithinHalfStepContext.internalSlot
          r324InternalVertexEdgeSlot at hedgeLt
        simp only [varIdx_val] at hedgeLt
        change
          (ctx.blockOrderIso jleft).1.val + 1 <
            i.val + 1 at hedgeLt
        exact Nat.lt_of_add_lt_add_right hedgeLt
      by_cases hiright : i ≤ head.1.2
      · have hleftLe : head.1.1 ≤ i :=
          (ctx.blockOrderIso jleft).2
            |> (fun hmem =>
              (r322AnalyticSchedule_forall_aligned
                pairing head ctx.step_mem_schedule).2.2
                  (ctx.blockOrderIso jleft).1 hmem)
            |>.1
            |>.trans hleftLt.le
        have hiBlock : i ∈ head.2 := by
          rw [hblock]
          exact Finset.mem_inter.mpr
            ⟨hiActive,
              Finset.mem_Icc.mpr
                ⟨hleftLe, hiright⟩⟩
        let ji :=
          ctx.blockOrderIso.symm ⟨i, hiBlock⟩
        have hjleft_lt_ji : jleft < ji := by
          apply ctx.blockOrderIso.lt_iff_lt.mp
          rw [ctx.blockOrderIso.apply_symm_apply
            ⟨i, hiBlock⟩]
          exact hleftLt
        have hjnext_le_ji : jnext ≤ ji := by
          change j.val + 1 ≤ ji.val
          change j.val < ji.val at hjleft_lt_ji
          omega
        have hmono :=
          ctx.blockOrderIso.monotone hjnext_le_ji
        rw [ctx.blockOrderIso.apply_symm_apply
          ⟨i, hiBlock⟩] at hmono
        change
          (ctx.blockOrderIso jnext).1.val + 1 ≤
            i.val + 1
        exact Nat.add_le_add_right hmono 1
      · have hrightLt : head.1.2 < i :=
          lt_of_not_ge hiright
        have hnextLeRight :
            (ctx.blockOrderIso jnext).1 ≤
              head.1.2 :=
          (r322AnalyticSchedule_forall_aligned
            pairing head ctx.step_mem_schedule).2.2
              (ctx.blockOrderIso jnext).1
              (ctx.blockOrderIso jnext).2 |>.2
        change
          (ctx.blockOrderIso jnext).1.val + 1 ≤
            i.val + 1
        exact
          Nat.add_le_add_right
            (hnextLeRight.trans hrightLt.le) 1

theorem outgoingSlot_mem_activeEdgeSlots :
    (res.headContext
        head tail hremaining).outgoingSlot ∈
      res.activeEdgeSlots := by
  unfold R324WithinHalfStepContext.outgoingSlot
  apply res.internalVertexEdgeSlot_mem_activeEdgeSlots
  apply res.head_block_subset_active
    head tail hremaining
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      pairing head
      (by
        rw [res.schedule_eq, hremaining]
        simp)
  exact haligned.2.1

theorem outgoingSlot_mem_remainingOutgoingSlots :
    (res.headContext
        head tail hremaining).outgoingSlot ∈
      res.remainingOutgoingSlots := by
  unfold remainingOutgoingSlots
  rw [hremaining]
  simp only [List.map_cons, List.mem_cons]
  left
  rfl

@[simp]
theorem residualChainEdgeFactor_predecessor
    (x y : T4) (v : Fin m → T4) :
    res.residualChainEdgeFactor x y v
        (r324WithinHalfPredecessorSlot
          res.state head) =
      res.state.edges
        (r324WithinHalfPredecessorSlot
          res.state head)
        (res.edgeDisplacement x y v
          (r324WithinHalfPredecessorSlot
            res.state head)) := by
  unfold residualChainEdgeFactor
  rw [if_pos
      (res.predecessorSlot_mem_activeEdgeSlots head),
    if_neg
      (res.predecessorSlot_not_mem_remainingOutgoingSlots
        head tail hremaining)]

@[simp]
theorem residualChainEdgeFactor_internal
    (x y : T4) (v : Fin m → T4)
    (j : Fin (2 * residualBlockOrder head.2 - 1)) :
    res.residualChainEdgeFactor x y v
        ((res.headContext
          head tail hremaining).internalSlot j) =
      res.state.edges
        ((res.headContext
          head tail hremaining).internalSlot j)
        (res.edgeDisplacement x y v
          ((res.headContext
            head tail hremaining).internalSlot j)) := by
  unfold residualChainEdgeFactor
  rw [if_pos
      (res.internalSlot_mem_activeEdgeSlots
        head tail hremaining j),
    if_neg
      (res.internalSlot_not_mem_remainingOutgoingSlots
        head tail hremaining j)]

@[simp]
theorem residualChainEdgeFactor_outgoing
    (x y : T4) (v : Fin m → T4) :
    res.residualChainEdgeFactor x y v
        (res.headContext
          head tail hremaining).outgoingSlot =
      1 := by
  unfold residualChainEdgeFactor
  rw [if_pos
      (res.outgoingSlot_mem_activeEdgeSlots
        head tail hremaining),
    if_pos
      (res.outgoingSlot_mem_remainingOutgoingSlots
        head tail hremaining)]

/-- Product of the ordinary sparse edges internal to the current block. -/
def headInternalChainProduct
    (x y : T4) (v : Fin m → T4) : ℝ :=
  ∏ j : Fin (2 * residualBlockOrder head.2 - 1),
    res.residualChainEdgeFactor x y v
      ((res.headContext
        head tail hremaining).internalSlot j)

@[simp]
theorem residualChainEdgeFactor_internal_split
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4)
    (j : Fin (2 * residualBlockOrder head.2 - 1)) :
    res.residualChainEdgeFactor x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v)))
        ((res.headContext
          head tail hremaining).internalSlot j) =
      (res.headContext
        head tail hremaining).internalEdges j
        (t
            ⟨j.val, by
              have hj := j.isLt
              omega⟩ -
          t
            ⟨j.val + 1, by
              have hj := j.isLt
              omega⟩) := by
  rw [res.residualChainEdgeFactor_internal
    head tail hremaining]
  unfold R324WithinHalfStepContext.internalEdges
    edgeDisplacement
  rw [res.edgeSuccessor_internalSlot
    head tail hremaining j]
  let ctx :=
    res.headContext head tail hremaining
  let jleft :
      Fin (2 * residualBlockOrder head.2) :=
    ⟨j.val, by
      have hj := j.isLt
      omega⟩
  let jnext :
      Fin (2 * residualBlockOrder head.2) :=
    ⟨j.val + 1, by
      have hj := j.isLt
      omega⟩
  have hslot :
      (ctx.internalSlot j).castSucc =
        varIdx (ctx.blockOrderIso jleft).1 := by
    apply Fin.ext
    rfl
  rw [hslot, assemble_varIdx, assemble_varIdx]
  rw [res.reconstruct_split_symm_block
      head tail hremaining t v jleft,
    res.reconstruct_split_symm_block
      head tail hremaining t v jnext]
  rfl

@[simp]
theorem headInternalChainProduct_split
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    res.headInternalChainProduct
        head tail hremaining x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))) =
      primitiveChainProduct
        (residualBlockOrder head.2)
        (res.headContext
          head tail hremaining).one_le_blockOrder
        (res.headContext
          head tail hremaining).internalEdges t := by
  unfold headInternalChainProduct
    primitiveChainProduct
  apply Finset.prod_congr rfl
  intro j _hj
  exact
    res.residualChainEdgeFactor_internal_split
      head tail hremaining x y t v j

/-- A base ambient internal tuple in which the current head coordinates are
zero and the post-prefix coordinates retain their actual values. -/
def headOuterBase
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    Fin m → T4 :=
  res.reconstruct
    ((res.splitSurvivingPiMeasurableEquiv
      head tail hremaining).symm
      ((fun _ : Fin (2 * residualBlockOrder head.2) => 0), v))

/-- The active successor anchoring the current outgoing difference, evaluated
only from post-prefix coordinates. -/
def headSuccessorPoint
    (x y : T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    T4 :=
  assemble x y (res.headOuterBase
    head tail hremaining v)
    (res.edgeSuccessor
      (res.headContext
        head tail hremaining).outgoingSlot)

/-- The actual predecessor point of the current head, evaluated only from
post-prefix coordinates. -/
def headPredecessorPoint
    (x y : T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    T4 :=
  assemble x y (res.headOuterBase
    head tail hremaining v)
    (r324WithinHalfPredecessorSlot
      res.state head).castSucc

/-- The current predecessor point is independent of every head coordinate. -/
theorem assemble_split_predecessor_eq_headPredecessorPoint
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    assemble x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v)))
        (r324WithinHalfPredecessorSlot
          res.state head).castSucc =
      res.headPredecessorPoint
        head tail hremaining x y v := by
  have hp :=
    r324WithinHalfPredecessorSlot_mem
      res.state head
  rw [r324WithinHalfPredecessorCandidates] at hp
  rcases Finset.mem_union.mp hp with
      hzero | hinter
  · have heq :
        r324WithinHalfPredecessorSlot
            res.state head =
          0 := by
      simpa using hzero
    unfold headPredecessorPoint
    rw [heq]
    change
      assemble x y
          (res.reconstruct
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v)))
          (0 : Fin (m + 2)) =
        assemble x y
          (res.headOuterBase
            head tail hremaining v)
          (0 : Fin (m + 2))
    rw [assemble_zero, assemble_zero]
  · obtain ⟨i, hi, heq⟩ :=
      Finset.mem_image.mp hinter
    have hiActive := (Finset.mem_filter.mp hi).1
    have hiLeft := (Finset.mem_filter.mp hi).2
    have hiNot : i ∉ head.2 := by
      intro hiBlock
      have hiLower :=
        (r322AnalyticSchedule_forall_aligned
          pairing head
          (by
            rw [res.schedule_eq, hremaining]
            simp)).2.2 i hiBlock |>.1
      exact (not_lt_of_ge hiLower) hiLeft
    let postI :
        (res.afterHead
          head tail hremaining).SurvivingCoordinate :=
      ⟨i, by
        change
          i ∈
            ((res.headContext
              head tail hremaining).absorb
              ρ lam ε).active
        rw [R324WithinHalfStepContext.absorb_active]
        exact Finset.mem_sdiff.mpr
          ⟨hiActive, hiNot⟩⟩
    have hslot :
        (r324WithinHalfPredecessorSlot
          res.state head).castSucc =
          varIdx i := by
      rw [← heq]
      apply Fin.ext
      rfl
    unfold headPredecessorPoint headOuterBase
    rw [hslot, assemble_varIdx, assemble_varIdx]
    rw [← show postI.1 = i from rfl,
      res.reconstruct_split_symm_post
        head tail hremaining,
      res.reconstruct_split_symm_post
        head tail hremaining]

/-- Under the exact head/post split, the incoming sparse factor is read
from the post-coordinate predecessor point to the first head coordinate. -/
@[simp]
theorem residualChainEdgeFactor_predecessor_split
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    res.residualChainEdgeFactor x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v)))
        (r324WithinHalfPredecessorSlot
          res.state head) =
      res.state.edges
        (r324WithinHalfPredecessorSlot
          res.state head)
        (res.headPredecessorPoint
            head tail hremaining x y v -
          t ⟨0, by
            have hn :=
              res.head_one_le_blockOrder
                head tail hremaining
            omega⟩) := by
  rw [res.residualChainEdgeFactor_predecessor
    head tail hremaining]
  unfold edgeDisplacement
  rw [
    res.assemble_split_predecessor_eq_headPredecessorPoint
      head tail hremaining]
  rw [res.edgeSuccessor_predecessorSlot
    head tail hremaining]
  let ctx :=
    res.headContext head tail hremaining
  have hleft :
      head.1.1 =
        (ctx.blockOrderIso
          ⟨0, by
            have hn := ctx.one_le_blockOrder
            omega⟩).1 :=
    ctx.blockOrderIso_zero.symm
  rw [hleft, assemble_varIdx]
  rw [res.reconstruct_split_symm_block
    head tail hremaining]
  congr 2

/-- The actual sparse successor of the outgoing head edge is independent of
all current-head coordinates. -/
theorem assemble_split_edgeSuccessor_outgoing_eq_headSuccessorPoint
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    assemble x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v)))
        (res.edgeSuccessor
          (res.headContext
            head tail hremaining).outgoingSlot) =
      res.headSuccessorPoint
        head tail hremaining x y v := by
  let ctx :=
    res.headContext head tail hremaining
  have hmem :=
    res.edgeSuccessor_mem_candidates ctx.outgoingSlot
  rw [edgeSuccessorCandidates] at hmem
  rcases Finset.mem_union.mp hmem with
      hlast | hinter
  · have heq :
        res.edgeSuccessor ctx.outgoingSlot =
          Fin.last (m + 1) := by
      simpa using hlast
    unfold headSuccessorPoint
    rw [heq, assemble_last, assemble_last]
  · obtain ⟨i, hi, heq⟩ :=
      Finset.mem_image.mp hinter
    have hiActive := (Finset.mem_filter.mp hi).1
    have houtLt := (Finset.mem_filter.mp hi).2
    have hiNot : i ∉ head.2 := by
      intro hiBlock
      have hiUpper :=
        (r322AnalyticSchedule_forall_aligned
          pairing head ctx.step_mem_schedule).2.2 i hiBlock |>.2
      unfold R324WithinHalfStepContext.outgoingSlot
        r324InternalVertexEdgeSlot at houtLt
      simp only [varIdx_val] at houtLt
      change head.1.2.val + 1 < i.val + 1 at houtLt
      exact
        (not_lt_of_ge hiUpper)
          (Nat.lt_of_add_lt_add_right houtLt)
    let postI :
        (res.afterHead
          head tail hremaining).SurvivingCoordinate :=
      ⟨i, by
        change
          i ∈ (ctx.absorb ρ lam ε).active
        rw [ctx.absorb_active]
        exact Finset.mem_sdiff.mpr
          ⟨hiActive, hiNot⟩⟩
    have hival : postI.1 = i := rfl
    unfold headSuccessorPoint headOuterBase
    rw [← heq, assemble_varIdx, assemble_varIdx]
    rw [← hival,
      res.reconstruct_split_symm_post
        head tail hremaining,
      res.reconstruct_split_symm_post
        head tail hremaining]

@[simp]
theorem standardBlockTuple_reconstruct_split
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    (res.headContext
        head tail hremaining).standardBlockTuple
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))) =
      t := by
  funext j
  exact
    res.reconstruct_split_symm_block
      head tail hremaining t v j

theorem extractionBlockPrimitiveSum_reconstruct_split
    (ρ : SmoothCutoff) (ε : ℝ)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    r322ExtractionBlockPrimitiveSum ρ ε pairing
        (res.headContext head tail hremaining).blockIndex
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))) =
      ∑ κB :
          {κ : PartialPairing
              (Fin (2 * residualBlockOrder head.2)) //
            κ ∈ primitiveFullPairings
              (residualBlockOrder head.2)},
        primitiveCovarianceProduct ρ ε
          (residualBlockOrder head.2) κB.1 t := by
  rw [
    (res.headContext
      head tail hremaining).extractionBlockPrimitiveSum_eq_standardBlock]
  rw [res.standardBlockTuple_reconstruct_split
    head tail hremaining]
  rfl

/-- The signed outgoing factor of the head reads the first and last standard
head coordinates against its post-coordinate sparse successor. -/
@[simp]
theorem residualStepDifference_head_split
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    res.residualStepDifference x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v)))
        head =
      res.state.edges
          (res.headContext
            head tail hremaining).outgoingSlot
          (t (primitiveLast
              (residualBlockOrder head.2)
              (res.head_one_le_blockOrder
                head tail hremaining)) -
            res.headSuccessorPoint
              head tail hremaining x y v) -
        res.state.edges
          (res.headContext
            head tail hremaining).outgoingSlot
          (t ⟨0, by
              have hn :=
                res.head_one_le_blockOrder
                  head tail hremaining
              omega⟩ -
            res.headSuccessorPoint
              head tail hremaining x y v) := by
  unfold residualStepDifference
  let ctx :=
    res.headContext head tail hremaining
  change
    res.state.edges ctx.outgoingSlot
        (assemble x y
            (res.reconstruct
              ((res.splitSurvivingPiMeasurableEquiv
                head tail hremaining).symm (t, v)))
            (varIdx head.1.2) -
          assemble x y
            (res.reconstruct
              ((res.splitSurvivingPiMeasurableEquiv
                head tail hremaining).symm (t, v)))
            (res.edgeSuccessor ctx.outgoingSlot)) -
      res.state.edges ctx.outgoingSlot
        (assemble x y
            (res.reconstruct
              ((res.splitSurvivingPiMeasurableEquiv
                head tail hremaining).symm (t, v)))
            (varIdx head.1.1) -
          assemble x y
            (res.reconstruct
              ((res.splitSurvivingPiMeasurableEquiv
                head tail hremaining).symm (t, v)))
            (res.edgeSuccessor ctx.outgoingSlot)) =
      _
  rw [
    res.assemble_split_edgeSuccessor_outgoing_eq_headSuccessorPoint
      head tail hremaining]
  have hright :
      head.1.2 =
        (ctx.blockOrderIso
          (primitiveLast
            (residualBlockOrder head.2)
            ctx.one_le_blockOrder)).1 :=
    ctx.blockOrderIso_last.symm
  have hleft :
      head.1.1 =
        (ctx.blockOrderIso
          ⟨0, by
            have hn := ctx.one_le_blockOrder
            omega⟩).1 :=
    ctx.blockOrderIso_zero.symm
  rw [hright, hleft, assemble_varIdx, assemble_varIdx]
  rw [res.reconstruct_split_symm_block
      head tail hremaining,
    res.reconstruct_split_symm_block
      head tail hremaining]
  rfl

/-- The four factors belonging to the literal head before its spatial
collapse. -/
def headLocalFactor
    (ρ : SmoothCutoff) (ε : ℝ)
    (x y : T4) (v : Fin m → T4) : ℝ :=
  res.residualChainEdgeFactor x y v
      (r324WithinHalfPredecessorSlot
        res.state head) *
    res.headInternalChainProduct
      head tail hremaining x y v *
    res.residualStepDifference x y v head *
    r322ExtractionBlockPrimitiveSum ρ ε pairing
      (res.headContext
        head tail hremaining).blockIndex v

/-- Primitive chains are unchanged by translating every standard coordinate
by the same torus point. -/
theorem primitiveChainProduct_sub_const
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (a : T4) :
    primitiveChainProduct
        (residualBlockOrder head.2)
        (res.headContext
          head tail hremaining).one_le_blockOrder
        (res.headContext
          head tail hremaining).internalEdges
        (fun j => t j - a) =
      primitiveChainProduct
        (residualBlockOrder head.2)
        (res.headContext
          head tail hremaining).one_le_blockOrder
        (res.headContext
          head tail hremaining).internalEdges t := by
  unfold primitiveChainProduct
  apply Finset.prod_congr rfl
  intro j _hj
  apply congrArg
    ((res.headContext
      head tail hremaining).internalEdges j)
  change
    (t (primitiveEdgeLeft
          (residualBlockOrder head.2)
          (res.headContext
            head tail hremaining).one_le_blockOrder j) - a) -
        (t (primitiveEdgeRight
          (residualBlockOrder head.2)
          (res.headContext
            head tail hremaining).one_le_blockOrder j) - a) =
      t (primitiveEdgeLeft
          (residualBlockOrder head.2)
          (res.headContext
            head tail hremaining).one_le_blockOrder j) -
        t (primitiveEdgeRight
          (residualBlockOrder head.2)
          (res.headContext
            head tail hremaining).one_le_blockOrder j)
  abel

omit tail hremaining in
/-- Primitive covariance products are unchanged by translating every
standard coordinate by the same torus point. -/
theorem primitiveCovarianceProduct_sub_const
    (ρ : SmoothCutoff) (ε : ℝ)
    (κ :
      PartialPairing
        (Fin (2 * residualBlockOrder head.2)))
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (a : T4) :
    primitiveCovarianceProduct ρ ε
        (residualBlockOrder head.2) κ
        (fun j => t j - a) =
      primitiveCovarianceProduct ρ ε
        (residualBlockOrder head.2) κ t := by
  unfold primitiveCovarianceProduct
  apply Finset.prod_congr rfl
  intro i _hi
  apply congrArg (ρ.etaEpsT4 ε)
  change
    (t i - a) - (t (κ i) - a) =
      t i - t (κ i)
  abel

/-- Under the exact coordinate split, the literal head factors are precisely
the translated raw local integrand consumed by the collapse theorem. -/
theorem headLocalFactor_reconstruct_split
    (ρ : SmoothCutoff) (ε : ℝ)
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    res.headLocalFactor
        head tail hremaining ρ ε x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))) =
      (res.headContext
        head tail hremaining).rawLocalIntegrand ρ ε
        (res.headPredecessorPoint
            head tail hremaining x y v -
          res.headSuccessorPoint
            head tail hremaining x y v)
        (fun j =>
          t j -
            res.headSuccessorPoint
              head tail hremaining x y v) := by
  let ctx :=
    res.headContext head tail hremaining
  unfold headLocalFactor
  rw [
    res.residualChainEdgeFactor_predecessor_split
      head tail hremaining,
    res.headInternalChainProduct_split
      head tail hremaining,
    res.residualStepDifference_head_split
      head tail hremaining,
    res.extractionBlockPrimitiveSum_reconstruct_split
      head tail hremaining]
  rw [ctx.rawLocalIntegrand_translated]
  rfl

@[simp]
theorem remainingOutgoingSlots_head :
    res.remainingOutgoingSlots =
      r324InternalVertexEdgeSlot head.1.2 ::
        (res.afterHead head tail hremaining).remainingOutgoingSlots := by
  unfold remainingOutgoingSlots
  rw [hremaining]
  rfl

end Head

end R324WithinHalfResidualPrefix

end

end Anderson4D
