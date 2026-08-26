import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfResidualIntegrand

/-!
# One-step transport of a complete R-324 within-half residual integrand

This module compares the complete sparse residual integrand before and after
one genuine head collapse.  It starts with the geometry that identifies the
new sparse successor of the absorbed predecessor edge.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res :
      R324WithinHalfResidualPrefix
        ρ lam ε pairing)

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

/-- The post-head active carrier is the literal set difference by the head
block. -/
theorem afterHead_active :
    (post res head tail hremaining).state.active =
      res.state.active \ head.2 := by
  change
    ((ctx res head tail hremaining).absorb
      ρ lam ε).active =
      res.state.active \ head.2
  exact
    (ctx res head tail hremaining).absorb_active
      ρ lam ε

/-- Seen from the old predecessor, deleting the current block leaves exactly
the same candidate vertices as looking to the right of the old outgoing
slot. -/
theorem edgeSuccessorCandidates_afterHead_predecessor :
    (post res head tail hremaining).edgeSuccessorCandidates
        (r324WithinHalfPredecessorSlot
          res.state head) =
      res.edgeSuccessorCandidates
        (ctx res head tail hremaining).outgoingSlot := by
  let pred :=
    r324WithinHalfPredecessorSlot
      res.state head
  let outgoing :=
    (ctx res head tail hremaining).outgoingSlot
  have hblock :
      head.2 =
        res.state.active ∩
          Finset.Icc head.1.1 head.1.2 := by
    simpa [R324WithinHalfEdgeState.active] using
      r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
        pairing res.state.processed tail head
        (ctx res head tail hremaining).schedule_eq
  have hfilter :
      ((post res head tail hremaining).state.active.filter
          fun i => pred.val < (varIdx i).val) =
        (res.state.active.filter
          fun i => outgoing.val < (varIdx i).val) := by
    ext i
    rw [res.afterHead_active head tail hremaining]
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hiActive, hiNotHead⟩, hpredLt⟩
      refine ⟨hiActive, ?_⟩
      have hrightLt : head.1.2 < i := by
        by_contra hnot
        have hiRight : i ≤ head.1.2 :=
          le_of_not_gt hnot
        have hiLeft : i < head.1.1 := by
          by_contra hnotLeft
          have hleftLe : head.1.1 ≤ i :=
            le_of_not_gt hnotLeft
          apply hiNotHead
          rw [hblock]
          exact Finset.mem_inter.mpr
            ⟨hiActive,
              Finset.mem_Icc.mpr
                ⟨hleftLe, hiRight⟩⟩
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
      dsimp only [outgoing, ctx]
      unfold R324WithinHalfStepContext.outgoingSlot
        r324InternalVertexEdgeSlot
      simp only [varIdx_val]
      change head.1.2.val + 1 < i.val + 1
      omega
    · rintro ⟨hiActive, houtLt⟩
      refine
        ⟨⟨hiActive, ?_⟩, ?_⟩
      · intro hiHead
        have hiUpper :=
          (r322AnalyticSchedule_forall_aligned
            pairing head
            (ctx res head tail hremaining).step_mem_schedule).2.2
              i hiHead |>.2
        dsimp only [outgoing, ctx] at houtLt
        unfold R324WithinHalfStepContext.outgoingSlot
          r324InternalVertexEdgeSlot at houtLt
        simp only [varIdx_val] at houtLt
        change head.1.2.val + 1 < i.val + 1 at houtLt
        exact
          (not_lt_of_ge hiUpper)
            (Nat.lt_of_add_lt_add_right houtLt)
      · have hp :=
          res.predecessorSlot_lt_outgoingSlot
            head tail hremaining
        change pred.val < outgoing.val at hp
        exact hp.trans houtLt
  unfold edgeSuccessorCandidates
  rw [hfilter]

/-- The sparse successor of the absorbed predecessor is exactly the old
successor beyond the outgoing head edge. -/
theorem edgeSuccessor_afterHead_predecessor :
    (post res head tail hremaining).edgeSuccessor
        (r324WithinHalfPredecessorSlot
          res.state head) =
      res.edgeSuccessor
        (ctx res head tail hremaining).outgoingSlot := by
  have hcandidates :=
    res.edgeSuccessorCandidates_afterHead_predecessor
      head tail hremaining
  apply le_antisymm
  · have hmem :
        res.edgeSuccessor
            (ctx res head tail hremaining).outgoingSlot ∈
          (post res head tail hremaining).edgeSuccessorCandidates
            (r324WithinHalfPredecessorSlot
              res.state head) := by
      rw [hcandidates]
      exact
        res.edgeSuccessor_mem_candidates
          (ctx res head tail hremaining).outgoingSlot
    unfold edgeSuccessor
    exact Finset.min'_le _ _ hmem
  · have hmem :
        (post res head tail hremaining).edgeSuccessor
            (r324WithinHalfPredecessorSlot
              res.state head) ∈
          res.edgeSuccessorCandidates
            (ctx res head tail hremaining).outgoingSlot := by
      rw [← hcandidates]
      exact
        (post res head tail hremaining).edgeSuccessor_mem_candidates
          (r324WithinHalfPredecessorSlot
            res.state head)
    unfold edgeSuccessor
    exact Finset.min'_le _ _ hmem

/-- Removing the current head does not change successor candidates of any
later outgoing edge: every removed head vertex lies strictly to its left. -/
theorem edgeSuccessorCandidates_afterHead_later
    (later : R322ExtractionStep m)
    (hlater : later ∈ tail) :
    (post res head tail hremaining).edgeSuccessorCandidates
        (r324InternalVertexEdgeSlot later.1.2) =
      res.edgeSuccessorCandidates
        (r324InternalVertexEdgeSlot later.1.2) := by
  have hright :=
    res.head_right_lt_tail_right
      head tail hremaining later hlater
  have hfilter :
      ((post res head tail hremaining).state.active.filter
          fun i =>
            (r324InternalVertexEdgeSlot later.1.2).val <
              (varIdx i).val) =
        (res.state.active.filter
          fun i =>
            (r324InternalVertexEdgeSlot later.1.2).val <
              (varIdx i).val) := by
    ext i
    rw [res.afterHead_active head tail hremaining]
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hiActive, _hiNot⟩, hedge⟩
      exact ⟨hiActive, hedge⟩
    · rintro ⟨hiActive, hedge⟩
      refine ⟨⟨hiActive, ?_⟩, hedge⟩
      intro hiHead
      have hiUpper :=
        (r322AnalyticSchedule_forall_aligned
          pairing head
          (ctx res head tail hremaining).step_mem_schedule).2.2
            i hiHead |>.2
      unfold r324InternalVertexEdgeSlot at hedge
      simp only [varIdx_val] at hedge
      change later.1.2.val + 1 < i.val + 1 at hedge
      change head.1.2.val < later.1.2.val at hright
      omega
  unfold edgeSuccessorCandidates
  rw [hfilter]

/-- Consequently every later outgoing edge has the same sparse successor
before and after the head collapse. -/
theorem edgeSuccessor_afterHead_later
    (later : R322ExtractionStep m)
    (hlater : later ∈ tail) :
    (post res head tail hremaining).edgeSuccessor
        (r324InternalVertexEdgeSlot later.1.2) =
      res.edgeSuccessor
        (r324InternalVertexEdgeSlot later.1.2) := by
  have hcandidates :=
    res.edgeSuccessorCandidates_afterHead_later
      head tail hremaining later hlater
  apply le_antisymm
  · have hmem :
        res.edgeSuccessor
            (r324InternalVertexEdgeSlot later.1.2) ∈
          (post res head tail hremaining).edgeSuccessorCandidates
            (r324InternalVertexEdgeSlot later.1.2) := by
      rw [hcandidates]
      exact
        res.edgeSuccessor_mem_candidates
          (r324InternalVertexEdgeSlot later.1.2)
    unfold edgeSuccessor
    exact Finset.min'_le _ _ hmem
  · have hmem :
        (post res head tail hremaining).edgeSuccessor
            (r324InternalVertexEdgeSlot later.1.2) ∈
          res.edgeSuccessorCandidates
            (r324InternalVertexEdgeSlot later.1.2) := by
      rw [← hcandidates]
      exact
        (post res head tail hremaining).edgeSuccessor_mem_candidates
            (r324InternalVertexEdgeSlot later.1.2)
    unfold edgeSuccessor
    exact Finset.min'_le _ _ hmem

/-- Every endpoint of a later suffix step already survives immediately
after the current head is removed. -/
theorem tail_step_endpoints_mem_afterHead_active
    (later : R322ExtractionStep m)
    (hlater : later ∈ tail) :
    later.1.1 ∈
        (post res head tail hremaining).state.active ∧
      later.1.2 ∈
        (post res head tail hremaining).state.active := by
  obtain ⟨before, after, htail⟩ :=
    List.mem_iff_append.mp hlater
  have hschedule :
      r322AnalyticSchedule pairing =
        ((post res head tail hremaining).state.processed ++
            before) ++
          later :: after := by
    rw [res.schedule_eq, hremaining]
    change
      res.state.processed ++
          head :: tail =
        ((res.state.processed ++ [head]) ++ before) ++
          later :: after
    rw [htail]
    simp only [List.append_assoc, List.cons_append,
      List.nil_append]
  have hend :=
    r322AnalyticSchedule_step_endpoints_mem_activeCarrier
      pairing
      ((post res head tail hremaining).state.processed ++
        before)
      after later hschedule
  have hsubset :=
    r322AnalyticActiveCarrier_append_subset
      (post res head tail hremaining).state.processed
      before
  constructor
  · change
      later.1.1 ∈
        r322AnalyticActiveCarrier
          (post res head tail hremaining).state.processed
    exact hsubset hend.1
  · change
      later.1.2 ∈
        r322AnalyticActiveCarrier
          (post res head tail hremaining).state.processed
    exact hsubset hend.2

/-- In fact the entire extraction block of every later suffix step already
survives immediately after the current head. -/
theorem tail_step_block_subset_afterHead_active
    (later : R322ExtractionStep m)
    (hlater : later ∈ tail) :
    later.2 ⊆
      (post res head tail hremaining).state.active := by
  obtain ⟨before, after, htail⟩ :=
    List.mem_iff_append.mp hlater
  have hschedule :
      r322AnalyticSchedule pairing =
        ((post res head tail hremaining).state.processed ++
            before) ++
          later :: after := by
    rw [res.schedule_eq, hremaining]
    change
      res.state.processed ++
          head :: tail =
        ((res.state.processed ++ [head]) ++ before) ++
          later :: after
    rw [htail]
    simp only [List.append_assoc, List.cons_append,
      List.nil_append]
  have hblock :
      later.2 =
        r322AnalyticActiveCarrier
            ((post res head tail hremaining).state.processed ++
              before) ∩
          Finset.Icc later.1.1 later.1.2 :=
    r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
      pairing
      ((post res head tail hremaining).state.processed ++
        before)
      after later hschedule
  have hsubset :=
    r322AnalyticActiveCarrier_append_subset
      (post res head tail hremaining).state.processed
      before
  intro i hi
  rw [hblock] at hi
  change
    i ∈
      r322AnalyticActiveCarrier
        (post res head tail hremaining).state.processed
  exact hsubset (Finset.mem_inter.mp hi).1

/-- A later outgoing slot is distinct from the predecessor updated by the
current head. -/
theorem later_outgoingSlot_ne_predecessor
    (later : R322ExtractionStep m)
    (hlater : later ∈ tail) :
    r324InternalVertexEdgeSlot later.1.2 ≠
      r324WithinHalfPredecessorSlot
        res.state head := by
  intro heq
  apply
    res.predecessorSlot_not_mem_remainingOutgoingSlots
      head tail hremaining
  rw [← heq]
  unfold remainingOutgoingSlots
  rw [hremaining]
  simp only [List.map_cons, List.mem_cons]
  right
  exact List.mem_map.mpr
    ⟨later, hlater, rfl⟩

/-- Absorbing the head leaves every later outgoing named edge unchanged. -/
theorem afterHead_edges_later_outgoing
    (later : R322ExtractionStep m)
    (hlater : later ∈ tail) :
    (post res head tail hremaining).state.edges
        (r324InternalVertexEdgeSlot later.1.2) =
      res.state.edges
        (r324InternalVertexEdgeSlot later.1.2) := by
  exact
    (ctx res head tail hremaining).absorb_edges_of_ne
      ρ lam ε
      (r324InternalVertexEdgeSlot later.1.2)
      (res.later_outgoingSlot_ne_predecessor
        head tail hremaining later hlater)

/-- Every post-head sparse successor is read identically by the exact
pre-head split tuple and by the post-head reconstruction. -/
theorem assemble_split_afterHead_edgeSuccessor_eq
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4)
    (edge : Fin (m + 1)) :
    assemble x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v)))
        ((post res head tail hremaining).edgeSuccessor edge) =
      assemble x y
        ((post res head tail hremaining).reconstruct v)
        ((post res head tail hremaining).edgeSuccessor edge) := by
  have hmem :=
    (post res head tail hremaining).edgeSuccessor_mem_candidates
      edge
  rw [edgeSuccessorCandidates] at hmem
  rcases Finset.mem_union.mp hmem with
      hlast | hinter
  · have heq :
        (post res head tail hremaining).edgeSuccessor edge =
          Fin.last (m + 1) := by
      simpa using hlast
    rw [heq, assemble_last, assemble_last]
  · obtain ⟨i, hi, heq⟩ :=
      Finset.mem_image.mp hinter
    let postI :
        (post res head tail hremaining).SurvivingCoordinate :=
      ⟨i, (Finset.mem_filter.mp hi).1⟩
    rw [← heq, assemble_varIdx, assemble_varIdx]
    exact
      res.reconstruct_split_symm_post
        head tail hremaining t v postI

/-- The exact split and post reconstruction agree at both endpoints of any
later suffix step. -/
theorem assemble_split_later_endpoints_eq_afterHead
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4)
    (later : R322ExtractionStep m)
    (hlater : later ∈ tail) :
    (assemble x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v)))
        (varIdx later.1.1) =
      assemble x y
        ((post res head tail hremaining).reconstruct v)
        (varIdx later.1.1)) ∧
    (assemble x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v)))
        (varIdx later.1.2) =
      assemble x y
        ((post res head tail hremaining).reconstruct v)
        (varIdx later.1.2)) := by
  have hend :=
    res.tail_step_endpoints_mem_afterHead_active
      head tail hremaining later hlater
  let leftI :
      (post res head tail hremaining).SurvivingCoordinate :=
    ⟨later.1.1, hend.1⟩
  let rightI :
      (post res head tail hremaining).SurvivingCoordinate :=
    ⟨later.1.2, hend.2⟩
  constructor
  · rw [assemble_varIdx, assemble_varIdx]
    exact
      res.reconstruct_split_symm_post
        head tail hremaining t v leftI
  · rw [assemble_varIdx, assemble_varIdx]
    exact
      res.reconstruct_split_symm_post
        head tail hremaining t v rightI

/-- A later signed residual difference is unchanged by the head collapse
and reads only the post-head coordinates. -/
theorem residualStepDifference_later_reconstruct_split
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4)
    (later : R322ExtractionStep m)
    (hlater : later ∈ tail) :
    res.residualStepDifference x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v)))
        later =
      (post res head tail hremaining).residualStepDifference
        x y
        ((post res head tail hremaining).reconstruct v)
        later := by
  have hend :=
    res.assemble_split_later_endpoints_eq_afterHead
      head tail hremaining x y t v later hlater
  have hsuccessor :
      assemble x y
          (res.reconstruct
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v)))
          (res.edgeSuccessor
            (r324InternalVertexEdgeSlot later.1.2)) =
        assemble x y
          ((post res head tail hremaining).reconstruct v)
          ((post res head tail hremaining).edgeSuccessor
            (r324InternalVertexEdgeSlot later.1.2)) := by
    rw [←
      res.edgeSuccessor_afterHead_later
        head tail hremaining later hlater]
    exact
      res.assemble_split_afterHead_edgeSuccessor_eq
        head tail hremaining x y t v
        (r324InternalVertexEdgeSlot later.1.2)
  unfold residualStepDifference
  dsimp only
  rw [
    res.afterHead_edges_later_outgoing
      head tail hremaining later hlater,
    hend.1, hend.2, hsuccessor]

/-- The full remaining signed-difference product splits into the literal
head difference and the post-head suffix product. -/
theorem residualDifferenceProduct_reconstruct_split
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4) :
    res.residualDifferenceProduct x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))) =
      res.residualStepDifference x y
          (res.reconstruct
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v)))
          head *
        (post res head tail hremaining).residualDifferenceProduct
          x y
          ((post res head tail hremaining).reconstruct v) := by
  unfold residualDifferenceProduct
  rw [hremaining]
  simp only [List.map_cons, List.prod_cons]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro later hlater
  exact
    res.residualStepDifference_later_reconstruct_split
      head tail hremaining x y t v later hlater

/-- Length form of the literal head/suffix decomposition. -/
theorem remaining_length_eq_tail_succ :
    res.remaining.length = tail.length + 1 := by
  rw [hremaining]
  simp

/-- Under the canonical finite-index cast, index zero of the old remaining
list is the current head block. -/
theorem remainingBlockIndex_cast_zero :
    res.remainingBlockIndex
        ((finCongr
          (res.remaining_length_eq_tail_succ
            head tail hremaining)).symm
          (0 : Fin (tail.length + 1))) =
      (ctx res head tail hremaining).blockIndex := by
  apply Subtype.ext
  simp [remainingBlockIndex, hremaining]
  change head.2 = head.2
  rfl

/-- Positive finite indices of the old remaining list are exactly the
post-head remaining block indices. -/
theorem remainingBlockIndex_cast_succ
    (j : Fin tail.length) :
    res.remainingBlockIndex
        ((finCongr
          (res.remaining_length_eq_tail_succ
            head tail hremaining)).symm j.succ) =
      (post res head tail hremaining).remainingBlockIndex j := by
  apply Subtype.ext
  simp [remainingBlockIndex, hremaining]

/-- The complete primitive sum of any later block is independent of all
head coordinates in the exact split. -/
theorem extractionBlockPrimitiveSum_later_reconstruct_split
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (B : ExtractionBlockIndex pairing)
    (later : R322ExtractionStep m)
    (hlater : later ∈ tail)
    (hB : B.1 = later.2)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4) :
    r322ExtractionBlockPrimitiveSum ρ' ε' pairing B
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))) =
      r322ExtractionBlockPrimitiveSum ρ' ε' pairing B
        ((post res head tail hremaining).reconstruct v) := by
  apply r322ExtractionBlockPrimitiveSum_eq_of_eq_on
  intro i hi
  have hiLater : i ∈ later.2 := by
    rw [← hB]
    exact hi
  let postI :
      (post res head tail hremaining).SurvivingCoordinate :=
    ⟨i,
      res.tail_step_block_subset_afterHead_active
        head tail hremaining later hlater hiLater⟩
  exact
    res.reconstruct_split_symm_post
      head tail hremaining t v postI

/-- The complete remaining primitive-coordinate product splits into the
current head block and the post-head suffix product. -/
theorem residualPrimitiveProduct_reconstruct_split
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4) :
    res.residualPrimitiveProduct ρ' ε'
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))) =
      r322ExtractionBlockPrimitiveSum ρ' ε' pairing
          (ctx res head tail hremaining).blockIndex
          (res.reconstruct
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v))) *
        (post res head tail hremaining).residualPrimitiveProduct
          ρ' ε'
          ((post res head tail hremaining).reconstruct v) := by
  let e :
      Fin res.remaining.length ≃
        Fin (tail.length + 1) :=
    finCongr
      (res.remaining_length_eq_tail_succ
        head tail hremaining)
  let preTuple : Fin m → T4 :=
    res.reconstruct
      ((res.splitSurvivingPiMeasurableEquiv
        head tail hremaining).symm (t, v))
  let postTuple : Fin m → T4 :=
    (post res head tail hremaining).reconstruct v
  calc
    res.residualPrimitiveProduct ρ' ε' preTuple =
        ∏ k : Fin (tail.length + 1),
          r322ExtractionBlockPrimitiveSum ρ' ε' pairing
            (res.remainingBlockIndex (e.symm k))
            preTuple := by
      unfold residualPrimitiveProduct
      apply Fintype.prod_equiv e
      intro j
      simp only [e, Equiv.symm_apply_apply]
    _ =
        r322ExtractionBlockPrimitiveSum ρ' ε' pairing
            (res.remainingBlockIndex
              (e.symm (0 : Fin (tail.length + 1))))
            preTuple *
          ∏ j : Fin tail.length,
            r322ExtractionBlockPrimitiveSum ρ' ε' pairing
              (res.remainingBlockIndex (e.symm j.succ))
              preTuple := by
      exact Fin.prod_univ_succ _
    _ =
        r322ExtractionBlockPrimitiveSum ρ' ε' pairing
            (ctx res head tail hremaining).blockIndex
            preTuple *
          (post res head tail hremaining).residualPrimitiveProduct
            ρ' ε' postTuple := by
      congr 1
      · rw [res.remainingBlockIndex_cast_zero
          head tail hremaining]
      · unfold residualPrimitiveProduct
        apply Finset.prod_congr rfl
        intro j _hj
        rw [res.remainingBlockIndex_cast_succ
          head tail hremaining j]
        exact
          res.extractionBlockPrimitiveSum_later_reconstruct_split
            head tail hremaining ρ' ε'
            ((post res head tail hremaining).remainingBlockIndex j)
            (tail.get j)
            (tail.get_mem j)
            rfl t v

/-! ## Ordinary sparse-chain partition -/

/-- The ordinary edge slots internal to the current head block. -/
def headInternalSlots : Finset (Fin (m + 1)) :=
  Finset.univ.image
    (ctx res head tail hremaining).internalSlot

/-- The predecessor together with every ordinary internal head slot. -/
def headChainSlots : Finset (Fin (m + 1)) :=
  {r324WithinHalfPredecessorSlot res.state head} ∪
    res.headInternalSlots head tail hremaining

/-- Distinct standard internal indices give distinct ambient edge slots. -/
theorem internalSlot_injective :
    Function.Injective
      (ctx res head tail hremaining).internalSlot := by
  intro j k hjk
  let c :=
    ctx res head tail hremaining
  let j0 :
      Fin (2 * residualBlockOrder c.step.2) :=
    ⟨j.val, by
      have hj := j.isLt
      change
        j.val <
          2 * residualBlockOrder c.step.2 - 1 at hj
      have hn := c.one_le_blockOrder
      omega⟩
  let k0 :
      Fin (2 * residualBlockOrder c.step.2) :=
    ⟨k.val, by
      have hk := k.isLt
      change
        k.val <
          2 * residualBlockOrder c.step.2 - 1 at hk
      have hn := c.one_le_blockOrder
      omega⟩
  have hval := congrArg Fin.val hjk
  unfold R324WithinHalfStepContext.internalSlot
    r324InternalVertexEdgeSlot at hval
  change
    (c.blockOrderIso j0).1.val + 1 =
      (c.blockOrderIso k0).1.val + 1 at hval
  have hvertex :
      (c.blockOrderIso j0).1 =
        (c.blockOrderIso k0).1 := by
    apply Fin.ext
    omega
  have hsub :
      c.blockOrderIso j0 =
        c.blockOrderIso k0 :=
    Subtype.ext hvertex
  have hidx : j0 = k0 :=
    c.blockOrderIso.injective hsub
  apply Fin.ext
  change j0.val = k0.val
  exact congrArg Fin.val hidx

/-- The predecessor lies strictly to the left of every internal head slot. -/
theorem predecessorSlot_lt_internalSlot
    (j : Fin (2 * residualBlockOrder head.2 - 1)) :
    r324WithinHalfPredecessorSlot res.state head <
      (ctx res head tail hremaining).internalSlot j := by
  let c :=
    ctx res head tail hremaining
  let j0 :
      Fin (2 * residualBlockOrder c.step.2) :=
    ⟨j.val, by
      have hj := j.isLt
      change
        j.val <
          2 * residualBlockOrder c.step.2 - 1 at hj
      have hn := c.one_le_blockOrder
      omega⟩
  have hp :=
    res.predecessorSlot_val_le_left head
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      pairing head c.step_mem_schedule
  have hleft :=
    (haligned.2.2
      (c.blockOrderIso j0).1
      (c.blockOrderIso j0).2).1
  unfold R324WithinHalfStepContext.internalSlot
    r324InternalVertexEdgeSlot
  change
    (r324WithinHalfPredecessorSlot
      res.state head).val <
      (c.blockOrderIso j0).1.val + 1
  omega

theorem predecessorSlot_not_mem_headInternalSlots :
    r324WithinHalfPredecessorSlot res.state head ∉
      res.headInternalSlots head tail hremaining := by
  intro hmem
  obtain ⟨j, _hj, heq⟩ :=
    Finset.mem_image.mp hmem
  exact
    (ne_of_lt
      (res.predecessorSlot_lt_internalSlot
        head tail hremaining j)) heq.symm

/-- Product reindexing from the internal-slot image back to standard
primitive-chain indices. -/
theorem prod_headInternalSlots
    (f : Fin (m + 1) → ℝ) :
    (∏ edge ∈ res.headInternalSlots
        head tail hremaining, f edge) =
      ∏ j : Fin (2 * residualBlockOrder head.2 - 1),
        f ((ctx res head tail hremaining).internalSlot j) := by
  unfold headInternalSlots
  exact
    Finset.prod_image
      (res.internalSlot_injective
        head tail hremaining).injOn

/-- The local-slot product is the predecessor factor followed by the
standard internal-chain product. -/
theorem prod_headChainSlots
    (f : Fin (m + 1) → ℝ) :
    (∏ edge ∈ res.headChainSlots
        head tail hremaining, f edge) =
      f (r324WithinHalfPredecessorSlot
          res.state head) *
        ∏ j : Fin (2 * residualBlockOrder head.2 - 1),
          f ((ctx res head tail hremaining).internalSlot j) := by
  unfold headChainSlots
  rw [Finset.prod_union]
  · simp only [Finset.prod_singleton]
    rw [res.prod_headInternalSlots
      head tail hremaining]
  · exact Finset.disjoint_singleton_left.mpr
      (res.predecessorSlot_not_mem_headInternalSlots
        head tail hremaining)

/-- Every internal head slot is inactive after the head block is removed. -/
theorem internalSlot_not_mem_afterHead_activeEdgeSlots
    (j : Fin (2 * residualBlockOrder head.2 - 1)) :
    (ctx res head tail hremaining).internalSlot j ∉
      (post res head tail hremaining).activeEdgeSlots := by
  intro hmem
  rw [activeEdgeSlots] at hmem
  rcases Finset.mem_union.mp hmem with
      hzero | hinter
  · have heq :
        (ctx res head tail hremaining).internalSlot j =
          0 := by
      simpa using hzero
    have hval := congrArg Fin.val heq
    have hpos :
        0 <
          ((ctx res head tail hremaining).internalSlot j).val := by
      let c :=
        ctx res head tail hremaining
      let j0 :
          Fin (2 * residualBlockOrder c.step.2) :=
        ⟨j.val, by
          have hj := j.isLt
          change
            j.val <
              2 * residualBlockOrder c.step.2 - 1 at hj
          have hn := c.one_le_blockOrder
          omega⟩
      change 0 < (c.blockOrderIso j0).1.val + 1
      omega
    exact (ne_of_gt hpos) hval
  · obtain ⟨i, hiActive, heq⟩ :=
      Finset.mem_image.mp hinter
    let c :=
      ctx res head tail hremaining
    let j0 :
        Fin (2 * residualBlockOrder c.step.2) :=
      ⟨j.val, by
        have hj := j.isLt
        change
          j.val <
            2 * residualBlockOrder c.step.2 - 1 at hj
        have hn := c.one_le_blockOrder
        omega⟩
    have hval := congrArg Fin.val heq
    unfold R324WithinHalfStepContext.internalSlot
      r324InternalVertexEdgeSlot at hval
    change
      i.val + 1 =
        (c.blockOrderIso j0).1.val + 1 at hval
    have hieq :
        i = (c.blockOrderIso j0).1 := by
      apply Fin.ext
      omega
    rw [res.afterHead_active
      head tail hremaining] at hiActive
    exact
      (Finset.mem_sdiff.mp hiActive).2
        (hieq ▸ (c.blockOrderIso j0).2)

/-- Thus every post-head ordinary internal factor is one. -/
@[simp]
theorem afterHead_residualChainEdgeFactor_internal
    (x y : T4) (v : Fin m → T4)
    (j : Fin (2 * residualBlockOrder head.2 - 1)) :
    (post res head tail hremaining).residualChainEdgeFactor
        x y v
        ((ctx res head tail hremaining).internalSlot j) =
      1 := by
  unfold residualChainEdgeFactor
  rw [if_neg
    (res.internalSlot_not_mem_afterHead_activeEdgeSlots
      head tail hremaining j)]

/-- The old local-slot product is exactly the incoming factor times the
standard internal-chain product. -/
theorem prod_headChainSlots_before
    (x y : T4) (v : Fin m → T4) :
    (∏ edge ∈ res.headChainSlots
        head tail hremaining,
      res.residualChainEdgeFactor x y v edge) =
      res.residualChainEdgeFactor x y v
          (r324WithinHalfPredecessorSlot
            res.state head) *
        res.headInternalChainProduct
          head tail hremaining x y v := by
  rw [res.prod_headChainSlots
    head tail hremaining]
  rfl

/-- The post-head local-slot product consists only of the updated
predecessor factor. -/
theorem prod_headChainSlots_after
    (x y : T4) (v : Fin m → T4) :
    (∏ edge ∈ res.headChainSlots
        head tail hremaining,
      (post res head tail hremaining).residualChainEdgeFactor
        x y v edge) =
      (post res head tail hremaining).residualChainEdgeFactor
        x y v
        (r324WithinHalfPredecessorSlot
          res.state head) := by
  rw [res.prod_headChainSlots
    head tail hremaining]
  simp only [
    res.afterHead_residualChainEdgeFactor_internal,
    Finset.prod_const_one, mul_one]

/-- Every head-block vertex except the right endpoint contributes one of the
standard internal ordinary slots. -/
theorem internalVertexEdgeSlot_mem_headInternalSlots
    (i : Fin m) (hi : i ∈ head.2)
    (hne : i ≠ head.1.2) :
    r324InternalVertexEdgeSlot i ∈
      res.headInternalSlots head tail hremaining := by
  let c :=
    ctx res head tail hremaining
  let ki :
      Fin (2 * residualBlockOrder c.step.2) :=
    c.blockOrderIso.symm ⟨i, hi⟩
  have hkiLast :
      ki ≠
        primitiveLast
          (residualBlockOrder c.step.2)
          c.one_le_blockOrder := by
    intro heq
    apply hne
    have himage :=
      congrArg Subtype.val
        (c.blockOrderIso.apply_symm_apply
          ⟨i, hi⟩)
    change (c.blockOrderIso ki).1 = i at himage
    rw [heq, c.blockOrderIso_last] at himage
    exact himage.symm
  have hkiLt :
      ki.val <
        2 * residualBlockOrder c.step.2 - 1 := by
    have hkibound := ki.isLt
    have hlastVal :
        (primitiveLast
          (residualBlockOrder c.step.2)
          c.one_le_blockOrder).val =
            2 * residualBlockOrder c.step.2 - 1 := rfl
    by_contra hnot
    have hval :
        ki.val =
          (primitiveLast
            (residualBlockOrder c.step.2)
            c.one_le_blockOrder).val := by
      rw [hlastVal]
      omega
    exact hkiLast (Fin.ext hval)
  let j :
      Fin (2 * residualBlockOrder head.2 - 1) :=
    ⟨ki.val, by
      change
        ki.val <
          2 * residualBlockOrder c.step.2 - 1
      exact hkiLt⟩
  rw [headInternalSlots]
  apply Finset.mem_image.mpr
  refine ⟨j, Finset.mem_univ _, ?_⟩
  unfold R324WithinHalfStepContext.internalSlot
  apply congrArg r324InternalVertexEdgeSlot
  have hjki :
      (⟨j.val, by
        have hj := j.isLt
        change
          j.val <
            2 * residualBlockOrder c.step.2 - 1 at hj
        have hn := c.one_le_blockOrder
        omega⟩ :
        Fin (2 * residualBlockOrder c.step.2)) =
        ki := by
    apply Fin.ext
    rfl
  rw [hjki]
  exact
    congrArg Subtype.val
      (c.blockOrderIso.apply_symm_apply
        ⟨i, hi⟩)

/-- Outside the local predecessor/internal slots and the reserved head
outgoing slot, every old active edge remains active after the head. -/
theorem mem_afterHead_activeEdgeSlots_of_outer
    (edge : Fin (m + 1))
    (hactive : edge ∈ res.activeEdgeSlots)
    (hinternal :
      edge ∉ res.headInternalSlots
        head tail hremaining)
    (hout :
      edge ≠ (ctx res head tail hremaining).outgoingSlot) :
    edge ∈
      (post res head tail hremaining).activeEdgeSlots := by
  rw [activeEdgeSlots] at hactive
  rcases Finset.mem_union.mp hactive with
      hzero | hinter
  · have heq : edge = 0 := by
      simpa using hzero
    rw [heq]
    exact
      (post res head tail hremaining).zero_mem_activeEdgeSlots
  · obtain ⟨i, hiActive, heq⟩ :=
      Finset.mem_image.mp hinter
    have hiNot : i ∉ head.2 := by
      intro hiHead
      by_cases hiright : i = head.1.2
      · apply hout
        rw [← heq, hiright]
        rfl
      · apply hinternal
        rw [← heq]
        exact
          res.internalVertexEdgeSlot_mem_headInternalSlots
            head tail hremaining i hiHead hiright
    rw [← heq]
    apply
      (post res head tail hremaining).internalVertexEdgeSlot_mem_activeEdgeSlots
    rw [res.afterHead_active head tail hremaining]
    exact Finset.mem_sdiff.mpr
      ⟨hiActive, hiNot⟩

/-- Away from the head outgoing slot, the reserved outgoing-slot list is
identical before and after the head. -/
theorem mem_remainingOutgoingSlots_iff_afterHead
    (edge : Fin (m + 1))
    (hout :
      edge ≠ (ctx res head tail hremaining).outgoingSlot) :
    edge ∈ res.remainingOutgoingSlots ↔
      edge ∈
        (post res head tail hremaining).remainingOutgoingSlots := by
  rw [res.remainingOutgoingSlots_head
    head tail hremaining]
  simp only [List.mem_cons]
  exact
    or_iff_right fun heq =>
      hout heq

/-- An active ordinary edge outside the local slots lies either strictly
before the predecessor or strictly after the head outgoing slot. -/
theorem outer_active_edge_dichotomy
    (edge : Fin (m + 1))
    (hactive : edge ∈ res.activeEdgeSlots)
    (hpred :
      edge ≠ r324WithinHalfPredecessorSlot
        res.state head)
    (hinternal :
      edge ∉ res.headInternalSlots
        head tail hremaining)
    (hout :
      edge ≠ (ctx res head tail hremaining).outgoingSlot) :
    edge <
        r324WithinHalfPredecessorSlot
          res.state head ∨
      (ctx res head tail hremaining).outgoingSlot <
        edge := by
  have hblock :
      head.2 =
        res.state.active ∩
          Finset.Icc head.1.1 head.1.2 := by
    simpa [R324WithinHalfEdgeState.active] using
      r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
        pairing res.state.processed tail head
        (ctx res head tail hremaining).schedule_eq
  rw [activeEdgeSlots] at hactive
  rcases Finset.mem_union.mp hactive with
      hzero | hinter
  · have heq : edge = 0 := by
      simpa using hzero
    left
    exact lt_of_le_of_ne
      (by
        rw [heq]
        exact Fin.zero_le _)
      hpred
  · obtain ⟨i, hiActive, heq⟩ :=
      Finset.mem_image.mp hinter
    by_cases hiLeft : i < head.1.1
    · left
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
      rw [heq] at hle
      exact lt_of_le_of_ne hle hpred
    · have hleftLe : head.1.1 ≤ i :=
        le_of_not_gt hiLeft
      by_cases hiRight : i ≤ head.1.2
      · have hiHead : i ∈ head.2 := by
          rw [hblock]
          exact Finset.mem_inter.mpr
            ⟨hiActive,
              Finset.mem_Icc.mpr
                ⟨hleftLe, hiRight⟩⟩
        by_cases hiright : i = head.1.2
        · exfalso
          apply hout
          rw [← heq, hiright]
          rfl
        · exfalso
          apply hinternal
          rw [← heq]
          exact
            res.internalVertexEdgeSlot_mem_headInternalSlots
              head tail hremaining i hiHead hiright
      · right
        have hrightLt : head.1.2 < i :=
          lt_of_not_ge hiRight
        rw [← heq]
        unfold R324WithinHalfStepContext.outgoingSlot
          r324InternalVertexEdgeSlot
        change head.1.2.val + 1 < i.val + 1
        omega

/-- If an edge lies before the old predecessor, its old sparse successor
cannot belong to the head block. -/
theorem edgeSuccessor_vertex_not_mem_head_of_lt_predecessor
    (edge : Fin (m + 1))
    (hedge :
      edge <
        r324WithinHalfPredecessorSlot
          res.state head)
    (i : Fin m)
    (hsuccessor :
      res.edgeSuccessor edge = varIdx i) :
    i ∉ head.2 := by
  intro hiHead
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
    rw [heq] at hedge
    exact (Fin.not_lt_zero edge) hedge
  · obtain ⟨p, hpData, hpEq⟩ :=
      Finset.mem_image.mp hinter
    have hpActive := (Finset.mem_filter.mp hpData).1
    have hpLeft := (Finset.mem_filter.mp hpData).2
    have hcandidate :
        varIdx p ∈
          res.edgeSuccessorCandidates edge := by
      rw [edgeSuccessorCandidates]
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine
        ⟨p,
          Finset.mem_filter.mpr
            ⟨hpActive, ?_⟩,
          rfl⟩
      have hpVal := congrArg Fin.val hpEq
      unfold r324InternalVertexEdgeSlot at hpVal
      change
        p.val + 1 =
          (r324WithinHalfPredecessorSlot
            res.state head).val at hpVal
      simp only [varIdx_val]
      change edge.val < p.val + 1
      change edge.val <
        (r324WithinHalfPredecessorSlot
          res.state head).val at hedge
      omega
    have hle :
        res.edgeSuccessor edge ≤ varIdx p := by
      unfold edgeSuccessor
      exact Finset.min'_le _ _ hcandidate
    have haligned :=
      r322AnalyticSchedule_forall_aligned
        pairing head
        (ctx res head tail hremaining).step_mem_schedule
    have hleftLe :=
      (haligned.2.2 i hiHead).1
    rw [hsuccessor] at hle
    change i.val + 1 ≤ p.val + 1 at hle
    change p.val < head.1.1.val at hpLeft
    change head.1.1.val ≤ i.val at hleftLe
    omega

/-- Every evaluated ordinary outer edge has the same sparse successor after
the head block is removed. -/
theorem edgeSuccessor_afterHead_outer
    (edge : Fin (m + 1))
    (hactive : edge ∈ res.activeEdgeSlots)
    (hpred :
      edge ≠ r324WithinHalfPredecessorSlot
        res.state head)
    (hinternal :
      edge ∉ res.headInternalSlots
        head tail hremaining)
    (hout :
      edge ≠ (ctx res head tail hremaining).outgoingSlot) :
    (post res head tail hremaining).edgeSuccessor edge =
      res.edgeSuccessor edge := by
  have hdichotomy :=
    res.outer_active_edge_dichotomy
      head tail hremaining edge hactive hpred
      hinternal hout
  have hpreInPost :
      res.edgeSuccessor edge ∈
        (post res head tail hremaining).edgeSuccessorCandidates
          edge := by
    have hmem :=
      res.edgeSuccessor_mem_candidates edge
    rw [edgeSuccessorCandidates] at hmem ⊢
    rcases Finset.mem_union.mp hmem with
        hlast | hinter
    · exact Finset.mem_union_left _ hlast
    · obtain ⟨i, hi, heq⟩ :=
        Finset.mem_image.mp hinter
      have hiActive := (Finset.mem_filter.mp hi).1
      have hedgeLt := (Finset.mem_filter.mp hi).2
      have hiNot : i ∉ head.2 := by
        rcases hdichotomy with hbefore | hafter
        · exact
            res.edgeSuccessor_vertex_not_mem_head_of_lt_predecessor
              head tail hremaining edge hbefore i heq.symm
        · intro hiHead
          have hiUpper :=
            (r322AnalyticSchedule_forall_aligned
              pairing head
              (ctx res head tail hremaining).step_mem_schedule).2.2
                i hiHead |>.2
          unfold R324WithinHalfStepContext.outgoingSlot
            r324InternalVertexEdgeSlot at hafter
          simp only [varIdx_val] at hedgeLt
          change head.1.2.val + 1 < edge.val at hafter
          change edge.val < i.val + 1 at hedgeLt
          omega
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine
        ⟨i,
          Finset.mem_filter.mpr
            ⟨?_, hedgeLt⟩,
          heq⟩
      rw [res.afterHead_active head tail hremaining]
      exact Finset.mem_sdiff.mpr
        ⟨hiActive, hiNot⟩
  have hpostInPre :
      (post res head tail hremaining).edgeSuccessor edge ∈
        res.edgeSuccessorCandidates edge := by
    have hmem :=
      (post res head tail hremaining).edgeSuccessor_mem_candidates
        edge
    rw [edgeSuccessorCandidates] at hmem ⊢
    rcases Finset.mem_union.mp hmem with
        hlast | hinter
    · exact Finset.mem_union_left _ hlast
    · obtain ⟨i, hi, heq⟩ :=
        Finset.mem_image.mp hinter
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine
        ⟨i,
          Finset.mem_filter.mpr
            ⟨?_, (Finset.mem_filter.mp hi).2⟩,
          heq⟩
      have hiActive := (Finset.mem_filter.mp hi).1
      rw [res.afterHead_active
        head tail hremaining] at hiActive
      exact (Finset.mem_sdiff.mp hiActive).1
  apply le_antisymm
  · unfold edgeSuccessor
    exact Finset.min'_le _ _ hpreInPost
  · unfold edgeSuccessor
    exact Finset.min'_le _ _ hpostInPre

/-- Post-head active edge slots form a subset of the old active edge slots. -/
theorem afterHead_activeEdgeSlots_subset :
    (post res head tail hremaining).activeEdgeSlots ⊆
      res.activeEdgeSlots := by
  intro edge hactive
  rw [activeEdgeSlots] at hactive ⊢
  rcases Finset.mem_union.mp hactive with
      hzero | hinter
  · exact Finset.mem_union_left _ hzero
  · obtain ⟨i, hiActive, heq⟩ :=
      Finset.mem_image.mp hinter
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, heq⟩
    rw [res.afterHead_active
      head tail hremaining] at hiActive
    exact (Finset.mem_sdiff.mp hiActive).1

/-- The head outgoing slot is inactive after the head block is removed. -/
theorem outgoingSlot_not_mem_afterHead_activeEdgeSlots :
    (ctx res head tail hremaining).outgoingSlot ∉
      (post res head tail hremaining).activeEdgeSlots := by
  intro hactive
  rw [activeEdgeSlots] at hactive
  rcases Finset.mem_union.mp hactive with
      hzero | hinter
  · have heq :
        (ctx res head tail hremaining).outgoingSlot =
          0 := by
      simpa using hzero
    have hpos :
        0 <
          ((ctx res head tail hremaining).outgoingSlot).val := by
      change 0 < head.1.2.val + 1
      omega
    exact (ne_of_gt hpos) (congrArg Fin.val heq)
  · obtain ⟨i, hiActive, heq⟩ :=
      Finset.mem_image.mp hinter
    have hival :
        i = head.1.2 := by
      have hval := congrArg Fin.val heq
      unfold R324WithinHalfStepContext.outgoingSlot
        r324InternalVertexEdgeSlot at hval
      change i.val + 1 = head.1.2.val + 1 at hval
      apply Fin.ext
      omega
    rw [res.afterHead_active
      head tail hremaining] at hiActive
    exact
      (Finset.mem_sdiff.mp hiActive).2
        (hival ▸
          (r322AnalyticSchedule_forall_aligned
            pairing head
            (ctx res head tail hremaining).step_mem_schedule).2.1)

/-- Therefore the post-head outgoing ordinary factor is one. -/
@[simp]
theorem afterHead_residualChainEdgeFactor_outgoing
    (x y : T4) (v : Fin m → T4) :
    (post res head tail hremaining).residualChainEdgeFactor
        x y v
        (ctx res head tail hremaining).outgoingSlot =
      1 := by
  unfold residualChainEdgeFactor
  rw [if_neg
    (res.outgoingSlot_not_mem_afterHead_activeEdgeSlots
      head tail hremaining)]

/-- Exact pre/post reconstructions agree at the left vertex of every
post-head active edge. -/
theorem assemble_split_activeEdge_castSucc_eq_afterHead
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4)
    (edge : Fin (m + 1))
    (hactive :
      edge ∈
        (post res head tail hremaining).activeEdgeSlots) :
    assemble x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v)))
        edge.castSucc =
      assemble x y
        ((post res head tail hremaining).reconstruct v)
        edge.castSucc := by
  rw [activeEdgeSlots] at hactive
  rcases Finset.mem_union.mp hactive with
      hzero | hinter
  · have heq : edge = 0 := by
      simpa using hzero
    rw [heq]
    change
      assemble x y
          (res.reconstruct
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v)))
          (0 : Fin (m + 2)) =
        assemble x y
          ((post res head tail hremaining).reconstruct v)
          (0 : Fin (m + 2))
    rw [assemble_zero, assemble_zero]
  · obtain ⟨i, hiActive, heq⟩ :=
      Finset.mem_image.mp hinter
    let postI :
        (post res head tail hremaining).SurvivingCoordinate :=
      ⟨i, hiActive⟩
    have hslot :
        edge.castSucc = varIdx i := by
      rw [← heq]
      apply Fin.ext
      rfl
    rw [hslot, assemble_varIdx, assemble_varIdx]
    exact
      res.reconstruct_split_symm_post
        head tail hremaining t v postI

/-- Every ordinary outer edge reads the same spatial displacement before
and after the head collapse. -/
theorem edgeDisplacement_reconstruct_split_outer
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4)
    (edge : Fin (m + 1))
    (hactive : edge ∈ res.activeEdgeSlots)
    (hpred :
      edge ≠ r324WithinHalfPredecessorSlot
        res.state head)
    (hinternal :
      edge ∉ res.headInternalSlots
        head tail hremaining)
    (hout :
      edge ≠ (ctx res head tail hremaining).outgoingSlot) :
    res.edgeDisplacement x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v)))
        edge =
      (post res head tail hremaining).edgeDisplacement
        x y
        ((post res head tail hremaining).reconstruct v)
        edge := by
  have hpostActive :=
    res.mem_afterHead_activeEdgeSlots_of_outer
      head tail hremaining edge hactive
      hinternal hout
  have hsuccessor :=
    res.edgeSuccessor_afterHead_outer
      head tail hremaining edge hactive hpred
      hinternal hout
  unfold edgeDisplacement
  rw [
    res.assemble_split_activeEdge_castSucc_eq_afterHead
      head tail hremaining x y t v edge hpostActive]
  rw [← hsuccessor]
  rw [
    res.assemble_split_afterHead_edgeSuccessor_eq
      head tail hremaining x y t v edge]

/-- Every ordinary edge outside the local predecessor/internal slots has
the same factor before and after the head collapse. -/
theorem residualChainEdgeFactor_reconstruct_split_outer
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4)
    (edge : Fin (m + 1))
    (houter :
      edge ∉ res.headChainSlots
        head tail hremaining) :
    res.residualChainEdgeFactor x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v)))
        edge =
      (post res head tail hremaining).residualChainEdgeFactor
        x y
        ((post res head tail hremaining).reconstruct v)
        edge := by
  have hpred :
      edge ≠ r324WithinHalfPredecessorSlot
        res.state head := by
    intro heq
    apply houter
    rw [headChainSlots, heq]
    simp
  have hinternal :
      edge ∉ res.headInternalSlots
        head tail hremaining := by
    intro hmem
    apply houter
    rw [headChainSlots]
    exact Finset.mem_union_right _ hmem
  by_cases houtEq :
      edge =
        (ctx res head tail hremaining).outgoingSlot
  · rw [houtEq,
      res.residualChainEdgeFactor_outgoing
        head tail hremaining,
      res.afterHead_residualChainEdgeFactor_outgoing
        head tail hremaining]
  · have hpostActiveOfActive
        (hactive : edge ∈ res.activeEdgeSlots) :
        edge ∈
          (post res head tail hremaining).activeEdgeSlots :=
      res.mem_afterHead_activeEdgeSlots_of_outer
        head tail hremaining edge hactive
        hinternal houtEq
    have hremainingIff :=
      res.mem_remainingOutgoingSlots_iff_afterHead
        head tail hremaining edge houtEq
    unfold residualChainEdgeFactor
    by_cases hactive :
        edge ∈ res.activeEdgeSlots
    · have hpostActive :=
        hpostActiveOfActive hactive
      rw [if_pos hactive, if_pos hpostActive]
      by_cases hreserved :
          edge ∈ res.remainingOutgoingSlots
      · rw [if_pos hreserved,
          if_pos (hremainingIff.mp hreserved)]
      · have hpostReserved :
            edge ∉
              (post res head tail hremaining).remainingOutgoingSlots :=
          fun hmem =>
            hreserved (hremainingIff.mpr hmem)
        rw [if_neg hreserved, if_neg hpostReserved]
        rw [res.afterHead_state
          head tail hremaining]
        rw [
          (ctx res head tail hremaining).absorb_edges_of_ne
            ρ lam ε edge hpred]
        rw [
          res.edgeDisplacement_reconstruct_split_outer
            head tail hremaining x y t v edge
            hactive hpred hinternal houtEq]
        rfl
    · have hpostInactive :
          edge ∉
            (post res head tail hremaining).activeEdgeSlots :=
        fun hmem =>
          hactive
            (res.afterHead_activeEdgeSlots_subset
              head tail hremaining hmem)
      rw [if_neg hactive, if_neg hpostInactive]

/-- Ordinary outer-chain product before the head collapse. -/
def headOuterChainProductBefore
    (x y : T4) (v : Fin m → T4) : ℝ :=
  ∏ edge ∈
      (Finset.univ \ res.headChainSlots
        head tail hremaining),
    res.residualChainEdgeFactor x y v edge

/-- Ordinary outer-chain product after the head collapse. -/
def headOuterChainProductAfter
    (x y : T4) (v : Fin m → T4) : ℝ :=
  ∏ edge ∈
      (Finset.univ \ res.headChainSlots
        head tail hremaining),
    (post res head tail hremaining).residualChainEdgeFactor
      x y v edge

/-- The ordinary outer-chain product is independent of the head
coordinates and unchanged by the collapse. -/
theorem headOuterChainProductBefore_reconstruct_split
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4) :
    res.headOuterChainProductBefore
        head tail hremaining x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))) =
      res.headOuterChainProductAfter
        head tail hremaining x y
        ((post res head tail hremaining).reconstruct v) := by
  unfold headOuterChainProductBefore
    headOuterChainProductAfter
  apply Finset.prod_congr rfl
  intro edge hedge
  exact
    res.residualChainEdgeFactor_reconstruct_split_outer
      head tail hremaining x y t v edge
      (Finset.mem_sdiff.mp hedge).2

/-- Exact ordinary-chain factorization before the head collapse. -/
theorem residualChainProduct_reconstruct_split
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4) :
    res.residualChainProduct x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))) =
      res.residualChainEdgeFactor x y
          (res.reconstruct
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v)))
          (r324WithinHalfPredecessorSlot
            res.state head) *
        res.headInternalChainProduct
          head tail hremaining x y
          (res.reconstruct
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v))) *
        res.headOuterChainProductAfter
          head tail hremaining x y
          ((post res head tail hremaining).reconstruct v) := by
  let preTuple :=
    res.reconstruct
      ((res.splitSurvivingPiMeasurableEquiv
        head tail hremaining).symm (t, v))
  have hpartition :=
    Finset.prod_inter_mul_prod_sdiff
      (Finset.univ : Finset (Fin (m + 1)))
      (res.headChainSlots head tail hremaining)
      (res.residualChainEdgeFactor x y preTuple)
  simp only [Finset.univ_inter] at hpartition
  unfold residualChainProduct
  rw [← hpartition]
  rw [res.prod_headChainSlots_before
    head tail hremaining]
  have houterEq :=
    res.headOuterChainProductBefore_reconstruct_split
      head tail hremaining x y t v
  unfold headOuterChainProductBefore at houterEq
  dsimp only [preTuple] at houterEq ⊢
  rw [houterEq]

/-- Exact ordinary-chain factorization after the head collapse. -/
theorem afterHead_residualChainProduct
    (x y : T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4) :
    (post res head tail hremaining).residualChainProduct
        x y
        ((post res head tail hremaining).reconstruct v) =
      (post res head tail hremaining).residualChainEdgeFactor
          x y
          ((post res head tail hremaining).reconstruct v)
          (r324WithinHalfPredecessorSlot
            res.state head) *
        res.headOuterChainProductAfter
          head tail hremaining x y
          ((post res head tail hremaining).reconstruct v) := by
  let postTuple :=
    (post res head tail hremaining).reconstruct v
  have hpartition :=
    Finset.prod_inter_mul_prod_sdiff
      (Finset.univ : Finset (Fin (m + 1)))
      (res.headChainSlots head tail hremaining)
      ((post res head tail hremaining).residualChainEdgeFactor
        x y postTuple)
  simp only [Finset.univ_inter] at hpartition
  unfold residualChainProduct
  rw [← hpartition]
  rw [res.prod_headChainSlots_after
    head tail hremaining]
  rfl

/-- All factors independent of the current head coordinates, expressed in
the actual post-head residual state. -/
def headOuterFactor
    (ρ : SmoothCutoff) (ε : ℝ)
    (x y : T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4) :
    ℝ :=
  res.headOuterChainProductAfter
      head tail hremaining x y
      ((post res head tail hremaining).reconstruct v) *
    (post res head tail hremaining).residualDifferenceProduct
      x y
      ((post res head tail hremaining).reconstruct v) *
    (post res head tail hremaining).residualPrimitiveProduct
      ρ ε
      ((post res head tail hremaining).reconstruct v)

/-- The complete pre-head residual integrand is exactly the genuine local
head factor times a post-coordinate outer factor. -/
theorem residualIntegrand_reconstruct_split
    (ρ : SmoothCutoff) (ε : ℝ)
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4) :
    res.residualIntegrand ρ ε x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))) =
      res.headLocalFactor
          head tail hremaining ρ ε x y
          (res.reconstruct
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v))) *
        res.headOuterFactor
          head tail hremaining ρ ε x y v := by
  unfold residualIntegrand headLocalFactor
    headOuterFactor
  rw [
    res.residualChainProduct_reconstruct_split
      head tail hremaining x y t v,
    res.residualDifferenceProduct_reconstruct_split
      head tail hremaining x y t v,
    res.residualPrimitiveProduct_reconstruct_split
      head tail hremaining ρ ε t v]
  ring

/-- The complete post-head residual integrand is the updated predecessor
factor times the same outer factor. -/
theorem afterHead_residualIntegrand
    (ρ : SmoothCutoff) (ε : ℝ)
    (x y : T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4) :
    (post res head tail hremaining).residualIntegrand
        ρ ε x y
        ((post res head tail hremaining).reconstruct v) =
      (post res head tail hremaining).residualChainEdgeFactor
          x y
          ((post res head tail hremaining).reconstruct v)
          (r324WithinHalfPredecessorSlot
            res.state head) *
        res.headOuterFactor
          head tail hremaining ρ ε x y v := by
  unfold residualIntegrand headOuterFactor
  rw [res.afterHead_residualChainProduct
    head tail hremaining x y v]
  ring

/-- The old predecessor slot survives as an ordinary active edge after the
head block is removed. -/
theorem predecessorSlot_mem_afterHead_activeEdgeSlots :
    r324WithinHalfPredecessorSlot res.state head ∈
      (post res head tail hremaining).activeEdgeSlots := by
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
    rw [heq]
    exact
      (post res head tail hremaining).zero_mem_activeEdgeSlots
  · obtain ⟨i, hi, heq⟩ :=
      Finset.mem_image.mp hinter
    have hiActive := (Finset.mem_filter.mp hi).1
    have hiLeft := (Finset.mem_filter.mp hi).2
    have hiNot : i ∉ head.2 := by
      intro hiHead
      have hiLower :=
        (r322AnalyticSchedule_forall_aligned
          pairing head
          (ctx res head tail hremaining).step_mem_schedule).2.2
            i hiHead |>.1
      exact (not_lt_of_ge hiLower) hiLeft
    rw [← heq]
    apply
      (post res head tail hremaining).internalVertexEdgeSlot_mem_activeEdgeSlots
    rw [res.afterHead_active head tail hremaining]
    exact Finset.mem_sdiff.mpr
      ⟨hiActive, hiNot⟩

/-- No later reserved outgoing edge is the old predecessor slot. -/
theorem predecessorSlot_not_mem_afterHead_remainingOutgoingSlots :
    r324WithinHalfPredecessorSlot res.state head ∉
      (post res head tail hremaining).remainingOutgoingSlots := by
  intro hmem
  apply
    res.predecessorSlot_not_mem_remainingOutgoingSlots
      head tail hremaining
  rw [res.remainingOutgoingSlots_head
    head tail hremaining]
  exact List.mem_cons_of_mem _ hmem

/-- Consequently the post-head sparse predecessor factor is the updated
named edge, without an indicator or reserved-slot branch. -/
@[simp]
theorem afterHead_residualChainEdgeFactor_predecessor
    (x y : T4) (v : Fin m → T4) :
    (post res head tail hremaining).residualChainEdgeFactor
        x y v
        (r324WithinHalfPredecessorSlot
          res.state head) =
      (post res head tail hremaining).state.edges
        (r324WithinHalfPredecessorSlot
          res.state head)
        ((post res head tail hremaining).edgeDisplacement
          x y v
          (r324WithinHalfPredecessorSlot
            res.state head)) := by
  unfold residualChainEdgeFactor
  rw [if_pos
      (res.predecessorSlot_mem_afterHead_activeEdgeSlots
        head tail hremaining),
    if_neg
      (res.predecessorSlot_not_mem_afterHead_remainingOutgoingSlots
        head tail hremaining)]

/-- A post-surviving internal coordinate has the same value in the
zero-filled pre-head base and in the actual post-head reconstruction. -/
theorem headOuterBase_eq_afterHead_reconstruct
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4)
    (i :
      (post res head tail hremaining).SurvivingCoordinate) :
    res.headOuterBase head tail hremaining v i.1 =
      (post res head tail hremaining).reconstruct v i.1 := by
  unfold headOuterBase
  exact
    res.reconstruct_split_symm_post
      head tail hremaining _ v i

/-- The post-head predecessor point is the named outer predecessor point
used by the translated local collapse. -/
theorem assemble_afterHead_predecessor_eq_headPredecessorPoint
    (x y : T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4) :
    assemble x y
        ((post res head tail hremaining).reconstruct v)
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
          ((post res head tail hremaining).reconstruct v)
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
      intro hiHead
      have hiLower :=
        (r322AnalyticSchedule_forall_aligned
          pairing head
          (ctx res head tail hremaining).step_mem_schedule).2.2
            i hiHead |>.1
      exact (not_lt_of_ge hiLower) hiLeft
    let postI :
        (post res head tail hremaining).SurvivingCoordinate :=
      ⟨i, by
        rw [res.afterHead_active head tail hremaining]
        exact Finset.mem_sdiff.mpr
          ⟨hiActive, hiNot⟩⟩
    have hslot :
        (r324WithinHalfPredecessorSlot
          res.state head).castSucc =
          varIdx i := by
      rw [← heq]
      apply Fin.ext
      rfl
    unfold headPredecessorPoint
    rw [hslot, assemble_varIdx, assemble_varIdx]
    exact
      (res.headOuterBase_eq_afterHead_reconstruct
        head tail hremaining v postI).symm

/-- Every post-head sparse successor is read identically from the pre-head
outer base and from the post-head reconstruction. -/
theorem assemble_headOuterBase_edgeSuccessor_eq_afterHead
    (x y : T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4)
    (edge : Fin (m + 1)) :
    assemble x y
        (res.headOuterBase
          head tail hremaining v)
        ((post res head tail hremaining).edgeSuccessor edge) =
      assemble x y
        ((post res head tail hremaining).reconstruct v)
        ((post res head tail hremaining).edgeSuccessor edge) := by
  have hmem :=
    (post res head tail hremaining).edgeSuccessor_mem_candidates
      edge
  rw [edgeSuccessorCandidates] at hmem
  rcases Finset.mem_union.mp hmem with
      hlast | hinter
  · have heq :
        (post res head tail hremaining).edgeSuccessor edge =
          Fin.last (m + 1) := by
      simpa using hlast
    rw [heq, assemble_last, assemble_last]
  · obtain ⟨i, hi, heq⟩ :=
      Finset.mem_image.mp hinter
    let postI :
        (post res head tail hremaining).SurvivingCoordinate :=
      ⟨i, (Finset.mem_filter.mp hi).1⟩
    rw [← heq, assemble_varIdx, assemble_varIdx]
    exact
      res.headOuterBase_eq_afterHead_reconstruct
        head tail hremaining v postI

/-- The post-head sparse successor point of the absorbed predecessor is the
outer successor point used by the local collapse. -/
theorem assemble_afterHead_edgeSuccessor_predecessor_eq_headSuccessorPoint
    (x y : T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4) :
    assemble x y
        ((post res head tail hremaining).reconstruct v)
        ((post res head tail hremaining).edgeSuccessor
          (r324WithinHalfPredecessorSlot
            res.state head)) =
      res.headSuccessorPoint
        head tail hremaining x y v := by
  unfold headSuccessorPoint
  rw [←
    res.edgeSuccessor_afterHead_predecessor
      head tail hremaining]
  exact
    (res.assemble_headOuterBase_edgeSuccessor_eq_afterHead
      head tail hremaining x y v
      (r324WithinHalfPredecessorSlot
        res.state head)).symm

/-- The post-head displacement of the absorbed predecessor is exactly the
relative point at which the local collapse returns its updated edge. -/
@[simp]
theorem afterHead_edgeDisplacement_predecessor
    (x y : T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4) :
    (post res head tail hremaining).edgeDisplacement
        x y
        ((post res head tail hremaining).reconstruct v)
        (r324WithinHalfPredecessorSlot
          res.state head) =
      res.headPredecessorPoint
          head tail hremaining x y v -
        res.headSuccessorPoint
          head tail hremaining x y v := by
  unfold edgeDisplacement
  rw [
    res.assemble_afterHead_predecessor_eq_headPredecessorPoint
      head tail hremaining,
    res.assemble_afterHead_edgeSuccessor_predecessor_eq_headSuccessorPoint
      head tail hremaining]

/-- The actual post-head predecessor factor is exactly the updated edge at
the translated local-collapse point. -/
@[simp]
theorem afterHead_residualChainEdgeFactor_predecessor_reconstruct
    (x y : T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4) :
    (post res head tail hremaining).residualChainEdgeFactor
        x y
        ((post res head tail hremaining).reconstruct v)
        (r324WithinHalfPredecessorSlot
          res.state head) =
      (post res head tail hremaining).state.edges
        (r324WithinHalfPredecessorSlot
          res.state head)
        (res.headPredecessorPoint
            head tail hremaining x y v -
          res.headSuccessorPoint
            head tail hremaining x y v) := by
  rw [
    res.afterHead_residualChainEdgeFactor_predecessor
      head tail hremaining,
    res.afterHead_edgeDisplacement_predecessor
      head tail hremaining]

/-- Head-typed wrapper around product-Haar translation invariance.  Keeping
the literal `head.2` carrier in this interface avoids leaking the reducible
`headContext.step` field into the physical residual statement. -/
theorem integral_head_rawLocal_sub_const_mul_complex
    (u a : T4) (outer : ℂ) :
    (∫ actual :
        Fin (2 * residualBlockOrder head.2) → T4,
      ((ctx res head tail hremaining).rawLocalIntegrand
          ρ ε u (fun i => actual i - a) : ℂ) * outer
      ∂Measure.pi fun _ => paperMeasure) =
      ∫ t :
          Fin (2 * residualBlockOrder head.2) → T4,
        ((ctx res head tail hremaining).rawLocalIntegrand
          ρ ε u t : ℂ) * outer
        ∂Measure.pi fun _ => paperMeasure := by
  change
    (∫ actual :
        Fin (2 *
          residualBlockOrder
            (ctx res head tail hremaining).step.2) → T4,
      ((ctx res head tail hremaining).rawLocalIntegrand
          ρ ε u (fun i => actual i - a) : ℂ) * outer
      ∂Measure.pi fun _ => paperMeasure) =
      ∫ t :
          Fin (2 *
            residualBlockOrder
              (ctx res head tail hremaining).step.2) → T4,
        ((ctx res head tail hremaining).rawLocalIntegrand
          ρ ε u t : ℂ) * outer
        ∂Measure.pi fun _ => paperMeasure
  exact
    (ctx res head tail hremaining).integral_rawLocal_sub_const_mul_complex
        ρ ε u a outer

/-- **One physical head section.**

After the exact coordinate split, integrating the genuine four-factor head
section replaces it by the predecessor factor of the absorbed residual
state.  The arbitrary complex outer factor is fixed throughout the local
integral. -/
theorem lamEps_pow_integral_headLocalFactor_eq_afterHead_predecessor
    (x y : T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4)
    (outer : ℂ)
    (hstandard :
      Integrable
        ((ctx res head tail hremaining).localIntegrand ρ ε
          (res.headPredecessorPoint
              head tail hremaining x y v -
            res.headSuccessorPoint
              head tail hremaining x y v))
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder head.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder head.2)},
          Integrable
            (fun w :
                Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder head.2)
                κB.1
                (ctx res head tail hremaining).internalEdges
                (primitiveAssemble
                  (residualBlockOrder head.2)
                  (ctx res head tail hremaining).one_le_blockOrder
                  p.1 p.2 w))
            (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε ^
          (2 * residualBlockOrder head.2) : ℂ) *
        (∫ t : Fin (2 * residualBlockOrder head.2) → T4,
          ((res.headLocalFactor
              head tail hremaining ρ ε x y
              (res.reconstruct
                ((res.splitSurvivingPiMeasurableEquiv
                  head tail hremaining).symm (t, v)))) : ℝ) *
              outer
          ∂Measure.pi fun _ => paperMeasure) =
      (((post res head tail hremaining).residualChainEdgeFactor
          x y
          ((post res head tail hremaining).reconstruct v)
          (r324WithinHalfPredecessorSlot
            res.state head) : ℝ) : ℂ) *
        outer := by
  simp_rw [
    res.headLocalFactor_reconstruct_split
      head tail hremaining]
  rw [
    res.afterHead_residualChainEdgeFactor_predecessor_reconstruct
      head tail hremaining]
  rw [
    res.integral_head_rawLocal_sub_const_mul_complex
        head tail hremaining
        (res.headPredecessorPoint
            head tail hremaining x y v -
          res.headSuccessorPoint
            head tail hremaining x y v)
        (res.headSuccessorPoint
          head tail hremaining x y v)
        outer]
  exact
    res.lamEps_pow_integral_head_rawLocal_eq_afterHead
      head tail hremaining
      (res.headPredecessorPoint
          head tail hremaining x y v -
        res.headSuccessorPoint
          head tail hremaining x y v)
      outer hstandard hinternal

/-- **Complete one-head residual section transition.**

At fixed post-head coordinates, the exact perturbative power times the
complete pre-head residual section integral is the complete post-head
residual integrand. -/
theorem lamEps_pow_integral_residualIntegrand_section_eq_afterHead
    (x y : T4)
    (v :
      (post res head tail hremaining).SurvivingCoordinate → T4)
    (hstandard :
      Integrable
        ((ctx res head tail hremaining).localIntegrand ρ ε
          (res.headPredecessorPoint
              head tail hremaining x y v -
            res.headSuccessorPoint
              head tail hremaining x y v))
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder head.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder head.2)},
          Integrable
            (fun w :
                Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder head.2)
                κB.1
                (ctx res head tail hremaining).internalEdges
                (primitiveAssemble
                  (residualBlockOrder head.2)
                  (ctx res head tail hremaining).one_le_blockOrder
                  p.1 p.2 w))
            (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε ^
          (2 * residualBlockOrder head.2) : ℂ) *
        (∫ t : Fin (2 * residualBlockOrder head.2) → T4,
          (res.residualIntegrand ρ ε x y
            (res.reconstruct
              ((res.splitSurvivingPiMeasurableEquiv
                head tail hremaining).symm (t, v))) : ℂ)
          ∂Measure.pi fun _ => paperMeasure) =
      ((post res head tail hremaining).residualIntegrand
          ρ ε x y
          ((post res head tail hremaining).reconstruct v) :
        ℂ) := by
  simp_rw [
    res.residualIntegrand_reconstruct_split
      head tail hremaining ρ ε x y]
  rw [res.afterHead_residualIntegrand
    head tail hremaining ρ ε x y v]
  have hlocal :=
    res.lamEps_pow_integral_headLocalFactor_eq_afterHead_predecessor
      head tail hremaining x y v
      ((res.headOuterFactor
        head tail hremaining ρ ε x y v : ℝ) : ℂ)
      hstandard hinternal
  simpa only [Complex.ofReal_mul] using hlocal

/-- Fubini for the exact head/post split, with the post coordinates on the
outside.  This is the order consumed by the one-section transition above. -/
theorem integral_splitSurviving_post_first
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (res.SurvivingCoordinate → T4) → E)
    (hf :
      Integrable f
        (Measure.pi fun _ : res.SurvivingCoordinate =>
          paperMeasure)) :
    (∫ w : res.SurvivingCoordinate → T4, f w
        ∂Measure.pi fun _ => paperMeasure) =
      ∫ v :
          (post res head tail hremaining).SurvivingCoordinate → T4,
        ∫ t :
            Fin (2 * residualBlockOrder head.2) → T4,
          f ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))
          ∂Measure.pi fun _ => paperMeasure
        ∂Measure.pi fun _ => paperMeasure := by
  let e :=
    res.splitSurvivingPiMeasurableEquiv
      head tail hremaining
  let μ :=
    Measure.pi fun _ : res.SurvivingCoordinate =>
      paperMeasure
  let μhead :=
    Measure.pi fun _ :
        Fin (2 * residualBlockOrder head.2) =>
      paperMeasure
  let μpost :=
    Measure.pi fun _ :
        (post res head tail hremaining).SurvivingCoordinate =>
      paperMeasure
  have hp :
      MeasurePreserving e μ (μhead.prod μpost) :=
    res.measurePreserving_splitSurvivingPiMeasurableEquiv
      head tail hremaining
  have hf' :
      Integrable (fun p => f (e.symm p))
        (μhead.prod μpost) := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p => f (e.symm p))
    apply hiff.mp
    have hcomp :
        Integrable
          (((fun p => f (e.symm p)) ∘ e)) μ := by
      convert hf using 1
      funext w
      simp only [Function.comp_apply, e.symm_apply_apply]
    exact hcomp
  calc
    (∫ w, f w ∂μ) =
        ∫ p, f (e.symm p) ∂(μhead.prod μpost) := by
      simpa only [Function.comp_apply,
        e.symm_apply_apply] using
        hp.integral_comp' (fun p => f (e.symm p))
    _ =
        ∫ v, ∫ t, f (e.symm (t, v))
          ∂μhead ∂μpost :=
      integral_prod_symm _ hf'
    _ = _ := rfl

/-- **Complete one-head residual-value transition, complex form.** -/
theorem lamEps_pow_integral_residual_eq_afterHead
    (x y : T4)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          (res.residualIntegrand ρ ε x y
            (res.reconstruct w) : ℂ))
        (Measure.pi fun _ => paperMeasure))
    (hstandard :
      ∀ v :
          (post res head tail hremaining).SurvivingCoordinate → T4,
        Integrable
          ((ctx res head tail hremaining).localIntegrand ρ ε
            (res.headPredecessorPoint
                head tail hremaining x y v -
              res.headSuccessorPoint
                head tail hremaining x y v))
          (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ _v :
          (post res head tail hremaining).SurvivingCoordinate → T4,
        ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
          ∀ κB :
              {κ : PartialPairing
                  (Fin (2 * residualBlockOrder head.2)) //
                κ ∈ primitiveFullPairings
                  (residualBlockOrder head.2)},
            Integrable
              (fun w :
                  Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
                detJclosedIntegrandWith ρ ε
                  (2 * residualBlockOrder head.2)
                  κB.1
                  (ctx res head tail hremaining).internalEdges
                  (primitiveAssemble
                    (residualBlockOrder head.2)
                    (ctx res head tail hremaining).one_le_blockOrder
                    p.1 p.2 w))
              (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^
          (2 * res.remainingOrder) *
        (∫ w : res.SurvivingCoordinate → T4,
          (res.residualIntegrand ρ ε x y
            (res.reconstruct w) : ℂ)
          ∂Measure.pi fun _ => paperMeasure) =
      (lamEps lam ε : ℂ) ^
          (2 *
            (post res head tail hremaining).remainingOrder) *
        (∫ v :
            (post res head tail hremaining).SurvivingCoordinate → T4,
          ((post res head tail hremaining).residualIntegrand
            ρ ε x y
            ((post res head tail hremaining).reconstruct v) : ℂ)
          ∂Measure.pi fun _ => paperMeasure) := by
  have hsplit :=
    res.integral_splitSurviving_post_first
      head tail hremaining
      (fun w : res.SurvivingCoordinate → T4 =>
        (res.residualIntegrand ρ ε x y
          (res.reconstruct w) : ℂ))
      hfull
  have hexponent :
      2 * res.remainingOrder =
        2 *
            (post res head tail hremaining).remainingOrder +
          2 * residualBlockOrder head.2 := by
    have horder :
        res.remainingOrder =
          residualBlockOrder head.2 +
            (post res head tail hremaining).remainingOrder := by
      simpa only [post] using
        res.remainingOrder_head head tail hremaining
    omega
  rw [hexponent, pow_add, hsplit]
  rw [mul_assoc]
  rw [← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with v
  exact
    res.lamEps_pow_integral_residualIntegrand_section_eq_afterHead
      head tail hremaining x y v
      (hstandard v) (hinternal v)

/-- Real scalar form of the complete one-head residual-value transition. -/
theorem residualValue_eq_afterHead
    (x y : T4)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          (res.residualIntegrand ρ ε x y
            (res.reconstruct w) : ℂ))
        (Measure.pi fun _ => paperMeasure))
    (hstandard :
      ∀ v :
          (post res head tail hremaining).SurvivingCoordinate → T4,
        Integrable
          ((ctx res head tail hremaining).localIntegrand ρ ε
            (res.headPredecessorPoint
                head tail hremaining x y v -
              res.headSuccessorPoint
                head tail hremaining x y v))
          (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ _v :
          (post res head tail hremaining).SurvivingCoordinate → T4,
        ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
          ∀ κB :
              {κ : PartialPairing
                  (Fin (2 * residualBlockOrder head.2)) //
                κ ∈ primitiveFullPairings
                  (residualBlockOrder head.2)},
            Integrable
              (fun w :
                  Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
                detJclosedIntegrandWith ρ ε
                  (2 * residualBlockOrder head.2)
                  κB.1
                  (ctx res head tail hremaining).internalEdges
                  (primitiveAssemble
                    (residualBlockOrder head.2)
                    (ctx res head tail hremaining).one_le_blockOrder
                    p.1 p.2 w))
              (Measure.pi fun _ => paperMeasure)) :
    res.residualValue ρ lam ε x y =
      (post res head tail hremaining).residualValue
        ρ lam ε x y := by
  apply Complex.ofReal_injective
  have hcomplex :=
    res.lamEps_pow_integral_residual_eq_afterHead
      head tail hremaining x y
      hfull hstandard hinternal
  simpa only [residualValue, Complex.ofReal_mul,
    Complex.ofReal_pow, ← integral_complex_ofReal] using
    hcomplex

end Head

/-! ## Exact iteration through the complete remaining suffix -/

/-- The precise Fubini and local-collapse evidence needed for one literal
head of a reachable within-half residual prefix.  Packaging these three
facts keeps the list iteration below independent of how integrability is
established (globally from the original moment integrand, or locally from a
tree majorant). -/
structure R324WithinHalfResidualStepReady
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (x y : T4) : Prop where
  full :
    Integrable
      (fun w : res.SurvivingCoordinate → T4 =>
        (res.residualIntegrand ρ ε x y
          (res.reconstruct w) : ℂ))
      (Measure.pi fun _ => paperMeasure)
  standard :
    ∀ v :
        (res.afterHead head tail hremaining).SurvivingCoordinate → T4,
      Integrable
        ((res.headContext head tail hremaining).localIntegrand ρ ε
          (res.headPredecessorPoint
              head tail hremaining x y v -
            res.headSuccessorPoint
              head tail hremaining x y v))
        (Measure.pi fun _ => paperMeasure)
  internal :
    ∀ _v :
        (res.afterHead head tail hremaining).SurvivingCoordinate → T4,
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder head.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder head.2)},
          Integrable
            (fun w :
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
                  p.1 p.2 w))
            (Measure.pi fun _ => paperMeasure)

/-- One packaged ready step preserves the complete residual value. -/
theorem R324WithinHalfResidualStepReady.value_eq_afterHead
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {head : R322ExtractionStep m}
    {tail : List (R322ExtractionStep m)}
    {hremaining : res.remaining = head :: tail}
    {x y : T4}
    (ready :
      R324WithinHalfResidualStepReady
        res head tail hremaining x y) :
    res.residualValue ρ lam ε x y =
      (res.afterHead head tail hremaining).residualValue
        ρ lam ε x y :=
  res.residualValue_eq_afterHead
    head tail hremaining x y
    ready.full ready.standard ready.internal

/-- Integrability provider for every genuine nonempty suffix.  This is the
single analytic datum consumed by the structural list iteration. -/
def R324WithinHalfResidualStepProvider
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (x y : T4) : Prop :=
  ∀ (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail),
    R324WithinHalfResidualStepReady
      res head tail hremaining x y

/-- A proof-relevant exact trace through every remaining schedule block. -/
inductive R324WithinHalfResidualIterationReady
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (x y : T4) :
    R324WithinHalfResidualPrefix ρ lam ε pairing → Prop
  | terminal
      (res :
        R324WithinHalfResidualPrefix ρ lam ε pairing)
      (hremaining : res.remaining = []) :
      R324WithinHalfResidualIterationReady x y res
  | step
      (res :
        R324WithinHalfResidualPrefix ρ lam ε pairing)
      (head : R322ExtractionStep m)
      (tail : List (R322ExtractionStep m))
      (hremaining : res.remaining = head :: tail)
      (ready :
        R324WithinHalfResidualStepReady
          res head tail hremaining x y)
      (next :
        R324WithinHalfResidualIterationReady x y
          (res.afterHead head tail hremaining)) :
      R324WithinHalfResidualIterationReady x y res

/-- A uniform step provider constructs the complete proof-relevant trace.
The recursion is on the literal remaining suffix, whose tail is definitionally
the suffix of `afterHead`. -/
theorem R324WithinHalfResidualIterationReady.of_provider
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (x y : T4)
    (provider :
      R324WithinHalfResidualStepProvider
        (ρ := ρ) (lam := lam) (ε := ε)
        (pairing := pairing) x y)
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing) :
    R324WithinHalfResidualIterationReady x y res := by
  cases hremaining : res.remaining with
  | nil =>
      exact
        R324WithinHalfResidualIterationReady.terminal
          res hremaining
  | cons head tail =>
      exact
        R324WithinHalfResidualIterationReady.step
          res head tail hremaining
          (provider res head tail hremaining)
          (R324WithinHalfResidualIterationReady.of_provider
            x y provider
            (res.afterHead head tail hremaining))
termination_by res.remaining.length
decreasing_by simp [hremaining]

/-- Iterating a ready trace reaches a genuine empty suffix and preserves the
complete residual value exactly. -/
theorem R324WithinHalfResidualIterationReady.exists_terminal_value_eq
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {x y : T4}
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    (ready :
      R324WithinHalfResidualIterationReady x y res) :
    ∃ terminal :
        R324WithinHalfResidualPrefix ρ lam ε pairing,
      terminal.remaining = [] ∧
      terminal.state.processed =
        r322AnalyticSchedule pairing ∧
      res.residualValue ρ lam ε x y =
        terminal.residualValue ρ lam ε x y := by
  induction ready with
  | terminal terminal hremaining =>
      refine ⟨terminal, hremaining, ?_, rfl⟩
      have hschedule := terminal.schedule_eq
      rw [hremaining, List.append_nil] at hschedule
      exact hschedule.symm
  | step current head tail hremaining hstep _next ih =>
      obtain ⟨terminal, hterminal, hprocessed, hvalue⟩ := ih
      refine ⟨terminal, hterminal, hprocessed, ?_⟩
      exact hstep.value_eq_afterHead.trans hvalue

/-- Consumer-facing list iteration from one uniform step provider. -/
theorem exists_terminal_residualValue_eq_of_provider
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (x y : T4)
    (provider :
      R324WithinHalfResidualStepProvider
        (ρ := ρ) (lam := lam) (ε := ε)
        (pairing := pairing) x y)
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing) :
    ∃ terminal :
        R324WithinHalfResidualPrefix ρ lam ε pairing,
      terminal.remaining = [] ∧
      terminal.state.processed =
        r322AnalyticSchedule pairing ∧
      res.residualValue ρ lam ε x y =
        terminal.residualValue ρ lam ε x y :=
  (R324WithinHalfResidualIterationReady.of_provider
      x y provider res).exists_terminal_value_eq

end R324WithinHalfResidualPrefix

end

end Anderson4D
