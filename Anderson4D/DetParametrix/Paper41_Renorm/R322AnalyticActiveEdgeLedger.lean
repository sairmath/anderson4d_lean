import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticPrimitiveCertificate

/-!
# Active-edge product ledger for the R-322 analytic schedule

The quantitative R-322 induction controls only edges whose left vertex is
still present in the sparse carrier.  This module packages that finite set
and proves its exact behavior under one proper block deletion.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- Ambient edge slots whose left vertex remains in the sparse carrier. -/
def r322AnalyticActiveEdges
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq) :
    Finset (Fin (2 * q - 1)) :=
  Finset.univ.filter fun edge =>
    r322AnalyticEdgeLeftVertex edge ∈ state.active

@[simp]
theorem mem_r322AnalyticActiveEdges
    {q : ℕ} {hq : 1 ≤ q}
    {state : R322AnalyticEdgeState q hq}
    {edge : Fin (2 * q - 1)} :
    edge ∈ r322AnalyticActiveEdges state ↔
      r322AnalyticEdgeLeftVertex edge ∈ state.active := by
  simp [r322AnalyticActiveEdges]

namespace R322AnalyticProperStepContext

variable {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticProperStepContext q hq)

/-- Every vertex of a proper concrete block determines an ambient edge slot:
the proper-block bound excludes the global last vertex. -/
def blockEdge
    (i : ctx.step.2) :
    Fin (2 * q - 1) :=
  ⟨i.1.val, (ctx.blockVertex_bounds i.1 i.2).2⟩

/-- Edge slots removed together with the proper concrete block. -/
def blockEdges : Finset (Fin (2 * q - 1)) :=
  ctx.step.2.attach.image ctx.blockEdge

theorem blockEdge_injective :
    Function.Injective ctx.blockEdge := by
  intro i j hij
  apply Subtype.ext
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simpa [blockEdge] using hval

@[simp]
theorem mem_blockEdges_iff
    {edge : Fin (2 * q - 1)} :
    edge ∈ ctx.blockEdges ↔
      r322AnalyticEdgeLeftVertex edge ∈ ctx.step.2 := by
  constructor
  · intro hedge
    obtain ⟨i, _hi, hieq⟩ :=
      Finset.mem_image.mp hedge
    have hleft :
        r322AnalyticEdgeLeftVertex edge = i.1 := by
      apply Fin.ext
      have hval := congrArg Fin.val hieq.symm
      simpa [r322AnalyticEdgeLeftVertex, blockEdge] using hval
    exact hleft ▸ i.2
  · intro hedge
    let i : ctx.step.2 :=
      ⟨r322AnalyticEdgeLeftVertex edge, hedge⟩
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_attach _ _, ?_⟩
    apply Fin.ext
    rfl

theorem blockEdges_subset_activeEdges :
    ctx.blockEdges ⊆
      r322AnalyticActiveEdges ctx.state := by
  intro edge hedge
  rw [mem_r322AnalyticActiveEdges,
    ctx.mem_blockEdges_iff] at *
  have hblockEq :=
    r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
      ctx.pairing ctx.state.processed ctx.suffix
      ctx.step ctx.schedule_eq
  rw [hblockEq] at hedge
  exact (Finset.mem_inter.mp hedge).1

theorem predecessorEdge_mem_activeEdges :
    ctx.predecessorEdge ∈
      r322AnalyticActiveEdges ctx.state := by
  rw [mem_r322AnalyticActiveEdges, predecessorEdge,
    r322AnalyticEdgeLeftVertex_predecessorEdge]
  exact
    r322AnalyticPredecessorVertex_mem_active
      ctx.state ctx.step ctx.bounds.1

theorem predecessorEdge_not_mem_blockEdges :
    ctx.predecessorEdge ∉ ctx.blockEdges := by
  rw [ctx.mem_blockEdges_iff, predecessorEdge,
    r322AnalyticEdgeLeftVertex_predecessorEdge]
  intro hmem
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      ctx.pairing ctx.step ctx.step_mem_schedule
  have hleftLe :
      ctx.step.1.1 ≤
        r322AnalyticPredecessorVertex
          ctx.state ctx.step ctx.bounds.1 :=
    (haligned.2.2 _ hmem).1
  exact
    (not_lt_of_ge hleftLe)
      (r322AnalyticPredecessorVertex_lt_left
        ctx.state ctx.step ctx.bounds.1)

/-- The last point in the canonical increasing block enumeration is the
selected right endpoint. -/
theorem blockOrderIso_last :
    (ctx.blockOrderIso
      (primitiveLast
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder)).1 =
      ctx.step.1.2 := by
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      ctx.pairing ctx.step ctx.step_mem_schedule
  let rightInBlock : ctx.step.2 :=
    ⟨ctx.step.1.2, haligned.2.1⟩
  obtain ⟨j, hj⟩ :=
    ctx.blockOrderIso.surjective rightInBlock
  have hjlast :
      j ≤
        primitiveLast
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder :=
    by
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

/-- Ambient slots of the internal chain edges in standard block order. -/
def internalEdgesFinset : Finset (Fin (2 * q - 1)) :=
  Finset.univ.image ctx.internalEdge

theorem internalEdge_injective :
    Function.Injective ctx.internalEdge := by
  intro i j hij
  have hleft :
      ctx.internalLeftVertex i =
        ctx.internalLeftVertex j := by
    apply Fin.ext
    simpa [internalEdge] using congrArg Fin.val hij
  have hindex :
      (⟨i.val, by
          have hi := i.isLt
          have hn := ctx.one_le_blockOrder
          omega⟩ :
        Fin (2 * residualBlockOrder ctx.step.2)) =
      ⟨j.val, by
          have hj := j.isLt
          have hn := ctx.one_le_blockOrder
          omega⟩ := by
    apply ctx.blockOrderIso.injective
    exact Subtype.ext hleft
  apply Fin.ext
  simpa using congrArg Fin.val hindex

theorem internalEdgesFinset_subset_blockEdges :
    ctx.internalEdgesFinset ⊆ ctx.blockEdges := by
  intro edge hedge
  obtain ⟨j, _hj, rfl⟩ :=
    Finset.mem_image.mp hedge
  rw [ctx.mem_blockEdges_iff]
  exact
    (ctx.blockOrderIso
      ⟨j.val, by
        have hj := j.isLt
        have hn := ctx.one_le_blockOrder
        omega⟩).2

theorem outgoingEdge_mem_blockEdges :
    ctx.outgoingEdge ∈ ctx.blockEdges := by
  rw [ctx.mem_blockEdges_iff]
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      ctx.pairing ctx.step ctx.step_mem_schedule
  simpa only [outgoingEdge, r322AnalyticOutgoingEdge,
    r322AnalyticEdgeLeftVertex] using haligned.2.1

theorem outgoingEdge_not_mem_internalEdgesFinset :
    ctx.outgoingEdge ∉ ctx.internalEdgesFinset := by
  intro hout
  obtain ⟨j, _hj, hj⟩ :=
    Finset.mem_image.mp hout
  have hvertex :
      ctx.internalLeftVertex j = ctx.step.1.2 := by
    apply Fin.ext
    have hval := congrArg Fin.val hj.symm
    simpa only [internalEdge, outgoingEdge,
      r322AnalyticOutgoingEdge] using hval.symm
  have hindex :
      (⟨j.val, by
          have hjlt := j.isLt
          have hn := ctx.one_le_blockOrder
          omega⟩ :
        Fin (2 * residualBlockOrder ctx.step.2)) =
      primitiveLast
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder := by
    apply ctx.blockOrderIso.injective
    apply Subtype.ext
    rw [ctx.blockOrderIso_last]
    exact hvertex
  have hval := congrArg Fin.val hindex
  have hjlt := j.isLt
  have hval' :
      j.val =
        2 * residualBlockOrder ctx.step.2 - 1 := by
    simpa only [primitiveLast] using hval
  omega

theorem card_blockEdges :
    ctx.blockEdges.card =
      2 * residualBlockOrder ctx.step.2 := by
  rw [blockEdges,
    Finset.card_image_of_injective _ ctx.blockEdge_injective,
    Finset.card_attach]
  exact
    Nat.two_mul_div_two_of_even
      (residualBlock_card_even
        ctx.pairing ctx.step.2 ctx.blockFullyPaired) |>.symm

theorem card_internalEdgesFinset :
    ctx.internalEdgesFinset.card =
      2 * residualBlockOrder ctx.step.2 - 1 := by
  rw [internalEdgesFinset,
    Finset.card_image_of_injective _ ctx.internalEdge_injective,
    Finset.card_univ, Fintype.card_fin]

/-- The deleted block slots split into its internal chain slots and its
outgoing right-endpoint slot. -/
theorem internalEdgesFinset_union_outgoing :
    ctx.internalEdgesFinset ∪ {ctx.outgoingEdge} =
      ctx.blockEdges := by
  apply Finset.eq_of_subset_of_card_le
  · apply Finset.union_subset
    · exact ctx.internalEdgesFinset_subset_blockEdges
    · simpa only [Finset.singleton_subset_iff] using
        ctx.outgoingEdge_mem_blockEdges
  · rw [ctx.card_blockEdges,
      Finset.card_union_of_disjoint]
    · rw [ctx.card_internalEdgesFinset,
        Finset.card_singleton]
      have hn := ctx.one_le_blockOrder
      omega
    · exact Finset.disjoint_singleton_right.mpr
        ctx.outgoingEdge_not_mem_internalEdgesFinset

/-- One proper state update removes exactly the edge slots based at the
vertices of its concrete block. -/
theorem activeEdges_nextState
    (ρ : SmoothCutoff) (lam ε : ℝ) :
    r322AnalyticActiveEdges (ctx.nextState ρ lam ε) =
      r322AnalyticActiveEdges ctx.state \ ctx.blockEdges := by
  ext edge
  rw [mem_r322AnalyticActiveEdges,
    Finset.mem_sdiff, mem_r322AnalyticActiveEdges,
    ctx.mem_blockEdges_iff]
  rw [nextState, R322AnalyticEdgeState.updateProper_active]
  exact Finset.mem_sdiff

/-! ## Exact product update on the active carrier -/

/-- Product of the numerical edge scales which remain visible on a sparse
carrier. -/
def activeEdgeScaleProduct
    (scale : Fin (2 * q - 1) → ℝ) : ℝ :=
  ∏ edge ∈ r322AnalyticActiveEdges ctx.state, scale edge

/-- Product of the scales based at the vertices deleted by this block. -/
def blockEdgeScaleProduct
    (scale : Fin (2 * q - 1) → ℝ) : ℝ :=
  ∏ edge ∈ ctx.blockEdges, scale edge

/-- The concrete internal-edge image has exactly the primitive certificate's
heterogeneous scale product. -/
theorem internalEdgesFinset_scaleProduct
    (scale : Fin (2 * q - 1) → ℝ) :
    (∏ edge ∈ ctx.internalEdgesFinset, scale edge) =
      r322AnalyticInternalEdgeScaleProduct ctx scale := by
  unfold internalEdgesFinset
    r322AnalyticInternalEdgeScaleProduct
  exact
    Finset.prod_image
      ctx.internalEdge_injective.injOn

/-- The complete deleted-block budget is the actual primitive internal
product times the one outgoing scale which the analytic collapse leaves as a
free Green factor. -/
theorem blockEdgeScaleProduct_eq_internal_mul_outgoing
    (scale : Fin (2 * q - 1) → ℝ) :
    ctx.blockEdgeScaleProduct scale =
      r322AnalyticInternalEdgeScaleProduct ctx scale *
        scale ctx.outgoingEdge := by
  unfold blockEdgeScaleProduct
  rw [← ctx.internalEdgesFinset_union_outgoing,
    Finset.prod_union]
  · rw [ctx.internalEdgesFinset_scaleProduct,
      Finset.prod_singleton]
  · exact Finset.disjoint_singleton_right.mpr
      ctx.outgoingEdge_not_mem_internalEdgesFinset

/-- Budget-level update which also absorbs the outgoing block-edge scale.
The analytic update absorbs all other block edges; the outgoing free Green
factor is inserted here only in the numerical majorant. -/
def budgetUpdatedEdgeScale
    (scale : Fin (2 * q - 1) → ℝ)
    (C lam K : ℝ) :
    Fin (2 * q - 1) → ℝ :=
  Function.update scale ctx.predecessorEdge
    (scale ctx.predecessorEdge *
      ctx.blockEdgeScaleProduct scale *
      (C * lam) ^ (2 * residualBlockOrder ctx.step.2) * K)

@[simp]
theorem budgetUpdatedEdgeScale_predecessor
    (scale : Fin (2 * q - 1) → ℝ)
    (C lam K : ℝ) :
    ctx.budgetUpdatedEdgeScale scale C lam K
        ctx.predecessorEdge =
      scale ctx.predecessorEdge *
        ctx.blockEdgeScaleProduct scale *
        (C * lam) ^ (2 * residualBlockOrder ctx.step.2) * K := by
  simp [budgetUpdatedEdgeScale]

theorem budgetUpdatedEdgeScale_of_ne
    (scale : Fin (2 * q - 1) → ℝ)
    (C lam K : ℝ) (edge : Fin (2 * q - 1))
    (hne : edge ≠ ctx.predecessorEdge) :
    ctx.budgetUpdatedEdgeScale scale C lam K edge =
      scale edge := by
  simp [budgetUpdatedEdgeScale, hne]

/-- At the updated predecessor the budget scale is exactly the proved
analytic scale times the outgoing scale; this is an identity, not an
estimate. -/
theorem budgetUpdatedEdgeScale_predecessor_eq_actual_mul_outgoing
    (scale : Fin (2 * q - 1) → ℝ)
    (C lam K : ℝ) :
    ctx.budgetUpdatedEdgeScale scale C lam K
        ctx.predecessorEdge =
      r322AnalyticUpdatedEdgeScale ctx scale
          (r322AnalyticInternalEdgeScaleProduct ctx scale)
          C lam K ctx.predecessorEdge *
        scale ctx.outgoingEdge := by
  rw [ctx.budgetUpdatedEdgeScale_predecessor,
    r322AnalyticUpdatedEdgeScale_predecessor,
    ctx.blockEdgeScaleProduct_eq_internal_mul_outgoing]
  ring

/-- Because a proper block is a subset of the current carrier and its
predecessor lies outside it, absorbing the complete block product at that
predecessor preserves the old active product up to exactly the one new
analytic factor. -/
theorem activeEdgeScaleProduct_budgetUpdate
    (ρ : SmoothCutoff) (ε C lam K : ℝ)
    (scale : Fin (2 * q - 1) → ℝ) :
    ∏ edge ∈
        r322AnalyticActiveEdges (ctx.nextState ρ lam ε),
      ctx.budgetUpdatedEdgeScale scale C lam K edge =
      ctx.activeEdgeScaleProduct scale *
        (C * lam) ^ (2 * residualBlockOrder ctx.step.2) * K := by
  let oldActive :=
    r322AnalyticActiveEdges ctx.state
  let newActive :=
    oldActive \ ctx.blockEdges
  have hpredNew :
      ctx.predecessorEdge ∈ newActive := by
    exact Finset.mem_sdiff.mpr
      ⟨ctx.predecessorEdge_mem_activeEdges,
        ctx.predecessorEdge_not_mem_blockEdges⟩
  have hblock :
      ctx.blockEdges ⊆ oldActive :=
    ctx.blockEdges_subset_activeEdges
  have hpartition :
      (∏ edge ∈ newActive, scale edge) *
          ctx.blockEdgeScaleProduct scale =
        ∏ edge ∈ oldActive, scale edge := by
    simpa only [newActive, blockEdgeScaleProduct,
      mul_comm] using
      (Finset.prod_sdiff hblock (f := scale))
  rw [ctx.activeEdges_nextState ρ lam ε]
  change
    (∏ edge ∈ newActive,
        ctx.budgetUpdatedEdgeScale scale C lam K edge) =
      (∏ edge ∈ oldActive, scale edge) *
        (C * lam) ^ (2 * residualBlockOrder ctx.step.2) * K
  simp only [budgetUpdatedEdgeScale]
  rw [Finset.prod_update_of_mem hpredNew]
  have hsplit :=
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
      hpredNew scale
  rw [← hpartition]
  rw [hsplit]
  ring

/-- A slotwise edge certificate may be enlarged along a pointwise scale
majorization. -/
theorem edgeCertificate_of_pointwise_scale_le
    {state : R322AnalyticEdgeState q hq}
    {scale budget : Fin (2 * q - 1) → ℝ}
    (hcert : R322AnalyticEdgeCertificate state scale)
    (hle : ∀ edge, scale edge ≤ budget edge) :
    R322AnalyticEdgeCertificate state budget := by
  refine ⟨?_, hcert.memE, ?_⟩
  · intro edge
    exact lt_of_lt_of_le (hcert.scale_pos edge) (hle edge)
  · intro edge z hz
    exact (hcert.bound edge z hz).trans
      (mul_le_mul_of_nonneg_right
        (hle edge) (invSqKer_nonneg z))

/-- Honest promotion from the scale delivered by the analytic one-block
estimate to the complete deleted-block budget.  The only extra numerical
premise is the explicit outgoing-scale normalization `1 ≤ scale outgoing`;
without it the enlarged-budget conclusion is false in general. -/
theorem
    edgeCertificate_to_budgetUpdatedEdgeScale
    (ρ : SmoothCutoff) (lam ε C K : ℝ)
    (scale : Fin (2 * q - 1) → ℝ)
    (hcert :
      R322AnalyticEdgeCertificate
        (ctx.nextState ρ lam ε)
        (r322AnalyticUpdatedEdgeScale ctx scale
          (r322AnalyticInternalEdgeScaleProduct ctx scale)
          C lam K))
    (hout : 1 ≤ scale ctx.outgoingEdge) :
    R322AnalyticEdgeCertificate
      (ctx.nextState ρ lam ε)
      (ctx.budgetUpdatedEdgeScale scale C lam K) := by
  apply edgeCertificate_of_pointwise_scale_le hcert
  intro edge
  by_cases hedge : edge = ctx.predecessorEdge
  · subst edge
    rw [ctx.budgetUpdatedEdgeScale_predecessor_eq_actual_mul_outgoing]
    have hnonneg :
        0 ≤
          r322AnalyticUpdatedEdgeScale ctx scale
            (r322AnalyticInternalEdgeScaleProduct ctx scale)
            C lam K ctx.predecessorEdge :=
      (hcert.scale_pos ctx.predecessorEdge).le
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hout hnonneg)
  · rw [
      r322AnalyticUpdatedEdgeScale_of_ne
        ctx scale
          (r322AnalyticInternalEdgeScaleProduct ctx scale)
          C lam K edge hedge,
      ctx.budgetUpdatedEdgeScale_of_ne
        scale C lam K edge hedge]

end R322AnalyticProperStepContext

end

end Anderson4D
