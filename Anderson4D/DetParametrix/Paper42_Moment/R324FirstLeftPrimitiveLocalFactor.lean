import Anderson4D.DetParametrix.Paper42_Moment.R324FirstLeftCarrierEdges
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticProperStepFubini
/-! # Primitive local-factor form of the first-left production chain -/
set_option warningAsError true
set_option autoImplicit false
namespace Anderson4D
noncomputable section
open scoped BigOperators

theorem r324FirstLeft_one_le_blockOrder
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b) :
    1 ≤ residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft) := by
  apply one_le_residualBlockOrder_of_nonempty
    e₀.1 _ (selectRel_isRelFullyPaired
      e₀.1 Finset.univ hleft).isFullyPairedOn
  exact ⟨(selectRel e₀.1 Finset.univ hleft).1,
    mem_relIcc.mpr
      ⟨Finset.mem_univ _, le_rfl,
        (selectRel_isRelFullyPaired
          e₀.1 Finset.univ hleft).le⟩⟩

def r324FirstLeftCarrierTuple
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (xt : Fin (m + 2) → T4) :
    Fin (2 * residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4 :=
  fun i => xt ⟨
    (selectRel e₀.1 Finset.univ hleft).1.val + 1 + i.val, by
      have hi := i.isLt
      have hs := r324FirstLeft_endpoint_span e₀ hleft
      have hb := (selectRel e₀.1 Finset.univ hleft).2.isLt
      omega⟩

def r324FirstLeftInternalEdge
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (j : Fin (2 * residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft) - 1)) :
    Fin (m + 1) :=
  ⟨(selectRel e₀.1 Finset.univ hleft).1.val + 1 + j.val, by
    have hj := j.isLt
    have hs := r324FirstLeft_endpoint_span e₀ hleft
    have hb := (selectRel e₀.1 Finset.univ hleft).2.isLt
    omega⟩

def r324ProductionGreenEdgeFactor
    {m : ℕ} (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) (edge : Fin (m + 1)) : ℂ :=
  originalGreenEdge xt edge -
    extractedShortcutGreenEdge κ xt edge

def r324FirstLeftInternalVertexLeft
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (j : Fin (2 * residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft) - 1)) :
    Fin (2 * residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft)) :=
  ⟨j.val, by
    have hj := j.isLt
    have hn := r324FirstLeft_one_le_blockOrder e₀ hleft
    omega⟩

def r324FirstLeftInternalVertexRight
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (j : Fin (2 * residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft) - 1)) :
    Fin (2 * residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft)) :=
  ⟨j.val + 1, by
    have hj := j.isLt
    have hn := r324FirstLeft_one_le_blockOrder e₀ hleft
    omega⟩

@[simp]
theorem touchingEdge_zero_eq_predecessor
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b) :
    r324FirstLeftTouchingEdge e₀ hleft 0 =
      r324FirstLeftPredecessorEdge e₀ hleft := by
  apply Fin.ext
  rfl

theorem r324FirstLeftInternalEdge_not_extracted_reference
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (j : Fin (2 * residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft) - 1)) :
    r324FirstLeftInternalEdge e₀ hleft j ∉
      extractedRightEdges e₀.1 := by
  intro hedge
  obtain ⟨p, hp, hpedge⟩ :=
    exists_extractedPairOfRightEdge e₀.1
      (r324FirstLeftInternalEdge e₀ hleft j) hedge
  have hm :
      m - 1 + 1 = m :=
    pred_add_one_eq_of_exists_relFullyPaired hleft
  unfold extract at hp
  have hp' : p ∈ extractAux e₀.1 (m - 1 + 1) Finset.univ := by
    simpa only [hm] using hp
  rw [extractAux_succ_pos (m - 1) hleft] at hp'
  rcases List.mem_cons.mp hp' with hp | hp
  · subst p
    have hv := congrArg Fin.val hpedge
    simp only [extractedRightEdge_val,
      r324FirstLeftInternalEdge] at hv
    have hj := j.isLt
    have hs := r324FirstLeft_endpoint_span e₀ hleft
    have hab := (selectRel_isRelFullyPaired
      e₀.1 Finset.univ hleft).le
    omega
  · have hpRel :=
      extractAux_mem_isRelFullyPaired e₀.1 (m - 1)
        ((Finset.univ : Finset (Fin m)) \
          selectedExtractionBlock e₀.1 Finset.univ hleft)
        p hp
    have hpNot :
        p.2 ∉ selectedExtractionBlock
          e₀.1 Finset.univ hleft :=
      (Finset.mem_sdiff.mp hpRel.right_mem).2
    apply hpNot
    rw [r324FirstLeft_selectedBlock_eq_Icc]
    apply Finset.mem_Icc.mpr
    have hv := congrArg Fin.val hpedge
    simp only [extractedRightEdge_val,
      r324FirstLeftInternalEdge] at hv
    have hj := j.isLt
    have hs := r324FirstLeft_endpoint_span e₀ hleft
    have hab := (selectRel_isRelFullyPaired
      e₀.1 Finset.univ hleft).le
    constructor <;> omega

theorem r324FirstLeftInternalEdge_not_extracted
    {m : ℕ} (κ : PartialPairing (Fin m))
    (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (hsig : reductionEndpointSignature κ =
      reductionEndpointSignature e₀.1)
    (j : Fin (2 * residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft) - 1)) :
    r324FirstLeftInternalEdge e₀ hleft j ∉
      extractedRightEdges κ := by
  rw [extractedRightEdges_eq_of_extract_perm κ e₀.1
    (extract_perm_of_reductionEndpointSignature_eq κ e₀.1 hsig)]
  exact r324FirstLeftInternalEdge_not_extracted_reference
    e₀ hleft j

theorem productionInternalFactor_eq_primitiveEdge
    {m : ℕ} (κ : PartialPairing (Fin m))
    (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (hsig : reductionEndpointSignature κ =
      reductionEndpointSignature e₀.1)
    (xt : Fin (m + 2) → T4)
    (j : Fin (2 * residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft) - 1)) :
    r324ProductionGreenEdgeFactor κ xt
        (r324FirstLeftInternalEdge e₀ hleft j) =
      (greenFn
        (r324FirstLeftCarrierTuple e₀ hleft xt
            (r324FirstLeftInternalVertexLeft e₀ hleft j) -
          r324FirstLeftCarrierTuple e₀ hleft xt
            (r324FirstLeftInternalVertexRight e₀ hleft j)) : ℂ) := by
  have hnot :=
    r324FirstLeftInternalEdge_not_extracted
      κ e₀ hleft hsig j
  unfold r324ProductionGreenEdgeFactor
    extractedShortcutGreenEdge originalGreenEdge
  rw [dif_neg hnot, sub_zero]
  rfl

theorem r324FirstLeftTouchingGreenProduct_eq_primitiveLocal
    {m : ℕ} (κ : PartialPairing (Fin m))
    (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (hsig : reductionEndpointSignature κ =
      reductionEndpointSignature e₀.1)
    (xt : Fin (m + 2) → T4) :
    r324FirstLeftTouchingGreenProduct κ e₀ hleft xt =
      r324ProductionGreenEdgeFactor κ xt
          (r324FirstLeftPredecessorEdge e₀ hleft) *
        ((primitiveChainProduct
          (residualBlockOrder
            (selectedExtractionBlock e₀.1 Finset.univ hleft))
          (r324FirstLeft_one_le_blockOrder e₀ hleft)
          (fun _ => greenFn)
          (r324FirstLeftCarrierTuple e₀ hleft xt) : ℝ) : ℂ) *
        r324ProductionGreenEdgeFactor κ xt
          (r324FirstLeftOutgoingEdge e₀ hleft) := by
  rw [r324FirstLeftTouchingGreenProduct_eq_edgeEnumeration]
  simp only [r324ProductionGreenEdgeFactor]
  rw [Fin.prod_univ_succ]
  let g : Fin (2 * residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft)) → ℂ :=
    fun k =>
      r324ProductionGreenEdgeFactor κ xt
        (r324FirstLeftTouchingEdge e₀ hleft k.succ)
  change
    r324ProductionGreenEdgeFactor κ xt
        (r324FirstLeftTouchingEdge e₀ hleft 0) *
      (∏ k, g k) = _
  let n := residualBlockOrder
    (selectedExtractionBlock e₀.1 Finset.univ hleft)
  have hn : 1 ≤ n := r324FirstLeft_one_le_blockOrder e₀ hleft
  have hcard : 2 * n - 1 + 1 = 2 * n := by omega
  let e : Fin (2 * n - 1 + 1) ≃ Fin (2 * n) :=
    finCongr hcard
  have hg :
      (∏ k : Fin (2 * n), g k) =
        ∏ j : Fin (2 * n - 1 + 1), g (e j) :=
    (Equiv.prod_comp e g).symm
  rw [hg, Fin.prod_univ_castSucc]
  simp only [touchingEdge_zero_eq_predecessor]
  have hout :
      r324FirstLeftTouchingEdge e₀ hleft
          (e (Fin.last (2 * n - 1))).succ =
        r324FirstLeftOutgoingEdge e₀ hleft := by
    apply Fin.ext
    have hs := r324FirstLeft_endpoint_span e₀ hleft
    have hab := (selectRel_isRelFullyPaired
      e₀.1 Finset.univ hleft).le
    change
      (selectRel e₀.1 Finset.univ hleft).1.val +
          ((2 * n - 1) + 1) =
        (selectRel e₀.1 Finset.univ hleft).2.val + 1
    dsimp only [n]
    omega
  have hgout :
      g (e (Fin.last (2 * n - 1))) =
        r324ProductionGreenEdgeFactor κ xt
          (r324FirstLeftOutgoingEdge e₀ hleft) := by
    change
      r324ProductionGreenEdgeFactor κ xt
          (r324FirstLeftTouchingEdge e₀ hleft
            (e (Fin.last (2 * n - 1))).succ) =
        _
    rw [hout]
  rw [hgout]
  rw [← mul_assoc]
  congr 1
  congr 1
  unfold primitiveChainProduct
  push_cast
  apply Finset.prod_congr rfl
  intro j _hj
  have hedge :
      r324FirstLeftTouchingEdge e₀ hleft
          (e j.castSucc).succ =
        r324FirstLeftInternalEdge e₀ hleft j := by
    apply Fin.ext
    change
      (selectRel e₀.1 Finset.univ hleft).1.val +
          (j.val + 1) =
        (selectRel e₀.1 Finset.univ hleft).1.val + 1 + j.val
    omega
  change
    r324ProductionGreenEdgeFactor κ xt
        (r324FirstLeftTouchingEdge e₀ hleft
          (e j.castSucc).succ) = _
  rw [hedge]
  simpa only [primitiveEdgeLeft, primitiveEdgeRight,
    r324FirstLeftInternalVertexLeft,
    r324FirstLeftInternalVertexRight] using
      productionInternalFactor_eq_primitiveEdge
        κ e₀ hleft hsig xt j

theorem r324FirstLeftReconstruct_touchingGreenProduct_eq_primitiveLocal
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (κB : R324FirstLeftBlockCoordinate e₀ hleft)
    (xt : Fin (m + 2) → T4) :
    let κ := (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
    r324FirstLeftTouchingGreenProduct κ e₀ hleft xt =
      r324ProductionGreenEdgeFactor κ xt
          (r324FirstLeftPredecessorEdge e₀ hleft) *
        ((primitiveChainProduct
          (residualBlockOrder
            (selectedExtractionBlock e₀.1 Finset.univ hleft))
          (r324FirstLeft_one_le_blockOrder e₀ hleft)
          (fun _ => greenFn)
          (r324FirstLeftCarrierTuple e₀ hleft xt) : ℝ) : ℂ) *
        r324ProductionGreenEdgeFactor κ xt
          (r324FirstLeftOutgoingEdge e₀ hleft) := by
  dsimp only
  apply r324FirstLeftTouchingGreenProduct_eq_primitiveLocal
  rw [r324FirstLeftReconstruct_leftPairing]
  exact
    ((reductionEndpointFiberEquivBlockComplement
      e₀.1 hleft).symm (κB, ω.1)).2

end
end Anderson4D
