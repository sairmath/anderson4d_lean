import Anderson4D.DetParametrix.Paper42_Moment.R324FirstLeftInitialPhysicalCollapse

/-!
# Complement independence and the first physical R-324 collapse

This module keeps the genuine first-left physical fibre while proving that
the factor exposed outside its selected block is a function of the
complementary coordinates alone.  It then reindexes the selected coordinate,
translates it, and invokes the honest complex outer-Fubini collapse.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Reading reconstructed complementary coordinates -/

@[simp]
theorem r324FirstLeftPhysicalReconstruct_complement
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4)
    (t :
      Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4)
    (i : {i : Fin (2 * m) //
      ¬r324FirstLeftSelected e₀ hleft i}) :
    r324FirstLeftPhysicalReconstruct e₀ hleft vC t i.1 =
      vC i := by
  unfold r324FirstLeftPhysicalReconstruct
  let split :=
    MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Fin (2 * m) => T4)
      (r324FirstLeftSelected e₀ hleft)
  have hsplit :=
    congrArg (fun p => p.2 i)
      (split.apply_symm_apply
        (r324FirstLeftSelectedTupleMeasurableEquiv
          e₀ hleft t, vC))
  exact hsplit

theorem r324FirstLeftPhysicalReconstruct_eq_of_not_selected
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4)
    (t t' :
      Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4)
    (i : Fin (2 * m))
    (hi : ¬r324FirstLeftSelected e₀ hleft i) :
    r324FirstLeftPhysicalReconstruct e₀ hleft vC t i =
      r324FirstLeftPhysicalReconstruct e₀ hleft vC t' i := by
  let iC :
      {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i} :=
    ⟨i, hi⟩
  rw [r324FirstLeftPhysicalReconstruct_complement
    e₀ hleft vC t iC]
  rw [r324FirstLeftPhysicalReconstruct_complement
    e₀ hleft vC t' iC]

theorem leftMomentIndex_not_selected_of_not_mem
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (i : Fin m)
    (hi :
      i ∉ selectedExtractionBlock
        e₀.1 Finset.univ hleft) :
    ¬r324FirstLeftSelected e₀ hleft
      (leftMomentIndex i) := by
  intro hselected
  unfold r324FirstLeftSelected at hselected
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hselected
  apply hi
  exact (leftMomentIndex_injective hji).symm ▸ hj

theorem rightMomentIndex_not_firstLeftSelected
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (i : Fin m) :
    ¬r324FirstLeftSelected e₀ hleft
      (rightMomentIndex i) := by
  intro hselected
  unfold r324FirstLeftSelected at hselected
  obtain ⟨j, _hj, hji⟩ := Finset.mem_image.mp hselected
  have hval := congrArg Fin.val hji
  simp only [leftMomentIndex, rightMomentIndex] at hval
  have hi := i.isLt
  omega

/-! ## Exterior production-chain reads -/

theorem assemble_leftPhysicalReconstruct_eq_of_not_shifted
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4)
    (t t' :
      Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4)
    (x y : T4) (j : Fin (m + 2))
    (hj :
      j ∉ r324FirstLeftShiftedBlock e₀ hleft) :
    assemble x y
        (r324LeftPhysicalTuple
          (r324FirstLeftPhysicalReconstruct
            e₀ hleft vC t)) j =
      assemble x y
        (r324LeftPhysicalTuple
          (r324FirstLeftPhysicalReconstruct
            e₀ hleft vC t')) j := by
  by_cases hzero : j.val = 0
  · simp only [assemble, hzero, ↓reduceDIte]
  by_cases hlast : j.val = m + 1
  · simp only [assemble, hlast, ↓reduceDIte]
  let i : Fin m :=
    ⟨j.val - 1, by
      have hjlt := j.isLt
      omega⟩
  have hvar : varIdx i = j := by
    apply Fin.ext
    dsimp only [i]
    simp only [varIdx_val]
    omega
  have hiB :
      i ∉ selectedExtractionBlock
        e₀.1 Finset.univ hleft := by
    intro hi
    apply hj
    rw [← hvar]
    exact
      (varIdx_mem_r324FirstLeftShiftedBlock_iff
        e₀ hleft i).2 hi
  have hcoord :=
    r324FirstLeftPhysicalReconstruct_eq_of_not_selected
      e₀ hleft vC t t' (leftMomentIndex i)
      (leftMomentIndex_not_selected_of_not_mem
        e₀ hleft i hiB)
  unfold assemble r324LeftPhysicalTuple
  simp only [dif_neg hzero, dif_neg hlast]
  simpa only [i] using hcoord

theorem r324FirstLeft_extractedShortcutParent_not_shifted
    {m : ℕ} (κ : PartialPairing (Fin m))
    (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (hsig :
      reductionEndpointSignature κ =
        reductionEndpointSignature e₀.1)
    (edge : Fin (m + 1))
    (hi : edge ∈ extractedRightEdges κ)
    (hout :
      R324FirstLeftChainEdgeOutside e₀ hleft edge) :
    (Fin.castLE (by omega)
        (extractedShortcutParent κ edge hi) :
      Fin (m + 2)) ∉
        r324FirstLeftShiftedBlock e₀ hleft := by
  let p := extractedPairOfRightEdge κ edge hi
  have hpκ : p ∈ extract κ :=
    extractedPairOfRightEdge_mem κ edge hi
  have hedge : extractedRightEdge p = edge :=
    extractedRightEdge_extractedPairOfRightEdge κ edge hi
  have hextract :
      extract κ = extract e₀.1 :=
    extract_eq_of_reductionEndpointSignature_eq
      κ e₀.1 hsig
  have hp : p ∈ extract e₀.1 := by
    rw [← hextract]
    exact hpκ
  have hm :
      m - 1 + 1 = m :=
    pred_add_one_eq_of_exists_relFullyPaired hleft
  unfold extract at hp
  have hp' :
      p ∈ extractAux e₀.1 (m - 1 + 1) Finset.univ := by
    simpa only [hm] using hp
  rw [extractAux_succ_pos (m - 1) hleft] at hp'
  rcases List.mem_cons.mp hp' with hpFirst | hpLater
  · have hpEq :
        p = selectRel e₀.1 Finset.univ hleft :=
      hpFirst
    have hright :
        (selectRel e₀.1 Finset.univ hleft).2 ∈
          selectedExtractionBlock
            e₀.1 Finset.univ hleft := by
      exact
        (selectRel_isRelFullyPaired
          e₀.1 Finset.univ hleft).right_mem_relIcc
    have hshift :
        varIdx (selectRel e₀.1 Finset.univ hleft).2 ∈
          r324FirstLeftShiftedBlock e₀ hleft :=
      (varIdx_mem_r324FirstLeftShiftedBlock_iff
        e₀ hleft _).2 hright
    apply False.elim
    apply hout.1
    rw [← hedge, hpEq]
    simpa only [extractedRightEdge_castSucc] using hshift
  · have hpRel :=
      extractAux_mem_isRelFullyPaired e₀.1 (m - 1)
        ((Finset.univ : Finset (Fin m)) \
          selectedExtractionBlock e₀.1 Finset.univ hleft)
        p hpLater
    have hpNot :
        p.1 ∉ selectedExtractionBlock
          e₀.1 Finset.univ hleft :=
      (Finset.mem_sdiff.mp hpRel.left_mem).2
    have hparent :
        (Fin.castLE (by omega)
            (extractedShortcutParent κ edge hi) :
          Fin (m + 2)) =
          varIdx p.1 := by
      apply Fin.ext
      unfold extractedShortcutParent
      rfl
    rw [hparent]
    exact
      (varIdx_mem_r324FirstLeftShiftedBlock_iff
        e₀ hleft p.1).not.mpr hpNot

theorem r324FirstLeftExteriorGreenProduct_physicalReconstruct_eq
    {m : ℕ} (κ : PartialPairing (Fin m))
    (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (hsig :
      reductionEndpointSignature κ =
        reductionEndpointSignature e₀.1)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4)
    (t t' :
      Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4)
    (x y : T4) :
    r324FirstLeftExteriorGreenProduct κ e₀ hleft
        (assemble x y
          (r324LeftPhysicalTuple
            (r324FirstLeftPhysicalReconstruct
              e₀ hleft vC t))) =
      r324FirstLeftExteriorGreenProduct κ e₀ hleft
        (assemble x y
          (r324LeftPhysicalTuple
            (r324FirstLeftPhysicalReconstruct
              e₀ hleft vC t'))) := by
  unfold r324FirstLeftExteriorGreenProduct
  apply Finset.prod_congr rfl
  intro edge _hedge
  by_cases hout :
      R324FirstLeftChainEdgeOutside e₀ hleft edge
  · simp only [hout, if_true]
    have hparent :=
      assemble_leftPhysicalReconstruct_eq_of_not_shifted
        e₀ hleft vC t t' x y edge.castSucc hout.1
    have hchild :=
      assemble_leftPhysicalReconstruct_eq_of_not_shifted
        e₀ hleft vC t t' x y edge.succ hout.2
    have horiginal :
        originalGreenEdge
            (assemble x y
              (r324LeftPhysicalTuple
                (r324FirstLeftPhysicalReconstruct
                  e₀ hleft vC t))) edge =
          originalGreenEdge
            (assemble x y
              (r324LeftPhysicalTuple
                (r324FirstLeftPhysicalReconstruct
                  e₀ hleft vC t'))) edge := by
      unfold originalGreenEdge
      rw [hparent, hchild]
    have hshortcut :
        extractedShortcutGreenEdge κ
            (assemble x y
              (r324LeftPhysicalTuple
                (r324FirstLeftPhysicalReconstruct
                  e₀ hleft vC t))) edge =
          extractedShortcutGreenEdge κ
            (assemble x y
              (r324LeftPhysicalTuple
                (r324FirstLeftPhysicalReconstruct
                  e₀ hleft vC t'))) edge := by
      unfold extractedShortcutGreenEdge
      split_ifs with hi
      · have hshortcutParent :=
          assemble_leftPhysicalReconstruct_eq_of_not_shifted
            e₀ hleft vC t t' x y
            (Fin.castLE (by omega)
              (extractedShortcutParent κ edge hi))
            (r324FirstLeft_extractedShortcutParent_not_shifted
              κ e₀ hleft hsig edge hi hout)
        rw [hshortcutParent, hchild]
      · rfl
    rw [horiginal, hshortcut]
  · simp only [hout, if_false]

theorem r324FirstLeftPredecessorVertex_not_shifted
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :
    (r324FirstLeftPredecessorEdge e₀ hleft).castSucc ∉
      r324FirstLeftShiftedBlock e₀ hleft := by
  rw [mem_r324FirstLeftShiftedBlock_iff_bounds]
  simp only [r324FirstLeftPredecessorEdge, Fin.castSucc_mk]
  omega

theorem r324FirstLeftSuccessorVertex_not_shifted
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :
    (r324FirstLeftOutgoingEdge e₀ hleft).succ ∉
      r324FirstLeftShiftedBlock e₀ hleft := by
  rw [mem_r324FirstLeftShiftedBlock_iff_bounds]
  simp only [r324FirstLeftOutgoingEdge,
    extractedRightEdge, Fin.succ_mk]
  omega

theorem r324FirstLeftPhysicalPredecessor_reconstruct_eq
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4)
    (t t' :
      Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4)
    (x y : T4) :
    r324FirstLeftPhysicalPredecessor e₀ hleft x y
        (r324FirstLeftPhysicalReconstruct e₀ hleft vC t) =
      r324FirstLeftPhysicalPredecessor e₀ hleft x y
        (r324FirstLeftPhysicalReconstruct e₀ hleft vC t') := by
  unfold r324FirstLeftPhysicalPredecessor
  exact
    assemble_leftPhysicalReconstruct_eq_of_not_shifted
      e₀ hleft vC t t' x y
      (r324FirstLeftPredecessorEdge e₀ hleft).castSucc
      (r324FirstLeftPredecessorVertex_not_shifted e₀ hleft)

theorem r324FirstLeftPhysicalSuccessor_reconstruct_eq
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4)
    (t t' :
      Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4)
    (x y : T4) :
    r324FirstLeftPhysicalSuccessor e₀ hleft x y
        (r324FirstLeftPhysicalReconstruct e₀ hleft vC t) =
      r324FirstLeftPhysicalSuccessor e₀ hleft x y
        (r324FirstLeftPhysicalReconstruct e₀ hleft vC t') := by
  unfold r324FirstLeftPhysicalSuccessor
  exact
    assemble_leftPhysicalReconstruct_eq_of_not_shifted
      e₀ hleft vC t t' x y
      (r324FirstLeftOutgoingEdge e₀ hleft).succ
      (r324FirstLeftSuccessorVertex_not_shifted e₀ hleft)

/-! ## Covariance factors on complementary coordinates -/

theorem pairingCovarianceProductOn_complement_physicalReconstruct_eq
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin m))
    (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (hfull :
      IsFullyPairedOn κ
        (selectedExtractionBlock
          e₀.1 Finset.univ hleft))
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4)
    (t t' :
      Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4) :
    pairingCovarianceProductOn ρ ε κ
        ((Finset.univ : Finset (Fin m)) \
          selectedExtractionBlock e₀.1 Finset.univ hleft)
        (fun i =>
          r324FirstLeftPhysicalReconstruct e₀ hleft vC t
            (leftMomentIndex i)) =
      pairingCovarianceProductOn ρ ε κ
        ((Finset.univ : Finset (Fin m)) \
          selectedExtractionBlock e₀.1 Finset.univ hleft)
        (fun i =>
          r324FirstLeftPhysicalReconstruct e₀ hleft vC t'
            (leftMomentIndex i)) := by
  unfold pairingCovarianceProductOn
  apply Finset.prod_congr rfl
  intro i hi
  have hiNot :
      i ∉ selectedExtractionBlock
        e₀.1 Finset.univ hleft :=
    (Finset.mem_sdiff.mp
      (Finset.mem_filter.mp hi).1).2
  have hκNot :
      κ i ∉ selectedExtractionBlock
        e₀.1 Finset.univ hleft :=
    hfull.apply_notMem hiNot
  change
    ρ.etaEpsT4 ε
        (r324FirstLeftPhysicalReconstruct e₀ hleft vC t
            (leftMomentIndex i) -
          r324FirstLeftPhysicalReconstruct e₀ hleft vC t
            (leftMomentIndex (κ i))) =
      ρ.etaEpsT4 ε
        (r324FirstLeftPhysicalReconstruct e₀ hleft vC t'
            (leftMomentIndex i) -
          r324FirstLeftPhysicalReconstruct e₀ hleft vC t'
            (leftMomentIndex (κ i)))
  rw [
    r324FirstLeftPhysicalReconstruct_eq_of_not_selected
      e₀ hleft vC t t' (leftMomentIndex i)
      (leftMomentIndex_not_selected_of_not_mem
        e₀ hleft i hiNot),
    r324FirstLeftPhysicalReconstruct_eq_of_not_selected
      e₀ hleft vC t t' (leftMomentIndex (κ i))
      (leftMomentIndex_not_selected_of_not_mem
        e₀ hleft (κ i) hκNot)]

theorem rightPhysicalTuple_reconstruct_eq
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4)
    (t t' :
      Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4) :
    (fun i : Fin m =>
        r324FirstLeftPhysicalReconstruct e₀ hleft vC t
          (rightMomentIndex i)) =
      fun i : Fin m =>
        r324FirstLeftPhysicalReconstruct e₀ hleft vC t'
          (rightMomentIndex i) := by
  funext i
  exact
    r324FirstLeftPhysicalReconstruct_eq_of_not_selected
      e₀ hleft vC t t' (rightMomentIndex i)
      (rightMomentIndex_not_firstLeftSelected e₀ hleft i)

theorem momentCrossCovarianceProduct_physicalReconstruct_eq
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (hfull :
      IsFullyPairedOn κp
        (selectedExtractionBlock
          e₀.1 Finset.univ hleft))
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4)
    (t t' :
      Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4) :
    momentCrossCovarianceProduct ρ ε m κp κm π
        (r324FirstLeftPhysicalReconstruct
          e₀ hleft vC t) =
      momentCrossCovarianceProduct ρ ε m κp κm π
        (r324FirstLeftPhysicalReconstruct
          e₀ hleft vC t') := by
  unfold momentCrossCovarianceProduct
  apply Finset.prod_congr rfl
  intro i _hi
  have hiNot :
      i.1 ∉ selectedExtractionBlock
        e₀.1 Finset.univ hleft := by
    intro hiB
    exact hfull.ne_of_mem hiB
      (PartialPairing.mem_singles.mp i.2)
  rw [
    r324FirstLeftPhysicalReconstruct_eq_of_not_selected
      e₀ hleft vC t t' (leftMomentIndex i.1)
      (leftMomentIndex_not_selected_of_not_mem
        e₀ hleft i.1 hiNot),
    r324FirstLeftPhysicalReconstruct_eq_of_not_selected
      e₀ hleft vC t t'
      (rightMomentIndex (π i).1)
      (rightMomentIndex_not_firstLeftSelected
        e₀ hleft (π i).1)]

theorem firstBlockReferenceEndpointFiber_isFullyPairedOn_selected
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (tail : List (R322ExtractionStep m))
    (hschedule :
      r322AnalyticSchedule e₀.1 =
        r324FirstLeftSelectedStep e₀ hleft :: tail) :
    IsFullyPairedOn
        (firstBlockReferenceEndpointFiber
          e₀.1 hleft ω.1).1
        (selectedExtractionBlock
          e₀.1 Finset.univ hleft) := by
  let ctx :=
    r324FirstLeftInitialStepContext e₀ hleft tail hschedule
  have hmem :
      selectedExtractionBlock e₀.1 Finset.univ hleft ∈
        extractionBlocks e₀.1 := by
    simpa only [ctx, r324FirstLeftInitialStepContext,
      r324FirstLeftSelectedStep_block] using
      ctx.block_mem_extractionBlocks
  apply extractionBlock_isFullyPairedOn_of_mem
  rw [extractionBlocks_eq_of_reductionEndpointSignature_eq
    (firstBlockReferenceEndpointFiber
      e₀.1 hleft ω.1).1 e₀.1
    (firstBlockReferenceEndpointFiber
      e₀.1 hleft ω.1).2]
  exact hmem

theorem r324FirstLeftInitialPhysicalOuterFactor_reconstruct_eq
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (α β : Z4) (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (tail : List (R322ExtractionStep m))
    (hschedule :
      r322AnalyticSchedule e₀.1 =
        r324FirstLeftSelectedStep e₀ hleft :: tail)
    (x y z w : T4)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4)
    (t t' :
      Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4) :
    r324FirstLeftInitialPhysicalOuterFactor
        ρ ε α β e₀ hleft ω x y z w
        (r324FirstLeftPhysicalReconstruct
          e₀ hleft vC t) =
      r324FirstLeftInitialPhysicalOuterFactor
        ρ ε α β e₀ hleft ω x y z w
        (r324FirstLeftPhysicalReconstruct
          e₀ hleft vC t') := by
  let κ₀ :=
    (firstBlockReferenceEndpointFiber e₀.1 hleft ω.1).1
  have hsig :
      reductionEndpointSignature κ₀ =
        reductionEndpointSignature e₀.1 :=
    (firstBlockReferenceEndpointFiber
      e₀.1 hleft ω.1).2
  have hfull :
      IsFullyPairedOn κ₀
        (selectedExtractionBlock
          e₀.1 Finset.univ hleft) :=
    firstBlockReferenceEndpointFiber_isFullyPairedOn_selected
      e₀ hleft ω tail hschedule
  have hright :=
    rightPhysicalTuple_reconstruct_eq
      e₀ hleft vC t t'
  unfold r324FirstLeftInitialPhysicalOuterFactor
  dsimp only [κ₀]
  rw [r324FirstLeftExteriorGreenProduct_physicalReconstruct_eq
    κ₀ e₀ hleft hsig vC t t' x y]
  rw [hright]
  rw [pairingCovarianceProductOn_complement_physicalReconstruct_eq
    ρ ε κ₀ e₀ hleft hfull vC t t']
  rw [momentCrossCovarianceProduct_physicalReconstruct_eq
    ρ ε κ₀ ω.2.1.1 ω.2.2 e₀ hleft hfull vC t t']

/-! ## Haar translation to successor-relative coordinates -/

namespace R324WithinHalfStepContext

variable {m : ℕ} {pairing : PartialPairing (Fin m)}
    (ctx : R324WithinHalfStepContext pairing)

def physicalBlockTranslation
    (a : T4) :
    (Fin (2 * residualBlockOrder ctx.step.2) → T4) ≃ᵐ
      (Fin (2 * residualBlockOrder ctx.step.2) → T4) :=
  MeasurableEquiv.piCongrRight fun _ =>
    MeasurableEquiv.addRight a

@[simp]
theorem physicalBlockTranslation_apply
    (a : T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ctx.physicalBlockTranslation a t =
      fun j => t j + a := by
  funext j
  rfl

theorem measurePreserving_physicalBlockTranslation
    (a : T4) :
    MeasurePreserving
      (ctx.physicalBlockTranslation a)
      (Measure.pi fun _ :
        Fin (2 * residualBlockOrder ctx.step.2) =>
          paperMeasure)
      (Measure.pi fun _ :
        Fin (2 * residualBlockOrder ctx.step.2) =>
          paperMeasure) := by
  change
    MeasurePreserving
      (fun t j => t j + a)
      (Measure.pi fun _ :
        Fin (2 * residualBlockOrder ctx.step.2) =>
          paperMeasure)
      (Measure.pi fun _ :
        Fin (2 * residualBlockOrder ctx.step.2) =>
          paperMeasure)
  exact measurePreserving_pi
    (fun _ :
      Fin (2 * residualBlockOrder ctx.step.2) =>
        paperMeasure)
    (fun _ :
      Fin (2 * residualBlockOrder ctx.step.2) =>
        paperMeasure)
    (f := fun _ x => x + a) fun _j => by
      rw [paperMeasure_eq_volume]
      exact measurePreserving_add_right
        (volume : Measure T4) a

theorem integral_rawLocal_sub_const_mul_complex
    (ρ : SmoothCutoff) (ε : ℝ)
    (u a : T4) (outer : ℂ) :
    (∫ actual :
        Fin (2 * residualBlockOrder ctx.step.2) → T4,
      (ctx.rawLocalIntegrand ρ ε u
        (fun i => actual i - a) : ℂ) * outer
      ∂Measure.pi fun _ => paperMeasure) =
      ∫ t :
          Fin (2 * residualBlockOrder ctx.step.2) → T4,
        (ctx.rawLocalIntegrand ρ ε u t : ℂ) * outer
        ∂Measure.pi fun _ => paperMeasure := by
  let f :
      (Fin (2 * residualBlockOrder ctx.step.2) → T4) → ℂ :=
    fun actual =>
      (ctx.rawLocalIntegrand ρ ε u
        (fun i => actual i - a) : ℂ) * outer
  calc
    (∫ actual :
        Fin (2 * residualBlockOrder ctx.step.2) → T4,
      (ctx.rawLocalIntegrand ρ ε u
        (fun i => actual i - a) : ℂ) * outer
      ∂Measure.pi fun _ => paperMeasure) =
      ∫ t :
          Fin (2 * residualBlockOrder ctx.step.2) → T4,
        f (ctx.physicalBlockTranslation a t)
        ∂Measure.pi fun _ => paperMeasure := by
      exact
        (ctx.measurePreserving_physicalBlockTranslation a).integral_comp' f
          |>.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [ctx.physicalBlockTranslation_apply]
      dsimp only [f]
      have ht :
          (fun i => (t i + a) - a) = t := by
        funext i
        abel
      rw [ht]

end R324WithinHalfStepContext

/-! ## Complement-only data for the actual selected section -/

def r324FirstLeftComplementBaseTuple
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4) :
    Fin (2 * m) → T4 :=
  r324FirstLeftPhysicalReconstruct e₀ hleft vC
    (fun _ => 0)

def r324FirstLeftComplementSuccessor
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (x y : T4)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4) : T4 :=
  r324FirstLeftPhysicalSuccessor e₀ hleft x y
    (r324FirstLeftComplementBaseTuple e₀ hleft vC)

def r324FirstLeftComplementDisplacement
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (x y : T4)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4) : T4 :=
  r324FirstLeftPhysicalPredecessor e₀ hleft x y
      (r324FirstLeftComplementBaseTuple e₀ hleft vC) -
    r324FirstLeftComplementSuccessor e₀ hleft x y vC

def r324FirstLeftComplementOuter
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (α β : Z4) (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (x y z w : T4)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4) : ℂ :=
  r324FirstLeftInitialPhysicalOuterFactor
    ρ ε α β e₀ hleft ω x y z w
    (r324FirstLeftComplementBaseTuple e₀ hleft vC)

/-- After genuine physical reconstruction, the original selected section is
the translated empty-prefix raw local integrand times complement-only data. -/
theorem r324FirstLeftPhysicalSection_reconstruct_eq_relativeRaw
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (α β : Z4) (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (tail : List (R322ExtractionStep m))
    (hschedule :
      r322AnalyticSchedule e₀.1 =
        r324FirstLeftSelectedStep e₀ hleft :: tail)
    (x y z w : T4)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4)
    (t :
      Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4) :
    let v :=
      r324FirstLeftPhysicalReconstruct e₀ hleft vC t
    let ctx :=
      r324FirstLeftInitialStepContext e₀ hleft tail hschedule
    r324FirstLeftOuterFactor ρ ε α β e₀ hleft ω
          x y z w v *
        (∑ κB : R324FirstLeftBlockCoordinate e₀ hleft,
          (primitiveCovarianceProduct ρ ε
            (residualBlockOrder
              (selectedExtractionBlock
                e₀.1 Finset.univ hleft))
            κB.1
            (r324FirstLeftPhysicalBlockTuple
              e₀ hleft v) : ℂ)) =
      (ctx.rawLocalIntegrand ρ ε
        (r324FirstLeftComplementDisplacement
          e₀ hleft x y vC)
        (fun i =>
          t i -
            r324FirstLeftComplementSuccessor
              e₀ hleft x y vC) : ℂ) *
        r324FirstLeftComplementOuter
          ρ ε α β e₀ hleft ω x y z w vC := by
  dsimp only
  rw [
    r324FirstLeftOuterFactor_mul_primitiveSum_eq_initialRaw_mul_outer
      ρ ε α β e₀ hleft ω tail hschedule x y z w
      (r324FirstLeftPhysicalReconstruct e₀ hleft vC t)]
  unfold r324FirstLeftTranslatedPhysicalBlockTuple
  rw [r324FirstLeftPhysicalBlockTuple_reconstruct]
  have hpred :=
    r324FirstLeftPhysicalPredecessor_reconstruct_eq
      e₀ hleft vC t (fun _ => 0) x y
  have hsucc :=
    r324FirstLeftPhysicalSuccessor_reconstruct_eq
      e₀ hleft vC t (fun _ => 0) x y
  have houter :=
    r324FirstLeftInitialPhysicalOuterFactor_reconstruct_eq
      ρ ε α β e₀ hleft ω tail hschedule
      x y z w vC t (fun _ => 0)
  rw [hpred, hsucc, houter]
  rfl

def r324FirstLeftSelectedPhysicalSection
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (α β : Z4) (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (x y z w : T4)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4)
    (vB :
      (i : {i : Fin (2 * m) //
        r324FirstLeftSelected e₀ hleft i}) → T4) : ℂ :=
  let v :=
    (MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Fin (2 * m) => T4)
      (r324FirstLeftSelected e₀ hleft)).symm
        (vB, vC)
  r324FirstLeftOuterFactor ρ ε α β e₀ hleft ω
        x y z w v *
    ∑ κB : R324FirstLeftBlockCoordinate e₀ hleft,
      (primitiveCovarianceProduct ρ ε
        (residualBlockOrder
          (selectedExtractionBlock
            e₀.1 Finset.univ hleft))
        κB.1
        (r324FirstLeftPhysicalBlockTuple
          e₀ hleft v) : ℂ)

theorem r324FirstLeftSelectedPhysicalSection_standardBlock
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (α β : Z4) (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (x y z w : T4)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4)
    (t :
      Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4) :
    r324FirstLeftSelectedPhysicalSection
        ρ ε α β e₀ hleft ω x y z w vC
        (r324FirstLeftSelectedTupleMeasurableEquiv
          e₀ hleft t) =
      let v :=
        r324FirstLeftPhysicalReconstruct e₀ hleft vC t
      r324FirstLeftOuterFactor ρ ε α β e₀ hleft ω
            x y z w v *
        (∑ κB : R324FirstLeftBlockCoordinate e₀ hleft,
          (primitiveCovarianceProduct ρ ε
            (residualBlockOrder
              (selectedExtractionBlock
                e₀.1 Finset.univ hleft))
            κB.1
            (r324FirstLeftPhysicalBlockTuple
              e₀ hleft v) : ℂ)) := by
  rfl

/-- Reindexing the genuine selected doubled coordinates and translating by
the complement-determined successor gives the exact raw local integral. -/
theorem integral_r324FirstLeftSelectedPhysicalSection_eq_initialRaw
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (α β : Z4) (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (tail : List (R322ExtractionStep m))
    (hschedule :
      r322AnalyticSchedule e₀.1 =
        r324FirstLeftSelectedStep e₀ hleft :: tail)
    (x y z w : T4)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4) :
    (∫ vB :
        (i : {i : Fin (2 * m) //
          r324FirstLeftSelected e₀ hleft i}) → T4,
      r324FirstLeftSelectedPhysicalSection
        ρ ε α β e₀ hleft ω x y z w vC vB
      ∂Measure.pi fun _ => paperMeasure) =
      ∫ t :
          Fin (2 * residualBlockOrder
            (selectedExtractionBlock
              e₀.1 Finset.univ hleft)) → T4,
        ((r324FirstLeftInitialStepContext
          e₀ hleft tail hschedule).rawLocalIntegrand
            ρ ε
            (r324FirstLeftComplementDisplacement
              e₀ hleft x y vC) t : ℂ) *
          r324FirstLeftComplementOuter
            ρ ε α β e₀ hleft ω x y z w vC
        ∂Measure.pi fun _ => paperMeasure := by
  rw [integral_r324FirstLeftSelected_eq_standardBlock
    e₀ hleft
    (r324FirstLeftSelectedPhysicalSection
      ρ ε α β e₀ hleft ω x y z w vC)]
  let ctx :=
    r324FirstLeftInitialStepContext e₀ hleft tail hschedule
  calc
    (∫ t :
        Fin (2 * residualBlockOrder
          (selectedExtractionBlock
            e₀.1 Finset.univ hleft)) → T4,
      r324FirstLeftSelectedPhysicalSection
        ρ ε α β e₀ hleft ω x y z w vC
        (r324FirstLeftSelectedTupleMeasurableEquiv
          e₀ hleft t)
      ∂Measure.pi fun _ => paperMeasure) =
      ∫ t :
          Fin (2 * residualBlockOrder
            (selectedExtractionBlock
              e₀.1 Finset.univ hleft)) → T4,
        (ctx.rawLocalIntegrand ρ ε
          (r324FirstLeftComplementDisplacement
            e₀ hleft x y vC)
          (fun i =>
            t i -
              r324FirstLeftComplementSuccessor
                e₀ hleft x y vC) : ℂ) *
          r324FirstLeftComplementOuter
            ρ ε α β e₀ hleft ω x y z w vC
        ∂Measure.pi fun _ => paperMeasure := by
      apply integral_congr_ae
      filter_upwards with t
      rw [r324FirstLeftSelectedPhysicalSection_standardBlock]
      exact
        r324FirstLeftPhysicalSection_reconstruct_eq_relativeRaw
          ρ ε α β e₀ hleft ω tail hschedule
          x y z w vC t
    _ = _ := by
      exact ctx.integral_rawLocal_sub_const_mul_complex
        ρ ε
        (r324FirstLeftComplementDisplacement
          e₀ hleft x y vC)
        (r324FirstLeftComplementSuccessor
          e₀ hleft x y vC)
        (r324FirstLeftComplementOuter
          ρ ε α β e₀ hleft ω x y z w vC)

/-- **Actual first-left physical selected integral = initial absorbed
integral.**

The left side is the selected section occurring literally in the routed
physical moment fibre.  The right side is the genuine all-Green initial
edge state after one `R324WithinHalfStepContext.absorb`.  The state change
occurs only after the selected spatial integral. -/
theorem
    lamEps_pow_integral_r324FirstLeftSelectedPhysicalSection_eq_initialAbsorb
    {m : ℕ} (ρ : SmoothCutoff) (lam ε : ℝ)
    (α β : Z4) (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (tail : List (R322ExtractionStep m))
    (hschedule :
      r322AnalyticSchedule e₀.1 =
        r324FirstLeftSelectedStep e₀ hleft :: tail)
    (x y z w : T4)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4)
    (hstandard :
      Integrable
        ((r324FirstLeftInitialStepContext
          e₀ hleft tail hschedule).localIntegrand ρ ε
            (r324FirstLeftComplementDisplacement
              e₀ hleft x y vC))
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB : R324FirstLeftBlockCoordinate e₀ hleft,
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder
                  (selectedExtractionBlock
                    e₀.1 Finset.univ hleft) - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder
                  (selectedExtractionBlock
                    e₀.1 Finset.univ hleft))
                κB.1
                (r324FirstLeftInitialStepContext
                  e₀ hleft tail hschedule).internalEdges
                (primitiveAssemble
                  (residualBlockOrder
                    (selectedExtractionBlock
                      e₀.1 Finset.univ hleft))
                  (r324FirstLeft_one_le_blockOrder e₀ hleft)
                  p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε ^
          (2 * residualBlockOrder
            (selectedExtractionBlock
              e₀.1 Finset.univ hleft)) : ℂ) *
        (∫ vB :
            (i : {i : Fin (2 * m) //
              r324FirstLeftSelected e₀ hleft i}) → T4,
          r324FirstLeftSelectedPhysicalSection
            ρ ε α β e₀ hleft ω x y z w vC vB
          ∂Measure.pi fun _ => paperMeasure) =
      (((r324FirstLeftInitialStepContext
          e₀ hleft tail hschedule).absorb ρ lam ε).edges
          (r324WithinHalfPredecessorSlot
            (r324FirstLeftInitialStepContext
              e₀ hleft tail hschedule).state
            (r324FirstLeftInitialStepContext
              e₀ hleft tail hschedule).step)
          (r324FirstLeftComplementDisplacement
            e₀ hleft x y vC) : ℝ) *
        r324FirstLeftComplementOuter
          ρ ε α β e₀ hleft ω x y z w vC := by
  rw [integral_r324FirstLeftSelectedPhysicalSection_eq_initialRaw
    ρ ε α β e₀ hleft ω tail hschedule x y z w vC]
  exact
    (r324FirstLeftInitialStepContext
      e₀ hleft tail hschedule).rawLocalSpatialIntegral_mul_complexOuter_eq_absorb
      ρ lam ε
      (r324FirstLeftComplementDisplacement
        e₀ hleft x y vC)
      (r324FirstLeftComplementOuter
        ρ ε α β e₀ hleft ω x y z w vC)
      hstandard hinternal

end

end Anderson4D
