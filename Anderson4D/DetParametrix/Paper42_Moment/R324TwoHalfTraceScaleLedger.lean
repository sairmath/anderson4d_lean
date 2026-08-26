import Anderson4D.DetParametrix.Paper42_Moment.R324TwoHalfCompleteScaleAbsorption
import Anderson4D.DetParametrix.Paper42_Moment.R324InitialTwoHalfRootIntegrability

/-!
# Closing the two certified within-half scale ledgers

This file contains only the finite combinatorial bookkeeping needed to use
the compatible analytic budgets.  It identifies the all-Green initial scale
product, bounds the number of processed blocks by their total perturbative
order, and combines the two terminal scale products with the initial nested
cross order.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- The literal all-Green active scale product has one factor for each of
the `m + 1` production-edge slots. -/
theorem r324InitialActiveScaleProduct_eq_pow
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m)) (A : ℝ) :
    (∏ _edge ∈
        ({0} ∪
          (r324InitialWithinHalfEdgeState m).active.image
            r324InternalVertexEdgeSlot), A) =
      A ^ (m + 1) := by
  have hslots :=
    R324WithinHalfResidualPrefix.initial_activeEdgeSlots
      ρ lam ε pairing
  change
    ({0} ∪
        (r324InitialWithinHalfEdgeState m).active.image
          r324InternalVertexEdgeSlot : Finset (Fin (m + 1))) =
      Finset.univ at hslots
  rw [hslots]
  simp

/-- Every block in the analytic schedule has positive perturbative order,
so the schedule length is no larger than its order sum. -/
theorem r322AnalyticSchedule_length_le_orderSum
    {m : ℕ} (pairing : PartialPairing (Fin m)) :
    (r322AnalyticSchedule pairing).length ≤
      ((r322AnalyticSchedule pairing).map
        (fun step => residualBlockOrder step.2)).sum := by
  have h := List.length_le_sum_of_one_le
    ((r322AnalyticSchedule pairing).map
      (fun step => residualBlockOrder step.2)) (by
        intro order horder
        obtain ⟨step, hstep, rfl⟩ := List.mem_map.mp horder
        have hblock :
            step.2 ∈ extractionBlocks pairing := by
          apply
            (r322AnalyticSchedule_blocks_perm_extractionBlocks
              pairing).mem_iff.mp
          exact List.mem_map.mpr ⟨step, hstep, rfl⟩
        have hfully : IsFullyPairedOn pairing step.2 :=
          extractionBlock_isFullyPairedOn_of_mem
            pairing step.2 hblock
        have haligned :=
          r322AnalyticSchedule_forall_aligned pairing step hstep
        have hnonempty : step.2.Nonempty :=
          ⟨step.1.1, haligned.1⟩
        exact one_le_residualBlockOrder_of_nonempty
          pairing step.2 hfully hnonempty)
  simpa using h

namespace R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

/-- A complete certified trace has processed exactly the order of the
initial analytic suffix. -/
theorem terminal_processedOrder_eq_initialRemainingOrder
    {ρ : SmoothCutoff} {lam ε A : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial ρ lam ε pairing)
        (fun _ => A)) :
    r324WithinHalfProcessedOrder trace.terminalPrefix.state =
      (R324WithinHalfResidualPrefix.initial
        ρ lam ε pairing).remainingOrder := by
  unfold r324WithinHalfProcessedOrder
    R324WithinHalfResidualPrefix.remainingOrder
  rw [trace.terminalPrefix_processed_eq_schedule]
  rfl

/-- The number of processed blocks in a complete certified trace is no
larger than the initial suffix order. -/
theorem terminal_processedLength_le_initialRemainingOrder
    {ρ : SmoothCutoff} {lam ε A : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial ρ lam ε pairing)
        (fun _ => A)) :
    trace.terminalPrefix.state.processed.length ≤
      (R324WithinHalfResidualPrefix.initial
        ρ lam ε pairing).remainingOrder := by
  rw [trace.terminalPrefix_processed_eq_schedule]
  unfold R324WithinHalfResidualPrefix.remainingOrder
  exact r322AnalyticSchedule_length_le_orderSum pairing

end R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

namespace R324WithinHalfResidualPrefix.R324CompatibleAnalyticBudgetTrace

/-- Closed form of one terminal scale product when its certified budget
starts from the constant all-Green scale. -/
theorem initial_analytic_activeEdgeScaleProduct_le_closedForm
    {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (data :
      R324CompatibleAnalyticBudgetTrace
        (C := C) (K := K) (A := A)
        (R324WithinHalfResidualPrefix.initial ρ lam ε pairing)
        (fun _ => A)) :
    (∏ edge ∈ data.analytic.terminalPrefix.activeEdgeSlots,
        data.analytic.terminalScale edge) ≤
      A ^ (m + 1) *
        (C * lam) ^
          (2 * (R324WithinHalfResidualPrefix.initial
            ρ lam ε pairing).remainingOrder) *
        K ^ data.analytic.terminalPrefix.state.processed.length := by
  calc
    _ ≤
        (∏ _edge ∈
            ({0} ∪
              (r324InitialWithinHalfEdgeState m).active.image
                r324InternalVertexEdgeSlot), A) *
          (C * lam) ^
            (2 * r324WithinHalfProcessedOrder
              data.analytic.terminalPrefix.state) *
          K ^ data.analytic.terminalPrefix.state.processed.length :=
      data.analytic_activeEdgeScaleProduct_le_closedForm
    _ = _ := by
      rw [r324InitialActiveScaleProduct_eq_pow ρ lam ε pairing A,
        data.analytic.terminal_processedOrder_eq_initialRemainingOrder]

end R324WithinHalfResidualPrefix.R324CompatibleAnalyticBudgetTrace

/-- The two certified terminal scale products and the complete initial
nested-cross inserted majorant are absorbed into one ambient-order inserted
majorant.  This is the exact three-schedule order ledger used after the
endpoint/run integral estimate. -/
theorem r324_twoHalf_initial_terminalScale_mul_majorant_le
    {ρ : SmoothCutoff} {C K A B lam ε supportConstant : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hB : 0 ≤ B) (hlam : 0 ≤ lam)
    (leftData :
      R324WithinHalfResidualPrefix.R324CompatibleAnalyticBudgetTrace
        (C := C) (K := K) (A := A)
        (R324WithinHalfResidualPrefix.initial ρ lam ε κp)
        (fun _ => A))
    (rightData :
      R324WithinHalfResidualPrefix.R324CompatibleAnalyticBudgetTrace
        (C := C) (K := K) (A := A)
        (R324WithinHalfResidualPrefix.initial ρ lam ε κm)
        (fun _ => A))
    (π : κp.singles ≃ κm.singles)
    (hm : 1 ≤ m) (z : T4) :
    (((∏ edge ∈ leftData.analytic.terminalPrefix.activeEdgeSlots,
          leftData.analytic.terminalScale edge) *
        (∏ edge ∈ rightData.analytic.terminalPrefix.activeEdgeSlots,
          rightData.analytic.terminalScale edge)) *
      invSqKerMass ^ 4) *
        primitiveInsertedMajorant B lam ε supportConstant
          (R324NestedCrossResidualPrefix.initial
            κp κm π).remainingOrder z ≤
      primitiveInsertedMajorant
        (r324TwoHalfCompleteAbsorbedBase A C K B)
        lam ε supportConstant m z := by
  let pleft :=
    (R324WithinHalfResidualPrefix.initial
      ρ lam ε κp).remainingOrder
  let pright :=
    (R324WithinHalfResidualPrefix.initial
      ρ lam ε κm).remainingOrder
  let cross :=
    (R324NestedCrossResidualPrefix.initial
      κp κm π).remainingOrder
  let leftLength :=
    leftData.analytic.terminalPrefix.state.processed.length
  let rightLength :=
    rightData.analytic.terminalPrefix.state.processed.length
  let leftProduct :=
    ∏ edge ∈ leftData.analytic.terminalPrefix.activeEdgeSlots,
      leftData.analytic.terminalScale edge
  let rightProduct :=
    ∏ edge ∈ rightData.analytic.terminalPrefix.activeEdgeSlots,
      rightData.analytic.terminalScale edge
  let leftBound :=
    A ^ (m + 1) * (C * lam) ^ (2 * pleft) * K ^ leftLength
  let rightBound :=
    A ^ (m + 1) * (C * lam) ^ (2 * pright) * K ^ rightLength
  have hleft : leftProduct ≤ leftBound := by
    exact leftData.initial_analytic_activeEdgeScaleProduct_le_closedForm
  have hright : rightProduct ≤ rightBound := by
    exact rightData.initial_analytic_activeEdgeScaleProduct_le_closedForm
  have hrightNonneg : 0 ≤ rightProduct := by
    dsimp only [rightProduct]
    exact Finset.prod_nonneg fun edge hedge =>
      (rightData.analytic.terminalCertificate.scale_pos edge).le
  have hleftBoundNonneg : 0 ≤ leftBound := by
    dsimp only [leftBound]
    positivity
  have hproducts :
      leftProduct * rightProduct ≤ leftBound * rightBound :=
    mul_le_mul hleft hright hrightNonneg hleftBoundNonneg
  have hwithMass :
      (leftProduct * rightProduct) * invSqKerMass ^ 4 ≤
        (leftBound * rightBound) * invSqKerMass ^ 4 :=
    mul_le_mul_of_nonneg_right hproducts (pow_nonneg invSqKerMass_nonneg _)
  have hmajorantNonneg :
      0 ≤ primitiveInsertedMajorant B lam ε supportConstant cross z :=
    primitiveInsertedMajorant_nonneg' B lam ε supportConstant cross z
  have hscaled :
      ((leftProduct * rightProduct) * invSqKerMass ^ 4) *
          primitiveInsertedMajorant B lam ε supportConstant cross z ≤
        ((leftBound * rightBound) * invSqKerMass ^ 4) *
          primitiveInsertedMajorant B lam ε supportConstant cross z :=
    mul_le_mul_of_nonneg_right hwithMass hmajorantNonneg
  have horder : pleft + pright + cross = m := by
    exact r324InitialSchedules_remainingOrders_eq_ambient
      ρ lam ε κp κm π
  have hleftLength : leftLength ≤ pleft :=
    leftData.analytic.terminal_processedLength_le_initialRemainingOrder
  have hrightLength : rightLength ≤ pright :=
    rightData.analytic.terminal_processedLength_le_initialRemainingOrder
  have habsorb := r324_twoHalf_complete_majorant_le
    (ε := ε) (supportConstant := supportConstant)
    hA hC hK hB hlam hm horder hleftLength hrightLength z
  simpa only [leftProduct, rightProduct, leftBound, rightBound,
    pleft, pright, cross, leftLength, rightLength] using
    hscaled.trans habsorb

end

end Anderson4D
