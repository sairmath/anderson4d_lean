import Anderson4D.DetParametrix.Paper42_Moment.R324FirstLeftPhysicalRouting
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticActiveCarrierGeometry

/-!
# Moving the genuine first-left selector block into analytic position

The first-left R-324 fibre is indexed by the first block chosen by
`selectRel`.  The R-322 analytic collapse instead sorts all extraction
steps by increasing right endpoint.  Those blocks need not be literally
the same list head: analytic steps preceding the selector block can be
disjoint from it.

This file closes that representation-order discrepancy.  It locates the
actual first-left selector step in the analytic schedule, moves it to the
front by an explicit list permutation, and proves that every crossed block
is disjoint from the selected coordinates occurring in
`R324FirstLeftPhysicalRouting`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-! ## The selector step inside the analytic schedule -/

/-- The endpoint/block pair selected by the genuine first left reduction
step of the R-324 fibre. -/
def r324FirstLeftSelectedStep
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :
    R322ExtractionStep m :=
  (selectRel e₀.1 Finset.univ hleft,
    selectedExtractionBlock e₀.1 Finset.univ hleft)

@[simp]
theorem r324FirstLeftSelectedStep_endpoint
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :
    (r324FirstLeftSelectedStep e₀ hleft).1 =
      selectRel e₀.1 Finset.univ hleft :=
  rfl

@[simp]
theorem r324FirstLeftSelectedStep_block
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :
    (r324FirstLeftSelectedStep e₀ hleft).2 =
      selectedExtractionBlock e₀.1 Finset.univ hleft :=
  rfl

/-- The genuine selector step occurs in the unsorted aligned extraction
trace.  This is the point where both its endpoint pair and its concrete
block are tied back to the original reduction recursion. -/
theorem r324FirstLeftSelectedStep_mem_extractionTrace
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :
    r324FirstLeftSelectedStep e₀ hleft ∈
      (extract e₀.1).zip (extractionBlocks e₀.1) := by
  have hleft' := hleft
  obtain ⟨a, b, hab⟩ := hleft'
  have hm : 0 < m := by
    exact Nat.pos_of_ne_zero fun hm0 => by
      subst m
      exact Fin.elim0 a
  obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  unfold extract extractionBlocks
  rw [extractAux_succ_pos fuel hleft,
    extractionBlocksAux_succ_pos fuel hleft]
  simp [r324FirstLeftSelectedStep,
    selectedExtractionBlock]

/-- Hence the genuine selector step also occurs in the right-endpoint
sorted analytic schedule. -/
theorem r324FirstLeftSelectedStep_mem_analyticSchedule
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :
    r324FirstLeftSelectedStep e₀ hleft ∈
      r322AnalyticSchedule e₀.1 := by
  apply (List.mem_insertionSort R322StepRightLE).mpr
  exact
    r324FirstLeftSelectedStep_mem_extractionTrace
      e₀ hleft

/-! ## Explicitly commuting the disjoint analytic prefix -/

/-- Exact schedule decomposition at the genuine first-left selector step.
Every analytic step which the selector step crosses is spatially disjoint
from it. -/
theorem exists_r324FirstLeft_analytic_decomposition
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :
    ∃ pre post,
      r322AnalyticSchedule e₀.1 =
          pre ++ r324FirstLeftSelectedStep e₀ hleft :: post ∧
        (∀ earlier ∈ pre,
          Disjoint earlier.2
            (selectedExtractionBlock
              e₀.1 Finset.univ hleft)) := by
  obtain ⟨pre, post, hschedule⟩ :=
    (List.mem_iff_append.mp
      (r324FirstLeftSelectedStep_mem_analyticSchedule
        e₀ hleft))
  refine ⟨pre, post, hschedule, ?_⟩
  intro earlier hearlier
  simpa using
    r322AnalyticSchedule_prefixBlock_disjoint_step
      e₀.1 pre post
      (r324FirstLeftSelectedStep e₀ hleft)
      earlier hschedule hearlier

/-- **Selector/analytic-order bridge.**

The actual first-left selector step may be moved to the head of the
analytic list.  The permutation crosses only disjoint blocks, and those
crossed blocks remain completely outside the doubled spatial-coordinate
set integrated on the inside by
`integral_sum_deterministicMomentIntegrand_eq_firstLeft_primitive`.
-/
theorem r324FirstLeft_analytic_reorder
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :
    ∃ pre post,
      r322AnalyticSchedule e₀.1 =
          pre ++ r324FirstLeftSelectedStep e₀ hleft :: post ∧
        List.Perm
          (r322AnalyticSchedule e₀.1)
          (r324FirstLeftSelectedStep e₀ hleft ::
            (pre ++ post)) ∧
        (∀ earlier ∈ pre,
          Disjoint
            (earlier.2.image leftMomentIndex)
            ((selectedExtractionBlock
              e₀.1 Finset.univ hleft).image
                leftMomentIndex)) ∧
        selectedExtractionBlock e₀.1 Finset.univ hleft =
          r322AnalyticActiveCarrier pre ∩
            Finset.Icc
              (selectRel e₀.1 Finset.univ hleft).1
              (selectRel e₀.1 Finset.univ hleft).2 := by
  obtain ⟨pre, post, hschedule, hdisjoint⟩ :=
    exists_r324FirstLeft_analytic_decomposition
      e₀ hleft
  refine ⟨pre, post, hschedule, ?_, ?_, ?_⟩
  · rw [hschedule]
    exact List.perm_middle
  · intro earlier hearlier
    exact
      (Finset.disjoint_image
        leftMomentIndex_injective).mpr
        (hdisjoint earlier hearlier)
  · simpa using
      r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
        e₀.1 pre post
        (r324FirstLeftSelectedStep e₀ hleft)
        hschedule

end

end Anderson4D
