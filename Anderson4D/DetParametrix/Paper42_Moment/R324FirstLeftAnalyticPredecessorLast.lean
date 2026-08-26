import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfPredecessorTransport

/-! # The analytic prefix step carrying the R-324 predecessor

If the production predecessor edge of the first-left block is extracted,
its generating analytic step is the last step before the selected block.
This is a statement about the genuine schedule and disjoint extraction
blocks, not a pointwise identity between pre- and post-collapse edges.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- Equality of extracted edge slots says exactly that the prefix block
ends immediately before the selected first-left block begins. -/
theorem r324FirstLeft_extractedPredecessor_adjacent
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (step : R322ExtractionStep m)
    (hedge :
      extractedRightEdge step.1 =
        r324FirstLeftPredecessorEdge e₀ hleft) :
    step.1.2.val + 1 =
      (r324FirstLeftSelectedStep e₀ hleft).1.1.val := by
  have hval := congrArg Fin.val hedge
  simpa only [extractedRightEdge_val,
    r324FirstLeftPredecessorEdge,
    r324FirstLeftSelectedStep_endpoint] using hval

/-- No scheduled block can occur between the block producing the selected
predecessor and the selected block itself. -/
theorem r324FirstLeft_prefixPredecessor_is_last
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (pre post : List (R322ExtractionStep m))
    (step : R322ExtractionStep m)
    (hschedule :
      r322AnalyticSchedule e₀.1 =
        pre ++ r324FirstLeftSelectedStep e₀ hleft :: post)
    (hstep : step ∈ pre)
    (hedge :
      extractedRightEdge step.1 =
        r324FirstLeftPredecessorEdge e₀ hleft) :
    ∃ prior, pre = prior ++ [step] := by
  obtain ⟨prior, rest, hpre⟩ :=
    List.mem_iff_append.mp hstep
  cases rest with
  | nil =>
      exact ⟨prior, by simpa using hpre⟩
  | cons later tail =>
      exfalso
      have hadjacent :=
        r324FirstLeft_extractedPredecessor_adjacent
          e₀ hleft step hedge
      have hlaterPre : later ∈ pre := by
        rw [hpre]
        simp
      have hdisjoint :
          Disjoint later.2
            (r324FirstLeftSelectedStep e₀ hleft).2 :=
        r322AnalyticSchedule_prefixBlock_disjoint_step
          e₀.1 pre post
          (r324FirstLeftSelectedStep e₀ hleft)
          later hschedule hlaterPre
      have hp :=
        r322AnalyticSchedule_pairwise_right_lt e₀.1
      have hpFull :
          (prior ++
            (step :: later :: tail ++
              r324FirstLeftSelectedStep e₀ hleft ::
                post)).Pairwise
              (fun s t => s.1.2 < t.1.2) := by
        rw [← List.append_assoc, ← hpre, ← hschedule]
        exact hp
      have hpTail :
          (step :: later :: tail ++
            r324FirstLeftSelectedStep e₀ hleft :: post).Pairwise
              (fun s t => s.1.2 < t.1.2) := by
        exact (List.pairwise_append.mp hpFull).2.1
      have hstepLater :
          step.1.2 < later.1.2 :=
        (List.pairwise_cons.mp hpTail).1 later (by simp)
      have hlaterSelected :
          later.1.2 <
            (r324FirstLeftSelectedStep e₀ hleft).1.2 :=
        (List.pairwise_cons.mp
          (List.pairwise_cons.mp hpTail).2).1
            (r324FirstLeftSelectedStep e₀ hleft) (by simp)
      have hlaterSchedule :
          later ∈ r322AnalyticSchedule e₀.1 := by
        rw [hschedule]
        exact List.mem_append_left _ hlaterPre
      have haligned :=
        r322AnalyticSchedule_forall_aligned
          e₀.1 later hlaterSchedule
      have hlaterBlock : later.1.2 ∈ later.2 :=
        haligned.2.1
      have hlaterSelectedBlock :
          later.1.2 ∈
            (r324FirstLeftSelectedStep e₀ hleft).2 := by
        rw [r324FirstLeftSelectedStep_block,
          r324FirstLeft_selectedBlock_eq_Icc]
        apply Finset.mem_Icc.mpr
        constructor
        · change
            (r324FirstLeftSelectedStep
              e₀ hleft).1.1.val ≤ later.1.2.val
          change step.1.2.val < later.1.2.val at hstepLater
          omega
        · exact hlaterSelected.le
      exact
        (Finset.disjoint_left.mp hdisjoint)
          hlaterBlock hlaterSelectedBlock

/-- Canonical decomposition at the extracted predecessor: the last prefix
step is adjacent to the selected first-left block. -/
theorem exists_r324FirstLeft_lastAnalyticPredecessor
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (hextracted :
      r324FirstLeftPredecessorEdge e₀ hleft ∈
        extractedRightEdges e₀.1) :
    ∃ prior step post,
      r322AnalyticSchedule e₀.1 =
          (prior ++ [step]) ++
            r324FirstLeftSelectedStep e₀ hleft :: post ∧
        extractedRightEdge step.1 =
          r324FirstLeftPredecessorEdge e₀ hleft ∧
        step.1.2.val + 1 =
          (r324FirstLeftSelectedStep e₀ hleft).1.1.val := by
  obtain
      ⟨pre, step, post, hschedule, hstep, _hdisjoint,
        hedge⟩ :=
    extracted_predecessor_belongs_disjoint_analyticPrefix
      e₀ hleft hextracted
  obtain ⟨prior, hpre⟩ :=
    r324FirstLeft_prefixPredecessor_is_last
      e₀ hleft pre post step hschedule hstep hedge
  refine ⟨prior, step, post, ?_, hedge, ?_⟩
  · rw [hschedule, hpre]
  · exact
      r324FirstLeft_extractedPredecessor_adjacent
        e₀ hleft step hedge

end

end Anderson4D
