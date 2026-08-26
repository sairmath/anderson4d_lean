import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticProperHeadCollapse

/-!
# Active carriers along the R-322 analytic schedule

After a prefix of the inside-to-outside schedule has been collapsed, its
concrete blocks have been deleted.  This file identifies the next concrete
block with the ambient endpoint interval restricted to that active carrier.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

/-- Ambient vertices which remain after deleting a schedule prefix. -/
def r322AnalyticActiveCarrier {m : ℕ}
    (pre : List (R322ExtractionStep m)) :
    Finset (Fin m) :=
  Finset.univ \
    finsetUnionList (pre.map Prod.snd)

@[simp]
theorem r322AnalyticActiveCarrier_nil {m : ℕ} :
    r322AnalyticActiveCarrier
        ([] : List (R322ExtractionStep m)) =
      Finset.univ := by
  simp [r322AnalyticActiveCarrier, finsetUnionList]

/-- Membership means avoiding every block already processed. -/
theorem mem_r322AnalyticActiveCarrier_iff
    {m : ℕ} (pre : List (R322ExtractionStep m))
    (i : Fin m) :
    i ∈ r322AnalyticActiveCarrier pre ↔
      ∀ s ∈ pre, i ∉ s.2 := by
  constructor
  · intro hi s hs his
    have hiUnion :
        i ∈ finsetUnionList
          (pre.map Prod.snd) := by
      exact
        (mem_finsetUnionList_iff
          (pre.map Prod.snd)).mpr
          ⟨s.2,
            List.mem_map.mpr ⟨s, hs, rfl⟩,
            his⟩
    exact
      (Finset.mem_sdiff.mp hi).2 hiUnion
  · intro hi
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ i, ?_⟩
    intro hiUnion
    obtain ⟨B, hB, hiB⟩ :=
      (mem_finsetUnionList_iff
        (pre.map Prod.snd)).mp hiUnion
    obtain ⟨s, hs, rfl⟩ :=
      List.mem_map.mp hB
    exact hi s hs hiB

/-- Processing more blocks can only shrink the active carrier. -/
theorem r322AnalyticActiveCarrier_append_subset
    {m : ℕ}
    (pre suffix : List (R322ExtractionStep m)) :
    r322AnalyticActiveCarrier (pre ++ suffix) ⊆
      r322AnalyticActiveCarrier pre := by
  intro i hi
  apply
    (mem_r322AnalyticActiveCarrier_iff
      pre i).mpr
  intro s hs
  exact
      (mem_r322AnalyticActiveCarrier_iff
      (pre ++ suffix) i).mp hi
      s (List.mem_append_left suffix hs)

/-- The next carrier is obtained by deleting exactly the next block. -/
@[simp]
theorem r322AnalyticActiveCarrier_append_singleton
    {m : ℕ}
    (pre : List (R322ExtractionStep m))
    (step : R322ExtractionStep m) :
    r322AnalyticActiveCarrier (pre ++ [step]) =
      r322AnalyticActiveCarrier pre \ step.2 := by
  ext i
  constructor
  · intro hi
    have hall :=
      (mem_r322AnalyticActiveCarrier_iff
        (pre ++ [step]) i).mp hi
    exact Finset.mem_sdiff.mpr
      ⟨(mem_r322AnalyticActiveCarrier_iff
          pre i).mpr
          (fun s hs =>
            hall s
              (List.mem_append_left [step] hs)),
        hall step
          (List.mem_append_right pre
            (by simp))⟩
  · intro hi
    have hparts := Finset.mem_sdiff.mp hi
    apply
      (mem_r322AnalyticActiveCarrier_iff
        (pre ++ [step]) i).mpr
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact
        (mem_r322AnalyticActiveCarrier_iff
          pre i).mp hparts.1 s hs
    · simpa only [List.mem_singleton] using
        (fun hsi : s = step => hsi ▸ hparts.2)
          (List.mem_singleton.mp hs)

/-- A scheduled step with smaller right endpoint lies in the displayed
prefix, rather than at or after the current step. -/
theorem r322AnalyticSchedule_mem_prefix_of_right_lt
    {m : ℕ} (κ : PartialPairing (Fin m))
    (pre suffix : List (R322ExtractionStep m))
    (step earlier : R322ExtractionStep m)
    (hschedule :
      r322AnalyticSchedule κ =
        pre ++ step :: suffix)
    (hearlier :
      earlier ∈ r322AnalyticSchedule κ)
    (hright : earlier.1.2 < step.1.2) :
    earlier ∈ pre := by
  have hp :=
    r322AnalyticSchedule_pairwise_right_lt κ
  rw [hschedule, List.pairwise_append] at hp
  rw [hschedule, List.mem_append] at hearlier
  rcases hearlier with hpre | hrest
  · exact hpre
  · rcases List.mem_cons.mp hrest with heq | hsuffix
    · subst earlier
      exact (lt_irrefl _ hright).elim
    · have hreverse :
          step.1.2 < earlier.1.2 :=
        (List.pairwise_cons.mp hp.2.1).1
          earlier hsuffix
      exact
        (not_lt_of_ge hright.le hreverse).elim

/-- Every block in the displayed prefix is disjoint from the next block. -/
theorem r322AnalyticSchedule_prefixBlock_disjoint_step
    {m : ℕ} (κ : PartialPairing (Fin m))
    (pre suffix : List (R322ExtractionStep m))
    (step earlier : R322ExtractionStep m)
    (hschedule :
      r322AnalyticSchedule κ =
        pre ++ step :: suffix)
    (hearlier : earlier ∈ pre) :
    Disjoint earlier.2 step.2 := by
  have hp :=
    r322AnalyticSchedule_blocks_pairwise_disjoint κ
  rw [hschedule, List.map_append,
    List.pairwise_append] at hp
  exact hp.2.2 earlier.2
    (List.mem_map.mpr
      ⟨earlier, hearlier, rfl⟩)
    step.2 (by simp)

/-- At any point of the analytic schedule, the next concrete block is the
endpoint interval relative to the current active carrier. -/
theorem r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
    {m : ℕ} (κ : PartialPairing (Fin m))
    (pre suffix : List (R322ExtractionStep m))
    (step : R322ExtractionStep m)
    (hschedule :
      r322AnalyticSchedule κ =
        pre ++ step :: suffix) :
    step.2 =
      r322AnalyticActiveCarrier pre ∩
        Finset.Icc step.1.1 step.1.2 := by
  have hstepMem :
      step ∈ r322AnalyticSchedule κ := by
    rw [hschedule]
    simp
  have hstepAligned :
      ExtractionPairBlockAligned step.1 step.2 :=
    r322AnalyticSchedule_forall_aligned
      κ step hstepMem
  apply Finset.Subset.antisymm
  · intro i hi
    apply Finset.mem_inter.mpr
    constructor
    · apply
        (mem_r322AnalyticActiveCarrier_iff
          pre i).mpr
      intro earlier hearlier hiEarlier
      exact
        (Finset.disjoint_left.mp
          (r322AnalyticSchedule_prefixBlock_disjoint_step
            κ pre suffix step earlier hschedule
            hearlier))
          hiEarlier hi
    · exact Finset.mem_Icc.mpr
        (hstepAligned.2.2 i hi)
  · intro i hi
    rcases Finset.mem_inter.mp hi with
      ⟨hiActive, hiIcc⟩
    by_contra hiStep
    have hstepRaw :
        step ∈
          r322ExtractionTraceAux κ m Finset.univ := by
      have hraw :
          step ∈
            (extract κ).zip (extractionBlocks κ) :=
        (List.mem_insertionSort
          R322StepRightLE).mp hstepMem
      simpa only [r322ExtractionTraceAux,
        extract, extractionBlocks] using hraw
    obtain
        ⟨rawPre, rawPost, hrawDecomp,
          earlier, hearlierPre, hiEarlier⟩ :=
      exists_previous_extractionStep_of_mem_Icc_not_mem
        κ m Finset.univ i (by simp) step hstepRaw
        hiIcc hiStep
    have hearlierRaw :
        earlier ∈
          r322ExtractionTraceAux κ m Finset.univ := by
      rw [hrawDecomp]
      exact List.mem_append_left _ hearlierPre
    have hearlierMem :
        earlier ∈ r322AnalyticSchedule κ := by
      apply
        (List.mem_insertionSort
          R322StepRightLE).mpr
      simpa only [r322ExtractionTraceAux,
        extract, extractionBlocks] using hearlierRaw
    have hearlierAligned :
        ExtractionPairBlockAligned
          earlier.1 earlier.2 :=
      r322AnalyticSchedule_forall_aligned
        κ earlier hearlierMem
    have hrawPairwise :=
      r322ExtractionTraceAux_pairwise_earlierCompatible
        κ m Finset.univ
    rw [hrawDecomp, List.pairwise_append] at hrawPairwise
    have hcompatible :
        EarlierReductionIntervalCompatible
          earlier.1 step.1 :=
      hrawPairwise.2.2 earlier hearlierPre
        step (by simp)
    have hiEarlierBounds :=
      hearlierAligned.2.2 i hiEarlier
    have hearlierRightLt :
        earlier.1.2 < step.1.2 := by
      rcases hcompatible with hleft | hright | hnested
      · have hiStepBounds :=
          Finset.mem_Icc.mp hiIcc
        exfalso
        omega
      · have hiStepBounds :=
          Finset.mem_Icc.mp hiIcc
        exfalso
        omega
      · exact hnested.2
    have hearlierPrefix :
        earlier ∈ pre :=
      r322AnalyticSchedule_mem_prefix_of_right_lt
        κ pre suffix step earlier hschedule
        hearlierMem hearlierRightLt
    exact
      ((mem_r322AnalyticActiveCarrier_iff
        pre i).mp hiActive earlier
        hearlierPrefix) hiEarlier

/-- Both endpoints of the next step are still active. -/
theorem r322AnalyticSchedule_step_endpoints_mem_activeCarrier
    {m : ℕ} (κ : PartialPairing (Fin m))
    (pre suffix : List (R322ExtractionStep m))
    (step : R322ExtractionStep m)
    (hschedule :
      r322AnalyticSchedule κ =
        pre ++ step :: suffix) :
    step.1.1 ∈ r322AnalyticActiveCarrier pre ∧
      step.1.2 ∈ r322AnalyticActiveCarrier pre := by
  have hstepMem :
      step ∈ r322AnalyticSchedule κ := by
    rw [hschedule]
    simp
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      κ step hstepMem
  rw [
    r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
      κ pre suffix step hschedule] at haligned
  exact
    ⟨(Finset.mem_inter.mp haligned.1).1,
      (Finset.mem_inter.mp haligned.2.1).1⟩

end Anderson4D
