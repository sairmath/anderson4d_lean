import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticActiveCarrierGeometry
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticScheduleLedger

/-!
# The full-pairing terminal schedule for the R-324 Step-1 branch

When a within-half pairing is full, its analytic R-322 schedule is nonempty
and ends at the unique scheduled block containing the last ambient vertex.
The terminal endpoint is therefore the global right endpoint, every preceding
step is earlier in paper order, and the terminal block is exactly the carrier
left after the preceding collapses.  This is the combinatorial schedule
package needed by the full/full branch of paper Section 4.2, without a
non-splitting hypothesis.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- A full pairing exhausts the active carrier after its complete analytic
schedule. -/
theorem r322AnalyticActiveCarrier_schedule_eq_empty_of_isFull
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull) :
    r322AnalyticActiveCarrier (r322AnalyticSchedule κ) = ∅ := by
  have hblocks :
      finsetUnionList
          ((r322AnalyticSchedule κ).map Prod.snd) =
        finsetUnionList (extractionBlocks κ) := by
    ext i
    simp only [mem_finsetUnionList_iff]
    constructor
    · rintro ⟨B, hB, hiB⟩
      exact
        ⟨B,
          (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).mem_iff.mp
            hB,
          hiB⟩
    · rintro ⟨B, hB, hiB⟩
      exact
        ⟨B,
          (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).mem_iff.mpr
            hB,
          hiB⟩
  unfold r322AnalyticActiveCarrier
  have hcover :
      finsetUnionList (extractionBlocks κ) =
        (Finset.univ : Finset (Fin m)) := by
    simpa only [extractionPrimitiveBlockPartition_blocks] using
      (extractionPrimitiveBlockPartition κ hκ).cover
  rw [hblocks, hcover, Finset.sdiff_self]

/-- The exact terminal data for one full within-half analytic schedule.
Unlike the non-splitting terminal package, the left endpoint is not required
to be zero: earlier primitive components may already have been removed. -/
structure R324FullPairingTerminalSchedule
    {m : ℕ} (κ : PartialPairing (Fin m)) where
  proper : List (R322ExtractionStep m)
  terminal : R322ExtractionStep m
  schedule_eq :
    r322AnalyticSchedule κ = proper ++ [terminal]
  terminal_right :
    terminal.1.2.val = m - 1
  proper_paperEarlier :
    ∀ step ∈ proper,
      R322PaperEarlier step.1 terminal.1
  terminal_block :
    terminal.2 = r322AnalyticActiveCarrier proper
  activeCarrier_schedule_eq_empty :
    r322AnalyticActiveCarrier (r322AnalyticSchedule κ) = ∅

/-- On an even ambient carrier, the proper-prefix orders and terminal order
retain the exact global perturbative ledger. -/
theorem R324FullPairingTerminalSchedule.sum_properBlockOrders_add_terminal
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    (data : R324FullPairingTerminalSchedule κ)
    (hκ : κ.IsFull) :
    (data.proper.map
        (fun step => residualBlockOrder step.2)).sum +
        residualBlockOrder data.terminal.2 =
      q :=
  sum_r322AnalyticSchedule_proper_add_terminal
    hκ data.proper data.terminal data.schedule_eq

/-- Every full pairing on a nonempty finite interval has a genuine last
analytic step with the exact terminal-carrier properties required in the
full/full R-324 branch. -/
theorem exists_r324FullPairingTerminalSchedule
    {m : ℕ} (hm : 1 ≤ m)
    (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull) :
    Nonempty (R324FullPairingTerminalSchedule κ) := by
  let last : Fin m := ⟨m - 1, by omega⟩
  obtain ⟨B, hB, hlastB⟩ :=
    (extractionPrimitiveBlockPartition κ hκ).exists_block_mem last
  have hBschedule :
      B ∈ (r322AnalyticSchedule κ).map Prod.snd :=
    (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).mem_iff.mpr hB
  obtain ⟨terminal, hterminalMem, hterminalBlock⟩ :=
    List.mem_map.mp hBschedule
  have hlastTerminal : last ∈ terminal.2 := by
    rw [hterminalBlock]
    exact hlastB
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      κ terminal hterminalMem
  have hterminalRight :
      terminal.1.2.val = m - 1 := by
    have hbounds := haligned.2.2 last hlastTerminal
    change terminal.1.1.val ≤ m - 1 ∧
      m - 1 ≤ terminal.1.2.val at hbounds
    have hlt := terminal.1.2.isLt
    omega
  obtain ⟨proper, suffix, hschedule⟩ :=
    List.mem_iff_append.mp hterminalMem
  have hsuffix : suffix = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro later hlater
    have hpairwise :
        (proper ++ terminal :: suffix).Pairwise
          (fun earlier later =>
            earlier.1.2 < later.1.2) := by
      rw [← hschedule]
      exact r322AnalyticSchedule_pairwise_right_lt κ
    have htail :
        (terminal :: suffix).Pairwise
          (fun earlier later =>
            earlier.1.2 < later.1.2) :=
      (List.pairwise_append.mp hpairwise).2.1
    have hright :
        terminal.1.2 < later.1.2 :=
      (List.pairwise_cons.mp htail).1 later hlater
    have hlaterLt := later.1.2.isLt
    change terminal.1.2.val < later.1.2.val at hright
    rw [hterminalRight] at hright
    omega
  subst suffix
  have hschedule' :
      r322AnalyticSchedule κ = proper ++ [terminal] := by
    simpa using hschedule
  have hproperEarlier :
      ∀ step ∈ proper,
        R322PaperEarlier step.1 terminal.1 := by
    have hpairwise :
        (proper ++ [terminal]).Pairwise
          (fun earlier later =>
            R322PaperEarlier earlier.1 later.1) := by
      rw [← hschedule']
      exact r322AnalyticSchedule_pairwise_paperEarlier κ
    intro step hstep
    exact
      (List.pairwise_append.mp hpairwise).2.2
        step hstep terminal (by simp)
  have hactiveFull :
      r322AnalyticActiveCarrier
          (r322AnalyticSchedule κ) = ∅ :=
    r322AnalyticActiveCarrier_schedule_eq_empty_of_isFull κ hκ
  have hactiveAfter :
      r322AnalyticActiveCarrier proper \ terminal.2 = ∅ := by
    rw [← r322AnalyticActiveCarrier_append_singleton,
      ← hschedule']
    exact hactiveFull
  have hterminalSubset :
      terminal.2 ⊆ r322AnalyticActiveCarrier proper := by
    have hblock :=
      r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
        κ proper [] terminal (by simpa using hschedule')
    rw [hblock]
    exact Finset.inter_subset_left
  have hterminalCarrier :
      terminal.2 = r322AnalyticActiveCarrier proper := by
    apply Finset.Subset.antisymm hterminalSubset
    exact Finset.sdiff_eq_empty_iff_subset.mp hactiveAfter
  exact
    ⟨{
      proper := proper
      terminal := terminal
      schedule_eq := hschedule'
      terminal_right := hterminalRight
      proper_paperEarlier := hproperEarlier
      terminal_block := hterminalCarrier
      activeCarrier_schedule_eq_empty := hactiveFull
    }⟩

end

end Anderson4D
