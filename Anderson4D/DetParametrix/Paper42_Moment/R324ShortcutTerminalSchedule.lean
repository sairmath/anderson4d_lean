import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticScheduleGeometry
import Anderson4D.DetParametrix.Paper42_Moment.R324DetIntegrability

/-!
# Terminal schedule for the R-324 outgoing-shortcut branch

If the final chain edge belongs to the extracted-edge set of a partial
pairing, the strict right-endpoint order on the analytic schedule forces its
unique corresponding extraction step to be last.  This file packages that
proper-prefix/terminal decomposition without assuming that the pairing is
full.  In particular, it deliberately records no claim that the terminal
block exhausts the active carrier.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- The proper-prefix/terminal decomposition of an analytic schedule whose
final extracted right edge is the outgoing chain edge. -/
structure R324ShortcutTerminalSchedule
    {m : ℕ} (κ : PartialPairing (Fin m)) where
  proper : List (R322ExtractionStep m)
  terminal : R322ExtractionStep m
  schedule_eq :
    r322AnalyticSchedule κ = proper ++ [terminal]
  terminal_extractedRightEdge_eq_last :
    extractedRightEdge terminal.1 = Fin.last m

namespace R324ShortcutTerminalSchedule

variable {m : ℕ} {κ : PartialPairing (Fin m)}

/-- The right endpoint of the terminal extracted interval is the final
internal vertex. -/
theorem terminal_right
    (data : R324ShortcutTerminalSchedule κ) :
    data.terminal.1.2.val = m - 1 := by
  have hedge :=
    congrArg Fin.val
      data.terminal_extractedRightEdge_eq_last
  simp only [extractedRightEdge_val, Fin.val_last] at hedge
  have hlt := data.terminal.1.2.isLt
  omega

/-- The distinguished terminal step occurs in the analytic schedule. -/
theorem terminal_mem_schedule
    (data : R324ShortcutTerminalSchedule κ) :
    data.terminal ∈ r322AnalyticSchedule κ := by
  rw [data.schedule_eq]
  simp

/-- Every step in the proper prefix occurs in the analytic schedule. -/
theorem mem_schedule_of_mem_proper
    (data : R324ShortcutTerminalSchedule κ)
    {step : R322ExtractionStep m}
    (hstep : step ∈ data.proper) :
    step ∈ r322AnalyticSchedule κ := by
  rw [data.schedule_eq]
  exact List.mem_append.mpr (Or.inl hstep)

/-- The endpoint pair of the terminal step belongs to the extraction list. -/
theorem terminal_endpoint_mem_extract
    (data : R324ShortcutTerminalSchedule κ) :
    data.terminal.1 ∈ extract κ :=
  r322AnalyticSchedule_endpoint_mem_extract κ
    data.terminal_mem_schedule

/-- Every endpoint pair in the proper prefix belongs to the extraction
list. -/
theorem proper_endpoint_mem_extract
    (data : R324ShortcutTerminalSchedule κ)
    {step : R322ExtractionStep m}
    (hstep : step ∈ data.proper) :
    step.1 ∈ extract κ :=
  r322AnalyticSchedule_endpoint_mem_extract κ
    (data.mem_schedule_of_mem_proper hstep)

/-- The outgoing edge is indeed present in the extracted-edge set. -/
theorem last_mem_extractedRightEdges
    (data : R324ShortcutTerminalSchedule κ) :
    Fin.last m ∈ extractedRightEdges κ := by
  rw [← data.terminal_extractedRightEdge_eq_last]
  exact
    extractedRightEdge_mem_extractedRightEdges
      κ data.terminal.1 data.terminal_endpoint_mem_extract

/-- No step in the proper prefix extracts the outgoing chain edge. -/
theorem proper_extractedRightEdge_ne_last
    (data : R324ShortcutTerminalSchedule κ)
    (step : R322ExtractionStep m)
    (hstep : step ∈ data.proper) :
    extractedRightEdge step.1 ≠ Fin.last m := by
  intro hedge
  have hpairwise :
      (data.proper ++ [data.terminal]).Pairwise
        (fun earlier later =>
          earlier.1.2 < later.1.2) := by
    rw [← data.schedule_eq]
    exact r322AnalyticSchedule_pairwise_right_lt κ
  have hright :
      step.1.2 < data.terminal.1.2 :=
    (List.pairwise_append.mp hpairwise).2.2
      step hstep data.terminal (by simp)
  have hstepEdge := congrArg Fin.val hedge
  have hterminalEdge :=
    congrArg Fin.val
      data.terminal_extractedRightEdge_eq_last
  simp only [extractedRightEdge_val, Fin.val_last] at hstepEdge hterminalEdge
  change step.1.2.val < data.terminal.1.2.val at hright
  omega

/-- The distinguished terminal is the unique scheduled step extracting the
outgoing chain edge. -/
theorem eq_terminal_of_mem_schedule_of_extractedRightEdge_eq_last
    (data : R324ShortcutTerminalSchedule κ)
    (step : R322ExtractionStep m)
    (hstep : step ∈ r322AnalyticSchedule κ)
    (hedge : extractedRightEdge step.1 = Fin.last m) :
    step = data.terminal := by
  rw [data.schedule_eq] at hstep
  rcases List.mem_append.mp hstep with hproper | hterminal
  · exact
      (data.proper_extractedRightEdge_ne_last
        step hproper hedge).elim
  · simpa using hterminal

/-- The proper-prefix/terminal decomposition is unique. -/
theorem unique
    (left right : R324ShortcutTerminalSchedule κ) :
    left = right := by
  have happend :
      left.proper ++ [left.terminal] =
        right.proper ++ [right.terminal] :=
    left.schedule_eq.symm.trans right.schedule_eq
  have hreverse := congrArg List.reverse happend
  have hcons :
      left.terminal :: left.proper.reverse =
        right.terminal :: right.proper.reverse := by
    simpa only [List.reverse_append, List.reverse_singleton,
      List.singleton_append] using hreverse
  have hterminal : left.terminal = right.terminal :=
    (List.cons.inj hcons).1
  have hproper : left.proper = right.proper := by
    have htails := (List.cons.inj hcons).2
    have hreversed := congrArg List.reverse htails
    simpa only [List.reverse_reverse] using hreversed
  cases left
  cases right
  simp_all

end R324ShortcutTerminalSchedule

/-- If the outgoing chain edge is extracted, strict schedule order produces
the canonical terminal decomposition without any fullness assumption. -/
theorem exists_r324ShortcutTerminalSchedule
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hshortcut : Fin.last m ∈ extractedRightEdges κ) :
    Nonempty (R324ShortcutTerminalSchedule κ) := by
  let p :=
    extractedPairOfRightEdge κ (Fin.last m) hshortcut
  have hpExtract : p ∈ extract κ :=
    extractedPairOfRightEdge_mem
      κ (Fin.last m) hshortcut
  have hpEdge : extractedRightEdge p = Fin.last m :=
    extractedRightEdge_extractedPairOfRightEdge
      κ (Fin.last m) hshortcut
  have hpScheduled :
      p ∈ (r322AnalyticSchedule κ).map Prod.fst :=
    (r322AnalyticSchedule_endpoints_perm_extract κ).mem_iff.mpr
      hpExtract
  obtain ⟨terminal, hterminalMem, hterminalEndpoint⟩ :=
    List.mem_map.mp hpScheduled
  have hterminalEdge :
      extractedRightEdge terminal.1 = Fin.last m := by
    rw [hterminalEndpoint]
    exact hpEdge
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
    have hterminalVal := congrArg Fin.val hterminalEdge
    simp only [extractedRightEdge_val, Fin.val_last] at hterminalVal
    have hlaterLt := later.1.2.isLt
    change terminal.1.2.val < later.1.2.val at hright
    omega
  subst suffix
  exact
    ⟨{
      proper := proper
      terminal := terminal
      schedule_eq := by simpa using hschedule
      terminal_extractedRightEdge_eq_last := hterminalEdge
    }⟩

/-- There is exactly one scheduled step whose extracted right edge is the
outgoing chain edge. -/
theorem existsUnique_r324ShortcutTerminalStep
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hshortcut : Fin.last m ∈ extractedRightEdges κ) :
    ∃! terminal : R322ExtractionStep m,
      terminal ∈ r322AnalyticSchedule κ ∧
        extractedRightEdge terminal.1 = Fin.last m := by
  obtain ⟨data⟩ :=
    exists_r324ShortcutTerminalSchedule κ hshortcut
  refine
    ⟨data.terminal,
      ⟨data.terminal_mem_schedule,
        data.terminal_extractedRightEdge_eq_last⟩, ?_⟩
  intro step hstep
  exact
    data.eq_terminal_of_mem_schedule_of_extractedRightEdge_eq_last
      step hstep.1 hstep.2

end

end Anderson4D
