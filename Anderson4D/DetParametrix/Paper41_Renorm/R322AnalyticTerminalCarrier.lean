import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticEdgeState

/-!
# The terminal carrier of the R-322 analytic schedule

The proper-prefix/terminal decomposition ends with the whole endpoint
interval.  Relative to the carrier left after the proper prefix, the
terminal concrete block is therefore the entire remaining carrier.  These
identities are the structural terminal case needed by the analytic iteration.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

/-- A scheduled whole-interval step occupies precisely the carrier which
remains after its prefix. -/
theorem r322AnalyticTerminal_block_eq_activeCarrier
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (proper : List (R322ExtractionStep (2 * q)))
    (terminal : R322ExtractionStep (2 * q))
    (hschedule :
      r322AnalyticSchedule κ = proper ++ [terminal])
    (hterminal :
      terminal.1 = r322WholeEndpoint q hq) :
    terminal.2 = r322AnalyticActiveCarrier proper := by
  letI : NeZero (2 * q) := ⟨by omega⟩
  have hblock :=
    r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
      κ proper [] terminal (by simpa using hschedule)
  rw [hblock]
  ext i
  simp only [Finset.mem_inter, and_iff_left_iff_imp]
  intro _hi
  rw [hterminal]
  change
    i ∈ Finset.Icc
      (⟨0, by omega⟩ : Fin (2 * q))
      (⟨2 * q - 1, by omega⟩ : Fin (2 * q))
  apply Finset.mem_Icc.mpr
  constructor <;> apply Fin.mk_le_mk.mpr
  · omega
  · have hi := i.isLt
    omega

/-- Processing the terminal whole-interval block exhausts the active
carrier. -/
theorem r322AnalyticActiveCarrier_after_terminal_eq_empty
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (proper : List (R322ExtractionStep (2 * q)))
    (terminal : R322ExtractionStep (2 * q))
    (hschedule :
      r322AnalyticSchedule κ = proper ++ [terminal])
    (hterminal :
      terminal.1 = r322WholeEndpoint q hq) :
    r322AnalyticActiveCarrier (proper ++ [terminal]) = ∅ := by
  rw [r322AnalyticActiveCarrier_append_singleton,
    r322AnalyticTerminal_block_eq_activeCarrier
      hq κ proper terminal hschedule hterminal,
    Finset.sdiff_self]

/-- The terminal block of every non-splitting schedule is exactly its
remaining carrier, and the complete schedule removes every vertex. -/
theorem exists_r322AnalyticTerminalCarrier_of_isNonSplit
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : IsNonSplit κ) :
    ∃ (proper : List (R322ExtractionStep (2 * q)))
        (terminal : R322ExtractionStep (2 * q)),
      r322AnalyticSchedule κ = proper ++ [terminal] ∧
        terminal.1 = r322WholeEndpoint q hq ∧
        (∀ s ∈ proper,
          s.1 ≠ r322WholeEndpoint q hq) ∧
        terminal.2 = r322AnalyticActiveCarrier proper ∧
        r322AnalyticActiveCarrier
          (r322AnalyticSchedule κ) = ∅ := by
  obtain ⟨proper, terminal, hschedule, hterminal, hproper⟩ :=
    r322AnalyticSchedule_eq_proper_append_terminal_of_isNonSplit
      hq hκ
  refine
    ⟨proper, terminal, hschedule, hterminal, hproper,
      r322AnalyticTerminal_block_eq_activeCarrier
        hq κ proper terminal hschedule hterminal, ?_⟩
  rw [hschedule]
  exact
    r322AnalyticActiveCarrier_after_terminal_eq_empty
      hq κ proper terminal hschedule hterminal

end Anderson4D
