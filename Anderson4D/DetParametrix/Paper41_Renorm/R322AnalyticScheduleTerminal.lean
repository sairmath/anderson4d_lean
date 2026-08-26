import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticScheduleGeometry

/-!
# Terminal structure of the R-322 analytic schedule

For a non-splitting full pairing, the whole-interval endpoint pair occurs in
the extraction list.  It cannot precede any other interval in paper order, so
the analytic schedule consists of a (possibly empty) proper prefix followed by
one terminal step with that endpoint pair.  The terminal step's concrete block
is intentionally left unspecified: it is the residual trace after the proper
collapses, not the original full carrier.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

/-- The endpoint pair spanning the full carrier of a nonempty pairing. -/
def r322WholeEndpoint (q : ℕ) (hq : 1 ≤ q) :
    Fin (2 * q) × Fin (2 * q) :=
  ((⟨0, by omega⟩ : Fin (2 * q)),
    (⟨2 * q - 1, by omega⟩ : Fin (2 * q)))

/-- A whole-interval endpoint cannot occur before another interval in the
paper's analytic order. -/
theorem r322WholeEndpoint_not_paperEarlier
    (q : ℕ) (hq : 1 ≤ q)
    (p : Fin (2 * q) × Fin (2 * q)) :
    ¬R322PaperEarlier (r322WholeEndpoint q hq) p := by
  unfold R322PaperEarlier r322WholeEndpoint
  change
    ¬((2 * q - 1 < p.1.val) ∨
      (p.1.val < 0 ∧
        2 * q - 1 < p.2.val))
  have hp1 := p.1.isLt
  have hp2 := p.2.isLt
  omega

private theorem list_eq_prefix_append_singleton_of_terminal'
    {α : Type*} {R : α → α → Prop}
    {xs : List α} {x : α}
    (hpairwise : xs.Pairwise R)
    (hx : x ∈ xs)
    (hterminal : ∀ y, R x y → False) :
    ∃ pre, xs = pre ++ [x] := by
  induction xs with
  | nil =>
      simp at hx
  | cons a xs ih =>
      rw [List.pairwise_cons] at hpairwise
      simp only [List.mem_cons] at hx
      rcases hx with hax | hx
      · subst a
        have hnil : xs = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro y hy
          exact hterminal y (hpairwise.1 y hy)
        subst xs
        exact ⟨[], rfl⟩
      · obtain ⟨pre, hpre⟩ :=
          ih hpairwise.2 hx
        exact
          ⟨a :: pre, by
            rw [hpre]
            rfl⟩

/-! ## Proper-prefix / terminal decomposition -/

/-- A non-splitting analytic schedule is a proper prefix followed by a step
whose endpoint is the whole interval.  No prefix endpoint is the whole
interval. -/
theorem r322AnalyticSchedule_eq_proper_append_terminal_of_isNonSplit
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    (hq : 1 ≤ q) (hκ : IsNonSplit κ) :
    ∃ (proper : List (R322ExtractionStep (2 * q)))
        (terminal : R322ExtractionStep (2 * q)),
      r322AnalyticSchedule κ =
          proper ++ [terminal] ∧
        terminal.1 = r322WholeEndpoint q hq ∧
        ∀ s ∈ proper,
          s.1 ≠ r322WholeEndpoint q hq := by
  have hwholeExtract :
      r322WholeEndpoint q hq ∈ extract κ := by
    simpa only [r322WholeEndpoint] using
      whole_pair_mem_extract_of_isNonSplit hq hκ
  have hwholeScheduled :
      r322WholeEndpoint q hq ∈
        (r322AnalyticSchedule κ).map Prod.fst := by
    exact
      (r322AnalyticSchedule_endpoints_perm_extract κ).mem_iff.mpr
        hwholeExtract
  obtain ⟨terminal, hterminalMem, hterminalEndpoint⟩ :=
    List.mem_map.mp hwholeScheduled
  obtain ⟨proper, hdecomp⟩ :=
    list_eq_prefix_append_singleton_of_terminal'
      (r322AnalyticSchedule_pairwise_paperEarlier κ)
      hterminalMem
      (fun later hlater =>
        r322WholeEndpoint_not_paperEarlier q hq later.1
          (by
            simpa only [hterminalEndpoint] using hlater))
  refine
    ⟨proper, terminal, hdecomp,
      hterminalEndpoint, ?_⟩
  intro s hs hwhole
  have hpairwise :
      (proper ++ [terminal]).Pairwise
        (fun earlier later =>
          R322PaperEarlier earlier.1 later.1) := by
    rw [← hdecomp]
    exact r322AnalyticSchedule_pairwise_paperEarlier κ
  have hcross :
      R322PaperEarlier s.1 terminal.1 :=
    (List.pairwise_append.mp hpairwise).2.2
      s hs terminal (by simp)
  rw [hwhole, hterminalEndpoint] at hcross
  exact
    r322WholeEndpoint_not_paperEarlier q hq
      (r322WholeEndpoint q hq) hcross

/-! ## Head/tail interface for the collapse induction -/

/-- At the head of a non-splitting schedule, an empty tail means that the
head is the terminal whole-interval step; a nonempty tail means that the head
is proper. -/
theorem r322AnalyticSchedule_head_proper_or_terminal
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    (hq : 1 ≤ q) (hκ : IsNonSplit κ)
    {head : R322ExtractionStep (2 * q)}
    {tail : List (R322ExtractionStep (2 * q))}
    (hschedule :
      r322AnalyticSchedule κ = head :: tail) :
    (tail = [] ∧
        head.1 = r322WholeEndpoint q hq) ∨
      (tail ≠ [] ∧
        head.1 ≠ r322WholeEndpoint q hq) := by
  obtain
      ⟨proper, terminal, hdecomp,
        hterminal, hproper⟩ :=
    r322AnalyticSchedule_eq_proper_append_terminal_of_isNonSplit
      hq hκ
  have heq :
      head :: tail = proper ++ [terminal] :=
    hschedule.symm.trans hdecomp
  cases proper with
  | nil =>
      simp only [List.nil_append] at heq
      have hhead : head = terminal :=
        List.cons.inj heq |>.1
      have htail : tail = [] :=
        List.cons.inj heq |>.2
      exact
        Or.inl
          ⟨htail, hhead ▸ hterminal⟩
  | cons first rest =>
      simp only [List.cons_append] at heq
      have hhead : head = first :=
        List.cons.inj heq |>.1
      have htail :
          tail = rest ++ [terminal] :=
        List.cons.inj heq |>.2
      exact
        Or.inr
          ⟨by
            rw [htail]
            simp,
            hhead ▸ hproper first (by simp)⟩

end Anderson4D
