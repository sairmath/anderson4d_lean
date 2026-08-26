import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticSchedule

/-!
# Geometry of the R-322 analytic schedule

The right-endpoint sort is useful only after reconnecting every scheduled
endpoint pair with the laminar extraction geometry.  This file proves that an
earlier scheduled interval is either strictly to the left of a later one, or
is strictly contained in it.  These are precisely the two geometric branches
that support the paper's inside-to-outside analytic collapse.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

/-- Paper-order geometry: the earlier interval is either strictly to the left
of the later interval, or strictly contained in it. -/
def R322PaperEarlier {m : ℕ}
    (p q : Fin m × Fin m) : Prop :=
  p.2 < q.1 ∨
    (q.1 < p.1 ∧ p.2 < q.2)

/-! ## Returning scheduled endpoints to the extraction list -/

/-- Every endpoint pair appearing in the analytic schedule still belongs to
the original extraction list. -/
theorem r322AnalyticSchedule_endpoint_mem_extract
    {m : ℕ} (κ : PartialPairing (Fin m))
    {s : R322ExtractionStep m}
    (hs : s ∈ r322AnalyticSchedule κ) :
    s.1 ∈ extract κ := by
  apply
    (r322AnalyticSchedule_endpoints_perm_extract κ).mem_iff.mp
  exact List.mem_map.mpr ⟨s, hs, rfl⟩

/-- Endpoint membership specialized to a list index. -/
theorem r322AnalyticSchedule_get_endpoint_mem_extract
    {m : ℕ} (κ : PartialPairing (Fin m))
    (i : Fin (r322AnalyticSchedule κ).length) :
    ((r322AnalyticSchedule κ).get i).1 ∈
      extract κ := by
  exact
    r322AnalyticSchedule_endpoint_mem_extract κ
      (List.get_mem _ i)

/-- Both endpoint pairs at two schedule indices belong to the original
extraction list. -/
theorem r322AnalyticSchedule_get_endpoints_mem_extract
    {m : ℕ} (κ : PartialPairing (Fin m))
    (i j : Fin (r322AnalyticSchedule κ).length) :
    ((r322AnalyticSchedule κ).get i).1 ∈ extract κ ∧
      ((r322AnalyticSchedule κ).get j).1 ∈ extract κ := by
  exact
    ⟨r322AnalyticSchedule_get_endpoint_mem_extract κ i,
      r322AnalyticSchedule_get_endpoint_mem_extract κ j⟩

/-! ## Indexed strict order -/

/-- Any earlier list index has a strictly smaller right endpoint. -/
theorem r322AnalyticSchedule_get_right_lt
    {m : ℕ} (κ : PartialPairing (Fin m))
    {i j : Fin (r322AnalyticSchedule κ).length}
    (hij : i < j) :
    ((r322AnalyticSchedule κ).get i).1.2 <
      ((r322AnalyticSchedule κ).get j).1.2 := by
  exact
    (r322AnalyticSchedule_pairwise_right_lt κ).rel_get_of_lt
      hij

/-! ## Laminarity independent of the selector's original list order -/

/-- Two distinct members of the extraction list are laminar, independently
of which one occurred first in the selector recursion. -/
theorem extract_laminar_of_mem_of_ne'
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {p q : Fin m × Fin m}
    (hp : p ∈ extract κ) (hq : q ∈ extract κ)
    (hpq : p ≠ q) :
    ReductionIntervalsLaminar p q := by
  obtain ⟨i, hi⟩ := List.get_of_mem hp
  obtain ⟨j, hj⟩ := List.get_of_mem hq
  have hij : i ≠ j := by
    intro hij
    apply hpq
    rw [← hi, ← hj, hij]
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hrel :=
      (extract_pairwise_laminar κ).rel_get_of_lt hij
    simpa only [hi, hj] using hrel
  · have hrel :=
      (extract_pairwise_laminar κ).rel_get_of_lt hji
    have hqp : ReductionIntervalsLaminar q p := by
      simpa only [hi, hj] using hrel
    exact hqp.symm

/-- Scheduled endpoint intervals are pairwise laminar. -/
theorem r322AnalyticSchedule_pairwise_laminar
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    (r322AnalyticSchedule κ).Pairwise
      (fun s t =>
        ReductionIntervalsLaminar s.1 t.1) := by
  apply
    (r322AnalyticSchedule_pairwise_right_lt κ).imp_of_mem
  intro s t hs ht hright
  have hsmem :=
    r322AnalyticSchedule_endpoint_mem_extract κ hs
  have htmem :=
    r322AnalyticSchedule_endpoint_mem_extract κ ht
  apply extract_laminar_of_mem_of_ne' hsmem htmem
  intro heq
  have hrightEq :
      s.1.2 = t.1.2 :=
    congrArg Prod.snd heq
  exact (ne_of_lt hright) hrightEq

/-! ## The two admissible paper-order branches -/

/-- Combining laminarity with increasing right endpoints eliminates the two
geometrically impossible branches. -/
theorem r322AnalyticSchedule_pairwise_paperEarlier
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    (r322AnalyticSchedule κ).Pairwise
      (fun s t => R322PaperEarlier s.1 t.1) := by
  have hright :=
    r322AnalyticSchedule_pairwise_right_lt κ
  have hlam :=
    r322AnalyticSchedule_pairwise_laminar κ
  apply (hright.and hlam).imp_of_mem
  intro s t hs _ hgeometry
  rcases hgeometry with ⟨hright, hlaminar⟩
  have hsmem :
      s.1 ∈ extract κ :=
    r322AnalyticSchedule_endpoint_mem_extract κ hs
  have hsstrict :=
    extract_mem_fst_lt_snd κ s.1 hsmem
  rcases hlaminar with hleft | hlaterLeft |
      hearlierContains | hlaterContains
  · exact Or.inl hleft
  · exfalso
    omega
  · exfalso
    omega
  · exact Or.inr hlaterContains

/-- Indexed form of the paper-order geometry. -/
theorem r322AnalyticSchedule_get_paperEarlier
    {m : ℕ} (κ : PartialPairing (Fin m))
    {i j : Fin (r322AnalyticSchedule κ).length}
    (hij : i < j) :
    R322PaperEarlier
      ((r322AnalyticSchedule κ).get i).1
      ((r322AnalyticSchedule κ).get j).1 := by
  exact
    (r322AnalyticSchedule_pairwise_paperEarlier κ).rel_get_of_lt
      hij

/-- Head/tail form consumed by an inside-to-outside collapse induction. -/
theorem r322AnalyticSchedule_head_later_right_or_contains
    {m : ℕ} (κ : PartialPairing (Fin m))
    {head : R322ExtractionStep m}
    {tail : List (R322ExtractionStep m)}
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    {later : R322ExtractionStep m}
    (hlater : later ∈ tail) :
    head.1.2 < later.1.1 ∨
      (later.1.1 < head.1.1 ∧
        head.1.2 < later.1.2) := by
  have hpairwise :
      (head :: tail).Pairwise
        (fun s t => R322PaperEarlier s.1 t.1) := by
    rw [← hschedule]
    exact r322AnalyticSchedule_pairwise_paperEarlier κ
  exact
    (List.pairwise_cons.mp hpairwise).1 later hlater

end Anderson4D
