import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticSchedule
import Anderson4D.DetParametrix.Core.Constants

/-!
# Coordinate independence for one analytic R-322 head block

The analytic schedule removes an innermost primitive block before every
interval which contains it.  For a head step `s = (p,B)` and a later step
`t = (q,C)`, the only coordinates read by the later generalized difference
factor are `q.1`, `q.2`, and (when it exists) `q.2 + 1`.  This file proves
that all three lie outside `B` under the exact disjoint-right/containing
interval dichotomy.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

/-! ## The three later difference coordinates avoid the head block -/

/-- The endpoints of an aligned later extraction step are ordered. -/
theorem r322ExtractionStep_fst_le_snd
    {m : ℕ} (t : R322ExtractionStep m)
    (ht : ExtractionPairBlockAligned t.1 t.2) :
    t.1.1 ≤ t.1.2 :=
  (ht.2.2 t.1.1 ht.1).2

/-- Under the analytic disjoint-right/containing dichotomy, the later left
endpoint does not belong to the head block. -/
theorem r322AnalyticLater_left_not_mem_headBlock
    {m : ℕ} (s t : R322ExtractionStep m)
    (hs : ExtractionPairBlockAligned s.1 s.2)
    (hrel :
      s.1.2 < t.1.1 ∨
        (t.1.1 < s.1.1 ∧ s.1.2 < t.1.2)) :
    t.1.1 ∉ s.2 := by
  intro hmem
  have hbounds := hs.2.2 t.1.1 hmem
  rcases hrel with hright | hcontains
  · exact (not_lt_of_ge hbounds.2) hright
  · exact (not_lt_of_ge hbounds.1) hcontains.1

/-- The later right endpoint is strictly to the right of the head right
endpoint. -/
theorem r322AnalyticHead_right_lt_laterRight
    {m : ℕ} (s t : R322ExtractionStep m)
    (ht : ExtractionPairBlockAligned t.1 t.2)
    (hrel :
      s.1.2 < t.1.1 ∨
        (t.1.1 < s.1.1 ∧ s.1.2 < t.1.2)) :
    s.1.2 < t.1.2 := by
  rcases hrel with hright | hcontains
  · exact hright.trans_le
      (r322ExtractionStep_fst_le_snd t ht)
  · exact hcontains.2

/-- Consequently the later right endpoint does not belong to the head
block. -/
theorem r322AnalyticLater_right_not_mem_headBlock
    {m : ℕ} (s t : R322ExtractionStep m)
    (hs : ExtractionPairBlockAligned s.1 s.2)
    (ht : ExtractionPairBlockAligned t.1 t.2)
    (hrel :
      s.1.2 < t.1.1 ∨
        (t.1.1 < s.1.1 ∧ s.1.2 < t.1.2)) :
    t.1.2 ∉ s.2 := by
  intro hmem
  have hupper := (hs.2.2 t.1.2 hmem).2
  exact
    (not_lt_of_ge hupper)
      (r322AnalyticHead_right_lt_laterRight
        s t ht hrel)

/-- The third coordinate read by `diffFactorJWith`, namely the successor of
the later right endpoint, also lies outside the head block. -/
theorem r322AnalyticLater_rightSucc_not_mem_headBlock
    {m : ℕ} (s t : R322ExtractionStep m)
    (hs : ExtractionPairBlockAligned s.1 s.2)
    (ht : ExtractionPairBlockAligned t.1 t.2)
    (hrel :
      s.1.2 < t.1.1 ∨
        (t.1.1 < s.1.1 ∧ s.1.2 < t.1.2))
    (hguard : t.1.2.val + 1 < m) :
    (⟨t.1.2.val + 1, hguard⟩ : Fin m) ∉ s.2 := by
  intro hmem
  have hupper :=
    (hs.2.2
      (⟨t.1.2.val + 1, hguard⟩ : Fin m) hmem).2
  have hright :=
    r322AnalyticHead_right_lt_laterRight
      s t ht hrel
  change t.1.2.val + 1 ≤ s.1.2.val at hupper
  change s.1.2.val < t.1.2.val at hright
  omega

/-- Bundled form matching the three actual tuple reads in a later
generalized difference factor. -/
theorem r322AnalyticLater_diffCoordinates_not_mem_headBlock
    {m : ℕ} (s t : R322ExtractionStep m)
    (hs : ExtractionPairBlockAligned s.1 s.2)
    (ht : ExtractionPairBlockAligned t.1 t.2)
    (hrel :
      s.1.2 < t.1.1 ∨
        (t.1.1 < s.1.1 ∧ s.1.2 < t.1.2)) :
    t.1.1 ∉ s.2 ∧
      t.1.2 ∉ s.2 ∧
      ∀ hguard : t.1.2.val + 1 < m,
        (⟨t.1.2.val + 1, hguard⟩ : Fin m) ∉ s.2 :=
  ⟨r322AnalyticLater_left_not_mem_headBlock s t hs hrel,
    r322AnalyticLater_right_not_mem_headBlock s t hs ht hrel,
    r322AnalyticLater_rightSucc_not_mem_headBlock
      s t hs ht hrel⟩

/-! ## Later differences are independent of head-block variables -/

/-- If two tuples agree away from the head block, every later generalized
difference factor has exactly the same value. -/
theorem diffFactorJWith_eq_of_eq_outside_analyticHeadBlock
    {m : ℕ}
    (G : Fin (m - 1) → T4 → ℝ)
    (x y : Fin m → T4)
    (s t : R322ExtractionStep m)
    (hs : ExtractionPairBlockAligned s.1 s.2)
    (ht : ExtractionPairBlockAligned t.1 t.2)
    (hrel :
      s.1.2 < t.1.1 ∨
        (t.1.1 < s.1.1 ∧ s.1.2 < t.1.2))
    (hxy : ∀ i, i ∉ s.2 → x i = y i) :
    diffFactorJWith G x t.1 =
      diffFactorJWith G y t.1 := by
  obtain ⟨hleft, hright, hsucc⟩ :=
    r322AnalyticLater_diffCoordinates_not_mem_headBlock
      s t hs ht hrel
  unfold diffFactorJWith
  split
  · rw [hxy t.1.2 hright,
      hxy t.1.1 hleft,
      hxy
        (⟨t.1.2.val + 1, by omega⟩ : Fin m)
        (hsucc (by omega))]
  · rfl

/-- Free-Green specialization of the same independence statement. -/
theorem diffFactorJ_eq_of_eq_outside_analyticHeadBlock
    {m : ℕ}
    (x y : Fin m → T4)
    (s t : R322ExtractionStep m)
    (hs : ExtractionPairBlockAligned s.1 s.2)
    (ht : ExtractionPairBlockAligned t.1 t.2)
    (hrel :
      s.1.2 < t.1.1 ∨
        (t.1.1 < s.1.1 ∧ s.1.2 < t.1.2))
    (hxy : ∀ i, i ∉ s.2 → x i = y i) :
    diffFactorJ x t.1 =
      diffFactorJ y t.1 := by
  rw [← diffFactorJWith_green x t.1,
    ← diffFactorJWith_green y t.1]
  exact
    diffFactorJWith_eq_of_eq_outside_analyticHeadBlock
      (fun _ => greenFn) x y s t hs ht hrel hxy

/-! ## The head outgoing coordinate is external to its own block -/

/-- In the proper guarded case, the successor of the head right endpoint
is outside the aligned head block. -/
theorem r322AnalyticHead_rightSucc_not_mem_headBlock
    {m : ℕ} (s : R322ExtractionStep m)
    (hs : ExtractionPairBlockAligned s.1 s.2)
    (hguard : s.1.2.val + 1 < m) :
    (⟨s.1.2.val + 1, hguard⟩ : Fin m) ∉ s.2 := by
  intro hmem
  have hupper :=
    (hs.2.2
      (⟨s.1.2.val + 1, hguard⟩ : Fin m) hmem).2
  change s.1.2.val + 1 ≤ s.1.2.val at hupper
  omega

end

end Anderson4D
