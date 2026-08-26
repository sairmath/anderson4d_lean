import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticScheduleTerminal
import Anderson4D.DetParametrix.Paper41_Renorm.R322ReductionClosure

/-!
# Exact order ledger for the R-322 analytic schedule

Sorting the extraction trace by paper order changes neither its block
orders nor their sum.  This module records that equality, its length
consequence, and the proper-prefix/terminal form used by the all-order
collapse.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- The perturbative orders in the paper-sorted analytic schedule add
exactly to the ambient order. -/
theorem sum_r322AnalyticSchedule_blockOrders_of_full
    {q : ℕ} (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ.IsFull) :
    ((r322AnalyticSchedule κ).map
      (fun s => residualBlockOrder s.2)).sum = q := by
  have hperm :=
    (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).map
      residualBlockOrder
  have hsum := hperm.sum_eq
  simpa only [List.map_map, Function.comp_def,
    sum_extractionBlockOrders_of_full κ hκ] using hsum

/-- Every scheduled block has positive perturbative order. -/
theorem r322AnalyticSchedule_blockOrder_pos
    {q : ℕ} (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ.IsFull)
    (s : R322ExtractionStep (2 * q))
    (hs : s ∈ r322AnalyticSchedule κ) :
    0 < residualBlockOrder s.2 := by
  have hB : s.2 ∈ extractionBlocks κ :=
    (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).mem_iff.mp
      (List.mem_map.mpr ⟨s, hs, rfl⟩)
  exact
    (extractionPrimitiveBlockPartition κ hκ).one_le_blockOrder hB

/-- A finite list of positive natural numbers has length at most its
sum. -/
private theorem r322Schedule_length_le_sum_of_pos
    (orders : List ℕ)
    (hpos : ∀ n ∈ orders, 0 < n) :
    orders.length ≤ orders.sum := by
  induction orders with
  | nil => simp
  | cons n orders ih =>
      have hn : 0 < n := hpos n (List.mem_cons_self)
      have htail : ∀ k ∈ orders, 0 < k :=
        fun k hk => hpos k (List.mem_cons_of_mem n hk)
      have hih := ih htail
      simp only [List.length_cons, List.sum_cons]
      omega

/-- Hence a full analytic schedule has at most one step per unit of
ambient perturbative order. -/
theorem length_r322AnalyticSchedule_le_of_full
    {q : ℕ} (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ.IsFull) :
    (r322AnalyticSchedule κ).length ≤ q := by
  let orders :=
    (r322AnalyticSchedule κ).map
      (fun s => residualBlockOrder s.2)
  have hpos : ∀ n ∈ orders, 0 < n := by
    intro n hn
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hn
    exact r322AnalyticSchedule_blockOrder_pos κ hκ s hs
  have hlen : orders.length ≤ orders.sum :=
    r322Schedule_length_le_sum_of_pos orders hpos
  simpa only [orders, List.length_map,
    sum_r322AnalyticSchedule_blockOrders_of_full κ hκ] using hlen

/-- In the paper's proper-prefix/terminal decomposition, the proper
orders plus the terminal order still add exactly to `q`. -/
theorem sum_r322AnalyticSchedule_proper_add_terminal
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    (hκfull : κ.IsFull)
    (proper : List (R322ExtractionStep (2 * q)))
    (terminal : R322ExtractionStep (2 * q))
    (hschedule :
      r322AnalyticSchedule κ = proper ++ [terminal]) :
    (proper.map
        (fun s => residualBlockOrder s.2)).sum +
        residualBlockOrder terminal.2 =
      q := by
  have hsum :=
    sum_r322AnalyticSchedule_blockOrders_of_full κ hκfull
  rw [hschedule, List.map_append, List.sum_append] at hsum
  simpa using hsum

end

end Anderson4D
