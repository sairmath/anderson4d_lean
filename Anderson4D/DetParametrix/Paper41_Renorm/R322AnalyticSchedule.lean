import Anderson4D.DetParametrix.Paper41_Renorm.R322SelectorFubiniClosure
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Zip

/-!
# The analytic schedule for R-322

The closed-form extraction list records the deterministic selector from the
combinatorial recursion.  The analytic collapse, however, must process a
primitive interval before every interval that contains it.  Since extraction
intervals are laminar, sorting the aligned endpoint/block steps by increasing
right endpoint gives exactly such an inside-to-outside schedule; disjoint
intervals may be interchanged.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

/-- An extraction endpoint together with the concrete trace removed at the
same recursive step. -/
abbrev R322ExtractionStep (m : ℕ) :=
  (Fin m × Fin m) × Finset (Fin m)

/-- The weak right-endpoint order used by insertion sort.  Right endpoints of
distinct extracted intervals are in fact distinct, so the resulting schedule
is strictly ordered. -/
def R322StepRightLE {m : ℕ}
    (s t : R322ExtractionStep m) : Prop :=
  s.1.2 ≤ t.1.2

instance {m : ℕ} : DecidableRel (@R322StepRightLE m) :=
  fun _ _ => inferInstanceAs (Decidable (_ ≤ _))

instance {m : ℕ} : Std.Total (@R322StepRightLE m) where
  total _ _ := le_total _ _

instance {m : ℕ} : IsTrans (R322ExtractionStep m)
    (@R322StepRightLE m) where
  trans _ _ _ := le_trans

/-- The endpoint/block extraction trace, reordered into the analytic
inside-to-outside schedule. -/
def r322AnalyticSchedule {m : ℕ}
    (κ : PartialPairing (Fin m)) :
    List (R322ExtractionStep m) :=
  ((extract κ).zip (extractionBlocks κ)).insertionSort
    R322StepRightLE

/-- Projection of the analytic schedule to endpoint pairs is a permutation of
the public extraction list. -/
theorem r322AnalyticSchedule_endpoints_perm_extract
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    List.Perm
      ((r322AnalyticSchedule κ).map Prod.fst)
      (extract κ) := by
  have hperm :=
    (List.perm_insertionSort R322StepRightLE
      ((extract κ).zip (extractionBlocks κ))).map Prod.fst
  have haligned :=
    extractAux_extractionBlocksAux_aligned
      κ m Finset.univ
  have hlength :
      (extract κ).length =
        (extractionBlocks κ).length := by
    simpa only [extract, extractionBlocks] using
      haligned.length_eq
  rw [List.map_fst_zip (Nat.le_of_eq hlength)] at hperm
  simpa only [r322AnalyticSchedule] using hperm

/-- Projection of the analytic schedule to concrete blocks is a permutation
of the public extraction-block list. -/
theorem r322AnalyticSchedule_blocks_perm_extractionBlocks
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    List.Perm
      ((r322AnalyticSchedule κ).map Prod.snd)
      (extractionBlocks κ) := by
  have hperm :=
    (List.perm_insertionSort R322StepRightLE
      ((extract κ).zip (extractionBlocks κ))).map Prod.snd
  have haligned :=
    extractAux_extractionBlocksAux_aligned
      κ m Finset.univ
  have hlength :
      (extract κ).length =
        (extractionBlocks κ).length := by
    simpa only [extract, extractionBlocks] using
      haligned.length_eq
  rw [List.map_snd_zip (Nat.le_of_eq hlength.symm)] at hperm
  simpa only [r322AnalyticSchedule] using hperm

/-- Sorting retains the pointwise endpoint/block alignment proved for the
original recursion. -/
theorem r322AnalyticSchedule_forall_aligned
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    ∀ s ∈ r322AnalyticSchedule κ,
      ExtractionPairBlockAligned s.1 s.2 := by
  intro s hs
  have hs' :
      s ∈ (extract κ).zip (extractionBlocks κ) := by
    exact
      (List.mem_insertionSort R322StepRightLE).mp hs
  exact
    List.forall₂_zip
      (extractAux_extractionBlocksAux_aligned
        κ m Finset.univ)
      hs'

/-! ## Strict right-endpoint order -/

/-- Insertion sort puts the analytic schedule in weakly increasing
right-endpoint order. -/
theorem r322AnalyticSchedule_pairwise_right_le
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    (r322AnalyticSchedule κ).Pairwise
      R322StepRightLE := by
  exact
    List.pairwise_insertionSort
      R322StepRightLE
      ((extract κ).zip (extractionBlocks κ))

/-- The schedule has no repeated right endpoints. -/
theorem r322AnalyticSchedule_rightEndpoints_nodup
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    ((r322AnalyticSchedule κ).map
      (fun s => s.1.2)).Nodup := by
  have hperm :=
    (r322AnalyticSchedule_endpoints_perm_extract κ).map
      Prod.snd
  have hsource := extract_map_snd_nodup κ
  have htarget :
      (((r322AnalyticSchedule κ).map Prod.fst).map
        Prod.snd).Nodup :=
    hperm.nodup_iff.mpr hsource
  simpa only [List.map_map, Function.comp_def] using htarget

/-- Right endpoints in analytic execution order are strictly increasing. -/
theorem r322AnalyticSchedule_pairwise_right_lt
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    (r322AnalyticSchedule κ).Pairwise
      (fun s t => s.1.2 < t.1.2) := by
  have hle :=
    r322AnalyticSchedule_pairwise_right_le κ
  have hne :
      (r322AnalyticSchedule κ).Pairwise
        (fun s t => s.1.2 ≠ t.1.2) := by
    exact
      List.pairwise_map.mp
        (r322AnalyticSchedule_rightEndpoints_nodup κ)
  exact
    hle.imp₂
      (fun s t hst hne' =>
        lt_of_le_of_ne hst hne')
      hne

end Anderson4D
