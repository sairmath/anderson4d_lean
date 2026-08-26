import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticScheduleTerminal
import Anderson4D.DetParametrix.Paper41_Renorm.R322CoordinateCollapseClosure
import Mathlib.Data.List.NodupEquivFin

/-!
# Reindexing R-322 block products into analytic order

The existing coordinate factorization uses the unordered finite type
`ExtractionBlockIndex κ`.  This file equips it with the exact order of
`r322AnalyticSchedule κ`.  The construction is purely finite and uses the
block-projection permutation together with block nodup; no integral is changed
here.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## The ordered block equivalence -/

/-- The scheduled block projection has no duplicates. -/
theorem r322AnalyticSchedule_blocks_nodup
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    ((r322AnalyticSchedule κ).map Prod.snd).Nodup := by
  exact
    (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).nodup_iff.mpr
      (extractionBlocks_nodup κ)

/-- Analytic list positions are exactly the concrete extraction-block
coordinates. -/
def r322AnalyticBlockEquiv
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    Fin (r322AnalyticSchedule κ).length ≃
      ExtractionBlockIndex κ :=
  ((finCongr
        (List.length_map
          (as := r322AnalyticSchedule κ)
          Prod.snd).symm).trans
      ((r322AnalyticSchedule_blocks_nodup κ).getEquiv
        ((r322AnalyticSchedule κ).map Prod.snd))).trans
    (Equiv.subtypeEquivRight fun _B =>
      (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).mem_iff)

/-- Applying the ordered block equivalence returns precisely the block stored
in the corresponding schedule step. -/
@[simp]
theorem r322AnalyticBlockEquiv_apply_val
    {m : ℕ} (κ : PartialPairing (Fin m))
    (i : Fin (r322AnalyticSchedule κ).length) :
    (r322AnalyticBlockEquiv κ i).1 =
      ((r322AnalyticSchedule κ).get i).2 := by
  simp [r322AnalyticBlockEquiv, List.Nodup.getEquiv]

/-! ## Exact finite-product reindexing -/

/-- Reindex an unordered product over extraction blocks by analytic schedule
position. -/
theorem extractionBlock_prod_eq_analyticSchedule
    {m : ℕ} (κ : PartialPairing (Fin m))
    {M : Type*} [CommMonoid M]
    (f : ExtractionBlockIndex κ → M) :
    (∏ B : ExtractionBlockIndex κ, f B) =
      ∏ i : Fin (r322AnalyticSchedule κ).length,
        f (r322AnalyticBlockEquiv κ i) := by
  exact
    (Equiv.prod_comp (r322AnalyticBlockEquiv κ) f).symm

/-! ## Splitting a nonempty analytic schedule -/

/-- The standard `Fin (n + 1)` indexing of a displayed `head :: tail`
schedule. -/
def r322AnalyticConsIndexEquiv
    {m : ℕ} (κ : PartialPairing (Fin m))
    {head : R322ExtractionStep m}
    {tail : List (R322ExtractionStep m)}
    (hschedule :
      r322AnalyticSchedule κ = head :: tail) :
    Fin (tail.length + 1) ≃
      Fin (r322AnalyticSchedule κ).length :=
  finCongr (by
    rw [hschedule]
    simp)

/-- The extraction-block coordinate at the head of a displayed schedule. -/
def r322AnalyticHeadBlockIndex
    {m : ℕ} (κ : PartialPairing (Fin m))
    {head : R322ExtractionStep m}
    {tail : List (R322ExtractionStep m)}
    (hschedule :
      r322AnalyticSchedule κ = head :: tail) :
    ExtractionBlockIndex κ :=
  r322AnalyticBlockEquiv κ
    (r322AnalyticConsIndexEquiv κ hschedule 0)

/-- The extraction-block coordinate at one position of the displayed tail. -/
def r322AnalyticTailBlockIndex
    {m : ℕ} (κ : PartialPairing (Fin m))
    {head : R322ExtractionStep m}
    {tail : List (R322ExtractionStep m)}
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (j : Fin tail.length) :
    ExtractionBlockIndex κ :=
  r322AnalyticBlockEquiv κ
    (r322AnalyticConsIndexEquiv κ hschedule j.succ)

/-- The head coordinate carries exactly the block stored in `head`. -/
@[simp]
theorem r322AnalyticHeadBlockIndex_val
    {m : ℕ} (κ : PartialPairing (Fin m))
    {head : R322ExtractionStep m}
    {tail : List (R322ExtractionStep m)}
    (hschedule :
      r322AnalyticSchedule κ = head :: tail) :
    (r322AnalyticHeadBlockIndex κ hschedule).1 =
      head.2 := by
  rw [r322AnalyticHeadBlockIndex,
    r322AnalyticBlockEquiv_apply_val]
  have hindex :
      r322AnalyticConsIndexEquiv κ hschedule 0 =
        (⟨0, by
          rw [hschedule]
          simp⟩ :
          Fin (r322AnalyticSchedule κ).length) := by
    apply Fin.ext
    rfl
  rw [hindex]
  have hget :=
    List.get_of_eq hschedule
      (⟨0, by
        rw [hschedule]
        simp⟩ :
        Fin (r322AnalyticSchedule κ).length)
  exact
    congrArg Prod.snd hget

/-- A tail coordinate carries exactly the block stored at that tail
position. -/
@[simp]
theorem r322AnalyticTailBlockIndex_val
    {m : ℕ} (κ : PartialPairing (Fin m))
    {head : R322ExtractionStep m}
    {tail : List (R322ExtractionStep m)}
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (j : Fin tail.length) :
    (r322AnalyticTailBlockIndex κ hschedule j).1 =
      (tail.get j).2 := by
  rw [r322AnalyticTailBlockIndex,
    r322AnalyticBlockEquiv_apply_val]
  have hindex :
      r322AnalyticConsIndexEquiv κ hschedule j.succ =
        (⟨j.val + 1, by
          rw [hschedule]
          simp⟩ :
          Fin (r322AnalyticSchedule κ).length) := by
    apply Fin.ext
    rfl
  rw [hindex]
  have hget :=
    List.get_of_eq hschedule
      (⟨j.val + 1, by
        rw [hschedule]
        simp⟩ :
        Fin (r322AnalyticSchedule κ).length)
  simpa only [List.get_cons_succ] using
    congrArg Prod.snd hget

/-- A product in analytic block order splits into the head factor followed
by the product over the displayed tail. -/
theorem extractionBlock_prod_eq_head_mul_tail
    {m : ℕ} (κ : PartialPairing (Fin m))
    {head : R322ExtractionStep m}
    {tail : List (R322ExtractionStep m)}
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    {M : Type*} [CommMonoid M]
    (f : ExtractionBlockIndex κ → M) :
    (∏ B : ExtractionBlockIndex κ, f B) =
      f (r322AnalyticHeadBlockIndex κ hschedule) *
        ∏ j : Fin tail.length,
          f (r322AnalyticTailBlockIndex κ hschedule j) := by
  rw [extractionBlock_prod_eq_analyticSchedule]
  calc
    (∏ i : Fin (r322AnalyticSchedule κ).length,
        f (r322AnalyticBlockEquiv κ i)) =
        ∏ j : Fin (tail.length + 1),
          f (r322AnalyticBlockEquiv κ
            (r322AnalyticConsIndexEquiv κ hschedule j)) := by
      exact
        (Equiv.prod_comp
          (r322AnalyticConsIndexEquiv κ hschedule)
          (fun i => f (r322AnalyticBlockEquiv κ i))).symm
    _ =
        f (r322AnalyticHeadBlockIndex κ hschedule) *
          ∏ j : Fin tail.length,
            f (r322AnalyticTailBlockIndex κ hschedule j) := by
      exact
        Fin.prod_univ_succ
          (fun j =>
            f (r322AnalyticBlockEquiv κ
              (r322AnalyticConsIndexEquiv κ hschedule j)))

end

end Anderson4D
