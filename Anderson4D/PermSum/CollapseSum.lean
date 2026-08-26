import Anderson4D.PermSum.CollapseCoordinates
import Anderson4D.PermSum.CollapseLedger

/-!
# Exact change of variables for collapse sums

The finite-word collapse is an `Equiv`, so sums over prescribed-multiplicity
words can be reindexed by fixed-length raw collapse data without any fiber
cardinality.  This file also inserts the definitional factorial ledger
pointwise.  The resulting marker inverse factorial is precisely the
`((s+1)!)⁻¹` in paper (5.45)(i).
-/

namespace Anderson4D

open scoped BigOperators

set_option warningAsError true
set_option autoImplicit false

noncomputable section

variable {A B : Type*}

/-- Fixed-length raw collapse data are finite because they are equivalent to
finite words. -/
noncomputable instance fixedRawCollapseDataFintype
    [Fintype A] [Fintype B] (n : ℕ) :
    Fintype (FixedRawCollapseData A B n) :=
  Fintype.ofEquiv _ (finWordRawCollapseEquiv A B n)

/-- The canonical collapse multiplicity specification is decidable on finite
alphabets. -/
instance collapseMultiplicitySpecDecidable
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) :
    DecidablePred (CollapseMultiplicitySpec mult) :=
  fun d => Classical.propDecidable (CollapseMultiplicitySpec mult d)

/-- The outside part of a multiplicity on a split alphabet. -/
def outsideMultiplicity (mult : A ⊕ B → ℕ) : B → ℕ :=
  fun b => mult (.inr b)

@[simp]
theorem sumMultiplicity_inside_outside (mult : A ⊕ B → ℕ) :
    sumMultiplicity (insideMultiplicity mult) (outsideMultiplicity mult) =
      mult := by
  funext x
  cases x <;> rfl

@[simp]
theorem collapsedMultiplicity_eq_markerMultiplicity
    (mult : A ⊕ B → ℕ) (d : RawCollapseData A B) :
    collapsedMultiplicity mult d =
      markerMultiplicity d.blocks.length (outsideMultiplicity mult) := by
  funext x
  cases x with
  | inl u => cases u; rfl
  | inr b => rfl

/-- The collapse factorial ledger specialized to the canonical inside and
collapsed multiplicities of a raw collapse datum. -/
theorem collapse_factorialLedger_raw
    [Fintype A] [Fintype B]
    (mult : A ⊕ B → ℕ) (d : RawCollapseData A B) :
    (∏ x : A ⊕ B, ((mult x).factorial : ℝ)) =
      (d.blocks.length.factorial : ℝ)⁻¹ *
        ((∏ a : A, ((insideMultiplicity mult a).factorial : ℝ)) *
          ∏ x : Unit ⊕ B,
            ((collapsedMultiplicity mult d x).factorial : ℝ)) := by
  have h :=
    factorialLedger_sum_eq_inv_marker_mul
      (insideMultiplicity mult) (outsideMultiplicity mult) d.blocks.length
  rw [sumMultiplicity_inside_outside mult] at h
  rw [collapsedMultiplicity_eq_markerMultiplicity]
  exact h

/-- Exact reindexing of a prescribed-multiplicity word sum by the honest
finite collapse equivalence. -/
theorem sum_validWords_eq_sum_fixedRawCollapseData
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (mult : A ⊕ B → ℕ) (F : (Fin n → A ⊕ B) → ℝ) :
    (∑ w ∈ validWords mult, F w) =
      ∑ d : FixedRawCollapseData A B n,
        if CollapseMultiplicitySpec mult d.1 then
          F ((finWordRawCollapseEquiv A B n).symm d)
        else 0 := by
  classical
  let e := finWordRawCollapseEquiv A B n
  let G : FixedRawCollapseData A B n → ℝ :=
    fun d =>
      if CollapseMultiplicitySpec mult d.1 then F (e.symm d) else 0
  calc
    (∑ w ∈ validWords mult, F w) =
        ∑ w : Fin n → A ⊕ B,
          if w ∈ validWords mult then F w else 0 := by
      simp
    _ = ∑ w : Fin n → A ⊕ B, G (e w) := by
      apply Fintype.sum_congr
      intro w
      have hspec :
          w ∈ validWords mult ↔
            CollapseMultiplicitySpec mult (e w).1 := by
        exact mem_validWords_iff_finWordRawCollapseSpec mult w
      change
        (if w ∈ validWords mult then F w else 0) =
          if CollapseMultiplicitySpec mult (e w).1 then
            F (e.symm (e w))
          else 0
      rw [e.symm_apply_apply]
      by_cases hw : w ∈ validWords mult
      · simp [hw, hspec.mp hw]
      · have hnot :
            ¬CollapseMultiplicitySpec mult (e w).1 :=
          fun h => hw (hspec.mpr h)
        simp [hw, hnot]
    _ = ∑ d : FixedRawCollapseData A B n, G d :=
      Equiv.sum_comp e G
    _ = ∑ d : FixedRawCollapseData A B n,
        if CollapseMultiplicitySpec mult d.1 then
          F ((finWordRawCollapseEquiv A B n).symm d)
        else 0 := by
      rfl

/-- Predicate-filtered version of the exact collapse change of variables. -/
theorem sum_validWords_filter_eq_sum_fixedRawCollapseData
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (mult : A ⊕ B → ℕ)
    (P : (Fin n → A ⊕ B) → Prop) [DecidablePred P]
    (F : (Fin n → A ⊕ B) → ℝ) :
    (∑ w ∈ (validWords mult).filter P, F w) =
      ∑ d : FixedRawCollapseData A B n,
        if CollapseMultiplicitySpec mult d.1 ∧
            P ((finWordRawCollapseEquiv A B n).symm d) then
          F ((finWordRawCollapseEquiv A B n).symm d)
        else 0 := by
  classical
  calc
    (∑ w ∈ (validWords mult).filter P, F w) =
        ∑ w ∈ validWords mult, if P w then F w else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ d : FixedRawCollapseData A B n,
        if CollapseMultiplicitySpec mult d.1 then
          (if P ((finWordRawCollapseEquiv A B n).symm d) then
            F ((finWordRawCollapseEquiv A B n).symm d)
          else 0)
        else 0 :=
      sum_validWords_eq_sum_fixedRawCollapseData mult
        (fun w => if P w then F w else 0)
    _ = ∑ d : FixedRawCollapseData A B n,
        if CollapseMultiplicitySpec mult d.1 ∧
            P ((finWordRawCollapseEquiv A B n).symm d) then
          F ((finWordRawCollapseEquiv A B n).symm d)
        else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hspec : CollapseMultiplicitySpec mult d.1
      · by_cases hp : P ((finWordRawCollapseEquiv A B n).symm d)
        · simp [hspec, hp]
        · simp [hspec, hp]
      · simp [hspec]

/-- `paperSum` after collapse reindexing.  The inverse marker factorial is
inserted pointwise, so it remains correct while the number of blocks varies
between collapse data. -/
theorem paperSum_eq_sum_fixedRawCollapseData
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (mult : A ⊕ B → ℕ) (F : (Fin n → A ⊕ B) → ℝ) :
    paperSum mult F =
      ∑ d : FixedRawCollapseData A B n,
        if CollapseMultiplicitySpec mult d.1 then
          (d.1.blocks.length.factorial : ℝ)⁻¹ *
            ((∏ a : A,
                ((insideMultiplicity mult a).factorial : ℝ)) *
              ∏ x : Unit ⊕ B,
                ((collapsedMultiplicity mult d.1 x).factorial : ℝ)) *
            F ((finWordRawCollapseEquiv A B n).symm d)
        else 0 := by
  classical
  unfold paperSum wordSum
  rw [sum_validWords_eq_sum_fixedRawCollapseData mult F,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : CollapseMultiplicitySpec mult d.1
  · simp only [hd, if_true]
    rw [collapse_factorialLedger_raw mult d.1]
  · simp [hd]

/-- Predicate-filtered `paperSum` after the same exact change of variables
and factorial-ledger insertion. -/
theorem paperSumFiltered_eq_sum_fixedRawCollapseData
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (mult : A ⊕ B → ℕ)
    (P : (Fin n → A ⊕ B) → Prop) [DecidablePred P]
    (F : (Fin n → A ⊕ B) → ℝ) :
    paperSumFiltered mult P F =
      ∑ d : FixedRawCollapseData A B n,
        if CollapseMultiplicitySpec mult d.1 ∧
            P ((finWordRawCollapseEquiv A B n).symm d) then
          (d.1.blocks.length.factorial : ℝ)⁻¹ *
            ((∏ a : A,
                ((insideMultiplicity mult a).factorial : ℝ)) *
              ∏ x : Unit ⊕ B,
                ((collapsedMultiplicity mult d.1 x).factorial : ℝ)) *
            F ((finWordRawCollapseEquiv A B n).symm d)
        else 0 := by
  classical
  unfold paperSumFiltered wordSumFiltered
  rw [sum_validWords_filter_eq_sum_fixedRawCollapseData mult P F,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd :
      CollapseMultiplicitySpec mult d.1 ∧
        P ((finWordRawCollapseEquiv A B n).symm d)
  · simp only [hd.1, hd.2, true_and, if_true]
    rw [collapse_factorialLedger_raw mult d.1]
  · simp [hd]

end

end Anderson4D
