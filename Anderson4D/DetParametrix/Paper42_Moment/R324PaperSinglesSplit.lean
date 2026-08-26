import Anderson4D.DetParametrix.Paper42_Moment.R324SingleProjectedSlotClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324FullFullTermFactorization

/-!
# The Steps 2--3 dichotomy: cross covariances, or none at all

Paper: R-324 — §4.2 Steps 2–3 — the cross-covariance dichotomy

The proved two-half physical collapse
(`twoHalf_lamEps_pow_integral_eq_initialNested`) is stated at a *selected*
residual cross-covariance slot

    `R324ResidualCovarianceSlot κp = ↥κp.singles`,

so it cannot be instantiated when the left half's pairing is full.  That
is not a gap: a full left half means the contraction has **no** cross-copy
covariances at all, the two halves of (4.18) are independent, and the
proved `deterministicMomentContractionTerm_eq_fullHalfIntegral_mul`
factors the term outright.

This module records the dichotomy and its two elementary supports: the two
halves have equally many singles (they are matched by `π`), and on a full
half the cross-covariance product is the empty product.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- The two halves of a contraction entity have equally many singles: `π`
matches them. -/
theorem r324_singles_card_eq {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (π : κp.singles ≃ κm.singles) :
    κp.singles.card = κm.singles.card := by
  have h := Fintype.card_congr π
  rwa [Fintype.card_coe, Fintype.card_coe] at h

/-- One half of a contraction entity is full exactly when the other is. -/
theorem r324_isFull_left_iff_right {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (π : κp.singles ≃ κm.singles) :
    κp.IsFull ↔ κm.IsFull := by
  have hcard := r324_singles_card_eq π
  constructor
  · intro hp
    rw [PartialPairing.isFull_iff_singles_eq_empty] at hp ⊢
    rw [hp, Finset.card_empty] at hcard
    exact Finset.card_eq_zero.mp hcard.symm
  · intro hm
    rw [PartialPairing.isFull_iff_singles_eq_empty] at hm ⊢
    rw [hm, Finset.card_empty] at hcard
    exact Finset.card_eq_zero.mp hcard

/-- On a full half the cross-copy covariance product is the empty
product. -/
theorem momentCrossCovarianceProduct_eq_one_of_isFull
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    {κp κm : PartialPairing (Fin m)}
    (π : κp.singles ≃ κm.singles) (hp : κp.IsFull)
    (v : Fin (2 * m) → T4) :
    momentCrossCovarianceProduct ρ ε m κp κm π v = 1 := by
  have hempty : κp.singles = ∅ :=
    PartialPairing.isFull_iff_singles_eq_empty.mp hp
  have : IsEmpty ↥κp.singles := Finset.isEmpty_coe_sort.mpr hempty
  unfold momentCrossCovarianceProduct
  rw [Finset.univ_eq_empty, Finset.prod_empty]

/-- **The Steps 2--3 dichotomy.**

At any contraction entity `(κp, κm, π)` either both halves are fully
paired — so there are no cross-copy covariances and the two halves of
(4.18) are independent — or the left half has a single, which is exactly
the residual covariance slot the two-half nested bridge consumes.  The
disjunction is exhaustive, so Steps 2--3 may branch on it. -/
theorem r324SinglesDichotomy {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (π : κp.singles ≃ κm.singles) :
    (κp.IsFull ∧ κm.IsFull) ∨ Nonempty (R324ResidualCovarianceSlot κp) := by
  by_cases h : κp.singles = ∅
  · exact Or.inl
      ⟨PartialPairing.isFull_iff_singles_eq_empty.mpr h,
        (r324_isFull_left_iff_right π).mp
          (PartialPairing.isFull_iff_singles_eq_empty.mpr h)⟩
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr h
    exact Or.inr ⟨⟨i, hi⟩⟩

/-- Entity-indexed form of the dichotomy. -/
theorem r324SinglesDichotomy_entity {m : ℕ} (e : MomentContraction m) :
    (e.1.IsFull ∧ e.2.1.IsFull) ∨
      Nonempty (R324ResidualCovarianceSlot e.1) :=
  r324SinglesDichotomy e.2.2

end

end Anderson4D
