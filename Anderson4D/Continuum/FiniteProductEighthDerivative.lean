import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Eighth derivative of a finite scalar product

This module records the numerical Leibniz ledger needed for the
fixed-cutoff relative-translation argument.  The factors are indexed by
slot IDs in a finset; equal function values therefore remain distinct when
their slot IDs are distinct.

Mathlib's symmetric-power bound groups the ordered choices of a
differentiated slot.  The multiplicity `Multiset.countPerms` is retained
until the final sum, where the multinomial theorem shows that its total is
exactly the eighth power of the number of slots.  Thus no additional `8!`
loss is introduced.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- A component of an eighth-order symmetric allocation assigns at most
eight derivatives to any one slot. -/
theorem symEight_count_le
    (p : Sym ι 8) (j : ι) :
    (p : Multiset ι).count j ≤ 8 := by
  simpa using
    (Multiset.count_le_card j (p : Multiset ι))

/-- Scalar specialization of mathlib's finite-product iterated Fréchet
derivative bound.

The carrier `u.sym 8` is the collection of weak derivative allocations.
Its `countPerms` weight remembers how many ordered sequences of eight
single-slot differentiations give the same allocation. -/
theorem abs_iteratedDeriv_eight_finsetProd_le_sym
    {u : Finset ι} {f : ι → ℝ → ℝ}
    (hf : ∀ j ∈ u, ContDiff ℝ 8 (f j))
    (x : ℝ) :
    |iteratedDeriv 8 (fun t => ∏ j ∈ u, f j t) x| ≤
      ∑ p ∈ u.sym 8,
        ((p : Multiset ι).countPerms : ℝ) *
          ∏ j ∈ u,
            |iteratedDeriv
              ((p : Multiset ι).count j) (f j) x| := by
  have h :=
    norm_iteratedFDeriv_prod_le
      (u := u) (f := f) hf (x := x) (n := 8)
        (by norm_num)
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs] using h

/-- The total multiplicity of all weak allocations of eight derivative
slots is exactly the number of ordered slot choices. -/
theorem sum_countPerms_symEight_eq_card_pow
    (u : Finset ι) :
    (∑ p ∈ u.sym 8,
        ((p : Multiset ι).countPerms : ℝ)) =
      (u.card : ℝ) ^ (8 : ℕ) := by
  have h :=
    Finset.sum_pow (s := u)
      (fun _ : ι => (1 : ℝ)) 8
  simpa using h.symm

/-- **Uniform eighth-derivative product bound without factorial loss.**

If every derivative through order eight of the factor in slot `j` is
bounded at `x` by `B j`, then the eighth derivative of the whole product is
bounded by `card(u)^8` times the product of those majorants. -/
theorem abs_iteratedDeriv_eight_finsetProd_le_card_pow
    {u : Finset ι} {f : ι → ℝ → ℝ}
    (hf : ∀ j ∈ u, ContDiff ℝ 8 (f j))
    (B : ι → ℝ) (x : ℝ)
    (hderiv :
      ∀ j ∈ u, ∀ r : ℕ, r ≤ 8 →
        |iteratedDeriv r (f j) x| ≤ B j) :
    |iteratedDeriv 8 (fun t => ∏ j ∈ u, f j t) x| ≤
      (u.card : ℝ) ^ (8 : ℕ) *
        ∏ j ∈ u, B j := by
  calc
    |iteratedDeriv 8 (fun t => ∏ j ∈ u, f j t) x| ≤
        ∑ p ∈ u.sym 8,
          ((p : Multiset ι).countPerms : ℝ) *
            ∏ j ∈ u,
              |iteratedDeriv
                ((p : Multiset ι).count j) (f j) x| :=
      abs_iteratedDeriv_eight_finsetProd_le_sym hf x
    _ ≤
        ∑ p ∈ u.sym 8,
          ((p : Multiset ι).countPerms : ℝ) *
            ∏ j ∈ u, B j := by
      apply Finset.sum_le_sum
      intro p _hp
      apply mul_le_mul_of_nonneg_left
      · apply Finset.prod_le_prod
        · intro j _hj
          exact abs_nonneg _
        · intro j hj
          exact hderiv j hj
            ((p : Multiset ι).count j)
            (symEight_count_le p j)
      · positivity
    _ =
        (∑ p ∈ u.sym 8,
          ((p : Multiset ι).countPerms : ℝ)) *
            ∏ j ∈ u, B j := by
      rw [Finset.sum_mul]
    _ =
        (u.card : ℝ) ^ (8 : ℕ) *
          ∏ j ∈ u, B j := by
      rw [sum_countPerms_symEight_eq_card_pow]

end

end Anderson4D
