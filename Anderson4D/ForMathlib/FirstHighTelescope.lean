import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# First-high finite telescoping identities

This file records the purely algebraic finite-slot decomposition used before
the probabilistic Wick expansion.  If every slot splits as
`full i = low i + high i`, the product (or any multilinear expression) is the
all-low term plus a sum indexed by the *first* high slot: slots before `i` are
low, slot `i` is high, and slots after `i` remain full.

The product identity is the order-dual form of `Finset.prod_add_ordered`.
The multilinear identity is proved directly by induction on the number of
slots.  Neither statement has any analytic or probabilistic hypotheses.
-/

namespace Anderson4D

open scoped BigOperators

section Product

variable {A ι : Type*} [CommSemiring A] [LinearOrder ι]

/--
The first-high orientation of `Finset.prod_add_ordered`.

The summand at `i` has a low prefix, a high factor at `i`, and the unsplit
full suffix.  Passing to `OrderDual ι` turns mathlib's last-high orientation
into this one.
-/
theorem Finset.prod_add_ordered_firstHigh (s : Finset ι) (low high : ι → A) :
    ∏ i ∈ s, (low i + high i) =
      (∏ i ∈ s, low i) +
        ∑ i ∈ s,
          (∏ j ∈ s with j < i, low j) * high i *
            ∏ j ∈ s with i < j, (low j + high j) := by
  classical
  refine Finset.induction_on_min s (by simp) ?_
  clear s
  intro a s ha ihs
  have ha' : a ∉ s := fun ha' => lt_irrefl a (ha a ha')
  rw [Finset.prod_insert ha', Finset.prod_insert ha', Finset.sum_insert ha', ihs]
  have hbefore :
      (insert a s).filter (fun j => j < a) = ∅ := by
    ext j
    constructor
    · intro hj
      obtain ⟨hjmem, hjlt⟩ := Finset.mem_filter.mp hj
      rcases Finset.mem_insert.mp hjmem with rfl | hjs
      · exact (lt_irrefl _ hjlt).elim
      · exact ((ha j hjs).not_gt hjlt).elim
    · simp
  have hafter :
      (insert a s).filter (fun j => a < j) = s := by
    ext j
    constructor
    · intro hj
      obtain ⟨hjmem, hjlt⟩ := Finset.mem_filter.mp hj
      rcases Finset.mem_insert.mp hjmem with rfl | hjs
      · exact (lt_irrefl _ hjlt).elim
      · exact hjs
    · intro hjs
      exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hjs, ha j hjs⟩
  have hterm :
      (∏ j ∈ insert a s with j < a, low j) * high a *
          ∏ j ∈ insert a s with a < j, (low j + high j) =
        high a * ∏ j ∈ s, (low j + high j) := by
    rw [hbefore, hafter]
    simp
  have hsum :
      (∑ i ∈ s,
          (∏ j ∈ insert a s with j < i, low j) * high i *
            ∏ j ∈ insert a s with i < j, (low j + high j)) =
        low a *
          ∑ i ∈ s,
            (∏ j ∈ s with j < i, low j) * high i *
              ∏ j ∈ s with i < j, (low j + high j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.filter_insert, if_pos (ha i hi),
      Finset.filter_insert, if_neg (ha i hi).not_gt, Finset.prod_insert]
    · ac_rfl
    · exact fun hai => ha' (Finset.mem_filter.mp hai).1
  rw [hterm, hsum, ihs]
  ring

/--
A finite product split at its first high slot.

This is the form consumed by the finite-slot Wick telescope: the index is the
original slot index, not a permutation or a reversed index.
-/
theorem Fin.prod_firstHigh {n : ℕ} (full low high : Fin n → A)
    (hfull : ∀ i, full i = low i + high i) :
    ∏ i, full i =
      (∏ i, low i) +
        ∑ i,
          (∏ j ∈ Finset.univ with j < i, low j) * high i *
            ∏ j ∈ Finset.univ with i < j, full j := by
  classical
  calc
    ∏ i, full i = ∏ i, (low i + high i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hfull i
    _ = (∏ i, low i) +
          ∑ i,
            (∏ j ∈ Finset.univ with j < i, low j) * high i *
              ∏ j ∈ Finset.univ with i < j, (low j + high j) := by
      simpa using
        (Finset.prod_add_ordered_firstHigh
          (s := Finset.univ) (low := low) (high := high))
    _ = (∏ i, low i) +
          ∑ i,
            (∏ j ∈ Finset.univ with j < i, low j) * high i *
              ∏ j ∈ Finset.univ with i < j, full j := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      exact (hfull j).symm

end Product

section Multilinear

variable {R M N : Type*}

/--
The input tuple for the summand whose first high slot is `i`.

It equals `low` before `i`, `high` at `i`, and `full` after `i`.
-/
def firstHighSlot {n : ℕ} (full low high : Fin n → M) (i : Fin n) : Fin n → M :=
  fun j => if j < i then low j else if j = i then high j else full j

@[simp]
theorem firstHighSlot_zero {n : ℕ} (full low high : Fin (n + 1) → M) :
    firstHighSlot full low high 0 =
      Fin.cons (high 0) (Fin.tail full) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [firstHighSlot]
  · simp [firstHighSlot, Fin.tail]

@[simp]
theorem firstHighSlot_succ {n : ℕ} (full low high : Fin (n + 1) → M) (i : Fin n) :
    firstHighSlot full low high i.succ =
      Fin.cons (low 0)
        (firstHighSlot (Fin.tail full) (Fin.tail low) (Fin.tail high) i) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [firstHighSlot]
  · simp [firstHighSlot, Fin.tail]

variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/--
A multilinear expression split at its first high slot.

Only additivity in each slot is used.  In particular this applies directly to
the deterministic multilinear carrier underneath a finite Wick expression.
-/
theorem MultilinearMap.map_add_firstHigh {n : ℕ}
    (f : MultilinearMap R (fun _ : Fin n => M) N)
    (full low high : Fin n → M)
    (hfull : ∀ i, full i = low i + high i) :
    f full = f low + ∑ i, f (firstHighSlot full low high i) := by
  induction n with
  | zero =>
      have hfl : full = low := Subsingleton.elim _ _
      simp [hfl]
  | succ n ih =>
      have htail :
          ∀ i : Fin n,
            Fin.tail full i = Fin.tail low i + Fin.tail high i :=
        fun i => hfull i.succ
      let fLow : MultilinearMap R (fun _ : Fin n => M) N :=
        f.curryLeft (low 0)
      have hind :=
        ih (f := fLow)
          (full := Fin.tail full) (low := Fin.tail low) (high := Fin.tail high)
          htail
      change
        f (Fin.cons (low 0) (Fin.tail full)) =
          f (Fin.cons (low 0) (Fin.tail low)) +
            ∑ i : Fin n,
              f (Fin.cons (low 0)
                (firstHighSlot
                  (Fin.tail full) (Fin.tail low) (Fin.tail high) i))
        at hind
      calc
        f full = f (Fin.cons (full 0) (Fin.tail full)) := by
          rw [Fin.cons_self_tail]
        _ = f (Fin.cons (low 0 + high 0) (Fin.tail full)) := by
          rw [hfull 0]
        _ = f (Fin.cons (low 0) (Fin.tail full)) +
              f (Fin.cons (high 0) (Fin.tail full)) :=
          f.cons_add (Fin.tail full) (low 0) (high 0)
        _ = (f (Fin.cons (low 0) (Fin.tail low)) +
              ∑ i : Fin n,
                f (Fin.cons (low 0)
                  (firstHighSlot
                    (Fin.tail full) (Fin.tail low) (Fin.tail high) i))) +
              f (Fin.cons (high 0) (Fin.tail full)) := by
          rw [hind]
        _ = f low + ∑ i, f (firstHighSlot full low high i) := by
          simp only [Fin.sum_univ_succ, firstHighSlot_zero, firstHighSlot_succ]
          rw [Fin.cons_self_tail low]
          ac_rfl

end Multilinear

end Anderson4D
