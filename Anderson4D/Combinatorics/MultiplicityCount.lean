import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Exponential bounds for multiplicity and relabelling choices

This file isolates the two elementary exponential counts used between
paper equations (5.8) and (5.9).  A positive tuple with prescribed total is
a composition after the index order is fixed.  Consequently the number of
such tuples is at most `2 ^ total`.

Using labelled slots here is deliberate: it bounds both the initial
multiplicity choice and the later `χ` assignment without introducing a
factorial for permuting leaves.
-/

namespace Anderson4D

open scoped BigOperators

/-- Positive `r`-tuples with sum `total`.  Values use a bounded carrier so
the type is finite without any classical finite-set truncation. -/
def PositiveTuple (r total : ℕ) :=
  {f : Fin r → Fin (total + 1) //
    (∀ i, 0 < (f i).1) ∧ ∑ i, (f i).1 = total}

namespace PositiveTuple

instance (r total : ℕ) : Fintype (PositiveTuple r total) :=
  inferInstanceAs
    (Fintype
      {f : Fin r → Fin (total + 1) //
        (∀ i, 0 < (f i).1) ∧ ∑ i, (f i).1 = total})

/-- Forget the fixed length of a positive tuple and regard it as an integer
composition. -/
def toComposition {r total : ℕ} (f : PositiveTuple r total) :
    Composition total where
  blocks := List.ofFn fun i => (f.1 i).1
  blocks_pos := by
    intro a ha
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact f.2.1 i
  blocks_sum := by
    rw [List.sum_ofFn]
    exact f.2.2

/-- The ordered list of blocks remembers the original tuple. -/
theorem toComposition_injective {r total : ℕ} :
    Function.Injective (@toComposition r total) := by
  intro f g h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrFun
    (List.ofFn_injective (congrArg Composition.blocks h)) i

/-- The number of positive ordered tuples of any fixed length and total
`total` is exponentially bounded.  This is the count used for both the
`(m_l)` and `χ` choices in paper (5.8)--(5.9). -/
theorem card_le_two_pow (r total : ℕ) :
    Fintype.card (PositiveTuple r total) ≤ 2 ^ total := by
  calc
    Fintype.card (PositiveTuple r total)
        ≤ Fintype.card (Composition total) :=
      Fintype.card_le_of_injective toComposition toComposition_injective
    _ = 2 ^ (total - 1) := composition_card total
    _ ≤ 2 ^ total := Nat.pow_le_pow_right (by omega) (by omega)

end PositiveTuple

/-- Positive assignments on an arbitrary finite labelled carrier with
prescribed total.  This is the form used for leaf multiplicities and for
the `χ` assignment to an enumeration of the realized set. -/
def PositiveAssignment (ι : Type*) [Fintype ι] (total : ℕ) :=
  {f : ι → Fin (total + 1) //
    (∀ i, 0 < (f i).1) ∧ ∑ i, (f i).1 = total}

namespace PositiveAssignment

variable {ι : Type*} [Fintype ι]

noncomputable instance (total : ℕ) :
    Fintype (PositiveAssignment ι total) := by
  classical
  exact inferInstanceAs
    (Fintype
      {f : ι → Fin (total + 1) //
        (∀ i, 0 < (f i).1) ∧ ∑ i, (f i).1 = total})

/-- Canonically order a finite labelled carrier and read an assignment as a
composition. -/
noncomputable def toComposition {total : ℕ}
    (f : PositiveAssignment ι total) : Composition total where
  blocks :=
    List.ofFn fun i => (f.1 ((Fintype.equivFin ι).symm i)).1
  blocks_pos := by
    intro a ha
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact f.2.1 _
  blocks_sum := by
    rw [List.sum_ofFn]
    exact (Equiv.sum_comp (Fintype.equivFin ι).symm
      (fun i => (f.1 i).1)).trans f.2.2

theorem toComposition_injective {total : ℕ} :
    Function.Injective
      (@toComposition ι _ total) := by
  intro f g h
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hfun := List.ofFn_injective (congrArg Composition.blocks h)
  simpa using congrFun hfun ((Fintype.equivFin ι) i)

/-- Paper (5.8)--(5.9): assignments to any finite labelled carrier have no
factorial loss. -/
theorem card_le_two_pow (total : ℕ) :
    Fintype.card (PositiveAssignment ι total) ≤ 2 ^ total := by
  calc
    Fintype.card (PositiveAssignment ι total)
        ≤ Fintype.card (Composition total) :=
      Fintype.card_le_of_injective toComposition toComposition_injective
    _ = 2 ^ (total - 1) := composition_card total
    _ ≤ 2 ^ total := Nat.pow_le_pow_right (by omega) (by omega)

end PositiveAssignment

end Anderson4D
