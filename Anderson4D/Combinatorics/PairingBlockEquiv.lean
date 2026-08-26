import Anderson4D.Combinatorics.PairingHeadCases

/-!
# Splitting a pairing along a closed finite block

A pairing which preserves a finite block is exactly a pair consisting of a
pairing on that block and a pairing on its complement.  This elementary
equivalence is the finite combinatorial engine needed to sum all primitive
pairings on one R-322/R-324 block before proceeding to the remaining
variables.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

namespace PartialPairing

variable {α : Type*} [DecidableEq α]

/-- Combine pairings on a finite block and its complement. -/
def combineAlongFinset
    (B : Finset α)
    (κB : PartialPairing B)
    (κC : PartialPairing {i : α // i ∉ B}) :
    PartialPairing α where
  toFun i :=
    if hi : i ∈ B then
      (κB ⟨i, hi⟩).1
    else
      (κC ⟨i, hi⟩).1
  involutive i := by
    by_cases hi : i ∈ B
    · have hout :
          (κB ⟨i, hi⟩).1 ∈ B :=
        (κB ⟨i, hi⟩).2
      simp only [hi, hout, dite_true]
      exact congrArg Subtype.val
        (κB.apply_apply ⟨i, hi⟩)
    · have hout :
          (κC ⟨i, hi⟩).1 ∉ B :=
        (κC ⟨i, hi⟩).2
      simp only [hi, hout, dite_false]
      exact congrArg Subtype.val
        (κC.apply_apply ⟨i, hi⟩)

@[simp]
theorem combineAlongFinset_apply_mem
    (B : Finset α)
    (κB : PartialPairing B)
    (κC : PartialPairing {i : α // i ∉ B})
    (i : α) (hi : i ∈ B) :
    combineAlongFinset B κB κC i =
      (κB ⟨i, hi⟩).1 := by
  simp [combineAlongFinset, hi]

@[simp]
theorem combineAlongFinset_apply_notMem
    (B : Finset α)
    (κB : PartialPairing B)
    (κC : PartialPairing {i : α // i ∉ B})
    (i : α) (hi : i ∉ B) :
    combineAlongFinset B κB κC i =
      (κC ⟨i, hi⟩).1 := by
  simp [combineAlongFinset, hi]

theorem combineAlongFinset_mapsTo
    (B : Finset α)
    (κB : PartialPairing B)
    (κC : PartialPairing {i : α // i ∉ B}) :
    ∀ i ∈ B,
      combineAlongFinset B κB κC i ∈ B := by
  intro i hi
  rw [combineAlongFinset_apply_mem B κB κC i hi]
  exact (κB ⟨i, hi⟩).2

/-- Pairings preserving `B`, with the closure certificate included in the
finite type. -/
abbrev ClosedOn (B : Finset α) :=
  {κ : PartialPairing α // ∀ i ∈ B, κ i ∈ B}

/-- Exact decomposition of a pairing along a closed finite block. -/
def closedOnEquiv
    (B : Finset α) :
    ClosedOn B ≃
      PartialPairing B ×
        PartialPairing {i : α // i ∉ B} where
  toFun κ :=
    (restrictTo κ.1 κ.2,
      restrictCompl κ.1 κ.2)
  invFun p :=
    ⟨combineAlongFinset B p.1 p.2,
      combineAlongFinset_mapsTo B p.1 p.2⟩
  left_inv κ := by
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ B
    · rw [combineAlongFinset_apply_mem]
      exact restrictTo_apply_val κ.1 κ.2 ⟨i, hi⟩
    · rw [combineAlongFinset_apply_notMem]
      exact restrictCompl_apply_coe κ.1 κ.2 ⟨i, hi⟩
  right_inv p := by
    apply Prod.ext
    · ext i
      exact combineAlongFinset_apply_mem
        B p.1 p.2 i.1 i.2
    · ext i
      exact combineAlongFinset_apply_notMem
        B p.1 p.2 i.1 i.2

@[simp]
theorem closedOnEquiv_apply_fst
    (B : Finset α) (κ : ClosedOn B) :
    (closedOnEquiv B κ).1 =
      restrictTo κ.1 κ.2 :=
  rfl

@[simp]
theorem closedOnEquiv_apply_snd
    (B : Finset α) (κ : ClosedOn B) :
    (closedOnEquiv B κ).2 =
      restrictCompl κ.1 κ.2 :=
  rfl

/-- Fullness of the combined pairing is equivalent to fullness on the
block and on its complement. -/
theorem combineAlongFinset_isFull_iff
    (B : Finset α)
    (κB : PartialPairing B)
    (κC : PartialPairing {i : α // i ∉ B}) :
    (combineAlongFinset B κB κC).IsFull ↔
      κB.IsFull ∧ κC.IsFull := by
  constructor
  · intro hfull
    constructor
    · intro i hiFix
      apply hfull i.1
      rw [combineAlongFinset_apply_mem B κB κC i.1 i.2]
      exact congrArg Subtype.val hiFix
    · intro i hiFix
      apply hfull i.1
      rw [combineAlongFinset_apply_notMem B κB κC i.1 i.2]
      exact congrArg Subtype.val hiFix
  · rintro ⟨hB, hC⟩ i hiFix
    by_cases hi : i ∈ B
    · have hval :
          (κB ⟨i, hi⟩).1 = i := by
        rw [← combineAlongFinset_apply_mem
          B κB κC i hi, hiFix]
      exact hB ⟨i, hi⟩ (Subtype.ext hval)
    · have hval :
          (κC ⟨i, hi⟩).1 = i := by
        rw [← combineAlongFinset_apply_notMem
          B κB κC i hi, hiFix]
      exact hC ⟨i, hi⟩ (Subtype.ext hval)

/-- Restriction to a closed block containing no fixed point is a full
pairing. -/
theorem restrictTo_isFull_of_ne
    (κ : PartialPairing α) (B : Finset α)
    (hclosed : ∀ i ∈ B, κ i ∈ B)
    (hne : ∀ i ∈ B, κ i ≠ i) :
    (restrictTo κ hclosed).IsFull := by
  intro i hi
  exact hne i.1 i.2
    (congrArg Subtype.val hi)

omit [DecidableEq α] in
/-- If the ambient pairing is full, its restriction to the complement of a
closed block is full as well. -/
theorem restrictCompl_isFull
    (κ : PartialPairing α) (B : Finset α)
    (hclosed : ∀ i ∈ B, κ i ∈ B)
    (hfull : κ.IsFull) :
    (restrictCompl κ hclosed).IsFull := by
  intro i hi
  exact hfull i.1
    (congrArg Subtype.val hi)

section FiniteSums

variable [Fintype α]

/-- A sum over pairings preserving `B` is exactly an iterated sum over the
pairing on `B` and the pairing on its complement. -/
theorem sum_closedOn_eq_sum_restrictions
    {M : Type*} [AddCommMonoid M]
    (B : Finset α) (F : ClosedOn B → M) :
    (∑ κ : ClosedOn B, F κ) =
      ∑ κB : PartialPairing B,
        ∑ κC : PartialPairing {i : α // i ∉ B},
          F ((closedOnEquiv B).symm (κB, κC)) := by
  calc
    (∑ κ : ClosedOn B, F κ) =
        ∑ p :
          PartialPairing B ×
            PartialPairing {i : α // i ∉ B},
          F ((closedOnEquiv B).symm p) :=
      ((closedOnEquiv B).symm.sum_comp F).symm
    _ = ∑ κB : PartialPairing B,
          ∑ κC : PartialPairing {i : α // i ∉ B},
            F ((closedOnEquiv B).symm (κB, κC)) := by
      rw [Fintype.sum_prod_type]

end FiniteSums

end PartialPairing

end Anderson4D
