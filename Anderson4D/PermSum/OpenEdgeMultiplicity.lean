import Anderson4D.Combinatorics.OpenEdgeAugmentation
import Anderson4D.PermSum.Statements

/-!
# Multiplicity ledger for one opened edge

Closing one covariance edge appends copies of its two endpoint labels.
This file records only the resulting finite counting facts:

* every letter count is the old count plus the two endpoint indicators;
* the total count is `m + 2`;
* a full augmented pairing respecting the augmented word makes every
  letter count even; and
* these counts package as the `Multiplicities` and order hypotheses
  consumed by `PermSumEstimate`.

There are no geometric or analytic hypotheses in this module.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open PlaneTree
open scoped BigOperators

/-- Number of occurrences of `x` in a finite word. -/
def wordFiberCount {α : Type*} [DecidableEq α] {m : ℕ}
    (w : Fin m → α) (x : α) : ℕ :=
  (Finset.univ.filter fun i => w i = x).card

/-- The occurrence count of a letter after closing one open edge is
the old count plus one copy of each endpoint label. -/
theorem wordFiberCount_openEdgeAugmentedWord
    {α : Type*} [DecidableEq α] {m : ℕ}
    (w : Fin m → α) (a b : Fin m) (x : α) :
    wordFiberCount (openEdgeAugmentedWord w a b) x =
      wordFiberCount w x +
        (if w a = x then 1 else 0) +
        (if w b = x then 1 else 0) := by
  let e :
      {i : Fin (m + 2) //
        openEdgeAugmentedWord w a b i = x} ≃
      {s : Fin m ⊕ Fin 2 //
        openEdgeAugmentedSumWord w a b s = x} :=
    Equiv.subtypeEquiv finSumFinEquiv.symm (fun _ => Iff.rfl)
  calc
    wordFiberCount (openEdgeAugmentedWord w a b) x =
        Fintype.card
          {i : Fin (m + 2) //
            openEdgeAugmentedWord w a b i = x} := by
      rw [wordFiberCount, Fintype.card_subtype]
    _ =
        Fintype.card
          {s : Fin m ⊕ Fin 2 //
            openEdgeAugmentedSumWord w a b s = x} :=
      Fintype.card_congr e
    _ =
        Fintype.card {i : Fin m // w i = x} +
          Fintype.card
            {j : Fin 2 //
              (if j = 0 then w a else w b) = x} := by
      rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
      simp only [openEdgeAugmentedSumWord]
      rfl
    _ =
        wordFiberCount w x +
          (if w a = x then 1 else 0) +
          (if w b = x then 1 else 0) := by
      have hright :
          Fintype.card
              {j : Fin 2 //
                (if j = 0 then w a else w b) = x} =
            (if w a = x then 1 else 0) +
              (if w b = x then 1 else 0) := by
        rw [Fintype.card_subtype, Finset.card_filter,
          Fin.sum_univ_two]
        simp
      rw [Fintype.card_subtype, wordFiberCount, hright]
      omega

/-- Every old word fibre injects into the corresponding augmented
fibre. -/
theorem wordFiberCount_le_openEdgeAugmentedWord
    {α : Type*} [DecidableEq α] {m : ℕ}
    (w : Fin m → α) (a b : Fin m) (x : α) :
    wordFiberCount w x ≤
      wordFiberCount (openEdgeAugmentedWord w a b) x := by
  rw [wordFiberCount_openEdgeAugmentedWord]
  omega

/-- Consequently, the full factorial ledger of the open word is
dominated by the factorial ledger after dummy closure. -/
theorem wordFiberFactorialLedger_le_openEdgeAugmented
    {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (w : Fin m → α) (a b : Fin m) :
    (∏ x : α, ((wordFiberCount w x).factorial : ℝ)) ≤
      ∏ x : α,
        ((wordFiberCount
          (openEdgeAugmentedWord w a b) x).factorial : ℝ) := by
  apply Finset.prod_le_prod
  · intro x _hx
    positivity
  · intro x _hx
    exact_mod_cast Nat.factorial_le
      (wordFiberCount_le_openEdgeAugmentedWord w a b x)

/-- The counts of all letters in a word sum to its length. -/
theorem sum_wordFiberCount
    {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (w : Fin m → α) :
    ∑ x : α, wordFiberCount w x = m := by
  simpa [wordFiberCount] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin m))
      (Finset.univ : Finset α) w)

/-- In particular, the augmented word has total length `m + 2`. -/
theorem sum_wordFiberCount_openEdgeAugmentedWord
    {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (w : Fin m → α) (a b : Fin m) :
    ∑ x : α,
        wordFiberCount (openEdgeAugmentedWord w a b) x =
      m + 2 :=
  sum_wordFiberCount (openEdgeAugmentedWord w a b)

namespace PartialPairing

/-- Restriction of a word-respecting pairing to one word fibre. -/
def restrictWordFiber
    {α : Type*} [DecidableEq α] {m : ℕ}
    (κ : PartialPairing (Fin m)) (w : Fin m → α)
    (hrespect : κ.RespectsWord w) (x : α) :
    PartialPairing {i : Fin m // w i = x} where
  toFun i :=
    ⟨κ i.1, by
      rw [← hrespect i.1]
      exact i.2⟩
  involutive i := by
    apply Subtype.ext
    exact κ.apply_apply i.1

/-- Fullness is inherited by every word fibre. -/
theorem restrictWordFiber_isFull
    {α : Type*} [DecidableEq α] {m : ℕ}
    {κ : PartialPairing (Fin m)} {w : Fin m → α}
    (hfull : κ.IsFull) (hrespect : κ.RespectsWord w)
    (x : α) :
    (κ.restrictWordFiber w hrespect x).IsFull := by
  intro i hi
  apply hfull i.1
  exact congrArg Subtype.val hi

end PartialPairing

/-- Every letter fibre of a full word-respecting pairing has even
cardinality. -/
theorem even_wordFiberCount_of_full_respectsWord
    {α : Type*} [DecidableEq α] {m : ℕ}
    {κ : PartialPairing (Fin m)} {w : Fin m → α}
    (hfull : κ.IsFull) (hrespect : κ.RespectsWord w)
    (x : α) :
    Even (wordFiberCount w x) := by
  rw [wordFiberCount, ← Fintype.card_subtype]
  exact
    (PartialPairing.restrictWordFiber_isFull
      hfull hrespect x).even_card

/-- Closing one open edge makes every augmented letter multiplicity even,
provided every unmarked old edge respects the old word. -/
theorem even_wordFiberCount_openEdgeAugmentedWord
    {α : Type*} [DecidableEq α] {m : ℕ}
    (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b)
    (hfull : κ.IsFull) (w : Fin m → α)
    (hrespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        w i = w (κ i)) :
    ∀ x : α,
      Even (wordFiberCount
        (openEdgeAugmentedWord w a b) x) := by
  intro x
  exact even_wordFiberCount_of_full_respectsWord
    (openEdgeAugmentedPairing_isFull
      κ a b hκab hab hfull)
    (openEdgeAugmentedPairing_respectsWord
      κ a b hκab hab w hrespect)
    x

/-! ## Packaging for `PermSumEstimate` -/

/-- Leaf multiplicities read directly from the augmented word. -/
def openEdgeAugmentedLeafMultiplicity
    {t : PlaneTree} {m : ℕ}
    (w : Fin m → HeppLeaf t) (a b : Fin m) :
    HeppLeaf t → ℕ :=
  fun l =>
    wordFiberCount (openEdgeAugmentedWord w a b) l

/-- The augmented counts form a `Multiplicities` bundle whenever the old
word realizes an existing multiplicity profile. -/
def openEdgeAugmentedMultiplicities
    {t : PlaneTree} {m : ℕ}
    (mu : Multiplicities t) (w : Fin m → HeppLeaf t)
    (hw : w ∈ validWords (leafMultiplicity mu))
    (a b : Fin m) : Multiplicities t where
  m := fun v =>
    if hv : v ∈ Leaves t then
      openEdgeAugmentedLeafMultiplicity w a b ⟨v, hv⟩
    else
      0
  two_le := by
    intro v hv
    rw [dif_pos hv]
    have hold :
        wordFiberCount w ⟨v, hv⟩ =
          leafMultiplicity mu ⟨v, hv⟩ := by
      exact (Finset.mem_filter.mp hw).2 ⟨v, hv⟩
    have htwo :
        2 ≤ wordFiberCount w ⟨v, hv⟩ := by
      rw [hold]
      exact mu.two_le v hv
    rw [openEdgeAugmentedLeafMultiplicity,
      wordFiberCount_openEdgeAugmentedWord]
    omega

@[simp]
theorem leafMultiplicity_openEdgeAugmentedMultiplicities
    {t : PlaneTree} {m : ℕ}
    (mu : Multiplicities t) (w : Fin m → HeppLeaf t)
    (hw : w ∈ validWords (leafMultiplicity mu))
    (a b : Fin m) (l : HeppLeaf t) :
    leafMultiplicity
        (openEdgeAugmentedMultiplicities mu w hw a b) l =
      openEdgeAugmentedLeafMultiplicity w a b l := by
  unfold leafMultiplicity openEdgeAugmentedMultiplicities
  dsimp only
  rw [dif_pos l.2]

/-- The augmented word realizes exactly its packaged multiplicities. -/
theorem openEdgeAugmentedWord_mem_packagedValidWords
    {t : PlaneTree} {m : ℕ}
    (mu : Multiplicities t) (w : Fin m → HeppLeaf t)
    (hw : w ∈ validWords (leafMultiplicity mu))
    (a b : Fin m) :
    openEdgeAugmentedWord w a b ∈
      validWords
        (leafMultiplicity
          (openEdgeAugmentedMultiplicities mu w hw a b)) := by
  rw [validWords, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun l => ?_⟩
  rw [leafMultiplicity_openEdgeAugmentedMultiplicities]
  rfl

/-- The packaged total multiplicity is exactly the augmented length. -/
theorem totalMultiplicity_openEdgeAugmentedMultiplicities
    {t : PlaneTree} {m : ℕ}
    (mu : Multiplicities t) (w : Fin m → HeppLeaf t)
    (hw : w ∈ validWords (leafMultiplicity mu))
    (a b : Fin m) :
    totalMultiplicity
        (openEdgeAugmentedMultiplicities mu w hw a b) =
      m + 2 := by
  unfold totalMultiplicity
  simp_rw [leafMultiplicity_openEdgeAugmentedMultiplicities]
  exact sum_wordFiberCount_openEdgeAugmentedWord w a b

/-- The packaged leaf multiplicities are all even under the one-open-edge
pairing hypotheses. -/
theorem even_leafMultiplicity_openEdgeAugmentedMultiplicities
    {t : PlaneTree} {m : ℕ}
    (mu : Multiplicities t) (w : Fin m → HeppLeaf t)
    (hw : w ∈ validWords (leafMultiplicity mu))
    (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b)
    (hfull : κ.IsFull)
    (hrespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        w i = w (κ i)) :
    ∀ l : HeppLeaf t,
      Even
        (leafMultiplicity
          (openEdgeAugmentedMultiplicities mu w hw a b) l) := by
  intro l
  rw [leafMultiplicity_openEdgeAugmentedMultiplicities]
  exact
    even_wordFiberCount_openEdgeAugmentedWord
      κ a b hκab hab hfull w hrespect l

/-- Exact order, total-multiplicity, parity, and valid-word certificate
needed to instantiate `PermSumEstimate` on the augmented word. -/
theorem exists_openEdgeAugmentedPermSumMultiplicityData
    {t : PlaneTree} {m : ℕ}
    (mu : Multiplicities t) (w : Fin m → HeppLeaf t)
    (hw : w ∈ validWords (leafMultiplicity mu))
    (κ : PartialPairing (Fin m))
    (a b : Fin m) (hm : 0 < m)
    (hκab : κ a = b) (hab : a ≠ b)
    (hfull : κ.IsFull)
    (hrespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        w i = w (κ i)) :
    ∃ n : ℕ,
      2 ≤ n ∧
      totalMultiplicity
          (openEdgeAugmentedMultiplicities mu w hw a b) =
        2 * n ∧
      (∀ l : HeppLeaf t,
        Even
          (leafMultiplicity
            (openEdgeAugmentedMultiplicities mu w hw a b) l)) ∧
      openEdgeAugmentedWord w a b ∈
        validWords
          (leafMultiplicity
            (openEdgeAugmentedMultiplicities mu w hw a b)) := by
  have hmEven : Even m := by
    simpa using hfull.even_card
  obtain ⟨r, hr⟩ := hmEven
  have hmTwo : 2 ≤ m := by omega
  have haugFull :
      (openEdgeAugmentedPairing κ a b hκab hab).IsFull :=
    openEdgeAugmentedPairing_isFull
      κ a b hκab hab hfull
  have haugEven : Even (m + 2) := by
    simpa using haugFull.even_card
  obtain ⟨n, hn⟩ := haugEven
  refine ⟨n, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [totalMultiplicity_openEdgeAugmentedMultiplicities]
    omega
  · exact
      even_leafMultiplicity_openEdgeAugmentedMultiplicities
        mu w hw κ a b hκab hab hfull hrespect
  · exact openEdgeAugmentedWord_mem_packagedValidWords
      mu w hw a b

end

end Anderson4D
