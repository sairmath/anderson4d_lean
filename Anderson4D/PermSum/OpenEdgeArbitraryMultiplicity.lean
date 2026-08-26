import Anderson4D.PermSum.OpenEdgePermSumApplication

/-!
# Augmented multiplicities from an arbitrary open-edge word

An open-edge word need not itself have leaf multiplicities at least two:
when the endpoint labels differ, either endpoint label may occur only once.
The two dummy copies supply exactly the missing multiplicities.  This file constructs the
paper-facing `Multiplicities` record directly from the augmented word,
without assuming an old `Multiplicities` profile.

Surjectivity of the old word makes every augmented leaf fibre positive.
The augmented full word-respecting pairing makes every fibre even.  Hence
every augmented multiplicity is at least two.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open PlaneTree
open scoped BigOperators

/-! ## Positivity and parity of the actual augmented counts -/

/-- Every letter occurs at least once in a surjective finite word. -/
theorem one_le_wordFiberCount_of_surjective
    {α : Type*} [DecidableEq α] {m : ℕ}
    {w : Fin m → α} (hsurj : Function.Surjective w)
    (x : α) :
    1 ≤ wordFiberCount w x := by
  obtain ⟨i, hi⟩ := hsurj x
  unfold wordFiberCount
  apply Finset.card_pos.mpr
  exact
    ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hi⟩⟩

/-- Every augmented letter fibre is positive when the old word is
surjective. -/
theorem one_le_wordFiberCount_openEdgeAugmentedWord
    {α : Type*} [DecidableEq α] {m : ℕ}
    (w : Fin m → α) (hsurj : Function.Surjective w)
    (a b : Fin m) (x : α) :
    1 ≤ wordFiberCount (openEdgeAugmentedWord w a b) x := by
  have hold :
      1 ≤ wordFiberCount w x :=
    one_le_wordFiberCount_of_surjective hsurj x
  rw [wordFiberCount_openEdgeAugmentedWord]
  omega

/-- Positivity plus the full word-respecting augmented pairing upgrades
every actual augmented leaf count to at least two. -/
theorem two_le_wordFiberCount_openEdgeAugmentedWord
    {α : Type*} [DecidableEq α] {m : ℕ}
    (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b)
    (hfull : κ.IsFull)
    (w : Fin m → α) (hsurj : Function.Surjective w)
    (hrespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        w i = w (κ i)) :
    ∀ x : α,
      2 ≤ wordFiberCount
        (openEdgeAugmentedWord w a b) x := by
  intro x
  have hpos :
      1 ≤ wordFiberCount
        (openEdgeAugmentedWord w a b) x :=
    one_le_wordFiberCount_openEdgeAugmentedWord
      w hsurj a b x
  have heven :
      Even
        (wordFiberCount
          (openEdgeAugmentedWord w a b) x) :=
    even_wordFiberCount_openEdgeAugmentedWord
      κ a b hκab hab hfull w hrespect x
  obtain ⟨q, hq⟩ := heven
  omega

/-! ## Direct construction of the augmented `Multiplicities` -/

/-- A word whose every leaf count is at least two defines the canonical
paper-facing multiplicity record from its actual fibre counts. -/
def wordFiberMultiplicities
    {t : PlaneTree} {q : ℕ}
    (u : Fin q → HeppLeaf t)
    (htwo : ∀ l : HeppLeaf t,
      2 ≤ wordFiberCount u l) :
    Multiplicities t where
  m := fun v =>
    if hv : v ∈ Leaves t then
      wordFiberCount u ⟨v, hv⟩
    else
      0
  two_le := by
    intro v hv
    rw [dif_pos hv]
    exact htwo ⟨v, hv⟩

@[simp]
theorem leafMultiplicity_wordFiberMultiplicities
    {t : PlaneTree} {q : ℕ}
    (u : Fin q → HeppLeaf t)
    (htwo : ∀ l : HeppLeaf t,
      2 ≤ wordFiberCount u l)
    (l : HeppLeaf t) :
    leafMultiplicity (wordFiberMultiplicities u htwo) l =
      wordFiberCount u l := by
  unfold leafMultiplicity wordFiberMultiplicities
  dsimp only
  rw [dif_pos l.2]

/-- The augmented multiplicity record constructed without any old
profile. -/
def openEdgeArbitraryMultiplicities
    {t : PlaneTree} {m : ℕ}
    (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b)
    (hfull : κ.IsFull)
    (w : Fin m → HeppLeaf t)
    (hsurj : Function.Surjective w)
    (hrespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        w i = w (κ i)) :
    Multiplicities t :=
  wordFiberMultiplicities
    (openEdgeAugmentedWord w a b)
    (two_le_wordFiberCount_openEdgeAugmentedWord
      κ a b hκab hab hfull w hsurj hrespect)

@[simp]
theorem leafMultiplicity_openEdgeArbitraryMultiplicities
    {t : PlaneTree} {m : ℕ}
    (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b)
    (hfull : κ.IsFull)
    (w : Fin m → HeppLeaf t)
    (hsurj : Function.Surjective w)
    (hrespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        w i = w (κ i))
    (l : HeppLeaf t) :
    leafMultiplicity
        (openEdgeArbitraryMultiplicities
          κ a b hκab hab hfull w hsurj hrespect) l =
      wordFiberCount
        (openEdgeAugmentedWord w a b) l := by
  exact leafMultiplicity_wordFiberMultiplicities _ _ l

/-- The directly constructed augmented profile has total length `m + 2`. -/
theorem totalMultiplicity_openEdgeArbitraryMultiplicities
    {t : PlaneTree} {m : ℕ}
    (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b)
    (hfull : κ.IsFull)
    (w : Fin m → HeppLeaf t)
    (hsurj : Function.Surjective w)
    (hrespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        w i = w (κ i)) :
    totalMultiplicity
        (openEdgeArbitraryMultiplicities
          κ a b hκab hab hfull w hsurj hrespect) =
      m + 2 := by
  unfold totalMultiplicity
  simp_rw [leafMultiplicity_openEdgeArbitraryMultiplicities]
  exact sum_wordFiberCount_openEdgeAugmentedWord w a b

/-- Every leaf multiplicity of the directly constructed profile is even. -/
theorem even_leafMultiplicity_openEdgeArbitraryMultiplicities
    {t : PlaneTree} {m : ℕ}
    (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b)
    (hfull : κ.IsFull)
    (w : Fin m → HeppLeaf t)
    (hsurj : Function.Surjective w)
    (hrespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        w i = w (κ i)) :
    ∀ l : HeppLeaf t,
      Even
        (leafMultiplicity
          (openEdgeArbitraryMultiplicities
            κ a b hκab hab hfull w hsurj hrespect) l) := by
  intro l
  rw [leafMultiplicity_openEdgeArbitraryMultiplicities]
  exact
    even_wordFiberCount_openEdgeAugmentedWord
      κ a b hκab hab hfull w hrespect l

/-- The augmented word realizes exactly the directly constructed profile. -/
theorem openEdgeAugmentedWord_mem_arbitraryValidWords
    {t : PlaneTree} {m : ℕ}
    (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b)
    (hfull : κ.IsFull)
    (w : Fin m → HeppLeaf t)
    (hsurj : Function.Surjective w)
    (hrespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        w i = w (κ i)) :
    openEdgeAugmentedWord w a b ∈
      validWords
        (leafMultiplicity
          (openEdgeArbitraryMultiplicities
            κ a b hκab hab hfull w hsurj hrespect)) := by
  rw [validWords, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun l => ?_⟩
  rw [leafMultiplicity_openEdgeArbitraryMultiplicities]
  rfl

/-- Exact order, total, parity, and valid-word certificate needed to apply
`PermSumEstimate`, with no old multiplicity hypothesis. -/
theorem exists_openEdgeArbitraryPermSumMultiplicityData
    {t : PlaneTree} {m : ℕ}
    (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b)
    (hfull : κ.IsFull)
    (w : Fin m → HeppLeaf t)
    (hsurj : Function.Surjective w)
    (hrespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        w i = w (κ i)) :
    ∃ n : ℕ,
      2 ≤ n ∧
      totalMultiplicity
          (openEdgeArbitraryMultiplicities
            κ a b hκab hab hfull w hsurj hrespect) =
        2 * n ∧
      (∀ l : HeppLeaf t,
        Even
          (leafMultiplicity
            (openEdgeArbitraryMultiplicities
              κ a b hκab hab hfull w hsurj hrespect) l)) ∧
      openEdgeAugmentedWord w a b ∈
        validWords
          (leafMultiplicity
            (openEdgeArbitraryMultiplicities
              κ a b hκab hab hfull w hsurj hrespect)) := by
  have hm : 0 < m :=
    lt_of_le_of_lt (Nat.zero_le a.val) a.isLt
  have haugFull :
      (openEdgeAugmentedPairing κ a b hκab hab).IsFull :=
    openEdgeAugmentedPairing_isFull
      κ a b hκab hab hfull
  have haugEven : Even (m + 2) := by
    simpa using haugFull.even_card
  obtain ⟨n, hnEq⟩ := haugEven
  refine ⟨n, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [totalMultiplicity_openEdgeArbitraryMultiplicities]
    omega
  · exact
      even_leafMultiplicity_openEdgeArbitraryMultiplicities
        κ a b hκab hab hfull w hsurj hrespect
  · exact
      openEdgeAugmentedWord_mem_arbitraryValidWords
        κ a b hκab hab hfull w hsurj hrespect

/-! ## Direct fixed-word use of Proposition 5.7 -/

/-- A single arbitrary open-edge word, after dummy closure, is controlled
by the literal Proposition 5.7 right-hand side for its actual augmented
profile. -/
theorem openEdgeArbitraryAugmented_chain_le_permSumRHS
    {C : ℝ} (hperm : PermSumEstimate C)
    {t : PlaneTree} {m M : ℕ}
    (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a < b)
    (hfull : κ.IsFull) (hprimitive : IsPrimitive κ)
    (w : Fin m → HeppLeaf t)
    (hsurj : Function.Surjective w)
    (hrespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        w i = w (κ i))
    (Nm : HeppMarking t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hadm : IsAdmissible Nm M z) :
    ∃ n : ℕ, 2 ≤ n ∧
      heppChainWeight z
          (openEdgeAugmentedWord w a b) ≤
        permSumRHS C n t Nm
          (openEdgeArbitraryMultiplicities
            κ a b hκab (ne_of_lt hab) hfull
              w hsurj hrespect) := by
  let mu' :=
    openEdgeArbitraryMultiplicities
      κ a b hκab (ne_of_lt hab) hfull
        w hsurj hrespect
  obtain ⟨n, hn, htotal, heven, hvalid⟩ :=
    exists_openEdgeArbitraryPermSumMultiplicityData
      κ a b hκab (ne_of_lt hab) hfull
        w hsurj hrespect
  change totalMultiplicity mu' = 2 * n at htotal
  change ∀ l : HeppLeaf t,
    Even (leafMultiplicity mu' l) at heven
  change openEdgeAugmentedWord w a b ∈
    validWords (leafMultiplicity mu') at hvalid
  have hlen : m + 2 = 2 * n := by
    rw [← htotal]
    exact
      (totalMultiplicity_openEdgeArbitraryMultiplicities
        κ a b hκab (ne_of_lt hab) hfull
          w hsurj hrespect).symm
  have hnp :
      NoProperLeafBlock
        (openEdgeAugmentedWord w a b) :=
    noProperLeafBlock_openEdgeAugmentedWord
      κ a b hκab hab hfull hprimitive w hrespect
  have hsingle :
      heppChainWeight z
          (openEdgeAugmentedWord w a b) ≤
        paperSum (M := m + 2) (leafMultiplicity mu')
          (primitiveChainWeight (m := m + 2) z) := by
    calc
      heppChainWeight z
          (openEdgeAugmentedWord w a b) =
          primitiveChainWeight z
            (openEdgeAugmentedWord w a b) := by
        simp [primitiveChainWeight, hnp]
      _ ≤ paperSum (M := m + 2) (leafMultiplicity mu')
            (primitiveChainWeight (m := m + 2) z) := by
        exact primitiveChainWeight_le_paperSum_of_mem
          mu' z (openEdgeAugmentedWord w a b) hvalid
  have hbound :
      paperSum (M := 2 * n) (leafMultiplicity mu')
          (primitiveChainWeight (m := 2 * n) z) ≤
        permSumRHS C n t Nm mu' :=
    hperm.2 n M t Nm mu' z hn ht hroot
      htotal heven hadm
  rw [← hlen] at hbound
  exact ⟨n, hn, hsingle.trans hbound⟩

end

end Anderson4D
