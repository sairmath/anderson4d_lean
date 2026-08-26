import Anderson4D.PermSum.OpenEdgeArbitraryMultiplicity
import Anderson4D.PermSum.OpenEdgeWeight

/-!
# Raw-count fixed-endpoint fibres for one open edge

The old open word may have singleton endpoint labels, so it need not
belong to the valid-word fibre of any `Multiplicities` record.  The
correct source fibre is instead determined by:

* the literal occurrence counts of a surjective reference word;
* its two selected endpoint labels; and
* equality of labels along every unmarked pairing edge.

Dummy augmentation makes all counts even and at least two.  The whole
raw source fibre then injects into the single augmented valid-word fibre
defined by the reference word, where Proposition 5.7 applies.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open PlaneTree
open scoped BigOperators

/-- The correct old-word fibre: raw counts, fixed selected endpoint
labels, and the unmarked pairing constraint. -/
def openEdgeRawCountFixedEndpointFiber
    {t : PlaneTree} {m : ℕ}
    (κ : PartialPairing (Fin m))
    (a b : Fin m)
    (reference : Fin m → HeppLeaf t) :
    Finset (Fin m → HeppLeaf t) :=
  Finset.univ.filter fun w =>
    (∀ l : HeppLeaf t,
      wordFiberCount w l =
        wordFiberCount reference l) ∧
    w a = reference a ∧
    w b = reference b ∧
    ∀ i : Fin m, i ≠ a → i ≠ b →
      w i = w (κ i)

@[simp]
theorem mem_openEdgeRawCountFixedEndpointFiber
    {t : PlaneTree} {m : ℕ}
    {κ : PartialPairing (Fin m)}
    {a b : Fin m}
    {reference w : Fin m → HeppLeaf t} :
    w ∈ openEdgeRawCountFixedEndpointFiber
        κ a b reference ↔
      (∀ l : HeppLeaf t,
        wordFiberCount w l =
          wordFiberCount reference l) ∧
      w a = reference a ∧
      w b = reference b ∧
      ∀ i : Fin m, i ≠ a → i ≠ b →
        w i = w (κ i) := by
  simp [openEdgeRawCountFixedEndpointFiber]

/-- The reference word belongs to its own raw-count fibre whenever it
obeys the unmarked pairing constraint. -/
theorem reference_mem_openEdgeRawCountFixedEndpointFiber
    {t : PlaneTree} {m : ℕ}
    (κ : PartialPairing (Fin m))
    (a b : Fin m)
    (reference : Fin m → HeppLeaf t)
    (hrespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        reference i = reference (κ i)) :
    reference ∈
      openEdgeRawCountFixedEndpointFiber
        κ a b reference := by
  rw [mem_openEdgeRawCountFixedEndpointFiber]
  exact ⟨fun _ => rfl, rfl, rfl, hrespect⟩

/-- A word with the raw occurrence profile of a surjective reference is
itself surjective. -/
theorem surjective_of_wordFiberCount_eq_surjective
    {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} (reference w : Fin m → α)
    (href : Function.Surjective reference)
    (hcount :
      ∀ x : α,
        wordFiberCount w x =
          wordFiberCount reference x) :
    Function.Surjective w := by
  intro x
  have hrefCount :
      1 ≤ wordFiberCount reference x :=
    one_le_wordFiberCount_of_surjective href x
  have hwPos : 0 < wordFiberCount w x := by
    rw [hcount x]
    omega
  unfold wordFiberCount at hwPos
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hwPos
  exact ⟨i, (Finset.mem_filter.mp hi).2⟩

/-- Every member of a raw-count fibre over a surjective reference is
surjective. -/
theorem surjective_of_mem_openEdgeRawCountFixedEndpointFiber
    {t : PlaneTree} {m : ℕ}
    {κ : PartialPairing (Fin m)}
    {a b : Fin m}
    {reference w : Fin m → HeppLeaf t}
    (href : Function.Surjective reference)
    (hw :
      w ∈ openEdgeRawCountFixedEndpointFiber
        κ a b reference) :
    Function.Surjective w :=
  surjective_of_wordFiberCount_eq_surjective
    reference w href
    (mem_openEdgeRawCountFixedEndpointFiber.mp hw).1

/-- Equal old raw counts and equal selected endpoint labels give equal
augmented raw counts. -/
theorem wordFiberCount_openEdgeAugmentedWord_eq_of_rawProfile_endpoints
    {α : Type*} [DecidableEq α] {m : ℕ}
    (reference w : Fin m → α)
    (a b : Fin m)
    (hcount :
      ∀ x : α,
        wordFiberCount w x =
          wordFiberCount reference x)
    (ha : w a = reference a)
    (hb : w b = reference b) :
    ∀ x : α,
      wordFiberCount (openEdgeAugmentedWord w a b) x =
        wordFiberCount
          (openEdgeAugmentedWord reference a b) x := by
  intro x
  rw [wordFiberCount_openEdgeAugmentedWord,
    wordFiberCount_openEdgeAugmentedWord,
    hcount x, ha, hb]

/-- All words in one raw-count fixed-endpoint fibre induce literally the
same arbitrary augmented `Multiplicities` profile. -/
theorem openEdgeArbitraryMultiplicities_eq_of_rawProfile_endpoints
    {t : PlaneTree} {m : ℕ}
    (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b)
    (hfull : κ.IsFull)
    (reference w : Fin m → HeppLeaf t)
    (href : Function.Surjective reference)
    (hwSurj : Function.Surjective w)
    (hrefRespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        reference i = reference (κ i))
    (hwRespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        w i = w (κ i))
    (hcount :
      ∀ l : HeppLeaf t,
        wordFiberCount w l =
          wordFiberCount reference l)
    (ha : w a = reference a)
    (hb : w b = reference b) :
    openEdgeArbitraryMultiplicities
        κ a b hκab hab hfull
        w hwSurj hwRespect =
      openEdgeArbitraryMultiplicities
        κ a b hκab hab hfull
        reference href hrefRespect := by
  unfold openEdgeArbitraryMultiplicities
    wordFiberMultiplicities
  rw [Multiplicities.mk.injEq]
  funext v
  by_cases hv : v ∈ Leaves t
  · simp only [hv, dif_pos]
    exact
      wordFiberCount_openEdgeAugmentedWord_eq_of_rawProfile_endpoints
        reference w a b hcount ha hb ⟨v, hv⟩
  · simp [hv]

/-- Dummy augmentation is injective because the old word is retained on
the initial segment. -/
theorem openEdgeAugmentedWord_injective_raw
    {α : Type*} {m : ℕ} (a b : Fin m) :
    Function.Injective
      (fun w : Fin m → α =>
        openEdgeAugmentedWord w a b) := by
  intro w u h
  funext i
  have hi := congrFun h (Fin.castAdd 2 i)
  simpa using hi

/-- The factorial-prefactored paper sum dominates its nonnegative
valid-word sum. -/
theorem rawWordSum_le_paperSum_of_nonneg
    {α : Type*} [Fintype α] [DecidableEq α] {q : ℕ}
    (mult : α → ℕ) (F : (Fin q → α) → ℝ)
    (hF : ∀ u, 0 ≤ F u) :
    wordSum mult F ≤ paperSum mult F := by
  have hsum : 0 ≤ wordSum mult F := by
    unfold wordSum
    exact Finset.sum_nonneg fun u _hu => hF u
  have hledger :
      1 ≤ ∏ x : α, ((mult x).factorial : ℝ) := by
    apply Finset.one_le_prod
    intro x _hx
    exact_mod_cast Nat.factorial_pos (mult x)
  unfold paperSum
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hledger hsum

/-- The complete raw-count fixed-endpoint fibre is bounded by one
augmented Proposition 5.7 right-hand side.  The explicit square box
penalty is left for the selected high covariance coefficient to pay. -/
theorem rawCountFixedEndpointFiberSum_le_boxPenalty_mul_permSumRHS
    {C : ℝ} (hperm : PermSumEstimate C)
    {t : PlaneTree} {m M : ℕ}
    (reference : Fin m → HeppLeaf t)
    (href : Function.Surjective reference)
    (κ : PartialPairing (Fin m))
    (a b : Fin m) (hm : 0 < m)
    (hκab : κ a = b) (hab : a < b)
    (hfull : κ.IsFull) (hprimitive : IsPrimitive κ)
    (hrefRespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        reference i = reference (κ i))
    (Nm : HeppMarking t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hadm : IsAdmissible Nm M z) :
    ∃ n : ℕ, 2 ≤ n ∧
      (∑ w ∈ openEdgeRawCountFixedEndpointFiber
          κ a b reference,
        heppChainWeight z w) ≤
        (1 + (2 * (M : ℝ)) ^ 2) ^ 2 *
          permSumRHS C n t Nm
            (openEdgeArbitraryMultiplicities
              κ a b hκab (ne_of_lt hab) hfull
              reference href hrefRespect) := by
  let S :=
    openEdgeRawCountFixedEndpointFiber
      κ a b reference
  let f :
      (Fin m → HeppLeaf t) →
        (Fin (m + 2) → HeppLeaf t) :=
    fun w => openEdgeAugmentedWord w a b
  let mu' :=
    openEdgeArbitraryMultiplicities
      κ a b hκab (ne_of_lt hab) hfull
      reference href hrefRespect
  obtain ⟨n, hn, htotal, heven, _hrefAug⟩ :=
    exists_openEdgeArbitraryPermSumMultiplicityData
      κ a b hκab (ne_of_lt hab) hfull
      reference href hrefRespect
  change totalMultiplicity mu' = 2 * n at htotal
  change
    ∀ l : HeppLeaf t,
      Even (leafMultiplicity mu' l) at heven
  have hlen : m + 2 = 2 * n := by
    rw [← htotal]
    exact
      (totalMultiplicity_openEdgeArbitraryMultiplicities
        κ a b hκab (ne_of_lt hab) hfull
        reference href hrefRespect).symm
  have hfInj : Function.Injective f :=
    openEdgeAugmentedWord_injective_raw a b
  have himageValid :
      S.image f ⊆ validWords (leafMultiplicity mu') := by
    intro u hu
    obtain ⟨w, hwS, rfl⟩ := Finset.mem_image.mp hu
    have hwData :=
      mem_openEdgeRawCountFixedEndpointFiber.mp hwS
    have hwSurj : Function.Surjective w :=
      surjective_of_mem_openEdgeRawCountFixedEndpointFiber
        href hwS
    have hmu :
        openEdgeArbitraryMultiplicities
            κ a b hκab (ne_of_lt hab) hfull
            w hwSurj hwData.2.2.2 =
          mu' := by
      exact
        openEdgeArbitraryMultiplicities_eq_of_rawProfile_endpoints
          κ a b hκab (ne_of_lt hab) hfull
          reference w href hwSurj
          hrefRespect hwData.2.2.2
          hwData.1 hwData.2.1 hwData.2.2.1
    have hvalid :=
      openEdgeAugmentedWord_mem_arbitraryValidWords
        κ a b hκab (ne_of_lt hab) hfull
        w hwSurj hwData.2.2.2
    rw [hmu] at hvalid
    exact hvalid
  have himagePrimitive :
      ∀ u ∈ S.image f, NoProperLeafBlock u := by
    intro u hu
    obtain ⟨w, hwS, rfl⟩ := Finset.mem_image.mp hu
    have hwData :=
      mem_openEdgeRawCountFixedEndpointFiber.mp hwS
    exact
      noProperLeafBlock_openEdgeAugmentedWord
        κ a b hκab hab hfull hprimitive
        w hwData.2.2.2
  have hsourceWeight :
      (∑ w ∈ S, heppChainWeight z w) ≤
        (1 + (2 * (M : ℝ)) ^ 2) ^ 2 *
          ∑ w ∈ S,
            heppChainWeight z (f w) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w _hwS
    exact
      heppChainWeight_le_boxPenalty_sq_mul_openEdgeAugmented
        hm z hadm w a b
  have himage :
      (∑ w ∈ S,
          heppChainWeight z (f w)) ≤
        wordSum (M := m + 2) (leafMultiplicity mu')
          (primitiveChainWeight z) := by
    calc
      (∑ w ∈ S,
          heppChainWeight z (f w)) =
          ∑ w ∈ S, primitiveChainWeight z (f w) := by
        apply Finset.sum_congr rfl
        intro w hwS
        rw [primitiveChainWeight]
        rw [if_pos
          (himagePrimitive (f w)
            (Finset.mem_image_of_mem f hwS))]
      _ =
          ∑ u ∈ S.image f,
            primitiveChainWeight z u := by
        exact (Finset.sum_image hfInj.injOn).symm
      _ ≤
          ∑ u ∈ validWords (leafMultiplicity mu'),
            primitiveChainWeight z u := by
        exact
          Finset.sum_le_sum_of_subset_of_nonneg
            himageValid
            (fun u _hu _hnot =>
              primitiveChainWeight_nonneg z u)
      _ =
          wordSum (M := m + 2) (leafMultiplicity mu')
            (primitiveChainWeight z) := rfl
  have hpaper :
      wordSum (M := m + 2) (leafMultiplicity mu')
          (primitiveChainWeight z) ≤
        paperSum (M := m + 2) (leafMultiplicity mu')
          (primitiveChainWeight z) :=
    rawWordSum_le_paperSum_of_nonneg
      (leafMultiplicity mu') (primitiveChainWeight z)
      (primitiveChainWeight_nonneg z)
  have hpermBound :
      paperSum (M := 2 * n) (leafMultiplicity mu')
          (primitiveChainWeight z) ≤
        permSumRHS C n t Nm mu' :=
    hperm.2 n M t Nm mu' z hn ht hroot
      htotal heven hadm
  rw [← hlen] at hpermBound
  refine ⟨n, hn, hsourceWeight.trans ?_⟩
  exact
    mul_le_mul_of_nonneg_left
      (himage.trans (hpaper.trans hpermBound))
      (by positivity)

end

end Anderson4D
