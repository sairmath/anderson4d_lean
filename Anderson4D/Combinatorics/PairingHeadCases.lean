import Anderson4D.Combinatorics.PairingExtract
import Anderson4D.Combinatorics.PairingRecursion

/-!
# The three head cases in the proof of Proposition 3.4

The paper indexes a pairing by `[1, m]`.  Here a pairing of `Fin (m + 1)`
uses zero-based indices, so its distinguished new index is `0`, and the
paper prefix `[1, 2q]` is exactly the finset of indices `i < 2q`, whose
last element is `2q - 1`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace PartialPairing

/-- The zero-based prefix corresponding to the paper interval `[1, 2q]`.
The bound `2q ≤ m + 1` is deliberately not built into the definition. -/
def headEvenPrefix (m q : ℕ) : Finset (Fin (m + 1)) :=
  Finset.univ.filter fun i => (i : ℕ) < 2 * q

@[simp]
theorem mem_headEvenPrefix {m q : ℕ} {i : Fin (m + 1)} :
    i ∈ headEvenPrefix m q ↔ (i : ℕ) < 2 * q := by
  simp [headEvenPrefix]

theorem card_headEvenPrefix {m q : ℕ} (hq : 2 * q ≤ m + 1) :
    (headEvenPrefix m q).card = 2 * q := by
  rw [headEvenPrefix, Fin.card_filter_val_lt]
  exact Nat.min_eq_right hq

/-- The endpoint `2q - 1` of the zero-based realization of `[1, 2q]`. -/
def headEvenPrefixLast {m q : ℕ} (hqpos : 1 ≤ q)
    (hq : 2 * q ≤ m + 1) : Fin (m + 1) :=
  ⟨2 * q - 1, by omega⟩

theorem headEvenPrefix_eq_Icc {m q : ℕ} (hqpos : 1 ≤ q)
    (hq : 2 * q ≤ m + 1) :
    headEvenPrefix m q =
      Finset.Icc 0 (headEvenPrefixLast hqpos hq) := by
  ext i
  rw [mem_headEvenPrefix]
  simp only [Finset.mem_Icc, Fin.zero_le, true_and]
  change (i : ℕ) < 2 * q ↔ (i : ℕ) ≤ 2 * q - 1
  omega

/-- A positive even prefix which is fully paired under `κ`. -/
def IsFullyPairedHeadPrefix {m : ℕ}
    (κ : PartialPairing (Fin (m + 1))) (q : ℕ) : Prop :=
  1 ≤ q ∧ 2 * q ≤ m + 1 ∧
    IsFullyPairedOn κ (headEvenPrefix m q)

instance {m : ℕ} (κ : PartialPairing (Fin (m + 1))) :
    DecidablePred (IsFullyPairedHeadPrefix κ) :=
  fun q => decidable_of_iff
    (1 ≤ q ∧ 2 * q ≤ m + 1 ∧
      IsFullyPairedOn κ (headEvenPrefix m q)) Iff.rfl

/-- There is a paper-style fully paired prefix `[1, 2q]`. -/
def HasFullyPairedHeadPrefix {m : ℕ}
    (κ : PartialPairing (Fin (m + 1))) : Prop :=
  ∃ q, IsFullyPairedHeadPrefix κ q

instance {m : ℕ} (κ : PartialPairing (Fin (m + 1))) :
    Decidable (HasFullyPairedHeadPrefix κ) :=
  Classical.dec _

/-- Case (1): the distinguished head index is a single. -/
def HeadIsSingle {m : ℕ}
    (κ : PartialPairing (Fin (m + 1))) : Prop :=
  κ 0 = 0

instance {m : ℕ} (κ : PartialPairing (Fin (m + 1))) :
    Decidable (HeadIsSingle κ) :=
  Classical.dec _

/-- Case (2): the head is paired, but no `[1, 2q]` is fully paired. -/
def HeadPairedNoPrefix {m : ℕ}
    (κ : PartialPairing (Fin (m + 1))) : Prop :=
  κ 0 ≠ 0 ∧ ¬HasFullyPairedHeadPrefix κ

instance {m : ℕ} (κ : PartialPairing (Fin (m + 1))) :
    Decidable (HeadPairedNoPrefix κ) :=
  Classical.dec _

/-- Case (3): the head is paired and some `[1, 2q]` is fully paired. -/
def HeadPairedWithPrefix {m : ℕ}
    (κ : PartialPairing (Fin (m + 1))) : Prop :=
  κ 0 ≠ 0 ∧ HasFullyPairedHeadPrefix κ

instance {m : ℕ} (κ : PartialPairing (Fin (m + 1))) :
    Decidable (HeadPairedWithPrefix κ) :=
  Classical.dec _

theorem head_paired_of_fullyPairedHeadPrefix
    {m q : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (h : IsFullyPairedHeadPrefix κ q) :
    κ 0 ≠ 0 := by
  have hzero : (0 : Fin (m + 1)) ∈ headEvenPrefix m q := by
    simp only [mem_headEvenPrefix, Fin.val_zero]
    have hq : 1 ≤ q := h.1
    omega
  exact h.2.2.ne_of_mem hzero

/-- The least `q` for which the paper prefix `[1, 2q]` is fully paired. -/
def firstFullyPairedHeadQ
    {m : ℕ} (κ : PartialPairing (Fin (m + 1)))
    (h : HasFullyPairedHeadPrefix κ) : ℕ :=
  Nat.find h

theorem firstFullyPairedHeadQ_spec
    {m : ℕ} (κ : PartialPairing (Fin (m + 1)))
    (h : HasFullyPairedHeadPrefix κ) :
    IsFullyPairedHeadPrefix κ (firstFullyPairedHeadQ κ h) :=
  Nat.find_spec h

theorem firstFullyPairedHeadQ_min
    {m : ℕ} (κ : PartialPairing (Fin (m + 1)))
    (h : HasFullyPairedHeadPrefix κ) {r : ℕ}
    (hr : IsFullyPairedHeadPrefix κ r) :
    firstFullyPairedHeadQ κ h ≤ r :=
  Nat.find_min' h hr

/-- Complete data attached to case (3).  The minimality field is the exact
formal counterpart of “choose the smallest `q`” in the proof of (3.16). -/
structure HeadPrefixDecomposition
    {m : ℕ} (κ : PartialPairing (Fin (m + 1))) where
  q : ℕ
  q_pos : 1 ≤ q
  two_mul_le : 2 * q ≤ m + 1
  fullyPaired :
    IsFullyPairedOn κ (headEvenPrefix m q)
  minimal :
    ∀ r, IsFullyPairedHeadPrefix κ r → q ≤ r

/-- The canonical minimal-prefix data of a case-(3) pairing. -/
def headPrefixDecomposition
    {m : ℕ} (κ : PartialPairing (Fin (m + 1)))
    (h : HasFullyPairedHeadPrefix κ) :
    HeadPrefixDecomposition κ :=
  let hs := firstFullyPairedHeadQ_spec κ h
  { q := firstFullyPairedHeadQ κ h
    q_pos := hs.1
    two_mul_le := hs.2.1
    fullyPaired := hs.2.2
    minimal := fun _ hr => firstFullyPairedHeadQ_min κ h hr }

theorem HeadPrefixDecomposition.isFullyPairedHeadPrefix
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d : HeadPrefixDecomposition κ) :
    IsFullyPairedHeadPrefix κ d.q :=
  ⟨d.q_pos, d.two_mul_le, d.fullyPaired⟩

theorem HeadPrefixDecomposition.head_paired
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d : HeadPrefixDecomposition κ) :
    κ 0 ≠ 0 :=
  head_paired_of_fullyPairedHeadPrefix d.isFullyPairedHeadPrefix

theorem HeadPrefixDecomposition.q_unique
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d₁ d₂ : HeadPrefixDecomposition κ) :
    d₁.q = d₂.q :=
  le_antisymm
    (d₁.minimal d₂.q d₂.isFullyPairedHeadPrefix)
    (d₂.minimal d₁.q d₁.isFullyPairedHeadPrefix)

theorem HeadPrefixDecomposition.no_smaller
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d : HeadPrefixDecomposition κ) {r : ℕ} (hr : r < d.q) :
    ¬IsFullyPairedHeadPrefix κ r :=
  fun h => (not_le_of_gt hr) (d.minimal r h)

/-- Restrict an involution to a closed finset. -/
def restrictTo {α : Type*} [DecidableEq α]
    (κ : PartialPairing α) {B : Finset α}
    (hB : ∀ i ∈ B, κ i ∈ B) :
    PartialPairing B where
  toFun i := ⟨κ i.1, hB i.1 i.2⟩
  involutive i := Subtype.ext (κ.apply_apply i.1)

@[simp]
theorem restrictTo_apply_val {α : Type*} [DecidableEq α]
    (κ : PartialPairing α) {B : Finset α}
    (hB : ∀ i ∈ B, κ i ∈ B) (i : B) :
    (restrictTo κ hB i).1 = κ i.1 :=
  rfl

theorem IsFull.congr
    {α β : Type*} {κ : PartialPairing α}
    (hκ : κ.IsFull) (e : α ≃ β) :
    (PartialPairing.congr e κ).IsFull := by
  intro j hj
  apply hκ (e.symm j)
  apply e.injective
  simpa only [PartialPairing.congr_apply_apply,
    e.apply_symm_apply] using hj

/-- Increasing identification of the selected prefix with `Fin (2q)`. -/
def HeadPrefixDecomposition.prefixOrderIso
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d : HeadPrefixDecomposition κ) :
    Fin (2 * d.q) ≃o {i : Fin (m + 1) // i ∈ headEvenPrefix m d.q} :=
  (headEvenPrefix m d.q).orderIsoOfFin
    (card_headEvenPrefix d.two_mul_le)

/-- Restriction of `κ` to its first fully paired prefix, reindexed from
zero through `2q-1`. -/
def HeadPrefixDecomposition.prefixPairing
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d : HeadPrefixDecomposition κ) :
    PartialPairing (Fin (2 * d.q)) :=
  PartialPairing.congr d.prefixOrderIso.symm.toEquiv
    (restrictTo κ d.fullyPaired.2)

theorem HeadPrefixDecomposition.prefixPairing_isFull
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d : HeadPrefixDecomposition κ) :
    d.prefixPairing.IsFull := by
  have hrestrict : (restrictTo κ d.fullyPaired.2).IsFull := by
    intro i hi
    exact d.fullyPaired.ne_of_mem i.2
      (congrArg Subtype.val hi)
  exact hrestrict.congr d.prefixOrderIso.symm.toEquiv

/-- Increasing reindexing of the external remainder.  Its source consists
of the ambient indices `2q, …, m`, i.e. paper indices `2q+1, …, m+1`. -/
def HeadPrefixDecomposition.remainderOrderIso
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d : HeadPrefixDecomposition κ) :
    {i : Fin (m + 1) // i ∉ headEvenPrefix m d.q} ≃o
      Fin (m + 1 - 2 * d.q) :=
  (complOrderIso (headEvenPrefix m d.q)).trans
    (Fin.castOrderIso (by
      rw [card_headEvenPrefix d.two_mul_le]))

/-- The external pairing `σ₂` from case (3), on exactly
`m+1-2q` reindexed positions. -/
def HeadPrefixDecomposition.remainderPairing
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d : HeadPrefixDecomposition κ) :
    PartialPairing (Fin (m + 1 - 2 * d.q)) :=
  PartialPairing.congr d.remainderOrderIso.toEquiv
    (κ.restrictCompl d.fullyPaired.2)

/-- The three cases are represented by disjoint subtypes, yielding a direct
finite-sum reindexing API. -/
def headCasesEquiv (m : ℕ) :
    PartialPairing (Fin (m + 1)) ≃
      {κ : PartialPairing (Fin (m + 1)) // HeadIsSingle κ} ⊕
        ({κ : PartialPairing (Fin (m + 1)) // HeadPairedNoPrefix κ} ⊕
          {κ : PartialPairing (Fin (m + 1)) //
            HeadPairedWithPrefix κ}) where
  toFun κ :=
    if hsingle : HeadIsSingle κ then
      Sum.inl ⟨κ, hsingle⟩
    else if hpref : HasFullyPairedHeadPrefix κ then
      Sum.inr (Sum.inr ⟨κ, hsingle, hpref⟩)
    else
      Sum.inr (Sum.inl ⟨κ, hsingle, hpref⟩)
  invFun
    | Sum.inl κ => κ.1
    | Sum.inr (Sum.inl κ) => κ.1
    | Sum.inr (Sum.inr κ) => κ.1
  left_inv κ := by
    by_cases hsingle : HeadIsSingle κ
    · simp [hsingle]
    · by_cases hpref : HasFullyPairedHeadPrefix κ
      · simp [hsingle, hpref]
      · simp [hsingle, hpref]
  right_inv s := by
    rcases s with κ | κ
    · have hs : HeadIsSingle κ.1 := κ.2
      simp [hs]
    · rcases κ with κ | κ
      · have hns : ¬HeadIsSingle κ.1 := κ.2.1
        have hnp : ¬HasFullyPairedHeadPrefix κ.1 := κ.2.2
        simp [hns, hnp]
      · have hns : ¬HeadIsSingle κ.1 := κ.2.1
        have hp : HasFullyPairedHeadPrefix κ.1 := κ.2.2
        simp [hns, hp]

@[simp]
theorem headCasesEquiv_symm_single {m : ℕ}
    (κ : {κ : PartialPairing (Fin (m + 1)) // HeadIsSingle κ}) :
    (headCasesEquiv m).symm (Sum.inl κ) = κ.1 :=
  rfl

@[simp]
theorem headCasesEquiv_symm_noPrefix {m : ℕ}
    (κ : {κ : PartialPairing (Fin (m + 1)) //
      HeadPairedNoPrefix κ}) :
    (headCasesEquiv m).symm (Sum.inr (Sum.inl κ)) = κ.1 :=
  rfl

@[simp]
theorem headCasesEquiv_symm_withPrefix {m : ℕ}
    (κ : {κ : PartialPairing (Fin (m + 1)) //
      HeadPairedWithPrefix κ}) :
    (headCasesEquiv m).symm (Sum.inr (Sum.inr κ)) = κ.1 :=
  rfl

theorem headCases_complete
    {m : ℕ} (κ : PartialPairing (Fin (m + 1))) :
    HeadIsSingle κ ∨ HeadPairedNoPrefix κ ∨
      HeadPairedWithPrefix κ := by
  by_cases hsingle : HeadIsSingle κ
  · exact Or.inl hsingle
  · by_cases hpref : HasFullyPairedHeadPrefix κ
    · exact Or.inr (Or.inr ⟨hsingle, hpref⟩)
    · exact Or.inr (Or.inl ⟨hsingle, hpref⟩)

theorem headCases_pairwise_disjoint
    {m : ℕ} (κ : PartialPairing (Fin (m + 1))) :
    (¬(HeadIsSingle κ ∧ HeadPairedNoPrefix κ)) ∧
      (¬(HeadIsSingle κ ∧ HeadPairedWithPrefix κ)) ∧
      (¬(HeadPairedNoPrefix κ ∧ HeadPairedWithPrefix κ)) := by
  constructor
  · rintro ⟨hs, hp, -⟩
    exact hp hs
  constructor
  · rintro ⟨hs, hp, -⟩
    exact hp hs
  · rintro ⟨⟨-, hn⟩, ⟨-, hh⟩⟩
    exact hn hh

/-- Reindex any finite sum over pairings into the three cases of the proof
of Proposition 3.4. -/
theorem sum_headCases
    {m : ℕ} {R : Type*} [AddCommMonoid R]
    (f : PartialPairing (Fin (m + 1)) → R) :
    (∑ κ, f κ) =
      (∑ κ : {κ // HeadIsSingle κ}, f κ.1) +
      (∑ κ : {κ // HeadPairedNoPrefix κ}, f κ.1) +
      ∑ κ : {κ // HeadPairedWithPrefix κ}, f κ.1 := by
  rw [← (headCasesEquiv m).symm.sum_comp f]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [headCasesEquiv_symm_single,
    headCasesEquiv_symm_noPrefix, headCasesEquiv_symm_withPrefix]
  abel

end PartialPairing

end

end Anderson4D
