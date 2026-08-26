import Anderson4D.Combinatorics.Pairing
import Anderson4D.Combinatorics.AcrossPairing

/-!
# Primitive across pairings and the word condition in paper (5.11)(c)

An across pairing `κ : A ≃ Aᶜ` determines a fixed-point-free involution of
all positions: use `κ` on `A` and `κ.symm` on its complement.  This file
connects that representation to `PartialPairing`, transfers primitivity to
the word-level leaf-block condition in (5.11)(c), and records the corresponding
filtered form of the factorial estimate (5.10).
-/

namespace Anderson4D

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}

namespace PartialPairing

/-- A pairing crosses the cut `A | Aᶜ` when every position is sent to the
opposite side. -/
def Crosses (κ : PartialPairing (Fin m)) (A : Finset (Fin m)) : Prop :=
  ∀ i, κ i ∈ A ↔ i ∉ A

instance (κ : PartialPairing (Fin m)) (A : Finset (Fin m)) :
    Decidable (κ.Crosses A) :=
  inferInstanceAs (Decidable (∀ i, κ i ∈ A ↔ i ∉ A))

/-- A partial pairing respects a word when paired positions carry the same
letter. -/
def RespectsWord (κ : PartialPairing (Fin m)) (w : Fin m → α) : Prop :=
  ∀ i, w i = w (κ i)

instance (κ : PartialPairing (Fin m)) (w : Fin m → α) :
    Decidable (κ.RespectsWord w) :=
  inferInstanceAs (Decidable (∀ i, w i = w (κ i)))

/-- Crossing a cut rules out fixed points. -/
theorem Crosses.isFull {κ : PartialPairing (Fin m)} {A : Finset (Fin m)}
    (hκ : κ.Crosses A) : κ.IsFull := by
  intro i hii
  by_cases hi : i ∈ A
  · have hκi : κ i ∈ A := by simpa [hii] using hi
    exact (hκ i).mp hκi hi
  · have hκi : κ i ∈ A := (hκ i).mpr hi
    exact hi (by simpa [hii] using hκi)

end PartialPairing

/-- The underlying map of the full involution associated with an across
pairing. -/
def acrossMap (A : Finset (Fin m)) (κ : AcrossPairing A) (i : Fin m) : Fin m :=
  if hi : i ∈ A then
    (κ ⟨i, hi⟩).1
  else
    (κ.symm ⟨i, Finset.mem_compl.mpr hi⟩).1

theorem acrossMap_involutive (A : Finset (Fin m)) (κ : AcrossPairing A) :
    Function.Involutive (acrossMap A κ) := by
  intro i
  by_cases hi : i ∈ A
  · have hmap : acrossMap A κ i = (κ ⟨i, hi⟩).1 := by
      simp [acrossMap, hi]
    rw [hmap]
    have hout : (κ ⟨i, hi⟩).1 ∉ A :=
      Finset.mem_compl.mp (κ ⟨i, hi⟩).2
    rw [acrossMap, dif_neg hout]
    exact congrArg Subtype.val (κ.symm_apply_apply ⟨i, hi⟩)
  · have hmap :
        acrossMap A κ i =
          (κ.symm ⟨i, Finset.mem_compl.mpr hi⟩).1 := by
      simp [acrossMap, hi]
    rw [hmap]
    have hin : (κ.symm ⟨i, Finset.mem_compl.mpr hi⟩).1 ∈ A :=
      (κ.symm ⟨i, Finset.mem_compl.mpr hi⟩).2
    rw [acrossMap, dif_pos hin]
    exact congrArg Subtype.val
      (κ.apply_symm_apply ⟨i, Finset.mem_compl.mpr hi⟩)

/-- Extend an across pairing to the full involution that uses `κ` on `A` and
`κ.symm` on `Aᶜ`. -/
def acrossToPartialPairing (A : Finset (Fin m)) (κ : AcrossPairing A) :
    PartialPairing (Fin m) :=
  ⟨acrossMap A κ, acrossMap_involutive A κ⟩

@[simp]
theorem acrossToPartialPairing_apply_mem (A : Finset (Fin m))
    (κ : AcrossPairing A) {i : Fin m} (hi : i ∈ A) :
    acrossToPartialPairing A κ i = (κ ⟨i, hi⟩).1 := by
  simp [acrossToPartialPairing, acrossMap, hi]

@[simp]
theorem acrossToPartialPairing_apply_notMem (A : Finset (Fin m))
    (κ : AcrossPairing A) {i : Fin m} (hi : i ∉ A) :
    acrossToPartialPairing A κ i =
      (κ.symm ⟨i, Finset.mem_compl.mpr hi⟩).1 := by
  simp [acrossToPartialPairing, acrossMap, hi]

/-- The extended involution crosses the prescribed cut. -/
theorem acrossToPartialPairing_crosses (A : Finset (Fin m))
    (κ : AcrossPairing A) :
    (acrossToPartialPairing A κ).Crosses A := by
  intro i
  by_cases hi : i ∈ A
  · rw [acrossToPartialPairing_apply_mem A κ hi]
    have hout : (κ ⟨i, hi⟩).1 ∉ A :=
      Finset.mem_compl.mp (κ ⟨i, hi⟩).2
    simp [hout, hi]
  · rw [acrossToPartialPairing_apply_notMem A κ hi]
    have hin : (κ.symm ⟨i, Finset.mem_compl.mpr hi⟩).1 ∈ A :=
      (κ.symm ⟨i, Finset.mem_compl.mpr hi⟩).2
    simp [hin, hi]

/-- In particular, the extended involution is a full pairing. -/
theorem acrossToPartialPairing_isFull (A : Finset (Fin m))
    (κ : AcrossPairing A) :
    (acrossToPartialPairing A κ).IsFull :=
  (acrossToPartialPairing_crosses A κ).isFull

omit [Fintype α] [DecidableEq α] in
/-- Compatibility with a word is unchanged by extending an across pairing to
the corresponding full involution. -/
theorem acrossToPartialPairing_respectsWord_iff (A : Finset (Fin m))
    (w : Fin m → α) (κ : AcrossPairing A) :
    (acrossToPartialPairing A κ).RespectsWord w ↔ RespectsWord A w κ := by
  constructor
  · intro h j
    simpa [acrossToPartialPairing_apply_mem A κ j.2] using h j.1
  · intro h i
    by_cases hi : i ∈ A
    · simpa [acrossToPartialPairing_apply_mem A κ hi] using h ⟨i, hi⟩
    · have hj := h (κ.symm ⟨i, Finset.mem_compl.mpr hi⟩)
      simpa [acrossToPartialPairing_apply_notMem A κ hi] using hj.symm

/-- Primitivity of an across pairing means primitivity of its associated full
partial pairing. -/
def IsPrimitiveAcross (A : Finset (Fin m)) (κ : AcrossPairing A) : Prop :=
  IsPrimitive (acrossToPartialPairing A κ)

instance (A : Finset (Fin m)) : DecidablePred (IsPrimitiveAcross A) :=
  fun κ => inferInstanceAs (Decidable (IsPrimitive (acrossToPartialPairing A κ)))

/-- All positions whose letters lie in `S`. -/
def letterPositions (w : Fin m → α) (S : Finset α) : Finset (Fin m) :=
  Finset.univ.filter fun i => w i ∈ S

omit [Fintype α] in
@[simp]
theorem mem_letterPositions {w : Fin m → α} {S : Finset α} {i : Fin m} :
    i ∈ letterPositions w S ↔ w i ∈ S := by
  simp [letterPositions]

/-- **Paper (5.11)(c).**  The positions occupied by any nonempty proper
subset of the letters cannot form a proper interval. -/
def NoProperLeafBlock (w : Fin m → α) : Prop :=
  ∀ S : Finset α, S.Nonempty → S ⊂ Finset.univ →
    ∀ a b : Fin m, a ≤ b → letterPositions w S = Finset.Icc a b →
      Finset.Icc a b = Finset.univ

instance (w : Fin m → α) : Decidable (NoProperLeafBlock w) :=
  inferInstanceAs
    (Decidable (∀ S : Finset α, S.Nonempty → S ⊂ Finset.univ →
      ∀ a b : Fin m, a ≤ b → letterPositions w S = Finset.Icc a b →
        Finset.Icc a b = Finset.univ))

omit [Fintype α] in
/-- Every union of word fibers is fully paired when a full pairing respects
the word. -/
theorem isFullyPairedOn_letterPositions {κ : PartialPairing (Fin m)}
    {w : Fin m → α} (hfull : κ.IsFull) (hword : κ.RespectsWord w)
    (S : Finset α) :
    IsFullyPairedOn κ (letterPositions w S) := by
  constructor
  · intro i _
    exact hfull i
  · intro i hi
    rw [mem_letterPositions] at hi ⊢
    simpa [hword i] using hi

/-- A primitive full pairing respecting a word forces (5.11)(c). -/
theorem noProperLeafBlock_of_primitive_full_respectsWord
    {κ : PartialPairing (Fin m)} {w : Fin m → α}
    (hprimitive : IsPrimitive κ) (hfull : κ.IsFull)
    (hword : κ.RespectsWord w) :
    NoProperLeafBlock w := by
  intro S _ _ a b hab hpositions
  apply hprimitive a b hab
  rw [← hpositions]
  exact isFullyPairedOn_letterPositions hfull hword S

/-- Primitive compatible across pairings imply the word restriction
in paper (5.11)(c). -/
theorem noProperLeafBlock_of_primitive_across
    {A : Finset (Fin m)} {w : Fin m → α} {κ : AcrossPairing A}
    (hprimitive : IsPrimitiveAcross A κ)
    (hword : RespectsWord A w κ) :
    NoProperLeafBlock w :=
  noProperLeafBlock_of_primitive_full_respectsWord hprimitive
    (acrossToPartialPairing_isFull A κ)
    ((acrossToPartialPairing_respectsWord_iff A w κ).mpr hword)

/-- Compatible across pairings whose associated full pairing is primitive. -/
def primitiveCompatibleAcrossPairings (A : Finset (Fin m)) (w : Fin m → α) :
    Finset (AcrossPairing A) :=
  (compatibleAcrossPairings A w).filter (IsPrimitiveAcross A)

omit [Fintype α] in
@[simp]
theorem mem_primitiveCompatibleAcrossPairings
    {A : Finset (Fin m)} {w : Fin m → α} {κ : AcrossPairing A} :
    κ ∈ primitiveCompatibleAcrossPairings A w ↔
      RespectsWord A w κ ∧ IsPrimitiveAcross A κ := by
  simp [primitiveCompatibleAcrossPairings, and_comm]

/-- A word violating (5.11)(c) admits no primitive compatible across
pairing. -/
theorem primitiveCompatibleAcrossPairings_eq_empty_of_not_noProperLeafBlock
    {A : Finset (Fin m)} {w : Fin m → α}
    (hw : ¬NoProperLeafBlock w) :
    primitiveCompatibleAcrossPairings A w = ∅ := by
  ext κ
  simp only [Finset.notMem_empty, iff_false]
  intro hκ
  obtain ⟨hword, hprimitive⟩ :=
    mem_primitiveCompatibleAcrossPairings.mp hκ
  exact hw (noProperLeafBlock_of_primitive_across hprimitive hword)

/-- The paired word sum restricted to primitive full pairings. -/
def primitivePairedWordSum (mult : α → ℕ) (A : Finset (Fin m))
    (F : (Fin m → α) → ℝ) : ℝ :=
  ∑ w ∈ validWords mult,
    ((primitiveCompatibleAcrossPairings A w).card : ℝ) * F w

/-- Word-level factorial estimate for primitive pairings, with the induced
(5.11)(c) word restriction retained on the right. -/
theorem primitivePairedWordSum_le_halfFactorial_mul_wordSumFiltered
    (mult : α → ℕ) (A : Finset (Fin m)) (F : (Fin m → α) → ℝ)
    (hF : ∀ w, 0 ≤ F w) :
    primitivePairedWordSum mult A F ≤
      (∏ a : α, ((mult a / 2).factorial : ℝ)) *
        wordSumFiltered mult NoProperLeafBlock F := by
  classical
  have hrestrict :
      primitivePairedWordSum mult A F =
        ∑ w ∈ (validWords mult).filter NoProperLeafBlock,
          ((primitiveCompatibleAcrossPairings A w).card : ℝ) * F w := by
    unfold primitivePairedWordSum
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro w hwvalid hwfilter
    have hnot : ¬NoProperLeafBlock w := by
      intro hproper
      exact hwfilter (Finset.mem_filter.mpr ⟨hwvalid, hproper⟩)
    rw [primitiveCompatibleAcrossPairings_eq_empty_of_not_noProperLeafBlock hnot]
    simp
  rw [hrestrict]
  unfold wordSumFiltered
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  have hwvalid : w ∈ validWords mult := (Finset.mem_filter.mp hw).1
  have hsubset :
      primitiveCompatibleAcrossPairings A w ⊆ compatibleAcrossPairings A w :=
    Finset.filter_subset _ _
  have hcardNat :
      (primitiveCompatibleAcrossPairings A w).card ≤
        ∏ a : α, (mult a / 2).factorial :=
    (Finset.card_le_card hsubset).trans
      (card_compatibleAcrossPairings_le A mult hwvalid)
  have hcard :
      ((primitiveCompatibleAcrossPairings A w).card : ℝ) ≤
        ∏ a : α, ((mult a / 2).factorial : ℝ) := by
    simpa only [Nat.cast_prod] using
      (Nat.cast_le.mpr hcardNat :
        ((primitiveCompatibleAcrossPairings A w).card : ℝ) ≤
          ((∏ a : α, (mult a / 2).factorial : ℕ) : ℝ))
  exact mul_le_mul_of_nonneg_right hcard (hF w)

/-- **Filtered (5.10).**  The exact factorial normalization for primitive
pairings, with the word condition (5.11)(c) exposed through
`paperSumFiltered`. -/
theorem primitivePairedWordSum_le_paperSumFiltered
    (mult : α → ℕ) (A : Finset (Fin m)) (F : (Fin m → α) → ℝ)
    (hF : ∀ w, 0 ≤ F w) :
    primitivePairedWordSum mult A F ≤
      (∏ a : α,
        ((mult a / 2).factorial : ℝ) / ((mult a).factorial : ℝ)) *
        paperSumFiltered mult NoProperLeafBlock F := by
  calc
    primitivePairedWordSum mult A F ≤
        (∏ a : α, ((mult a / 2).factorial : ℝ)) *
          wordSumFiltered mult NoProperLeafBlock F :=
      primitivePairedWordSum_le_halfFactorial_mul_wordSumFiltered
        mult A F hF
    _ = (∏ a : α,
        ((mult a / 2).factorial : ℝ) / ((mult a).factorial : ℝ)) *
        paperSumFiltered mult NoProperLeafBlock F := by
      unfold paperSumFiltered
      rw [← mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro a _
      exact (div_mul_cancel₀ _ (by positivity)).symm

end Anderson4D
