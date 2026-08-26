import Anderson4D.PermSum.Words

/-!
# Across-half pairings and the factorial bound in paper (5.10)

This file isolates the finite combinatorics used in the master decomposition.
For a fixed half `A ⊆ Fin m`, an across pairing is a bijection from `A` to its
complement.  A pairing respects a word when paired positions carry the same
letter.  Restricting such a pairing to each letter fiber gives an injective map
into a family of fiberwise equivalences.  Consequently the number of compatible
pairings is at most

`∏ a, (mult a / 2)!`.

Together with the definitional factorial ledger `paperSum`, this is exactly the
factor in (5.10).
-/

namespace Anderson4D

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}

/-- A pairing across a fixed half `A`: a bijection from `A` to its complement. -/
abbrev AcrossPairing (A : Finset (Fin m)) := (↥A ≃ ↥(Aᶜ))

/-- An across pairing respects `w` when paired positions carry the same letter. -/
def RespectsWord (A : Finset (Fin m)) (w : Fin m → α) (κ : AcrossPairing A) : Prop :=
  ∀ j : ↥A, w j.1 = w (κ j).1

instance (A : Finset (Fin m)) (w : Fin m → α) :
    DecidablePred (RespectsWord A w) :=
  fun κ => inferInstanceAs (Decidable (∀ j : ↥A, w j.1 = w (κ j).1))

/-- The finite set of across pairings compatible with a word. -/
def compatibleAcrossPairings (A : Finset (Fin m)) (w : Fin m → α) :
    Finset (AcrossPairing A) :=
  Finset.univ.filter (RespectsWord A w)

omit [Fintype α] in
@[simp] theorem mem_compatibleAcrossPairings {A : Finset (Fin m)}
    {w : Fin m → α} {κ : AcrossPairing A} :
    κ ∈ compatibleAcrossPairings A w ↔ RespectsWord A w κ := by
  simp [compatibleAcrossPairings]

/-- Positions in `A` carrying the letter `a`. -/
abbrev leftFiber (A : Finset (Fin m)) (w : Fin m → α) (a : α) :=
  ↥(A.filter fun j => w j = a)

/-- Positions outside `A` carrying the letter `a`. -/
abbrev rightFiber (A : Finset (Fin m)) (w : Fin m → α) (a : α) :=
  ↥(Aᶜ.filter fun j => w j = a)

/-- A compatible across pairing restricts to an equivalence on every letter fiber. -/
def restrictFiberEquiv (A : Finset (Fin m)) (w : Fin m → α)
    (κ : AcrossPairing A) (hκ : RespectsWord A w κ) (a : α) :
    leftFiber A w a ≃ rightFiber A w a where
  toFun j :=
    ⟨(κ ⟨j.1, (Finset.mem_filter.mp j.2).1⟩).1,
      Finset.mem_filter.mpr
        ⟨(κ ⟨j.1, (Finset.mem_filter.mp j.2).1⟩).2,
          (hκ ⟨j.1, (Finset.mem_filter.mp j.2).1⟩).symm.trans
            (Finset.mem_filter.mp j.2).2⟩⟩
  invFun j :=
    ⟨(κ.symm ⟨j.1, (Finset.mem_filter.mp j.2).1⟩).1,
      Finset.mem_filter.mpr
        ⟨(κ.symm ⟨j.1, (Finset.mem_filter.mp j.2).1⟩).2,
          (hκ (κ.symm ⟨j.1, (Finset.mem_filter.mp j.2).1⟩)).trans
            (by simpa using (Finset.mem_filter.mp j.2).2)⟩⟩
  left_inv j := by
    apply Subtype.ext
    change
      (κ.symm (κ ⟨j.1, (Finset.mem_filter.mp j.2).1⟩)).1 = j.1
    exact congrArg Subtype.val
      (κ.symm_apply_apply ⟨j.1, (Finset.mem_filter.mp j.2).1⟩)
  right_inv j := by
    apply Subtype.ext
    change
      (κ (κ.symm ⟨j.1, (Finset.mem_filter.mp j.2).1⟩)).1 = j.1
    exact congrArg Subtype.val
      (κ.apply_symm_apply ⟨j.1, (Finset.mem_filter.mp j.2).1⟩)

/-- Compatible pairings inject into the family of their letter-fiber restrictions. -/
def compatibleToFiberEquivs (A : Finset (Fin m)) (w : Fin m → α) :
    {κ : AcrossPairing A // RespectsWord A w κ} →
      ∀ a : α, leftFiber A w a ≃ rightFiber A w a :=
  fun κ a => restrictFiberEquiv A w κ.1 κ.2 a

omit [Fintype α] in
theorem compatibleToFiberEquivs_injective (A : Finset (Fin m)) (w : Fin m → α) :
    Function.Injective (compatibleToFiberEquivs A w) := by
  intro κ κ' h
  apply Subtype.ext
  apply Equiv.ext
  intro j
  have ha := congrFun h (w j.1)
  have hj := congrArg
    (fun e : leftFiber A w (w j.1) ≃ rightFiber A w (w j.1) =>
      e ⟨j.1, Finset.mem_filter.mpr ⟨j.2, rfl⟩⟩) ha
  apply Subtype.ext
  change (κ.1 j).1 = (κ'.1 j).1
  simpa [compatibleToFiberEquivs, restrictFiberEquiv] using congrArg Subtype.val hj

omit [Fintype α] in
theorem card_leftFiber (A : Finset (Fin m)) (w : Fin m → α) (a : α) :
    Fintype.card (leftFiber A w a) = (A.filter fun j => w j = a).card := by
  exact Fintype.card_coe _

omit [Fintype α] in
theorem card_rightFiber (A : Finset (Fin m)) (w : Fin m → α) (a : α) :
    Fintype.card (rightFiber A w a) = (Aᶜ.filter fun j => w j = a).card := by
  exact Fintype.card_coe _

omit [Fintype α] in
theorem card_leftFiber_add_card_rightFiber (A : Finset (Fin m))
    (w : Fin m → α) (a : α) :
    Fintype.card (leftFiber A w a) + Fintype.card (rightFiber A w a) =
      (Finset.univ.filter fun j => w j = a).card := by
  rw [card_leftFiber, card_rightFiber]
  classical
  have hdisj :
      Disjoint (A.filter fun j => w j = a) (Aᶜ.filter fun j => w j = a) := by
    rw [Finset.disjoint_left]
    intro j hjA hjAc
    exact (Finset.mem_compl.mp (Finset.mem_filter.mp hjAc).1)
      (Finset.mem_filter.mp hjA).1
  rw [← Finset.card_union_of_disjoint hdisj]
  congr
  ext j
  by_cases hj : j ∈ A <;> simp [hj]

/-- If a valid word admits a compatible across pairing, every prescribed
letter multiplicity is even.  This is the multiplicity clause of paper
Lemma 5.5. -/
theorem even_mult_of_compatibleAcrossPairing (A : Finset (Fin m))
    (mult : α → ℕ) {w : Fin m → α} (hw : w ∈ validWords mult)
    (κ : AcrossPairing A) (hκ : RespectsWord A w κ) :
    ∀ a, Even (mult a) := by
  intro a
  have heq :
      Fintype.card (leftFiber A w a) =
        Fintype.card (rightFiber A w a) :=
    Fintype.card_congr (restrictFiberEquiv A w κ hκ a)
  have hsum := card_leftFiber_add_card_rightFiber A w a
  have htotal := (Finset.mem_filter.mp hw).2 a
  refine ⟨Fintype.card (leftFiber A w a), ?_⟩
  omega

/-- Fiber-counting bound: a compatible pairing has at most
`∏ a, (mult a / 2)!` possibilities. -/
theorem card_compatibleAcrossPairings_le (A : Finset (Fin m))
    (mult : α → ℕ) {w : Fin m → α} (hw : w ∈ validWords mult) :
    (compatibleAcrossPairings A w).card ≤
      ∏ a : α, (mult a / 2).factorial := by
  by_cases hne : (compatibleAcrossPairings A w).Nonempty
  · obtain ⟨κ, hκmem⟩ := hne
    have hκ : RespectsWord A w κ := mem_compatibleAcrossPairings.mp hκmem
    have hleft (a : α) :
        Fintype.card (leftFiber A w a) = mult a / 2 := by
      have heq :
          Fintype.card (leftFiber A w a) = Fintype.card (rightFiber A w a) :=
        Fintype.card_congr (restrictFiberEquiv A w κ hκ a)
      have hsum := card_leftFiber_add_card_rightFiber A w a
      have htotal := (Finset.mem_filter.mp hw).2 a
      omega
    have hfamily :
        Fintype.card (∀ a : α, leftFiber A w a ≃ rightFiber A w a) =
          ∏ a : α, (mult a / 2).factorial := by
      rw [Fintype.card_pi]
      apply Finset.prod_congr rfl
      intro a _
      rw [Fintype.card_equiv (restrictFiberEquiv A w κ hκ a), hleft a]
    have hinj :
        Fintype.card {κ : AcrossPairing A // RespectsWord A w κ} ≤
          Fintype.card (∀ a : α, leftFiber A w a ≃ rightFiber A w a) :=
      Fintype.card_le_of_injective (compatibleToFiberEquivs A w)
        (compatibleToFiberEquivs_injective A w)
    rw [hfamily] at hinj
    simpa [compatibleAcrossPairings, Fintype.card_subtype] using hinj
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/-- The left side of paper (5.10): sum over distinct multiset words, weighted
by the number of compatible across-half pairings. -/
def pairedWordSum (mult : α → ℕ) (A : Finset (Fin m))
    (F : (Fin m → α) → ℝ) : ℝ :=
  ∑ w ∈ validWords mult, ((compatibleAcrossPairings A w).card : ℝ) * F w

/-- Word-level form of the factorial estimate underlying paper (5.10). -/
theorem pairedWordSum_le_halfFactorial_mul_wordSum (mult : α → ℕ)
    (A : Finset (Fin m)) (F : (Fin m → α) → ℝ) (hF : ∀ w, 0 ≤ F w) :
    pairedWordSum mult A F ≤
      (∏ a : α, ((mult a / 2).factorial : ℝ)) * wordSum mult F := by
  unfold pairedWordSum wordSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  have hcard :
      ((compatibleAcrossPairings A w).card : ℝ) ≤
        ∏ a : α, ((mult a / 2).factorial : ℝ) := by
    simpa only [Nat.cast_prod] using
      (Nat.cast_le.mpr (card_compatibleAcrossPairings_le A mult hw) :
        ((compatibleAcrossPairings A w).card : ℝ) ≤
          ((∏ a : α, (mult a / 2).factorial : ℕ) : ℝ))
  exact mul_le_mul_of_nonneg_right
    hcard (hF w)

/-- **Paper (5.10), exact factorial normalization.**

The labeled normalization is `paperSum mult F = (∏ a, mult a!) * wordSum mult F`.
The compatible-pairing count cancels it to the printed factor
`∏ a, (mult a / 2)! / mult a!`. -/
theorem pairedWordSum_le_paperSum (mult : α → ℕ) (A : Finset (Fin m))
    (F : (Fin m → α) → ℝ) (hF : ∀ w, 0 ≤ F w) :
    pairedWordSum mult A F ≤
      (∏ a : α, ((mult a / 2).factorial : ℝ) / ((mult a).factorial : ℝ)) *
        paperSum mult F := by
  calc
    pairedWordSum mult A F ≤
        (∏ a : α, ((mult a / 2).factorial : ℝ)) * wordSum mult F :=
      pairedWordSum_le_halfFactorial_mul_wordSum mult A F hF
    _ = (∏ a : α,
        ((mult a / 2).factorial : ℝ) / ((mult a).factorial : ℝ)) *
        paperSum mult F := by
      unfold paperSum
      rw [← mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro a _
      exact (div_mul_cancel₀ _ (by positivity)).symm

end Anderson4D
