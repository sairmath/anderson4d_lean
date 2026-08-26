import Anderson4D.Probability.ComplexWickRegroup
import Anderson4D.Probability.PartialPairingWick

/-!
# Full partial pairings and the recursive Wick sum

The paper writes Wick limits as a sum over full `PartialPairing`s, whereas
the finite multilinearity API uses the head-partner recursion
`finWickPairing`.  This file proves that the two presentations agree, for
an arbitrary commutative semiring of edge weights.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace PartialPairing

/-- Product of edge weights, selecting the lower endpoint of every
two-cycle by an explicit strict relation. -/
def covarianceProductBy
    {α ι R : Type*} [Fintype α] [DecidableEq α]
    (lt : α → α → Prop) [DecidableRel lt]
    [CommMonoid R]
    (C : ι → ι → R) (v : α → ι)
    (κ : PartialPairing α) : R :=
  ∏ i ∈ κ.representativesBy lt, C (v i) (v (κ i))

/-- Sum of covariance products over full pairings, with representatives
selected by an explicit strict relation. -/
def fullCovarianceSumBy
    {α ι R : Type*} [Fintype α] [DecidableEq α]
    (lt : α → α → Prop) [DecidableRel lt]
    [CommSemiring R]
    (C : ι → ι → R) (v : α → ι) : R :=
  ∑ κ : PartialPairing α,
    if κ.IsFull then covarianceProductBy lt C v κ else 0

/-- The standard linearly ordered presentation of the full-pairing
covariance sum. -/
def fullCovarianceSum
    {α ι R : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    [CommSemiring R]
    (C : ι → ι → R) (v : α → ι) : R :=
  fullCovarianceSumBy (· < ·) C v

/-- Filtered-finset presentation used verbatim by Proposition 3.6. -/
theorem fullCovarianceSum_eq_filter_sum
    {α ι R : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    [CommSemiring R]
    (C : ι → ι → R) (v : α → ι) :
    fullCovarianceSum C v =
      ∑ κ ∈ Finset.univ.filter
          (fun κ : PartialPairing α => κ.IsFull),
        ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
          C (v i) (v (κ i)) := by
  classical
  simp only [fullCovarianceSum, fullCovarianceSumBy,
    covarianceProductBy, representativesBy]
  rw [Finset.sum_filter]

theorem covarianceProductBy_congr
    {α β ι R : Type*}
    [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ltα : α → α → Prop) [DecidableRel ltα]
    (ltβ : β → β → Prop) [DecidableRel ltβ]
    [CommMonoid R]
    (e : α ≃ β)
    (hlt : ∀ i j, ltβ (e i) (e j) ↔ ltα i j)
    (C : ι → ι → R) (v : β → ι)
    (κ : PartialPairing α) :
    covarianceProductBy ltβ C v (PartialPairing.congr e κ) =
      covarianceProductBy ltα C (v ∘ e) κ := by
  classical
  unfold covarianceProductBy
  rw [representativesBy_congr ltα ltβ e hlt κ,
    Finset.prod_image e.injective.injOn]
  simp only [congr_apply_apply, e.symm_apply_apply,
    Function.comp_apply]

theorem isFull_congr
    {α β : Type*} (e : α ≃ β) (κ : PartialPairing α) :
    (PartialPairing.congr e κ).IsFull ↔ κ.IsFull := by
  constructor
  · intro h i hi
    have := h (e i)
    rw [congr_apply_apply, e.symm_apply_apply] at this
    exact this (congrArg e hi)
  · intro h j hj
    have := h (e.symm j)
    change e (κ (e.symm j)) = j at hj
    apply this
    apply e.injective
    simpa only [e.apply_symm_apply] using hj

theorem fullCovarianceSumBy_congr
    {α β ι R : Type*}
    [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ltα : α → α → Prop) [DecidableRel ltα]
    (ltβ : β → β → Prop) [DecidableRel ltβ]
    [CommSemiring R]
    (e : α ≃ β)
    (hlt : ∀ i j, ltβ (e i) (e j) ↔ ltα i j)
    (C : ι → ι → R) (v : β → ι) :
    fullCovarianceSumBy ltβ C v =
      fullCovarianceSumBy ltα C (v ∘ e) := by
  classical
  unfold fullCovarianceSumBy
  rw [← (PartialPairing.congr e).sum_comp
    (fun κ =>
      if κ.IsFull then covarianceProductBy ltβ C v κ else 0)]
  apply Fintype.sum_congr
  intro κ
  rw [if_congr (isFull_congr e κ) rfl rfl]
  split_ifs
  · exact covarianceProductBy_congr ltα ltβ e hlt C v κ
  · rfl

theorem isFull_optionFixed
    {α : Type*} [DecidableEq α] (κ : PartialPairing α) :
    ¬(optionFixed κ).IsFull := by
  intro h
  exact h none (optionFixed_none κ)

theorem isFull_optionPaired
    {α : Type*} [DecidableEq α] (j : α)
    (κ : PartialPairing {i : α // i ≠ j}) :
    (optionPaired j κ).IsFull ↔ κ.IsFull := by
  constructor
  · intro h i hi
    have hne := h (some i.1)
    rw [optionPaired_some_ne j κ i.1 i.2] at hne
    apply hne
    exact congrArg some (congrArg Subtype.val hi)
  · intro h o
    cases o with
    | none =>
        simp
    | some i =>
        by_cases hi : i = j
        · subst i
          simp
        · rw [optionPaired_some_ne j κ i hi]
          intro heq
          apply h ⟨i, hi⟩
          apply Subtype.ext
          exact Option.some.inj heq

theorem covarianceProductBy_optionPaired
    {α ι R : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    [CommMonoid R]
    (C : ι → ι → R) (x : ι) (v : α → ι)
    (j : α) (κ : PartialPairing {i : α // i ≠ j}) :
    covarianceProductBy optionHeadLT C
        (fun o => o.elim x v) (optionPaired j κ) =
      C x (v j) *
        covarianceProductBy (· < ·) C
          (fun i : {i : α // i ≠ j} => v i.1) κ := by
  classical
  unfold covarianceProductBy
  rw [representatives_optionPaired]
  have hnone :
      none ∉ κ.representatives.image (fun i => some i.1) := by
    simp
  rw [Finset.prod_insert hnone]
  rw [Finset.prod_image (fun a _ha b _hb hab =>
    Subtype.ext (Option.some.inj hab))]
  simp only [Option.elim_none, optionPaired_none, Option.elim_some]
  apply congrArg (C x (v j) * ·)
  apply Finset.prod_congr rfl
  intro i hi
  rw [optionPaired_some_ne j κ i.1 i.2]
  simp only [Option.elim_some]

/-- Head-partner recurrence for the full partial-pairing sum. -/
theorem fullCovarianceSumBy_option
    {α ι R : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    [CommSemiring R]
    (C : ι → ι → R) (x : ι) (v : α → ι) :
    fullCovarianceSumBy optionHeadLT C (fun o => o.elim x v) =
      ∑ j : α,
        C x (v j) *
          fullCovarianceSum C
            (fun i : {i : α // i ≠ j} => v i.1) := by
  classical
  unfold fullCovarianceSumBy
  rw [← optionHeadEquiv.symm.sum_comp
    (fun κ =>
      if κ.IsFull then
        covarianceProductBy optionHeadLT C
          (fun o => o.elim x v) κ
      else 0)]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [optionHeadEquiv_symm_inl, optionHeadEquiv_symm_inr,
    isFull_optionFixed, ↓reduceIte, Finset.sum_const_zero,
    zero_add, isFull_optionPaired]
  apply Fintype.sum_congr
  intro j
  simp_rw [covarianceProductBy_optionPaired C x v j]
  simp only [fullCovarianceSum, fullCovarianceSumBy]
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro κ
  by_cases hκ : κ.IsFull <;> simp [hκ]

/-- Transporting labels through an order isomorphism does not change a
full-pairing covariance sum. -/
theorem fullCovarianceSum_orderIso
    {α β ι R : Type*}
    [Fintype α] [DecidableEq α] [LinearOrder α]
    [Fintype β] [DecidableEq β] [LinearOrder β]
    [CommSemiring R]
    (e : α ≃o β) (C : ι → ι → R) (v : β → ι) :
    fullCovarianceSum C v =
      fullCovarianceSum C (v ∘ e) := by
  exact fullCovarianceSumBy_congr
    (· < ·) (· < ·) e.toEquiv (fun i j => e.lt_iff_lt) C v

/-- Full-pairing sum on `Fin 0`. -/
@[simp]
theorem fullCovarianceSum_fin_zero
    {ι R : Type*} [CommSemiring R]
    (C : ι → ι → R) (v : Fin 0 → ι) :
    fullCovarianceSum C v = 1 := by
  letI : Unique (PartialPairing (Fin 0)) :=
    { default := PartialPairing.id
      uniq := fun κ => by
        apply PartialPairing.ext
        exact fun i => Fin.elim0 i }
  simp [fullCovarianceSum, fullCovarianceSumBy,
    covarianceProductBy, representativesBy,
    PartialPairing.pairSupport, PartialPairing.IsFull]

/-- There is no full pairing of a singleton. -/
@[simp]
theorem fullCovarianceSum_fin_one
    {ι R : Type*} [CommSemiring R]
    (C : ι → ι → R) (v : Fin 1 → ι) :
    fullCovarianceSum C v = 0 := by
  unfold fullCovarianceSum fullCovarianceSumBy
  apply Fintype.sum_eq_zero
  intro κ
  split_ifs with hκ
  · obtain ⟨q, hq⟩ := hκ.even_card
    simp only [Fintype.card_fin] at hq
    omega
  · rfl

/-- Removing the head and its selected partner gives the same
head-partner recurrence as `finWickPairing`. -/
theorem fullCovarianceSum_fin_add_two
    {ι R : Type*} [CommSemiring R]
    (C : ι → ι → R) (n : ℕ) (v : Fin (n + 2) → ι) :
    fullCovarianceSum C v =
      ∑ j : Fin (n + 1),
        C (v 0) (v j.succ) *
          fullCovarianceSum C
            (fun i => v (j.succAbove i).succ) := by
  let eHead : Option (Fin (n + 1)) ≃ Fin (n + 2) :=
    (finSuccEquiv (n + 1)).symm
  have htransport :
      fullCovarianceSum C v =
        fullCovarianceSumBy optionHeadLT C (v ∘ eHead) := by
    exact fullCovarianceSumBy_congr
      optionHeadLT (· < ·) eHead
        (finSuccEquiv_symm_lt_iff (n + 1)) C v
  have hlabel :
      v ∘ eHead =
        fun o => o.elim (v 0) (fun i => v i.succ) := by
    funext o
    cases o <;> simp [eHead, Function.comp_apply]
  rw [htransport, hlabel, fullCovarianceSumBy_option]
  apply Fintype.sum_congr
  intro j
  let eTail : Fin n ≃o {i : Fin (n + 1) // i ≠ j} :=
    finSuccAboveOrderIso j
  rw [fullCovarianceSum_orderIso eTail C
    (fun i : {i : Fin (n + 1) // i ≠ j} => v i.1.succ)]
  rfl

/-- The paper's explicit sum over full involutions is exactly the
recursive Wick-pairing sum. -/
theorem fullCovarianceSum_fin_eq_finWickPairing
    {ι R : Type*} [CommSemiring R]
    (C : ι → ι → R) :
    ∀ (n : ℕ) (v : Fin n → ι),
      fullCovarianceSum C v = finWickPairing C n v := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      intro v
      simp
  | one =>
      intro v
      simp
  | more n ih _ihSucc =>
      intro v
      rw [fullCovarianceSum_fin_add_two, finWickPairing_add_two]
      apply Fintype.sum_congr
      intro j
      rw [ih]

end PartialPairing

/-! ## Constant covariance -/

/-- A recursive full-pairing sum with constant covariance vanishes in
odd degree. -/
theorem finWickPairing_const_odd
    {α R : Type*} [CommSemiring R] (c : R) :
    ∀ (q : ℕ) (v : Fin (2 * q + 1) → α),
      finWickPairing (fun _ _ => c) (2 * q + 1) v = 0 := by
  intro q
  induction q with
  | zero =>
      intro v
      simp
  | succ q ih =>
      intro v
      simp only [Nat.mul_succ] at v ⊢
      rw [finWickPairing_add_two]
      apply Finset.sum_eq_zero
      intro j hj
      rw [ih]
      simp

/-- A recursive full-pairing sum with constant covariance is the
pairing count times the corresponding covariance power. -/
theorem finWickPairing_const_even
    {α R : Type*} [CommSemiring R] (c : R) :
    ∀ (q : ℕ) (v : Fin (2 * q) → α),
      finWickPairing (fun _ _ => c) (2 * q) v =
        (gaussianPairingCount q : R) * c ^ q := by
  intro q
  induction q with
  | zero =>
      intro v
      simp [gaussianPairingCount]
  | succ q ih =>
      intro v
      simp only [Nat.mul_succ] at v ⊢
      rw [finWickPairing_add_two]
      simp_rw [ih]
      simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, gaussianPairingCount]
      push_cast
      rw [pow_succ]
      ac_rfl

end

end Anderson4D
