import Anderson4D.Parametrix.Identity

/-!
# Pairing reindexing for Proposition 3.4

This file supplies the finite equivalences behind the creation--contraction
step in Proposition 3.4.  A contraction is indexed by a partial pairing
together with one marked single.  Removing that marked single leaves a
pairing on its complement; adjoining the new head and pairing it with the
marked index is therefore exactly the paired branch of `finHeadEquiv`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace PartialPairing

/-! ## Removing and restoring a marked single -/

/-- Remove a specified fixed point from a partial pairing. -/
def eraseSingle {α : Type*} [DecidableEq α]
    (κ : PartialPairing α) (j : α) (hj : κ j = j) :
    PartialPairing {i : α // i ≠ j} where
  toFun i :=
    ⟨κ i.1, by
      intro h
      apply i.2
      rw [← κ.apply_apply i.1, h, hj]⟩
  involutive i :=
    Subtype.ext (κ.apply_apply i.1)

@[simp]
theorem eraseSingle_apply_val
    {α : Type*} [DecidableEq α]
    (κ : PartialPairing α) (j : α) (hj : κ j = j)
    (i : {i : α // i ≠ j}) :
    (eraseSingle κ j hj i).1 = κ i.1 :=
  rfl

/-- Restore a distinguished fixed point to a pairing of its complement. -/
def insertSingle {α : Type*} [DecidableEq α]
    (j : α) (κ : PartialPairing {i : α // i ≠ j}) :
    PartialPairing α where
  toFun i :=
    if h : i = j then j else (κ ⟨i, h⟩).1
  involutive i := by
    by_cases hi : i = j
    · subst i
      simp
    · have hout : (κ ⟨i, hi⟩).1 ≠ j := (κ ⟨i, hi⟩).2
      simp [hi, hout]

@[simp]
theorem insertSingle_apply_eq
    {α : Type*} [DecidableEq α]
    (j : α) (κ : PartialPairing {i : α // i ≠ j}) :
    insertSingle j κ j = j := by
  simp [insertSingle]

@[simp]
theorem insertSingle_apply_ne
    {α : Type*} [DecidableEq α]
    (j : α) (κ : PartialPairing {i : α // i ≠ j})
    (i : α) (hi : i ≠ j) :
    insertSingle j κ i = (κ ⟨i, hi⟩).1 := by
  simp [insertSingle, hi]

@[simp]
theorem eraseSingle_insertSingle
    {α : Type*} [DecidableEq α]
    (j : α) (κ : PartialPairing {i : α // i ≠ j}) :
    eraseSingle (insertSingle j κ) j
      (insertSingle_apply_eq j κ) = κ := by
  apply PartialPairing.ext
  intro i
  apply Subtype.ext
  rw [eraseSingle_apply_val, insertSingle_apply_ne j κ i.1 i.2]

@[simp]
theorem insertSingle_eraseSingle
    {α : Type*} [DecidableEq α]
    (κ : PartialPairing α) (j : α) (hj : κ j = j) :
    insertSingle j (eraseSingle κ j hj) = κ := by
  apply PartialPairing.ext
  intro i
  by_cases hi : i = j
  · subst i
    rw [insertSingle_apply_eq, hj]
  · rw [insertSingle_apply_ne _ _ _ hi, eraseSingle_apply_val]

/-- Wick-contraction data: a partial pairing and one of its single
indices.  A structure (rather than a nested subtype) keeps equality of
the computational fields independent of proof terms. -/
structure MarkedSingle (α : Type*) [Fintype α] [DecidableEq α] where
  pairing : PartialPairing α
  index : α
  isSingle : index ∈ pairing.singles

@[ext]
theorem MarkedSingle.ext
    {α : Type*} [Fintype α] [DecidableEq α]
    {d e : MarkedSingle α}
    (hpairing : d.pairing = e.pairing)
    (hindex : d.index = e.index) :
    d = e := by
  cases d
  cases e
  simp only [MarkedSingle.mk.injEq] at hpairing hindex ⊢
  exact ⟨hpairing, hindex⟩

/-- A pairing with a marked single is equivalently a choice of the marked
index and a pairing of its complement. -/
def markedSingleEquiv (α : Type*) [Fintype α] [DecidableEq α] :
    MarkedSingle α ≃
      ((j : α) × PartialPairing {i : α // i ≠ j}) where
  toFun d :=
    ⟨d.index, eraseSingle d.pairing d.index
      (mem_singles.mp d.isSingle)⟩
  invFun d :=
    ⟨insertSingle d.1 d.2, d.1,
      mem_singles.mpr (insertSingle_apply_eq d.1 d.2)⟩
  left_inv d := by
    apply MarkedSingle.ext
    · exact insertSingle_eraseSingle d.pairing d.index
        (mem_singles.mp d.isSingle)
    · rfl
  right_inv d := by
    rcases d with ⟨j, κ⟩
    exact Sigma.ext rfl
      (heq_of_eq (eraseSingle_insertSingle j κ))

noncomputable instance markedSingleFintype
    (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype (MarkedSingle α) :=
  Fintype.ofEquiv
    ((j : α) × PartialPairing {i : α // i ≠ j})
    (markedSingleEquiv α).symm

/-! ### Ordered singles, as used by `wickAtSingleLabels` -/

/-- A pairing together with the rank of one single in increasing order. -/
abbrev RankedSingle (α : Type*) [Fintype α] [LinearOrder α] :=
  (κ : PartialPairing α) × Fin κ.singles.card

/-- The nested sigma representation of a marked single is definitionally
the same data as `MarkedSingle`. -/
def markedSingleSigmaEquiv
    (α : Type*) [Fintype α] [LinearOrder α] :
    ((κ : PartialPairing α) × {j : α // j ∈ κ.singles}) ≃
      MarkedSingle α where
  toFun d := ⟨d.1, d.2.1, d.2.2⟩
  invFun d := ⟨d.pairing, ⟨d.index, d.isSingle⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Increasing enumeration converts the rank used in the Wick list into
the corresponding marked ambient single. -/
def rankedSingleEquiv
    (α : Type*) [Fintype α] [LinearOrder α] :
    RankedSingle α ≃ MarkedSingle α :=
  (Equiv.sigmaCongrRight fun κ : PartialPairing α =>
      (κ.singles.orderIsoOfFin rfl).toEquiv).trans
    (markedSingleSigmaEquiv α)

/-- The actual list index in `wickAtSingleLabels` is the increasing
single-index enumeration. -/
@[simp]
theorem wickAtSingleLabels_length {m : ℕ}
    (κ : PartialPairing (Fin m)) (xt : Fin (m + 2) → T4) :
    (wickAtSingleLabels κ xt).length = κ.singles.card := by
  rw [wickAtSingleLabels, List.length_ofFn]

def wickLabelIndexEquiv {m : ℕ}
    (κ : PartialPairing (Fin m)) (xt : Fin (m + 2) → T4) :
    Fin (wickAtSingleLabels κ xt).length ≃
      {i : Fin m // i ∈ κ.singles} :=
  (Fin.castOrderIso (wickAtSingleLabels_length κ xt)).trans
    (κ.singles.orderIsoOfFin rfl)

@[simp]
theorem wickAtSingleLabels_get_eq
    {m : ℕ} (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4)
    (j : Fin (wickAtSingleLabels κ xt).length) :
    (wickAtSingleLabels κ xt).get j =
      xt (varIdx (wickLabelIndexEquiv κ xt j).1) := by
  change
    (List.ofFn fun k : Fin κ.singles.card =>
      xt (varIdx (κ.singles.orderEmbOfFin rfl k))).get j =
        xt (varIdx (wickLabelIndexEquiv κ xt j).1)
  rw [List.get_ofFn]
  apply congrArg xt
  apply congrArg varIdx
  apply Fin.ext
  rfl

/-- Reindex a nested Wick contraction sum by marked singles. -/
theorem sum_rankedSingle
    {α R : Type*} [Fintype α] [LinearOrder α]
    [AddCommMonoid R] (f : MarkedSingle α → R) :
    (∑ κ : PartialPairing α,
      ∑ j : Fin κ.singles.card,
        f (rankedSingleEquiv α ⟨κ, j⟩)) =
      ∑ d : MarkedSingle α, f d := by
  calc
    _ = ∑ d : RankedSingle α,
        f (rankedSingleEquiv α d) := by
      rw [Fintype.sum_sigma]
    _ = _ := (rankedSingleEquiv α).sum_comp f

/-! ## Creation and contraction as the two head branches -/

/-- The Wick creation/contraction indexing set is exactly the set of
partial pairings after adjoining a new zero-indexed head. -/
def wickHeadEquiv (n : ℕ) :
    PartialPairing (Fin n) ⊕ MarkedSingle (Fin n) ≃
      PartialPairing (Fin (n + 1)) :=
  (Equiv.sumCongr (Equiv.refl _) (markedSingleEquiv (Fin n))).trans
    (finHeadEquiv n).symm

@[simp]
theorem wickHeadEquiv_apply_creation
    (n : ℕ) (κ : PartialPairing (Fin n)) :
    wickHeadEquiv n (Sum.inl κ) =
      (finHeadEquiv n).symm (Sum.inl κ) :=
  rfl

@[simp]
theorem wickHeadEquiv_apply_contraction
    (n : ℕ) (d : MarkedSingle (Fin n)) :
    wickHeadEquiv n (Sum.inr d) =
      (finHeadEquiv n).symm
        (Sum.inr (markedSingleEquiv (Fin n) d)) :=
  rfl

/-- The creation branch fixes the new head. -/
theorem wickHeadEquiv_creation_isSingle
    (n : ℕ) (κ : PartialPairing (Fin n)) :
    HeadIsSingle (wickHeadEquiv n (Sum.inl κ)) := by
  unfold wickHeadEquiv finHeadEquiv HeadIsSingle
  simp [optionHeadEquiv, optionHeadAssemble]
  change
    PartialPairing.congr (finSuccEquiv n).symm
        (optionFixed κ) 0 = 0
  rw [PartialPairing.congr_apply_apply]
  simp

/-- The contraction branch pairs the new head with the marked old
single, hence cannot fix it. -/
theorem wickHeadEquiv_contraction_not_isSingle
    (n : ℕ) (d : MarkedSingle (Fin n)) :
    ¬HeadIsSingle (wickHeadEquiv n (Sum.inr d)) := by
  unfold wickHeadEquiv finHeadEquiv HeadIsSingle
  simp [optionHeadEquiv, optionHeadAssemble, markedSingleEquiv]
  change
    ¬PartialPairing.congr (finSuccEquiv n).symm
        (optionPaired d.index
          (eraseSingle d.pairing d.index
            (mem_singles.mp d.isSingle))) 0 = 0
  rw [PartialPairing.congr_apply_apply]
  simp

/-! ### Restricted equivalences matching `PairingHeadCases` -/

/-- Predicate selecting the creation summand. -/
def IsCreation {A B : Type*} : A ⊕ B → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- Predicate selecting the contraction summand. -/
def IsContraction {A B : Type*} : A ⊕ B → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

/-- A subtype of the left summand is canonically the left type. -/
def creationSubtypeEquiv (A B : Type*) :
    {s : A ⊕ B // IsCreation s} ≃ A where
  toFun
    | ⟨Sum.inl a, _⟩ => a
    | ⟨Sum.inr _, h⟩ => False.elim h
  invFun a := ⟨Sum.inl a, trivial⟩
  left_inv s := by
    rcases s with ⟨a | b, h⟩
    · rfl
    · exact False.elim h
  right_inv _ := rfl

/-- A subtype of the right summand is canonically the right type. -/
def contractionSubtypeEquiv (A B : Type*) :
    {s : A ⊕ B // IsContraction s} ≃ B where
  toFun
    | ⟨Sum.inl _, h⟩ => False.elim h
    | ⟨Sum.inr b, _⟩ => b
  invFun b := ⟨Sum.inr b, trivial⟩
  left_inv s := by
    rcases s with ⟨a | b, h⟩
    · exact False.elim h
    · rfl
  right_inv _ := rfl

theorem isCreation_iff_headIsSingle
    (n : ℕ)
    (s : PartialPairing (Fin n) ⊕ MarkedSingle (Fin n)) :
    IsCreation s ↔ HeadIsSingle (wickHeadEquiv n s) := by
  cases s with
  | inl κ =>
      exact iff_of_true trivial
        (wickHeadEquiv_creation_isSingle n κ)
  | inr d =>
      exact iff_of_false (by simp [IsCreation])
        (wickHeadEquiv_contraction_not_isSingle n d)

theorem isContraction_iff_not_headIsSingle
    (n : ℕ)
    (s : PartialPairing (Fin n) ⊕ MarkedSingle (Fin n)) :
    IsContraction s ↔
      ¬HeadIsSingle (wickHeadEquiv n s) := by
  cases s with
  | inl κ =>
      exact iff_of_false (by simp [IsContraction])
        (not_not.mpr
          (wickHeadEquiv_creation_isSingle n κ))
  | inr d =>
      exact iff_of_true trivial
        (wickHeadEquiv_contraction_not_isSingle n d)

/-- Created pairings are exactly the `HeadIsSingle` class. -/
def creationHeadEquiv (n : ℕ) :
    PartialPairing (Fin n) ≃
      {κ : PartialPairing (Fin (n + 1)) // HeadIsSingle κ} :=
  (creationSubtypeEquiv
      (PartialPairing (Fin n)) (MarkedSingle (Fin n))).symm.trans
    ((wickHeadEquiv n).subtypeEquiv
      (isCreation_iff_headIsSingle n))

/-- Contracted pairings are exactly the complement of the
`HeadIsSingle` class. -/
def contractionHeadEquiv (n : ℕ) :
    MarkedSingle (Fin n) ≃
      {κ : PartialPairing (Fin (n + 1)) // ¬HeadIsSingle κ} :=
  (contractionSubtypeEquiv
      (PartialPairing (Fin n)) (MarkedSingle (Fin n))).symm.trans
    ((wickHeadEquiv n).subtypeEquiv
      (isContraction_iff_not_headIsSingle n))

@[simp]
theorem creationHeadEquiv_apply_val
    (n : ℕ) (κ : PartialPairing (Fin n)) :
    (creationHeadEquiv n κ).1 =
      wickHeadEquiv n (Sum.inl κ) :=
  rfl

@[simp]
theorem contractionHeadEquiv_apply_val
    (n : ℕ) (d : MarkedSingle (Fin n)) :
    (contractionHeadEquiv n d).1 =
      wickHeadEquiv n (Sum.inr d) :=
  rfl

/-- Split a paired-head pairing according to existence of a fully paired
head prefix. -/
def pairedHeadCasesEquiv (n : ℕ) :
    {κ : PartialPairing (Fin (n + 1)) // ¬HeadIsSingle κ} ≃
      {κ : PartialPairing (Fin (n + 1)) // HeadPairedNoPrefix κ} ⊕
        {κ : PartialPairing (Fin (n + 1)) //
          HeadPairedWithPrefix κ} where
  toFun κ :=
    if h : HasFullyPairedHeadPrefix κ.1 then
      Sum.inr ⟨κ.1, κ.2, h⟩
    else
      Sum.inl ⟨κ.1, κ.2, h⟩
  invFun
    | Sum.inl κ => ⟨κ.1, κ.2.1⟩
    | Sum.inr κ => ⟨κ.1, κ.2.1⟩
  left_inv κ := by
    by_cases h : HasFullyPairedHeadPrefix κ.1
    · simp [h]
    · simp [h]
  right_inv κ := by
    rcases κ with κ | κ
    · have h := κ.2.2
      simp [h]
    · have h := κ.2.2
      simp [h]

/-- Evaluate the same ambient-pairing function on either paired-head
case. -/
def pairedHeadCasesValue
    {R : Type*} {n : ℕ}
    (f : PartialPairing (Fin (n + 1)) → R) :
    {κ : PartialPairing (Fin (n + 1)) // HeadPairedNoPrefix κ} ⊕
        {κ : PartialPairing (Fin (n + 1)) //
          HeadPairedWithPrefix κ} → R
  | Sum.inl κ => f κ.1
  | Sum.inr κ => f κ.1

@[simp]
theorem pairedHeadCasesValue_equiv_apply
    {R : Type*} (n : ℕ)
    (f : PartialPairing (Fin (n + 1)) → R)
    (κ : {κ : PartialPairing (Fin (n + 1)) //
      ¬HeadIsSingle κ}) :
    pairedHeadCasesValue f (pairedHeadCasesEquiv n κ) = f κ.1 := by
  change pairedHeadCasesValue f
    (if h : HasFullyPairedHeadPrefix κ.1 then
      Sum.inr ⟨κ.1, κ.2, h⟩
    else
      Sum.inl ⟨κ.1, κ.2, h⟩) = f κ.1
  split <;> rfl

/-- Final pairing-index equivalence for the Wick contraction sum: every
marked single produces, uniquely, either case (2) or case (3) of
Proposition 3.4. -/
def contractionHeadCasesEquiv (n : ℕ) :
    MarkedSingle (Fin n) ≃
      {κ : PartialPairing (Fin (n + 1)) // HeadPairedNoPrefix κ} ⊕
        {κ : PartialPairing (Fin (n + 1)) //
          HeadPairedWithPrefix κ} :=
  (contractionHeadEquiv n).trans (pairedHeadCasesEquiv n)

/-- The exact index type occurring in the nested Wick contraction sum,
followed by the paper case-(2)/(3) classification. -/
def rankedContractionHeadCasesEquiv (n : ℕ) :
    RankedSingle (Fin n) ≃
      {κ : PartialPairing (Fin (n + 1)) // HeadPairedNoPrefix κ} ⊕
        {κ : PartialPairing (Fin (n + 1)) //
          HeadPairedWithPrefix κ} :=
  (rankedSingleEquiv (Fin n)).trans
    (contractionHeadCasesEquiv n)

/-! ### Finite-sum reindexing -/

/-- Creation and contraction together enumerate every pairing with a new
head exactly once. -/
theorem sum_creation_contraction
    {R : Type*} [AddCommMonoid R] (n : ℕ)
    (f : PartialPairing (Fin (n + 1)) → R) :
    (∑ κ : PartialPairing (Fin n),
        f (creationHeadEquiv n κ).1) +
      (∑ d : MarkedSingle (Fin n),
        f (contractionHeadEquiv n d).1) =
      ∑ κ : PartialPairing (Fin (n + 1)), f κ := by
  calc
    _ = ∑ s :
        PartialPairing (Fin n) ⊕ MarkedSingle (Fin n),
        f (wickHeadEquiv n s) := by
      rw [Fintype.sum_sum_type]
      rfl
    _ = _ := (wickHeadEquiv n).sum_comp f

/-- The contraction sum is exactly the sum of paper head cases (2) and
(3), with no multiplicity. -/
theorem sum_contraction_headCases
    {R : Type*} [AddCommMonoid R] (n : ℕ)
    (f : PartialPairing (Fin (n + 1)) → R) :
    (∑ d : MarkedSingle (Fin n),
        f (contractionHeadEquiv n d).1) =
      (∑ κ : {κ : PartialPairing (Fin (n + 1)) //
          HeadPairedNoPrefix κ}, f κ.1) +
        ∑ κ : {κ : PartialPairing (Fin (n + 1)) //
          HeadPairedWithPrefix κ}, f κ.1 := by
  calc
    _ = ∑ κ : {κ : PartialPairing (Fin (n + 1)) //
        ¬HeadIsSingle κ}, f κ.1 :=
      (contractionHeadEquiv n).sum_comp (fun κ => f κ.1)
    _ = ∑ s :
        {κ : PartialPairing (Fin (n + 1)) //
            HeadPairedNoPrefix κ} ⊕
          {κ : PartialPairing (Fin (n + 1)) //
            HeadPairedWithPrefix κ},
        pairedHeadCasesValue f s := by
      simpa only [pairedHeadCasesValue_equiv_apply] using
        (pairedHeadCasesEquiv n).sum_comp
          (pairedHeadCasesValue f)
    _ = _ := by
      rw [Fintype.sum_sum_type]
      rfl

/-- The creation sum is precisely head case (1). -/
theorem sum_creation_headCase
    {R : Type*} [AddCommMonoid R] (n : ℕ)
    (f : PartialPairing (Fin (n + 1)) → R) :
    (∑ κ : PartialPairing (Fin n),
        f (creationHeadEquiv n κ).1) =
      ∑ κ : {κ : PartialPairing (Fin (n + 1)) //
        HeadIsSingle κ}, f κ.1 :=
  (creationHeadEquiv n).sum_comp (fun κ => f κ.1)

/-- Nested Wick contraction ranks reindex with multiplicity one to the
paper's paired-head cases. -/
theorem sum_ranked_contraction_headCases
    {R : Type*} [AddCommMonoid R] (n : ℕ)
    (f : PartialPairing (Fin (n + 1)) → R) :
    (∑ κ : PartialPairing (Fin n),
      ∑ j : Fin κ.singles.card,
        f (contractionHeadEquiv n
          (rankedSingleEquiv (Fin n) ⟨κ, j⟩)).1) =
      (∑ κ : {κ : PartialPairing (Fin (n + 1)) //
          HeadPairedNoPrefix κ}, f κ.1) +
        ∑ κ : {κ : PartialPairing (Fin (n + 1)) //
          HeadPairedWithPrefix κ}, f κ.1 := by
  calc
    _ = ∑ d : MarkedSingle (Fin n),
        f (contractionHeadEquiv n d).1 :=
      sum_rankedSingle
        (fun d : MarkedSingle (Fin n) =>
          f (contractionHeadEquiv n d).1)
    _ = _ := sum_contraction_headCases n f

/-- Full Wick indexing ledger: the created term and every contraction
term enumerate the three disjoint head classes exactly once. -/
theorem sum_wickIndices_headCases
    {R : Type*} [AddCommMonoid R] (n : ℕ)
    (f : PartialPairing (Fin (n + 1)) → R) :
    (∑ κ : PartialPairing (Fin n),
        f (creationHeadEquiv n κ).1) +
      (∑ κ : PartialPairing (Fin n),
        ∑ j : Fin κ.singles.card,
          f (contractionHeadEquiv n
            (rankedSingleEquiv (Fin n) ⟨κ, j⟩)).1) =
      (∑ κ : {κ : PartialPairing (Fin (n + 1)) //
          HeadIsSingle κ}, f κ.1) +
        (∑ κ : {κ : PartialPairing (Fin (n + 1)) //
          HeadPairedNoPrefix κ}, f κ.1) +
        ∑ κ : {κ : PartialPairing (Fin (n + 1)) //
          HeadPairedWithPrefix κ}, f κ.1 := by
  rw [sum_creation_headCase, sum_ranked_contraction_headCases]
  abel

/-! ## Concatenating a closed prefix and an external remainder -/

/-- Disjoint sum of two partial pairings. -/
def sumPairing {α β : Type*}
    (σ : PartialPairing α) (τ : PartialPairing β) :
    PartialPairing (α ⊕ β) where
  toFun
    | Sum.inl i => Sum.inl (σ i)
    | Sum.inr j => Sum.inr (τ j)
  involutive
    | Sum.inl i => by simp
    | Sum.inr j => by simp

@[simp]
theorem sumPairing_apply_left
    {α β : Type*} (σ : PartialPairing α)
    (τ : PartialPairing β) (i : α) :
    sumPairing σ τ (Sum.inl i) = Sum.inl (σ i) :=
  rfl

@[simp]
theorem sumPairing_apply_right
    {α β : Type*} (σ : PartialPairing α)
    (τ : PartialPairing β) (j : β) :
    sumPairing σ τ (Sum.inr j) = Sum.inr (τ j) :=
  rfl

/-- Concatenate pairings on two finite consecutive blocks. -/
def appendPairing {a b : ℕ}
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin b)) :
    PartialPairing (Fin (a + b)) :=
  PartialPairing.congr finSumFinEquiv (sumPairing σ τ)

@[simp]
theorem appendPairing_apply_castAdd
    {a b : ℕ} (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin b)) (i : Fin a) :
    appendPairing σ τ (Fin.castAdd b i) =
      Fin.castAdd b (σ i) := by
  unfold appendPairing
  rw [PartialPairing.congr_apply_apply]
  simp

@[simp]
theorem appendPairing_apply_natAdd
    {a b : ℕ} (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin b)) (j : Fin b) :
    appendPairing σ τ (Fin.natAdd a j) =
      Fin.natAdd a (τ j) := by
  unfold appendPairing
  rw [PartialPairing.congr_apply_apply]
  simp

/-- Concatenate a block of length `a` and its arithmetic complement
inside `Fin N`. -/
def appendPairingTo {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a))) :
    PartialPairing (Fin N) :=
  PartialPairing.congr
    (Fin.castOrderIso (by omega :
      a + (N - a) = N)).toEquiv
    (appendPairing σ τ)

@[simp]
theorem appendPairingTo_apply_prefix
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (i : Fin a) :
    appendPairingTo ha σ τ (Fin.castLE ha i) =
      Fin.castLE ha (σ i) := by
  unfold appendPairingTo
  rw [PartialPairing.congr_apply_apply]
  apply Fin.ext
  change
    (appendPairing σ τ
      ((Fin.castOrderIso (by omega :
        a + (N - a) = N)).symm (Fin.castLE ha i))).val =
      (σ i).val
  have hin :
      (Fin.castOrderIso (by omega :
        a + (N - a) = N)).symm (Fin.castLE ha i) =
        Fin.castAdd (N - a) i := by
    apply Fin.ext
    rfl
  rw [hin, appendPairing_apply_castAdd]
  rfl

/-- Canonical embedding of a remainder coordinate after the first
`a` entries. -/
def suffixFin {N a : ℕ} (ha : a ≤ N)
    (j : Fin (N - a)) : Fin N :=
  ⟨a + j.val, by omega⟩

@[simp]
theorem suffixFin_val
    {N a : ℕ} (ha : a ≤ N) (j : Fin (N - a)) :
    (suffixFin ha j).val = a + j.val :=
  rfl

@[simp]
theorem appendPairingTo_apply_suffix
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (j : Fin (N - a)) :
    appendPairingTo ha σ τ (suffixFin ha j) =
      suffixFin ha (τ j) := by
  unfold appendPairingTo suffixFin
  rw [PartialPairing.congr_apply_apply]
  apply Fin.ext
  change
    (appendPairing σ τ
      ((Fin.castOrderIso (by omega :
        a + (N - a) = N)).symm
          (⟨a + j.val, by omega⟩ : Fin N))).val =
      a + (τ j).val
  have hin :
      (Fin.castOrderIso (by omega :
        a + (N - a) = N)).symm
          (⟨a + j.val, by omega⟩ : Fin N) =
        Fin.natAdd a j := by
    apply Fin.ext
    rfl
  rw [hin, appendPairing_apply_natAdd]
  rfl

/-- The first block of an appended pairing is closed and full whenever
the prefix pairing is full. -/
theorem appendPairingTo_prefix_fullyPaired
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (hσ : σ.IsFull) :
    IsFullyPairedOn (appendPairingTo ha σ τ)
      (Finset.univ.filter fun i : Fin N => i.val < a) := by
  constructor
  · intro i hi
    have hia : i.val < a := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
    let j : Fin a := ⟨i.val, hia⟩
    have hij : Fin.castLE ha j = i := Fin.ext rfl
    rw [← hij, appendPairingTo_apply_prefix]
    intro hfix
    apply hσ j
    apply Fin.ext
    exact congrArg (fun x : Fin N => x.val) hfix
  · intro i hi
    have hia : i.val < a := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
    let j : Fin a := ⟨i.val, hia⟩
    have hij : Fin.castLE ha j = i := Fin.ext rfl
    rw [← hij, appendPairingTo_apply_prefix]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (σ j).isLt

/-- Any smaller fully paired prefix of an appended pairing restricts to
the corresponding fully paired prefix of its first block. -/
theorem prefix_fullyPaired_of_appendPairingTo
    {N a r : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (h :
      IsFullyPairedOn (appendPairingTo ha σ τ)
        (Finset.univ.filter fun i : Fin N => i.val < r)) :
    IsFullyPairedOn σ
      (Finset.univ.filter fun i : Fin a => i.val < r) := by
  constructor
  · intro i hi
    have hir : i.val < r := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
    have hiN :
        Fin.castLE ha i ∈
          Finset.univ.filter (fun j : Fin N => j.val < r) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hir
    intro hfix
    apply h.ne_of_mem hiN
    rw [appendPairingTo_apply_prefix, hfix]
  · intro i hi
    have hir : i.val < r := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
    have hiN :
        Fin.castLE ha i ∈
          Finset.univ.filter (fun j : Fin N => j.val < r) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hir
    have hout := h.apply_mem hiN
    rw [appendPairingTo_apply_prefix] at hout
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hout ⊢
    change (σ i).val < r at hout
    exact hout

/-! ### The canonical case-(3) assembly -/

/-- Assemble a non-split closed head block with an arbitrary remainder. -/
def assembleCaseThree
    {m q : ℕ} (hq : 2 * q ≤ m + 1)
    (σ : PartialPairing (Fin (2 * q)))
    (τ : PartialPairing (Fin (m + 1 - 2 * q))) :
    PartialPairing (Fin (m + 1)) :=
  appendPairingTo hq σ τ

theorem assembleCaseThree_isFullyPairedHeadPrefix
    {m q : ℕ} (hqpos : 1 ≤ q) (hq : 2 * q ≤ m + 1)
    (σ : PartialPairing (Fin (2 * q)))
    (τ : PartialPairing (Fin (m + 1 - 2 * q)))
    (hσ : IsNonSplit σ) :
    IsFullyPairedHeadPrefix
      (assembleCaseThree hq σ τ) q := by
  refine ⟨hqpos, hq, ?_⟩
  exact appendPairingTo_prefix_fullyPaired hq σ τ hσ.1

theorem assembleCaseThree_headPairedWithPrefix
    {m q : ℕ} (hqpos : 1 ≤ q) (hq : 2 * q ≤ m + 1)
    (σ : PartialPairing (Fin (2 * q)))
    (τ : PartialPairing (Fin (m + 1 - 2 * q)))
    (hσ : IsNonSplit σ) :
    HeadPairedWithPrefix (assembleCaseThree hq σ τ) := by
  have hp :=
    assembleCaseThree_isFullyPairedHeadPrefix
      hqpos hq σ τ hσ
  exact
    ⟨head_paired_of_fullyPairedHeadPrefix hp,
      ⟨q, hp⟩⟩

/-- Non-splitting of the internal block rules out every smaller fully
paired head prefix after assembly. -/
theorem assembleCaseThree_no_smaller
    {m q : ℕ} (hq : 2 * q ≤ m + 1)
    (σ : PartialPairing (Fin (2 * q)))
    (τ : PartialPairing (Fin (m + 1 - 2 * q)))
    (hσ : IsNonSplit σ) {r : ℕ} (hr : r < q) :
    ¬IsFullyPairedHeadPrefix
      (assembleCaseThree hq σ τ) r := by
  intro hprefix
  have hrpos : 1 ≤ r := hprefix.1
  have hrestricted :
      IsFullyPairedOn σ
        (Finset.univ.filter fun i : Fin (2 * q) =>
          i.val < 2 * r) :=
    prefix_fullyPaired_of_appendPairingTo hq
      σ τ hprefix.2.2
  apply hσ.2
  let p := 2 * r - 1
  refine ⟨p, ?_, ?_, ?_⟩
  · exact Finset.mem_range.mpr (by omega)
  · omega
  · have hsets :
        Finset.univ.filter
            (fun i : Fin (2 * q) => i.val ≤ p) =
          Finset.univ.filter
            (fun i : Fin (2 * q) => i.val < 2 * r) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp [p]
      omega
    simpa only [hsets] using hrestricted

/-- The first fully paired head prefix of the assembled pairing is
exactly the prescribed non-split block. -/
theorem assembleCaseThree_firstQ
    {m q : ℕ} (hqpos : 1 ≤ q) (hq : 2 * q ≤ m + 1)
    (σ : PartialPairing (Fin (2 * q)))
    (τ : PartialPairing (Fin (m + 1 - 2 * q)))
    (hσ : IsNonSplit σ) :
    firstFullyPairedHeadQ
        (assembleCaseThree hq σ τ)
        (assembleCaseThree_headPairedWithPrefix
          hqpos hq σ τ hσ).2 =
      q := by
  let κ := assembleCaseThree hq σ τ
  let hp : HasFullyPairedHeadPrefix κ :=
    (assembleCaseThree_headPairedWithPrefix
      hqpos hq σ τ hσ).2
  apply le_antisymm
  · exact firstFullyPairedHeadQ_min κ hp
      (assembleCaseThree_isFullyPairedHeadPrefix
        hqpos hq σ τ hσ)
  · by_contra hnot
    have hlt :
        firstFullyPairedHeadQ κ hp < q :=
      Nat.lt_of_not_ge hnot
    exact assembleCaseThree_no_smaller
      hq σ τ hσ hlt
      (firstFullyPairedHeadQ_spec κ hp)

/-- Two minimal-prefix decompositions of the same pairing are equal once
their numerical prefix orders agree; all remaining fields are
propositions. -/
theorem HeadPrefixDecomposition.eq_of_q_eq
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d₁ d₂ : HeadPrefixDecomposition κ)
    (h : d₁.q = d₂.q) :
    d₁ = d₂ := by
  cases d₁
  cases d₂
  simp only [HeadPrefixDecomposition.mk.injEq] at h ⊢
  exact h

/-- The explicit minimal-prefix decomposition of an assembled case-(3)
pairing. -/
def assembledHeadPrefixDecomposition
    {m q : ℕ} (hqpos : 1 ≤ q) (hq : 2 * q ≤ m + 1)
    (σ : PartialPairing (Fin (2 * q)))
    (τ : PartialPairing (Fin (m + 1 - 2 * q)))
    (hσ : IsNonSplit σ) :
    HeadPrefixDecomposition (assembleCaseThree hq σ τ) where
  q := q
  q_pos := hqpos
  two_mul_le := hq
  fullyPaired :=
    (assembleCaseThree_isFullyPairedHeadPrefix
      hqpos hq σ τ hσ).2.2
  minimal := by
    intro r hr
    by_contra hnot
    exact assembleCaseThree_no_smaller
      hq σ τ hσ (Nat.lt_of_not_ge hnot) hr

/-- Bundle an assembled pairing in the case-(3) subtype. -/
def assembleCaseThreeSubtype
    {m q : ℕ} (hqpos : 1 ≤ q) (hq : 2 * q ≤ m + 1)
    (σ : PartialPairing (Fin (2 * q)))
    (τ : PartialPairing (Fin (m + 1 - 2 * q)))
    (hσ : IsNonSplit σ) :
    {κ : PartialPairing (Fin (m + 1)) //
      HeadPairedWithPrefix κ} :=
  ⟨assembleCaseThree hq σ τ,
    assembleCaseThree_headPairedWithPrefix
      hqpos hq σ τ hσ⟩

@[simp]
theorem assembleCaseThreeSubtype_q
    {m q : ℕ} (hqpos : 1 ≤ q) (hq : 2 * q ≤ m + 1)
    (σ : PartialPairing (Fin (2 * q)))
    (τ : PartialPairing (Fin (m + 1 - 2 * q)))
    (hσ : IsNonSplit σ) :
    caseThreeQ
      (assembleCaseThreeSubtype hqpos hq σ τ hσ) = q :=
  assembleCaseThree_firstQ hqpos hq σ τ hσ

/-- Restricting the explicit assembled pairing back to its first block
recovers the original non-split pairing. -/
theorem assembledHeadPrefix_collapse_eq
    {m q : ℕ} (hqpos : 1 ≤ q) (hq : 2 * q ≤ m + 1)
    (σ : PartialPairing (Fin (2 * q)))
    (τ : PartialPairing (Fin (m + 1 - 2 * q)))
    (hσ : IsNonSplit σ) :
    (assembledHeadPrefixDecomposition
      hqpos hq σ τ hσ).collapsePrefixPairing = σ := by
  apply PartialPairing.ext
  intro i
  change Fin (2 * q) at i
  apply Fin.ext
  rw [HeadPrefixDecomposition.collapsePrefixPairing_apply_val]
  change
    (appendPairingTo hq σ τ
      (Fin.castLE hq i)).val = (σ i).val
  rw [appendPairingTo_apply_prefix]
  rfl

/-- The canonical decomposition chosen by `caseThreeDecomposition`
coincides with the explicit assembled decomposition. -/
theorem caseThreeDecomposition_assemble
    {m q : ℕ} (hqpos : 1 ≤ q) (hq : 2 * q ≤ m + 1)
    (σ : PartialPairing (Fin (2 * q)))
    (τ : PartialPairing (Fin (m + 1 - 2 * q)))
    (hσ : IsNonSplit σ) :
    caseThreeDecomposition
        (assembleCaseThreeSubtype hqpos hq σ τ hσ) =
      assembledHeadPrefixDecomposition
        hqpos hq σ τ hσ := by
  apply HeadPrefixDecomposition.eq_of_q_eq
  exact assembleCaseThreeSubtype_q hqpos hq σ τ hσ

/-! ### Recovering the external remainder -/

/-- The complement of the first `a` consecutive coordinates is
order-isomorphic to `Fin (N-a)` by subtracting `a`. -/
def suffixComplOrderIso {N a : ℕ} (ha : a ≤ N) :
    {i : Fin N //
      i ∉ Finset.univ.filter (fun j : Fin N => j.val < a)} ≃o
        Fin (N - a) where
  toFun i :=
    ⟨i.1.val - a, by
      have hge : a ≤ i.1.val := by
        apply Nat.le_of_not_gt
        intro hlt
        apply i.2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hlt
      omega⟩
  invFun j :=
    ⟨suffixFin ha j, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        suffixFin_val]
      omega⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have hge : a ≤ i.1.val := by
      apply Nat.le_of_not_gt
      intro hlt
      apply i.2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hlt
    simp only [suffixFin_val]
    omega
  right_inv j := by
    apply Fin.ext
    simp only [suffixFin_val]
    omega
  map_rel_iff' := by
    intro i j
    change i.1.val - a ≤ j.1.val - a ↔ i.1.val ≤ j.1.val
    have hi : a ≤ i.1.val := by
      apply Nat.le_of_not_gt
      intro hlt
      apply i.2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hlt
    have hj : a ≤ j.1.val := by
      apply Nat.le_of_not_gt
      intro hlt
      apply j.2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hlt
    omega

@[simp]
theorem suffixComplOrderIso_symm_apply_val
    {N a : ℕ} (ha : a ≤ N) (j : Fin (N - a)) :
    ((suffixComplOrderIso ha).symm j).1 =
      suffixFin ha j :=
  rfl

/-- For every head-prefix decomposition, the abstract monotone remainder
enumeration is the concrete suffix enumeration. -/
theorem HeadPrefixDecomposition.remainderOrderIso_eq_suffix
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d : HeadPrefixDecomposition κ) :
    d.remainderOrderIso =
      suffixComplOrderIso d.two_mul_le := by
  apply Subsingleton.elim

/-- The remainder pairing, embedded back after the prefix, agrees with
the ambient pairing on every suffix coordinate. -/
theorem HeadPrefixDecomposition.remainderPairing_apply_suffix
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d : HeadPrefixDecomposition κ)
    (j : Fin (m + 1 - 2 * d.q)) :
    suffixFin d.two_mul_le (d.remainderPairing j) =
      κ (suffixFin d.two_mul_le j) := by
  unfold HeadPrefixDecomposition.remainderPairing
  rw [d.remainderOrderIso_eq_suffix]
  rw [PartialPairing.congr_apply_apply]
  let v :
      {i : Fin (m + 1) //
        i ∉ Finset.univ.filter
          (fun k : Fin (m + 1) => k.val < 2 * d.q)} :=
    (κ.restrictCompl d.fullyPaired.2)
      ((suffixComplOrderIso d.two_mul_le).symm j)
  have h :=
    congrArg
      (fun x :
        {i : Fin (m + 1) //
          i ∉ Finset.univ.filter
            (fun k : Fin (m + 1) => k.val < 2 * d.q)} => x.1)
      ((suffixComplOrderIso d.two_mul_le).symm_apply_apply v)
  change
    suffixFin d.two_mul_le
        ((suffixComplOrderIso d.two_mul_le).toEquiv v) =
      κ (suffixFin d.two_mul_le j) at h
  change
    suffixFin d.two_mul_le
        ((suffixComplOrderIso d.two_mul_le).toEquiv v) =
      κ (suffixFin d.two_mul_le j)
  exact h

/-- The generic monotone complement enumeration used by
`remainderOrderIso` is the concrete suffix enumeration on an assembled
head block. -/
theorem assembled_remainderOrderIso_eq
    {m q : ℕ} (hqpos : 1 ≤ q) (hq : 2 * q ≤ m + 1)
    (σ : PartialPairing (Fin (2 * q)))
    (τ : PartialPairing (Fin (m + 1 - 2 * q)))
    (hσ : IsNonSplit σ) :
    (assembledHeadPrefixDecomposition
        hqpos hq σ τ hσ).remainderOrderIso =
      suffixComplOrderIso hq := by
  apply Subsingleton.elim

/-- Restricting the explicit assembled pairing to the suffix recovers the
original external remainder pairing. -/
theorem assembledHeadPrefix_remainder_eq
    {m q : ℕ} (hqpos : 1 ≤ q) (hq : 2 * q ≤ m + 1)
    (σ : PartialPairing (Fin (2 * q)))
    (τ : PartialPairing (Fin (m + 1 - 2 * q)))
    (hσ : IsNonSplit σ) :
    (assembledHeadPrefixDecomposition
      hqpos hq σ τ hσ).remainderPairing = τ := by
  apply PartialPairing.ext
  intro j
  change Fin (m + 1 - 2 * q) at j
  apply Fin.ext
  unfold HeadPrefixDecomposition.remainderPairing
  rw [assembled_remainderOrderIso_eq]
  rw [PartialPairing.congr_apply_apply]
  let u :
      {i : Fin (m + 1) //
        i ∉ Finset.univ.filter
          (fun k : Fin (m + 1) => k.val < 2 * q)} :=
    ⟨appendPairingTo hq σ τ (suffixFin hq j), by
      intro hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      have hv := congrArg (fun x : Fin (m + 1) => x.val)
        (appendPairingTo_apply_suffix hq σ τ j)
      simp only [suffixFin_val] at hv
      omega⟩
  change ((suffixComplOrderIso hq) u).val = (τ j).val
  have hu :
      u = ⟨suffixFin hq (τ j), by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          suffixFin_val]
        omega⟩ := by
    apply Subtype.ext
    exact appendPairingTo_apply_suffix hq σ τ j
  rw [hu]
  change 2 * q + (τ j).val - 2 * q = (τ j).val
  omega

/-- Reassembling the collapsed head block and the canonical remainder of
an arbitrary head-prefix decomposition recovers the ambient pairing. -/
theorem HeadPrefixDecomposition.assemble_collapse_remainder
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d : HeadPrefixDecomposition κ) :
    assembleCaseThree d.two_mul_le
        d.collapsePrefixPairing d.remainderPairing = κ := by
  apply PartialPairing.ext
  intro i
  apply Fin.ext
  by_cases hi : i.val < 2 * d.q
  · let j : Fin (2 * d.q) := ⟨i.val, hi⟩
    have hcast : Fin.castLE d.two_mul_le j = i := Fin.ext rfl
    rw [← hcast]
    change
      (appendPairingTo d.two_mul_le
        d.collapsePrefixPairing d.remainderPairing
          (Fin.castLE d.two_mul_le j)).val =
        (κ (Fin.castLE d.two_mul_le j)).val
    rw [appendPairingTo_apply_prefix]
    exact d.collapsePrefixPairing_apply_val j
  · have hge : 2 * d.q ≤ i.val := Nat.le_of_not_gt hi
    let j : Fin (m + 1 - 2 * d.q) :=
      ⟨i.val - 2 * d.q, by omega⟩
    have hsuffix : suffixFin d.two_mul_le j = i := by
      apply Fin.ext
      simp only [suffixFin_val]
      dsimp [j]
      omega
    rw [← hsuffix]
    change
      (appendPairingTo d.two_mul_le
        d.collapsePrefixPairing d.remainderPairing
          (suffixFin d.two_mul_le j)).val =
        (κ (suffixFin d.two_mul_le j)).val
    rw [appendPairingTo_apply_suffix]
    exact congrArg Fin.val
      (d.remainderPairing_apply_suffix j)

/-! ### The exact fixed-prefix fibre bijection -/

/-- The paper's independent data at a fixed counterterm length `2q`: a
non-split full head pairing together with an arbitrary tail pairing. -/
abbrev CaseThreeAssemblyData (m q : ℕ) :=
  {σ : PartialPairing (Fin (2 * q)) // IsNonSplit σ} ×
    PartialPairing (Fin (m + 1 - 2 * q))

/-- The ambient case-(3) pairings whose least closed head block has length
exactly `2q`. -/
abbrev CaseThreeFiber (m q : ℕ) :=
  {κ :
      {κ : PartialPairing (Fin (m + 1)) //
        HeadPairedWithPrefix κ} //
    caseThreeQ κ = q}

/-- Assemble fixed-`q` counterterm data as an ambient case-(3) pairing. -/
def caseThreeFiberAssembly
    {m q : ℕ} (hqpos : 1 ≤ q) (hq : 2 * q ≤ m + 1) :
    CaseThreeAssemblyData m q → CaseThreeFiber m q :=
  fun data =>
    ⟨assembleCaseThreeSubtype hqpos hq
        data.1.1 data.2 data.1.2,
      assembleCaseThreeSubtype_q hqpos hq
        data.1.1 data.2 data.1.2⟩

/-- Assembly is injective: the prefix and suffix coordinates can each be
read back from the ambient involution. -/
theorem caseThreeFiberAssembly_injective
    {m q : ℕ} (hqpos : 1 ≤ q) (hq : 2 * q ≤ m + 1) :
    Function.Injective (caseThreeFiberAssembly hqpos hq) := by
  intro x y hxy
  have hpair := congrArg (fun z => z.1.1) hxy
  change
    assembleCaseThree hq x.1.1 x.2 =
      assembleCaseThree hq y.1.1 y.2 at hpair
  apply Prod.ext
  · apply Subtype.ext
    apply PartialPairing.ext
    intro i
    have hi :=
      congrArg
        (fun ν : PartialPairing (Fin (m + 1)) =>
          ν (Fin.castLE hq i))
        hpair
    apply Fin.ext
    have hiv := congrArg Fin.val hi
    simp only [assembleCaseThree,
      appendPairingTo_apply_prefix] at hiv
    change (x.1.1 i).val = (y.1.1 i).val at hiv
    exact hiv
  · apply PartialPairing.ext
    intro j
    have hj :=
      congrArg
        (fun ν : PartialPairing (Fin (m + 1)) =>
          ν (suffixFin hq j))
        hpair
    apply Fin.ext
    have hjv := congrArg Fin.val hj
    simp only [assembleCaseThree,
      appendPairingTo_apply_suffix, suffixFin_val] at hjv
    omega

/-- Every ambient pairing in the fixed-`q` fibre is obtained by assembling
its canonical collapsed prefix and remainder. -/
theorem caseThreeFiberAssembly_surjective
    {m q : ℕ} (hqpos : 1 ≤ q) (hq : 2 * q ≤ m + 1) :
    Function.Surjective (caseThreeFiberAssembly hqpos hq) := by
  rintro ⟨K, hKq⟩
  let d := caseThreeDecomposition K
  have hdq : d.q = q := by
    change caseThreeQ K = q
    exact hKq
  subst q
  refine
    ⟨⟨⟨d.collapsePrefixPairing,
          d.collapsePrefixPairing_isNonSplit⟩,
        d.remainderPairing⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact d.assemble_collapse_remainder

/-- Exact multiplicity-one correspondence between the paper's
`(σ₁, σ₂)` data and ambient case-(3) pairings at a fixed `q`. -/
def caseThreeFiberEquiv
    {m q : ℕ} (hqpos : 1 ≤ q) (hq : 2 * q ≤ m + 1) :
    CaseThreeAssemblyData m q ≃ CaseThreeFiber m q :=
  Equiv.ofBijective
    (caseThreeFiberAssembly hqpos hq)
    ⟨caseThreeFiberAssembly_injective hqpos hq,
      caseThreeFiberAssembly_surjective hqpos hq⟩

@[simp]
theorem caseThreeFiberEquiv_apply
    {m q : ℕ} (hqpos : 1 ≤ q) (hq : 2 * q ≤ m + 1)
    (data : CaseThreeAssemblyData m q) :
    (caseThreeFiberEquiv hqpos hq data).1 =
      assembleCaseThreeSubtype hqpos hq
        data.1.1 data.2 data.1.2 :=
  rfl

/-- Reindex a sum over the fixed-`q` ambient fibre by the independent
non-split prefix and remainder data, with no multiplicity factor. -/
theorem sum_caseThreeFiber_equiv
    {m q : ℕ} (hqpos : 1 ≤ q) (hq : 2 * q ≤ m + 1)
    {R : Type*} [AddCommMonoid R]
    (f :
      {κ : PartialPairing (Fin (m + 1)) //
        HeadPairedWithPrefix κ} → R) :
    (∑ K : CaseThreeFiber m q, f K.1) =
      ∑ data : CaseThreeAssemblyData m q,
        f (assembleCaseThreeSubtype hqpos hq
          data.1.1 data.2 data.1.2) := by
  simpa only [caseThreeFiberEquiv_apply] using
    ((caseThreeFiberEquiv hqpos hq).sum_comp
      (fun K : CaseThreeFiber m q => f K.1)).symm

/-- Filtered form used directly after `sum_caseThree_by_q`: the fibre
filter is exactly the independent prefix--tail product. -/
theorem sum_caseThree_filter_equiv
    {m q : ℕ} (hqpos : 1 ≤ q) (hq : 2 * q ≤ m + 1)
    {R : Type*} [AddCommMonoid R]
    (f :
      {κ : PartialPairing (Fin (m + 1)) //
        HeadPairedWithPrefix κ} → R) :
    (∑ K ∈ Finset.univ.filter
        (fun K :
          {κ : PartialPairing (Fin (m + 1)) //
            HeadPairedWithPrefix κ} =>
          caseThreeQ K = q),
        f K) =
      ∑ σ :
          {σ : PartialPairing (Fin (2 * q)) //
            IsNonSplit σ},
        ∑ τ : PartialPairing (Fin (m + 1 - 2 * q)),
          f (assembleCaseThreeSubtype hqpos hq
            σ.1 τ σ.2) := by
  calc
    _ = ∑ K : CaseThreeFiber m q, f K.1 := by
      apply Finset.sum_subtype
      intro K
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    _ = ∑ data : CaseThreeAssemblyData m q,
        f (assembleCaseThreeSubtype hqpos hq
          data.1.1 data.2 data.1.2) :=
      sum_caseThreeFiber_equiv hqpos hq f
    _ = _ := by
      rw [Fintype.sum_prod_type]

/-! ### Support bookkeeping for the assembled pairing -/

@[simp]
theorem appendPairingTo_prefix_mem_singles
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (i : Fin a) :
    Fin.castLE ha i ∈ (appendPairingTo ha σ τ).singles ↔
      i ∈ σ.singles := by
  simp only [mem_singles, appendPairingTo_apply_prefix]
  constructor
  · intro h
    apply Fin.ext
    exact congrArg (fun k : Fin N => k.val) h
  · intro h
    rw [h]

@[simp]
theorem appendPairingTo_suffix_mem_singles
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (j : Fin (N - a)) :
    suffixFin ha j ∈ (appendPairingTo ha σ τ).singles ↔
      j ∈ τ.singles := by
  simp only [mem_singles, appendPairingTo_apply_suffix]
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [suffixFin_val] at hv
    omega
  · intro h
    rw [h]

@[simp]
theorem appendPairingTo_prefix_mem_pairSupport
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (i : Fin a) :
    Fin.castLE ha i ∈ (appendPairingTo ha σ τ).pairSupport ↔
      i ∈ σ.pairSupport := by
  simp only [mem_pairSupport, appendPairingTo_apply_prefix]
  constructor
  · intro hne heq
    apply hne
    rw [heq]
  · intro hne heq
    apply hne
    apply Fin.ext
    exact congrArg (fun k : Fin N => k.val) heq

@[simp]
theorem appendPairingTo_suffix_mem_pairSupport
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (j : Fin (N - a)) :
    suffixFin ha j ∈ (appendPairingTo ha σ τ).pairSupport ↔
      j ∈ τ.pairSupport := by
  simp only [mem_pairSupport, appendPairingTo_apply_suffix]
  constructor
  · intro hne heq
    apply hne
    rw [heq]
  · intro hne heq
    apply hne
    apply Fin.ext
    have hv := congrArg (fun k : Fin N => k.val) heq
    simp only [suffixFin_val] at hv
    omega

@[simp]
theorem appendPairingTo_prefix_lt_apply
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (i : Fin a) :
    Fin.castLE ha i <
        appendPairingTo ha σ τ (Fin.castLE ha i) ↔
      i < σ i := by
  rw [appendPairingTo_apply_prefix]
  rfl

@[simp]
theorem appendPairingTo_suffix_lt_apply
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (j : Fin (N - a)) :
    suffixFin ha j <
        appendPairingTo ha σ τ (suffixFin ha j) ↔
      j < τ j := by
  rw [appendPairingTo_apply_suffix]
  change a + j.val < a + (τ j).val ↔ j.val < (τ j).val
  omega

/-- Consecutive prefix--suffix decomposition of `Fin N`. -/
def prefixSuffixEquiv {N a : ℕ} (ha : a ≤ N) :
    Fin a ⊕ Fin (N - a) ≃ Fin N :=
  finSumFinEquiv.trans
    (Fin.castOrderIso (by omega : a + (N - a) = N)).toEquiv

@[simp]
theorem prefixSuffixEquiv_apply_left
    {N a : ℕ} (ha : a ≤ N) (i : Fin a) :
    prefixSuffixEquiv ha (Sum.inl i) = Fin.castLE ha i := by
  apply Fin.ext
  rfl

@[simp]
theorem prefixSuffixEquiv_apply_right
    {N a : ℕ} (ha : a ≤ N) (j : Fin (N - a)) :
    prefixSuffixEquiv ha (Sum.inr j) = suffixFin ha j := by
  apply Fin.ext
  rfl

/-- Split a product over a finite ordinal into consecutive prefix and
suffix products. -/
theorem prod_prefix_suffix
    {N a : ℕ} (ha : a ≤ N)
    {R : Type*} [CommMonoid R] (f : Fin N → R) :
    (∏ i : Fin N, f i) =
      (∏ i : Fin a, f (Fin.castLE ha i)) *
        ∏ j : Fin (N - a), f (suffixFin ha j) := by
  rw [← (prefixSuffixEquiv ha).prod_comp f]
  rw [Fintype.prod_sum_type]
  simp only [prefixSuffixEquiv_apply_left,
    prefixSuffixEquiv_apply_right]

/-- Products indexed by oriented pairs split over an appended pairing.
This is the covariance-product ledger used by the case-(3) closed form. -/
theorem prod_orientedPairSupport_appendPairingTo
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    {R : Type*} [CommMonoid R]
    (F : Fin N → Fin N → R) :
    (∏ k ∈
        (appendPairingTo ha σ τ).pairSupport.filter
          (fun k => k < appendPairingTo ha σ τ k),
        F k (appendPairingTo ha σ τ k)) =
      (∏ i ∈ σ.pairSupport.filter (fun i => i < σ i),
          F (Fin.castLE ha i) (Fin.castLE ha (σ i))) *
        ∏ j ∈ τ.pairSupport.filter (fun j => j < τ j),
          F (suffixFin ha j) (suffixFin ha (τ j)) := by
  classical
  rw [← Finset.prod_ite_mem_eq]
  rw [prod_prefix_suffix ha]
  have hp (i : Fin a) :
      Fin.castLE ha i < Fin.castLE ha (σ i) ↔ i < σ i :=
    Iff.rfl
  have hs (j : Fin (N - a)) :
      suffixFin ha j < suffixFin ha (τ j) ↔ j < τ j := by
    change a + j.val < a + (τ j).val ↔ j.val < (τ j).val
    omega
  have hmp (i : Fin a) :
      (i ∈ σ.pairSupport ∧ i < σ i) ↔
        i ∈ σ.pairSupport.filter (fun k => k < σ k) := by
    simp only [Finset.mem_filter]
  have hms (j : Fin (N - a)) :
      (j ∈ τ.pairSupport ∧ j < τ j) ↔
        j ∈ τ.pairSupport.filter (fun k => k < τ k) := by
    simp only [Finset.mem_filter]
  simp only [Finset.mem_filter,
    appendPairingTo_prefix_mem_pairSupport,
    appendPairingTo_suffix_mem_pairSupport,
    appendPairingTo_apply_prefix,
    appendPairingTo_apply_suffix,
    hp, hs]
  simp only [hmp, hms]
  rw [Finset.prod_ite_mem_eq, Finset.prod_ite_mem_eq]

/-- If the prefix pairing is full, every single of the appended pairing
lies uniquely in the suffix. -/
def appendSinglesEquiv
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (hσ : σ.IsFull) :
    {k : Fin N // k ∈ (appendPairingTo ha σ τ).singles} ≃
      {j : Fin (N - a) // j ∈ τ.singles} where
  toFun k := by
    have hge : a ≤ k.1.val := by
      apply Nat.le_of_not_gt
      intro hlt
      let i : Fin a := ⟨k.1.val, hlt⟩
      have hcast : Fin.castLE ha i = k.1 := Fin.ext rfl
      have hsingle :
          i ∈ σ.singles := by
        rw [← appendPairingTo_prefix_mem_singles ha σ τ i]
        simpa only [hcast] using k.2
      exact hσ i (mem_singles.mp hsingle)
    let j : Fin (N - a) :=
      ⟨k.1.val - a, by omega⟩
    have hsuffix : suffixFin ha j = k.1 := by
      apply Fin.ext
      simp only [suffixFin_val]
      dsimp [j]
      omega
    exact
      ⟨j, (appendPairingTo_suffix_mem_singles
        ha σ τ j).mp (by simpa only [hsuffix] using k.2)⟩
  invFun j :=
    ⟨suffixFin ha j.1,
      (appendPairingTo_suffix_mem_singles
        ha σ τ j.1).mpr j.2⟩
  left_inv k := by
    apply Subtype.ext
    apply Fin.ext
    simp only [suffixFin_val]
    have hge : a ≤ k.1.val := by
      by_contra hnot
      have hlt : k.1.val < a := Nat.lt_of_not_ge hnot
      let i : Fin a := ⟨k.1.val, hlt⟩
      have hcast : Fin.castLE ha i = k.1 := Fin.ext rfl
      have hsingle :
          i ∈ σ.singles := by
        rw [← appendPairingTo_prefix_mem_singles ha σ τ i]
        simpa only [hcast] using k.2
      exact hσ i (mem_singles.mp hsingle)
    omega
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    simp only [suffixFin_val]
    omega

@[simp]
theorem appendSinglesEquiv_symm_apply_val
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (hσ : σ.IsFull)
    (j : {j : Fin (N - a) // j ∈ τ.singles}) :
    ((appendSinglesEquiv ha σ τ hσ).symm j).1 =
      suffixFin ha j.1 :=
  rfl

@[simp]
theorem appendSinglesEquiv_apply_val
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (hσ : σ.IsFull)
    (i :
      {i : Fin N // i ∈ (appendPairingTo ha σ τ).singles}) :
    ((appendSinglesEquiv ha σ τ hσ i).1).val =
      i.1.val - a :=
  rfl

theorem appendSinglesEquiv_lt_iff
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (hσ : σ.IsFull)
    (i j :
      {i : Fin N // i ∈ (appendPairingTo ha σ τ).singles}) :
    appendSinglesEquiv ha σ τ hσ i <
        appendSinglesEquiv ha σ τ hσ j ↔
      i < j := by
  change i.1.val - a < j.1.val - a ↔ i.1.val < j.1.val
  have hi : a ≤ i.1.val := by
    by_contra hnot
    have hlt : i.1.val < a := Nat.lt_of_not_ge hnot
    let k : Fin a := ⟨i.1.val, hlt⟩
    have hcast : Fin.castLE ha k = i.1 := Fin.ext rfl
    have hsingle :
        k ∈ σ.singles := by
      rw [← appendPairingTo_prefix_mem_singles ha σ τ k]
      simpa only [hcast] using i.2
    exact hσ k (mem_singles.mp hsingle)
  have hj : a ≤ j.1.val := by
    by_contra hnot
    have hlt : j.1.val < a := Nat.lt_of_not_ge hnot
    let k : Fin a := ⟨j.1.val, hlt⟩
    have hcast : Fin.castLE ha k = j.1 := Fin.ext rfl
    have hsingle :
        k ∈ σ.singles := by
      rw [← appendPairingTo_prefix_mem_singles ha σ τ k]
      simpa only [hcast] using j.2
    exact hσ k (mem_singles.mp hsingle)
  omega

/-- With a full appended prefix, the Wick factor is exactly the Wick
factor of the suffix pairing.  Only the values of the two tuples at
suffix variables have to agree. -/
theorem wickAt_appendPairingTo
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (hσ : σ.IsFull)
    (xt : Fin (N + 2) → T4)
    (yt : Fin (N - a + 2) → T4)
    (hxt : ∀ j : Fin (N - a),
      xt (varIdx (suffixFin ha j)) = yt (varIdx j))
    (ω : M.Ω) :
    wickAt M ρ ε (appendPairingTo ha σ τ) xt ω =
      wickAt M ρ ε τ yt ω := by
  rw [wickAt_eq_explicitPartialPairingWick,
    wickAt_eq_explicitPartialPairingWick]
  let e := appendSinglesEquiv ha σ τ hσ
  have hlabels :
      (fun i :
          {i : Fin N //
            i ∈ (appendPairingTo ha σ τ).singles} =>
        xt (varIdx i.1)) =
        (fun j : {j : Fin (N - a) // j ∈ τ.singles} =>
          yt (varIdx j.1)) ∘ e := by
    funext i
    have hsuffix :
        suffixFin ha (e i).1 = i.1 := by
      calc
        suffixFin ha (e i).1 =
            (e.symm (e i)).1 := by
          rw [appendSinglesEquiv_symm_apply_val]
        _ = i.1 :=
          congrArg Subtype.val (e.symm_apply_apply i)
    change xt (varIdx i.1) = yt (varIdx (e i).1)
    rw [← hxt (e i).1, hsuffix]
  rw [hlabels]
  exact
    (explicitPartialPairingWickBy_congr
      (fun i j :
        {i : Fin N //
          i ∈ (appendPairingTo ha σ τ).singles} => i < j)
      (fun i j :
        {j : Fin (N - a) // j ∈ τ.singles} => i < j)
      e
      (appendSinglesEquiv_lt_iff ha σ τ hσ)
      (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
      (fun x ω' => M.xiEps ρ ε ω' x)
      (fun j : {j : Fin (N - a) // j ∈ τ.singles} =>
        yt (varIdx j.1))
      ω).symm

@[simp]
theorem appendPairing_castAdd_mem_singles
    {a b : ℕ} (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin b)) (i : Fin a) :
    Fin.castAdd b i ∈ (appendPairing σ τ).singles ↔
      i ∈ σ.singles := by
  simp only [mem_singles, appendPairing_apply_castAdd]
  constructor
  · intro h
    apply Fin.ext
    exact congrArg (fun k : Fin (a + b) => k.val) h
  · intro h
    rw [h]

@[simp]
theorem appendPairing_natAdd_mem_singles
    {a b : ℕ} (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin b)) (j : Fin b) :
    Fin.natAdd a j ∈ (appendPairing σ τ).singles ↔
      j ∈ τ.singles := by
  simp only [mem_singles, appendPairing_apply_natAdd]
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg (fun k : Fin (a + b) => k.val) h
    change a + (τ j).val = a + j.val at hv
    omega
  · intro h
    rw [h]

/-- Singles equivalence for the arithmetic-exact `appendPairing`. -/
def appendPairingSinglesEquiv
    {a b : ℕ} (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin b)) (hσ : σ.IsFull) :
    {k : Fin (a + b) // k ∈ (appendPairing σ τ).singles} ≃
      {j : Fin b // j ∈ τ.singles} where
  toFun k := by
    have hge : a ≤ k.1.val := by
      apply Nat.le_of_not_gt
      intro hlt
      let i : Fin a := ⟨k.1.val, hlt⟩
      have hcast : Fin.castAdd b i = k.1 := Fin.ext rfl
      have hsingle :
          i ∈ σ.singles := by
        rw [← appendPairing_castAdd_mem_singles σ τ i]
        simpa only [hcast] using k.2
      exact hσ i (mem_singles.mp hsingle)
    let j : Fin b := ⟨k.1.val - a, by omega⟩
    have hnat : Fin.natAdd a j = k.1 := by
      apply Fin.ext
      dsimp [j]
      omega
    exact
      ⟨j, (appendPairing_natAdd_mem_singles
        σ τ j).mp (by simpa only [hnat] using k.2)⟩
  invFun j :=
    ⟨Fin.natAdd a j.1,
      (appendPairing_natAdd_mem_singles σ τ j.1).mpr j.2⟩
  left_inv k := by
    apply Subtype.ext
    apply Fin.ext
    have hge : a ≤ k.1.val := by
      by_contra hnot
      have hlt : k.1.val < a := Nat.lt_of_not_ge hnot
      let i : Fin a := ⟨k.1.val, hlt⟩
      have hcast : Fin.castAdd b i = k.1 := Fin.ext rfl
      have hsingle :
          i ∈ σ.singles := by
        rw [← appendPairing_castAdd_mem_singles σ τ i]
        simpa only [hcast] using k.2
      exact hσ i (mem_singles.mp hsingle)
    change a + (k.1.val - a) = k.1.val
    omega
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    change a + j.1.val - a = j.1.val
    omega

@[simp]
theorem appendPairingSinglesEquiv_symm_apply_val
    {a b : ℕ} (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin b)) (hσ : σ.IsFull)
    (j : {j : Fin b // j ∈ τ.singles}) :
    ((appendPairingSinglesEquiv σ τ hσ).symm j).1 =
      Fin.natAdd a j.1 :=
  rfl

@[simp]
theorem appendPairingSinglesEquiv_apply_val
    {a b : ℕ} (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin b)) (hσ : σ.IsFull)
    (i : {i : Fin (a + b) //
      i ∈ (appendPairing σ τ).singles}) :
    ((appendPairingSinglesEquiv σ τ hσ i).1).val =
      i.1.val - a :=
  rfl

theorem appendPairingSinglesEquiv_lt_iff
    {a b : ℕ} (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin b)) (hσ : σ.IsFull)
    (i j : {i : Fin (a + b) //
      i ∈ (appendPairing σ τ).singles}) :
    appendPairingSinglesEquiv σ τ hσ i <
        appendPairingSinglesEquiv σ τ hσ j ↔
      i < j := by
  change i.1.val - a < j.1.val - a ↔ i.1.val < j.1.val
  have hge (k : {i : Fin (a + b) //
      i ∈ (appendPairing σ τ).singles}) :
      a ≤ k.1.val := by
    by_contra hnot
    have hlt : k.1.val < a := Nat.lt_of_not_ge hnot
    let l : Fin a := ⟨k.1.val, hlt⟩
    have hcast : Fin.castAdd b l = k.1 := Fin.ext rfl
    have hsingle :
        l ∈ σ.singles := by
      rw [← appendPairing_castAdd_mem_singles σ τ l]
      simpa only [hcast] using k.2
    exact hσ l (mem_singles.mp hsingle)
  have hi := hge i
  have hj := hge j
  omega

/-- Direct `appendPairing` form of `wickAt_appendPairingTo`. -/
theorem wickAt_appendPairing
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {a b : ℕ}
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin b)) (hσ : σ.IsFull)
    (xt : Fin (a + b + 2) → T4)
    (yt : Fin (b + 2) → T4)
    (hxt : ∀ j : Fin b,
      xt (varIdx (Fin.natAdd a j)) = yt (varIdx j))
    (ω : M.Ω) :
    wickAt M ρ ε (appendPairing σ τ) xt ω =
      wickAt M ρ ε τ yt ω := by
  rw [wickAt_eq_explicitPartialPairingWick,
    wickAt_eq_explicitPartialPairingWick]
  let e := appendPairingSinglesEquiv σ τ hσ
  have hlabels :
      (fun i :
          {i : Fin (a + b) //
            i ∈ (appendPairing σ τ).singles} =>
        xt (varIdx i.1)) =
        (fun j : {j : Fin b // j ∈ τ.singles} =>
          yt (varIdx j.1)) ∘ e := by
    funext i
    have hnat :
        Fin.natAdd a (e i).1 = i.1 := by
      calc
        Fin.natAdd a (e i).1 =
            (e.symm (e i)).1 := by
          rw [appendPairingSinglesEquiv_symm_apply_val]
        _ = i.1 :=
          congrArg Subtype.val (e.symm_apply_apply i)
    change xt (varIdx i.1) = yt (varIdx (e i).1)
    rw [← hxt (e i).1, hnat]
  rw [hlabels]
  exact
    (explicitPartialPairingWickBy_congr
      (fun i j :
        {i : Fin (a + b) //
          i ∈ (appendPairing σ τ).singles} => i < j)
      (fun i j :
        {j : Fin b // j ∈ τ.singles} => i < j)
      e
      (appendPairingSinglesEquiv_lt_iff σ τ hσ)
      (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
      (fun x ω' => M.xiEps ρ ε ω' x)
      (fun j : {j : Fin b // j ∈ τ.singles} =>
        yt (varIdx j.1))
      ω).symm

/-! ### Spatial tuples for the case-(3) closed-form bridge -/

/-- Ambient internal variables in paper order:
`(z, u₁, …, u₂q, w, v₁, …, vᵣ)`. -/
def caseThreeAmbientInternal
    (q r : ℕ) (z w : T4)
    (t : Fin (2 * q + r) → T4) :
    Fin (2 * (q + 1) + r) → T4 :=
  Fin.append
    (detJTupleSucc q z w
      (fun i => t (Fin.castAdd r i)))
    (fun j => t (Fin.natAdd (2 * q) j))

@[simp]
theorem caseThreeAmbientInternal_prefix
    (q r : ℕ) (z w : T4)
    (t : Fin (2 * q + r) → T4)
    (i : Fin (2 * (q + 1))) :
    caseThreeAmbientInternal q r z w t
        (Fin.castAdd r i) =
      detJTupleSucc q z w
        (fun k => t (Fin.castAdd r k)) i := by
  simp only [caseThreeAmbientInternal, Fin.append_left]

@[simp]
theorem caseThreeAmbientInternal_suffix
    (q r : ℕ) (z w : T4)
    (t : Fin (2 * q + r) → T4)
    (j : Fin r) :
    caseThreeAmbientInternal q r z w t
        (Fin.natAdd (2 * (q + 1)) j) =
      t (Fin.natAdd (2 * q) j) := by
  simp only [caseThreeAmbientInternal, Fin.append_right]

/-- The suffix random tuple beginning at `w`. -/
def caseThreeTailTuple
    (q r : ℕ) (w y : T4)
    (t : Fin (2 * q + r) → T4) :
    Fin (r + 2) → T4 :=
  assemble w y (fun j => t (Fin.natAdd (2 * q) j))

/-- Wick factors of a case-(3) assembled pairing are precisely those of
the external tail. -/
theorem wickAt_caseThreeAmbient
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : σ.IsFull)
    (x z w y : T4)
    (t : Fin (2 * q + r) → T4)
    (ω : M.Ω) :
    wickAt M ρ ε
        (appendPairing σ τ)
        (assemble x y
          (caseThreeAmbientInternal q r z w t)) ω =
      wickAt M ρ ε τ
        (caseThreeTailTuple q r w y t) ω := by
  apply wickAt_appendPairing
    M ρ ε σ τ hσ
  intro j
  unfold caseThreeTailTuple
  rw [assemble_varIdx, assemble_varIdx]
  rw [caseThreeAmbientInternal_suffix]


end PartialPairing

end

end Anderson4D
