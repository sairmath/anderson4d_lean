import Anderson4D.Combinatorics.Pairing

/-!
# Head recursion for partial pairings

This file classifies a partial pairing after adjoining one distinguished
index.  The distinguished index is either fixed, or it is paired with a
unique old index and the remaining involution lives on the complement of
that partner.  This is the finite combinatorial split used by the
creation--contraction recursion for Wick products.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

namespace PartialPairing

variable {α : Type*}

/-- Adjoin a new fixed point to a partial pairing. -/
def optionFixed (κ : PartialPairing α) : PartialPairing (Option α) where
  toFun
    | none => none
    | some i => some (κ i)
  involutive
    | none => rfl
    | some i => by simp

@[simp]
theorem optionFixed_none (κ : PartialPairing α) :
    optionFixed κ none = none := rfl

@[simp]
theorem optionFixed_some (κ : PartialPairing α) (i : α) :
    optionFixed κ (some i) = some (κ i) := rfl

variable [DecidableEq α]

/-- Pair the new point with `j`, and use `κ` on the complement of `j`. -/
def optionPaired (j : α) (κ : PartialPairing {i : α // i ≠ j}) :
    PartialPairing (Option α) := by
  classical
  refine
    { toFun := fun
        | none => some j
        | some i =>
            if h : i = j then none else some (κ ⟨i, h⟩).1
      involutive := ?_ }
  intro o
  cases o with
  | none => simp
  | some i =>
      by_cases h : i = j
      · subst i
        simp
      · have hκ : (κ ⟨i, h⟩).1 ≠ j := (κ ⟨i, h⟩).2
        simp [h, hκ]

@[simp]
theorem optionPaired_none (j : α)
    (κ : PartialPairing {i : α // i ≠ j}) :
    optionPaired j κ none = some j := rfl

@[simp]
theorem optionPaired_partner (j : α)
    (κ : PartialPairing {i : α // i ≠ j}) :
    optionPaired j κ (some j) = none := by
  simp [optionPaired]

@[simp]
theorem optionPaired_some_ne (j : α)
    (κ : PartialPairing {i : α // i ≠ j})
    (i : α) (hi : i ≠ j) :
    optionPaired j κ (some i) = some (κ ⟨i, hi⟩).1 := by
  simp [optionPaired, hi]

/-- The complement of `none` in `Option α` is canonically `α`. -/
def optionFixedComplEquiv :
    {o : Option α // o ∉ ({none} : Finset (Option α))} ≃ α where
  toFun o :=
    o.1.get (Option.isSome_iff_ne_none.mpr
      (fun h => o.2 (by simp [h])))
  invFun i := ⟨some i, by simp⟩
  left_inv o := by
    apply Subtype.ext
    exact Option.some_get _
  right_inv i := rfl

omit [DecidableEq α] in
@[simp]
theorem optionFixedComplEquiv_symm_apply (i : α) :
    (optionFixedComplEquiv (α := α)).symm i = ⟨some i, by simp⟩ :=
  rfl

/-- The complement of `none` and `some j` is canonically the complement
of `j` in `α`. -/
def optionPairedComplEquiv (j : α) :
    {o : Option α // o ∉ ({none, some j} : Finset (Option α))} ≃
      {i : α // i ≠ j} where
  toFun o :=
    let ho : o.1.isSome :=
      Option.isSome_iff_ne_none.mpr (fun h => o.2 (by simp [h]))
    ⟨o.1.get ho, by
      intro hj
      apply o.2
      have hs : some (o.1.get ho) = o.1 := Option.some_get ho
      rw [← hs, hj]
      simp⟩
  invFun i := ⟨some i.1, by simp [i.2]⟩
  left_inv o := by
    apply Subtype.ext
    exact Option.some_get _
  right_inv i := by
    apply Subtype.ext
    rfl

@[simp]
theorem optionPairedComplEquiv_symm_apply (j : α)
    (i : {i : α // i ≠ j}) :
    (optionPairedComplEquiv j).symm i =
      ⟨some i.1, by simp [i.2]⟩ :=
  rfl

/-- Removing a fixed new point leaves a pairing of the old carrier. -/
def optionTailOfFixed (κ : PartialPairing (Option α))
    (hκ : κ none = none) : PartialPairing α :=
  PartialPairing.congr optionFixedComplEquiv
    (κ.restrictCompl (by
      intro o ho
      have : o = none := by simpa using ho
      subst o
      simp [hκ]))

omit [DecidableEq α] in
@[simp]
theorem optionTailOfFixed_apply (κ : PartialPairing (Option α))
    (hκ : κ none = none) (i : α) :
    some (optionTailOfFixed κ hκ i) = κ (some i) := by
  rw [optionTailOfFixed, congr_apply_apply]
  simp only [optionFixedComplEquiv_symm_apply]
  cases h : κ (some i) with
  | none =>
      have happ := congrArg κ h
      rw [κ.apply_apply, hκ] at happ
      contradiction
  | some a =>
      change some ((κ (some i)).get _) = some a
      exact (Option.some_get _).trans h

/-- Removing the new point and its partner leaves a pairing of the
complement of that partner. -/
def optionTailOfPaired (κ : PartialPairing (Option α)) (j : α)
    (hκ : κ none = some j) :
    PartialPairing {i : α // i ≠ j} :=
  PartialPairing.congr (optionPairedComplEquiv j)
    (κ.restrictCompl (by
      intro o ho
      simp only [Finset.mem_insert, Finset.mem_singleton] at ho ⊢
      rcases ho with rfl | rfl
      · exact Or.inr hκ
      · exact Or.inl (by
          rw [← hκ, κ.apply_apply])))

@[simp]
theorem optionTailOfPaired_apply (κ : PartialPairing (Option α))
    (j : α) (hκ : κ none = some j) (i : {i : α // i ≠ j}) :
    some (optionTailOfPaired κ j hκ i).1 = κ (some i.1) := by
  rw [optionTailOfPaired, congr_apply_apply]
  simp only [optionPairedComplEquiv_symm_apply]
  cases h : κ (some i.1) with
  | none =>
      have happ := congrArg κ h
      rw [κ.apply_apply, hκ] at happ
      exact False.elim (i.2 (Option.some.inj happ))
  | some a =>
      change some ((κ (some i.1)).get _) = some a
      exact (Option.some_get _).trans h

omit [DecidableEq α] in
/-- Reattaching a fixed head after removing it recovers the pairing. -/
theorem optionFixed_optionTailOfFixed
    (κ : PartialPairing (Option α)) (hκ : κ none = none) :
    optionFixed (optionTailOfFixed κ hκ) = κ := by
  apply PartialPairing.ext
  intro o
  cases o with
  | none =>
      exact hκ.symm
  | some i =>
      exact optionTailOfFixed_apply κ hκ i

omit [DecidableEq α] in
/-- Removing the fixed head adjoined by `optionFixed` recovers the tail. -/
theorem optionTailOfFixed_optionFixed (κ : PartialPairing α) :
    optionTailOfFixed (optionFixed κ) rfl = κ := by
  apply PartialPairing.ext
  intro i
  apply Option.some.inj
  rw [optionTailOfFixed_apply]
  rfl

/-- Reattaching a paired head and its partner after removing them recovers
the pairing. -/
theorem optionPaired_optionTailOfPaired
    (κ : PartialPairing (Option α)) (j : α)
    (hκ : κ none = some j) :
    optionPaired j (optionTailOfPaired κ j hκ) = κ := by
  apply PartialPairing.ext
  intro o
  cases o with
  | none =>
      exact hκ.symm
  | some i =>
      by_cases hi : i = j
      · subst i
        rw [optionPaired_partner, ← hκ, κ.apply_apply]
      · rw [optionPaired_some_ne _ _ _ hi]
        exact optionTailOfPaired_apply κ j hκ ⟨i, hi⟩

/-- Removing the head and partner adjoined by `optionPaired` recovers the
complement pairing. -/
theorem optionTailOfPaired_optionPaired
    (j : α) (κ : PartialPairing {i : α // i ≠ j}) :
    optionTailOfPaired (optionPaired j κ) j
      (optionPaired_none j κ) = κ := by
  apply PartialPairing.ext
  intro i
  apply Subtype.ext
  have htail :=
    optionTailOfPaired_apply (optionPaired j κ) j
      (optionPaired_none j κ) i
  rw [optionPaired_some_ne j κ i.1 i.2] at htail
  exact Option.some.inj htail

/-- Classification map underlying `optionHeadEquiv`. -/
def optionHeadClassify :
    PartialPairing (Option α) →
      PartialPairing α ⊕
        ((j : α) × PartialPairing {i : α // i ≠ j}) :=
  fun κ =>
    match h : κ none with
    | none => Sum.inl (optionTailOfFixed κ h)
    | some j => Sum.inr ⟨j, optionTailOfPaired κ j h⟩

/-- Assembly map underlying `optionHeadEquiv`. -/
def optionHeadAssemble :
    (PartialPairing α ⊕
      ((j : α) × PartialPairing {i : α // i ≠ j})) →
      PartialPairing (Option α)
  | Sum.inl κ => optionFixed κ
  | Sum.inr d => optionPaired d.1 d.2

theorem optionHeadAssemble_classify
    (κ : PartialPairing (Option α)) :
    optionHeadAssemble (optionHeadClassify κ) = κ := by
  unfold optionHeadClassify
  split
  · rename_i h
    exact optionFixed_optionTailOfFixed κ h
  · rename_i j h
    exact optionPaired_optionTailOfPaired κ j h

theorem optionHeadClassify_assemble
    (s : PartialPairing α ⊕
      ((j : α) × PartialPairing {i : α // i ≠ j})) :
    optionHeadClassify (optionHeadAssemble s) = s := by
  cases s with
  | inl κ =>
      unfold optionHeadClassify optionHeadAssemble
      simp only [optionFixed_none]
      exact congrArg Sum.inl (optionTailOfFixed_optionFixed κ)
  | inr d =>
      rcases d with ⟨j, κ⟩
      unfold optionHeadClassify optionHeadAssemble
      simp only [optionPaired_none]
      exact congrArg Sum.inr
        (Sigma.ext rfl (by
          have htail := optionTailOfPaired_optionPaired j κ
          exact heq_of_eq htail))

/-- **Head classification equivalence.**  A pairing on `Option α` has
either a fixed head and a pairing on `α`, or a unique partner `j` and a
pairing on the complement of `j`. -/
def optionHeadEquiv :
    PartialPairing (Option α) ≃
      PartialPairing α ⊕
        ((j : α) × PartialPairing {i : α // i ≠ j}) where
  toFun := optionHeadClassify
  invFun := optionHeadAssemble
  left_inv := optionHeadAssemble_classify
  right_inv := optionHeadClassify_assemble

@[simp]
theorem optionHeadEquiv_symm_inl (κ : PartialPairing α) :
    optionHeadEquiv.symm (Sum.inl κ) = optionFixed κ :=
  rfl

@[simp]
theorem optionHeadEquiv_symm_inr
    (d : (j : α) × PartialPairing {i : α // i ≠ j}) :
    optionHeadEquiv.symm (Sum.inr d) = optionPaired d.1 d.2 :=
  rfl

/-- Finite-ordinal form of `optionHeadEquiv`: after identifying the new
zero of `Fin (n + 1)` with `none`, a pairing either fixes zero or pairs it
with a unique old index. -/
def finHeadEquiv (n : ℕ) :
    PartialPairing (Fin (n + 1)) ≃
      PartialPairing (Fin n) ⊕
        ((j : Fin n) × PartialPairing {i : Fin n // i ≠ j}) :=
  (PartialPairing.congr (finSuccEquiv n)).trans optionHeadEquiv

end PartialPairing

end

end Anderson4D
