import Anderson4D.PermSum.CollapseData
import Anderson4D.PermSum.CollapseSum

/-!
# Alphabet transport for collapse sums

The structural leaf decomposition is an equivalence

`HeppLeaf t ≃ InsideLeaf r ⊕ OutsideLeaf r`.

This file proves that `validWords`, `wordSum`, and the definitional
`paperSum` are invariant under an arbitrary finite alphabet equivalence, and
then specializes the construction to that leaf decomposition.
-/

namespace Anderson4D

open scoped BigOperators

set_option warningAsError true
set_option autoImplicit false

noncomputable section

variable {α β : Type*}

/-- Transport a multiplicity function covariantly along an equivalence. -/
def renameMultiplicity (e : α ≃ β) (mult : α → ℕ) : β → ℕ :=
  fun b => mult (e.symm b)

@[simp]
theorem renameMultiplicity_apply (e : α ≃ β) (mult : α → ℕ) (a : α) :
    renameMultiplicity e mult (e a) = mult a := by
  simp [renameMultiplicity]

/-- Apply an alphabet equivalence pointwise to a finite word. -/
def wordRenameEquiv (e : α ≃ β) (n : ℕ) :
    (Fin n → α) ≃ (Fin n → β) where
  toFun w i := e (w i)
  invFun w i := e.symm (w i)
  left_inv w := by
    funext i
    simp
  right_inv w := by
    funext i
    simp

@[simp]
theorem wordRenameEquiv_apply (e : α ≃ β) (n : ℕ)
    (w : Fin n → α) (i : Fin n) :
    wordRenameEquiv e n w i = e (w i) :=
  rfl

@[simp]
theorem wordRenameEquiv_symm_apply (e : α ≃ β) (n : ℕ)
    (w : Fin n → β) (i : Fin n) :
    (wordRenameEquiv e n).symm w i = e.symm (w i) :=
  rfl

/-- Prescribed fiber cardinalities are invariant under renaming letters. -/
theorem wordRename_mem_validWords_iff
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {n : ℕ} (e : α ≃ β) (mult : α → ℕ) (w : Fin n → α) :
    wordRenameEquiv e n w ∈ validWords (renameMultiplicity e mult) ↔
      w ∈ validWords mult := by
  rw [validWords, validWords]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h a
    have ha := h (e a)
    simpa only [wordRenameEquiv_apply, renameMultiplicity_apply,
      e.apply_eq_iff_eq] using ha
  · intro h b
    have hb := h (e.symm b)
    simpa only [wordRenameEquiv_apply, renameMultiplicity,
      Equiv.apply_eq_iff_eq_symm_apply] using hb

/-- The product of multiplicity factorials is invariant under renaming the
finite alphabet. -/
theorem factorialLedger_rename
    [Fintype α] [Fintype β]
    (e : α ≃ β) (mult : α → ℕ) :
    (∏ b : β, ((renameMultiplicity e mult b).factorial : ℝ)) =
      ∏ a : α, ((mult a).factorial : ℝ) := by
  have h :=
    Equiv.prod_comp e
      (fun b : β => ((renameMultiplicity e mult b).factorial : ℝ))
  simpa only [renameMultiplicity_apply] using h.symm

/-- Raw word sums are unchanged by a finite alphabet equivalence. -/
theorem wordSum_rename
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {n : ℕ} (e : α ≃ β) (mult : α → ℕ)
    (F : (Fin n → α) → ℝ) :
    wordSum mult F =
      wordSum (renameMultiplicity e mult)
        (fun w => F ((wordRenameEquiv e n).symm w)) := by
  classical
  let E := wordRenameEquiv e n
  let G : (Fin n → β) → ℝ :=
    fun w =>
      if w ∈ validWords (renameMultiplicity e mult) then
        F (E.symm w)
      else 0
  unfold wordSum
  calc
    (∑ w ∈ validWords mult, F w) =
        ∑ w : Fin n → α,
          if w ∈ validWords mult then F w else 0 := by
      simp
    _ = ∑ w : Fin n → α, G (E w) := by
      apply Fintype.sum_congr
      intro w
      change
        (if w ∈ validWords mult then F w else 0) =
          if E w ∈ validWords (renameMultiplicity e mult) then
            F (E.symm (E w))
          else 0
      rw [E.symm_apply_apply]
      have hvalid :=
        wordRename_mem_validWords_iff e mult w
      by_cases hw : w ∈ validWords mult
      · rw [if_pos hw, if_pos (hvalid.mpr hw)]
      · have hnot :
            E w ∉ validWords (renameMultiplicity e mult) :=
          fun h => hw (hvalid.mp h)
        rw [if_neg hw, if_neg hnot]
    _ = ∑ w : Fin n → β, G w :=
      Equiv.sum_comp E G
    _ = ∑ w ∈ validWords (renameMultiplicity e mult),
        F (E.symm w) := by
      simp [G]

/-- The definitional paper sum is invariant under the same renaming. -/
theorem paperSum_rename
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {n : ℕ} (e : α ≃ β) (mult : α → ℕ)
    (F : (Fin n → α) → ℝ) :
    paperSum mult F =
      paperSum (renameMultiplicity e mult)
        (fun w => F ((wordRenameEquiv e n).symm w)) := by
  unfold paperSum
  rw [factorialLedger_rename e mult, wordSum_rename e mult F]

/-! ## The Hepp-leaf split alphabet -/

open PlaneTree

/-- Original leaf multiplicities expressed on the canonical inside/outside
sum alphabet. -/
def splitLeafMultiplicity {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t) :
    InsideLeaf r ⊕ OutsideLeaf r → ℕ :=
  renameMultiplicity (leafInsideOutsideEquiv r) (leafMultiplicity mu)

@[simp]
theorem splitLeafMultiplicity_inl {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t) (l : InsideLeaf r) :
    splitLeafMultiplicity mu r (.inl l) = leafMultiplicity mu l.1 := by
  rfl

@[simp]
theorem splitLeafMultiplicity_inr {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t) (l : OutsideLeaf r) :
    splitLeafMultiplicity mu r (.inr l) = leafMultiplicity mu l.1 := by
  rfl

/-- The original leaf word renamed to the inside/outside sum alphabet. -/
def splitLeafWordEquiv {t : PlaneTree} (r : VPos t) (n : ℕ) :
    (Fin n → HeppLeaf t) ≃
      (Fin n → InsideLeaf r ⊕ OutsideLeaf r) :=
  wordRenameEquiv (leafInsideOutsideEquiv r) n

/-- Tree-facing alphabet split for arbitrary paper-sum statistics. -/
theorem paperSum_eq_splitLeafAlphabet
    {t : PlaneTree} {n : ℕ}
    (mu : Multiplicities t) (r : VPos t)
    (F : (Fin n → HeppLeaf t) → ℝ) :
    paperSum (leafMultiplicity mu) F =
      paperSum (splitLeafMultiplicity mu r)
        (fun w => F ((splitLeafWordEquiv r n).symm w)) := by
  exact paperSum_rename (leafInsideOutsideEquiv r)
    (leafMultiplicity mu) F

end

end Anderson4D
