import Anderson4D.PermSum.Words

/-!
# Factorial normalization across run compression

`paperSum` carries the labeled-copy factorial ledger.  When the
multiplicity changes from `ml` to `sl`, the quotient of the two ledgers
converts the compressed `paperSum` back to the original normalization.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open scoped BigOperators

noncomputable section

/-- Quotient of the original and compressed labeled-copy ledgers. -/
def mergeLedgerRatio
    {α : Type*} [Fintype α]
    (ml sl : α → ℕ) : ℝ :=
  ∏ a : α,
    ((ml a).factorial : ℝ) /
      ((sl a).factorial : ℝ)

theorem mergeLedgerRatio_nonneg
    {α : Type*} [Fintype α]
    (ml sl : α → ℕ) :
    0 ≤ mergeLedgerRatio ml sl := by
  unfold mergeLedgerRatio
  positivity

/-- The quotient ledger times the compressed `paperSum` is the original
factorial product times the compressed raw word sum. -/
theorem mergeLedgerRatio_mul_paperSum
    {α : Type*} [Fintype α] [DecidableEq α]
    {M : ℕ} (ml sl : α → ℕ)
    (F : (Fin M → α) → ℝ) :
    mergeLedgerRatio ml sl * paperSum sl F =
      (∏ a : α, ((ml a).factorial : ℝ)) *
        wordSum sl F := by
  have hledger :
      mergeLedgerRatio ml sl *
          (∏ a : α, ((sl a).factorial : ℝ)) =
        ∏ a : α, ((ml a).factorial : ℝ) := by
    unfold mergeLedgerRatio
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro a _
    field_simp
  unfold paperSum
  calc
    mergeLedgerRatio ml sl *
          ((∏ a : α, ((sl a).factorial : ℝ)) *
            wordSum sl F) =
        (mergeLedgerRatio ml sl *
          ∏ a : α, ((sl a).factorial : ℝ)) *
            wordSum sl F := by ring
    _ = (∏ a : α, ((ml a).factorial : ℝ)) *
          wordSum sl F := by rw [hledger]

end

end Anderson4D
