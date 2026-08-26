import Anderson4D.PermSum.Words

/-!
# Factorial ledger for the collapse coordinates

The inverse `((s+1)!)⁻¹` in (5.45) comes only from the normalization of
`paperSum`.  Collapsing all inside blocks to one marker introduces a marker
of multiplicity `k = s+1` in the contracted alphabet.  Consequently, the
product of the inside and contracted factorial ledgers is exactly `k!` times
the original ledger.

No fiber cardinality is used here.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open scoped BigOperators

/-- Multiplicity on a split alphabet. -/
def sumMultiplicity {A B : Type*}
    (a : A → ℕ) (b : B → ℕ) : A ⊕ B → ℕ
  | .inl x => a x
  | .inr y => b y

/-- Multiplicity on the contracted alphabet: one marker with multiplicity
`k`, and all outside multiplicities unchanged. -/
def markerMultiplicity {B : Type*}
    (k : ℕ) (b : B → ℕ) : Unit ⊕ B → ℕ
  | .inl _ => k
  | .inr y => b y

/-- A factorial product over a sum type splits exactly. -/
theorem factorialLedger_sum
    {A B : Type*} [Fintype A] [Fintype B]
    (a : A → ℕ) (b : B → ℕ) :
    (∏ x : A ⊕ B, ((sumMultiplicity a b x).factorial : ℝ)) =
      (∏ x : A, ((a x).factorial : ℝ)) *
        ∏ y : B, ((b y).factorial : ℝ) := by
  simp [sumMultiplicity, Fintype.prod_sum_type]

/-- The contracted ledger is the marker factorial times the outside
ledger. -/
theorem factorialLedger_marker
    {B : Type*} [Fintype B]
    (k : ℕ) (b : B → ℕ) :
    (∏ x : Unit ⊕ B, ((markerMultiplicity k b x).factorial : ℝ)) =
      (k.factorial : ℝ) * ∏ y : B, ((b y).factorial : ℝ) := by
  simp [markerMultiplicity, Fintype.prod_sum_type]

/-- **Collapse factorial ledger.**  Inside ledger times contracted ledger
equals the new marker factorial times the original ledger. -/
theorem collapse_factorialLedger
    {A B : Type*} [Fintype A] [Fintype B]
    (a : A → ℕ) (b : B → ℕ) (k : ℕ) :
    (∏ x : A, ((a x).factorial : ℝ)) *
        (∏ x : Unit ⊕ B,
          ((markerMultiplicity k b x).factorial : ℝ)) =
      (k.factorial : ℝ) *
        ∏ x : A ⊕ B,
          ((sumMultiplicity a b x).factorial : ℝ) := by
  rw [factorialLedger_sum, factorialLedger_marker]
  ring

/-- Division form used in (5.44)--(5.45).  This is the unique source of
`(k!)⁻¹`; the word-collapse map itself remains an honest equivalence. -/
theorem factorialLedger_sum_eq_inv_marker_mul
    {A B : Type*} [Fintype A] [Fintype B]
    (a : A → ℕ) (b : B → ℕ) (k : ℕ) :
    (∏ x : A ⊕ B,
        ((sumMultiplicity a b x).factorial : ℝ)) =
      (k.factorial : ℝ)⁻¹ *
        ((∏ x : A, ((a x).factorial : ℝ)) *
          ∏ x : Unit ⊕ B,
            ((markerMultiplicity k b x).factorial : ℝ)) := by
  have hk : (0 : ℝ) < k.factorial := by positivity
  rw [collapse_factorialLedger a b k]
  field_simp

end Anderson4D
