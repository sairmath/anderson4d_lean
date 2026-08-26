import Anderson4D.ForMathlib.GaussianMoments

/-!
# Recursive Wick pairing sums

This file isolates the finite combinatorics used by Isserlis' theorem.  The
recursion pairs the first label with each remaining label exactly once and
then removes that partner.  Thus it enumerates labeled full pairings without
quotients or a choice of ordering inside each pair.

The constant-covariance specialization is proved to satisfy exactly the same
recurrence as the centered univariate Gaussian moments.  A later bridge
identifies this recursive presentation with the project's
`PartialPairing.IsFull` sum.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- Recursive sum of covariance products over all full pairings of a list of
labeled variables.  An odd list evaluates to zero because the recursion
eventually reaches a singleton. -/
def wickPairingList {α : Type*} (C : α → α → ℝ) : List α → ℝ
  | [] => 1
  | x :: xs =>
      ∑ j : Fin xs.length,
        C x (xs.get j) * wickPairingList C (xs.eraseIdx j)
termination_by xs => xs.length
decreasing_by
  simp_wf
  have := List.length_eraseIdx_add_one j.isLt
  omega

@[simp]
theorem wickPairingList_nil {α : Type*} (C : α → α → ℝ) :
    wickPairingList C [] = 1 := by
  rw [wickPairingList]

@[simp]
theorem wickPairingList_cons {α : Type*} (C : α → α → ℝ)
    (x : α) (xs : List α) :
    wickPairingList C (x :: xs) =
      ∑ j : Fin xs.length,
        C x (xs.get j) * wickPairingList C (xs.eraseIdx j) := by
  rw [wickPairingList]

@[simp]
theorem wickPairingList_singleton {α : Type*} (C : α → α → ℝ) (x : α) :
    wickPairingList C [x] = 0 := by
  simp

@[simp]
theorem wickPairingList_pair {α : Type*} (C : α → α → ℝ) (x y : α) :
    wickPairingList C [x, y] = C x y := by
  simp

/-- Recursive Wick sums vanish on lists of odd length. -/
theorem wickPairingList_odd_length {α : Type*} (C : α → α → ℝ) :
    ∀ (q : ℕ) (xs : List α), xs.length = 2 * q + 1 →
      wickPairingList C xs = 0 := by
  intro q
  induction q with
  | zero =>
      intro xs hxs
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp (by omega)
      simp
  | succ q ih =>
      intro xs hxs
      cases xs with
      | nil => simp at hxs
      | cons x tail =>
          rw [wickPairingList_cons]
          apply Finset.sum_eq_zero
          intro j _
          have herase : (tail.eraseIdx j).length = 2 * q + 1 := by
            simp only [List.length_cons] at hxs
            rw [List.length_eraseIdx_of_lt j.isLt]
            omega
          rw [ih (tail.eraseIdx j) herase, mul_zero]

/-- If every covariance entry equals `c`, the recursive full-pairing sum on
`2q` labels is `(2q-1)!! c^q`, with the double factorial represented by
`gaussianPairingCount`. -/
theorem wickPairingList_const_even {α : Type*} (c : ℝ) :
    ∀ (q : ℕ) (xs : List α), xs.length = 2 * q →
      wickPairingList (fun _ _ => c) xs =
        (gaussianPairingCount q : ℝ) * c ^ q := by
  intro q
  induction q with
  | zero =>
      intro xs hxs
      have : xs = [] := List.length_eq_zero_iff.mp (by omega)
      subst xs
      simp [gaussianPairingCount]
  | succ q ih =>
      intro xs hxs
      cases xs with
      | nil => simp at hxs
      | cons x tail =>
          rw [wickPairingList_cons]
          have htail : tail.length = 2 * q + 1 := by
            simp only [List.length_cons] at hxs
            omega
          have hterm (j : Fin tail.length) :
              wickPairingList (fun _ _ : α => c) (tail.eraseIdx j) =
                (gaussianPairingCount q : ℝ) * c ^ q := by
            apply ih
            have herase := List.length_eraseIdx_add_one j.isLt
            omega
          simp_rw [hterm]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, gaussianPairingCount]
          rw [htail]
          push_cast
          ring

/-- Full-pairing sum for a covariance matrix indexed by `Fin n`. -/
def wickPairingSum {n : ℕ} (C : Fin n → Fin n → ℝ) : ℝ :=
  wickPairingList C (List.ofFn id)

@[simp]
theorem wickPairingSum_zero (C : Fin 0 → Fin 0 → ℝ) :
    wickPairingSum C = 1 := by
  simp [wickPairingSum]

theorem wickPairingSum_odd (q : ℕ) (C : Fin (2 * q + 1) → Fin (2 * q + 1) → ℝ) :
    wickPairingSum C = 0 := by
  apply wickPairingList_odd_length C q
  simp

theorem wickPairingSum_const_even (q : ℕ) (c : ℝ) :
    wickPairingSum (n := 2 * q) (fun _ _ => c) =
      (gaussianPairingCount q : ℝ) * c ^ q := by
  apply wickPairingList_const_even c q
  simp

end

end Anderson4D
