import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic

/-!
# Finite products of absolutely convergent series

This small utility expands a finite product of `tsum`s as one `tsum`
over mode assignments.  It is the deterministic Fubini lemma needed
to turn a product of cutoff covariances into a countable Fourier
configuration sum.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- Product of one term from each of `n` series. -/
def finSeriesAssignmentTerm
    {A : Type*} (n : ℕ) (f : Fin n → A → ℂ)
    (q : Fin n → A) : ℂ :=
  ∏ i, f i (q i)

/-- Absolute convergence is preserved when finitely many series are
expanded over all assignments of their indices. -/
theorem summable_norm_finSeriesAssignmentTerm
    {A : Type*} (n : ℕ) (f : Fin n → A → ℂ)
    (hf : ∀ i, Summable fun a => ‖f i a‖) :
    Summable fun q => ‖finSeriesAssignmentTerm n f q‖ := by
  induction n with
  | zero =>
      exact Summable.of_finite
  | succ n ih =>
      let fTail : Fin n → A → ℂ := fun i => f i.succ
      have hheadNorm :
          Summable fun a => ‖f 0 a‖ := hf 0
      have htailNorm :
          Summable fun q =>
            ‖finSeriesAssignmentTerm n fTail q‖ :=
        ih fTail (fun i => hf i.succ)
      have hpairNorm :
          Summable (fun p : A × (Fin n → A) =>
            ‖f 0 p.1‖ *
              ‖finSeriesAssignmentTerm n fTail p.2‖) :=
        @Summable.mul_of_nonneg A (Fin n → A)
          (fun a => ‖f 0 a‖)
          (fun q => ‖finSeriesAssignmentTerm n fTail q‖)
          hheadNorm htailNorm
          (fun _ => norm_nonneg _)
          (fun _ => norm_nonneg _)
      let e : A × (Fin n → A) ≃ (Fin (n + 1) → A) :=
        Fin.consEquiv fun _ => A
      apply (e.summable_iff).1
      exact hpairNorm.congr fun p => by
        change
          ‖f 0 p.1‖ *
              ‖finSeriesAssignmentTerm n fTail p.2‖ =
            ‖finSeriesAssignmentTerm (n + 1) f (e p)‖
        unfold finSeriesAssignmentTerm fTail e
        rw [Fin.prod_univ_succ]
        rw [norm_mul]
        rfl

/-- In particular the finite assignment series itself is summable. -/
theorem summable_finSeriesAssignmentTerm
    {A : Type*} (n : ℕ) (f : Fin n → A → ℂ)
    (hf : ∀ i, Summable fun a => ‖f i a‖) :
    Summable (finSeriesAssignmentTerm n f) :=
  Summable.of_norm
    (summable_norm_finSeriesAssignmentTerm n f hf)

/-- A finite product of `tsum`s is the `tsum` over all finite mode
assignments. -/
theorem tsum_finSeriesAssignmentTerm
    {A : Type*} (n : ℕ) (f : Fin n → A → ℂ)
    (hf : ∀ i, Summable fun a => ‖f i a‖) :
    (∑' q : Fin n → A,
        finSeriesAssignmentTerm n f q) =
      ∏ i : Fin n, ∑' a : A, f i a := by
  induction n with
  | zero =>
      simp [finSeriesAssignmentTerm]
  | succ n ih =>
      let fTail : Fin n → A → ℂ := fun i => f i.succ
      have hhead : Summable (f 0) :=
        Summable.of_norm (hf 0)
      have htail :
          Summable (finSeriesAssignmentTerm n fTail) :=
        summable_finSeriesAssignmentTerm n fTail
          (fun i => hf i.succ)
      have hpairNorm :
          Summable (fun p : A × (Fin n → A) =>
            ‖f 0 p.1‖ *
              ‖finSeriesAssignmentTerm n fTail p.2‖) :=
        @Summable.mul_of_nonneg A (Fin n → A)
          (fun a => ‖f 0 a‖)
          (fun q => ‖finSeriesAssignmentTerm n fTail q‖)
          (hf 0)
          (summable_norm_finSeriesAssignmentTerm n fTail
            (fun i => hf i.succ))
          (fun _ => norm_nonneg _)
          (fun _ => norm_nonneg _)
      have hpair :
          Summable fun p : A × (Fin n → A) =>
            f 0 p.1 *
              finSeriesAssignmentTerm n fTail p.2 := by
        apply Summable.of_norm
        exact hpairNorm.congr fun p => by rw [norm_mul]
      let e : A × (Fin n → A) ≃ (Fin (n + 1) → A) :=
        Fin.consEquiv fun _ => A
      calc
        (∑' q : Fin (n + 1) → A,
            finSeriesAssignmentTerm (n + 1) f q) =
            ∑' p : A × (Fin n → A),
              finSeriesAssignmentTerm (n + 1) f (e p) := by
          exact (e.tsum_eq
            (finSeriesAssignmentTerm (n + 1) f)).symm
        _ = ∑' p : A × (Fin n → A),
              f 0 p.1 *
                finSeriesAssignmentTerm n fTail p.2 := by
          apply tsum_congr
          intro p
          unfold finSeriesAssignmentTerm fTail e
          rw [Fin.prod_univ_succ]
          rfl
        _ = (∑' a : A, f 0 a) *
              ∑' q : Fin n → A,
                finSeriesAssignmentTerm n fTail q :=
          (hhead.tsum_mul_tsum htail hpair).symm
        _ = (∑' a : A, f 0 a) *
              ∏ i : Fin n, ∑' a : A, fTail i a := by
          rw [ih fTail (fun i => hf i.succ)]
        _ = ∏ i : Fin (n + 1), ∑' a : A, f i a := by
          rw [Fin.prod_univ_succ]

end

end Anderson4D
