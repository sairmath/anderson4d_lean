import Anderson4D.Probability.Chaos
import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# Algebraic orthogonality of multivariate Wick polynomials

This file proves the Wick-product orthogonality theorem from one transparent
Gaussian integration-by-parts interface.  The proof is polynomial and works
for a possibly degenerate covariance matrix.

The polynomial normal ordering is implemented by the creation operator

`Aₓ p = Xₓ p - Dₓ p`,

where `Dₓ` is the derivation sending `Xᵧ` to the covariance `C x y`.
The commutator identity and Gaussian integration by parts give

`E[(Aₓ p)q] = E[p(Dₓ q)]`.

Iterating this identity leaves exactly the recursive sum of cross
contractions and proves that different homogeneous Wick orders are
orthogonal.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory MvPolynomial
open scoped BigOperators

/-- Covariance-weighted derivation on the multivariate polynomial ring. -/
def covarianceDerivation {ι : Type*}
    (C : ι → ι → ℝ) (x : ι) :
    Derivation ℝ (MvPolynomial ι ℝ) (MvPolynomial ι ℝ) :=
  MvPolynomial.mkDerivation ℝ fun y => MvPolynomial.C (C x y)

@[simp]
theorem covarianceDerivation_X {ι : Type*}
    (C : ι → ι → ℝ) (x y : ι) :
    covarianceDerivation C x (MvPolynomial.X y) =
      MvPolynomial.C (C x y) := by
  rw [covarianceDerivation, MvPolynomial.mkDerivation_X]

@[simp]
theorem covarianceDerivation_C {ι : Type*}
    (C : ι → ι → ℝ) (x : ι) (r : ℝ) :
    covarianceDerivation C x (MvPolynomial.C r) = 0 :=
  MvPolynomial.derivation_C _ _

theorem covarianceDerivation_mul {ι : Type*}
    (C : ι → ι → ℝ) (x : ι)
    (p q : MvPolynomial ι ℝ) :
    covarianceDerivation C x (p * q) =
      covarianceDerivation C x p * q +
        p * covarianceDerivation C x q := by
  rw [(covarianceDerivation C x).leibniz]
  simp only [smul_eq_mul]
  ring

/-- Covariance derivations commute when the covariance is symmetric. -/
theorem covarianceDerivation_comm {ι : Type*}
    (C : ι → ι → ℝ) (_hC : ∀ x y, C x y = C y x)
    (x y : ι) (p : MvPolynomial ι ℝ) :
    covarianceDerivation C x (covarianceDerivation C y p) =
      covarianceDerivation C y (covarianceDerivation C x p) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | mul_X p z hp =>
      simp only [covarianceDerivation_mul, covarianceDerivation_X,
        map_add, covarianceDerivation_C]
      rw [hp]
      ring

/-- Creation operator associated with the covariance. -/
def wickCreation {ι : Type*}
    (C : ι → ι → ℝ) (x : ι) (p : MvPolynomial ι ℝ) :
    MvPolynomial ι ℝ :=
  MvPolynomial.X x * p - covarianceDerivation C x p

/-- Polynomial obtained by iterated normal ordering. -/
def wickMvPolynomial {ι : Type*}
    (C : ι → ι → ℝ) : List ι → MvPolynomial ι ℝ
  | [] => 1
  | x :: xs => wickCreation C x (wickMvPolynomial C xs)

@[simp]
theorem wickMvPolynomial_nil {ι : Type*}
    (C : ι → ι → ℝ) :
    wickMvPolynomial C [] = 1 := rfl

@[simp]
theorem wickMvPolynomial_cons {ι : Type*}
    (C : ι → ι → ℝ) (x : ι) (xs : List ι) :
    wickMvPolynomial C (x :: xs) =
      wickCreation C x (wickMvPolynomial C xs) := rfl

/-- The covariance derivation and creation operator satisfy the canonical
commutator relation. -/
theorem covarianceDerivation_wickCreation {ι : Type*}
    (C : ι → ι → ℝ) (hC : ∀ x y, C x y = C y x)
    (a x : ι) (p : MvPolynomial ι ℝ) :
    covarianceDerivation C a (wickCreation C x p) =
      MvPolynomial.C (C a x) * p +
        wickCreation C x (covarianceDerivation C a p) := by
  unfold wickCreation
  rw [map_sub, covarianceDerivation_mul, covarianceDerivation_X,
    covarianceDerivation_comm C hC]
  ring

/-- Appell property of the multivariate Wick polynomial. -/
theorem covarianceDerivation_wickMvPolynomial {ι : Type*}
    (C : ι → ι → ℝ) (hC : ∀ x y, C x y = C y x)
    (a : ι) :
    ∀ xs : List ι,
      covarianceDerivation C a (wickMvPolynomial C xs) =
        ∑ j : Fin xs.length,
          MvPolynomial.C (C a (xs.get j)) *
            wickMvPolynomial C (xs.eraseIdx j) := by
  intro xs
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [wickMvPolynomial_cons,
        covarianceDerivation_wickCreation C hC, ih]
      change
        MvPolynomial.C (C a x) * wickMvPolynomial C xs +
            wickCreation C x
              (∑ j : Fin xs.length,
                MvPolynomial.C (C a (xs.get j)) *
                  wickMvPolynomial C (xs.eraseIdx j)) =
          ∑ j : Fin (xs.length + 1),
            MvPolynomial.C (C a ((x :: xs).get j)) *
              wickMvPolynomial C ((x :: xs).eraseIdx j)
      rw [Fin.sum_univ_succ]
      simp only [List.get_cons_zero]
      congr 1
      unfold wickCreation
      simp only [map_sum, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      change
        MvPolynomial.X x *
              (MvPolynomial.C (C a (xs.get j)) *
                wickMvPolynomial C (xs.eraseIdx j)) -
            covarianceDerivation C x
              (MvPolynomial.C (C a (xs.get j)) *
                wickMvPolynomial C (xs.eraseIdx j)) =
          MvPolynomial.C (C a (xs.get j)) *
            wickMvPolynomial C (x :: xs.eraseIdx j)
      rw [covarianceDerivation_mul, covarianceDerivation_C,
        wickMvPolynomial_cons]
      unfold wickCreation
      ring

/-- Normal ordering satisfies exactly the recursive definition frozen in
`Probability/Chaos.lean`. -/
theorem wickMvPolynomial_cons_explicit {ι : Type*}
    (C : ι → ι → ℝ) (hC : ∀ x y, C x y = C y x)
    (x : ι) (xs : List ι) :
    wickMvPolynomial C (x :: xs) =
      MvPolynomial.X x * wickMvPolynomial C xs -
        ∑ j : Fin xs.length,
          MvPolynomial.C (C x (xs.get j)) *
            wickMvPolynomial C (xs.eraseIdx j) := by
  rw [wickMvPolynomial_cons, wickCreation,
    covarianceDerivation_wickMvPolynomial C hC]

/-- Evaluation of the polynomial normal ordering is the recursive random
Wick polynomial. -/
theorem eval_wickMvPolynomial_eq_wickPolynomial
    {ι Ω : Type*}
    (C : ι → ι → ℝ) (hC : ∀ x y, C x y = C y x)
    (X : ι → Ω → ℝ) :
    ∀ (xs : List ι) (ω : Ω),
      MvPolynomial.eval (fun x => X x ω) (wickMvPolynomial C xs) =
        wickPolynomial C X xs ω := by
  have aux :
      ∀ n : ℕ, ∀ xs : List ι, xs.length = n → ∀ ω : Ω,
        MvPolynomial.eval (fun x => X x ω) (wickMvPolynomial C xs) =
          wickPolynomial C X xs ω := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro xs hlen ω
        cases xs with
        | nil =>
            simp
        | cons x xs =>
            rw [wickMvPolynomial_cons_explicit C hC,
              wickPolynomial_cons]
            simp only [map_sub, map_mul, eval_X, eval_C, map_sum]
            refine congrArg₂ (fun u v : ℝ => u - v) ?_ ?_
            · congr 1
              have hlt : xs.length < n := by
                simp only [List.length_cons] at hlen
                omega
              exact ih _ hlt _ rfl ω
            · apply Finset.sum_congr rfl
              intro j _hj
              congr 1
              have herase :=
                List.length_eraseIdx_add_one j.isLt
              have hlt : (xs.eraseIdx j).length < n := by
                simp only [List.length_cons] at hlen
                omega
              exact ih _ hlt _ rfl ω
  intro xs ω
  exact aux xs.length xs rfl ω

/-- Recursive cross-contraction sum.  It is automatically zero when the
two lists have different lengths. -/
def crossWickList {ι : Type*}
    (C : ι → ι → ℝ) : List ι → List ι → ℝ
  | [], [] => 1
  | [], _ :: _ => 0
  | x :: xs, ys =>
      ∑ j : Fin ys.length,
        C x (ys.get j) * crossWickList C xs (ys.eraseIdx j)

@[simp]
theorem crossWickList_nil_nil {ι : Type*}
    (C : ι → ι → ℝ) :
    crossWickList C [] [] = 1 := rfl

@[simp]
theorem crossWickList_nil_cons {ι : Type*}
    (C : ι → ι → ℝ) (y : ι) (ys : List ι) :
    crossWickList C [] (y :: ys) = 0 := rfl

@[simp]
theorem crossWickList_cons {ι : Type*}
    (C : ι → ι → ℝ) (x : ι) (xs ys : List ι) :
    crossWickList C (x :: xs) ys =
      ∑ j : Fin ys.length,
        C x (ys.get j) * crossWickList C xs (ys.eraseIdx j) := rfl

/-- Recursive cross-contraction sums vanish for unequal list lengths. -/
theorem crossWickList_eq_zero_of_length_ne {ι : Type*}
    (C : ι → ι → ℝ) :
    ∀ xs ys : List ι, xs.length ≠ ys.length →
      crossWickList C xs ys = 0 := by
  intro xs
  induction xs with
  | nil =>
      intro ys hlen
      cases ys with
      | nil => exact (hlen rfl).elim
      | cons y ys => rfl
  | cons x xs ih =>
      intro ys hlen
      rw [crossWickList_cons]
      apply Finset.sum_eq_zero
      intro j _hj
      rw [ih]
      · ring
      · intro heq
        have herase := List.length_eraseIdx_add_one j.isLt
        simp only [List.length_cons] at hlen
        omega

/-- Polynomial integration-by-parts interface for a centered Gaussian
family.  The later noise specialization proves this from `NoiseModel`'s
joint Gaussianity; it is not an additional axiom. -/
structure GaussianPolynomialLaw
    {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (C : ι → ι → ℝ) (X : ι → Ω → ℝ) : Prop where
  measureReal_univ : μ.real Set.univ = 1
  covariance_symm : ∀ x y, C x y = C y x
  integrable_eval : ∀ p : MvPolynomial ι ℝ,
    Integrable
      (fun ω => MvPolynomial.eval (fun x => X x ω) p) μ
  integration_by_parts :
    ∀ (x : ι) (p : MvPolynomial ι ℝ),
      (∫ ω,
          MvPolynomial.eval (fun y => X y ω)
            (MvPolynomial.X x * p) ∂μ) =
        ∫ ω,
          MvPolynomial.eval (fun y => X y ω)
            (covarianceDerivation C x p) ∂μ

/-- Expectation of a polynomial under a `GaussianPolynomialLaw`. -/
def polynomialExpectation
    {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ι → Ω → ℝ)
    (p : MvPolynomial ι ℝ) : ℝ :=
  ∫ ω, MvPolynomial.eval (fun x => X x ω) p ∂μ

theorem GaussianPolynomialLaw.expectation_add
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (h : GaussianPolynomialLaw μ C X)
    (p q : MvPolynomial ι ℝ) :
    polynomialExpectation μ X (p + q) =
      polynomialExpectation μ X p + polynomialExpectation μ X q := by
  unfold polynomialExpectation
  simp only [map_add]
  exact integral_add (h.integrable_eval p) (h.integrable_eval q)

theorem GaussianPolynomialLaw.expectation_sub
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (h : GaussianPolynomialLaw μ C X)
    (p q : MvPolynomial ι ℝ) :
    polynomialExpectation μ X (p - q) =
      polynomialExpectation μ X p - polynomialExpectation μ X q := by
  unfold polynomialExpectation
  simp only [map_sub]
  exact integral_sub (h.integrable_eval p) (h.integrable_eval q)

theorem GaussianPolynomialLaw.expectation_finsetSum
    {ι Ω α : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (h : GaussianPolynomialLaw μ C X)
    (s : Finset α) (p : α → MvPolynomial ι ℝ) :
    polynomialExpectation μ X (∑ i ∈ s, p i) =
      ∑ i ∈ s, polynomialExpectation μ X (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [polynomialExpectation]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [h.expectation_add, ih]

theorem GaussianPolynomialLaw.expectation_fintypeSum
    {ι Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (h : GaussianPolynomialLaw μ C X)
    (p : α → MvPolynomial ι ℝ) :
    polynomialExpectation μ X (∑ i, p i) =
      ∑ i, polynomialExpectation μ X (p i) := by
  exact h.expectation_finsetSum Finset.univ p

theorem GaussianPolynomialLaw.expectation_C_mul
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (_h : GaussianPolynomialLaw μ C X)
    (r : ℝ) (p : MvPolynomial ι ℝ) :
    polynomialExpectation μ X (MvPolynomial.C r * p) =
      r * polynomialExpectation μ X p := by
  unfold polynomialExpectation
  simp only [map_mul, eval_C]
  exact integral_const_mul r _

theorem GaussianPolynomialLaw.expectation_X_mul
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (h : GaussianPolynomialLaw μ C X)
    (x : ι) (p : MvPolynomial ι ℝ) :
    polynomialExpectation μ X (MvPolynomial.X x * p) =
      polynomialExpectation μ X (covarianceDerivation C x p) :=
  h.integration_by_parts x p

/-- Creation is adjoint to covariance differentiation under Gaussian
expectation. -/
theorem GaussianPolynomialLaw.expectation_wickCreation_mul
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (h : GaussianPolynomialLaw μ C X)
    (x : ι) (p q : MvPolynomial ι ℝ) :
    polynomialExpectation μ X (wickCreation C x p * q) =
      polynomialExpectation μ X
        (p * covarianceDerivation C x q) := by
  rw [show wickCreation C x p * q =
      MvPolynomial.X x * (p * q) -
        covarianceDerivation C x p * q by
      unfold wickCreation
      ring]
  rw [h.expectation_sub, h.expectation_X_mul,
    covarianceDerivation_mul, h.expectation_add]
  ring

/-- A nonconstant Wick polynomial is centered. -/
theorem GaussianPolynomialLaw.expectation_wickMvPolynomial_cons
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (h : GaussianPolynomialLaw μ C X)
    (x : ι) (xs : List ι) :
    polynomialExpectation μ X (wickMvPolynomial C (x :: xs)) = 0 := by
  rw [wickMvPolynomial_cons]
  have hadj :=
    h.expectation_wickCreation_mul x (wickMvPolynomial C xs) 1
  simpa [polynomialExpectation] using hadj

/-- **Generic multivariate Wick orthogonality.**

The expectation of two normal-ordered products is exactly the recursive
sum of cross contractions. -/
theorem GaussianPolynomialLaw.expectation_wickMvPolynomial_mul
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (h : GaussianPolynomialLaw μ C X) :
    ∀ xs ys : List ι,
      polynomialExpectation μ X
          (wickMvPolynomial C xs * wickMvPolynomial C ys) =
        crossWickList C xs ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys
      cases ys with
      | nil =>
          simp [polynomialExpectation, h.measureReal_univ]
      | cons y ys =>
          simpa [polynomialExpectation] using
            h.expectation_wickMvPolynomial_cons y ys
  | cons x xs ih =>
      intro ys
      rw [wickMvPolynomial_cons,
        h.expectation_wickCreation_mul,
        covarianceDerivation_wickMvPolynomial C h.covariance_symm,
        crossWickList_cons]
      rw [Finset.mul_sum]
      rw [h.expectation_fintypeSum]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [show
        wickMvPolynomial C xs *
            (MvPolynomial.C (C x (ys.get j)) *
              wickMvPolynomial C (ys.eraseIdx j)) =
          MvPolynomial.C (C x (ys.get j)) *
            (wickMvPolynomial C xs *
              wickMvPolynomial C (ys.eraseIdx j)) by ring]
      rw [h.expectation_C_mul, ih]

/-- Function-level version of generic Wick orthogonality. -/
theorem GaussianPolynomialLaw.integral_wickPolynomial_mul
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (h : GaussianPolynomialLaw μ C X)
    (xs ys : List ι) :
    (∫ ω, wickPolynomial C X xs ω * wickPolynomial C X ys ω ∂μ) =
      crossWickList C xs ys := by
  rw [← h.expectation_wickMvPolynomial_mul xs ys]
  unfold polynomialExpectation
  apply integral_congr_ae
  filter_upwards with ω
  rw [map_mul,
    eval_wickMvPolynomial_eq_wickPolynomial C h.covariance_symm,
    eval_wickMvPolynomial_eq_wickPolynomial C h.covariance_symm]

/-- Finite Gaussian products projected to different chaos degrees are
orthogonal.  This is the precise `Projₖ` property used for the
noise-product factors in the parametrix. -/
theorem GaussianPolynomialLaw.integral_chaosProjProduct_mul_eq_zero_of_ne
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (h : GaussianPolynomialLaw μ C X)
    {k l : ℕ} (hkl : k ≠ l)
    (xs ys : List ι)
    (hxs : xs.length = k) (hys : ys.length = l) :
    (∫ ω,
        chaosProjProduct k C X xs ω *
          chaosProjProduct l C X ys ω ∂μ) = 0 := by
  rw [chaosProjProduct_eq_wickPolynomial C X hxs,
    chaosProjProduct_eq_wickPolynomial C X hys,
    h.integral_wickPolynomial_mul,
    crossWickList_eq_zero_of_length_ne]
  intro hlength
  apply hkl
  omega

/-- Every product of two Wick polynomials is integrable. -/
theorem GaussianPolynomialLaw.integrable_wickPolynomial_mul
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (h : GaussianPolynomialLaw μ C X)
    (xs ys : List ι) :
    Integrable
      (fun ω => wickPolynomial C X xs ω * wickPolynomial C X ys ω) μ := by
  refine (h.integrable_eval
    (wickMvPolynomial C xs * wickMvPolynomial C ys)).congr ?_
  filter_upwards with ω
  rw [map_mul,
    eval_wickMvPolynomial_eq_wickPolynomial C h.covariance_symm,
    eval_wickMvPolynomial_eq_wickPolynomial C h.covariance_symm]

end

end Anderson4D
