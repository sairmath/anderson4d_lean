import Anderson4D.Probability.WickOrthogonality
import Anderson4D.ForMathlib.QuadraticExpDeriv

/-!
# Gaussian list moments imply polynomial integration by parts

This file bridges the Isserlis moment formula to the polynomial
integration-by-parts interface used by the generic Wick orthogonality
theorem.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory MvPolynomial
open scoped BigOperators RealInnerProductSpace

/-- Product of the coordinates selected by a list. -/
def gaussianListProduct {ι Ω : Type*}
    (X : ι → Ω → ℝ) (xs : List ι) (ω : Ω) : ℝ :=
  (xs.map fun i => X i ω).prod

@[simp]
theorem gaussianListProduct_nil {ι Ω : Type*}
    (X : ι → Ω → ℝ) (ω : Ω) :
    gaussianListProduct X [] ω = 1 := rfl

@[simp]
theorem gaussianListProduct_cons {ι Ω : Type*}
    (X : ι → Ω → ℝ) (x : ι) (xs : List ι) (ω : Ω) :
    gaussianListProduct X (x :: xs) ω =
      X x ω * gaussianListProduct X xs ω := by
  simp [gaussianListProduct]

/-- Raw Isserlis moment interface for a centered Gaussian family. -/
structure GaussianListMomentLaw
    {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (C : ι → ι → ℝ) (X : ι → Ω → ℝ) : Prop where
  covariance_symm : ∀ x y, C x y = C y x
  integrable_listProduct :
    ∀ xs : List ι, Integrable (gaussianListProduct X xs) μ
  integral_listProduct :
    ∀ xs : List ι,
      ∫ ω, gaussianListProduct X xs ω ∂μ =
        wickPairingList C xs

/-- Expectation of a polynomial times a coordinate-list monomial. -/
def polynomialListExpectation
    {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ι → Ω → ℝ)
    (p : MvPolynomial ι ℝ) (xs : List ι) : ℝ :=
  ∫ ω,
    MvPolynomial.eval (fun i => X i ω) p *
      gaussianListProduct X xs ω ∂μ

theorem GaussianListMomentLaw.integrable_eval_mul_listProduct
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (h : GaussianListMomentLaw μ C X) :
    ∀ (p : MvPolynomial ι ℝ) (xs : List ι),
      Integrable
        (fun ω =>
          MvPolynomial.eval (fun i => X i ω) p *
            gaussianListProduct X xs ω) μ := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C r =>
      intro xs
      simpa using (h.integrable_listProduct xs).const_mul r
  | add p q hp hq =>
      intro xs
      refine ((hp xs).add (hq xs)).congr ?_
      filter_upwards with ω
      simp only [Pi.add_apply, map_add]
      ring
  | mul_X p y hp =>
      intro xs
      refine (hp (y :: xs)).congr ?_
      filter_upwards with ω
      simp only [map_mul, eval_X, gaussianListProduct_cons]
      ring

theorem GaussianListMomentLaw.integrable_eval
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (h : GaussianListMomentLaw μ C X)
    (p : MvPolynomial ι ℝ) :
    Integrable
      (fun ω => MvPolynomial.eval (fun i => X i ω) p) μ := by
  refine (h.integrable_eval_mul_listProduct p []).congr ?_
  filter_upwards with ω
  simp

theorem GaussianListMomentLaw.expectation_C
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (h : GaussianListMomentLaw μ C X)
    (r : ℝ) (xs : List ι) :
    polynomialListExpectation μ X (MvPolynomial.C r) xs =
      r * wickPairingList C xs := by
  unfold polynomialListExpectation
  simp only [eval_C]
  rw [integral_const_mul, h.integral_listProduct]

theorem GaussianListMomentLaw.expectation_add
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (h : GaussianListMomentLaw μ C X)
    (p q : MvPolynomial ι ℝ) (xs : List ι) :
    polynomialListExpectation μ X (p + q) xs =
      polynomialListExpectation μ X p xs +
        polynomialListExpectation μ X q xs := by
  unfold polynomialListExpectation
  simp only [map_add, add_mul]
  exact integral_add
    (h.integrable_eval_mul_listProduct p xs)
    (h.integrable_eval_mul_listProduct q xs)

theorem GaussianListMomentLaw.expectation_mul_X
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (_h : GaussianListMomentLaw μ C X)
    (p : MvPolynomial ι ℝ) (y : ι) (xs : List ι) :
    polynomialListExpectation μ X (p * MvPolynomial.X y) xs =
      polynomialListExpectation μ X p (y :: xs) := by
  unfold polynomialListExpectation
  apply integral_congr_ae
  filter_upwards with ω
  simp only [map_mul, eval_X, gaussianListProduct_cons]
  ring

theorem GaussianListMomentLaw.expectation_C_mul
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (_h : GaussianListMomentLaw μ C X)
    (r : ℝ) (p : MvPolynomial ι ℝ) (xs : List ι) :
    polynomialListExpectation μ X (MvPolynomial.C r * p) xs =
      r * polynomialListExpectation μ X p xs := by
  unfold polynomialListExpectation
  simp only [map_mul, eval_C]
  rw [show
    (fun ω =>
      r * MvPolynomial.eval (fun i => X i ω) p *
        gaussianListProduct X xs ω) =
      fun ω =>
        r * (MvPolynomial.eval (fun i => X i ω) p *
          gaussianListProduct X xs ω) by
    funext ω
    ring]
  rw [integral_const_mul]

/-- Strong polynomial integration by parts, with an additional coordinate
list carried through the induction. -/
theorem GaussianListMomentLaw.integrationByParts_with_list
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (h : GaussianListMomentLaw μ C X)
    (x : ι) :
    ∀ (p : MvPolynomial ι ℝ) (xs : List ι),
      polynomialListExpectation μ X (MvPolynomial.X x * p) xs =
        polynomialListExpectation μ X
          (covarianceDerivation C x p) xs +
          ∑ j : Fin xs.length,
            C x (xs.get j) *
              polynomialListExpectation μ X p (xs.eraseIdx j) := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C r =>
      intro xs
      rw [show MvPolynomial.X x * MvPolynomial.C r =
          MvPolynomial.C r * MvPolynomial.X x by ring,
        h.expectation_mul_X, h.expectation_C,
        covarianceDerivation_C]
      have hzero :
          polynomialListExpectation μ X 0 xs = 0 := by
        unfold polynomialListExpectation
        simp
      rw [hzero, zero_add]
      rw [wickPairingList_cons, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [h.expectation_C]
      ring
  | add p q hp hq =>
      intro xs
      rw [mul_add, h.expectation_add, hp xs, hq xs, map_add,
        h.expectation_add]
      simp_rw [h.expectation_add p q, mul_add]
      rw [Finset.sum_add_distrib]
      ring
  | mul_X p y hp =>
      intro xs
      rw [show
          MvPolynomial.X x * (p * MvPolynomial.X y) =
            (MvPolynomial.X x * p) * MvPolynomial.X y by ring,
        h.expectation_mul_X, hp (y :: xs),
        covarianceDerivation_mul, covarianceDerivation_X,
        h.expectation_add, h.expectation_mul_X]
      rw [show
          p * MvPolynomial.C (C x y) =
            MvPolynomial.C (C x y) * p by ring,
        h.expectation_C_mul]
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      have herase0 :
          (y :: xs).eraseIdx (0 : Fin (xs.length + 1)) = xs := by
        simp
      rw [herase0]
      have htail :
          (∑ j : Fin xs.length,
              C x ((y :: xs).get j.succ) *
                polynomialListExpectation μ X p
                  ((y :: xs).eraseIdx j.succ)) =
            ∑ j : Fin xs.length,
              C x (xs.get j) *
                polynomialListExpectation μ X
                  (p * MvPolynomial.X y) (xs.eraseIdx j) := by
        apply Finset.sum_congr rfl
        intro j _hj
        have hget :
            (y :: xs).get j.succ = xs.get j := by
          rfl
        have herase :
            (y :: xs).eraseIdx (j.succ : ℕ) =
              y :: xs.eraseIdx (j : ℕ) := by
          simp only [Fin.val_succ, List.eraseIdx_cons_succ]
        rw [hget, herase, h.expectation_mul_X]
      rw [htail]
      simp only [List.get_cons_zero]
      ring

/-- Isserlis list moments yield the exact polynomial integration-by-parts
interface used by generic Wick orthogonality. -/
theorem GaussianListMomentLaw.toGaussianPolynomialLaw
    {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    (h : GaussianListMomentLaw μ C X) :
    GaussianPolynomialLaw μ C X where
  measureReal_univ := by simp
  covariance_symm := h.covariance_symm
  integrable_eval := h.integrable_eval
  integration_by_parts := by
    intro x p
    have hstrong := h.integrationByParts_with_list x p []
    simpa [polynomialListExpectation] using hstrong

end

end Anderson4D
