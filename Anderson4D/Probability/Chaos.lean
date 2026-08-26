import Anderson4D.ForMathlib.WickRecursion

/-!
# Recursive Gaussian Wick polynomials

This file supplies the algebraic core of the minimal chaos API used in
paper equations (2.4) and (3.16).  A Wick polynomial is defined by the
creation--contraction recursion.  The defining identity says that
multiplication by one Gaussian coordinate either creates a new single or
contracts it with exactly one existing single.

The construction is pointwise and therefore independent of a probability
space.  Probabilistic moment and orthogonality statements can subsequently
identify this recursion with Wiener-chaos projection without changing the
combinatorial object used by the parametrix proof.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- The recursively normal-ordered product of a labeled list of real
variables with covariance kernel `C`. -/
def wickPolynomial {ι Ω : Type*} (C : ι → ι → ℝ)
    (X : ι → Ω → ℝ) : List ι → Ω → ℝ
  | [] => fun _ => 1
  | x :: xs => fun ω =>
      X x ω * wickPolynomial C X xs ω -
        ∑ j : Fin xs.length,
          C x (xs.get j) * wickPolynomial C X (xs.eraseIdx j) ω
termination_by xs => xs.length
decreasing_by
  simp_wf
  simp only [List.length_cons]
  have h := List.length_eraseIdx_add_one j.isLt
  omega

@[simp]
theorem wickPolynomial_nil {ι Ω : Type*} (C : ι → ι → ℝ)
    (X : ι → Ω → ℝ) (ω : Ω) :
    wickPolynomial C X [] ω = 1 := by
  rw [wickPolynomial]

@[simp]
theorem wickPolynomial_cons {ι Ω : Type*} (C : ι → ι → ℝ)
    (X : ι → Ω → ℝ) (x : ι) (xs : List ι) (ω : Ω) :
    wickPolynomial C X (x :: xs) ω =
      X x ω * wickPolynomial C X xs ω -
        ∑ j : Fin xs.length,
          C x (xs.get j) * wickPolynomial C X (xs.eraseIdx j) ω := by
  rw [wickPolynomial]

@[simp]
theorem wickPolynomial_singleton {ι Ω : Type*} (C : ι → ι → ℝ)
    (X : ι → Ω → ℝ) (x : ι) (ω : Ω) :
    wickPolynomial C X [x] ω = X x ω := by
  simp

@[simp]
theorem wickPolynomial_pair {ι Ω : Type*} (C : ι → ι → ℝ)
    (X : ι → Ω → ℝ) (x y : ι) (ω : Ω) :
    wickPolynomial C X [x, y] ω =
      X x ω * X y ω - C x y := by
  simp

/-- Creation--contraction identity.  This is the exact algebra used when
the new noise index in Proposition 3.4 is either left single or paired with
one of the old single indices. -/
theorem mul_wickPolynomial_eq_create_add_contract
    {ι Ω : Type*} (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (x : ι) (xs : List ι) (ω : Ω) :
    X x ω * wickPolynomial C X xs ω =
      wickPolynomial C X (x :: xs) ω +
        ∑ j : Fin xs.length,
          C x (xs.get j) * wickPolynomial C X (xs.eraseIdx j) ω := by
  rw [wickPolynomial_cons]
  ring

/-- With zero covariance there are no contractions, so normal ordering is
the ordinary product. -/
theorem wickPolynomial_zeroCovariance
    {ι Ω : Type*} (X : ι → Ω → ℝ) :
    ∀ (xs : List ι) (ω : Ω),
      wickPolynomial (fun _ _ => 0) X xs ω =
        (xs.map fun x => X x ω).prod := by
  intro xs
  induction xs with
  | nil =>
      intro ω
      simp
  | cons x xs ih =>
      intro ω
      rw [wickPolynomial_cons, ih]
      simp

/-- Wick polynomials are measurable whenever all generating coordinates
are measurable. -/
theorem measurable_wickPolynomial
    {ι Ω : Type*} [MeasurableSpace Ω]
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) :
    ∀ xs : List ι, Measurable (wickPolynomial C X xs) := by
  intro xs
  generalize hn : xs.length = n
  induction n using Nat.strongRecOn generalizing xs with
  | ind n ih =>
      cases xs with
      | nil =>
          rw [show wickPolynomial C X [] =
              fun _ : Ω => (1 : ℝ) by
            funext ω
            exact wickPolynomial_nil C X ω]
          exact measurable_const
      | cons x tail =>
          have hn' : tail.length + 1 = n := by
            simpa only [List.length_cons] using hn
          have htail : Measurable (wickPolynomial C X tail) :=
            ih tail.length (by omega) tail rfl
          have herase :
              ∀ j : Fin tail.length,
                Measurable (wickPolynomial C X (tail.eraseIdx j)) := by
            intro j
            exact ih (tail.eraseIdx j).length (by
              rw [List.length_eraseIdx_of_lt j.isLt]
              omega) (tail.eraseIdx j) rfl
          rw [show wickPolynomial C X (x :: tail) =
              fun ω =>
                X x ω * wickPolynomial C X tail ω -
                  ∑ j : Fin tail.length,
                    C x (tail.get j) *
                      wickPolynomial C X (tail.eraseIdx j) ω by
            funext ω
            rw [wickPolynomial_cons]]
          exact
            (hX x).mul htail |>.sub
              (Finset.measurable_sum _ fun j _ =>
                measurable_const.mul (herase j))

/-! ## The finite-product chaos projection used in the paper -/

/-- The degree-`k` chaos projection of one finite coordinate product.

The paper only applies `Projₖ` to a product of exactly `k` Gaussian
coordinates.  On that domain the projection is the normal-ordered
product; a mismatched degree is set to zero.  This deliberately avoids
claiming a global orthogonal-projection operator on all of `L²(Ω)`,
which is not needed by the parametrix construction. -/
def chaosProjProduct {ι Ω : Type*} (k : ℕ)
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (xs : List ι) : Ω → ℝ :=
  if xs.length = k then wickPolynomial C X xs else 0

@[simp]
theorem chaosProjProduct_eq_wickPolynomial
    {ι Ω : Type*} {k : ℕ}
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    {xs : List ι} (hdegree : xs.length = k) :
    chaosProjProduct k C X xs =
      wickPolynomial C X xs := by
  simp [chaosProjProduct, hdegree]

@[simp]
theorem chaosProjProduct_eq_zero
    {ι Ω : Type*} {k : ℕ}
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    {xs : List ι} (hdegree : xs.length ≠ k) :
    chaosProjProduct k C X xs = 0 := by
  simp [chaosProjProduct, hdegree]

/-- Finite-product chaos projections are measurable whenever the
underlying Gaussian coordinates are measurable. -/
theorem measurable_chaosProjProduct
    {ι Ω : Type*} [MeasurableSpace Ω]
    (k : ℕ) (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (xs : List ι) :
    Measurable (chaosProjProduct k C X xs) := by
  by_cases hdegree : xs.length = k
  · rw [chaosProjProduct_eq_wickPolynomial C X hdegree]
    exact measurable_wickPolynomial C X hX xs
  · rw [chaosProjProduct_eq_zero C X hdegree]
    exact measurable_const

/-- A pointwise family obeys the Gaussian Wick recursion when it has the
empty value `1` and the same creation--contraction rule as
`wickPolynomial`. -/
structure WickRecursionLaw {ι Ω : Type*} (C : ι → ι → ℝ)
    (X : ι → Ω → ℝ) (W : List ι → Ω → ℝ) : Prop where
  empty : ∀ ω, W [] ω = 1
  create_contract :
    ∀ (x : ι) (xs : List ι) (ω : Ω),
      X x ω * W xs ω =
        W (x :: xs) ω +
          ∑ j : Fin xs.length,
            C x (xs.get j) * W (xs.eraseIdx j) ω

/-- The recursively defined Wick polynomial satisfies its abstract
creation--contraction specification. -/
theorem wickPolynomial_recursionLaw {ι Ω : Type*}
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ) :
    WickRecursionLaw C X (wickPolynomial C X) where
  empty := fun ω => wickPolynomial_nil C X ω
  create_contract := mul_wickPolynomial_eq_create_add_contract C X

/-- The creation--contraction law determines the Wick family uniquely.
This is the comparison principle used later to identify the combinatorial
normal ordering with a Hilbert-space Wiener-chaos projection. -/
theorem WickRecursionLaw.eq_wickPolynomial
    {ι Ω : Type*} {C : ι → ι → ℝ} {X : ι → Ω → ℝ}
    {W : List ι → Ω → ℝ} (hW : WickRecursionLaw C X W) :
    ∀ xs : List ι, W xs = wickPolynomial C X xs := by
  intro xs
  generalize hn : xs.length = n
  induction n using Nat.strongRecOn generalizing xs with
  | ind n ih =>
      cases xs with
      | nil =>
          funext ω
          exact (hW.empty ω).trans (wickPolynomial_nil C X ω).symm
      | cons x tail =>
          funext ω
          have hn' : tail.length + 1 = n := by
            simpa only [List.length_cons] using hn
          have htail :
              W tail ω = wickPolynomial C X tail ω := by
            exact congrFun
              (ih tail.length (by omega) tail rfl) ω
          have herase :
              ∀ j : Fin tail.length,
                W (tail.eraseIdx j) ω =
                  wickPolynomial C X (tail.eraseIdx j) ω := by
            intro j
            apply congrFun
              (ih (tail.eraseIdx j).length (by
                rw [List.length_eraseIdx_of_lt j.isLt]
                omega) (tail.eraseIdx j) rfl)
          have hcreate := hW.create_contract x tail ω
          rw [htail] at hcreate
          simp_rw [herase] at hcreate
          rw [wickPolynomial_cons]
          linarith

end

end Anderson4D
