import Anderson4D.ForMathlib.Isserlis
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
# Derivatives of exponential covariance quadratics

This file closes the analytic-combinatorial step in Isserlis' theorem.  We
differentiate a symmetric continuous quadratic form by directional
derivatives, prove the exact Leibniz rule for a linear factor, and identify
the resulting recursion with `wickPairingList`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Iterated directional derivatives, with the head of the list applied
outermost.  This orientation agrees with `iteratedFDeriv_succ_apply_left`. -/
def directionalFDerivList (f : E → ℂ) : List E → E → ℂ
  | [], t => f t
  | x :: xs, t => fderiv ℝ (directionalFDerivList f xs) t x

@[simp]
theorem directionalFDerivList_nil (f : E → ℂ) :
    directionalFDerivList f [] = f := rfl

@[simp]
theorem directionalFDerivList_cons (f : E → ℂ) (x : E) (xs : List E) :
    directionalFDerivList f (x :: xs) =
      fun t => fderiv ℝ (directionalFDerivList f xs) t x := rfl

/-- Splitting a list of directions splits the corresponding derivative
iteration, with the right-hand block differentiated first. -/
theorem directionalFDerivList_append (f : E → ℂ) (xs ys : List E) :
    directionalFDerivList f (xs ++ ys) =
      directionalFDerivList (directionalFDerivList f ys) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, directionalFDerivList_cons, ih]

/-- The list presentation is exactly the standard iterated Fréchet
derivative, evaluated on the list entries in their given order. -/
theorem directionalFDerivList_eq_iteratedFDeriv
    (f : E → ℂ) (hf : ContDiff ℝ ⊤ f) (xs : List E) (t : E) :
    directionalFDerivList f xs t =
      iteratedFDeriv ℝ xs.length f t xs.get := by
  induction xs generalizing t with
  | nil => simp
  | cons x xs ih =>
      have hfun :
          directionalFDerivList f xs =
            fun y => iteratedFDeriv ℝ xs.length f y xs.get := by
        funext y
        exact ih y
      rw [directionalFDerivList_cons, hfun]
      have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ xs.length f) t :=
        (hf.differentiable_iteratedFDeriv (by simp)) t
      have hstep := hd.iteratedFDeriv_succ_apply_left'
        (m := Fin.cons x xs.get)
      change fderiv ℝ (fun y => iteratedFDeriv ℝ xs.length f y xs.get) t x =
        iteratedFDeriv ℝ (x :: xs).length f t (x :: xs).get
      calc
        _ = iteratedFDeriv ℝ (xs.length + 1) f t
              (Fin.cons x xs.get) := by
          simpa using hstep.symm
        _ = _ := by
          congr 1
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Vector-indexed specialization of
`directionalFDerivList_eq_iteratedFDeriv`. -/
theorem directionalFDerivList_ofFn
    (f : E → ℂ) (hf : ContDiff ℝ ⊤ f) {n : ℕ}
    (v : Fin n → E) (t : E) :
    directionalFDerivList f (List.ofFn v) t =
      iteratedFDeriv ℝ n f t v := by
  have hbase :=
    directionalFDerivList_eq_iteratedFDeriv f hf (List.ofFn v) t
  have hsigma :
      (⟨(List.ofFn v).length, (List.ofFn v).get⟩ :
        Σ k, Fin k → E) = ⟨n, v⟩ :=
    List.equivSigmaTuple.apply_symm_apply ⟨n, v⟩
  exact hbase.trans <| congrArg
    (fun p : Σ k, Fin k → E =>
      iteratedFDeriv ℝ p.1 f t p.2) hsigma

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem List.ofFn_snoc_eq_append_singleton
    {n : ℕ} (v : Fin n → E) (x : E) :
    List.ofFn (Fin.snoc v x) = List.ofFn v ++ [x] := by
  rw [Fin.snoc_eq_append, List.ofFn_fin_append]
  simp

/-- Symmetry of smooth iterated derivatives, specialized to moving the head
direction to the end of a list. -/
theorem directionalFDerivList_cons_rotate
    (f : E → ℂ) (hf : ContDiff ℝ ⊤ f)
    (x : E) (xs : List E) (t : E) :
    directionalFDerivList f (x :: xs) t =
      directionalFDerivList f (xs ++ [x]) t := by
  let v : Fin (xs.length + 1) → E := Fin.cons x xs.get
  have hsym :
      iteratedFDeriv ℝ (xs.length + 1) f t v =
        iteratedFDeriv ℝ (xs.length + 1) f t (Fin.snoc xs.get x) := by
    have h :=
      (hf.contDiffAt : ContDiffAt ℝ ⊤ f t).iteratedFDeriv_comp_perm
        v (finRotate (xs.length + 1))
    have hv :
        Fin.snoc xs.get x =
          v ∘ finRotate (xs.length + 1) := by
      simpa [v, Function.comp_def] using
        (Fin.snoc_eq_cons_rotate xs.get x)
    rw [hv]
    exact h.symm
  calc
    directionalFDerivList f (x :: xs) t =
        directionalFDerivList f (List.ofFn v) t := by
      simp [v]
    _ = iteratedFDeriv ℝ (xs.length + 1) f t v :=
      directionalFDerivList_ofFn f hf v t
    _ = iteratedFDeriv ℝ (xs.length + 1) f t
          (Fin.snoc xs.get x) := hsym
    _ = directionalFDerivList f
          (List.ofFn (Fin.snoc xs.get x)) t :=
      (directionalFDerivList_ofFn f hf (Fin.snoc xs.get x) t).symm
    _ = directionalFDerivList f (xs ++ [x]) t := by
      rw [List.ofFn_snoc_eq_append_singleton, List.ofFn_get]

/-- Smoothness is preserved by taking any fixed finite list of directional
derivatives. -/
theorem directionalFDerivList_contDiff
    (f : E → ℂ) (hf : ContDiff ℝ ⊤ f) (xs : List E) :
    ContDiff ℝ ⊤ (directionalFDerivList f xs) := by
  induction xs with
  | nil => exact hf
  | cons x xs ih =>
      rw [directionalFDerivList_cons]
      exact (ih.fderiv_right (m := ⊤) (by simp)).clm_apply contDiff_const

/-- Exact higher Leibniz rule when one factor is continuous linear.  Since
the linear factor has no derivatives above order one, the sum records the
unique direction that differentiates it. -/
theorem directionalFDerivList_linear_mul
    (L : E →L[ℝ] ℂ) (f : E → ℂ) (hf : ContDiff ℝ ⊤ f)
    (xs : List E) (t : E) :
    directionalFDerivList (fun y => L y * f y) xs t =
      L t * directionalFDerivList f xs t +
        ∑ j : Fin xs.length,
          L (xs.get j) * directionalFDerivList f (xs.eraseIdx j) t := by
  induction xs generalizing t with
  | nil => simp
  | cons x xs ih =>
      have hfun :
          directionalFDerivList (fun y => L y * f y) xs =
            fun y =>
              L y * directionalFDerivList f xs y +
                ∑ j : Fin xs.length,
                  L (xs.get j) *
                    directionalFDerivList f (xs.eraseIdx j) y := by
        funext y
        exact ih y
      rw [directionalFDerivList_cons, hfun]
      change fderiv ℝ
        (fun y =>
          L y * directionalFDerivList f xs y +
            ∑ j : Fin xs.length,
              L (xs.get j) *
                directionalFDerivList f (xs.eraseIdx j) y) t x = _
      have hD (ys : List E) :
          DifferentiableAt ℝ (directionalFDerivList f ys) t :=
        ((directionalFDerivList_contDiff f hf ys).differentiable
          (by simp)) t
      have hA :
          DifferentiableAt ℝ
            (fun y => L y * directionalFDerivList f xs y) t :=
        L.differentiableAt.mul (hD xs)
      have hterm (j : Fin xs.length) :
          DifferentiableAt ℝ
            (fun y =>
              L (xs.get j) *
                directionalFDerivList f (xs.eraseIdx j) y) t :=
        differentiableAt_const (c := L (xs.get j)) |>.mul
          (hD (xs.eraseIdx j))
      have hsum :
          DifferentiableAt ℝ
            (fun y =>
              ∑ j : Fin xs.length,
                L (xs.get j) *
                  directionalFDerivList f (xs.eraseIdx j) y) t :=
        DifferentiableAt.fun_sum fun j _ => hterm j
      rw [show
        (fun y =>
          L y * directionalFDerivList f xs y +
            ∑ j : Fin xs.length,
              L (xs.get j) *
                directionalFDerivList f (xs.eraseIdx j) y) =
          (fun y => L y * directionalFDerivList f xs y) +
            fun y =>
              ∑ j : Fin xs.length,
                L (xs.get j) *
                  directionalFDerivList f (xs.eraseIdx j) y by rfl]
      rw [fderiv_add hA hsum]
      have hAderiv :
          fderiv ℝ
              (fun y => L y * directionalFDerivList f xs y) t =
            L t • fderiv ℝ (directionalFDerivList f xs) t +
              directionalFDerivList f xs t • L := by
        rw [show
          (fun y => L y * directionalFDerivList f xs y) =
            (fun y => L y) * directionalFDerivList f xs by rfl]
        rw [fderiv_mul L.differentiableAt (hD xs)]
        simp
      rw [hAderiv]
      rw [fderiv_fun_sum (fun j _ => hterm j)]
      have htermDeriv (j : Fin xs.length) :
          fderiv ℝ
              (fun y =>
                L (xs.get j) *
                  directionalFDerivList f (xs.eraseIdx j) y) t =
            L (xs.get j) •
              fderiv ℝ (directionalFDerivList f (xs.eraseIdx j)) t := by
        rw [show
          (fun y =>
            L (xs.get j) *
              directionalFDerivList f (xs.eraseIdx j) y) =
            (fun _ : E => L (xs.get j)) *
              directionalFDerivList f (xs.eraseIdx j) by rfl]
        rw [fderiv_mul
          (differentiableAt_const (c := L (xs.get j)))
          (hD (xs.eraseIdx j))]
        rw [fderiv_const_apply]
        have hz :
            directionalFDerivList f (xs.eraseIdx j) t •
              (0 : E →L[ℝ] ℂ) = 0 :=
          by
            ext z
            simp
        rw [hz, add_zero]
      simp_rw [htermDeriv]
      simp only [add_apply, _root_.sum_apply, smul_apply, smul_eq_mul,
        directionalFDerivList_cons, List.length_cons]
      rw [Fin.sum_univ_succ]
      simp [directionalFDerivList_cons, mul_comm, add_assoc, add_left_comm,
        add_comm]

/-- The real quadratic exponent associated with a continuous bilinear form. -/
def covarianceQuadratic (B : E →L[ℝ] E →L[ℝ] ℝ) (t : E) : ℝ :=
  -(B t t) / 2

/-- The complex exponential of `covarianceQuadratic`. -/
def covarianceQuadraticExp (B : E →L[ℝ] E →L[ℝ] ℝ) (t : E) : ℂ :=
  Complex.exp (covarianceQuadratic B t)

theorem covarianceQuadratic_contDiff
    (B : E →L[ℝ] E →L[ℝ] ℝ) :
    ContDiff ℝ ⊤ (covarianceQuadratic B) := by
  unfold covarianceQuadratic
  fun_prop

theorem covarianceQuadraticExp_contDiff
    (B : E →L[ℝ] E →L[ℝ] ℝ) :
    ContDiff ℝ ⊤ (covarianceQuadraticExp B) := by
  have hreal :
      ContDiff ℝ ⊤
        (fun t => Complex.ofRealCLM (covarianceQuadratic B t)) :=
    Complex.ofRealCLM.contDiff.comp (covarianceQuadratic_contDiff B)
  have hexp : ContDiff ℝ ⊤ Complex.exp :=
    (Complex.contDiff_exp (𝕜 := ℂ) :
      ContDiff ℂ ⊤ Complex.exp).restrict_scalars ℝ
  change ContDiff ℝ ⊤
    (fun t => Complex.exp ((covarianceQuadratic B t : ℝ) : ℂ))
  simpa only [Complex.ofRealCLM_apply, Function.comp_def] using
    hexp.comp hreal

/-- For a symmetric bilinear form, the derivative of
`t ↦ -B(t,t)/2` in direction `x` is `-B(t,x)`. -/
theorem fderiv_covarianceQuadratic_apply
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u) (t x : E) :
    fderiv ℝ (covarianceQuadratic B) t x = -B t x := by
  have hdiag :
      fderiv ℝ (fun y : E => B y y) t x =
        B t x + B x t := by
    have h :=
      fderiv_clm_apply (x := t) B.differentiableAt differentiableAt_id
    have hx := congrArg (fun L : E →L[ℝ] ℝ => L x) h
    simpa using hx
  rw [show covarianceQuadratic B =
    fun y => (-1 / 2 : ℝ) * (B y y) by
      funext y
      simp [covarianceQuadratic]
      ring]
  rw [fderiv_const_mul (by fun_prop) (-1 / 2 : ℝ)]
  simp only [smul_apply, smul_eq_mul, hdiag, hB x t]
  ring

/-- The complex continuous linear form `t ↦ -B(t,x)`. -/
def negCovarianceDirection
    (B : E →L[ℝ] E →L[ℝ] ℝ) (x : E) : E →L[ℝ] ℂ :=
  -(Complex.ofRealCLM.comp (B.flip x))

@[simp]
theorem negCovarianceDirection_apply
    (B : E →L[ℝ] E →L[ℝ] ℝ) (x t : E) :
    negCovarianceDirection B x t = -(B t x : ℂ) := by
  simp [negCovarianceDirection]

/-- First derivative of the covariance quadratic exponential. -/
theorem fderiv_covarianceQuadraticExp_apply
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u) (t x : E) :
    fderiv ℝ (covarianceQuadraticExp B) t x =
      negCovarianceDirection B x t * covarianceQuadraticExp B t := by
  have hqDiff :
      DifferentiableAt ℝ (covarianceQuadratic B) t :=
    ((covarianceQuadratic_contDiff B).differentiable (by simp)) t
  have hqFDeriv :
      fderiv ℝ (covarianceQuadratic B) t = -B t := by
    ext z
    simp [fderiv_covarianceQuadratic_apply B hB t z]
  have hq :
      HasFDerivAt (covarianceQuadratic B) (-B t) t := by
    simpa only [hqFDeriv] using hqDiff.hasFDerivAt
  have hreal :
      HasFDerivAt
        (fun y => Complex.ofRealCLM (covarianceQuadratic B y))
        (Complex.ofRealCLM.comp (-B t)) t :=
    Complex.ofRealCLM.hasFDerivAt.comp t hq
  have hexp := hreal.cexp
  have happ := congrArg (fun L : E →L[ℝ] ℂ => L x) hexp.fderiv
  change
    fderiv ℝ
        (fun y => Complex.exp ((covarianceQuadratic B y : ℝ) : ℂ)) t x =
      -(B t x : ℂ) *
        Complex.exp ((covarianceQuadratic B t : ℝ) : ℂ)
  simpa [mul_comm] using happ

/-- Directional derivatives of the quadratic exponential satisfy exactly the
recursive Wick pairing formula, with covariance `-B`. -/
theorem directionalFDerivList_covarianceQuadraticExp_zero
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u) (xs : List E) :
    directionalFDerivList (covarianceQuadraticExp B) xs 0 =
      (wickPairingList (fun u v => -B u v) xs : ℂ) := by
  induction hlen : xs.length using Nat.strongRecOn generalizing xs with
  | ind n ih =>
      cases xs with
      | nil =>
          simp [covarianceQuadraticExp, covarianceQuadratic]
      | cons x xs =>
          have hsmooth := covarianceQuadraticExp_contDiff B
          rw [directionalFDerivList_cons_rotate
            (covarianceQuadraticExp B) hsmooth x xs 0]
          rw [directionalFDerivList_append]
          have hfirst :
              directionalFDerivList (covarianceQuadraticExp B) [x] =
                fun t =>
                  negCovarianceDirection B x t *
                    covarianceQuadraticExp B t := by
            funext t
            exact fderiv_covarianceQuadraticExp_apply B hB t x
          rw [hfirst]
          rw [directionalFDerivList_linear_mul
            (negCovarianceDirection B x) (covarianceQuadraticExp B)
            hsmooth xs 0]
          rw [wickPairingList_cons]
          have ihErase (j : Fin xs.length) :
              directionalFDerivList (covarianceQuadraticExp B)
                  (xs.eraseIdx j) 0 =
                (wickPairingList (fun u v => -B u v)
                  (xs.eraseIdx j) : ℂ) := by
            apply ih (xs.eraseIdx j).length
            · rw [List.length_eraseIdx_of_lt j.isLt]
              simp only [List.length_cons] at hlen
              omega
            · rfl
          simp_rw [ihErase]
          simp [negCovarianceDirection_apply, hB, mul_comm]

/-- Recursive Wick sums commute with relabeling a list. -/
theorem wickPairingList_map
    {α β : Type*} (C : β → β → ℝ) (f : α → β) (xs : List α) :
    wickPairingList C (xs.map f) =
      wickPairingList (fun i j => C (f i) (f j)) xs := by
  induction hlen : xs.length using Nat.strongRecOn generalizing xs with
  | ind n ih =>
      cases xs with
      | nil => simp
      | cons x xs =>
          rw [List.map_cons, wickPairingList_cons, wickPairingList_cons]
          let e : Fin (xs.map f).length ≃ Fin xs.length :=
            finCongr (by simp)
          refine Fintype.sum_equiv e _ _ ?_
          intro j
          have hget :
              (xs.map f).get j = f (xs.get (e j)) := by
            simp [e]
          rw [hget]
          rw [List.eraseIdx_map]
          rw [ih (xs.eraseIdx j).length]
          · rfl
          · have hj : (j : ℕ) < xs.length := by
              simpa using j.isLt
            rw [List.length_eraseIdx_of_lt hj]
            simp only [List.length_cons] at hlen
            omega
          · rfl

/-- The exact iterated Fréchet derivative at zero, in the project's
`wickPairingSum` presentation. -/
theorem iteratedFDeriv_covarianceQuadraticExp_zero_eq_wick
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u)
    (n : ℕ) (x : Fin n → E) :
    iteratedFDeriv ℝ n (covarianceQuadraticExp B) 0 x =
      (wickPairingSum
        (fun i j => -B (x i) (x j)) : ℂ) := by
  rw [← directionalFDerivList_ofFn
    (covarianceQuadraticExp B) (covarianceQuadraticExp_contDiff B) x 0]
  rw [directionalFDerivList_covarianceQuadraticExp_zero B hB]
  rw [show List.ofFn x = (List.ofFn id).map x by
    simp]
  rw [wickPairingList_map]
  rfl

/-- Scaling every covariance entry by `a` scales a full pairing on `2q`
labels by `a^q`. -/
theorem wickPairingList_scale_even
    {α : Type*} (a : ℝ) (C : α → α → ℝ) :
    ∀ (q : ℕ) (xs : List α), xs.length = 2 * q →
      wickPairingList (fun i j => a * C i j) xs =
        a ^ q * wickPairingList C xs := by
  intro q
  induction q with
  | zero =>
      intro xs hxs
      have : xs = [] := List.length_eq_zero_iff.mp (by omega)
      subst xs
      simp
  | succ q ih =>
      intro xs hxs
      cases xs with
      | nil => simp at hxs
      | cons x tail =>
          rw [wickPairingList_cons, wickPairingList_cons]
          have htail : tail.length = 2 * q + 1 := by
            simp only [List.length_cons] at hxs
            omega
          have hterm (j : Fin tail.length) :
              wickPairingList (fun i j => a * C i j)
                  (tail.eraseIdx j) =
                a ^ q * wickPairingList C (tail.eraseIdx j) := by
            apply ih
            rw [List.length_eraseIdx_of_lt j.isLt]
            omega
          simp_rw [hterm]
          calc
            _ = ∑ j : Fin tail.length,
                a ^ (q + 1) *
                  (C x (tail.get j) *
                    wickPairingList C (tail.eraseIdx j)) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [pow_succ]
              ring
            _ = a ^ (q + 1) *
                ∑ j : Fin tail.length,
                  C x (tail.get j) *
                    wickPairingList C (tail.eraseIdx j) := by
              rw [Finset.mul_sum]

/-- Negating covariance contributes one minus sign per pair. -/
theorem wickPairingSum_neg_even
    (q : ℕ) (C : Fin (2 * q) → Fin (2 * q) → ℝ) :
    wickPairingSum (fun i j => -C i j) =
      (-1 : ℝ) ^ q * wickPairingSum C := by
  unfold wickPairingSum
  simpa using
    (wickPairingList_scale_even (-1) C q (List.ofFn id) (by simp))

/-- Even-order derivative of the exact quadratic exponential appearing in
the characteristic-function formula. -/
theorem iteratedFDeriv_covarianceExp_even_zero
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u)
    (q : ℕ) (x : Fin (2 * q) → E) :
    iteratedFDeriv ℝ (2 * q)
        (fun t : E => Complex.exp (-((B t t : ℝ) : ℂ) / 2))
        0 x =
      (-1 : ℂ) ^ q *
        (wickPairingSum (fun i j => B (x i) (x j)) : ℂ) := by
  have hfun :
      (fun t : E => Complex.exp (-((B t t : ℝ) : ℂ) / 2)) =
        covarianceQuadraticExp B := by
    funext t
    simp only [covarianceQuadraticExp, covarianceQuadratic]
    congr 1
    push_cast
    ring
  rw [hfun,
    iteratedFDeriv_covarianceQuadraticExp_zero_eq_wick B hB,
    wickPairingSum_neg_even]
  push_cast
  norm_num

/-- Odd-order derivatives vanish. -/
theorem iteratedFDeriv_covarianceExp_odd_zero
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u)
    (q : ℕ) (x : Fin (2 * q + 1) → E) :
    iteratedFDeriv ℝ (2 * q + 1)
        (fun t : E => Complex.exp (-((B t t : ℝ) : ℂ) / 2))
        0 x = 0 := by
  have hfun :
      (fun t : E => Complex.exp (-((B t t : ℝ) : ℂ) / 2)) =
        covarianceQuadraticExp B := by
    funext t
    simp only [covarianceQuadraticExp, covarianceQuadratic]
    congr 1
    push_cast
    ring
  rw [hfun,
    iteratedFDeriv_covarianceQuadraticExp_zero_eq_wick B hB,
    wickPairingSum_odd]
  norm_num

section Isserlis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H]

/-- **Isserlis' theorem, even case.**  Mixed moments of a centered Gaussian
measure are the sum of covariance products over all labeled full pairings. -/
theorem centeredGaussian_mixedMoment_eq_wickPairingSum
    (μ : Measure H) [IsGaussian μ] (hμ : ∫ y, y ∂μ = 0)
    (q : ℕ) (x : Fin (2 * q) → H) :
    (∫ y, ∏ i, ⟪y, x i⟫ ∂μ : ℝ) =
      wickPairingSum
        (fun i j => covarianceBilin μ (x i) (x j)) := by
  have hcalc :=
    iteratedFDeriv_covarianceExp_even_zero
      (covarianceBilin μ)
      (fun u v => covarianceBilin_comm u v) q x
  have hred :=
    iteratedFDeriv_covarianceExp_zero μ hμ (2 * q) x
  have heq :
      (-1 : ℂ) ^ q *
          (wickPairingSum
            (fun i j => covarianceBilin μ (x i) (x j)) : ℂ) =
        I ^ (2 * q) *
          ((∫ y, ∏ i, ⟪y, x i⟫ ∂μ : ℝ) : ℂ) :=
    hcalc.symm.trans hred
  have hIpow : I ^ (2 * q) = (-1 : ℂ) ^ q := by
    rw [pow_mul]
    norm_num
  rw [hIpow] at heq
  have hsign : (-1 : ℂ) ^ q ≠ 0 := pow_ne_zero q (by norm_num)
  have hcast :
      (wickPairingSum
        (fun i j => covarianceBilin μ (x i) (x j)) : ℂ) =
        ((∫ y, ∏ i, ⟪y, x i⟫ ∂μ : ℝ) : ℂ) :=
    mul_left_cancel₀ hsign heq
  exact_mod_cast hcast.symm

/-- **Isserlis' theorem, odd case.**  Every centered Gaussian mixed moment of
odd total degree vanishes. -/
theorem centeredGaussian_mixedMoment_odd_eq_zero
    (μ : Measure H) [IsGaussian μ] (hμ : ∫ y, y ∂μ = 0)
    (q : ℕ) (x : Fin (2 * q + 1) → H) :
    (∫ y, ∏ i, ⟪y, x i⟫ ∂μ : ℝ) = 0 := by
  have hcalc :=
    iteratedFDeriv_covarianceExp_odd_zero
      (covarianceBilin μ)
      (fun u v => covarianceBilin_comm u v) q x
  have hred :=
    iteratedFDeriv_covarianceExp_zero μ hμ (2 * q + 1) x
  have heq :
      I ^ (2 * q + 1) *
          ((∫ y, ∏ i, ⟪y, x i⟫ ∂μ : ℝ) : ℂ) = 0 :=
    hred.symm.trans hcalc
  have hIpow : I ^ (2 * q + 1) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hcast :
      ((∫ y, ∏ i, ⟪y, x i⟫ ∂μ : ℝ) : ℂ) = 0 :=
    (mul_eq_zero.mp heq).resolve_left hIpow
  exact_mod_cast hcast

end Isserlis

end

end Anderson4D
