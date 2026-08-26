import Anderson4D.Combinatorics.FactorialBounds
import Anderson4D.PermSum.SingleScaleSetup

/-!
# Factorial absorption after the fixed-class inner estimate

This file formalizes the numerical factorial step between paper (5.88) and
(5.89).  For one `(N,X)` fiber, write `M = m_{N,X}` and let `S` be the
number of skipped incoming edges in that fiber.  The two square-root factors

`√(X^M) · √((XY)^(M-S))`

are the algebraic envelope of
`(X Y^(1/2))^M (XY)^(-S/2)`.  The first is absorbed by the leaf
factorials, using `X ≤ m_l`; the second is absorbed by `(M-S)!`, using
`XY ≤ M` and the exponential series estimate `A^B ≤ exp(A) B!`.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/--
Square roots commute with natural powers on nonnegative real numbers.

This elementary normalization lemma is kept local to the single-scale
ledger because the paper writes half-powers while the implementation uses
ordinary powers of square roots.
-/
theorem sqrt_pow_of_nonneg (x : ℝ) (n : ℕ) (hx : 0 ≤ x) :
    Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih, pow_succ]

/--
The exact per-fiber factor printed after (5.88):

`(X √Y)^M (XY)^(-S/2)`.

Because `S` is a natural number, the negative half-power is represented
without real-exponent bookkeeping as the `S`-th power of the inverse square
root.  The next theorem proves that this literal form is exactly the
factorial envelope used below.
-/
def singleScalePrintedFiberFactor (X Y M S : ℕ) : ℝ :=
  ((X : ℝ) * Real.sqrt (Y : ℝ)) ^ M *
    (Real.sqrt (((X * Y : ℕ) : ℝ)))⁻¹ ^ S

/--
The same printed expression with its negative half-power represented
literally by `Real.rpow`.
-/
def singleScalePrintedRpowFiberFactor (X Y M S : ℕ) : ℝ :=
  ((X : ℝ) * Real.sqrt (Y : ℝ)) ^ M *
    (((X * Y : ℕ) : ℝ) ^ (-(S : ℝ) / 2))

/--
The inverse-square-root encoding of `(XY)^(-S/2)` agrees with the literal
`Real.rpow` notation used at the paper-facing statement boundary.
-/
theorem singleScalePrintedFiberFactor_eq_rpow
    (X Y M S : ℕ) :
    singleScalePrintedFiberFactor X Y M S =
      singleScalePrintedRpowFiberFactor X Y M S := by
  have hxy : 0 ≤ (((X * Y : ℕ) : ℝ)) := by positivity
  have hhalf :
      -((S : ℝ)) / 2 = -(1 / 2 * (S : ℝ)) := by ring
  have hrpow :
      (((X * Y : ℕ) : ℝ) ^ (-((S : ℝ)) / 2)) =
        ((((X * Y : ℕ) : ℝ) ^ (1 / 2 : ℝ)) ^ S)⁻¹ := by
    rw [hhalf, Real.rpow_neg hxy, Real.rpow_mul hxy,
      Real.rpow_natCast]
  unfold singleScalePrintedFiberFactor
    singleScalePrintedRpowFiberFactor
  simp only [Real.sqrt_eq_rpow, inv_pow]
  rw [hrpow]

/--
The printed factor after (5.88) is exactly
`√(X^M) √((XY)^(M-S))` when the fiber is active and no more than `M`
incoming edges are skipped.
-/
theorem singleScalePrintedFiberFactor_eq_envelope
    (X Y M S : ℕ) (hX : 0 < X) (hY : 0 < Y) (hS : S ≤ M) :
    singleScalePrintedFiberFactor X Y M S =
      Real.sqrt ((X : ℝ) ^ M) *
        Real.sqrt (((X * Y : ℕ) : ℝ) ^ (M - S)) := by
  have hx : 0 ≤ (X : ℝ) := by positivity
  have hy : 0 ≤ (Y : ℝ) := by positivity
  have hxy : 0 ≤ (X : ℝ) * (Y : ℝ) := mul_nonneg hx hy
  have hxyPos : 0 < (X : ℝ) * (Y : ℝ) := by
    exact mul_pos (by exact_mod_cast hX) (by exact_mod_cast hY)
  have hbase :
      (X : ℝ) * Real.sqrt (Y : ℝ) =
        Real.sqrt (X : ℝ) * Real.sqrt ((X : ℝ) * (Y : ℝ)) := by
    rw [Real.sqrt_mul hx]
    rw [← mul_assoc, Real.mul_self_sqrt hx]
  have hsqrtNe :
      Real.sqrt ((X : ℝ) * (Y : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hxyPos)
  unfold singleScalePrintedFiberFactor
  push_cast
  change
    ((X : ℝ) * Real.sqrt (Y : ℝ)) ^ M *
        (Real.sqrt ((X : ℝ) * (Y : ℝ)))⁻¹ ^ S =
      Real.sqrt ((X : ℝ) ^ M) *
        Real.sqrt (((X : ℝ) * (Y : ℝ)) ^ (M - S))
  rw [hbase, mul_pow, sqrt_pow_of_nonneg _ M hx,
    sqrt_pow_of_nonneg _ (M - S) hxy, pow_sub₀ _ hsqrtNe hS, inv_pow]
  ring

/-- The elementary exponential-series inequality used after paper (5.88). -/
theorem natCast_pow_le_exp_mul_factorial (A B : ℕ) :
    (A : ℝ) ^ B ≤ Real.exp (A : ℝ) * (B.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp
    (x := (A : ℝ)) (Nat.cast_nonneg (α := ℝ) A) B
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (B.factorial : ℝ))] at h
  exact h

/--
The factor `√(X^M)` is absorbed by the product of leaf factorials at an
exponential cost.  This is the quantitative form of `m_l ∼ X` needed here;
only the lower bound `X ≤ m_l` and the exact mass ledger are used.
-/
theorem sqrt_pow_le_two_pow_mul_prod_sqrt_factorial
    {α : Type*} (s : Finset α) (q : α → ℕ) (X M : ℕ)
    (hX : ∀ a ∈ s, X ≤ q a)
    (hsum : ∑ a ∈ s, q a = M) :
    Real.sqrt ((X : ℝ) ^ M) ≤
      (2 : ℝ) ^ M * ∏ a ∈ s, Real.sqrt ((q a).factorial : ℝ) := by
  have hnat :
      X ^ M ≤ 4 ^ M * ∏ a ∈ s, (q a).factorial := by
    calc
      X ^ M = ∏ a ∈ s, X ^ q a := by
        rw [Finset.prod_pow_eq_pow_sum, hsum]
      _ ≤ ∏ a ∈ s, (q a) ^ q a := by
        apply Finset.prod_le_prod
        · intro a ha
          exact Nat.zero_le _
        · intro a ha
          exact Nat.pow_le_pow_left (hX a ha) (q a)
      _ ≤ ∏ a ∈ s, 4 ^ q a * (q a).factorial := by
        apply Finset.prod_le_prod
        · intro a ha
          exact Nat.zero_le _
        · intro a ha
          exact pow_self_le_four_pow_mul_factorial (q a)
      _ = 4 ^ M * ∏ a ∈ s, (q a).factorial := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
  have hreal :
      (X : ℝ) ^ M ≤
        (4 : ℝ) ^ M * ∏ a ∈ s, ((q a).factorial : ℝ) := by
    exact_mod_cast hnat
  calc
    Real.sqrt ((X : ℝ) ^ M) ≤
        Real.sqrt
          ((4 : ℝ) ^ M * ∏ a ∈ s, ((q a).factorial : ℝ)) :=
      Real.sqrt_le_sqrt hreal
    _ = Real.sqrt ((4 : ℝ) ^ M) *
          Real.sqrt (∏ a ∈ s, ((q a).factorial : ℝ)) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ M)]
    _ = (2 : ℝ) ^ M *
          ∏ a ∈ s, Real.sqrt ((q a).factorial : ℝ) := by
      rw [show (4 : ℝ) ^ M = ((2 : ℝ) ^ M) ^ 2 by
        calc
          (4 : ℝ) ^ M = ((2 : ℝ) ^ 2) ^ M := by norm_num
          _ = (2 : ℝ) ^ (2 * M) := by rw [← pow_mul]
          _ = (2 : ℝ) ^ (M * 2) := by rw [Nat.mul_comm]
          _ = ((2 : ℝ) ^ M) ^ 2 := by rw [pow_mul],
        Real.sqrt_sq (by positivity)]
      rw [Real.sqrt_prod s (fun a _ => by positivity)]

/--
The factor `√((XY)^(M-S))` is absorbed by `√((M-S)!)`.
The intentionally coarse cost `exp(M)` is uniform in `S`.
-/
theorem sqrt_xy_pow_sub_le_exp_mul_sqrt_factorial
    (X Y M S : ℕ) (hXY : X * Y ≤ M) :
    Real.sqrt (((X * Y : ℕ) : ℝ) ^ (M - S)) ≤
      Real.exp (M : ℝ) * Real.sqrt ((M - S).factorial : ℝ) := by
  have hpow :
      (((X * Y : ℕ) : ℝ) ^ (M - S)) ≤
        (M : ℝ) ^ (M - S) := by
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hXY) _
  have hexp :
      (M : ℝ) ^ (M - S) ≤
        Real.exp (M : ℝ) * ((M - S).factorial : ℝ) :=
    natCast_pow_le_exp_mul_factorial M (M - S)
  calc
    Real.sqrt (((X * Y : ℕ) : ℝ) ^ (M - S)) ≤
        Real.sqrt
          (Real.exp (M : ℝ) * ((M - S).factorial : ℝ)) :=
      Real.sqrt_le_sqrt (hpow.trans hexp)
    _ = Real.exp ((M : ℝ) / 2) *
          Real.sqrt ((M - S).factorial : ℝ) := by
      rw [Real.sqrt_mul (Real.exp_nonneg _), ← Real.exp_half]
    _ ≤ Real.exp (M : ℝ) *
          Real.sqrt ((M - S).factorial : ℝ) := by
      gcongr
      have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      linarith

/-- The per-`(N,X)` factorial envelope occurring after (5.87). -/
def singleScaleFactorialEnvelope (X Y M S : ℕ) : ℝ :=
  Real.sqrt ((X : ℝ) ^ M) *
    Real.sqrt (((X * Y : ℕ) : ℝ) ^ (M - S))

theorem singleScalePrintedFiberFactor_eq_factorialEnvelope
    (X Y M S : ℕ) (hX : 0 < X) (hY : 0 < Y) (hS : S ≤ M) :
    singleScalePrintedFiberFactor X Y M S =
      singleScaleFactorialEnvelope X Y M S := by
  exact singleScalePrintedFiberFactor_eq_envelope X Y M S hX hY hS

/--
Uniform factorial absorption used in the passage (5.88) → (5.89).
The explicit universal base is `2e`; later paper constants may enlarge it.
-/
theorem singleScaleFactorialEnvelope_le
    {α : Type*} (s : Finset α) (q : α → ℕ)
    (X Y M S : ℕ)
    (hX : ∀ a ∈ s, X ≤ q a)
    (hsum : ∑ a ∈ s, q a = M)
    (hXY : X * Y ≤ M) :
    singleScaleFactorialEnvelope X Y M S ≤
      (2 * Real.exp 1) ^ M *
        Real.sqrt ((M - S).factorial : ℝ) *
          ∏ a ∈ s, Real.sqrt ((q a).factorial : ℝ) := by
  have hleft :=
    sqrt_pow_le_two_pow_mul_prod_sqrt_factorial s q X M hX hsum
  have hright :=
    sqrt_xy_pow_sub_le_exp_mul_sqrt_factorial X Y M S hXY
  have hleft0 : 0 ≤ Real.sqrt ((X : ℝ) ^ M) := Real.sqrt_nonneg _
  have hright0 :
      0 ≤ Real.sqrt (((X * Y : ℕ) : ℝ) ^ (M - S)) :=
    Real.sqrt_nonneg _
  have hprod0 :
      0 ≤ ∏ a ∈ s, Real.sqrt ((q a).factorial : ℝ) := by positivity
  have hfac0 : 0 ≤ Real.sqrt ((M - S).factorial : ℝ) :=
    Real.sqrt_nonneg _
  have hexp :
      Real.exp (M : ℝ) = (Real.exp 1) ^ M := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  unfold singleScaleFactorialEnvelope
  calc
    Real.sqrt ((X : ℝ) ^ M) *
        Real.sqrt (((X * Y : ℕ) : ℝ) ^ (M - S)) ≤
      ((2 : ℝ) ^ M *
          ∏ a ∈ s, Real.sqrt ((q a).factorial : ℝ)) *
        (Real.exp (M : ℝ) *
          Real.sqrt ((M - S).factorial : ℝ)) :=
      mul_le_mul hleft hright hright0
        (mul_nonneg (by positivity) hprod0)
    _ = (2 * Real.exp 1) ^ M *
        Real.sqrt ((M - S).factorial : ℝ) *
          ∏ a ∈ s, Real.sqrt ((q a).factorial : ℝ) := by
      rw [hexp, mul_pow]
      ring

/--
Specialization to an active `(N,X)` fiber.  This packages exactly the
`m_l ∈ [X,2X)` and `XY ≤ m_{N,X}` ledgers from (5.75), so the final
single-scale assembly does not need to repeat the factorial arithmetic.
-/
theorem singleScaleNXFactorialEnvelope_le
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) (S : ℕ) :
    singleScaleFactorialEnvelope
        a.2 (singleScaleSigma2 Nm mu a).2
        (multiplicityNX Nm mu a) S ≤
      (2 * Real.exp 1) ^ multiplicityNX Nm mu a *
        Real.sqrt ((multiplicityNX Nm mu a - S).factorial : ℝ) *
          ∏ l ∈ leavesAtNX Nm mu a,
            Real.sqrt ((leafMultiplicity mu l).factorial : ℝ) := by
  apply singleScaleFactorialEnvelope_le
  · intro l hl
    have hclass : singleScaleSigma1 Nm mu l = a :=
      (Finset.mem_filter.mp hl).2
    simpa [hclass] using (sigma1_bucket Nm mu l).1
  · rfl
  · exact (multiplicityNX_bounds Nm mu ha).1

/--
Active-fiber specialization of the exact printed-factor normalization.
-/
theorem singleScaleNXPrintedFiberFactor_eq_envelope
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) (S : ℕ)
    (hS : S ≤ multiplicityNX Nm mu a) :
    singleScalePrintedFiberFactor
        a.2 (singleScaleSigma2 Nm mu a).2
        (multiplicityNX Nm mu a) S =
      singleScaleFactorialEnvelope
        a.2 (singleScaleSigma2 Nm mu a).2
        (multiplicityNX Nm mu a) S := by
  apply singleScalePrintedFiberFactor_eq_factorialEnvelope
  · exact lt_of_lt_of_le Nat.zero_lt_one (one_le_nxClass_X Nm mu ha)
  · unfold singleScaleSigma2 dyadicFloor
    positivity
  · exact hS

/-! ### Global `(N,X)` factorial aggregation -/

/--
The product of square-root factorials is bounded by the square-root
factorial of the total mass.  This is the square-root form of the
multinomial divisibility ledger.
-/
theorem prod_sqrt_factorial_le_sqrt_factorial_sum
    {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∏ a ∈ s, Real.sqrt ((f a).factorial : ℝ)) ≤
      Real.sqrt ((∑ a ∈ s, f a).factorial : ℝ) := by
  have hnat := prod_factorial_le_factorial_sum s f
  have hreal :
      (∏ a ∈ s, ((f a).factorial : ℝ)) ≤
        ((∑ a ∈ s, f a).factorial : ℝ) := by
    exact_mod_cast hnat
  calc
    (∏ a ∈ s, Real.sqrt ((f a).factorial : ℝ)) =
        Real.sqrt (∏ a ∈ s, ((f a).factorial : ℝ)) := by
      symm
      rw [Real.sqrt_prod s (fun a _ => by positivity)]
    _ ≤ Real.sqrt ((∑ a ∈ s, f a).factorial : ℝ) :=
      Real.sqrt_le_sqrt hreal

/--
Square-root factorial deficits aggregate across a finite partition.  The
pointwise condition is what prevents truncated natural subtraction from
losing mass.
-/
theorem prod_sqrt_factorial_sub_le
    {α : Type*} (s : Finset α) (M S : α → ℕ)
    (hsub : ∀ a ∈ s, S a ≤ M a) :
    (∏ a ∈ s, Real.sqrt ((M a - S a).factorial : ℝ)) ≤
      Real.sqrt
        (((∑ a ∈ s, M a) - ∑ a ∈ s, S a).factorial : ℝ) := by
  simpa [Finset.sum_tsub_distrib s hsub] using
    prod_sqrt_factorial_le_sqrt_factorial_sum s (fun a => M a - S a)

/--
The deficit factorials from all active `(N,X)` fibers combine into the
single global `(m-s)!` factor in (5.89).
-/
theorem prod_nx_sqrt_factorial_sub_le
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (S : NXClass → ℕ)
    (hsub : ∀ a ∈ nxCarrier Nm mu, S a ≤ multiplicityNX Nm mu a) :
    (∏ a ∈ nxCarrier Nm mu,
        Real.sqrt ((multiplicityNX Nm mu a - S a).factorial : ℝ)) ≤
      Real.sqrt
        ((totalMultiplicity mu -
          ∑ a ∈ nxCarrier Nm mu, S a).factorial : ℝ) := by
  simpa [sum_multiplicityNX] using
    prod_sqrt_factorial_sub_le
      (nxCarrier Nm mu) (multiplicityNX Nm mu) S hsub

/--
Multiplying the per-fiber bounds gives precisely one exponential factor,
one global deficit factorial, and one factorial for every original leaf.
This is the complete numerical passage from the product following (5.88)
to the factorial part of (5.89).
-/
theorem prod_singleScaleFactorialEnvelope_le
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (S : NXClass → ℕ)
    (hsub : ∀ a ∈ nxCarrier Nm mu, S a ≤ multiplicityNX Nm mu a) :
    (∏ a ∈ nxCarrier Nm mu,
        singleScaleFactorialEnvelope
          a.2 (singleScaleSigma2 Nm mu a).2
          (multiplicityNX Nm mu a) (S a)) ≤
      (2 * Real.exp 1) ^ totalMultiplicity mu *
        Real.sqrt
          ((totalMultiplicity mu -
            ∑ a ∈ nxCarrier Nm mu, S a).factorial : ℝ) *
        ∏ l : HeppLeaf t,
          Real.sqrt ((leafMultiplicity mu l).factorial : ℝ) := by
  let B : ℝ := 2 * Real.exp 1
  let deficit : NXClass → ℝ := fun a =>
    Real.sqrt ((multiplicityNX Nm mu a - S a).factorial : ℝ)
  let leafFac : HeppLeaf t → ℝ := fun l =>
    Real.sqrt ((leafMultiplicity mu l).factorial : ℝ)
  have hpoint :
      ∀ a ∈ nxCarrier Nm mu,
        singleScaleFactorialEnvelope
            a.2 (singleScaleSigma2 Nm mu a).2
            (multiplicityNX Nm mu a) (S a) ≤
          B ^ multiplicityNX Nm mu a * deficit a *
            ∏ l ∈ leavesAtNX Nm mu a, leafFac l := by
    intro a ha
    exact singleScaleNXFactorialEnvelope_le Nm mu ha (S a)
  have henvNonneg :
      ∀ a ∈ nxCarrier Nm mu,
        0 ≤ singleScaleFactorialEnvelope
          a.2 (singleScaleSigma2 Nm mu a).2
          (multiplicityNX Nm mu a) (S a) := by
    intro a ha
    unfold singleScaleFactorialEnvelope
    positivity
  have hdeficit :
      (∏ a ∈ nxCarrier Nm mu, deficit a) ≤
        Real.sqrt
          ((totalMultiplicity mu -
            ∑ a ∈ nxCarrier Nm mu, S a).factorial : ℝ) := by
    exact prod_nx_sqrt_factorial_sub_le Nm mu S hsub
  have hleaf :
      (∏ a ∈ nxCarrier Nm mu,
          ∏ l ∈ leavesAtNX Nm mu a, leafFac l) =
        ∏ l : HeppLeaf t, leafFac l := by
    simpa [leavesAtNX, nxCarrier] using
      (Finset.prod_fiberwise_of_maps_to
        (s := (Finset.univ : Finset (HeppLeaf t)))
        (t := nxCarrier Nm mu) (g := singleScaleSigma1 Nm mu)
        (fun l hl => Finset.mem_image_of_mem _ hl) leafFac)
  calc
    (∏ a ∈ nxCarrier Nm mu,
        singleScaleFactorialEnvelope
          a.2 (singleScaleSigma2 Nm mu a).2
          (multiplicityNX Nm mu a) (S a)) ≤
        ∏ a ∈ nxCarrier Nm mu,
          (B ^ multiplicityNX Nm mu a * deficit a *
            ∏ l ∈ leavesAtNX Nm mu a, leafFac l) := by
      apply Finset.prod_le_prod
      · exact henvNonneg
      · exact hpoint
    _ = B ^ totalMultiplicity mu *
        (∏ a ∈ nxCarrier Nm mu, deficit a) *
        (∏ a ∈ nxCarrier Nm mu,
          ∏ l ∈ leavesAtNX Nm mu a, leafFac l) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, sum_multiplicityNX]
    _ ≤ B ^ totalMultiplicity mu *
        Real.sqrt
          ((totalMultiplicity mu -
            ∑ a ∈ nxCarrier Nm mu, S a).factorial : ℝ) *
        (∏ a ∈ nxCarrier Nm mu,
          ∏ l ∈ leavesAtNX Nm mu a, leafFac l) := by
      gcongr
    _ = (2 * Real.exp 1) ^ totalMultiplicity mu *
        Real.sqrt
          ((totalMultiplicity mu -
            ∑ a ∈ nxCarrier Nm mu, S a).factorial : ℝ) *
        ∏ l : HeppLeaf t,
          Real.sqrt ((leafMultiplicity mu l).factorial : ℝ) := by
      rw [hleaf]

/--
Paper-facing form of the global factorial absorption: the left side is the
literal product of `(X √Y)^M (XY)^(-S/2)` from the sentence after (5.88).
-/
theorem prod_singleScalePrintedFiberFactor_le
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (S : NXClass → ℕ)
    (hsub : ∀ a ∈ nxCarrier Nm mu, S a ≤ multiplicityNX Nm mu a) :
    (∏ a ∈ nxCarrier Nm mu,
        singleScalePrintedFiberFactor
          a.2 (singleScaleSigma2 Nm mu a).2
          (multiplicityNX Nm mu a) (S a)) ≤
      (2 * Real.exp 1) ^ totalMultiplicity mu *
        Real.sqrt
          ((totalMultiplicity mu -
            ∑ a ∈ nxCarrier Nm mu, S a).factorial : ℝ) *
        ∏ l : HeppLeaf t,
          Real.sqrt ((leafMultiplicity mu l).factorial : ℝ) := by
  calc
    (∏ a ∈ nxCarrier Nm mu,
        singleScalePrintedFiberFactor
          a.2 (singleScaleSigma2 Nm mu a).2
          (multiplicityNX Nm mu a) (S a)) =
        ∏ a ∈ nxCarrier Nm mu,
          singleScaleFactorialEnvelope
            a.2 (singleScaleSigma2 Nm mu a).2
            (multiplicityNX Nm mu a) (S a) := by
      apply Finset.prod_congr rfl
      intro a ha
      exact singleScaleNXPrintedFiberFactor_eq_envelope
        Nm mu ha (S a) (hsub a ha)
    _ ≤ _ := prod_singleScaleFactorialEnvelope_le Nm mu S hsub

/--
The same result with the global ledgers `∑ M_{N,X}=m` and
`∑ S_{N,X}=s` rewritten exactly as they appear in (5.89).
-/
theorem prod_singleScalePrintedFiberFactor_le_of_ledgers
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (S : NXClass → ℕ) (m s : ℕ)
    (hsub : ∀ a ∈ nxCarrier Nm mu, S a ≤ multiplicityNX Nm mu a)
    (hm : totalMultiplicity mu = m)
    (hs : ∑ a ∈ nxCarrier Nm mu, S a = s) :
    (∏ a ∈ nxCarrier Nm mu,
        singleScalePrintedFiberFactor
          a.2 (singleScaleSigma2 Nm mu a).2
          (multiplicityNX Nm mu a) (S a)) ≤
      (2 * Real.exp 1) ^ m *
        Real.sqrt ((m - s).factorial : ℝ) *
        ∏ l : HeppLeaf t,
          Real.sqrt ((leafMultiplicity mu l).factorial : ℝ) := by
  simpa [hm, hs] using
    prod_singleScalePrintedFiberFactor_le Nm mu S hsub

end

end Anderson4D
