import Mathlib.Algebra.BigOperators.Sym
import Anderson4D.Continuum.CovariancePeriodizationDerivativeClosure
import Anderson4D.Continuum.FiniteProductEighthDerivative
import Anderson4D.Continuum.PeriodicFourierIBPPeriodicity

/-!
# Fourier decay for finite products of periodized covariance factors

This file closes the analytic bridge between the coordinate-line
periodization estimates and eight-fold periodic Fourier integration by
parts.  The derivative allocation is kept in symmetric-power form until
the multinomial sum is evaluated.  Consequently the only combinatorial
loss is the eighth power of the number of factors, and compact support
does not introduce a lattice-cardinality factor.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace SmoothCutoff

variable {ι : Type*} [DecidableEq ι]

/-- A true covariance-periodization factor restricted to a translated
coordinate line. -/
def etaPeriodizationCoordLineFactor
    (ρ : SmoothCutoff) (ε : ℝ) (x : R4) (i : Fin dim)
    (a t : ℝ) : ℝ :=
  ρ.etaPeriodizationR4 ε (Function.update x i (a + t))

/-- A translated coordinate line of the true periodization is `C⁸`. -/
theorem contDiff_etaPeriodizationCoordLineFactor_eight
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : R4) (i : Fin dim) (a : ℝ) :
    ContDiff ℝ 8 (ρ.etaPeriodizationCoordLineFactor ε x i a) := by
  unfold etaPeriodizationCoordLineFactor
  exact
    (ρ.contDiff_etaPeriodizationR4_coordLine_eight hε x i).comp
      (contDiff_const.add contDiff_id)

/-- Translation commutes with every iterated derivative of a coordinate
line factor. -/
theorem iteratedDeriv_etaPeriodizationCoordLineFactor
    (ρ : SmoothCutoff) (ε : ℝ) (x : R4) (i : Fin dim)
    (a t : ℝ) (r : ℕ) :
    iteratedDeriv r
        (ρ.etaPeriodizationCoordLineFactor ε x i a) t =
      iteratedDeriv r
        (fun s =>
          ρ.etaPeriodizationR4 ε (Function.update x i s))
        (a + t) := by
  change
    iteratedDeriv r
        (fun z =>
          ρ.etaPeriodizationR4 ε
            (Function.update x i (a + z))) t =
      iteratedDeriv r
        (fun s =>
          ρ.etaPeriodizationR4 ε (Function.update x i s))
        (a + t)
  exact congrFun
    (iteratedDeriv_comp_const_add r
      (fun s =>
        ρ.etaPeriodizationR4 ε (Function.update x i s)) a) t

/-- Global derivative majorant for a translated coordinate-line factor.
There is no lattice-cardinality loss. -/
theorem abs_iteratedDeriv_etaPeriodizationCoordLineFactor_le
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : R4) (i : Fin dim) (a t : ℝ)
    {r : ℕ} (hr : r ≤ 8) :
    |iteratedDeriv r
        (ρ.etaPeriodizationCoordLineFactor ε x i a) t| ≤
      (ρ.etaDerivativeMajorantConstant * ε⁻¹ ^ r) *
        ρ.auxiliaryCutoff.etaPeriodizationR4 ε
          (Function.update x i (a + t)) := by
  rw [ρ.iteratedDeriv_etaPeriodizationCoordLineFactor ε x i a t r]
  exact
    ρ.abs_iteratedDeriv_etaPeriodizationR4_coordLine_le_global
      hε x i (a + t) hr

/-- A finite product of true covariance-periodization coordinate lines.
The index finset consists of slots, so equal factor data remain distinct. -/
def etaPeriodizationCoordLineProduct
    (ρ : SmoothCutoff) (u : Finset ι) (ε : ℝ)
    (x : ι → R4) (i : ι → Fin dim) (a : ι → ℝ)
    (t : ℝ) : ℝ :=
  ∏ j ∈ u,
    ρ.etaPeriodizationCoordLineFactor ε (x j) (i j) (a j) t

omit [DecidableEq ι] in
/-- The product of finitely many true coordinate-line factors is `C⁸`. -/
theorem contDiff_etaPeriodizationCoordLineProduct_eight
    (ρ : SmoothCutoff) (u : Finset ι) {ε : ℝ} (hε : 0 < ε)
    (x : ι → R4) (i : ι → Fin dim) (a : ι → ℝ) :
    ContDiff ℝ 8
      (ρ.etaPeriodizationCoordLineProduct u ε x i a) := by
  unfold etaPeriodizationCoordLineProduct
  apply contDiff_prod
  intro j _hj
  exact
    ρ.contDiff_etaPeriodizationCoordLineFactor_eight
      hε (x j) (i j) (a j)

/-- The product of the auxiliary periodizations which majorizes all
derivative allocations of the true product. -/
def etaAuxiliaryCoordLineProduct
    (ρ : SmoothCutoff) (u : Finset ι) (ε : ℝ)
    (x : ι → R4) (i : ι → Fin dim) (a : ι → ℝ)
    (t : ℝ) : ℝ :=
  ∏ j ∈ u,
    ρ.auxiliaryCutoff.etaPeriodizationR4 ε
      (Function.update (x j) (i j) (a j + t))

omit [DecidableEq ι] in
/-- The auxiliary product is continuous (indeed `C⁸`). -/
theorem contDiff_etaAuxiliaryCoordLineProduct_eight
    (ρ : SmoothCutoff) (u : Finset ι) {ε : ℝ} (hε : 0 < ε)
    (x : ι → R4) (i : ι → Fin dim) (a : ι → ℝ) :
    ContDiff ℝ 8
      (ρ.etaAuxiliaryCoordLineProduct u ε x i a) := by
  unfold etaAuxiliaryCoordLineProduct
  apply contDiff_prod
  intro j _hj
  exact
    (ρ.auxiliaryCutoff.contDiff_etaPeriodizationR4_coordLine_eight
      hε (x j) (i j)).comp
      (contDiff_const.add contDiff_id)

/-- The arbitrary-representative periodization is nonnegative. -/
theorem etaPeriodizationR4_nonneg
    (ρ : SmoothCutoff) (ε : ℝ) (y : R4) :
    0 ≤ ρ.etaPeriodizationR4 ε y := by
  rw [← ρ.etaEpsT4_periodizeR4_eq_etaPeriodizationR4 ε y]
  exact ρ.etaEpsT4_nonneg ε (periodizeR4 y)

omit [DecidableEq ι] in
/-- Pointwise nonnegativity of the auxiliary product. -/
theorem etaAuxiliaryCoordLineProduct_nonneg
    (ρ : SmoothCutoff) (u : Finset ι) (ε : ℝ)
    (x : ι → R4) (i : ι → Fin dim) (a : ι → ℝ)
    (t : ℝ) :
    0 ≤ ρ.etaAuxiliaryCoordLineProduct u ε x i a t := by
  unfold etaAuxiliaryCoordLineProduct
  exact Finset.prod_nonneg fun j _hj =>
    ρ.auxiliaryCutoff.etaPeriodizationR4_nonneg ε
      (Function.update (x j) (i j) (a j + t))

/-- Every component count of an order-`r` symmetric allocation is at
most `r`. -/
theorem sym_count_le_order
    {r : ℕ} (p : Sym ι r) (j : ι) :
    (p : Multiset ι).count j ≤ r := by
  simpa using Multiset.count_le_card j (p : Multiset ι)

/-- The total multiplicity of all weak allocations of `r` derivative
slots is exactly the `r`-th power of the number of product slots. -/
theorem sum_countPerms_sym_eq_card_pow
    (u : Finset ι) (r : ℕ) :
    (∑ p ∈ u.sym r,
        ((p : Multiset ι).countPerms : ℝ)) =
      (u.card : ℝ) ^ r := by
  have h :=
    Finset.sum_pow (s := u)
      (fun _ : ι => (1 : ℝ)) r
  simpa using h.symm

/-- Exact algebraic collapse of one derivative allocation.  The total
power of `ε⁻¹` is the derivative order, not the number of factors times
that order. -/
theorem prod_derivativeMajorant_eq
    (ρ : SmoothCutoff) (u : Finset ι) (ε : ℝ)
    (x : ι → R4) (i : ι → Fin dim) (a : ι → ℝ)
    (t : ℝ) {r : ℕ} {p : Sym ι r}
    (hp : p ∈ u.sym r) :
    (∏ j ∈ u,
        ((ρ.etaDerivativeMajorantConstant *
            ε⁻¹ ^ (p : Multiset ι).count j) *
          ρ.auxiliaryCutoff.etaPeriodizationR4 ε
            (Function.update (x j) (i j) (a j + t)))) =
      ρ.etaDerivativeMajorantConstant ^ u.card *
        ε⁻¹ ^ r *
        ρ.etaAuxiliaryCoordLineProduct u ε x i a t := by
  unfold etaAuxiliaryCoordLineProduct
  calc
    (∏ j ∈ u,
        ((ρ.etaDerivativeMajorantConstant *
            ε⁻¹ ^ (p : Multiset ι).count j) *
          ρ.auxiliaryCutoff.etaPeriodizationR4 ε
            (Function.update (x j) (i j) (a j + t)))) =
      (∏ j ∈ u, ρ.etaDerivativeMajorantConstant) *
        (∏ j ∈ u, ε⁻¹ ^ (p : Multiset ι).count j) *
        ∏ j ∈ u,
          ρ.auxiliaryCutoff.etaPeriodizationR4 ε
            (Function.update (x j) (i j) (a j + t)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    _ =
      ρ.etaDerivativeMajorantConstant ^ u.card *
        ε⁻¹ ^ r *
        ∏ j ∈ u,
          ρ.auxiliaryCutoff.etaPeriodizationR4 ε
            (Function.update (x j) (i j) (a j + t)) := by
      rw [Finset.prod_const, Finset.prod_pow_eq_pow_sum,
        Finset.sum_count_of_mem_sym hp]

/-- Derivative majorant for every order through eight.  The symmetric
allocation sum costs exactly `card(u)^r`; in particular the order-eight
cost is `card(u)^8`. -/
theorem abs_iteratedDeriv_etaPeriodizationCoordLineProduct_le
    (ρ : SmoothCutoff) (u : Finset ι) {ε : ℝ} (hε : 0 < ε)
    (x : ι → R4) (i : ι → Fin dim) (a : ι → ℝ)
    (t : ℝ) {r : ℕ} (hr : r ≤ 8) :
    |iteratedDeriv r
        (ρ.etaPeriodizationCoordLineProduct u ε x i a) t| ≤
      (u.card : ℝ) ^ r *
        (ρ.etaDerivativeMajorantConstant ^ u.card *
          ε⁻¹ ^ r *
          ρ.etaAuxiliaryCoordLineProduct u ε x i a t) := by
  have hprod :
      |iteratedDeriv r
          (ρ.etaPeriodizationCoordLineProduct u ε x i a) t| ≤
        ∑ p ∈ u.sym r,
          ((p : Multiset ι).countPerms : ℝ) *
            ∏ j ∈ u,
              |iteratedDeriv
                ((p : Multiset ι).count j)
                (ρ.etaPeriodizationCoordLineFactor
                  ε (x j) (i j) (a j)) t| := by
    have h :=
      norm_iteratedFDeriv_prod_le
        (u := u)
        (f := fun j =>
          ρ.etaPeriodizationCoordLineFactor
            ε (x j) (i j) (a j))
        (fun j _hj =>
          ρ.contDiff_etaPeriodizationCoordLineFactor_eight
            hε (x j) (i j) (a j))
        (x := t) (n := r)
        (by exact_mod_cast hr)
    change
      |iteratedDeriv r
          (fun s =>
            ∏ j ∈ u,
              ρ.etaPeriodizationCoordLineFactor
                ε (x j) (i j) (a j) s) t| ≤
        ∑ p ∈ u.sym r,
          ((p : Multiset ι).countPerms : ℝ) *
            ∏ j ∈ u,
              |iteratedDeriv
                ((p : Multiset ι).count j)
                (ρ.etaPeriodizationCoordLineFactor
                  ε (x j) (i j) (a j)) t|
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      Real.norm_eq_abs] using h
  calc
    |iteratedDeriv r
        (ρ.etaPeriodizationCoordLineProduct u ε x i a) t| ≤
      ∑ p ∈ u.sym r,
        ((p : Multiset ι).countPerms : ℝ) *
          ∏ j ∈ u,
            |iteratedDeriv
              ((p : Multiset ι).count j)
              (ρ.etaPeriodizationCoordLineFactor
                ε (x j) (i j) (a j)) t| :=
      hprod
    _ ≤
      ∑ p ∈ u.sym r,
        ((p : Multiset ι).countPerms : ℝ) *
          (ρ.etaDerivativeMajorantConstant ^ u.card *
            ε⁻¹ ^ r *
            ρ.etaAuxiliaryCoordLineProduct u ε x i a t) := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left
      · calc
          (∏ j ∈ u,
              |iteratedDeriv
                ((p : Multiset ι).count j)
                (ρ.etaPeriodizationCoordLineFactor
                  ε (x j) (i j) (a j)) t|) ≤
            ∏ j ∈ u,
              ((ρ.etaDerivativeMajorantConstant *
                  ε⁻¹ ^ (p : Multiset ι).count j) *
                ρ.auxiliaryCutoff.etaPeriodizationR4 ε
                  (Function.update (x j) (i j) (a j + t))) := by
            apply Finset.prod_le_prod
            · intro j _hj
              exact abs_nonneg _
            · intro j _hj
              exact
                ρ.abs_iteratedDeriv_etaPeriodizationCoordLineFactor_le
                  hε (x j) (i j) (a j) t
                  (sym_count_le_order p j |>.trans hr)
          _ =
            ρ.etaDerivativeMajorantConstant ^ u.card *
              ε⁻¹ ^ r *
              ρ.etaAuxiliaryCoordLineProduct u ε x i a t :=
            ρ.prod_derivativeMajorant_eq u ε x i a t hp
      · positivity
    _ =
      (∑ p ∈ u.sym r,
          ((p : Multiset ι).countPerms : ℝ)) *
        (ρ.etaDerivativeMajorantConstant ^ u.card *
          ε⁻¹ ^ r *
          ρ.etaAuxiliaryCoordLineProduct u ε x i a t) := by
      rw [Finset.sum_mul]
    _ =
      (u.card : ℝ) ^ r *
        (ρ.etaDerivativeMajorantConstant ^ u.card *
          ε⁻¹ ^ r *
          ρ.etaAuxiliaryCoordLineProduct u ε x i a t) := by
      rw [sum_countPerms_sym_eq_card_pow]

/-- The order-eight specialization used in periodic Fourier decay. -/
theorem abs_iteratedDeriv_eight_etaPeriodizationCoordLineProduct_le
    (ρ : SmoothCutoff) (u : Finset ι) {ε : ℝ} (hε : 0 < ε)
    (x : ι → R4) (i : ι → Fin dim) (a : ι → ℝ)
    (t : ℝ) :
    |iteratedDeriv 8
        (ρ.etaPeriodizationCoordLineProduct u ε x i a) t| ≤
      (u.card : ℝ) ^ 8 *
        (ρ.etaDerivativeMajorantConstant ^ u.card *
          ε⁻¹ ^ 8 *
          ρ.etaAuxiliaryCoordLineProduct u ε x i a t) :=
  ρ.abs_iteratedDeriv_etaPeriodizationCoordLineProduct_le
    u hε x i a t le_rfl

/-- Each translated coordinate-line factor has period `2π`. -/
theorem etaPeriodizationCoordLineFactor_add_two_pi
    (ρ : SmoothCutoff) (ε : ℝ) (x : R4) (i : Fin dim)
    (a t : ℝ) :
    ρ.etaPeriodizationCoordLineFactor ε x i a
        (t + 2 * Real.pi) =
      ρ.etaPeriodizationCoordLineFactor ε x i a t := by
  unfold etaPeriodizationCoordLineFactor
  convert
    ρ.etaPeriodizationR4_update_add_two_pi
      ε x i (a + t) using 1
  ring_nf

omit [DecidableEq ι] in
/-- The finite product has period `2π`. -/
theorem periodic_etaPeriodizationCoordLineProduct
    (ρ : SmoothCutoff) (u : Finset ι) (ε : ℝ)
    (x : ι → R4) (i : ι → Fin dim) (a : ι → ℝ) :
    Function.Periodic
      (ρ.etaPeriodizationCoordLineProduct u ε x i a)
      (2 * Real.pi) := by
  intro t
  unfold etaPeriodizationCoordLineProduct
  apply Finset.prod_congr rfl
  intro j _hj
  exact
    ρ.etaPeriodizationCoordLineFactor_add_two_pi
      ε (x j) (i j) (a j) t

/-- Complexification of the real covariance product. -/
def etaPeriodizationCoordLineProductC
    (ρ : SmoothCutoff) (u : Finset ι) (ε : ℝ)
    (x : ι → R4) (i : ι → Fin dim) (a : ι → ℝ)
    (t : ℝ) : ℂ :=
  (ρ.etaPeriodizationCoordLineProduct u ε x i a t : ℂ)

omit [DecidableEq ι] in
/-- The complexified product is `C⁸` over `ℝ`. -/
theorem contDiff_etaPeriodizationCoordLineProductC_eight
    (ρ : SmoothCutoff) (u : Finset ι) {ε : ℝ} (hε : 0 < ε)
    (x : ι → R4) (i : ι → Fin dim) (a : ι → ℝ) :
    ContDiff ℝ 8
      (ρ.etaPeriodizationCoordLineProductC u ε x i a) := by
  change
    ContDiff ℝ 8
      (Complex.ofRealCLM ∘
        ρ.etaPeriodizationCoordLineProduct u ε x i a)
  exact
    Complex.ofRealCLM.contDiff.comp
      (ρ.contDiff_etaPeriodizationCoordLineProduct_eight
        u hε x i a)

omit [DecidableEq ι] in
/-- Complexification preserves the derivative norm up to the (unit)
operator norm of `ofRealCLM`. -/
theorem norm_iteratedDeriv_etaPeriodizationCoordLineProductC_le_abs
    (ρ : SmoothCutoff) (u : Finset ι) {ε : ℝ} (hε : 0 < ε)
    (x : ι → R4) (i : ι → Fin dim) (a : ι → ℝ)
    (t : ℝ) {r : ℕ} (hr : r ≤ 8) :
    ‖iteratedDeriv r
        (ρ.etaPeriodizationCoordLineProductC u ε x i a) t‖ ≤
      |iteratedDeriv r
        (ρ.etaPeriodizationCoordLineProduct u ε x i a) t| := by
  change
    ‖iteratedDeriv r
        (fun s =>
          Complex.ofRealCLM
            (ρ.etaPeriodizationCoordLineProduct u ε x i a s)) t‖ ≤
      |iteratedDeriv r
        (ρ.etaPeriodizationCoordLineProduct u ε x i a) t|
  have h :=
    Complex.ofRealCLM.norm_iteratedFDeriv_comp_left
      (x := t)
      ((ρ.contDiff_etaPeriodizationCoordLineProduct_eight
        u hε x i a).contDiffAt)
      (by exact_mod_cast hr)
  simpa only [Function.comp_def,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Complex.ofRealCLM_norm, one_mul, Real.norm_eq_abs] using h

/-- Pointwise complex derivative majorant for every order through eight. -/
theorem norm_iteratedDeriv_etaPeriodizationCoordLineProductC_le
    (ρ : SmoothCutoff) (u : Finset ι) {ε : ℝ} (hε : 0 < ε)
    (x : ι → R4) (i : ι → Fin dim) (a : ι → ℝ)
    (t : ℝ) {r : ℕ} (hr : r ≤ 8) :
    ‖iteratedDeriv r
        (ρ.etaPeriodizationCoordLineProductC u ε x i a) t‖ ≤
      (u.card : ℝ) ^ r *
        (ρ.etaDerivativeMajorantConstant ^ u.card *
          ε⁻¹ ^ r *
          ρ.etaAuxiliaryCoordLineProduct u ε x i a t) :=
  (ρ.norm_iteratedDeriv_etaPeriodizationCoordLineProductC_le_abs
      u hε x i a t hr).trans
    (ρ.abs_iteratedDeriv_etaPeriodizationCoordLineProduct_le
      u hε x i a t hr)

omit [DecidableEq ι] in
/-- The complexified product has period `2π`. -/
theorem periodic_etaPeriodizationCoordLineProductC
    (ρ : SmoothCutoff) (u : Finset ι) (ε : ℝ)
    (x : ι → R4) (i : ι → Fin dim) (a : ι → ℝ) :
    Function.Periodic
      (ρ.etaPeriodizationCoordLineProductC u ε x i a)
      (2 * Real.pi) := by
  intro t
  exact congrArg Complex.ofReal
    (ρ.periodic_etaPeriodizationCoordLineProduct u ε x i a t)

omit [DecidableEq ι] in
/-- The complex covariance product supplies all endpoint jets required
for eight integrations by parts. -/
theorem negPiPiPeriodicJets_etaPeriodizationCoordLineProductC
    (ρ : SmoothCutoff) (u : Finset ι) (ε : ℝ)
    (x : ι → R4) (i : ι → Fin dim) (a : ι → ℝ) :
    NegPiPiPeriodicJets
      (ρ.etaPeriodizationCoordLineProductC u ε x i a) 8 :=
  negPiPiPeriodicJets_of_two_pi_periodic
    (ρ.periodic_etaPeriodizationCoordLineProductC u ε x i a) 8

/-- Eight-fold periodic integration by parts with the derivative
integral replaced by the honest auxiliary-periodization majorant. -/
theorem norm_fourierCoeffOn_etaPeriodizationCoordLineProductC_le_auxIntegral
    (ρ : SmoothCutoff) (u : Finset ι) {ε : ℝ} (hε : 0 < ε)
    (x : ι → R4) (i : ι → Fin dim) (a : ι → ℝ)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn
        (neg_lt_self Real.pi_pos)
        (ρ.etaPeriodizationCoordLineProductC u ε x i a) n‖ ≤
      |(n : ℝ)|⁻¹ ^ 8 * (2 * Real.pi)⁻¹ *
        ∫ t in -Real.pi..Real.pi,
          (u.card : ℝ) ^ 8 *
            (ρ.etaDerivativeMajorantConstant ^ u.card *
              ε⁻¹ ^ 8 *
              ρ.etaAuxiliaryCoordLineProduct u ε x i a t) := by
  have hf :
      ContDiff ℝ 8
        (ρ.etaPeriodizationCoordLineProductC u ε x i a) :=
    ρ.contDiff_etaPeriodizationCoordLineProductC_eight
      u hε x i a
  refine
    (norm_fourierCoeffOn_negPi_pi_le_eighthDeriv_integral
      hn hf
      (ρ.negPiPiPeriodicJets_etaPeriodizationCoordLineProductC
        u ε x i a)).trans ?_
  have hleft :
      IntervalIntegrable
        (fun t =>
          ‖iteratedDeriv 8
            (ρ.etaPeriodizationCoordLineProductC u ε x i a) t‖)
        volume (-Real.pi) Real.pi :=
    (hf.continuous_iteratedDeriv' 8).norm.intervalIntegrable _ _
  have hright :
      IntervalIntegrable
        (fun t =>
          (u.card : ℝ) ^ 8 *
            (ρ.etaDerivativeMajorantConstant ^ u.card *
              ε⁻¹ ^ 8 *
              ρ.etaAuxiliaryCoordLineProduct u ε x i a t))
        volume (-Real.pi) Real.pi :=
    (continuous_const.mul
      (continuous_const.mul
        (ρ.contDiff_etaAuxiliaryCoordLineProduct_eight
          u hε x i a).continuous)).intervalIntegrable _ _
  apply mul_le_mul_of_nonneg_left
  · exact intervalIntegral.integral_mono
      (le_of_lt (neg_lt_self Real.pi_pos))
      hleft hright fun t =>
        ρ.norm_iteratedDeriv_etaPeriodizationCoordLineProductC_le
          u hε x i a t le_rfl
  · exact
      mul_nonneg
        (pow_nonneg (inv_nonneg.mpr (abs_nonneg _)) _)
        (inv_nonneg.mpr (by positivity))

/-- Pulled-constant form of the preceding estimate.  This is the
reusable `|n|⁻⁸` Fourier-decay statement; the remaining integral contains
only true auxiliary-cutoff periodizations. -/
theorem norm_fourierCoeffOn_etaPeriodizationCoordLineProductC_le
    (ρ : SmoothCutoff) (u : Finset ι) {ε : ℝ} (hε : 0 < ε)
    (x : ι → R4) (i : ι → Fin dim) (a : ι → ℝ)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn
        (neg_lt_self Real.pi_pos)
        (ρ.etaPeriodizationCoordLineProductC u ε x i a) n‖ ≤
      |(n : ℝ)|⁻¹ ^ 8 * (2 * Real.pi)⁻¹ *
        ((u.card : ℝ) ^ 8 *
          ρ.etaDerivativeMajorantConstant ^ u.card *
          ε⁻¹ ^ 8) *
        ∫ t in -Real.pi..Real.pi,
          ρ.etaAuxiliaryCoordLineProduct u ε x i a t := by
  have h :=
    ρ.norm_fourierCoeffOn_etaPeriodizationCoordLineProductC_le_auxIntegral
      u hε x i a hn
  rw [intervalIntegral.integral_const_mul] at h
  rw [intervalIntegral.integral_const_mul] at h
  simpa only [mul_assoc] using h

end SmoothCutoff

end

end Anderson4D
