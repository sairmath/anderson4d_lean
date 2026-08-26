import Anderson4D.Continuum.GreenDerivatives
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The smooth nonzero-lattice remainder of the torus Green kernel

On the open principal cube, the periodized heat kernel is the Euclidean
zero-lattice summand plus a uniformly smooth sum over nonzero lattice
translates.  This file establishes the absolute summability needed to
differentiate that remainder twice.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Real Set
open scoped Topology

/-- Nonzero lattice points. -/
abbrev NZ4 := {k : Z4 // k ≠ 0}

/-- Translation of a Euclidean lift by the period indexed by `k`. -/
def latticeTranslate (x : R4) (k : Z4) : R4 :=
  fun i => x i + 2 * π * (k i : ℝ)

/-- The `k`-th Euclidean Bessel summand of the periodized Green kernel. -/
def latticeBesselTerm (x : R4) (k : Z4) : ℝ :=
  euclideanBessel4 (latticeTranslate x k)

/-- First-coordinate derivative of a lattice Bessel summand. -/
def latticeBesselGrad (x : R4) (k : Z4) (i : Fin dim) : ℝ :=
  euclideanBesselGrad (latticeTranslate x k) i

/-- Coordinate Hessian entry of a lattice Bessel summand. -/
def latticeBesselHess (x : R4) (k : Z4) (i j : Fin dim) : ℝ :=
  euclideanBesselHess (latticeTranslate x k) i j

/-- Sum of absolute integer coordinates. -/
def latticeL1 (k : Z4) : ℕ :=
  ∑ i, Int.natAbs (k i)

/-- Squared Euclidean lattice length. -/
def latticeSq (k : Z4) : ℝ :=
  ∑ i, (k i : ℝ) ^ 2

private theorem latticeSq_nonneg (k : Z4) :
    0 ≤ latticeSq k := by
  unfold latticeSq
  positivity

private theorem latticeL1_cast (k : Z4) :
    (latticeL1 k : ℝ) = ∑ i, |(k i : ℝ)| := by
  unfold latticeL1
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_natAbs, Int.cast_abs]

/-- Product-geometric lattice majorant.  Its square polynomial factor
absorbs all numerators appearing through the Hessian. -/
def latticeGeomWeight (k : Z4) : ℝ :=
  ∏ i, ((Int.natAbs (k i) : ℝ) + 1) ^ 2 *
    exp (-(1 / 2 : ℝ)) ^ Int.natAbs (k i)

private theorem summable_nat_succ_sq_geometric {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ 2 * r ^ n := by
  have h0 : Summable fun n : ℕ => r ^ n :=
    summable_geometric_of_lt_one hr0 hr1
  have hrnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have h1 : Summable fun n : ℕ => (n : ℝ) * r ^ n := by
    have hs :=
      summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (r := r) hrnorm
    refine hs.congr fun n => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp
  have h2 : Summable fun n : ℕ => (n : ℝ) ^ 2 * r ^ n := by
    have hs :=
      summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
        (r := r) hrnorm
    refine hs.congr fun n => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hs := h2.add ((h1.mul_left 2).add h0)
  refine hs.congr fun n => ?_
  ring

private theorem summable_int_succ_sq_geometric {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun m : ℤ =>
      ((Int.natAbs m : ℝ) + 1) ^ 2 * r ^ Int.natAbs m := by
  have hnat := summable_nat_succ_sq_geometric hr0 hr1
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using hnat
  · have hshift :
        Summable fun n : ℕ => (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * r ^ (n + 1) := by
      exact hnat.comp_injective Nat.succ_injective
    refine hshift.congr fun n => ?_
    have habs : (-((n : ℤ) + 1)).natAbs = n + 1 := by
      change (Int.negSucc n).natAbs = n + 1
      rw [Int.natAbs_negSucc]
    rw [habs]

private theorem summable_pi_product {g : ℤ → ℝ}
    (h0 : ∀ m, 0 ≤ g m) (hg : Summable g) :
    ∀ n : ℕ, Summable fun k : Fin n → ℤ => ∏ i, g (k i) := by
  intro n
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    have hg0 : (0 : ℤ → ℝ) ≤ g := fun m => h0 m
    have hp0 : (0 : (Fin n → ℤ) → ℝ) ≤ fun k => ∏ i, g (k i) :=
      fun k => Finset.prod_nonneg fun i _ => h0 _
    have hstep :
        Summable fun p : ℤ × (Fin n → ℤ) =>
          g p.1 * ∏ i, g (p.2 i) :=
      @Summable.mul_of_nonneg ℤ (Fin n → ℤ) g
        (fun k => ∏ i, g (k i)) hg ih hg0 hp0
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).summable_iff]
    refine hstep.congr fun p => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ]

theorem summable_latticeGeomWeight :
    Summable latticeGeomWeight := by
  have hr0 : 0 ≤ exp (-(1 / 2 : ℝ)) := (exp_pos _).le
  have hr1 : exp (-(1 / 2 : ℝ)) < 1 := by
    rw [← exp_zero]
    exact exp_lt_exp.mpr (by norm_num)
  unfold latticeGeomWeight
  exact summable_pi_product
    (fun m => mul_nonneg (sq_nonneg _) (pow_nonneg hr0 _))
    (summable_int_succ_sq_geometric hr0 hr1) dim

/-- Closed principal cube, used for uniform lattice estimates. -/
def InClosedPrincipalCube (x : R4) : Prop :=
  ∀ i, |x i| ≤ π

/-- Open principal cube, where the quotient lift is locally smooth. -/
def InOpenPrincipalCube (x : R4) : Prop :=
  ∀ i, |x i| < π

private theorem abs_latticeTranslate_coord_lower
    {x : R4} (hx : InClosedPrincipalCube x) (k : Z4) (i : Fin dim) :
    π * |(k i : ℝ)| ≤ |latticeTranslate x k i| := by
  unfold latticeTranslate
  rcases eq_or_ne (k i) 0 with hzero | hne
  · rw [hzero]
    norm_num
  · have hone : (1 : ℝ) ≤ |(k i : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hne
    have htri :
        |2 * π * (k i : ℝ)| ≤
          |x i + 2 * π * (k i : ℝ)| + |x i| := by
      calc
        |2 * π * (k i : ℝ)| =
            |x i + 2 * π * (k i : ℝ) + -(x i)| := by
              congr 1
              ring
        _ ≤ |x i + 2 * π * (k i : ℝ)| + |-(x i)| :=
          abs_add_le _ _
        _ = |x i + 2 * π * (k i : ℝ)| + |x i| := by
          rw [abs_neg]
    have habs :
        |2 * π * (k i : ℝ)| = 2 * π * |(k i : ℝ)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    rw [habs] at htri
    have hxi := hx i
    nlinarith [Real.pi_pos]

theorem latticeTranslate_sq_lower {x : R4}
    (hx : InClosedPrincipalCube x) (k : Z4) :
    π ^ 2 * ∑ i, (k i : ℝ) ^ 2 ≤
      euclideanDistSq (latticeTranslate x k) := by
  unfold euclideanDistSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := abs_latticeTranslate_coord_lower hx k i
  have hs := mul_self_le_mul_self
    (mul_nonneg Real.pi_pos.le (abs_nonneg (k i : ℝ))) h
  rw [← sq_abs (latticeTranslate x k i), ← sq_abs (k i : ℝ)]
  nlinarith [hs]

private theorem abs_latticeTranslate_coord_upper
    {x : R4} (hx : InClosedPrincipalCube x) (k : Z4) (i : Fin dim) :
    |latticeTranslate x k i| ≤
      2 * π * ((Int.natAbs (k i) : ℝ) + 1) := by
  unfold latticeTranslate
  have htri :
      |x i + 2 * π * (k i : ℝ)| ≤
        |x i| + |2 * π * (k i : ℝ)| :=
    abs_add_le _ _
  have habs :
      |2 * π * (k i : ℝ)| =
        2 * π * (Int.natAbs (k i) : ℝ) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
      Nat.cast_natAbs, Int.cast_abs]
  rw [habs] at htri
  have hxi := hx i
  have hn : 0 ≤ (Int.natAbs (k i) : ℝ) := by positivity
  nlinarith [Real.pi_pos]

private theorem exists_ne_coord {k : Z4} (hk : k ≠ 0) :
    ∃ i, k i ≠ 0 := by
  by_contra h
  push Not at h
  apply hk
  funext i
  exact h i

theorem one_le_lattice_sq {k : Z4} (hk : k ≠ 0) :
    (1 : ℝ) ≤ latticeSq k := by
  unfold latticeSq
  obtain ⟨i, hi⟩ := exists_ne_coord hk
  have hone : (1 : ℝ) ≤ (k i : ℝ) ^ 2 := by
    have habs : (1 : ℝ) ≤ |(k i : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hi
    nlinarith [sq_abs (k i : ℝ)]
  exact hone.trans
    (Finset.single_le_sum (fun j _ => sq_nonneg (k j : ℝ))
      (Finset.mem_univ i))

private theorem lattice_amgm_coord (t : ℝ) (ht : 0 < t) (m : ℤ) :
    |(m : ℝ)| / 2 ≤
      t / 8 + π ^ 2 * (m : ℝ) ^ 2 / (16 * t) := by
  have hpi : (9 : ℝ) ≤ π ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hsquare :
      0 ≤ 2 * (t - 2 * |(m : ℝ)|) ^ 2 + |(m : ℝ)| ^ 2 := by
    positivity
  rw [show t / 8 + π ^ 2 * (m : ℝ) ^ 2 / (16 * t) =
    (2 * t ^ 2 + π ^ 2 * (m : ℝ) ^ 2) / (16 * t) by
      field_simp
      ring]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * t)]
  rw [← sq_abs (m : ℝ)]
  nlinarith

private theorem lattice_amgm (t : ℝ) (ht : 0 < t) (k : Z4) :
    (latticeL1 k : ℝ) / 2 ≤
      t / 2 + π ^ 2 * latticeSq k / (16 * t) := by
  have hsum :=
    Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
      lattice_amgm_coord t ht (k i)
  calc
    (latticeL1 k : ℝ) / 2 =
        (∑ i, |(k i : ℝ)|) / 2 := by rw [latticeL1_cast]
    _ = ∑ i, |(k i : ℝ)| / 2 := by rw [Finset.sum_div]
    _ ≤
        ∑ i, (t / 8 + π ^ 2 * (k i : ℝ) ^ 2 / (16 * t)) :=
      hsum
    _ = t / 2 + π ^ 2 * latticeSq k / (16 * t) := by
      unfold latticeSq
      simp only [Fin.sum_univ_four]
      ring

private theorem exp_time_lattice_le {x : R4}
    (hx : InClosedPrincipalCube x) (k : Z4) {t : ℝ} (ht : 0 < t) :
    exp (-t) *
        exp (-(euclideanDistSq (latticeTranslate x k) / 4 / t)) ≤
      exp (-((latticeL1 k : ℝ) / 2)) *
        exp (-(π ^ 2 * latticeSq k / 8 / t)) := by
  rw [← exp_add, ← exp_add]
  apply exp_le_exp.mpr
  have hdist := latticeTranslate_sq_lower hx k
  have hbase :
      π ^ 2 * latticeSq k ≤
        euclideanDistSq (latticeTranslate x k) := by
    simpa [latticeSq] using hdist
  have hdist' :
      π ^ 2 * latticeSq k / 4 / t ≤
        euclideanDistSq (latticeTranslate x k) / 4 / t := by
    gcongr
  have hamgm := lattice_amgm t ht k
  have hnonneg : 0 ≤ π ^ 2 * latticeSq k / (16 * t) := by
    exact div_nonneg (mul_nonneg (sq_nonneg π) (latticeSq_nonneg k))
      (by positivity)
  have hsplit :
      (latticeL1 k : ℝ) / 2 + π ^ 2 * latticeSq k / 8 / t ≤
        t + π ^ 2 * latticeSq k / 4 / t := by
    have h8 :
        π ^ 2 * latticeSq k / 8 / t =
          2 * (π ^ 2 * latticeSq k / (16 * t)) := by
      field_simp
      ring
    have h4 :
        π ^ 2 * latticeSq k / 4 / t =
          4 * (π ^ 2 * latticeSq k / (16 * t)) := by
      field_simp
      ring
    rw [h8, h4]
    nlinarith
  have htotal :
      (latticeL1 k : ℝ) / 2 + π ^ 2 * latticeSq k / 8 / t ≤
        t + euclideanDistSq (latticeTranslate x k) / 4 / t :=
    hsplit.trans (by simpa [add_comm] using add_le_add_left hdist' t)
  calc
    -t + -(euclideanDistSq (latticeTranslate x k) / 4 / t) =
        -(t + euclideanDistSq (latticeTranslate x k) / 4 / t) := by ring
    _ ≤ -((latticeL1 k : ℝ) / 2 +
        π ^ 2 * latticeSq k / 8 / t) :=
      neg_le_neg htotal
    _ = -((latticeL1 k : ℝ) / 2) +
        -(π ^ 2 * latticeSq k / 8 / t) := by ring

private theorem heat_lattice_majorant {x : R4}
    (hx : InClosedPrincipalCube x) (k : Z4) {t : ℝ} (ht : 0 < t) :
    |exp (-t) * euclideanHeatKernel4 t (latticeTranslate x k)| ≤
      (16 * π ^ 2)⁻¹ * ((t ^ 2)⁻¹ *
        (exp (-((latticeL1 k : ℝ) / 2)) *
          exp (-(π ^ 2 * latticeSq k / 8 / t)))) := by
  rw [abs_mul, abs_of_pos (exp_pos (-t)),
    abs_of_nonneg (by
      unfold euclideanHeatKernel4
      positivity),
    euclideanHeatKernel4_eq_timeMajorant ht]
  have htime := exp_time_lattice_le hx k ht
  calc
    exp (-t) * ((16 * π ^ 2)⁻¹ *
        ((t ^ 2)⁻¹ *
          exp (-(euclideanDistSq (latticeTranslate x k) / 4 / t))))
        = (16 * π ^ 2)⁻¹ * (t ^ 2)⁻¹ *
          (exp (-t) *
            exp (-(euclideanDistSq (latticeTranslate x k) / 4 / t))) := by
              ring
    _ ≤ (16 * π ^ 2)⁻¹ * (t ^ 2)⁻¹ *
          (exp (-((latticeL1 k : ℝ) / 2)) *
            exp (-(π ^ 2 * latticeSq k / 8 / t))) := by
      gcongr
    _ = _ := by ring

private theorem grad_lattice_majorant {x : R4}
    (hx : InClosedPrincipalCube x) (k : Z4) (i : Fin dim)
    {t : ℝ} (ht : 0 < t) :
    |exp (-t) * euclideanHeatGrad t (latticeTranslate x k) i| ≤
      ((Int.natAbs (k i) : ℝ) + 1) / (16 * π) *
        ((t ^ 3)⁻¹ *
          (exp (-((latticeL1 k : ℝ) / 2)) *
            exp (-(π ^ 2 * latticeSq k / 8 / t)))) := by
  rw [abs_mul, abs_of_pos (exp_pos (-t)),
    abs_euclideanHeatGrad ht]
  have hcoord := abs_latticeTranslate_coord_upper hx k i
  have htime := exp_time_lattice_le hx k ht
  have hcoef :
      |latticeTranslate x k i| / (32 * π ^ 2) ≤
        ((Int.natAbs (k i) : ℝ) + 1) / (16 * π) := by
    calc
      |latticeTranslate x k i| / (32 * π ^ 2) ≤
          (2 * π * ((Int.natAbs (k i) : ℝ) + 1)) /
            (32 * π ^ 2) := by
        exact div_le_div_of_nonneg_right hcoord (by positivity)
      _ = ((Int.natAbs (k i) : ℝ) + 1) / (16 * π) := by
        field_simp
        ring
  calc
    exp (-t) *
        (|latticeTranslate x k i| / (32 * π ^ 2) *
          ((t ^ 3)⁻¹ *
            exp (-(euclideanDistSq (latticeTranslate x k) / 4 / t))))
        = (|latticeTranslate x k i| / (32 * π ^ 2) * (t ^ 3)⁻¹) *
            (exp (-t) *
              exp (-(euclideanDistSq (latticeTranslate x k) / 4 / t))) := by
          ring
    _ ≤ (((Int.natAbs (k i) : ℝ) + 1) / (16 * π) * (t ^ 3)⁻¹) *
            (exp (-((latticeL1 k : ℝ) / 2)) *
              exp (-(π ^ 2 * latticeSq k / 8 / t))) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hcoef (by positivity))
        htime (by positivity) (by positivity)
    _ = 1 * (((Int.natAbs (k i) : ℝ) + 1) / (16 * π) *
          ((t ^ 3)⁻¹ *
            (exp (-((latticeL1 k : ℝ) / 2)) *
              exp (-(π ^ 2 * latticeSq k / 8 / t))))) := by ring
    _ = _ := by ring

private theorem hess_lattice_majorant {x : R4}
    (hx : InClosedPrincipalCube x) (k : Z4) (i j : Fin dim)
    {t : ℝ} (ht : 0 < t) :
    |exp (-t) * euclideanHeatHess t (latticeTranslate x k) i j| ≤
      (((Int.natAbs (k i) : ℝ) + 1) *
          ((Int.natAbs (k j) : ℝ) + 1) / 16) *
        ((t ^ 4)⁻¹ *
          (exp (-((latticeL1 k : ℝ) / 2)) *
            exp (-(π ^ 2 * latticeSq k / 8 / t)))) +
      1 / (32 * π ^ 2) *
        ((t ^ 3)⁻¹ *
          (exp (-((latticeL1 k : ℝ) / 2)) *
            exp (-(π ^ 2 * latticeSq k / 8 / t)))) := by
  rw [abs_mul, abs_of_pos (exp_pos (-t))]
  have hbase := abs_euclideanHeatHess_le ht (latticeTranslate x k) i j
  have hi := abs_latticeTranslate_coord_upper hx k i
  have hj := abs_latticeTranslate_coord_upper hx k j
  have hproduct :
      |latticeTranslate x k i * latticeTranslate x k j| ≤
        (2 * π * ((Int.natAbs (k i) : ℝ) + 1)) *
          (2 * π * ((Int.natAbs (k j) : ℝ) + 1)) := by
    rw [abs_mul]
    exact mul_le_mul hi hj (abs_nonneg _) (by positivity)
  have hcoef :
      |latticeTranslate x k i * latticeTranslate x k j| /
          (64 * π ^ 2) ≤
        ((Int.natAbs (k i) : ℝ) + 1) *
          ((Int.natAbs (k j) : ℝ) + 1) / 16 := by
    calc
      |latticeTranslate x k i * latticeTranslate x k j| /
            (64 * π ^ 2) ≤
          ((2 * π * ((Int.natAbs (k i) : ℝ) + 1)) *
            (2 * π * ((Int.natAbs (k j) : ℝ) + 1))) /
              (64 * π ^ 2) :=
        div_le_div_of_nonneg_right hproduct (by positivity)
      _ = ((Int.natAbs (k i) : ℝ) + 1) *
          ((Int.natAbs (k j) : ℝ) + 1) / 16 := by
        field_simp
        ring
  have htime := exp_time_lattice_le hx k ht
  calc
    exp (-t) *
        |euclideanHeatHess t (latticeTranslate x k) i j| ≤
      exp (-t) *
        (|latticeTranslate x k i * latticeTranslate x k j| /
              (64 * π ^ 2) *
            ((t ^ 4)⁻¹ *
              exp (-(euclideanDistSq (latticeTranslate x k) / 4 / t))) +
          1 / (32 * π ^ 2) *
            ((t ^ 3)⁻¹ *
              exp (-(euclideanDistSq (latticeTranslate x k) / 4 / t)))) :=
      mul_le_mul_of_nonneg_left hbase (exp_pos _).le
    _ = (|latticeTranslate x k i * latticeTranslate x k j| /
            (64 * π ^ 2) * (t ^ 4)⁻¹) *
          (exp (-t) *
            exp (-(euclideanDistSq (latticeTranslate x k) / 4 / t))) +
        (1 / (32 * π ^ 2) * (t ^ 3)⁻¹) *
          (exp (-t) *
            exp (-(euclideanDistSq (latticeTranslate x k) / 4 / t))) := by
      ring
    _ ≤ ((((Int.natAbs (k i) : ℝ) + 1) *
            ((Int.natAbs (k j) : ℝ) + 1) / 16) * (t ^ 4)⁻¹) *
          (exp (-((latticeL1 k : ℝ) / 2)) *
            exp (-(π ^ 2 * latticeSq k / 8 / t))) +
        (1 / (32 * π ^ 2) * (t ^ 3)⁻¹) *
          (exp (-((latticeL1 k : ℝ) / 2)) *
            exp (-(π ^ 2 * latticeSq k / 8 / t))) := by
      apply add_le_add
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_right hcoef (by positivity))
          htime (by positivity) (by positivity)
      · exact mul_le_mul_of_nonneg_left htime (by positivity)
    _ = _ := by ring

/-- Time scale furnished by a nonzero lattice translate. -/
def latticeTimeScale (k : Z4) : ℝ :=
  π ^ 2 * latticeSq k / 8

private theorem latticeTimeScale_pos {k : Z4} (hk : k ≠ 0) :
    0 < latticeTimeScale k := by
  unfold latticeTimeScale
  have hs := one_le_lattice_sq hk
  positivity

private theorem integrableOn_lattice_heat_integrand {x : R4}
    (hx : InClosedPrincipalCube x) {k : Z4} (hk : k ≠ 0) :
    IntegrableOn
      (fun t => exp (-t) *
        euclideanHeatKernel4 t (latticeTranslate x k))
      (Ioi (0 : ℝ)) := by
  have ha := latticeTimeScale_pos hk
  have hmajor :
      IntegrableOn
        (fun t => ((16 * π ^ 2)⁻¹ *
            exp (-((latticeL1 k : ℝ) / 2))) *
          ((t ^ 2)⁻¹ * exp (-(latticeTimeScale k / t))))
        (Ioi (0 : ℝ)) :=
    (integrableOn_inv_sq_exp ha).const_mul _
  apply Integrable.mono' hmajor
  · apply Measurable.aestronglyMeasurable
    unfold euclideanHeatKernel4 euclideanDistSq latticeTranslate
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    exact Filter.Eventually.of_forall fun t ht => by
      change |exp (-t) *
        euclideanHeatKernel4 t (latticeTranslate x k)| ≤ _
      calc
        |exp (-t) * euclideanHeatKernel4 t (latticeTranslate x k)| ≤
            (16 * π ^ 2)⁻¹ * ((t ^ 2)⁻¹ *
              (exp (-((latticeL1 k : ℝ) / 2)) *
                exp (-(π ^ 2 * latticeSq k / 8 / t)))) :=
          heat_lattice_majorant hx k ht
        _ = _ := by
          unfold latticeTimeScale
          ring_nf

private theorem integral_abs_lattice_heat_le {x : R4}
    (hx : InClosedPrincipalCube x) {k : Z4} (hk : k ≠ 0) :
    ∫ t in Ioi (0 : ℝ),
        |exp (-t) * euclideanHeatKernel4 t (latticeTranslate x k)| ≤
      ((16 * π ^ 2)⁻¹ * exp (-((latticeL1 k : ℝ) / 2))) *
        (latticeTimeScale k)⁻¹ := by
  have ha := latticeTimeScale_pos hk
  have hmajor :
      IntegrableOn
        (fun t => ((16 * π ^ 2)⁻¹ *
            exp (-((latticeL1 k : ℝ) / 2))) *
          ((t ^ 2)⁻¹ * exp (-(latticeTimeScale k / t))))
        (Ioi (0 : ℝ)) :=
    (integrableOn_inv_sq_exp ha).const_mul _
  calc
    ∫ t in Ioi (0 : ℝ),
        |exp (-t) * euclideanHeatKernel4 t (latticeTranslate x k)| ≤
      ∫ t in Ioi (0 : ℝ),
        ((16 * π ^ 2)⁻¹ * exp (-((latticeL1 k : ℝ) / 2))) *
          ((t ^ 2)⁻¹ * exp (-(latticeTimeScale k / t))) := by
      refine setIntegral_mono_on
        (integrableOn_lattice_heat_integrand hx hk).norm hmajor
        measurableSet_Ioi fun t ht => ?_
      calc
        |exp (-t) * euclideanHeatKernel4 t (latticeTranslate x k)| ≤
            (16 * π ^ 2)⁻¹ * ((t ^ 2)⁻¹ *
              (exp (-((latticeL1 k : ℝ) / 2)) *
                exp (-(π ^ 2 * latticeSq k / 8 / t)))) :=
          heat_lattice_majorant hx k ht
        _ = _ := by
          unfold latticeTimeScale
          ring_nf
    _ = _ := by
      rw [integral_const_mul, integral_inv_sq_exp ha]

private theorem integrableOn_lattice_grad_integrand {x : R4}
    (hx : InClosedPrincipalCube x) {k : Z4} (hk : k ≠ 0)
    (i : Fin dim) :
    IntegrableOn
      (fun t => exp (-t) *
        euclideanHeatGrad t (latticeTranslate x k) i)
      (Ioi (0 : ℝ)) := by
  have ha := latticeTimeScale_pos hk
  have hmajor :
      IntegrableOn
        (fun t => (((Int.natAbs (k i) : ℝ) + 1) / (16 * π) *
            exp (-((latticeL1 k : ℝ) / 2))) *
          ((t ^ 3)⁻¹ * exp (-(latticeTimeScale k / t))))
        (Ioi (0 : ℝ)) :=
    (integrableOn_inv_cube_exp ha).const_mul _
  apply Integrable.mono' hmajor
  · apply Measurable.aestronglyMeasurable
    unfold euclideanHeatGrad euclideanHeatKernel4 euclideanDistSq
      latticeTranslate
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    exact Filter.Eventually.of_forall fun t ht => by
      change |exp (-t) *
        euclideanHeatGrad t (latticeTranslate x k) i| ≤ _
      calc
        |exp (-t) * euclideanHeatGrad t (latticeTranslate x k) i| ≤
            ((Int.natAbs (k i) : ℝ) + 1) / (16 * π) *
              ((t ^ 3)⁻¹ *
                (exp (-((latticeL1 k : ℝ) / 2)) *
                  exp (-(π ^ 2 * latticeSq k / 8 / t)))) :=
          grad_lattice_majorant hx k i ht
        _ = _ := by
          unfold latticeTimeScale
          ring

private theorem integral_abs_lattice_grad_le {x : R4}
    (hx : InClosedPrincipalCube x) {k : Z4} (hk : k ≠ 0)
    (i : Fin dim) :
    ∫ t in Ioi (0 : ℝ),
        |exp (-t) * euclideanHeatGrad t (latticeTranslate x k) i| ≤
      ((((Int.natAbs (k i) : ℝ) + 1) / (16 * π)) *
        exp (-((latticeL1 k : ℝ) / 2))) *
        (latticeTimeScale k)⁻¹ ^ 2 := by
  have ha := latticeTimeScale_pos hk
  have hmajor :
      IntegrableOn
        (fun t => ((((Int.natAbs (k i) : ℝ) + 1) / (16 * π)) *
            exp (-((latticeL1 k : ℝ) / 2))) *
          ((t ^ 3)⁻¹ * exp (-(latticeTimeScale k / t))))
        (Ioi (0 : ℝ)) :=
    (integrableOn_inv_cube_exp ha).const_mul _
  calc
    ∫ t in Ioi (0 : ℝ),
        |exp (-t) * euclideanHeatGrad t (latticeTranslate x k) i| ≤
      ∫ t in Ioi (0 : ℝ),
        ((((Int.natAbs (k i) : ℝ) + 1) / (16 * π)) *
            exp (-((latticeL1 k : ℝ) / 2))) *
          ((t ^ 3)⁻¹ * exp (-(latticeTimeScale k / t))) := by
      refine setIntegral_mono_on
        (integrableOn_lattice_grad_integrand hx hk i).norm hmajor
        measurableSet_Ioi fun t ht => ?_
      calc
        |exp (-t) * euclideanHeatGrad t (latticeTranslate x k) i| ≤
            ((Int.natAbs (k i) : ℝ) + 1) / (16 * π) *
              ((t ^ 3)⁻¹ *
                (exp (-((latticeL1 k : ℝ) / 2)) *
                  exp (-(π ^ 2 * latticeSq k / 8 / t)))) :=
          grad_lattice_majorant hx k i ht
        _ = _ := by
          unfold latticeTimeScale
          ring
    _ = _ := by
      rw [integral_const_mul, integral_inv_cube_exp ha]

private theorem integrableOn_lattice_hess_integrand {x : R4}
    (hx : InClosedPrincipalCube x) {k : Z4} (hk : k ≠ 0)
    (i j : Fin dim) :
    IntegrableOn
      (fun t => exp (-t) *
        euclideanHeatHess t (latticeTranslate x k) i j)
      (Ioi (0 : ℝ)) := by
  have ha := latticeTimeScale_pos hk
  have hfourth :
      IntegrableOn
        (fun t => ((((Int.natAbs (k i) : ℝ) + 1) *
              ((Int.natAbs (k j) : ℝ) + 1) / 16) *
            exp (-((latticeL1 k : ℝ) / 2))) *
          ((t ^ 4)⁻¹ * exp (-(latticeTimeScale k / t))))
        (Ioi (0 : ℝ)) :=
    (integrableOn_inv_fourth_exp ha).const_mul _
  have hcube :
      IntegrableOn
        (fun t => ((1 / (32 * π ^ 2)) *
            exp (-((latticeL1 k : ℝ) / 2))) *
          ((t ^ 3)⁻¹ * exp (-(latticeTimeScale k / t))))
        (Ioi (0 : ℝ)) :=
    (integrableOn_inv_cube_exp ha).const_mul _
  apply Integrable.mono' (hfourth.add hcube)
  · apply Measurable.aestronglyMeasurable
    unfold euclideanHeatHess euclideanHeatKernel4 euclideanDistSq
      latticeTranslate
    by_cases hij : i = j
    · simp only [hij, if_true]
      fun_prop
    · simp only [hij, if_false]
      fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    exact Filter.Eventually.of_forall fun t ht => by
      change |exp (-t) *
        euclideanHeatHess t (latticeTranslate x k) i j| ≤ _
      calc
        |exp (-t) * euclideanHeatHess t (latticeTranslate x k) i j| ≤
            (((Int.natAbs (k i) : ℝ) + 1) *
                ((Int.natAbs (k j) : ℝ) + 1) / 16) *
              ((t ^ 4)⁻¹ *
                (exp (-((latticeL1 k : ℝ) / 2)) *
                  exp (-(π ^ 2 * latticeSq k / 8 / t)))) +
            1 / (32 * π ^ 2) *
              ((t ^ 3)⁻¹ *
                (exp (-((latticeL1 k : ℝ) / 2)) *
                  exp (-(π ^ 2 * latticeSq k / 8 / t)))) :=
          hess_lattice_majorant hx k i j ht
        _ = _ := by
          simp only [Pi.add_apply]
          unfold latticeTimeScale
          ring_nf

private theorem integral_abs_lattice_hess_le {x : R4}
    (hx : InClosedPrincipalCube x) {k : Z4} (hk : k ≠ 0)
    (i j : Fin dim) :
    ∫ t in Ioi (0 : ℝ),
        |exp (-t) * euclideanHeatHess t (latticeTranslate x k) i j| ≤
      ((((Int.natAbs (k i) : ℝ) + 1) *
          ((Int.natAbs (k j) : ℝ) + 1) / 16) *
        exp (-((latticeL1 k : ℝ) / 2))) *
          (2 * (latticeTimeScale k)⁻¹ ^ 3) +
      ((1 / (32 * π ^ 2)) *
        exp (-((latticeL1 k : ℝ) / 2))) *
          (latticeTimeScale k)⁻¹ ^ 2 := by
  have ha := latticeTimeScale_pos hk
  have hfourth :
      IntegrableOn
        (fun t => ((((Int.natAbs (k i) : ℝ) + 1) *
              ((Int.natAbs (k j) : ℝ) + 1) / 16) *
            exp (-((latticeL1 k : ℝ) / 2))) *
          ((t ^ 4)⁻¹ * exp (-(latticeTimeScale k / t))))
        (Ioi (0 : ℝ)) :=
    (integrableOn_inv_fourth_exp ha).const_mul _
  have hcube :
      IntegrableOn
        (fun t => ((1 / (32 * π ^ 2)) *
            exp (-((latticeL1 k : ℝ) / 2))) *
          ((t ^ 3)⁻¹ * exp (-(latticeTimeScale k / t))))
        (Ioi (0 : ℝ)) :=
    (integrableOn_inv_cube_exp ha).const_mul _
  calc
    ∫ t in Ioi (0 : ℝ),
        |exp (-t) * euclideanHeatHess t (latticeTranslate x k) i j| ≤
      ∫ t in Ioi (0 : ℝ),
        (((((Int.natAbs (k i) : ℝ) + 1) *
              ((Int.natAbs (k j) : ℝ) + 1) / 16) *
            exp (-((latticeL1 k : ℝ) / 2))) *
              ((t ^ 4)⁻¹ * exp (-(latticeTimeScale k / t))) +
          ((1 / (32 * π ^ 2)) *
            exp (-((latticeL1 k : ℝ) / 2))) *
              ((t ^ 3)⁻¹ * exp (-(latticeTimeScale k / t)))) := by
      refine setIntegral_mono_on
        (integrableOn_lattice_hess_integrand hx hk i j).norm
        (hfourth.add hcube) measurableSet_Ioi fun t ht => ?_
      calc
        |exp (-t) * euclideanHeatHess t (latticeTranslate x k) i j| ≤
            (((Int.natAbs (k i) : ℝ) + 1) *
                ((Int.natAbs (k j) : ℝ) + 1) / 16) *
              ((t ^ 4)⁻¹ *
                (exp (-((latticeL1 k : ℝ) / 2)) *
                  exp (-(π ^ 2 * latticeSq k / 8 / t)))) +
            1 / (32 * π ^ 2) *
              ((t ^ 3)⁻¹ *
                (exp (-((latticeL1 k : ℝ) / 2)) *
                  exp (-(π ^ 2 * latticeSq k / 8 / t)))) :=
          hess_lattice_majorant hx k i j ht
        _ = _ := by
          unfold latticeTimeScale
          ring_nf
    _ = _ := by
      rw [integral_add hfourth hcube, integral_const_mul,
        integral_const_mul, integral_inv_fourth_exp ha,
        integral_inv_cube_exp ha]

private theorem exp_latticeL1_eq_product (k : Z4) :
    exp (-((latticeL1 k : ℝ) / 2)) =
      ∏ i, exp (-(1 / 2 : ℝ)) ^ Int.natAbs (k i) := by
  calc
    exp (-((latticeL1 k : ℝ) / 2)) =
        exp (∑ i, -(|(k i : ℝ)| / 2)) := by
      rw [latticeL1_cast, Finset.sum_div, Finset.sum_neg_distrib]
    _ = ∏ i, exp (- (|(k i : ℝ)| / 2)) := exp_sum Finset.univ _
    _ = ∏ i, exp (-(1 / 2 : ℝ)) ^ Int.natAbs (k i) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← Real.exp_nat_mul]
      congr 1
      rw [Nat.cast_natAbs, Int.cast_abs]
      ring

private theorem one_add_sum_le_prod_one_add
    (a : Fin dim → ℝ) (ha : ∀ i, 0 ≤ a i) :
    1 + ∑ i, a i ≤ ∏ i, (1 + a i) := by
  classical
  have hgeneral :
      ∀ s : Finset (Fin dim),
        1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
      rw [Finset.sum_insert his, Finset.prod_insert his]
      have hp : 1 ≤ ∏ j ∈ s, (1 + a j) := by
        apply Finset.one_le_prod
        intro j hj
        linarith [ha j]
      have hai := ha i
      nlinarith
  simpa using hgeneral Finset.univ

private theorem lattice_poly_exp_le_weight (k : Z4) :
    (((latticeL1 k : ℝ) + 1) ^ 2) *
        exp (-((latticeL1 k : ℝ) / 2)) ≤
      latticeGeomWeight k := by
  have hprod :
      (latticeL1 k : ℝ) + 1 ≤
        ∏ i, ((Int.natAbs (k i) : ℝ) + 1) := by
    rw [add_comm, show (latticeL1 k : ℝ) =
      ∑ i, (Int.natAbs (k i) : ℝ) by
        unfold latticeL1
        rw [Nat.cast_sum]]
    have h := one_add_sum_le_prod_one_add
      (fun i => (Int.natAbs (k i) : ℝ)) fun _ => by positivity
    simpa [add_comm] using h
  have hsquare :
      ((latticeL1 k : ℝ) + 1) ^ 2 ≤
        (∏ i, ((Int.natAbs (k i) : ℝ) + 1)) ^ 2 := by
    gcongr
  rw [latticeGeomWeight, exp_latticeL1_eq_product,
    Finset.prod_mul_distrib]
  calc
    ((latticeL1 k : ℝ) + 1) ^ 2 *
          ∏ i, exp (-(1 / 2 : ℝ)) ^ Int.natAbs (k i) ≤
        (∏ i, ((Int.natAbs (k i) : ℝ) + 1)) ^ 2 *
          ∏ i, exp (-(1 / 2 : ℝ)) ^ Int.natAbs (k i) :=
      mul_le_mul_of_nonneg_right hsquare
        (Finset.prod_nonneg fun i _ => pow_nonneg (exp_pos _).le _)
    _ = (∏ i, ((Int.natAbs (k i) : ℝ) + 1) ^ 2) *
          ∏ i, exp (-(1 / 2 : ℝ)) ^ Int.natAbs (k i) := by
      rw [Finset.prod_pow]

private theorem one_le_latticeTimeScale {k : Z4} (hk : k ≠ 0) :
    (1 : ℝ) ≤ latticeTimeScale k := by
  have hpi : (9 : ℝ) ≤ π ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hs := one_le_lattice_sq hk
  unfold latticeTimeScale
  calc
    (1 : ℝ) ≤ 9 / 8 := by norm_num
    _ ≤ π ^ 2 * latticeSq k / 8 := by
      gcongr
      calc
        (9 : ℝ) = 9 * 1 := by ring
        _ ≤ π ^ 2 * latticeSq k :=
          mul_le_mul hpi hs (by norm_num) (sq_nonneg π)

private theorem latticeTimeScale_inv_pow_le_one {k : Z4}
    (hk : k ≠ 0) (n : ℕ) :
    (latticeTimeScale k)⁻¹ ^ n ≤ 1 := by
  apply pow_le_one₀
  · exact inv_nonneg.mpr (latticeTimeScale_pos hk).le
  · exact (inv_le_one₀ (latticeTimeScale_pos hk)).2
      (one_le_latticeTimeScale hk)

private theorem lattice_coord_succ_le_l1_succ (k : Z4)
    (i : Fin dim) :
    (Int.natAbs (k i) : ℝ) + 1 ≤ (latticeL1 k : ℝ) + 1 := by
  have hnat :
      Int.natAbs (k i) ≤ latticeL1 k := by
    unfold latticeL1
    exact Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (Int.natAbs (k j)))
      (Finset.mem_univ i)
  exact_mod_cast Nat.add_le_add_right hnat 1

private theorem exp_latticeL1_le_poly_exp (k : Z4) :
    exp (-((latticeL1 k : ℝ) / 2)) ≤
      (((latticeL1 k : ℝ) + 1) ^ 2) *
        exp (-((latticeL1 k : ℝ) / 2)) := by
  have hbase : (1 : ℝ) ≤ (latticeL1 k : ℝ) + 1 := by
    have hn : 0 ≤ (latticeL1 k : ℝ) := by positivity
    linarith
  have hsquare : (1 : ℝ) ≤ ((latticeL1 k : ℝ) + 1) ^ 2 := by
    nlinarith
  simpa using mul_le_mul_of_nonneg_right hsquare
    (exp_pos (-((latticeL1 k : ℝ) / 2))).le

private theorem heat_integral_weight_bound {x : R4}
    (hx : InClosedPrincipalCube x) {k : Z4} (hk : k ≠ 0) :
    ∫ t in Ioi (0 : ℝ),
        |exp (-t) * euclideanHeatKernel4 t (latticeTranslate x k)| ≤
      latticeGeomWeight k := by
  have hraw := integral_abs_lattice_heat_le hx hk
  have hcoef : (16 * π ^ 2)⁻¹ ≤ (1 : ℝ) := by
    apply (inv_le_one₀ (by positivity)).2
    nlinarith [Real.pi_gt_three]
  have hinv := latticeTimeScale_inv_pow_le_one hk 1
  simp only [pow_one] at hinv
  have hexp := exp_latticeL1_le_poly_exp k
  have hpoly := lattice_poly_exp_le_weight k
  calc
    ∫ t in Ioi (0 : ℝ),
        |exp (-t) * euclideanHeatKernel4 t (latticeTranslate x k)| ≤
        ((16 * π ^ 2)⁻¹ * exp (-((latticeL1 k : ℝ) / 2))) *
          (latticeTimeScale k)⁻¹ := hraw
    _ ≤ exp (-((latticeL1 k : ℝ) / 2)) := by
      have he : 0 ≤ exp (-((latticeL1 k : ℝ) / 2)) := (exp_pos _).le
      have hi : 0 ≤ (latticeTimeScale k)⁻¹ :=
        inv_nonneg.mpr (latticeTimeScale_pos hk).le
      exact (mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left he hcoef) hi).trans
          (mul_le_of_le_one_right he hinv)
    _ ≤ (((latticeL1 k : ℝ) + 1) ^ 2) *
          exp (-((latticeL1 k : ℝ) / 2)) := hexp
    _ ≤ latticeGeomWeight k := hpoly

private theorem grad_integral_weight_bound {x : R4}
    (hx : InClosedPrincipalCube x) {k : Z4} (hk : k ≠ 0)
    (i : Fin dim) :
    ∫ t in Ioi (0 : ℝ),
        |exp (-t) * euclideanHeatGrad t (latticeTranslate x k) i| ≤
      latticeGeomWeight k := by
  have hraw := integral_abs_lattice_grad_le hx hk i
  have hcoef : (16 * π)⁻¹ ≤ (1 : ℝ) := by
    apply (inv_le_one₀ (by positivity)).2
    nlinarith [Real.pi_gt_three]
  have hinv := latticeTimeScale_inv_pow_le_one hk 2
  have hcoord := lattice_coord_succ_le_l1_succ k i
  have hpoly := lattice_poly_exp_le_weight k
  calc
    ∫ t in Ioi (0 : ℝ),
        |exp (-t) * euclideanHeatGrad t (latticeTranslate x k) i| ≤
      ((((Int.natAbs (k i) : ℝ) + 1) / (16 * π)) *
        exp (-((latticeL1 k : ℝ) / 2))) *
        (latticeTimeScale k)⁻¹ ^ 2 := hraw
    _ ≤ ((latticeL1 k : ℝ) + 1) *
        exp (-((latticeL1 k : ℝ) / 2)) := by
      have hA : 0 ≤ (Int.natAbs (k i) : ℝ) + 1 := by positivity
      have hL : 0 ≤ (latticeL1 k : ℝ) + 1 := by positivity
      have he : 0 ≤ exp (-((latticeL1 k : ℝ) / 2)) := (exp_pos _).le
      have hi : 0 ≤ (latticeTimeScale k)⁻¹ ^ 2 :=
        pow_nonneg (inv_nonneg.mpr (latticeTimeScale_pos hk).le) _
      rw [div_eq_mul_inv]
      have hAc :
          ((Int.natAbs (k i) : ℝ) + 1) * (16 * π)⁻¹ ≤
            (latticeL1 k : ℝ) + 1 :=
        (mul_le_of_le_one_right hA hcoef).trans hcoord
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hAc he) hi).trans
          (mul_le_of_le_one_right (mul_nonneg hL he) hinv)
    _ ≤ (((latticeL1 k : ℝ) + 1) ^ 2) *
        exp (-((latticeL1 k : ℝ) / 2)) := by
      have hL : (1 : ℝ) ≤ (latticeL1 k : ℝ) + 1 := by
        have hn : 0 ≤ (latticeL1 k : ℝ) := by positivity
        linarith
      have he : 0 ≤ exp (-((latticeL1 k : ℝ) / 2)) := (exp_pos _).le
      apply mul_le_mul_of_nonneg_right _ he
      nlinarith
    _ ≤ latticeGeomWeight k := hpoly

private theorem hess_integral_weight_bound {x : R4}
    (hx : InClosedPrincipalCube x) {k : Z4} (hk : k ≠ 0)
    (i j : Fin dim) :
    ∫ t in Ioi (0 : ℝ),
        |exp (-t) * euclideanHeatHess t (latticeTranslate x k) i j| ≤
      2 * latticeGeomWeight k := by
  have hraw := integral_abs_lattice_hess_le hx hk i j
  have hi3 := latticeTimeScale_inv_pow_le_one hk 3
  have hi2 := latticeTimeScale_inv_pow_le_one hk 2
  have hcoordi := lattice_coord_succ_le_l1_succ k i
  have hcoordj := lattice_coord_succ_le_l1_succ k j
  have hcoef : (32 * π ^ 2)⁻¹ ≤ (1 : ℝ) := by
    apply (inv_le_one₀ (by positivity)).2
    nlinarith [Real.pi_gt_three]
  have hpoly := lattice_poly_exp_le_weight k
  have hexp := exp_latticeL1_le_poly_exp k
  have hfirst :
      ((((Int.natAbs (k i) : ℝ) + 1) *
          ((Int.natAbs (k j) : ℝ) + 1) / 16) *
        exp (-((latticeL1 k : ℝ) / 2))) *
          (2 * (latticeTimeScale k)⁻¹ ^ 3) ≤
        (((latticeL1 k : ℝ) + 1) ^ 2) *
          exp (-((latticeL1 k : ℝ) / 2)) := by
    have hAi : 0 ≤ (Int.natAbs (k i) : ℝ) + 1 := by positivity
    have hAj : 0 ≤ (Int.natAbs (k j) : ℝ) + 1 := by positivity
    have hL : 0 ≤ (latticeL1 k : ℝ) + 1 := by positivity
    have he : 0 ≤ exp (-((latticeL1 k : ℝ) / 2)) := (exp_pos _).le
    have hi : 0 ≤ (latticeTimeScale k)⁻¹ ^ 3 :=
      pow_nonneg (inv_nonneg.mpr (latticeTimeScale_pos hk).le) _
    have hproduct :
        ((Int.natAbs (k i) : ℝ) + 1) *
            ((Int.natAbs (k j) : ℝ) + 1) ≤
          ((latticeL1 k : ℝ) + 1) ^ 2 := by
      rw [pow_two]
      exact mul_le_mul hcoordi hcoordj hAj hL
    have hfactor :
        2 * (latticeTimeScale k)⁻¹ ^ 3 / 16 ≤ (1 : ℝ) := by
      nlinarith
    calc
      ((((Int.natAbs (k i) : ℝ) + 1) *
          ((Int.natAbs (k j) : ℝ) + 1) / 16) *
        exp (-((latticeL1 k : ℝ) / 2))) *
          (2 * (latticeTimeScale k)⁻¹ ^ 3) =
        (((Int.natAbs (k i) : ℝ) + 1) *
          ((Int.natAbs (k j) : ℝ) + 1) *
            exp (-((latticeL1 k : ℝ) / 2))) *
          (2 * (latticeTimeScale k)⁻¹ ^ 3 / 16) := by ring
      _ ≤ ((Int.natAbs (k i) : ℝ) + 1) *
          ((Int.natAbs (k j) : ℝ) + 1) *
            exp (-((latticeL1 k : ℝ) / 2)) :=
        mul_le_of_le_one_right
          (mul_nonneg (mul_nonneg hAi hAj) he) hfactor
      _ ≤ (((latticeL1 k : ℝ) + 1) ^ 2) *
          exp (-((latticeL1 k : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hproduct he
  have hsecond :
      ((1 / (32 * π ^ 2)) *
        exp (-((latticeL1 k : ℝ) / 2))) *
          (latticeTimeScale k)⁻¹ ^ 2 ≤
        (((latticeL1 k : ℝ) + 1) ^ 2) *
          exp (-((latticeL1 k : ℝ) / 2)) := by
    have he : 0 ≤ exp (-((latticeL1 k : ℝ) / 2)) := (exp_pos _).le
    have hi : 0 ≤ (latticeTimeScale k)⁻¹ ^ 2 :=
      pow_nonneg (inv_nonneg.mpr (latticeTimeScale_pos hk).le) _
    rw [one_div]
    exact ((mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left he hcoef) hi).trans
        (mul_le_of_le_one_right he hi2)).trans hexp
  calc
    ∫ t in Ioi (0 : ℝ),
        |exp (-t) * euclideanHeatHess t (latticeTranslate x k) i j| ≤
        ((((Int.natAbs (k i) : ℝ) + 1) *
            ((Int.natAbs (k j) : ℝ) + 1) / 16) *
          exp (-((latticeL1 k : ℝ) / 2))) *
            (2 * (latticeTimeScale k)⁻¹ ^ 3) +
        ((1 / (32 * π ^ 2)) *
          exp (-((latticeL1 k : ℝ) / 2))) *
            (latticeTimeScale k)⁻¹ ^ 2 := hraw
    _ ≤ 2 * ((((latticeL1 k : ℝ) + 1) ^ 2) *
          exp (-((latticeL1 k : ℝ) / 2))) := by
      nlinarith
    _ ≤ 2 * latticeGeomWeight k := by
      gcongr

private theorem latticeTranslate_distSq_ne_zero {x : R4}
    (hx : InClosedPrincipalCube x) {k : Z4} (hk : k ≠ 0) :
    euclideanDistSq (latticeTranslate x k) ≠ 0 := by
  have hlow :
      π ^ 2 * latticeSq k ≤
        euclideanDistSq (latticeTranslate x k) := by
    simpa [latticeSq] using latticeTranslate_sq_lower hx k
  have hpos : 0 < π ^ 2 * latticeSq k :=
    mul_pos (sq_pos_of_pos Real.pi_pos) (lt_of_lt_of_le zero_lt_one
      (one_le_lattice_sq hk))
  exact ne_of_gt (hpos.trans_le hlow)

/-- A nonzero Bessel summand is controlled by the common geometric
lattice majorant, uniformly on the closed principal cube. -/
theorem abs_latticeBesselTerm_le {x : R4}
    (hx : InClosedPrincipalCube x) {k : Z4} (hk : k ≠ 0) :
    |latticeBesselTerm x k| ≤ latticeGeomWeight k := by
  unfold latticeBesselTerm euclideanBessel4
  calc
    |∫ t in Ioi (0 : ℝ),
        exp (-t) * euclideanHeatKernel4 t (latticeTranslate x k)| =
        ‖∫ t in Ioi (0 : ℝ),
          exp (-t) * euclideanHeatKernel4 t (latticeTranslate x k)‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∫ t in Ioi (0 : ℝ),
        ‖exp (-t) * euclideanHeatKernel4 t (latticeTranslate x k)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t in Ioi (0 : ℝ),
        |exp (-t) * euclideanHeatKernel4 t (latticeTranslate x k)| := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      change ‖exp (-t) *
        euclideanHeatKernel4 t (latticeTranslate x k)‖ =
          |exp (-t) * euclideanHeatKernel4 t (latticeTranslate x k)|
      exact Real.norm_eq_abs _
    _ ≤ latticeGeomWeight k := heat_integral_weight_bound hx hk

/-- The first derivative of a nonzero Bessel summand has the same
uniform geometric lattice majorant. -/
theorem abs_latticeBesselGrad_le {x : R4}
    (hx : InClosedPrincipalCube x) {k : Z4} (hk : k ≠ 0)
    (i : Fin dim) :
    |latticeBesselGrad x k i| ≤ latticeGeomWeight k := by
  unfold latticeBesselGrad euclideanBesselGrad
  calc
    |∫ t in Ioi (0 : ℝ),
        exp (-t) * euclideanHeatGrad t (latticeTranslate x k) i| =
        ‖∫ t in Ioi (0 : ℝ),
          exp (-t) * euclideanHeatGrad t (latticeTranslate x k) i‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∫ t in Ioi (0 : ℝ),
        ‖exp (-t) * euclideanHeatGrad t (latticeTranslate x k) i‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t in Ioi (0 : ℝ),
        |exp (-t) * euclideanHeatGrad t (latticeTranslate x k) i| := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      change ‖exp (-t) *
        euclideanHeatGrad t (latticeTranslate x k) i‖ =
          |exp (-t) * euclideanHeatGrad t (latticeTranslate x k) i|
      exact Real.norm_eq_abs _
    _ ≤ latticeGeomWeight k := grad_integral_weight_bound hx hk i

/-- The Hessian of a nonzero Bessel summand is uniformly dominated by
twice the common geometric lattice weight. -/
theorem abs_latticeBesselHess_le {x : R4}
    (hx : InClosedPrincipalCube x) {k : Z4} (hk : k ≠ 0)
    (i j : Fin dim) :
    |latticeBesselHess x k i j| ≤ 2 * latticeGeomWeight k := by
  unfold latticeBesselHess euclideanBesselHess
  calc
    |∫ t in Ioi (0 : ℝ),
        exp (-t) * euclideanHeatHess t (latticeTranslate x k) i j| =
        ‖∫ t in Ioi (0 : ℝ),
          exp (-t) * euclideanHeatHess t (latticeTranslate x k) i j‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∫ t in Ioi (0 : ℝ),
        ‖exp (-t) * euclideanHeatHess t (latticeTranslate x k) i j‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t in Ioi (0 : ℝ),
        |exp (-t) * euclideanHeatHess t (latticeTranslate x k) i j| := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      change ‖exp (-t) *
        euclideanHeatHess t (latticeTranslate x k) i j‖ =
          |exp (-t) * euclideanHeatHess t (latticeTranslate x k) i j|
      exact Real.norm_eq_abs _
    _ ≤ 2 * latticeGeomWeight k := hess_integral_weight_bound hx hk i j

theorem summable_nz_latticeGeomWeight :
    Summable fun k : NZ4 => latticeGeomWeight k :=
  summable_latticeGeomWeight.subtype _

theorem summable_latticeBesselTerm {x : R4}
    (hx : InClosedPrincipalCube x) :
    Summable fun k : NZ4 => latticeBesselTerm x k := by
  apply Summable.of_norm_bounded summable_nz_latticeGeomWeight
  intro k
  rw [Real.norm_eq_abs]
  exact abs_latticeBesselTerm_le hx k.property

theorem summable_latticeBesselGrad {x : R4}
    (hx : InClosedPrincipalCube x) (i : Fin dim) :
    Summable fun k : NZ4 => latticeBesselGrad x k i := by
  apply Summable.of_norm_bounded summable_nz_latticeGeomWeight
  intro k
  rw [Real.norm_eq_abs]
  exact abs_latticeBesselGrad_le hx k.property i

theorem summable_latticeBesselHess {x : R4}
    (hx : InClosedPrincipalCube x) (i j : Fin dim) :
    Summable fun k : NZ4 => latticeBesselHess x k i j := by
  apply Summable.of_norm_bounded
    (summable_nz_latticeGeomWeight.mul_left 2)
  intro k
  rw [Real.norm_eq_abs]
  exact abs_latticeBesselHess_le hx k.property i j

/-- Scalar shifts that keep the selected coordinate inside the open
principal interval. -/
def coordPrincipalInterval (x : R4) (i : Fin dim) : Set ℝ :=
  Ioo (-π - x i) (π - x i)

private theorem zero_mem_coordPrincipalInterval {x : R4}
    (hx : InOpenPrincipalCube x) (i : Fin dim) :
    (0 : ℝ) ∈ coordPrincipalInterval x i := by
  unfold coordPrincipalInterval
  have hi := hx i
  rw [abs_lt] at hi
  constructor <;> linarith

private theorem coordLine_closed_of_mem {x : R4}
    (hx : InOpenPrincipalCube x) (i : Fin dim) {s : ℝ}
    (hs : s ∈ coordPrincipalInterval x i) :
    InClosedPrincipalCube (coordLine x i s) := by
  intro j
  unfold coordPrincipalInterval at hs
  rcases hs with ⟨hslo, hshi⟩
  rcases eq_or_ne j i with rfl | hji
  · have hb :
        -π ≤ x j + s ∧ x j + s ≤ π := by
      constructor <;> linarith
    simpa [coordLine, abs_le] using hb
  · have hj := (hx j).le
    simpa [coordLine, hji] using hj

private theorem coordLine_open_of_mem {x : R4}
    (hx : InOpenPrincipalCube x) (i : Fin dim) {s : ℝ}
    (hs : s ∈ coordPrincipalInterval x i) :
    InOpenPrincipalCube (coordLine x i s) := by
  intro j
  unfold coordPrincipalInterval at hs
  rcases hs with ⟨hslo, hshi⟩
  rcases eq_or_ne j i with rfl | hji
  · have hb :
        -π < x j + s ∧ x j + s < π := by
      constructor <;> linarith
    simpa [coordLine, abs_lt] using hb
  · simpa [coordLine, hji] using hx j

private theorem mem_Ico_of_openCube {x : R4}
    (hx : InOpenPrincipalCube x) :
    ∀ i, x i ∈ Ico (-π) π := by
  intro i
  have hi := hx i
  rw [abs_lt] at hi
  exact ⟨hi.1.le, hi.2⟩

private theorem latticeTranslate_coordLine (x : R4) (k : Z4)
    (i : Fin dim) (s : ℝ) :
    latticeTranslate (coordLine x i s) k =
      coordLine (latticeTranslate x k) i s := by
  funext j
  rcases eq_or_ne j i with rfl | hji
  · simp [latticeTranslate, coordLine]
    ring
  · simp [latticeTranslate, coordLine, hji]

private theorem coordLine_add_local (x : R4) (i : Fin dim)
    (s u : ℝ) :
    coordLine (coordLine x i s) i u = coordLine x i (s + u) := by
  unfold coordLine
  module

private theorem hasDerivAt_latticeBesselTerm_coord_at
    {x : R4} (hx : InOpenPrincipalCube x) (k : NZ4)
    (i : Fin dim) {s : ℝ} (hs : s ∈ coordPrincipalInterval x i) :
    HasDerivAt
      (fun r => latticeBesselTerm (coordLine x i r) k)
      (latticeBesselGrad (coordLine x i s) k i) s := by
  have hcube := coordLine_closed_of_mem hx i hs
  have hbase :=
    hasDerivAt_euclideanBessel4_coord
      (latticeTranslate_distSq_ne_zero hcube k.property) i
  have hshift :
      HasDerivAt (fun r : ℝ => r - s) 1 s :=
    (hasDerivAt_id (x := s)).sub_const s
  have hcomp := hbase.comp_of_eq s hshift (by simp)
  unfold latticeBesselGrad
  refine (hcomp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => ?_)).congr_deriv ?_
  · simp only [Function.comp_apply]
    unfold latticeBesselTerm
    rw [← latticeTranslate_coordLine, coordLine_add_local]
    congr 3
    ring
  · simp

private theorem hasDerivAt_latticeBesselGrad_coord_at
    {x : R4} (hx : InOpenPrincipalCube x) (k : NZ4)
    (i j : Fin dim) {s : ℝ} (hs : s ∈ coordPrincipalInterval x j) :
    HasDerivAt
      (fun r => latticeBesselGrad (coordLine x j r) k i)
      (latticeBesselHess (coordLine x j s) k i j) s := by
  have hcube := coordLine_closed_of_mem hx j hs
  have hbase :=
    hasDerivAt_euclideanBesselGrad_coord
      (latticeTranslate_distSq_ne_zero hcube k.property) i j
  have hshift :
      HasDerivAt (fun r : ℝ => r - s) 1 s :=
    (hasDerivAt_id (x := s)).sub_const s
  have hcomp := hbase.comp_of_eq s hshift (by simp)
  unfold latticeBesselHess
  refine (hcomp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => ?_)).congr_deriv ?_
  · simp only [Function.comp_apply]
    unfold latticeBesselGrad
    rw [← latticeTranslate_coordLine, coordLine_add_local]
    congr 3
    ring
  · simp

/-- The actual nonzero-lattice part of the periodized Bessel kernel. -/
def nonzeroLatticeRemainder (x : R4) : ℝ :=
  ∑' k : NZ4, latticeBesselTerm x k

/-- Coordinate derivative series of the nonzero-lattice remainder. -/
def nonzeroLatticeRemainderGrad (x : R4) (i : Fin dim) : ℝ :=
  ∑' k : NZ4, latticeBesselGrad x k i

/-- Coordinate Hessian series of the nonzero-lattice remainder. -/
def nonzeroLatticeRemainderHess (x : R4) (i j : Fin dim) : ℝ :=
  ∑' k : NZ4, latticeBesselHess x k i j

/-- A global finite constant controlling the nonzero-lattice remainder
and its first two coordinate derivatives on the principal cube. -/
def nonzeroLatticeRemainderBound : ℝ :=
  ∑' k : NZ4, latticeGeomWeight k

/-- The nonzero-lattice series can be differentiated termwise on every
coordinate interval contained in the open principal cube. -/
theorem hasDerivAt_nonzeroLatticeRemainder_coord_at {x : R4}
    (hx : InOpenPrincipalCube x) (i : Fin dim) {s : ℝ}
    (hs : s ∈ coordPrincipalInterval x i) :
    HasDerivAt
      (fun r => nonzeroLatticeRemainder (coordLine x i r))
      (nonzeroLatticeRemainderGrad (coordLine x i s) i) s := by
  have hcube := coordLine_closed_of_mem hx i hs
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (u := fun k : NZ4 => latticeGeomWeight k)
    (t := coordPrincipalInterval x i)
    (g := fun k : NZ4 => fun r =>
      latticeBesselTerm (coordLine x i r) k)
    (g' := fun k : NZ4 => fun r =>
      latticeBesselGrad (coordLine x i r) k i)
    (y₀ := s) (y := s)
    summable_nz_latticeGeomWeight
    isOpen_Ioo isPreconnected_Ioo
    (fun k r hr =>
      hasDerivAt_latticeBesselTerm_coord_at hx k i hr)
    (fun k r hr => by
      rw [Real.norm_eq_abs]
      exact abs_latticeBesselGrad_le
        (coordLine_closed_of_mem hx i hr) k.property i)
    hs (summable_latticeBesselTerm hcube) hs
  simpa [nonzeroLatticeRemainder, nonzeroLatticeRemainderGrad] using hmain

/-- The first-derivative series is differentiable termwise, with Hessian
given by the absolutely convergent second-derivative series. -/
theorem hasDerivAt_nonzeroLatticeRemainderGrad_coord_at {x : R4}
    (hx : InOpenPrincipalCube x) (i j : Fin dim) {s : ℝ}
    (hs : s ∈ coordPrincipalInterval x j) :
    HasDerivAt
      (fun r => nonzeroLatticeRemainderGrad (coordLine x j r) i)
      (nonzeroLatticeRemainderHess (coordLine x j s) i j) s := by
  have hcube := coordLine_closed_of_mem hx j hs
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (u := fun k : NZ4 => 2 * latticeGeomWeight k)
    (t := coordPrincipalInterval x j)
    (g := fun k : NZ4 => fun r =>
      latticeBesselGrad (coordLine x j r) k i)
    (g' := fun k : NZ4 => fun r =>
      latticeBesselHess (coordLine x j r) k i j)
    (y₀ := s) (y := s)
    (summable_nz_latticeGeomWeight.mul_left 2)
    isOpen_Ioo isPreconnected_Ioo
    (fun k r hr =>
      hasDerivAt_latticeBesselGrad_coord_at hx k i j hr)
    (fun k r hr => by
      rw [Real.norm_eq_abs]
      exact abs_latticeBesselHess_le
        (coordLine_closed_of_mem hx j hr) k.property i j)
    hs (summable_latticeBesselGrad hcube i) hs
  simpa [nonzeroLatticeRemainderGrad,
    nonzeroLatticeRemainderHess] using hmain

theorem hasDerivAt_nonzeroLatticeRemainder_coord {x : R4}
    (hx : InOpenPrincipalCube x) (i : Fin dim) :
    HasDerivAt
      (fun r => nonzeroLatticeRemainder (coordLine x i r))
      (nonzeroLatticeRemainderGrad x i) 0 := by
  have h := hasDerivAt_nonzeroLatticeRemainder_coord_at hx i
    (zero_mem_coordPrincipalInterval hx i)
  simpa [coordLine] using h

theorem hasDerivAt_nonzeroLatticeRemainderGrad_coord {x : R4}
    (hx : InOpenPrincipalCube x) (i j : Fin dim) :
    HasDerivAt
      (fun r => nonzeroLatticeRemainderGrad (coordLine x j r) i)
      (nonzeroLatticeRemainderHess x i j) 0 := by
  have h := hasDerivAt_nonzeroLatticeRemainderGrad_coord_at hx i j
    (zero_mem_coordPrincipalInterval hx j)
  simpa [coordLine] using h

theorem nonzeroLatticeRemainderBound_nonneg :
    0 ≤ nonzeroLatticeRemainderBound := by
  unfold nonzeroLatticeRemainderBound
  exact tsum_nonneg fun k => by
    unfold latticeGeomWeight
    positivity

theorem abs_nonzeroLatticeRemainder_le {x : R4}
    (hx : InClosedPrincipalCube x) :
    |nonzeroLatticeRemainder x| ≤ nonzeroLatticeRemainderBound := by
  unfold nonzeroLatticeRemainder nonzeroLatticeRemainderBound
  rw [← Real.norm_eq_abs]
  apply (norm_tsum_le_tsum_norm (summable_latticeBesselTerm hx).norm).trans
  exact (summable_latticeBesselTerm hx).norm.tsum_le_tsum
    (fun k => by
      rw [Real.norm_eq_abs]
      exact abs_latticeBesselTerm_le hx k.property)
    summable_nz_latticeGeomWeight

theorem abs_nonzeroLatticeRemainderGrad_le {x : R4}
    (hx : InClosedPrincipalCube x) (i : Fin dim) :
    |nonzeroLatticeRemainderGrad x i| ≤ nonzeroLatticeRemainderBound := by
  unfold nonzeroLatticeRemainderGrad nonzeroLatticeRemainderBound
  rw [← Real.norm_eq_abs]
  apply (norm_tsum_le_tsum_norm
    (summable_latticeBesselGrad hx i).norm).trans
  exact (summable_latticeBesselGrad hx i).norm.tsum_le_tsum
    (fun k => by
      rw [Real.norm_eq_abs]
      exact abs_latticeBesselGrad_le hx k.property i)
    summable_nz_latticeGeomWeight

theorem abs_nonzeroLatticeRemainderHess_le {x : R4}
    (hx : InClosedPrincipalCube x) (i j : Fin dim) :
    |nonzeroLatticeRemainderHess x i j| ≤
      2 * nonzeroLatticeRemainderBound := by
  unfold nonzeroLatticeRemainderHess nonzeroLatticeRemainderBound
  rw [← Real.norm_eq_abs]
  apply (norm_tsum_le_tsum_norm
    (summable_latticeBesselHess hx i j).norm).trans
  calc
    ∑' k : NZ4, ‖latticeBesselHess x k i j‖ ≤
        ∑' k : NZ4, 2 * latticeGeomWeight k :=
      (summable_latticeBesselHess hx i j).norm.tsum_le_tsum
        (fun k => by
          rw [Real.norm_eq_abs]
          exact abs_latticeBesselHess_le hx k.property i j)
        (summable_nz_latticeGeomWeight.mul_left 2)
    _ = 2 * ∑' k : NZ4, latticeGeomWeight k :=
      summable_nz_latticeGeomWeight.tsum_mul_left 2

private theorem closedCube_of_mem_Ico {x : R4}
    (hx : ∀ i, x i ∈ Ico (-π) π) :
    InClosedPrincipalCube x := by
  intro i
  exact abs_le.mpr ⟨(hx i).1, (hx i).2.le⟩

theorem latticeDistSq_greenLocalPoint {x : R4}
    (hx : ∀ i, x i ∈ Ico (-π) π) (k : Z4) :
    latticeDistSq (greenLocalPoint x) k =
      euclideanDistSq (latticeTranslate x k) := by
  unfold latticeDistSq euclideanDistSq latticeTranslate
  rw [torusLift_greenLocalPoint hx]

private theorem greenLocal_integrand_eq_tsum {x : R4}
    (hx : ∀ i, x i ∈ Ico (-π) π) (t : ℝ) :
    exp (-t) * heatKernelT4 t (greenLocalPoint x) =
      ∑' k : Z4, exp (-t) *
        euclideanHeatKernel4 t (latticeTranslate x k) := by
  have hheat :
      heatKernelT4 t (greenLocalPoint x) =
        ∑' k : Z4, euclideanHeatKernel4 t (latticeTranslate x k) := by
    unfold heatKernelT4
    apply tsum_congr
    intro k
    unfold euclideanHeatKernel4
    rw [latticeDistSq_greenLocalPoint hx k]
  rw [hheat, tsum_mul_left]

private theorem integrableOn_zeroBesselIntegrand {x : R4}
    (hx : euclideanDistSq x ≠ 0) :
    IntegrableOn
      (fun t => exp (-t) * euclideanHeatKernel4 t x)
      (Ioi (0 : ℝ)) := by
  apply Integrable.mono' (integrableOn_euclideanHeatKernel4 hx)
  · apply Measurable.aestronglyMeasurable
    unfold euclideanHeatKernel4 euclideanDistSq
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    exact Filter.Eventually.of_forall fun t ht => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos (-t)),
        abs_of_nonneg (by
          unfold euclideanHeatKernel4
          positivity)]
      have hexp : exp (-t) ≤ 1 := by
        rw [exp_le_one_iff]
        have htpos : 0 < t := ht
        linarith
      exact mul_le_of_le_one_left (by
        unfold euclideanHeatKernel4
        positivity) hexp

private def nzEquivComplZero :
    NZ4 ≃ {k : Z4 // k ∉ ({0} : Finset Z4)} where
  toFun k := ⟨k, by simpa using k.property⟩
  invFun k := ⟨k, by simpa using k.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem summable_integral_norm_all_lattice {x : R4}
    (hx : ∀ i, x i ∈ Ico (-π) π) :
    Summable fun k : Z4 =>
      ∫ t in Ioi (0 : ℝ),
        ‖exp (-t) *
          euclideanHeatKernel4 t (latticeTranslate x k)‖ := by
  have hcube := closedCube_of_mem_Ico hx
  have hcompl :
      Summable fun k : {k : Z4 // k ∉ ({0} : Finset Z4)} =>
        ∫ t in Ioi (0 : ℝ),
          ‖exp (-t) *
            euclideanHeatKernel4 t (latticeTranslate x k)‖ := by
    apply Summable.of_norm_bounded
      (summable_latticeGeomWeight.subtype
        fun k => k ∉ ({0} : Finset Z4))
    intro k
    have hk : (k : Z4) ≠ 0 := by simpa using k.property
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simpa only [Real.norm_eq_abs, Function.comp_apply] using
      heat_integral_weight_bound hcube hk
  exact Summable.add_compl (s := ({0} : Finset Z4))
    Summable.of_finite hcompl

private theorem integrable_all_lattice_terms {x : R4}
    (hx : ∀ i, x i ∈ Ico (-π) π)
    (hx0 : euclideanDistSq x ≠ 0) (k : Z4) :
    Integrable
      (fun t => exp (-t) *
        euclideanHeatKernel4 t (latticeTranslate x k))
      (volume.restrict (Ioi (0 : ℝ))) := by
  rcases eq_or_ne k 0 with rfl | hk
  · have hzero : latticeTranslate x (0 : Z4) = x := by
      funext i
      simp [latticeTranslate]
    rw [hzero]
    exact integrableOn_zeroBesselIntegrand hx0
  · exact integrableOn_lattice_heat_integrand
      (closedCube_of_mem_Ico hx) hk

/-- On the principal cell away from its singular point, the heat-kernel
definition of the torus Green function is exactly the zero Euclidean
Bessel term plus the absolutely convergent nonzero-lattice remainder. -/
theorem greenLocalLift_eq_bessel_add_nonzeroRemainder {x : R4}
    (hx : ∀ i, x i ∈ Ico (-π) π)
    (hx0 : euclideanDistSq x ≠ 0) :
    greenLocalLift x =
      euclideanBessel4 x + nonzeroLatticeRemainder x := by
  let F : Z4 → ℝ → ℝ := fun k t =>
    exp (-t) * euclideanHeatKernel4 t (latticeTranslate x k)
  have hFnorm : Summable fun k : Z4 =>
      ∫ t, ‖F k t‖ ∂volume.restrict (Ioi (0 : ℝ)) := by
    simpa [F] using summable_integral_norm_all_lattice hx
  have hFint : ∀ k : Z4,
      Integrable (F k) (volume.restrict (Ioi (0 : ℝ))) := by
    intro k
    simpa [F] using integrable_all_lattice_terms hx hx0 k
  have hswap :
      ∑' k : Z4, (∫ t, F k t ∂volume.restrict (Ioi (0 : ℝ))) =
        ∫ t, (∑' k : Z4, F k t)
          ∂volume.restrict (Ioi (0 : ℝ)) :=
    integral_tsum_of_summable_integral_norm hFint hFnorm
  have hFvalues :
      Summable fun k : Z4 =>
        ∫ t, F k t ∂volume.restrict (Ioi (0 : ℝ)) :=
    hFnorm.of_norm_bounded fun k => norm_integral_le_integral_norm _
  calc
    greenLocalLift x =
        ∫ t in Ioi (0 : ℝ),
          ∑' k : Z4, F k t := by
      rw [greenLocalLift_eq]
      unfold greenFn
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      simpa [F] using greenLocal_integrand_eq_tsum hx t
    _ = ∑' k : Z4,
        ∫ t in Ioi (0 : ℝ), F k t := hswap.symm
    _ = (∑ k ∈ ({0} : Finset Z4),
          ∫ t in Ioi (0 : ℝ), F k t) +
        ∑' k : {k : Z4 // k ∉ ({0} : Finset Z4)},
          ∫ t in Ioi (0 : ℝ), F k t :=
      (hFvalues.sum_add_tsum_subtype_compl ({0} : Finset Z4)).symm
    _ = (∫ t in Ioi (0 : ℝ), F 0 t) +
        ∑' k : NZ4, ∫ t in Ioi (0 : ℝ), F k t := by
      rw [Finset.sum_singleton]
      congr 1
      exact (nzEquivComplZero.tsum_eq
        (fun k : {k : Z4 // k ∉ ({0} : Finset Z4)} =>
          ∫ t in Ioi (0 : ℝ), F k t)).symm
    _ = euclideanBessel4 x + nonzeroLatticeRemainder x := by
      unfold euclideanBessel4 nonzeroLatticeRemainder latticeBesselTerm
      congr 1
      have hzero : latticeTranslate x (0 : Z4) = x := by
        funext i
        simp [latticeTranslate]
      simp only [F, hzero]

theorem greenLocalRemainder_eq_nonzeroLatticeRemainder {x : R4}
    (hx : ∀ i, x i ∈ Ico (-π) π)
    (hx0 : euclideanDistSq x ≠ 0) :
    greenLocalRemainder x = nonzeroLatticeRemainder x := by
  unfold greenLocalRemainder
  rw [greenLocalLift_eq_bessel_add_nonzeroRemainder hx hx0]
  ring

/-- Actual first-coordinate derivative of the regular part of the local
Green kernel. -/
def greenLocalRemainderGrad (x : R4) (i : Fin dim) : ℝ :=
  nonzeroLatticeRemainderGrad x i

/-- Actual coordinate Hessian entry of the regular part. -/
def greenLocalRemainderHess (x : R4) (i j : Fin dim) : ℝ :=
  nonzeroLatticeRemainderHess x i j

theorem hasDerivAt_greenLocalRemainder_coord {x : R4}
    (hx : InOpenPrincipalCube x) (hx0 : euclideanDistSq x ≠ 0)
    (i : Fin dim) :
    HasDerivAt
      (fun s => greenLocalRemainder (coordLine x i s))
      (greenLocalRemainderGrad x i) 0 := by
  have hbase := hasDerivAt_nonzeroLatticeRemainder_coord hx i
  have hmem :
      ∀ᶠ s : ℝ in 𝓝 0, s ∈ coordPrincipalInterval x i :=
    isOpen_Ioo.mem_nhds (zero_mem_coordPrincipalInterval hx i)
  have hcont :
      ContinuousAt
        (fun s : ℝ => euclideanDistSq (coordLine x i s)) 0 := by
    unfold euclideanDistSq coordLine
    fun_prop
  have hzero :
      euclideanDistSq (coordLine x i 0) ≠ 0 := by
    simpa [coordLine] using hx0
  have hne :
      ∀ᶠ s : ℝ in 𝓝 0,
        euclideanDistSq (coordLine x i s) ≠ 0 :=
    hcont.eventually_ne hzero
  unfold greenLocalRemainderGrad
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards [hmem, hne] with s hs hs0
  have hopen := coordLine_open_of_mem hx i hs
  exact greenLocalRemainder_eq_nonzeroLatticeRemainder
    (mem_Ico_of_openCube hopen) hs0

theorem hasDerivAt_greenLocalRemainderGrad_coord {x : R4}
    (hx : InOpenPrincipalCube x) (i j : Fin dim) :
    HasDerivAt
      (fun s => greenLocalRemainderGrad (coordLine x j s) i)
      (greenLocalRemainderHess x i j) 0 := by
  simpa [greenLocalRemainderGrad, greenLocalRemainderHess] using
    hasDerivAt_nonzeroLatticeRemainderGrad_coord hx i j

theorem abs_greenLocalRemainder_le {x : R4}
    (hx : ∀ i, x i ∈ Ico (-π) π)
    (hx0 : euclideanDistSq x ≠ 0) :
    |greenLocalRemainder x| ≤ nonzeroLatticeRemainderBound := by
  rw [greenLocalRemainder_eq_nonzeroLatticeRemainder hx hx0]
  exact abs_nonzeroLatticeRemainder_le (closedCube_of_mem_Ico hx)

theorem abs_greenLocalRemainderGrad_le {x : R4}
    (hx : InClosedPrincipalCube x) (i : Fin dim) :
    |greenLocalRemainderGrad x i| ≤ nonzeroLatticeRemainderBound := by
  exact abs_nonzeroLatticeRemainderGrad_le hx i

theorem abs_greenLocalRemainderHess_le {x : R4}
    (hx : InClosedPrincipalCube x) (i j : Fin dim) :
    |greenLocalRemainderHess x i j| ≤
      2 * nonzeroLatticeRemainderBound := by
  exact abs_nonzeroLatticeRemainderHess_le hx i j

/-- Coordinate gradient entry of the full local Green kernel. -/
def greenLocalGrad (x : R4) (i : Fin dim) : ℝ :=
  euclideanBesselGrad x i + greenLocalRemainderGrad x i

/-- Coordinate Hessian entry of the full local Green kernel. -/
def greenLocalHess (x : R4) (i j : Fin dim) : ℝ :=
  euclideanBesselHess x i j + greenLocalRemainderHess x i j

theorem hasDerivAt_greenLocalLift_coord {x : R4}
    (hx : InOpenPrincipalCube x) (hx0 : euclideanDistSq x ≠ 0)
    (i : Fin dim) :
    HasDerivAt (fun s => greenLocalLift (coordLine x i s))
      (greenLocalGrad x i) 0 := by
  have hsing := hasDerivAt_euclideanBessel4_coord hx0 i
  have hreg := hasDerivAt_greenLocalRemainder_coord hx hx0 i
  unfold greenLocalGrad
  refine (hsing.add hreg).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => ?_)
  exact greenLocalLift_decomposition (coordLine x i s)

theorem hasDerivAt_greenLocalGrad_coord {x : R4}
    (hx : InOpenPrincipalCube x) (hx0 : euclideanDistSq x ≠ 0)
    (i j : Fin dim) :
    HasDerivAt (fun s => greenLocalGrad (coordLine x j s) i)
      (greenLocalHess x i j) 0 := by
  have hsing := hasDerivAt_euclideanBesselGrad_coord hx0 i j
  have hreg := hasDerivAt_greenLocalRemainderGrad_coord hx i j
  unfold greenLocalGrad greenLocalHess
  refine (hsing.add hreg).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

theorem abs_euclideanBessel4_le_laplaceFundamental4 {x : R4}
    (hx : euclideanDistSq x ≠ 0) :
    |euclideanBessel4 x| ≤ laplaceFundamental4 x := by
  have hleft := integrableOn_zeroBesselIntegrand hx
  have hright := integrableOn_euclideanHeatKernel4 hx
  unfold euclideanBessel4
  rw [abs_of_nonneg (integral_nonneg fun t => by
    exact mul_nonneg (exp_pos _).le (by
      unfold euclideanHeatKernel4
      positivity))]
  calc
    ∫ t in Ioi (0 : ℝ), exp (-t) * euclideanHeatKernel4 t x ≤
        ∫ t in Ioi (0 : ℝ), euclideanHeatKernel4 t x := by
      refine setIntegral_mono_on hleft hright measurableSet_Ioi
        fun t ht => ?_
      have hexp : exp (-t) ≤ 1 := by
        rw [exp_le_one_iff]
        have htpos : 0 < t := ht
        linarith
      exact mul_le_of_le_one_left (by
        unfold euclideanHeatKernel4
        positivity) hexp
    _ = laplaceFundamental4 x := integral_euclideanHeatKernel4 hx

/-- Zeroth-order singular estimate for the actual local Green kernel,
with the bounded periodization remainder kept explicit. -/
theorem abs_greenLocalLift_le {x : R4}
    (hx : ∀ i, x i ∈ Ico (-π) π)
    (hx0 : euclideanDistSq x ≠ 0) :
    |greenLocalLift x| ≤
      laplaceFundamental4 x + nonzeroLatticeRemainderBound := by
  rw [greenLocalLift_eq_bessel_add_nonzeroRemainder hx hx0]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_euclideanBessel4_le_laplaceFundamental4 hx0)
    (abs_nonzeroLatticeRemainder_le (closedCube_of_mem_Ico hx)))

/-- First-order `|x|⁻³`-scale singular estimate, plus the global smooth
periodization constant. -/
theorem abs_greenLocalGrad_le {x : R4}
    (hx : InClosedPrincipalCube x) (hx0 : euclideanDistSq x ≠ 0)
    (i : Fin dim) :
    |greenLocalGrad x i| ≤
      |x i| / (2 * π ^ 2) * (euclideanDistSq x)⁻¹ ^ 2 +
        nonzeroLatticeRemainderBound := by
  unfold greenLocalGrad
  exact (abs_add_le _ _).trans (add_le_add
    (abs_euclideanBesselGrad_le hx0 i)
    (abs_greenLocalRemainderGrad_le hx i))

/-- Second-order `|x|⁻⁴`-scale singular estimate, plus the global smooth
periodization constant. -/
theorem abs_greenLocalHess_le {x : R4}
    (hx : InClosedPrincipalCube x) (hx0 : euclideanDistSq x ≠ 0)
    (i j : Fin dim) :
    |greenLocalHess x i j| ≤
      |x i * x j| / (64 * π ^ 2) *
          (2 * (euclideanDistSq x / 4)⁻¹ ^ 3) +
        1 / (32 * π ^ 2) * (euclideanDistSq x / 4)⁻¹ ^ 2 +
        2 * nonzeroLatticeRemainderBound := by
  unfold greenLocalHess
  exact (abs_add_le _ _).trans (add_le_add
    (abs_euclideanBesselHess_le hx0 i j)
    (abs_greenLocalRemainderHess_le hx i j))

/-- The Euclidean part left after subtracting the exact four-dimensional
Laplace singularity. -/
def euclideanBesselLaplaceRemainder (x : R4) : ℝ :=
  euclideanBessel4 x - laplaceFundamental4 x

theorem euclideanBesselLaplaceRemainder_eq_integral {x : R4}
    (hx : euclideanDistSq x ≠ 0) :
    euclideanBesselLaplaceRemainder x =
      ∫ t in Ioi (0 : ℝ),
        (exp (-t) - 1) * euclideanHeatKernel4 t x := by
  unfold euclideanBesselLaplaceRemainder euclideanBessel4
  rw [← integral_euclideanHeatKernel4 hx,
    ← integral_sub (integrableOn_zeroBesselIntegrand hx)
      (integrableOn_euclideanHeatKernel4 hx)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  ring

private theorem exp_neg_div_le_sqrt_div {a t : ℝ}
    (ha : 0 < a) (ht : 0 < t) :
    exp (-(a / t)) ≤ √t / √a := by
  have hu : 0 < a / t := div_pos ha ht
  have hsqrt_nonneg : 0 ≤ √(a / t) := Real.sqrt_nonneg _
  have hsqrt_sq : √(a / t) ^ 2 = a / t :=
    Real.sq_sqrt hu.le
  have hsqrt_exp : √(a / t) ≤ exp (a / t) := by
    calc
      √(a / t) ≤ a / t + 1 := by
        nlinarith [sq_nonneg (√(a / t) - 1)]
      _ ≤ exp (a / t) := add_one_le_exp (a / t)
  calc
    exp (-(a / t)) = (exp (a / t))⁻¹ := by rw [exp_neg]
    _ ≤ (√(a / t))⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.2 hu) hsqrt_exp
    _ = √t / √a := by
      rw [Real.sqrt_div ha.le, inv_div]

private theorem one_sub_exp_neg_le (t : ℝ) :
    1 - exp (-t) ≤ t := by
  have h := add_one_le_exp (-t)
  linarith

private theorem inv_sqrt_eq_rpow {t : ℝ} (ht : 0 ≤ t) :
    (√t)⁻¹ = t ^ (-1 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht]
  congr 1
  ring

private theorem integrableOn_inv_sqrt_Ioc :
    IntegrableOn (fun t : ℝ => (√t)⁻¹) (Ioc 0 1) := by
  have hr :
      IntervalIntegrable (fun t : ℝ => t ^ (-1 / 2 : ℝ))
        volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hr' :
      IntegrableOn (fun t : ℝ => t ^ (-1 / 2 : ℝ)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      zero_le_one).mp hr
  refine hr'.congr_fun (fun t ht => ?_) measurableSet_Ioc
  exact (inv_sqrt_eq_rpow ht.1.le).symm

private theorem integral_inv_sqrt_Ioc :
    ∫ t in Ioc (0 : ℝ) 1, (√t)⁻¹ = 2 := by
  calc
    ∫ t in Ioc (0 : ℝ) 1, (√t)⁻¹ =
        ∫ t in Ioc (0 : ℝ) 1, t ^ (-1 / 2 : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      exact inv_sqrt_eq_rpow ht.1.le
    _ = ∫ t in (0 : ℝ)..1, t ^ (-1 / 2 : ℝ) :=
      (intervalIntegral.integral_of_le zero_le_one).symm
    _ = 2 := by
      rw [integral_rpow (Or.inl (by norm_num))]
      norm_num

private theorem inv_sq_eq_rpow_neg_two {t : ℝ} (ht : 0 ≤ t) :
    (t ^ 2)⁻¹ = t ^ (-2 : ℝ) := by
  rw [Real.rpow_neg ht, Real.rpow_two]

private theorem integrableOn_inv_sq_Ioi_one :
    IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Ioi 1) := by
  have hr :
      IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  refine hr.congr_fun (fun t ht => ?_) measurableSet_Ioi
  exact (inv_sq_eq_rpow_neg_two (by
    have htpos : 1 < t := ht
    linarith)).symm

private theorem integral_inv_sq_Ioi_one :
    ∫ t in Ioi (1 : ℝ), (t ^ 2)⁻¹ = 1 := by
  calc
    ∫ t in Ioi (1 : ℝ), (t ^ 2)⁻¹ =
        ∫ t in Ioi (1 : ℝ), t ^ (-2 : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact inv_sq_eq_rpow_neg_two (by
        have htpos : 1 < t := ht
        linarith)
    _ = 1 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
      norm_num

private theorem integrableOn_euclideanBesselLaplaceIntegrand {x : R4}
    (hx : euclideanDistSq x ≠ 0) :
    IntegrableOn
      (fun t => (exp (-t) - 1) * euclideanHeatKernel4 t x)
      (Ioi (0 : ℝ)) := by
  have h := (integrableOn_zeroBesselIntegrand hx).sub
    (integrableOn_euclideanHeatKernel4 hx)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  change exp (-t) * euclideanHeatKernel4 t x -
      euclideanHeatKernel4 t x =
    (exp (-t) - 1) * euclideanHeatKernel4 t x
  ring

/-- Improved `|x|⁻¹`-scale estimate for the Euclidean Bessel kernel
after subtracting its exact Laplace singularity.  The right-hand side is
kept in the natural heat-time scale `a = |x|²/4`. -/
theorem abs_euclideanBesselLaplaceRemainder_le {x : R4}
    (hx : euclideanDistSq x ≠ 0) :
    |euclideanBesselLaplaceRemainder x| ≤
      (16 * π ^ 2)⁻¹ *
        (2 * (√(euclideanDistSq x / 4))⁻¹ + 1) := by
  let a : ℝ := euclideanDistSq x / 4
  have hd : 0 < euclideanDistSq x :=
    lt_of_le_of_ne (euclideanDistSq_nonneg x) (Ne.symm hx)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  let f : ℝ → ℝ := fun t =>
    (exp (-t) - 1) * euclideanHeatKernel4 t x
  have hf : IntegrableOn f (Ioi (0 : ℝ)) := by
    simpa [f] using integrableOn_euclideanBesselLaplaceIntegrand hx
  have hfnorm :
      IntegrableOn (fun t => |f t|) (Ioi (0 : ℝ)) := by
    change Integrable (fun t => |f t|)
      (volume.restrict (Ioi (0 : ℝ)))
    simpa only [Real.norm_eq_abs] using hf.norm
  have hsmall :
      IntegrableOn (fun t => |f t|) (Ioc (0 : ℝ) 1) :=
    hfnorm.mono_set Ioc_subset_Ioi_self
  have hlarge :
      IntegrableOn (fun t => |f t|) (Ioi (1 : ℝ)) :=
    hfnorm.mono_set (fun t ht =>
      show 0 < t from lt_trans zero_lt_one ht)
  have hsmallMajor :
      IntegrableOn
        (fun t => ((16 * π ^ 2)⁻¹ * (√a)⁻¹) * (√t)⁻¹)
        (Ioc (0 : ℝ) 1) :=
    integrableOn_inv_sqrt_Ioc.const_mul _
  have hlargeMajor :
      IntegrableOn
        (fun t => (16 * π ^ 2)⁻¹ * (t ^ 2)⁻¹)
        (Ioi (1 : ℝ)) :=
    integrableOn_inv_sq_Ioi_one.const_mul _
  rw [euclideanBesselLaplaceRemainder_eq_integral hx]
  change |∫ t in Ioi (0 : ℝ), f t| ≤ _
  calc
    |∫ t in Ioi (0 : ℝ), f t| ≤
        ∫ t in Ioi (0 : ℝ), |f t| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (μ := volume.restrict (Ioi (0 : ℝ))) f)
    _ = (∫ t in Ioc (0 : ℝ) 1, |f t|) +
        ∫ t in Ioi (1 : ℝ), |f t| := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        hsmall hlarge, Ioc_union_Ioi_eq_Ioi zero_le_one]
    _ ≤ (∫ t in Ioc (0 : ℝ) 1,
          ((16 * π ^ 2)⁻¹ * (√a)⁻¹) * (√t)⁻¹) +
        ∫ t in Ioi (1 : ℝ),
          (16 * π ^ 2)⁻¹ * (t ^ 2)⁻¹ := by
      apply add_le_add
      · refine setIntegral_mono_on hsmall hsmallMajor
          measurableSet_Ioc fun t ht => ?_
        have htpos : 0 < t := ht.1
        have hexpLe : exp (-t) ≤ 1 := by
          rw [exp_le_one_iff]
          linarith
        have hdiff :
            |exp (-t) - 1| = 1 - exp (-t) := by
          rw [abs_of_nonpos (sub_nonpos.mpr hexpLe)]
          ring
        have hspace := exp_neg_div_le_sqrt_div ha htpos
        have htime := one_sub_exp_neg_le t
        change |(exp (-t) - 1) * euclideanHeatKernel4 t x| ≤ _
        rw [abs_mul, hdiff,
          abs_of_nonneg (by
            unfold euclideanHeatKernel4
            positivity),
          euclideanHeatKernel4_eq_timeMajorant htpos]
        calc
          (1 - exp (-t)) *
              ((16 * π ^ 2)⁻¹ *
                ((t ^ 2)⁻¹ *
                  exp (-(euclideanDistSq x / 4 / t)))) ≤
            t * ((16 * π ^ 2)⁻¹ *
                ((t ^ 2)⁻¹ * (√t / √a))) := by
              dsimp [a] at hspace
              gcongr
          _ = ((16 * π ^ 2)⁻¹ * (√a)⁻¹) * (√t)⁻¹ := by
            have ht0 : t ≠ 0 := ne_of_gt htpos
            have hsa0 : √a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
            have hst0 : √t ≠ 0 := (Real.sqrt_pos.2 htpos).ne'
            field_simp
            nlinarith [Real.sq_sqrt htpos.le]
      · refine setIntegral_mono_on hlarge hlargeMajor
          measurableSet_Ioi fun t ht => ?_
        have htpos : 0 < t := lt_trans zero_lt_one ht
        have hexpLe : exp (-t) ≤ 1 := by
          rw [exp_le_one_iff]
          linarith
        have hdiff :
            |exp (-t) - 1| = 1 - exp (-t) := by
          rw [abs_of_nonpos (sub_nonpos.mpr hexpLe)]
          ring
        have hdiffLe : 1 - exp (-t) ≤ 1 := by
          linarith [exp_pos (-t)]
        have hspace :
            exp (-(euclideanDistSq x / 4 / t)) ≤ 1 := by
          rw [exp_le_one_iff]
          exact neg_nonpos.mpr (by positivity)
        change |(exp (-t) - 1) * euclideanHeatKernel4 t x| ≤ _
        rw [abs_mul, hdiff,
          abs_of_nonneg (by
            unfold euclideanHeatKernel4
            positivity),
          euclideanHeatKernel4_eq_timeMajorant htpos]
        calc
          (1 - exp (-t)) *
              ((16 * π ^ 2)⁻¹ *
                ((t ^ 2)⁻¹ *
                  exp (-(euclideanDistSq x / 4 / t)))) ≤
            1 * ((16 * π ^ 2)⁻¹ * ((t ^ 2)⁻¹ * 1)) := by
              gcongr
          _ = (16 * π ^ 2)⁻¹ * (t ^ 2)⁻¹ := by ring
    _ = (16 * π ^ 2)⁻¹ * (2 * (√a)⁻¹ + 1) := by
      rw [integral_const_mul, integral_inv_sqrt_Ioc,
        integral_const_mul, integral_inv_sq_Ioi_one]
      ring
    _ = (16 * π ^ 2)⁻¹ *
        (2 * (√(euclideanDistSq x / 4))⁻¹ + 1) := by
      rfl

/-- Full near-diagonal remainder from paper (4.1), in principal
coordinates. -/
def greenLocalImprovedRemainder (x : R4) : ℝ :=
  greenLocalLift x - laplaceFundamental4 x

theorem greenLocalImprovedRemainder_decomposition {x : R4}
    (hx : ∀ i, x i ∈ Ico (-π) π)
    (hx0 : euclideanDistSq x ≠ 0) :
    greenLocalImprovedRemainder x =
      euclideanBesselLaplaceRemainder x +
        nonzeroLatticeRemainder x := by
  unfold greenLocalImprovedRemainder euclideanBesselLaplaceRemainder
  rw [greenLocalLift_eq_bessel_add_nonzeroRemainder hx hx0]
  ring

theorem abs_greenLocalImprovedRemainder_raw_le {x : R4}
    (hx : ∀ i, x i ∈ Ico (-π) π)
    (hx0 : euclideanDistSq x ≠ 0) :
    |greenLocalImprovedRemainder x| ≤
      (16 * π ^ 2)⁻¹ *
          (2 * (√(euclideanDistSq x / 4))⁻¹ + 1) +
        nonzeroLatticeRemainderBound := by
  rw [greenLocalImprovedRemainder_decomposition hx hx0]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_euclideanBesselLaplaceRemainder_le hx0)
    (abs_nonzeroLatticeRemainder_le (closedCube_of_mem_Ico hx)))

private theorem euclideanDistSq_le_four_pi_sq {x : R4}
    (hx : InClosedPrincipalCube x) :
    euclideanDistSq x ≤ 4 * π ^ 2 := by
  unfold euclideanDistSq
  have hcoord : ∀ i, x i ^ 2 ≤ π ^ 2 := by
    intro i
    have hi := hx i
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg (x i)) Real.pi_pos.le).2 hi
  simp only [Fin.sum_univ_four]
  linarith [hcoord 0, hcoord 1, hcoord 2, hcoord 3]

/-- Explicit global coefficient for the `|x|⁻¹` improved bound on the
principal cube. -/
def greenLocalImprovedBound : ℝ :=
  4 * (16 * π ^ 2)⁻¹ +
    2 * π * ((16 * π ^ 2)⁻¹ + nonzeroLatticeRemainderBound)

theorem greenLocalImprovedBound_pos :
    0 < greenLocalImprovedBound := by
  unfold greenLocalImprovedBound
  have hB := nonzeroLatticeRemainderBound_nonneg
  positivity

/-- Paper (4.1), improved zeroth-order near-diagonal estimate:
`G(x) - (4π²|x|²)⁻¹ = O(|x|⁻¹)`. -/
theorem abs_greenLocalImprovedRemainder_le {x : R4}
    (hx : ∀ i, x i ∈ Ico (-π) π)
    (hx0 : euclideanDistSq x ≠ 0) :
    |greenLocalImprovedRemainder x| ≤
      greenLocalImprovedBound * (√(euclideanDistSq x))⁻¹ := by
  have hraw := abs_greenLocalImprovedRemainder_raw_le hx hx0
  have hcube := closedCube_of_mem_Ico hx
  have hd : 0 < euclideanDistSq x :=
    lt_of_le_of_ne (euclideanDistSq_nonneg x) (Ne.symm hx0)
  have hsd : 0 < √(euclideanDistSq x) := Real.sqrt_pos.2 hd
  have hmax := euclideanDistSq_le_four_pi_sq hcube
  have hsqrtMax : √(euclideanDistSq x) ≤ 2 * π := by
    have hsq := Real.sq_sqrt hd.le
    have hs0 := Real.sqrt_nonneg (euclideanDistSq x)
    nlinarith [Real.pi_pos]
  have hone :
      (1 : ℝ) ≤ 2 * π * (√(euclideanDistSq x))⁻¹ := by
    rw [le_mul_inv_iff₀ hsd]
    simpa [one_mul] using hsqrtMax
  have hsqrtScale :
      (√(euclideanDistSq x / 4))⁻¹ =
        2 * (√(euclideanDistSq x))⁻¹ := by
    rw [Real.sqrt_div hd.le]
    norm_num
    rw [div_eq_mul_inv]
  have hc0 : 0 ≤ (16 * π ^ 2)⁻¹ := by positivity
  have hK :
      0 ≤ (16 * π ^ 2)⁻¹ + nonzeroLatticeRemainderBound :=
    add_nonneg hc0 nonzeroLatticeRemainderBound_nonneg
  have hconst :
      (16 * π ^ 2)⁻¹ + nonzeroLatticeRemainderBound ≤
        ((16 * π ^ 2)⁻¹ + nonzeroLatticeRemainderBound) *
          (2 * π * (√(euclideanDistSq x))⁻¹) := by
    calc
      (16 * π ^ 2)⁻¹ + nonzeroLatticeRemainderBound =
          ((16 * π ^ 2)⁻¹ + nonzeroLatticeRemainderBound) * 1 := by ring
      _ ≤ ((16 * π ^ 2)⁻¹ + nonzeroLatticeRemainderBound) *
          (2 * π * (√(euclideanDistSq x))⁻¹) :=
        mul_le_mul_of_nonneg_left hone hK
  calc
    |greenLocalImprovedRemainder x| ≤
        (16 * π ^ 2)⁻¹ *
            (2 * (√(euclideanDistSq x / 4))⁻¹ + 1) +
          nonzeroLatticeRemainderBound := hraw
    _ = 4 * (16 * π ^ 2)⁻¹ *
          (√(euclideanDistSq x))⁻¹ +
        ((16 * π ^ 2)⁻¹ + nonzeroLatticeRemainderBound) := by
      rw [hsqrtScale]
      ring
    _ ≤ 4 * (16 * π ^ 2)⁻¹ *
          (√(euclideanDistSq x))⁻¹ +
        ((16 * π ^ 2)⁻¹ + nonzeroLatticeRemainderBound) *
          (2 * π * (√(euclideanDistSq x))⁻¹) :=
      add_le_add le_rfl hconst
    _ = greenLocalImprovedBound *
          (√(euclideanDistSq x))⁻¹ := by
      unfold greenLocalImprovedBound
      ring

private theorem abs_coord_le_sqrt_dist (x : R4) (i : Fin dim) :
    |x i| ≤ √(euclideanDistSq x) := by
  have hi :
      x i ^ 2 ≤ euclideanDistSq x := by
    unfold euclideanDistSq
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j))
      (Finset.mem_univ i)
  apply (sq_le_sq₀ (abs_nonneg (x i))
    (Real.sqrt_nonneg (euclideanDistSq x))).mp
  rw [sq_abs, Real.sq_sqrt (euclideanDistSq_nonneg x)]
  exact hi

private theorem abs_coord_mul_le_dist (x : R4) (i j : Fin dim) :
    |x i * x j| ≤ euclideanDistSq x := by
  rw [abs_mul]
  calc
    |x i| * |x j| ≤
        √(euclideanDistSq x) * √(euclideanDistSq x) :=
      mul_le_mul (abs_coord_le_sqrt_dist x i)
        (abs_coord_le_sqrt_dist x j) (abs_nonneg (x j))
        (Real.sqrt_nonneg _)
    _ = euclideanDistSq x := by
      rw [← pow_two, Real.sq_sqrt (euclideanDistSq_nonneg x)]

/-- Explicit constants for the three singular estimates in paper
(4.1), for coordinate derivatives of order `0`, `1`, and `2`. -/
def greenLocalValueSingularBound : ℝ :=
  (4 * π ^ 2)⁻¹ +
    4 * π ^ 2 * nonzeroLatticeRemainderBound

def greenLocalGradSingularBound : ℝ :=
  (2 * π ^ 2)⁻¹ +
    (2 * π) ^ 3 * nonzeroLatticeRemainderBound

def greenLocalHessSingularBound : ℝ :=
  5 / (2 * π ^ 2) +
    2 * (2 * π) ^ 4 * nonzeroLatticeRemainderBound

theorem abs_greenLocalLift_singular {x : R4}
    (hx : ∀ i, x i ∈ Ico (-π) π)
    (hx0 : euclideanDistSq x ≠ 0) :
    |greenLocalLift x| ≤
      greenLocalValueSingularBound * (euclideanDistSq x)⁻¹ := by
  have hraw := abs_greenLocalLift_le hx hx0
  have hmax := euclideanDistSq_le_four_pi_sq
    (closedCube_of_mem_Ico hx)
  have hd : 0 < euclideanDistSq x :=
    lt_of_le_of_ne (euclideanDistSq_nonneg x) (Ne.symm hx0)
  have hone :
      (1 : ℝ) ≤ 4 * π ^ 2 * (euclideanDistSq x)⁻¹ := by
    rw [le_mul_inv_iff₀ hd]
    simpa using hmax
  have hB :
      nonzeroLatticeRemainderBound ≤
        nonzeroLatticeRemainderBound *
          (4 * π ^ 2 * (euclideanDistSq x)⁻¹) := by
    calc
      nonzeroLatticeRemainderBound =
          nonzeroLatticeRemainderBound * 1 := by ring
      _ ≤ nonzeroLatticeRemainderBound *
          (4 * π ^ 2 * (euclideanDistSq x)⁻¹) :=
        mul_le_mul_of_nonneg_left hone
          nonzeroLatticeRemainderBound_nonneg
  calc
    |greenLocalLift x| ≤
        laplaceFundamental4 x +
          nonzeroLatticeRemainderBound := hraw
    _ = (4 * π ^ 2)⁻¹ * (euclideanDistSq x)⁻¹ +
          nonzeroLatticeRemainderBound := by
      unfold laplaceFundamental4
      rw [mul_inv]
    _ ≤ (4 * π ^ 2)⁻¹ * (euclideanDistSq x)⁻¹ +
        nonzeroLatticeRemainderBound *
          (4 * π ^ 2 * (euclideanDistSq x)⁻¹) :=
      add_le_add le_rfl hB
    _ = greenLocalValueSingularBound *
        (euclideanDistSq x)⁻¹ := by
      unfold greenLocalValueSingularBound
      ring

theorem abs_greenLocalGrad_singular {x : R4}
    (hx : InClosedPrincipalCube x)
    (hx0 : euclideanDistSq x ≠ 0) (i : Fin dim) :
    |greenLocalGrad x i| ≤
      greenLocalGradSingularBound *
        (√(euclideanDistSq x))⁻¹ ^ 3 := by
  have hraw := abs_greenLocalGrad_le hx hx0 i
  have hd : 0 < euclideanDistSq x :=
    lt_of_le_of_ne (euclideanDistSq_nonneg x) (Ne.symm hx0)
  have hs : 0 < √(euclideanDistSq x) := Real.sqrt_pos.2 hd
  have hsSq := Real.sq_sqrt hd.le
  have hsmax : √(euclideanDistSq x) ≤ 2 * π := by
    have hmax := euclideanDistSq_le_four_pi_sq hx
    have hs0 := Real.sqrt_nonneg (euclideanDistSq x)
    nlinarith [Real.pi_pos]
  have hterm :
      |x i| / (2 * π ^ 2) * (euclideanDistSq x)⁻¹ ^ 2 ≤
        (2 * π ^ 2)⁻¹ * (√(euclideanDistSq x))⁻¹ ^ 3 := by
    calc
      |x i| / (2 * π ^ 2) * (euclideanDistSq x)⁻¹ ^ 2 ≤
          √(euclideanDistSq x) / (2 * π ^ 2) *
            (euclideanDistSq x)⁻¹ ^ 2 := by
        gcongr
        exact abs_coord_le_sqrt_dist x i
      _ = (2 * π ^ 2)⁻¹ *
          (√(euclideanDistSq x))⁻¹ ^ 3 := by
        have hpi : π ≠ 0 := Real.pi_ne_zero
        field_simp [hd.ne', hs.ne']
        nlinarith
  have hs3 :
      (√(euclideanDistSq x)) ^ 3 ≤ (2 * π) ^ 3 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsmax 3
  have hone3 :
      (1 : ℝ) ≤ (2 * π) ^ 3 *
          (√(euclideanDistSq x))⁻¹ ^ 3 := by
    rw [inv_pow]
    rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hs 3)]
    simpa using hs3
  have hB :
      nonzeroLatticeRemainderBound ≤
        ((2 * π) ^ 3 * nonzeroLatticeRemainderBound) *
          (√(euclideanDistSq x))⁻¹ ^ 3 := by
    calc
      nonzeroLatticeRemainderBound =
          nonzeroLatticeRemainderBound * 1 := by ring
      _ ≤ nonzeroLatticeRemainderBound *
          ((2 * π) ^ 3 *
            (√(euclideanDistSq x))⁻¹ ^ 3) :=
        mul_le_mul_of_nonneg_left hone3
          nonzeroLatticeRemainderBound_nonneg
      _ = ((2 * π) ^ 3 * nonzeroLatticeRemainderBound) *
          (√(euclideanDistSq x))⁻¹ ^ 3 := by ring
  calc
    |greenLocalGrad x i| ≤
        |x i| / (2 * π ^ 2) * (euclideanDistSq x)⁻¹ ^ 2 +
          nonzeroLatticeRemainderBound := hraw
    _ ≤ (2 * π ^ 2)⁻¹ * (√(euclideanDistSq x))⁻¹ ^ 3 +
        ((2 * π) ^ 3 * nonzeroLatticeRemainderBound) *
          (√(euclideanDistSq x))⁻¹ ^ 3 :=
      add_le_add hterm hB
    _ = greenLocalGradSingularBound *
        (√(euclideanDistSq x))⁻¹ ^ 3 := by
      unfold greenLocalGradSingularBound
      ring

theorem abs_greenLocalHess_singular {x : R4}
    (hx : InClosedPrincipalCube x)
    (hx0 : euclideanDistSq x ≠ 0) (i j : Fin dim) :
    |greenLocalHess x i j| ≤
      greenLocalHessSingularBound *
        (√(euclideanDistSq x))⁻¹ ^ 4 := by
  have hraw := abs_greenLocalHess_le hx hx0 i j
  have hd : 0 < euclideanDistSq x :=
    lt_of_le_of_ne (euclideanDistSq_nonneg x) (Ne.symm hx0)
  have hs : 0 < √(euclideanDistSq x) := Real.sqrt_pos.2 hd
  have hsSq := Real.sq_sqrt hd.le
  have hsmax : √(euclideanDistSq x) ≤ 2 * π := by
    have hmax := euclideanDistSq_le_four_pi_sq hx
    have hs0 := Real.sqrt_nonneg (euclideanDistSq x)
    nlinarith [Real.pi_pos]
  have hfirst :
      |x i * x j| / (64 * π ^ 2) *
          (2 * (euclideanDistSq x / 4)⁻¹ ^ 3) ≤
        2 / π ^ 2 * (euclideanDistSq x)⁻¹ ^ 2 := by
    calc
      |x i * x j| / (64 * π ^ 2) *
          (2 * (euclideanDistSq x / 4)⁻¹ ^ 3) ≤
        euclideanDistSq x / (64 * π ^ 2) *
          (2 * (euclideanDistSq x / 4)⁻¹ ^ 3) := by
            gcongr
            exact abs_coord_mul_le_dist x i j
      _ = 2 / π ^ 2 * (euclideanDistSq x)⁻¹ ^ 2 := by
        have hpi : π ≠ 0 := Real.pi_ne_zero
        field_simp [hd.ne']
        ring
  have hsecond :
      1 / (32 * π ^ 2) * (euclideanDistSq x / 4)⁻¹ ^ 2 =
        1 / (2 * π ^ 2) * (euclideanDistSq x)⁻¹ ^ 2 := by
    have hpi : π ≠ 0 := Real.pi_ne_zero
    field_simp [hd.ne']
    ring
  have hlocal :
      |x i * x j| / (64 * π ^ 2) *
          (2 * (euclideanDistSq x / 4)⁻¹ ^ 3) +
        1 / (32 * π ^ 2) * (euclideanDistSq x / 4)⁻¹ ^ 2 ≤
      5 / (2 * π ^ 2) * (√(euclideanDistSq x))⁻¹ ^ 4 := by
    calc
      _ ≤ 2 / π ^ 2 * (euclideanDistSq x)⁻¹ ^ 2 +
          1 / (2 * π ^ 2) * (euclideanDistSq x)⁻¹ ^ 2 := by
        rw [hsecond]
        exact add_le_add hfirst le_rfl
      _ = 5 / (2 * π ^ 2) *
          (√(euclideanDistSq x))⁻¹ ^ 4 := by
        have hpi : π ≠ 0 := Real.pi_ne_zero
        field_simp [hd.ne', hs.ne']
        nlinarith
  have hs4 :
      (√(euclideanDistSq x)) ^ 4 ≤ (2 * π) ^ 4 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsmax 4
  have hone4 :
      (1 : ℝ) ≤ (2 * π) ^ 4 *
          (√(euclideanDistSq x))⁻¹ ^ 4 := by
    rw [inv_pow]
    rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hs 4)]
    simpa using hs4
  have hB :
      2 * nonzeroLatticeRemainderBound ≤
        (2 * (2 * π) ^ 4 * nonzeroLatticeRemainderBound) *
          (√(euclideanDistSq x))⁻¹ ^ 4 := by
    calc
      2 * nonzeroLatticeRemainderBound =
          (2 * nonzeroLatticeRemainderBound) * 1 := by ring
      _ ≤ (2 * nonzeroLatticeRemainderBound) *
          ((2 * π) ^ 4 *
            (√(euclideanDistSq x))⁻¹ ^ 4) :=
        mul_le_mul_of_nonneg_left hone4
          (mul_nonneg (by norm_num)
            nonzeroLatticeRemainderBound_nonneg)
      _ = (2 * (2 * π) ^ 4 * nonzeroLatticeRemainderBound) *
          (√(euclideanDistSq x))⁻¹ ^ 4 := by ring
  calc
    |greenLocalHess x i j| ≤
        (|x i * x j| / (64 * π ^ 2) *
            (2 * (euclideanDistSq x / 4)⁻¹ ^ 3) +
          1 / (32 * π ^ 2) *
            (euclideanDistSq x / 4)⁻¹ ^ 2) +
          2 * nonzeroLatticeRemainderBound := by
      simpa only [add_assoc] using hraw
    _ ≤ 5 / (2 * π ^ 2) *
          (√(euclideanDistSq x))⁻¹ ^ 4 +
        (2 * (2 * π) ^ 4 * nonzeroLatticeRemainderBound) *
          (√(euclideanDistSq x))⁻¹ ^ 4 :=
      add_le_add hlocal hB
    _ = greenLocalHessSingularBound *
        (√(euclideanDistSq x))⁻¹ ^ 4 := by
      unfold greenLocalHessSingularBound
      ring

end

end Anderson4D
