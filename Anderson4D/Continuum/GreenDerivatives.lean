import Anderson4D.Continuum.GreenTimeIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Derivatives of the local Euclidean part of the Green kernel

The singular summand of the periodized Bessel kernel is the `k = 0`
Euclidean heat kernel.  This file differentiates that summand under its
time integral.  The resulting first- and second-coordinate derivative
formulas, together with explicit `|x|⁻³` and `|x|⁻⁴` majorants, are the
singular part of paper (4.1).
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Real Set

/-- The `k = 0` Euclidean contribution to the Bessel Green kernel. -/
def euclideanBessel4 (x : R4) : ℝ :=
  ∫ t in Ioi (0 : ℝ), exp (-t) * euclideanHeatKernel4 t x

/-- Coordinate derivative of the Euclidean heat kernel. -/
def euclideanHeatGrad (t : ℝ) (x : R4) (i : Fin dim) : ℝ :=
  -(x i) / (2 * t) * euclideanHeatKernel4 t x

/-- Coordinate Hessian entry of the Euclidean heat kernel. -/
def euclideanHeatHess (t : ℝ) (x : R4) (i j : Fin dim) : ℝ :=
  ((x i * x j) / (4 * t ^ 2) -
      (if i = j then (2 * t)⁻¹ else 0)) *
    euclideanHeatKernel4 t x

/-- First-coordinate derivative candidate after the Bessel time integral. -/
def euclideanBesselGrad (x : R4) (i : Fin dim) : ℝ :=
  ∫ t in Ioi (0 : ℝ), exp (-t) * euclideanHeatGrad t x i

/-- Coordinate Hessian candidate after the Bessel time integral. -/
def euclideanBesselHess (x : R4) (i j : Fin dim) : ℝ :=
  ∫ t in Ioi (0 : ℝ), exp (-t) * euclideanHeatHess t x i j

/-- The Green function pulled back along the coordinatewise quotient
`ℝ⁴ → 𝕋⁴`.  On the principal cube its singular summand is
`euclideanBessel4`. -/
def greenLocalLift (x : R4) : ℝ :=
  greenFn (fun i => (x i : AddCircle (2 * π)))

/-- Coordinatewise quotient point associated with a Euclidean lift. -/
def greenLocalPoint (x : R4) : T4 :=
  fun i => (x i : AddCircle (2 * π))

/-- The regular part left after removing the local Euclidean Bessel
summand from the pulled-back torus Green function. -/
def greenLocalRemainder (x : R4) : ℝ :=
  greenLocalLift x - euclideanBessel4 x

theorem greenLocalLift_eq (x : R4) :
    greenLocalLift x = greenFn (greenLocalPoint x) :=
  rfl

theorem greenLocalLift_decomposition (x : R4) :
    greenLocalLift x =
      euclideanBessel4 x + greenLocalRemainder x := by
  unfold greenLocalRemainder
  ring

theorem torusLift_greenLocalPoint {x : R4}
    (hx : ∀ i, x i ∈ Ico (-π) π) :
    torusLift (greenLocalPoint x) = x := by
  funext i
  have hmem : x i ∈ Ico (-π) (-π + 2 * π) :=
    ⟨(hx i).1, by have := (hx i).2; linarith⟩
  show ((AddCircle.equivIco (2 * π) (-π))
    ((x i : ℝ) : AddCircle (2 * π)) : ℝ) = x i
  rw [AddCircle.equivIco_coe_eq hmem]

theorem latticeDistSq_greenLocalPoint_zero {x : R4}
    (hx : ∀ i, x i ∈ Ico (-π) π) :
    latticeDistSq (greenLocalPoint x) (0 : Z4) =
      euclideanDistSq x := by
  unfold latticeDistSq euclideanDistSq
  rw [torusLift_greenLocalPoint hx]
  simp

/-- On the principal cube, the Euclidean heat kernel is exactly the
zero lattice summand of the heat kernel defining `greenLocalLift`. -/
theorem euclideanHeatKernel4_eq_greenLocalTerm_zero {x : R4}
    (hx : ∀ i, x i ∈ Ico (-π) π) (t : ℝ) :
    euclideanHeatKernel4 t x =
      (4 * π * t) ^ (-2 : ℤ) *
        exp (-latticeDistSq (greenLocalPoint x) (0 : Z4) / (4 * t)) := by
  unfold euclideanHeatKernel4
  rw [latticeDistSq_greenLocalPoint_zero hx]

/-- The local Euclidean heat kernel is a genuine summand, rather than an
auxiliary comparison kernel: it is bounded by the periodized heat kernel
whose Bessel integral defines `greenFn`. -/
theorem euclideanHeatKernel4_le_heatKernelT4_greenLocal {x : R4}
    (hx : ∀ i, x i ∈ Ico (-π) π) {t : ℝ} (ht : 0 < t) :
    euclideanHeatKernel4 t x ≤ heatKernelT4 t (greenLocalPoint x) := by
  rw [euclideanHeatKernel4_eq_greenLocalTerm_zero hx]
  unfold heatKernelT4
  exact (summable_heatKernel_terms ht (greenLocalPoint x)).le_tsum
    (0 : Z4) (fun k _ => by positivity)

/-- Coordinate line through a Euclidean lift. -/
def coordLine (x : R4) (i : Fin dim) (s : ℝ) : R4 :=
  x + s • Pi.single i 1

private theorem coordLine_apply_same (x : R4) (i : Fin dim) (s : ℝ) :
    coordLine x i s i = x i + s := by
  simp [coordLine]

private theorem coordLine_apply_ne (x : R4) {i j : Fin dim} (hij : j ≠ i) (s : ℝ) :
    coordLine x i s j = x j := by
  simp [coordLine, hij]

@[simp] private theorem coordLine_zero (x : R4) (i : Fin dim) :
    coordLine x i 0 = x := by
  simp [coordLine]

private theorem coordLine_add (x : R4) (i : Fin dim) (s u : ℝ) :
    coordLine (coordLine x i s) i u = coordLine x i (s + u) := by
  unfold coordLine
  module

private theorem euclideanDistSq_coordLine (x : R4) (i : Fin dim) (s : ℝ) :
    euclideanDistSq (coordLine x i s) =
      euclideanDistSq x + 2 * s * x i + s ^ 2 := by
  classical
  unfold euclideanDistSq
  calc
    ∑ j, coordLine x i s j ^ 2 =
        ∑ j, (x j ^ 2 + 2 * x j * (if j = i then s else 0) +
          (if j = i then s ^ 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      rcases eq_or_ne j i with rfl | hji
      · rw [coordLine_apply_same]
        simp
        ring
      · rw [coordLine_apply_ne x hji]
        simp [hji]
    _ = ∑ j, x j ^ 2 + 2 * s * x i + s ^ 2 := by
      simp [Finset.sum_add_distrib]
      ring

private theorem exists_coord_ne_zero {x : R4}
    (hx : euclideanDistSq x ≠ 0) :
    ∃ k : Fin dim, x k ≠ 0 := by
  by_contra h
  push Not at h
  apply hx
  unfold euclideanDistSq
  simp [h]

private theorem sq_coord_le_euclideanDistSq (x : R4) (k : Fin dim) :
    x k ^ 2 ≤ euclideanDistSq x := by
  unfold euclideanDistSq
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ k)

private theorem abs_coordLine_apply_le (x : R4) (j q : Fin dim)
    {s δ : ℝ} (hs : |s| ≤ δ) :
    |coordLine x j s q| ≤ |x q| + δ := by
  rcases eq_or_ne q j with rfl | hqj
  · rw [coordLine_apply_same]
    exact (abs_add_le _ _).trans (by linarith)
  · rw [coordLine_apply_ne x hqj]
    have hδ : 0 ≤ δ := (abs_nonneg s).trans hs
    linarith

private theorem euclideanDistSq_coordLine_lower (x : R4) (j k : Fin dim)
    {s : ℝ} (hs : |s| < |x k| / 2) :
    (x k) ^ 2 / 4 ≤ euclideanDistSq (coordLine x j s) := by
  have habs : |x k| / 2 ≤ |coordLine x j s k| := by
    rcases eq_or_ne k j with rfl | hkj
    · rw [coordLine_apply_same]
      have htri : |x k| ≤ |x k + s| + |s| := by
        calc
          |x k| = |x k + s + -s| := by congr 1; ring
          _ ≤ |x k + s| + |-s| := abs_add_le _ _
          _ = |x k + s| + |s| := by rw [abs_neg]
      linarith
    · rw [coordLine_apply_ne x hkj]
      linarith [abs_nonneg (x k)]
  have hsquare :
      (x k) ^ 2 / 4 ≤ (coordLine x j s k) ^ 2 := by
    rw [← sq_abs (x k), ← sq_abs (coordLine x j s k)]
    nlinarith [abs_nonneg (x k), abs_nonneg (coordLine x j s k)]
  exact hsquare.trans (sq_coord_le_euclideanDistSq _ k)

theorem hasDerivAt_euclideanHeatKernel4_coord {t : ℝ} (ht : t ≠ 0)
    (x : R4) (i : Fin dim) :
    HasDerivAt (fun s => euclideanHeatKernel4 t (coordLine x i s))
      (euclideanHeatGrad t x i) 0 := by
  rw [show (fun s => euclideanHeatKernel4 t (coordLine x i s)) =
      fun s => (4 * π * t) ^ (-2 : ℤ) *
        exp (-(euclideanDistSq x + 2 * s * x i + s ^ 2) / (4 * t)) by
    funext s
    rw [euclideanHeatKernel4, euclideanDistSq_coordLine]]
  have hpoly :
      HasDerivAt
        (fun s : ℝ => euclideanDistSq x + 2 * s * x i + s ^ 2)
        (2 * x i) 0 := by
    have hraw :=
      ((hasDerivAt_const (x := (0 : ℝ)) (c := euclideanDistSq x)).add
        ((hasDerivAt_id (x := (0 : ℝ))).const_mul (2 * x i))).add
        ((hasDerivAt_id (x := (0 : ℝ))).pow 2)
    refine (hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
    · dsimp
      ring
    · dsimp
      ring
  have harg :
      HasDerivAt
        (fun s : ℝ => -(euclideanDistSq x + 2 * s * x i + s ^ 2) / (4 * t))
        (-(2 * x i) / (4 * t)) 0 :=
    hpoly.neg.div_const (4 * t)
  have hexp :
      HasDerivAt
        (fun s : ℝ => exp (-(euclideanDistSq x + 2 * s * x i + s ^ 2) / (4 * t)))
        (exp (-(euclideanDistSq x) / (4 * t)) * (-(2 * x i) / (4 * t))) 0 := by
    have hraw := (Real.hasDerivAt_exp
      (-(euclideanDistSq x + 2 * (0 : ℝ) * x i + (0 : ℝ) ^ 2) /
        (4 * t))).comp (0 : ℝ) harg
    exact hraw.congr_deriv (by ring)
  have hraw := hexp.const_mul ((4 * π * t) ^ (-2 : ℤ))
  refine hraw.congr_deriv ?_
  simp only [euclideanHeatGrad, euclideanHeatKernel4]
  field_simp [ht]
  ring

theorem hasDerivAt_euclideanHeatKernel4_coord_at {t : ℝ} (ht : t ≠ 0)
    (x : R4) (i : Fin dim) (s : ℝ) :
    HasDerivAt (fun r => euclideanHeatKernel4 t (coordLine x i r))
      (euclideanHeatGrad t (coordLine x i s) i) s := by
  have hbase :=
    hasDerivAt_euclideanHeatKernel4_coord ht (coordLine x i s) i
  have hshift :
      HasDerivAt (fun r : ℝ => r - s) 1 s :=
    (hasDerivAt_id (x := s)).sub_const s
  have hcomp := hbase.comp_of_eq s hshift (by simp)
  refine (hcomp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => ?_)).congr_deriv (by simp)
  simp only [Function.comp_apply]
  rw [coordLine_add]
  congr 2
  ring

theorem hasDerivAt_euclideanHeatGrad_coord {t : ℝ} (ht : t ≠ 0)
    (x : R4) (i j : Fin dim) :
    HasDerivAt (fun s => euclideanHeatGrad t (coordLine x j s) i)
      (euclideanHeatHess t x i j) 0 := by
  have hcoord :
      HasDerivAt (fun s : ℝ => -(coordLine x j s i) / (2 * t))
        (if i = j then -(2 * t)⁻¹ else 0) 0 := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      have hraw := (hasDerivAt_id (x := (0 : ℝ))).add_const (x i)
      have hraw' := hraw.neg.div_const (2 * t)
      refine (hraw'.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
      · rw [coordLine_apply_same]
        dsimp
        ring
      · simp [div_eq_mul_inv]
    · rw [if_neg hij]
      have hconst := hasDerivAt_const (x := (0 : ℝ)) (c := -(x i) / (2 * t))
      simpa only [coordLine_apply_ne x hij] using hconst
  have hheat := hasDerivAt_euclideanHeatKernel4_coord ht x j
  have hraw := hcoord.mul hheat
  have hraw' :
      HasDerivAt (fun s => euclideanHeatGrad t (coordLine x j s) i)
        ((if i = j then -(2 * t)⁻¹ else 0) *
          euclideanHeatKernel4 t (coordLine x j 0) +
          (-(coordLine x j 0 i) / (2 * t)) * euclideanHeatGrad t x j) 0 := by
    exact hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  refine hraw'.congr_deriv ?_
  simp only [coordLine_zero, euclideanHeatHess, euclideanHeatGrad]
  by_cases hij : i = j
  · subst j
    simp only [if_pos]
    field_simp [ht]
    ring
  · simp only [if_neg hij]
    field_simp [ht]
    ring

theorem hasDerivAt_euclideanHeatGrad_coord_at {t : ℝ} (ht : t ≠ 0)
    (x : R4) (i j : Fin dim) (s : ℝ) :
    HasDerivAt (fun r => euclideanHeatGrad t (coordLine x j r) i)
      (euclideanHeatHess t (coordLine x j s) i j) s := by
  have hbase :=
    hasDerivAt_euclideanHeatGrad_coord ht (coordLine x j s) i j
  have hshift :
      HasDerivAt (fun r : ℝ => r - s) 1 s :=
    (hasDerivAt_id (x := s)).sub_const s
  have hcomp := hbase.comp_of_eq s hshift (by simp)
  refine (hcomp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => ?_)).congr_deriv (by simp)
  simp only [Function.comp_apply]
  rw [coordLine_add]
  congr 3
  ring

theorem abs_euclideanHeatGrad {t : ℝ} (ht : 0 < t)
    (x : R4) (i : Fin dim) :
    |euclideanHeatGrad t x i| =
      |x i| / (32 * π ^ 2) *
        ((t ^ 3)⁻¹ * exp (-(euclideanDistSq x / 4 / t))) := by
  rw [euclideanHeatGrad, euclideanHeatKernel4_eq_timeMajorant ht x]
  rw [abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * t),
    abs_of_nonneg (by positivity :
      0 ≤ (16 * π ^ 2)⁻¹ *
        ((t ^ 2)⁻¹ * exp (-(euclideanDistSq x / 4 / t))))]
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem integrableOn_euclideanHeatGrad {x : R4}
    (hx : euclideanDistSq x ≠ 0) (i : Fin dim) :
    IntegrableOn (fun t => euclideanHeatGrad t x i) (Ioi (0 : ℝ)) := by
  have hs : 0 < euclideanDistSq x :=
    lt_of_le_of_ne (euclideanDistSq_nonneg x) (Ne.symm hx)
  have ha : 0 < euclideanDistSq x / 4 := by positivity
  have hmajor :
      IntegrableOn
        (fun t => |x i| / (32 * π ^ 2) *
          ((t ^ 3)⁻¹ * exp (-(euclideanDistSq x / 4 / t))))
        (Ioi (0 : ℝ)) :=
    (integrableOn_inv_cube_exp ha).const_mul _
  apply (integrable_norm_iff
    (μ := volume.restrict (Ioi (0 : ℝ))) (by
      apply Measurable.aestronglyMeasurable
      unfold euclideanHeatGrad euclideanHeatKernel4 euclideanDistSq
      fun_prop)).mp
  refine hmajor.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simpa [Real.norm_eq_abs] using (abs_euclideanHeatGrad ht x i).symm

theorem integral_abs_euclideanHeatGrad {x : R4}
    (hx : euclideanDistSq x ≠ 0) (i : Fin dim) :
    ∫ t in Ioi (0 : ℝ), |euclideanHeatGrad t x i| =
      |x i| / (2 * π ^ 2) * (euclideanDistSq x)⁻¹ ^ 2 := by
  have hs : 0 < euclideanDistSq x :=
    lt_of_le_of_ne (euclideanDistSq_nonneg x) (Ne.symm hx)
  have ha : 0 < euclideanDistSq x / 4 := by positivity
  calc
    ∫ t in Ioi (0 : ℝ), |euclideanHeatGrad t x i| =
        ∫ t in Ioi (0 : ℝ), |x i| / (32 * π ^ 2) *
          ((t ^ 3)⁻¹ * exp (-(euclideanDistSq x / 4 / t))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact abs_euclideanHeatGrad ht x i
    _ = |x i| / (32 * π ^ 2) * (euclideanDistSq x / 4)⁻¹ ^ 2 := by
      rw [integral_const_mul, integral_inv_cube_exp ha]
    _ = |x i| / (2 * π ^ 2) * (euclideanDistSq x)⁻¹ ^ 2 := by
      have hpi : π ≠ 0 := Real.pi_ne_zero
      field_simp
      ring

theorem abs_euclideanHeatHess_le {t : ℝ} (ht : 0 < t)
    (x : R4) (i j : Fin dim) :
    |euclideanHeatHess t x i j| ≤
      |x i * x j| / (64 * π ^ 2) *
          ((t ^ 4)⁻¹ * exp (-(euclideanDistSq x / 4 / t))) +
        1 / (32 * π ^ 2) *
          ((t ^ 3)⁻¹ * exp (-(euclideanDistSq x / 4 / t))) := by
  have hheat : 0 ≤ euclideanHeatKernel4 t x := by
    unfold euclideanHeatKernel4
    positivity
  rw [euclideanHeatHess, abs_mul, abs_of_nonneg hheat]
  calc
    |x i * x j / (4 * t ^ 2) -
        (if i = j then (2 * t)⁻¹ else 0)| *
          euclideanHeatKernel4 t x
        ≤ (|x i * x j / (4 * t ^ 2)| +
            |if i = j then (2 * t)⁻¹ else 0|) *
          euclideanHeatKernel4 t x := by
            gcongr
            exact abs_sub _ _
    _ ≤ |x i * x j| / (64 * π ^ 2) *
          ((t ^ 4)⁻¹ * exp (-(euclideanDistSq x / 4 / t))) +
        1 / (32 * π ^ 2) *
          ((t ^ 3)⁻¹ * exp (-(euclideanDistSq x / 4 / t))) := by
      rw [euclideanHeatKernel4_eq_timeMajorant ht x]
      by_cases hij : i = j
      · apply le_of_eq
        rw [if_pos hij]
        rw [abs_div, abs_inv, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 4 * t ^ 2),
          abs_of_pos (by positivity : (0 : ℝ) < 2 * t)]
        have ht0 : t ≠ 0 := ne_of_gt ht
        have hpi : π ≠ 0 := Real.pi_ne_zero
        field_simp
        ring
      · rw [if_neg hij, abs_zero, add_zero]
        calc
          |x i * x j / (4 * t ^ 2)| *
                ((16 * π ^ 2)⁻¹ *
                  ((t ^ 2)⁻¹ * exp (-(euclideanDistSq x / 4 / t)))) =
              |x i * x j| / (64 * π ^ 2) *
                ((t ^ 4)⁻¹ * exp (-(euclideanDistSq x / 4 / t))) := by
            rw [abs_div,
              abs_of_pos (by positivity : (0 : ℝ) < 4 * t ^ 2)]
            have ht0 : t ≠ 0 := ne_of_gt ht
            have hpi : π ≠ 0 := Real.pi_ne_zero
            field_simp
            ring
          _ ≤ _ := le_add_of_nonneg_right (by positivity)

theorem integrableOn_euclideanHeatHess {x : R4}
    (hx : euclideanDistSq x ≠ 0) (i j : Fin dim) :
    IntegrableOn (fun t => euclideanHeatHess t x i j) (Ioi (0 : ℝ)) := by
  have hs : 0 < euclideanDistSq x :=
    lt_of_le_of_ne (euclideanDistSq_nonneg x) (Ne.symm hx)
  have ha : 0 < euclideanDistSq x / 4 := by positivity
  have hfourth :
      IntegrableOn
        (fun t => |x i * x j| / (64 * π ^ 2) *
          ((t ^ 4)⁻¹ * exp (-(euclideanDistSq x / 4 / t))))
        (Ioi (0 : ℝ)) :=
    (integrableOn_inv_fourth_exp ha).const_mul _
  have hcube :
      IntegrableOn
        (fun t => 1 / (32 * π ^ 2) *
          ((t ^ 3)⁻¹ * exp (-(euclideanDistSq x / 4 / t))))
        (Ioi (0 : ℝ)) :=
    (integrableOn_inv_cube_exp ha).const_mul _
  apply Integrable.mono' (hfourth.add hcube)
  · apply Measurable.aestronglyMeasurable
    unfold euclideanHeatHess euclideanHeatKernel4 euclideanDistSq
    by_cases hij : i = j
    · simp only [hij, if_true]
      fun_prop
    · simp only [hij, if_false]
      fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht => ?_)
    simpa [Real.norm_eq_abs] using abs_euclideanHeatHess_le ht x i j

theorem integral_abs_euclideanHeatHess_le {x : R4}
    (hx : euclideanDistSq x ≠ 0) (i j : Fin dim) :
    ∫ t in Ioi (0 : ℝ), |euclideanHeatHess t x i j| ≤
      |x i * x j| / (64 * π ^ 2) *
          (2 * (euclideanDistSq x / 4)⁻¹ ^ 3) +
        1 / (32 * π ^ 2) * (euclideanDistSq x / 4)⁻¹ ^ 2 := by
  have hs : 0 < euclideanDistSq x :=
    lt_of_le_of_ne (euclideanDistSq_nonneg x) (Ne.symm hx)
  have ha : 0 < euclideanDistSq x / 4 := by positivity
  have hfourth :
      IntegrableOn
        (fun t => |x i * x j| / (64 * π ^ 2) *
          ((t ^ 4)⁻¹ * exp (-(euclideanDistSq x / 4 / t))))
        (Ioi (0 : ℝ)) :=
    (integrableOn_inv_fourth_exp ha).const_mul _
  have hcube :
      IntegrableOn
        (fun t => 1 / (32 * π ^ 2) *
          ((t ^ 3)⁻¹ * exp (-(euclideanDistSq x / 4 / t))))
        (Ioi (0 : ℝ)) :=
    (integrableOn_inv_cube_exp ha).const_mul _
  calc
    ∫ t in Ioi (0 : ℝ), |euclideanHeatHess t x i j| ≤
        ∫ t in Ioi (0 : ℝ),
          (|x i * x j| / (64 * π ^ 2) *
              ((t ^ 4)⁻¹ * exp (-(euclideanDistSq x / 4 / t))) +
            1 / (32 * π ^ 2) *
              ((t ^ 3)⁻¹ * exp (-(euclideanDistSq x / 4 / t)))) := by
      refine setIntegral_mono_on (integrableOn_euclideanHeatHess hx i j).norm
        (hfourth.add hcube) measurableSet_Ioi fun t ht => ?_
      simpa using abs_euclideanHeatHess_le ht x i j
    _ = |x i * x j| / (64 * π ^ 2) *
          (2 * (euclideanDistSq x / 4)⁻¹ ^ 3) +
        1 / (32 * π ^ 2) * (euclideanDistSq x / 4)⁻¹ ^ 2 := by
      rw [integral_add hfourth hcube, integral_const_mul,
        integral_const_mul, integral_inv_fourth_exp ha,
        integral_inv_cube_exp ha]

private theorem integrableOn_euclideanBesselIntegrand {x : R4}
    (hx : euclideanDistSq x ≠ 0) :
    IntegrableOn (fun t => exp (-t) * euclideanHeatKernel4 t x)
      (Ioi (0 : ℝ)) := by
  apply Integrable.mono' (integrableOn_euclideanHeatKernel4 hx)
  · apply Measurable.aestronglyMeasurable
    unfold euclideanHeatKernel4 euclideanDistSq
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos (-t)),
      abs_of_nonneg (by
        unfold euclideanHeatKernel4
        positivity)]
    have htpos : 0 < t := ht
    have hexp : exp (-t) ≤ 1 := by
      rw [exp_le_one_iff]
      linarith
    exact mul_le_of_le_one_left (by
      unfold euclideanHeatKernel4
      positivity) hexp

private theorem local_euclideanHeatGrad_bound (x : R4) (i k : Fin dim)
    {s t : ℝ} (ht : 0 < t) (hs : |s| < |x k| / 2) :
    |exp (-t) * euclideanHeatGrad t (coordLine x i s) i| ≤
      (|x i| + |x k| / 2) / (32 * π ^ 2) *
        ((t ^ 3)⁻¹ * exp (-((x k) ^ 2 / 16 / t))) := by
  rw [abs_mul, abs_of_pos (exp_pos (-t)),
    abs_euclideanHeatGrad ht (coordLine x i s) i]
  have hδ : 0 ≤ |x k| / 2 := by positivity
  have hcoord :
      |coordLine x i s i| ≤ |x i| + |x k| / 2 :=
    abs_coordLine_apply_le x i i hs.le
  have hdist := euclideanDistSq_coordLine_lower x i k hs
  have hexpTime : exp (-t) ≤ 1 := by
    rw [exp_le_one_iff]
    linarith
  have hexpSpace :
      exp (-(euclideanDistSq (coordLine x i s) / 4 / t)) ≤
        exp (-((x k) ^ 2 / 16 / t)) := by
    apply exp_le_exp.mpr
    rw [neg_le_neg_iff]
    rw [div_le_div_iff₀ ht] <;> nlinarith
  have hpi : 0 < 32 * π ^ 2 := by positivity
  have hconst :
      |coordLine x i s i| / (32 * π ^ 2) ≤
        (|x i| + |x k| / 2) / (32 * π ^ 2) :=
    div_le_div_of_nonneg_right hcoord hpi.le
  calc
    exp (-t) *
        (|coordLine x i s i| / (32 * π ^ 2) *
          ((t ^ 3)⁻¹ *
            exp (-(euclideanDistSq (coordLine x i s) / 4 / t))))
        ≤ 1 * ((|x i| + |x k| / 2) / (32 * π ^ 2) *
          ((t ^ 3)⁻¹ * exp (-((x k) ^ 2 / 16 / t)))) := by
            gcongr
    _ = _ := by ring

/-- The `k = 0` Bessel contribution is genuinely differentiable in every
coordinate away from its singular point, with derivative obtained by
differentiating the heat kernel under the time integral. -/
theorem hasDerivAt_euclideanBessel4_coord {x : R4}
    (hx : euclideanDistSq x ≠ 0) (i : Fin dim) :
    HasDerivAt (fun s => euclideanBessel4 (coordLine x i s))
      (euclideanBesselGrad x i) 0 := by
  obtain ⟨k, hk⟩ := exists_coord_ne_zero hx
  let δ : ℝ := |x k| / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let a : ℝ := (x k) ^ 2 / 16
  have ha : 0 < a := by
    dsimp [a]
    positivity
  let C : ℝ := (|x i| + δ) / (32 * π ^ 2)
  let bound : ℝ → ℝ := fun t =>
    C * ((t ^ 3)⁻¹ * exp (-(a / t)))
  have hboundInt :
      Integrable bound (volume.restrict (Ioi (0 : ℝ))) := by
    change IntegrableOn
      (fun t => C * ((t ^ 3)⁻¹ * exp (-(a / t)))) (Ioi (0 : ℝ))
    exact (integrableOn_inv_cube_exp ha).const_mul C
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun s t => exp (-t) *
      euclideanHeatKernel4 t (coordLine x i s))
    (F' := fun s t => exp (-t) *
      euclideanHeatGrad t (coordLine x i s) i)
    (bound := bound) (s := Ioo (-δ) δ) (x₀ := (0 : ℝ))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun s => by
      apply Measurable.aestronglyMeasurable
      unfold euclideanHeatKernel4 euclideanDistSq coordLine
      fun_prop)
    (by
      change IntegrableOn
        (fun t => exp (-t) * euclideanHeatKernel4 t (coordLine x i 0))
        (Ioi (0 : ℝ))
      simpa only [coordLine_zero] using
        integrableOn_euclideanBesselIntegrand hx)
    (by
      apply Measurable.aestronglyMeasurable
      unfold euclideanHeatGrad euclideanHeatKernel4 euclideanDistSq coordLine
      fun_prop)
    (by
      refine (ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun t ht s hs => ?_)
      have habs : |s| < δ := abs_lt.mpr hs
      change |exp (-t) * euclideanHeatGrad t (coordLine x i s) i| ≤ bound t
      simpa only [bound, C, a, δ] using
        local_euclideanHeatGrad_bound x i k ht habs)
    hboundInt
    (by
      refine (ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun t ht s _ => ?_)
      exact (hasDerivAt_euclideanHeatKernel4_coord_at ht.ne' x i s).const_mul
        (exp (-t)))
  simpa only [euclideanBessel4, euclideanBesselGrad, coordLine_zero] using hmain.2

private theorem integrableOn_euclideanBesselGradIntegrand {x : R4}
    (hx : euclideanDistSq x ≠ 0) (i : Fin dim) :
    IntegrableOn (fun t => exp (-t) * euclideanHeatGrad t x i)
      (Ioi (0 : ℝ)) := by
  apply Integrable.mono (integrableOn_euclideanHeatGrad hx i)
  · apply Measurable.aestronglyMeasurable
    unfold euclideanHeatGrad euclideanHeatKernel4 euclideanDistSq
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos (-t))]
    have htpos : 0 < t := ht
    have hexp : exp (-t) ≤ 1 := by
      rw [exp_le_one_iff]
      linarith
    exact mul_le_of_le_one_left (abs_nonneg _) hexp

/-- Explicit `|x|⁻³`-scale bound for each coordinate derivative of the
local Bessel contribution.  The anisotropic numerator is useful in the
later Taylor contraction and is exactly the time-integrated Gaussian
bound. -/
theorem abs_euclideanBesselGrad_le {x : R4}
    (hx : euclideanDistSq x ≠ 0) (i : Fin dim) :
    |euclideanBesselGrad x i| ≤
      |x i| / (2 * π ^ 2) * (euclideanDistSq x)⁻¹ ^ 2 := by
  calc
    |euclideanBesselGrad x i| ≤
        ∫ t in Ioi (0 : ℝ),
          |exp (-t) * euclideanHeatGrad t x i| := by
      unfold euclideanBesselGrad
      simpa [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (μ := volume.restrict (Ioi (0 : ℝ)))
          (fun t => exp (-t) * euclideanHeatGrad t x i))
    _ ≤ ∫ t in Ioi (0 : ℝ), |euclideanHeatGrad t x i| := by
      refine setIntegral_mono_on
        (integrableOn_euclideanBesselGradIntegrand hx i).norm
        (integrableOn_euclideanHeatGrad hx i).norm measurableSet_Ioi
        fun t ht => ?_
      rw [abs_mul, abs_of_pos (exp_pos (-t))]
      have htpos : 0 < t := ht
      have hexp : exp (-t) ≤ 1 := by
        rw [exp_le_one_iff]
        linarith
      exact mul_le_of_le_one_left (abs_nonneg _) hexp
    _ = _ := integral_abs_euclideanHeatGrad hx i

private theorem local_euclideanHeatHess_bound (x : R4) (i j k : Fin dim)
    {s t : ℝ} (ht : 0 < t) (hs : |s| < |x k| / 2) :
    |exp (-t) * euclideanHeatHess t (coordLine x j s) i j| ≤
      ((|x i| + |x k| / 2) * (|x j| + |x k| / 2)) /
          (64 * π ^ 2) *
        ((t ^ 4)⁻¹ * exp (-((x k) ^ 2 / 16 / t))) +
      1 / (32 * π ^ 2) *
        ((t ^ 3)⁻¹ * exp (-((x k) ^ 2 / 16 / t))) := by
  rw [abs_mul, abs_of_pos (exp_pos (-t))]
  have hi :
      |coordLine x j s i| ≤ |x i| + |x k| / 2 :=
    abs_coordLine_apply_le x j i hs.le
  have hj :
      |coordLine x j s j| ≤ |x j| + |x k| / 2 :=
    abs_coordLine_apply_le x j j hs.le
  have hproduct :
      |coordLine x j s i * coordLine x j s j| ≤
        (|x i| + |x k| / 2) * (|x j| + |x k| / 2) := by
    rw [abs_mul]
    exact mul_le_mul hi hj (abs_nonneg _) (by positivity)
  have hdist := euclideanDistSq_coordLine_lower x j k hs
  have hexpTime : exp (-t) ≤ 1 := by
    rw [exp_le_one_iff]
    linarith
  have hexpSpace :
      exp (-(euclideanDistSq (coordLine x j s) / 4 / t)) ≤
        exp (-((x k) ^ 2 / 16 / t)) := by
    apply exp_le_exp.mpr
    rw [neg_le_neg_iff]
    rw [div_le_div_iff₀ ht] <;> nlinarith
  calc
    exp (-t) * |euclideanHeatHess t (coordLine x j s) i j| ≤
        1 * (|coordLine x j s i * coordLine x j s j| /
            (64 * π ^ 2) *
              ((t ^ 4)⁻¹ *
                exp (-(euclideanDistSq (coordLine x j s) / 4 / t))) +
          1 / (32 * π ^ 2) *
              ((t ^ 3)⁻¹ *
                exp (-(euclideanDistSq (coordLine x j s) / 4 / t)))) := by
      gcongr
      exact abs_euclideanHeatHess_le ht (coordLine x j s) i j
    _ ≤ 1 * (((|x i| + |x k| / 2) * (|x j| + |x k| / 2)) /
            (64 * π ^ 2) *
              ((t ^ 4)⁻¹ * exp (-((x k) ^ 2 / 16 / t))) +
          1 / (32 * π ^ 2) *
              ((t ^ 3)⁻¹ * exp (-((x k) ^ 2 / 16 / t)))) := by
      gcongr
    _ = _ := by ring

/-- The time-integrated first derivative is itself differentiable away
from the singularity; its coordinate derivative is the time-integrated
Hessian.  This is the genuine `k = 2` local Bessel part of (4.1). -/
theorem hasDerivAt_euclideanBesselGrad_coord {x : R4}
    (hx : euclideanDistSq x ≠ 0) (i j : Fin dim) :
    HasDerivAt (fun s => euclideanBesselGrad (coordLine x j s) i)
      (euclideanBesselHess x i j) 0 := by
  obtain ⟨k, hk⟩ := exists_coord_ne_zero hx
  let δ : ℝ := |x k| / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let a : ℝ := (x k) ^ 2 / 16
  have ha : 0 < a := by
    dsimp [a]
    positivity
  let C₄ : ℝ := ((|x i| + δ) * (|x j| + δ)) / (64 * π ^ 2)
  let C₃ : ℝ := 1 / (32 * π ^ 2)
  let bound : ℝ → ℝ := fun t =>
    C₄ * ((t ^ 4)⁻¹ * exp (-(a / t))) +
      C₃ * ((t ^ 3)⁻¹ * exp (-(a / t)))
  have hboundInt :
      Integrable bound (volume.restrict (Ioi (0 : ℝ))) := by
    change IntegrableOn
      (fun t => C₄ * ((t ^ 4)⁻¹ * exp (-(a / t))) +
        C₃ * ((t ^ 3)⁻¹ * exp (-(a / t)))) (Ioi (0 : ℝ))
    exact ((integrableOn_inv_fourth_exp ha).const_mul C₄).add
      ((integrableOn_inv_cube_exp ha).const_mul C₃)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun s t => exp (-t) *
      euclideanHeatGrad t (coordLine x j s) i)
    (F' := fun s t => exp (-t) *
      euclideanHeatHess t (coordLine x j s) i j)
    (bound := bound) (s := Ioo (-δ) δ) (x₀ := (0 : ℝ))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun s => by
      apply Measurable.aestronglyMeasurable
      unfold euclideanHeatGrad euclideanHeatKernel4 euclideanDistSq coordLine
      fun_prop)
    (by
      change IntegrableOn
        (fun t => exp (-t) *
          euclideanHeatGrad t (coordLine x j 0) i) (Ioi (0 : ℝ))
      simpa only [coordLine_zero] using
        integrableOn_euclideanBesselGradIntegrand hx i)
    (by
      apply Measurable.aestronglyMeasurable
      unfold euclideanHeatHess euclideanHeatKernel4 euclideanDistSq coordLine
      by_cases hij : i = j
      · simp only [hij, if_true]
        fun_prop
      · simp only [hij, if_false]
        fun_prop)
    (by
      refine (ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun t ht s hs => ?_)
      have habs : |s| < δ := abs_lt.mpr hs
      change |exp (-t) *
        euclideanHeatHess t (coordLine x j s) i j| ≤ bound t
      simpa only [bound, C₄, C₃, a, δ] using
        local_euclideanHeatHess_bound x i j k ht habs)
    hboundInt
    (by
      refine (ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun t ht s _ => ?_)
      exact (hasDerivAt_euclideanHeatGrad_coord_at ht.ne' x i j s).const_mul
        (exp (-t)))
  simpa only [euclideanBesselGrad, euclideanBesselHess, coordLine_zero] using hmain.2

private theorem integrableOn_euclideanBesselHessIntegrand {x : R4}
    (hx : euclideanDistSq x ≠ 0) (i j : Fin dim) :
    IntegrableOn (fun t => exp (-t) * euclideanHeatHess t x i j)
      (Ioi (0 : ℝ)) := by
  apply Integrable.mono (integrableOn_euclideanHeatHess hx i j)
  · apply Measurable.aestronglyMeasurable
    unfold euclideanHeatHess euclideanHeatKernel4 euclideanDistSq
    by_cases hij : i = j
    · simp only [hij, if_true]
      fun_prop
    · simp only [hij, if_false]
      fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos (-t))]
    have htpos : 0 < t := ht
    have hexp : exp (-t) ≤ 1 := by
      rw [exp_le_one_iff]
      linarith
    exact mul_le_of_le_one_left (abs_nonneg _) hexp

/-- Explicit `|x|⁻⁴`-scale anisotropic majorant for every Hessian entry
of the local Bessel contribution. -/
theorem abs_euclideanBesselHess_le {x : R4}
    (hx : euclideanDistSq x ≠ 0) (i j : Fin dim) :
    |euclideanBesselHess x i j| ≤
      |x i * x j| / (64 * π ^ 2) *
          (2 * (euclideanDistSq x / 4)⁻¹ ^ 3) +
        1 / (32 * π ^ 2) * (euclideanDistSq x / 4)⁻¹ ^ 2 := by
  calc
    |euclideanBesselHess x i j| ≤
        ∫ t in Ioi (0 : ℝ),
          |exp (-t) * euclideanHeatHess t x i j| := by
      unfold euclideanBesselHess
      simpa [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (μ := volume.restrict (Ioi (0 : ℝ)))
          (fun t => exp (-t) * euclideanHeatHess t x i j))
    _ ≤ ∫ t in Ioi (0 : ℝ), |euclideanHeatHess t x i j| := by
      refine setIntegral_mono_on
        (integrableOn_euclideanBesselHessIntegrand hx i j).norm
        (integrableOn_euclideanHeatHess hx i j).norm measurableSet_Ioi
        fun t ht => ?_
      rw [abs_mul, abs_of_pos (exp_pos (-t))]
      have htpos : 0 < t := ht
      have hexp : exp (-t) ≤ 1 := by
        rw [exp_le_one_iff]
        linarith
      exact mul_le_of_le_one_left (abs_nonneg _) hexp
    _ ≤ _ := integral_abs_euclideanHeatHess_le hx i j

end

end Anderson4D
