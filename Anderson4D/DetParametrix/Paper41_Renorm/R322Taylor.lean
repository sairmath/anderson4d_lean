import Anderson4D.Continuum.GreenTaylor
import Anderson4D.DetParametrix.Core.ReductionSymmetry
import Mathlib.Algebra.Order.Chebyshev

/-!
# The Taylor-cancellation input for R-322

This file connects the local Green Taylor theorem to the actual torus
difference in paper (4.9).  A compatible-lift hypothesis records the
geometric fact that the short displacement does not wrap in the chosen
chart.  Under the chart-safety and radius hypotheses proved by the local
region decomposition, the *defined* remainder is bounded by
`C |u|² r⁻⁴`.  The linear part is a genuine continuous linear functional,
so `ReductionSymmetry.taylor_cancellation_bound` can remove it for every
kernel in the paper's class `E`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Real Set

/-- The gradient at a local lift, bundled as a continuous linear
functional on `ℝ⁴`. -/
def greenGradientCLM (x : R4) : R4 →L[ℝ] ℝ :=
  ∑ i : Fin dim,
    greenLocalGrad x i • ContinuousLinearMap.proj i

@[simp]
theorem greenGradientCLM_apply (x h : R4) :
    greenGradientCLM x h = ∑ i, greenLocalGrad x i * h i := by
  simp [greenGradientCLM]

/-- Cauchy--Schwarz in the fixed four-dimensional coordinate chart. -/
theorem coordinateL1Dist_sq_le_four_euclideanDistSq
    (a b : R4) :
    coordinateL1Dist a b ^ 2 ≤
      4 * euclideanDistSq (b - a) := by
  have h :=
    sq_sum_le_card_mul_sum_sq
      (s := Finset.univ)
      (f := fun i : Fin dim => |b i - a i|)
  simpa [coordinateL1Dist, euclideanDistSq, sq_abs] using h

/-! ## Concatenating Taylor estimates across a periodic seam -/

private theorem abs_concat_taylor_le
    {fa fc fd fb ga gd p q M : ℝ}
    (hM : 0 ≤ M) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hvalue : fc = fd)
    (hfirst : |fc - fa - ga * p| ≤ M * p ^ 2)
    (hsecond : |fb - fd - gd * q| ≤ M * q ^ 2)
    (hgrad : |gd - ga| ≤ M * p) :
    |fb - fa - ga * (p + q)| ≤ M * (p + q) ^ 2 := by
  have hdecomp :
      fb - fa - ga * (p + q) =
        (fb - fd - gd * q) +
          (fc - fa - ga * p) +
          (gd - ga) * q := by
    rw [hvalue]
    ring
  rw [hdecomp]
  calc
    |(fb - fd - gd * q) + (fc - fa - ga * p) +
        (gd - ga) * q| ≤
        |fb - fd - gd * q| +
          |fc - fa - ga * p| +
          |(gd - ga) * q| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ M * q ^ 2 + M * p ^ 2 + (M * p) * q := by
      rw [abs_mul, abs_of_nonneg hq]
      exact add_le_add (add_le_add hsecond hfirst)
        (mul_le_mul_of_nonneg_right hgrad hq)
    _ ≤ M * (p + q) ^ 2 := by
      nlinarith [mul_nonneg hp hq]

private theorem abs_concat_reverse_taylor_le
    {fa fc fd fb ga gd p q M : ℝ}
    (hM : 0 ≤ M) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hvalue : fc = fd)
    (hfirst : |fc - fa - ga * (-p)| ≤ (2 * M) * p ^ 2)
    (hsecond : |fb - fd - gd * (-q)| ≤ (2 * M) * q ^ 2)
    (hgrad : |gd - ga| ≤ M * p) :
    |fb - fa - ga * (-(p + q))| ≤
      (2 * M) * (p + q) ^ 2 := by
  have hdecomp :
      fb - fa - ga * (-(p + q)) =
        (fb - fd - gd * (-q)) +
          (fc - fa - ga * (-p)) -
          (gd - ga) * q := by
    rw [hvalue]
    ring
  rw [hdecomp]
  calc
    |(fb - fd - gd * (-q)) + (fc - fa - ga * (-p)) -
        (gd - ga) * q| ≤
        |fb - fd - gd * (-q)| +
          |fc - fa - ga * (-p)| +
          |(gd - ga) * q| := by
      rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _)
          (by rw [abs_neg]))
    _ ≤ (2 * M) * q ^ 2 + (2 * M) * p ^ 2 +
        (M * p) * q := by
      rw [abs_mul, abs_of_nonneg hq]
      exact add_le_add (add_le_add hsecond hfirst)
        (mul_le_mul_of_nonneg_right hgrad hq)
    _ ≤ (2 * M) * (p + q) ^ 2 := by
      nlinarith [mul_nonneg hp hq, mul_nonneg hM hp,
        mul_nonneg hM hq]

private theorem inClosedPrincipalCube_coordLine_of_bounds
    {x : R4} (hx : InClosedPrincipalCube x)
    (j : Fin dim) {t : ℝ}
    (hlower : -π ≤ x j + t) (hupper : x j + t ≤ π) :
    InClosedPrincipalCube (coordLine x j t) := by
  intro i
  by_cases hij : i = j
  · subst i
    rw [abs_le]
    simpa [coordLine] using And.intro hlower hupper
  · simpa [coordLine, hij] using hx i

private theorem coordLine_sub_period_eq_addPeriod
    (x : R4) (j : Fin dim) :
    coordLine x j (-2 * π) =
      x + realPeriodShift (Pi.single j (-1)) := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [coordLine, realPeriodShift]
  · simp [coordLine, realPeriodShift, hij]

private theorem coordLine_add_period_eq_addPeriod
    (x : R4) (j : Fin dim) :
    coordLine x j (2 * π) =
      x + realPeriodShift (Pi.single j 1) := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [coordLine, realPeriodShift]
  · simp [coordLine, realPeriodShift, hij]

/-- One-coordinate Taylor estimate when a positive displacement crosses
the upper face of the principal cell. -/
theorem greenLocalLift_coord_taylor_upper_wrap
    {x : R4} (j : Fin dim) {h r : ℝ}
    (hx : InClosedPrincipalCube x)
    (hxj : x j < π)
    (hwrap : π < x j + h)
    (hhpi : h ≤ π) (hr : 0 < r)
    (hradius₁ : ∀ t ∈ Icc 0 (π - x j),
      r ≤ √(euclideanDistSq (coordLine x j t)))
    (hradius₂ : ∀ t ∈ Icc (π - x j) h,
      r ≤ √(euclideanDistSq
        (coordLine (coordLine x j (-2 * π)) j t))) :
    |greenLocalLift (coordLine x j h) - greenLocalLift x -
        greenLocalGrad x j * h| ≤
      (greenLocalHessSingularBound * r⁻¹ ^ 4) * h ^ 2 := by
  let p : ℝ := π - x j
  let q : ℝ := x j + h - π
  let x₂ : R4 := coordLine x j (-2 * π)
  let M : ℝ := greenLocalHessSingularBound * r⁻¹ ^ 4
  have hp : 0 < p := by
    dsimp only [p]
    linarith
  have hp_le : p ≤ h := by
    dsimp only [p]
    linarith
  have hp_lt_h : p < h := by
    dsimp only [p]
    linarith
  have hq : 0 < q := by
    dsimp only [q]
    linarith
  have hpq : p + q = h := by
    dsimp only [p, q]
    ring
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg greenLocalHessSingularBound_nonneg
      (pow_nonneg (inv_nonneg.mpr hr.le) _)
  have hclosed₁ :
      ∀ t ∈ Icc 0 p,
        InClosedPrincipalCube (coordLine x j t) := by
    intro t ht
    apply inClosedPrincipalCube_coordLine_of_bounds hx j
    · have hxlower := (abs_le.mp (hx j)).1
      linarith [ht.1]
    · dsimp only [p] at ht
      linarith [ht.2]
  have hcoord₁ :
      ∀ t ∈ Ioo 0 p,
        |coordLine x j t j| < π := by
    intro t ht
    rw [abs_lt]
    simp only [coordLine, Pi.add_apply, Pi.smul_apply,
      Pi.single_eq_same, smul_eq_mul, mul_one]
    have hxlower := (abs_le.mp (hx j)).1
    dsimp only [p] at ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hx₂coord :
      ∀ t : ℝ, coordLine x₂ j t j =
        x j - 2 * π + t := by
    intro t
    simp [x₂, coordLine]
    ring
  have hclosed₂ :
      ∀ t ∈ Icc p h,
        InClosedPrincipalCube (coordLine x₂ j t) := by
    intro t ht i
    by_cases hij : i = j
    · subst i
      rw [abs_le, hx₂coord]
      dsimp only [p] at ht
      constructor
      · linarith [ht.1]
      · linarith [ht.2, hhpi, hxj]
    · have hi := hx i
      simpa [x₂, coordLine, hij] using hi
  have hcoord₂ :
      ∀ t ∈ Ioo p h,
        |coordLine x₂ j t j| < π := by
    intro t ht
    rw [abs_lt, hx₂coord]
    dsimp only [p] at ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2, hhpi, hxj]
  have hfirst :=
    greenLocalLift_coord_taylor_closed_interval_of_radius
      (x := x) j hp hr hclosed₁ hcoord₁
      (by simpa only [p] using hradius₁)
  have hsecond :=
    greenLocalLift_coord_taylor_closed_interval_of_radius
      (x := x₂) j hp_lt_h hr hclosed₂ hcoord₂
      (by simpa only [x₂, p] using hradius₂)
  have hgrad₁ :=
    greenLocalGrad_coord_lipschitz_closed_interval_of_radius
      (x := x) j j hp hr hclosed₁ hcoord₁
      (by simpa only [p] using hradius₁)
  have hlowerClosed :
      InClosedPrincipalCube (coordLine x₂ j p) :=
    hclosed₂ p (left_mem_Icc.mpr hp_le)
  have hlowerCoord :
      coordLine x₂ j p j = -π := by
    rw [hx₂coord]
    dsimp only [p]
    ring
  have hseamPoint :
      coordLine (coordLine x₂ j p) j (2 * π) =
        coordLine x j p := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [x₂, coordLine]
      ring
    · simp [x₂, coordLine, hij]
  have hvalue :
      greenLocalLift (coordLine x j p) =
        greenLocalLift (coordLine x₂ j p) := by
    rw [← hseamPoint, coordLine_add_period_eq_addPeriod,
      greenLocalLift_add_period]
  have hgradSeam :
      greenLocalGrad (coordLine x₂ j p) j =
        greenLocalGrad (coordLine x j p) j := by
    symm
    rw [← hseamPoint]
    exact greenLocalGrad_lower_upper_boundary
      hlowerClosed j j hlowerCoord
  have hendPoint :
      coordLine x₂ j h =
        coordLine x j h +
          realPeriodShift (Pi.single j (-1)) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [x₂, coordLine, realPeriodShift]
      ring
    · simp [x₂, coordLine, realPeriodShift, hij]
  have hendValue :
      greenLocalLift (coordLine x₂ j h) =
        greenLocalLift (coordLine x j h) := by
    rw [hendPoint, greenLocalLift_add_period]
  have hfirst' :
      |greenLocalLift (coordLine x j p) -
          greenLocalLift x -
          greenLocalGrad x j * p| ≤ M * p ^ 2 := by
    simpa [M, coordLine] using hfirst
  have hsecond' :
      |greenLocalLift (coordLine x₂ j h) -
          greenLocalLift (coordLine x₂ j p) -
          greenLocalGrad (coordLine x₂ j p) j * q| ≤
        M * q ^ 2 := by
    have hlen : h - p = q := by
      dsimp only [p, q]
      ring
    simpa only [M, hlen] using hsecond
  have hgrad' :
      |greenLocalGrad (coordLine x₂ j p) j -
          greenLocalGrad x j| ≤ M * p := by
    rw [hgradSeam]
    simpa [M, coordLine] using hgrad₁
  have hconcat :=
    abs_concat_taylor_le hM hp.le hq.le hvalue
      hfirst' hsecond' hgrad'
  rw [hpq] at hconcat
  simpa only [hendValue, M] using hconcat

/-- One-coordinate Taylor estimate when a negative displacement crosses
the lower face of the principal cell. -/
theorem greenLocalLift_coord_taylor_lower_wrap
    {x : R4} (j : Fin dim) {h r : ℝ}
    (hx : InClosedPrincipalCube x)
    (hxj : -π < x j)
    (hwrap : x j + h < -π)
    (hhpi : -π ≤ h) (hr : 0 < r)
    (hradius₁ : ∀ t ∈ Icc (-π - x j) 0,
      r ≤ √(euclideanDistSq (coordLine x j t)))
    (hradius₂ : ∀ t ∈ Icc h (-π - x j),
      r ≤ √(euclideanDistSq
        (coordLine (coordLine x j (2 * π)) j t))) :
    |greenLocalLift (coordLine x j h) - greenLocalLift x -
        greenLocalGrad x j * h| ≤
      (2 * (greenLocalHessSingularBound * r⁻¹ ^ 4)) *
        h ^ 2 := by
  let p : ℝ := x j + π
  let q : ℝ := -π - (x j + h)
  let c : ℝ := -π - x j
  let x₂ : R4 := coordLine x j (2 * π)
  let M : ℝ := greenLocalHessSingularBound * r⁻¹ ^ 4
  have hp : 0 < p := by
    dsimp only [p]
    linarith
  have hq : 0 < q := by
    dsimp only [q]
    linarith
  have hc : c < 0 := by
    dsimp only [c]
    linarith
  have hh_lt_c : h < c := by
    dsimp only [c]
    linarith
  have hc_eq : c = -p := by
    dsimp only [c, p]
    ring
  have hpq : p + q = -h := by
    dsimp only [p, q]
    ring
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg greenLocalHessSingularBound_nonneg
      (pow_nonneg (inv_nonneg.mpr hr.le) _)
  have hclosed₁ :
      ∀ t ∈ Icc c 0,
        InClosedPrincipalCube (coordLine x j t) := by
    intro t ht
    apply inClosedPrincipalCube_coordLine_of_bounds hx j
    · dsimp only [c] at ht
      linarith [ht.1]
    · have hxupper := (abs_le.mp (hx j)).2
      linarith [ht.2]
  have hcoord₁ :
      ∀ t ∈ Ioo c 0,
        |coordLine x j t j| < π := by
    intro t ht
    rw [abs_lt]
    simp only [coordLine, Pi.add_apply, Pi.smul_apply,
      Pi.single_eq_same, smul_eq_mul, mul_one]
    have hxupper := (abs_le.mp (hx j)).2
    dsimp only [c] at ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hx₂coord :
      ∀ t : ℝ, coordLine x₂ j t j =
        x j + 2 * π + t := by
    intro t
    simp [x₂, coordLine]
  have hclosed₂ :
      ∀ t ∈ Icc h c,
        InClosedPrincipalCube (coordLine x₂ j t) := by
    intro t ht i
    by_cases hij : i = j
    · subst i
      rw [abs_le, hx₂coord]
      dsimp only [c] at ht
      constructor
      · linarith [ht.1, hhpi, hxj]
      · linarith [ht.2]
    · have hi := hx i
      simpa [x₂, coordLine, hij] using hi
  have hcoord₂ :
      ∀ t ∈ Ioo h c,
        |coordLine x₂ j t j| < π := by
    intro t ht
    rw [abs_lt, hx₂coord]
    dsimp only [c] at ht
    constructor
    · linarith [ht.1, hhpi, hxj]
    · linarith [ht.2]
  have hfirst :=
    greenLocalLift_coord_taylor_closed_interval_rev_of_radius
      (x := x) j hc hr hclosed₁ hcoord₁
      (by simpa only [c] using hradius₁)
  have hsecond :=
    greenLocalLift_coord_taylor_closed_interval_rev_of_radius
      (x := x₂) j hh_lt_c hr hclosed₂ hcoord₂
      (by simpa only [x₂, c] using hradius₂)
  have hgrad₁ :=
    greenLocalGrad_coord_lipschitz_closed_interval_of_radius
      (x := x) j j hc hr hclosed₁ hcoord₁
      (by simpa only [c] using hradius₁)
  have hlowerClosed :
      InClosedPrincipalCube (coordLine x j c) :=
    hclosed₁ c (left_mem_Icc.mpr hc.le)
  have hlowerCoord :
      coordLine x j c j = -π := by
    simp only [coordLine, Pi.add_apply, Pi.smul_apply,
      Pi.single_eq_same, smul_eq_mul, mul_one]
    dsimp only [c]
    ring
  have hseamPoint :
      coordLine (coordLine x j c) j (2 * π) =
        coordLine x₂ j c := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [x₂, coordLine]
      ring
    · simp [x₂, coordLine, hij]
  have hvalue :
      greenLocalLift (coordLine x j c) =
        greenLocalLift (coordLine x₂ j c) := by
    rw [← hseamPoint, coordLine_add_period_eq_addPeriod,
      greenLocalLift_add_period]
  have hgradSeam :
      greenLocalGrad (coordLine x₂ j c) j =
        greenLocalGrad (coordLine x j c) j := by
    rw [← hseamPoint]
    exact greenLocalGrad_lower_upper_boundary
      hlowerClosed j j hlowerCoord
  have hendPoint :
      coordLine x₂ j h =
        coordLine x j h +
          realPeriodShift (Pi.single j 1) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [x₂, coordLine, realPeriodShift]
      ring
    · simp [x₂, coordLine, realPeriodShift, hij]
  have hendValue :
      greenLocalLift (coordLine x₂ j h) =
        greenLocalLift (coordLine x j h) := by
    rw [hendPoint, greenLocalLift_add_period]
  have hfirst' :
      |greenLocalLift (coordLine x j c) -
          greenLocalLift x -
          greenLocalGrad x j * (-p)| ≤
        (2 * M) * p ^ 2 := by
    have hlen : 0 - c = p := by
      rw [hc_eq]
      ring
    have hstep : c - 0 = -p := by
      rw [hc_eq]
      ring
    simpa [M, coordLine, hlen, hstep] using hfirst
  have hsecond' :
      |greenLocalLift (coordLine x₂ j h) -
          greenLocalLift (coordLine x₂ j c) -
          greenLocalGrad (coordLine x₂ j c) j * (-q)| ≤
        (2 * M) * q ^ 2 := by
    have hlen : c - h = q := by
      dsimp only [c, q]
      ring
    have hstep : h - c = -q := by
      dsimp only [c, q]
      ring
    simpa only [M, hlen, hstep] using hsecond
  have hgrad' :
      |greenLocalGrad (coordLine x₂ j c) j -
          greenLocalGrad x j| ≤ M * p := by
    rw [hgradSeam]
    have hlen : 0 - c = p := by
      rw [hc_eq]
      ring
    rw [abs_sub_comm]
    simpa [M, coordLine, hlen] using hgrad₁
  have hconcat :=
    abs_concat_reverse_taylor_le hM hp.le hq.le hvalue
      hfirst' hsecond' hgrad'
  have hneg : -(p + q) = h := by rw [hpq]; ring
  rw [hneg] at hconcat
  have hsq : (p + q) ^ 2 = h ^ 2 := by rw [hpq]; ring
  rw [hsq] at hconcat
  simpa only [hendValue, M] using hconcat

/-- One-coordinate Taylor estimate when the whole displacement remains in
the chosen closed principal cell. -/
theorem greenLocalLift_coord_taylor_no_wrap
    {x : R4} (j : Fin dim) {h r : ℝ}
    (hx : InClosedPrincipalCube x)
    (hlower : -π ≤ x j + h)
    (hupper : x j + h ≤ π)
    (hr : 0 < r)
    (hradius : ∀ t ∈ uIcc 0 h,
      r ≤ √(torusDistSq
        (greenLocalPoint (coordLine x j t)))) :
    |greenLocalLift (coordLine x j h) - greenLocalLift x -
        greenLocalGrad x j * h| ≤
      (2 * (greenLocalHessSingularBound * r⁻¹ ^ 4)) *
        h ^ 2 := by
  let M : ℝ := greenLocalHessSingularBound * r⁻¹ ^ 4
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg greenLocalHessSingularBound_nonneg
      (pow_nonneg (inv_nonneg.mpr hr.le) _)
  by_cases hz : h = 0
  · subst h
    simp [coordLine]
  by_cases hpos : 0 < h
  · have hclosed :
        ∀ t ∈ Icc 0 h,
          InClosedPrincipalCube (coordLine x j t) := by
      intro t ht
      apply inClosedPrincipalCube_coordLine_of_bounds hx j
      · have hxlower := (abs_le.mp (hx j)).1
        linarith [ht.1]
      · linarith [ht.2, hupper]
    have hcoord :
        ∀ t ∈ Ioo 0 h,
          |coordLine x j t j| < π := by
      intro t ht
      rw [abs_lt]
      simp only [coordLine, Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_same, smul_eq_mul, mul_one]
      have hxlower := (abs_le.mp (hx j)).1
      constructor
      · linarith [ht.1]
      · linarith [ht.2, hupper]
    have hradius' :
        ∀ t ∈ Icc 0 h,
          r ≤ √(euclideanDistSq (coordLine x j t)) := by
      intro t ht
      rw [← torusDistSq_greenLocalPoint_of_closed
        (hclosed t ht)]
      exact hradius t (by
        rw [uIcc_of_le hpos.le]
        exact ht)
    have htaylor :=
      greenLocalLift_coord_taylor_closed_interval_of_radius
        (x := x) j hpos hr hclosed hcoord hradius'
    have hbase :
        |greenLocalLift (coordLine x j h) - greenLocalLift x -
            greenLocalGrad x j * h| ≤ M * h ^ 2 := by
      simpa [M, coordLine] using htaylor
    exact hbase.trans (by
      have hsq : 0 ≤ h ^ 2 := sq_nonneg h
      nlinarith)
  · have hneg : h < 0 := lt_of_le_of_ne
      (le_of_not_gt hpos) hz
    have hclosed :
        ∀ t ∈ Icc h 0,
          InClosedPrincipalCube (coordLine x j t) := by
      intro t ht
      apply inClosedPrincipalCube_coordLine_of_bounds hx j
      · linarith [ht.1, hlower]
      · have hxupper := (abs_le.mp (hx j)).2
        linarith [ht.2]
    have hcoord :
        ∀ t ∈ Ioo h 0,
          |coordLine x j t j| < π := by
      intro t ht
      rw [abs_lt]
      simp only [coordLine, Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_same, smul_eq_mul, mul_one]
      have hxupper := (abs_le.mp (hx j)).2
      constructor
      · linarith [ht.1, hlower]
      · linarith [ht.2]
    have hradius' :
        ∀ t ∈ Icc h 0,
          r ≤ √(euclideanDistSq (coordLine x j t)) := by
      intro t ht
      rw [← torusDistSq_greenLocalPoint_of_closed
        (hclosed t ht)]
      exact hradius t (by
        rw [uIcc_of_ge hneg.le]
        exact ht)
    have htaylor :=
      greenLocalLift_coord_taylor_closed_interval_rev_of_radius
        (x := x) j hneg hr hclosed hcoord hradius'
    simpa [M, coordLine] using htaylor

/-- The lower-wrap estimate when the canonical starting coordinate is
exactly the half-open-cell boundary `-π`. -/
theorem greenLocalLift_coord_taylor_from_lower_boundary
    {x : R4} (j : Fin dim) {h r : ℝ}
    (hx : InClosedPrincipalCube x)
    (hxj : x j = -π)
    (hneg : h < 0) (hhpi : -π ≤ h) (hr : 0 < r)
    (hradius : ∀ t ∈ uIcc 0 h,
      r ≤ √(torusDistSq
        (greenLocalPoint (coordLine x j t)))) :
    |greenLocalLift (coordLine x j h) - greenLocalLift x -
        greenLocalGrad x j * h| ≤
      (2 * (greenLocalHessSingularBound * r⁻¹ ^ 4)) *
        h ^ 2 := by
  let x₂ : R4 := coordLine x j (2 * π)
  have hx₂coord :
      ∀ t : ℝ, coordLine x₂ j t j = π + t := by
    intro t
    simp [x₂, coordLine, hxj]
    ring
  have hclosed :
      ∀ t ∈ Icc h 0,
        InClosedPrincipalCube (coordLine x₂ j t) := by
    intro t ht i
    by_cases hij : i = j
    · subst i
      rw [abs_le, hx₂coord]
      constructor
      · linarith [ht.1, hhpi, Real.pi_pos]
      · linarith [ht.2]
    · have hi := hx i
      simpa [x₂, coordLine, hij] using hi
  have hcoord :
      ∀ t ∈ Ioo h 0,
        |coordLine x₂ j t j| < π := by
    intro t ht
    rw [abs_lt, hx₂coord]
    constructor
    · linarith [ht.1, hhpi, Real.pi_pos]
    · linarith [ht.2]
  have hpoint :
      ∀ t : ℝ,
        coordLine x₂ j t =
          coordLine x j t +
            realPeriodShift (Pi.single j 1) := by
    intro t
    funext i
    by_cases hij : i = j
    · subst i
      simp [x₂, coordLine, realPeriodShift]
      ring
    · simp [x₂, coordLine, realPeriodShift, hij]
  have hradius' :
      ∀ t ∈ Icc h 0,
        r ≤ √(euclideanDistSq (coordLine x₂ j t)) := by
    intro t ht
    rw [← torusDistSq_greenLocalPoint_of_closed
      (hclosed t ht)]
    rw [hpoint, greenLocalPoint_add_period]
    exact hradius t (by
      rw [uIcc_of_ge hneg.le]
      exact ht)
  have htaylor :=
    greenLocalLift_coord_taylor_closed_interval_rev_of_radius
      (x := x₂) j hneg hr hclosed hcoord hradius'
  have hbaseValue :
      greenLocalLift x₂ = greenLocalLift x := by
    rw [show x₂ = x + realPeriodShift (Pi.single j 1) by
      exact coordLine_add_period_eq_addPeriod x j,
      greenLocalLift_add_period]
  have hbaseGrad :
      greenLocalGrad x₂ j = greenLocalGrad x j := by
    rw [show x₂ = coordLine x j (2 * π) by rfl]
    exact greenLocalGrad_lower_upper_boundary hx j j hxj
  have hendValue :
      greenLocalLift (coordLine x₂ j h) =
        greenLocalLift (coordLine x j h) := by
    rw [hpoint, greenLocalLift_add_period]
  rw [hendValue,
    show coordLine x₂ j 0 = x₂ by simp [coordLine],
    hbaseValue, hbaseGrad] at htaylor
  simpa [coordLine] using htaylor

/-- Global one-coordinate Taylor estimate on the torus.  The displacement
is represented in `[-π,π]`; the proof covers no wrap, upper wrap, lower
wrap, and the half-open-boundary starting point. -/
theorem greenLocalLift_coord_taylor_wrapped
    {x : R4} (j : Fin dim) {h r : ℝ}
    (hx : InClosedPrincipalCube x)
    (hxIco : x j ∈ Ico (-π) π)
    (hh : h ∈ Icc (-π) π)
    (hr : 0 < r)
    (hradius : ∀ t ∈ uIcc 0 h,
      r ≤ √(torusDistSq
        (greenLocalPoint (coordLine x j t)))) :
    |greenLocalLift (coordLine x j h) - greenLocalLift x -
        greenLocalGrad x j * h| ≤
      (2 * (greenLocalHessSingularBound * r⁻¹ ^ 4)) *
        h ^ 2 := by
  by_cases hupperWrap : π < x j + h
  · have hpos : 0 < h := by linarith [hxIco.2]
    let p : ℝ := π - x j
    let x₂ : R4 := coordLine x j (-2 * π)
    have hp : 0 < p := by
      dsimp only [p]
      linarith [hxIco.2]
    have hp_le : p ≤ h := by
      dsimp only [p]
      linarith
    have hclosed₁ :
        ∀ t ∈ Icc 0 p,
          InClosedPrincipalCube (coordLine x j t) := by
      intro t ht
      apply inClosedPrincipalCube_coordLine_of_bounds hx j
      · linarith [hxIco.1, ht.1]
      · dsimp only [p] at ht
        linarith [ht.2]
    have hradius₁ :
        ∀ t ∈ Icc 0 p,
          r ≤ √(euclideanDistSq (coordLine x j t)) := by
      intro t ht
      rw [← torusDistSq_greenLocalPoint_of_closed
        (hclosed₁ t ht)]
      exact hradius t (by
        rw [uIcc_of_le hpos.le]
        exact ⟨ht.1, ht.2.trans hp_le⟩)
    have hx₂coord :
        ∀ t : ℝ, coordLine x₂ j t j =
          x j - 2 * π + t := by
      intro t
      simp [x₂, coordLine]
      ring
    have hclosed₂ :
        ∀ t ∈ Icc p h,
          InClosedPrincipalCube (coordLine x₂ j t) := by
      intro t ht i
      by_cases hij : i = j
      · subst i
        rw [abs_le, hx₂coord]
        dsimp only [p] at ht
        constructor
        · linarith [ht.1]
        · linarith [ht.2, hh.2, hxIco.2]
      · have hi := hx i
        simpa [x₂, coordLine, hij] using hi
    have hpoint₂ :
        ∀ t : ℝ,
          coordLine x₂ j t =
            coordLine x j t +
              realPeriodShift (Pi.single j (-1)) := by
      intro t
      funext i
      by_cases hij : i = j
      · subst i
        simp [x₂, coordLine, realPeriodShift]
        ring
      · simp [x₂, coordLine, realPeriodShift, hij]
    have hradius₂ :
        ∀ t ∈ Icc p h,
          r ≤ √(euclideanDistSq (coordLine x₂ j t)) := by
      intro t ht
      rw [← torusDistSq_greenLocalPoint_of_closed
        (hclosed₂ t ht), hpoint₂,
        greenLocalPoint_add_period]
      exact hradius t (by
        rw [uIcc_of_le hpos.le]
        exact ⟨hp.le.trans ht.1, ht.2⟩)
    have hbase :=
      greenLocalLift_coord_taylor_upper_wrap
        (x := x) j hx hxIco.2 hupperWrap hh.2 hr
        (by simpa only [p] using hradius₁)
        (by simpa only [x₂, p] using hradius₂)
    exact hbase.trans (by
      have hnonneg :
          0 ≤ (greenLocalHessSingularBound * r⁻¹ ^ 4) *
            h ^ 2 :=
        mul_nonneg
          (mul_nonneg greenLocalHessSingularBound_nonneg
            (pow_nonneg (inv_nonneg.mpr hr.le) _))
          (sq_nonneg h)
      linarith)
  · by_cases hlowerWrap : x j + h < -π
    · have hneg : h < 0 := by linarith [hxIco.1]
      rcases eq_or_lt_of_le hxIco.1 with hxBoundary | hxInterior
      · exact greenLocalLift_coord_taylor_from_lower_boundary
          (x := x) j hx hxBoundary.symm hneg hh.1 hr hradius
      · let c : ℝ := -π - x j
        let x₂ : R4 := coordLine x j (2 * π)
        have hc : h ≤ c := by
          dsimp only [c]
          linarith
        have hc_le : c ≤ 0 := by
          dsimp only [c]
          linarith
        have hclosed₁ :
            ∀ t ∈ Icc c 0,
              InClosedPrincipalCube (coordLine x j t) := by
          intro t ht
          apply inClosedPrincipalCube_coordLine_of_bounds hx j
          · dsimp only [c] at ht
            linarith [ht.1]
          · linarith [hxIco.2, ht.2]
        have hradius₁ :
            ∀ t ∈ Icc c 0,
              r ≤ √(euclideanDistSq (coordLine x j t)) := by
          intro t ht
          rw [← torusDistSq_greenLocalPoint_of_closed
            (hclosed₁ t ht)]
          exact hradius t (by
            rw [uIcc_of_ge hneg.le]
            exact ⟨hc.trans ht.1, ht.2⟩)
        have hx₂coord :
            ∀ t : ℝ, coordLine x₂ j t j =
              x j + 2 * π + t := by
          intro t
          simp [x₂, coordLine]
        have hclosed₂ :
            ∀ t ∈ Icc h c,
              InClosedPrincipalCube (coordLine x₂ j t) := by
          intro t ht i
          by_cases hij : i = j
          · subst i
            rw [abs_le, hx₂coord]
            dsimp only [c] at ht
            constructor
            · linarith [ht.1, hh.1, hxInterior]
            · linarith [ht.2]
          · have hi := hx i
            simpa [x₂, coordLine, hij] using hi
        have hpoint₂ :
            ∀ t : ℝ,
              coordLine x₂ j t =
                coordLine x j t +
                  realPeriodShift (Pi.single j 1) := by
          intro t
          funext i
          by_cases hij : i = j
          · subst i
            simp [x₂, coordLine, realPeriodShift]
            ring
          · simp [x₂, coordLine, realPeriodShift, hij]
        have hradius₂ :
            ∀ t ∈ Icc h c,
              r ≤ √(euclideanDistSq (coordLine x₂ j t)) := by
          intro t ht
          rw [← torusDistSq_greenLocalPoint_of_closed
            (hclosed₂ t ht), hpoint₂,
            greenLocalPoint_add_period]
          exact hradius t (by
            rw [uIcc_of_ge hneg.le]
            exact ⟨ht.1, ht.2.trans hc_le⟩)
        exact greenLocalLift_coord_taylor_lower_wrap
          (x := x) j hx hxInterior hlowerWrap hh.1 hr
          (by simpa only [c] using hradius₁)
          (by simpa only [x₂, c] using hradius₂)
    · exact greenLocalLift_coord_taylor_no_wrap
        (x := x) j hx (le_of_not_gt hlowerWrap)
          (le_of_not_gt hupperWrap) hr hradius

/-- Canonical endpoint of a real coordinate displacement. -/
def wrappedCoordEndpoint (x : R4) (j : Fin dim) (h : ℝ) : R4 :=
  torusLift (greenLocalPoint (coordLine x j h))

theorem wrappedCoordEndpoint_mem_Ico
    (x : R4) (j : Fin dim) (h : ℝ) :
    ∀ i, wrappedCoordEndpoint x j h i ∈ Ico (-π) π :=
  torusLift_mem_Ico _

theorem wrappedCoordEndpoint_closed
    (x : R4) (j : Fin dim) (h : ℝ) :
    InClosedPrincipalCube (wrappedCoordEndpoint x j h) := by
  intro i
  exact abs_le.mpr
    ⟨(wrappedCoordEndpoint_mem_Ico x j h i).1,
      (wrappedCoordEndpoint_mem_Ico x j h i).2.le⟩

private theorem greenLocalGrad_wrappedCoordEndpoint_eq_of_closed
    {x z : R4} (j : Fin dim) (h : ℝ)
    (hz : InClosedPrincipalCube z)
    (hpoint :
      greenLocalPoint z =
        greenLocalPoint (coordLine x j h))
    (i : Fin dim) :
    greenLocalGrad (wrappedCoordEndpoint x j h) i =
      greenLocalGrad z i := by
  unfold wrappedCoordEndpoint
  rw [← hpoint, torusLift_greenLocalPoint_of_closed hz]
  exact greenLocalGrad_halfOpenRepresentative hz i

/-- Wrapped gradient Lipschitz estimate.  Each wrap is split at the
fundamental-cell seam and the two closed-cell estimates are concatenated. -/
theorem greenLocalGrad_coord_lipschitz_wrapped
    {x : R4} (i j : Fin dim) {h r : ℝ}
    (hx : InClosedPrincipalCube x)
    (hxIco : ∀ k, x k ∈ Ico (-π) π)
    (hh : h ∈ Icc (-π) π)
    (hr : 0 < r)
    (hradius : ∀ t ∈ uIcc 0 h,
      r ≤ √(torusDistSq
        (greenLocalPoint (coordLine x j t)))) :
    |greenLocalGrad (wrappedCoordEndpoint x j h) i -
        greenLocalGrad x i| ≤
      (4 * (greenLocalHessSingularBound * r⁻¹ ^ 4)) *
        |h| := by
  let M := greenLocalHessSingularBound * r⁻¹ ^ 4
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg greenLocalHessSingularBound_nonneg
      (pow_nonneg (inv_nonneg.mpr hr.le) _)
  by_cases hz : h = 0
  · subst h
    have hend :
        wrappedCoordEndpoint x j 0 = x := by
      unfold wrappedCoordEndpoint
      rw [show coordLine x j 0 = x by simp [coordLine],
        torusLift_greenLocalPoint hxIco]
    simp [hend]
  by_cases hupperWrap : π < x j + h
  · have hpos : 0 < h := by linarith [(hxIco j).2]
    let p : ℝ := π - x j
    let x₂ : R4 := coordLine x j (-2 * π)
    have hp : 0 < p := by
      dsimp only [p]
      linarith [(hxIco j).2]
    have hp_lt_h : p < h := by
      dsimp only [p]
      linarith
    have hclosed₁ :
        ∀ t ∈ Icc 0 p,
          InClosedPrincipalCube (coordLine x j t) := by
      intro t ht
      apply inClosedPrincipalCube_coordLine_of_bounds hx j
      · linarith [(hxIco j).1, ht.1]
      · dsimp only [p] at ht
        linarith [ht.2]
    have hradius₁ :
        ∀ t ∈ Icc 0 p,
          r ≤ √(euclideanDistSq (coordLine x j t)) := by
      intro t ht
      rw [← torusDistSq_greenLocalPoint_of_closed
        (hclosed₁ t ht)]
      exact hradius t (by
        rw [uIcc_of_le hpos.le]
        exact ⟨ht.1, ht.2.trans hp_lt_h.le⟩)
    have hcoord₁ :
        ∀ t ∈ Ioo 0 p,
          |coordLine x j t j| < π := by
      intro t ht
      rw [abs_lt]
      simp only [coordLine, Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_same, smul_eq_mul, mul_one]
      constructor
      · linarith [(hxIco j).1, ht.1]
      · dsimp only [p] at ht
        linarith [ht.2]
    have hx₂coord :
        ∀ t : ℝ, coordLine x₂ j t j =
          x j - 2 * π + t := by
      intro t
      simp [x₂, coordLine]
      ring
    have hclosed₂ :
        ∀ t ∈ Icc p h,
          InClosedPrincipalCube (coordLine x₂ j t) := by
      intro t ht k
      by_cases hkj : k = j
      · subst k
        rw [abs_le, hx₂coord]
        dsimp only [p] at ht
        constructor
        · linarith [ht.1]
        · linarith [ht.2, hh.2, (hxIco j).2]
      · simpa [x₂, coordLine, hkj] using hx k
    have hcoord₂ :
        ∀ t ∈ Ioo p h,
          |coordLine x₂ j t j| < π := by
      intro t ht
      rw [abs_lt, hx₂coord]
      dsimp only [p] at ht
      constructor
      · linarith [ht.1]
      · linarith [ht.2, hh.2, (hxIco j).2]
    have hpoint₂ :
        ∀ t : ℝ,
          coordLine x₂ j t =
            coordLine x j t +
              realPeriodShift (Pi.single j (-1)) := by
      intro t
      funext k
      by_cases hkj : k = j
      · subst k
        simp [x₂, coordLine, realPeriodShift]
        ring
      · simp [x₂, coordLine, realPeriodShift, hkj]
    have hradius₂ :
        ∀ t ∈ Icc p h,
          r ≤ √(euclideanDistSq (coordLine x₂ j t)) := by
      intro t ht
      rw [← torusDistSq_greenLocalPoint_of_closed
        (hclosed₂ t ht), hpoint₂,
        greenLocalPoint_add_period]
      exact hradius t (by
        rw [uIcc_of_le hpos.le]
        exact ⟨hp.le.trans ht.1, ht.2⟩)
    have hg₁ :=
      greenLocalGrad_coord_lipschitz_closed_interval_of_radius
        (x := x) i j hp hr hclosed₁ hcoord₁ hradius₁
    have hg₂ :=
      greenLocalGrad_coord_lipschitz_closed_interval_of_radius
        (x := x₂) i j hp_lt_h hr hclosed₂ hcoord₂ hradius₂
    have hlowerClosed :=
      hclosed₂ p (left_mem_Icc.mpr hp_lt_h.le)
    have hlowerCoord :
        coordLine x₂ j p j = -π := by
      rw [hx₂coord]
      dsimp only [p]
      ring
    have hseamPoint :
        coordLine (coordLine x₂ j p) j (2 * π) =
          coordLine x j p := by
      funext k
      by_cases hkj : k = j
      · subst k
        simp [x₂, coordLine]
        ring
      · simp [x₂, coordLine, hkj]
    have hseam :
        greenLocalGrad (coordLine x₂ j p) i =
          greenLocalGrad (coordLine x j p) i := by
      symm
      rw [← hseamPoint]
      exact greenLocalGrad_lower_upper_boundary
        hlowerClosed j i hlowerCoord
    have hendEq :
        greenLocalGrad (wrappedCoordEndpoint x j h) i =
          greenLocalGrad (coordLine x₂ j h) i := by
      apply greenLocalGrad_wrappedCoordEndpoint_eq_of_closed
        j h (hclosed₂ h (right_mem_Icc.mpr hp_lt_h.le)) _ i
      rw [hpoint₂, greenLocalPoint_add_period]
    have hraw :
        |greenLocalGrad (coordLine x₂ j h) i -
            greenLocalGrad x i| ≤ M * h := by
      calc
        |greenLocalGrad (coordLine x₂ j h) i -
            greenLocalGrad x i| ≤
            |greenLocalGrad (coordLine x₂ j h) i -
              greenLocalGrad (coordLine x₂ j p) i| +
            |greenLocalGrad (coordLine x₂ j p) i -
              greenLocalGrad x i| :=
          abs_sub_le _ _ _
        _ ≤ M * (h - p) + M * p := by
          exact add_le_add
            (by simpa only [M] using hg₂)
            (by
              calc
                |greenLocalGrad (coordLine x₂ j p) i -
                    greenLocalGrad x i| =
                    |greenLocalGrad (coordLine x j p) i -
                      greenLocalGrad x i| := by rw [hseam]
                _ ≤ M * p := by
                  simpa [M, coordLine] using hg₁)
        _ = M * h := by ring
    rw [hendEq]
    exact hraw.trans (by
      rw [abs_of_pos hpos]
      nlinarith [mul_nonneg hM hpos.le])
  · by_cases hlowerWrap : x j + h < -π
    · have hneg : h < 0 := by linarith [(hxIco j).1]
      rcases eq_or_lt_of_le (hxIco j).1 with hxBoundary | hxInterior
      · let x₂ : R4 := coordLine x j (2 * π)
        have hxj : x j = -π := hxBoundary.symm
        have hx₂coord :
            ∀ t : ℝ, coordLine x₂ j t j = π + t := by
          intro t
          simp [x₂, coordLine, hxj]
          ring
        have hclosed :
            ∀ t ∈ Icc h 0,
              InClosedPrincipalCube (coordLine x₂ j t) := by
          intro t ht k
          by_cases hkj : k = j
          · subst k
            rw [abs_le, hx₂coord]
            constructor
            · linarith [ht.1, hh.1, Real.pi_pos]
            · linarith [ht.2]
          · simpa [x₂, coordLine, hkj] using hx k
        have hcoord :
            ∀ t ∈ Ioo h 0,
              |coordLine x₂ j t j| < π := by
          intro t ht
          rw [abs_lt, hx₂coord]
          constructor
          · linarith [ht.1, hh.1, Real.pi_pos]
          · linarith [ht.2]
        have hpoint :
            ∀ t : ℝ,
              coordLine x₂ j t =
                coordLine x j t +
                  realPeriodShift (Pi.single j 1) := by
          intro t
          funext k
          by_cases hkj : k = j
          · subst k
            simp [x₂, coordLine, realPeriodShift]
            ring
          · simp [x₂, coordLine, realPeriodShift, hkj]
        have hradius' :
            ∀ t ∈ Icc h 0,
              r ≤ √(euclideanDistSq (coordLine x₂ j t)) := by
          intro t ht
          rw [← torusDistSq_greenLocalPoint_of_closed
            (hclosed t ht), hpoint,
            greenLocalPoint_add_period]
          exact hradius t (by
            rw [uIcc_of_ge hneg.le]
            exact ht)
        have hg :=
          greenLocalGrad_coord_lipschitz_closed_interval_of_radius
            (x := x₂) i j hneg hr hclosed hcoord hradius'
        have hbase :
            greenLocalGrad x₂ i = greenLocalGrad x i := by
          rw [show x₂ = coordLine x j (2 * π) by rfl]
          exact greenLocalGrad_lower_upper_boundary hx j i hxj
        have hendEq :
            greenLocalGrad (wrappedCoordEndpoint x j h) i =
              greenLocalGrad (coordLine x₂ j h) i := by
          apply greenLocalGrad_wrappedCoordEndpoint_eq_of_closed
            j h (hclosed h (left_mem_Icc.mpr hneg.le)) _ i
          rw [hpoint, greenLocalPoint_add_period]
        rw [hendEq]
        rw [show
          |greenLocalGrad (coordLine x₂ j h) i -
              greenLocalGrad x i| =
            |greenLocalGrad x₂ i -
              greenLocalGrad (coordLine x₂ j h) i| by
          rw [hbase, abs_sub_comm]]
        have hraw :
            |greenLocalGrad x₂ i -
                greenLocalGrad (coordLine x₂ j h) i| ≤
              M * (-h) := by
          simpa [M, coordLine] using hg
        exact hraw.trans (by
          rw [abs_of_neg hneg]
          nlinarith [mul_nonneg hM (neg_nonneg.mpr hneg.le)])
      · let c : ℝ := -π - x j
        let x₂ : R4 := coordLine x j (2 * π)
        have hc : h < c := by
          dsimp only [c]
          linarith
        have hc0 : c < 0 := by
          dsimp only [c]
          linarith
        have hclosed₁ :
            ∀ t ∈ Icc c 0,
              InClosedPrincipalCube (coordLine x j t) := by
          intro t ht
          apply inClosedPrincipalCube_coordLine_of_bounds hx j
          · dsimp only [c] at ht
            linarith [ht.1]
          · linarith [(hxIco j).2, ht.2]
        have hcoord₁ :
            ∀ t ∈ Ioo c 0,
              |coordLine x j t j| < π := by
          intro t ht
          rw [abs_lt]
          simp only [coordLine, Pi.add_apply, Pi.smul_apply,
            Pi.single_eq_same, smul_eq_mul, mul_one]
          dsimp only [c] at ht
          constructor
          · linarith [ht.1]
          · linarith [(hxIco j).2, ht.2]
        have hradius₁ :
            ∀ t ∈ Icc c 0,
              r ≤ √(euclideanDistSq (coordLine x j t)) := by
          intro t ht
          rw [← torusDistSq_greenLocalPoint_of_closed
            (hclosed₁ t ht)]
          exact hradius t (by
            rw [uIcc_of_ge hneg.le]
            exact ⟨hc.le.trans ht.1, ht.2⟩)
        have hx₂coord :
            ∀ t : ℝ, coordLine x₂ j t j =
              x j + 2 * π + t := by
          intro t
          simp [x₂, coordLine]
        have hclosed₂ :
            ∀ t ∈ Icc h c,
              InClosedPrincipalCube (coordLine x₂ j t) := by
          intro t ht k
          by_cases hkj : k = j
          · subst k
            rw [abs_le, hx₂coord]
            dsimp only [c] at ht
            constructor
            · linarith [ht.1, hh.1, hxInterior]
            · linarith [ht.2]
          · simpa [x₂, coordLine, hkj] using hx k
        have hcoord₂ :
            ∀ t ∈ Ioo h c,
              |coordLine x₂ j t j| < π := by
          intro t ht
          rw [abs_lt, hx₂coord]
          dsimp only [c] at ht
          constructor
          · linarith [ht.1, hh.1, hxInterior]
          · linarith [ht.2]
        have hpoint₂ :
            ∀ t : ℝ,
              coordLine x₂ j t =
                coordLine x j t +
                  realPeriodShift (Pi.single j 1) := by
          intro t
          funext k
          by_cases hkj : k = j
          · subst k
            simp [x₂, coordLine, realPeriodShift]
            ring
          · simp [x₂, coordLine, realPeriodShift, hkj]
        have hradius₂ :
            ∀ t ∈ Icc h c,
              r ≤ √(euclideanDistSq (coordLine x₂ j t)) := by
          intro t ht
          rw [← torusDistSq_greenLocalPoint_of_closed
            (hclosed₂ t ht), hpoint₂,
            greenLocalPoint_add_period]
          exact hradius t (by
            rw [uIcc_of_ge hneg.le]
            exact ⟨ht.1, ht.2.trans hc0.le⟩)
        have hg₁ :=
          greenLocalGrad_coord_lipschitz_closed_interval_of_radius
            (x := x) i j hc0 hr hclosed₁ hcoord₁ hradius₁
        have hg₂ :=
          greenLocalGrad_coord_lipschitz_closed_interval_of_radius
            (x := x₂) i j hc hr hclosed₂ hcoord₂ hradius₂
        have hlowerClosed :=
          hclosed₁ c (left_mem_Icc.mpr hc0.le)
        have hlowerCoord :
            coordLine x j c j = -π := by
          simp only [coordLine, Pi.add_apply, Pi.smul_apply,
            Pi.single_eq_same, smul_eq_mul, mul_one]
          dsimp only [c]
          ring
        have hseamPoint :
            coordLine (coordLine x j c) j (2 * π) =
              coordLine x₂ j c := by
          funext k
          by_cases hkj : k = j
          · subst k
            simp [x₂, coordLine]
            ring
          · simp [x₂, coordLine, hkj]
        have hseam :
            greenLocalGrad (coordLine x₂ j c) i =
              greenLocalGrad (coordLine x j c) i := by
          rw [← hseamPoint]
          exact greenLocalGrad_lower_upper_boundary
            hlowerClosed j i hlowerCoord
        have hendEq :
            greenLocalGrad (wrappedCoordEndpoint x j h) i =
              greenLocalGrad (coordLine x₂ j h) i := by
          apply greenLocalGrad_wrappedCoordEndpoint_eq_of_closed
            j h (hclosed₂ h (left_mem_Icc.mpr hc.le)) _ i
          rw [hpoint₂, greenLocalPoint_add_period]
        have hraw :
            |greenLocalGrad (coordLine x₂ j h) i -
                greenLocalGrad x i| ≤ M * (-h) := by
          calc
            |greenLocalGrad (coordLine x₂ j h) i -
                greenLocalGrad x i| ≤
                |greenLocalGrad (coordLine x₂ j h) i -
                  greenLocalGrad (coordLine x₂ j c) i| +
                |greenLocalGrad (coordLine x₂ j c) i -
                  greenLocalGrad x i| :=
              abs_sub_le _ _ _
            _ ≤ M * (c - h) + M * (0 - c) := by
              exact add_le_add
                (by
                  calc
                    |greenLocalGrad (coordLine x₂ j h) i -
                        greenLocalGrad (coordLine x₂ j c) i| =
                        |greenLocalGrad (coordLine x₂ j c) i -
                          greenLocalGrad (coordLine x₂ j h) i| :=
                      abs_sub_comm _ _
                    _ ≤ M * (c - h) := by
                      simpa only [M] using hg₂)
                (by
                  calc
                    |greenLocalGrad (coordLine x₂ j c) i -
                        greenLocalGrad x i| =
                        |greenLocalGrad (coordLine x j c) i -
                          greenLocalGrad x i| := by rw [hseam]
                    _ = |greenLocalGrad x i -
                          greenLocalGrad (coordLine x j c) i| :=
                      abs_sub_comm _ _
                    _ ≤ M * (0 - c) := by
                      simpa [M, coordLine] using hg₁)
            _ = M * (-h) := by ring
        rw [hendEq]
        exact hraw.trans (by
          rw [abs_of_neg hneg]
          nlinarith [mul_nonneg hM (neg_nonneg.mpr hneg.le)])
    · have hlower : -π ≤ x j + h := le_of_not_gt hlowerWrap
      have hupper : x j + h ≤ π := le_of_not_gt hupperWrap
      by_cases hpos : 0 < h
      · have hclosed :
            ∀ t ∈ Icc 0 h,
              InClosedPrincipalCube (coordLine x j t) := by
          intro t ht
          apply inClosedPrincipalCube_coordLine_of_bounds hx j
          · linarith [(hxIco j).1, ht.1]
          · linarith [ht.2, hupper]
        have hcoord :
            ∀ t ∈ Ioo 0 h,
              |coordLine x j t j| < π := by
          intro t ht
          rw [abs_lt]
          simp only [coordLine, Pi.add_apply, Pi.smul_apply,
            Pi.single_eq_same, smul_eq_mul, mul_one]
          constructor
          · linarith [(hxIco j).1, ht.1]
          · linarith [ht.2, hupper]
        have hradius' :
            ∀ t ∈ Icc 0 h,
              r ≤ √(euclideanDistSq (coordLine x j t)) := by
          intro t ht
          rw [← torusDistSq_greenLocalPoint_of_closed
            (hclosed t ht)]
          exact hradius t (by
            rw [uIcc_of_le hpos.le]
            exact ht)
        have hg :=
          greenLocalGrad_coord_lipschitz_closed_interval_of_radius
            (x := x) i j hpos hr hclosed hcoord hradius'
        have hendEq :=
          greenLocalGrad_wrappedCoordEndpoint_eq_of_closed
            j h (hclosed h (right_mem_Icc.mpr hpos.le))
            rfl i
        rw [hendEq]
        have hraw :
            |greenLocalGrad (coordLine x j h) i -
                greenLocalGrad x i| ≤ M * h := by
          simpa [M, coordLine] using hg
        exact hraw.trans (by
          rw [abs_of_pos hpos]
          nlinarith [mul_nonneg hM hpos.le])
      · have hneg : h < 0 :=
          lt_of_le_of_ne (le_of_not_gt hpos) hz
        have hclosed :
            ∀ t ∈ Icc h 0,
              InClosedPrincipalCube (coordLine x j t) := by
          intro t ht
          apply inClosedPrincipalCube_coordLine_of_bounds hx j
          · linarith [ht.1, hlower]
          · linarith [(hxIco j).2, ht.2]
        have hcoord :
            ∀ t ∈ Ioo h 0,
              |coordLine x j t j| < π := by
          intro t ht
          rw [abs_lt]
          simp only [coordLine, Pi.add_apply, Pi.smul_apply,
            Pi.single_eq_same, smul_eq_mul, mul_one]
          constructor
          · linarith [ht.1, hlower]
          · linarith [(hxIco j).2, ht.2]
        have hradius' :
            ∀ t ∈ Icc h 0,
              r ≤ √(euclideanDistSq (coordLine x j t)) := by
          intro t ht
          rw [← torusDistSq_greenLocalPoint_of_closed
            (hclosed t ht)]
          exact hradius t (by
            rw [uIcc_of_ge hneg.le]
            exact ht)
        have hg :=
          greenLocalGrad_coord_lipschitz_closed_interval_of_radius
            (x := x) i j hneg hr hclosed hcoord hradius'
        have hendEq :=
          greenLocalGrad_wrappedCoordEndpoint_eq_of_closed
            j h (hclosed h (left_mem_Icc.mpr hneg.le))
            rfl i
        rw [hendEq, abs_sub_comm]
        have hraw :
            |greenLocalGrad x i -
                greenLocalGrad (coordLine x j h) i| ≤
              M * (-h) := by
          simpa [M, coordLine] using hg
        exact hraw.trans (by
          rw [abs_of_neg hneg]
          nlinarith [mul_nonneg hM (neg_nonneg.mpr hneg.le)])

/-- The exact nonlinear remainder in the Green difference from (4.9). -/
def r322GreenRemainder (q u : T4) : ℝ :=
  greenFn q - greenFn (q - u) -
    torusLinearTerm (greenGradientCLM (torusLift q)) u

theorem r322GreenDifference_expansion (q u : T4) :
    greenFn q - greenFn (q - u) =
      torusLinearTerm (greenGradientCLM (torusLift q)) u +
        r322GreenRemainder q u := by
  unfold r322GreenRemainder
  ring

/-! ## Wrapped four-coordinate rectangular path -/

/-- The torus corner obtained after subtracting the first `k` coordinates
of `u` from `q`.  Unlike `coordinateCorner`, every intermediate point is
intrinsically defined on the torus and hence remains valid across a face of
the principal cell. -/
def torusCoordinateCorner
    (q u : T4) (k : Fin (dim + 1)) : T4 :=
  fun i => if i.val < k.val then q i - u i else q i

@[simp]
theorem torusCoordinateCorner_zero (q u : T4) :
    torusCoordinateCorner q u 0 = q := by
  funext i
  simp [torusCoordinateCorner]

@[simp]
theorem torusCoordinateCorner_last (q u : T4) :
    torusCoordinateCorner q u
        (⟨dim, by omega⟩ : Fin (dim + 1)) =
      q - u := by
  funext i
  simp [torusCoordinateCorner, i.isLt]

/-- Consecutive torus corners are joined by the canonical real lift of the
corresponding coordinate of `-u`. -/
theorem torusCoordinateCorner_succ
    (q u : T4) (i : Fin dim) :
    torusCoordinateCorner q u i.succ =
      greenLocalPoint
        (coordLine
          (torusLift
            (torusCoordinateCorner q u i.castSucc))
          i (-torusLift u i)) := by
  funext j
  have hcoeCorner :
      (((torusLift
          (torusCoordinateCorner q u i.castSucc) j : ℝ) :
            AddCircle (2 * π))) =
        torusCoordinateCorner q u i.castSucc j :=
    AddCircle.coe_equivIco
  have hcoeU :
      (((torusLift u j : ℝ) : AddCircle (2 * π))) = u j :=
    AddCircle.coe_equivIco
  by_cases hji : j = i
  · subst j
    simp only [torusCoordinateCorner, greenLocalPoint, coordLine,
      Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one, Fin.val_succ, Fin.val_castSucc] at hcoeCorner ⊢
    rw [AddCircle.coe_add, AddCircle.coe_neg,
      hcoeCorner, hcoeU]
    split <;> split <;>
      simp_all [sub_eq_add_neg]
  · simp only [torusCoordinateCorner, greenLocalPoint, coordLine,
      Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hji,
      smul_zero, add_zero, Fin.val_succ,
      Fin.val_castSucc] at hcoeCorner ⊢
    have hval : j.val ≠ i.val := by
      intro h
      exact hji (Fin.ext h)
    by_cases hlt : j.val < i.val
    · rw [if_pos hlt] at hcoeCorner
      rw [if_pos (by omega)]
      exact hcoeCorner.symm
    · rw [if_neg hlt] at hcoeCorner
      rw [if_neg (by omega)]
      exact hcoeCorner.symm

/-- Canonical real lifts of consecutive torus corners are exactly the
wrapped coordinate endpoints used by the one-dimensional estimates. -/
theorem torusLift_torusCoordinateCorner_succ
    (q u : T4) (i : Fin dim) :
    torusLift (torusCoordinateCorner q u i.succ) =
      wrappedCoordEndpoint
        (torusLift
          (torusCoordinateCorner q u i.castSucc))
        i (-torusLift u i) := by
  unfold wrappedCoordEndpoint
  rw [torusCoordinateCorner_succ]

/-- A point in the unoriented interval from zero to `a` has absolute
value at most `|a|`. -/
theorem abs_le_abs_of_mem_uIcc_zero
    {a t : ℝ} (ht : t ∈ uIcc 0 a) :
    |t| ≤ |a| := by
  rcases Set.mem_uIcc.mp ht with ht | ht
  · rw [abs_of_nonneg ht.1,
      abs_of_nonneg (ht.1.trans ht.2)]
    exact ht.2
  · rw [abs_of_nonpos ht.2,
      abs_of_nonpos (ht.1.trans ht.2)]
    linarith [ht.1]

/-- Every intermediate point on a wrapped coordinate edge lies within
the torus sup-distance `‖u‖` of the initial point `q`. -/
theorem norm_greenLocalPoint_coordLine_torusCorner_sub_le
    (q u : T4) (j : Fin dim) {t : ℝ}
    (ht : t ∈ uIcc 0 (-torusLift u j)) :
    ‖greenLocalPoint
          (coordLine
            (torusLift
              (torusCoordinateCorner q u j.castSucc))
            j t) - q‖ ≤
      ‖u‖ := by
  let c : T4 :=
    torusCoordinateCorner q u j.castSucc
  let p : T4 :=
    greenLocalPoint (coordLine (torusLift c) j t)
  have hcoeC (k : Fin dim) :
      (((torusLift c k : ℝ) :
        AddCircle (2 * π))) = c k :=
    AddCircle.coe_equivIco
  have hp_same :
      p j = q j + ((t : ℝ) : AddCircle (2 * π)) := by
    dsimp only [p]
    simp only [greenLocalPoint, coordLine, Pi.add_apply,
      Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    change
      (((torusLift c j + t : ℝ) :
          AddCircle (2 * π))) =
        q j + ((t : ℝ) : AddCircle (2 * π))
    rw [AddCircle.coe_add, hcoeC]
    have hcj : c j = q j := by
      simp [c, torusCoordinateCorner, Fin.val_castSucc]
    rw [hcj]
  have hp_ne (k : Fin dim) (hkj : k ≠ j) :
      p k = c k := by
    dsimp only [p]
    simp only [greenLocalPoint, coordLine, Pi.add_apply,
      Pi.smul_apply, Pi.single_eq_of_ne hkj,
      smul_zero, add_zero]
    exact hcoeC k
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2
  intro k
  by_cases hkj : k = j
  · subst k
    have hpt :
        (p - q) j =
          ((t : ℝ) : AddCircle (2 * π)) := by
      rw [Pi.sub_apply, hp_same]
      abel
    rw [show greenLocalPoint
          (coordLine
            (torusLift
              (torusCoordinateCorner q u j.castSucc))
            j t) = p by rfl,
      hpt]
    calc
      ‖((t : ℝ) : AddCircle (2 * π))‖ ≤ |t| := by
        simpa only [Real.norm_eq_abs] using
          (QuotientAddGroup.norm_mk_le_norm
            (S := AddSubgroup.zmultiples (2 * π))
            (m := t))
      _ ≤ |-torusLift u j| :=
        abs_le_abs_of_mem_uIcc_zero ht
      _ = ‖u j‖ := by
        rw [abs_neg, norm_eq_abs_torusLift]
      _ ≤ ‖u‖ := norm_le_pi_norm u j
  · rw [show greenLocalPoint
          (coordLine
            (torusLift
              (torusCoordinateCorner q u j.castSucc))
            j t) = p by rfl]
    rw [Pi.sub_apply, hp_ne k hkj]
    by_cases hlt : k.val < j.val
    · have hcorner :
          c k = q k - u k := by
        simp [c, torusCoordinateCorner, Fin.val_castSucc, hlt]
      rw [hcorner]
      simp only [sub_sub_cancel_left, norm_neg]
      exact norm_le_pi_norm u k
    · have hcorner :
          c k = q k := by
        simp [c, torusCoordinateCorner, Fin.val_castSucc, hlt]
      rw [hcorner, sub_self, norm_zero]
      exact norm_nonneg u

/-- Exact telescoping along the intrinsic torus rectangular path. -/
theorem torusCoordinateCorner_telescope
    (f : T4 → ℝ) (q u : T4) :
    f (q - u) - f q =
      ∑ i : Fin dim,
        (f (torusCoordinateCorner q u i.succ) -
          f (torusCoordinateCorner q u i.castSucc)) := by
  change f (q - u) - f q =
    ∑ i : Fin 4,
      (f (torusCoordinateCorner q u i.succ) -
        f (torusCoordinateCorner q u i.castSucc))
  have hlast :
      torusCoordinateCorner q u (4 : Fin 5) = q - u :=
    torusCoordinateCorner_last q u
  simp [Fin.sum_univ_succ, hlast]
  ring

/-- Prefix form of the torus rectangular telescope. -/
theorem torusCoordinateCorner_prefix_telescope
    (f : T4 → ℝ) (q u : T4) (k : Fin (dim + 1)) :
    f (torusCoordinateCorner q u k) - f q =
      ∑ i : Fin dim with i.val < k.val,
        (f (torusCoordinateCorner q u i.succ) -
          f (torusCoordinateCorner q u i.castSucc)) := by
  change f (torusCoordinateCorner q u k) - f q =
    ∑ i : Fin 4 with i.val < k.val,
      (f (torusCoordinateCorner q u i.succ) -
        f (torusCoordinateCorner q u i.castSucc))
  fin_cases k <;>
    rw [Finset.sum_filter] <;>
    simp [Fin.sum_univ_succ]
  ring

/-- The `ℓ¹` length of the canonical torus displacement. -/
def torusCoordinateL1 (u : T4) : ℝ :=
  ∑ i : Fin dim, |torusLift u i|

theorem torusCoordinateL1_nonneg (u : T4) :
    0 ≤ torusCoordinateL1 u := by
  unfold torusCoordinateL1
  positivity

theorem sum_sq_torusLift_le_torusCoordinateL1_sq (u : T4) :
    (∑ i : Fin dim, |torusLift u i| ^ 2) ≤
      torusCoordinateL1 u ^ 2 := by
  have hcoord :
      ∀ i : Fin dim, |torusLift u i| ≤ torusCoordinateL1 u := by
    intro i
    unfold torusCoordinateL1
    exact Finset.single_le_sum
      (fun j (_hj : j ∈ Finset.univ) =>
        abs_nonneg (torusLift u j))
      (Finset.mem_univ i)
  calc
    (∑ i : Fin dim, |torusLift u i| ^ 2) ≤
        ∑ i : Fin dim,
          |torusLift u i| * torusCoordinateL1 u := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left (hcoord i)
        (abs_nonneg (torusLift u i))
    _ = torusCoordinateL1 u ^ 2 := by
      rw [← Finset.sum_mul]
      unfold torusCoordinateL1
      ring

/-- Fixed-dimensional Cauchy--Schwarz for the canonical torus lift. -/
theorem torusCoordinateL1_sq_le_four_torusDistSq
    (u : T4) :
    torusCoordinateL1 u ^ 2 ≤ 4 * torusDistSq u := by
  have h :=
    sq_sum_le_card_mul_sum_sq
      (s := Finset.univ)
      (f := fun i : Fin dim => |torusLift u i|)
  simpa [torusCoordinateL1, torusDistSq, sq_abs] using h

/-- Exact Taylor decomposition along the wrapped torus rectangular path. -/
theorem torusCoordinateTaylor_decomposition
    (f : T4 → ℝ) (df : T4 → Fin dim → ℝ)
    (q u : T4) :
    f (q - u) - f q -
        (∑ i : Fin dim,
          df q i * (-torusLift u i)) =
      (∑ i : Fin dim,
        (f (torusCoordinateCorner q u i.succ) -
          f (torusCoordinateCorner q u i.castSucc) -
          df (torusCoordinateCorner q u i.castSucc) i *
            (-torusLift u i))) +
      ∑ i : Fin dim,
        (df (torusCoordinateCorner q u i.castSucc) i -
          df q i) * (-torusLift u i) := by
  have hgradient :
      (∑ i : Fin dim,
          (df (torusCoordinateCorner q u i.castSucc) i -
            df q i) * (-torusLift u i)) =
        (∑ i : Fin dim,
          df (torusCoordinateCorner q u i.castSucc) i *
            (-torusLift u i)) -
        ∑ i : Fin dim,
          df q i * (-torusLift u i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [torusCoordinateCorner_telescope]
  rw [hgradient]
  simp only [Finset.sum_sub_distrib]
  ring

/-- Abstract quantitative Taylor estimate on the wrapped rectangular path.
The coefficient `6` records `2` for the four edge remainders and `4` for
moving each intermediate gradient back to the initial point. -/
theorem torusCoordinateTaylor_bound
    (f : T4 → ℝ) (df : T4 → Fin dim → ℝ)
    (q u : T4) {M : ℝ}
    (hM : 0 ≤ M)
    (hremainder : ∀ i : Fin dim,
      |f (torusCoordinateCorner q u i.succ) -
          f (torusCoordinateCorner q u i.castSucc) -
          df (torusCoordinateCorner q u i.castSucc) i *
            (-torusLift u i)| ≤
        (2 * M) * |torusLift u i| ^ 2)
    (hgradient : ∀ i : Fin dim,
      |df (torusCoordinateCorner q u i.castSucc) i -
          df q i| ≤
        (4 * M) * torusCoordinateL1 u) :
    |f (q - u) - f q -
        (∑ i : Fin dim,
          df q i * (-torusLift u i))| ≤
      (6 * M) * torusCoordinateL1 u ^ 2 := by
  let rem : Fin dim → ℝ := fun i =>
    f (torusCoordinateCorner q u i.succ) -
      f (torusCoordinateCorner q u i.castSucc) -
      df (torusCoordinateCorner q u i.castSucc) i *
        (-torusLift u i)
  let gradMove : Fin dim → ℝ := fun i =>
    (df (torusCoordinateCorner q u i.castSucc) i -
      df q i) * (-torusLift u i)
  have hrem :
      |∑ i, rem i| ≤
        (2 * M) * torusCoordinateL1 u ^ 2 := by
    calc
      |∑ i, rem i| ≤ ∑ i, |rem i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (2 * M) * |torusLift u i| ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hremainder i
      _ = (2 * M) *
          ∑ i, |torusLift u i| ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ (2 * M) * torusCoordinateL1 u ^ 2 :=
        mul_le_mul_of_nonneg_left
          (sum_sq_torusLift_le_torusCoordinateL1_sq u)
          (mul_nonneg (by norm_num) hM)
  have hgrad :
      |∑ i, gradMove i| ≤
        (4 * M) * torusCoordinateL1 u ^ 2 := by
    calc
      |∑ i, gradMove i| ≤ ∑ i, |gradMove i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i,
          ((4 * M) * torusCoordinateL1 u) *
            |torusLift u i| := by
        apply Finset.sum_le_sum
        intro i _hi
        change
          |(df (torusCoordinateCorner q u i.castSucc) i -
              df q i) * (-torusLift u i)| ≤
            ((4 * M) * torusCoordinateL1 u) *
              |torusLift u i|
        rw [abs_mul, abs_neg]
        exact mul_le_mul_of_nonneg_right
          (hgradient i) (abs_nonneg (torusLift u i))
      _ = (4 * M) * torusCoordinateL1 u ^ 2 := by
        rw [← Finset.mul_sum]
        unfold torusCoordinateL1
        ring
  rw [torusCoordinateTaylor_decomposition]
  change |(∑ i, rem i) + ∑ i, gradMove i| ≤ _
  calc
    |(∑ i, rem i) + ∑ i, gradMove i| ≤
        |∑ i, rem i| + |∑ i, gradMove i| :=
      abs_add_le _ _
    _ ≤ (2 * M) * torusCoordinateL1 u ^ 2 +
        (4 * M) * torusCoordinateL1 u ^ 2 :=
      add_le_add hrem hgrad
    _ = (6 * M) * torusCoordinateL1 u ^ 2 := by ring

/-- Moving the Green gradient from any wrapped rectangular-path corner
back to the starting point costs at most four times the Hessian bound
times the total coordinate length. -/
theorem greenLocalGrad_torusCoordinateCorner_le
    (q u : T4) (i : Fin dim) {r : ℝ}
    (hr : 0 < r)
    (hradius : ∀ j : Fin dim,
      ∀ t ∈ uIcc 0 (-torusLift u j),
        r ≤ √(torusDistSq
          (greenLocalPoint
            (coordLine
              (torusLift
                (torusCoordinateCorner q u j.castSucc))
              j t)))) :
    |greenLocalGrad
          (torusLift
            (torusCoordinateCorner q u i.castSucc)) i -
        greenLocalGrad (torusLift q) i| ≤
      (4 * (greenLocalHessSingularBound * r⁻¹ ^ 4)) *
        torusCoordinateL1 u := by
  let M : ℝ :=
    greenLocalHessSingularBound * r⁻¹ ^ 4
  let f : T4 → ℝ := fun z =>
    greenLocalGrad (torusLift z) i
  have htelescope :=
    torusCoordinateCorner_prefix_telescope
      f q u i.castSucc
  have hedge :
      ∀ j : Fin dim,
        |f (torusCoordinateCorner q u j.succ) -
            f (torusCoordinateCorner q u j.castSucc)| ≤
          (4 * M) * |torusLift u j| := by
    intro j
    have hjIco := torusLift_mem_Ico
      (torusCoordinateCorner q u j.castSucc)
    have hjClosed :
        InClosedPrincipalCube
          (torusLift
            (torusCoordinateCorner q u j.castSucc)) := by
      intro k
      exact abs_le.mpr
        ⟨(hjIco k).1, (hjIco k).2.le⟩
    have hdisp : -torusLift u j ∈ Icc (-π) π := by
      have hu := torusLift_mem_Ico u j
      exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have hstep :=
      greenLocalGrad_coord_lipschitz_wrapped
        (x := torusLift
          (torusCoordinateCorner q u j.castSucc))
        i j hjClosed hjIco hdisp hr (hradius j)
    rw [← torusLift_torusCoordinateCorner_succ] at hstep
    simpa only [f, M, abs_neg] using hstep
  rw [htelescope]
  calc
    |∑ j : Fin dim with j.val < i.castSucc.val,
        (f (torusCoordinateCorner q u j.succ) -
          f (torusCoordinateCorner q u j.castSucc))| ≤
        ∑ j : Fin dim with j.val < i.castSucc.val,
          |f (torusCoordinateCorner q u j.succ) -
            f (torusCoordinateCorner q u j.castSucc)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin dim with j.val < i.castSucc.val,
          (4 * M) * |torusLift u j| := by
      exact Finset.sum_le_sum fun j _hj => hedge j
    _ ≤ ∑ j : Fin dim,
          (4 * M) * |torusLift u j| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro j _hj _hnot
        exact mul_nonneg
          (mul_nonneg (by norm_num)
            (mul_nonneg greenLocalHessSingularBound_nonneg
              (pow_nonneg (inv_nonneg.mpr hr.le) _)))
          (abs_nonneg (torusLift u j))
    _ = (4 * M) * torusCoordinateL1 u := by
      unfold torusCoordinateL1
      rw [Finset.mul_sum]

/-- Global torus Taylor estimate for the Green kernel.  No chart
compatibility hypothesis remains: each coordinate edge is allowed to wrap
once and is glued through periodic boundary values and gradients. -/
theorem abs_r322GreenRemainder_le_of_wrapped_radius
    (q u : T4) {r : ℝ}
    (hr : 0 < r)
    (hradius : ∀ j : Fin dim,
      ∀ t ∈ uIcc 0 (-torusLift u j),
        r ≤ √(torusDistSq
          (greenLocalPoint
            (coordLine
              (torusLift
                (torusCoordinateCorner q u j.castSucc))
              j t)))) :
    |r322GreenRemainder q u| ≤
      (24 * greenLocalHessSingularBound * r⁻¹ ^ 4) *
        torusDistSq u := by
  let M : ℝ :=
    greenLocalHessSingularBound * r⁻¹ ^ 4
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg greenLocalHessSingularBound_nonneg
      (pow_nonneg (inv_nonneg.mpr hr.le) _)
  have hedge :
      ∀ i : Fin dim,
        |greenFn (torusCoordinateCorner q u i.succ) -
            greenFn (torusCoordinateCorner q u i.castSucc) -
            greenLocalGrad
              (torusLift
                (torusCoordinateCorner q u i.castSucc)) i *
              (-torusLift u i)| ≤
          (2 * M) * |torusLift u i| ^ 2 := by
    intro i
    have hiIco := torusLift_mem_Ico
      (torusCoordinateCorner q u i.castSucc)
    have hiClosed :
        InClosedPrincipalCube
          (torusLift
            (torusCoordinateCorner q u i.castSucc)) := by
      intro k
      exact abs_le.mpr
        ⟨(hiIco k).1, (hiIco k).2.le⟩
    have hdisp : -torusLift u i ∈ Icc (-π) π := by
      have hu := torusLift_mem_Ico u i
      exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have hstep :=
      greenLocalLift_coord_taylor_wrapped
        (x := torusLift
          (torusCoordinateCorner q u i.castSucc))
        i hiClosed (hiIco i) hdisp hr (hradius i)
    rw [greenLocalLift_eq,
      ← torusCoordinateCorner_succ] at hstep
    simpa only [greenLocalLift_torusLift, M, neg_sq,
      sq_abs] using hstep
  have htaylor :=
    torusCoordinateTaylor_bound
      greenFn
      (fun z i => greenLocalGrad (torusLift z) i)
      q u hM hedge
      (greenLocalGrad_torusCoordinateCorner_le
        q u · hr hradius)
  have hlinear :
      (∑ i : Fin dim,
        greenLocalGrad (torusLift q) i *
          (-torusLift u i)) =
        -torusLinearTerm
          (greenGradientCLM (torusLift q)) u := by
    unfold torusLinearTerm
    rw [greenGradientCLM_apply, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hlinear] at htaylor
  have hremainder :
      |r322GreenRemainder q u| ≤
        (6 * M) * torusCoordinateL1 u ^ 2 := by
    calc
      |r322GreenRemainder q u| =
          |-(greenFn (q - u) - greenFn q -
            -torusLinearTerm
              (greenGradientCLM (torusLift q)) u)| := by
        congr 1
        unfold r322GreenRemainder
        ring
      _ = |greenFn (q - u) - greenFn q -
            -torusLinearTerm
              (greenGradientCLM (torusLift q)) u| :=
        abs_neg _
      _ ≤ (6 * M) * torusCoordinateL1 u ^ 2 :=
        htaylor
  calc
    |r322GreenRemainder q u| ≤
        (6 * M) * torusCoordinateL1 u ^ 2 :=
      hremainder
    _ ≤ (6 * M) * (4 * torusDistSq u) :=
      mul_le_mul_of_nonneg_left
        (torusCoordinateL1_sq_le_four_torusDistSq u)
        (mul_nonneg (by norm_num) hM)
    _ = (24 * greenLocalHessSingularBound * r⁻¹ ^ 4) *
          torusDistSq u := by
      dsimp only [M]
      ring

/-- In region (4.10), every point of every wrapped rectangular edge stays
at least `√(torusDistSq q) / 4` away from the Green singularity. -/
theorem wrapped_path_radius_of_reductionRegion_one
    (q u : T4)
    (hregion : 2 * ‖u‖ ≤ ‖q‖)
    (hq : q ≠ 0)
    (j : Fin dim) (t : ℝ)
    (ht : t ∈ uIcc 0 (-torusLift u j)) :
    √(torusDistSq q) / 4 ≤
      √(torusDistSq
        (greenLocalPoint
          (coordLine
            (torusLift
              (torusCoordinateCorner q u j.castSucc))
            j t))) := by
  let p : T4 :=
    greenLocalPoint
      (coordLine
        (torusLift
          (torusCoordinateCorner q u j.castSucc))
        j t)
  have hpath : ‖p - q‖ ≤ ‖u‖ :=
    norm_greenLocalPoint_coordLine_torusCorner_sub_le
      q u j ht
  have hreverse := norm_sub_norm_le q p
  rw [norm_sub_rev] at hreverse
  have hpLower : ‖q‖ / 2 ≤ ‖p‖ := by
    nlinarith
  have hsqrtUpper :
      √(torusDistSq q) ≤ 2 * ‖q‖ := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [torusDistSq_le_four_mul_sq_norm q]
  calc
    √(torusDistSq q) / 4 ≤ ‖q‖ / 2 := by
      nlinarith
    _ ≤ ‖p‖ := hpLower
    _ = √(‖p‖ ^ 2) := by
      rw [Real.sqrt_sq (norm_nonneg p)]
    _ ≤ √(torusDistSq p) :=
      Real.sqrt_le_sqrt (sq_norm_le_torusDistSq p)

/-- Pointwise form of the region-(4.10) Taylor estimate, expressed in the
same inverse-square kernel used by Proposition 4.1. -/
theorem abs_r322GreenRemainder_le_of_reductionRegion_one
    (q u : T4)
    (hregion : 2 * ‖u‖ ≤ ‖q‖)
    (hq : q ≠ 0) :
    |r322GreenRemainder q u| ≤
      (6144 * greenLocalHessSingularBound *
        invSqKer q ^ 2) * torusDistSq u := by
  have hdne : torusDistSq q ≠ 0 := by
    intro hzero
    exact hq ((torusDistSq_eq_zero_iff q).mp hzero)
  have hd : 0 < torusDistSq q :=
    lt_of_le_of_ne (torusDistSq_nonneg q) hdne.symm
  have hr :
      0 < √(torusDistSq q) / 4 := by
    exact div_pos (Real.sqrt_pos.2 hd) (by norm_num)
  have hraw :=
    abs_r322GreenRemainder_le_of_wrapped_radius
      q u hr
      (fun j t ht =>
        wrapped_path_radius_of_reductionRegion_one
          q u hregion hq j t ht)
  have hrpow :
      (√(torusDistSq q) / 4)⁻¹ ^ 4 =
        256 * (torusDistSq q)⁻¹ ^ 2 := by
    have hs :
        √(torusDistSq q) ^ 2 = torusDistSq q :=
      Real.sq_sqrt hd.le
    have hs0 : √(torusDistSq q) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hd)
    field_simp [hs0, hdne]
    nlinarith
  calc
    |r322GreenRemainder q u| ≤
        (24 * greenLocalHessSingularBound *
          (√(torusDistSq q) / 4)⁻¹ ^ 4) *
            torusDistSq u :=
      hraw
    _ = (6144 * greenLocalHessSingularBound *
          invSqKer q ^ 2) * torusDistSq u := by
      rw [hrpow]
      unfold invSqKer
      ring

/-- Coordinate permutations preserve the sup norm on `T4`. -/
theorem norm_comp_perm_eq
    (σ : Equiv.Perm (Fin dim)) (u : T4) :
    ‖u ∘ σ‖ = ‖u‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2
    intro i
    exact norm_le_pi_norm u (σ i)
  · apply (pi_norm_le_iff_of_nonneg
      (norm_nonneg (u ∘ σ))).2
    intro i
    have h := norm_le_pi_norm (u ∘ σ) (σ.symm i)
    simpa using h

/-- A single-coordinate sign flip preserves the sup norm on `T4`. -/
theorem norm_update_neg_eq
    (i : Fin dim) (u : T4) :
    ‖Function.update u i (-(u i))‖ = ‖u‖ := by
  have hcoord :
      ∀ j : Fin dim,
        ‖Function.update u i (-(u i)) j‖ = ‖u j‖ := by
    intro j
    by_cases hji : j = i
    · subst j
      simp
    · rw [Function.update_of_ne hji]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2
    intro j
    rw [hcoord]
    exact norm_le_pi_norm u j
  · apply (pi_norm_le_iff_of_nonneg
      (norm_nonneg (Function.update u i (-(u i))))).2
    intro j
    rw [← hcoord]
    exact norm_le_pi_norm
      (Function.update u i (-(u i))) j

/-- Restriction of a kernel to region (4.10), for a fixed outer
displacement `q`. -/
def reductionRegionOneKernel
    (q : T4) (J : T4 → ℝ) (u : T4) : ℝ :=
  if 2 * ‖u‖ ≤ ‖q‖ then J u else 0

/-- Region (4.10) is hyperoctahedrally invariant in its integration
variable, so restricting a class-`E` kernel preserves class `E`. -/
theorem reductionRegionOneKernel_memE
    {J : T4 → ℝ} (hJ : MemEClassT4 J) (q : T4) :
    MemEClassT4 (reductionRegionOneKernel q J) where
  perm_invariant := by
    intro σ u
    unfold reductionRegionOneKernel
    rw [norm_comp_perm_eq, hJ.perm_invariant]
  even_coord := by
    intro i u
    unfold reductionRegionOneKernel
    rw [norm_update_neg_eq, hJ.even_coord]

/-- If the canonical endpoint lifts differ by the canonical increment
lift, the coordinate Taylor linear term is the expected directional
derivative. -/
theorem coordinateLinearTerm_green_eq_neg_torusLinearTerm
    (q u : T4)
    (hcompat :
      torusLift (q - u) = torusLift q - torusLift u) :
    coordinateLinearTerm greenLocalGrad
        (torusLift q) (torusLift (q - u)) =
      -torusLinearTerm (greenGradientCLM (torusLift q)) u := by
  unfold coordinateLinearTerm torusLinearTerm
  rw [greenGradientCLM_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  have hi := congrFun hcompat i
  simp only [Pi.sub_apply] at hi
  rw [hi]
  ring

private theorem torusLinearTerm_eq_sum_r322
    (D : R4 →L[ℝ] ℝ) (u : T4) :
    torusLinearTerm D u =
      ∑ i : Fin dim,
        torusLift u i * D (Pi.single i 1) := by
  classical
  have hlift :
      torusLift u =
        ∑ i : Fin dim,
          (torusLift u i) • Pi.single i (1 : ℝ) := by
    exact pi_eq_sum_univ' (torusLift u)
  calc
    torusLinearTerm D u = D (torusLift u) := rfl
    _ = D (∑ i : Fin dim,
        (torusLift u i) • Pi.single i (1 : ℝ)) := by
      exact congrArg D hlift
    _ = ∑ i : Fin dim,
        D ((torusLift u i) • Pi.single i (1 : ℝ)) := by
      exact map_sum D _ _
    _ = ∑ i : Fin dim,
        torusLift u i * D (Pi.single i 1) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [map_smul]
      simp [smul_eq_mul]

/-- Weighted version of Taylor cancellation.  Unlike the generic theorem
in `ReductionSymmetry`, the remainder estimate is required only after
multiplication by `J`.  Consequently, geometric Taylor hypotheses need
only hold on the support of the region-restricted kernel. -/
theorem taylor_cancellation_bound_weighted
    {J δ remainder : T4 → ℝ} (hJ : MemEClassT4 J)
    (D : R4 →L[ℝ] ℝ) {C : ℝ}
    (hmoment : ∀ i : Fin dim,
      Integrable (fun u => J u * torusLift u i) paperMeasure)
    (hexpand : ∀ u,
      δ u = -torusLinearTerm D u + remainder u)
    (hweighted : ∀ u,
      |J u * remainder u| ≤
        |J u| * (C * torusDistSq u))
    (hintR : Integrable
      (fun u => J u * remainder u) paperMeasure)
    (hintMajorant : Integrable
      (fun u => |J u| * (C * torusDistSq u)) paperMeasure) :
    |∫ u, J u * δ u ∂paperMeasure| ≤
      ∫ u, |J u| * (C * torusDistSq u)
        ∂paperMeasure := by
  have hintLinear :
      Integrable
        (fun u => J u * torusLinearTerm D u)
        paperMeasure := by
    rw [show
      (fun u => J u * torusLinearTerm D u) =
        fun u => ∑ i : Fin dim,
          D (Pi.single i 1) *
            (J u * torusLift u i) by
      funext u
      rw [torusLinearTerm_eq_sum_r322]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring]
    exact integrable_finsetSum _ fun i _hi =>
      (hmoment i).const_mul _
  have hintegral :
      (∫ u, J u * δ u ∂paperMeasure) =
        ∫ u, J u * remainder u ∂paperMeasure := by
    calc
      (∫ u, J u * δ u ∂paperMeasure) =
          ∫ u, (-(J u * torusLinearTerm D u) +
            J u * remainder u) ∂paperMeasure := by
        apply integral_congr_ae
        filter_upwards with u
        rw [hexpand]
        ring
      _ = -(∫ u, J u * torusLinearTerm D u
              ∂paperMeasure) +
            ∫ u, J u * remainder u ∂paperMeasure := by
        calc
          (∫ u, (-(J u * torusLinearTerm D u) +
              J u * remainder u) ∂paperMeasure) =
              (∫ u, -(J u * torusLinearTerm D u)
                ∂paperMeasure) +
              ∫ u, J u * remainder u ∂paperMeasure := by
            exact integral_add hintLinear.neg hintR
          _ = -(∫ u, J u * torusLinearTerm D u
                  ∂paperMeasure) +
                ∫ u, J u * remainder u ∂paperMeasure := by
            rw [integral_neg]
      _ = ∫ u, J u * remainder u ∂paperMeasure := by
        rw [eClass_linear_moment_eq_zero hJ D hmoment]
        simp
  rw [hintegral]
  calc
    |∫ u, J u * remainder u ∂paperMeasure| ≤
        ∫ u, |J u * remainder u| ∂paperMeasure := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (μ := paperMeasure)
          (fun u => J u * remainder u))
    _ ≤ ∫ u, |J u| * (C * torusDistSq u)
          ∂paperMeasure := by
      exact integral_mono_of_nonneg
        (.of_forall fun u => abs_nonneg (J u * remainder u))
        hintMajorant (.of_forall hweighted)

/-- Integrated region-(4.10) cancellation.  The linear Green term is
removed by class-`E` symmetry; only the quadratic remainder survives. -/
theorem r322GreenDifference_regionOne_integral_le
    {J : T4 → ℝ} (hJ : MemEClassT4 J)
    (q : T4) (hq : q ≠ 0)
    (hmoment : ∀ i : Fin dim,
      Integrable
        (fun u =>
          reductionRegionOneKernel q J u *
            torusLift u i)
        paperMeasure)
    (hintR : Integrable
      (fun u =>
        reductionRegionOneKernel q J u *
          r322GreenRemainder q u)
      paperMeasure)
    (hintMajorant : Integrable
      (fun u =>
        |reductionRegionOneKernel q J u| *
          ((6144 * greenLocalHessSingularBound *
            invSqKer q ^ 2) * torusDistSq u))
      paperMeasure) :
    |∫ u,
        reductionRegionOneKernel q J u *
          (greenFn q - greenFn (q - u))
        ∂paperMeasure| ≤
      ∫ u,
        |reductionRegionOneKernel q J u| *
          ((6144 * greenLocalHessSingularBound *
            invSqKer q ^ 2) * torusDistSq u)
        ∂paperMeasure := by
  let C : ℝ :=
    6144 * greenLocalHessSingularBound * invSqKer q ^ 2
  refine taylor_cancellation_bound_weighted
    (J := reductionRegionOneKernel q J)
    (δ := fun u => greenFn q - greenFn (q - u))
    (remainder := r322GreenRemainder q)
    (reductionRegionOneKernel_memE hJ q)
    (-greenGradientCLM (torusLift q))
    (C := C) hmoment ?_ ?_ hintR hintMajorant
  · intro u
    rw [r322GreenDifference_expansion]
    simp [torusLinearTerm]
  · intro u
    by_cases hregion : 2 * ‖u‖ ≤ ‖q‖
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_r322GreenRemainder_le_of_reductionRegion_one
          q u hregion hq)
        (abs_nonneg (reductionRegionOneKernel q J u))
    · simp [reductionRegionOneKernel, hregion]

/-- The quantitative remainder estimate behind paper (4.9), on a safe
local chart.  The factor `8` is `2` from the rectangular Taylor theorem
times `4` from `ℓ¹² ≤ 4ℓ²²`. -/
theorem abs_r322GreenRemainder_le_of_safe_lifts
    (q u : T4) {r : ℝ}
    (hr : 0 < r)
    (hcompat :
      torusLift (q - u) = torusLift q - torusLift u)
    (hopen : ∀ j : Fin dim,
      ∀ t ∈ uIcc 0
          (torusLift (q - u) j - torusLift q j),
        InOpenPrincipalCube
          (coordLine
            (coordinateCorner (torusLift q) (torusLift (q - u))
              j.castSucc) j t))
    (hradius : ∀ j : Fin dim,
      ∀ t ∈ uIcc 0
          (torusLift (q - u) j - torusLift q j),
        r ≤ √(euclideanDistSq
          (coordLine
            (coordinateCorner (torusLift q) (torusLift (q - u))
              j.castSucc) j t))) :
    |r322GreenRemainder q u| ≤
      (8 * greenLocalHessSingularBound * r⁻¹ ^ 4) *
        torusDistSq u := by
  have htaylor :=
    greenFn_rectangular_taylor_of_safe_lifts
      q (q - u) hr hopen hradius
  rw [coordinateLinearTerm_green_eq_neg_torusLinearTerm
    q u hcompat] at htaylor
  have hremainder :
      |r322GreenRemainder q u| ≤
        (2 * (greenLocalHessSingularBound * r⁻¹ ^ 4)) *
          coordinateL1Dist
            (torusLift q) (torusLift (q - u)) ^ 2 := by
    calc
      |r322GreenRemainder q u| =
          |-r322GreenRemainder q u| := (abs_neg _).symm
      _ = |greenFn (q - u) - greenFn q -
          -torusLinearTerm
            (greenGradientCLM (torusLift q)) u| := by
        congr 1
        unfold r322GreenRemainder
        ring
      _ ≤ (2 * (greenLocalHessSingularBound * r⁻¹ ^ 4)) *
          coordinateL1Dist
            (torusLift q) (torusLift (q - u)) ^ 2 :=
        htaylor
  have hdist :
      euclideanDistSq
          (torusLift (q - u) - torusLift q) =
        torusDistSq u := by
    rw [hcompat]
    unfold euclideanDistSq torusDistSq
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [Pi.sub_apply]
    ring
  have hl1 :
      coordinateL1Dist
          (torusLift q) (torusLift (q - u)) ^ 2 ≤
        4 * torusDistSq u := by
    calc
      coordinateL1Dist
          (torusLift q) (torusLift (q - u)) ^ 2 ≤
          4 * euclideanDistSq
            (torusLift (q - u) - torusLift q) :=
        coordinateL1Dist_sq_le_four_euclideanDistSq _ _
      _ = 4 * torusDistSq u := by rw [hdist]
  have hcoef :
      0 ≤ 2 * (greenLocalHessSingularBound * r⁻¹ ^ 4) := by
    exact mul_nonneg (by norm_num)
      (mul_nonneg greenLocalHessSingularBound_nonneg
        (pow_nonneg (inv_nonneg.mpr hr.le) _))
  calc
    |r322GreenRemainder q u| ≤
        (2 * (greenLocalHessSingularBound * r⁻¹ ^ 4)) *
          coordinateL1Dist
            (torusLift q) (torusLift (q - u)) ^ 2 :=
      hremainder
    _ ≤ (2 * (greenLocalHessSingularBound * r⁻¹ ^ 4)) *
          (4 * torusDistSq u) :=
      mul_le_mul_of_nonneg_left hl1 hcoef
    _ = (8 * greenLocalHessSingularBound * r⁻¹ ^ 4) *
          torusDistSq u := by ring

/-- Integrated Taylor cancellation on a safe chart.  Every premise other
than integrability is discharged from the concrete Green construction and
the geometric chart conditions above. -/
theorem r322GreenDifference_integral_le_of_safe_lifts
    {J : T4 → ℝ} (hJ : MemEClassT4 J)
    (q : T4) {r : ℝ}
    (hr : 0 < r)
    (hcompat : ∀ u : T4,
      J u ≠ 0 →
        torusLift (q - u) = torusLift q - torusLift u)
    (hopen : ∀ u : T4, J u ≠ 0 → ∀ j : Fin dim,
      ∀ t ∈ uIcc 0
          (torusLift (q - u) j - torusLift q j),
        InOpenPrincipalCube
          (coordLine
            (coordinateCorner (torusLift q) (torusLift (q - u))
              j.castSucc) j t))
    (hradius : ∀ u : T4, J u ≠ 0 → ∀ j : Fin dim,
      ∀ t ∈ uIcc 0
          (torusLift (q - u) j - torusLift q j),
        r ≤ √(euclideanDistSq
          (coordLine
            (coordinateCorner (torusLift q) (torusLift (q - u))
              j.castSucc) j t)))
    (hmoment : ∀ i : Fin dim,
      Integrable (fun u => J u * torusLift u i) paperMeasure)
    (hintR : Integrable
      (fun u => J u * r322GreenRemainder q u) paperMeasure)
    (hintMajorant : Integrable
      (fun u => |J u| *
        ((8 * greenLocalHessSingularBound * r⁻¹ ^ 4) *
          torusDistSq u)) paperMeasure) :
    |∫ u, J u * (greenFn q - greenFn (q - u))
        ∂paperMeasure| ≤
      ∫ u, |J u| *
        ((8 * greenLocalHessSingularBound * r⁻¹ ^ 4) *
          torusDistSq u) ∂paperMeasure := by
  let C : ℝ :=
    8 * greenLocalHessSingularBound * r⁻¹ ^ 4
  refine taylor_cancellation_bound_weighted
    (J := J)
    (δ := fun u => greenFn q - greenFn (q - u))
    (remainder := r322GreenRemainder q)
    hJ (-greenGradientCLM (torusLift q))
    (C := C) hmoment ?_ ?_ hintR hintMajorant
  · intro u
    rw [r322GreenDifference_expansion]
    simp [torusLinearTerm]
  · intro u
    by_cases hu : J u = 0
    · simp [hu]
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_r322GreenRemainder_le_of_safe_lifts
          q u hr (hcompat u hu) (hopen u hu) (hradius u hu))
        (abs_nonneg (J u))

end

end Anderson4D
