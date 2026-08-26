import Anderson4D.Continuum.GreenBounds

/-!
# Time integrals for derivatives of the four-dimensional Green kernel

The zeroth-order Green bound in `GreenBounds.lean` uses

`∫₀∞ t⁻² exp (-a / t) dt = a⁻¹`.

Differentiating the Gaussian once and twice introduces the two adjacent
integrals proved here.  Keeping these scalar identities separate avoids
repeating the inversion substitution in the derivative estimates for
blueprint node I-green.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Real Set

/-- Squared Euclidean length on the lifted space `ℝ⁴`.  It is kept
separate from the ambient Pi norm because the paper's heat kernel uses
the Euclidean quadratic form while `R4` deliberately carries mathlib's
Pi norm. -/
def euclideanDistSq (x : R4) : ℝ :=
  ∑ i, x i ^ 2

/-- The non-periodized four-dimensional Gaussian heat kernel. -/
def euclideanHeatKernel4 (t : ℝ) (x : R4) : ℝ :=
  (4 * π * t) ^ (-2 : ℤ) *
    exp (-euclideanDistSq x / (4 * t))

/-- The principal singularity in paper (4.1):
`(4π²|x|²)⁻¹`. -/
def laplaceFundamental4 (x : R4) : ℝ :=
  (4 * π ^ 2 * euclideanDistSq x)⁻¹

/-- The Euclidean squared length is nonnegative. -/
theorem euclideanDistSq_nonneg (x : R4) :
    0 ≤ euclideanDistSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Algebraic normal form of the Euclidean heat kernel used by all three
time-integral calculations. -/
theorem euclideanHeatKernel4_eq_timeMajorant {t : ℝ}
    (ht : 0 < t) (x : R4) :
    euclideanHeatKernel4 t x =
      (16 * π ^ 2)⁻¹ * ((t ^ 2)⁻¹ *
        exp (-(euclideanDistSq x / 4 / t))) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hpi : π ≠ 0 := Real.pi_ne_zero
  unfold euclideanHeatKernel4
  rw [zpow_neg, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num,
    zpow_natCast]
  field_simp
  ring

/-- The Euclidean heat kernel is genuinely integrable in time away from
the spatial origin. -/
theorem integrableOn_euclideanHeatKernel4 {x : R4}
    (hx : euclideanDistSq x ≠ 0) :
    IntegrableOn (fun t => euclideanHeatKernel4 t x)
      (Ioi (0 : ℝ)) := by
  have hs : 0 < euclideanDistSq x :=
    lt_of_le_of_ne (euclideanDistSq_nonneg x) (Ne.symm hx)
  have ha : 0 < euclideanDistSq x / 4 := by positivity
  have hint :
      IntegrableOn
        (fun t => (t ^ 2)⁻¹ *
          exp (-(euclideanDistSq x / 4 / t)))
        (Ioi (0 : ℝ)) :=
    integrableOn_inv_sq_exp ha
  have hint' :
      IntegrableOn
        (fun t => (16 * π ^ 2)⁻¹ * ((t ^ 2)⁻¹ *
          exp (-(euclideanDistSq x / 4 / t))))
        (Ioi (0 : ℝ)) :=
    hint.const_mul _
  refine hint'.congr_fun (fun t ht => ?_) measurableSet_Ioi
  exact (euclideanHeatKernel4_eq_timeMajorant ht x).symm

/-- The exact Bessel-time representation of the four-dimensional
principal singularity.  This fixes the coefficient `1/(4π²)` appearing
in the improved part of (4.1). -/
theorem integral_euclideanHeatKernel4 {x : R4}
    (hx : euclideanDistSq x ≠ 0) :
    ∫ t in Ioi (0 : ℝ), euclideanHeatKernel4 t x =
      laplaceFundamental4 x := by
  have hs : 0 < euclideanDistSq x :=
    lt_of_le_of_ne (euclideanDistSq_nonneg x) (Ne.symm hx)
  have ha : 0 < euclideanDistSq x / 4 := by positivity
  calc
    ∫ t in Ioi (0 : ℝ), euclideanHeatKernel4 t x
        = ∫ t in Ioi (0 : ℝ),
            (16 * π ^ 2)⁻¹ *
              ((t ^ 2)⁻¹ *
                exp (-(euclideanDistSq x / 4 / t))) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          exact euclideanHeatKernel4_eq_timeMajorant ht x
    _ = (16 * π ^ 2)⁻¹ * (euclideanDistSq x / 4)⁻¹ := by
          rw [integral_const_mul, integral_inv_sq_exp ha]
    _ = laplaceFundamental4 x := by
          unfold laplaceFundamental4
          field_simp
          ring

/-- The first-derivative time integral:
`∫₀∞ t⁻³ exp (-a/t) dt = a⁻²`. -/
theorem integral_inv_cube_exp {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), (t ^ 3)⁻¹ * exp (-(a / t)) = a⁻¹ ^ 2 := by
  calc
    ∫ t in Ioi (0 : ℝ), (t ^ 3)⁻¹ * exp (-(a / t))
        = ∫ x in Ioi (0 : ℝ),
            (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
              (x ^ (-1 : ℝ) * exp (-(a * x ^ (-1 : ℝ)))) := by
          refine (setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_).symm
          have hx0 : (0 : ℝ) < x := hx
          rw [smul_eq_mul, abs_neg, abs_one, one_mul,
            show ((-1 : ℝ) - 1) = -2 by norm_num,
            Real.rpow_neg hx0.le, Real.rpow_neg_one,
            show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
          field_simp [div_eq_mul_inv]
    _ = ∫ y in Ioi (0 : ℝ), y * exp (-(a * y)) :=
          integral_comp_rpow_Ioi
            (fun y : ℝ => y * exp (-(a * y))) (by norm_num)
    _ = a⁻¹ ^ 2 := by
          have hgamma :=
            Real.integral_rpow_mul_exp_neg_mul_Ioi
              (a := (2 : ℝ)) (r := a) (by norm_num) ha
          calc
            ∫ y in Ioi (0 : ℝ), y * exp (-(a * y))
                = ∫ y in Ioi (0 : ℝ),
                    y ^ ((2 : ℝ) - 1) * exp (-(a * y)) := by
                  apply setIntegral_congr_fun measurableSet_Ioi
                  intro y hy
                  change y * exp (-(a * y)) =
                    y ^ ((2 : ℝ) - 1) * exp (-(a * y))
                  rw [show ((2 : ℝ) - 1) = 1 by norm_num, Real.rpow_one]
            _ = (1 / a) ^ (2 : ℝ) * Real.Gamma (2 : ℝ) := hgamma
            _ = a⁻¹ ^ 2 := by
                  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
                    Real.rpow_natCast]
                  norm_num [div_eq_mul_inv]

/-- The second-derivative time integral:
`∫₀∞ t⁻⁴ exp (-a/t) dt = 2a⁻³`. -/
theorem integral_inv_fourth_exp {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), (t ^ 4)⁻¹ * exp (-(a / t)) =
      2 * a⁻¹ ^ 3 := by
  calc
    ∫ t in Ioi (0 : ℝ), (t ^ 4)⁻¹ * exp (-(a / t))
        = ∫ x in Ioi (0 : ℝ),
            (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
              ((x ^ (-1 : ℝ)) ^ 2 *
                exp (-(a * x ^ (-1 : ℝ)))) := by
          refine (setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_).symm
          have hx0 : (0 : ℝ) < x := hx
          rw [smul_eq_mul, abs_neg, abs_one, one_mul,
            show ((-1 : ℝ) - 1) = -2 by norm_num,
            Real.rpow_neg hx0.le, Real.rpow_neg_one,
            show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
          field_simp [div_eq_mul_inv]
    _ = ∫ y in Ioi (0 : ℝ), y ^ 2 * exp (-(a * y)) :=
          integral_comp_rpow_Ioi
            (fun y : ℝ => y ^ 2 * exp (-(a * y))) (by norm_num)
    _ = 2 * a⁻¹ ^ 3 := by
          have hgamma :=
            Real.integral_rpow_mul_exp_neg_mul_Ioi
              (a := (3 : ℝ)) (r := a) (by norm_num) ha
          calc
            ∫ y in Ioi (0 : ℝ), y ^ 2 * exp (-(a * y))
                = ∫ y in Ioi (0 : ℝ),
                    y ^ ((3 : ℝ) - 1) * exp (-(a * y)) := by
                  apply setIntegral_congr_fun measurableSet_Ioi
                  intro y hy
                  change y ^ 2 * exp (-(a * y)) =
                    y ^ ((3 : ℝ) - 1) * exp (-(a * y))
                  rw [show ((3 : ℝ) - 1) = 2 by norm_num,
                    show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
                    Real.rpow_natCast]
            _ = (1 / a) ^ (3 : ℝ) * Real.Gamma (3 : ℝ) := hgamma
            _ = 2 * a⁻¹ ^ 3 := by
                  rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num,
                    Real.rpow_natCast]
                  norm_num [div_eq_mul_inv]
                  ring

/-- Absolute integrability of the first-derivative time majorant.  This is
the hypothesis needed to exchange a first spatial derivative with the
Bessel-potential time integral. -/
theorem integrableOn_inv_cube_exp {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t => (t ^ 3)⁻¹ * exp (-(a / t)))
      (Ioi (0 : ℝ)) := by
  have hbase :
      IntegrableOn (fun y : ℝ => y ^ (1 : ℝ) *
        exp (-a * y ^ (1 : ℝ))) (Ioi (0 : ℝ)) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (1 : ℝ)) (b := a)
      (by norm_num) (by norm_num) ha
  have hbase' :
      IntegrableOn (fun y : ℝ => y * exp (-(a * y)))
        (Ioi (0 : ℝ)) := by
    simpa [Real.rpow_one] using hbase
  have hsubst :=
    (integrableOn_Ioi_comp_rpow_iff
      (fun y : ℝ => y * exp (-(a * y)))
      (p := (-1 : ℝ)) (by norm_num)).mpr hbase'
  refine hsubst.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := hx
  simp only [smul_eq_mul]
  rw [abs_neg, abs_one, one_mul,
    show ((-1 : ℝ) - 1) = -2 by norm_num,
    Real.rpow_neg hx0.le, Real.rpow_neg_one,
    show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  field_simp [div_eq_mul_inv]

/-- Absolute integrability of the second-derivative time majorant. -/
theorem integrableOn_inv_fourth_exp {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t => (t ^ 4)⁻¹ * exp (-(a / t)))
      (Ioi (0 : ℝ)) := by
  have hbase :
      IntegrableOn (fun y : ℝ => y ^ (2 : ℝ) *
        exp (-a * y ^ (1 : ℝ))) (Ioi (0 : ℝ)) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (2 : ℝ)) (b := a)
      (by norm_num) (by norm_num) ha
  have hbase' :
      IntegrableOn (fun y : ℝ => y ^ 2 * exp (-(a * y)))
        (Ioi (0 : ℝ)) := by
    refine hbase.congr_fun (fun y hy => ?_) measurableSet_Ioi
    change y ^ (2 : ℝ) * exp (-a * y ^ (1 : ℝ)) =
      y ^ (2 : ℕ) * exp (-(a * y))
    rw [Real.rpow_one,
      show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    rw [neg_mul]
  have hsubst :=
    (integrableOn_Ioi_comp_rpow_iff
      (fun y : ℝ => y ^ 2 * exp (-(a * y)))
      (p := (-1 : ℝ)) (by norm_num)).mpr hbase'
  refine hsubst.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := hx
  simp only [smul_eq_mul]
  rw [abs_neg, abs_one, one_mul,
    show ((-1 : ℝ) - 1) = -2 by norm_num,
    Real.rpow_neg hx0.le, Real.rpow_neg_one,
    show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  field_simp [div_eq_mul_inv]

end

end Anderson4D
