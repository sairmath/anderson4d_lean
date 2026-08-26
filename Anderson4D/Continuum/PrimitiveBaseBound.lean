import Anderson4D.Continuum.PeriodizedCovariance
import Anderson4D.Continuum.PrimitiveBase

/-!
# Analytic bounds at the first primitive order

The exact `n = 1` formulas from `PrimitiveBase` are closed here using the
periodized covariance estimates.  This isolates the base case of paper §5
from the Hepp-tree argument needed at higher orders.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- Squaring the logarithmically scaled coupling removes the square root. -/
theorem lamEps_sq {lam ε : ℝ} (hlog : 0 < |Real.log ε|) :
    lamEps lam ε ^ 2 = lam ^ 2 / |Real.log ε| := by
  unfold lamEps
  rw [div_pow, Real.sq_sqrt hlog.le]

/-- Exact all-order coupling ledger used throughout Propositions 4.1 and
3.5: every pair of noise factors contributes one power of
`|log ε|⁻¹`. -/
theorem abs_lamEps_even_pow {lam ε : ℝ} (n : ℕ)
    (hlog : 0 < |Real.log ε|) :
    |lamEps lam ε| ^ (2 * n) =
      lam ^ (2 * n) / |Real.log ε| ^ n := by
  calc
    |lamEps lam ε| ^ (2 * n) =
        (|lamEps lam ε| ^ 2) ^ n := by rw [pow_mul]
    _ = (lamEps lam ε ^ 2) ^ n := by rw [sq_abs]
    _ = (lam ^ 2 / |Real.log ε|) ^ n := by
      rw [lamEps_sq hlog]
    _ = lam ^ (2 * n) / |Real.log ε| ^ n := by
      rw [div_pow, pow_mul]

/-- The ordinary `n = 1` kernel is controlled by the local term in (4.3).
The covariance constant and the support radius remain explicit. -/
theorem primitiveKernelDiff_one_le_local
    (ρ : SmoothCutoff) {lam ε Cη C supportConstant : ℝ}
    (hε : 0 < ε) (hlog : 0 < |Real.log ε|)
    (heta : ∀ z : T4,
      ρ.etaEpsT4 ε z ≤ ε⁻¹ ^ (dim : ℕ) * Cη)
    (hC : Cη ≤ C ^ 2)
    (hsupport : 4 * ρ.radius ≤ supportConstant)
    (G : Fin 1 → T4 → ℝ)
    (hG : ∀ z, |G 0 z| ≤ invSqKer z) (z : T4) :
    |primitiveKernelDiff ρ lam ε 1 (by omega) G z| ≤
      (C * lam) ^ 2 *
        (((ε⁻¹) ^ 4 / |Real.log ε|) * invSqKer z *
          primitiveSupportIndicator supportConstant ε z) := by
  rw [primitiveKernelDiff, primitiveKernel_one, sub_zero]
  by_cases hηzero : ρ.etaEpsT4 ε z = 0
  · simp only [hηzero, mul_zero, abs_zero]
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg
        (mul_nonneg (div_nonneg (by positivity) hlog.le)
          (invSqKer_nonneg z))
        (primitiveSupportIndicator_nonneg supportConstant ε z))
  have hηnonneg := ρ.etaEpsT4_nonneg ε z
  have hsupport0 :=
    ρ.torusDistSq_le_support_of_etaEpsT4_ne_zero hε hηzero
  have hsquares :
      (4 * ρ.radius * ε) ^ 2 ≤ (supportConstant * ε) ^ 2 := by
    exact pow_le_pow_left₀
      (mul_nonneg (by nlinarith [ρ.radius_pos]) hε.le)
      (mul_le_mul_of_nonneg_right hsupport hε.le) 2
  have hind :
      primitiveSupportIndicator supportConstant ε z = 1 :=
    primitiveSupportIndicator_eq_one (hsupport0.trans hsquares)
  have hdim : (dim : ℕ) = 4 := rfl
  have hη :
      ρ.etaEpsT4 ε z ≤ (ε⁻¹) ^ 4 * Cη := by
    simpa [hdim] using heta z
  have hscaled :
      |G 0 z| * ρ.etaEpsT4 ε z ≤
        invSqKer z * ((ε⁻¹) ^ 4 * Cη) :=
    mul_le_mul (hG z) hη hηnonneg (invSqKer_nonneg z)
  have hcoupling : 0 ≤ lamEps lam ε ^ 2 := sq_nonneg _
  calc
    |lamEps lam ε ^ 2 * (G 0 z * ρ.etaEpsT4 ε z)| =
        lamEps lam ε ^ 2 *
          (|G 0 z| * ρ.etaEpsT4 ε z) := by
            rw [abs_mul, abs_of_nonneg hcoupling, abs_mul,
              abs_of_nonneg hηnonneg]
    _ ≤ lamEps lam ε ^ 2 *
          (invSqKer z * ((ε⁻¹) ^ 4 * Cη)) :=
      mul_le_mul_of_nonneg_left hscaled hcoupling
    _ = (lam ^ 2 / |Real.log ε| * invSqKer z *
          (ε⁻¹) ^ 4) * Cη := by
      rw [lamEps_sq hlog]
      ring
    _ ≤ (lam ^ 2 / |Real.log ε| * invSqKer z *
          (ε⁻¹) ^ 4) * C ^ 2 := by
      exact mul_le_mul_of_nonneg_left hC
        (mul_nonneg
          (mul_nonneg (div_nonneg (sq_nonneg _) hlog.le)
            (invSqKer_nonneg z))
          (by positivity))
    _ = (C * lam) ^ 2 *
        (((ε⁻¹) ^ 4 / |Real.log ε|) * invSqKer z *
          primitiveSupportIndicator supportConstant ε z) := by
      rw [hind]
      ring

/-- The inserted `n = 1` kernel is controlled by the local term in (4.4).
The additional factor is paid for by the explicit covariance support. -/
theorem primitiveKernelInsertedDiff_one_le_local
    (ρ : SmoothCutoff) {lam ε Cη C supportConstant : ℝ}
    (hε : 0 < ε) (hlog : 0 < |Real.log ε|)
    (heta : ∀ z : T4,
      ρ.etaEpsT4 ε z ≤ ε⁻¹ ^ (dim : ℕ) * Cη)
    (hC : Cη * (1 + supportConstant ^ 2) ≤ C ^ 2)
    (hsupport : 4 * ρ.radius ≤ supportConstant)
    (G : Fin 1 → T4 → ℝ)
    (hG : ∀ z, |G 0 z| ≤ invSqKer z) (z : T4) :
    |primitiveKernelInsertedDiff ρ lam ε 1 (by omega) G z| ≤
      (C * lam) ^ 2 *
        (((ε⁻¹) ^ 2 / |Real.log ε|) * invSqKer z *
          primitiveSupportIndicator supportConstant ε z) := by
  rw [primitiveKernelInsertedDiff, primitiveKernelInserted_one, sub_zero]
  by_cases hηzero : ρ.etaEpsT4 ε z = 0
  · simp only [hηzero, mul_zero, abs_zero]
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg
        (mul_nonneg (div_nonneg (by positivity) hlog.le)
          (invSqKer_nonneg z))
        (primitiveSupportIndicator_nonneg supportConstant ε z))
  have hηnonneg := ρ.etaEpsT4_nonneg ε z
  have hsupport0 :=
    ρ.torusDistSq_le_support_of_etaEpsT4_ne_zero hε hηzero
  have hsquares :
      (4 * ρ.radius * ε) ^ 2 ≤ (supportConstant * ε) ^ 2 := by
    exact pow_le_pow_left₀
      (mul_nonneg (by nlinarith [ρ.radius_pos]) hε.le)
      (mul_le_mul_of_nonneg_right hsupport hε.le) 2
  have hdist : torusDistSq z ≤ (supportConstant * ε) ^ 2 :=
    hsupport0.trans hsquares
  have hind :
      primitiveSupportIndicator supportConstant ε z = 1 :=
    primitiveSupportIndicator_eq_one hdist
  have hfactor :
      ε ^ 2 + torusDistSq z ≤
        (1 + supportConstant ^ 2) * ε ^ 2 := by
    calc
      ε ^ 2 + torusDistSq z ≤
          ε ^ 2 + (supportConstant * ε) ^ 2 :=
        add_le_add le_rfl hdist
      _ = (1 + supportConstant ^ 2) * ε ^ 2 := by ring
  have hfactor_nonneg :
      0 ≤ ε ^ 2 + torusDistSq z :=
    add_nonneg (sq_nonneg ε) (torusDistSq_nonneg z)
  have hdim : (dim : ℕ) = 4 := rfl
  have hη :
      ρ.etaEpsT4 ε z ≤ (ε⁻¹) ^ 4 * Cη := by
    simpa [hdim] using heta z
  have hproduct :
      (ε ^ 2 + torusDistSq z) *
          (|G 0 z| * ρ.etaEpsT4 ε z) ≤
        ((1 + supportConstant ^ 2) * ε ^ 2) *
          (invSqKer z * ((ε⁻¹) ^ 4 * Cη)) := by
    exact mul_le_mul hfactor
      (mul_le_mul (hG z) hη hηnonneg (invSqKer_nonneg z))
      (mul_nonneg (abs_nonneg _) hηnonneg)
      (mul_nonneg
        (add_nonneg zero_le_one (sq_nonneg supportConstant))
        (sq_nonneg ε))
  have hcoupling : 0 ≤ lamEps lam ε ^ 2 := sq_nonneg _
  calc
    |lamEps lam ε ^ 2 *
        ((ε ^ 2 + torusDistSq z) *
          (G 0 z * ρ.etaEpsT4 ε z))| =
        lamEps lam ε ^ 2 *
          ((ε ^ 2 + torusDistSq z) *
            (|G 0 z| * ρ.etaEpsT4 ε z)) := by
      rw [abs_mul, abs_of_nonneg hcoupling, abs_mul,
        abs_of_nonneg hfactor_nonneg, abs_mul,
        abs_of_nonneg hηnonneg]
    _ ≤ lamEps lam ε ^ 2 *
        (((1 + supportConstant ^ 2) * ε ^ 2) *
          (invSqKer z * ((ε⁻¹) ^ 4 * Cη))) :=
      mul_le_mul_of_nonneg_left hproduct hcoupling
    _ = (lam ^ 2 / |Real.log ε| * invSqKer z *
          (ε⁻¹) ^ 2) *
        (Cη * (1 + supportConstant ^ 2)) := by
      rw [lamEps_sq hlog]
      field_simp [hε.ne']
    _ ≤ (lam ^ 2 / |Real.log ε| * invSqKer z *
          (ε⁻¹) ^ 2) * C ^ 2 := by
      exact mul_le_mul_of_nonneg_left hC
        (mul_nonneg
          (mul_nonneg (div_nonneg (sq_nonneg _) hlog.le)
            (invSqKer_nonneg z))
          (by positivity))
    _ = (C * lam) ^ 2 *
        (((ε⁻¹) ^ 2 / |Real.log ε|) * invSqKer z *
          primitiveSupportIndicator supportConstant ε z) := by
      rw [hind]
      ring

/-- The two base-order local terms imply the full (4.3)--(4.4)
majorants, since their long-range terms are nonnegative. -/
theorem primitiveKernelBounds_one
    (ρ : SmoothCutoff) {lam ε Cη C supportConstant : ℝ}
    (hε : 0 < ε) (_hε1 : ε ≤ 1) (hlog : 0 < |Real.log ε|)
    (hlam : 0 ≤ lam) (hCnonneg : 0 ≤ C)
    (heta : ∀ z : T4,
      ρ.etaEpsT4 ε z ≤ ε⁻¹ ^ (dim : ℕ) * Cη)
    (hCordinary : Cη ≤ C ^ 2)
    (hCinserted : Cη * (1 + supportConstant ^ 2) ≤ C ^ 2)
    (hsupport : 4 * ρ.radius ≤ supportConstant)
    (G : Fin 1 → T4 → ℝ)
    (hG : ∀ z, |G 0 z| ≤ invSqKer z) :
    PrimitiveKernelBounds ρ lam ε 1 (by omega) G supportConstant C := by
  intro z
  constructor
  · refine (primitiveKernelDiff_one_le_local ρ hε hlog heta
      hCordinary hsupport G hG z).trans ?_
    unfold primitiveKernelMajorant
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right
        (mul_nonneg
          (div_nonneg zero_le_one (sq_nonneg _))
          (pow_nonneg
            (inv_nonneg.mpr
              (add_nonneg (torusDistSq_nonneg z) (sq_nonneg ε))) 3)))
      (pow_nonneg (mul_nonneg hCnonneg hlam) _)
  · refine (primitiveKernelInsertedDiff_one_le_local ρ hε hlog
      heta hCinserted hsupport G hG z).trans ?_
    unfold primitiveInsertedMajorant
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right
        (mul_nonneg
          (div_nonneg zero_le_one (sq_nonneg _))
          (pow_nonneg
            (inv_nonneg.mpr
              (add_nonneg (torusDistSq_nonneg z) (sq_nonneg ε))) 2)))
      (pow_nonneg (mul_nonneg hCnonneg hlam) _)

end

end Anderson4D
