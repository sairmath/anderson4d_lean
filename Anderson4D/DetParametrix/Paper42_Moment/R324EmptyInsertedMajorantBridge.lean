import Anderson4D.DetParametrix.Core.MomentReduction

/-!
# The ordinary-to-inserted majorant bridge for empty residual R-324 fibres

In the full/full branch of paper Section 4.2 Step 1, no residual primitive
block remains.  The surviving quadratic gap must therefore be used directly
against the ordinary Proposition 4.1 majorant.  This file records the honest
numerical comparison: the support term costs `supportConstant²`, while the
regularized term costs `1`.

This is a comparison of the two explicit nonnegative majorants.  It does not
assert a pointwise comparison between either signed primitive kernel.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- Multiplication by the surviving squared gap converts the ordinary
Proposition 4.1 majorant into the inserted majorant, at the sharp uniform
factor `max 1 supportConstant²`.

No sign assumptions on `C` or `lam` are needed because their common exponent
is even.  The degenerate scale `ε = 0` is also valid algebraically (both
majorants vanish under Lean's totalized inverse convention). -/
theorem
    torusDistSq_mul_primitiveKernelMajorant_le_max_one_sq_mul_inserted
    (C lam ε supportConstant : ℝ) (n : ℕ) (z : T4) :
    torusDistSq z *
        primitiveKernelMajorant C lam ε supportConstant n z ≤
      max 1 (supportConstant ^ 2) *
        primitiveInsertedMajorant C lam ε supportConstant n z := by
  by_cases hε : ε = 0
  · subst ε
    simp [primitiveKernelMajorant, primitiveInsertedMajorant]
  have hεsq : 0 < ε ^ 2 := sq_pos_of_ne_zero hε
  have hd : 0 ≤ torusDistSq z := torusDistSq_nonneg z
  have hD : 0 < torusDistSq z + ε ^ 2 :=
    add_pos_of_nonneg_of_pos hd hεsq
  have hA : 0 ≤ (C * lam) ^ (2 * n) :=
    (even_two_mul n).pow_nonneg (C * lam)
  have hFone : 1 ≤ max 1 (supportConstant ^ 2) :=
    le_max_left _ _
  have hFsupport :
      supportConstant ^ 2 ≤ max 1 (supportConstant ^ 2) :=
    le_max_right _ _
  have hlocalInserted :
      0 ≤
        ((ε⁻¹) ^ 2 / |Real.log ε|) * invSqKer z *
          primitiveSupportIndicator supportConstant ε z := by
    exact mul_nonneg
      (mul_nonneg
        (div_nonneg (sq_nonneg _) (abs_nonneg _))
        (invSqKer_nonneg z))
      (primitiveSupportIndicator_nonneg supportConstant ε z)
  have hregularInserted :
      0 ≤
        (1 / |Real.log ε| ^ 2) *
          (torusDistSq z + ε ^ 2)⁻¹ ^ 2 := by
    positivity
  have hlocal :
      torusDistSq z *
          (((ε⁻¹) ^ 4 / |Real.log ε|) * invSqKer z *
            primitiveSupportIndicator supportConstant ε z) ≤
        supportConstant ^ 2 *
          (((ε⁻¹) ^ 2 / |Real.log ε|) * invSqKer z *
            primitiveSupportIndicator supportConstant ε z) := by
    by_cases hs :
        torusDistSq z ≤ (supportConstant * ε) ^ 2
    · rw [primitiveSupportIndicator_eq_one hs]
      have hscale :
          torusDistSq z * (ε⁻¹) ^ 4 ≤
            supportConstant ^ 2 * (ε⁻¹) ^ 2 := by
        calc
          torusDistSq z * (ε⁻¹) ^ 4 ≤
              (supportConstant * ε) ^ 2 * (ε⁻¹) ^ 4 :=
            mul_le_mul_of_nonneg_right hs (by positivity)
          _ = supportConstant ^ 2 * (ε⁻¹) ^ 2 := by
            field_simp [hε]
      have hfactor :
          0 ≤ (1 / |Real.log ε|) * invSqKer z := by
        exact mul_nonneg
          (div_nonneg zero_le_one (abs_nonneg _))
          (invSqKer_nonneg z)
      calc
        torusDistSq z *
            (((ε⁻¹) ^ 4 / |Real.log ε|) * invSqKer z * 1) =
            (torusDistSq z * (ε⁻¹) ^ 4) *
              ((1 / |Real.log ε|) * invSqKer z) := by
          ring
        _ ≤
            (supportConstant ^ 2 * (ε⁻¹) ^ 2) *
              ((1 / |Real.log ε|) * invSqKer z) :=
          mul_le_mul_of_nonneg_right hscale hfactor
        _ =
            supportConstant ^ 2 *
              (((ε⁻¹) ^ 2 / |Real.log ε|) * invSqKer z * 1) := by
          ring
    · rw [primitiveSupportIndicator_eq_zero hs]
      norm_num
  have hregular :
      torusDistSq z *
          ((1 / |Real.log ε| ^ 2) *
            (torusDistSq z + ε ^ 2)⁻¹ ^ 3) ≤
        (1 / |Real.log ε| ^ 2) *
          (torusDistSq z + ε ^ 2)⁻¹ ^ 2 := by
    have hcore :
        torusDistSq z *
            (torusDistSq z + ε ^ 2)⁻¹ ^ 3 ≤
          (torusDistSq z + ε ^ 2)⁻¹ ^ 2 := by
      calc
        torusDistSq z *
              (torusDistSq z + ε ^ 2)⁻¹ ^ 3 ≤
            (torusDistSq z + ε ^ 2) *
              (torusDistSq z + ε ^ 2)⁻¹ ^ 3 :=
          mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right (sq_nonneg ε))
            (by positivity)
        _ = (torusDistSq z + ε ^ 2)⁻¹ ^ 2 := by
          field_simp [hD.ne']
    calc
      torusDistSq z *
          ((1 / |Real.log ε| ^ 2) *
            (torusDistSq z + ε ^ 2)⁻¹ ^ 3) =
          (1 / |Real.log ε| ^ 2) *
            (torusDistSq z *
              (torusDistSq z + ε ^ 2)⁻¹ ^ 3) := by
        ring
      _ ≤
          (1 / |Real.log ε| ^ 2) *
            (torusDistSq z + ε ^ 2)⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
  unfold primitiveKernelMajorant primitiveInsertedMajorant
  calc
    torusDistSq z *
        ((C * lam) ^ (2 * n) *
          (((ε⁻¹) ^ 4 / |Real.log ε|) * invSqKer z *
              primitiveSupportIndicator supportConstant ε z +
            (1 / |Real.log ε| ^ 2) *
              (torusDistSq z + ε ^ 2)⁻¹ ^ 3)) =
        (C * lam) ^ (2 * n) *
          (torusDistSq z *
              (((ε⁻¹) ^ 4 / |Real.log ε|) * invSqKer z *
                primitiveSupportIndicator supportConstant ε z) +
            torusDistSq z *
              ((1 / |Real.log ε| ^ 2) *
                (torusDistSq z + ε ^ 2)⁻¹ ^ 3)) := by
      ring
    _ ≤
        (C * lam) ^ (2 * n) *
          (supportConstant ^ 2 *
              (((ε⁻¹) ^ 2 / |Real.log ε|) * invSqKer z *
                primitiveSupportIndicator supportConstant ε z) +
            (1 / |Real.log ε| ^ 2) *
              (torusDistSq z + ε ^ 2)⁻¹ ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hlocal hregular) hA
    _ ≤
        (C * lam) ^ (2 * n) *
          (max 1 (supportConstant ^ 2) *
              (((ε⁻¹) ^ 2 / |Real.log ε|) * invSqKer z *
                primitiveSupportIndicator supportConstant ε z) +
            max 1 (supportConstant ^ 2) *
              ((1 / |Real.log ε| ^ 2) *
                (torusDistSq z + ε ^ 2)⁻¹ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact add_le_add
        (mul_le_mul_of_nonneg_right hFsupport hlocalInserted)
        (by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hFone hregularInserted)
    _ =
        max 1 (supportConstant ^ 2) *
          ((C * lam) ^ (2 * n) *
            (((ε⁻¹) ^ 2 / |Real.log ε|) * invSqKer z *
                primitiveSupportIndicator supportConstant ε z +
              (1 / |Real.log ε| ^ 2) *
                (torusDistSq z + ε ^ 2)⁻¹ ^ 2)) := by
      ring

/-- Integrated form of
`torusDistSq_mul_primitiveKernelMajorant_le_max_one_sq_mul_inserted`.
Positivity of `ε` is required only for the two integrability facts; no
positivity assumption on the coupling parameters is needed. -/
theorem
    integral_torusDistSq_mul_primitiveKernelMajorant_le_max_one_sq_mul_integral_inserted
    (C lam ε supportConstant : ℝ) (n : ℕ)
    (hε : 0 < ε) :
    (∫ z : T4,
        torusDistSq z *
          primitiveKernelMajorant C lam ε supportConstant n z
        ∂paperMeasure) ≤
      max 1 (supportConstant ^ 2) *
        ∫ z : T4,
          primitiveInsertedMajorant C lam ε supportConstant n z
          ∂paperMeasure := by
  let F : ℝ := max 1 (supportConstant ^ 2)
  have hordinary :
      Integrable
        (fun z : T4 =>
          torusDistSq z *
            primitiveKernelMajorant C lam ε supportConstant n z)
        paperMeasure := by
    have hinserted :
        Integrable
          (fun z : T4 =>
            F *
              primitiveInsertedMajorant
                C lam ε supportConstant n z)
          paperMeasure :=
      (integrable_primitiveInsertedMajorant
        C lam ε supportConstant n hε).const_mul F
    have hmeas :
        AEStronglyMeasurable
          (fun z : T4 =>
            torusDistSq z *
              primitiveKernelMajorant C lam ε supportConstant n z)
          paperMeasure :=
      measurable_torusDistSq.aestronglyMeasurable.mul
        (integrable_primitiveKernelMajorant
          C lam ε supportConstant n hε).aestronglyMeasurable
    refine Integrable.mono' hinserted hmeas (.of_forall fun z => ?_)
    have hkernel :
        0 ≤ primitiveKernelMajorant
          C lam ε supportConstant n z := by
      unfold primitiveKernelMajorant
      apply mul_nonneg
      · exact (even_two_mul n).pow_nonneg (C * lam)
      · apply add_nonneg
        · exact mul_nonneg
            (mul_nonneg
              (div_nonneg (by positivity) (abs_nonneg _))
              (invSqKer_nonneg z))
            (primitiveSupportIndicator_nonneg
              supportConstant ε z)
        · exact mul_nonneg
            (div_nonneg zero_le_one (sq_nonneg _))
            (pow_nonneg
              (inv_nonneg.mpr
                (add_nonneg (torusDistSq_nonneg z)
                  (sq_nonneg ε))) 3)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (torusDistSq_nonneg z) hkernel)]
    exact
      torusDistSq_mul_primitiveKernelMajorant_le_max_one_sq_mul_inserted
        C lam ε supportConstant n z
  have hinserted :
      Integrable
        (fun z : T4 =>
          F *
            primitiveInsertedMajorant
              C lam ε supportConstant n z)
        paperMeasure :=
    (integrable_primitiveInsertedMajorant
      C lam ε supportConstant n hε).const_mul F
  calc
    (∫ z : T4,
        torusDistSq z *
          primitiveKernelMajorant C lam ε supportConstant n z
        ∂paperMeasure) ≤
        ∫ z : T4,
          F *
            primitiveInsertedMajorant C lam ε supportConstant n z
          ∂paperMeasure := by
      apply integral_mono hordinary hinserted
      intro z
      exact
        torusDistSq_mul_primitiveKernelMajorant_le_max_one_sq_mul_inserted
          C lam ε supportConstant n z
    _ =
        F *
          ∫ z : T4,
            primitiveInsertedMajorant
              C lam ε supportConstant n z
            ∂paperMeasure := by
      rw [integral_const_mul]
    _ =
        max 1 (supportConstant ^ 2) *
          ∫ z : T4,
            primitiveInsertedMajorant
              C lam ε supportConstant n z
            ∂paperMeasure := by
      rfl

end

end Anderson4D
