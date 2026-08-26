import Anderson4D.DetParametrix.Paper42_Moment.R324CompleteTerminalHeadBound
import Anderson4D.DetParametrix.Paper42_Moment.R324PrimitiveIterationClosure

/-!
# Absorbing the complete nested-cross order ledger

The proper shells contribute `(D λ)^(2p)` and the final complete block
contributes one paper-volume factor times the order-`t` inserted majorant.
This file absorbs both into one order-`p+t` inserted majorant with a single
named base constant.  The proof is purely numerical and does not change the
order in which any physical integral or finite pairing sum is evaluated.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- A convenient base large enough to absorb both head constants and the
single translation-volume cost. -/
def r324CompleteAbsorbedBase (D C : ℝ) : ℝ :=
  max 1 D * max 1 C * max 1 ((2 * Real.pi) ^ (dim : ℕ))

theorem r324CompleteAbsorbedBase_pos (D C : ℝ) :
    0 < r324CompleteAbsorbedBase D C := by
  unfold r324CompleteAbsorbedBase
  positivity

private theorem r324_complete_base_power_le
    {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (p t : ℕ) (htotal : 1 ≤ p + t) :
    D ^ (2 * p) * C ^ (2 * t) *
        (2 * Real.pi) ^ (dim : ℕ) ≤
      r324CompleteAbsorbedBase D C ^ (2 * (p + t)) := by
  let d := max 1 D
  let c := max 1 C
  let V := (2 * Real.pi) ^ (dim : ℕ)
  let v := max 1 V
  have hd1 : (1 : ℝ) ≤ d := le_max_left _ _
  have hc1 : (1 : ℝ) ≤ c := le_max_left _ _
  have hV0 : 0 ≤ V := by positivity
  have hv1 : (1 : ℝ) ≤ v := le_max_left _ _
  have hDp : D ^ (2 * p) ≤ d ^ (2 * (p + t)) := by
    calc
      D ^ (2 * p) ≤ d ^ (2 * p) :=
        pow_le_pow_left₀ hD (le_max_right _ _) _
      _ ≤ d ^ (2 * (p + t)) :=
        pow_le_pow_right₀ hd1 (by omega)
  have hCt : C ^ (2 * t) ≤ c ^ (2 * (p + t)) := by
    calc
      C ^ (2 * t) ≤ c ^ (2 * t) :=
        pow_le_pow_left₀ hC (le_max_right _ _) _
      _ ≤ c ^ (2 * (p + t)) :=
        pow_le_pow_right₀ hc1 (by omega)
  have hV : V ≤ v ^ (2 * (p + t)) := by
    calc
      V ≤ v := le_max_right _ _
      _ = v ^ (1 : ℕ) := (pow_one v).symm
      _ ≤ v ^ (2 * (p + t)) :=
        pow_le_pow_right₀ hv1 (by omega)
  have hDC :
      D ^ (2 * p) * C ^ (2 * t) ≤
        d ^ (2 * (p + t)) * c ^ (2 * (p + t)) :=
    mul_le_mul hDp hCt (pow_nonneg hC _)
      (pow_nonneg (zero_le_one.trans hd1) _)
  calc
    D ^ (2 * p) * C ^ (2 * t) * V ≤
        (d ^ (2 * (p + t)) * c ^ (2 * (p + t))) *
          v ^ (2 * (p + t)) :=
      mul_le_mul hDC hV hV0
        (mul_nonneg (pow_nonneg (zero_le_one.trans hd1) _)
          (pow_nonneg (zero_le_one.trans hc1) _))
    _ = (d * c * v) ^ (2 * (p + t)) := by
      rw [mul_pow, mul_pow]
    _ = r324CompleteAbsorbedBase D C ^ (2 * (p + t)) := rfl

/-- Proper-prefix cost times the final order-`t` majorant is pointwise
dominated by the single majorant at the total order. -/
theorem r324_complete_prefix_mul_terminalMajorant_le
    {D C lam ε supportConstant : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (p t : ℕ) (htotal : 1 ≤ p + t) (z : T4) :
    (D * lam) ^ (2 * p) *
        (2 * Real.pi) ^ (dim : ℕ) *
        primitiveInsertedMajorant
          C lam ε supportConstant t z ≤
      primitiveInsertedMajorant
        (r324CompleteAbsorbedBase D C) lam ε supportConstant
          (p + t) z := by
  let Q : ℝ :=
    (((ε⁻¹) ^ 2 / |Real.log ε|) * invSqKer z *
        primitiveSupportIndicator supportConstant ε z +
      (1 / |Real.log ε| ^ 2) *
        (torusDistSq z + ε ^ 2)⁻¹ ^ 2)
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    apply add_nonneg
    · exact mul_nonneg
        (mul_nonneg (div_nonneg (by positivity) (abs_nonneg _))
          (invSqKer_nonneg z))
        (primitiveSupportIndicator_nonneg supportConstant ε z)
    · exact mul_nonneg (div_nonneg zero_le_one (sq_nonneg _))
        (pow_nonneg
          (inv_nonneg.mpr
            (add_nonneg (torusDistSq_nonneg z) (sq_nonneg ε))) 2)
  have hbase := r324_complete_base_power_le hD hC p t htotal
  have hlamPow : 0 ≤ lam ^ (2 * (p + t)) := pow_nonneg hlam _
  have hcoef :
      (D * lam) ^ (2 * p) *
          (2 * Real.pi) ^ (dim : ℕ) *
          (C * lam) ^ (2 * t) ≤
        (r324CompleteAbsorbedBase D C * lam) ^
          (2 * (p + t)) := by
    rw [mul_pow D lam, mul_pow C lam,
      mul_pow (r324CompleteAbsorbedBase D C) lam]
    rw [show 2 * (p + t) = 2 * p + 2 * t by omega, pow_add]
    calc
      D ^ (2 * p) * lam ^ (2 * p) *
            (2 * Real.pi) ^ (dim : ℕ) *
            (C ^ (2 * t) * lam ^ (2 * t)) =
          (D ^ (2 * p) * C ^ (2 * t) *
              (2 * Real.pi) ^ (dim : ℕ)) *
            lam ^ (2 * (p + t)) := by ring
      _ ≤ r324CompleteAbsorbedBase D C ^ (2 * (p + t)) *
            lam ^ (2 * (p + t)) :=
        mul_le_mul_of_nonneg_right hbase hlamPow
      _ = _ := by ring
  unfold primitiveInsertedMajorant
  have hmul := mul_le_mul_of_nonneg_right hcoef hQ
  simpa only [Q, mul_assoc] using hmul

/-- Integrated form used by the complete nested budget iterator. -/
theorem r324_complete_prefix_mul_terminalIntegral_le
    {D C lam ε supportConstant : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hε : 0 < ε)
    (p t : ℕ) (htotal : 1 ≤ p + t) :
    (D * lam) ^ (2 * p) *
        ((2 * Real.pi) ^ (dim : ℕ) *
          ∫ z, primitiveInsertedMajorant
            C lam ε supportConstant t z ∂paperMeasure) ≤
      ∫ z, primitiveInsertedMajorant
        (r324CompleteAbsorbedBase D C) lam ε supportConstant
          (p + t) z ∂paperMeasure := by
  have hleft : Integrable
      (fun z =>
        (D * lam) ^ (2 * p) *
          (2 * Real.pi) ^ (dim : ℕ) *
          primitiveInsertedMajorant
            C lam ε supportConstant t z) paperMeasure :=
    (integrable_primitiveInsertedMajorant
      C lam ε supportConstant t hε).const_mul _
  have hright := integrable_primitiveInsertedMajorant
    (r324CompleteAbsorbedBase D C) lam ε supportConstant
      (p + t) hε
  calc
    (D * lam) ^ (2 * p) *
          ((2 * Real.pi) ^ (dim : ℕ) *
            ∫ z, primitiveInsertedMajorant
              C lam ε supportConstant t z ∂paperMeasure) =
        ((D * lam) ^ (2 * p) *
          (2 * Real.pi) ^ (dim : ℕ)) *
            ∫ z, primitiveInsertedMajorant
              C lam ε supportConstant t z ∂paperMeasure := by ring
    _ = ∫ z,
          ((D * lam) ^ (2 * p) *
            (2 * Real.pi) ^ (dim : ℕ)) *
            primitiveInsertedMajorant
              C lam ε supportConstant t z
          ∂paperMeasure := by
      rw [integral_const_mul]
    _ =
        ∫ z,
          (D * lam) ^ (2 * p) *
            (2 * Real.pi) ^ (dim : ℕ) *
            primitiveInsertedMajorant
              C lam ε supportConstant t z
          ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with z
      ring
    _ ≤ _ := integral_mono hleft hright fun z =>
      r324_complete_prefix_mul_terminalMajorant_le
        hD hC hlam p t htotal z

end

end Anderson4D
