import Anderson4D.Parametrix.FredholmCoefficientBridge
import Anderson4D.Continuum.LogAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Vanishing of the Fredholm fixed-mode error

The one-sided operator comparison gives the normalized fixed-mode error

`|T⁴| · |λ_ε⁻¹| · ε¹²`.

Since `λ_ε = λ / sqrt |log ε|`, this is a constant multiple of
`sqrt |log ε| · ε¹²` and therefore vanishes as `ε ↓ 0`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter Set
open scoped Topology

/-- The scalar error in the Fredholm coefficient bridge. -/
def fredholmModeErrorScale (lam ε : ℝ) : ℝ :=
  ‖(paperTorusVolume : ℂ) *
      (lamEps lam ε : ℂ)⁻¹‖ * ε ^ 12

theorem fredholmModeErrorScale_nonneg (lam ε : ℝ) :
    0 ≤ fredholmModeErrorScale lam ε := by
  unfold fredholmModeErrorScale
  positivity

/-- A polynomial beats one absolute logarithm at the positive side of
zero. -/
theorem tendsto_abs_log_mul_pow_twelve_nhdsGT_zero :
    Tendsto
      (fun ε : ℝ => |Real.log ε| * ε ^ 12)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  have h :=
    (tendsto_log_mul_rpow_nhdsGT_zero
      (r := ((12 : ℕ) : ℝ)) (by norm_num)).neg
  have h' :
      Tendsto
        (fun ε : ℝ =>
          -(Real.log ε * ε ^ ((12 : ℕ) : ℝ)))
        (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    simpa using h
  refine h'.congr' ?_
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_smallScale_le zero_lt_one] with ε hε hεle
  have hlog : Real.log ε ≤ 0 :=
    Real.log_nonpos hε.le hεle
  rw [Real.rpow_natCast]
  simp only [abs_of_nonpos hlog, neg_mul]

/-- The square-root logarithmic loss is also absorbed by `ε¹²`. -/
theorem tendsto_sqrt_abs_log_mul_pow_twelve_nhdsGT_zero :
    Tendsto
      (fun ε : ℝ => Real.sqrt |Real.log ε| * ε ^ 12)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  apply squeeze_zero'
    (Eventually.of_forall fun ε => by positivity)
    _ tendsto_abs_log_mul_pow_twelve_nhdsGT_zero
  filter_upwards [eventually_one_le_abs_log] with ε hlog
  exact mul_le_mul_of_nonneg_right
    (Real.sqrt_le_self_iff.mpr (Or.inr hlog))
    (by positivity)

/-- For every positive coupling, the exact normalized Fredholm
fixed-mode error tends to zero. -/
theorem tendsto_fredholmModeErrorScale_nhdsGT_zero
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto
      (fredholmModeErrorScale lam)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  have hbase :=
    Tendsto.const_mul
      (paperTorusVolume / lam)
      tendsto_sqrt_abs_log_mul_pow_twelve_nhdsGT_zero
  have hscaled :
      Tendsto
        (fun ε : ℝ =>
          (paperTorusVolume / lam) *
            (Real.sqrt |Real.log ε| * ε ^ 12))
        (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    simpa only [mul_zero] using hbase
  refine hscaled.congr' ?_
  filter_upwards [eventually_abs_log_pos] with ε hlog
  have hsqrt : 0 < Real.sqrt |Real.log ε| :=
    Real.sqrt_pos.2 hlog
  have hlamEps : 0 < lamEps lam ε := by
    unfold lamEps
    exact div_pos hlam hsqrt
  unfold fredholmModeErrorScale
  rw [norm_mul, norm_inv]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos paperTorusVolume_pos,
    abs_of_pos hlamEps]
  unfold lamEps
  field_simp [hlam.ne', hsqrt.ne']

/-- The finite-family error used by the Cramér--Wold test is
nonnegative. -/
theorem sum_norm_mul_fredholmModeErrorScale_nonneg
    {s : ℕ} (c : Fin s → ℂ) (lam ε : ℝ) :
    0 ≤ ∑ j : Fin s, ‖c j‖ *
      fredholmModeErrorScale lam ε :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (norm_nonneg _)
      (fredholmModeErrorScale_nonneg lam ε)

/-- A fixed finite coefficient family preserves the vanishing
Fredholm error. -/
theorem tendsto_sum_norm_mul_fredholmModeErrorScale_nhdsGT_zero
    {s : ℕ} (c : Fin s → ℂ)
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto
      (fun ε : ℝ =>
        ∑ j : Fin s, ‖c j‖ *
          fredholmModeErrorScale lam ε)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  have h :=
    Tendsto.const_mul
      (∑ j : Fin s, ‖c j‖)
      (tendsto_fredholmModeErrorScale_nhdsGT_zero hlam)
  simpa only [mul_zero, Finset.sum_mul] using h

end

end Anderson4D
