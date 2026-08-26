import Anderson4D.Continuum.PrimitiveEstimate

/-!
# Integral bounds for the primitive-kernel majorant

This file records the analytic bridge from the pointwise primitive estimate
(4.3) to the `ε⁻² |log ε|⁻¹` scale used in the deterministic
renormalization estimate (3.22).  Both summands are integrated from proved
continuum estimates:

* the local `|z|⁻²` term uses the four-dimensional ball bound;
* the regularized `(dist² + ε²)⁻³` term uses its exact scaling bound.

No integrability or numerical estimate is supplied as a hypothesis.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set

lemma measurable_primitiveSupportIndicator (supportConstant ε : ℝ) :
    Measurable (primitiveSupportIndicator supportConstant ε) := by
  unfold primitiveSupportIndicator
  exact Measurable.ite
    (measurable_torusDistSq measurableSet_Iic) measurable_const measurable_const

private lemma invSqKer_mul_primitiveSupportIndicator_eq_indicator
    (supportConstant ε : ℝ) :
    (fun z : T4 =>
      invSqKer z * primitiveSupportIndicator supportConstant ε z) =
      {z : T4 |
        torusDistSq z ≤ (supportConstant * ε) ^ 2}.indicator invSqKer := by
  funext z
  by_cases hz : torusDistSq z ≤ (supportConstant * ε) ^ 2
  · rw [primitiveSupportIndicator_eq_one hz,
      Set.indicator_of_mem (show z ∈ {w : T4 |
        torusDistSq w ≤ (supportConstant * ε) ^ 2} from hz)]
    ring
  · rw [primitiveSupportIndicator_eq_zero hz,
      Set.indicator_of_notMem (show z ∉ {w : T4 |
        torusDistSq w ≤ (supportConstant * ε) ^ 2} from hz)]
    ring

theorem integrable_invSqKer_mul_primitiveSupportIndicator
    (supportConstant ε : ℝ) :
    Integrable
      (fun z : T4 =>
        invSqKer z * primitiveSupportIndicator supportConstant ε z)
      paperMeasure := by
  rw [invSqKer_mul_primitiveSupportIndicator_eq_indicator]
  exact integrable_invSqKer.indicator
    (measurable_torusDistSq measurableSet_Iic)

/-- The local summand of (4.3) integrates to the volume scale
`(supportConstant * ε)²`. -/
theorem exists_integral_invSqKer_mul_primitiveSupportIndicator_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ supportConstant ε : ℝ, 0 < supportConstant → 0 < ε →
        ∫ z,
            invSqKer z * primitiveSupportIndicator supportConstant ε z
              ∂paperMeasure
          ≤ C * supportConstant ^ 2 * ε ^ 2 := by
  obtain ⟨C, hC, hball⟩ := setIntegral_invSqKer_ball_le
  refine ⟨C, hC, fun supportConstant ε hs hε => ?_⟩
  rw [invSqKer_mul_primitiveSupportIndicator_eq_indicator]
  rw [MeasureTheory.integral_indicator
    (μ := paperMeasure) (f := invSqKer)
    (s := {z : T4 |
      torusDistSq z ≤ (supportConstant * ε) ^ 2})
    (measurable_torusDistSq measurableSet_Iic)]
  calc
    ∫ z in {z : T4 |
        torusDistSq z ≤ (supportConstant * ε) ^ 2},
        invSqKer z ∂paperMeasure
        ≤ C * (supportConstant * ε) ^ 2 :=
      hball (supportConstant * ε) (mul_pos hs hε)
    _ = C * supportConstant ^ 2 * ε ^ 2 := by ring

/-- The full (4.3) majorant is integrable at every positive scale. -/
theorem integrable_primitiveKernelMajorant
    (C lam ε supportConstant : ℝ) (n : ℕ)
    (hε : 0 < ε) :
    Integrable
      (primitiveKernelMajorant C lam ε supportConstant n)
      paperMeasure := by
  have hlocal :=
    integrable_invSqKer_mul_primitiveSupportIndicator supportConstant ε
  have hreg := integrable_regularizedInvCube ε hε
  have hinside : Integrable
      (fun z : T4 =>
        (((ε⁻¹) ^ 4 / |Real.log ε|) *
            (invSqKer z * primitiveSupportIndicator supportConstant ε z)) +
          (1 / |Real.log ε| ^ 2) * regularizedInvCube ε z)
      paperMeasure :=
    (hlocal.const_mul ((ε⁻¹) ^ 4 / |Real.log ε|)).add
      (hreg.const_mul (1 / |Real.log ε| ^ 2))
  refine (hinside.const_mul ((C * lam) ^ (2 * n))).congr
    (.of_forall fun z => ?_)
  unfold primitiveKernelMajorant regularizedInvCube
  ring

/-- **Integrated primitive majorant.**  If `|log ε| ≥ 1`, integrating
(4.3) loses exactly `ε⁻² |log ε|⁻¹`.  The two universal constants are
chosen once, before every cutoff support radius, scale, coupling, order,
and pointwise constant. -/
theorem exists_integral_primitiveKernelMajorant_le :
    ∃ Cball Creg : ℝ, 0 < Cball ∧ 0 < Creg ∧
      ∀ (C lam ε supportConstant : ℝ) (n : ℕ),
        0 < ε → 0 < supportConstant → 1 ≤ |Real.log ε| →
          ∫ z, primitiveKernelMajorant C lam ε supportConstant n z
              ∂paperMeasure
            ≤ (C * lam) ^ (2 * n) *
              ((Cball * supportConstant ^ 2 + Creg) *
                ε⁻¹ ^ (2 : ℕ) / |Real.log ε|) := by
  obtain ⟨Cball, hCball, hlocal⟩ :=
    exists_integral_invSqKer_mul_primitiveSupportIndicator_le
  obtain ⟨Creg, hCreg, hreg⟩ := integral_regularizedInvCube_le
  refine ⟨Cball, Creg, hCball, hCreg,
    fun C lam ε supportConstant n hε hs hlog => ?_⟩
  have hlogPos : 0 < |Real.log ε| :=
    zero_lt_one.trans_le hlog
  have hlocalInt :=
    hlocal supportConstant ε hs hε
  have hregInt := hreg ε hε
  have hlocalIntegrable :=
    integrable_invSqKer_mul_primitiveSupportIndicator supportConstant ε
  have hregIntegrable := integrable_regularizedInvCube ε hε
  have hpow : 0 ≤ (C * lam) ^ (2 * n) :=
    (even_two_mul n).pow_nonneg (C * lam)
  have hlocalCoeff : 0 ≤ (ε⁻¹) ^ 4 / |Real.log ε| :=
    div_nonneg (by positivity) hlogPos.le
  have hregCoeff : 0 ≤ 1 / |Real.log ε| ^ 2 :=
    div_nonneg zero_le_one (sq_nonneg _)
  have hεInvSq : 0 ≤ ε⁻¹ ^ (2 : ℕ) := sq_nonneg _
  have hlocalScale :
      ((ε⁻¹) ^ 4 / |Real.log ε|) *
          (Cball * supportConstant ^ 2 * ε ^ 2) =
        Cball * supportConstant ^ 2 *
          ε⁻¹ ^ (2 : ℕ) / |Real.log ε| := by
    field_simp [hε.ne', hlogPos.ne']
  have hregScale :
      (1 / |Real.log ε| ^ 2) *
          (Creg * ε⁻¹ ^ (2 : ℕ)) ≤
        Creg * ε⁻¹ ^ (2 : ℕ) / |Real.log ε| := by
    have hCregScale : 0 ≤ Creg * ε⁻¹ ^ (2 : ℕ) :=
      mul_nonneg hCreg.le hεInvSq
    rw [show
      1 / |Real.log ε| ^ 2 * (Creg * ε⁻¹ ^ (2 : ℕ)) =
        (Creg * ε⁻¹ ^ (2 : ℕ)) / |Real.log ε| ^ 2 by ring]
    apply (div_le_div_iff₀ (sq_pos_of_pos hlogPos) hlogPos).2
    have hscale :
        Creg * ε⁻¹ ^ (2 : ℕ) ≤
          (Creg * ε⁻¹ ^ (2 : ℕ)) * |Real.log ε| :=
      le_mul_of_one_le_right hCregScale hlog
    calc
      (Creg * ε⁻¹ ^ (2 : ℕ)) * |Real.log ε| ≤
          ((Creg * ε⁻¹ ^ (2 : ℕ)) * |Real.log ε|) *
            |Real.log ε| :=
        mul_le_mul_of_nonneg_right hscale hlogPos.le
      _ = (Creg * ε⁻¹ ^ (2 : ℕ)) * |Real.log ε| ^ 2 := by ring
  have hintegral :
      (∫ z,
          ((ε⁻¹) ^ 4 / |Real.log ε|) * invSqKer z *
              primitiveSupportIndicator supportConstant ε z +
            (1 / |Real.log ε| ^ 2) *
              (torusDistSq z + ε ^ 2)⁻¹ ^ 3
          ∂paperMeasure) =
        ((ε⁻¹) ^ 4 / |Real.log ε|) *
              ∫ z,
                invSqKer z *
                  primitiveSupportIndicator supportConstant ε z
                ∂paperMeasure +
            (1 / |Real.log ε| ^ 2) *
              ∫ z, regularizedInvCube ε z ∂paperMeasure := by
    calc
      (∫ z,
          ((ε⁻¹) ^ 4 / |Real.log ε|) * invSqKer z *
              primitiveSupportIndicator supportConstant ε z +
            (1 / |Real.log ε| ^ 2) *
              (torusDistSq z + ε ^ 2)⁻¹ ^ 3
          ∂paperMeasure) =
          ∫ z,
            ((ε⁻¹) ^ 4 / |Real.log ε|) *
                (invSqKer z *
                  primitiveSupportIndicator supportConstant ε z) +
              (1 / |Real.log ε| ^ 2) * regularizedInvCube ε z
            ∂paperMeasure := by
              apply integral_congr_ae
              filter_upwards with z
              unfold regularizedInvCube
              ring
      _ = ((ε⁻¹) ^ 4 / |Real.log ε|) *
              ∫ z,
                invSqKer z *
                  primitiveSupportIndicator supportConstant ε z
                ∂paperMeasure +
            (1 / |Real.log ε| ^ 2) *
              ∫ z, regularizedInvCube ε z ∂paperMeasure := by
          rw [integral_add
            (hlocalIntegrable.const_mul
              ((ε⁻¹) ^ 4 / |Real.log ε|))
            (hregIntegrable.const_mul (1 / |Real.log ε| ^ 2)),
            integral_const_mul, integral_const_mul]
  unfold primitiveKernelMajorant
  rw [integral_const_mul, hintegral]
  apply mul_le_mul_of_nonneg_left _ hpow
  calc
    ((ε⁻¹) ^ 4 / |Real.log ε|) *
          ∫ z,
            invSqKer z *
              primitiveSupportIndicator supportConstant ε z
            ∂paperMeasure +
        (1 / |Real.log ε| ^ 2) *
          ∫ z, regularizedInvCube ε z ∂paperMeasure
        ≤ ((ε⁻¹) ^ 4 / |Real.log ε|) *
              (Cball * supportConstant ^ 2 * ε ^ 2) +
            (1 / |Real.log ε| ^ 2) *
              (Creg * ε⁻¹ ^ (2 : ℕ)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hlocalInt hlocalCoeff)
        (mul_le_mul_of_nonneg_left hregInt hregCoeff)
    _ ≤ Cball * supportConstant ^ 2 *
          ε⁻¹ ^ (2 : ℕ) / |Real.log ε| +
        Creg * ε⁻¹ ^ (2 : ℕ) / |Real.log ε| := by
      rw [hlocalScale]
      exact add_le_add le_rfl hregScale
    _ = (Cball * supportConstant ^ 2 + Creg) *
          ε⁻¹ ^ (2 : ℕ) / |Real.log ε| := by ring

end

end Anderson4D
