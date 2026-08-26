import Anderson4D.DetParametrix.Core.ResidualPrimitiveRouting
import Anderson4D.Continuum.CellSingular
import Anderson4D.Continuum.GreenFourier

/-!
# Entity-level reduction for the deterministic second moment

This file continues paper Section 4.2 after the concrete L3 pairing sum was
frozen in `FinalBound.lean`.

This module contains the original downstream ledgers for two abstract
reduction interfaces:

* `MomentUniformReductionOutputAt` is a pointwise-density interface.  Its density
  variable is an absolute translation coordinate, whereas the majorant in
  (4.4) is a surviving relative endpoint.  The concrete proof therefore
  uses the integrated scalar interface in
  `R324PrimitiveIterationClosure` instead;
* `RoutedMomentReductionOutput` is a finite decomposition into concrete
  summands, each carrying the decay of every possible frequency increment.

Neither abstract output proves either branch of (3.24).  This file proves
the numerical consequences of the stated hypotheses; the final concrete
R-324 closure uses the integrated interface.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set
open scoped BigOperators

/-! ## The critical regularized square integral -/

/-- The regularized power in the second term of the inserted primitive
majorant (4.4). -/
def regularizedInvSquare (ε : ℝ) (z : T4) : ℝ :=
  (torusDistSq z + ε ^ 2)⁻¹ ^ (2 : ℕ)

theorem regularizedInvSquare_nonneg (ε : ℝ) (z : T4) :
    0 ≤ regularizedInvSquare ε z := by
  unfold regularizedInvSquare
  positivity

theorem measurable_regularizedInvSquare (ε : ℝ) :
    Measurable (regularizedInvSquare ε) := by
  unfold regularizedInvSquare
  exact (measurable_torusDistSq.add measurable_const).inv.pow_const 2

theorem integrable_regularizedInvSquare
    (ε : ℝ) (hε : 0 < ε) :
    Integrable (regularizedInvSquare ε) paperMeasure := by
  let B : ℝ := ((ε ^ 2)⁻¹) ^ (2 : ℕ)
  have hB : Integrable (fun _ : T4 => B) paperMeasure :=
    integrable_const B
  refine Integrable.mono' hB
    (measurable_regularizedInvSquare ε).aestronglyMeasurable
    (.of_forall fun z => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (regularizedInvSquare_nonneg ε z)]
  dsimp only [B]
  unfold regularizedInvSquare
  exact pow_le_pow_left₀
    (inv_nonneg.mpr
      (add_nonneg (torusDistSq_nonneg z) (sq_nonneg ε)))
    (inv_anti₀ (sq_pos_of_pos hε)
      (le_add_of_nonneg_left (torusDistSq_nonneg z)))
    2

/-- On the inner ball the regularized square is bounded by `ε⁻⁴`. -/
theorem regularizedInvSquare_le_inv_four
    (ε : ℝ) (hε : 0 < ε) (z : T4) :
    regularizedInvSquare ε z ≤ ε⁻¹ ^ (4 : ℕ) := by
  unfold regularizedInvSquare
  have h :=
    pow_le_pow_left₀
      (inv_nonneg.mpr
        (add_nonneg (torusDistSq_nonneg z) (sq_nonneg ε)))
      (inv_anti₀ (sq_pos_of_pos hε)
        (le_add_of_nonneg_left (torusDistSq_nonneg z)))
      2
  calc
    (torusDistSq z + ε ^ 2)⁻¹ ^ 2 ≤ (ε ^ 2)⁻¹ ^ 2 := h
    _ = ε⁻¹ ^ (4 : ℕ) := by
      rw [inv_pow, ← pow_mul]
      norm_num

/-- Outside the scale-`ε` ball the regularized square is bounded by the
critical kernel `|z|⁻⁴`. -/
theorem regularizedInvSquare_le_invSqKer_sq
    (ε : ℝ) (hε : 0 < ε) (z : T4)
    (hz : ε ^ 2 ≤ torusDistSq z) :
    regularizedInvSquare ε z ≤ invSqKer z ^ 2 := by
  unfold regularizedInvSquare invSqKer
  exact pow_le_pow_left₀
    (inv_nonneg.mpr
      (add_nonneg (torusDistSq_nonneg z) (sq_nonneg ε)))
    (inv_anti₀
      ((sq_pos_of_pos hε).trans_le hz)
      (le_add_of_nonneg_right (sq_nonneg ε)))
    2

def momentInnerBall (ε : ℝ) : Set T4 :=
  {z | torusDistSq z ≤ ε ^ 2}

def momentOuterAnnulus (ε : ℝ) : Set T4 :=
  {z | ε ^ 2 ≤ torusDistSq z}

theorem measurableSet_momentInnerBall (ε : ℝ) :
    MeasurableSet (momentInnerBall ε) :=
  measurable_torusDistSq measurableSet_Iic

theorem measurableSet_momentOuterAnnulus (ε : ℝ) :
    MeasurableSet (momentOuterAnnulus ε) :=
  measurable_torusDistSq measurableSet_Ici

theorem integrableOn_invSqKer_sq_momentOuterAnnulus
    (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun z : T4 => invSqKer z ^ 2)
      (momentOuterAnnulus ε) paperMeasure := by
  let B : ℝ := ((ε ^ 2)⁻¹) ^ (2 : ℕ)
  have hconst :
      Integrable (fun _ : T4 => B)
        (paperMeasure.restrict (momentOuterAnnulus ε)) :=
    integrable_const B
  refine Integrable.mono' hconst
    (measurable_invSqKer.pow_const 2).aestronglyMeasurable.restrict
    ?_
  filter_upwards
      [ae_restrict_mem (measurableSet_momentOuterAnnulus ε)] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  dsimp only [B]
  unfold invSqKer
  exact pow_le_pow_left₀
    (inv_nonneg.mpr (torusDistSq_nonneg z))
    (inv_anti₀ (sq_pos_of_pos hε) hz)
    2

/-- The scale ball is contained in the metric ball of twice the radius.
The harmless factor `2` avoids a closed/open boundary issue. -/
theorem momentInnerBall_subset_metricBall
    (ε : ℝ) (hε : 0 < ε) :
    momentInnerBall ε ⊆ Metric.ball (0 : T4) (2 * ε) := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right]
  have hsq : ‖z‖ ^ 2 ≤ ε ^ 2 :=
    (sq_norm_le_torusDistSq z).trans hz
  have hnorm : ‖z‖ ≤ ε := by
    nlinarith [norm_nonneg z]
  linarith

/-- The critical regularized square has only a logarithmic integral
divergence in four dimensions. -/
theorem integral_regularizedInvSquare_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∫ z, regularizedInvSquare ε z ∂paperMeasure ≤
          C * (1 + |Real.log ε|) := by
  obtain ⟨Cball, hCball, hball⟩ := paperMeasure_ball_toReal_le
  obtain ⟨Cann, hCann, hann⟩ :=
    setIntegral_invSqKer_sq_annulus_le
  let C : ℝ := 16 * Cball + Cann
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro ε hε hε1
  let S : Set T4 := momentInnerBall ε
  have hS : MeasurableSet S :=
    measurableSet_momentInnerBall ε
  have hint := integrable_regularizedInvSquare ε hε
  have hnear :
      ∫ z in S, regularizedInvSquare ε z ∂paperMeasure ≤
        16 * Cball := by
    have hconstInt :
        IntegrableOn (fun _ : T4 => ε⁻¹ ^ (4 : ℕ))
          S paperMeasure :=
      integrableOn_const
    calc
      ∫ z in S, regularizedInvSquare ε z ∂paperMeasure ≤
          ∫ _z in S, ε⁻¹ ^ (4 : ℕ) ∂paperMeasure := by
        exact setIntegral_mono_on hint.integrableOn hconstInt hS
          fun z _ => regularizedInvSquare_le_inv_four ε hε z
      _ = ε⁻¹ ^ (4 : ℕ) * (paperMeasure S).toReal := by
        rw [setIntegral_const]
        simp only [smul_eq_mul, measureReal_def]
        ring
      _ ≤ ε⁻¹ ^ (4 : ℕ) *
          (paperMeasure (Metric.ball (0 : T4) (2 * ε))).toReal := by
        exact mul_le_mul_of_nonneg_left
          (measureReal_mono (momentInnerBall_subset_metricBall ε hε))
          (by positivity)
      _ ≤ ε⁻¹ ^ (4 : ℕ) * (Cball * (2 * ε) ^ 4) := by
        exact mul_le_mul_of_nonneg_left
          (hball 0 (2 * ε) (by positivity)) (by positivity)
      _ = 16 * Cball := by
        field_simp [hε.ne']
        ring
  have hfar :
      ∫ z in Sᶜ, regularizedInvSquare ε z ∂paperMeasure ≤
        Cann * (1 + |Real.log ε|) := by
    have hsubset : Sᶜ ⊆ momentOuterAnnulus ε := by
      intro z hz
      change ¬torusDistSq z ≤ ε ^ 2 at hz
      exact le_of_not_ge hz
    have hinv :=
      integrableOn_invSqKer_sq_momentOuterAnnulus ε hε
    calc
      ∫ z in Sᶜ, regularizedInvSquare ε z ∂paperMeasure ≤
          ∫ z in Sᶜ, invSqKer z ^ 2 ∂paperMeasure := by
        exact setIntegral_mono_on hint.integrableOn
          (hinv.mono_set hsubset) hS.compl
          fun z hz => by
            change ¬torusDistSq z ≤ ε ^ 2 at hz
            exact regularizedInvSquare_le_invSqKer_sq
              ε hε z (le_of_not_ge hz)
      _ ≤ ∫ z in momentOuterAnnulus ε,
          invSqKer z ^ 2 ∂paperMeasure := by
        exact setIntegral_mono_set hinv
          (.of_forall fun z => sq_nonneg (invSqKer z))
          (.of_forall hsubset)
      _ ≤ Cann * (1 + |Real.log ε|) := hann ε hε hε1
  calc
    ∫ z, regularizedInvSquare ε z ∂paperMeasure =
        (∫ z in S, regularizedInvSquare ε z ∂paperMeasure) +
          ∫ z in Sᶜ, regularizedInvSquare ε z ∂paperMeasure :=
      (integral_add_compl hS hint).symm
    _ ≤ 16 * Cball + Cann * (1 + |Real.log ε|) :=
      add_le_add hnear hfar
    _ ≤ (16 * Cball + Cann) * (1 + |Real.log ε|) := by
      have hlog : 1 ≤ 1 + |Real.log ε| := by
        linarith [abs_nonneg (Real.log ε)]
      nlinarith [hCball.le]
    _ = C * (1 + |Real.log ε|) := by rfl

/-! ## Integrating the inserted Proposition 4.1 majorant -/

theorem integrable_primitiveInsertedMajorant
    (C lam ε supportConstant : ℝ) (n : ℕ)
    (hε : 0 < ε) :
    Integrable
      (primitiveInsertedMajorant C lam ε supportConstant n)
      paperMeasure := by
  have hlocal :=
    integrable_invSqKer_mul_primitiveSupportIndicator supportConstant ε
  have hreg := integrable_regularizedInvSquare ε hε
  have hinside : Integrable
      (fun z : T4 =>
        (((ε⁻¹) ^ 2 / |Real.log ε|) *
            (invSqKer z *
              primitiveSupportIndicator supportConstant ε z)) +
          (1 / |Real.log ε| ^ 2) * regularizedInvSquare ε z)
      paperMeasure :=
    (hlocal.const_mul ((ε⁻¹) ^ 2 / |Real.log ε|)).add
      (hreg.const_mul (1 / |Real.log ε| ^ 2))
  refine (hinside.const_mul ((C * lam) ^ (2 * n))).congr
    (.of_forall fun z => ?_)
  unfold primitiveInsertedMajorant regularizedInvSquare
  ring

/-- Giving up one quadratic diameter insertion costs exactly `ε⁻²`:
the ordinary primitive majorant (4.3) is bounded by `ε⁻²` times the
inserted majorant (4.4).  Paper §4.2 Step 4 uses this once at each of the
four external endpoints. -/
theorem primitiveKernelMajorant_le_invSq_mul_inserted
    (C lam ε supportConstant : ℝ) (n : ℕ) (z : T4)
    (hε : 0 < ε) :
    primitiveKernelMajorant C lam ε supportConstant n z ≤
      ε⁻¹ ^ (2 : ℕ) *
        primitiveInsertedMajorant C lam ε supportConstant n z := by
  have hpow : 0 ≤ (C * lam) ^ (2 * n) :=
    (even_two_mul n).pow_nonneg (C * lam)
  have hden :
      0 ≤ torusDistSq z + ε ^ 2 :=
    add_nonneg (torusDistSq_nonneg z) (sq_nonneg ε)
  have hinv :
      (torusDistSq z + ε ^ 2)⁻¹ ≤ ε⁻¹ ^ (2 : ℕ) := by
    calc
      (torusDistSq z + ε ^ 2)⁻¹ ≤ (ε ^ 2)⁻¹ :=
        inv_anti₀ (sq_pos_of_pos hε)
          (le_add_of_nonneg_left (torusDistSq_nonneg z))
      _ = ε⁻¹ ^ (2 : ℕ) := by rw [inv_pow]
  have hreg :
      (torusDistSq z + ε ^ 2)⁻¹ ^ 3 ≤
        ε⁻¹ ^ (2 : ℕ) *
          (torusDistSq z + ε ^ 2)⁻¹ ^ 2 := by
    rw [show (3 : ℕ) = 2 + 1 by omega, pow_add, pow_one]
    calc
      (torusDistSq z + ε ^ 2)⁻¹ ^ 2 *
            (torusDistSq z + ε ^ 2)⁻¹
          ≤ (torusDistSq z + ε ^ 2)⁻¹ ^ 2 *
              ε⁻¹ ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hinv
          (pow_nonneg (inv_nonneg.mpr hden) 2)
      _ = ε⁻¹ ^ (2 : ℕ) *
          (torusDistSq z + ε ^ 2)⁻¹ ^ 2 := by ring
  unfold primitiveKernelMajorant primitiveInsertedMajorant
  calc
    (C * lam) ^ (2 * n) *
        (((ε⁻¹) ^ 4 / |Real.log ε|) * invSqKer z *
            primitiveSupportIndicator supportConstant ε z +
          (1 / |Real.log ε| ^ 2) *
            (torusDistSq z + ε ^ 2)⁻¹ ^ 3)
        ≤ (C * lam) ^ (2 * n) *
          (ε⁻¹ ^ (2 : ℕ) *
            (((ε⁻¹) ^ 2 / |Real.log ε|) * invSqKer z *
                primitiveSupportIndicator supportConstant ε z +
              (1 / |Real.log ε| ^ 2) *
                (torusDistSq z + ε ^ 2)⁻¹ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hpow
      have hlocal :
          ((ε⁻¹) ^ 4 / |Real.log ε|) * invSqKer z *
              primitiveSupportIndicator supportConstant ε z =
            ε⁻¹ ^ (2 : ℕ) *
              (((ε⁻¹) ^ 2 / |Real.log ε|) * invSqKer z *
                primitiveSupportIndicator supportConstant ε z) := by
        ring
      rw [hlocal, mul_add]
      apply add_le_add le_rfl
      calc
        (1 / |Real.log ε| ^ 2) *
              (torusDistSq z + ε ^ 2)⁻¹ ^ 3
            ≤ (1 / |Real.log ε| ^ 2) *
                (ε⁻¹ ^ (2 : ℕ) *
                  (torusDistSq z + ε ^ 2)⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_left hreg (by positivity)
        _ = ε⁻¹ ^ (2 : ℕ) *
            ((1 / |Real.log ε| ^ 2) *
              (torusDistSq z + ε ^ 2)⁻¹ ^ 2) := by ring
    _ = ε⁻¹ ^ (2 : ℕ) *
        ((C * lam) ^ (2 * n) *
          (((ε⁻¹) ^ 2 / |Real.log ε|) * invSqKer z *
              primitiveSupportIndicator supportConstant ε z +
            (1 / |Real.log ε| ^ 2) *
              (torusDistSq z + ε ^ 2)⁻¹ ^ 2)) := by ring

/-- Four endpoint sacrifices produce the explicit `ε⁻⁸` loss in
(3.24). -/
theorem four_endpoint_invSq_loss (ε : ℝ) :
    (ε⁻¹ ^ (2 : ℕ)) ^ 4 = ε⁻¹ ^ (8 : ℕ) := by
  rw [← pow_mul]

/-- The inserted majorant integrates to one inverse logarithm.  This is
the radial calculation used after the final primitive reduction in paper
§4.2 Step 3. -/
theorem exists_integral_primitiveInsertedMajorant_le :
    ∃ Cball Creg : ℝ, 0 < Cball ∧ 0 < Creg ∧
      ∀ (C lam ε supportConstant : ℝ) (n : ℕ),
        0 < ε → ε ≤ 1 → 0 < supportConstant →
        1 ≤ |Real.log ε| →
          ∫ z, primitiveInsertedMajorant C lam ε
              supportConstant n z ∂paperMeasure
            ≤ (C * lam) ^ (2 * n) *
              ((Cball * supportConstant ^ 2 + 2 * Creg) /
                |Real.log ε|) := by
  obtain ⟨Cball, hCball, hlocal⟩ :=
    exists_integral_invSqKer_mul_primitiveSupportIndicator_le
  obtain ⟨Creg, hCreg, hreg⟩ :=
    integral_regularizedInvSquare_le
  refine ⟨Cball, Creg, hCball, hCreg, ?_⟩
  intro C lam ε supportConstant n hε hε1 hs hlog
  have hlogPos : 0 < |Real.log ε| :=
    zero_lt_one.trans_le hlog
  have hlocalInt := hlocal supportConstant ε hs hε
  have hregInt := hreg ε hε hε1
  have hlocalIntegrable :=
    integrable_invSqKer_mul_primitiveSupportIndicator supportConstant ε
  have hregIntegrable := integrable_regularizedInvSquare ε hε
  have hpow : 0 ≤ (C * lam) ^ (2 * n) :=
    (even_two_mul n).pow_nonneg (C * lam)
  have hlocalCoeff : 0 ≤ (ε⁻¹) ^ 2 / |Real.log ε| := by
    positivity
  have hregCoeff : 0 ≤ 1 / |Real.log ε| ^ 2 := by
    positivity
  have hlocalScale :
      ((ε⁻¹) ^ 2 / |Real.log ε|) *
          (Cball * supportConstant ^ 2 * ε ^ 2) =
        Cball * supportConstant ^ 2 / |Real.log ε| := by
    field_simp [hε.ne', hlogPos.ne']
  have hregScale :
      (1 / |Real.log ε| ^ 2) *
          (Creg * (1 + |Real.log ε|)) ≤
        (2 * Creg) / |Real.log ε| := by
    have hL : 1 + |Real.log ε| ≤ 2 * |Real.log ε| := by
      linarith
    calc
      (1 / |Real.log ε| ^ 2) *
          (Creg * (1 + |Real.log ε|))
          ≤ (1 / |Real.log ε| ^ 2) *
              (Creg * (2 * |Real.log ε|)) := by
        gcongr
      _ = (2 * Creg) / |Real.log ε| := by
        field_simp [hlogPos.ne']
  have hintegral :
      (∫ z,
          ((ε⁻¹) ^ 2 / |Real.log ε|) * invSqKer z *
              primitiveSupportIndicator supportConstant ε z +
            (1 / |Real.log ε| ^ 2) *
              (torusDistSq z + ε ^ 2)⁻¹ ^ 2
          ∂paperMeasure) =
        ((ε⁻¹) ^ 2 / |Real.log ε|) *
              ∫ z,
                invSqKer z *
                  primitiveSupportIndicator supportConstant ε z
                ∂paperMeasure +
            (1 / |Real.log ε| ^ 2) *
              ∫ z, regularizedInvSquare ε z ∂paperMeasure := by
    calc
      (∫ z,
          ((ε⁻¹) ^ 2 / |Real.log ε|) * invSqKer z *
              primitiveSupportIndicator supportConstant ε z +
            (1 / |Real.log ε| ^ 2) *
              (torusDistSq z + ε ^ 2)⁻¹ ^ 2
          ∂paperMeasure) =
          ∫ z,
            ((ε⁻¹) ^ 2 / |Real.log ε|) *
                (invSqKer z *
                  primitiveSupportIndicator supportConstant ε z) +
              (1 / |Real.log ε| ^ 2) * regularizedInvSquare ε z
            ∂paperMeasure := by
              apply integral_congr_ae
              filter_upwards with z
              unfold regularizedInvSquare
              ring
      _ = ((ε⁻¹) ^ 2 / |Real.log ε|) *
              ∫ z,
                invSqKer z *
                  primitiveSupportIndicator supportConstant ε z
                ∂paperMeasure +
            (1 / |Real.log ε| ^ 2) *
              ∫ z, regularizedInvSquare ε z ∂paperMeasure := by
          rw [integral_add
            (hlocalIntegrable.const_mul
              ((ε⁻¹) ^ 2 / |Real.log ε|))
            (hregIntegrable.const_mul (1 / |Real.log ε| ^ 2)),
            integral_const_mul, integral_const_mul]
  unfold primitiveInsertedMajorant
  rw [integral_const_mul, hintegral]
  apply mul_le_mul_of_nonneg_left _ hpow
  calc
    ((ε⁻¹) ^ 2 / |Real.log ε|) *
          ∫ z,
            invSqKer z *
              primitiveSupportIndicator supportConstant ε z
            ∂paperMeasure +
        (1 / |Real.log ε| ^ 2) *
          ∫ z, regularizedInvSquare ε z ∂paperMeasure
        ≤ ((ε⁻¹) ^ 2 / |Real.log ε|) *
              (Cball * supportConstant ^ 2 * ε ^ 2) +
            (1 / |Real.log ε| ^ 2) *
              (Creg * (1 + |Real.log ε|)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hlocalInt hlocalCoeff)
        (mul_le_mul_of_nonneg_left hregInt hregCoeff)
    _ ≤ Cball * supportConstant ^ 2 / |Real.log ε| +
        (2 * Creg) / |Real.log ε| := by
      rw [hlocalScale]
      exact add_le_add le_rfl hregScale
    _ = (Cball * supportConstant ^ 2 + 2 * Creg) /
          |Real.log ε| := by ring

/-! ## Uniform grouped branch of R-324 -/

/-- One contraction term in the concrete deterministic moment sum, before
the common `λ_ε^(2m)` factor. -/
def deterministicMomentPairingTerm
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) : ℂ :=
  ∫ x, ∫ y, ∫ z, ∫ w,
    ∫ v : Fin (2 * m) → T4,
      deterministicMomentIntegrand ρ ε m α β
        κp κm π x y z w v
      ∂(Measure.pi fun _ => paperMeasure)
    ∂paperMeasure ∂paperMeasure ∂paperMeasure ∂paperMeasure

/-- The frozen deterministic moment sum is exactly the common coupling
times the three finite contraction sums from (4.18). -/
theorem deterministicMomentPairingSum_eq_nested_terms
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4) :
    deterministicMomentPairingSum ρ lam ε m α β =
      (lamEps lam ε ^ (2 * m) : ℂ) *
        ∑ κp : PartialPairing (Fin m),
          ∑ κm : PartialPairing (Fin m),
            ∑ π : κp.singles ≃ κm.singles,
              deterministicMomentPairingTerm ρ ε m α β κp κm π := by
  rfl

/-- A contraction term indexed by the single doubled-entity type. -/
def deterministicMomentContractionTerm
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (e : MomentContraction m) : ℂ :=
  deterministicMomentPairingTerm ρ ε m α β
    e.1 e.2.1 e.2.2

/-- Entity-indexed form of the frozen deterministic moment sum. -/
theorem deterministicMomentPairingSum_eq_contractionTerms
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4) :
    deterministicMomentPairingSum ρ lam ε m α β =
      (lamEps lam ε ^ (2 * m) : ℂ) *
        ∑ e : MomentContraction m,
          deterministicMomentContractionTerm ρ ε m α β e := by
  rw [deterministicMomentPairingSum_eq_nested_terms,
    sum_momentContractions_eq_nested]
  rfl

/-- The cancellation-preserving Step 1 quantity for R-324: sum the
contraction terms sharing a doubled extraction signature before taking
their norm. -/
def groupedDeterministicMomentTermNormSum
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4) : ℝ :=
  ∑ s ∈ momentContractionSignatures m,
    ‖∑ e ∈ (Finset.univ :
        Finset (MomentContraction m)) with
      momentContractionSignature e = s,
      deterministicMomentContractionTerm ρ ε m α β e‖

/-- Triangle inequality only across doubled endpoint signatures.  No
absolute value is moved inside a primitive-pairing fiber. -/
theorem deterministicMomentPairingSum_le_groupedSignatures
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      |lamEps lam ε| ^ (2 * m) *
        groupedDeterministicMomentTermNormSum ρ ε m α β := by
  rw [deterministicMomentPairingSum_eq_contractionTerms,
    norm_mul, norm_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg _) _)
  rw [← sum_momentContractions_by_signature m
    (deterministicMomentContractionTerm ρ ε m α β)]
  exact norm_sum_le _ _

/-- Cancellation-preserving upstream data produced by the successive
primitive reductions (4.18)--(4.20).

The density is indexed by the extraction signature of the doubled full
pairing.  All contraction terms in one signature fiber are summed before
their norm is taken, exactly as the primitive-pairing sums in Proposition
4.1 require.  The integrability field licenses the final finite
sum/integral exchange, and the pointwise field is strictly upstream of the
integrated conclusion (3.24). -/
structure MomentUniformReductionData
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4)
    (primitiveConstant supportConstant : ℝ) where
  density :
    (Finset (Fin (2 * m)) ×
      Finset (Fin (2 * m))) → T4 → ℝ
  density_integrable :
    ∀ s ∈ momentContractionSignatures m,
      Integrable (density s) paperMeasure
  density_nonneg :
    ∀ s ∈ momentContractionSignatures m,
      ∀ z, 0 ≤ density s z
  fiber_le_density_integral :
    ∀ s ∈ momentContractionSignatures m,
      ‖∑ e ∈ (Finset.univ :
          Finset (MomentContraction m)) with
        momentContractionSignature e = s,
        deterministicMomentContractionTerm ρ ε m α β e‖ ≤
          ∫ z, density s z ∂paperMeasure
  pointwise_primitive_domination :
    ∀ z,
      |lamEps lam ε| ^ (2 * m) *
          (∑ s ∈ momentContractionSignatures m,
            density s z) ≤
        primitiveInsertedMajorant primitiveConstant lam ε
          supportConstant m z

/-- Fixed-signature pointwise-density interface.

The concrete R-324 proof instead uses `MomentRefinedIntegratedReductionData`:
`density` here is parameterized by an absolute translation coordinate, whereas
the paper integrates all external variables before majorizing the surviving
relative endpoint. -/
structure MomentFiberReductionData
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4)
    (primitiveConstant supportConstant : ℝ) where
  density :
    (Finset (Fin (2 * m)) ×
      Finset (Fin (2 * m))) → T4 → ℝ
  density_integrable :
    ∀ s ∈ momentContractionSignatures m,
      Integrable (density s) paperMeasure
  density_nonneg :
    ∀ s ∈ momentContractionSignatures m,
      ∀ z, 0 ≤ density s z
  fiber_le_density_integral :
    ∀ s ∈ momentContractionSignatures m,
      ‖∑ e ∈ (Finset.univ :
          Finset (MomentContraction m)) with
        momentContractionSignature e = s,
        deterministicMomentContractionTerm ρ ε m α β e‖ ≤
          ∫ z, density s z ∂paperMeasure
  pointwise_fiber_domination :
    ∀ s ∈ momentContractionSignatures m,
      ∀ z,
        |lamEps lam ε| ^ (2 * m) * density s z ≤
          primitiveInsertedMajorant primitiveConstant lam ε
            supportConstant m z

/-- Sum the independent fixed-signature collapse estimates and absorb
the exact coarse `4^(2m)` signature count by replacing `C` with `4C`.
This is the R-324 counterpart of
`RenormFiberReductionOutput.toRenormReductionOutput`. -/
def MomentFiberReductionData.toMomentUniformReductionData
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {α β : Z4}
    {primitiveConstant supportConstant : ℝ}
    (hC : 0 ≤ primitiveConstant) (hlam : 0 ≤ lam)
    (d : MomentFiberReductionData ρ lam ε m α β
      primitiveConstant supportConstant) :
    MomentUniformReductionData ρ lam ε m α β
      (4 * primitiveConstant) supportConstant := by
  refine
    { density := d.density
      density_integrable := d.density_integrable
      density_nonneg := d.density_nonneg
      fiber_le_density_integral := d.fiber_le_density_integral
      pointwise_primitive_domination := fun z => ?_ }
  calc
    |lamEps lam ε| ^ (2 * m) *
          (∑ s ∈ momentContractionSignatures m,
            d.density s z) =
        ∑ s ∈ momentContractionSignatures m,
          |lamEps lam ε| ^ (2 * m) * d.density s z := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _s ∈ momentContractionSignatures m,
          primitiveInsertedMajorant primitiveConstant lam ε
            supportConstant m z :=
      Finset.sum_le_sum fun s hs =>
        d.pointwise_fiber_domination s hs z
    _ =
        ((momentContractionSignatures m).card : ℝ) *
          primitiveInsertedMajorant primitiveConstant lam ε
            supportConstant m z := by
      simp
    _ ≤ (4 : ℝ) ^ (2 * m) *
          primitiveInsertedMajorant primitiveConstant lam ε
            supportConstant m z := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_momentContractionSignatures_le m
      · exact primitiveInsertedMajorant_nonneg hC hlam
    _ = primitiveInsertedMajorant
          (4 * primitiveConstant) lam ε supportConstant m z := by
      unfold primitiveInsertedMajorant
      rw [show (4 * primitiveConstant) * lam =
          4 * (primitiveConstant * lam) by ring,
        mul_pow]
      ring

def MomentUniformReductionOutputAt
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4)
    (primitiveConstant supportConstant : ℝ) : Prop :=
  Nonempty (MomentUniformReductionData ρ lam ε m α β
    primitiveConstant supportConstant)

/-- Existence wrapper for the fixed-signature constructor. -/
theorem MomentFiberReductionData.toMomentUniformReductionOutputAt
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {α β : Z4}
    {primitiveConstant supportConstant : ℝ}
    (hC : 0 ≤ primitiveConstant) (hlam : 0 ≤ lam)
    (d : MomentFiberReductionData ρ lam ε m α β
      primitiveConstant supportConstant) :
    MomentUniformReductionOutputAt ρ lam ε m α β
      (4 * primitiveConstant) supportConstant :=
  ⟨d.toMomentUniformReductionData hC hlam⟩

/-- Integrate the genuine pointwise primitive domination supplied by the
uniform reduction. -/
theorem deterministicMomentPairingSum_le_integral_insertedMajorant
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {α β : Z4}
    {primitiveConstant supportConstant : ℝ}
    (hε : 0 < ε)
    (hred : MomentUniformReductionOutputAt ρ lam ε m α β
      primitiveConstant supportConstant) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      ∫ z, primitiveInsertedMajorant primitiveConstant lam ε
        supportConstant m z ∂paperMeasure := by
  obtain ⟨d⟩ := hred
  have hsumInt :
      Integrable
        (fun z : T4 =>
          ∑ s ∈ momentContractionSignatures m,
            d.density s z)
        paperMeasure := by
    apply integrable_finsetSum
    intro s hs
    exact d.density_integrable s hs
  have hscaledInt :
      Integrable
        (fun z : T4 =>
          |lamEps lam ε| ^ (2 * m) *
            ∑ s ∈ momentContractionSignatures m,
              d.density s z)
        paperMeasure :=
    hsumInt.const_mul _
  have hfiberSum :
      groupedDeterministicMomentTermNormSum ρ ε m α β ≤
        ∑ s ∈ momentContractionSignatures m,
          ∫ z, d.density s z ∂paperMeasure := by
    unfold groupedDeterministicMomentTermNormSum
    apply Finset.sum_le_sum
    intro s hs
    exact d.fiber_le_density_integral s hs
  calc
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        |lamEps lam ε| ^ (2 * m) *
          groupedDeterministicMomentTermNormSum ρ ε m α β :=
      deterministicMomentPairingSum_le_groupedSignatures
        ρ lam ε m α β
    _ ≤ |lamEps lam ε| ^ (2 * m) *
          ∑ s ∈ momentContractionSignatures m,
            ∫ z, d.density s z ∂paperMeasure := by
      exact mul_le_mul_of_nonneg_left hfiberSum
        (pow_nonneg (abs_nonneg _) _)
    _ = ∫ z,
          |lamEps lam ε| ^ (2 * m) *
            ∑ s ∈ momentContractionSignatures m,
              d.density s z
          ∂paperMeasure := by
      rw [integral_const_mul, integral_finsetSum]
      intro s hs
      exact d.density_integrable s hs
    _ ≤ ∫ z, primitiveInsertedMajorant primitiveConstant lam ε
          supportConstant m z ∂paperMeasure := by
      exact integral_mono hscaledInt
        (integrable_primitiveInsertedMajorant primitiveConstant lam ε
          supportConstant m hε)
        d.pointwise_primitive_domination

/-- **Uniform entity branch of P-3.5b-det.**

For fixed constants coming from Proposition 4.1, the radial integration
constants are chosen once and absorbed into the paper's leading absolute
constant.  The conclusion is the exact uniform branch
`λ_ε² C (Cλ)^(2m-2)`. -/
theorem exists_deterministicMoment_uniform_bound_of_reduction
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 1 ≤ m →
        MomentUniformReductionOutputAt ρ lam ε m α β
          primitiveConstant supportConstant →
          ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
            lamEps lam ε ^ 2 * outerConstant *
              (primitiveConstant * lam) ^ (2 * m - 2) := by
  obtain ⟨Cball, Creg, hCball, hCreg, hmajorant⟩ :=
    exists_integral_primitiveInsertedMajorant_le
  let K : ℝ := Cball * supportConstant ^ 2 + 2 * Creg
  let outerConstant : ℝ := K * primitiveConstant ^ 2
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have houter : 0 < outerConstant := by
    dsimp only [outerConstant]
    positivity
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m α β hε hε1 hlog hm hred
  have hlogPos : 0 < |Real.log ε| :=
    zero_lt_one.trans_le hlog
  have hraw :=
    (deterministicMomentPairingSum_le_integral_insertedMajorant
      hε hred).trans
      (hmajorant primitiveConstant lam ε supportConstant m
        hε hε1 hsupport hlog)
  calc
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        (primitiveConstant * lam) ^ (2 * m) *
          (K / |Real.log ε|) := by
      simpa only [K] using hraw
    _ = lamEps lam ε ^ 2 * outerConstant *
          (primitiveConstant * lam) ^ (2 * m - 2) := by
      have hexp : 2 * m = (2 * m - 2) + 2 := by omega
      have hpow :
          (primitiveConstant * lam) ^ (2 * m) =
            (primitiveConstant * lam) ^ (2 * m - 2) *
              (primitiveConstant * lam) ^ 2 := by
        calc
          (primitiveConstant * lam) ^ (2 * m) =
              (primitiveConstant * lam) ^ ((2 * m - 2) + 2) :=
            congrArg (fun e : ℕ => (primitiveConstant * lam) ^ e) hexp
          _ = (primitiveConstant * lam) ^ (2 * m - 2) *
              (primitiveConstant * lam) ^ 2 := pow_add _ _ _
      rw [hpow, lamEps_sq hlogPos]
      dsimp only [outerConstant]
      ring

/-! ## Routed entity branch of R-324 -/

/-- The endpoint Green multiplier `⟨k⟩⁻²`. -/
def secondOrderModeDecay (k : Z4) : ℝ :=
  (1 + z4FrequencyNorm k ^ 2)⁻¹

theorem secondOrderModeDecay_nonneg (k : Z4) :
    0 ≤ secondOrderModeDecay k := by
  unfold secondOrderModeDecay
  positivity

/-- The squared Euclidean frequency used by the paper's Japanese bracket. -/
def paperModeNormSq (k : Z4) : ℝ :=
  ∑ i, (k i : ℝ) ^ 2

def paperSecondOrderModeDecay (k : Z4) : ℝ :=
  (1 + paperModeNormSq k)⁻¹

def paperFourthOrderModeDecay (k : Z4) : ℝ :=
  ((1 + paperModeNormSq k) ^ 2)⁻¹

theorem paperSecondOrderModeDecay_nonneg (k : Z4) :
    0 ≤ paperSecondOrderModeDecay k := by
  unfold paperSecondOrderModeDecay paperModeNormSq
  positivity

theorem paperFourthOrderModeDecay_nonneg (k : Z4) :
    0 ≤ paperFourthOrderModeDecay k := by
  unfold paperFourthOrderModeDecay paperModeNormSq
  positivity

/-- Sup-norm comparison for the project's real Fourier vectors. -/
theorem z4FrequencyNorm_sq_le_sum (k : Z4) :
    z4FrequencyNorm k ^ 2 ≤ ∑ i, (k i : ℝ) ^ 2 := by
  let x : R4 := fun i => (k i : ℝ)
  have hs : 0 ≤ ∑ i, x i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have h : ‖x‖ ≤ Real.sqrt (∑ i, x i ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    calc
      |x i| = Real.sqrt (x i ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (∑ j, x j ^ 2) :=
        Real.sqrt_le_sqrt
          (Finset.single_le_sum
            (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))
  change ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2
  calc
    ‖x‖ ^ 2 ≤ Real.sqrt (∑ i, x i ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i, x i ^ 2 := Real.sq_sqrt hs

/-- Exact Green coefficient in the paper's Euclidean bracket. -/
theorem norm_paperFourierCoeff_greenFn_eq (k : Z4) :
    ‖∫ z : T4, charT4 k z * (greenFn z : ℂ) ∂paperMeasure‖ =
      paperSecondOrderModeDecay k := by
  rw [paperFourierCoeff_greenFn]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  rfl

/-- Euclidean bracket decay is at least as strong as the project's
sup-norm bracket decay. -/
theorem paperSecondOrderModeDecay_le (k : Z4) :
    paperSecondOrderModeDecay k ≤ secondOrderModeDecay k := by
  unfold paperSecondOrderModeDecay secondOrderModeDecay
  exact inv_anti₀ (by positivity)
    (by
      simpa only [paperModeNormSq, add_comm] using
        (add_le_add_left (z4FrequencyNorm_sq_le_sum k) 1))

/-- The heat-kernel Green construction supplies the endpoint multiplier
used in §4.2 Step 4.  The project uses the sup norm on `R4`, so this is
the faithful one-sided comparison with the paper's Euclidean bracket. -/
theorem norm_paperFourierCoeff_greenFn_le (k : Z4) :
    ‖∫ z : T4, charT4 k z * (greenFn z : ℂ) ∂paperMeasure‖ ≤
      secondOrderModeDecay k := by
  rw [norm_paperFourierCoeff_greenFn_eq]
  exact paperSecondOrderModeDecay_le k

theorem secondOrderModeDecay_sq (k : Z4) :
    secondOrderModeDecay k ^ 2 = fourthOrderModeDecay k := by
  unfold secondOrderModeDecay fourthOrderModeDecay
  rw [inv_pow]

theorem paperSecondOrderModeDecay_sq (k : Z4) :
    paperSecondOrderModeDecay k ^ 2 =
      paperFourthOrderModeDecay k := by
  unfold paperSecondOrderModeDecay paperFourthOrderModeDecay
  rw [inv_pow]

theorem paperFourthOrderModeDecay_le (k : Z4) :
    paperFourthOrderModeDecay k ≤ fourthOrderModeDecay k := by
  rw [← paperSecondOrderModeDecay_sq, ← secondOrderModeDecay_sq]
  exact pow_le_pow_left₀
    (paperSecondOrderModeDecay_nonneg k)
    (paperSecondOrderModeDecay_le k) 2

/-- Two Green endpoints on each copy are bounded by the
`⟨α⟩⁻⁴⟨β⟩⁻⁴` factor. -/
theorem four_endpoint_green_decay_le (α β : Z4) :
    ‖∫ z : T4, charT4 α z * (greenFn z : ℂ) ∂paperMeasure‖ ^ 2 *
        ‖∫ z : T4, charT4 β z * (greenFn z : ℂ) ∂paperMeasure‖ ^ 2 ≤
      fourthOrderModeDecay α * fourthOrderModeDecay β := by
  calc
    ‖∫ z : T4, charT4 α z * (greenFn z : ℂ) ∂paperMeasure‖ ^ 2 *
          ‖∫ z : T4, charT4 β z * (greenFn z : ℂ) ∂paperMeasure‖ ^ 2
        ≤ secondOrderModeDecay α ^ 2 *
            secondOrderModeDecay β ^ 2 := by
      gcongr
      · exact norm_paperFourierCoeff_greenFn_le α
      · exact norm_paperFourierCoeff_greenFn_le β
    _ = fourthOrderModeDecay α * fourthOrderModeDecay β := by
      rw [secondOrderModeDecay_sq, secondOrderModeDecay_sq]

/-- Exact Euclidean-bracket version of the preceding four-endpoint
identity. -/
theorem four_endpoint_green_paper_decay (α β : Z4) :
    ‖∫ z : T4, charT4 α z * (greenFn z : ℂ) ∂paperMeasure‖ ^ 2 *
        ‖∫ z : T4, charT4 β z * (greenFn z : ℂ) ∂paperMeasure‖ ^ 2 =
      paperFourthOrderModeDecay α *
        paperFourthOrderModeDecay β := by
  rw [norm_paperFourierCoeff_greenFn_eq,
    norm_paperFourierCoeff_greenFn_eq,
    paperSecondOrderModeDecay_sq,
    paperSecondOrderModeDecay_sq]

/-- Bounded endpoint oscillation preserves one Green Fourier decay while
costing the explicit factor `2`, as in the last paragraph of §4.2. -/
theorem endpoint_phase_decay_le_two
    (k : Z4) (θ : ℝ) :
    secondOrderModeDecay k * |Real.cos θ - 1| ≤
      2 * secondOrderModeDecay k := by
  have h := abs_cos_sub_one_le_two θ
  nlinarith [secondOrderModeDecay_nonneg k]

/-- The alternative quadratic endpoint bound is the diameter insertion
used in Steps 1 and 3. -/
theorem endpoint_phase_decay_le_quadratic
    (k : Z4) (θ : ℝ) :
    secondOrderModeDecay k * |Real.cos θ - 1| ≤
      secondOrderModeDecay k * θ ^ 2 :=
  mul_le_mul_of_nonneg_left (abs_cos_sub_one_le_sq θ)
    (secondOrderModeDecay_nonneg k)

/-- Cast a Fourier mode to Euclidean frequency space, so the routing
argument produces the paper's exact Japanese bracket rather than merely
an equivalent sup-norm bracket. -/
def z4EuclideanFrequency (k : Z4) :
    EuclideanSpace ℝ (Fin dim) :=
  WithLp.toLp 2 fun i => (k i : ℝ)

theorem norm_sq_z4EuclideanFrequency (k : Z4) :
    ‖z4EuclideanFrequency k‖ ^ 2 = paperModeNormSq k := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-- Exact Euclidean decay branch printed in (3.24). -/
def paperDeterministicMomentDecay
    (ε : ℝ) (α β : Z4) : ℝ :=
  ε⁻¹ ^ (8 : ℕ) *
    paperFourthOrderModeDecay α *
    paperFourthOrderModeDecay β *
    eighthOrderFrequencyDecay
      (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖)

theorem paperDeterministicMomentDecay_nonneg
    (ε : ℝ) (α β : Z4) :
    0 ≤ paperDeterministicMomentDecay ε α β := by
  unfold paperDeterministicMomentDecay
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by positivity)
        (paperFourthOrderModeDecay_nonneg α))
      (paperFourthOrderModeDecay_nonneg β))
    (eighthOrderFrequencyDecay_nonneg _)

/-- The exact paper decay is stronger than the sup-norm ledger frozen in
`FinalBound.lean`. -/
theorem paperDeterministicMomentDecay_le
    (ε : ℝ) (α β : Z4) :
    paperDeterministicMomentDecay ε α β ≤
      deterministicMomentDecay ε α β := by
  have hnorm :
      z4FrequencyNorm (α + β) ≤
        ‖z4EuclideanFrequency (α + β)‖ := by
    have hsq := z4FrequencyNorm_sq_le_sum (α + β)
    change z4FrequencyNorm (α + β) ^ 2 ≤
      paperModeNormSq (α + β) at hsq
    rw [← norm_sq_z4EuclideanFrequency] at hsq
    nlinarith [z4FrequencyNorm_nonneg (α + β),
      norm_nonneg (z4EuclideanFrequency (α + β))]
  have heighth :
      eighthOrderFrequencyDecay
          (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) ≤
        eighthOrderFrequencyDecay
          (ε ^ 2 * z4FrequencyNorm (α + β)) := by
    apply eighthOrderFrequencyDecay_anti
    · exact mul_nonneg (sq_nonneg ε)
        (z4FrequencyNorm_nonneg (α + β))
    · exact mul_le_mul_of_nonneg_left hnorm (sq_nonneg ε)
  unfold paperDeterministicMomentDecay deterministicMomentDecay
  have hα := paperFourthOrderModeDecay_le α
  have hβ := paperFourthOrderModeDecay_le β
  have hεpow : 0 ≤ ε⁻¹ ^ (8 : ℕ) := by positivity
  have hpaperα : 0 ≤ paperFourthOrderModeDecay α :=
    paperFourthOrderModeDecay_nonneg α
  have hpaperβ : 0 ≤ paperFourthOrderModeDecay β :=
    paperFourthOrderModeDecay_nonneg β
  have hfinalα : 0 ≤ fourthOrderModeDecay α :=
    fourthOrderModeDecay_nonneg α
  have hePaper :
      0 ≤ eighthOrderFrequencyDecay
        (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) :=
    eighthOrderFrequencyDecay_nonneg _
  calc
    ε⁻¹ ^ (8 : ℕ) *
          paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β *
          eighthOrderFrequencyDecay
            (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖)
        ≤ ε⁻¹ ^ (8 : ℕ) *
          fourthOrderModeDecay α *
          fourthOrderModeDecay β *
          eighthOrderFrequencyDecay
            (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) := by
      apply mul_le_mul_of_nonneg_right _ hePaper
      calc
        ε⁻¹ ^ (8 : ℕ) *
              paperFourthOrderModeDecay α *
              paperFourthOrderModeDecay β
            ≤ ε⁻¹ ^ (8 : ℕ) *
              fourthOrderModeDecay α *
              paperFourthOrderModeDecay β := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hα hεpow) hpaperβ
        _ ≤ ε⁻¹ ^ (8 : ℕ) *
              fourthOrderModeDecay α *
              fourthOrderModeDecay β := by
          exact mul_le_mul_of_nonneg_left hβ
            (mul_nonneg hεpow hfinalα)
    _ ≤ ε⁻¹ ^ (8 : ℕ) *
          fourthOrderModeDecay α *
          fourthOrderModeDecay β *
          eighthOrderFrequencyDecay
            (ε ^ 2 * z4FrequencyNorm (α + β)) := by
      exact mul_le_mul_of_nonneg_left heighth
        (mul_nonneg
          (mul_nonneg hεpow hfinalα)
          (fourthOrderModeDecay_nonneg β))

/-- A finite, term-by-term frequency decomposition of the concrete
deterministic moment sum.

This is the entity-level output of paper §4.2 Step 4, before the
pigeonhole/routing argument:

* each term is a genuine summand of `deterministicMomentPairingSum`;
* its increment list telescopes exactly to `α+β`;
* every possible increment exposes the corresponding cutoff decay;
* the sum of nonnegative term weights is controlled by the already
  reduced uniform amplitude.

These fields are strictly upstream of the target decay estimate. -/
structure RoutedMomentDecomposition
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (amplitude : ℝ) where
  termCount : ℕ
  term : Fin termCount → ℂ
  weight : Fin termCount → ℝ
  incrementCount : Fin termCount → ℕ
  increment :
    ∀ a : Fin termCount,
      Fin (incrementCount a) → EuclideanSpace ℝ (Fin dim)
  sum_eq :
    deterministicMomentPairingSum ρ lam ε m α β =
      ∑ a, term a
  weight_nonneg : ∀ a, 0 ≤ weight a
  incrementCount_pos : ∀ a, 0 < incrementCount a
  incrementCount_le_trunc :
    ∀ a, incrementCount a ≤ truncOrder ε
  increment_sum :
    ∀ a, (∑ i, increment a i) = z4EuclideanFrequency (α + β)
  term_le_increment_decay :
    ∀ (a : Fin termCount) (i : Fin (incrementCount a)),
      ‖term a‖ ≤
        weight a *
          (ε⁻¹ ^ (8 : ℕ) *
            paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β *
            eighthOrderFrequencyDecay ‖increment a i‖)
  sum_weight_le : (∑ a, weight a) ≤ amplitude

/-- Existence form used as the R-324 reduction interface. -/
def RoutedMomentReductionOutput
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (amplitude : ℝ) : Prop :=
  Nonempty (RoutedMomentDecomposition ρ lam ε m α β amplitude)

/-- The concrete frequency decomposition and the truncation-length routing
lemma imply the paper's exact Euclidean decaying branch of (3.24). -/
theorem deterministicMomentPairingSum_paperDecay_bound_of_routedReduction
    {ρ : SmoothCutoff} {lam ε amplitude : ℝ} {m : ℕ}
    {α β : Z4}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hred : RoutedMomentReductionOutput ρ lam ε m α β amplitude) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      amplitude * paperDeterministicMomentDecay ε α β := by
  obtain ⟨d⟩ := hred
  have hterm :
      ∀ a : Fin d.termCount,
        ‖d.term a‖ ≤
          d.weight a * paperDeterministicMomentDecay ε α β := by
    intro a
    obtain ⟨i, hi⟩ :=
      exists_increment_with_eighth_order_payoff
        (d.incrementCount a) (d.incrementCount_pos a)
        (d.increment a) ε hε hεsmall
        (d.incrementCount_le_trunc a)
    have hselected :
        ε⁻¹ ^ (8 : ℕ) *
            paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β *
            eighthOrderFrequencyDecay ‖d.increment a i‖ ≤
          paperDeterministicMomentDecay ε α β := by
      unfold paperDeterministicMomentDecay
      apply mul_le_mul_of_nonneg_left
      · simpa only [d.increment_sum a] using hi
      · exact mul_nonneg
          (mul_nonneg (by positivity)
            (paperFourthOrderModeDecay_nonneg α))
          (paperFourthOrderModeDecay_nonneg β)
    exact (d.term_le_increment_decay a i).trans
      (mul_le_mul_of_nonneg_left hselected (d.weight_nonneg a))
  calc
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ =
        ‖∑ a, d.term a‖ := by rw [d.sum_eq]
    _ ≤ ∑ a, ‖d.term a‖ := norm_sum_le _ _
    _ ≤ ∑ a, d.weight a * paperDeterministicMomentDecay ε α β :=
      Finset.sum_le_sum fun a _ => hterm a
    _ = (∑ a, d.weight a) *
        paperDeterministicMomentDecay ε α β := by
      rw [Finset.sum_mul]
    _ ≤ amplitude * paperDeterministicMomentDecay ε α β :=
      mul_le_mul_of_nonneg_right d.sum_weight_le
        (paperDeterministicMomentDecay_nonneg ε α β)

/-- Compatibility corollary for the sup-norm decay ledger frozen in
`FinalBound.lean`. -/
theorem deterministicMomentPairingSum_decay_bound_of_routedReduction
    {ρ : SmoothCutoff} {lam ε amplitude : ℝ} {m : ℕ}
    {α β : Z4}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hred : RoutedMomentReductionOutput ρ lam ε m α β amplitude) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      amplitude * deterministicMomentDecay ε α β := by
  exact
    (deterministicMomentPairingSum_paperDecay_bound_of_routedReduction
      hε hεsmall hred).trans
      (mul_le_mul_of_nonneg_left
        (paperDeterministicMomentDecay_le ε α β)
        (by
          obtain ⟨d⟩ := hred
          exact (Finset.sum_nonneg fun a _ => d.weight_nonneg a).trans
            d.sum_weight_le))

/-! ## Complete conditional closure of P-3.5b-det -/

/-- Exact Euclidean-bracket right side printed in (3.24). -/
def paperDeterministicMomentRHS
    (outerConstant powerConstant lam ε : ℝ) (m : ℕ)
    (α β : Z4) : ℝ :=
  lamEps lam ε ^ 2 * outerConstant *
    (powerConstant * lam) ^ (2 * m - 2) *
    min 1 (paperDeterministicMomentDecay ε α β)

/-- Strong, paper-bracket form of the complete deterministic closure. -/
theorem exists_deterministicMoment_paper_bound_of_reductions
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4),
        0 < ε → ε ≤ 1 / 4 → 1 ≤ |Real.log ε| → 1 ≤ m →
        MomentUniformReductionOutputAt ρ lam ε m α β
          primitiveConstant supportConstant →
        RoutedMomentReductionOutput ρ lam ε m α β
          (lamEps lam ε ^ 2 * outerConstant *
            (primitiveConstant * lam) ^ (2 * m - 2)) →
          ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
            paperDeterministicMomentRHS outerConstant primitiveConstant
              lam ε m α β := by
  obtain ⟨outerConstant, houter, huniform⟩ :=
    exists_deterministicMoment_uniform_bound_of_reduction
      hprimitive hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m α β hε hεsmall hlog hm
    huniformRed hroutedRed
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hu :=
    huniform ρ lam ε m α β hε hε1 hlog hm huniformRed
  have hd :=
    deterministicMomentPairingSum_paperDecay_bound_of_routedReduction
      hε hεsmall hroutedRed
  unfold paperDeterministicMomentRHS
  exact le_mul_min_of_le_of_le_mul hu hd

/-- **Entity-level deterministic second-moment bound, paper (3.24).**

The theorem consumes exactly the two strictly upstream outputs modeled
above: the final primitive density from Steps 1--3 and the termwise
frequency decomposition from Step 4.  It returns the exact
`λ_ε² C(Cλ)^(2m-2) min(1, ...)` bound on the frozen concrete L3 pairing
sum. -/
theorem exists_deterministicMoment_bound_of_reductions
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4),
        0 < ε → ε ≤ 1 / 4 → 1 ≤ |Real.log ε| → 1 ≤ m →
        MomentUniformReductionOutputAt ρ lam ε m α β
          primitiveConstant supportConstant →
        RoutedMomentReductionOutput ρ lam ε m α β
          (lamEps lam ε ^ 2 * outerConstant *
            (primitiveConstant * lam) ^ (2 * m - 2)) →
          ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
            deterministicMomentRHS outerConstant primitiveConstant
              lam ε m α β := by
  obtain ⟨outerConstant, houter, huniform⟩ :=
    exists_deterministicMoment_uniform_bound_of_reduction
      hprimitive hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m α β hε hεsmall hlog hm
    huniformRed hroutedRed
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hu :=
    huniform ρ lam ε m α β hε hε1 hlog hm huniformRed
  have hd :=
    deterministicMomentPairingSum_decay_bound_of_routedReduction
      hε hεsmall hroutedRed
  exact deterministicMomentPairingSum_bound_of_two_branches hu hd

end

end Anderson4D
