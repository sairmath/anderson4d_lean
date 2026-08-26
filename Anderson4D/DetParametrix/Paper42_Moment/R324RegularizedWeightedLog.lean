import Anderson4D.DetParametrix.Core.MomentReduction
import Anderson4D.Continuum.CriticalLogWeight

/-!
# The regularized weighted logarithm in R-324 Step 3

The second term of the inserted Proposition 4.1 majorant is the
regularized critical square

`(torusDistSq z + ε²)⁻²`.

After one sharp binary inverse-square convolution, it must be averaged
against the moving critical logarithm `1 + |log ‖x - z‖|`.  This file
proves both the genuine integrability of that product and its uniform
`O(|log ε|²)` integral bound.

The proof separates a ball about the moving logarithmic singularity.
When `x` is at the regularization scale, the regularized square is
bounded by `ε⁻⁴`.  When `x` is farther away, the moving ball stays away
from the origin and the regularized square is bounded by the square of
the inverse-square kernel.  Off the moving ball, the logarithmic weight
has only one fixed-scale logarithmic loss.  The remaining mass estimate
is `integral_regularizedInvSquare_le`, whose proof is precisely the
`momentInnerBall`/outer-annulus decomposition.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory Set

/-! ## Integrability certificates -/

/-- The translated critical logarithm is integrable on the compact
four-torus.  This certificate is kept separate because both moving-ball
branches below use it as a domination target. -/
private theorem integrable_criticalLogWeight_sub_left
    (x : T4) :
    Integrable
      (fun z : T4 => criticalLogWeight (x - z))
      paperMeasure := by
  let g : T4 → ℝ := fun z =>
    (3 + |Real.log 4|) +
      64 * invSqKer (x - z)
  have hg : Integrable g paperMeasure := by
    dsimp only [g]
    exact
      (integrable_const (3 + |Real.log 4|)).add
        ((integrable_invSqKer_sub_left x).const_mul 64)
  have hpoint :
      ∀ z : T4,
        criticalLogWeight (x - z) ≤ g z := by
    intro z
    have hnorm : ‖x - z‖ ≤ 1 * (4 : ℝ) := by
      rw [one_mul]
      exact (norm_t4_le_pi (x - z)).trans Real.pi_le_four
    have h :=
      criticalLogWeight_le_scaled_invSq
        (r := (4 : ℝ)) (A := (1 : ℝ))
        (by norm_num) zero_le_one (x - z) hnorm
    dsimp only [g]
    norm_num at h ⊢
    linarith
  refine Integrable.mono' hg
    (measurable_criticalLogWeight.comp
      (measurable_const.sub measurable_id)
      |>.aestronglyMeasurable)
    (.of_forall fun z => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (criticalLogWeight_nonneg (x - z))]
  exact hpoint z

/-- The regularized square times the translated critical logarithm is a
genuine integrable function.  No small-scale upper bound is needed:
positivity of `ε` gives the global domination by
`ε⁻⁴ * criticalLogWeight`. -/
theorem integrable_regularizedInvSquare_mul_criticalLogWeight
    (ε : ℝ) (x : T4) (hε : 0 < ε) :
    Integrable
      (fun z : T4 =>
        regularizedInvSquare ε z *
          criticalLogWeight (x - z))
      paperMeasure := by
  let g : T4 → ℝ := fun z =>
    ε⁻¹ ^ (4 : ℕ) *
      criticalLogWeight (x - z)
  have hg : Integrable g paperMeasure := by
    dsimp only [g]
    exact
      (integrable_criticalLogWeight_sub_left x).const_mul
        (ε⁻¹ ^ (4 : ℕ))
  refine Integrable.mono' hg
    ((measurable_regularizedInvSquare ε).mul
      (measurable_criticalLogWeight.comp
        (measurable_const.sub measurable_id))
      |>.aestronglyMeasurable)
    (.of_forall fun z => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (mul_nonneg
        (regularizedInvSquare_nonneg ε z)
        (criticalLogWeight_nonneg (x - z)))]
  exact mul_le_mul_of_nonneg_right
    (regularizedInvSquare_le_inv_four ε hε z)
    (criticalLogWeight_nonneg (x - z))

/-! ## Pointwise control away from the regularized origin -/

/-- If both the regularization scale and the origin are below a positive
radius `r`, then the regularized square is bounded by `r⁻⁴`. -/
private theorem regularizedInvSquare_le_inv_radius_four
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (z : T4) (hεr : ε ≤ r) (hrz : r ≤ ‖z‖) :
    regularizedInvSquare ε z ≤ r⁻¹ ^ (4 : ℕ) := by
  have hεdist : ε ^ 2 ≤ torusDistSq z := by
    exact
      (pow_le_pow_left₀ hε.le (hεr.trans hrz) 2).trans
        (sq_norm_le_torusDistSq z)
  calc
    regularizedInvSquare ε z ≤ invSqKer z ^ 2 :=
      regularizedInvSquare_le_invSqKer_sq
        ε hε z hεdist
    _ ≤ ((r ^ 2)⁻¹) ^ (2 : ℕ) := by
      apply pow_le_pow_left₀ (invSqKer_nonneg z)
      unfold invSqKer
      exact inv_anti₀ (sq_pos_of_pos hr)
        ((pow_le_pow_left₀ hr.le hrz 2).trans
          (sq_norm_le_torusDistSq z))
    _ = r⁻¹ ^ (4 : ℕ) := by
      rw [inv_pow, ← pow_mul]
      norm_num

/-! ## Uniform `|log ε|²` estimate -/

/-- The regularized critical square averages the moving binary
logarithm with at most two logarithmic losses, uniformly in the
translation `x`. -/
theorem exists_integral_regularizedInvSquare_mul_criticalLogWeight_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ε : ℝ) (x : T4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        (∫ z,
          regularizedInvSquare ε z *
            criticalLogWeight (x - z)
          ∂paperMeasure) ≤
            K * |Real.log ε| ^ 2 := by
  obtain ⟨Creg, hCreg, hregMass⟩ :=
    integral_regularizedInvSquare_le
  obtain ⟨Clog, hClog, hlogBall⟩ :=
    exists_setIntegral_criticalLogWeight_ball_le
  let Bfix : ℝ := 5 + |Real.log 2|
  let Kclose : ℝ :=
    16 * Clog * (4 + |Real.log 2|)
  let Kfar : ℝ := 5 * Clog
  let Koutside : ℝ := 2 * Bfix * Creg
  let K : ℝ :=
    Kclose + Kfar + 2 * Koutside + 1
  have hBfix : 0 < Bfix := by
    dsimp only [Bfix]
    positivity
  have hKclose : 0 ≤ Kclose := by
    dsimp only [Kclose]
    positivity
  have hKfar : 0 ≤ Kfar := by
    dsimp only [Kfar]
    positivity
  have hKoutside : 0 ≤ Koutside := by
    dsimp only [Koutside]
    positivity
  have hK : 0 < K := by
    dsimp only [K]
    linarith
  refine ⟨K, hK, ?_⟩
  intro ε x hε hε1 hlog
  let L : ℝ := |Real.log ε|
  let f : T4 → ℝ := fun z =>
    regularizedInvSquare ε z *
      criticalLogWeight (x - z)
  have hL : 0 < L :=
    zero_lt_one.trans_le hlog
  have hlogε :
      L = -Real.log ε := by
    dsimp only [L]
    exact abs_of_nonpos
      (Real.log_nonpos hε.le hε1)
  have hf : Integrable f paperMeasure := by
    dsimp only [f]
    exact
      integrable_regularizedInvSquare_mul_criticalLogWeight
        ε x hε
  have hreg : Integrable
      (regularizedInvSquare ε) paperMeasure :=
    integrable_regularizedInvSquare ε hε
  have hweight : Integrable
      (fun z : T4 => criticalLogWeight (x - z))
      paperMeasure :=
    integrable_criticalLogWeight_sub_left x
  have hregTotal :
      (∫ z, regularizedInvSquare ε z ∂paperMeasure) ≤
        Creg * (1 + L) := by
    simpa only [L] using hregMass ε hε hε1

  /- Off any ball whose radius is at least `2ε`, the translated
  logarithm has one fixed-scale logarithmic loss.  This certificate is
  used in both geometric branches. -/
  have houtside :
      ∀ r : ℝ, 2 * ε ≤ r →
        (∫ z in (Metric.ball x r)ᶜ,
          f z ∂paperMeasure) ≤
            Koutside * L ^ 2 := by
    intro r hradius
    let B : Set T4 := Metric.ball x r
    let g : T4 → ℝ := fun z =>
      Bfix * L * regularizedInvSquare ε z
    have hB : MeasurableSet B :=
      measurableSet_ball
    have hg : Integrable g paperMeasure := by
      dsimp only [g]
      exact hreg.const_mul (Bfix * L)
    have hpoint :
        ∀ z ∈ Bᶜ, f z ≤ g z := by
      intro z hz
      have hdist : r ≤ dist z x := by
        simpa only [B, Set.mem_compl_iff,
          Metric.mem_ball, not_lt] using hz
      have hsep : 2 * ε ≤ ‖x - z‖ := by
        calc
          2 * ε ≤ r := hradius
          _ ≤ dist z x := hdist
          _ = ‖x - z‖ := by
            rw [dist_eq_norm, norm_sub_rev]
      have hw :=
        criticalLogWeight_le_of_fixedScale
          (a := (2 : ℝ)) (by norm_num)
          hε hε1 hlog (x - z) hsep
      have hregNonneg :=
        regularizedInvSquare_nonneg ε z
      dsimp only [f, g, Bfix, L]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hw hregNonneg
    have hmono :
        (∫ z in Bᶜ, f z ∂paperMeasure) ≤
          ∫ z in Bᶜ, g z ∂paperMeasure :=
      setIntegral_mono_on
        hf.integrableOn hg.integrableOn hB.compl hpoint
    have hsetReg :
        (∫ z in Bᶜ,
          regularizedInvSquare ε z ∂paperMeasure) ≤
            ∫ z, regularizedInvSquare ε z ∂paperMeasure :=
      setIntegral_le_integral hreg
        (.of_forall fun z =>
          regularizedInvSquare_nonneg ε z)
    calc
      (∫ z in Bᶜ, f z ∂paperMeasure) ≤
          ∫ z in Bᶜ, g z ∂paperMeasure :=
        hmono
      _ =
          Bfix * L *
            ∫ z in Bᶜ,
              regularizedInvSquare ε z ∂paperMeasure := by
        dsimp only [g]
        rw [integral_const_mul]
      _ ≤
          Bfix * L *
            ∫ z, regularizedInvSquare ε z
              ∂paperMeasure := by
        exact mul_le_mul_of_nonneg_left hsetReg
          (mul_nonneg hBfix.le hL.le)
      _ ≤ Bfix * L * (Creg * (1 + L)) := by
        exact mul_le_mul_of_nonneg_left hregTotal
          (mul_nonneg hBfix.le hL.le)
      _ ≤ Bfix * L * (Creg * (2 * L)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left
            (by linarith : 1 + L ≤ 2 * L)
            hCreg.le
        · exact mul_nonneg hBfix.le hL.le
      _ = Koutside * L ^ 2 := by
        dsimp only [Koutside]
        ring

  by_cases hclose : ‖x‖ ≤ 4 * ε
  · /- At the regularization scale, use a radius-`2ε` ball about the
    moving logarithmic singularity. -/
    let r : ℝ := 2 * ε
    let B : Set T4 := Metric.ball x r
    let g : T4 → ℝ := fun z =>
      ε⁻¹ ^ (4 : ℕ) *
        criticalLogWeight (x - z)
    have hr : 0 < r := by
      dsimp only [r]
      positivity
    have hB : MeasurableSet B :=
      measurableSet_ball
    have hg : Integrable g paperMeasure := by
      dsimp only [g]
      exact hweight.const_mul (ε⁻¹ ^ (4 : ℕ))
    have hpoint :
        ∀ z ∈ B, f z ≤ g z := by
      intro z _hz
      dsimp only [f, g]
      exact mul_le_mul_of_nonneg_right
        (regularizedInvSquare_le_inv_four ε hε z)
        (criticalLogWeight_nonneg (x - z))
    have hmono :
        (∫ z in B, f z ∂paperMeasure) ≤
          ∫ z in B, g z ∂paperMeasure :=
      setIntegral_mono_on
        hf.integrableOn hg.integrableOn hB hpoint
    have hball :=
      hlogBall x r hr
    have hlogMul :
        |Real.log (2 * ε)| ≤
          |Real.log 2| + L := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        hε.ne']
      dsimp only [L]
      exact abs_add_le _ _
    have hscaleLog :
        3 + |Real.log (2 * ε)| ≤
          (4 + |Real.log 2|) * L := by
      nlinarith [abs_nonneg (Real.log 2)]
    have hballBound :
        (∫ z in B, f z ∂paperMeasure) ≤
          Kclose * L ^ 2 := by
      calc
        (∫ z in B, f z ∂paperMeasure) ≤
            ∫ z in B, g z ∂paperMeasure :=
          hmono
        _ =
            ε⁻¹ ^ (4 : ℕ) *
              ∫ z in B,
                criticalLogWeight (x - z)
                  ∂paperMeasure := by
          dsimp only [g]
          rw [integral_const_mul]
        _ ≤
            ε⁻¹ ^ (4 : ℕ) *
              (Clog * r ^ 4 *
                (3 + |Real.log r|)) := by
          exact mul_le_mul_of_nonneg_left hball
            (by positivity)
        _ =
            16 * Clog *
              (3 + |Real.log (2 * ε)|) := by
          dsimp only [r]
          field_simp [hε.ne']
          ring
        _ ≤
            16 * Clog *
              ((4 + |Real.log 2|) * L) :=
          mul_le_mul_of_nonneg_left hscaleLog
            (mul_nonneg (by norm_num) hClog.le)
        _ =
            Kclose * L := by
          dsimp only [Kclose]
          ring
        _ ≤ Kclose * L ^ 2 := by
          exact mul_le_mul_of_nonneg_left
            (by nlinarith : L ≤ L ^ 2)
            hKclose
    have hout :
        (∫ z in Bᶜ, f z ∂paperMeasure) ≤
          Koutside * L ^ 2 := by
      apply houtside r
      dsimp only [r]
      exact le_rfl
    calc
      (∫ z, f z ∂paperMeasure) =
          (∫ z in B, f z ∂paperMeasure) +
            ∫ z in Bᶜ, f z ∂paperMeasure :=
        (integral_add_compl hB hf).symm
      _ ≤
          Kclose * L ^ 2 +
            Koutside * L ^ 2 :=
        add_le_add hballBound hout
      _ =
          (Kclose + Koutside) *
            |Real.log ε| ^ 2 := by
        dsimp only [L]
        ring
      _ ≤ K * |Real.log ε| ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (by
            dsimp only [K]
            nlinarith)
          (sq_nonneg |Real.log ε|)
  · /- Far from the regularized origin, use the radius `‖x‖ / 2`.
    On this moving ball every `z` stays at least that far from the
    origin, so the inverse fourth-power bound cancels its volume. -/
    have hxfar : 4 * ε < ‖x‖ :=
      lt_of_not_ge hclose
    let r : ℝ := ‖x‖ / 2
    let B : Set T4 := Metric.ball x r
    let g : T4 → ℝ := fun z =>
      r⁻¹ ^ (4 : ℕ) *
        criticalLogWeight (x - z)
    have hx : x ≠ 0 := by
      intro hxzero
      subst x
      rw [norm_zero] at hxfar
      linarith
    have hr : 0 < r := by
      dsimp only [r]
      positivity
    have hεr : ε ≤ r := by
      dsimp only [r]
      linarith
    have htwoεr : 2 * ε ≤ r := by
      dsimp only [r]
      linarith
    have hrUpper : r ≤ 2 := by
      have hxpi := norm_t4_le_pi x
      have hpifour := Real.pi_le_four
      dsimp only [r]
      linarith
    have hB : MeasurableSet B :=
      measurableSet_ball
    have hg : Integrable g paperMeasure := by
      dsimp only [g]
      exact hweight.const_mul (r⁻¹ ^ (4 : ℕ))
    have hpoint :
        ∀ z ∈ B, f z ≤ g z := by
      intro z hz
      have hzx : ‖x - z‖ < r := by
        have :
            dist z x < r := by
          simpa only [B, Metric.mem_ball] using hz
        simpa only [dist_eq_norm, norm_sub_rev] using this
      have hxtri : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
        calc
          ‖x‖ = ‖x - z + z‖ := by
            rw [sub_add_cancel]
          _ ≤ ‖x - z‖ + ‖z‖ :=
            norm_add_le _ _
      have hrz : r ≤ ‖z‖ := by
        dsimp only [r] at hzx hxtri ⊢
        linarith
      have hregPoint :=
        regularizedInvSquare_le_inv_radius_four
          hε hr z hεr hrz
      dsimp only [f, g]
      exact mul_le_mul_of_nonneg_right hregPoint
        (criticalLogWeight_nonneg (x - z))
    have hmono :
        (∫ z in B, f z ∂paperMeasure) ≤
          ∫ z in B, g z ∂paperMeasure :=
      setIntegral_mono_on
        hf.integrableOn hg.integrableOn hB hpoint
    have hball :=
      hlogBall x r hr
    have hlogr :
        |Real.log r| ≤ 2 * L := by
      by_cases hr1 : r ≤ 1
      · have hlogLower :
            Real.log ε ≤ Real.log r :=
          Real.log_le_log hε hεr
        have hlogrNonpos :
            Real.log r ≤ 0 :=
          Real.log_nonpos hr.le hr1
        rw [abs_of_nonpos hlogrNonpos, hlogε]
        linarith
      · have hrOne : 1 ≤ r :=
          le_of_not_ge hr1
        have hlogrNonneg :
            0 ≤ Real.log r :=
          Real.log_nonneg hrOne
        have hlogrUpper :=
          Real.log_le_sub_one_of_pos hr
        rw [abs_of_nonneg hlogrNonneg]
        nlinarith
    have hscaleLog :
        3 + |Real.log r| ≤ 5 * L := by
      nlinarith
    have hballBound :
        (∫ z in B, f z ∂paperMeasure) ≤
          Kfar * L ^ 2 := by
      calc
        (∫ z in B, f z ∂paperMeasure) ≤
            ∫ z in B, g z ∂paperMeasure :=
          hmono
        _ =
            r⁻¹ ^ (4 : ℕ) *
              ∫ z in B,
                criticalLogWeight (x - z)
                  ∂paperMeasure := by
          dsimp only [g]
          rw [integral_const_mul]
        _ ≤
            r⁻¹ ^ (4 : ℕ) *
              (Clog * r ^ 4 *
                (3 + |Real.log r|)) := by
          exact mul_le_mul_of_nonneg_left hball
            (by positivity)
        _ =
            Clog * (3 + |Real.log r|) := by
          field_simp [hr.ne']
        _ ≤ Clog * (5 * L) :=
          mul_le_mul_of_nonneg_left hscaleLog hClog.le
        _ = Kfar * L := by
          dsimp only [Kfar]
          ring
        _ ≤ Kfar * L ^ 2 := by
          exact mul_le_mul_of_nonneg_left
            (by nlinarith : L ≤ L ^ 2)
            hKfar
    have hout :
        (∫ z in Bᶜ, f z ∂paperMeasure) ≤
          Koutside * L ^ 2 :=
      houtside r htwoεr
    calc
      (∫ z, f z ∂paperMeasure) =
          (∫ z in B, f z ∂paperMeasure) +
            ∫ z in Bᶜ, f z ∂paperMeasure :=
        (integral_add_compl hB hf).symm
      _ ≤
          Kfar * L ^ 2 +
            Koutside * L ^ 2 :=
        add_le_add hballBound hout
      _ =
          (Kfar + Koutside) *
            |Real.log ε| ^ 2 := by
        dsimp only [L]
        ring
      _ ≤ K * |Real.log ε| ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (by
            dsimp only [K]
            nlinarith)
          (sq_nonneg |Real.log ε|)

end

end Anderson4D
