import Anderson4D.DetParametrix.Paper42_Moment.R324DifferenceRetainingCore
import Anderson4D.Parametrix.CriticalGreenConvolution
import Anderson4D.Continuum.CutoffFourierDecay

/-!
# Cross-pairing complement core estimates at order two

The difference-retaining estimate reduces the order-two middle estimate to
the complement schedules: contractions whose within-half pairings are
trivial (`idPairingFinTwo` in both halves), so that no primitive
interval is extracted, no difference factor exists, and the two halves
are coupled only through the two cross-half covariance factors — the
paper §4.2 Step 3 cross-cut objects.

This file proves the scalar analytic core:

* `integral_charT4_mul_etaEpsT4_shift` — the exact translated
  covariance mode: `∫ charT4 b s · η_ε(v-s) = charT4 b v · (2π)⁴ ĉ(b)`;
* `integral_integral_charT4_greenFn_pair` — the two-variable
  Green–character orthogonality
  `∫∫ G(s-t) e_a(s) e_b(t) = (2π)⁴ ⟨b⟩⁻² [a+b=0]`;
* `integral_pi_crossHalf_eq_tsum` — the coupled half collapse: the
  half chain integrated against both cross covariances is the explicit
  diagonal mode series;
* `integral_crossCore_le_tsum` — the full cross-cut core
  `∫∫ G G η η = Σ_k ĉ(k)² ⟨k⟩⁻⁴`-type diagonal window, bounded by
  `Σ_k ‖ρ̂(εk)‖⁴ ⟨k⟩⁻⁴`;
* `exists_crossWindow_le_log` — the `ε`-supported window sum is
  `≤ C(ρ)·|log ε|`: the low cube `|k|∞ ≤ ⌈ε⁻¹⌉` contributes the
  harmonic-shell logarithm, and the tail is `O(1)` by the degree-8
  Schwartz decay of the mollifier symbol against the eighth-order
  radial tail.

The constant is uniform in `ε`, `λ`, and both external modes, but (in
contrast with the difference-retaining two-block bound) genuinely
depends on the mollifier: as the mollifier radius shrinks, the symbol
window widens to `|k| ≲ (radius·ε)⁻¹` and the diagonal sum grows like
`|log ε| + |log radius|`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## Character algebra on differences -/

theorem charT4_mul_charT4_neg_self (k : Z4) (x : T4) :
    charT4 k x * charT4 (-k) x = 1 := by
  rw [← charT4_add]
  simp

/-- Characters split across a difference of points. -/
theorem charT4_sub (k : Z4) (x y : T4) :
    charT4 k (x - y) = charT4 k x * charT4 (-k) y := by
  have h : charT4 k (x - y) * charT4 k y = charT4 k x := by
    rw [← charT4_point_add, sub_add_cancel]
  calc
    charT4 k (x - y) =
        charT4 k (x - y) * (charT4 k y * charT4 (-k) y) := by
      rw [charT4_mul_charT4_neg_self, mul_one]
    _ = (charT4 k (x - y) * charT4 k y) * charT4 (-k) y := by ring
    _ = charT4 k x * charT4 (-k) y := by rw [h]

theorem paperModeNormSq_neg (k : Z4) :
    paperModeNormSq (-k) = paperModeNormSq k := by
  unfold paperModeNormSq
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.neg_apply]
  push_cast
  ring

/-! ## The exact translated covariance mode -/

theorem integrable_charT4 (k : Z4) :
    Integrable (charT4 k) paperMeasure :=
  (continuous_charT4 k).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- **The translated covariance mode, exactly.**  Integrating one
character against a translated covariance extracts the base-point
character times the total-mass-normalized Fourier coefficient. -/
theorem integral_charT4_mul_etaEpsT4_shift
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (b : Z4) (v : T4) :
    (∫ s, charT4 b s * ((ρ.etaEpsT4 ε (v - s) : ℝ) : ℂ)
      ∂paperMeasure) =
      charT4 b v *
        ((((2 * Real.pi) ^ (dim : ℕ) : ℝ) : ℂ) *
          ρ.covarianceModeCoeff ε b) := by
  have hpoint :
      ∀ s : T4,
        charT4 b s * ((ρ.etaEpsT4 ε (v - s) : ℝ) : ℂ) =
          ∑' q : Z4,
            ρ.covarianceModeCoeff ε q * charT4 q v *
              charT4 (b + -q) s := by
    intro s
    have hseries := ρ.complexFourierCovarianceT4_eq_etaEpsT4 hε (v - s)
    unfold SmoothCutoff.complexFourierCovarianceT4 at hseries
    rw [← hseries, ← tsum_mul_left]
    apply tsum_congr
    intro q
    rw [charT4_sub, charT4_add]
    ring
  have hint : ∀ q : Z4,
      Integrable
        (fun s : T4 =>
          ρ.covarianceModeCoeff ε q * charT4 q v *
            charT4 (b + -q) s)
        paperMeasure :=
    fun q => (integrable_charT4 (b + -q)).const_mul _
  have hnorm : ∀ q : Z4,
      (∫ s, ‖ρ.covarianceModeCoeff ε q * charT4 q v *
          charT4 (b + -q) s‖ ∂paperMeasure) =
        ‖ρ.covarianceModeCoeff ε q‖ * (2 * Real.pi) ^ (dim : ℕ) := by
    intro q
    have hfun :
        (fun s : T4 =>
          ‖ρ.covarianceModeCoeff ε q * charT4 q v *
            charT4 (b + -q) s‖) =
          fun _ : T4 => ‖ρ.covarianceModeCoeff ε q‖ := by
      funext s
      rw [norm_mul, norm_mul, norm_charT4, norm_charT4,
        mul_one, mul_one]
    rw [hfun, integral_const, measureReal_def, paperMeasure_univ,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul, mul_comm]
  have hsummable :
      Summable fun q : Z4 =>
        ∫ s, ‖ρ.covarianceModeCoeff ε q * charT4 q v *
          charT4 (b + -q) s‖ ∂paperMeasure := by
    refine ((ρ.summable_norm_covarianceModeCoeff hε).mul_right
      ((2 * Real.pi) ^ (dim : ℕ))).congr fun q => ?_
    exact (hnorm q).symm
  have hswap := integral_tsum_of_summable_integral_norm hint hsummable
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), ← hswap]
  have hterm : ∀ q : Z4,
      (∫ s, ρ.covarianceModeCoeff ε q * charT4 q v *
          charT4 (b + -q) s ∂paperMeasure) =
        if q = b then
          charT4 b v *
            ((((2 * Real.pi) ^ (dim : ℕ) : ℝ) : ℂ) *
              ρ.covarianceModeCoeff ε b)
        else 0 := by
    intro q
    rw [integral_const_mul, integral_charT4_paper]
    by_cases hq : q = b
    · subst hq
      rw [if_pos (by abel), if_pos rfl]
      ring
    · rw [if_neg ?_, if_neg hq, mul_zero]
      intro h0
      apply hq
      have : b = q := by
        have h := congrArg (fun t => t + q) h0
        simpa using h
      exact this.symm
  rw [tsum_congr hterm, tsum_eq_single b ?_, if_pos rfl]
  intro q hq
  rw [if_neg hq]

/-! ## Two-variable Green--character orthogonality -/

/-- The Green pair kernel is integrable on the product. -/
theorem integrable_greenFn_pair :
    Integrable (fun p : T4 × T4 => greenFn (p.1 - p.2))
      (paperMeasure.prod paperMeasure) := by
  have hmeas :
      AEStronglyMeasurable (fun p : T4 × T4 => greenFn (p.1 - p.2))
        (paperMeasure.prod paperMeasure) :=
    (measurable_greenFn.comp
      (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with s
    have hflip :
        (fun t : T4 => greenFn (s - t)) =
          fun t : T4 => greenFn (t - s) := by
      funext t
      rw [show s - t = -(t - s) by abel, greenFn_memE.neg_invariant]
    rw [hflip]
    exact integrable_greenFn_sub s
  · have hfun :
        (fun s : T4 => ∫ t, ‖greenFn (s - t)‖ ∂paperMeasure) =
          fun _ : T4 => (1 : ℝ) := by
      funext s
      have hpt : ∀ t : T4, ‖greenFn (s - t)‖ = greenFn (s - t) := by
        intro t
        rw [Real.norm_eq_abs, abs_of_nonneg (greenFn_nonneg _)]
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_greenFn_shift_left]
    rw [hfun]
    exact integrable_const 1

/-- **Two-variable Green--character orthogonality.**  The double
integral of the Green edge against two characters is diagonal: it
vanishes unless the two modes cancel, and then carries one boundary
coefficient and one paper volume. -/
theorem integral_integral_charT4_greenFn_pair (a b : Z4) :
    (∫ s, ∫ t,
        charT4 a s * charT4 b t * ((greenFn (s - t) : ℝ) : ℂ)
      ∂paperMeasure ∂paperMeasure) =
      if a + b = 0 then
        ((((2 * Real.pi) ^ (dim : ℕ) *
          (1 + paperModeNormSq b)⁻¹ : ℝ)) : ℂ)
      else 0 := by
  have hinner : ∀ s : T4,
      (∫ t,
          charT4 a s * charT4 b t * ((greenFn (s - t) : ℝ) : ℂ)
        ∂paperMeasure) =
        (((1 + paperModeNormSq b)⁻¹ : ℝ) : ℂ) *
          charT4 (a + b) s := by
    intro s
    have hassoc : ∀ t : T4,
        charT4 a s * charT4 b t * ((greenFn (s - t) : ℝ) : ℂ) =
          charT4 a s *
            (charT4 b t * ((greenFn (s - t) : ℝ) : ℂ)) := by
      intro t
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hassoc),
      integral_const_mul, integral_charT4_mul_greenFn_shift,
      charT4_add]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner),
    integral_const_mul, integral_charT4_paper]
  by_cases hab : a + b = 0
  · rw [if_pos hab, if_pos hab]
    push_cast
    ring
  · rw [if_neg hab, if_neg hab, mul_zero]

/-! ## Translated covariance mass -/

theorem integrable_etaEpsT4_sub (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (z : T4) :
    Integrable (fun x : T4 => ρ.etaEpsT4 ε (x - z)) paperMeasure := by
  have hη := ρ.integrable_etaEpsT4_paper hε hε1
  rw [paperMeasure_eq_volume] at hη ⊢
  have h :=
    (measurePreserving_add_right (volume : Measure T4) (-z)).integrable_comp
      hη.aestronglyMeasurable
  simpa only [Function.comp_def, sub_eq_add_neg] using h.mpr hη

theorem integral_etaEpsT4_sub_le_one (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (z : T4) :
    (∫ x, ρ.etaEpsT4 ε (x - z) ∂paperMeasure) ≤ 1 := by
  have hshift :
      (∫ x, ρ.etaEpsT4 ε (x - z) ∂paperMeasure) =
        ∫ x, ρ.etaEpsT4 ε x ∂paperMeasure := by
    rw [paperMeasure_eq_volume]
    simpa only [sub_eq_add_neg] using
      integral_add_right_eq_self (fun x => ρ.etaEpsT4 ε x) (-z)
  rw [hshift]
  exact integral_etaEpsT4_paper_le_one ρ hε

/-! ## The coupled cross-half collapse -/

/-- The diagonal coefficient of one cross-cut covariance pairing: one
boundary Green weight, one paper volume, and the squared covariance
mode. -/
def r324CrossPairCoefficient
    (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) : ℂ :=
  (((1 + paperModeNormSq k)⁻¹ : ℝ) : ℂ) *
    (((2 * Real.pi) ^ (dim : ℕ) : ℝ) : ℂ) *
    ρ.covarianceModeCoeff ε k ^ 2

/-- **The coupled half collapses to a diagonal mode series.**  The
half chain edge is integrated jointly with both cross covariances; the
two internal integrals produce one Green coefficient and one squared
covariance coefficient on the *same* mode, tied to the two coupling
points by opposite characters. -/
theorem integral_integral_greenFn_etaPair_eq_tsum
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (p q : T4) :
    (∫ t, ∫ s,
        ((greenFn (s - t) *
          (ρ.etaEpsT4 ε (s - p) * ρ.etaEpsT4 ε (t - q)) : ℝ) : ℂ)
      ∂paperMeasure ∂paperMeasure) =
      ∑' k : Z4,
        r324CrossPairCoefficient ρ ε k *
          (charT4 (-k) p * charT4 k q) := by
  obtain ⟨Cη, hCη, hηbound⟩ := ρ.exists_pos_etaEpsT4_uniform_bound
  set Mη : ℝ := ε⁻¹ ^ (dim : ℕ) * Cη with hMηdef
  have hMη : 0 ≤ Mη := by positivity
  have hinner : ∀ t : T4,
      (∫ s,
          ((greenFn (s - t) *
            (ρ.etaEpsT4 ε (s - p) * ρ.etaEpsT4 ε (t - q)) : ℝ) : ℂ)
        ∂paperMeasure) =
        ∑' k : Z4,
          (ρ.covarianceModeCoeff ε k * charT4 (-k) p *
              (((1 + paperModeNormSq k)⁻¹ : ℝ) : ℂ)) *
            (charT4 k t * ((ρ.etaEpsT4 ε (t - q) : ℝ) : ℂ)) := by
    intro t
    have hpoint : ∀ s : T4,
        ((greenFn (s - t) *
          (ρ.etaEpsT4 ε (s - p) * ρ.etaEpsT4 ε (t - q)) : ℝ) : ℂ) =
          ∑' k : Z4,
            (ρ.covarianceModeCoeff ε k * charT4 (-k) p *
                ((ρ.etaEpsT4 ε (t - q) : ℝ) : ℂ)) *
              (charT4 k s * ((greenFn (s - t) : ℝ) : ℂ)) := by
      intro s
      have hη₁ : ((ρ.etaEpsT4 ε (s - p) : ℝ) : ℂ) =
          ∑' k : Z4,
            ρ.covarianceModeCoeff ε k * charT4 k s *
              charT4 (-k) p := by
        rw [← ρ.complexFourierCovarianceT4_eq_etaEpsT4 hε (s - p)]
        unfold SmoothCutoff.complexFourierCovarianceT4
        apply tsum_congr
        intro k
        rw [charT4_sub]
        ring
      calc
        ((greenFn (s - t) *
            (ρ.etaEpsT4 ε (s - p) * ρ.etaEpsT4 ε (t - q)) : ℝ) : ℂ) =
            ((ρ.etaEpsT4 ε (s - p) : ℝ) : ℂ) *
              (((ρ.etaEpsT4 ε (t - q) : ℝ) : ℂ) *
                ((greenFn (s - t) : ℝ) : ℂ)) := by
          push_cast
          ring
        _ = ∑' k : Z4,
              (ρ.covarianceModeCoeff ε k * charT4 k s *
                  charT4 (-k) p) *
                (((ρ.etaEpsT4 ε (t - q) : ℝ) : ℂ) *
                  ((greenFn (s - t) : ℝ) : ℂ)) := by
          rw [hη₁, ← tsum_mul_right]
        _ = _ := by
          apply tsum_congr
          intro k
          ring
    have hint : ∀ k : Z4,
        Integrable
          (fun s : T4 =>
            (ρ.covarianceModeCoeff ε k * charT4 (-k) p *
                ((ρ.etaEpsT4 ε (t - q) : ℝ) : ℂ)) *
              (charT4 k s * ((greenFn (s - t) : ℝ) : ℂ)))
          paperMeasure :=
      fun k => (integrable_charT4_mul_greenFn_sub k t).const_mul _
    have hsummable :
        Summable fun k : Z4 =>
          ∫ s, ‖(ρ.covarianceModeCoeff ε k * charT4 (-k) p *
              ((ρ.etaEpsT4 ε (t - q) : ℝ) : ℂ)) *
            (charT4 k s * ((greenFn (s - t) : ℝ) : ℂ))‖
            ∂paperMeasure := by
      refine Summable.of_nonneg_of_le
        (fun k => integral_nonneg fun s => norm_nonneg _)
        (fun k => ?_)
        ((ρ.summable_norm_covarianceModeCoeff hε).mul_right Mη)
      have hpt : ∀ s : T4,
          ‖(ρ.covarianceModeCoeff ε k * charT4 (-k) p *
              ((ρ.etaEpsT4 ε (t - q) : ℝ) : ℂ)) *
            (charT4 k s * ((greenFn (s - t) : ℝ) : ℂ))‖ ≤
            (‖ρ.covarianceModeCoeff ε k‖ * Mη) * greenFn (s - t) := by
        intro s
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_charT4,
          norm_charT4, mul_one, one_mul, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (ρ.etaEpsT4_nonneg ε _),
          abs_of_nonneg (greenFn_nonneg _)]
        have hη := hηbound hε hε1 (t - q)
        have hG := greenFn_nonneg (s - t)
        have hc := norm_nonneg (ρ.covarianceModeCoeff ε k)
        calc
          ‖ρ.covarianceModeCoeff ε k‖ * ρ.etaEpsT4 ε (t - q) *
              greenFn (s - t) ≤
              ‖ρ.covarianceModeCoeff ε k‖ * Mη * greenFn (s - t) := by
            apply mul_le_mul_of_nonneg_right _ hG
            exact mul_le_mul_of_nonneg_left (by rw [hMηdef]; exact hη) hc
          _ = (‖ρ.covarianceModeCoeff ε k‖ * Mη) * greenFn (s - t) := by
            ring
      calc
        (∫ s, ‖(ρ.covarianceModeCoeff ε k * charT4 (-k) p *
              ((ρ.etaEpsT4 ε (t - q) : ℝ) : ℂ)) *
            (charT4 k s * ((greenFn (s - t) : ℝ) : ℂ))‖
            ∂paperMeasure) ≤
            ∫ s, (‖ρ.covarianceModeCoeff ε k‖ * Mη) * greenFn (s - t)
              ∂paperMeasure := by
          apply integral_mono_ae
          · exact (hint k).norm
          · exact (integrable_greenFn_sub t).const_mul _
          · exact Filter.Eventually.of_forall hpt
        _ = ‖ρ.covarianceModeCoeff ε k‖ * Mη := by
          rw [integral_const_mul, integral_greenFn_sub, mul_one]
    have hswap := integral_tsum_of_summable_integral_norm hint hsummable
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), ← hswap]
    apply tsum_congr
    intro k
    rw [integral_const_mul]
    have hflip :
        (fun s : T4 => charT4 k s * ((greenFn (s - t) : ℝ) : ℂ)) =
          fun s : T4 => charT4 k s * ((greenFn (t - s) : ℝ) : ℂ) := by
      funext s
      rw [show s - t = -(t - s) by abel, greenFn_memE.neg_invariant]
    rw [hflip, integral_charT4_mul_greenFn_shift]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
  have hint₂ : ∀ k : Z4,
      Integrable
        (fun t : T4 =>
          (ρ.covarianceModeCoeff ε k * charT4 (-k) p *
              (((1 + paperModeNormSq k)⁻¹ : ℝ) : ℂ)) *
            (charT4 k t * ((ρ.etaEpsT4 ε (t - q) : ℝ) : ℂ)))
        paperMeasure := by
    intro k
    refine (((integrable_etaEpsT4_sub ρ hε hε1 q).ofReal).bdd_mul
      (c := 1) (continuous_charT4 k).aestronglyMeasurable ?_).const_mul _
    filter_upwards with t
    rw [norm_charT4]
  have hsummable₂ :
      Summable fun k : Z4 =>
        ∫ t, ‖(ρ.covarianceModeCoeff ε k * charT4 (-k) p *
            (((1 + paperModeNormSq k)⁻¹ : ℝ) : ℂ)) *
          (charT4 k t * ((ρ.etaEpsT4 ε (t - q) : ℝ) : ℂ))‖
          ∂paperMeasure := by
    refine Summable.of_nonneg_of_le
      (fun k => integral_nonneg fun t => norm_nonneg _)
      (fun k => ?_)
      (ρ.summable_norm_covarianceModeCoeff hε)
    have hcoef :
        ‖(((1 + paperModeNormSq k)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h0 := paperModeNormSq_nonneg k
      rw [abs_of_nonneg (by positivity)]
      rw [inv_le_one_iff₀]
      right
      linarith
    have hpt : ∀ t : T4,
        ‖(ρ.covarianceModeCoeff ε k * charT4 (-k) p *
            (((1 + paperModeNormSq k)⁻¹ : ℝ) : ℂ)) *
          (charT4 k t * ((ρ.etaEpsT4 ε (t - q) : ℝ) : ℂ))‖ ≤
          ‖ρ.covarianceModeCoeff ε k‖ * ρ.etaEpsT4 ε (t - q) := by
      intro t
      have hE : ‖((ρ.etaEpsT4 ε (t - q) : ℝ) : ℂ)‖ =
          ρ.etaEpsT4 ε (t - q) := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (ρ.etaEpsT4_nonneg ε _)]
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_charT4,
        norm_charT4, mul_one, one_mul, hE]
      have hc := norm_nonneg (ρ.covarianceModeCoeff ε k)
      have hη := ρ.etaEpsT4_nonneg ε (t - q)
      calc
        ‖ρ.covarianceModeCoeff ε k‖ *
            ‖(((1 + paperModeNormSq k)⁻¹ : ℝ) : ℂ)‖ *
            ρ.etaEpsT4 ε (t - q) ≤
            ‖ρ.covarianceModeCoeff ε k‖ * 1 * ρ.etaEpsT4 ε (t - q) := by
          apply mul_le_mul_of_nonneg_right _ hη
          exact mul_le_mul_of_nonneg_left hcoef hc
        _ = ‖ρ.covarianceModeCoeff ε k‖ * ρ.etaEpsT4 ε (t - q) := by
          ring
    calc
      (∫ t, ‖(ρ.covarianceModeCoeff ε k * charT4 (-k) p *
            (((1 + paperModeNormSq k)⁻¹ : ℝ) : ℂ)) *
          (charT4 k t * ((ρ.etaEpsT4 ε (t - q) : ℝ) : ℂ))‖
          ∂paperMeasure) ≤
          ∫ t, ‖ρ.covarianceModeCoeff ε k‖ * ρ.etaEpsT4 ε (t - q)
            ∂paperMeasure := by
        apply integral_mono_ae
        · exact (hint₂ k).norm
        · exact (integrable_etaEpsT4_sub ρ hε hε1 q).const_mul _
        · exact Filter.Eventually.of_forall hpt
      _ = ‖ρ.covarianceModeCoeff ε k‖ *
            ∫ t, ρ.etaEpsT4 ε (t - q) ∂paperMeasure :=
        integral_const_mul _ _
      _ ≤ ‖ρ.covarianceModeCoeff ε k‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (integral_etaEpsT4_sub_le_one ρ hε q) (norm_nonneg _)
      _ = ‖ρ.covarianceModeCoeff ε k‖ := mul_one _
  have hswap₂ := integral_tsum_of_summable_integral_norm hint₂ hsummable₂
  rw [← hswap₂]
  apply tsum_congr
  intro k
  rw [integral_const_mul]
  have hflip :
      (fun t : T4 =>
        charT4 k t * ((ρ.etaEpsT4 ε (t - q) : ℝ) : ℂ)) =
        fun t : T4 =>
          charT4 k t * ((ρ.etaEpsT4 ε (q - t) : ℝ) : ℂ) := by
    funext t
    rw [show t - q = -(q - t) by abel,
      (ρ.etaEpsT4_memE ε).neg_invariant]
  rw [hflip, integral_charT4_mul_etaEpsT4_shift ρ hε]
  unfold r324CrossPairCoefficient
  ring

/-! ## The outer cross-cut collapse -/

theorem integral_prod_greenFn :
    (∫ r : T4 × T4, greenFn (r.1 - r.2)
      ∂(paperMeasure.prod paperMeasure)) =
      (2 * Real.pi) ^ (dim : ℕ) := by
  rw [integral_prod _ integrable_greenFn_pair]
  have hinner : ∀ s : T4,
      (∫ t, greenFn (s - t) ∂paperMeasure) = 1 := fun s =>
    integral_greenFn_shift_left s
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner),
    integral_const, measureReal_def, paperMeasure_univ,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul, mul_one]

/-- Product form of the two-variable Green--character orthogonality. -/
theorem integral_prod_charPair_greenFn (a b : Z4) :
    (∫ r : T4 × T4,
        (charT4 a r.1 * charT4 b r.2) *
          ((greenFn (r.1 - r.2) : ℝ) : ℂ)
      ∂(paperMeasure.prod paperMeasure)) =
      if a + b = 0 then
        ((((2 * Real.pi) ^ (dim : ℕ) *
          (1 + paperModeNormSq b)⁻¹ : ℝ)) : ℂ)
      else 0 := by
  have hint :
      Integrable
        (fun r : T4 × T4 =>
          (charT4 a r.1 * charT4 b r.2) *
            ((greenFn (r.1 - r.2) : ℝ) : ℂ))
        (paperMeasure.prod paperMeasure) := by
    have hbase :
        Integrable
          (fun r : T4 × T4 => ((greenFn (r.1 - r.2) : ℝ) : ℂ))
          (paperMeasure.prod paperMeasure) :=
      integrable_greenFn_pair.ofReal
    have hmeas :
        AEStronglyMeasurable
          (fun r : T4 × T4 => charT4 a r.1 * charT4 b r.2)
          (paperMeasure.prod paperMeasure) :=
      (((continuous_charT4 a).comp continuous_fst).mul
        ((continuous_charT4 b).comp continuous_snd)).aestronglyMeasurable
    refine (hbase.bdd_mul (c := 1) hmeas ?_)
    filter_upwards with r
    rw [norm_mul, norm_charT4, norm_charT4, mul_one]
  rw [← integral_integral_charT4_greenFn_pair a b,
    integral_prod _ hint]

theorem norm_r324CrossPairCoefficient_le
    (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    ‖r324CrossPairCoefficient ρ ε k‖ ≤
      ‖ρ.covarianceModeCoeff ε k‖ := by
  unfold r324CrossPairCoefficient
  have hP := paperModeNormSq_nonneg k
  have hc : ‖ρ.covarianceModeCoeff ε k‖ ≤
      NoiseModel.whiteNoiseFourierScale ^ 2 := by
    rw [ρ.norm_covarianceModeCoeff]
    calc
      NoiseModel.whiteNoiseFourierScale ^ 2 * ‖ρ.symbol ε k‖ ^ 2 ≤
          NoiseModel.whiteNoiseFourierScale ^ 2 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h := ρ.norm_symbol_le_one ε k
        nlinarith [norm_nonneg (ρ.symbol ε k)]
      _ = NoiseModel.whiteNoiseFourierScale ^ 2 := mul_one _
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + paperModeNormSq k)⁻¹),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 * Real.pi) ^ (dim : ℕ))]
  have hinv : (1 + paperModeNormSq k)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    linarith
  calc
    (1 + paperModeNormSq k)⁻¹ * (2 * Real.pi) ^ (dim : ℕ) *
        ‖ρ.covarianceModeCoeff ε k‖ ^ 2 ≤
        1 * (2 * Real.pi) ^ (dim : ℕ) *
          (NoiseModel.whiteNoiseFourierScale ^ 2 *
            ‖ρ.covarianceModeCoeff ε k‖) := by
      have hnn := norm_nonneg (ρ.covarianceModeCoeff ε k)
      have hsq :
          ‖ρ.covarianceModeCoeff ε k‖ ^ 2 ≤
            NoiseModel.whiteNoiseFourierScale ^ 2 *
              ‖ρ.covarianceModeCoeff ε k‖ := by
        calc
          ‖ρ.covarianceModeCoeff ε k‖ ^ 2 =
              ‖ρ.covarianceModeCoeff ε k‖ *
                ‖ρ.covarianceModeCoeff ε k‖ := sq _
          _ ≤ NoiseModel.whiteNoiseFourierScale ^ 2 *
              ‖ρ.covarianceModeCoeff ε k‖ :=
            mul_le_mul_of_nonneg_right hc hnn
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hinv (by positivity)
      · exact hsq
      · positivity
      · positivity
    _ = (2 * Real.pi) ^ (dim : ℕ) *
          NoiseModel.whiteNoiseFourierScale ^ 2 *
          ‖ρ.covarianceModeCoeff ε k‖ := by ring
    _ = ‖ρ.covarianceModeCoeff ε k‖ := by
      rw [mul_comm ((2 * Real.pi) ^ (dim : ℕ))
        (NoiseModel.whiteNoiseFourierScale ^ 2),
        whiteNoiseFourierScale_sq_mul_pow_dim, one_mul]

/-- **The outer cross-cut collapse.**  The second half chain edge
integrated against the diagonal mode series of the collapsed first
half: every mode pairs its opposite characters across the outer edge
and receives the second boundary Green coefficient.  The two possible
cross matchings differ only in the character arrangement, absorbed by
the hypotheses. -/
theorem integral_prod_greenFn_mul_tsum_crossModes
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (a b : Z4 → Z4)
    (hab : ∀ k, a k + b k = 0)
    (hbP : ∀ k, paperModeNormSq (b k) = paperModeNormSq k) :
    (∫ r : T4 × T4,
        ((greenFn (r.1 - r.2) : ℝ) : ℂ) *
          ∑' k : Z4,
            r324CrossPairCoefficient ρ ε k *
              (charT4 (a k) r.1 * charT4 (b k) r.2)
      ∂(paperMeasure.prod paperMeasure)) =
      ∑' k : Z4,
        r324CrossPairCoefficient ρ ε k *
          ((((2 * Real.pi) ^ (dim : ℕ) *
            (1 + paperModeNormSq k)⁻¹ : ℝ)) : ℂ) := by
  have hpoint : ∀ r : T4 × T4,
      ((greenFn (r.1 - r.2) : ℝ) : ℂ) *
          ∑' k : Z4,
            r324CrossPairCoefficient ρ ε k *
              (charT4 (a k) r.1 * charT4 (b k) r.2) =
        ∑' k : Z4,
          r324CrossPairCoefficient ρ ε k *
            ((charT4 (a k) r.1 * charT4 (b k) r.2) *
              ((greenFn (r.1 - r.2) : ℝ) : ℂ)) := by
    intro r
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    ring
  have hint : ∀ k : Z4,
      Integrable
        (fun r : T4 × T4 =>
          r324CrossPairCoefficient ρ ε k *
            ((charT4 (a k) r.1 * charT4 (b k) r.2) *
              ((greenFn (r.1 - r.2) : ℝ) : ℂ)))
        (paperMeasure.prod paperMeasure) := by
    intro k
    have hmeas :
        AEStronglyMeasurable
          (fun r : T4 × T4 => charT4 (a k) r.1 * charT4 (b k) r.2)
          (paperMeasure.prod paperMeasure) :=
      (((continuous_charT4 (a k)).comp continuous_fst).mul
        ((continuous_charT4 (b k)).comp
          continuous_snd)).aestronglyMeasurable
    refine ((integrable_greenFn_pair.ofReal.bdd_mul (c := 1)
      hmeas ?_).const_mul _)
    filter_upwards with r
    rw [norm_mul, norm_charT4, norm_charT4, mul_one]
  have hnorm : ∀ k : Z4,
      (∫ r : T4 × T4,
          ‖r324CrossPairCoefficient ρ ε k *
            ((charT4 (a k) r.1 * charT4 (b k) r.2) *
              ((greenFn (r.1 - r.2) : ℝ) : ℂ))‖
        ∂(paperMeasure.prod paperMeasure)) =
        ‖r324CrossPairCoefficient ρ ε k‖ *
          (2 * Real.pi) ^ (dim : ℕ) := by
    intro k
    have hfun :
        (fun r : T4 × T4 =>
          ‖r324CrossPairCoefficient ρ ε k *
            ((charT4 (a k) r.1 * charT4 (b k) r.2) *
              ((greenFn (r.1 - r.2) : ℝ) : ℂ))‖) =
          fun r : T4 × T4 =>
            ‖r324CrossPairCoefficient ρ ε k‖ *
              greenFn (r.1 - r.2) := by
      funext r
      rw [norm_mul, norm_mul, norm_mul, norm_charT4, norm_charT4,
        mul_one, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (greenFn_nonneg _)]
    rw [hfun, integral_const_mul, integral_prod_greenFn]
  have hsummable :
      Summable fun k : Z4 =>
        ∫ r : T4 × T4,
          ‖r324CrossPairCoefficient ρ ε k *
            ((charT4 (a k) r.1 * charT4 (b k) r.2) *
              ((greenFn (r.1 - r.2) : ℝ) : ℂ))‖
          ∂(paperMeasure.prod paperMeasure) := by
    refine Summable.of_nonneg_of_le
      (fun k => integral_nonneg fun r => norm_nonneg _)
      (fun k => ?_)
      ((ρ.summable_norm_covarianceModeCoeff hε).mul_right
        ((2 * Real.pi) ^ (dim : ℕ)))
    rw [hnorm k]
    exact mul_le_mul_of_nonneg_right
      (norm_r324CrossPairCoefficient_le ρ ε k) (by positivity)
  have hswap := integral_tsum_of_summable_integral_norm hint hsummable
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), ← hswap]
  apply tsum_congr
  intro k
  rw [integral_const_mul, integral_prod_charPair_greenFn,
    if_pos (hab k), hbP k]

/-! ## The `ε`-supported diagonal window -/

theorem paperModeNormSq_eq_and_supRadius_le (k : Z4) :
    ((z4SupRadius k : ℝ)) ^ 2 ≤ paperModeNormSq k := by
  obtain ⟨i₀, _hi₀, hsup⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin dim))
      ⟨0, Finset.mem_univ 0⟩ (fun i => Int.natAbs (k i))
  have hcoord : ((z4SupRadius k : ℝ)) ^ 2 = ((k i₀ : ℝ)) ^ 2 := by
    unfold z4SupRadius
    rw [hsup]
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rw [hcoord]
  unfold paperModeNormSq
  exact Finset.single_le_sum
    (f := fun i => ((k i : ℝ)) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ i₀)

/-- The Euclidean bracket dominated by the sup bracket:
`(1+P)⁻¹ ≤ 2 (1+s)⁻²`. -/
theorem inv_one_add_paperModeNormSq_le (k : Z4) :
    (1 + paperModeNormSq k)⁻¹ ≤
      2 * ((1 + (z4SupRadius k : ℝ)) ^ 2)⁻¹ := by
  set s : ℝ := (z4SupRadius k : ℝ) with hsdef
  have hs : 0 ≤ s := Nat.cast_nonneg _
  have hP : s ^ 2 ≤ paperModeNormSq k := by
    rw [hsdef]
    exact paperModeNormSq_eq_and_supRadius_le k
  have hP0 := paperModeNormSq_nonneg k
  have hkey : (1 + s) ^ 2 / 2 ≤ 1 + paperModeNormSq k := by
    nlinarith [sq_nonneg (s - 1)]
  calc
    (1 + paperModeNormSq k)⁻¹ ≤ ((1 + s) ^ 2 / 2)⁻¹ :=
      inv_anti₀ (by positivity) hkey
    _ = 2 * ((1 + s) ^ 2)⁻¹ := by
      rw [inv_div]
      ring

/-- Degree-two decay of the scaled symbol against the sup bracket,
uniformly in the scale: `‖ρ̂(εk)‖ ≤ 2π C₀ ε⁻¹ (1+s)⁻¹`-squared form. -/
theorem symbol_sq_le_of_decay
    (ρ : SmoothCutoff) {C0 : ℝ}
    (hdecay : ∀ ξ : R4,
      (1 + ‖SmoothCutoff.euclideanFrequency ξ‖) ^ 8 *
        ‖fourierR4 ρ ξ‖ ≤ C0)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (k : Z4) :
    ‖ρ.symbol ε k‖ ^ 2 ≤
      (C0 ^ 2 * (2 * Real.pi) ^ 4) *
        (ε⁻¹ ^ 4 * (((1 + (z4SupRadius k : ℝ)) ^ 4)⁻¹)) := by
  set ξ : R4 := fun i => ε * (k i : ℝ) with hξdef
  set w := SmoothCutoff.euclideanFrequency ξ with hwdef
  set s : ℝ := (z4SupRadius k : ℝ) with hsdef
  have hs : 0 ≤ s := Nat.cast_nonneg _
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have hC0 : 0 ≤ C0 := by
    have h := hdecay 0
    have h1 : 0 ≤
        (1 + ‖SmoothCutoff.euclideanFrequency (0 : R4)‖) ^ 8 := by
      positivity
    nlinarith [norm_nonneg (fourierR4 ρ (0 : R4)),
      norm_nonneg (SmoothCutoff.euclideanFrequency (0 : R4))]
  have hsym : ‖ρ.symbol ε k‖ = ‖fourierR4 ρ ξ‖ := rfl
  have hwlow : ε / (2 * Real.pi) * s ≤ ‖w‖ := by
    obtain ⟨i₀, _hi₀, hsup⟩ :=
      Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin dim))
        ⟨0, Finset.mem_univ 0⟩ (fun i => Int.natAbs (k i))
    have hcoord : ε / (2 * Real.pi) * s = ‖w i₀‖ := by
      rw [hsdef]
      unfold z4SupRadius
      rw [hsup]
      simp only [hwdef, hξdef,
        SmoothCutoff.euclideanFrequency_apply, Real.norm_eq_abs]
      rw [abs_div, abs_mul, abs_of_pos hε,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
        Nat.cast_natAbs, Int.cast_abs]
      field_simp
    rw [hcoord]
    exact PiLp.norm_apply_le w i₀
  have hbracket : ε / (2 * Real.pi) * (1 + s) ≤ 1 + ‖w‖ := by
    have hone : ε / (2 * Real.pi) ≤ 1 := by
      have hπ : (1 : ℝ) ≤ 2 * Real.pi := by
        nlinarith [Real.pi_gt_three]
      rw [div_le_one (by positivity)]
      linarith
    calc
      ε / (2 * Real.pi) * (1 + s) =
          ε / (2 * Real.pi) + ε / (2 * Real.pi) * s := by ring
      _ ≤ 1 + ‖w‖ := add_le_add hone hwlow
  have hsymle : ‖ρ.symbol ε k‖ ≤ C0 * ((1 + ‖w‖) ^ 2)⁻¹ := by
    have h8 := hdecay ξ
    rw [← hwdef, ← hsym] at h8
    have hpow : (1 + ‖w‖) ^ 2 ≤ (1 + ‖w‖) ^ 8 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    have h2 : (1 + ‖w‖) ^ 2 * ‖ρ.symbol ε k‖ ≤ C0 :=
      le_trans
        (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) h8
    rw [mul_comm, ← le_div_iff₀
      (by positivity : (0:ℝ) < (1 + ‖w‖) ^ 2), div_eq_mul_inv]
      at h2
    exact h2
  have hbr2 :
      ((1 + ‖w‖) ^ 2)⁻¹ ≤
        ((2 * Real.pi) ^ 2 * ε⁻¹ ^ 2) * ((1 + s) ^ 2)⁻¹ := by
    have hlhs : 0 < ε / (2 * Real.pi) * (1 + s) := by positivity
    have hinv :
        (1 + ‖w‖)⁻¹ ≤ (ε / (2 * Real.pi) * (1 + s))⁻¹ :=
      inv_anti₀ hlhs hbracket
    have hval :
        (ε / (2 * Real.pi) * (1 + s))⁻¹ =
          (2 * Real.pi) * ε⁻¹ * (1 + s)⁻¹ := by
      rw [mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
      ring
    have hsq :
        ((1 + ‖w‖)⁻¹) ^ 2 ≤
          ((2 * Real.pi) * ε⁻¹ * (1 + s)⁻¹) ^ 2 := by
      rw [← hval]
      exact pow_le_pow_left₀ (by positivity) hinv 2
    calc
      ((1 + ‖w‖) ^ 2)⁻¹ = ((1 + ‖w‖)⁻¹) ^ 2 := by
        rw [inv_pow]
      _ ≤ ((2 * Real.pi) * ε⁻¹ * (1 + s)⁻¹) ^ 2 := hsq
      _ = ((2 * Real.pi) ^ 2 * ε⁻¹ ^ 2) * ((1 + s) ^ 2)⁻¹ := by
        have h1s : (1 + s) ≠ 0 := by positivity
        field_simp
  have hfinal :
      (C0 * (((2 * Real.pi) ^ 2 * ε⁻¹ ^ 2) * ((1 + s) ^ 2)⁻¹)) ^ 2 =
        (C0 ^ 2 * (2 * Real.pi) ^ 4) *
          (ε⁻¹ ^ 4 * (((1 + s) ^ 4)⁻¹)) := by
    have h1s : (1 + s) ≠ 0 := by positivity
    field_simp
  calc
    ‖ρ.symbol ε k‖ ^ 2 ≤
        (C0 * (((2 * Real.pi) ^ 2 * ε⁻¹ ^ 2) *
          ((1 + s) ^ 2)⁻¹)) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      calc
        ‖ρ.symbol ε k‖ ≤ C0 * ((1 + ‖w‖) ^ 2)⁻¹ := hsymle
        _ ≤ C0 * (((2 * Real.pi) ^ 2 * ε⁻¹ ^ 2) *
              ((1 + s) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hbr2 hC0
    _ = (C0 ^ 2 * (2 * Real.pi) ^ 4) *
          (ε⁻¹ ^ 4 * (((1 + s) ^ 4)⁻¹)) := hfinal

/-- **The `ε`-supported diagonal window is logarithmic.**  Inside the
cube `|k|∞ ≤ ⌈ε⁻¹⌉` the unit symbol bound leaves the fourth-order
shell sum `≈ log`; outside, the degree-8 Schwartz decay of the symbol
converts four inverse powers of `ε` into the eighth-order radial tail
`≤ 20 (N+1)⁻⁴ ≤ 20 ε⁴`.  The constant depends only on the mollifier. -/
theorem exists_crossWindow_le_log (ρ : SmoothCutoff) :
    ∃ CW : ℝ, 0 < CW ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        (∑' k : Z4,
          ‖ρ.symbol ε k‖ ^ 4 *
            ((1 + paperModeNormSq k)⁻¹) ^ 2) ≤
          CW * |Real.log ε| := by
  obtain ⟨C0, hC0, hdecay⟩ := ρ.exists_fourierR4_one_add_norm_bound
  set TC : ℝ := 4 * (C0 ^ 2 * (2 * Real.pi) ^ 4) with hTCdef
  have hTC : 0 < TC := by rw [hTCdef]; positivity
  refine ⟨1280 + 20 * TC, by positivity, ?_⟩
  intro ε hε hε1 hlog
  set L : ℝ := |Real.log ε| with hLdef
  have hL1 : (1 : ℝ) ≤ L := hlog
  set N : ℕ := ⌈ε⁻¹⌉₊ with hNdef
  have hεinv1 : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
  have hNε : ε⁻¹ ≤ (N : ℝ) := Nat.le_ceil _
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_trans hεinv1 hNε
  have hNup : (N : ℝ) + 1 ≤ 3 * ε⁻¹ := by
    have hceil : (N : ℝ) < ε⁻¹ + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith
  set f : Z4 → ℝ := fun k =>
    ‖ρ.symbol ε k‖ ^ 4 * ((1 + paperModeNormSq k)⁻¹) ^ 2
    with hfdef
  set g : Z4 → ℝ := fun k =>
    if k ∈ z4Cube N then 4 * l2LatticeRadialWeight 4 k else 0
    with hgdef
  set h : Z4 → ℝ := fun k =>
    (TC * ε⁻¹ ^ 4) * z4EighthRadialTail (N + 1) k
    with hhdef
  have hf0 : ∀ k, 0 ≤ f k := by
    intro k
    simp only [hfdef]
    positivity
  have hh0 : ∀ k, 0 ≤ h k := by
    intro k
    simp only [hhdef]
    exact mul_nonneg (by positivity)
      (z4EighthRadialTail_nonneg _ _)
  have hg0 : ∀ k, 0 ≤ g k := by
    intro k
    simp only [hgdef]
    by_cases hk : k ∈ z4Cube N
    · rw [if_pos hk]
      unfold l2LatticeRadialWeight
      positivity
    · rw [if_neg hk]
  have hsqsym : ∀ k : Z4, ‖ρ.symbol ε k‖ ^ 4 ≤ ‖ρ.symbol ε k‖ ^ 2 := by
    intro k
    have h1 := ρ.norm_symbol_le_one ε k
    have h0 := norm_nonneg (ρ.symbol ε k)
    calc
      ‖ρ.symbol ε k‖ ^ 4 = ‖ρ.symbol ε k‖ ^ 2 * ‖ρ.symbol ε k‖ ^ 2 := by
        ring
      _ ≤ 1 * ‖ρ.symbol ε k‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
      _ = ‖ρ.symbol ε k‖ ^ 2 := one_mul _
  have hbracket4 : ∀ k : Z4,
      ((1 + paperModeNormSq k)⁻¹) ^ 2 ≤
        4 * (((1 + (z4SupRadius k : ℝ)) ^ 4)⁻¹) := by
    intro k
    have hb := inv_one_add_paperModeNormSq_le k
    have h0 : (0:ℝ) ≤ (1 + paperModeNormSq k)⁻¹ := by
      have := paperModeNormSq_nonneg k
      positivity
    calc
      ((1 + paperModeNormSq k)⁻¹) ^ 2 ≤
          (2 * (((1 + (z4SupRadius k : ℝ)) ^ 2)⁻¹)) ^ 2 :=
        pow_le_pow_left₀ h0 hb 2
      _ = 4 * (((1 + (z4SupRadius k : ℝ)) ^ 2) ^ 2)⁻¹ := by
        rw [mul_pow, inv_pow]
        norm_num
      _ = 4 * (((1 + (z4SupRadius k : ℝ)) ^ 4)⁻¹) := by
        rw [← pow_mul]
  have hfg : ∀ k, f k ≤ g k + h k := by
    intro k
    by_cases hk : k ∈ z4Cube N
    · refine le_trans ?_ (le_add_of_nonneg_right (hh0 k))
      simp only [hfdef, hgdef]
      rw [if_pos hk]
      calc
        ‖ρ.symbol ε k‖ ^ 4 * ((1 + paperModeNormSq k)⁻¹) ^ 2 ≤
            1 * ((1 + paperModeNormSq k)⁻¹) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact pow_le_one₀ (norm_nonneg _) (ρ.norm_symbol_le_one ε k)
        _ = ((1 + paperModeNormSq k)⁻¹) ^ 2 := one_mul _
        _ ≤ 4 * (((1 + (z4SupRadius k : ℝ)) ^ 4)⁻¹) := hbracket4 k
        _ = 4 * l2LatticeRadialWeight 4 k := by
          rw [l2LatticeRadialWeight_eq_z4SupRadius]
    · refine le_trans ?_ (le_add_of_nonneg_left (hg0 k))
      have hrad : N + 1 ≤ z4SupRadius k := by
        rw [mem_z4Cube_iff_z4SupRadius_le] at hk
        omega
      simp only [hfdef, hhdef]
      have htail :
          z4EighthRadialTail (N + 1) k =
            l2LatticeRadialWeight 8 k := by
        unfold z4EighthRadialTail
        rw [if_pos hrad]
      rw [htail, l2LatticeRadialWeight_eq_z4SupRadius]
      set s : ℝ := (z4SupRadius k : ℝ) with hsdef
      have hs : (0:ℝ) ≤ s := Nat.cast_nonneg _
      have hsym2 := symbol_sq_le_of_decay ρ hdecay hε hε1 k
      rw [← hsdef] at hsym2
      calc
        ‖ρ.symbol ε k‖ ^ 4 * ((1 + paperModeNormSq k)⁻¹) ^ 2 ≤
            ‖ρ.symbol ε k‖ ^ 2 * ((1 + paperModeNormSq k)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_right (hsqsym k) (by positivity)
        _ ≤ ((C0 ^ 2 * (2 * Real.pi) ^ 4) *
              (ε⁻¹ ^ 4 * (((1 + s) ^ 4)⁻¹))) *
            (4 * (((1 + s) ^ 4)⁻¹)) := by
          apply mul_le_mul hsym2 (hbracket4 k) (by positivity) ?_
          positivity
        _ = (TC * ε⁻¹ ^ 4) * ((1 + s) ^ 8)⁻¹ := by
          rw [hTCdef]
          have hpow : ((1 + s) ^ 4)⁻¹ * ((1 + s) ^ 4)⁻¹ =
              ((1 + s) ^ 8)⁻¹ := by
            rw [← mul_inv, ← pow_add]
          calc
            ((C0 ^ 2 * (2 * Real.pi) ^ 4) *
                (ε⁻¹ ^ 4 * (((1 + s) ^ 4)⁻¹))) *
              (4 * (((1 + s) ^ 4)⁻¹)) =
                (4 * (C0 ^ 2 * (2 * Real.pi) ^ 4) * ε⁻¹ ^ 4) *
                  (((1 + s) ^ 4)⁻¹ * ((1 + s) ^ 4)⁻¹) := by
              ring
            _ = (4 * (C0 ^ 2 * (2 * Real.pi) ^ 4) * ε⁻¹ ^ 4) *
                  ((1 + s) ^ 8)⁻¹ := by
              rw [hpow]
            _ = 4 * (C0 ^ 2 * (2 * Real.pi) ^ 4) * ε⁻¹ ^ 4 *
                  ((1 + s) ^ 8)⁻¹ := by ring
  have hgsummable : Summable g := by
    apply summable_of_ne_finset_zero (s := z4Cube N)
    intro k hk
    simp only [hgdef]
    exact if_neg hk
  have hhsummable : Summable h := by
    simp only [hhdef]
    exact (summable_z4EighthRadialTail (N + 1)).mul_left _
  have hfsummable : Summable f :=
    Summable.of_nonneg_of_le hf0 hfg (hgsummable.add hhsummable)
  have hgsum : (∑' k, g k) ≤ 1280 * L := by
    have hgeq : (∑' k, g k) =
        ∑ k ∈ z4Cube N, 4 * l2LatticeRadialWeight 4 k := by
      rw [tsum_eq_sum (s := z4Cube N) ?_]
      · apply Finset.sum_congr rfl
        intro k hk
        simp only [hgdef]
        exact if_pos hk
      · intro k hk
        simp only [hgdef]
        exact if_neg hk
    rw [hgeq, ← Finset.mul_sum]
    have hshell := sum_z4Cube_l2LatticeRadialWeight_four_le_log N
    have hlogN : Real.log ((N : ℝ) + 1) ≤ 2 + L := by
      have h3 : Real.log ((N : ℝ) + 1) ≤ Real.log (3 * ε⁻¹) :=
        Real.log_le_log (by positivity) hNup
      have hsplit : Real.log (3 * ε⁻¹) =
          Real.log 3 + Real.log ε⁻¹ :=
        Real.log_mul (by norm_num) (by positivity)
      have hlog3 : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (x := 3) (by norm_num)
        linarith
      have hinvlog : Real.log ε⁻¹ = L := by
        rw [Real.log_inv, hLdef,
          abs_of_nonpos (Real.log_nonpos hε.le hε1)]
      linarith [h3, hsplit.le, hsplit.ge]
    calc
      4 * ∑ k ∈ z4Cube N, l2LatticeRadialWeight 4 k ≤
          4 * (80 * (1 + Real.log ((N : ℝ) + 1))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa using hshell
      _ ≤ 4 * (80 * (1 + (2 + L))) := by
        have : (1 : ℝ) + Real.log ((N : ℝ) + 1) ≤ 1 + (2 + L) := by
          linarith
        nlinarith
      _ ≤ 1280 * L := by nlinarith
  have hhsum : (∑' k, h k) ≤ 20 * TC := by
    have hN1pos : 0 < N + 1 := Nat.succ_pos N
    have htail := tsum_z4EighthRadialTail_le (N + 1) hN1pos
    have hεN : ((N : ℝ) + 1)⁻¹ ≤ ε := by
      have hstep : ε⁻¹ ≤ (N : ℝ) + 1 := by linarith
      calc
        ((N : ℝ) + 1)⁻¹ ≤ (ε⁻¹)⁻¹ := inv_anti₀ (by positivity) hstep
        _ = ε := inv_inv ε
    have hεN4 : (((N + 1 : ℕ) : ℝ)⁻¹) ^ 4 ≤ ε ^ 4 := by
      push_cast
      exact pow_le_pow_left₀ (by positivity) hεN 4
    simp only [hhdef]
    rw [tsum_mul_left]
    calc
      (TC * ε⁻¹ ^ 4) * ∑' k, z4EighthRadialTail (N + 1) k ≤
          (TC * ε⁻¹ ^ 4) * (20 * (((N + 1 : ℕ) : ℝ)⁻¹) ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact htail
      _ ≤ (TC * ε⁻¹ ^ 4) * (20 * ε ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      _ = 20 * TC * (ε⁻¹ ^ 4 * ε ^ 4) := by ring
      _ = 20 * TC := by
        rw [← mul_pow, inv_mul_cancel₀ hε.ne', one_pow, mul_one]
  calc
    (∑' k, f k) ≤ ∑' k, (g k + h k) :=
      hfsummable.tsum_le_tsum hfg (hgsummable.add hhsummable)
    _ = (∑' k, g k) + ∑' k, h k :=
      hgsummable.tsum_add hhsummable
    _ ≤ 1280 * L + 20 * TC := add_le_add hgsum hhsum
    _ ≤ 1280 * L + 20 * TC * L := by nlinarith
    _ = (1280 + 20 * TC) * L := by ring

/-! ## The trivial-pairing half integrand -/

theorem idPairingFinTwo_extract :
    extract idPairingFinTwo = ([] : List (Fin 2 × Fin 2)) := by
  decide

/-- **Closed form of the order-two trivial-pairing integrand**: the
plain three-edge chain.  Nothing is extracted, no difference factor
exists, and no within-half covariance appears. -/
theorem detIntegrand_idPairingFinTwo_assemble
    (ρ : SmoothCutoff) (ε : ℝ) (x y : T4) (u : Fin 2 → T4) :
    detIntegrand ρ ε 2 idPairingFinTwo (assemble x y u) =
      greenFn (x - u 0) * greenFn (u 0 - u 1) *
        greenFn (u 1 - y) := by
  unfold detIntegrand
  rw [idPairingFinTwo_extract]
  have hxt1 : assemble x y u (1 : Fin (2 + 2)) = u 0 := by
    have h : (1 : Fin (2 + 2)) = varIdx (0 : Fin 2) := rfl
    rw [h, assemble_varIdx]
  have hxt2 : assemble x y u (2 : Fin (2 + 2)) = u 1 := by
    have h : (2 : Fin (2 + 2)) = varIdx (1 : Fin 2) := rfl
    rw [h, assemble_varIdx]
  have hxt3 : assemble x y u (3 : Fin (2 + 2)) = y := by
    have h : (3 : Fin (2 + 2)) = Fin.last (2 + 1) := rfl
    rw [h, assemble_last]
  have hcov :
      (∏ i ∈ idPairingFinTwo.pairSupport.filter
          (fun i => i < idPairingFinTwo i),
        ρ.etaEpsT4 ε
          (assemble x y u (varIdx i) -
            assemble x y u (varIdx (idPairingFinTwo i)))) = 1 := by
    have hset :
        idPairingFinTwo.pairSupport.filter
            (fun i => i < idPairingFinTwo i) =
          (∅ : Finset (Fin 2)) := by decide
    rw [hset, Finset.prod_empty]
  have hchain :
      (∏ e : Fin (2 + 1),
        if e.val ∈ ([] : List (Fin 2 × Fin 2)).map
            (fun p => p.2.val + 1) then 1
        else greenFn (assemble x y u e.castSucc -
          assemble x y u e.succ)) =
        greenFn (x - u 0) * greenFn (u 0 - u 1) *
          greenFn (u 1 - y) := by
    rw [Fin.prod_univ_three]
    simp only [List.map_nil, List.not_mem_nil, if_false]
    have hc0 : (0 : Fin (2 + 1)).castSucc = (0 : Fin (2 + 2)) := rfl
    have hs0 : (0 : Fin (2 + 1)).succ = (1 : Fin (2 + 2)) := rfl
    have hc1 : (1 : Fin (2 + 1)).castSucc = (1 : Fin (2 + 2)) := rfl
    have hs1 : (1 : Fin (2 + 1)).succ = (2 : Fin (2 + 2)) := rfl
    have hc2 : (2 : Fin (2 + 1)).castSucc = (2 : Fin (2 + 2)) := rfl
    have hs2 : (2 : Fin (2 + 1)).succ = (3 : Fin (2 + 2)) := rfl
    rw [hc0, hs0, hc1, hs1, hc2, hs2, assemble_zero,
      hxt1, hxt2, hxt3]
  rw [hchain, hcov, List.map_nil, List.prod_nil, mul_one, mul_one]

/-! ## The two cross matchings -/

/-- The first single of the trivial pairing. -/
def idSingleZero : { x : Fin 2 // x ∈ idPairingFinTwo.singles } :=
  ⟨0, by decide⟩

/-- The second single of the trivial pairing. -/
def idSingleOne : { x : Fin 2 // x ∈ idPairingFinTwo.singles } :=
  ⟨1, by decide⟩

theorem idSingle_cases
    (j : { x : Fin 2 // x ∈ idPairingFinTwo.singles }) :
    j = idSingleZero ∨ j = idSingleOne := by
  obtain ⟨⟨jv, hjv⟩, hj⟩ := j
  interval_cases jv
  · left; rfl
  · right; rfl

/-- A bijection of the trivial singles is the identity matching or the
swap matching. -/
theorem crossSingleEquiv_classify
    (π : idPairingFinTwo.singles ≃ idPairingFinTwo.singles) :
    (π idSingleZero = idSingleZero ∧ π idSingleOne = idSingleOne) ∨
      (π idSingleZero = idSingleOne ∧ π idSingleOne = idSingleZero) := by
  have hne : idSingleZero ≠ idSingleOne := by decide
  rcases idSingle_cases (π idSingleZero) with h0 | h0
  · left
    refine ⟨h0, ?_⟩
    rcases idSingle_cases (π idSingleOne) with h1 | h1
    · exact absurd (π.injective (h0.trans h1.symm)) hne
    · exact h1
  · right
    refine ⟨h0, ?_⟩
    rcases idSingle_cases (π idSingleOne) with h1 | h1
    · exact h1
    · exact absurd (π.injective (h0.trans h1.symm)) hne

/-- The cross covariance of a trivial-pairing contraction: exactly the
two cross-half factors selected by the matching. -/
theorem momentCrossCovarianceProduct_id_id
    (ρ : SmoothCutoff) (ε : ℝ)
    (π : idPairingFinTwo.singles ≃ idPairingFinTwo.singles)
    (v : Fin (2 * 2) → T4) :
    momentCrossCovarianceProduct ρ ε 2
        idPairingFinTwo idPairingFinTwo π v =
      ρ.etaEpsT4 ε
          (v (leftMomentIndex 0) -
            v (rightMomentIndex (π idSingleZero).val)) *
        ρ.etaEpsT4 ε
          (v (leftMomentIndex 1) -
            v (rightMomentIndex (π idSingleOne).val)) := by
  unfold momentCrossCovarianceProduct
  have huniv :
      (Finset.univ :
        Finset { x : Fin 2 // x ∈ idPairingFinTwo.singles }) =
        {idSingleZero, idSingleOne} := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
      Finset.mem_singleton]
    exact idSingle_cases j
  rw [huniv, Finset.prod_insert (by decide), Finset.prod_singleton]
  rfl

/-! ## The cross physical density and its exact external peeling -/

/-- The internal core of the cross density: both middle chain edges
against both cross covariances. -/
def r324CrossCoreDensity (ρ : SmoothCutoff) (ε : ℝ)
    (j₀ j₁ : Fin 2) (v : Fin (2 * 2) → T4) : ℝ :=
  greenFn (v (leftMomentIndex 0) - v (leftMomentIndex 1)) *
    greenFn (v (rightMomentIndex 0) - v (rightMomentIndex 1)) *
    (ρ.etaEpsT4 ε
        (v (leftMomentIndex 0) - v (rightMomentIndex j₀)) *
      ρ.etaEpsT4 ε
        (v (leftMomentIndex 1) - v (rightMomentIndex j₁)))

/-- The full cross physical density in peel-ready nested form: each
external variable multiplies one unit-mass boundary Green edge. -/
def r324CrossPhysicalDensity (ρ : SmoothCutoff) (ε : ℝ)
    (j₀ j₁ : Fin 2) (p : R324PhysicalPoint 2) : ℝ :=
  greenFn (p.1 - p.2.2.2.2 (leftMomentIndex 0)) *
    (greenFn (p.2.2.2.2 (leftMomentIndex 1) - p.2.1) *
      (greenFn (p.2.2.1 - p.2.2.2.2 (rightMomentIndex 0)) *
        (greenFn (p.2.2.2.2 (rightMomentIndex 1) - p.2.2.2.1) *
          r324CrossCoreDensity ρ ε j₀ j₁ p.2.2.2.2)))

/-- **Exact peeling of the four external variables.**  Each boundary
Green edge has unit paper mass; the flat cross density integrates to
the internal core integral. -/
theorem integral_flat_crossPhysicalDensity
    (ρ : SmoothCutoff) (ε : ℝ) (j₀ j₁ : Fin 2)
    (hint :
      Integrable (r324CrossPhysicalDensity ρ ε j₀ j₁)
        (r324PhysicalMeasure 2)) :
    (∫ p, r324CrossPhysicalDensity ρ ε j₀ j₁ p
        ∂(r324PhysicalMeasure 2)) =
      ∫ v : Fin (2 * 2) → T4,
        r324CrossCoreDensity ρ ε j₀ j₁ v
        ∂(Measure.pi fun _ : Fin (2 * 2) => paperMeasure) := by
  unfold r324PhysicalMeasure r324PhysicalRestMeasure at hint ⊢
  unfold r324CrossPhysicalDensity at hint ⊢
  rw [integral_prod_symm _ hint]
  have heval1 :
      (fun q : T4 × (T4 × (T4 × (Fin (2 * 2) → T4))) =>
        ∫ x, greenFn (x - q.2.2.2 (leftMomentIndex 0)) *
          (greenFn (q.2.2.2 (leftMomentIndex 1) - q.1) *
            (greenFn (q.2.1 - q.2.2.2 (rightMomentIndex 0)) *
              (greenFn (q.2.2.2 (rightMomentIndex 1) - q.2.2.1) *
                r324CrossCoreDensity ρ ε j₀ j₁ q.2.2.2)))
          ∂paperMeasure) =
        fun q : T4 × (T4 × (T4 × (Fin (2 * 2) → T4))) =>
          greenFn (q.2.2.2 (leftMomentIndex 1) - q.1) *
            (greenFn (q.2.1 - q.2.2.2 (rightMomentIndex 0)) *
              (greenFn (q.2.2.2 (rightMomentIndex 1) - q.2.2.1) *
                r324CrossCoreDensity ρ ε j₀ j₁ q.2.2.2)) := by
    funext q
    rw [integral_mul_const, integral_greenFn_sub, one_mul]
  have hint1 := hint.integral_prod_right
  rw [heval1] at hint1 ⊢
  rw [integral_prod_symm _ hint1]
  have heval2 :
      (fun q : T4 × (T4 × (Fin (2 * 2) → T4)) =>
        ∫ y, greenFn (q.2.2 (leftMomentIndex 1) - y) *
          (greenFn (q.1 - q.2.2 (rightMomentIndex 0)) *
            (greenFn (q.2.2 (rightMomentIndex 1) - q.2.1) *
              r324CrossCoreDensity ρ ε j₀ j₁ q.2.2))
          ∂paperMeasure) =
        fun q : T4 × (T4 × (Fin (2 * 2) → T4)) =>
          greenFn (q.1 - q.2.2 (rightMomentIndex 0)) *
            (greenFn (q.2.2 (rightMomentIndex 1) - q.2.1) *
              r324CrossCoreDensity ρ ε j₀ j₁ q.2.2) := by
    funext q
    rw [integral_mul_const, integral_greenFn_shift_left, one_mul]
  have hint2 := hint1.integral_prod_right
  rw [heval2] at hint2 ⊢
  rw [integral_prod_symm _ hint2]
  have heval3 :
      (fun q : T4 × (Fin (2 * 2) → T4) =>
        ∫ z, greenFn (z - q.2 (rightMomentIndex 0)) *
          (greenFn (q.2 (rightMomentIndex 1) - q.1) *
            r324CrossCoreDensity ρ ε j₀ j₁ q.2)
          ∂paperMeasure) =
        fun q : T4 × (Fin (2 * 2) → T4) =>
          greenFn (q.2 (rightMomentIndex 1) - q.1) *
            r324CrossCoreDensity ρ ε j₀ j₁ q.2 := by
    funext q
    rw [integral_mul_const, integral_greenFn_sub, one_mul]
  have hint3 := hint2.integral_prod_right
  rw [heval3] at hint3 ⊢
  rw [integral_prod_symm _ hint3]
  have heval4 :
      (fun v : Fin (2 * 2) → T4 =>
        ∫ w, greenFn (v (rightMomentIndex 1) - w) *
          r324CrossCoreDensity ρ ε j₀ j₁ v
          ∂paperMeasure) =
        fun v : Fin (2 * 2) → T4 =>
          r324CrossCoreDensity ρ ε j₀ j₁ v := by
    funext v
    rw [integral_mul_const, integral_greenFn_shift_left, one_mul]
  rw [heval4]

/-! ## The internal core evaluation -/

theorem integrable_crossHalfPair
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (p q : T4) :
    Integrable
      (fun r : T4 × T4 =>
        ((greenFn (r.1 - r.2) *
          (ρ.etaEpsT4 ε (r.1 - p) * ρ.etaEpsT4 ε (r.2 - q)) : ℝ) : ℂ))
      (paperMeasure.prod paperMeasure) := by
  obtain ⟨Cη, hCη, hηbound⟩ := ρ.exists_pos_etaEpsT4_uniform_bound
  set Mη : ℝ := ε⁻¹ ^ (dim : ℕ) * Cη with hMηdef
  have hpoint :
      ∀ r : T4 × T4,
        ((greenFn (r.1 - r.2) *
          (ρ.etaEpsT4 ε (r.1 - p) * ρ.etaEpsT4 ε (r.2 - q)) : ℝ) : ℂ) =
          ((ρ.etaEpsT4 ε (r.1 - p) *
              ρ.etaEpsT4 ε (r.2 - q) : ℝ) : ℂ) *
            ((greenFn (r.1 - r.2) : ℝ) : ℂ) := by
    intro r
    push_cast
    ring
  rw [funext hpoint]
  have hmeas :
      AEStronglyMeasurable
        (fun r : T4 × T4 =>
          ((ρ.etaEpsT4 ε (r.1 - p) *
            ρ.etaEpsT4 ε (r.2 - q) : ℝ) : ℂ))
        (paperMeasure.prod paperMeasure) := by
    apply Measurable.aestronglyMeasurable
    apply Complex.measurable_ofReal.comp
    exact ((ρ.measurable_etaEpsT4 ε).comp
      (measurable_fst.sub measurable_const)).mul
      ((ρ.measurable_etaEpsT4 ε).comp
        (measurable_snd.sub measurable_const))
  refine integrable_greenFn_pair.ofReal.bdd_mul hmeas
    (c := Mη * Mη) ?_
  filter_upwards with r
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (ρ.etaEpsT4_nonneg ε _) (ρ.etaEpsT4_nonneg ε _))]
  have h1 := hηbound hε hε1 (r.1 - p)
  have h2 := hηbound hε hε1 (r.2 - q)
  have h1' := ρ.etaEpsT4_nonneg ε (r.1 - p)
  have h2' := ρ.etaEpsT4_nonneg ε (r.2 - q)
  rw [hMηdef]
  exact mul_le_mul h1 h2 h2' (by positivity)

theorem norm_crossPairMode_eq
    (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    ‖r324CrossPairCoefficient ρ ε k *
        ((((2 * Real.pi) ^ (dim : ℕ) *
          (1 + paperModeNormSq k)⁻¹ : ℝ)) : ℂ)‖ =
      ‖ρ.symbol ε k‖ ^ 4 * ((1 + paperModeNormSq k)⁻¹) ^ 2 := by
  have hP := paperModeNormSq_nonneg k
  unfold r324CrossPairCoefficient
  rw [norm_mul, norm_mul, norm_mul, norm_pow,
    ρ.norm_covarianceModeCoeff, Complex.norm_real,
    Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + paperModeNormSq k)⁻¹),
    abs_of_nonneg
      (by positivity : (0:ℝ) ≤ (2 * Real.pi) ^ (dim : ℕ)),
    abs_of_nonneg
      (mul_nonneg
        (by positivity : (0:ℝ) ≤ (2 * Real.pi) ^ (dim : ℕ))
        (by positivity : (0:ℝ) ≤ (1 + paperModeNormSq k)⁻¹))]
  have hunit :
      (2 * Real.pi) ^ (dim : ℕ) *
        NoiseModel.whiteNoiseFourierScale ^ 2 = 1 := by
    rw [mul_comm]
    exact whiteNoiseFourierScale_sq_mul_pow_dim
  calc
    (1 + paperModeNormSq k)⁻¹ * (2 * Real.pi) ^ (dim : ℕ) *
        (NoiseModel.whiteNoiseFourierScale ^ 2 *
          ‖ρ.symbol ε k‖ ^ 2) ^ 2 *
        ((2 * Real.pi) ^ (dim : ℕ) *
          (1 + paperModeNormSq k)⁻¹) =
        (((2 * Real.pi) ^ (dim : ℕ) *
            NoiseModel.whiteNoiseFourierScale ^ 2) *
          ((2 * Real.pi) ^ (dim : ℕ) *
            NoiseModel.whiteNoiseFourierScale ^ 2)) *
          (‖ρ.symbol ε k‖ ^ 4 *
            ((1 + paperModeNormSq k)⁻¹) ^ 2) := by
      ring
    _ = ‖ρ.symbol ε k‖ ^ 4 * ((1 + paperModeNormSq k)⁻¹) ^ 2 := by
      rw [hunit, one_mul, one_mul]

theorem summable_crossWindowTerm
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) :
    Summable fun k : Z4 =>
      ‖ρ.symbol ε k‖ ^ 4 * ((1 + paperModeNormSq k)⁻¹) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => by positivity)
    (fun k => ?_) (ρ.summable_norm_symbol hε)
  have hP := paperModeNormSq_nonneg k
  have hsym1 := ρ.norm_symbol_le_one ε k
  have hsym0 := norm_nonneg (ρ.symbol ε k)
  have hb : ((1 + paperModeNormSq k)⁻¹) ^ 2 ≤ 1 := by
    have h1 : (1 + paperModeNormSq k)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      linarith
    nlinarith [inv_nonneg.mpr
      (by linarith : (0:ℝ) ≤ 1 + paperModeNormSq k)]
  calc
    ‖ρ.symbol ε k‖ ^ 4 * ((1 + paperModeNormSq k)⁻¹) ^ 2 ≤
        ‖ρ.symbol ε k‖ ^ 4 * 1 :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ‖ρ.symbol ε k‖ ^ 4 := mul_one _
    _ = ‖ρ.symbol ε k‖ * ‖ρ.symbol ε k‖ ^ 3 := by ring
    _ ≤ ‖ρ.symbol ε k‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (pow_le_one₀ hsym0 hsym1) hsym0
    _ = ‖ρ.symbol ε k‖ := mul_one _
/-- **The internal cross core is the diagonal window.**  Both middle
chain edges integrated against both cross covariances collapse, for
either matching, to the diagonal mode sum
`Σ_k ‖ρ̂(εk)‖⁴ ⟨k⟩⁻⁴`-type — the squared-Green analogue of the raw
block mass, with no `ε`-divergence. -/
theorem integral_crossCoreDensity_le
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {j₀ j₁ : Fin 2}
    (hj : (j₀ = 0 ∧ j₁ = 1) ∨ (j₀ = 1 ∧ j₁ = 0))
    (hint :
      Integrable (r324CrossCoreDensity ρ ε j₀ j₁)
        (Measure.pi fun _ : Fin (2 * 2) => paperMeasure)) :
    (∫ v, r324CrossCoreDensity ρ ε j₀ j₁ v
        ∂(Measure.pi fun _ : Fin (2 * 2) => paperMeasure)) ≤
      ∑' k : Z4,
        ‖ρ.symbol ε k‖ ^ 4 * ((1 + paperModeNormSq k)⁻¹) ^ 2 := by
  set g : (Fin 2 → T4) × (Fin 2 → T4) → ℝ := fun ab =>
    greenFn (ab.1 0 - ab.1 1) * greenFn (ab.2 0 - ab.2 1) *
      (ρ.etaEpsT4 ε (ab.1 0 - ab.2 j₀) *
        ρ.etaEpsT4 ε (ab.1 1 - ab.2 j₁))
    with hgdef
  have hcomp :
      r324CrossCoreDensity ρ ε j₀ j₁ =
        fun v => g (r324DoublePiMeasurableEquiv 2 v) := by
    funext v
    rw [r324DoublePiMeasurableEquiv_apply]
    rfl
  have htrans :=
    (measurePreserving_r324DoublePiMeasurableEquiv 2).integral_comp' g
  have hgint :
      Integrable g
        ((Measure.pi fun _ : Fin 2 => paperMeasure).prod
          (Measure.pi fun _ : Fin 2 => paperMeasure)) := by
    have hiff :=
      (measurePreserving_r324DoublePiMeasurableEquiv 2).integrable_comp_emb
        (r324DoublePiMeasurableEquiv 2).measurableEmbedding
        (g := g)
    rw [hcomp] at hint
    exact hiff.mp hint
  have hval : (∫ v, r324CrossCoreDensity ρ ε j₀ j₁ v
      ∂(Measure.pi fun _ : Fin (2 * 2) => paperMeasure)) =
      ∫ ab, g ab
        ∂((Measure.pi fun _ : Fin 2 => paperMeasure).prod
          (Measure.pi fun _ : Fin 2 => paperMeasure)) := by
    rw [hcomp]
    exact htrans
  have hnonneg :
      0 ≤ ∫ ab, g ab
        ∂((Measure.pi fun _ : Fin 2 => paperMeasure).prod
          (Measure.pi fun _ : Fin 2 => paperMeasure)) := by
    apply integral_nonneg
    intro ab
    simp only [hgdef]
    have h1 := greenFn_nonneg (ab.1 0 - ab.1 1)
    have h2 := greenFn_nonneg (ab.2 0 - ab.2 1)
    have h3 := ρ.etaEpsT4_nonneg ε (ab.1 0 - ab.2 j₀)
    have h4 := ρ.etaEpsT4_nonneg ε (ab.1 1 - ab.2 j₁)
    positivity
  have hCeval :
      ((∫ ab, g ab
        ∂((Measure.pi fun _ : Fin 2 => paperMeasure).prod
          (Measure.pi fun _ : Fin 2 => paperMeasure)) : ℝ) : ℂ) =
        ∑' k : Z4,
          r324CrossPairCoefficient ρ ε k *
            ((((2 * Real.pi) ^ (dim : ℕ) *
              (1 + paperModeNormSq k)⁻¹ : ℝ)) : ℂ) := by
    have hcast :
        ((∫ ab, g ab
          ∂((Measure.pi fun _ : Fin 2 => paperMeasure).prod
            (Measure.pi fun _ : Fin 2 => paperMeasure)) : ℝ) : ℂ) =
          ∫ ab, ((g ab : ℝ) : ℂ)
            ∂((Measure.pi fun _ : Fin 2 => paperMeasure).prod
              (Measure.pi fun _ : Fin 2 => paperMeasure)) :=
      integral_ofReal.symm
    rw [hcast, integral_prod_symm _ hgint.ofReal]
    have hinner : ∀ b : Fin 2 → T4,
        (∫ a : Fin 2 → T4, ((g (a, b) : ℝ) : ℂ)
          ∂(Measure.pi fun _ : Fin 2 => paperMeasure)) =
          ((greenFn (b 0 - b 1) : ℝ) : ℂ) *
            ∑' k : Z4,
              r324CrossPairCoefficient ρ ε k *
                (charT4 (-k) (b j₀) * charT4 k (b j₁)) := by
      intro b
      have hpoint : ∀ a : Fin 2 → T4,
          ((g (a, b) : ℝ) : ℂ) =
            ((greenFn (b 0 - b 1) : ℝ) : ℂ) *
              ((greenFn (a 0 - a 1) *
                (ρ.etaEpsT4 ε (a 0 - b j₀) *
                  ρ.etaEpsT4 ε (a 1 - b j₁)) : ℝ) : ℂ) := by
        intro a
        simp only [hgdef]
        push_cast
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
        integral_const_mul]
      congr 1
      have hpair :
          (fun a : Fin 2 → T4 =>
            ((greenFn (a 0 - a 1) *
              (ρ.etaEpsT4 ε (a 0 - b j₀) *
                ρ.etaEpsT4 ε (a 1 - b j₁)) : ℝ) : ℂ)) =
            fun a : Fin 2 → T4 =>
              ((greenFn ((MeasurableEquiv.piFinTwo
                    (fun _ : Fin 2 => T4) a).1 -
                  (MeasurableEquiv.piFinTwo
                    (fun _ : Fin 2 => T4) a).2) *
                (ρ.etaEpsT4 ε ((MeasurableEquiv.piFinTwo
                    (fun _ : Fin 2 => T4) a).1 - b j₀) *
                  ρ.etaEpsT4 ε ((MeasurableEquiv.piFinTwo
                    (fun _ : Fin 2 => T4) a).2 - b j₁)) : ℝ) : ℂ) :=
        rfl
      rw [hpair,
        (measurePreserving_piFinTwo
          (fun _ : Fin 2 => paperMeasure)).integral_comp'
          (fun r : T4 × T4 =>
            ((greenFn (r.1 - r.2) *
              (ρ.etaEpsT4 ε (r.1 - b j₀) *
                ρ.etaEpsT4 ε (r.2 - b j₁)) : ℝ) : ℂ)),
        integral_prod_symm _
          (integrable_crossHalfPair ρ hε hε1 (b j₀) (b j₁)),
        integral_integral_greenFn_etaPair_eq_tsum ρ hε hε1]
    rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
    rcases hj with ⟨hj0, hj1⟩ | ⟨hj0, hj1⟩
    · subst hj0
      subst hj1
      have houter :
          (fun b : Fin 2 → T4 =>
            ((greenFn (b 0 - b 1) : ℝ) : ℂ) *
              ∑' k : Z4,
                r324CrossPairCoefficient ρ ε k *
                  (charT4 (-k) (b 0) * charT4 k (b 1))) =
            fun b : Fin 2 → T4 =>
              (fun r : T4 × T4 =>
                ((greenFn (r.1 - r.2) : ℝ) : ℂ) *
                  ∑' k : Z4,
                    r324CrossPairCoefficient ρ ε k *
                      (charT4 (-k) r.1 * charT4 k r.2))
                (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => T4) b) :=
        rfl
      rw [houter,
        (measurePreserving_piFinTwo
          (fun _ : Fin 2 => paperMeasure)).integral_comp'
          (fun r : T4 × T4 =>
            ((greenFn (r.1 - r.2) : ℝ) : ℂ) *
              ∑' k : Z4,
                r324CrossPairCoefficient ρ ε k *
                  (charT4 (-k) r.1 * charT4 k r.2))]
      exact
        integral_prod_greenFn_mul_tsum_crossModes ρ hε
          (fun k => -k) (fun k => k)
          (fun k => neg_add_cancel k) (fun k => rfl)
    · subst hj0
      subst hj1
      have hcommute : ∀ b : Fin 2 → T4,
          ((greenFn (b 0 - b 1) : ℝ) : ℂ) *
              ∑' k : Z4,
                r324CrossPairCoefficient ρ ε k *
                  (charT4 (-k) (b 1) * charT4 k (b 0)) =
            ((greenFn (b 0 - b 1) : ℝ) : ℂ) *
              ∑' k : Z4,
                r324CrossPairCoefficient ρ ε k *
                  (charT4 k (b 0) * charT4 (-k) (b 1)) := by
        intro b
        congr 1
        apply tsum_congr
        intro k
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hcommute)]
      have houter :
          (fun b : Fin 2 → T4 =>
            ((greenFn (b 0 - b 1) : ℝ) : ℂ) *
              ∑' k : Z4,
                r324CrossPairCoefficient ρ ε k *
                  (charT4 k (b 0) * charT4 (-k) (b 1))) =
            fun b : Fin 2 → T4 =>
              (fun r : T4 × T4 =>
                ((greenFn (r.1 - r.2) : ℝ) : ℂ) *
                  ∑' k : Z4,
                    r324CrossPairCoefficient ρ ε k *
                      (charT4 k r.1 * charT4 (-k) r.2))
                (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => T4) b) :=
        rfl
      rw [houter,
        (measurePreserving_piFinTwo
          (fun _ : Fin 2 => paperMeasure)).integral_comp'
          (fun r : T4 × T4 =>
            ((greenFn (r.1 - r.2) : ℝ) : ℂ) *
              ∑' k : Z4,
                r324CrossPairCoefficient ρ ε k *
                  (charT4 k r.1 * charT4 (-k) r.2))]
      exact
        integral_prod_greenFn_mul_tsum_crossModes ρ hε
          (fun k => k) (fun k => -k)
          (fun k => add_neg_cancel k)
          (fun k => paperModeNormSq_neg k)
  have hsummnorms :
      Summable fun k : Z4 =>
        ‖r324CrossPairCoefficient ρ ε k *
          ((((2 * Real.pi) ^ (dim : ℕ) *
            (1 + paperModeNormSq k)⁻¹ : ℝ)) : ℂ)‖ :=
    (summable_crossWindowTerm ρ hε).congr
      (fun k => (norm_crossPairMode_eq ρ ε k).symm)
  calc
    (∫ v, r324CrossCoreDensity ρ ε j₀ j₁ v
        ∂(Measure.pi fun _ : Fin (2 * 2) => paperMeasure)) =
        ∫ ab, g ab
          ∂((Measure.pi fun _ : Fin 2 => paperMeasure).prod
            (Measure.pi fun _ : Fin 2 => paperMeasure)) := hval
    _ = ‖((∫ ab, g ab
          ∂((Measure.pi fun _ : Fin 2 => paperMeasure).prod
            (Measure.pi fun _ : Fin 2 => paperMeasure)) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = ‖∑' k : Z4,
          r324CrossPairCoefficient ρ ε k *
            ((((2 * Real.pi) ^ (dim : ℕ) *
              (1 + paperModeNormSq k)⁻¹ : ℝ)) : ℂ)‖ := by
      rw [hCeval]
    _ ≤ ∑' k : Z4,
          ‖r324CrossPairCoefficient ρ ε k *
            ((((2 * Real.pi) ^ (dim : ℕ) *
              (1 + paperModeNormSq k)⁻¹ : ℝ)) : ℂ)‖ :=
      norm_tsum_le_tsum_norm hsummnorms
    _ = ∑' k : Z4,
          ‖ρ.symbol ε k‖ ^ 4 * ((1 + paperModeNormSq k)⁻¹) ^ 2 :=
      tsum_congr fun k => norm_crossPairMode_eq ρ ε k

/-- The internal core inherits integrability from the flat density
through the same four unit-mass peels. -/
theorem integrable_crossCoreDensity_of_flat
    (ρ : SmoothCutoff) (ε : ℝ) (j₀ j₁ : Fin 2)
    (hint :
      Integrable (r324CrossPhysicalDensity ρ ε j₀ j₁)
        (r324PhysicalMeasure 2)) :
    Integrable (r324CrossCoreDensity ρ ε j₀ j₁)
      (Measure.pi fun _ : Fin (2 * 2) => paperMeasure) := by
  unfold r324PhysicalMeasure r324PhysicalRestMeasure at hint
  unfold r324CrossPhysicalDensity at hint
  have hint1 := hint.integral_prod_right
  have heval1 :
      (fun q : T4 × (T4 × (T4 × (Fin (2 * 2) → T4))) =>
        ∫ x, greenFn (x - q.2.2.2 (leftMomentIndex 0)) *
          (greenFn (q.2.2.2 (leftMomentIndex 1) - q.1) *
            (greenFn (q.2.1 - q.2.2.2 (rightMomentIndex 0)) *
              (greenFn (q.2.2.2 (rightMomentIndex 1) - q.2.2.1) *
                r324CrossCoreDensity ρ ε j₀ j₁ q.2.2.2)))
          ∂paperMeasure) =
        fun q : T4 × (T4 × (T4 × (Fin (2 * 2) → T4))) =>
          greenFn (q.2.2.2 (leftMomentIndex 1) - q.1) *
            (greenFn (q.2.1 - q.2.2.2 (rightMomentIndex 0)) *
              (greenFn (q.2.2.2 (rightMomentIndex 1) - q.2.2.1) *
                r324CrossCoreDensity ρ ε j₀ j₁ q.2.2.2)) := by
    funext q
    rw [integral_mul_const, integral_greenFn_sub, one_mul]
  rw [heval1] at hint1
  have hint2 := hint1.integral_prod_right
  have heval2 :
      (fun q : T4 × (T4 × (Fin (2 * 2) → T4)) =>
        ∫ y, greenFn (q.2.2 (leftMomentIndex 1) - y) *
          (greenFn (q.1 - q.2.2 (rightMomentIndex 0)) *
            (greenFn (q.2.2 (rightMomentIndex 1) - q.2.1) *
              r324CrossCoreDensity ρ ε j₀ j₁ q.2.2))
          ∂paperMeasure) =
        fun q : T4 × (T4 × (Fin (2 * 2) → T4)) =>
          greenFn (q.1 - q.2.2 (rightMomentIndex 0)) *
            (greenFn (q.2.2 (rightMomentIndex 1) - q.2.1) *
              r324CrossCoreDensity ρ ε j₀ j₁ q.2.2) := by
    funext q
    rw [integral_mul_const, integral_greenFn_shift_left, one_mul]
  rw [heval2] at hint2
  have hint3 := hint2.integral_prod_right
  have heval3 :
      (fun q : T4 × (Fin (2 * 2) → T4) =>
        ∫ z, greenFn (z - q.2 (rightMomentIndex 0)) *
          (greenFn (q.2 (rightMomentIndex 1) - q.1) *
            r324CrossCoreDensity ρ ε j₀ j₁ q.2)
          ∂paperMeasure) =
        fun q : T4 × (Fin (2 * 2) → T4) =>
          greenFn (q.2 (rightMomentIndex 1) - q.1) *
            r324CrossCoreDensity ρ ε j₀ j₁ q.2 := by
    funext q
    rw [integral_mul_const, integral_greenFn_sub, one_mul]
  rw [heval3] at hint3
  have hint4 := hint3.integral_prod_right
  have heval4 :
      (fun v : Fin (2 * 2) → T4 =>
        ∫ w, greenFn (v (rightMomentIndex 1) - w) *
          r324CrossCoreDensity ρ ε j₀ j₁ v
          ∂paperMeasure) =
        fun v : Fin (2 * 2) → T4 =>
          r324CrossCoreDensity ρ ε j₀ j₁ v := by
    funext v
    rw [integral_mul_const, integral_greenFn_shift_left, one_mul]
  rw [heval4] at hint4
  exact hint4

/-- **The cross contraction term obeys the diagonal window bound.**
For either cross matching, the complete order-two trivial-pairing
contraction term is bounded by the diagonal mode window — with all
four external variables consumed at unit mass and no dependence on
the external modes. -/
theorem norm_deterministicMomentContractionTerm_cross_le
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (α β : Z4)
    (π : idPairingFinTwo.singles ≃ idPairingFinTwo.singles) :
    ‖deterministicMomentContractionTerm ρ ε 2 α β
        ⟨idPairingFinTwo, ⟨idPairingFinTwo, π⟩⟩‖ ≤
      ∑' k : Z4,
        ‖ρ.symbol ε k‖ ^ 4 * ((1 + paperModeNormSq k)⁻¹) ^ 2 := by
  set e : MomentContraction 2 :=
    ⟨idPairingFinTwo, ⟨idPairingFinTwo, π⟩⟩ with hedef
  set j₀ : Fin 2 := (π idSingleZero).val with hj₀def
  set j₁ : Fin 2 := (π idSingleOne).val with hj₁def
  have hj : (j₀ = 0 ∧ j₁ = 1) ∨ (j₀ = 1 ∧ j₁ = 0) := by
    rcases crossSingleEquiv_classify π with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · left
      constructor
      · rw [hj₀def, h0]; rfl
      · rw [hj₁def, h1]; rfl
    · right
      constructor
      · rw [hj₀def, h0]; rfl
      · rw [hj₁def, h1]; rfl
  have hflat := r324MomentIntegrable_all ρ hε hε1 α β e
  have hterm :
      deterministicMomentContractionTerm ρ ε 2 α β e =
        ∫ p, r324Flatten
          (deterministicMomentIntegrand ρ ε 2 α β
            e.1 e.2.1 e.2.2) p
          ∂(r324PhysicalMeasure 2) :=
    (integral_r324Flatten_deterministicMomentIntegrand
      ρ ε 2 α β e hflat).symm
  have hnormeq : ∀ p : R324PhysicalPoint 2,
      ‖r324Flatten
        (deterministicMomentIntegrand ρ ε 2 α β
          e.1 e.2.1 e.2.2) p‖ =
        r324CrossPhysicalDensity ρ ε j₀ j₁ p := by
    intro p
    unfold r324Flatten deterministicMomentIntegrand
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_charT4,
      norm_charT4, norm_charT4, norm_charT4, mul_one, one_mul,
      one_mul, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hD :
        detIntegrand ρ ε 2 e.1
            (assemble p.1 p.2.1
              (fun i => p.2.2.2.2 (leftMomentIndex i))) *
          detIntegrand ρ ε 2 e.2.1
            (assemble p.2.2.1 p.2.2.2.1
              (fun i => p.2.2.2.2 (rightMomentIndex i))) *
          momentCrossCovarianceProduct ρ ε 2 e.1 e.2.1 e.2.2
            p.2.2.2.2 =
          r324CrossPhysicalDensity ρ ε j₀ j₁ p := by
      show
        detIntegrand ρ ε 2 idPairingFinTwo
            (assemble p.1 p.2.1
              (fun i => p.2.2.2.2 (leftMomentIndex i))) *
          detIntegrand ρ ε 2 idPairingFinTwo
            (assemble p.2.2.1 p.2.2.2.1
              (fun i => p.2.2.2.2 (rightMomentIndex i))) *
          momentCrossCovarianceProduct ρ ε 2
            idPairingFinTwo idPairingFinTwo π p.2.2.2.2 =
          r324CrossPhysicalDensity ρ ε j₀ j₁ p
      simp only [detIntegrand_idPairingFinTwo_assemble,
        momentCrossCovarianceProduct_id_id]
      unfold r324CrossPhysicalDensity r324CrossCoreDensity
      rw [← hj₀def, ← hj₁def]
      ring
    rw [hD]
    rw [abs_of_nonneg ?_]
    unfold r324CrossPhysicalDensity r324CrossCoreDensity
    have h1 := greenFn_nonneg
      (p.1 - p.2.2.2.2 (leftMomentIndex 0))
    have h2 := greenFn_nonneg
      (p.2.2.2.2 (leftMomentIndex 1) - p.2.1)
    have h3 := greenFn_nonneg
      (p.2.2.1 - p.2.2.2.2 (rightMomentIndex 0))
    have h4 := greenFn_nonneg
      (p.2.2.2.2 (rightMomentIndex 1) - p.2.2.2.1)
    have h5 := greenFn_nonneg
      (p.2.2.2.2 (leftMomentIndex 0) -
        p.2.2.2.2 (leftMomentIndex 1))
    have h6 := greenFn_nonneg
      (p.2.2.2.2 (rightMomentIndex 0) -
        p.2.2.2.2 (rightMomentIndex 1))
    have h7 := ρ.etaEpsT4_nonneg ε
      (p.2.2.2.2 (leftMomentIndex 0) -
        p.2.2.2.2 (rightMomentIndex j₀))
    have h8 := ρ.etaEpsT4_nonneg ε
      (p.2.2.2.2 (leftMomentIndex 1) -
        p.2.2.2.2 (rightMomentIndex j₁))
    positivity
  have hdensityint :
      Integrable (r324CrossPhysicalDensity ρ ε j₀ j₁)
        (r324PhysicalMeasure 2) := by
    refine hflat.norm.congr ?_
    filter_upwards with p
    exact hnormeq p
  calc
    ‖deterministicMomentContractionTerm ρ ε 2 α β e‖ =
        ‖∫ p, r324Flatten
          (deterministicMomentIntegrand ρ ε 2 α β
            e.1 e.2.1 e.2.2) p
          ∂(r324PhysicalMeasure 2)‖ := by rw [hterm]
    _ ≤ ∫ p, ‖r324Flatten
          (deterministicMomentIntegrand ρ ε 2 α β
            e.1 e.2.1 e.2.2) p‖
          ∂(r324PhysicalMeasure 2) :=
      norm_integral_le_integral_norm _
    _ = ∫ p, r324CrossPhysicalDensity ρ ε j₀ j₁ p
          ∂(r324PhysicalMeasure 2) :=
      integral_congr_ae (Filter.Eventually.of_forall hnormeq)
    _ = ∫ v : Fin (2 * 2) → T4,
          r324CrossCoreDensity ρ ε j₀ j₁ v
          ∂(Measure.pi fun _ : Fin (2 * 2) => paperMeasure) :=
      integral_flat_crossPhysicalDensity ρ ε j₀ j₁ hdensityint
    _ ≤ ∑' k : Z4,
          ‖ρ.symbol ε k‖ ^ 4 * ((1 + paperModeNormSq k)⁻¹) ^ 2 :=
      integral_crossCoreDensity_le ρ hε hε1 hj
        (integrable_crossCoreDensity_of_flat ρ ε j₀ j₁ hdensityint)

/-- **Logarithmic bound for the cross contraction term.**  The
mollifier-dependent constant is uniform in the scale, the coupling,
and both external modes. -/
theorem exists_norm_crossContractionTerm_le_log (ρ : SmoothCutoff) :
    ∃ CW : ℝ, 0 < CW ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        ∀ (α β : Z4)
          (π : idPairingFinTwo.singles ≃ idPairingFinTwo.singles),
          ‖deterministicMomentContractionTerm ρ ε 2 α β
              ⟨idPairingFinTwo, ⟨idPairingFinTwo, π⟩⟩‖ ≤
            CW * |Real.log ε| := by
  obtain ⟨CW, hCW, hwindow⟩ := exists_crossWindow_le_log ρ
  refine ⟨CW, hCW, ?_⟩
  intro ε hε hε1 hlog α β π
  exact le_trans
    (norm_deterministicMomentContractionTerm_cross_le
      ρ hε hε1 α β π)
    (hwindow hε hε1 hlog)

end

end Anderson4D
