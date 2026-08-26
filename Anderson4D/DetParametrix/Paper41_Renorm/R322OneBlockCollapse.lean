import Anderson4D.DetParametrix.Paper41_Renorm.R322OneBlock
import Anderson4D.DetParametrix.Paper41_Renorm.R322Collapse
import Anderson4D.DetParametrix.Paper41_Renorm.R322Normalize

/-!
# Closing one proper-block collapse

Paper: R-322 — §4.1 — closing one proper-block collapse

This file inserts the three-region inner estimate into the concrete
two-variable collapse of (4.8).  The first step records the Haar
change of variables `u = q - w`; the second is the Fubini identity
which exposes `r322GreenDifferenceSection` in the outer integral.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set

private def r322SubLeftMeasurableEquiv
    (q : T4) : T4 ≃ᵐ T4 :=
  MeasurableEquiv.piCongrRight fun i =>
    (MeasurableEquiv.neg
        (AddCircle (2 * Real.pi))).trans
      (MeasurableEquiv.addLeft (q i))

@[simp]
private theorem r322SubLeftMeasurableEquiv_apply
    (q u : T4) :
    r322SubLeftMeasurableEquiv q u = q - u := by
  funext i
  change
    (Equiv.piCongrRight (fun i =>
      ((MeasurableEquiv.neg
          (AddCircle (2 * Real.pi))).trans
        (MeasurableEquiv.addLeft (q i))).toEquiv) u) i =
      q i - u i
  rw [Equiv.piCongrRight_apply, Pi.map_apply]
  change q i + -u i = q i - u i
  rw [sub_eq_add_neg]

private theorem measurePreserving_r322SubLeft
    (q : T4) :
    MeasurePreserving (r322SubLeftMeasurableEquiv q)
      paperMeasure paperMeasure := by
  rw [paperMeasure_eq_volume]
  have hpi :
      MeasurePreserving
        (fun u : T4 => fun i => q i + -u i)
        (volume : Measure T4) (volume : Measure T4) :=
    measurePreserving_pi
      (fun _ : Fin dim =>
        (volume : Measure (AddCircle (2 * Real.pi))))
      (fun _ : Fin dim =>
        (volume : Measure (AddCircle (2 * Real.pi))))
      (f := fun i u => q i + -u) fun i =>
        (measurePreserving_add_left
          (volume : Measure (AddCircle (2 * Real.pi)))
          (q i)).comp
          (Measure.measurePreserving_neg _)
  have hfun :
      (r322SubLeftMeasurableEquiv q : T4 → T4) =
        fun u : T4 => fun i => q i + -u i := by
    funext u i
    rw [r322SubLeftMeasurableEquiv_apply]
    change q i - u i = q i + -u i
    rw [sub_eq_add_neg]
  rw [hfun]
  exact hpi

/-- Translation-reflection invariance of paper measure in exactly the
orientation used by the proper-block collapse. -/
theorem integral_r322GreenDifference_change
    (J : T4 → ℝ) (q : T4) :
    (∫ w,
      J (q - w) * (greenFn w - greenFn q)
        ∂paperMeasure) =
      r322GreenDifferenceSection J q := by
  unfold r322GreenDifferenceSection
  calc
    (∫ w,
      J (q - w) * (greenFn w - greenFn q)
        ∂paperMeasure) =
      ∫ w,
        (fun u =>
          J u * (greenFn (q - u) - greenFn q))
            (r322SubLeftMeasurableEquiv q w)
        ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with w
      rw [r322SubLeftMeasurableEquiv_apply]
      simp
    _ = ∫ u,
        J u * (greenFn (q - u) - greenFn q)
        ∂paperMeasure :=
      (measurePreserving_r322SubLeft q).integral_comp
        (r322SubLeftMeasurableEquiv q).measurableEmbedding
        (fun u : T4 =>
          J u * (greenFn (q - u) - greenFn q))

/-- Fubini and the translated Haar change of variables turn the concrete
collapse into the outer convolution of the left input with the Green
difference section. -/
theorem r322Collapse_eq_integral_greenDifferenceSection
    (Gp J : T4 → ℝ) (x : T4)
    (hint :
      Integrable
        (r322CollapseIntegrand Gp J greenFn x)
        (paperMeasure.prod paperMeasure)) :
    r322Collapse Gp J greenFn x =
      ∫ q,
        Gp (x - q) *
          r322GreenDifferenceSection J q
        ∂paperMeasure := by
  unfold r322Collapse
  rw [integral_prod _ hint]
  apply integral_congr_ae
  filter_upwards with q
  calc
    (∫ w,
      r322CollapseIntegrand Gp J greenFn x (q, w)
        ∂paperMeasure) =
      Gp (x - q) *
        (∫ w,
          J (q - w) *
            (greenFn w - greenFn q)
          ∂paperMeasure) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with w
      unfold r322CollapseIntegrand
      ring
    _ = Gp (x - q) *
        r322GreenDifferenceSection J q := by
      rw [integral_r322GreenDifference_change]

/-- Joint integrability of the concrete collapse supplies integrability
of its section form; no separate Fubini hypothesis is needed later. -/
theorem integrable_r322Collapse_greenDifferenceSection
    (Gp J : T4 → ℝ) (x : T4)
    (hint :
      Integrable
        (r322CollapseIntegrand Gp J greenFn x)
        (paperMeasure.prod paperMeasure)) :
    Integrable
      (fun q =>
        Gp (x - q) *
          r322GreenDifferenceSection J q)
      paperMeasure := by
  have houter :
      Integrable
        (fun q =>
          ∫ w,
            r322CollapseIntegrand Gp J greenFn x (q, w)
            ∂paperMeasure)
        paperMeasure :=
    hint.integral_prod_left
  refine houter.congr (.of_forall fun q => ?_)
  calc
    (∫ w,
      r322CollapseIntegrand Gp J greenFn x (q, w)
        ∂paperMeasure) =
      Gp (x - q) *
        (∫ w,
          J (q - w) *
            (greenFn w - greenFn q)
          ∂paperMeasure) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with w
      unfold r322CollapseIntegrand
      ring
    _ = Gp (x - q) *
        r322GreenDifferenceSection J q := by
      rw [integral_r322GreenDifference_change]

/-! ## Integrability of the three outer profiles -/

theorem integrable_r322TaylorDensity_convolution
    {supportConstant C lam ε : ℝ} {n : ℕ} {x : T4}
    (hsupport : 0 < supportConstant)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) :
    Integrable
      (fun q =>
        invSqKer (x - q) *
          r322TaylorDensity
            C lam ε supportConstant n q)
      paperMeasure := by
  obtain ⟨Kinner, hKinner, hinner⟩ :=
    exists_r322TaylorDensity_inner_le
  obtain ⟨Kouter, hKouter, houter⟩ :=
    exists_r322TaylorDensity_outer_le hsupport
  let L : ℝ := |Real.log ε|
  let A : ℝ := (C * lam) ^ (2 * n)
  let Sin : Set T4 := r322ScaleBall 1 ε
  let Sout : Set T4 := r322CriticalAnnulus ε
  let f : T4 → ℝ := fun q =>
    invSqKer (x - q) *
      r322TaylorDensity C lam ε supportConstant n q
  let g₁ : T4 → ℝ := fun q =>
    Sin.indicator
      (fun z =>
        (A * Kinner * (ε⁻¹ ^ (4 : ℕ) / L)) *
          invSqKer (x - z)) q
  let g₂ : T4 → ℝ := fun q =>
    Sout.indicator
      (fun z =>
        (A * Kouter) *
          ((1 / L) *
            (invSqKer (x - z) * invSqKer z ^ 2))) q
  have hA : 0 ≤ A := pow_nonneg (mul_nonneg hC hlam) _
  have hSin : MeasurableSet Sin :=
    measurableSet_r322ScaleBall 1 ε
  have hSout : MeasurableSet Sout :=
    measurableSet_r322CriticalAnnulus ε
  have hg₁ : Integrable g₁ paperMeasure := by
    dsimp only [g₁]
    exact
      ((integrable_invSqKer_sub_left x).const_mul
        (A * Kinner * (ε⁻¹ ^ (4 : ℕ) / L))).indicator hSin
  have hg₂ : Integrable g₂ paperMeasure := by
    dsimp only [g₂]
    have hg₂On :
        IntegrableOn
          (fun z : T4 =>
            (A * Kouter) *
              ((1 / L) *
                (invSqKer (x - z) *
                  invSqKer z ^ 2)))
          Sout paperMeasure :=
      ((integrableOn_r322Critical_product hε x).const_mul
        (1 / L)).const_mul (A * Kouter)
    exact hg₂On.integrable_indicator hSout
  have hpoint : ∀ q, f q ≤ g₁ q + g₂ q := by
    intro q
    by_cases hqin : torusDistSq q ≤ ε ^ 2
    · have hmem : q ∈ Sin := by
        change torusDistSq q ≤ (1 * ε) ^ 2
        simpa only [one_mul] using hqin
      rw [show g₁ q =
          (A * Kinner * (ε⁻¹ ^ (4 : ℕ) / L)) *
            invSqKer (x - q) by
        simp [g₁, hmem]]
      by_cases hq : q = 0
      · subst q
        unfold f r322TaylorDensity
        rw [invSqKer_zero_r322,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0),
          zero_mul, mul_zero]
        have hg₂0 : 0 ≤ g₂ 0 := by
          dsimp only [g₂]
          apply Set.indicator_nonneg
          intro z _
          exact mul_nonneg
            (mul_nonneg hA hKouter.le)
            (mul_nonneg (by positivity)
              (mul_nonneg
                (invSqKer_nonneg _)
                (sq_nonneg _)))
        exact add_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg hA hKinner.le)
              (by positivity))
            (by
              simpa only [sub_zero] using
                invSqKer_nonneg x))
          hg₂0
      · have hdensity :=
          hinner C lam ε supportConstant n q
            hC hlam hε hsupport hlog hq hqin
        unfold f
        have hmul :
            invSqKer (x - q) *
                r322TaylorDensity C lam ε
                  supportConstant n q ≤
              invSqKer (x - q) *
                (A * Kinner *
                  (ε⁻¹ ^ (4 : ℕ) / L)) :=
          mul_le_mul_of_nonneg_left hdensity
            (invSqKer_nonneg (x - q))
        exact le_add_of_le_of_nonneg
          (by
            calc
              invSqKer (x - q) *
                    r322TaylorDensity C lam ε
                      supportConstant n q ≤
                  invSqKer (x - q) *
                    (A * Kinner *
                      (ε⁻¹ ^ (4 : ℕ) / L)) := hmul
              _ = (A * Kinner *
                    (ε⁻¹ ^ (4 : ℕ) / L)) *
                  invSqKer (x - q) := by ring)
          (Set.indicator_nonneg
            (fun _ _ =>
              mul_nonneg
                (mul_nonneg hA hKouter.le)
                (mul_nonneg (by positivity)
                  (mul_nonneg
                    (invSqKer_nonneg _)
                    (sq_nonneg _)))) q)
    · have hqout : ε ^ 2 ≤ torusDistSq q :=
        le_of_not_ge hqin
      have hmem : q ∈ Sout := hqout
      rw [show g₂ q =
          (A * Kouter) *
            ((1 / L) *
              (invSqKer (x - q) * invSqKer q ^ 2)) by
        simp [g₂, hmem]]
      have hdensity :=
        houter C lam ε n q hC hlam hε hε1 hlog
      unfold f
      have hmul :
          invSqKer (x - q) *
              r322TaylorDensity C lam ε supportConstant n q ≤
            invSqKer (x - q) *
              (A * Kouter *
                ((1 / L) * invSqKer q ^ 2)) :=
        mul_le_mul_of_nonneg_left hdensity
          (invSqKer_nonneg (x - q))
      exact le_add_of_nonneg_of_le
        (Set.indicator_nonneg
          (fun _ _ =>
            mul_nonneg
              (mul_nonneg
                (mul_nonneg hA hKinner.le)
                (by positivity))
              (invSqKer_nonneg _)) q)
        (hmul.trans_eq (by ring))
  apply (hg₁.add hg₂).mono'
    (((measurable_invSqKer.comp
        (measurable_const.sub measurable_id)).mul
      (measurable_r322TaylorDensity
        C lam ε supportConstant n)).aestronglyMeasurable)
  filter_upwards with q
  change
    |invSqKer (x - q) *
        r322TaylorDensity
          C lam ε supportConstant n q| ≤
      g₁ q + g₂ q
  rw [abs_of_nonneg
      (mul_nonneg (invSqKer_nonneg (x - q))
        (r322TaylorDensity_nonneg hC hlam
          ε supportConstant n q))]
  exact hpoint q

theorem integrable_r322RegionTwoDensity_convolution
    {supportConstant C lam ε : ℝ} {n : ℕ} {x : T4}
    (hsupport : 0 < supportConstant)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) (hx : x ≠ 0) :
    Integrable
      (fun q =>
        invSqKer (x - q) *
          r322RegionTwoDensity
            C lam ε supportConstant n q)
      paperMeasure := by
  obtain
    ⟨Knear, Kouter, hKnear, hKouter, hprofile⟩ :=
      exists_r322RegionTwoDensity_profile_le hsupport
  let L : ℝ := |Real.log ε|
  let P : ℝ := (C * lam) ^ (2 * n)
  let Sin : Set T4 :=
    r322ScaleBall (4 * supportConstant + 1) ε
  let Sout : Set T4 :=
    r322CriticalAnnulus ε
  let f : T4 → ℝ := fun q =>
    invSqKer (x - q) *
      r322RegionTwoDensity
        C lam ε supportConstant n q
  let g₁ : T4 → ℝ := fun q =>
    Sin.indicator
      (fun z =>
        (P * Knear *
          (ε⁻¹ ^ (2 : ℕ) / L)) *
            (invSqKer (x - z) * invSqKer z)) q
  let g₂ : T4 → ℝ := fun q =>
    Sout.indicator
      (fun z =>
        (P * Kouter) *
          ((1 / L) *
            (invSqKer (x - z) *
              invSqKer z ^ 2))) q
  have hP : 0 ≤ P :=
    pow_nonneg (mul_nonneg hC hlam) _
  have hSin : MeasurableSet Sin :=
    measurableSet_r322ScaleBall
      (4 * supportConstant + 1) ε
  have hSout : MeasurableSet Sout :=
    measurableSet_r322CriticalAnnulus ε
  have hg₁ : Integrable g₁ paperMeasure := by
    dsimp only [g₁]
    exact
      ((integrable_invSqKer_sub_mul_invSqKer_of_ne hx)
        |>.const_mul
          (P * Knear *
            (ε⁻¹ ^ (2 : ℕ) / L)))
        |>.indicator hSin
  have hg₂ : Integrable g₂ paperMeasure := by
    dsimp only [g₂]
    have hg₂On :
        IntegrableOn
          (fun z : T4 =>
            (P * Kouter) *
              ((1 / L) *
                (invSqKer (x - z) *
                  invSqKer z ^ 2)))
          Sout paperMeasure :=
      ((integrableOn_r322Critical_product hε x)
        |>.const_mul (1 / L))
        |>.const_mul (P * Kouter)
    exact hg₂On.integrable_indicator hSout
  have hpoint : ∀ q, f q ≤ g₁ q + g₂ q := by
    intro q
    have hdensity :=
      hprofile C lam ε n q hC hlam hε hε1 hlog
    dsimp only [f]
    calc
      invSqKer (x - q) *
            r322RegionTwoDensity
              C lam ε supportConstant n q ≤
          invSqKer (x - q) *
            ((r322ScaleBall
              (4 * supportConstant + 1) ε).indicator
              (fun z =>
                (C * lam) ^ (2 * n) * Knear *
                  (ε⁻¹ ^ (2 : ℕ) /
                    |Real.log ε|) *
                      invSqKer z) q +
            (r322CriticalAnnulus ε).indicator
              (fun z =>
                (C * lam) ^ (2 * n) * Kouter *
                  (1 / |Real.log ε|) *
                    invSqKer z ^ 2) q) :=
        mul_le_mul_of_nonneg_left hdensity
          (invSqKer_nonneg (x - q))
      _ = g₁ q + g₂ q := by
        dsimp only [g₁, g₂, Sin, Sout, P, L]
        by_cases hqSin :
            q ∈ r322ScaleBall
              (4 * supportConstant + 1) ε
        <;> by_cases hqSout :
            q ∈ r322CriticalAnnulus ε
        <;> simp [hqSin, hqSout]
        <;> ring
  apply (hg₁.add hg₂).mono'
    (((measurable_invSqKer.comp
        (measurable_const.sub measurable_id)).mul
      (measurable_r322RegionTwoDensity
        C lam ε supportConstant n)).aestronglyMeasurable)
  filter_upwards with q
  change
    |invSqKer (x - q) *
        r322RegionTwoDensity
          C lam ε supportConstant n q| ≤
      g₁ q + g₂ q
  rw [abs_of_nonneg
    (mul_nonneg (invSqKer_nonneg (x - q))
      (r322RegionTwoDensity_nonneg
        hC hlam ε supportConstant n q))]
  exact hpoint q

theorem integrable_r322RegionThreeDensity_convolution
    {supportConstant C lam ε : ℝ} {n : ℕ} {x : T4}
    (hsupport : 0 < supportConstant)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) :
    Integrable
      (fun q =>
        invSqKer (x - q) *
          r322RegionThreeDensity
            C lam ε supportConstant n q)
      paperMeasure := by
  obtain
    ⟨Knear, Kouter, hKnear, hKouter, hprofile⟩ :=
      exists_r322RegionThreeDensity_profile_le hsupport
  let L : ℝ := |Real.log ε|
  let P : ℝ := (C * lam) ^ (2 * n)
  let Sin : Set T4 :=
    r322ScaleBall (3 * supportConstant + 1) ε
  let Sout : Set T4 :=
    r322CriticalAnnulus ε
  let f : T4 → ℝ := fun q =>
    invSqKer (x - q) *
      r322RegionThreeDensity
        C lam ε supportConstant n q
  let g₁ : T4 → ℝ := fun q =>
    Sin.indicator
      (fun z =>
        (P * Knear *
          (ε⁻¹ ^ (4 : ℕ) / L)) *
            invSqKer (x - z)) q
  let g₂ : T4 → ℝ := fun q =>
    Sout.indicator
      (fun z =>
        (P * Kouter) *
          ((1 / L) *
            (invSqKer (x - z) *
              invSqKer z ^ 2))) q
  have hP : 0 ≤ P :=
    pow_nonneg (mul_nonneg hC hlam) _
  have hSin : MeasurableSet Sin :=
    measurableSet_r322ScaleBall
      (3 * supportConstant + 1) ε
  have hSout : MeasurableSet Sout :=
    measurableSet_r322CriticalAnnulus ε
  have hg₁ : Integrable g₁ paperMeasure := by
    dsimp only [g₁]
    exact
      ((integrable_invSqKer_sub_left x).const_mul
        (P * Knear *
          (ε⁻¹ ^ (4 : ℕ) / L))).indicator hSin
  have hg₂ : Integrable g₂ paperMeasure := by
    dsimp only [g₂]
    have hg₂On :
        IntegrableOn
          (fun z : T4 =>
            (P * Kouter) *
              ((1 / L) *
                (invSqKer (x - z) *
                  invSqKer z ^ 2)))
          Sout paperMeasure :=
      ((integrableOn_r322Critical_product hε x)
        |>.const_mul (1 / L))
        |>.const_mul (P * Kouter)
    exact hg₂On.integrable_indicator hSout
  have hpoint : ∀ q, f q ≤ g₁ q + g₂ q := by
    intro q
    have hdensity :=
      hprofile C lam ε n q hC hlam hε hε1 hlog
    dsimp only [f]
    calc
      invSqKer (x - q) *
            r322RegionThreeDensity
              C lam ε supportConstant n q ≤
          invSqKer (x - q) *
            ((r322ScaleBall
              (3 * supportConstant + 1) ε).indicator
              (fun _ =>
                (C * lam) ^ (2 * n) * Knear *
                  (ε⁻¹ ^ (4 : ℕ) /
                    |Real.log ε|)) q +
            (r322CriticalAnnulus ε).indicator
              (fun z =>
                (C * lam) ^ (2 * n) * Kouter *
                  (1 / |Real.log ε|) *
                    invSqKer z ^ 2) q) :=
        mul_le_mul_of_nonneg_left hdensity
          (invSqKer_nonneg (x - q))
      _ = g₁ q + g₂ q := by
        dsimp only [g₁, g₂, Sin, Sout, P, L]
        by_cases hqSin :
            q ∈ r322ScaleBall
              (3 * supportConstant + 1) ε
        <;> by_cases hqSout :
            q ∈ r322CriticalAnnulus ε
        <;> simp [hqSin, hqSout]
        <;> ring
  apply (hg₁.add hg₂).mono'
    (((measurable_invSqKer.comp
        (measurable_const.sub measurable_id)).mul
      (measurable_r322RegionThreeDensity
        C lam ε supportConstant n)).aestronglyMeasurable)
  filter_upwards with q
  change
    |invSqKer (x - q) *
        r322RegionThreeDensity
          C lam ε supportConstant n q| ≤
      g₁ q + g₂ q
  rw [abs_of_nonneg
    (mul_nonneg (invSqKer_nonneg (x - q))
      (r322RegionThreeDensity_nonneg
        hC hlam ε supportConstant n q))]
  exact hpoint q

/-! ## Quantitative closure of one block -/

/-- A proper primitive block can be collapsed without losing the
inverse-square input class.  The constant is chosen once before the
scale, coupling, order, input kernel, primitive block, and endpoint. -/
theorem exists_r322Collapse_le
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C lam ε A : ℝ) (n : ℕ)
        (Gp J : T4 → ℝ) (x : T4),
        0 ≤ C → 0 ≤ lam → 0 ≤ A →
        0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| → x ≠ 0 →
        Measurable J → MemEClassT4 J →
        (∀ u, |J u| ≤
          primitiveKernelMajorant
            C lam ε supportConstant n u) →
        (∀ z, z ≠ 0 →
          |Gp z| ≤ A * invSqKer z) →
        Integrable
          (r322CollapseIntegrand Gp J greenFn x)
          (paperMeasure.prod paperMeasure) →
        |r322Collapse Gp J greenFn x| ≤
          A * (C * lam) ^ (2 * n) * K *
            invSqKer x := by
  obtain ⟨greenConstant, hgreenConstant, hgreen⟩ :=
    greenFn_le
  obtain ⟨Ktaylor, hKtaylor, htaylor⟩ :=
    exists_r322TaylorDensity_convolution_le hsupport
  obtain ⟨Ktwo, hKtwo, htwo⟩ :=
    exists_r322RegionTwoDensity_convolution_le hsupport
  obtain ⟨Kthree, hKthree, hthree⟩ :=
    exists_r322RegionThreeDensity_convolution_le hsupport
  let taylorConstant : ℝ :=
    6144 * greenLocalHessSingularBound
  let K : ℝ :=
    taylorConstant * Ktaylor +
      37 * greenConstant * Ktwo +
      greenConstant * Kthree
  have htaylorConstant : 0 ≤ taylorConstant := by
    dsimp only [taylorConstant]
    exact mul_nonneg (by positivity)
      greenLocalHessSingularBound_nonneg
  have hK : 0 < K := by
    dsimp only [K]
    have hpos :
        0 < 37 * greenConstant * Ktwo := by
      positivity
    nlinarith [
      mul_nonneg htaylorConstant hKtaylor.le,
      mul_nonneg hgreenConstant.le hKthree.le]
  refine ⟨K, hK, ?_⟩
  intro C lam ε A n Gp J x hC hlam hA
    hε hε1 hlog hx hJmeas hJmem hJbound
    hGp hint
  let P : ℝ := (C * lam) ^ (2 * n)
  let M : T4 → ℝ := fun q =>
    (A * taylorConstant) *
        (invSqKer (x - q) *
          r322TaylorDensity
            C lam ε supportConstant n q) +
      (A * (37 * greenConstant)) *
        (invSqKer (x - q) *
          r322RegionTwoDensity
            C lam ε supportConstant n q) +
      (A * greenConstant) *
        (invSqKer (x - q) *
          r322RegionThreeDensity
            C lam ε supportConstant n q)
  have hP : 0 ≤ P :=
    pow_nonneg (mul_nonneg hC hlam) _
  have hTaylorInt :
      Integrable
        (fun q =>
          invSqKer (x - q) *
            r322TaylorDensity
              C lam ε supportConstant n q)
        paperMeasure :=
    integrable_r322TaylorDensity_convolution
      hsupport hC hlam hε hε1 hlog
  have hTwoInt :
      Integrable
        (fun q =>
          invSqKer (x - q) *
            r322RegionTwoDensity
              C lam ε supportConstant n q)
        paperMeasure :=
    integrable_r322RegionTwoDensity_convolution
      hsupport hC hlam hε hε1 hlog hx
  have hThreeInt :
      Integrable
        (fun q =>
          invSqKer (x - q) *
            r322RegionThreeDensity
              C lam ε supportConstant n q)
        paperMeasure :=
    integrable_r322RegionThreeDensity_convolution
      hsupport hC hlam hε hε1 hlog
  have hM : Integrable M paperMeasure := by
    dsimp only [M]
    exact
      ((hTaylorInt.const_mul
        (A * taylorConstant)).add
        (hTwoInt.const_mul
          (A * (37 * greenConstant)))).add
        (hThreeInt.const_mul
          (A * greenConstant))
  have houter :
      Integrable
        (fun q =>
          Gp (x - q) *
            r322GreenDifferenceSection J q)
        paperMeasure :=
    integrable_r322Collapse_greenDifferenceSection
      Gp J x hint
  have hpoint :
      ∀ᵐ q ∂paperMeasure,
        |Gp (x - q) *
          r322GreenDifferenceSection J q| ≤ M q := by
    filter_upwards
      [compl_mem_ae_iff.mpr
          (paperMeasure_singleton (0 : T4)),
        compl_mem_ae_iff.mpr
          (paperMeasure_singleton x)]
      with q hq0 hqx
    have hq : q ≠ 0 := by
      simpa only [mem_compl_iff, mem_singleton_iff] using hq0
    have hqne : q ≠ x := by
      simpa only [mem_compl_iff, mem_singleton_iff] using hqx
    have hxq : x - q ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm hqne)
    have hsection :=
      abs_r322GreenDifferenceSection_le_of_majorant
        hJmem hJmeas hgreenConstant.le hgreen hC hlam
        hsupport hε hq hJbound
    have hGpBound := hGp (x - q) hxq
    have hright :
        0 ≤
          taylorConstant *
              r322TaylorDensity
                C lam ε supportConstant n q +
            37 * greenConstant *
              r322RegionTwoDensity
                C lam ε supportConstant n q +
            greenConstant *
              r322RegionThreeDensity
                C lam ε supportConstant n q := by
      exact add_nonneg
        (add_nonneg
          (mul_nonneg htaylorConstant
            (r322TaylorDensity_nonneg hC hlam
              ε supportConstant n q))
          (mul_nonneg
            (mul_nonneg (by positivity)
              hgreenConstant.le)
            (r322RegionTwoDensity_nonneg hC hlam
              ε supportConstant n q)))
        (mul_nonneg hgreenConstant.le
          (r322RegionThreeDensity_nonneg hC hlam
            ε supportConstant n q))
    rw [abs_mul]
    calc
      |Gp (x - q)| *
          |r322GreenDifferenceSection J q| ≤
        (A * invSqKer (x - q)) *
          (taylorConstant *
              r322TaylorDensity
                C lam ε supportConstant n q +
            37 * greenConstant *
              r322RegionTwoDensity
                C lam ε supportConstant n q +
            greenConstant *
              r322RegionThreeDensity
                C lam ε supportConstant n q) :=
        mul_le_mul hGpBound
          (by simpa only [taylorConstant] using hsection)
          (abs_nonneg _)
          (mul_nonneg hA (invSqKer_nonneg (x - q)))
      _ = M q := by
        dsimp only [M]
        ring
  rw [r322Collapse_eq_integral_greenDifferenceSection
    Gp J x hint]
  calc
    |∫ q,
        Gp (x - q) *
          r322GreenDifferenceSection J q
        ∂paperMeasure| ≤
      ∫ q,
        |Gp (x - q) *
          r322GreenDifferenceSection J q|
        ∂paperMeasure := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (μ := paperMeasure)
          (fun q =>
            Gp (x - q) *
              r322GreenDifferenceSection J q))
    _ ≤ ∫ q, M q ∂paperMeasure :=
      integral_mono_ae houter.abs hM hpoint
    _ =
        (A * taylorConstant) *
            (∫ q,
              invSqKer (x - q) *
                r322TaylorDensity
                  C lam ε supportConstant n q
              ∂paperMeasure) +
          (A * (37 * greenConstant)) *
            (∫ q,
              invSqKer (x - q) *
                r322RegionTwoDensity
                  C lam ε supportConstant n q
              ∂paperMeasure) +
          (A * greenConstant) *
            (∫ q,
              invSqKer (x - q) *
                r322RegionThreeDensity
                  C lam ε supportConstant n q
              ∂paperMeasure) := by
      dsimp only [M]
      calc
        (∫ q,
            (A * taylorConstant *
                (invSqKer (x - q) *
                  r322TaylorDensity
                    C lam ε supportConstant n q) +
              A * (37 * greenConstant) *
                (invSqKer (x - q) *
                  r322RegionTwoDensity
                    C lam ε supportConstant n q)) +
              A * greenConstant *
                (invSqKer (x - q) *
                  r322RegionThreeDensity
                    C lam ε supportConstant n q)
            ∂paperMeasure) =
          (∫ q,
              A * taylorConstant *
                  (invSqKer (x - q) *
                    r322TaylorDensity
                      C lam ε supportConstant n q) +
                A * (37 * greenConstant) *
                  (invSqKer (x - q) *
                    r322RegionTwoDensity
                      C lam ε supportConstant n q)
              ∂paperMeasure) +
            ∫ q,
              A * greenConstant *
                (invSqKer (x - q) *
                  r322RegionThreeDensity
                    C lam ε supportConstant n q)
              ∂paperMeasure := by
          exact integral_add
            ((hTaylorInt.const_mul
              (A * taylorConstant)).add
              (hTwoInt.const_mul
                (A * (37 * greenConstant))))
            (hThreeInt.const_mul
              (A * greenConstant))
        _ =
          ((∫ q,
              A * taylorConstant *
                (invSqKer (x - q) *
                  r322TaylorDensity
                    C lam ε supportConstant n q)
              ∂paperMeasure) +
            ∫ q,
              A * (37 * greenConstant) *
                (invSqKer (x - q) *
                  r322RegionTwoDensity
                    C lam ε supportConstant n q)
              ∂paperMeasure) +
            ∫ q,
              A * greenConstant *
                (invSqKer (x - q) *
                  r322RegionThreeDensity
                    C lam ε supportConstant n q)
              ∂paperMeasure := by
          rw [integral_add
            (hTaylorInt.const_mul
              (A * taylorConstant))
            (hTwoInt.const_mul
              (A * (37 * greenConstant)))]
        _ = _ := by
          rw [integral_const_mul, integral_const_mul,
            integral_const_mul]
    _ ≤
        (A * taylorConstant) *
            (P * Ktaylor * invSqKer x) +
          (A * (37 * greenConstant)) *
            (P * Ktwo * invSqKer x) +
          (A * greenConstant) *
            (P * Kthree * invSqKer x) := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left
            (htaylor C lam ε n x hC hlam
              hε hε1 hlog hx)
            (mul_nonneg hA htaylorConstant))
          (mul_le_mul_of_nonneg_left
            (htwo C lam ε n x hC hlam
              hε hε1 hlog hx)
            (mul_nonneg hA
              (mul_nonneg (by positivity)
                hgreenConstant.le))))
        (mul_le_mul_of_nonneg_left
          (hthree C lam ε n x hC hlam
            hε hε1 hlog hx)
          (mul_nonneg hA hgreenConstant.le))
    _ = A * (C * lam) ^ (2 * n) * K *
          invSqKer x := by
      dsimp only [P, K]
      ring

/-- After dividing by its proved scale factor and changing only the null
diagonal, a collapsed kernel is an admissible input in every later use of
Proposition 4.1.  This is the analytic induction interface behind (4.13). -/
theorem exists_normalized_r322Collapse_admissible
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C lam ε A : ℝ) (n : ℕ)
        (Gp J : T4 → ℝ),
        0 < C → 0 < lam → 0 < A →
        0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| →
        Measurable J →
        MemEClassT4 Gp → MemEClassT4 J →
        (∀ u, |J u| ≤
          primitiveKernelMajorant
            C lam ε supportConstant n u) →
        (∀ z, z ≠ 0 →
          |Gp z| ≤ A * invSqKer z) →
        (∀ x,
          Integrable
            (r322CollapseIntegrand Gp J greenFn x)
            (paperMeasure.prod paperMeasure)) →
        ∀ m : ℕ,
          IsAdmissiblePrimitiveInput m
            (fun _ =>
              normalizedOffDiagonalRepresentative
                (A * (C * lam) ^ (2 * n) * K)
                (r322Collapse Gp J greenFn)) := by
  obtain ⟨K, hK, hcollapse⟩ :=
    exists_r322Collapse_le hsupport
  refine ⟨K, hK, ?_⟩
  intro C lam ε A n Gp J hC hlam hA hε hε1
    hlog hJmeas hGpMem hJmem hJbound hGpBound
    hint m
  let B : ℝ := A * (C * lam) ^ (2 * n) * K
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  apply normalizedOffDiagonalRepresentative_admissible
    (C := fun _ : Fin (2 * m - 1) => B)
  · intro _
    exact hB
  · intro _
    exact r322Collapse_memE hGpMem hJmem greenFn_memE
  · intro _ z hz
    apply hcollapse C lam ε A n Gp J z
      hC.le hlam.le hA.le hε hε1 hlog hz
      hJmeas hJmem hJbound hGpBound
    exact hint z

/-! ## Abstract iteration of the analytic collapse -/

/-- One already-summed primitive coordinate in the interval reduction.
Its fields are exactly the outputs of Proposition 4.1 used in (4.13). -/
structure R322AnalyticStage
    (C lam ε supportConstant : ℝ) where
  order : ℕ
  order_pos : 1 ≤ order
  kernel : T4 → ℝ
  measurable_kernel : Measurable kernel
  memE_kernel : MemEClassT4 kernel
  kernel_le : ∀ u,
    |kernel u| ≤
      primitiveKernelMajorant
        C lam ε supportConstant order u

/-- Successively insert the collapsed input produced by each primitive
coordinate into the left Green slot of the next coordinate. -/
def r322Iterate
    {C lam ε supportConstant : ℝ}
    (Gp : T4 → ℝ) :
    List (R322AnalyticStage C lam ε supportConstant) →
      T4 → ℝ
  | [] => Gp
  | stage :: stages =>
      r322Iterate
        (r322Collapse Gp stage.kernel greenFn) stages

/-- Exact Fubini licenses required by the successive concrete collapses. -/
def R322IterationIntegrable
    {C lam ε supportConstant : ℝ}
    (Gp : T4 → ℝ) :
    List (R322AnalyticStage C lam ε supportConstant) →
      Prop
  | [] => True
  | stage :: stages =>
      (∀ x,
        Integrable
          (r322CollapseIntegrand
            Gp stage.kernel greenFn x)
          (paperMeasure.prod paperMeasure)) ∧
      R322IterationIntegrable
        (r322Collapse Gp stage.kernel greenFn) stages

theorem r322Iterate_memE
    {C lam ε supportConstant : ℝ}
    {Gp : T4 → ℝ} (hGp : MemEClassT4 Gp) :
    ∀ stages :
      List (R322AnalyticStage C lam ε supportConstant),
      MemEClassT4 (r322Iterate Gp stages)
  | [] => hGp
  | stage :: stages =>
      r322Iterate_memE
        (r322Collapse_memE hGp stage.memE_kernel
          greenFn_memE) stages

/-- Quantitative induction for paper (4.13).  Every removed primitive
coordinate contributes its exact perturbative order and one universal
collapse constant; no scale or order dependence is hidden in that
constant. -/
theorem exists_r322Iterate_le
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C lam ε A : ℝ)
        (stages :
          List (R322AnalyticStage
            C lam ε supportConstant))
        (Gp : T4 → ℝ) (x : T4),
        0 ≤ C → 0 ≤ lam → 0 ≤ A →
        0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| → x ≠ 0 →
        (∀ z, z ≠ 0 →
          |Gp z| ≤ A * invSqKer z) →
        R322IterationIntegrable Gp stages →
        |r322Iterate Gp stages x| ≤
          A * K ^ stages.length *
            (C * lam) ^
              (2 * (stages.map
                R322AnalyticStage.order).sum) *
            invSqKer x := by
  obtain ⟨K, hK, hcollapse⟩ :=
    exists_r322Collapse_le hsupport
  refine ⟨K, hK, ?_⟩
  intro C lam ε A stages
  induction stages generalizing A with
  | nil =>
      intro Gp x hC hlam hA hε hε1 hlog hx
        hGp _hint
      simpa [r322Iterate] using hGp x hx
  | cons stage stages ih =>
      intro Gp x hC hlam hA hε hε1 hlog hx
        hGp hint
      have hfirst :
          ∀ z, z ≠ 0 →
            |r322Collapse Gp stage.kernel greenFn z| ≤
              (A * (C * lam) ^ (2 * stage.order) * K) *
                invSqKer z := by
        intro z hz
        simpa only [mul_assoc] using
          hcollapse C lam ε A stage.order
            Gp stage.kernel z hC hlam hA hε hε1
            hlog hz stage.measurable_kernel
            stage.memE_kernel stage.kernel_le hGp
            (hint.1 z)
      have htail :=
        ih (Gp :=
          r322Collapse Gp stage.kernel greenFn)
          (A :=
            A * (C * lam) ^ (2 * stage.order) * K)
          x hC hlam
          (mul_nonneg
            (mul_nonneg hA
              (pow_nonneg
                (mul_nonneg hC hlam) _))
            hK.le)
          hε hε1 hlog hx hfirst hint.2
      calc
        |r322Iterate Gp (stage :: stages) x| =
            |r322Iterate
              (r322Collapse Gp stage.kernel greenFn)
              stages x| := rfl
        _ ≤
            (A * (C * lam) ^ (2 * stage.order) * K) *
              K ^ stages.length *
              (C * lam) ^
                (2 * (stages.map
                  R322AnalyticStage.order).sum) *
              invSqKer x := htail
        _ =
            A * K ^ (stage :: stages).length *
              (C * lam) ^
                (2 * ((stage :: stages).map
                  R322AnalyticStage.order).sum) *
              invSqKer x := by
          simp only [List.length_cons, List.map_cons,
            List.sum_cons, pow_succ]
          rw [show
            2 * (stage.order +
              (stages.map
                R322AnalyticStage.order).sum) =
              2 * stage.order +
                2 * (stages.map
                  R322AnalyticStage.order).sum by omega,
            pow_add]
          ring

end

end Anderson4D
