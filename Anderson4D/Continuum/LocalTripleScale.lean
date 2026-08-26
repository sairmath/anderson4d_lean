import Anderson4D.Continuum.CellSingular

/-!
# The scale-covariant local triple convolution

This file closes the one analytic predicate deliberately isolated in
`Continuum/CellSingular.lean`.  The proof uses the following
four-dimensional scaling argument.

* the `3/2` power of the inverse-square kernel has local mass `O(r)`;
* pointwise AM--GM bounds a product of three inverse-square kernels by
  the sum of the three products of two `3/2` powers;
* in the all-near cell configuration, every relevant cell is contained
  in a ball of radius `6r` about the adjacent endpoint.

Thus each of the three separated products costs `O(r) · O(r) = O(r²)`.
The local `3/2`-power estimate is proved by transporting to the
fundamental cube and evaluating the radial integral
`∫_{‖x‖<r} ‖x‖⁻³ dx = 4 vol(B₁) r` in dimension four.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set

/-! ## The subcritical `3/2` power -/

/-- The `3/2` power of the inverse-square kernel, i.e. the model
`|z|⁻³` singularity. -/
def invSqKerThreeHalf (z : T4) : ℝ :=
  (invSqKer z) ^ (3 / 2 : ℝ)

theorem invSqKerThreeHalf_nonneg (z : T4) :
    0 ≤ invSqKerThreeHalf z :=
  Real.rpow_nonneg (invSqKer_nonneg z) _

theorem measurable_invSqKerThreeHalf :
    Measurable invSqKerThreeHalf :=
  measurable_invSqKer.pow_const _

theorem invSqKerThreeHalf_neg (z : T4) :
    invSqKerThreeHalf (-z) = invSqKerThreeHalf z := by
  unfold invSqKerThreeHalf
  rw [invSqKer_neg]

theorem invSqKerThreeHalf_sub_comm (x y : T4) :
    invSqKerThreeHalf (x - y) = invSqKerThreeHalf (y - x) := by
  rw [← invSqKerThreeHalf_neg (x - y), neg_sub]

/-! ## Cube transport for the local mass -/

private def localMkT4 (x : R4) : T4 :=
  fun i => (x i : AddCircle (2 * Real.pi))

private def localBoxIoc : Set R4 :=
  Set.univ.pi fun _ : Fin dim => Ioc (-Real.pi) Real.pi

private theorem measurableSet_localBoxIoc :
    MeasurableSet localBoxIoc :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

private theorem measurePreserving_localMkT4 :
    MeasurePreserving localMkT4 (volume.restrict localBoxIoc)
      paperMeasure := by
  rw [paperMeasure_eq_volume]
  have h := measurePreserving_pi
    (fun _ : Fin dim =>
      volume.restrict (Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)))
    (fun _ : Fin dim =>
      (volume : Measure (AddCircle (2 * Real.pi))))
    (fun _ => AddCircle.measurePreserving_mk
      (2 * Real.pi) (-Real.pi))
  have hIoc :
      Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) =
        Ioc (-Real.pi) Real.pi := by
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
  rw [hIoc] at h
  have hsrc :
      (Measure.pi fun _ : Fin dim =>
          volume.restrict (Ioc (-Real.pi) Real.pi)) =
        volume.restrict localBoxIoc := by
    rw [← Measure.restrict_pi_pi]
    rfl
  rwa [hsrc] at h

private theorem measurable_localMkT4 :
    Measurable localMkT4 :=
  measurable_pi_lambda _ fun i =>
    AddCircle.measurable_mk'.comp (measurable_pi_apply i)

private theorem local_torus_integral_eq_cube {g : T4 → ℝ}
    (hg : AEStronglyMeasurable g paperMeasure) :
    ∫ z, g z ∂paperMeasure =
      ∫ x in localBoxIoc, g (localMkT4 x) ∂volume := by
  rw [← measurePreserving_localMkT4.map_eq] at hg
  rw [← measurePreserving_localMkT4.map_eq,
    integral_map measurable_localMkT4.aemeasurable hg]

private theorem ae_localBox :
    ∀ᵐ x ∂volume.restrict localBoxIoc,
      ∀ i, x i ∈ Ico (-Real.pi) Real.pi := by
  have hbad :
      volume (⋃ i : Fin dim, {x : R4 | x i = Real.pi}) = 0 :=
    measure_iUnion_null fun i => Measure.pi_hyperplane _ i _
  have hmem :
      ∀ᵐ x ∂volume.restrict localBoxIoc, x ∈ localBoxIoc :=
    ae_restrict_mem measurableSet_localBoxIoc
  have hgood :
      ∀ᵐ x ∂volume.restrict localBoxIoc,
        x ∈ (⋃ i : Fin dim, {x : R4 | x i = Real.pi})ᶜ :=
    ae_restrict_of_ae (compl_mem_ae_iff.mpr hbad)
  filter_upwards [hmem, hgood] with x hxbox hxbad
  intro i
  have hi := hxbox i (mem_univ i)
  have hne : x i ≠ Real.pi :=
    fun he => hxbad (mem_iUnion.mpr ⟨i, he⟩)
  exact ⟨hi.1.le, lt_of_le_of_ne hi.2 hne⟩

private theorem torusLift_localMkT4 {x : R4}
    (hx : ∀ i, x i ∈ Ico (-Real.pi) Real.pi) :
    torusLift (localMkT4 x) = x := by
  funext i
  have hmem :
      x i ∈ Ico (-Real.pi) (-Real.pi + 2 * Real.pi) :=
    ⟨(hx i).1, by have := (hx i).2; linarith⟩
  show ((AddCircle.equivIco (2 * Real.pi) (-Real.pi))
    ((x i : ℝ) : AddCircle (2 * Real.pi)) : ℝ) = x i
  rw [AddCircle.equivIco_coe_eq hmem]

private theorem norm_localMkT4 {x : R4}
    (hx : ∀ i, x i ∈ Ico (-Real.pi) Real.pi) :
    ‖localMkT4 x‖ = ‖x‖ := by
  have hcomp :
      ∀ i, ‖localMkT4 x i‖ = ‖x i‖ := by
    intro i
    rw [norm_eq_abs_torusLift (localMkT4 x) i,
      torusLift_localMkT4 hx, Real.norm_eq_abs]
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun i => ?_
    rw [hcomp i]
    exact norm_le_pi_norm x i
  · refine
      (pi_norm_le_iff_of_nonneg
        (norm_nonneg (localMkT4 x))).mpr fun i => ?_
    rw [← hcomp i]
    exact norm_le_pi_norm (localMkT4 x) i

private theorem torusDistSq_localMkT4 {x : R4}
    (hx : ∀ i, x i ∈ Ico (-Real.pi) Real.pi) :
    torusDistSq (localMkT4 x) = ∑ i, x i ^ 2 := by
  unfold torusDistSq
  rw [torusLift_localMkT4 hx]

private theorem sq_norm_le_sum_local (x : R4) :
    ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := by
  have hs : 0 ≤ ∑ i, x i ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h :
      ‖x‖ ≤ Real.sqrt (∑ i, x i ^ 2) := by
    refine
      (pi_norm_le_iff_of_nonneg
        (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    calc
      |x i| = Real.sqrt (x i ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (∑ j, x j ^ 2) :=
        Real.sqrt_le_sqrt
          (Finset.single_le_sum
            (fun j _ => sq_nonneg (x j))
            (Finset.mem_univ i))
  calc
    ‖x‖ ^ 2 ≤ Real.sqrt (∑ i, x i ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i, x i ^ 2 := Real.sq_sqrt hs

private theorem rpow_neg_anti_local
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    {p : ℝ} (hp : 0 ≤ p) :
    d ^ (-p) ≤ c ^ (-p) := by
  rw [Real.rpow_neg (hc.trans_le hcd).le,
    Real.rpow_neg hc.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hc p)
    (Real.rpow_le_rpow hc.le hcd hp)

private theorem invSqKerThreeHalf_localMkT4_le
    {x : R4}
    (hx : ∀ i, x i ∈ Ico (-Real.pi) Real.pi) :
    invSqKerThreeHalf (localMkT4 x) ≤
      ‖x‖ ^ (-(3 : ℝ)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · unfold invSqKerThreeHalf invSqKer
    rw [torusDistSq_localMkT4 hx]
    norm_num [Real.zero_rpow]
  unfold invSqKerThreeHalf invSqKer
  rw [torusDistSq_localMkT4 hx]
  have hrewrite :
      ((‖x‖ ^ (2 : ℕ) : ℝ)⁻¹) ^ (3 / 2 : ℝ) =
        ‖x‖ ^ (-(3 : ℝ)) := by
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    rw [← Real.rpow_neg_one (‖x‖ ^ (2 : ℕ)),
      ← Real.rpow_mul (pow_nonneg hn.le 2)]
    rw [← Real.rpow_natCast ‖x‖ 2,
      ← Real.rpow_mul hn.le]
    norm_num
  rw [← hrewrite]
  have hsum : 0 < ∑ i, x i ^ 2 := by
    have hn : 0 < ‖x‖ ^ 2 := by positivity
    exact hn.trans_le (sq_norm_le_sum_local x)
  have hinv :
      (∑ i, x i ^ 2)⁻¹ ≤ (‖x‖ ^ 2)⁻¹ :=
    inv_anti₀ (pow_pos (norm_pos_iff.mpr hx0) 2)
      (sq_norm_le_sum_local x)
  exact Real.rpow_le_rpow
    (inv_nonneg.mpr hsum.le) hinv (by norm_num)

private def localUnitBallVolume : ℝ :=
  volume.real (Metric.ball (0 : R4) 1)

private theorem localUnitBallVolume_pos :
    0 < localUnitBallVolume :=
  ENNReal.toReal_pos
    (Metric.measure_ball_pos volume 0 one_pos).ne'
    measure_ball_lt_top.ne

private theorem finrank_R4_local :
    Module.finrank ℝ R4 = 4 := by
  rw [Module.finrank_pi]
  simp

private theorem radial4_local (g : ℝ → ℝ) :
    ∫ x : R4, g ‖x‖ ∂volume =
      4 * localUnitBallVolume *
        ∫ y in Ioi (0 : ℝ), y ^ (3 : ℕ) * g y := by
  have h := integral_fun_norm_addHaar
    (volume : Measure R4) g
  rw [finrank_R4_local] at h
  simpa [localUnitBallVolume, smul_eq_mul, mul_assoc] using h

private theorem cube_ball_rpow_neg_three
    (r : ℝ) (hr : 0 < r) :
    (∫ x in Metric.ball (0 : R4) r,
        ‖x‖ ^ (-(3 : ℝ)) ∂volume) =
      4 * localUnitBallVolume * r := by
  have hind :
      ∀ x : R4,
        (Iio r).indicator
            (fun y : ℝ => y ^ (-(3 : ℝ))) ‖x‖ =
          (Metric.ball (0 : R4) r).indicator
            (fun x : R4 => ‖x‖ ^ (-(3 : ℝ))) x := by
    intro x
    by_cases h : ‖x‖ < r
    · rw [Set.indicator_of_mem
          (show ‖x‖ ∈ Iio r from h),
        Set.indicator_of_mem
          (show x ∈ Metric.ball (0 : R4) r by
            simpa [Metric.mem_ball, dist_zero_right] using h)]
    · rw [Set.indicator_of_notMem
          (show ‖x‖ ∉ Iio r from h),
        Set.indicator_of_notMem
          (show x ∉ Metric.ball (0 : R4) r by
            simpa [Metric.mem_ball, dist_zero_right] using h)]
  have hrad :=
    radial4_local
      ((Iio r).indicator fun y : ℝ => y ^ (-(3 : ℝ)))
  have hleft :
      (∫ x : R4,
          (Iio r).indicator
            (fun y : ℝ => y ^ (-(3 : ℝ))) ‖x‖ ∂volume) =
        ∫ x in Metric.ball (0 : R4) r,
          ‖x‖ ^ (-(3 : ℝ)) ∂volume := by
    rw [← integral_indicator measurableSet_ball]
    exact integral_congr_ae (.of_forall hind)
  have hright :
      (∫ y in Ioi (0 : ℝ),
          y ^ (3 : ℕ) *
            (Iio r).indicator
              (fun y : ℝ => y ^ (-(3 : ℝ))) y) =
        ∫ y in Ioo (0 : ℝ) r, (1 : ℝ) := by
    have e :
        ∀ y : ℝ,
          y ^ (3 : ℕ) *
              (Iio r).indicator
                (fun y : ℝ => y ^ (-(3 : ℝ))) y =
            (Iio r).indicator
              (fun y : ℝ =>
                y ^ (3 : ℕ) * y ^ (-(3 : ℝ))) y := by
      intro y
      simp only [Set.indicator_apply]
      split <;> simp
    simp only [e]
    rw [setIntegral_indicator measurableSet_Iio,
      Set.Ioi_inter_Iio]
    refine
      setIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    rw [← Real.rpow_natCast y 3,
      ← Real.rpow_add hy.1]
    norm_num
  rw [hleft, hright] at hrad
  rw [hrad, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hr.le]
  have hone :
      (∫ _y : ℝ in (0 : ℝ)..r, (1 : ℝ)) = r := by
    simp
  rw [hone]

private theorem integrableOn_rpow_neg_three_ball (R : ℝ) :
    IntegrableOn (fun x : R4 => ‖x‖ ^ (-(3 : ℝ)))
      (Metric.ball (0 : R4) R) volume := by
  have hd : 1 ≤ Module.finrank ℝ R4 := by
    rw [finrank_R4_local]
    norm_num
  have hα : (3 : ℝ) < Module.finrank ℝ R4 := by
    rw [finrank_R4_local]
    norm_num
  exact integrableOn_ball_of_norm_le_rpow
    (C := 1) hd hα
    (.of_forall fun x => by
      rw [one_mul, Real.norm_eq_abs,
        abs_of_nonneg
          (Real.rpow_nonneg (norm_nonneg _) _)])
    (Measurable.aestronglyMeasurable (by fun_prop))

private theorem box_norm_le_local {x : R4}
    (hx : x ∈ localBoxIoc) :
    ‖x‖ ≤ Real.pi := by
  refine
    (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr fun i => ?_
  have hi := hx i (mem_univ i)
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨hi.1.le, hi.2⟩

private theorem localBox_subset_ball :
    localBoxIoc ⊆ Metric.ball (0 : R4) 5 := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  have hb := box_norm_le_local hx
  linarith [Real.pi_le_four]

/-- The `|z|⁻³` kernel is integrable on the torus. -/
theorem integrable_invSqKerThreeHalf :
    Integrable invSqKerThreeHalf paperMeasure := by
  have hcomp := measurePreserving_localMkT4.integrable_comp
    measurable_invSqKerThreeHalf.aestronglyMeasurable
  rw [← hcomp]
  refine Integrable.mono'
    (g := fun x : R4 => ‖x‖ ^ (-(3 : ℝ)))
    ((integrableOn_rpow_neg_three_ball 5).mono_set
      localBox_subset_ball)
    (measurable_invSqKerThreeHalf.comp
      measurable_localMkT4).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_localBox] with x hx
  change ‖invSqKerThreeHalf (localMkT4 x)‖ ≤ _
  rw [Real.norm_eq_abs,
    abs_of_nonneg (invSqKerThreeHalf_nonneg _)]
  exact invSqKerThreeHalf_localMkT4_le hx

theorem integrable_invSqKerThreeHalf_sub_left (x : T4) :
    Integrable (fun z => invSqKerThreeHalf (x - z))
      paperMeasure := by
  have heq :
      (fun z : T4 => invSqKerThreeHalf (x - z)) =
        fun z => invSqKerThreeHalf (z - x) := by
    funext z
    exact invSqKerThreeHalf_sub_comm x z
  rw [heq]
  exact
    ((measurePreserving_sub_paper x).integrable_comp
      measurable_invSqKerThreeHalf.aestronglyMeasurable).mpr
      integrable_invSqKerThreeHalf

theorem integrable_invSqKerThreeHalf_sub_right (x : T4) :
    Integrable (fun z => invSqKerThreeHalf (z - x))
      paperMeasure :=
  ((measurePreserving_sub_paper x).integrable_comp
    measurable_invSqKerThreeHalf.aestronglyMeasurable).mpr
    integrable_invSqKerThreeHalf

/-- Translation invariance of the total `|z|⁻³` mass. -/
theorem integral_invSqKerThreeHalf_sub_left (x : T4) :
    (∫ z, invSqKerThreeHalf (x - z) ∂paperMeasure) =
      ∫ z, invSqKerThreeHalf z ∂paperMeasure := by
  have heq :
      (fun z : T4 => invSqKerThreeHalf (x - z)) =
        fun z => invSqKerThreeHalf (z - x) := by
    funext z
    exact invSqKerThreeHalf_sub_comm x z
  rw [heq]
  have hmap := integral_map
    (μ := paperMeasure) (φ := fun z : T4 => z - x)
    (measurePreserving_sub_paper x).measurable.aemeasurable
    measurable_invSqKerThreeHalf.aestronglyMeasurable
  rw [(measurePreserving_sub_paper x).map_eq] at hmap
  exact hmap.symm

theorem integral_invSqKerThreeHalf_sub_right (x : T4) :
    (∫ z, invSqKerThreeHalf (z - x) ∂paperMeasure) =
      ∫ z, invSqKerThreeHalf z ∂paperMeasure := by
  have hmap := integral_map
    (μ := paperMeasure) (φ := fun z : T4 => z - x)
    (measurePreserving_sub_paper x).measurable.aemeasurable
    measurable_invSqKerThreeHalf.aestronglyMeasurable
  rw [(measurePreserving_sub_paper x).map_eq] at hmap
  exact hmap.symm

private theorem centered_invSqKerThreeHalf_indicator_le
    (s : ℝ) (hs : 0 < s) :
    (∫ z,
        ({z : T4 | ‖z‖ ≤ s}.indicator
          invSqKerThreeHalf) z ∂paperMeasure) ≤
      8 * localUnitBallVolume * s := by
  have hmeas :
      MeasurableSet {z : T4 | ‖z‖ ≤ s} :=
    measurable_norm measurableSet_Iic
  have hg :
      AEStronglyMeasurable
        ({z : T4 | ‖z‖ ≤ s}.indicator
          invSqKerThreeHalf) paperMeasure :=
    Measurable.aestronglyMeasurable
      (measurable_invSqKerThreeHalf.indicator hmeas)
  rw [local_torus_integral_eq_cube hg]
  let m : R4 → ℝ :=
    (Metric.ball (0 : R4) (2 * s)).indicator
      fun x => ‖x‖ ^ (-(3 : ℝ))
  have hmnn : ∀ x, 0 ≤ m x :=
    fun x =>
      Set.indicator_nonneg
        (fun y _ =>
          Real.rpow_nonneg (norm_nonneg y) _) x
  have hmi : Integrable m volume := by
    dsimp [m]
    rw [integrable_indicator_iff measurableSet_ball]
    exact integrableOn_rpow_neg_three_ball _
  have hcube :
      (∫ x in localBoxIoc,
          ({z : T4 | ‖z‖ ≤ s}.indicator
            invSqKerThreeHalf) (localMkT4 x) ∂volume) ≤
        ∫ x in localBoxIoc, m x ∂volume := by
    refine integral_mono_of_nonneg
      (.of_forall fun x =>
        Set.indicator_nonneg
          (fun z _ => invSqKerThreeHalf_nonneg z)
          (localMkT4 x))
      hmi.restrict ?_
    filter_upwards [ae_localBox] with x hx
    by_cases hmem :
        localMkT4 x ∈ {z : T4 | ‖z‖ ≤ s}
    · rw [Set.indicator_of_mem hmem]
      have hball :
          x ∈ Metric.ball (0 : R4) (2 * s) := by
        rw [Metric.mem_ball, dist_zero_right,
          ← norm_localMkT4 hx]
        exact lt_of_le_of_lt hmem (by linarith)
      rw [show m x = ‖x‖ ^ (-(3 : ℝ)) by
        dsimp [m]
        rw [Set.indicator_of_mem hball]]
      exact invSqKerThreeHalf_localMkT4_le hx
    · rw [Set.indicator_of_notMem hmem]
      exact hmnn x
  refine hcube.trans ?_
  calc
    (∫ x in localBoxIoc, m x ∂volume)
        ≤ ∫ x, m x ∂volume :=
      setIntegral_le_integral hmi (.of_forall hmnn)
    _ = 4 * localUnitBallVolume * (2 * s) := by
      dsimp [m]
      rw [integral_indicator measurableSet_ball]
      exact cube_ball_rpow_neg_three _ (by positivity)
    _ = 8 * localUnitBallVolume * s := by ring

/-- **Uniform local `|z|⁻³` mass.**  A radius-`r` torus ball
about the singularity has mass `O(r)`, uniformly in its centre. -/
theorem invSqKerThreeHalf_ball_sub_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x : T4) (r : ℝ), 0 < r →
        (∫ z in Metric.ball x r,
          invSqKerThreeHalf (x - z) ∂paperMeasure) ≤ C * r := by
  refine
    ⟨8 * localUnitBallVolume,
      by have := localUnitBallVolume_pos; positivity,
      fun x r hr => ?_⟩
  let F : T4 → ℝ :=
    {w : T4 | ‖w‖ ≤ r}.indicator invSqKerThreeHalf
  have hFmeas : Measurable F :=
    measurable_invSqKerThreeHalf.indicator
      (measurable_norm measurableSet_Iic)
  have hshift :
      (∫ z, F (z - x) ∂paperMeasure) =
        ∫ z, F z ∂paperMeasure := by
    have hmap := integral_map
      (μ := paperMeasure) (φ := fun z : T4 => z - x)
      (measurePreserving_sub_paper x).measurable.aemeasurable
      hFmeas.aestronglyMeasurable
    rw [(measurePreserving_sub_paper x).map_eq] at hmap
    exact hmap.symm
  have hFint :
      Integrable F paperMeasure :=
    integrable_invSqKerThreeHalf.indicator
      (measurable_norm measurableSet_Iic)
  have hFshiftInt :
      Integrable (fun z => F (z - x)) paperMeasure :=
    ((measurePreserving_sub_paper x).integrable_comp
      hFmeas.aestronglyMeasurable).mpr hFint
  have hdom :
      (∫ z in Metric.ball x r,
          invSqKerThreeHalf (x - z) ∂paperMeasure) ≤
        ∫ z, F (z - x) ∂paperMeasure := by
    rw [← integral_indicator measurableSet_ball]
    exact integral_mono_of_nonneg
      (.of_forall fun z =>
        Set.indicator_nonneg
          (fun w _ => invSqKerThreeHalf_nonneg (x - w)) z)
      hFshiftInt
      (.of_forall fun z => by
        by_cases hz : z ∈ Metric.ball x r
        · rw [Set.indicator_of_mem hz]
          have hnorm : ‖z - x‖ ≤ r := by
            rw [Metric.mem_ball] at hz
            simpa [dist_eq_norm] using hz.le
          have hmem :
              z - x ∈ {w : T4 | ‖w‖ ≤ r} :=
            hnorm
          change
            invSqKerThreeHalf (x - z) ≤ F (z - x)
          rw [show F (z - x) =
              invSqKerThreeHalf (z - x) by
            dsimp [F]
            rw [Set.indicator_of_mem hmem],
            invSqKerThreeHalf_sub_comm]
        · rw [Set.indicator_of_notMem hz]
          change 0 ≤ F (z - x)
          dsimp [F]
          exact Set.indicator_nonneg
            (fun w _ => invSqKerThreeHalf_nonneg w) _)
  calc
    (∫ z in Metric.ball x r,
        invSqKerThreeHalf (x - z) ∂paperMeasure)
        ≤ ∫ z, F (z - x) ∂paperMeasure := hdom
    _ = ∫ z, F z ∂paperMeasure := hshift
    _ ≤ 8 * localUnitBallVolume * r :=
      centered_invSqKerThreeHalf_indicator_le r hr

/-! ## Pointwise AM--GM and cell geometry -/

private theorem mul_three_le_pair_threeHalves
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤
      a ^ (3 / 2 : ℝ) * b ^ (3 / 2 : ℝ) +
      b ^ (3 / 2 : ℝ) * c ^ (3 / 2 : ℝ) +
      a ^ (3 / 2 : ℝ) * c ^ (3 / 2 : ℝ) := by
  have hab := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (1 / 3 : ℝ)) (w₂ := (1 / 3 : ℝ))
    (w₃ := (1 / 3 : ℝ))
    (p₁ := (a * b) ^ (3 / 2 : ℝ))
    (p₂ := (b * c) ^ (3 / 2 : ℝ))
    (p₃ := (a * c) ^ (3 / 2 : ℝ))
    (by positivity) (by positivity) (by positivity)
    (Real.rpow_nonneg (mul_nonneg ha hb) _)
    (Real.rpow_nonneg (mul_nonneg hb hc) _)
    (Real.rpow_nonneg (mul_nonneg ha hc) _)
    (by norm_num)
  have hleft :
      ((a * b) ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) *
          ((b * c) ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) *
          ((a * c) ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) =
        a * b * c := by
    rw [← Real.rpow_mul (mul_nonneg ha hb),
      ← Real.rpow_mul (mul_nonneg hb hc),
      ← Real.rpow_mul (mul_nonneg ha hc)]
    norm_num
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow]
    rw [Real.sqrt_mul ha, Real.sqrt_mul hb,
      Real.sqrt_mul ha]
    calc
      (√a * √b) * (√b * √c) * (√a * √c) =
          (√a) ^ 2 * (√b) ^ 2 * (√c) ^ 2 := by ring
      _ = a * b * c := by
        rw [Real.sq_sqrt ha, Real.sq_sqrt hb,
          Real.sq_sqrt hc]
  rw [hleft] at hab
  have hpair₁ :
      (a * b) ^ (3 / 2 : ℝ) =
        a ^ (3 / 2 : ℝ) * b ^ (3 / 2 : ℝ) :=
    Real.mul_rpow ha hb
  have hpair₂ :
      (b * c) ^ (3 / 2 : ℝ) =
        b ^ (3 / 2 : ℝ) * c ^ (3 / 2 : ℝ) :=
    Real.mul_rpow hb hc
  have hpair₃ :
      (a * c) ^ (3 / 2 : ℝ) =
        a ^ (3 / 2 : ℝ) * c ^ (3 / 2 : ℝ) :=
    Real.mul_rpow ha hc
  rw [hpair₁, hpair₂, hpair₃] at hab
  have hsum :
      0 ≤
        a ^ (3 / 2 : ℝ) * b ^ (3 / 2 : ℝ) +
        b ^ (3 / 2 : ℝ) * c ^ (3 / 2 : ℝ) +
        a ^ (3 / 2 : ℝ) * c ^ (3 / 2 : ℝ) := by
    positivity
  nlinarith

theorem invSqKer_triple_le_threeHalf_pairs
    (u v w : T4) :
    invSqKer u * invSqKer v * invSqKer w ≤
      invSqKerThreeHalf u * invSqKerThreeHalf v +
      invSqKerThreeHalf v * invSqKerThreeHalf w +
      invSqKerThreeHalf u * invSqKerThreeHalf w := by
  exact mul_three_le_pair_threeHalves
    (invSqKer_nonneg u) (invSqKer_nonneg v)
    (invSqKer_nonneg w)

private theorem ball_subset_ball_of_near
    {a b z : T4} {r A : ℝ}
    (hz : z ∈ Metric.ball b r)
    (hab : dist a b ≤ A * r) :
    z ∈ Metric.ball a ((A + 1) * r) := by
  rw [Metric.mem_ball] at hz ⊢
  calc
    dist z a ≤ dist z b + dist b a := dist_triangle _ _ _
    _ = dist z b + dist a b := by rw [dist_comm b a]
    _ < (A + 1) * r := by linarith

private theorem setIntegral_invSqKerThreeHalf_ball_le
    {x c : T4} {r : ℝ} (hr : 0 < r)
    (hxc : dist x c ≤ 5 * r)
    {C : ℝ}
    (hlocal : ∀ (a : T4) (s : ℝ), 0 < s →
      (∫ z in Metric.ball a s,
        invSqKerThreeHalf (a - z) ∂paperMeasure) ≤ C * s) :
    (∫ z in Metric.ball c r,
        invSqKerThreeHalf (x - z) ∂paperMeasure) ≤
      C * (6 * r) := by
  have hsubset :
      Metric.ball c r ⊆ Metric.ball x (6 * r) := by
    intro z hz
    have := ball_subset_ball_of_near
      (a := x) (b := c) (A := 5) hz hxc
    norm_num at this ⊢
    exact this
  calc
    (∫ z in Metric.ball c r,
        invSqKerThreeHalf (x - z) ∂paperMeasure)
        ≤ ∫ z in Metric.ball x (6 * r),
            invSqKerThreeHalf (x - z) ∂paperMeasure :=
      setIntegral_mono_set
        ((integrable_invSqKerThreeHalf_sub_left x).integrableOn)
        (.of_forall fun z => invSqKerThreeHalf_nonneg _)
        (.of_forall hsubset)
    _ ≤ C * (6 * r) := hlocal x (6 * r) (by positivity)

/-! ## Closure of the all-near predicate -/

/-- The local three-edge cell convolution has the sharp `O(r²)` scale
whenever its four consecutive cell centres are `4r`-near. -/
theorem localTripleCellIntegral_le_scale :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r : ℝ), 0 < r →
      ∀ (c₀ c₁ c₂ c₃ x y : T4),
        x ∈ Metric.ball c₀ r →
        y ∈ Metric.ball c₃ r →
        dist c₀ c₁ ≤ 4 * r →
        dist c₁ c₂ ≤ 4 * r →
        dist c₂ c₃ ≤ 4 * r →
        localTripleCellIntegral r c₁ c₂ x y ≤
          C * r ^ 2 := by
  obtain ⟨C₁, hC₁, hlocal⟩ :=
    invSqKerThreeHalf_ball_sub_le
  refine ⟨108 * C₁ ^ 2, by positivity, ?_⟩
  intro r hr c₀ c₁ c₂ c₃ x y hx hy h01 h12 h23
  have hxc₁ : dist x c₁ ≤ 5 * r := by
    have hx' : dist x c₀ < r := by
      simpa only [Metric.mem_ball] using hx
    calc
      dist x c₁ ≤ dist x c₀ + dist c₀ c₁ :=
        dist_triangle _ _ _
      _ ≤ 5 * r := by linarith [hx']
  have hyc₂ : dist y c₂ ≤ 5 * r := by
    have hy' : dist y c₃ < r := by
      simpa only [Metric.mem_ball] using hy
    calc
      dist y c₂ ≤ dist y c₃ + dist c₃ c₂ :=
        dist_triangle _ _ _
      _ ≤ 5 * r := by
        rw [dist_comm c₃ c₂]
        linarith [hy']
  have hxmass :
      (∫ z in Metric.ball c₁ r,
          invSqKerThreeHalf (x - z) ∂paperMeasure) ≤
        C₁ * (6 * r) :=
    setIntegral_invSqKerThreeHalf_ball_le hr hxc₁ hlocal
  have hymass :
      (∫ z in Metric.ball c₂ r,
          invSqKerThreeHalf (y - z) ∂paperMeasure) ≤
        C₁ * (6 * r) :=
    setIntegral_invSqKerThreeHalf_ball_le hr hyc₂ hlocal
  have hmiddle :
      ∀ z₁ ∈ Metric.ball c₁ r,
        (∫ z₂ in Metric.ball c₂ r,
            invSqKerThreeHalf (z₁ - z₂) ∂paperMeasure) ≤
          C₁ * (6 * r) := by
    intro z₁ hz₁
    have hz₁c₂ : dist z₁ c₂ ≤ 5 * r := by
      have hz₁' : dist z₁ c₁ < r := by
        simpa only [Metric.mem_ball] using hz₁
      calc
        dist z₁ c₂ ≤ dist z₁ c₁ + dist c₁ c₂ :=
          dist_triangle _ _ _
        _ ≤ 5 * r := by linarith [hz₁']
    exact
      setIntegral_invSqKerThreeHalf_ball_le
        hr hz₁c₂ hlocal
  let K : ℝ := C₁ * (6 * r)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hxmassK :
      (∫ z in Metric.ball c₁ r,
          invSqKerThreeHalf (x - z) ∂paperMeasure) ≤ K :=
    hxmass
  have hymassRightK :
      (∫ z in Metric.ball c₂ r,
          invSqKerThreeHalf (z - y) ∂paperMeasure) ≤ K := by
    calc
      (∫ z in Metric.ball c₂ r,
          invSqKerThreeHalf (z - y) ∂paperMeasure) =
          ∫ z in Metric.ball c₂ r,
            invSqKerThreeHalf (y - z) ∂paperMeasure := by
        apply integral_congr_ae
        exact .of_forall fun z =>
          invSqKerThreeHalf_sub_comm z y
      _ ≤ K := hymass
  have hmiddleK :
      ∀ z₁ ∈ Metric.ball c₁ r,
        (∫ z₂ in Metric.ball c₂ r,
            invSqKerThreeHalf (z₁ - z₂) ∂paperMeasure) ≤ K :=
    hmiddle
  have hmiddleSwapK :
      ∀ z₂ ∈ Metric.ball c₂ r,
        (∫ z₁ in Metric.ball c₁ r,
            invSqKerThreeHalf (z₁ - z₂) ∂paperMeasure) ≤ K := by
    intro z₂ hz₂
    have hz₂' : dist z₂ c₂ < r := by
      simpa only [Metric.mem_ball] using hz₂
    have hz₂c₁ : dist z₂ c₁ ≤ 5 * r := by
      calc
        dist z₂ c₁ ≤ dist z₂ c₂ + dist c₂ c₁ :=
          dist_triangle _ _ _
        _ ≤ 5 * r := by
          rw [dist_comm c₂ c₁]
          linarith [hz₂']
    have hlocal' :=
      setIntegral_invSqKerThreeHalf_ball_le
        (x := z₂) (c := c₁) hr hz₂c₁ hlocal
    calc
      (∫ z₁ in Metric.ball c₁ r,
          invSqKerThreeHalf (z₁ - z₂) ∂paperMeasure) =
          ∫ z₁ in Metric.ball c₁ r,
            invSqKerThreeHalf (z₂ - z₁) ∂paperMeasure := by
        apply integral_congr_ae
        exact .of_forall fun z₁ =>
          invSqKerThreeHalf_sub_comm z₁ z₂
      _ ≤ K := hlocal'
  let fB : T4 → T4 → ℝ :=
    fun z₁ z₂ =>
      invSqKerThreeHalf (z₁ - z₂) *
        invSqKerThreeHalf (z₂ - y)
  have hfBmeas :
      AEStronglyMeasurable (Function.uncurry fB)
        (paperMeasure.prod paperMeasure) := by
    apply Measurable.aestronglyMeasurable
    exact
      (measurable_invSqKerThreeHalf.comp
          (measurable_fst.sub measurable_snd)).mul
        (measurable_invSqKerThreeHalf.comp
          (measurable_snd.sub measurable_const))
  let M : ℝ :=
    ∫ z, invSqKerThreeHalf z ∂paperMeasure
  have hM : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg invSqKerThreeHalf_nonneg
  have hfBfull :
      Integrable (Function.uncurry fB)
        (paperMeasure.prod paperMeasure) := by
    rw [integrable_prod_iff' hfBmeas]
    constructor
    · exact .of_forall fun z₂ => by
        dsimp [fB, Function.uncurry]
        exact
          (integrable_invSqKerThreeHalf_sub_right z₂).mul_const
            (invSqKerThreeHalf (z₂ - y))
    · have heq :
          (fun z₂ : T4 =>
            ∫ z₁,
              ‖Function.uncurry fB (z₁, z₂)‖
                ∂paperMeasure) =
            fun z₂ => M * invSqKerThreeHalf (z₂ - y) := by
        funext z₂
        have hpoint :
            (fun z₁ : T4 =>
              ‖Function.uncurry fB (z₁, z₂)‖) =
              fun z₁ =>
                invSqKerThreeHalf (z₁ - z₂) *
                  invSqKerThreeHalf (z₂ - y) := by
          funext z₁
          dsimp [fB, Function.uncurry]
          rw [abs_of_nonneg
            (mul_nonneg (invSqKerThreeHalf_nonneg _)
              (invSqKerThreeHalf_nonneg _))]
        rw [hpoint, integral_mul_const,
          integral_invSqKerThreeHalf_sub_right]
      rw [heq]
      exact
        (integrable_invSqKerThreeHalf_sub_right y).const_mul M
  have hfB :
      Integrable (Function.uncurry fB)
        ((paperMeasure.restrict (Metric.ball c₁ r)).prod
          (paperMeasure.restrict (Metric.ball c₂ r))) :=
    hfBfull.mono_measure
      (Measure.prod_mono Measure.restrict_le_self
        Measure.restrict_le_self)
  have hfBouter :
      Integrable
        (fun z₁ =>
          ∫ z₂ in Metric.ball c₂ r, fB z₁ z₂
            ∂paperMeasure)
        (paperMeasure.restrict (Metric.ball c₁ r)) := by
    exact hfB.integral_prod_left
  have hBswap :
      (∫ z₁ in Metric.ball c₁ r,
          ∫ z₂ in Metric.ball c₂ r, fB z₁ z₂
            ∂paperMeasure ∂paperMeasure) =
        ∫ z₂ in Metric.ball c₂ r,
          ∫ z₁ in Metric.ball c₁ r, fB z₁ z₂
            ∂paperMeasure ∂paperMeasure :=
    integral_integral_swap hfB
  have hnonnegInner :
      ∀ z₁ : T4, 0 ≤
        ∫ z₂ in Metric.ball c₂ r,
          invSqKer (x - z₁) *
            invSqKer (z₁ - z₂) *
            invSqKer (z₂ - y) ∂paperMeasure :=
    fun z₁ => integral_nonneg fun z₂ =>
      mul_nonneg
        (mul_nonneg (invSqKer_nonneg _)
          (invSqKer_nonneg _))
        (invSqKer_nonneg _)
  have hqxInt :
      Integrable (fun z₁ => invSqKerThreeHalf (x - z₁))
        (paperMeasure.restrict (Metric.ball c₁ r)) :=
    (integrable_invSqKerThreeHalf_sub_left x).mono_measure
      Measure.restrict_le_self
  have hGint :
      Integrable
        (fun z₁ =>
          2 * K * invSqKerThreeHalf (x - z₁) +
            ∫ z₂ in Metric.ball c₂ r, fB z₁ z₂
              ∂paperMeasure)
        (paperMeasure.restrict (Metric.ball c₁ r)) :=
    (hqxInt.const_mul (2 * K)).add hfBouter
  have hinner :
      ∀ᵐ z₁ ∂paperMeasure.restrict (Metric.ball c₁ r),
        (∫ z₂ in Metric.ball c₂ r,
          invSqKer (x - z₁) *
            invSqKer (z₁ - z₂) *
            invSqKer (z₂ - y) ∂paperMeasure) ≤
          2 * K * invSqKerThreeHalf (x - z₁) +
            ∫ z₂ in Metric.ball c₂ r, fB z₁ z₂
              ∂paperMeasure := by
    filter_upwards
      [ae_restrict_mem measurableSet_ball,
        hfB.prod_right_ae] with z₁ hz₁ hfBz₁
    have hmidInt :
        Integrable
          (fun z₂ => invSqKerThreeHalf (z₁ - z₂))
          (paperMeasure.restrict (Metric.ball c₂ r)) :=
      (integrable_invSqKerThreeHalf_sub_left z₁).mono_measure
        Measure.restrict_le_self
    have hyInt :
        Integrable
          (fun z₂ => invSqKerThreeHalf (z₂ - y))
          (paperMeasure.restrict (Metric.ball c₂ r)) :=
      (integrable_invSqKerThreeHalf_sub_right y).mono_measure
        Measure.restrict_le_self
    have hAInt :
        Integrable
          (fun z₂ =>
            invSqKerThreeHalf (x - z₁) *
              invSqKerThreeHalf (z₁ - z₂))
          (paperMeasure.restrict (Metric.ball c₂ r)) :=
      hmidInt.const_mul _
    have hfBz₁' :
        Integrable (fun z₂ => fB z₁ z₂)
          (paperMeasure.restrict (Metric.ball c₂ r)) := by
      simpa only [Function.uncurry_apply_pair] using hfBz₁
    have hCInt :
        Integrable
          (fun z₂ =>
            invSqKerThreeHalf (x - z₁) *
              invSqKerThreeHalf (z₂ - y))
          (paperMeasure.restrict (Metric.ball c₂ r)) :=
      hyInt.const_mul _
    have hsumIntegral :
        (∫ z₂ in Metric.ball c₂ r,
          (invSqKerThreeHalf (x - z₁) *
              invSqKerThreeHalf (z₁ - z₂) +
            fB z₁ z₂ +
            invSqKerThreeHalf (x - z₁) *
              invSqKerThreeHalf (z₂ - y))
            ∂paperMeasure) =
          (∫ z₂ in Metric.ball c₂ r,
            invSqKerThreeHalf (x - z₁) *
              invSqKerThreeHalf (z₁ - z₂)
                ∂paperMeasure) +
          (∫ z₂ in Metric.ball c₂ r, fB z₁ z₂
            ∂paperMeasure) +
          (∫ z₂ in Metric.ball c₂ r,
            invSqKerThreeHalf (x - z₁) *
              invSqKerThreeHalf (z₂ - y)
                ∂paperMeasure) := by
      have hAB :=
        integral_add hAInt hfBz₁'
      have hABC :=
        integral_add (hAInt.add hfBz₁') hCInt
      calc
        _ =
            (∫ z₂ in Metric.ball c₂ r,
              (invSqKerThreeHalf (x - z₁) *
                  invSqKerThreeHalf (z₁ - z₂) +
                fB z₁ z₂) ∂paperMeasure) +
            (∫ z₂ in Metric.ball c₂ r,
              invSqKerThreeHalf (x - z₁) *
                invSqKerThreeHalf (z₂ - y)
                  ∂paperMeasure) := by
          simpa only [Pi.add_apply] using hABC
        _ = _ := by
          rw [show
            (∫ z₂ in Metric.ball c₂ r,
              (invSqKerThreeHalf (x - z₁) *
                  invSqKerThreeHalf (z₁ - z₂) +
                fB z₁ z₂) ∂paperMeasure) =
              (∫ z₂ in Metric.ball c₂ r,
                invSqKerThreeHalf (x - z₁) *
                  invSqKerThreeHalf (z₁ - z₂)
                    ∂paperMeasure) +
              (∫ z₂ in Metric.ball c₂ r,
                fB z₁ z₂ ∂paperMeasure) by
              simpa only [Pi.add_apply] using hAB]
    have hAIntegral :
        (∫ z₂ in Metric.ball c₂ r,
          invSqKerThreeHalf (x - z₁) *
            invSqKerThreeHalf (z₁ - z₂)
              ∂paperMeasure) =
          invSqKerThreeHalf (x - z₁) *
            (∫ z₂ in Metric.ball c₂ r,
              invSqKerThreeHalf (z₁ - z₂)
                ∂paperMeasure) := by
      rw [integral_const_mul]
    have hCIntegral :
        (∫ z₂ in Metric.ball c₂ r,
          invSqKerThreeHalf (x - z₁) *
            invSqKerThreeHalf (z₂ - y)
              ∂paperMeasure) =
          invSqKerThreeHalf (x - z₁) *
            (∫ z₂ in Metric.ball c₂ r,
              invSqKerThreeHalf (z₂ - y)
                ∂paperMeasure) := by
      rw [integral_const_mul]
    have hmono :
        (∫ z₂ in Metric.ball c₂ r,
          invSqKer (x - z₁) *
            invSqKer (z₁ - z₂) *
            invSqKer (z₂ - y) ∂paperMeasure) ≤
          ∫ z₂ in Metric.ball c₂ r,
            (invSqKerThreeHalf (x - z₁) *
                invSqKerThreeHalf (z₁ - z₂) +
              fB z₁ z₂ +
              invSqKerThreeHalf (x - z₁) *
                invSqKerThreeHalf (z₂ - y))
              ∂paperMeasure := by
      exact integral_mono_of_nonneg
        (.of_forall fun z₂ =>
          mul_nonneg
            (mul_nonneg (invSqKer_nonneg _)
              (invSqKer_nonneg _))
            (invSqKer_nonneg _))
        ((hAInt.add hfBz₁').add hCInt)
        (.of_forall fun z₂ => by
          dsimp [fB]
          exact invSqKer_triple_le_threeHalf_pairs
            (x - z₁) (z₁ - z₂) (z₂ - y))
    calc
      (∫ z₂ in Metric.ball c₂ r,
          invSqKer (x - z₁) *
            invSqKer (z₁ - z₂) *
            invSqKer (z₂ - y) ∂paperMeasure)
          ≤ ∫ z₂ in Metric.ball c₂ r,
              (invSqKerThreeHalf (x - z₁) *
                  invSqKerThreeHalf (z₁ - z₂) +
                fB z₁ z₂ +
                invSqKerThreeHalf (x - z₁) *
                  invSqKerThreeHalf (z₂ - y))
                ∂paperMeasure := hmono
      _ =
          invSqKerThreeHalf (x - z₁) *
              (∫ z₂ in Metric.ball c₂ r,
                invSqKerThreeHalf (z₁ - z₂)
                  ∂paperMeasure) +
            (∫ z₂ in Metric.ball c₂ r, fB z₁ z₂
              ∂paperMeasure) +
            invSqKerThreeHalf (x - z₁) *
              (∫ z₂ in Metric.ball c₂ r,
                invSqKerThreeHalf (z₂ - y)
                  ∂paperMeasure) := by
        rw [hsumIntegral, hAIntegral, hCIntegral]
      _ ≤
          invSqKerThreeHalf (x - z₁) * K +
            (∫ z₂ in Metric.ball c₂ r, fB z₁ z₂
              ∂paperMeasure) +
            invSqKerThreeHalf (x - z₁) * K := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left
              (hmiddleK z₁ hz₁)
              (invSqKerThreeHalf_nonneg _))
            le_rfl)
          (mul_le_mul_of_nonneg_left hymassRightK
            (invSqKerThreeHalf_nonneg _))
      _ =
          2 * K * invSqKerThreeHalf (x - z₁) +
            ∫ z₂ in Metric.ball c₂ r, fB z₁ z₂
              ∂paperMeasure := by ring
  have hBnonneg :
      ∀ z₁ z₂, 0 ≤ fB z₁ z₂ := by
    intro z₁ z₂
    dsimp [fB]
    exact mul_nonneg (invSqKerThreeHalf_nonneg _)
      (invSqKerThreeHalf_nonneg _)
  have hBbound :
      (∫ z₁ in Metric.ball c₁ r,
          ∫ z₂ in Metric.ball c₂ r, fB z₁ z₂
            ∂paperMeasure ∂paperMeasure) ≤ K * K := by
    rw [hBswap]
    calc
      (∫ z₂ in Metric.ball c₂ r,
          ∫ z₁ in Metric.ball c₁ r, fB z₁ z₂
            ∂paperMeasure ∂paperMeasure)
          ≤ ∫ z₂ in Metric.ball c₂ r,
              K * invSqKerThreeHalf (z₂ - y)
                ∂paperMeasure := by
        exact integral_mono_of_nonneg
          (.of_forall fun z₂ =>
            integral_nonneg fun z₁ => hBnonneg z₁ z₂)
          (Integrable.mono_measure
            ((integrable_invSqKerThreeHalf_sub_right y).const_mul K)
            Measure.restrict_le_self)
          (by
            filter_upwards [ae_restrict_mem measurableSet_ball]
              with z₂ hz₂
            have hinnerEq :
                (∫ z₁ in Metric.ball c₁ r, fB z₁ z₂
                  ∂paperMeasure) =
                  (∫ z₁ in Metric.ball c₁ r,
                    invSqKerThreeHalf (z₁ - z₂)
                      ∂paperMeasure) *
                    invSqKerThreeHalf (z₂ - y) := by
              dsimp [fB]
              rw [integral_mul_const]
            rw [hinnerEq]
            calc
              (∫ z₁ in Metric.ball c₁ r,
                  invSqKerThreeHalf (z₁ - z₂)
                    ∂paperMeasure) *
                    invSqKerThreeHalf (z₂ - y)
                  ≤ K * invSqKerThreeHalf (z₂ - y) :=
                mul_le_mul_of_nonneg_right
                  (hmiddleSwapK z₂ hz₂)
                  (invSqKerThreeHalf_nonneg _))
      _ = K * (∫ z₂ in Metric.ball c₂ r,
            invSqKerThreeHalf (z₂ - y)
              ∂paperMeasure) := by
        rw [integral_const_mul]
      _ ≤ K * K :=
        mul_le_mul_of_nonneg_left hymassRightK hK
  unfold localTripleCellIntegral
  calc
    (∫ z₁ in Metric.ball c₁ r,
        ∫ z₂ in Metric.ball c₂ r,
          invSqKer (x - z₁) *
            invSqKer (z₁ - z₂) *
            invSqKer (z₂ - y)
          ∂paperMeasure ∂paperMeasure)
        ≤ ∫ z₁ in Metric.ball c₁ r,
            (2 * K * invSqKerThreeHalf (x - z₁) +
              ∫ z₂ in Metric.ball c₂ r, fB z₁ z₂
                ∂paperMeasure) ∂paperMeasure :=
      integral_mono_of_nonneg
        (.of_forall hnonnegInner) hGint hinner
    _ =
        2 * K *
            (∫ z₁ in Metric.ball c₁ r,
              invSqKerThreeHalf (x - z₁)
                ∂paperMeasure) +
          (∫ z₁ in Metric.ball c₁ r,
            ∫ z₂ in Metric.ball c₂ r, fB z₁ z₂
              ∂paperMeasure ∂paperMeasure) := by
      rw [integral_add
        ((hqxInt.const_mul (2 * K))) hfBouter,
        integral_const_mul]
    _ ≤ 2 * K * K + K * K := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hxmassK (by positivity))
        hBbound
    _ = 3 * (C₁ * (6 * r)) ^ 2 := by
      dsimp [K]
      ring
    _ = (108 * C₁ ^ 2) * r ^ 2 := by ring

/-- The isolated analytic predicate from `CellSingular.lean` is true. -/
theorem localTripleCellScaleBound :
    LocalTripleCellScaleBound :=
  localTripleCellIntegral_le_scale

end

end Anderson4D
