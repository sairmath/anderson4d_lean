import Anderson4D.DetParametrix.Paper41_Renorm.R322RegionThreeProfile
import Anderson4D.Continuum.FourPointFourier

/-!
# The analytic one-block estimate in R-322

This file connects the three explicit profile estimates (4.10)--(4.12)
to the Green difference which occurs in one proper-block collapse.
The Taylor region uses class-`E` cancellation.  On its complement the
free Green function is split into the two crude regions of the paper.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set

/-- The Green difference after the inner change of variables
`u = z - w`. -/
def r322GreenDifferenceSection
    (J : T4 → ℝ) (q : T4) : ℝ :=
  ∫ u, J u * (greenFn (q - u) - greenFn q) ∂paperMeasure

/-- The complement of the Taylor region in the inner Green difference. -/
def r322CrudeSectionIntegrand
    (J : T4 → ℝ) (q u : T4) : ℝ :=
  if 2 * ‖u‖ ≤ ‖q‖ then 0
  else J u * (greenFn (q - u) - greenFn q)

/-- The positive majorant supplied by the two crude regions
(4.11)--(4.12). -/
def r322CrudeSectionMajorant
    (greenConstant : ℝ) (P : T4 → ℝ) (q u : T4) : ℝ :=
  37 * greenConstant * invSqKer q *
      reductionRegionTwoKernel q P u +
    greenConstant * reductionRegionThreeKernel q P u

theorem measurable_r322CrudeSectionIntegrand
    {J : T4 → ℝ} (hJ : Measurable J) (q : T4) :
    Measurable (r322CrudeSectionIntegrand J q) := by
  unfold r322CrudeSectionIntegrand
  exact Measurable.ite
    (measurableSet_le
      (measurable_const.mul measurable_norm)
      measurable_const)
    measurable_const
    (hJ.mul
      ((measurable_greenFn.comp
        (measurable_const.sub measurable_id)).sub
          (measurable_greenFn.comp measurable_const)))

theorem measurable_r322CrudeSectionMajorant
    {P : T4 → ℝ} (hP : Measurable P)
    (greenConstant : ℝ) (q : T4) :
    Measurable (r322CrudeSectionMajorant greenConstant P q) := by
  unfold r322CrudeSectionMajorant
  exact
    ((measurable_const.mul
      (measurable_reductionRegionTwoKernel q hP)).add
      (measurable_const.mul
        (measurable_reductionRegionThreeKernel q hP)))

theorem measurable_reductionRegionOneKernel
    (q : T4) {J : T4 → ℝ} (hJ : Measurable J) :
    Measurable (reductionRegionOneKernel q J) := by
  unfold reductionRegionOneKernel
  exact Measurable.ite
    (measurableSet_le
      (measurable_const.mul measurable_norm)
      measurable_const)
    hJ measurable_const

theorem measurable_r322GreenRemainder (q : T4) :
    Measurable (r322GreenRemainder q) := by
  unfold r322GreenRemainder torusLinearTerm
  exact
    ((measurable_greenFn.comp measurable_const).sub
      (measurable_greenFn.comp
        (measurable_const.sub measurable_id))).sub
      ((greenGradientCLM (torusLift q)).continuous.measurable.comp
        measurable_torusLift)

theorem torusLinearTerm_eq_sum_r322OneBlock
    (D : R4 →L[ℝ] ℝ) (u : T4) :
    torusLinearTerm D u =
      ∑ i : Fin dim,
        torusLift u i * D (Pi.single i 1) := by
  classical
  have hlift :
      torusLift u =
        ∑ i : Fin dim,
          (torusLift u i) • Pi.single i (1 : ℝ) :=
    pi_eq_sum_univ' (torusLift u)
  calc
    torusLinearTerm D u = D (torusLift u) := rfl
    _ = D (∑ i : Fin dim,
        (torusLift u i) • Pi.single i (1 : ℝ)) := by
      exact congrArg D hlift
    _ = ∑ i : Fin dim,
        D ((torusLift u i) • Pi.single i (1 : ℝ)) :=
      map_sum D _ _
    _ = ∑ i : Fin dim,
        torusLift u i * D (Pi.single i 1) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [map_smul]
      simp [smul_eq_mul]

/-- Outside the Taylor region, `q` lies in the first crude region. -/
theorem reductionRegionTwo_of_not_regionOne
    {q u : T4} (hregion : ¬ 2 * ‖u‖ ≤ ‖q‖) :
    ‖q‖ ≤ 2 * ‖u‖ :=
  le_of_lt (lt_of_not_ge hregion)

/-- In the overlap complement of the last crude region, the singular
point `q-u` controls `q` with the numerical constant used in (4.11). -/
theorem torusDistSq_le_thirtySix_mul_of_crude_regions
    {q u : T4}
    (hregionThree : ¬ 2 * ‖q - u‖ ≤ ‖u‖) :
    torusDistSq q ≤ 36 * torusDistSq (q - u) := by
  have hu : ‖u‖ < 2 * ‖q - u‖ :=
    lt_of_not_ge hregionThree
  have hq :
      ‖q‖ ≤ ‖q - u‖ + ‖u‖ := by
    simpa only [sub_add_cancel] using
      (norm_add_le (q - u) u)
  have hqv : ‖q‖ ≤ 3 * ‖q - u‖ := by
    linarith
  calc
    torusDistSq q ≤ 4 * ‖q‖ ^ 2 :=
      torusDistSq_le_four_mul_sq_norm q
    _ ≤ 36 * ‖q - u‖ ^ 2 := by
      nlinarith [norm_nonneg q, norm_nonneg (q - u)]
    _ ≤ 36 * torusDistSq (q - u) := by
      gcongr
      exact sq_norm_le_torusDistSq (q - u)

theorem invSqKer_sub_le_thirtySix_mul
    {q u : T4} (hq : q ≠ 0) (huq : u ≠ q)
    (hregionThree : ¬ 2 * ‖q - u‖ ≤ ‖u‖) :
    invSqKer (q - u) ≤ 36 * invSqKer q := by
  have hqdist : 0 < torusDistSq q := by
    exact lt_of_le_of_ne (torusDistSq_nonneg q)
      (Ne.symm fun h => hq ((torusDistSq_eq_zero_iff q).mp h))
  have hsub : q - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huq)
  have hsubdist : 0 < torusDistSq (q - u) := by
    exact lt_of_le_of_ne (torusDistSq_nonneg (q - u))
      (Ne.symm fun h =>
        hsub ((torusDistSq_eq_zero_iff (q - u)).mp h))
  have hdist :=
    torusDistSq_le_thirtySix_mul_of_crude_regions
      hregionThree
  unfold invSqKer
  calc
    (torusDistSq (q - u))⁻¹ =
        1 / torusDistSq (q - u) := by rw [one_div]
    _ ≤ 36 / torusDistSq q :=
      (div_le_div_iff₀ hsubdist hqdist).2 (by
        simpa only [one_mul] using hdist)
    _ = 36 * (torusDistSq q)⁻¹ := by
      rw [div_eq_mul_inv]

/-- Pointwise domination of the non-Taylor part of a Green difference.
The only excluded point is the null set `u = q`, where the off-diagonal
Green estimate is not stated. -/
theorem abs_r322CrudeSectionIntegrand_le
    {J P : T4 → ℝ} {greenConstant : ℝ} {q u : T4}
    (hgreenConstant : 0 ≤ greenConstant)
    (hgreen : ∀ z : T4, torusDistSq z ≠ 0 →
      greenFn z ≤ greenConstant / torusDistSq z)
    (hq : q ≠ 0) (huq : u ≠ q)
    (hP : 0 ≤ P u) (hJ : |J u| ≤ P u) :
    |r322CrudeSectionIntegrand J q u| ≤
      r322CrudeSectionMajorant greenConstant P q u := by
  by_cases hregionOne : 2 * ‖u‖ ≤ ‖q‖
  · rw [r322CrudeSectionIntegrand, if_pos hregionOne,
      abs_zero]
    unfold r322CrudeSectionMajorant
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) hgreenConstant)
          (invSqKer_nonneg q))
        (by
          unfold reductionRegionTwoKernel
          split_ifs
          · exact hP
          · exact le_rfl))
      (mul_nonneg hgreenConstant
        (by
          unfold reductionRegionThreeKernel
          split_ifs
          · exact mul_nonneg
              (invSqKer_nonneg (q - u)) hP
          · exact le_rfl))
  have hregionTwo :=
    reductionRegionTwo_of_not_regionOne hregionOne
  have hqGreen :
      |greenFn q| ≤ greenConstant * invSqKer q :=
    by
      have hdist : torusDistSq q ≠ 0 := by
        intro hzero
        exact hq ((torusDistSq_eq_zero_iff q).mp hzero)
      simpa only [abs_of_nonneg (greenFn_nonneg q),
        invSqKer, div_eq_mul_inv] using hgreen q hdist
  have hsub : q - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huq)
  have hsubGreen :
      |greenFn (q - u)| ≤
        greenConstant * invSqKer (q - u) :=
    by
      have hdist : torusDistSq (q - u) ≠ 0 := by
        intro hzero
        exact hsub
          ((torusDistSq_eq_zero_iff (q - u)).mp hzero)
      simpa only [abs_of_nonneg (greenFn_nonneg (q - u)),
        invSqKer, div_eq_mul_inv] using
          hgreen (q - u) hdist
  have hdiff :
      |greenFn (q - u) - greenFn q| ≤
        greenConstant * invSqKer (q - u) +
          greenConstant * invSqKer q := by
    calc
      |greenFn (q - u) - greenFn q| ≤
          |greenFn (q - u)| + |greenFn q| :=
        abs_sub _ _
      _ ≤ greenConstant * invSqKer (q - u) +
          greenConstant * invSqKer q :=
        add_le_add hsubGreen hqGreen
  by_cases hregionThree : 2 * ‖q - u‖ ≤ ‖u‖
  · rw [r322CrudeSectionIntegrand, if_neg hregionOne,
      r322CrudeSectionMajorant]
    rw [reductionRegionTwoKernel, if_pos hregionTwo,
      reductionRegionThreeKernel, if_pos hregionThree]
    rw [abs_mul]
    calc
      |J u| * |greenFn (q - u) - greenFn q| ≤
          P u * (greenConstant * invSqKer (q - u) +
            greenConstant * invSqKer q) :=
        mul_le_mul hJ hdiff (abs_nonneg _) hP
      _ ≤ 37 * greenConstant * invSqKer q * P u +
          greenConstant * (invSqKer (q - u) * P u) := by
        nlinarith [mul_nonneg hgreenConstant
          (invSqKer_nonneg q),
          mul_nonneg hgreenConstant
            (invSqKer_nonneg (q - u))]
  · have hinv :=
      invSqKer_sub_le_thirtySix_mul hq huq hregionThree
    rw [r322CrudeSectionIntegrand, if_neg hregionOne,
      r322CrudeSectionMajorant]
    rw [reductionRegionTwoKernel, if_pos hregionTwo,
      reductionRegionThreeKernel, if_neg hregionThree]
    simp only [mul_zero, add_zero]
    rw [abs_mul]
    calc
      |J u| * |greenFn (q - u) - greenFn q| ≤
          P u * (greenConstant * invSqKer (q - u) +
            greenConstant * invSqKer q) :=
        mul_le_mul hJ hdiff (abs_nonneg _) hP
      _ ≤ P u * (37 * greenConstant * invSqKer q) := by
        gcongr
        nlinarith [mul_le_mul_of_nonneg_left hinv
          hgreenConstant]
      _ = 37 * greenConstant * invSqKer q * P u := by
        ring

/-- The region-(4.12) restriction of the full Proposition 4.1
majorant is integrable.  This is the integrability fact implicit in the
exact density identity. -/
theorem integrable_reductionRegionThreeKernel_primitiveKernelMajorant
    (C lam ε supportConstant : ℝ) (n : ℕ) (q : T4)
    (hε : 0 < ε) :
    Integrable
      (reductionRegionThreeKernel q
        (primitiveKernelMajorant
          C lam ε supportConstant n))
      paperMeasure := by
  let P : ℝ := (C * lam) ^ (2 * n)
  let a : ℝ := (ε⁻¹) ^ 4 / |Real.log ε|
  let b : ℝ := 1 / |Real.log ε| ^ 2
  let Jloc : T4 → ℝ := fun u =>
    invSqKer u *
      primitiveSupportIndicator supportConstant ε u
  let Jreg : T4 → ℝ := regularizedInvCube ε
  have hloc : Integrable
      (reductionRegionThreeKernel q Jloc)
      paperMeasure := by
    by_cases hq : q = 0
    · subst q
      rw [reductionRegionThreeKernel_zero]
      exact integrable_zero _ _ _
    · exact integrable_reductionRegionThreeLocal hq
  have hreg : Integrable
      (reductionRegionThreeKernel q Jreg)
      paperMeasure :=
    integrable_reductionRegionThreeRegular hε q
  have hfun :
      reductionRegionThreeKernel q
          (primitiveKernelMajorant
            C lam ε supportConstant n) =
        fun u =>
          P *
            (a * reductionRegionThreeKernel q Jloc u +
              b * reductionRegionThreeKernel q Jreg u) := by
    funext u
    unfold reductionRegionThreeKernel
    split_ifs
    · unfold primitiveKernelMajorant Jloc Jreg
        regularizedInvCube
      dsimp only [P, a, b]
      ring
    · ring
  rw [hfun]
  exact
    ((hloc.const_mul a).add
      (hreg.const_mul b)).const_mul P

theorem integrable_r322CrudeSectionMajorant
    (greenConstant C lam ε supportConstant : ℝ)
    (n : ℕ) (q : T4) (hε : 0 < ε) :
    Integrable
      (r322CrudeSectionMajorant greenConstant
        (primitiveKernelMajorant
          C lam ε supportConstant n) q)
      paperMeasure := by
  unfold r322CrudeSectionMajorant
  exact
    ((integrable_reductionRegionTwoKernel q
      (integrable_primitiveKernelMajorant
        C lam ε supportConstant n hε)).const_mul
          (37 * greenConstant * invSqKer q)).add
      ((integrable_reductionRegionThreeKernel_primitiveKernelMajorant
        C lam ε supportConstant n q hε).const_mul
          greenConstant)

theorem r322CrudeSectionMajorant_nonneg
    {greenConstant C lam : ℝ}
    (hgreenConstant : 0 ≤ greenConstant)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (ε supportConstant : ℝ) (n : ℕ) (q u : T4) :
    0 ≤ r322CrudeSectionMajorant greenConstant
      (primitiveKernelMajorant
        C lam ε supportConstant n) q u := by
  unfold r322CrudeSectionMajorant
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) hgreenConstant)
        (invSqKer_nonneg q))
      (by
        unfold reductionRegionTwoKernel
        split_ifs
        · exact primitiveKernelMajorant_nonneg hC hlam
        · exact le_rfl))
    (mul_nonneg hgreenConstant
      (r322RegionThreeKernel_nonneg
        (fun _ =>
          primitiveKernelMajorant_nonneg hC hlam) u))

theorem integrable_r322CrudeSectionIntegrand
    {J : T4 → ℝ}
    {greenConstant C lam ε supportConstant : ℝ}
    {n : ℕ} {q : T4}
    (hJmeas : Measurable J)
    (hgreenConstant : 0 ≤ greenConstant)
    (hgreen : ∀ z : T4, torusDistSq z ≠ 0 →
      greenFn z ≤ greenConstant / torusDistSq z)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hq : q ≠ 0)
    (hJ : ∀ u, |J u| ≤
      primitiveKernelMajorant
        C lam ε supportConstant n u) :
    Integrable (r322CrudeSectionIntegrand J q)
      paperMeasure := by
  let P : T4 → ℝ :=
    primitiveKernelMajorant
      C lam ε supportConstant n
  let M : T4 → ℝ :=
    r322CrudeSectionMajorant greenConstant P q
  have hMint : Integrable M paperMeasure :=
    integrable_r322CrudeSectionMajorant
      greenConstant C lam ε supportConstant n q hε
  refine Integrable.mono' hMint
    (measurable_r322CrudeSectionIntegrand
      hJmeas q).aestronglyMeasurable ?_
  filter_upwards
    [compl_mem_ae_iff.mpr (paperMeasure_singleton q)]
    with u hu
  rw [Real.norm_eq_abs]
  apply abs_r322CrudeSectionIntegrand_le
    hgreenConstant hgreen hq
  · simpa only [mem_compl_iff, mem_singleton_iff] using hu
  · exact primitiveKernelMajorant_nonneg hC hlam
  · exact hJ u

/-- The crude section is absolutely integrable and its integral is bounded
by the exact sum of the densities from (4.11) and (4.12). -/
theorem abs_integral_r322CrudeSectionIntegrand_le
    {J : T4 → ℝ}
    {greenConstant C lam ε supportConstant : ℝ}
    {n : ℕ} {q : T4}
    (hJmeas : Measurable J)
    (hgreenConstant : 0 ≤ greenConstant)
    (hgreen : ∀ z : T4, torusDistSq z ≠ 0 →
      greenFn z ≤ greenConstant / torusDistSq z)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hq : q ≠ 0)
    (hJ : ∀ u, |J u| ≤
      primitiveKernelMajorant
        C lam ε supportConstant n u) :
    |∫ u, r322CrudeSectionIntegrand J q u
        ∂paperMeasure| ≤
      37 * greenConstant *
          r322RegionTwoDensity
            C lam ε supportConstant n q +
        greenConstant *
          r322RegionThreeDensity
            C lam ε supportConstant n q := by
  let P : T4 → ℝ :=
    primitiveKernelMajorant
      C lam ε supportConstant n
  let M : T4 → ℝ :=
    r322CrudeSectionMajorant greenConstant P q
  have hMint : Integrable M paperMeasure :=
    integrable_r322CrudeSectionMajorant
      greenConstant C lam ε supportConstant n q hε
  have hbound :
      ∀ᵐ u ∂paperMeasure,
        |r322CrudeSectionIntegrand J q u| ≤ M u := by
    filter_upwards
      [compl_mem_ae_iff.mpr (paperMeasure_singleton q)]
      with u hu
    apply abs_r322CrudeSectionIntegrand_le
      hgreenConstant hgreen hq
    · simpa only [mem_compl_iff, mem_singleton_iff] using hu
    · exact primitiveKernelMajorant_nonneg hC hlam
    · exact hJ u
  have hsection :
      Integrable (r322CrudeSectionIntegrand J q)
        paperMeasure := by
    exact integrable_r322CrudeSectionIntegrand
      hJmeas hgreenConstant hgreen hC hlam hε hq hJ
  calc
    |∫ u, r322CrudeSectionIntegrand J q u
        ∂paperMeasure| ≤
        ∫ u, |r322CrudeSectionIntegrand J q u|
          ∂paperMeasure := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (μ := paperMeasure)
          (r322CrudeSectionIntegrand J q))
    _ ≤ ∫ u, M u ∂paperMeasure := by
      exact integral_mono_ae
        hsection.abs hMint hbound
    _ = 37 * greenConstant *
          r322RegionTwoDensity
            C lam ε supportConstant n q +
        greenConstant *
          r322RegionThreeDensity
            C lam ε supportConstant n q := by
      dsimp only [M, P]
      unfold r322CrudeSectionMajorant
      rw [integral_add
        ((integrable_reductionRegionTwoKernel q
          (integrable_primitiveKernelMajorant
            C lam ε supportConstant n hε)).const_mul
              (37 * greenConstant * invSqKer q))
        ((integrable_reductionRegionThreeKernel_primitiveKernelMajorant
          C lam ε supportConstant n q hε).const_mul
            greenConstant)]
      rw [integral_const_mul, integral_const_mul,
        r322RegionTwoDensity_eq_integral
          C lam ε supportConstant n q hε,
        r322RegionThreeDensity_eq_integral
          C lam ε supportConstant n q hε]
      ring

theorem integrable_r322RegionOne_coordinateMoment
    {J : T4 → ℝ} {C lam ε supportConstant : ℝ}
    {n : ℕ} (q : T4) (i : Fin dim)
    (hJmeas : Measurable J)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hε : 0 < ε)
    (hJ : ∀ u, |J u| ≤
      primitiveKernelMajorant
        C lam ε supportConstant n u) :
    Integrable
      (fun u =>
        reductionRegionOneKernel q J u *
          torusLift u i)
      paperMeasure := by
  let P : T4 → ℝ :=
    primitiveKernelMajorant
      C lam ε supportConstant n
  have hPint : Integrable P paperMeasure :=
    integrable_primitiveKernelMajorant
      C lam ε supportConstant n hε
  refine Integrable.mono'
    (hPint.const_mul Real.pi)
    ((measurable_reductionRegionOneKernel q hJmeas).mul
      ((measurable_pi_apply i).comp
        measurable_torusLift)).aestronglyMeasurable
    (.of_forall fun u => ?_)
  have hlift : |torusLift u i| ≤ Real.pi := by
    obtain ⟨hlow, hupp⟩ := torusLift_mem_Ico u i
    exact abs_le.mpr ⟨hlow, hupp.le⟩
  have hregion :
      |reductionRegionOneKernel q J u| ≤ P u := by
    unfold reductionRegionOneKernel
    split_ifs
    · exact hJ u
    · exact abs_zero.trans_le
        (primitiveKernelMajorant_nonneg hC hlam)
  have hPnonneg : 0 ≤ P u :=
    primitiveKernelMajorant_nonneg hC hlam
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul hregion hlift
    (abs_nonneg _) hPnonneg).trans_eq (mul_comm _ _)

theorem integrable_r322TaylorMajorant_of_bound
    {J : T4 → ℝ} {C lam ε supportConstant : ℝ}
    {n : ℕ} {q : T4}
    (hJmeas : Measurable J)
    (hsupport : 0 < supportConstant)
    (hε : 0 < ε)
    (hJ : ∀ u, |J u| ≤
      primitiveKernelMajorant
        C lam ε supportConstant n u) :
    Integrable
      (fun u =>
        |reductionRegionOneKernel q J u| *
          ((6144 * greenLocalHessSingularBound *
            invSqKer q ^ 2) * torusDistSq u))
      paperMeasure := by
  let A : ℝ :=
    6144 * greenLocalHessSingularBound *
      invSqKer q ^ 2
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg (by positivity)
        greenLocalHessSingularBound_nonneg)
      (sq_nonneg (invSqKer q))
  have hmajor :
      Integrable
        (fun u =>
          A *
            (reductionRegionOneKernel q
              (primitiveKernelMajorant
                C lam ε supportConstant n) u *
              torusDistSq u))
        paperMeasure :=
    (integrable_r322TaylorMoment_integrand
      (C := C) (lam := lam) (ε := ε)
      (supportConstant := supportConstant) (n := n)
      (q := q) hsupport hε).const_mul A
  refine Integrable.mono' hmajor
    (((measurable_reductionRegionOneKernel q hJmeas).abs.mul
      (measurable_const.mul measurable_torusDistSq))
      |>.aestronglyMeasurable)
    (.of_forall fun u => ?_)
  have hregion :
      |reductionRegionOneKernel q J u| ≤
        reductionRegionOneKernel q
          (primitiveKernelMajorant
            C lam ε supportConstant n) u := by
    unfold reductionRegionOneKernel
    split_ifs
    · exact hJ u
    · simp
  have hPregion :
      0 ≤ reductionRegionOneKernel q
        (primitiveKernelMajorant
          C lam ε supportConstant n) u := by
    unfold reductionRegionOneKernel
    split_ifs
    · exact primitiveKernelMajorant_nonneg_even
        C lam ε supportConstant n u
    · exact le_rfl
  have hdist := torusDistSq_nonneg u
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (mul_nonneg (abs_nonneg _)
        (mul_nonneg hA hdist))]
  calc
    |reductionRegionOneKernel q J u| *
        (A * torusDistSq u) ≤
      reductionRegionOneKernel q
          (primitiveKernelMajorant
            C lam ε supportConstant n) u *
        (A * torusDistSq u) :=
      mul_le_mul_of_nonneg_right hregion
        (mul_nonneg hA hdist)
    _ = A *
        (reductionRegionOneKernel q
          (primitiveKernelMajorant
            C lam ε supportConstant n) u *
          torusDistSq u) := by ring

theorem integrable_r322GreenRemainder_of_bound
    {J : T4 → ℝ} {C lam ε supportConstant : ℝ}
    {n : ℕ} {q : T4}
    (hJmeas : Measurable J)
    (hsupport : 0 < supportConstant)
    (hε : 0 < ε) (hq : q ≠ 0)
    (hJ : ∀ u, |J u| ≤
      primitiveKernelMajorant
        C lam ε supportConstant n u) :
    Integrable
      (fun u =>
        reductionRegionOneKernel q J u *
          r322GreenRemainder q u)
      paperMeasure := by
  have hmajor :=
    integrable_r322TaylorMajorant_of_bound
      (C := C) (lam := lam) (ε := ε)
      (supportConstant := supportConstant)
      (n := n) (q := q)
      hJmeas hsupport hε hJ
  refine Integrable.mono' hmajor
    ((measurable_reductionRegionOneKernel q hJmeas).mul
      (measurable_r322GreenRemainder q)
      |>.aestronglyMeasurable)
    (.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hweighted :
      |reductionRegionOneKernel q J u| *
          |r322GreenRemainder q u| ≤
        |reductionRegionOneKernel q J u| *
          ((6144 * greenLocalHessSingularBound *
            invSqKer q ^ 2) * torusDistSq u) := by
    by_cases hregion : 2 * ‖u‖ ≤ ‖q‖
    · exact mul_le_mul_of_nonneg_left
        (abs_r322GreenRemainder_le_of_reductionRegion_one
          q u hregion hq)
        (abs_nonneg
          (reductionRegionOneKernel q J u))
    · simp [reductionRegionOneKernel, hregion]
  have hnonneg :
      0 ≤ |reductionRegionOneKernel q J u| *
          ((6144 * greenLocalHessSingularBound *
            invSqKer q ^ 2) * torusDistSq u) := by
    exact mul_nonneg (abs_nonneg _)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity)
            greenLocalHessSingularBound_nonneg)
          (sq_nonneg (invSqKer q)))
        (torusDistSq_nonneg u))
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg hnonneg] using hweighted

theorem integrable_r322TaylorDifference_of_bound
    {J : T4 → ℝ} {C lam ε supportConstant : ℝ}
    {n : ℕ} {q : T4}
    (hJmeas : Measurable J)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hsupport : 0 < supportConstant)
    (hε : 0 < ε) (hq : q ≠ 0)
    (hJ : ∀ u, |J u| ≤
      primitiveKernelMajorant
        C lam ε supportConstant n u) :
    Integrable
      (fun u =>
        reductionRegionOneKernel q J u *
          (greenFn q - greenFn (q - u)))
      paperMeasure := by
  let D : R4 →L[ℝ] ℝ :=
    greenGradientCLM (torusLift q)
  have hmoment : ∀ i : Fin dim,
      Integrable
        (fun u =>
          reductionRegionOneKernel q J u *
            torusLift u i)
        paperMeasure :=
    fun i =>
      integrable_r322RegionOne_coordinateMoment
        q i hJmeas hC hlam hε hJ
  have hlinear :
      Integrable
        (fun u =>
          reductionRegionOneKernel q J u *
            torusLinearTerm D u)
        paperMeasure := by
    rw [show
      (fun u =>
        reductionRegionOneKernel q J u *
          torusLinearTerm D u) =
      fun u =>
        ∑ i : Fin dim,
          D (Pi.single i 1) *
            (reductionRegionOneKernel q J u *
              torusLift u i) by
      funext u
      rw [torusLinearTerm_eq_sum_r322OneBlock]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring]
    exact integrable_finsetSum _ fun i _hi =>
      (hmoment i).const_mul _
  have hrem :
      Integrable
        (fun u =>
          reductionRegionOneKernel q J u *
            r322GreenRemainder q u)
        paperMeasure :=
    integrable_r322GreenRemainder_of_bound
      hJmeas hsupport hε hq hJ
  rw [show
    (fun u =>
      reductionRegionOneKernel q J u *
        (greenFn q - greenFn (q - u))) =
    fun u =>
      reductionRegionOneKernel q J u *
          torusLinearTerm D u +
        reductionRegionOneKernel q J u *
          r322GreenRemainder q u by
    funext u
    rw [r322GreenDifference_expansion]
    dsimp only [D]
    ring]
  exact hlinear.add hrem

/-- Algebraic splitting of the full Green difference into the Taylor
region and its crude complement. -/
theorem r322GreenDifferenceSection_eq_taylor_add_crude
    (J : T4 → ℝ) (q : T4)
    (hintTaylor : Integrable
      (fun u =>
        reductionRegionOneKernel q J u *
          (greenFn q - greenFn (q - u)))
      paperMeasure)
    (hintCrude : Integrable
      (r322CrudeSectionIntegrand J q)
      paperMeasure) :
    r322GreenDifferenceSection J q =
      -(∫ u,
          reductionRegionOneKernel q J u *
            (greenFn q - greenFn (q - u))
          ∂paperMeasure) +
        ∫ u, r322CrudeSectionIntegrand J q u
          ∂paperMeasure := by
  have hfun :
      (fun u =>
        J u * (greenFn (q - u) - greenFn q)) =
      fun u =>
        -(reductionRegionOneKernel q J u *
            (greenFn q - greenFn (q - u))) +
          r322CrudeSectionIntegrand J q u := by
    funext u
    by_cases hregion : 2 * ‖u‖ ≤ ‖q‖
    · simp [reductionRegionOneKernel,
        r322CrudeSectionIntegrand, hregion]
      ring
    · simp [reductionRegionOneKernel,
        r322CrudeSectionIntegrand, hregion]
  unfold r322GreenDifferenceSection
  have hneg : Integrable
      (fun u =>
        -(reductionRegionOneKernel q J u *
          (greenFn q - greenFn (q - u))))
      paperMeasure :=
    hintTaylor.neg
  rw [hfun, integral_add hneg hintCrude,
    integral_neg]

/-- The three-region inner estimate.  This is the analytic content of
(4.10)--(4.12) before the outer convolution. -/
theorem abs_r322GreenDifferenceSection_le
    {J : T4 → ℝ}
    {greenConstant C lam ε supportConstant : ℝ}
    {n : ℕ} {q : T4}
    (hJmem : MemEClassT4 J)
    (hJmeas : Measurable J)
    (hgreenConstant : 0 ≤ greenConstant)
    (hgreen : ∀ z : T4, torusDistSq z ≠ 0 →
      greenFn z ≤ greenConstant / torusDistSq z)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hsupport : 0 < supportConstant)
    (hε : 0 < ε) (hq : q ≠ 0)
    (hJ : ∀ u, |J u| ≤
      primitiveKernelMajorant
        C lam ε supportConstant n u)
    (hmoment : ∀ i : Fin dim,
      Integrable
        (fun u =>
          reductionRegionOneKernel q J u *
            torusLift u i)
        paperMeasure)
    (hintR : Integrable
      (fun u =>
        reductionRegionOneKernel q J u *
          r322GreenRemainder q u)
      paperMeasure)
    (hintMajorant : Integrable
      (fun u =>
        |reductionRegionOneKernel q J u| *
          ((6144 * greenLocalHessSingularBound *
            invSqKer q ^ 2) * torusDistSq u))
      paperMeasure)
    (hintTaylor : Integrable
      (fun u =>
        reductionRegionOneKernel q J u *
          (greenFn q - greenFn (q - u)))
      paperMeasure) :
    |r322GreenDifferenceSection J q| ≤
      (6144 * greenLocalHessSingularBound) *
          r322TaylorDensity
            C lam ε supportConstant n q +
        37 * greenConstant *
          r322RegionTwoDensity
            C lam ε supportConstant n q +
        greenConstant *
          r322RegionThreeDensity
            C lam ε supportConstant n q := by
  have hintCrude :
      Integrable (r322CrudeSectionIntegrand J q)
        paperMeasure :=
    integrable_r322CrudeSectionIntegrand
      hJmeas hgreenConstant hgreen hC hlam hε hq hJ
  have hTaylor :=
    r322GreenDifference_regionOne_integral_le
      hJmem q hq hmoment hintR hintMajorant
  have hPint :=
    integrable_r322TaylorMoment_integrand
      (C := C) (lam := lam) (ε := ε)
      (supportConstant := supportConstant) (n := n)
      (q := q) hsupport hε
  have hTaylorDensity :
      (∫ u,
        |reductionRegionOneKernel q J u| *
          ((6144 * greenLocalHessSingularBound *
            invSqKer q ^ 2) * torusDistSq u)
        ∂paperMeasure) ≤
      (6144 * greenLocalHessSingularBound) *
        r322TaylorDensity
          C lam ε supportConstant n q := by
    calc
      (∫ u,
        |reductionRegionOneKernel q J u| *
          ((6144 * greenLocalHessSingularBound *
            invSqKer q ^ 2) * torusDistSq u)
        ∂paperMeasure) ≤
          ∫ u,
            (6144 * greenLocalHessSingularBound *
              invSqKer q ^ 2) *
              (reductionRegionOneKernel q
                (primitiveKernelMajorant
                  C lam ε supportConstant n) u *
                torusDistSq u)
            ∂paperMeasure := by
        apply integral_mono hintMajorant
          (hPint.const_mul
            (6144 * greenLocalHessSingularBound *
              invSqKer q ^ 2))
        intro u
        have hregion :
            |reductionRegionOneKernel q J u| ≤
              reductionRegionOneKernel q
                (primitiveKernelMajorant
                  C lam ε supportConstant n) u := by
          unfold reductionRegionOneKernel
          split_ifs
          · exact hJ u
          · simp
        have hcoef :
            0 ≤ 6144 * greenLocalHessSingularBound *
              invSqKer q ^ 2 := by
          exact mul_nonneg
            (mul_nonneg (by positivity)
              greenLocalHessSingularBound_nonneg)
            (sq_nonneg (invSqKer q))
        have hdist := torusDistSq_nonneg u
        calc
          |reductionRegionOneKernel q J u| *
              ((6144 * greenLocalHessSingularBound *
                invSqKer q ^ 2) * torusDistSq u) ≤
            reductionRegionOneKernel q
                (primitiveKernelMajorant
                  C lam ε supportConstant n) u *
              ((6144 * greenLocalHessSingularBound *
                invSqKer q ^ 2) * torusDistSq u) :=
            mul_le_mul_of_nonneg_right hregion
              (mul_nonneg hcoef hdist)
          _ = _ := by ring
      _ = (6144 * greenLocalHessSingularBound) *
          r322TaylorDensity
            C lam ε supportConstant n q := by
        rw [integral_const_mul]
        unfold r322TaylorDensity r322TaylorMoment
        ring
  have hCrude :=
    abs_integral_r322CrudeSectionIntegrand_le
      hJmeas hgreenConstant hgreen hC hlam hε hq hJ
  rw [r322GreenDifferenceSection_eq_taylor_add_crude
    J q hintTaylor hintCrude]
  calc
    |-(∫ u,
          reductionRegionOneKernel q J u *
            (greenFn q - greenFn (q - u))
          ∂paperMeasure) +
        ∫ u, r322CrudeSectionIntegrand J q u
          ∂paperMeasure| ≤
      |∫ u,
          reductionRegionOneKernel q J u *
            (greenFn q - greenFn (q - u))
          ∂paperMeasure| +
        |∫ u, r322CrudeSectionIntegrand J q u
          ∂paperMeasure| := by
      simpa only [abs_neg] using
        abs_add_le
          (-(∫ u,
            reductionRegionOneKernel q J u *
              (greenFn q - greenFn (q - u))
            ∂paperMeasure))
          (∫ u, r322CrudeSectionIntegrand J q u
            ∂paperMeasure)
    _ ≤ (6144 * greenLocalHessSingularBound) *
          r322TaylorDensity
            C lam ε supportConstant n q +
        (37 * greenConstant *
          r322RegionTwoDensity
            C lam ε supportConstant n q +
        greenConstant *
          r322RegionThreeDensity
            C lam ε supportConstant n q) :=
      add_le_add (hTaylor.trans hTaylorDensity) hCrude
    _ = _ := by ring

/-- Constructive one-block inner estimate with no technical
integrability assumptions left to the caller. -/
theorem abs_r322GreenDifferenceSection_le_of_majorant
    {J : T4 → ℝ}
    {greenConstant C lam ε supportConstant : ℝ}
    {n : ℕ} {q : T4}
    (hJmem : MemEClassT4 J)
    (hJmeas : Measurable J)
    (hgreenConstant : 0 ≤ greenConstant)
    (hgreen : ∀ z : T4, torusDistSq z ≠ 0 →
      greenFn z ≤ greenConstant / torusDistSq z)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hsupport : 0 < supportConstant)
    (hε : 0 < ε) (hq : q ≠ 0)
    (hJ : ∀ u, |J u| ≤
      primitiveKernelMajorant
        C lam ε supportConstant n u) :
    |r322GreenDifferenceSection J q| ≤
      (6144 * greenLocalHessSingularBound) *
          r322TaylorDensity
            C lam ε supportConstant n q +
        37 * greenConstant *
          r322RegionTwoDensity
            C lam ε supportConstant n q +
        greenConstant *
          r322RegionThreeDensity
            C lam ε supportConstant n q := by
  apply abs_r322GreenDifferenceSection_le
    hJmem hJmeas hgreenConstant hgreen hC hlam
    hsupport hε hq hJ
  · intro i
    exact integrable_r322RegionOne_coordinateMoment
      q i hJmeas hC hlam hε hJ
  · exact integrable_r322GreenRemainder_of_bound
      hJmeas hsupport hε hq hJ
  · exact integrable_r322TaylorMajorant_of_bound
      hJmeas hsupport hε hJ
  · exact integrable_r322TaylorDifference_of_bound
      hJmeas hC hlam hsupport hε hq hJ

end

end Anderson4D
