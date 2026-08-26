import Anderson4D.DetParametrix.Paper41_Renorm.R322RegionTwoProfile

/-!
# The crude Green profile in region (4.12)

In the last region put `q = z-y`, `u = z-w`, so `q-u = w-y`.
The condition `2‖q-u‖ ≤ ‖u‖` makes `u` comparable with `q`.
Consequently the inner inverse-square mass supplies a factor
`O(torusDistSq q)`.  Applied to the two Proposition 4.1 summands this
gives a flat `ε⁻⁴ / |log ε|` profile at primitive scale and the same
critical `invSqKer² / |log ε|` profile as in region (4.11).
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set

/-- Restriction and inner Green factor for the last crude region. -/
def reductionRegionThreeKernel
    (q : T4) (J : T4 → ℝ) (u : T4) : ℝ :=
  if 2 * ‖q - u‖ ≤ ‖u‖ then
    invSqKer (q - u) * J u
  else 0

theorem measurableSet_reductionRegionThree (q : T4) :
    MeasurableSet {u : T4 | 2 * ‖q - u‖ ≤ ‖u‖} :=
  measurableSet_le
    (measurable_const.mul
      (measurable_const.sub measurable_id).norm)
    measurable_norm

theorem reductionRegionThreeKernel_eq_indicator
    (q : T4) (J : T4 → ℝ) :
    reductionRegionThreeKernel q J =
      {u : T4 | 2 * ‖q - u‖ ≤ ‖u‖}.indicator
        (fun u => invSqKer (q - u) * J u) := by
  funext u
  unfold reductionRegionThreeKernel
  by_cases hu : 2 * ‖q - u‖ ≤ ‖u‖
  · simp [hu]
  · simp [hu]

theorem measurable_reductionRegionThreeKernel_joint
    {J : T4 → ℝ} (hJ : Measurable J) :
    Measurable fun p : T4 × T4 =>
      reductionRegionThreeKernel p.1 J p.2 := by
  unfold reductionRegionThreeKernel
  exact Measurable.ite
    (measurableSet_le
      (measurable_const.mul
        (measurable_fst.sub measurable_snd).norm)
      measurable_snd.norm)
    ((measurable_invSqKer.comp
      (measurable_fst.sub measurable_snd)).mul
        (hJ.comp measurable_snd))
    measurable_const

theorem measurable_reductionRegionThreeKernel
    (q : T4) {J : T4 → ℝ} (hJ : Measurable J) :
    Measurable (reductionRegionThreeKernel q J) := by
  unfold reductionRegionThreeKernel
  exact Measurable.ite
    (measurableSet_le
      (measurable_const.mul
        (measurable_const.sub measurable_id).norm)
      measurable_norm)
    ((measurable_invSqKer.comp
      (measurable_const.sub measurable_id)).mul hJ)
    measurable_const

/-- The local-support part of the (4.12) inner integral. -/
def r322RegionThreeLocalMoment
    (supportConstant ε : ℝ) (q : T4) : ℝ :=
  ∫ u,
    reductionRegionThreeKernel q
      (fun v =>
        invSqKer v *
          primitiveSupportIndicator supportConstant ε v) u
    ∂paperMeasure

/-- The regularized part of the (4.12) inner integral. -/
def r322RegionThreeRegularMoment
    (ε : ℝ) (q : T4) : ℝ :=
  ∫ u,
    reductionRegionThreeKernel q
      (regularizedInvCube ε) u
    ∂paperMeasure

theorem measurable_r322RegionThreeLocalMoment
    (supportConstant ε : ℝ) :
    Measurable
      (r322RegionThreeLocalMoment supportConstant ε) := by
  unfold r322RegionThreeLocalMoment
  rw [paperMeasure_eq_volume]
  exact
    (measurable_reductionRegionThreeKernel_joint
      (measurable_invSqKer.mul
        (measurable_primitiveSupportIndicator
          supportConstant ε)))
      |>.stronglyMeasurable.integral_prod_right.measurable

theorem measurable_r322RegionThreeRegularMoment
    (ε : ℝ) :
    Measurable (r322RegionThreeRegularMoment ε) := by
  unfold r322RegionThreeRegularMoment
  rw [paperMeasure_eq_volume]
  exact
    (measurable_reductionRegionThreeKernel_joint
      (measurable_regularizedInvCube ε))
      |>.stronglyMeasurable.integral_prod_right.measurable

theorem r322RegionThreeKernel_nonneg
    {q : T4} {J : T4 → ℝ}
    (hJ : ∀ u, 0 ≤ J u) (u : T4) :
    0 ≤ reductionRegionThreeKernel q J u := by
  unfold reductionRegionThreeKernel
  split_ifs
  · exact mul_nonneg (invSqKer_nonneg _) (hJ _)
  · exact le_rfl

theorem r322RegionThreeLocalMoment_nonneg
    (supportConstant ε : ℝ) (q : T4) :
    0 ≤ r322RegionThreeLocalMoment
      supportConstant ε q := by
  unfold r322RegionThreeLocalMoment
  exact integral_nonneg
    (r322RegionThreeKernel_nonneg fun u =>
      mul_nonneg (invSqKer_nonneg u)
        (primitiveSupportIndicator_nonneg _ _ u))

theorem r322RegionThreeRegularMoment_nonneg
    (ε : ℝ) (q : T4) :
    0 ≤ r322RegionThreeRegularMoment ε q := by
  unfold r322RegionThreeRegularMoment
  exact integral_nonneg
    (r322RegionThreeKernel_nonneg
      (regularizedInvCube_nonneg ε))

@[simp]
theorem reductionRegionThreeKernel_zero
    (J : T4 → ℝ) :
    reductionRegionThreeKernel 0 J = 0 := by
  funext u
  unfold reductionRegionThreeKernel
  split_ifs with hregion
  · have hu : u = 0 := by
      rw [zero_sub, norm_neg] at hregion
      have : ‖u‖ = 0 := by
        nlinarith [norm_nonneg u]
      exact norm_eq_zero.mp this
    subst u
    simp [invSqKer_zero_r322]
  · rfl

@[simp]
theorem r322RegionThreeLocalMoment_zero
    (supportConstant ε : ℝ) :
    r322RegionThreeLocalMoment supportConstant ε 0 = 0 := by
  unfold r322RegionThreeLocalMoment
  rw [reductionRegionThreeKernel_zero]
  simp

@[simp]
theorem r322RegionThreeRegularMoment_zero
    (ε : ℝ) :
    r322RegionThreeRegularMoment ε 0 = 0 := by
  unfold r322RegionThreeRegularMoment
  rw [reductionRegionThreeKernel_zero]
  simp

/-- In region (4.12), the inner Green singularity lies in a ball about
`q`, and the primitive displacement is comparable to `q`. -/
theorem r322RegionThree_geometry
    {q u : T4} (hq : q ≠ 0)
    (hregion : 2 * ‖q - u‖ ≤ ‖u‖) :
    u ∈ Metric.ball q (2 * ‖q‖) ∧
      torusDistSq q ≤ 9 * torusDistSq u := by
  have htri : ‖u‖ ≤ ‖q‖ + ‖q - u‖ := by
    have h := norm_sub_le q (q - u)
    simpa only [sub_sub_cancel] using h
  have hvq : ‖q - u‖ ≤ ‖q‖ := by
    linarith
  have hqNorm : 2 * ‖q‖ ≤ 3 * ‖u‖ := by
    have hreverse := norm_sub_norm_le q u
    linarith
  constructor
  · rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt (by
      simpa only [norm_sub_rev] using hvq) (by
      have := norm_pos_iff.mpr hq
      linarith)
  · calc
      torusDistSq q ≤ 4 * ‖q‖ ^ 2 :=
        torusDistSq_le_four_mul_sq_norm q
      _ ≤ 9 * ‖u‖ ^ 2 := by
        nlinarith [norm_nonneg q, norm_nonneg u]
      _ ≤ 9 * torusDistSq u :=
        mul_le_mul_of_nonneg_left
          (sq_norm_le_torusDistSq u) (by norm_num)

theorem invSqKer_le_nine_mul_regionThree
    {q u : T4} (hq : q ≠ 0)
    (hregion : 2 * ‖q - u‖ ≤ ‖u‖) :
    invSqKer u ≤ 9 * invSqKer q := by
  have hqu :=
    (r322RegionThree_geometry hq hregion).2
  have hqDist : 0 < torusDistSq q := by
    have hne : torusDistSq q ≠ 0 := by
      intro hzero
      exact hq ((torusDistSq_eq_zero_iff q).mp hzero)
    exact lt_of_le_of_ne
      (torusDistSq_nonneg q) hne.symm
  have huDist : 0 < torusDistSq u := by
    nlinarith
  unfold invSqKer
  rw [le_mul_inv_iff₀ hqDist, inv_mul_eq_div,
    div_le_iff₀ huDist]
  exact hqu

theorem regularizedInvCube_le_regionThree
    {ε : ℝ} (hε : 0 < ε)
    {q u : T4} (hq : q ≠ 0)
    (hregion : 2 * ‖q - u‖ ≤ ‖u‖) :
    regularizedInvCube ε u ≤
      729 * (torusDistSq q + ε ^ 2)⁻¹ ^ 3 := by
  have hqu :=
    (r322RegionThree_geometry hq hregion).2
  have hqBase :
      0 < torusDistSq q + ε ^ 2 :=
    add_pos_of_nonneg_of_pos
      (torusDistSq_nonneg q) (sq_pos_of_pos hε)
  have huBase :
      0 < torusDistSq u + ε ^ 2 :=
    add_pos_of_nonneg_of_pos
      (torusDistSq_nonneg u) (sq_pos_of_pos hε)
  have hcompare :
      torusDistSq q + ε ^ 2 ≤
        9 * (torusDistSq u + ε ^ 2) := by
    nlinarith [sq_nonneg ε]
  have hinv :
      (torusDistSq u + ε ^ 2)⁻¹ ≤
        9 * (torusDistSq q + ε ^ 2)⁻¹ := by
    rw [le_mul_inv_iff₀ hqBase, inv_mul_eq_div,
      div_le_iff₀ huBase]
    exact hcompare
  unfold regularizedInvCube
  calc
    (torusDistSq u + ε ^ 2)⁻¹ ^ 3 ≤
        (9 * (torusDistSq q + ε ^ 2)⁻¹) ^ 3 :=
      pow_le_pow_left₀
        (inv_nonneg.mpr huBase.le) hinv 3
    _ = 729 *
        (torusDistSq q + ε ^ 2)⁻¹ ^ 3 := by
      ring

theorem integrable_reductionRegionThreeLocal
    {supportConstant ε : ℝ} {q : T4}
    (hq : q ≠ 0) :
    Integrable
      (reductionRegionThreeKernel q
        (fun u =>
          invSqKer u *
            primitiveSupportIndicator supportConstant ε u))
      paperMeasure := by
  have hmajorant :=
    integrable_invSqKer_sub_mul_invSqKer_of_ne hq
  apply hmajorant.mono'
    (measurable_reductionRegionThreeKernel q
      (measurable_invSqKer.mul
      (measurable_primitiveSupportIndicator
          supportConstant ε))
      |>.aestronglyMeasurable)
  filter_upwards with u
  have hnonneg :
      0 ≤ reductionRegionThreeKernel q
        (invSqKer *
          primitiveSupportIndicator supportConstant ε) u :=
    r322RegionThreeKernel_nonneg
      (fun v =>
        mul_nonneg (invSqKer_nonneg v)
          (primitiveSupportIndicator_nonneg _ _ v)) u
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  unfold reductionRegionThreeKernel
  split_ifs
  · calc
      invSqKer (q - u) *
            (invSqKer u *
              primitiveSupportIndicator
                supportConstant ε u) ≤
          invSqKer (q - u) * (invSqKer u * 1) := by
        apply mul_le_mul_of_nonneg_left _
          (invSqKer_nonneg (q - u))
        have hind :
            primitiveSupportIndicator
                supportConstant ε u ≤ 1 := by
          unfold primitiveSupportIndicator
          split_ifs <;> norm_num
        exact mul_le_mul_of_nonneg_left
          hind
          (invSqKer_nonneg u)
      _ = invSqKer (q - u) * invSqKer u := by
        ring
  · exact mul_nonneg
      (invSqKer_nonneg (q - u))
      (invSqKer_nonneg u)

theorem integrable_reductionRegionThreeRegular
    {ε : ℝ} (hε : 0 < ε) (q : T4) :
    Integrable
      (reductionRegionThreeKernel q
        (regularizedInvCube ε))
      paperMeasure := by
  let B : ℝ := ε⁻¹ ^ (6 : ℕ)
  have hmajorant :
      Integrable
        (fun u : T4 =>
          invSqKer (q - u) * B)
        paperMeasure :=
    (integrable_invSqKer_sub_left q).mul_const B
  apply hmajorant.mono'
    (measurable_reductionRegionThreeKernel q
      (measurable_regularizedInvCube ε)
      |>.aestronglyMeasurable)
  filter_upwards with u
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (r322RegionThreeKernel_nonneg
        (regularizedInvCube_nonneg ε) u)]
  unfold reductionRegionThreeKernel
  split_ifs
  · apply mul_le_mul_of_nonneg_left _
      (invSqKer_nonneg (q - u))
    unfold regularizedInvCube B
    have hbase :
        ε ^ 2 ≤ torusDistSq u + ε ^ 2 :=
      le_add_of_nonneg_left (torusDistSq_nonneg u)
    have hinv :
        (torusDistSq u + ε ^ 2)⁻¹ ≤
          (ε ^ 2)⁻¹ :=
      inv_anti₀ (sq_pos_of_pos hε) hbase
    calc
      (torusDistSq u + ε ^ 2)⁻¹ ^ 3 ≤
          (ε ^ 2)⁻¹ ^ 3 :=
        pow_le_pow_left₀
          (inv_nonneg.mpr
            (add_nonneg (torusDistSq_nonneg u)
              (sq_nonneg ε))) hinv 3
      _ = ε⁻¹ ^ (6 : ℕ) := by
        field_simp [hε.ne']
  · exact mul_nonneg
      (invSqKer_nonneg (q - u))
      (pow_nonneg (inv_nonneg.mpr hε.le) 6)

/-- Comparability part of the last-region geometry, without the
off-diagonal hypothesis needed only for the open-ball statement. -/
theorem r322RegionThree_torusDistSq_le
    {q u : T4}
    (hregion : 2 * ‖q - u‖ ≤ ‖u‖) :
    torusDistSq q ≤ 9 * torusDistSq u := by
  have hqNorm : 2 * ‖q‖ ≤ 3 * ‖u‖ := by
    have hreverse := norm_sub_norm_le q u
    linarith
  calc
    torusDistSq q ≤ 4 * ‖q‖ ^ 2 :=
      torusDistSq_le_four_mul_sq_norm q
    _ ≤ 9 * ‖u‖ ^ 2 := by
      nlinarith [norm_nonneg q, norm_nonneg u]
    _ ≤ 9 * torusDistSq u :=
      mul_le_mul_of_nonneg_left
        (sq_norm_le_torusDistSq u) (by norm_num)

theorem r322RegionThreeLocalMoment_eq_zero_of_not_scale
    {supportConstant ε : ℝ}
    (hsupport : 0 < supportConstant) (hε : 0 < ε)
    {q : T4}
    (hq :
      q ∉ r322ScaleBall
        (3 * supportConstant + 1) ε) :
    r322RegionThreeLocalMoment supportConstant ε q = 0 := by
  unfold r322RegionThreeLocalMoment
  have hfun :
      reductionRegionThreeKernel q
          (fun u =>
            invSqKer u *
              primitiveSupportIndicator
                supportConstant ε u) =
        fun _ => 0 := by
    funext u
    unfold reductionRegionThreeKernel
    split_ifs with hregion
    · have huNot :
          ¬torusDistSq u ≤
            (supportConstant * ε) ^ 2 := by
        intro hu
        have hqDist :
            torusDistSq q ≤
              (3 * supportConstant * ε) ^ 2 := by
          calc
            torusDistSq q ≤ 9 * torusDistSq u :=
              r322RegionThree_torusDistSq_le hregion
            _ ≤ 9 * (supportConstant * ε) ^ 2 :=
              mul_le_mul_of_nonneg_left hu (by norm_num)
            _ = (3 * supportConstant * ε) ^ 2 := by
              ring
        have hnear :
            q ∈ r322ScaleBall
              (3 * supportConstant + 1) ε := by
          change torusDistSq q ≤
            ((3 * supportConstant + 1) * ε) ^ 2
          have hscaled :
              0 ≤ 3 * supportConstant * ε := by
            positivity
          have hscaled' :
              3 * supportConstant * ε ≤
                (3 * supportConstant + 1) * ε := by
            nlinarith
          exact hqDist.trans
            (pow_le_pow_left₀ hscaled hscaled' 2)
        exact hq hnear
      dsimp only
      rw [primitiveSupportIndicator_eq_zero huNot,
        mul_zero, mul_zero]
    · rfl
  rw [hfun]
  simp

/-- The local-support inner Green integral in (4.12) is uniformly
bounded; its outer support is handled separately above. -/
theorem exists_r322RegionThreeLocalMoment_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ (supportConstant ε : ℝ) (q : T4),
        r322RegionThreeLocalMoment
          supportConstant ε q ≤ K := by
  obtain ⟨Cker, hCker, hker⟩ :=
    invSqKerBallIntegral_le
  let K : ℝ := 36 * Cker + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro supportConstant ε q
  by_cases hq : q = 0
  · subst q
    simp
    exact hK.le
  · let B : Set T4 := Metric.ball q (2 * ‖q‖)
    let f : T4 → ℝ := fun u =>
      reductionRegionThreeKernel q
        (fun v =>
          invSqKer v *
            primitiveSupportIndicator
              supportConstant ε v) u
    let g : T4 → ℝ := fun u =>
      B.indicator
        (fun v =>
          9 * invSqKer q * invSqKer (q - v)) u
    have hB : MeasurableSet B := measurableSet_ball
    have hf : Integrable f paperMeasure := by
      dsimp only [f]
      exact integrable_reductionRegionThreeLocal hq
    have hg : Integrable g paperMeasure := by
      dsimp only [g]
      exact
        ((integrable_invSqKer_sub_left q).const_mul
          (9 * invSqKer q)).indicator hB
    have hpoint : ∀ u, f u ≤ g u := by
      intro u
      unfold f reductionRegionThreeKernel
      split_ifs with hregion
      · have huB :
            u ∈ B :=
          (r322RegionThree_geometry hq hregion).1
        rw [show g u =
            9 * invSqKer q * invSqKer (q - u) by
          simp [g, huB]]
        have huKer :=
          invSqKer_le_nine_mul_regionThree
            hq hregion
        have hind :
            primitiveSupportIndicator
                supportConstant ε u ≤ 1 := by
          unfold primitiveSupportIndicator
          split_ifs <;> norm_num
        calc
          invSqKer (q - u) *
                (invSqKer u *
                  primitiveSupportIndicator
                    supportConstant ε u) ≤
              invSqKer (q - u) *
                (invSqKer u * 1) := by
            apply mul_le_mul_of_nonneg_left _
              (invSqKer_nonneg (q - u))
            exact mul_le_mul_of_nonneg_left hind
              (invSqKer_nonneg u)
          _ ≤ invSqKer (q - u) *
                (9 * invSqKer q) :=
            mul_le_mul_of_nonneg_left
              (by simpa only [mul_one] using huKer)
              (invSqKer_nonneg (q - u))
          _ = 9 * invSqKer q *
                invSqKer (q - u) := by ring
      · exact Set.indicator_nonneg
          (fun v _ =>
            mul_nonneg
              (mul_nonneg (by norm_num)
                (invSqKer_nonneg q))
              (invSqKer_nonneg (q - v))) u
    have hint :
        (∫ u, f u ∂paperMeasure) ≤
          36 * Cker := by
      calc
        (∫ u, f u ∂paperMeasure) ≤
            ∫ u, g u ∂paperMeasure :=
          integral_mono hf hg hpoint
        _ = 9 * invSqKer q *
              invSqKerBallIntegral q (2 * ‖q‖) := by
          dsimp only [g]
          rw [integral_indicator hB, integral_const_mul]
          rfl
        _ ≤ 9 * invSqKer q *
              (Cker * (2 * ‖q‖) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (hker q (2 * ‖q‖) (by positivity))
            (mul_nonneg (by norm_num)
              (invSqKer_nonneg q))
        _ = 36 * Cker *
              (‖q‖ ^ 2 * invSqKer q) := by ring
        _ ≤ 36 * Cker * 1 :=
          mul_le_mul_of_nonneg_left
            (sq_norm_mul_invSqKer_le_one_r322 q)
            (mul_nonneg (by norm_num) hCker.le)
        _ = 36 * Cker := by ring
    unfold r322RegionThreeLocalMoment
    exact hint.trans (by
      dsimp only [K]
      linarith)

/-- The regularized inner Green integral is controlled by the radial
quadratic profile at the external variable. -/
theorem exists_r322RegionThreeRegularMoment_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ε : ℝ) (q : T4), 0 < ε →
        r322RegionThreeRegularMoment ε q ≤
          K * torusDistSq q *
            (torusDistSq q + ε ^ 2)⁻¹ ^ 3 := by
  obtain ⟨Cker, hCker, hker⟩ :=
    invSqKerBallIntegral_le
  let K : ℝ := 2916 * Cker + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro ε q hε
  by_cases hq : q = 0
  · subst q
    rw [r322RegionThreeRegularMoment_zero]
    have hzero : torusDistSq (0 : T4) = 0 :=
      (torusDistSq_eq_zero_iff 0).mpr rfl
    rw [hzero]
    positivity
  · let B : Set T4 := Metric.ball q (2 * ‖q‖)
    let f : T4 → ℝ := fun u =>
      reductionRegionThreeKernel q
        (regularizedInvCube ε) u
    let g : T4 → ℝ := fun u =>
      B.indicator
        (fun v =>
          (729 *
            (torusDistSq q + ε ^ 2)⁻¹ ^ 3) *
              invSqKer (q - v)) u
    have hB : MeasurableSet B := measurableSet_ball
    have hf : Integrable f paperMeasure := by
      dsimp only [f]
      exact integrable_reductionRegionThreeRegular hε q
    have hg : Integrable g paperMeasure := by
      dsimp only [g]
      exact
        ((integrable_invSqKer_sub_left q).const_mul
          (729 *
            (torusDistSq q + ε ^ 2)⁻¹ ^ 3))
        |>.indicator hB
    have hpoint : ∀ u, f u ≤ g u := by
      intro u
      unfold f reductionRegionThreeKernel
      split_ifs with hregion
      · have huB :
            u ∈ B :=
          (r322RegionThree_geometry hq hregion).1
        rw [show g u =
            (729 *
              (torusDistSq q + ε ^ 2)⁻¹ ^ 3) *
                invSqKer (q - u) by
          simp [g, huB]]
        exact
          (mul_le_mul_of_nonneg_left
            (regularizedInvCube_le_regionThree
              hε hq hregion)
            (invSqKer_nonneg (q - u))).trans_eq
              (by ring)
      · exact Set.indicator_nonneg
          (fun v _ =>
            mul_nonneg
              (mul_nonneg (by norm_num)
                (pow_nonneg
                  (inv_nonneg.mpr
                    (add_nonneg
                      (torusDistSq_nonneg q)
                      (sq_nonneg ε))) 3))
              (invSqKer_nonneg (q - v))) u
    have hint :
        (∫ u, f u ∂paperMeasure) ≤
          2916 * Cker * torusDistSq q *
            (torusDistSq q + ε ^ 2)⁻¹ ^ 3 := by
      calc
        (∫ u, f u ∂paperMeasure) ≤
            ∫ u, g u ∂paperMeasure :=
          integral_mono hf hg hpoint
        _ = (729 *
                (torusDistSq q + ε ^ 2)⁻¹ ^ 3) *
              invSqKerBallIntegral q (2 * ‖q‖) := by
          dsimp only [g]
          rw [integral_indicator hB, integral_const_mul]
          rfl
        _ ≤ (729 *
                (torusDistSq q + ε ^ 2)⁻¹ ^ 3) *
              (Cker * (2 * ‖q‖) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (hker q (2 * ‖q‖) (by positivity))
            (mul_nonneg (by norm_num)
              (pow_nonneg
                (inv_nonneg.mpr
                  (add_nonneg
                    (torusDistSq_nonneg q)
                    (sq_nonneg ε))) 3))
        _ = 2916 * Cker * ‖q‖ ^ 2 *
              (torusDistSq q + ε ^ 2)⁻¹ ^ 3 := by
          ring
        _ ≤ 2916 * Cker * torusDistSq q *
              (torusDistSq q + ε ^ 2)⁻¹ ^ 3 := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left
              (sq_norm_le_torusDistSq q)
              (mul_nonneg (by norm_num) hCker.le)
          · exact pow_nonneg
              (inv_nonneg.mpr
                (add_nonneg (torusDistSq_nonneg q)
                  (sq_nonneg ε))) 3
    unfold r322RegionThreeRegularMoment
    exact hint.trans (by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · dsimp only [K]
          linarith
        · exact torusDistSq_nonneg q
      · exact pow_nonneg
          (inv_nonneg.mpr
            (add_nonneg (torusDistSq_nonneg q)
              (sq_nonneg ε))) 3)

/-- Full outer density of the last crude region. -/
def r322RegionThreeDensity
    (C lam ε supportConstant : ℝ) (n : ℕ)
    (q : T4) : ℝ :=
  (C * lam) ^ (2 * n) *
    (((ε⁻¹) ^ 4 / |Real.log ε|) *
        r322RegionThreeLocalMoment supportConstant ε q +
      (1 / |Real.log ε| ^ 2) *
        r322RegionThreeRegularMoment ε q)

theorem measurable_r322RegionThreeDensity
    (C lam ε supportConstant : ℝ) (n : ℕ) :
    Measurable
      (r322RegionThreeDensity
        C lam ε supportConstant n) := by
  unfold r322RegionThreeDensity
  exact measurable_const.mul
    ((measurable_const.mul
        (measurable_r322RegionThreeLocalMoment
          supportConstant ε)).add
      (measurable_const.mul
        (measurable_r322RegionThreeRegularMoment ε)))

theorem r322RegionThreeDensity_nonneg
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (ε supportConstant : ℝ) (n : ℕ) (q : T4) :
    0 ≤ r322RegionThreeDensity
      C lam ε supportConstant n q := by
  unfold r322RegionThreeDensity
  exact mul_nonneg
    (pow_nonneg (mul_nonneg hC hlam) _)
    (add_nonneg
      (mul_nonneg (by positivity)
        (r322RegionThreeLocalMoment_nonneg
          supportConstant ε q))
      (mul_nonneg (by positivity)
        (r322RegionThreeRegularMoment_nonneg ε q)))

/-- The split expression is exactly the region-restricted primitive
majorant with the inner Green factor. -/
theorem r322RegionThreeDensity_eq_integral
    (C lam ε supportConstant : ℝ) (n : ℕ)
    (q : T4) (hε : 0 < ε) :
    r322RegionThreeDensity C lam ε supportConstant n q =
      ∫ u,
        reductionRegionThreeKernel q
          (primitiveKernelMajorant
            C lam ε supportConstant n) u
        ∂paperMeasure := by
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
  rw [hfun, integral_const_mul,
    integral_add (hloc.const_mul a)
      (hreg.const_mul b),
    integral_const_mul, integral_const_mul]
  unfold r322RegionThreeDensity
    r322RegionThreeLocalMoment
    r322RegionThreeRegularMoment
  dsimp only [P, a, b, Jloc, Jreg]

/-- Pointwise two-profile estimate for (4.12). -/
theorem exists_r322RegionThreeDensity_profile_le
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ Knear Kouter : ℝ,
      0 < Knear ∧ 0 < Kouter ∧
      ∀ (C lam ε : ℝ) (n : ℕ) (q : T4),
        0 ≤ C → 0 ≤ lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| →
        r322RegionThreeDensity
            C lam ε supportConstant n q ≤
          (r322ScaleBall
            (3 * supportConstant + 1) ε).indicator
            (fun _ =>
              (C * lam) ^ (2 * n) * Knear *
                (ε⁻¹ ^ (4 : ℕ) /
                  |Real.log ε|)) q +
          (r322CriticalAnnulus ε).indicator
            (fun z =>
              (C * lam) ^ (2 * n) * Kouter *
                (1 / |Real.log ε|) *
                  invSqKer z ^ 2) q := by
  obtain ⟨Klocal, hKlocal, hlocal⟩ :=
    exists_r322RegionThreeLocalMoment_le
  obtain ⟨Kregular, hKregular, hregular⟩ :=
    exists_r322RegionThreeRegularMoment_le
  let Knear : ℝ := Klocal + Kregular
  let Kouter : ℝ := Kregular
  have hKnear : 0 < Knear := by
    dsimp only [Knear]
    positivity
  have hKouter : 0 < Kouter := by
    simpa only [Kouter] using hKregular
  refine
    ⟨Knear, Kouter, hKnear, hKouter, ?_⟩
  intro C lam ε n q hC hlam hε _hε1 hlog
  let L : ℝ := |Real.log ε|
  let P : ℝ := (C * lam) ^ (2 * n)
  let Snear : ℝ := 3 * supportConstant + 1
  have hL : 0 < L :=
    lt_of_lt_of_le zero_lt_one hlog
  have hP : 0 ≤ P :=
    pow_nonneg (mul_nonneg hC hlam) _
  have hLocalMoment :
      r322RegionThreeLocalMoment
          supportConstant ε q ≤ Klocal :=
    hlocal supportConstant ε q
  have hRegularMoment :
      r322RegionThreeRegularMoment ε q ≤
        Kregular * torusDistSq q *
          (torusDistSq q + ε ^ 2)⁻¹ ^ 3 :=
    hregular ε q hε
  have hLocalScaled :
      ((ε⁻¹) ^ 4 / L) *
          r322RegionThreeLocalMoment
            supportConstant ε q ≤
        Klocal * ε⁻¹ ^ (4 : ℕ) / L := by
    calc
      ((ε⁻¹) ^ 4 / L) *
            r322RegionThreeLocalMoment
              supportConstant ε q ≤
          ((ε⁻¹) ^ 4 / L) * Klocal :=
        mul_le_mul_of_nonneg_left hLocalMoment
          (by positivity)
      _ = Klocal * ε⁻¹ ^ (4 : ℕ) / L := by
        ring
  have hfrac :
      1 / L ^ 2 ≤ 1 / L := by
    field_simp [hL.ne']
    nlinarith
  have hinnerMem :
      torusDistSq q ≤ ε ^ 2 →
      q ∈ r322ScaleBall Snear ε := by
    intro hq
    change torusDistSq q ≤ (Snear * ε) ^ 2
    have hSnear : 1 ≤ Snear := by
      dsimp only [Snear]
      linarith
    have hscaled :
        ε ≤ Snear * ε := by
      nlinarith
    exact hq.trans
      (pow_le_pow_left₀ hε.le hscaled 2)
  by_cases hqZero : q = 0
  · subst q
    unfold r322RegionThreeDensity
    rw [r322RegionThreeLocalMoment_zero,
      r322RegionThreeRegularMoment_zero,
      mul_zero, mul_zero, add_zero, mul_zero]
    exact add_nonneg
      (Set.indicator_nonneg
        (fun _ _ =>
          mul_nonneg
            (mul_nonneg hP hKnear.le)
            (by positivity)) 0)
      (Set.indicator_nonneg
        (fun z _ =>
          mul_nonneg
            (mul_nonneg
              (mul_nonneg hP hKouter.le)
              (by positivity))
            (sq_nonneg (invSqKer z))) 0)
  · by_cases hqInner : torusDistSq q ≤ ε ^ 2
    · have hbase :
          (torusDistSq q + ε ^ 2)⁻¹ ≤
            (ε ^ 2)⁻¹ :=
        inv_anti₀ (sq_pos_of_pos hε)
          (le_add_of_nonneg_left
            (torusDistSq_nonneg q))
      have hradial :
          torusDistSq q *
              (torusDistSq q + ε ^ 2)⁻¹ ^ 3 ≤
            ε⁻¹ ^ (4 : ℕ) := by
        calc
          torusDistSq q *
                (torusDistSq q + ε ^ 2)⁻¹ ^ 3 ≤
              ε ^ 2 * ((ε ^ 2)⁻¹ ^ 3) := by
            exact mul_le_mul hqInner
              (pow_le_pow_left₀
                (inv_nonneg.mpr
                  (add_nonneg
                    (torusDistSq_nonneg q)
                    (sq_nonneg ε))) hbase 3)
              (pow_nonneg
                (inv_nonneg.mpr
                  (add_nonneg
                    (torusDistSq_nonneg q)
                    (sq_nonneg ε))) 3)
              (sq_nonneg ε)
          _ = ε⁻¹ ^ (4 : ℕ) := by
            field_simp [hε.ne']
      have hRegularScaled :
          (1 / L ^ 2) *
              r322RegionThreeRegularMoment ε q ≤
            Kregular * ε⁻¹ ^ (4 : ℕ) / L := by
        calc
          (1 / L ^ 2) *
                r322RegionThreeRegularMoment ε q ≤
              (1 / L ^ 2) *
                (Kregular * torusDistSq q *
                  (torusDistSq q + ε ^ 2)⁻¹ ^ 3) :=
            mul_le_mul_of_nonneg_left hRegularMoment
              (by positivity)
          _ ≤ (1 / L ^ 2) *
                (Kregular * ε⁻¹ ^ (4 : ℕ)) := by
            apply mul_le_mul_of_nonneg_left _
              (by positivity)
            simpa only [mul_assoc] using
              (mul_le_mul_of_nonneg_left hradial
                hKregular.le)
          _ = (Kregular * ε⁻¹ ^ (4 : ℕ)) *
                (1 / L ^ 2) := by ring
          _ ≤ (Kregular * ε⁻¹ ^ (4 : ℕ)) *
                (1 / L) :=
            mul_le_mul_of_nonneg_left hfrac
              (mul_nonneg hKregular.le
                (pow_nonneg (inv_nonneg.mpr hε.le) 4))
          _ = Kregular * ε⁻¹ ^ (4 : ℕ) / L := by
            ring
      have hnear : q ∈ r322ScaleBall Snear ε :=
        hinnerMem hqInner
      rw [Set.indicator_of_mem hnear]
      have hinside :
          ((ε⁻¹) ^ 4 / L) *
                r322RegionThreeLocalMoment
                  supportConstant ε q +
              (1 / L ^ 2) *
                r322RegionThreeRegularMoment ε q ≤
            Knear * ε⁻¹ ^ (4 : ℕ) / L := by
        calc
          ((ε⁻¹) ^ 4 / L) *
                  r322RegionThreeLocalMoment
                    supportConstant ε q +
                (1 / L ^ 2) *
                  r322RegionThreeRegularMoment ε q ≤
              Klocal * ε⁻¹ ^ (4 : ℕ) / L +
                Kregular * ε⁻¹ ^ (4 : ℕ) / L :=
            add_le_add hLocalScaled hRegularScaled
          _ = Knear * ε⁻¹ ^ (4 : ℕ) / L := by
            dsimp only [Knear]
            ring
      have hmain :
          r322RegionThreeDensity
              C lam ε supportConstant n q ≤
            P * Knear *
              (ε⁻¹ ^ (4 : ℕ) / L) := by
        unfold r322RegionThreeDensity
        dsimp only [P, L]
        calc
          (C * lam) ^ (2 * n) *
                (((ε⁻¹) ^ 4 / |Real.log ε|) *
                    r322RegionThreeLocalMoment
                      supportConstant ε q +
                  (1 / |Real.log ε| ^ 2) *
                    r322RegionThreeRegularMoment ε q) ≤
              P * (Knear *
                ε⁻¹ ^ (4 : ℕ) / L) :=
            mul_le_mul_of_nonneg_left hinside hP
          _ = P * Knear *
                (ε⁻¹ ^ (4 : ℕ) / L) := by
            ring
      exact le_add_of_le_of_nonneg hmain
        (Set.indicator_nonneg
          (fun z _ =>
            mul_nonneg
              (mul_nonneg
                (mul_nonneg hP hKouter.le)
                (by positivity))
              (sq_nonneg (invSqKer z))) q)
    · have hqOuter :
          ε ^ 2 ≤ torusDistSq q :=
        le_of_not_ge hqInner
      have hqDist : 0 < torusDistSq q :=
        lt_of_lt_of_le (sq_pos_of_pos hε) hqOuter
      have hbase :
          (torusDistSq q + ε ^ 2)⁻¹ ≤
            (torusDistSq q)⁻¹ :=
        inv_anti₀ hqDist
          (le_add_of_nonneg_right (sq_nonneg ε))
      have hradial :
          torusDistSq q *
              (torusDistSq q + ε ^ 2)⁻¹ ^ 3 ≤
            invSqKer q ^ 2 := by
        calc
          torusDistSq q *
                (torusDistSq q + ε ^ 2)⁻¹ ^ 3 ≤
              torusDistSq q *
                (torusDistSq q)⁻¹ ^ 3 :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀
                (inv_nonneg.mpr
                  (add_nonneg
                    (torusDistSq_nonneg q)
                    (sq_nonneg ε))) hbase 3)
              (torusDistSq_nonneg q)
          _ = invSqKer q ^ 2 := by
            unfold invSqKer
            field_simp [hqDist.ne']
      have hRegularScaled :
          (1 / L ^ 2) *
              r322RegionThreeRegularMoment ε q ≤
            (Kregular / L) * invSqKer q ^ 2 := by
        calc
          (1 / L ^ 2) *
                r322RegionThreeRegularMoment ε q ≤
              (1 / L ^ 2) *
                (Kregular * torusDistSq q *
                  (torusDistSq q + ε ^ 2)⁻¹ ^ 3) :=
            mul_le_mul_of_nonneg_left hRegularMoment
              (by positivity)
          _ ≤ (1 / L ^ 2) *
                (Kregular * invSqKer q ^ 2) := by
            apply mul_le_mul_of_nonneg_left _
              (by positivity)
            simpa only [mul_assoc] using
              (mul_le_mul_of_nonneg_left hradial
                hKregular.le)
          _ = (Kregular * invSqKer q ^ 2) *
                (1 / L ^ 2) := by ring
          _ ≤ (Kregular * invSqKer q ^ 2) *
                (1 / L) :=
            mul_le_mul_of_nonneg_left hfrac
              (mul_nonneg hKregular.le
                (sq_nonneg (invSqKer q)))
          _ = (Kregular / L) * invSqKer q ^ 2 := by
            ring
      have hcrit :
          q ∈ r322CriticalAnnulus ε := hqOuter
      by_cases hnear :
          q ∈ r322ScaleBall Snear ε
      · rw [Set.indicator_of_mem hnear,
          Set.indicator_of_mem hcrit]
        unfold r322RegionThreeDensity
        calc
          (C * lam) ^ (2 * n) *
                (((ε⁻¹) ^ 4 / |Real.log ε|) *
                    r322RegionThreeLocalMoment
                      supportConstant ε q +
                  (1 / |Real.log ε| ^ 2) *
                    r322RegionThreeRegularMoment ε q) ≤
              P *
                (Klocal * ε⁻¹ ^ (4 : ℕ) / L +
                  (Kregular / L) * invSqKer q ^ 2) :=
            mul_le_mul_of_nonneg_left
              (add_le_add hLocalScaled hRegularScaled) hP
          _ = P * Klocal *
                (ε⁻¹ ^ (4 : ℕ) / L) +
              P * Kregular * (1 / L) *
                invSqKer q ^ 2 := by ring
          _ ≤ P * Knear *
                (ε⁻¹ ^ (4 : ℕ) / L) +
              P * Kouter * (1 / L) *
                invSqKer q ^ 2 := by
            apply add_le_add
            · have hcoeff : Klocal ≤ Knear := by
                dsimp only [Knear]
                linarith
              calc
                P * Klocal *
                      (ε⁻¹ ^ (4 : ℕ) / L) =
                    (P *
                      (ε⁻¹ ^ (4 : ℕ) / L)) *
                        Klocal := by ring
                _ ≤ (P *
                      (ε⁻¹ ^ (4 : ℕ) / L)) *
                        Knear :=
                  mul_le_mul_of_nonneg_left hcoeff
                    (mul_nonneg hP (by positivity))
                _ = P * Knear *
                      (ε⁻¹ ^ (4 : ℕ) / L) := by ring
            · dsimp only [Kouter]
              exact le_rfl
      · rw [Set.indicator_of_notMem hnear,
          Set.indicator_of_mem hcrit]
        have hLocalZero :=
          r322RegionThreeLocalMoment_eq_zero_of_not_scale
            hsupport hε
            (show q ∉ r322ScaleBall
                (3 * supportConstant + 1) ε by
              simpa only [Snear] using hnear)
        unfold r322RegionThreeDensity
        rw [hLocalZero, mul_zero, zero_add]
        calc
          (C * lam) ^ (2 * n) *
                ((1 / |Real.log ε| ^ 2) *
                  r322RegionThreeRegularMoment ε q) ≤
              P * ((Kregular / L) *
                invSqKer q ^ 2) :=
            mul_le_mul_of_nonneg_left
              hRegularScaled hP
          _ = P * Kouter * (1 / L) *
                invSqKer q ^ 2 := by
            dsimp only [Kouter]
            ring
          _ = 0 + P * Kouter * (1 / L) *
                invSqKer q ^ 2 := by ring

/-- The full (4.12) density preserves the inverse-square Green
majorant after the outer integration. -/
theorem exists_r322RegionThreeDensity_convolution_le
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C lam ε : ℝ) (n : ℕ) (x : T4),
        0 ≤ C → 0 ≤ lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| → x ≠ 0 →
        (∫ q,
          invSqKer (x - q) *
            r322RegionThreeDensity
              C lam ε supportConstant n q
          ∂paperMeasure) ≤
          (C * lam) ^ (2 * n) * K * invSqKer x := by
  obtain
    ⟨Knear, Kouter, hKnear, hKouter, hprofile⟩ :=
      exists_r322RegionThreeDensity_profile_le hsupport
  obtain ⟨Kscale, hKscale, hscale⟩ :=
    exists_r322ScaleBall_convolution_le
      (show 0 < 3 * supportConstant + 1 by
        linarith)
  obtain ⟨Kcritical, hKcritical, hcritical⟩ :=
    exists_r322CriticalAnnulus_convolution_le
  let K : ℝ :=
    Knear * Kscale + Kouter * Kcritical
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro C lam ε n x hC hlam hε hε1 hlog hx
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
  have hL : 0 < L :=
    lt_of_lt_of_le zero_lt_one hlog
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
  have hf : Integrable f paperMeasure := by
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
  have hg₁Int :
      (∫ q, g₁ q ∂paperMeasure) ≤
        P * Knear * Kscale * invSqKer x := by
    have hs :=
      hscale ε x hε hx
    dsimp only [g₁]
    rw [integral_indicator hSin, integral_const_mul]
    calc
      P * Knear *
            (ε⁻¹ ^ (4 : ℕ) / L) *
              ∫ q in Sin, invSqKer (x - q)
                ∂paperMeasure =
          (P * Knear / L) *
            (ε⁻¹ ^ (4 : ℕ) *
              ∫ q in Sin, invSqKer (x - q)
                ∂paperMeasure) := by ring
      _ ≤ (P * Knear / L) *
            (Kscale * invSqKer x) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [Sin] using hs)
          (by positivity)
      _ ≤ (P * Knear) *
            (Kscale * invSqKer x) := by
        apply mul_le_mul_of_nonneg_right _
          (mul_nonneg hKscale.le (invSqKer_nonneg x))
        simpa only [L] using
          (div_le_self
            (mul_nonneg hP hKnear.le) hlog)
      _ = P * Knear * Kscale * invSqKer x := by
        ring
  have hg₂Int :
      (∫ q, g₂ q ∂paperMeasure) ≤
        P * Kouter * Kcritical * invSqKer x := by
    have hc :=
      hcritical ε x hε hε1 hlog hx
    dsimp only [g₂]
    rw [integral_indicator hSout, integral_const_mul,
      integral_const_mul]
    calc
      P * Kouter *
            ((1 / L) *
              ∫ q in Sout,
                invSqKer (x - q) * invSqKer q ^ 2
                  ∂paperMeasure) ≤
          P * Kouter *
            (Kcritical * invSqKer x) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [L, Sout] using hc)
          (mul_nonneg hP hKouter.le)
      _ = P * Kouter * Kcritical * invSqKer x := by
        ring
  calc
    (∫ q, f q ∂paperMeasure) ≤
        ∫ q, g₁ q + g₂ q ∂paperMeasure :=
      integral_mono hf (hg₁.add hg₂) hpoint
    _ = (∫ q, g₁ q ∂paperMeasure) +
          ∫ q, g₂ q ∂paperMeasure :=
      integral_add hg₁ hg₂
    _ ≤ P * Knear * Kscale * invSqKer x +
        P * Kouter * Kcritical * invSqKer x :=
      add_le_add hg₁Int hg₂Int
    _ = (C * lam) ^ (2 * n) * K * invSqKer x := by
      dsimp only [P, K]
      ring

end

end Anderson4D
