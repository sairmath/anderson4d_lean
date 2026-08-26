import Anderson4D.DetParametrix.Paper41_Renorm.R322ScaleInvSq
import Anderson4D.Continuum.PrimitiveMajorantIntegral

/-!
# The crude Green profile in region (4.11)

Write `q = z - y` and `u = z - w`.  The first non-Taylor region has
`‖q‖ ≤ 2 ‖u‖`; after taking the crude Green bound, its density is
`invSqKer q` times the primitive-kernel mass on that region.

The local part of Proposition 4.1 is supported at `q = O(ε)` and has
size `ε⁻² / |log ε|`.  For the regularized part, the same bound holds
at `q = O(ε)`, while outside that ball one inverse-square factor is
extracted and the remaining critical square contributes one logarithm.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set

/-- Restriction to the crude `z-y` region in (4.11). -/
def reductionRegionTwoKernel
    (q : T4) (J : T4 → ℝ) (u : T4) : ℝ :=
  if ‖q‖ ≤ 2 * ‖u‖ then J u else 0

theorem measurableSet_reductionRegionTwo (q : T4) :
    MeasurableSet {u : T4 | ‖q‖ ≤ 2 * ‖u‖} :=
  measurableSet_le measurable_const
    (measurable_const.mul measurable_norm)

theorem reductionRegionTwoKernel_eq_indicator
    (q : T4) (J : T4 → ℝ) :
    reductionRegionTwoKernel q J =
      {u : T4 | ‖q‖ ≤ 2 * ‖u‖}.indicator J := by
  funext u
  unfold reductionRegionTwoKernel
  by_cases hu : ‖q‖ ≤ 2 * ‖u‖
  · simp [hu]
  · simp [hu]

theorem measurable_reductionRegionTwoKernel
    (q : T4) {J : T4 → ℝ} (hJ : Measurable J) :
    Measurable (reductionRegionTwoKernel q J) := by
  rw [reductionRegionTwoKernel_eq_indicator]
  exact hJ.indicator (measurableSet_reductionRegionTwo q)

theorem integrable_reductionRegionTwoKernel
    (q : T4) {J : T4 → ℝ}
    (hJ : Integrable J paperMeasure) :
    Integrable (reductionRegionTwoKernel q J)
      paperMeasure := by
  rw [reductionRegionTwoKernel_eq_indicator]
  exact hJ.indicator (measurableSet_reductionRegionTwo q)

theorem measurable_reductionRegionTwoKernel_joint
    {J : T4 → ℝ} (hJ : Measurable J) :
    Measurable fun p : T4 × T4 =>
      reductionRegionTwoKernel p.1 J p.2 := by
  unfold reductionRegionTwoKernel
  exact Measurable.ite
    (measurableSet_le measurable_fst.norm
      (measurable_const.mul measurable_snd.norm))
    (hJ.comp measurable_snd) measurable_const

/-- Local-support primitive mass left after integrating `w`. -/
def r322RegionTwoLocalMoment
    (supportConstant ε : ℝ) (q : T4) : ℝ :=
  ∫ u,
    reductionRegionTwoKernel q
      (fun v =>
        invSqKer v *
          primitiveSupportIndicator supportConstant ε v) u
    ∂paperMeasure

/-- Regularized primitive mass left after integrating `w`. -/
def r322RegionTwoRegularMoment
    (ε : ℝ) (q : T4) : ℝ :=
  ∫ u,
    reductionRegionTwoKernel q
      (regularizedInvCube ε) u
    ∂paperMeasure

theorem measurable_r322RegionTwoLocalMoment
    (supportConstant ε : ℝ) :
    Measurable
      (r322RegionTwoLocalMoment supportConstant ε) := by
  unfold r322RegionTwoLocalMoment
  rw [paperMeasure_eq_volume]
  exact
    (measurable_reductionRegionTwoKernel_joint
      (measurable_invSqKer.mul
        (measurable_primitiveSupportIndicator
          supportConstant ε)))
      |>.stronglyMeasurable.integral_prod_right.measurable

theorem measurable_r322RegionTwoRegularMoment
    (ε : ℝ) :
    Measurable (r322RegionTwoRegularMoment ε) := by
  unfold r322RegionTwoRegularMoment
  rw [paperMeasure_eq_volume]
  exact
    (measurable_reductionRegionTwoKernel_joint
      (measurable_regularizedInvCube ε))
      |>.stronglyMeasurable.integral_prod_right.measurable

theorem r322RegionTwoLocalMoment_nonneg
    (supportConstant ε : ℝ) (q : T4) :
    0 ≤ r322RegionTwoLocalMoment supportConstant ε q := by
  unfold r322RegionTwoLocalMoment
  exact integral_nonneg fun u => by
    unfold reductionRegionTwoKernel
    split_ifs
    · exact mul_nonneg (invSqKer_nonneg _)
        (primitiveSupportIndicator_nonneg _ _ _)
    · exact le_rfl

theorem r322RegionTwoRegularMoment_nonneg
    (ε : ℝ) (q : T4) :
    0 ≤ r322RegionTwoRegularMoment ε q := by
  unfold r322RegionTwoRegularMoment
  exact integral_nonneg fun u => by
    unfold reductionRegionTwoKernel
    split_ifs
    · exact regularizedInvCube_nonneg _ _
    · exact le_rfl

theorem r322RegionTwoLocalMoment_le_total
    {supportConstant ε : ℝ} (q : T4) :
    r322RegionTwoLocalMoment supportConstant ε q ≤
      ∫ u,
        invSqKer u *
          primitiveSupportIndicator supportConstant ε u
        ∂paperMeasure := by
  unfold r322RegionTwoLocalMoment
  exact integral_mono
    (integrable_reductionRegionTwoKernel q
      (integrable_invSqKer_mul_primitiveSupportIndicator
        supportConstant ε))
    (integrable_invSqKer_mul_primitiveSupportIndicator
      supportConstant ε)
    (fun u => by
      unfold reductionRegionTwoKernel
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (invSqKer_nonneg _)
          (primitiveSupportIndicator_nonneg _ _ _))

theorem r322RegionTwoRegularMoment_le_total
    {ε : ℝ} (hε : 0 < ε) (q : T4) :
    r322RegionTwoRegularMoment ε q ≤
      ∫ u, regularizedInvCube ε u ∂paperMeasure := by
  unfold r322RegionTwoRegularMoment
  exact integral_mono
    (integrable_reductionRegionTwoKernel q
      (integrable_regularizedInvCube ε hε))
    (integrable_regularizedInvCube ε hε)
    (fun u => by
      unfold reductionRegionTwoKernel
      split_ifs
      · exact le_rfl
      · exact regularizedInvCube_nonneg _ _)

/-- The local primitive contribution can occur only when the outer
variable is itself at primitive scale. -/
theorem r322RegionTwoLocalMoment_eq_zero_of_not_scale
    {supportConstant ε : ℝ}
    (hsupport : 0 < supportConstant) (hε : 0 < ε)
    {q : T4}
    (hq :
      q ∉ r322ScaleBall
        (4 * supportConstant + 1) ε) :
    r322RegionTwoLocalMoment supportConstant ε q = 0 := by
  unfold r322RegionTwoLocalMoment
  have hfun :
      reductionRegionTwoKernel q
          (fun v =>
            invSqKer v *
              primitiveSupportIndicator
                supportConstant ε v) =
        fun _ => 0 := by
    funext u
    unfold reductionRegionTwoKernel
    split_ifs with hregion
    · have huNot :
        ¬torusDistSq u ≤
          (supportConstant * ε) ^ 2 := by
        intro hu
        have hqNormSq :
          ‖q‖ ^ 2 ≤ (2 * ‖u‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg q) hregion 2
        have hqDist :
          torusDistSq q ≤
            (4 * supportConstant * ε) ^ 2 := by
          calc
            torusDistSq q ≤ 4 * ‖q‖ ^ 2 :=
              torusDistSq_le_four_mul_sq_norm q
            _ ≤ 4 * (2 * ‖u‖) ^ 2 :=
              mul_le_mul_of_nonneg_left hqNormSq
                (by norm_num)
            _ ≤ 16 * torusDistSq u := by
              nlinarith [sq_norm_le_torusDistSq u]
            _ ≤ 16 * (supportConstant * ε) ^ 2 := by
              exact mul_le_mul_of_nonneg_left hu
                (by norm_num)
            _ = (4 * supportConstant * ε) ^ 2 := by
              ring
        have hnear :
          q ∈ r322ScaleBall
            (4 * supportConstant + 1) ε := by
          change torusDistSq q ≤
            ((4 * supportConstant + 1) * ε) ^ 2
          have hcoeff :
            4 * supportConstant ≤
              4 * supportConstant + 1 := by linarith
          have hscaled :
            0 ≤ 4 * supportConstant * ε := by positivity
          have hscaled' :
            4 * supportConstant * ε ≤
              (4 * supportConstant + 1) * ε := by
            nlinarith
          exact hqDist.trans
            (pow_le_pow_left₀ hscaled hscaled' 2)
        exact hq hnear
      dsimp only
      rw [primitiveSupportIndicator_eq_zero huNot,
        mul_zero]
    · rfl
  rw [hfun]
  simp

/-- The region condition converts outer scale in `q` into an annular
lower bound for the primitive variable. -/
theorem r322RegionTwo_torusDistSq_le
    {q u : T4} (hregion : ‖q‖ ≤ 2 * ‖u‖) :
    torusDistSq q ≤ 16 * torusDistSq u := by
  calc
    torusDistSq q ≤ 4 * ‖q‖ ^ 2 :=
      torusDistSq_le_four_mul_sq_norm q
    _ ≤ 4 * (2 * ‖u‖) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg q) hregion 2)
        (by norm_num)
    _ ≤ 16 * torusDistSq u := by
      nlinarith [sq_norm_le_torusDistSq u]

theorem regularizedInvCube_le_regionTwo_outer
    {ε : ℝ} (hε : 0 < ε)
    {q u : T4} (hq : ε ^ 2 ≤ torusDistSq q)
    (hregion : ‖q‖ ≤ 2 * ‖u‖) :
    regularizedInvCube ε u ≤
      16 * invSqKer q * invSqKer u ^ 2 := by
  have hqu :=
    r322RegionTwo_torusDistSq_le hregion
  have hqDist : 0 < torusDistSq q :=
    lt_of_lt_of_le (sq_pos_of_pos hε) hq
  have huDist : 0 < torusDistSq u := by
    nlinarith
  have hinv :
      invSqKer u ≤ 16 * invSqKer q := by
    unfold invSqKer
    rw [le_mul_inv_iff₀ hqDist, inv_mul_eq_div,
      div_le_iff₀ huDist]
    exact hqu
  have hbase :
      (torusDistSq u + ε ^ 2)⁻¹ ≤
        (torusDistSq u)⁻¹ :=
    inv_anti₀ huDist
      (le_add_of_nonneg_right (sq_nonneg ε))
  unfold regularizedInvCube
  calc
    (torusDistSq u + ε ^ 2)⁻¹ ^ 3 ≤
        (torusDistSq u)⁻¹ ^ 3 :=
      pow_le_pow_left₀
        (inv_nonneg.mpr
          (add_nonneg (torusDistSq_nonneg u)
            (sq_nonneg ε))) hbase 3
    _ = invSqKer u * invSqKer u ^ 2 := by
      unfold invSqKer
      ring
    _ ≤ (16 * invSqKer q) * invSqKer u ^ 2 :=
      mul_le_mul_of_nonneg_right hinv
        (sq_nonneg (invSqKer u))
    _ = 16 * invSqKer q * invSqKer u ^ 2 := by
      ring

/-- Outside primitive scale, the regularized region-(4.11) mass gains
one inverse-square factor and loses exactly one logarithm. -/
theorem exists_r322RegionTwoRegularMoment_outer_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ε : ℝ) (q : T4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        ε ^ 2 ≤ torusDistSq q →
        r322RegionTwoRegularMoment ε q ≤
          K * |Real.log ε| * invSqKer q := by
  obtain ⟨Cann, hCann, hann⟩ :=
    setIntegral_invSqKer_sq_annulus_le
  let K : ℝ := 80 * Cann + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro ε q hε hε1 hlog hq
  let L : ℝ := |Real.log ε|
  let R : Set T4 := {u | ‖q‖ ≤ 2 * ‖u‖}
  let A : Set T4 := r322CriticalAnnulus (ε / 4)
  have hR : MeasurableSet R :=
    measurableSet_le measurable_const
      (measurable_const.mul measurable_norm)
  have hA : MeasurableSet A :=
    measurableSet_r322CriticalAnnulus (ε / 4)
  have hsubset : R ⊆ A := by
    intro u hu
    change (ε / 4) ^ 2 ≤ torusDistSq u
    have hqu :=
      r322RegionTwo_torusDistSq_le hu
    nlinarith
  have hupperInt :
      IntegrableOn
        (fun u : T4 =>
          16 * invSqKer q * invSqKer u ^ 2)
        R paperMeasure :=
    (((integrableOn_invSqKer_sq_r322CriticalAnnulus
      (show 0 < ε / 4 by positivity)).mono_set hsubset)
      |>.const_mul (16 * invSqKer q))
  have hsourceInt :
      IntegrableOn (regularizedInvCube ε) R
        paperMeasure :=
    (integrable_regularizedInvCube ε hε).integrableOn
  have hraw :
      r322RegionTwoRegularMoment ε q ≤
        16 * invSqKer q *
          ∫ u in A, invSqKer u ^ 2
            ∂paperMeasure := by
    unfold r322RegionTwoRegularMoment
    rw [reductionRegionTwoKernel_eq_indicator,
      integral_indicator hR]
    change
      (∫ u in R, regularizedInvCube ε u
        ∂paperMeasure) ≤ _
    calc
      (∫ u in R, regularizedInvCube ε u
          ∂paperMeasure) ≤
          ∫ u in R,
            16 * invSqKer q * invSqKer u ^ 2
              ∂paperMeasure := by
        exact setIntegral_mono_on
          hsourceInt hupperInt hR
          (fun u hu =>
            regularizedInvCube_le_regionTwo_outer
              hε hq hu)
      _ = 16 * invSqKer q *
            ∫ u in R, invSqKer u ^ 2
              ∂paperMeasure := by
        rw [integral_const_mul]
      _ ≤ 16 * invSqKer q *
            ∫ u in A, invSqKer u ^ 2
              ∂paperMeasure := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (by norm_num) (invSqKer_nonneg q))
        exact setIntegral_mono_set
          (integrableOn_invSqKer_sq_r322CriticalAnnulus
            (show 0 < ε / 4 by positivity))
          (.of_forall fun u => sq_nonneg (invSqKer u))
          (.of_forall hsubset)
  have hannulus :
      (∫ u in A, invSqKer u ^ 2
          ∂paperMeasure) ≤
        Cann * (1 + |Real.log (ε / 4)|) := by
    simpa only [A, r322CriticalAnnulus] using
      hann (ε / 4) (by positivity)
        (by linarith)
  have hlogFour : Real.log 4 ≤ 3 := by
    have h :=
      Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < 4 by norm_num)
    linarith
  have hlogFourNonneg : 0 ≤ Real.log 4 :=
    Real.log_nonneg (by norm_num)
  have habs :
      |Real.log (ε / 4)| ≤ L + 3 := by
    rw [Real.log_div hε.ne' (by norm_num)]
    calc
      |Real.log ε - Real.log 4| ≤
          |Real.log ε| + |Real.log 4| :=
        abs_sub _ _
      _ = L + Real.log 4 := by
        rw [abs_of_nonneg hlogFourNonneg]
      _ ≤ L + 3 := by linarith
  have hratio :
      1 + |Real.log (ε / 4)| ≤ 5 * L := by
    dsimp only [L]
    calc
      1 + |Real.log (ε / 4)| ≤
          1 + (|Real.log ε| + 3) := by
        linarith
      _ ≤ 5 * |Real.log ε| := by
        linarith
  calc
    r322RegionTwoRegularMoment ε q ≤
        16 * invSqKer q *
          ∫ u in A, invSqKer u ^ 2
            ∂paperMeasure := hraw
    _ ≤ 16 * invSqKer q *
          (Cann * (1 + |Real.log (ε / 4)|)) :=
      mul_le_mul_of_nonneg_left hannulus
        (mul_nonneg (by norm_num) (invSqKer_nonneg q))
    _ ≤ 16 * invSqKer q * (Cann * (5 * L)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hratio hCann.le)
        (mul_nonneg (by norm_num) (invSqKer_nonneg q))
    _ = 80 * Cann * L * invSqKer q := by ring
    _ ≤ K * L * invSqKer q := by
      apply mul_le_mul_of_nonneg_right _
        (invSqKer_nonneg q)
      apply mul_le_mul_of_nonneg_right _
        (abs_nonneg (Real.log ε))
      dsimp only [K]
      linarith

/-- Full outer density of the (4.11) contribution, split according to
the two explicit summands of Proposition 4.1. -/
def r322RegionTwoDensity
    (C lam ε supportConstant : ℝ) (n : ℕ)
    (q : T4) : ℝ :=
  invSqKer q * (C * lam) ^ (2 * n) *
    (((ε⁻¹) ^ 4 / |Real.log ε|) *
        r322RegionTwoLocalMoment supportConstant ε q +
      (1 / |Real.log ε| ^ 2) *
        r322RegionTwoRegularMoment ε q)

theorem measurable_r322RegionTwoDensity
    (C lam ε supportConstant : ℝ) (n : ℕ) :
    Measurable
      (r322RegionTwoDensity
        C lam ε supportConstant n) := by
  unfold r322RegionTwoDensity
  exact (measurable_invSqKer.mul measurable_const).mul
    ((measurable_const.mul
        (measurable_r322RegionTwoLocalMoment
          supportConstant ε)).add
      (measurable_const.mul
        (measurable_r322RegionTwoRegularMoment ε)))

theorem r322RegionTwoDensity_nonneg
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (ε supportConstant : ℝ) (n : ℕ) (q : T4) :
    0 ≤ r322RegionTwoDensity
      C lam ε supportConstant n q := by
  unfold r322RegionTwoDensity
  exact mul_nonneg
    (mul_nonneg (invSqKer_nonneg q)
      (pow_nonneg (mul_nonneg hC hlam) _))
    (add_nonneg
      (mul_nonneg (by positivity)
        (r322RegionTwoLocalMoment_nonneg
          supportConstant ε q))
      (mul_nonneg (by positivity)
        (r322RegionTwoRegularMoment_nonneg ε q)))

/-- The split density is exactly `invSqKer q` times the restricted
primitive majorant, rather than a new comparison kernel. -/
theorem r322RegionTwoDensity_eq_integral
    (C lam ε supportConstant : ℝ) (n : ℕ)
    (q : T4) (hε : 0 < ε) :
    r322RegionTwoDensity C lam ε supportConstant n q =
      invSqKer q *
        ∫ u,
          reductionRegionTwoKernel q
            (primitiveKernelMajorant
              C lam ε supportConstant n) u
          ∂paperMeasure := by
  let A : ℝ := (C * lam) ^ (2 * n)
  let a : ℝ := (ε⁻¹) ^ 4 / |Real.log ε|
  let b : ℝ := 1 / |Real.log ε| ^ 2
  let Jloc : T4 → ℝ := fun u =>
    invSqKer u *
      primitiveSupportIndicator supportConstant ε u
  let Jreg : T4 → ℝ := regularizedInvCube ε
  have hloc : Integrable
      (reductionRegionTwoKernel q Jloc) paperMeasure :=
    integrable_reductionRegionTwoKernel q
      (integrable_invSqKer_mul_primitiveSupportIndicator
        supportConstant ε)
  have hreg : Integrable
      (reductionRegionTwoKernel q Jreg) paperMeasure :=
    integrable_reductionRegionTwoKernel q
      (integrable_regularizedInvCube ε hε)
  have hfun :
      reductionRegionTwoKernel q
          (primitiveKernelMajorant
            C lam ε supportConstant n) =
        fun u =>
          A *
            (a * reductionRegionTwoKernel q Jloc u +
              b * reductionRegionTwoKernel q Jreg u) := by
    funext u
    unfold reductionRegionTwoKernel
    split_ifs
    · unfold primitiveKernelMajorant Jloc Jreg
        regularizedInvCube
      dsimp only [A, a, b]
      ring
    · ring
  rw [hfun, integral_const_mul,
    integral_add (hloc.const_mul a)
      (hreg.const_mul b),
    integral_const_mul, integral_const_mul]
  unfold r322RegionTwoDensity
    r322RegionTwoLocalMoment
    r322RegionTwoRegularMoment
  dsimp only [A, a, b, Jloc, Jreg]
  ring

/-- Pointwise two-profile estimate for (4.11): a scale-local
inverse-square density plus the logarithmically normalized critical
density. -/
theorem exists_r322RegionTwoDensity_profile_le
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ Knear Kouter : ℝ,
      0 < Knear ∧ 0 < Kouter ∧
      ∀ (C lam ε : ℝ) (n : ℕ) (q : T4),
        0 ≤ C → 0 ≤ lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| →
        r322RegionTwoDensity
            C lam ε supportConstant n q ≤
          (r322ScaleBall
            (4 * supportConstant + 1) ε).indicator
            (fun z =>
              (C * lam) ^ (2 * n) * Knear *
                (ε⁻¹ ^ (2 : ℕ) /
                  |Real.log ε|) * invSqKer z) q +
          (r322CriticalAnnulus ε).indicator
            (fun z =>
              (C * lam) ^ (2 * n) * Kouter *
                (1 / |Real.log ε|) *
                  invSqKer z ^ 2) q := by
  obtain ⟨Clocal, hClocal, hlocal⟩ :=
    exists_integral_invSqKer_mul_primitiveSupportIndicator_le
  obtain ⟨Creg, hCreg, hreg⟩ :=
    integral_regularizedInvCube_le
  obtain ⟨Kouter, hKouter, houter⟩ :=
    exists_r322RegionTwoRegularMoment_outer_le
  let Knear : ℝ :=
    Clocal * supportConstant ^ 2 + Creg
  have hKnear : 0 < Knear := by
    dsimp only [Knear]
    positivity
  refine
    ⟨Knear, Kouter, hKnear, hKouter, ?_⟩
  intro C lam ε n q hC hlam hε hε1 hlog
  let L : ℝ := |Real.log ε|
  let P : ℝ := (C * lam) ^ (2 * n)
  let Snear : ℝ := 4 * supportConstant + 1
  have hL : 0 < L :=
    lt_of_lt_of_le zero_lt_one hlog
  have hP : 0 ≤ P :=
    pow_nonneg (mul_nonneg hC hlam) _
  have hLocalMoment :
      r322RegionTwoLocalMoment
          supportConstant ε q ≤
        Clocal * supportConstant ^ 2 * ε ^ 2 := by
    exact
      (r322RegionTwoLocalMoment_le_total q).trans
        (hlocal supportConstant ε hsupport hε)
  have hRegularMoment :
      r322RegionTwoRegularMoment ε q ≤
        Creg * ε⁻¹ ^ (2 : ℕ) :=
    (r322RegionTwoRegularMoment_le_total hε q).trans
      (hreg ε hε)
  have hLocalScaled :
      ((ε⁻¹) ^ 4 / L) *
          r322RegionTwoLocalMoment
            supportConstant ε q ≤
        (Clocal * supportConstant ^ 2) *
          ε⁻¹ ^ (2 : ℕ) / L := by
    calc
      ((ε⁻¹) ^ 4 / L) *
            r322RegionTwoLocalMoment
              supportConstant ε q ≤
          ((ε⁻¹) ^ 4 / L) *
            (Clocal * supportConstant ^ 2 * ε ^ 2) :=
        mul_le_mul_of_nonneg_left hLocalMoment
          (by positivity)
      _ = (Clocal * supportConstant ^ 2) *
            ε⁻¹ ^ (2 : ℕ) / L := by
        field_simp [hε.ne', hL.ne']
  have hfrac :
      1 / L ^ 2 ≤ 1 / L := by
    field_simp [hL.ne']
    nlinarith
  have hRegularInnerScaled :
      (1 / L ^ 2) *
          r322RegionTwoRegularMoment ε q ≤
        Creg * ε⁻¹ ^ (2 : ℕ) / L := by
    calc
      (1 / L ^ 2) *
            r322RegionTwoRegularMoment ε q ≤
          (1 / L ^ 2) *
            (Creg * ε⁻¹ ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hRegularMoment
          (by positivity)
      _ = (Creg * ε⁻¹ ^ (2 : ℕ)) *
            (1 / L ^ 2) := by ring
      _ ≤ (Creg * ε⁻¹ ^ (2 : ℕ)) *
            (1 / L) :=
        mul_le_mul_of_nonneg_left hfrac
          (mul_nonneg hCreg.le
            (pow_nonneg (inv_nonneg.mpr hε.le) 2))
      _ = Creg * ε⁻¹ ^ (2 : ℕ) / L := by
        ring
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
  by_cases hqNear :
      q ∈ r322ScaleBall Snear ε
  · rw [Set.indicator_of_mem hqNear]
    by_cases hqInner : torusDistSq q ≤ ε ^ 2
    · have hinside :
          ((ε⁻¹) ^ 4 / L) *
                r322RegionTwoLocalMoment
                  supportConstant ε q +
              (1 / L ^ 2) *
                r322RegionTwoRegularMoment ε q ≤
            Knear * ε⁻¹ ^ (2 : ℕ) / L := by
        calc
          ((ε⁻¹) ^ 4 / L) *
                  r322RegionTwoLocalMoment
                    supportConstant ε q +
                (1 / L ^ 2) *
                  r322RegionTwoRegularMoment ε q ≤
              (Clocal * supportConstant ^ 2) *
                  ε⁻¹ ^ (2 : ℕ) / L +
                Creg * ε⁻¹ ^ (2 : ℕ) / L :=
            add_le_add hLocalScaled hRegularInnerScaled
          _ = Knear * ε⁻¹ ^ (2 : ℕ) / L := by
            dsimp only [Knear]
            ring
      have hmain :
          r322RegionTwoDensity
              C lam ε supportConstant n q ≤
            P * Knear *
              (ε⁻¹ ^ (2 : ℕ) / L) *
                invSqKer q := by
        unfold r322RegionTwoDensity
        dsimp only [P, L]
        calc
          invSqKer q * (C * lam) ^ (2 * n) *
                (((ε⁻¹) ^ 4 / |Real.log ε|) *
                    r322RegionTwoLocalMoment
                      supportConstant ε q +
                  (1 / |Real.log ε| ^ 2) *
                    r322RegionTwoRegularMoment ε q) ≤
              invSqKer q * (C * lam) ^ (2 * n) *
                (Knear * ε⁻¹ ^ (2 : ℕ) /
                  |Real.log ε|) :=
            mul_le_mul_of_nonneg_left hinside
              (mul_nonneg (invSqKer_nonneg q) hP)
          _ = (C * lam) ^ (2 * n) * Knear *
                (ε⁻¹ ^ (2 : ℕ) /
                  |Real.log ε|) * invSqKer q := by
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
      have hRegularOuter :=
        houter ε q hε hε1 hlog hqOuter
      have hRegularOuterScaled :
          (1 / L ^ 2) *
              r322RegionTwoRegularMoment ε q ≤
            (Kouter / L) * invSqKer q := by
        calc
          (1 / L ^ 2) *
                r322RegionTwoRegularMoment ε q ≤
              (1 / L ^ 2) *
                (Kouter * L * invSqKer q) :=
            mul_le_mul_of_nonneg_left
              (by simpa only [L] using hRegularOuter)
              (by positivity)
          _ = (Kouter / L) * invSqKer q := by
            field_simp [hL.ne']
      have hcritMem :
          q ∈ r322CriticalAnnulus ε := hqOuter
      rw [Set.indicator_of_mem hcritMem]
      unfold r322RegionTwoDensity
      calc
        invSqKer q * (C * lam) ^ (2 * n) *
              (((ε⁻¹) ^ 4 / |Real.log ε|) *
                  r322RegionTwoLocalMoment
                    supportConstant ε q +
                (1 / |Real.log ε| ^ 2) *
                  r322RegionTwoRegularMoment ε q) ≤
            invSqKer q * (C * lam) ^ (2 * n) *
              (((Clocal * supportConstant ^ 2) *
                  ε⁻¹ ^ (2 : ℕ) /
                    |Real.log ε|) +
                (Kouter / |Real.log ε|) *
                  invSqKer q) :=
          mul_le_mul_of_nonneg_left
            (add_le_add hLocalScaled
              hRegularOuterScaled)
            (mul_nonneg (invSqKer_nonneg q) hP)
        _ = (C * lam) ^ (2 * n) *
                (Clocal * supportConstant ^ 2) *
                (ε⁻¹ ^ (2 : ℕ) /
                  |Real.log ε|) * invSqKer q +
              (C * lam) ^ (2 * n) * Kouter *
                (1 / |Real.log ε|) *
                  invSqKer q ^ 2 := by ring
        _ ≤ (C * lam) ^ (2 * n) * Knear *
                (ε⁻¹ ^ (2 : ℕ) /
                  |Real.log ε|) * invSqKer q +
              (C * lam) ^ (2 * n) * Kouter *
                (1 / |Real.log ε|) *
                  invSqKer q ^ 2 := by
          apply add_le_add
          apply mul_le_mul_of_nonneg_right _ (invSqKer_nonneg q)
          have hcoeff :
              Clocal * supportConstant ^ 2 ≤ Knear := by
            dsimp only [Knear]
            linarith
          calc
            (C * lam) ^ (2 * n) *
                  (Clocal * supportConstant ^ 2) *
                  (ε⁻¹ ^ (2 : ℕ) /
                    |Real.log ε|) =
                (P *
                  (ε⁻¹ ^ (2 : ℕ) /
                    |Real.log ε|)) *
                  (Clocal * supportConstant ^ 2) := by
              dsimp only [P]
              ring
            _ ≤ (P *
                  (ε⁻¹ ^ (2 : ℕ) /
                    |Real.log ε|)) * Knear :=
              mul_le_mul_of_nonneg_left hcoeff
                (mul_nonneg hP (by positivity))
            _ = (C * lam) ^ (2 * n) * Knear *
                  (ε⁻¹ ^ (2 : ℕ) /
                    |Real.log ε|) := by
              dsimp only [P]
              ring
          exact le_rfl
  · rw [Set.indicator_of_notMem hqNear]
    have hLocalZero :=
      r322RegionTwoLocalMoment_eq_zero_of_not_scale
        hsupport hε
        (show q ∉ r322ScaleBall
            (4 * supportConstant + 1) ε by
          simpa only [Snear] using hqNear)
    have hqOuter :
        ε ^ 2 ≤ torusDistSq q := by
      by_contra hnot
      have hqInner :
          torusDistSq q ≤ ε ^ 2 :=
        le_of_not_ge hnot
      exact hqNear (hinnerMem hqInner)
    have hRegularOuter :=
      houter ε q hε hε1 hlog hqOuter
    have hRegularOuterScaled :
        (1 / L ^ 2) *
            r322RegionTwoRegularMoment ε q ≤
          (Kouter / L) * invSqKer q := by
      calc
        (1 / L ^ 2) *
              r322RegionTwoRegularMoment ε q ≤
            (1 / L ^ 2) *
              (Kouter * L * invSqKer q) :=
          mul_le_mul_of_nonneg_left
            (by simpa only [L] using hRegularOuter)
            (by positivity)
        _ = (Kouter / L) * invSqKer q := by
          field_simp [hL.ne']
    have hcritMem :
        q ∈ r322CriticalAnnulus ε := hqOuter
    rw [Set.indicator_of_mem hcritMem]
    unfold r322RegionTwoDensity
    rw [hLocalZero, mul_zero, zero_add]
    calc
      invSqKer q * (C * lam) ^ (2 * n) *
            ((1 / |Real.log ε| ^ 2) *
              r322RegionTwoRegularMoment ε q) ≤
          invSqKer q * (C * lam) ^ (2 * n) *
            ((Kouter / |Real.log ε|) *
              invSqKer q) :=
        mul_le_mul_of_nonneg_left
          hRegularOuterScaled
          (mul_nonneg (invSqKer_nonneg q) hP)
      _ = (C * lam) ^ (2 * n) * Kouter *
            (1 / |Real.log ε|) *
              invSqKer q ^ 2 := by ring
      _ = 0 +
          (C * lam) ^ (2 * n) * Kouter *
            (1 / |Real.log ε|) *
              invSqKer q ^ 2 := by ring

/-- The full (4.11) density preserves the inverse-square Green
majorant after the outer `z` integration. -/
theorem exists_r322RegionTwoDensity_convolution_le
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C lam ε : ℝ) (n : ℕ) (x : T4),
        0 ≤ C → 0 ≤ lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| → x ≠ 0 →
        (∫ q,
          invSqKer (x - q) *
            r322RegionTwoDensity
              C lam ε supportConstant n q
          ∂paperMeasure) ≤
          (C * lam) ^ (2 * n) * K * invSqKer x := by
  obtain
    ⟨Knear, Kouter, hKnear, hKouter, hprofile⟩ :=
      exists_r322RegionTwoDensity_profile_le hsupport
  obtain ⟨Kscale, hKscale, hscale⟩ :=
    exists_r322ScaleBall_invSq_convolution_le
      (show 0 < 4 * supportConstant + 1 by
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
  have hL : 0 < L :=
    lt_of_lt_of_le zero_lt_one hlog
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
  have hf : Integrable f paperMeasure := by
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
  have hg₁Int :
      (∫ q, g₁ q ∂paperMeasure) ≤
        P * Knear * Kscale * invSqKer x := by
    have hs :=
      hscale ε x hε hx
    dsimp only [g₁]
    rw [integral_indicator hSin, integral_const_mul]
    calc
      P * Knear *
            (ε⁻¹ ^ (2 : ℕ) / L) *
              ∫ q in Sin,
                invSqKer (x - q) * invSqKer q
                  ∂paperMeasure =
          (P * Knear / L) *
            (ε⁻¹ ^ (2 : ℕ) *
              ∫ q in Sin,
                invSqKer (x - q) * invSqKer q
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
