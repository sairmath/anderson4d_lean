import Anderson4D.DetParametrix.Core.MomentReduction
import Anderson4D.Continuum.CriticalLogWeight

/-!
# The local weighted logarithm in R-324 Step 3

After the sharp binary inverse-square convolution, the local part of the
inserted Proposition 4.1 majorant is an inverse-square kernel restricted to
an `ε`-scale ball and multiplied by the critical logarithmic weight.  This
file proves the exact support-indicator identity and its uniform
`ε² |log ε|` integral bound.

The support radius is fixed before the constant is selected.  Accordingly,
the resulting constant may depend on `supportConstant`, but is uniform in
the mollification scale and the translated logarithmic singularity.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory Set

/-- Pointwise indicator spelling of the locally supported weighted
logarithmic kernel. -/
private theorem invSq_support_mul_criticalLogWeight_eq_indicator
    (supportConstant ε : ℝ) (x : T4) :
    (fun z : T4 =>
      invSqKer z *
        primitiveSupportIndicator supportConstant ε z *
        criticalLogWeight (x - z)) =
      {z : T4 |
        torusDistSq z ≤ (supportConstant * ε) ^ 2}.indicator
        (fun z =>
          invSqKer z * criticalLogWeight (x - z)) := by
  funext z
  by_cases hz :
      torusDistSq z ≤ (supportConstant * ε) ^ 2
  · rw [primitiveSupportIndicator_eq_one hz,
      Set.indicator_of_mem
        (show z ∈ {w : T4 |
          torusDistSq w ≤
            (supportConstant * ε) ^ 2} from hz)]
    ring
  · rw [primitiveSupportIndicator_eq_zero hz,
      Set.indicator_of_notMem
        (show z ∉ {w : T4 |
          torusDistSq w ≤
            (supportConstant * ε) ^ 2} from hz)]
    ring

/-- Exact support-indicator integral identity for the local weighted
logarithmic kernel. -/
theorem integral_invSq_support_mul_criticalLogWeight_eq_setIntegral
    (supportConstant ε : ℝ) (x : T4) :
    (∫ z,
      invSqKer z *
        primitiveSupportIndicator supportConstant ε z *
        criticalLogWeight (x - z)
      ∂paperMeasure) =
      ∫ z in
          {z : T4 |
            torusDistSq z ≤ (supportConstant * ε) ^ 2},
        invSqKer z * criticalLogWeight (x - z)
        ∂paperMeasure := by
  rw [invSq_support_mul_criticalLogWeight_eq_indicator]
  exact
    integral_indicator
      (μ := paperMeasure)
      (f := fun z : T4 =>
        invSqKer z * criticalLogWeight (x - z))
      (measurable_torusDistSq measurableSet_Iic)

/-- Genuine Bochner integrability of the locally supported weighted
logarithmic kernel.  The proof uses the same honest near/far split as the
quantitative estimate below, rather than the totalized value of an
otherwise non-integrable integral. -/
theorem integrable_invSq_support_mul_criticalLogWeight
    {supportConstant ε : ℝ}
    (hsupport : 0 < supportConstant)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|)
    (x : T4) :
    Integrable
      (fun z : T4 =>
        invSqKer z *
          primitiveSupportIndicator supportConstant ε z *
          criticalLogWeight (x - z))
      paperMeasure := by
  let r : ℝ := supportConstant * ε
  let S : Set T4 :=
    {z | torusDistSq z ≤ r ^ 2}
  let f : T4 → ℝ := fun z =>
    invSqKer z * criticalLogWeight (x - z)
  have hr : 0 < r := mul_pos hsupport hε
  have hS : MeasurableSet S :=
    measurable_torusDistSq measurableSet_Iic
  have hnormS :
      ∀ z ∈ S, ‖z‖ ≤ r := by
    intro z hz
    have hsq :
        ‖z‖ ^ 2 ≤ r ^ 2 :=
      (sq_norm_le_torusDistSq z).trans hz
    nlinarith [norm_nonneg z]
  have hfOn : IntegrableOn f S paperMeasure := by
    by_cases hnear : ‖x‖ ≤ 4 * r
    · let g : T4 → ℝ := fun z =>
        (6 + |Real.log r|) * invSqKer z +
          2 * r *
            (invSqKerThreeHalf z +
              invSqKerThreeHalf (x - z))
      have hpoint :
          ∀ z ∈ S, f z ≤ g z := by
        intro z hz
        have hznorm := hnormS z hz
        have hynorm : ‖x - z‖ ≤ 5 * r := by
          calc
            ‖x - z‖ ≤ ‖x‖ + ‖z‖ := norm_sub_le _ _
            _ ≤ 4 * r + r := by linarith
            _ = 5 * r := by ring
        have hweight :=
          criticalLogWeight_le_scaled_half
            hr (by norm_num : (0 : ℝ) ≤ 5)
            (x - z) hynorm
        have hkernel :=
          invSqKer_mul_half_le_threeHalf_add
            z (x - z)
        have hG : 0 ≤ invSqKer z :=
          invSqKer_nonneg z
        dsimp only [f, g]
        calc
          invSqKer z * criticalLogWeight (x - z) ≤
              invSqKer z *
                (1 + |Real.log r| + 5 +
                  2 * r * invSqKerHalf (x - z)) :=
            mul_le_mul_of_nonneg_left hweight hG
          _ =
              (6 + |Real.log r|) * invSqKer z +
                2 * r *
                  (invSqKer z *
                    invSqKerHalf (x - z)) := by ring
          _ ≤
              (6 + |Real.log r|) * invSqKer z +
                2 * r *
                  (invSqKerThreeHalf z +
                    invSqKerThreeHalf (x - z)) := by
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_left hkernel
                (mul_nonneg (by norm_num) hr.le))
      have hg :
          IntegrableOn g S paperMeasure := by
        dsimp only [g]
        exact
          ((integrable_invSqKer.const_mul
            (6 + |Real.log r|)).add
            (((integrable_invSqKerThreeHalf.add
              (integrable_invSqKerThreeHalf_sub_left x))
              |>.const_mul (2 * r)))).integrableOn
      refine Integrable.mono' hg
        (((measurable_invSqKer.mul
          (measurable_criticalLogWeight.comp
            (measurable_const.sub measurable_id)))
          |>.aestronglyMeasurable.restrict)) ?_
      filter_upwards [ae_restrict_mem hS] with z hz
      rw [Real.norm_eq_abs,
        abs_of_nonneg
          (mul_nonneg (invSqKer_nonneg z)
            (criticalLogWeight_nonneg (x - z)))]
      exact hpoint z hz
    · have hfar : 4 * r < ‖x‖ :=
        lt_of_not_ge hnear
      let B : ℝ :=
        5 + |Real.log (3 * supportConstant)|
      let L : ℝ := |Real.log ε|
      let g : T4 → ℝ := fun z =>
        B * L * invSqKer z
      have hpoint :
          ∀ z ∈ S, f z ≤ g z := by
        intro z hz
        have hznorm := hnormS z hz
        have hyLower :
            (3 * supportConstant) * ε ≤ ‖x - z‖ := by
          have hreverse := norm_sub_norm_le x z
          have : 3 * r < ‖x - z‖ := by
            linarith
          dsimp only [r] at this
          linarith
        have hweight :=
          criticalLogWeight_le_of_fixedScale
            (mul_pos (by norm_num) hsupport)
            hε hε1 hlog (x - z) hyLower
        have hG := invSqKer_nonneg z
        dsimp only [f, g, B, L]
        calc
          invSqKer z * criticalLogWeight (x - z) ≤
              invSqKer z *
                ((5 + |Real.log (3 * supportConstant)|) *
                  |Real.log ε|) :=
            mul_le_mul_of_nonneg_left hweight hG
          _ =
              (5 + |Real.log (3 * supportConstant)|) *
                |Real.log ε| * invSqKer z := by ring
      have hg :
          IntegrableOn g S paperMeasure := by
        dsimp only [g]
        exact
          (integrable_invSqKer.const_mul (B * L)).integrableOn
      refine Integrable.mono' hg
        (((measurable_invSqKer.mul
          (measurable_criticalLogWeight.comp
            (measurable_const.sub measurable_id)))
          |>.aestronglyMeasurable.restrict)) ?_
      filter_upwards [ae_restrict_mem hS] with z hz
      rw [Real.norm_eq_abs,
        abs_of_nonneg
          (mul_nonneg (invSqKer_nonneg z)
            (criticalLogWeight_nonneg (x - z)))]
      exact hpoint z hz
  rw [invSq_support_mul_criticalLogWeight_eq_indicator]
  exact hfOn.integrable_indicator hS

/-- The scale-local inverse-square kernel averages the critical binary
logarithm with the sharp `ε² |log ε|` mass.  This is the local half of the
proper inserted convolution in R-324 Step 3. -/
theorem exists_integral_invSq_support_mul_criticalLogWeight_le
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ε : ℝ) (x : T4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        (∫ z,
          invSqKer z *
            primitiveSupportIndicator supportConstant ε z *
            criticalLogWeight (x - z)
          ∂paperMeasure) ≤
            K * ε ^ 2 * |Real.log ε| := by
  obtain ⟨Cmass, hCmass, hmass⟩ :=
    setIntegral_invSqKer_ball_le
  obtain ⟨Cthree, hCthree, hthree⟩ :=
    invSqKerThreeHalf_ball_sub_le
  let Knear : ℝ :=
    supportConstant ^ 2 *
      (Cmass * (7 + |Real.log supportConstant|) +
        16 * Cthree)
  let Kfar : ℝ :=
    supportConstant ^ 2 * Cmass *
      (5 + |Real.log (3 * supportConstant)|)
  let K : ℝ := Knear + Kfar + 1
  have hKnear : 0 ≤ Knear := by
    dsimp only [Knear]
    positivity
  have hKfar : 0 ≤ Kfar := by
    dsimp only [Kfar]
    positivity
  have hK : 0 < K := by
    dsimp only [K]
    linarith
  refine ⟨K, hK, ?_⟩
  intro ε x hε hε1 hlog
  let r : ℝ := supportConstant * ε
  let L : ℝ := |Real.log ε|
  let S : Set T4 :=
    {z | torusDistSq z ≤ r ^ 2}
  let f : T4 → ℝ := fun z =>
    invSqKer z * criticalLogWeight (x - z)
  have hr : 0 < r := mul_pos hsupport hε
  have hL : 0 < L := zero_lt_one.trans_le hlog
  have hS : MeasurableSet S :=
    measurable_torusDistSq measurableSet_Iic
  have hnormS :
      ∀ z ∈ S, ‖z‖ ≤ r := by
    intro z hz
    have hsq :
        ‖z‖ ^ 2 ≤ r ^ 2 :=
      (sq_norm_le_torusDistSq z).trans hz
    nlinarith [norm_nonneg z]
  have hmassS :
      (∫ z in S, invSqKer z ∂paperMeasure) ≤
        Cmass * r ^ 2 := by
    simpa only [S] using hmass r hr
  have hfullEq :
      (∫ z,
        invSqKer z *
          primitiveSupportIndicator supportConstant ε z *
          criticalLogWeight (x - z)
        ∂paperMeasure) =
        ∫ z in S, f z ∂paperMeasure := by
    simpa only [S, f] using
      integral_invSq_support_mul_criticalLogWeight_eq_setIntegral
        supportConstant ε x
  by_cases hnear : ‖x‖ ≤ 4 * r
  · let g : T4 → ℝ := fun z =>
      (6 + |Real.log r|) * invSqKer z +
        2 * r *
          (invSqKerThreeHalf z +
            invSqKerThreeHalf (x - z))
    have hpoint :
        ∀ z ∈ S, f z ≤ g z := by
      intro z hz
      have hznorm := hnormS z hz
      have hynorm : ‖x - z‖ ≤ 5 * r := by
        calc
          ‖x - z‖ ≤ ‖x‖ + ‖z‖ := norm_sub_le _ _
          _ ≤ 4 * r + r := by linarith
          _ = 5 * r := by ring
      have hweight :=
        criticalLogWeight_le_scaled_half
          hr (by norm_num : (0 : ℝ) ≤ 5)
          (x - z) hynorm
      have hkernel :=
        invSqKer_mul_half_le_threeHalf_add
          z (x - z)
      have hG : 0 ≤ invSqKer z :=
        invSqKer_nonneg z
      dsimp only [f, g]
      calc
        invSqKer z * criticalLogWeight (x - z) ≤
            invSqKer z *
              (1 + |Real.log r| + 5 +
                2 * r * invSqKerHalf (x - z)) :=
          mul_le_mul_of_nonneg_left hweight hG
        _ =
            (6 + |Real.log r|) * invSqKer z +
              2 * r *
                (invSqKer z *
                  invSqKerHalf (x - z)) := by ring
        _ ≤
            (6 + |Real.log r|) * invSqKer z +
              2 * r *
                (invSqKerThreeHalf z +
                  invSqKerThreeHalf (x - z)) := by
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hkernel
              (mul_nonneg (by norm_num) hr.le))
    have hthreeS :
        (∫ z in S, invSqKerThreeHalf z
            ∂paperMeasure) ≤
          Cthree * (2 * r) := by
      have hsubset :
          S ⊆ Metric.ball (0 : T4) (2 * r) := by
        intro z hz
        rw [Metric.mem_ball, dist_zero_right]
        exact (hnormS z hz).trans_lt (by linarith)
      have hmono :
          (∫ z in S, invSqKerThreeHalf z
              ∂paperMeasure) ≤
            ∫ z in Metric.ball (0 : T4) (2 * r),
              invSqKerThreeHalf z
                ∂paperMeasure := by
        have hlarge :
            IntegrableOn invSqKerThreeHalf
              (Metric.ball (0 : T4) (2 * r))
              paperMeasure :=
          integrable_invSqKerThreeHalf.integrableOn
        exact setIntegral_mono_set hlarge
          (.of_forall fun z =>
            invSqKerThreeHalf_nonneg z)
          (.of_forall fun z hz => hsubset hz)
      have hbound :=
        hthree (0 : T4) (2 * r) (by positivity)
      have hbound' :
          (∫ z in Metric.ball (0 : T4) (2 * r),
              invSqKerThreeHalf z
              ∂paperMeasure) ≤
            Cthree * (2 * r) := by
        simpa only [zero_sub, invSqKerThreeHalf_neg] using
          hbound
      exact hmono.trans hbound'
    have hthreeShiftS :
        (∫ z in S, invSqKerThreeHalf (x - z)
            ∂paperMeasure) ≤
          Cthree * (6 * r) := by
      have hsubset :
          S ⊆ Metric.ball x (6 * r) := by
        intro z hz
        rw [Metric.mem_ball, dist_eq_norm]
        have hznorm := hnormS z hz
        rw [norm_sub_rev]
        calc
          ‖x - z‖ ≤ ‖x‖ + ‖z‖ := norm_sub_le _ _
          _ ≤ 4 * r + r := by linarith
          _ < 6 * r := by linarith
      have hmono :
          (∫ z in S, invSqKerThreeHalf (x - z)
              ∂paperMeasure) ≤
            ∫ z in Metric.ball x (6 * r),
              invSqKerThreeHalf (x - z)
                ∂paperMeasure :=
        setIntegral_mono_set
          (integrable_invSqKerThreeHalf_sub_left x).integrableOn
          (.of_forall fun z =>
            invSqKerThreeHalf_nonneg (x - z))
          (.of_forall fun z hz => hsubset hz)
      exact hmono.trans
        (hthree x (6 * r) (by positivity))
    have hg :
        IntegrableOn g S paperMeasure := by
      dsimp only [g]
      exact
        ((integrable_invSqKer.const_mul
          (6 + |Real.log r|)).add
          (((integrable_invSqKerThreeHalf.add
            (integrable_invSqKerThreeHalf_sub_left x))
            |>.const_mul (2 * r)))).integrableOn
    have hf :
        IntegrableOn f S paperMeasure := by
      refine Integrable.mono' hg
        (((measurable_invSqKer.mul
          (measurable_criticalLogWeight.comp
            (measurable_const.sub measurable_id)))
          |>.aestronglyMeasurable.restrict)) ?_
      filter_upwards [ae_restrict_mem hS] with z hz
      rw [Real.norm_eq_abs,
        abs_of_nonneg
          (mul_nonneg (invSqKer_nonneg z)
            (criticalLogWeight_nonneg (x - z)))]
      exact hpoint z hz
    have hmono :
        (∫ z in S, f z ∂paperMeasure) ≤
          ∫ z in S, g z ∂paperMeasure :=
      setIntegral_mono_on hf hg hS hpoint
    have hsplit :
        (∫ z in S, g z ∂paperMeasure) =
          (6 + |Real.log r|) *
              ∫ z in S, invSqKer z ∂paperMeasure +
            2 * r *
              ((∫ z in S, invSqKerThreeHalf z
                  ∂paperMeasure) +
                ∫ z in S,
                  invSqKerThreeHalf (x - z)
                    ∂paperMeasure) := by
      have hfirst :
          IntegrableOn
            (fun z : T4 =>
              (6 + |Real.log r|) * invSqKer z)
            S paperMeasure :=
        (integrable_invSqKer.const_mul
          (6 + |Real.log r|)).integrableOn
      have hsecond :
          IntegrableOn
            (fun z : T4 =>
              2 * r *
                (invSqKerThreeHalf z +
                  invSqKerThreeHalf (x - z)))
            S paperMeasure :=
        (((integrable_invSqKerThreeHalf.add
          (integrable_invSqKerThreeHalf_sub_left x))
          |>.const_mul (2 * r))).integrableOn
      calc
        (∫ z in S, g z ∂paperMeasure) =
            ∫ z in S,
              (6 + |Real.log r|) * invSqKer z +
                2 * r *
                  (invSqKerThreeHalf z +
                    invSqKerThreeHalf (x - z))
              ∂paperMeasure := by rfl
        _ =
            (∫ z in S,
              (6 + |Real.log r|) * invSqKer z
              ∂paperMeasure) +
              ∫ z in S,
                2 * r *
                  (invSqKerThreeHalf z +
                    invSqKerThreeHalf (x - z))
                ∂paperMeasure :=
          integral_add hfirst hsecond
        _ = _ := by
          rw [integral_const_mul, integral_const_mul,
            integral_add
              integrable_invSqKerThreeHalf.integrableOn
              (integrable_invSqKerThreeHalf_sub_left x).integrableOn]
    rw [hfullEq]
    calc
      (∫ z in S, f z ∂paperMeasure) ≤
          ∫ z in S, g z ∂paperMeasure := hmono
      _ =
          (6 + |Real.log r|) *
              ∫ z in S, invSqKer z ∂paperMeasure +
            2 * r *
              ((∫ z in S, invSqKerThreeHalf z
                  ∂paperMeasure) +
                ∫ z in S,
                  invSqKerThreeHalf (x - z)
                    ∂paperMeasure) := hsplit
      _ ≤
          (6 + |Real.log r|) * (Cmass * r ^ 2) +
            2 * r *
              (Cthree * (2 * r) +
                Cthree * (6 * r)) := by
        gcongr
      _ ≤ Knear * ε ^ 2 * L := by
        have hscale :
            6 + |Real.log (supportConstant * ε)| ≤
              (7 + |Real.log supportConstant|) *
                |Real.log ε| := by
          have hlogr :
              |Real.log (supportConstant * ε)| ≤
                |Real.log supportConstant| +
                  |Real.log ε| := by
            rw [Real.log_mul hsupport.ne' hε.ne']
            exact abs_add_le _ _
          nlinarith [abs_nonneg (Real.log supportConstant)]
        have hfirst :
            (6 + |Real.log r|) * (Cmass * r ^ 2) ≤
              ((7 + |Real.log supportConstant|) * L) *
                (Cmass * r ^ 2) := by
          exact mul_le_mul_of_nonneg_right
            (by simpa only [r, L] using hscale)
            (mul_nonneg hCmass.le (sq_nonneg r))
        have hsecond :
            2 * r *
                (Cthree * (2 * r) +
                  Cthree * (6 * r)) ≤
              (16 * Cthree * r ^ 2) * L := by
          rw [show
            2 * r *
                (Cthree * (2 * r) +
                  Cthree * (6 * r)) =
              16 * Cthree * r ^ 2 by ring]
          exact le_mul_of_one_le_right
            (mul_nonneg
              (mul_nonneg (by norm_num) hCthree.le)
              (sq_nonneg r))
            (by simpa only [L] using hlog)
        calc
          (6 + |Real.log r|) * (Cmass * r ^ 2) +
                2 * r *
                  (Cthree * (2 * r) +
                    Cthree * (6 * r)) ≤
              ((7 + |Real.log supportConstant|) * L) *
                  (Cmass * r ^ 2) +
                (16 * Cthree * r ^ 2) * L :=
            add_le_add hfirst hsecond
          _ = Knear * ε ^ 2 * L := by
            dsimp only [Knear, r]
            ring
      _ ≤ K * ε ^ 2 * |Real.log ε| := by
        have hKnearK : Knear ≤ K := by
          dsimp only [K]
          linarith
        calc
          Knear * ε ^ 2 * |Real.log ε| =
              Knear * (ε ^ 2 * |Real.log ε|) := by ring
          _ ≤ K * (ε ^ 2 * |Real.log ε|) :=
            mul_le_mul_of_nonneg_right hKnearK
              (mul_nonneg (sq_nonneg ε) (abs_nonneg _))
          _ = K * ε ^ 2 * |Real.log ε| := by ring
  · have hfar : 4 * r < ‖x‖ :=
      lt_of_not_ge hnear
    let B : ℝ :=
      5 + |Real.log (3 * supportConstant)|
    let g : T4 → ℝ := fun z =>
      B * L * invSqKer z
    have hpoint :
        ∀ z ∈ S, f z ≤ g z := by
      intro z hz
      have hznorm := hnormS z hz
      have hyLower :
          (3 * supportConstant) * ε ≤ ‖x - z‖ := by
        have hreverse := norm_sub_norm_le x z
        have : 3 * r < ‖x - z‖ := by
          linarith
        dsimp only [r] at this
        linarith
      have hweight :=
        criticalLogWeight_le_of_fixedScale
          (mul_pos (by norm_num) hsupport)
          hε hε1 hlog (x - z) hyLower
      have hG := invSqKer_nonneg z
      dsimp only [f, g, B, L]
      calc
        invSqKer z * criticalLogWeight (x - z) ≤
            invSqKer z *
              ((5 + |Real.log (3 * supportConstant)|) *
                |Real.log ε|) :=
          mul_le_mul_of_nonneg_left hweight hG
        _ =
            (5 + |Real.log (3 * supportConstant)|) *
              |Real.log ε| * invSqKer z := by ring
    have hg :
        IntegrableOn g S paperMeasure := by
      dsimp only [g]
      exact
        (integrable_invSqKer.const_mul (B * L)).integrableOn
    have hf :
        IntegrableOn f S paperMeasure := by
      refine Integrable.mono' hg
        (((measurable_invSqKer.mul
          (measurable_criticalLogWeight.comp
            (measurable_const.sub measurable_id)))
          |>.aestronglyMeasurable.restrict)) ?_
      filter_upwards [ae_restrict_mem hS] with z hz
      rw [Real.norm_eq_abs,
        abs_of_nonneg
          (mul_nonneg (invSqKer_nonneg z)
            (criticalLogWeight_nonneg (x - z)))]
      exact hpoint z hz
    have hmono :
        (∫ z in S, f z ∂paperMeasure) ≤
          ∫ z in S, g z ∂paperMeasure :=
      setIntegral_mono_on hf hg hS hpoint
    rw [hfullEq]
    calc
      (∫ z in S, f z ∂paperMeasure) ≤
          ∫ z in S, g z ∂paperMeasure := hmono
      _ =
          B * L *
            ∫ z in S, invSqKer z ∂paperMeasure := by
        dsimp only [g]
        rw [integral_const_mul]
      _ ≤ B * L * (Cmass * r ^ 2) := by
        exact mul_le_mul_of_nonneg_left hmassS
          (mul_nonneg
            (by
              dsimp only [B]
              positivity)
            hL.le)
      _ = Kfar * ε ^ 2 * L := by
        dsimp only [B, Kfar, r]
        ring
      _ ≤ K * ε ^ 2 * |Real.log ε| := by
        have hKfarK : Kfar ≤ K := by
          dsimp only [K]
          linarith
        dsimp only [L]
        calc
          Kfar * ε ^ 2 * |Real.log ε| =
              Kfar * (ε ^ 2 * |Real.log ε|) := by ring
          _ ≤ K * (ε ^ 2 * |Real.log ε|) :=
            mul_le_mul_of_nonneg_right hKfarK
              (mul_nonneg (sq_nonneg ε) (abs_nonneg _))
          _ = K * ε ^ 2 * |Real.log ε| := by ring

end

end Anderson4D
