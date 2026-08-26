import Anderson4D.DetParametrix.Paper41_Renorm.R322Profile

/-!
# A scale-local inverse-square approximate identity

The non-Taylor regions (4.11) and (4.12) leave, at the primitive scale,
the truncated kernel

`ε⁻² 1_{d(z) ≤ (S ε)²} invSqKer z`.

Its mass is uniformly bounded, but that fact alone does not control the
second singularity when the external point is also at scale `ε`.  The
proof below separates a ball around that moving singularity and keeps
the local `O(‖x‖²)` mass before applying the normalization.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set

theorem sq_norm_mul_invSqKer_le_one_r322 (z : T4) :
    ‖z‖ ^ 2 * invSqKer z ≤ 1 := by
  unfold invSqKer
  rcases (torusDistSq_nonneg z).eq_or_lt with hz | hz
  · rw [← hz]
    simp
  · rw [mul_inv_le_iff₀ hz]
    simpa only [one_mul] using sq_norm_le_torusDistSq z

/-- The scale-truncated inverse-square kernel, normalized by `ε⁻²`,
preserves the inverse-square external profile. -/
theorem exists_r322ScaleBall_invSq_convolution_le
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ε : ℝ) (x : T4),
        0 < ε → x ≠ 0 →
        ε⁻¹ ^ (2 : ℕ) *
            (∫ z in r322ScaleBall supportConstant ε,
              invSqKer (x - z) * invSqKer z
                ∂paperMeasure) ≤
          K * invSqKer x := by
  obtain ⟨Cker, hCker, hker⟩ :=
    invSqKerBallIntegral_le
  obtain ⟨Cmass, hCmass, hmassBall⟩ :=
    setIntegral_invSqKer_ball_le
  let K : ℝ :=
    (256 * Cker + 16 * Cmass) *
        supportConstant ^ 2 + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro ε x hε hx
  let r : ℝ := supportConstant * ε
  let S : Set T4 := r322ScaleBall supportConstant ε
  have hr : 0 < r := mul_pos hsupport hε
  have hS : MeasurableSet S :=
    measurableSet_r322ScaleBall supportConstant ε
  have hsource :
      Integrable
        (fun z : T4 =>
          invSqKer (x - z) * invSqKer z)
        paperMeasure :=
    integrable_invSqKer_sub_mul_invSqKer_of_ne hx
  have hmass :
      (∫ z in S, invSqKer z ∂paperMeasure) ≤
        Cmass * r ^ 2 := by
    simpa only [S, r, r322ScaleBall] using
      hmassBall r hr
  have hxDist : 0 < torusDistSq x := by
    have hne : torusDistSq x ≠ 0 := by
      intro hzero
      exact hx ((torusDistSq_eq_zero_iff x).mp hzero)
    exact lt_of_le_of_ne
      (torusDistSq_nonneg x) hne.symm
  by_cases hnear : ‖x‖ ≤ 4 * r
  · let B : Set T4 := Metric.ball x (‖x‖ / 2)
    let f : T4 → ℝ := fun z =>
      S.indicator
        (fun w =>
          invSqKer (x - w) * invSqKer w) z
    let g₁ : T4 → ℝ := fun z =>
      B.indicator
        (fun w =>
          16 * invSqKer x * invSqKer (x - w)) z
    let g₂ : T4 → ℝ := fun z =>
      Bᶜ.indicator
        (fun w =>
          16 * invSqKer x *
            S.indicator invSqKer w) z
    have hxNorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hB : MeasurableSet B := measurableSet_ball
    have hf : Integrable f paperMeasure := by
      dsimp only [f]
      exact hsource.indicator hS
    have hg₁ : Integrable g₁ paperMeasure := by
      dsimp only [g₁]
      exact
        ((integrable_invSqKer_sub_left x).const_mul
          (16 * invSqKer x)).indicator hB
    have hg₂ : Integrable g₂ paperMeasure := by
      dsimp only [g₂]
      exact
        ((integrable_invSqKer.indicator hS).const_mul
          (16 * invSqKer x)).indicator hB.compl
    have hpoint : ∀ z, f z ≤ g₁ z + g₂ z := by
      intro z
      by_cases hzS : z ∈ S
      · rw [show f z =
            invSqKer (x - z) * invSqKer z by
          simp [f, hzS]]
        by_cases hzB : z ∈ B
        · rw [show g₁ z =
              16 * invSqKer x * invSqKer (x - z) by
            simp [g₁, hzB]]
          have hzNear : ‖z - x‖ < ‖x‖ / 2 := by
            simpa only [B, Metric.mem_ball, dist_eq_norm] using hzB
          have hzHalf : ‖x‖ / 2 ≤ ‖z‖ := by
            have hreverse := norm_sub_norm_le x z
            rw [norm_sub_rev] at hreverse
            linarith
          have hzKer :=
            invSqKer_le_sixteen_mul_of_half_norm hx hzHalf
          exact le_add_of_le_of_nonneg
            (by
              calc
                invSqKer (x - z) * invSqKer z ≤
                    invSqKer (x - z) *
                      (16 * invSqKer x) :=
                  mul_le_mul_of_nonneg_left hzKer
                    (invSqKer_nonneg (x - z))
                _ = 16 * invSqKer x *
                      invSqKer (x - z) := by ring)
            (Set.indicator_nonneg
              (fun _ _ =>
                mul_nonneg
                  (mul_nonneg (by norm_num)
                    (invSqKer_nonneg x))
                  (Set.indicator_nonneg
                    (fun _ _ => invSqKer_nonneg _) z)) z)
        · rw [show g₂ z =
              16 * invSqKer x * invSqKer z by
            simp [g₂, hzB, hzS]]
          have hdiffHalf :
              ‖x‖ / 2 ≤ ‖x - z‖ := by
            have hzFar : ‖z - x‖ ≥ ‖x‖ / 2 := by
              change z ∉ Metric.ball x (‖x‖ / 2) at hzB
              rw [Metric.mem_ball, dist_eq_norm] at hzB
              exact le_of_not_gt hzB
            simpa only [norm_sub_rev] using hzFar
          have hdiffKer :=
            invSqKer_le_sixteen_mul_of_half_norm
              hx hdiffHalf
          exact le_add_of_nonneg_of_le
            (Set.indicator_nonneg
              (fun _ _ =>
                mul_nonneg
                  (mul_nonneg (by norm_num)
                    (invSqKer_nonneg x))
                  (invSqKer_nonneg _)) z)
            (mul_le_mul_of_nonneg_right hdiffKer
              (invSqKer_nonneg z))
      · rw [show f z = 0 by simp [f, hzS]]
        exact add_nonneg
          (Set.indicator_nonneg
            (fun _ _ =>
              mul_nonneg
                (mul_nonneg (by norm_num)
                  (invSqKer_nonneg x))
                (invSqKer_nonneg _)) z)
          (Set.indicator_nonneg
            (fun _ _ =>
              mul_nonneg
                (mul_nonneg (by norm_num)
                  (invSqKer_nonneg x))
                (Set.indicator_nonneg
                  (fun _ _ => invSqKer_nonneg _) z)) z)
    have hg₁Int :
        (∫ z, g₁ z ∂paperMeasure) ≤ 4 * Cker := by
      dsimp only [g₁]
      rw [integral_indicator hB, integral_const_mul]
      calc
        16 * invSqKer x *
              ∫ z in B, invSqKer (x - z) ∂paperMeasure ≤
            16 * invSqKer x *
              (Cker * (‖x‖ / 2) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (by
              simpa only [B, invSqKerBallIntegral] using
                hker x (‖x‖ / 2) (by positivity))
            (mul_nonneg (by norm_num) (invSqKer_nonneg x))
        _ = 4 * Cker *
              (‖x‖ ^ 2 * invSqKer x) := by ring
        _ ≤ 4 * Cker * 1 :=
          mul_le_mul_of_nonneg_left
            (sq_norm_mul_invSqKer_le_one_r322 x)
            (mul_nonneg (by norm_num) hCker.le)
        _ = 4 * Cker := by ring
    have hg₂Int :
        (∫ z, g₂ z ∂paperMeasure) ≤
          16 * invSqKer x * (Cmass * r ^ 2) := by
      dsimp only [g₂]
      rw [integral_indicator hB.compl, integral_const_mul]
      calc
        16 * invSqKer x *
              ∫ z in Bᶜ, S.indicator invSqKer z
                ∂paperMeasure ≤
            16 * invSqKer x *
              ∫ z, S.indicator invSqKer z
                ∂paperMeasure := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (by norm_num) (invSqKer_nonneg x))
          exact setIntegral_le_integral
            (integrable_invSqKer.indicator hS)
            (.of_forall fun z =>
              Set.indicator_nonneg
                (fun _ _ => invSqKer_nonneg _) z)
        _ = 16 * invSqKer x *
              ∫ z in S, invSqKer z ∂paperMeasure := by
          rw [integral_indicator hS]
        _ ≤ 16 * invSqKer x * (Cmass * r ^ 2) :=
          mul_le_mul_of_nonneg_left hmass
            (mul_nonneg (by norm_num) (invSqKer_nonneg x))
    have hraw :
        (∫ z in S,
            invSqKer (x - z) * invSqKer z
              ∂paperMeasure) ≤
          4 * Cker +
            16 * invSqKer x * (Cmass * r ^ 2) := by
      calc
        (∫ z in S,
            invSqKer (x - z) * invSqKer z
              ∂paperMeasure) =
            ∫ z, f z ∂paperMeasure := by
          dsimp only [f]
          exact (integral_indicator hS).symm
        _ ≤ ∫ z, g₁ z + g₂ z ∂paperMeasure :=
          integral_mono hf (hg₁.add hg₂) hpoint
        _ = (∫ z, g₁ z ∂paperMeasure) +
              ∫ z, g₂ z ∂paperMeasure :=
          integral_add hg₁ hg₂
        _ ≤ 4 * Cker +
              16 * invSqKer x * (Cmass * r ^ 2) :=
          add_le_add hg₁Int hg₂Int
    have hxUpper :
        torusDistSq x ≤ 64 * r ^ 2 := by
      calc
        torusDistSq x ≤ 4 * ‖x‖ ^ 2 :=
          torusDistSq_le_four_mul_sq_norm x
        _ ≤ 4 * (4 * r) ^ 2 := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg x) hnear 2)
            (by norm_num)
        _ = 64 * r ^ 2 := by ring
    have hconstant :
        ε⁻¹ ^ (2 : ℕ) * (4 * Cker) ≤
          (256 * Cker * supportConstant ^ 2) *
            invSqKer x := by
      unfold invSqKer
      rw [le_mul_inv_iff₀ hxDist]
      dsimp only [r] at hxUpper
      field_simp [hε.ne']
      nlinarith [hCker.le, sq_nonneg supportConstant]
    have hmassScaled :
        ε⁻¹ ^ (2 : ℕ) *
            (16 * invSqKer x * (Cmass * r ^ 2)) =
          (16 * Cmass * supportConstant ^ 2) *
            invSqKer x := by
      dsimp only [r]
      field_simp [hε.ne']
    calc
      ε⁻¹ ^ (2 : ℕ) *
          (∫ z in S,
            invSqKer (x - z) * invSqKer z
              ∂paperMeasure) ≤
          ε⁻¹ ^ (2 : ℕ) *
            (4 * Cker +
              16 * invSqKer x * (Cmass * r ^ 2)) :=
        mul_le_mul_of_nonneg_left hraw
          (pow_nonneg (inv_nonneg.mpr hε.le) 2)
      _ = ε⁻¹ ^ (2 : ℕ) * (4 * Cker) +
            ε⁻¹ ^ (2 : ℕ) *
              (16 * invSqKer x * (Cmass * r ^ 2)) := by
        ring
      _ ≤ (256 * Cker * supportConstant ^ 2) *
              invSqKer x +
            (16 * Cmass * supportConstant ^ 2) *
              invSqKer x := by
        exact add_le_add hconstant hmassScaled.le
      _ = ((256 * Cker + 16 * Cmass) *
              supportConstant ^ 2) *
            invSqKer x := by ring
      _ ≤ K * invSqKer x := by
        apply mul_le_mul_of_nonneg_right _ (invSqKer_nonneg x)
        dsimp only [K]
        linarith
  · have hfar : 4 * r < ‖x‖ := lt_of_not_ge hnear
    have hpoint :
        ∀ z ∈ S,
          invSqKer (x - z) * invSqKer z ≤
            16 * invSqKer x * invSqKer z := by
      intro z hz
      have hzsq : ‖z‖ ^ 2 ≤ r ^ 2 :=
        (sq_norm_le_torusDistSq z).trans hz
      have hznorm : ‖z‖ ≤ r := by
        nlinarith [norm_nonneg z]
      have hdiffHalf :
          ‖x‖ / 2 ≤ ‖x - z‖ := by
        have hreverse := norm_sub_norm_le x z
        linarith
      have hdiffKer :=
        invSqKer_le_sixteen_mul_of_half_norm
          hx hdiffHalf
      exact mul_le_mul_of_nonneg_right hdiffKer
        (invSqKer_nonneg z)
    have hconstInt :
        IntegrableOn
          (fun z : T4 =>
            16 * invSqKer x * invSqKer z)
          S paperMeasure :=
      (integrable_invSqKer.const_mul
        (16 * invSqKer x)).integrableOn
    have hintegral :
        (∫ z in S,
            invSqKer (x - z) * invSqKer z
              ∂paperMeasure) ≤
          16 * invSqKer x *
            (Cmass * r ^ 2) := by
      calc
        (∫ z in S,
            invSqKer (x - z) * invSqKer z
              ∂paperMeasure) ≤
            ∫ z in S,
              16 * invSqKer x * invSqKer z
                ∂paperMeasure :=
          setIntegral_mono_on hsource.integrableOn
            hconstInt hS hpoint
        _ = 16 * invSqKer x *
              ∫ z in S, invSqKer z ∂paperMeasure := by
          rw [integral_const_mul]
        _ ≤ 16 * invSqKer x *
              (Cmass * r ^ 2) :=
          mul_le_mul_of_nonneg_left hmass
            (mul_nonneg (by norm_num) (invSqKer_nonneg x))
    calc
      ε⁻¹ ^ (2 : ℕ) *
          (∫ z in S,
            invSqKer (x - z) * invSqKer z
              ∂paperMeasure) ≤
          ε⁻¹ ^ (2 : ℕ) *
            (16 * invSqKer x *
              (Cmass * r ^ 2)) :=
        mul_le_mul_of_nonneg_left hintegral
          (pow_nonneg (inv_nonneg.mpr hε.le) 2)
      _ = (16 * Cmass * supportConstant ^ 2) *
            invSqKer x := by
        dsimp only [r]
        field_simp [hε.ne']
      _ ≤ K * invSqKer x := by
        apply mul_le_mul_of_nonneg_right _ (invSqKer_nonneg x)
        dsimp only [K]
        nlinarith [hCker.le, sq_nonneg supportConstant]

end

end Anderson4D
