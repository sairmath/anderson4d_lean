import Anderson4D.DetParametrix.Paper41_Renorm.R322Taylor
import Anderson4D.Continuum.PrimitiveEstimate

/-!
# Radial moment ledger for the R-322 collapse

The Taylor region of paper (4.10) and the two crude regions (4.11)--(4.12)
all reduce to the same scale-free fact: after multiplying the ordinary
Proposition 4.1 majorant by `torusDistSq`, its integral is bounded uniformly
in the cutoff scale.  This file proves that fact from the public ball and
critical-annulus estimates in `SingularConv`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set

/-- The local-support contribution after multiplication by the quadratic
Taylor factor. -/
def r322LocalMoment
    (supportConstant ε : ℝ) (z : T4) : ℝ :=
  torusDistSq z * invSqKer z *
    primitiveSupportIndicator supportConstant ε z

/-- The regularized contribution after multiplication by the quadratic
Taylor factor. -/
def r322RegularizedMoment (ε : ℝ) (z : T4) : ℝ :=
  torusDistSq z * (torusDistSq z + ε ^ 2)⁻¹ ^ 3

theorem r322LocalMoment_nonneg
    (supportConstant ε : ℝ) (z : T4) :
    0 ≤ r322LocalMoment supportConstant ε z := by
  unfold r322LocalMoment
  exact mul_nonneg
    (mul_nonneg (torusDistSq_nonneg z)
      (invSqKer_nonneg z))
    (primitiveSupportIndicator_nonneg
      supportConstant ε z)

theorem r322RegularizedMoment_nonneg
    (ε : ℝ) (z : T4) :
    0 ≤ r322RegularizedMoment ε z := by
  unfold r322RegularizedMoment
  exact mul_nonneg (torusDistSq_nonneg z)
    (pow_nonneg
      (inv_nonneg.mpr
        (add_nonneg (torusDistSq_nonneg z)
          (sq_nonneg ε))) 3)

theorem measurable_r322LocalMoment
    (supportConstant ε : ℝ) :
    Measurable (r322LocalMoment supportConstant ε) := by
  unfold r322LocalMoment primitiveSupportIndicator
  apply Measurable.mul
  · exact measurable_torusDistSq.mul measurable_invSqKer
  · exact Measurable.ite
      (measurableSet_le measurable_torusDistSq measurable_const)
      measurable_const measurable_const

theorem measurable_r322RegularizedMoment (ε : ℝ) :
    Measurable (r322RegularizedMoment ε) := by
  unfold r322RegularizedMoment
  exact measurable_torusDistSq.mul
    ((measurable_torusDistSq.add measurable_const).inv.pow_const 3)

theorem integrable_r322LocalMoment
    {supportConstant ε : ℝ}
    (hsupport : 0 < supportConstant) (hε : 0 < ε) :
    Integrable (r322LocalMoment supportConstant ε)
      paperMeasure := by
  let r := supportConstant * ε
  have hr : 0 < r := mul_pos hsupport hε
  have hmajorant :
      Integrable (fun z : T4 => r ^ 2 * invSqKer z)
        paperMeasure :=
    integrable_invSqKer.const_mul _
  apply hmajorant.mono'
    (measurable_r322LocalMoment
      supportConstant ε).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (r322LocalMoment_nonneg supportConstant ε z)]
  unfold r322LocalMoment primitiveSupportIndicator
  split_ifs with hz
  · simpa only [mul_one, r] using
      (mul_le_mul_of_nonneg_right hz
        (invSqKer_nonneg z))
  · simpa only [mul_zero] using
      (mul_nonneg (sq_nonneg r)
        (invSqKer_nonneg z))

theorem integrable_r322RegularizedMoment
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (r322RegularizedMoment ε) paperMeasure := by
  have hmajorant :
      Integrable
        (fun z : T4 =>
          (4 * Real.pi ^ 2) * regularizedInvCube ε z)
        paperMeasure :=
    (integrable_regularizedInvCube ε hε).const_mul _
  apply hmajorant.mono'
    (measurable_r322RegularizedMoment ε).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs,
    abs_of_nonneg (r322RegularizedMoment_nonneg ε z)]
  unfold r322RegularizedMoment regularizedInvCube
  exact mul_le_mul_of_nonneg_right
    (torusDistSq_le z)
    (pow_nonneg
      (inv_nonneg.mpr
        (add_nonneg (torusDistSq_nonneg z)
          (sq_nonneg ε))) 3)

/-- The local-support moment is `O((supportConstant * ε)^4)`. -/
theorem integral_r322LocalMoment_le
    {Cball supportConstant ε : ℝ}
    (hball : ∀ r : ℝ, 0 < r →
      ∫ z in {z : T4 | torusDistSq z ≤ r ^ 2},
          invSqKer z ∂paperMeasure ≤
        Cball * r ^ 2)
    (hsupport : 0 < supportConstant) (hε : 0 < ε) :
    ∫ z, r322LocalMoment supportConstant ε z
        ∂paperMeasure ≤
      Cball * (supportConstant * ε) ^ 4 := by
  let r := supportConstant * ε
  let S : Set T4 := {z | torusDistSq z ≤ r ^ 2}
  have hr : 0 < r := mul_pos hsupport hε
  have hS : MeasurableSet S :=
    measurable_torusDistSq measurableSet_Iic
  have hfun :
      r322LocalMoment supportConstant ε =
        S.indicator (fun z =>
          torusDistSq z * invSqKer z) := by
    funext z
    unfold r322LocalMoment primitiveSupportIndicator S r
    by_cases hz :
        torusDistSq z ≤ (supportConstant * ε) ^ 2
    · simp [hz]
    · simp [hz]
  rw [hfun, integral_indicator hS]
  have hright :
      IntegrableOn (fun z : T4 => r ^ 2 * invSqKer z)
        S paperMeasure :=
    (integrable_invSqKer.const_mul _).integrableOn
  have hleft :
      IntegrableOn
        (fun z : T4 => torusDistSq z * invSqKer z)
        S paperMeasure := by
    have hmeas :
        AEStronglyMeasurable
          (fun z : T4 => torusDistSq z * invSqKer z)
          (paperMeasure.restrict S) :=
      (measurable_torusDistSq.mul measurable_invSqKer)
        |>.aestronglyMeasurable.restrict
    apply hright.mono' hmeas
    filter_upwards [ae_restrict_mem hS] with z hz
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (mul_nonneg (torusDistSq_nonneg z)
          (invSqKer_nonneg z))]
    exact mul_le_mul_of_nonneg_right hz
      (invSqKer_nonneg z)
  calc
    (∫ z in S, torusDistSq z * invSqKer z
        ∂paperMeasure) ≤
        ∫ z in S, r ^ 2 * invSqKer z
          ∂paperMeasure := by
      apply setIntegral_mono_ae_restrict hleft hright
      filter_upwards [ae_restrict_mem hS] with z hz
      exact mul_le_mul_of_nonneg_right hz
        (invSqKer_nonneg z)
    _ = r ^ 2 *
        ∫ z in S, invSqKer z ∂paperMeasure := by
      rw [integral_const_mul]
    _ ≤ r ^ 2 * (Cball * r ^ 2) :=
      mul_le_mul_of_nonneg_left
        (hball r hr) (sq_nonneg r)
    _ = Cball * (supportConstant * ε) ^ 4 := by
      dsimp only [r]
      ring

/-- The regularized moment has only the critical logarithmic loss. -/
theorem integral_r322RegularizedMoment_le
    {Cball Cannulus ε : ℝ}
    (hball : ∀ r : ℝ, 0 < r →
      ∫ z in {z : T4 | torusDistSq z ≤ r ^ 2},
          invSqKer z ∂paperMeasure ≤
        Cball * r ^ 2)
    (hannulus : ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫ z in {z : T4 | r ^ 2 ≤ torusDistSq z},
          invSqKer z ^ 2 ∂paperMeasure ≤
        Cannulus * (1 + |Real.log r|))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ z, r322RegularizedMoment ε z ∂paperMeasure ≤
      Cball + Cannulus * (1 + |Real.log ε|) := by
  let Sin : Set T4 :=
    {z | torusDistSq z ≤ ε ^ 2}
  let Sout : Set T4 :=
    {z | ε ^ 2 ≤ torusDistSq z}
  let gin : T4 → ℝ := fun z =>
    Sin.indicator (fun w => ε⁻¹ ^ 2 * invSqKer w) z
  let gout : T4 → ℝ := fun z =>
    Sout.indicator (fun w => invSqKer w ^ 2) z
  have hSin : MeasurableSet Sin :=
    measurable_torusDistSq measurableSet_Iic
  have hSout : MeasurableSet Sout :=
    measurable_torusDistSq measurableSet_Ici
  have hgin :
      Integrable gin paperMeasure := by
    dsimp only [gin]
    exact (integrable_invSqKer.const_mul _).indicator hSin
  have hgoutOn :
      IntegrableOn (fun z : T4 => invSqKer z ^ 2)
        Sout paperMeasure := by
    have hconst :
        Integrable (fun _ : T4 => ε⁻¹ ^ 4)
          paperMeasure :=
      integrable_const _
    have hmeas :
        AEStronglyMeasurable
          (fun z : T4 => invSqKer z ^ 2)
          (paperMeasure.restrict Sout) :=
      (measurable_invSqKer.pow_const 2)
        |>.aestronglyMeasurable.restrict
    apply hconst.integrableOn.mono' hmeas
    filter_upwards [ae_restrict_mem hSout] with z hz
    rw [Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (invSqKer z))]
    have hd : 0 < torusDistSq z :=
      lt_of_lt_of_le (sq_pos_of_pos hε) hz
    have hinv :
        (torusDistSq z)⁻¹ ≤ (ε ^ 2)⁻¹ :=
      (inv_le_inv₀ hd (sq_pos_of_pos hε)).2 hz
    have hpow :=
      pow_le_pow_left₀
        (inv_nonneg.mpr (torusDistSq_nonneg z))
        hinv 2
    unfold invSqKer
    calc
      (torusDistSq z)⁻¹ ^ 2 ≤
          (ε ^ 2)⁻¹ ^ 2 := hpow
      _ = ε⁻¹ ^ 4 := by
        field_simp [hε.ne']
  have hgout :
      Integrable gout paperMeasure := by
    dsimp only [gout]
    exact hgoutOn.integrable_indicator hSout
  have hg :
      Integrable (fun z => gin z + gout z)
        paperMeasure :=
    hgin.add hgout
  have hpoint :
      ∀ z : T4,
        r322RegularizedMoment ε z ≤
          gin z + gout z := by
    intro z
    let d := torusDistSq z
    by_cases hd0 : d = 0
    · unfold r322RegularizedMoment
      rw [show torusDistSq z = 0 by exact hd0]
      simp only [zero_mul]
      exact add_nonneg
        (Set.indicator_nonneg
          (fun _ _ =>
            mul_nonneg
              (pow_nonneg (inv_nonneg.mpr hε.le) 2)
              (invSqKer_nonneg _)) z)
        (Set.indicator_nonneg
          (fun _ _ => sq_nonneg _) z)
    have hd : 0 < d :=
      lt_of_le_of_ne (torusDistSq_nonneg z) (Ne.symm hd0)
    by_cases hin : d ≤ ε ^ 2
    · have hlocal :
          d * (d + ε ^ 2)⁻¹ ^ 3 ≤
            ε⁻¹ ^ 2 * d⁻¹ := by
        field_simp [hd.ne', hε.ne']
        nlinarith [sq_nonneg d, sq_nonneg (ε ^ 2 - d),
          mul_nonneg hd.le (sq_nonneg ε)]
      unfold r322RegularizedMoment
      change d * (d + ε ^ 2)⁻¹ ^ 3 ≤ _
      dsimp only [gin, Sin, gout, Sout]
      have hzin :
          z ∈ {z : T4 | torusDistSq z ≤ ε ^ 2} := by
        exact hin
      rw [Set.indicator_of_mem hzin]
      unfold invSqKer
      exact hlocal.trans
        (le_add_of_nonneg_right
          (Set.indicator_nonneg
            (fun _ _ => sq_nonneg _) z))
    · have hout : ε ^ 2 ≤ d := le_of_not_ge hin
      have hglobal :
          d * (d + ε ^ 2)⁻¹ ^ 3 ≤ d⁻¹ ^ 2 := by
        have hp : d ^ 3 ≤ (d + ε ^ 2) ^ 3 :=
          pow_le_pow_left₀ hd.le
            (by nlinarith [sq_nonneg ε]) 3
        field_simp [hd.ne', hε.ne']
        exact hp
      unfold r322RegularizedMoment
      change d * (d + ε ^ 2)⁻¹ ^ 3 ≤ _
      dsimp only [gin, Sin, gout, Sout]
      have hzout :
          z ∈ {z : T4 | ε ^ 2 ≤ torusDistSq z} := by
        exact hout
      rw [Set.indicator_of_mem hzout]
      unfold invSqKer
      exact hglobal.trans
        (le_add_of_nonneg_left
          (Set.indicator_nonneg
            (fun _ _ =>
              mul_nonneg
                (pow_nonneg (inv_nonneg.mpr hε.le) 2)
                (invSqKer_nonneg _)) z))
  have hmono :
      (∫ z, r322RegularizedMoment ε z
          ∂paperMeasure) ≤
        ∫ z, gin z + gout z ∂paperMeasure :=
    integral_mono_of_nonneg
      (.of_forall (r322RegularizedMoment_nonneg ε))
      hg (.of_forall hpoint)
  calc
    (∫ z, r322RegularizedMoment ε z
        ∂paperMeasure) ≤
        ∫ z, gin z + gout z ∂paperMeasure :=
      hmono
    _ = (∫ z, gin z ∂paperMeasure) +
        ∫ z, gout z ∂paperMeasure :=
      integral_add hgin hgout
    _ = ε⁻¹ ^ 2 *
          ∫ z in Sin, invSqKer z ∂paperMeasure +
        ∫ z in Sout, invSqKer z ^ 2
          ∂paperMeasure := by
      dsimp only [gin, gout]
      rw [integral_indicator hSin,
        integral_indicator hSout, integral_const_mul]
    _ ≤ ε⁻¹ ^ 2 * (Cball * ε ^ 2) +
        Cannulus * (1 + |Real.log ε|) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (hball ε hε) (pow_nonneg (inv_nonneg.mpr hε.le) 2))
        (hannulus ε hε hε1)
    _ = Cball + Cannulus * (1 + |Real.log ε|) := by
      field_simp [hε.ne']

/-- Uniform quadratic-moment bound for the complete ordinary
Proposition 4.1 majorant.  The constant is chosen before the coupling,
scale, and perturbative order. -/
theorem exists_primitiveKernelMajorant_moment_bound
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C lam ε : ℝ) (n : ℕ),
        0 ≤ C → 0 ≤ lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| →
          Integrable
            (fun z : T4 =>
              torusDistSq z *
                primitiveKernelMajorant C lam ε
                  supportConstant n z)
            paperMeasure ∧
          (∫ z, torusDistSq z *
              primitiveKernelMajorant C lam ε
                supportConstant n z
              ∂paperMeasure) ≤
            (C * lam) ^ (2 * n) * K := by
  obtain ⟨Cball, hCball, hball⟩ :=
    setIntegral_invSqKer_ball_le
  obtain ⟨Cannulus, hCannulus, hannulus⟩ :=
    setIntegral_invSqKer_sq_annulus_le
  let K : ℝ :=
    Cball * supportConstant ^ 4 +
      Cball + 2 * Cannulus
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro C lam ε n hC hlam hε hε1 hlog
  let L : ℝ := |Real.log ε|
  let A : ℝ := (C * lam) ^ (2 * n)
  let a : ℝ := ε⁻¹ ^ 4 / L
  let b : ℝ := 1 / L ^ 2
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hlog
  have hA : 0 ≤ A :=
    pow_nonneg (mul_nonneg hC hlam) _
  have ha : 0 ≤ a := by
    dsimp only [a]
    positivity
  have hb : 0 ≤ b := by
    dsimp only [b]
    positivity
  have hlocalInt :=
    integrable_r322LocalMoment hsupport hε
  have hregInt :=
    integrable_r322RegularizedMoment hε
  have hdecomp :
      (fun z : T4 =>
        torusDistSq z *
          primitiveKernelMajorant C lam ε
            supportConstant n z) =
        fun z =>
          A * (a * r322LocalMoment
            supportConstant ε z +
            b * r322RegularizedMoment ε z) := by
    funext z
    unfold primitiveKernelMajorant
      r322LocalMoment r322RegularizedMoment
    dsimp only [A, a, b, L]
    ring
  have hintInner :
      Integrable
        (fun z =>
          a * r322LocalMoment supportConstant ε z +
            b * r322RegularizedMoment ε z)
        paperMeasure :=
    (hlocalInt.const_mul a).add
      (hregInt.const_mul b)
  have hint :
      Integrable
        (fun z : T4 =>
          torusDistSq z *
            primitiveKernelMajorant C lam ε
              supportConstant n z)
        paperMeasure := by
    rw [hdecomp]
    exact hintInner.const_mul A
  refine ⟨hint, ?_⟩
  have hlocal :=
    integral_r322LocalMoment_le hball hsupport hε
  have hreg :=
    integral_r322RegularizedMoment_le
      hball hannulus hε hε1
  have hlocalScaled :
      a * (∫ z, r322LocalMoment supportConstant ε z
          ∂paperMeasure) ≤
        Cball * supportConstant ^ 4 := by
    calc
      a * (∫ z, r322LocalMoment supportConstant ε z
          ∂paperMeasure) ≤
          a * (Cball * (supportConstant * ε) ^ 4) :=
        mul_le_mul_of_nonneg_left hlocal ha
      _ = (Cball * supportConstant ^ 4) / L := by
        dsimp only [a]
        field_simp [hε.ne', hL.ne']
      _ ≤ Cball * supportConstant ^ 4 :=
        div_le_self
          (mul_nonneg hCball.le
            (pow_nonneg hsupport.le 4))
          hlog
  have hfracOne : 1 / L ^ 2 ≤ 1 := by
    rw [div_le_iff₀ (sq_pos_of_pos hL)]
    nlinarith [sq_nonneg (L - 1)]
  have hfracLinear :
      (1 + L) / L ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (sq_pos_of_pos hL)]
    nlinarith [sq_nonneg (L - 1)]
  have hregScaled :
      b * (∫ z, r322RegularizedMoment ε z
          ∂paperMeasure) ≤
        Cball + 2 * Cannulus := by
    calc
      b * (∫ z, r322RegularizedMoment ε z
          ∂paperMeasure) ≤
          b * (Cball +
            Cannulus * (1 + L)) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [L] using hreg) hb
      _ = Cball * (1 / L ^ 2) +
          Cannulus * ((1 + L) / L ^ 2) := by
        dsimp only [b]
        ring
      _ ≤ Cball * 1 + Cannulus * 2 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hfracOne hCball.le)
          (mul_le_mul_of_nonneg_left
            hfracLinear hCannulus.le)
      _ = Cball + 2 * Cannulus := by ring
  rw [hdecomp, integral_const_mul,
    integral_add (hlocalInt.const_mul a)
      (hregInt.const_mul b),
    integral_const_mul, integral_const_mul]
  calc
    A * (a *
          ∫ z, r322LocalMoment supportConstant ε z
            ∂paperMeasure +
        b * ∫ z, r322RegularizedMoment ε z
            ∂paperMeasure) ≤
        A * (Cball * supportConstant ^ 4 +
          (Cball + 2 * Cannulus)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hlocalScaled hregScaled) hA
    _ = (C * lam) ^ (2 * n) * K := by
      dsimp only [A, K]
      ring

/-- Sharpened form of the preceding moment ledger, retaining the inverse
logarithm which is needed before the outer approximate-identity
convolution in paper (4.10). -/
theorem exists_primitiveKernelMajorant_moment_bound_div_log
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C lam ε : ℝ) (n : ℕ),
        0 ≤ C → 0 ≤ lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| →
          Integrable
            (fun z : T4 =>
              torusDistSq z *
                primitiveKernelMajorant C lam ε
                  supportConstant n z)
            paperMeasure ∧
          (∫ z, torusDistSq z *
              primitiveKernelMajorant C lam ε
                supportConstant n z
              ∂paperMeasure) ≤
            (C * lam) ^ (2 * n) *
              (K / |Real.log ε|) := by
  obtain ⟨Cball, hCball, hball⟩ :=
    setIntegral_invSqKer_ball_le
  obtain ⟨Cannulus, hCannulus, hannulus⟩ :=
    setIntegral_invSqKer_sq_annulus_le
  let K : ℝ :=
    Cball * supportConstant ^ 4 +
      Cball + 2 * Cannulus
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro C lam ε n hC hlam hε hε1 hlog
  let L : ℝ := |Real.log ε|
  let A : ℝ := (C * lam) ^ (2 * n)
  let a : ℝ := ε⁻¹ ^ 4 / L
  let b : ℝ := 1 / L ^ 2
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hlog
  have hA : 0 ≤ A :=
    pow_nonneg (mul_nonneg hC hlam) _
  have ha : 0 ≤ a := by
    dsimp only [a]
    positivity
  have hb : 0 ≤ b := by
    dsimp only [b]
    positivity
  have hlocalInt :=
    integrable_r322LocalMoment hsupport hε
  have hregInt :=
    integrable_r322RegularizedMoment hε
  have hdecomp :
      (fun z : T4 =>
        torusDistSq z *
          primitiveKernelMajorant C lam ε
            supportConstant n z) =
        fun z =>
          A * (a * r322LocalMoment
            supportConstant ε z +
            b * r322RegularizedMoment ε z) := by
    funext z
    unfold primitiveKernelMajorant
      r322LocalMoment r322RegularizedMoment
    dsimp only [A, a, b, L]
    ring
  have hintInner :
      Integrable
        (fun z =>
          a * r322LocalMoment supportConstant ε z +
            b * r322RegularizedMoment ε z)
        paperMeasure :=
    (hlocalInt.const_mul a).add
      (hregInt.const_mul b)
  have hint :
      Integrable
        (fun z : T4 =>
          torusDistSq z *
            primitiveKernelMajorant C lam ε
              supportConstant n z)
        paperMeasure := by
    rw [hdecomp]
    exact hintInner.const_mul A
  refine ⟨hint, ?_⟩
  have hlocal :=
    integral_r322LocalMoment_le hball hsupport hε
  have hreg :=
    integral_r322RegularizedMoment_le
      hball hannulus hε hε1
  have hlocalScaled :
      a * (∫ z, r322LocalMoment supportConstant ε z
          ∂paperMeasure) ≤
        (Cball * supportConstant ^ 4) / L := by
    calc
      a * (∫ z, r322LocalMoment supportConstant ε z
          ∂paperMeasure) ≤
          a * (Cball * (supportConstant * ε) ^ 4) :=
        mul_le_mul_of_nonneg_left hlocal ha
      _ = (Cball * supportConstant ^ 4) / L := by
        dsimp only [a]
        field_simp [hε.ne', hL.ne']
  have hfracOne :
      1 / L ^ 2 ≤ 1 / L := by
    field_simp [hL.ne']
    nlinarith
  have hfracLinear :
      (1 + L) / L ^ 2 ≤ 2 / L := by
    field_simp [hL.ne']
    nlinarith
  have hregScaled :
      b * (∫ z, r322RegularizedMoment ε z
          ∂paperMeasure) ≤
        (Cball + 2 * Cannulus) / L := by
    calc
      b * (∫ z, r322RegularizedMoment ε z
          ∂paperMeasure) ≤
          b * (Cball +
            Cannulus * (1 + L)) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [L] using hreg) hb
      _ = Cball * (1 / L ^ 2) +
          Cannulus * ((1 + L) / L ^ 2) := by
        dsimp only [b]
        ring
      _ ≤ Cball * (1 / L) +
          Cannulus * (2 / L) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hfracOne hCball.le)
          (mul_le_mul_of_nonneg_left
            hfracLinear hCannulus.le)
      _ = (Cball + 2 * Cannulus) / L := by ring
  rw [hdecomp, integral_const_mul,
    integral_add (hlocalInt.const_mul a)
      (hregInt.const_mul b),
    integral_const_mul, integral_const_mul]
  calc
    A * (a *
          ∫ z, r322LocalMoment supportConstant ε z
            ∂paperMeasure +
        b * ∫ z, r322RegularizedMoment ε z
            ∂paperMeasure) ≤
        A * ((Cball * supportConstant ^ 4) / L +
          (Cball + 2 * Cannulus) / L) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hlocalScaled hregScaled) hA
    _ = (C * lam) ^ (2 * n) *
        (K / |Real.log ε|) := by
      dsimp only [A, K, L]
      ring

end

end Anderson4D
