import Anderson4D.DetParametrix.Core.MomentReduction
import Anderson4D.Continuum.CellChainComplete
import Anderson4D.DetParametrix.Paper42_Moment.R324ProperConvolutionReindex
import Anderson4D.DetParametrix.Paper42_Moment.R324LocalWeightedLog
import Anderson4D.DetParametrix.Paper42_Moment.R324RegularizedWeightedLog

/-!
# The proper inserted convolution in R-324 Step 3

After the within-half reductions and one nested cross collapse, paper §4.2
integrates the inserted Proposition 4.1 majorant between two surviving
inverse-square Green edges.  This file starts the direct proof of that
critical convolution.  The support radius is fixed before its eventual
uniform constant is selected; a constant uniform in an arbitrary support
radius would be false.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

private theorem ae_r324Proper_binary_argument_ne_zero
    (u v : T4) :
    ∀ᵐ h ∂paperMeasure, u - v - h ≠ 0 := by
  filter_upwards
      [compl_mem_ae_iff.mpr
        (paperMeasure_singleton (u - v))] with h hh
  have hne : h ≠ u - v := by
    simpa only [Set.mem_compl_iff,
      Set.mem_singleton_iff] using hh
  intro hzero
  exact hne (sub_eq_zero.mp hzero).symm

/-- Product-space form of the proper inserted convolution integrand. -/
def r324ProperInsertedConvolutionIntegrand
    (C lam ε supportConstant : ℝ) (n : ℕ)
    (u v : T4) (p : T4 × T4) : ℝ :=
  invSqKer (u - p.1) *
    primitiveInsertedMajorant
      C lam ε supportConstant n (p.1 - p.2) *
    invSqKer (p.2 - v)

theorem r324ProperInsertedConvolutionIntegrand_eq_kernelTriple
    (C lam ε supportConstant : ℝ) (n : ℕ)
    (u v : T4) :
    r324ProperInsertedConvolutionIntegrand
        C lam ε supportConstant n u v =
      r324KernelTriple
        (primitiveInsertedMajorant
          C lam ε supportConstant n) u v := by
  rfl

private def r324ProperLocalTriple
    (supportConstant ε : ℝ)
    (u v : T4) (p : T4 × T4) : ℝ :=
  invSqKer (u - p.1) *
    invSqKer (p.1 - p.2) *
    primitiveSupportIndicator
      supportConstant ε (p.1 - p.2) *
    invSqKer (p.2 - v)

private def r324ProperRegularizedTriple
    (ε : ℝ) (u v : T4) (p : T4 × T4) : ℝ :=
  invSqKer (u - p.1) *
    regularizedInvSquare ε (p.1 - p.2) *
    invSqKer (p.2 - v)

private theorem integrable_r324ProperLocalTriple
    (supportConstant ε : ℝ) (u v : T4) :
    Integrable
      (r324ProperLocalTriple supportConstant ε u v)
      (paperMeasure.prod paperMeasure) := by
  have htriple := integrable_localTripleProduct u v
  change
    Integrable
      (fun p : T4 × T4 =>
        invSqKer (u - p.1) *
          invSqKer (p.1 - p.2) *
          invSqKer (p.2 - v))
      (paperMeasure.prod paperMeasure) at htriple
  have hindicatorMeas :
      Measurable fun p : T4 × T4 =>
        primitiveSupportIndicator
          supportConstant ε (p.1 - p.2) :=
    (measurable_primitiveSupportIndicator
      supportConstant ε).comp
        (measurable_fst.sub measurable_snd)
  have hindicatorBound :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ‖primitiveSupportIndicator
            supportConstant ε (p.1 - p.2)‖ ≤ 1 := by
    filter_upwards with p
    unfold primitiveSupportIndicator
    split_ifs <;> norm_num
  have hmul :=
    htriple.bdd_mul
      hindicatorMeas.aestronglyMeasurable
      hindicatorBound
  convert hmul using 1
  funext p
  unfold r324ProperLocalTriple
  ring

private theorem integrable_r324ProperRegularizedTriple
    {ε : ℝ} (hε : 0 < ε) (u v : T4) :
    Integrable
      (r324ProperRegularizedTriple ε u v)
      (paperMeasure.prod paperMeasure) := by
  have hleft :
      Integrable (fun a : T4 => invSqKer (u - a))
        paperMeasure := by
    simpa only [invSqKer_sub_comm] using
      integrable_invSqKer_sub u
  have hright :
      Integrable (fun b : T4 => invSqKer (b - v))
        paperMeasure :=
    integrable_invSqKer_sub v
  have hseparated :
      Integrable
        (fun p : T4 × T4 =>
          invSqKer (u - p.1) *
            invSqKer (p.2 - v))
        (paperMeasure.prod paperMeasure) :=
    hleft.mul_prod hright
  have hregMeas :
      Measurable fun p : T4 × T4 =>
        regularizedInvSquare ε (p.1 - p.2) :=
    (measurable_regularizedInvSquare ε).comp
      (measurable_fst.sub measurable_snd)
  have hregBound :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ‖regularizedInvSquare ε (p.1 - p.2)‖ ≤
          ε⁻¹ ^ (4 : ℕ) := by
    filter_upwards with p
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (regularizedInvSquare_nonneg ε (p.1 - p.2))]
    exact regularizedInvSquare_le_inv_four
      ε hε (p.1 - p.2)
  have hmul :=
    hseparated.bdd_mul
      hregMeas.aestronglyMeasurable hregBound
  convert hmul using 1
  funext p
  unfold r324ProperRegularizedTriple
  ring

/-- For every positive mollification scale, the complete proper inserted
integrand is genuinely Bochner integrable on the product torus.  This
licenses the two applications of Fubini used in Step 3. -/
theorem integrable_r324ProperInsertedConvolutionIntegrand
    (C lam supportConstant : ℝ) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) (u v : T4) :
    Integrable
      (r324ProperInsertedConvolutionIntegrand
        C lam ε supportConstant n u v)
      (paperMeasure.prod paperMeasure) := by
  have hlocal :=
    integrable_r324ProperLocalTriple
      supportConstant ε u v
  have hregular :=
    integrable_r324ProperRegularizedTriple
      hε u v
  have hinside :
      Integrable
        (fun p : T4 × T4 =>
          (((ε⁻¹) ^ 2 / |Real.log ε|) *
              r324ProperLocalTriple
                supportConstant ε u v p) +
            (1 / |Real.log ε| ^ 2) *
              r324ProperRegularizedTriple ε u v p)
        (paperMeasure.prod paperMeasure) :=
    (hlocal.const_mul
      ((ε⁻¹) ^ 2 / |Real.log ε|)).add
      (hregular.const_mul
        (1 / |Real.log ε| ^ 2))
  refine
    (hinside.const_mul
      ((C * lam) ^ (2 * n))).congr
      (Filter.Eventually.of_forall fun p => ?_)
  unfold r324ProperInsertedConvolutionIntegrand
    primitiveInsertedMajorant
    r324ProperLocalTriple
    r324ProperRegularizedTriple
    regularizedInvSquare
  ring

/-- Product-integral and paper iterated-integral forms agree exactly. -/
theorem integral_r324ProperInsertedConvolutionIntegrand_eq_iterated
    (C lam supportConstant : ℝ) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) (u v : T4) :
    (∫ p,
      r324ProperInsertedConvolutionIntegrand
        C lam ε supportConstant n u v p
      ∂(paperMeasure.prod paperMeasure)) =
      ∫ a, ∫ b,
        invSqKer (u - a) *
          primitiveInsertedMajorant
            C lam ε supportConstant n (a - b) *
          invSqKer (b - v)
        ∂paperMeasure ∂paperMeasure := by
  exact
    integral_prod _
      (integrable_r324ProperInsertedConvolutionIntegrand
        C lam supportConstant n hε u v)

/-- Exact critical-convolution form of the proper inserted integral. -/
theorem integral_r324ProperInsertedConvolutionIntegrand_eq_weightedBinary
    (C lam supportConstant : ℝ) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) (u v : T4) :
    (∫ p,
      r324ProperInsertedConvolutionIntegrand
        C lam ε supportConstant n u v p
      ∂(paperMeasure.prod paperMeasure)) =
      ∫ h,
        primitiveInsertedMajorant
            C lam ε supportConstant n h *
          (∫ z,
            invSqKer ((u - v - h) - z) *
              invSqKer z
            ∂paperMeasure)
        ∂paperMeasure := by
  rw [r324ProperInsertedConvolutionIntegrand_eq_kernelTriple]
  exact
    integral_r324KernelTriple_eq_weightedBinary
      (primitiveInsertedMajorant
        C lam ε supportConstant n) u v
      (by
        simpa only [
          ← r324ProperInsertedConvolutionIntegrand_eq_kernelTriple]
          using
            integrable_r324ProperInsertedConvolutionIntegrand
              C lam supportConstant n hε u v)

/-- The weighted-binary form is genuinely integrable; this is the
certificate needed before applying the sharp binary-convolution
majorant a.e. -/
theorem integrable_r324ProperInsertedWeightedBinary
    (C lam supportConstant : ℝ) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) (u v : T4) :
    Integrable
      (fun h =>
        primitiveInsertedMajorant
            C lam ε supportConstant n h *
          (∫ z,
            invSqKer ((u - v - h) - z) *
              invSqKer z
            ∂paperMeasure))
      paperMeasure := by
  apply integrable_r324KernelTriple_weightedBinary
  simpa only [
    ← r324ProperInsertedConvolutionIntegrand_eq_kernelTriple]
    using
      integrable_r324ProperInsertedConvolutionIntegrand
        C lam supportConstant n hε u v

/-- The inserted majorant times the moving critical logarithm is
genuinely integrable. -/
theorem integrable_primitiveInsertedMajorant_mul_criticalLogWeight
    {supportConstant : ℝ} (hsupport : 0 < supportConstant)
    (C lam : ℝ) (n : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) (x : T4) :
    Integrable
      (fun h =>
        primitiveInsertedMajorant
            C lam ε supportConstant n h *
          criticalLogWeight (x - h))
      paperMeasure := by
  have hlocal :=
    integrable_invSq_support_mul_criticalLogWeight
      hsupport hε hε1 hlog x
  have hregular :=
    integrable_regularizedInvSquare_mul_criticalLogWeight
      ε x hε
  have hsum :
      Integrable
        (fun h =>
          (((ε⁻¹) ^ 2 / |Real.log ε|) *
              (invSqKer h *
                primitiveSupportIndicator
                  supportConstant ε h *
                criticalLogWeight (x - h))) +
            (1 / |Real.log ε| ^ 2) *
              (regularizedInvSquare ε h *
                criticalLogWeight (x - h)))
        paperMeasure :=
    (hlocal.const_mul
      ((ε⁻¹) ^ 2 / |Real.log ε|)).add
      (hregular.const_mul
        (1 / |Real.log ε| ^ 2))
  refine
    (hsum.const_mul ((C * lam) ^ (2 * n))).congr
      (.of_forall fun h => ?_)
  unfold primitiveInsertedMajorant
    regularizedInvSquare
  ring

/-- The two scale factors in the inserted Proposition 4.1 majorant
cancel exactly against the local `ε²|log ε|` and regularized
`|log ε|²` masses. -/
theorem
    exists_integral_primitiveInsertedMajorant_mul_criticalLogWeight_le
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C lam ε : ℝ) (n : ℕ) (x : T4),
        0 ≤ C → 0 ≤ lam →
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        (∫ h,
          primitiveInsertedMajorant
              C lam ε supportConstant n h *
            criticalLogWeight (x - h)
          ∂paperMeasure) ≤
          (C * lam) ^ (2 * n) * K := by
  obtain ⟨Klocal, hKlocal, hlocalBound⟩ :=
    exists_integral_invSq_support_mul_criticalLogWeight_le
      hsupport
  obtain ⟨Kregular, hKregular, hregularBound⟩ :=
    exists_integral_regularizedInvSquare_mul_criticalLogWeight_le
  let K : ℝ := Klocal + Kregular + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro C lam ε n x hC hlam hε hε1 hlog
  let L : ℝ := |Real.log ε|
  let P : ℝ := (C * lam) ^ (2 * n)
  let a : ℝ := (ε⁻¹) ^ 2 / L
  let b : ℝ := 1 / L ^ 2
  let localPart : T4 → ℝ := fun h =>
    invSqKer h *
      primitiveSupportIndicator supportConstant ε h *
      criticalLogWeight (x - h)
  let regularPart : T4 → ℝ := fun h =>
    regularizedInvSquare ε h *
      criticalLogWeight (x - h)
  have hL : 0 < L :=
    zero_lt_one.trans_le hlog
  have hP : 0 ≤ P := by
    dsimp only [P]
    positivity
  have ha : 0 ≤ a := by
    dsimp only [a]
    exact div_nonneg (sq_nonneg _) hL.le
  have hb : 0 ≤ b := by
    dsimp only [b]
    positivity
  have hlocalInt :
      Integrable localPart paperMeasure := by
    dsimp only [localPart]
    exact
      integrable_invSq_support_mul_criticalLogWeight
        hsupport hε hε1 hlog x
  have hregularInt :
      Integrable regularPart paperMeasure := by
    dsimp only [regularPart]
    exact
      integrable_regularizedInvSquare_mul_criticalLogWeight
        ε x hε
  have hsplit :
      (∫ h,
        primitiveInsertedMajorant
            C lam ε supportConstant n h *
          criticalLogWeight (x - h)
        ∂paperMeasure) =
        P *
          (a * (∫ h, localPart h ∂paperMeasure) +
            b * (∫ h, regularPart h ∂paperMeasure)) := by
    have hfun :
        (fun h =>
          primitiveInsertedMajorant
              C lam ε supportConstant n h *
            criticalLogWeight (x - h)) =
          fun h =>
            P * (a * localPart h +
              b * regularPart h) := by
      funext h
      dsimp only [P, a, b, localPart, regularPart]
      unfold primitiveInsertedMajorant
        regularizedInvSquare
      ring
    rw [hfun, integral_const_mul,
      integral_add
        (hlocalInt.const_mul a)
        (hregularInt.const_mul b),
      integral_const_mul, integral_const_mul]
  have hlocal :
      (∫ h, localPart h ∂paperMeasure) ≤
        Klocal * ε ^ 2 * L := by
    dsimp only [localPart, L]
    exact hlocalBound ε x hε hε1 hlog
  have hregular :
      (∫ h, regularPart h ∂paperMeasure) ≤
        Kregular * L ^ 2 := by
    dsimp only [regularPart, L]
    exact hregularBound ε x hε hε1 hlog
  have hlocalScaled :
      a * (∫ h, localPart h ∂paperMeasure) ≤
        Klocal := by
    calc
      a * (∫ h, localPart h ∂paperMeasure) ≤
          a * (Klocal * ε ^ 2 * L) :=
        mul_le_mul_of_nonneg_left hlocal ha
      _ = Klocal := by
        dsimp only [a, L]
        field_simp [hε.ne', hL.ne']
  have hregularScaled :
      b * (∫ h, regularPart h ∂paperMeasure) ≤
        Kregular := by
    calc
      b * (∫ h, regularPart h ∂paperMeasure) ≤
          b * (Kregular * L ^ 2) :=
        mul_le_mul_of_nonneg_left hregular hb
      _ = Kregular := by
        dsimp only [b]
        field_simp [hL.ne']
  rw [hsplit]
  calc
    P *
        (a * (∫ h, localPart h ∂paperMeasure) +
          b * (∫ h, regularPart h ∂paperMeasure)) ≤
        P * (Klocal + Kregular) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hlocalScaled hregularScaled) hP
    _ ≤ P * K := by
      exact mul_le_mul_of_nonneg_left
        (by
          dsimp only [K]
          linarith)
        hP
    _ =
        (C * lam) ^ (2 * n) * K := by
      rfl

/-- Sharp proper inserted convolution estimate used by every proper
head of the nested R-324 reduction.  The constant is selected after the
fixed support radius and is uniform in the order, scale, endpoints and
coupling parameters. -/
theorem exists_r324ProperInsertedConvolution_le
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C lam ε : ℝ) (n : ℕ) (u v : T4),
        0 ≤ C → 0 ≤ lam →
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        Integrable
          (r324ProperInsertedConvolutionIntegrand
            C lam ε supportConstant n u v)
          (paperMeasure.prod paperMeasure) ∧
        (∫ a, ∫ b,
          invSqKer (u - a) *
            primitiveInsertedMajorant
              C lam ε supportConstant n (a - b) *
            invSqKer (b - v)
          ∂paperMeasure ∂paperMeasure) ≤
          (C * lam) ^ (2 * n) * K := by
  obtain ⟨Cbinary, hCbinary, hbinary⟩ :=
    binary_conv_invSqKer_log_le
  obtain ⟨Kweight, hKweight, hweight⟩ :=
    exists_integral_primitiveInsertedMajorant_mul_criticalLogWeight_le
      hsupport
  let K : ℝ := Cbinary * Kweight + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro C lam ε n u v hC hlam hε hε1 hlog
  have hint :=
    integrable_r324ProperInsertedConvolutionIntegrand
      C lam supportConstant n hε u v
  refine ⟨hint, ?_⟩
  let q : T4 → ℝ :=
    primitiveInsertedMajorant
      C lam ε supportConstant n
  let x : T4 := u - v
  have hweighted :=
    integrable_r324ProperInsertedWeightedBinary
      C lam supportConstant n hε u v
  have hcritical :
      Integrable
        (fun h => q h * criticalLogWeight (x - h))
        paperMeasure := by
    dsimp only [q, x]
    exact
      integrable_primitiveInsertedMajorant_mul_criticalLogWeight
        hsupport C lam n hε hε1 hlog (u - v)
  have hmajorant :
      Integrable
        (fun h =>
          Cbinary *
            (q h * criticalLogWeight (x - h)))
        paperMeasure :=
    hcritical.const_mul Cbinary
  have hpoint :
      ∀ᵐ h ∂paperMeasure,
        q h *
            (∫ z,
              invSqKer ((x - h) - z) * invSqKer z
              ∂paperMeasure) ≤
          Cbinary *
            (q h * criticalLogWeight (x - h)) := by
    filter_upwards
        [ae_r324Proper_binary_argument_ne_zero u v] with h hh
    have hconv :=
      hbinary (x - h) (by
        dsimp only [x]
        exact hh)
    have hconv' :
        (∫ z,
          invSqKer ((x - h) - z) * invSqKer z
          ∂paperMeasure) ≤
          Cbinary * criticalLogWeight (x - h) := by
      simpa only [criticalLogWeight] using hconv
    have hq : 0 ≤ q h := by
      dsimp only [q]
      exact primitiveInsertedMajorant_nonneg hC hlam
    calc
      q h *
          (∫ z,
            invSqKer ((x - h) - z) * invSqKer z
            ∂paperMeasure) ≤
          q h *
            (Cbinary * criticalLogWeight (x - h)) :=
        mul_le_mul_of_nonneg_left hconv' hq
      _ =
          Cbinary *
            (q h * criticalLogWeight (x - h)) := by
        ring
  have hbinaryIntegral :
      (∫ h,
        q h *
          (∫ z,
            invSqKer ((x - h) - z) * invSqKer z
            ∂paperMeasure)
        ∂paperMeasure) ≤
        ∫ h,
          Cbinary *
            (q h * criticalLogWeight (x - h))
          ∂paperMeasure :=
    integral_mono_ae hweighted hmajorant hpoint
  have hweightBound :
      (∫ h,
        q h * criticalLogWeight (x - h)
        ∂paperMeasure) ≤
        (C * lam) ^ (2 * n) * Kweight := by
    dsimp only [q, x]
    exact
      hweight C lam ε n (u - v)
        hC hlam hε hε1 hlog
  rw [←
    integral_r324ProperInsertedConvolutionIntegrand_eq_iterated
      C lam supportConstant n hε u v]
  rw [
    integral_r324ProperInsertedConvolutionIntegrand_eq_weightedBinary
      C lam supportConstant n hε u v]
  change
    (∫ h,
      q h *
        (∫ z,
          invSqKer ((x - h) - z) * invSqKer z
          ∂paperMeasure)
      ∂paperMeasure) ≤
      (C * lam) ^ (2 * n) * K
  calc
    (∫ h,
      q h *
        (∫ z,
          invSqKer ((x - h) - z) * invSqKer z
          ∂paperMeasure)
      ∂paperMeasure) ≤
        ∫ h,
          Cbinary *
            (q h * criticalLogWeight (x - h))
          ∂paperMeasure :=
      hbinaryIntegral
    _ =
        Cbinary *
          (∫ h,
            q h * criticalLogWeight (x - h)
            ∂paperMeasure) := by
      rw [integral_const_mul]
    _ ≤
        Cbinary *
          ((C * lam) ^ (2 * n) * Kweight) :=
      mul_le_mul_of_nonneg_left hweightBound hCbinary.le
    _ ≤
        (C * lam) ^ (2 * n) * K := by
      dsimp only [K]
      have hpow :
          0 ≤ (C * lam) ^ (2 * n) := by
        positivity
      nlinarith [mul_nonneg hCbinary.le hKweight.le]

end

end Anderson4D
