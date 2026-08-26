import Anderson4D.DetParametrix.Core.FinalBound
import Anderson4D.Continuum.PrimitiveBase
import Anderson4D.Continuum.GreenFourier
import Anderson4D.Continuum.PeriodizedCovariance
import Mathlib.Analysis.Fourier.Convolution

/-!
# Base case of the deterministic interval reduction

At order `2q = 2` the non-splitting class contains only the swap
pairing.  Its extraction list is the whole interval, whose terminal
difference factor is the value `1`.  This file computes that branch
exactly and identifies it with the first primitive kernel.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open MeasureTheory
open scoped Convolution

noncomputable section

theorem pairingFinTwo_extract :
    extract pairingFinTwo = [(0, 1)] := by
  decide

theorem nonSplitPairings_one_eq :
    nonSplitPairings 1 = {pairingFinTwo} := by
  decide

theorem detJintegrand_one_pairingFinTwo
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin 2 → T4) :
    detJintegrand ρ ε 1 pairingFinTwo x =
      greenFn (x 0 - x 1) *
        ρ.etaEpsT4 ε (x 0 - x 1) := by
  rw [detJintegrand, pairingFinTwo_extract,
    pairingFinTwo_lowerSupport]
  simp [diffFactorJ]

/-- Exact order-two `J` formula. -/
theorem detJ_one_pairingFinTwo
    (ρ : SmoothCutoff) (lam ε : ℝ) (z w : T4) :
    detJ ρ lam ε 1 pairingFinTwo z w =
      lamEps lam ε ^ 2 *
        (greenFn (z - w) *
          ρ.etaEpsT4 ε (z - w)) := by
  rw [detJ]
  have hconst : ∀ v : Fin 0 → T4,
      detJintegrand ρ ε 1 pairingFinTwo
          (fun j =>
            assemble z w v
              (Fin.cast (by omega : 2 * 1 = 2 * 0 + 2) j)) =
        greenFn (z - w) *
          ρ.etaEpsT4 ε (z - w) := by
    intro v
    rw [detJintegrand_one_pairingFinTwo]
    have hx0 :
        assemble z w v (0 : Fin 2) = z := by
      simp
    have hx1 :
        assemble z w v (1 : Fin 2) = w := by
      simpa only [show (1 : Fin 2) = Fin.last 1 by decide] using
        assemble_last z w v
    change
      greenFn (assemble z w v 0 - assemble z w v 1) *
          ρ.etaEpsT4 ε (assemble z w v 0 - assemble z w v 1) =
        greenFn (z - w) * ρ.etaEpsT4 ε (z - w)
    rw [hx0, hx1]
  rw [integral_congr_ae
      (Filter.Eventually.of_forall hconst),
    integral_const]
  simp [measureReal_def]

/-- The order-two deterministic kernel is literally the first primitive
kernel with the free Green function as its unique chain input. -/
theorem detJ_one_eq_primitiveKernel
    (ρ : SmoothCutoff) (lam ε : ℝ) (z w : T4) :
    detJ ρ lam ε 1 pairingFinTwo z w =
      primitiveKernel ρ lam ε 1 (by omega)
        (fun _ => greenFn) z w := by
  rw [detJ_one_pairingFinTwo,
    primitiveKernel_one]

theorem sum_nonSplit_detJ_abs_one
    (ρ : SmoothCutoff) (lam ε : ℝ) (z w : T4) :
    (∑ σ ∈ nonSplitPairings 1,
        |detJ ρ lam ε 1 σ z w|) =
      |primitiveKernel ρ lam ε 1 (by omega)
        (fun _ => greenFn) z w| := by
  rw [nonSplitPairings_one_eq]
  simp only [Finset.sum_singleton]
  rw [detJ_one_eq_primitiveKernel]

/-- At the base order there is one endpoint signature and its fiber has
one pairing, so the grouped form of (4.15) is the same single kernel. -/
theorem groupedDetJAbsSum_one
    (ρ : SmoothCutoff) (lam ε : ℝ) (z : T4) :
    groupedDetJAbsSum ρ lam ε 1 z =
      |primitiveKernel ρ lam ε 1 (by omega)
        (fun _ => greenFn) z 0| := by
  unfold groupedDetJAbsSum
  unfold nonSplitReductionEndpointSignatures
  rw [nonSplitPairings_one_eq]
  simp only [Finset.image_singleton, Finset.sum_singleton]
  unfold endpointFiberDetJSum
  rw [nonSplitPairings_one_eq]
  simp only [Finset.filter_singleton]
  simp only [if_true, Finset.sum_singleton]
  rw [detJ_one_eq_primitiveKernel]

theorem renormC2q_one
    (ρ : SmoothCutoff) (lam ε : ℝ) :
    renormC2q ρ lam ε 1 =
      ∫ z,
        primitiveKernel ρ lam ε 1 (by omega)
          (fun _ => greenFn) z 0
        ∂paperMeasure := by
  rw [renormC2q_eq_sum, nonSplitPairings_one_eq]
  simp only [Finset.sum_singleton, renormC2qTerm]
  apply integral_congr_ae
  filter_upwards with z
  exact detJ_one_eq_primitiveKernel ρ lam ε z 0

/-! ## Honest integrability of the base branch -/

theorem SmoothCutoff.measurable_etaPeriodTerm
    (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    Measurable (fun z : T4 => ρ.etaPeriodTerm ε z k) := by
  have hcontinuous : Continuous ρ.eta := by
    change Continuous
      ((ρ : R4 → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ]
        (ρ : R4 → ℝ))
    exact ρ.hasCompactSupport.continuous_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ)
      ρ.integrable.locallyIntegrable ρ.continuous
  unfold SmoothCutoff.etaPeriodTerm
  apply Measurable.const_mul
  exact hcontinuous.measurable.comp
    (measurable_pi_lambda _ fun i =>
      measurable_const.mul
        (((measurable_pi_apply i).comp measurable_torusLift).add
          measurable_const))

/-- In the positive small-scale regime, the covariance periodization is
a finite measurable sum.  This public lemma is also useful to the later
R-322 interval-integration steps. -/
theorem SmoothCutoff.measurable_etaEpsT4_of_pos_of_le_one
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Measurable (ρ.etaEpsT4 ε) := by
  rw [show ρ.etaEpsT4 ε =
      fun z =>
        ∑ k ∈ ρ.covariancePeriodBox,
          ρ.etaPeriodTerm ε z k by
    funext z
    exact ρ.etaEpsT4_eq_sum_covariancePeriodBox hε hε1 z]
  exact Finset.measurable_sum _ fun k _ =>
    ρ.measurable_etaPeriodTerm ε k

/-- The exact order-two deterministic summand is genuinely integrable;
this rules out any use of the junk value of the Bochner integral in the
base case of R-322. -/
theorem integrable_detJ_one_pairingFinTwo
    (ρ : SmoothCutoff) (lam : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable
      (fun z : T4 =>
        detJ ρ lam ε 1 pairingFinTwo z 0)
      paperMeasure := by
  obtain ⟨Cη, hCη, hetaBound⟩ :=
    ρ.exists_pos_etaEpsT4_uniform_bound
  let B : ℝ := ε⁻¹ ^ (dim : ℕ) * Cη
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hetaMeas :
      AEStronglyMeasurable (ρ.etaEpsT4 ε)
        paperMeasure :=
    (ρ.measurable_etaEpsT4_of_pos_of_le_one
      hε hε1).aestronglyMeasurable
  have hprodMeas :
      AEStronglyMeasurable
        (fun z : T4 =>
          greenFn z * ρ.etaEpsT4 ε z)
        paperMeasure :=
    integrable_greenFn_paper.aestronglyMeasurable.mul hetaMeas
  have hmajorant :
      Integrable (fun z : T4 => B * |greenFn z|)
        paperMeasure :=
    integrable_greenFn_paper.abs.const_mul B
  have hprod :
      Integrable
        (fun z : T4 =>
          greenFn z * ρ.etaEpsT4 ε z)
        paperMeasure := by
    apply hmajorant.mono' hprodMeas
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (ρ.etaEpsT4_nonneg ε z)]
    calc
      |greenFn z| * ρ.etaEpsT4 ε z ≤
          |greenFn z| * B :=
        mul_le_mul_of_nonneg_left
          (hetaBound hε hε1 z) (abs_nonneg _)
      _ = B * |greenFn z| := by ring
  have hscaled :
      Integrable
        (fun z : T4 =>
          lamEps lam ε ^ 2 *
            (greenFn z * ρ.etaEpsT4 ε z))
        paperMeasure :=
    hprod.const_mul _
  refine hscaled.congr ?_
  filter_upwards with z
  rw [detJ_one_pairingFinTwo, sub_zero]

/-- Absolute integrability of the base summand, derived from genuine
integrability rather than used as a proxy for measurability. -/
theorem integrable_abs_detJ_one_pairingFinTwo
    (ρ : SmoothCutoff) (lam : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable
      (fun z : T4 =>
        |detJ ρ lam ε 1 pairingFinTwo z 0|)
      paperMeasure :=
  (integrable_detJ_one_pairingFinTwo
    ρ lam hε hε1).abs

/-! ## Pointwise base reduction -/

theorem eps_sq_mul_abs_log_le_one
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε ^ 2 * |Real.log ε| ≤ 1 := by
  have habs : |Real.log ε| = -Real.log ε :=
    abs_of_nonpos (Real.log_nonpos hε.le hε1)
  have hlogInv :=
    Real.log_le_sub_one_of_pos (inv_pos.mpr hε)
  rw [Real.log_inv] at hlogInv
  have hεlog : ε * |Real.log ε| ≤ 1 := by
    rw [habs]
    have hmul :=
      mul_le_mul_of_nonneg_left hlogInv hε.le
    field_simp [hε.ne'] at hmul
    linarith
  have hεsq : ε ^ 2 ≤ ε := by
    nlinarith
  exact
    (mul_le_mul_of_nonneg_right hεsq
      (abs_nonneg _)).trans hεlog

/-- The exact base summand obeys the Proposition 4.1 majorant after
absorbing the fixed Green and covariance constants.  At the single
singular point `z = 0`, the global regularized term pays for the
junk-totalized value of `greenFn 0`; away from zero, the local
`|z|⁻²` term is used. -/
theorem abs_detJ_one_pairingFinTwo_le_majorant
    (ρ : SmoothCutoff)
    {Cg Cη supportConstant C lam ε : ℝ}
    (hCg : 0 ≤ Cg) (_hCη : 0 ≤ Cη)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 0 < |Real.log ε|)
    (hgreen :
      ∀ z : T4, torusDistSq z ≠ 0 →
        greenFn z ≤ Cg / torusDistSq z)
    (heta :
      ∀ z : T4,
        ρ.etaEpsT4 ε z ≤
          ε⁻¹ ^ (dim : ℕ) * Cη)
    (hsupport : 4 * ρ.radius ≤ supportConstant)
    (hClocal : Cg * Cη ≤ C ^ 2)
    (hCzero : greenFn 0 * Cη ≤ C ^ 2)
    (z : T4) :
    |detJ ρ lam ε 1 pairingFinTwo z 0| ≤
      primitiveKernelMajorant C lam ε
        supportConstant 1 z := by
  rw [detJ_one_pairingFinTwo, sub_zero]
  by_cases hηzero : ρ.etaEpsT4 ε z = 0
  · simp only [hηzero, mul_zero, abs_zero]
    exact primitiveKernelMajorant_nonneg hC hlam
  have hηnonneg := ρ.etaEpsT4_nonneg ε z
  have hη :
      ρ.etaEpsT4 ε z ≤ ε⁻¹ ^ 4 * Cη := by
    simpa only [dim] using heta z
  have hcoupling : 0 ≤ lamEps lam ε ^ 2 :=
    sq_nonneg _
  by_cases hdist : torusDistSq z = 0
  · have hz : z = 0 :=
      (torusDistSq_eq_zero_iff z).mp hdist
    subst z
    have hscale :
        ε⁻¹ ^ (4 : ℕ) / |Real.log ε| ≤
          (1 / |Real.log ε| ^ 2) *
            (ε ^ 2)⁻¹ ^ (3 : ℕ) := by
      field_simp [hε.ne', hlog.ne']
      nlinarith [eps_sq_mul_abs_log_le_one hε hε1]
    calc
      |lamEps lam ε ^ 2 *
          (greenFn 0 * ρ.etaEpsT4 ε 0)| =
        lamEps lam ε ^ 2 *
          (greenFn 0 * ρ.etaEpsT4 ε 0) := by
        rw [abs_of_nonneg
          (mul_nonneg hcoupling
            (mul_nonneg (greenFn_nonneg 0) hηnonneg))]
      _ ≤ lamEps lam ε ^ 2 *
          (greenFn 0 * (ε⁻¹ ^ 4 * Cη)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hη
            (greenFn_nonneg 0)) hcoupling
      _ = (lam ^ 2 / |Real.log ε|) *
          (greenFn 0 * Cη) * ε⁻¹ ^ 4 := by
        rw [lamEps_sq hlog]
        ring
      _ ≤ (lam ^ 2 / |Real.log ε|) *
          C ^ 2 * ε⁻¹ ^ 4 := by
        gcongr
      _ = (C * lam) ^ 2 *
          (ε⁻¹ ^ 4 / |Real.log ε|) := by
        ring
      _ ≤ (C * lam) ^ 2 *
          ((1 / |Real.log ε| ^ 2) *
            (ε ^ 2)⁻¹ ^ 3) :=
        mul_le_mul_of_nonneg_left hscale
          (sq_nonneg (C * lam))
      _ ≤ primitiveKernelMajorant C lam ε
          supportConstant 1 0 := by
        unfold primitiveKernelMajorant
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left
        · have hlocal :
              0 ≤ (ε⁻¹ ^ 4 / |Real.log ε|) *
                invSqKer 0 *
                primitiveSupportIndicator
                  supportConstant ε 0 :=
            mul_nonneg
              (mul_nonneg
                (div_nonneg (by positivity) hlog.le)
                (invSqKer_nonneg 0))
              (primitiveSupportIndicator_nonneg
                supportConstant ε 0)
          rw [hdist, zero_add]
          nlinarith
        · exact sq_nonneg (C * lam)
  · have hgreenAbs :
        |greenFn z| ≤ Cg * invSqKer z := by
      rw [abs_of_nonneg (greenFn_nonneg z)]
      calc
        greenFn z ≤ Cg / torusDistSq z :=
          hgreen z hdist
        _ = Cg * invSqKer z := by
          unfold invSqKer
          rw [div_eq_mul_inv]
    have hsupport0 :=
      ρ.torusDistSq_le_support_of_etaEpsT4_ne_zero
        hε hηzero
    have hsquares :
        (4 * ρ.radius * ε) ^ 2 ≤
          (supportConstant * ε) ^ 2 := by
      exact pow_le_pow_left₀
        (mul_nonneg
          (by nlinarith [ρ.radius_pos]) hε.le)
        (mul_le_mul_of_nonneg_right
          hsupport hε.le) 2
    have hind :
        primitiveSupportIndicator
            supportConstant ε z = 1 :=
      primitiveSupportIndicator_eq_one
        (hsupport0.trans hsquares)
    have hscaled :
        |greenFn z| * ρ.etaEpsT4 ε z ≤
          (Cg * invSqKer z) *
            (ε⁻¹ ^ 4 * Cη) :=
      mul_le_mul hgreenAbs hη hηnonneg
        (mul_nonneg hCg (invSqKer_nonneg z))
    calc
      |lamEps lam ε ^ 2 *
          (greenFn z * ρ.etaEpsT4 ε z)| =
        lamEps lam ε ^ 2 *
          (|greenFn z| *
            ρ.etaEpsT4 ε z) := by
        rw [abs_mul, abs_of_nonneg hcoupling,
          abs_mul, abs_of_nonneg hηnonneg]
      _ ≤ lamEps lam ε ^ 2 *
          ((Cg * invSqKer z) *
            (ε⁻¹ ^ 4 * Cη)) :=
        mul_le_mul_of_nonneg_left hscaled hcoupling
      _ = (lam ^ 2 / |Real.log ε| *
          invSqKer z * ε⁻¹ ^ 4) *
            (Cg * Cη) := by
        rw [lamEps_sq hlog]
        ring
      _ ≤ (lam ^ 2 / |Real.log ε| *
          invSqKer z * ε⁻¹ ^ 4) *
            C ^ 2 := by
        exact mul_le_mul_of_nonneg_left hClocal
          (mul_nonneg
            (mul_nonneg
              (div_nonneg (sq_nonneg lam) hlog.le)
              (invSqKer_nonneg z))
            (by positivity))
      _ = (C * lam) ^ 2 *
          (((ε⁻¹) ^ 4 / |Real.log ε|) *
            invSqKer z *
            primitiveSupportIndicator
              supportConstant ε z) := by
        rw [hind]
        ring
      _ ≤ primitiveKernelMajorant C lam ε
          supportConstant 1 z := by
        unfold primitiveKernelMajorant
        apply mul_le_mul_of_nonneg_left
        · exact le_add_of_nonneg_right
            (mul_nonneg
              (div_nonneg zero_le_one (sq_nonneg _))
              (pow_nonneg
                (inv_nonneg.mpr
                  (add_nonneg
                    (torusDistSq_nonneg z)
                    (sq_nonneg ε))) 3))
        · exact sq_nonneg (C * lam)

/-- Fully closed R-322 output at the base perturbative order.  All
constants are selected before `λ` and `ε`, and both the pointwise
majorant and the required integrability are proved from the concrete
`J` kernel. -/
theorem exists_renormReductionOutput_one
    (ρ : SmoothCutoff) :
    ∃ primitiveConstant supportConstant : ℝ,
      0 < primitiveConstant ∧ 0 < supportConstant ∧
        ∀ (lam ε : ℝ),
          0 ≤ lam → 0 < ε → ε ≤ 1 →
          0 < |Real.log ε| →
            RenormReductionOutput ρ lam ε 1
              primitiveConstant supportConstant := by
  obtain ⟨Cg, hCg, hgreen⟩ := greenFn_le
  obtain ⟨Cη, hCη, heta⟩ :=
    ρ.exists_pos_etaEpsT4_uniform_bound
  let supportConstant : ℝ := 1 + 4 * ρ.radius
  let primitiveConstant : ℝ :=
    1 + Cg * Cη + greenFn 0 * Cη
  have hsupport : 0 < supportConstant := by
    dsimp only [supportConstant]
    nlinarith [ρ.radius_pos]
  have hprimitive : 0 < primitiveConstant := by
    dsimp only [primitiveConstant]
    nlinarith [mul_nonneg hCg.le hCη.le,
      mul_nonneg (greenFn_nonneg 0) hCη.le]
  have hone : (1 : ℝ) ≤ primitiveConstant := by
    dsimp only [primitiveConstant]
    nlinarith [mul_nonneg hCg.le hCη.le,
      mul_nonneg (greenFn_nonneg 0) hCη.le]
  have hClocal :
      Cg * Cη ≤ primitiveConstant ^ 2 := by
    have hle : Cg * Cη ≤ primitiveConstant := by
      dsimp only [primitiveConstant]
      nlinarith [mul_nonneg hCg.le hCη.le,
        mul_nonneg (greenFn_nonneg 0) hCη.le]
    exact hle.trans (by nlinarith)
  have hCzero :
      greenFn 0 * Cη ≤ primitiveConstant ^ 2 := by
    have hle :
        greenFn 0 * Cη ≤ primitiveConstant := by
      dsimp only [primitiveConstant]
      nlinarith [mul_nonneg hCg.le hCη.le,
        mul_nonneg (greenFn_nonneg 0) hCη.le]
    exact hle.trans (by nlinarith)
  have hsupportBound :
      4 * ρ.radius ≤ supportConstant := by
    dsimp only [supportConstant]
    linarith
  refine
    ⟨primitiveConstant, supportConstant,
      hprimitive, hsupport, ?_⟩
  intro lam ε hlam hε hε1 hlog
  constructor
  · intro σ hσ
    rw [nonSplitPairings_one_eq] at hσ
    simp only [Finset.mem_singleton] at hσ
    subst σ
    exact
      integrable_detJ_one_pairingFinTwo
        ρ lam hε hε1
  · intro z _hz
    rw [groupedDetJAbsSum_one]
    rw [← detJ_one_eq_primitiveKernel]
    exact abs_detJ_one_pairingFinTwo_le_majorant
      ρ hCg.le hCη.le hprimitive.le hlam
        hε hε1 hlog hgreen
        (heta hε hε1) hsupportBound
        hClocal hCzero z

/-- The actual `(3.22)` estimate at `q = 1`, with one constant chosen
before the coupling and scale.  This is the completely closed base case
of P-3.5a, not an output-interface theorem. -/
theorem exists_renormC_bound_one
    (ρ : SmoothCutoff) :
    ∃ Crenorm : ℝ, 0 < Crenorm ∧
      ∀ (lam ε : ℝ),
        0 ≤ lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| →
          |renormC2q ρ lam ε 1| ≤
            ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
              (Crenorm * lam) ^ 2 := by
  obtain
    ⟨primitiveConstant, supportConstant,
      hprimitive, hsupport, hred⟩ :=
    exists_renormReductionOutput_one ρ
  obtain ⟨Crenorm, hCrenorm, hbound⟩ :=
    exists_renormC_bound_of_reduction
      hprimitive hsupport
  refine ⟨Crenorm, hCrenorm, ?_⟩
  intro lam ε hlam hε hε1 hlog
  simpa only [one_mul] using
    hbound ρ lam ε 1 hlam hε hlog
      (by omega)
      (hred lam ε hlam hε hε1
        (zero_lt_one.trans_le hlog))

end

end Anderson4D
