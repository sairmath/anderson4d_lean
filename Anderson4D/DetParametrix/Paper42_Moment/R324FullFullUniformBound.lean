import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfIntegrable
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperIteration
import Anderson4D.DetParametrix.Paper42_Moment.R324InteriorCoreEstimate

/-!
# The full/full refined-fibre branch of R-324

Paper Section 4.2 Step 1 treats a contraction whose two within-copy
pairings are full.  Such a refined fibre has no cross-copy covariance and
factors exactly into the two complete endpoint-signature half fibres.  This
file joins that exact factorization to the already proved numerical closure
of Step 1.

The only hypotheses left below are the two literal `R324Step1Reduction`
statements identifying the weighted half-fibre sums with outputs of the
successive-removal argument.  In particular, the conclusion has exactly the
`MomentRefinedIntegratedReductionData.refined_bound` shape; no target-shaped
analytic estimate is assumed.  The product of the two Step-1 logarithmic
gains is absorbed by the explicit lower bound for the integrated inserted
majorant (with support constant `1`).
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Exact weighted factorization -/

/-- After the full/full finite-fibre factorization, the complete `2m`
coupling weight splits exactly into one `m` weight on each half. -/
theorem norm_weighted_momentRefinedDeterministicTermSum_eq_fullFull_product
    (rho : SmoothCutoff) {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (lam : ℝ) (m : ℕ) (alpha beta : Z4)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e0 : MomentContraction m)
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (hp : e0.1.IsFull) (hm : e0.2.1.IsFull) :
    |lamEps lam eps| ^ (2 * m) *
        ‖momentRefinedDeterministicTermSum
          rho eps m alpha beta s r‖ =
      ‖(lamEps lam eps : ℂ) ^ m *
          (∑ kp : ReductionEndpointFiberAt e0.1,
            deterministicFullHalfIntegral
              rho eps m alpha beta kp.1)‖ *
        ‖(lamEps lam eps : ℂ) ^ m *
          (∑ km : ReductionEndpointFiberAt e0.2.1,
            deterministicFullHalfIntegral
              rho eps m (-alpha) (-beta) km.1)‖ := by
  rw [show momentRefinedDeterministicTermSum rho eps m alpha beta s r =
      ∑ e ∈ momentRefinedContractionFiber m s r,
        deterministicMomentContractionTerm rho eps m alpha beta e by rfl]
  rw [sum_momentRefinedContractionFiber_eq_fullHalfFiber_mul_of_isFull
    rho heps heps1 m alpha beta e0 he0 hp hm]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [show 2 * m = m + m by omega, pow_add]
  ring

/-! ## Step 1 numerical closure in the refined-bound shape -/

/-- **Full/full branch of `MomentRefinedIntegratedReductionData.refined_bound`.**

Assume the two weighted endpoint-fibre sums have been identified with the
successive-removal output in the precise paper vocabulary
`R324Step1Reduction`.  The proved Step-1 theorem bounds each half by
`(C lambda)^m / |log eps|`.  Their product has two inverse logarithms, while
the inserted majorant at support constant `1` needs only one; the paper
range `1 ≤ |log eps|` closes the comparison.

Thus the only missing full/full interface is the exact removal
identification for each half.  All finite-fibre, Fourier-integrability, and
numerical-majorant bookkeeping is discharged here. -/
theorem exists_fullFull_refined_bound_of_step1Reductions
    (rho : SmoothCutoff) {removalConstant : ℝ}
    (hremovalConstant : 0 < removalConstant) :
    ∃ primitiveConstant : ℝ, 0 < primitiveConstant ∧
      ∀ (lam eps : ℝ) (m : ℕ) (alpha beta : Z4),
        0 < lam → 0 < eps → eps ≤ 1 →
        1 ≤ |Real.log eps| → 1 ≤ m →
        ∀ {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
          (e0 : MomentContraction m),
          e0 ∈ momentRefinedContractionFiber m s r →
          e0.1.IsFull → e0.2.1.IsFull →
          R324Step1Reduction rho lam eps m alpha beta removalConstant
            ((lamEps lam eps : ℂ) ^ m *
              ∑ kp : ReductionEndpointFiberAt e0.1,
                deterministicFullHalfIntegral
                  rho eps m alpha beta kp.1) →
          R324Step1Reduction rho lam eps m (-alpha) (-beta)
            removalConstant
            ((lamEps lam eps : ℂ) ^ m *
              ∑ km : ReductionEndpointFiberAt e0.2.1,
                deterministicFullHalfIntegral
                  rho eps m (-alpha) (-beta) km.1) →
          |lamEps lam eps| ^ (2 * m) *
              ‖momentRefinedDeterministicTermSum
                rho eps m alpha beta s r‖ ≤
            ∫ z,
              primitiveInsertedMajorant
                primitiveConstant lam eps 1 m z
              ∂paperMeasure := by
  obtain ⟨primitiveConstant, hprimitiveConstant, hstep1⟩ :=
    exists_r324Step1_deterministic_bound rho hremovalConstant
  refine ⟨primitiveConstant, hprimitiveConstant, ?_⟩
  intro lam eps m alpha beta hlam heps heps1 hlog hm s r e0 he0 hp hright
    hleftReduction hrightReduction
  let leftHalf : ℂ :=
    ∑ kp : ReductionEndpointFiberAt e0.1,
      deterministicFullHalfIntegral rho eps m alpha beta kp.1
  let rightHalf : ℂ :=
    ∑ km : ReductionEndpointFiberAt e0.2.1,
      deterministicFullHalfIntegral rho eps m (-alpha) (-beta) km.1
  have hleft :
      ‖(lamEps lam eps : ℂ) ^ m * leftHalf‖ ≤
        (primitiveConstant * lam) ^ m / |Real.log eps| := by
    exact hstep1 lam eps m alpha beta
      ((lamEps lam eps : ℂ) ^ m * leftHalf)
      hlam heps heps1 hlog hleftReduction
  have hrightBound :
      ‖(lamEps lam eps : ℂ) ^ m * rightHalf‖ ≤
        (primitiveConstant * lam) ^ m / |Real.log eps| := by
    exact hstep1 lam eps m (-alpha) (-beta)
      ((lamEps lam eps : ℂ) ^ m * rightHalf)
      hlam heps heps1 hlog hrightReduction
  have hlogPos : 0 < |Real.log eps| := one_pos.trans_le hlog
  have hbase : 0 ≤ (primitiveConstant * lam) ^ m :=
    pow_nonneg (mul_nonneg hprimitiveConstant.le hlam.le) m
  have hhalfRhs :
      0 ≤ (primitiveConstant * lam) ^ m / |Real.log eps| :=
    div_nonneg hbase hlogPos.le
  have hproduct :
      ‖(lamEps lam eps : ℂ) ^ m * leftHalf‖ *
          ‖(lamEps lam eps : ℂ) ^ m * rightHalf‖ ≤
        ((primitiveConstant * lam) ^ m / |Real.log eps|) ^ 2 := by
    calc
      ‖(lamEps lam eps : ℂ) ^ m * leftHalf‖ *
            ‖(lamEps lam eps : ℂ) ^ m * rightHalf‖ ≤
          ((primitiveConstant * lam) ^ m / |Real.log eps|) *
            ((primitiveConstant * lam) ^ m / |Real.log eps|) :=
        mul_le_mul hleft hrightBound (norm_nonneg _) hhalfRhs
      _ = ((primitiveConstant * lam) ^ m / |Real.log eps|) ^ 2 := by
        ring
  have hsquareToSingle :
      ((primitiveConstant * lam) ^ m / |Real.log eps|) ^ 2 ≤
        (primitiveConstant * lam) ^ (2 * m) /
          |Real.log eps| := by
    have hpow :
        ((primitiveConstant * lam) ^ m) ^ 2 =
          (primitiveConstant * lam) ^ (2 * m) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [div_pow, hpow]
    have hlogSq :
        |Real.log eps| ≤ |Real.log eps| ^ 2 := by
      nlinarith [hlog]
    exact div_le_div_of_nonneg_left
      (pow_nonneg (mul_nonneg hprimitiveConstant.le hlam.le) (2 * m))
      hlogPos hlogSq
  have hlower :=
    le_integral_primitiveInsertedMajorant
      primitiveConstant lam eps 1 m heps heps1 one_pos
  have hlower' :
      (primitiveConstant * lam) ^ (2 * m) /
          |Real.log eps| ≤
        ∫ z,
          primitiveInsertedMajorant
            primitiveConstant lam eps 1 m z
          ∂paperMeasure := by
    change
      (primitiveConstant * lam) ^ (2 * m) *
          |Real.log eps|⁻¹ ≤ _
    simpa using hlower
  calc
    |lamEps lam eps| ^ (2 * m) *
          ‖momentRefinedDeterministicTermSum
            rho eps m alpha beta s r‖ =
        ‖(lamEps lam eps : ℂ) ^ m * leftHalf‖ *
          ‖(lamEps lam eps : ℂ) ^ m * rightHalf‖ := by
      simpa only [leftHalf, rightHalf] using
        norm_weighted_momentRefinedDeterministicTermSum_eq_fullFull_product
          rho heps heps1 lam m alpha beta e0 he0 hp hright
    _ ≤ ((primitiveConstant * lam) ^ m /
          |Real.log eps|) ^ 2 := hproduct
    _ ≤ (primitiveConstant * lam) ^ (2 * m) /
          |Real.log eps| := hsquareToSingle
    _ ≤ ∫ z,
          primitiveInsertedMajorant
            primitiveConstant lam eps 1 m z
          ∂paperMeasure := hlower'

end

end Anderson4D
