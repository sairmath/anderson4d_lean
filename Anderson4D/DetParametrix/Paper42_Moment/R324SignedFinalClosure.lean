import Anderson4D.DetParametrix.Paper42_Moment.R324FinalDeterministicClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324CountableFinalClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324SignedRoutedEndpointBudget

/-!
# Final R-324 closure from the signed phase-A certificate

The uniform and routed branches of paper (3.24) are proved by different
integrations and therefore initially choose different harmless constants.
This file replaces both by their maximum and enlarges the routed power base
from `2 * primitiveConstant` to the uniform branch's
`16 * primitiveConstant`.  The resulting theorem consumes the two genuine
upstream outputs of Steps 1--4 and concludes the literal paper bracket with
one common named constant.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- **Signed constructive closure of deterministic R-324.**

The first input is the integrated refined primitive collapse used by the
uniform branch.  The second is the signed, endpoint-case-indexed phase-A
certificate used by the countable routing branch.  Neither input contains a
moment bound.  A single outer constant, chosen before the cutoff, coupling,
scale, order, and Fourier modes, controls both branches. -/
theorem
    exists_deterministicMoment_paper_bound_of_refinedIntegrated_and_signedCollapse
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
        (hm : 0 < m) (α β : Z4),
        0 ≤ lam →
        0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        m ≤ truncOrder ε →
        MomentRefinedIntegratedReductionOutputAt
          ρ lam ε m α β primitiveConstant supportConstant →
        ρ.SignedRoutedPrimitiveSlotCollapseData
          lam ε m hm primitiveConstant supportConstant →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (16 * primitiveConstant) lam ε m α β := by
  obtain ⟨uniformConstant, huniformConstant, huniform⟩ :=
    exists_deterministicMoment_uniform_bound_of_refinedIntegratedReduction
      hprimitive hsupport
  obtain ⟨routedConstant, hroutedConstant, hrouted⟩ :=
    SmoothCutoff.exists_countableCentralRoutedMomentReductionOutput_of_signedPrimitiveCollapse
      hprimitive hsupport
  let outerConstant : ℝ :=
    max uniformConstant routedConstant
  have houterConstant : 0 < outerConstant := by
    dsimp only [outerConstant]
    exact huniformConstant.trans_le
      (le_max_left uniformConstant routedConstant)
  refine ⟨outerConstant, houterConstant, ?_⟩
  intro ρ lam ε m hm α β
    hlam hε hεsmall hlog hmtrunc
    hrefined hsigned
  have hm' : 1 ≤ m := by
    omega
  have hε1 : ε ≤ 1 :=
    hεsmall.trans (by norm_num)
  let commonAmplitude : ℝ :=
    lamEps lam ε ^ 2 * outerConstant *
      ((16 * primitiveConstant) * lam) ^ (2 * m - 2)
  have hcommon_nonneg : 0 ≤ commonAmplitude := by
    dsimp only [commonAmplitude]
    positivity
  have huniformRaw :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        lamEps lam ε ^ 2 * uniformConstant *
          ((16 * primitiveConstant) * lam) ^
            (2 * m - 2) :=
    huniform ρ lam ε m α β
      hlam hε hε1 hlog hm' hrefined
  have huniformCommon :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        commonAmplitude := by
    apply huniformRaw.trans
    dsimp only [commonAmplitude, outerConstant]
    gcongr
    exact le_max_left uniformConstant routedConstant
  have hroutedRaw :
      CountableCentralRoutedMomentReductionOutput
        ρ lam ε m α β
        ((lamEps lam ε ^ 2 * routedConstant *
            ((2 * primitiveConstant) * lam) ^
              (2 * m - 2)) *
          r324EndpointLoss ε α β) :=
    hrouted ρ lam ε m hm α β
      hlam hε hεsmall hlog hmtrunc hsigned
  have hbase_nonneg :
      0 ≤ (2 * primitiveConstant) * lam := by
    positivity
  have hbase_le :
      (2 * primitiveConstant) * lam ≤
        (16 * primitiveConstant) * lam := by
    nlinarith [hprimitive.le, hlam]
  have hpower_le :
      ((2 * primitiveConstant) * lam) ^
          (2 * m - 2) ≤
        ((16 * primitiveConstant) * lam) ^
          (2 * m - 2) :=
    pow_le_pow_left₀ hbase_nonneg hbase_le _
  have hrouteAmplitude :
      lamEps lam ε ^ 2 * routedConstant *
          ((2 * primitiveConstant) * lam) ^
            (2 * m - 2) ≤
        commonAmplitude := by
    dsimp only [commonAmplitude, outerConstant]
    have hfront :
        lamEps lam ε ^ 2 * routedConstant ≤
          lamEps lam ε ^ 2 *
            max uniformConstant routedConstant :=
      mul_le_mul_of_nonneg_left
        (le_max_right uniformConstant routedConstant)
        (sq_nonneg _)
    exact mul_le_mul hfront hpower_le
      (pow_nonneg hbase_nonneg _)
      (mul_nonneg (sq_nonneg _)
        (le_max_of_le_right hroutedConstant.le))
  have hroutedCommon :
      CountableCentralRoutedMomentReductionOutput
        ρ lam ε m α β
          (commonAmplitude *
            r324EndpointLoss ε α β) := by
    apply hroutedRaw.mono
    exact mul_le_mul_of_nonneg_right hrouteAmplitude
      (r324EndpointLoss_nonneg ε α β)
  have hcombined :=
    deterministicMomentPairingSum_paper_bound_of_uniform_and_countable
      hε hεsmall huniformCommon hroutedCommon (le_refl _)
  simpa only [paperDeterministicMomentRHS, commonAmplitude] using
    hcombined

end

end Anderson4D
