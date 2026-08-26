import Anderson4D.DetParametrix.Paper42_Moment.R324InteriorCoreProof

/-!
# Shrinking the high-frequency residue (band closure)

The proved reduction leaves the signed central-decay budget open for
all central frequencies `‖freq(α+β)‖ > ε⁻¹`.  This file closes the
*routed band* `ε⁻¹ < ‖freq(α+β)‖ ≤ truncOrder ε · ε⁻¹` unconditionally
from the interior inserted-majorant estimate: at the maximal admissible
increment count `nInc = truncOrder ε` the routed argument
`‖freq‖/nInc` is still below the covariance frequency `ε⁻¹`, so the
routed decay unit is worth `ε⁸/16` and the `ε⁻⁸` endpoint sacrifice
closes the budget inequality exactly as in the low regime.

Consequently the remaining high-frequency residue is only the *very
high* regime `‖freq(α+β)‖ > truncOrder ε · ε⁻¹`, where the covariance
bracket satisfies `ε‖freq‖ > ⌊|log ε|⌋` and the paper's rapid symbol
decay first has genuine room.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- **Band closure of the signed budget.**  For central frequencies up
to `truncOrder ε · ε⁻¹` the routed decay unit at the *maximal*
increment count `nInc = truncOrder ε` is still worth `ε⁸/16`, so the
mode-decay aggregation and the `ε⁻⁸` endpoint sacrifice close the
budget inequality on the whole band. -/
theorem signedCentralDecay_ineq_of_interiorCore_bandFrequency
    {ρ : SmoothCutoff} {lam ε amplitude : ℝ} {m : ℕ}
    {primitiveConstant supportConstant : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : 0 < m)
    (hlog : 1 ≤ |Real.log ε|) (α β : Z4)
    (hcore :
      R324InteriorCoreMajorantBound ρ lam ε m
        primitiveConstant supportConstant)
    (hAmaj :
      16 * ((16 : ℝ) ^ (2 * m) *
        ∫ z, primitiveInsertedMajorant
          primitiveConstant lam ε supportConstant m z
        ∂paperMeasure) ≤ amplitude)
    (hband : ‖z4EuclideanFrequency (α + β)‖ ≤
      (truncOrder ε : ℝ) * ε⁻¹) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      (amplitude * r324EndpointLoss ε α β) *
        eighthOrderFrequencyDecay
          (((truncOrder ε : ℕ) : ℝ)⁻¹ *
            ‖z4EuclideanFrequency (α + β)‖) := by
  have hmaj0 :
      0 ≤ ∫ z, primitiveInsertedMajorant
          primitiveConstant lam ε supportConstant m z ∂paperMeasure :=
    integral_nonneg fun z =>
      primitiveInsertedMajorant_nonneg' _ _ _ _ _ z
  have hamp : 0 ≤ amplitude := le_trans (by positivity) hAmaj
  have htrunc1 : 1 ≤ truncOrder ε := one_le_truncOrder_of_abs_log hlog
  have htruncR : (0 : ℝ) < ((truncOrder ε : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one htrunc1
  have hy0 : 0 ≤ ((truncOrder ε : ℕ) : ℝ)⁻¹ *
      ‖z4EuclideanFrequency (α + β)‖ :=
    mul_nonneg (inv_nonneg.mpr htruncR.le) (norm_nonneg _)
  have hyε : ((truncOrder ε : ℕ) : ℝ)⁻¹ *
      ‖z4EuclideanFrequency (α + β)‖ ≤ ε⁻¹ := by
    rw [inv_mul_le_iff₀ htruncR]
    linarith [hband]
  have hdecayLB :
      ε ^ (8 : ℕ) / 16 ≤
        eighthOrderFrequencyDecay
          (((truncOrder ε : ℕ) : ℝ)⁻¹ *
            ‖z4EuclideanFrequency (α + β)‖) :=
    eps_pow_eight_div_sixteen_le_eighthOrderFrequencyDecay
      hε hε1 hy0 hyε
  refine (norm_deterministicMomentPairingSum_le_modeDecay_mul_card_majorant
    hε hε1 hm α β hcore).trans ?_
  have hkey :
      paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
          ((16 : ℝ) ^ (2 * m) *
            ∫ z, primitiveInsertedMajorant
              primitiveConstant lam ε supportConstant m z
            ∂paperMeasure) ≤
        (amplitude * r324EndpointLoss ε α β) * (ε ^ (8 : ℕ) / 16) := by
    have hexp :
        (amplitude * r324EndpointLoss ε α β) * (ε ^ (8 : ℕ) / 16) =
          paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
            (amplitude * (ε⁻¹ ^ (8 : ℕ) * ε ^ (8 : ℕ)) / 16) := by
      unfold r324EndpointLoss
      ring
    have hepsone : ε⁻¹ ^ (8 : ℕ) * ε ^ (8 : ℕ) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hε.ne', one_pow]
    rw [hexp, hepsone]
    have hinner :
        (16 : ℝ) ^ (2 * m) *
            ∫ z, primitiveInsertedMajorant
              primitiveConstant lam ε supportConstant m z
            ∂paperMeasure ≤ amplitude * 1 / 16 := by
      rw [mul_one]
      linarith
    exact mul_le_mul_of_nonneg_left hinner
      (mul_nonneg (paperFourthOrderModeDecay_nonneg α)
        (paperFourthOrderModeDecay_nonneg β))
  refine hkey.trans ?_
  exact mul_le_mul_of_nonneg_left hdecayLB
    (mul_nonneg hamp (r324EndpointLoss_nonneg ε α β))

/-- **The very-high-frequency residue.**  Only central frequencies
above `truncOrder ε · ε⁻¹` remain: there the covariance-scale bracket
satisfies `ε‖freq(α+β)‖ > ⌊|log ε|⌋`, the regime where the rapid decay
of the covariance symbol first has genuine room.  The band
`ε⁻¹ < ‖freq(α+β)‖ ≤ truncOrder ε · ε⁻¹` is discharged by
`signedCentralDecay_ineq_of_interiorCore_bandFrequency`, so this Prop
is strictly smaller than `R324HighCentralFrequencySignedBound`. -/
def R324VeryHighCentralFrequencySignedBound
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (amplitude : ℝ) : Prop :=
  ∀ α β : Z4,
    (truncOrder ε : ℝ) * ε⁻¹ < ‖z4EuclideanFrequency (α + β)‖ →
    R324SignedCentralDecayBudget ρ lam ε m α β amplitude

/-- The very-high residue is monotone in the amplitude. -/
theorem R324VeryHighCentralFrequencySignedBound.mono
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    {amplitude amplitude' : ℝ}
    (h : R324VeryHighCentralFrequencySignedBound ρ lam ε m amplitude)
    (hle : amplitude ≤ amplitude') :
    R324VeryHighCentralFrequencySignedBound ρ lam ε m amplitude' :=
  fun α β hfreq => (h α β hfreq).mono hle

/-- **Shrinking the high-frequency residue.**  The interior
inserted-majorant estimate and its aggregated amplitude close the band
`ε⁻¹ < ‖freq(α+β)‖ ≤ truncOrder ε · ε⁻¹` with `nInc = truncOrder ε`,
so the full high-frequency signed bound follows from the very-high
residue alone. -/
theorem r324HighCentralFrequencySignedBound_of_interiorCore_and_veryHigh
    {ρ : SmoothCutoff} {lam ε amplitude : ℝ} {m : ℕ}
    {primitiveConstant supportConstant : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : 0 < m)
    (hlog : 1 ≤ |Real.log ε|)
    (hcore :
      R324InteriorCoreMajorantBound ρ lam ε m
        primitiveConstant supportConstant)
    (hAmaj :
      16 * ((16 : ℝ) ^ (2 * m) *
        ∫ z, primitiveInsertedMajorant
          primitiveConstant lam ε supportConstant m z
        ∂paperMeasure) ≤ amplitude)
    (hveryhigh :
      R324VeryHighCentralFrequencySignedBound ρ lam ε m amplitude) :
    R324HighCentralFrequencySignedBound ρ lam ε m amplitude := by
  intro α β _hhigh
  rcases le_or_gt ‖z4EuclideanFrequency (α + β)‖
      ((truncOrder ε : ℝ) * ε⁻¹) with hband | hvery
  · exact ⟨truncOrder ε, one_le_truncOrder_of_abs_log hlog, le_refl _,
      signedCentralDecay_ineq_of_interiorCore_bandFrequency
        hε hε1 hm hlog α β hcore hAmaj hband⟩
  · exact hveryhigh α β hvery

/-- **The reduced final assembly at the very-high residue.**  The paper
bound (3.24) in its frozen `paperDeterministicMomentRHS` shape at an
`ε`-uniform outer constant follows from the interior inserted-majorant
estimate together with only the *very-high-frequency* residue of the
signed central-decay budget: central frequencies up to
`truncOrder ε · ε⁻¹` are closed unconditionally here. -/
theorem exists_deterministicMoment_paper_bound_of_interiorCore_and_veryHighFrequency
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4),
        0 < m → 0 ≤ lam → 0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        R324InteriorCoreMajorantBound ρ lam ε m
          primitiveConstant supportConstant →
        R324VeryHighCentralFrequencySignedBound ρ lam ε m
          (lamEps lam ε ^ 2 * outerConstant *
            ((16 * primitiveConstant) * lam) ^ (2 * m - 2)) →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (16 * primitiveConstant) lam ε m α β := by
  obtain ⟨Cball, Creg, hCball, hCreg, hmajUB⟩ :=
    exists_integral_primitiveInsertedMajorant_le
  refine ⟨16 * (Cball * supportConstant ^ 2 + 2 * Creg) *
    (16 * primitiveConstant) ^ 2, by positivity, ?_⟩
  intro ρ lam ε m α β hm hlam hε hεsmall hlog hcore hveryhigh
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hmaj :=
    hmajUB primitiveConstant lam ε supportConstant m hε hε1
      hsupport hlog
  have hI0 :
      0 ≤ ∫ z, primitiveInsertedMajorant
          primitiveConstant lam ε supportConstant m z ∂paperMeasure :=
    integral_nonneg fun z =>
      primitiveInsertedMajorant_nonneg' _ _ _ _ _ z
  have hAmaj :
      16 * ((16 : ℝ) ^ (2 * m) *
        ∫ z, primitiveInsertedMajorant
          primitiveConstant lam ε supportConstant m z
        ∂paperMeasure) ≤
      lamEps lam ε ^ 2 *
        (16 * (Cball * supportConstant ^ 2 + 2 * Creg) *
          (16 * primitiveConstant) ^ 2) *
        ((16 * primitiveConstant) * lam) ^ (2 * m - 2) := by
    rw [paper_amplitude_eq_majorant_budget
      (Cball * supportConstant ^ 2 + 2 * Creg)
      primitiveConstant lam ε hm]
    have hinner :
        (16 : ℝ) ^ (2 * m) *
          ∫ z, primitiveInsertedMajorant
            primitiveConstant lam ε supportConstant m z
          ∂paperMeasure ≤
        (16 : ℝ) ^ (2 * m) *
          ((primitiveConstant * lam) ^ (2 * m) *
            ((Cball * supportConstant ^ 2 + 2 * Creg) /
              |Real.log ε|)) :=
      mul_le_mul_of_nonneg_left hmaj (by positivity)
    linarith
  have hhigh :
      R324HighCentralFrequencySignedBound ρ lam ε m
        (lamEps lam ε ^ 2 *
          (16 * (Cball * supportConstant ^ 2 + 2 * Creg) *
            (16 * primitiveConstant) ^ 2) *
          ((16 * primitiveConstant) * lam) ^ (2 * m - 2)) :=
    r324HighCentralFrequencySignedBound_of_interiorCore_and_veryHigh
      hε hε1 hm hlog hcore hAmaj hveryhigh
  have hA0 :
      0 ≤ lamEps lam ε ^ 2 *
        (16 * (Cball * supportConstant ^ 2 + 2 * Creg) *
          (16 * primitiveConstant) ^ 2) *
        ((16 * primitiveConstant) * lam) ^ (2 * m - 2) :=
    le_trans (by positivity) hAmaj
  have huniform :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        lamEps lam ε ^ 2 *
          (16 * (Cball * supportConstant ^ 2 + 2 * Creg) *
            (16 * primitiveConstant) ^ 2) *
          ((16 * primitiveConstant) * lam) ^ (2 * m - 2) := by
    refine (norm_deterministicMomentPairingSum_le_modeDecay_mul_card_majorant
      hε hε1 hm α β hcore).trans ?_
    have hmd :
        paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
            ((16 : ℝ) ^ (2 * m) *
              ∫ z, primitiveInsertedMajorant
                primitiveConstant lam ε supportConstant m z
              ∂paperMeasure) ≤
          (16 : ℝ) ^ (2 * m) *
            ∫ z, primitiveInsertedMajorant
              primitiveConstant lam ε supportConstant m z
            ∂paperMeasure := by
      have h1 :
          paperFourthOrderModeDecay α * paperFourthOrderModeDecay β ≤
            1 :=
        mul_le_one₀ (paperFourthOrderModeDecay_le_one α)
          (paperFourthOrderModeDecay_nonneg β)
          (paperFourthOrderModeDecay_le_one β)
      calc
        paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
            ((16 : ℝ) ^ (2 * m) *
              ∫ z, primitiveInsertedMajorant
                primitiveConstant lam ε supportConstant m z
              ∂paperMeasure) ≤
            1 * ((16 : ℝ) ^ (2 * m) *
              ∫ z, primitiveInsertedMajorant
                primitiveConstant lam ε supportConstant m z
              ∂paperMeasure) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (16 : ℝ) ^ (2 * m) *
              ∫ z, primitiveInsertedMajorant
                primitiveConstant lam ε supportConstant m z
              ∂paperMeasure := one_mul _
    refine hmd.trans ?_
    nlinarith [hAmaj, hI0]
  have hsigned :=
    r324SignedCentralDecayBudget_of_interiorCore_and_highFrequency
      hε hε1 hm hlog α β hcore hAmaj hhigh
  have hcombined :=
    deterministicMomentPairingSum_paper_bound_of_uniform_and_signedCentralDecay
      hε hεsmall hA0 huniform hsigned
  simpa only [paperDeterministicMomentRHS] using hcombined

/-- **The sharpened complete reduced form of the deterministic moment estimate.**
The paper bound (3.24) at `ε`-uniform constants follows from exactly
two residual scalar statements: the `ε`-uniform interior-core
logarithmic budget, and the signed bound at central frequencies above
`truncOrder ε · ε⁻¹` only.  This strictly improves the proved
reduction, whose second residue began at `ε⁻¹`. -/
theorem exists_deterministicMoment_paper_bound_of_logBudget_and_veryHighFrequency
    {C supportConstant : ℝ}
    (hC : 0 < C) (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4),
        0 < m → 0 ≤ lam → 0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        R324InteriorCoreLogBudget ρ ε m C →
        R324VeryHighCentralFrequencySignedBound ρ lam ε m
          (lamEps lam ε ^ 2 * outerConstant *
            ((16 * (supportConstant / min supportConstant 1 ^ 2 * C)) *
              lam) ^ (2 * m - 2)) →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (16 * (supportConstant / min supportConstant 1 ^ 2 * C))
            lam ε m α β := by
  have hpC : 0 < supportConstant / min supportConstant 1 ^ 2 * C := by
    have hmin : 0 < min supportConstant 1 := lt_min hsupport one_pos
    positivity
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_interiorCore_and_veryHighFrequency
      hpC hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m α β hm hlam hε hεsmall hlog hbudget hveryhigh
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  exact h ρ lam ε m α β hm hlam hε hεsmall hlog
    (r324InteriorCoreMajorantBound_of_uniform_logBudget
      hm hε hε1 hlog hlam hsupport hbudget)
    hveryhigh

/-- **Literal decay-bracket corollary** of the sharpened reduction. -/
theorem exists_deterministicMoment_decay_bound_of_logBudget_and_veryHighFrequency
    {C supportConstant : ℝ}
    (hC : 0 < C) (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4),
        0 < m → 0 ≤ lam → 0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        R324InteriorCoreLogBudget ρ ε m C →
        R324VeryHighCentralFrequencySignedBound ρ lam ε m
          (lamEps lam ε ^ 2 * outerConstant *
            ((16 * (supportConstant / min supportConstant 1 ^ 2 * C)) *
              lam) ^ (2 * m - 2)) →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          lamEps lam ε ^ 2 * outerConstant *
            ((16 * (supportConstant / min supportConstant 1 ^ 2 * C)) *
              lam) ^ (2 * m - 2) *
            paperDeterministicMomentDecay ε α β := by
  have hpC : 0 < supportConstant / min supportConstant 1 ^ 2 * C := by
    have hmin : 0 < min supportConstant 1 := lt_min hsupport one_pos
    positivity
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_logBudget_and_veryHighFrequency
      hC hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m α β hm hlam hε hεsmall hlog hbudget hveryhigh
  refine (h ρ lam ε m α β hm hlam hε hεsmall hlog hbudget
    hveryhigh).trans ?_
  exact paperDeterministicMomentRHS_le_decayBracket outerConstant
    (16 * (supportConstant / min supportConstant 1 ^ 2 * C))
    lam ε m α β houter.le
    (mul_nonneg (by positivity) hlam)

end

end Anderson4D
