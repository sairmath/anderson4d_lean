import Anderson4D.DetParametrix.Paper42_Moment.R324SignedPhysicalBudget
import Anderson4D.DetParametrix.Paper42_Moment.R324KeyedDecayBudget
import Anderson4D.DetParametrix.Paper42_Moment.R324InteriorCoreEstimate

/-!
# The signed central-decay budget: low-frequency closure

This file closes the *low central-frequency* half of
`R324SignedCentralDecayBudget` unconditionally from the interior
inserted-majorant estimate (Statement 1), and isolates the exact
high-frequency residue.

* `eighthOrderFrequencyDecay_eps_scale_le` — the paper's `ε⁻⁸` endpoint
  sacrifice converts any eighth-order decay at covariance scale `ε`
  into the routed decay at every weaker scale, with no loss:
  `(1+x²)⁴ ≤ ε⁻⁸ (1+(εy)²)⁴` for `x ≤ y`.
* `norm_deterministicMomentPairingSum_le_modeDecay_mul_card_majorant` —
  the schedule decomposition, the universal per-fibre mode decay
  `16⟨α⟩⁻⁴⟨β⟩⁻⁴`, the interior estimate, and the count `16^{2m}` give
  `‖Σ‖ ≤ ⟨α⟩⁻⁴⟨β⟩⁻⁴ · 16^{2m} · ∫ inserted majorant`.
* `signedCentralDecay_ineq_of_interiorCore_lowFrequency` — for
  `‖freq(α+β)‖ ≤ ε⁻¹` the routed decay unit at one increment is worth
  `ε⁸/16`, so the `ε⁻⁸` sacrifice closes the budget inequality.
* `R324HighCentralFrequencySignedBound` — the residue: the budget's own
  `∃ nInc ≤ truncOrder ε` inequality, required only for
  `‖freq(α+β)‖ > ε⁻¹`.
* `exists_deterministicMoment_paper_bound_of_interiorCore_and_highFrequency`
  and its literal decay-bracket corollary — the frozen (3.24) shape at
  the explicit `ε`-uniform outer constant
  `16·(Cball·sC² + 2·Creg)·(16 pC)²`, from Statement 1 plus the
  high-frequency residue alone.

The amplitude ledger is exact: aggregated mass
`16·16^{2m}·∫maj ≤ 16·16^{2m}·(pC λ)^{2m}·CK/|log ε|
 = λ_ε² · [16·CK·(16 pC)²] · ((16 pC) λ)^{2m-2}`,
so the mode-decay route consumes the amplitude with no `ε` or `log`
slack, and the `ε⁻⁸` bracket is spent exactly once, on the passage
from unit frequency to `ε⁻¹`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- One quadratic bracket at scale `ε` absorbs the unit-scale bracket at
cost `ε⁻²`. -/
theorem one_add_sq_le_inv_sq_mul_one_add_eps_sq
    {ε y : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 + y ^ 2 ≤ ε⁻¹ ^ (2 : ℕ) * (1 + (ε * y) ^ 2) := by
  have hinv : (1 : ℝ) ≤ ε⁻¹ ^ (2 : ℕ) := by
    have h1 : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv_iff₀).mpr ⟨hε, hε1⟩
    calc (1 : ℝ) = 1 ^ (2 : ℕ) := by norm_num
    _ ≤ ε⁻¹ ^ (2 : ℕ) := pow_le_pow_left₀ (by norm_num) h1 2
  have hy : ε⁻¹ ^ (2 : ℕ) * (ε * y) ^ 2 = y ^ 2 := by
    field_simp
  calc
    1 + y ^ 2 ≤ ε⁻¹ ^ (2 : ℕ) * 1 + y ^ 2 := by nlinarith
    _ = ε⁻¹ ^ (2 : ℕ) * 1 + ε⁻¹ ^ (2 : ℕ) * (ε * y) ^ 2 := by
      rw [hy]
    _ = ε⁻¹ ^ (2 : ℕ) * (1 + (ε * y) ^ 2) := by ring

/-- **Scale conversion at the endpoint sacrifice.**  An eighth-order
central decay at covariance scale `ε` dominates, after paying the
paper's `ε⁻⁸` endpoint loss, the same decay at any weaker scale
`x ≤ y`; in particular at the routed increment scale `y / nInc`. -/
theorem eighthOrderFrequencyDecay_eps_scale_le
    {ε x y : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    eighthOrderFrequencyDecay (ε * y) ≤
      ε⁻¹ ^ (8 : ℕ) * eighthOrderFrequencyDecay x := by
  have hbracket : 1 + x ^ 2 ≤ ε⁻¹ ^ (2 : ℕ) * (1 + (ε * y) ^ 2) := by
    refine le_trans ?_ (one_add_sq_le_inv_sq_mul_one_add_eps_sq hε hε1)
    have : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx hxy 2
    linarith
  have hxpos : (0 : ℝ) < (1 + x ^ 2) ^ 4 := by positivity
  have hepos : (0 : ℝ) < (1 + (ε * y) ^ 2) ^ 4 := by positivity
  have hpow :
      (1 + x ^ 2) ^ 4 ≤
        ε⁻¹ ^ (8 : ℕ) * (1 + (ε * y) ^ 2) ^ 4 := by
    calc
      (1 + x ^ 2) ^ 4 ≤
          (ε⁻¹ ^ (2 : ℕ) * (1 + (ε * y) ^ 2)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hbracket 4
      _ = ε⁻¹ ^ (8 : ℕ) * (1 + (ε * y) ^ 2) ^ 4 := by ring
  unfold eighthOrderFrequencyDecay
  calc
    ((1 + (ε * y) ^ 2) ^ 4)⁻¹ =
        (1 + x ^ 2) ^ 4 *
          (((1 + x ^ 2) ^ 4)⁻¹ * ((1 + (ε * y) ^ 2) ^ 4)⁻¹) := by
      field_simp
    _ ≤ (ε⁻¹ ^ (8 : ℕ) * (1 + (ε * y) ^ 2) ^ 4) *
          (((1 + x ^ 2) ^ 4)⁻¹ * ((1 + (ε * y) ^ 2) ^ 4)⁻¹) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = ε⁻¹ ^ (8 : ℕ) * ((1 + x ^ 2) ^ 4)⁻¹ := by
      field_simp

/-- Below the covariance frequency `ε⁻¹`, the eighth-order decay unit
is worth at least `ε⁸/16`: the paper's endpoint sacrifice `ε⁻⁸` buys
the whole low-central-frequency regime. -/
theorem eps_pow_eight_div_sixteen_le_eighthOrderFrequencyDecay
    {ε y : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hy : 0 ≤ y) (hyε : y ≤ ε⁻¹) :
    ε ^ (8 : ℕ) / 16 ≤ eighthOrderFrequencyDecay y := by
  refine le_trans ?_ (eighthOrderFrequencyDecay_anti hy hyε)
  have hinv : (1 : ℝ) ≤ ε⁻¹ ^ 2 := by
    have h1 : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv_iff₀).mpr ⟨hε, hε1⟩
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
    _ ≤ ε⁻¹ ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
  have hbracket : 1 + (ε⁻¹) ^ 2 ≤ 2 * ε⁻¹ ^ 2 := by linarith
  have hpow :
      (1 + (ε⁻¹) ^ 2) ^ 4 ≤ 16 * ε⁻¹ ^ (8 : ℕ) := by
    calc
      (1 + (ε⁻¹) ^ 2) ^ 4 ≤ (2 * ε⁻¹ ^ 2) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hbracket 4
      _ = 16 * ε⁻¹ ^ (8 : ℕ) := by ring
  unfold eighthOrderFrequencyDecay
  have h16 : (0 : ℝ) < 16 * ε⁻¹ ^ (8 : ℕ) := by positivity
  have hle := inv_anti₀ (by positivity) hpow
  refine le_trans (le_of_eq ?_) hle
  rw [mul_inv, ← inv_pow, inv_inv]
  ring

/-- **Mode-decay aggregation over the refined schedule set.**  The
interior inserted-majorant estimate (Statement 1) turns the universal
per-fibre mode decay into a bound on the full signed pairing sum by
`⟨α⟩⁻⁴⟨β⟩⁻⁴` times `16^{2m}` copies of the integrated majorant. -/
theorem norm_deterministicMomentPairingSum_le_modeDecay_mul_card_majorant
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    {primitiveConstant supportConstant : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : 0 < m) (α β : Z4)
    (hcore :
      R324InteriorCoreMajorantBound ρ lam ε m
        primitiveConstant supportConstant) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
        ((16 : ℝ) ^ (2 * m) *
          ∫ z, primitiveInsertedMajorant
            primitiveConstant lam ε supportConstant m z
          ∂paperMeasure) := by
  have hmaj0 :
      0 ≤ ∫ z, primitiveInsertedMajorant
          primitiveConstant lam ε supportConstant m z ∂paperMeasure :=
    integral_nonneg fun z =>
      primitiveInsertedMajorant_nonneg' _ _ _ _ _ z
  rw [deterministicMomentPairingSum_eq_sum_refinedPhysicalIntegral
    ρ lam hε hε1 α β]
  rw [norm_mul, norm_pow, Complex.norm_real]
  calc
    |lamEps lam ε| ^ (2 * m) *
        ‖∑ p : R324RefinedScheduleIndex m,
          r324RefinedPhysicalIntegral ρ ε m α β p‖ ≤
        |lamEps lam ε| ^ (2 * m) *
          ∑ p : R324RefinedScheduleIndex m,
            ‖r324RefinedPhysicalIntegral ρ ε m α β p‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _)
        (pow_nonneg (abs_nonneg _) _)
    _ = ∑ p : R324RefinedScheduleIndex m,
          |lamEps lam ε| ^ (2 * m) *
            ‖r324RefinedPhysicalIntegral ρ ε m α β p‖ := by
      rw [Finset.mul_sum]
    _ ≤ ∑ p : R324RefinedScheduleIndex m,
          paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
            ∫ z, primitiveInsertedMajorant
              primitiveConstant lam ε supportConstant m z
            ∂paperMeasure := by
      refine Finset.sum_le_sum fun p _ => ?_
      have hphys :=
        norm_r324RefinedPhysicalIntegral_le_modeDecay_mul_interiorCore
          ρ hε hε1 hm α β p
      have hstep :
          |lamEps lam ε| ^ (2 * m) *
              ‖r324RefinedPhysicalIntegral ρ ε m α β p‖ ≤
            paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
              (16 * (|lamEps lam ε| ^ (2 * m) *
                r324RefinedInteriorCoreIntegral ρ ε m p)) := by
        calc
          |lamEps lam ε| ^ (2 * m) *
              ‖r324RefinedPhysicalIntegral ρ ε m α β p‖ ≤
              |lamEps lam ε| ^ (2 * m) *
                (16 * paperFourthOrderModeDecay α *
                    paperFourthOrderModeDecay β *
                  r324RefinedInteriorCoreIntegral ρ ε m p) :=
            mul_le_mul_of_nonneg_left hphys
              (pow_nonneg (abs_nonneg _) _)
          _ = paperFourthOrderModeDecay α *
                paperFourthOrderModeDecay β *
                (16 * (|lamEps lam ε| ^ (2 * m) *
                  r324RefinedInteriorCoreIntegral ρ ε m p)) := by
            ring
      exact hstep.trans
        (mul_le_mul_of_nonneg_left (hcore p)
          (mul_nonneg (paperFourthOrderModeDecay_nonneg α)
            (paperFourthOrderModeDecay_nonneg β)))
    _ = (Fintype.card (R324RefinedScheduleIndex m) : ℝ) *
          (paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
            ∫ z, primitiveInsertedMajorant
              primitiveConstant lam ε supportConstant m z
            ∂paperMeasure) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
          ((16 : ℝ) ^ (2 * m) *
            ∫ z, primitiveInsertedMajorant
              primitiveConstant lam ε supportConstant m z
            ∂paperMeasure) := by
      have hcard : (Fintype.card (R324RefinedScheduleIndex m) : ℝ) ≤
          (16 : ℝ) ^ (2 * m) := by
        calc
          (Fintype.card (R324RefinedScheduleIndex m) : ℝ) ≤
              ((16 ^ (2 * m) : ℕ) : ℝ) := by
            exact_mod_cast card_r324RefinedScheduleIndex_le m
          _ = (16 : ℝ) ^ (2 * m) := by push_cast; ring
      calc
        (Fintype.card (R324RefinedScheduleIndex m) : ℝ) *
            (paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
              ∫ z, primitiveInsertedMajorant
                primitiveConstant lam ε supportConstant m z
              ∂paperMeasure) ≤
            (16 : ℝ) ^ (2 * m) *
              (paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
                ∫ z, primitiveInsertedMajorant
                  primitiveConstant lam ε supportConstant m z
                ∂paperMeasure) := by
          refine mul_le_mul_of_nonneg_right hcard ?_
          exact mul_nonneg
            (mul_nonneg (paperFourthOrderModeDecay_nonneg α)
              (paperFourthOrderModeDecay_nonneg β)) hmaj0
        _ = paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
              ((16 : ℝ) ^ (2 * m) *
                ∫ z, primitiveInsertedMajorant
                  primitiveConstant lam ε supportConstant m z
                ∂paperMeasure) := by
          ring

/-- **Low central-frequency branch of the signed budget.**  Below the
covariance frequency `ε⁻¹` the routed decay unit at one increment is
worth `ε⁸/16`, so the mode-decay aggregation plus the paper's `ε⁻⁸`
endpoint sacrifice already deliver the routed inequality. -/
theorem signedCentralDecay_ineq_of_interiorCore_lowFrequency
    {ρ : SmoothCutoff} {lam ε amplitude : ℝ} {m : ℕ}
    {primitiveConstant supportConstant : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : 0 < m) (α β : Z4)
    (hcore :
      R324InteriorCoreMajorantBound ρ lam ε m
        primitiveConstant supportConstant)
    (hAmaj :
      16 * ((16 : ℝ) ^ (2 * m) *
        ∫ z, primitiveInsertedMajorant
          primitiveConstant lam ε supportConstant m z
        ∂paperMeasure) ≤ amplitude)
    (hlow : ‖z4EuclideanFrequency (α + β)‖ ≤ ε⁻¹) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      (amplitude * r324EndpointLoss ε α β) *
        eighthOrderFrequencyDecay
          (((1 : ℕ) : ℝ)⁻¹ * ‖z4EuclideanFrequency (α + β)‖) := by
  have hmaj0 :
      0 ≤ ∫ z, primitiveInsertedMajorant
          primitiveConstant lam ε supportConstant m z ∂paperMeasure :=
    integral_nonneg fun z =>
      primitiveInsertedMajorant_nonneg' _ _ _ _ _ z
  have hM0 : 0 ≤ (16 : ℝ) ^ (2 * m) *
      ∫ z, primitiveInsertedMajorant
        primitiveConstant lam ε supportConstant m z ∂paperMeasure := by
    positivity
  have hamp : 0 ≤ amplitude := le_trans (by linarith) hAmaj
  have hfreq : (((1 : ℕ) : ℝ)⁻¹ * ‖z4EuclideanFrequency (α + β)‖) =
      ‖z4EuclideanFrequency (α + β)‖ := by
    norm_num
  have hdecayLB :
      ε ^ (8 : ℕ) / 16 ≤
        eighthOrderFrequencyDecay
          (((1 : ℕ) : ℝ)⁻¹ * ‖z4EuclideanFrequency (α + β)‖) := by
    rw [hfreq]
    exact eps_pow_eight_div_sixteen_le_eighthOrderFrequencyDecay
      hε hε1 (norm_nonneg _) hlow
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

/-- **The precise residual oscillation statement in the high regime.**
Only central frequencies above the covariance scale `ε⁻¹` remain: there
the signed pairing sum must carry one eighth-order decay unit at unit
lattice scale beyond the endpoint loss.  The complementary regime
`‖freq(α+β)‖ ≤ ε⁻¹` is discharged unconditionally by
`signedCentralDecay_ineq_of_interiorCore_lowFrequency`, so this Prop is
strictly smaller than `R324SignedCentralDecayBudget`. -/
def R324HighCentralFrequencySignedBound
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (amplitude : ℝ) : Prop :=
  ∀ α β : Z4,
    ε⁻¹ < ‖z4EuclideanFrequency (α + β)‖ →
    ∃ nInc : ℕ, 1 ≤ nInc ∧ nInc ≤ truncOrder ε ∧
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        (amplitude * r324EndpointLoss ε α β) *
          eighthOrderFrequencyDecay
            ((nInc : ℝ)⁻¹ * ‖z4EuclideanFrequency (α + β)‖)

/-- **Statement 2 from Statement 1 and the high-frequency residue.**
The full signed central-decay budget follows, at one routed increment,
from the interior inserted-majorant estimate (which covers all central
frequencies up to `ε⁻¹`) together with the high-frequency signed
bound. -/
theorem r324SignedCentralDecayBudget_of_interiorCore_and_highFrequency
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
    (hhigh :
      R324HighCentralFrequencySignedBound ρ lam ε m amplitude) :
    R324SignedCentralDecayBudget ρ lam ε m α β amplitude := by
  rcases le_or_gt ‖z4EuclideanFrequency (α + β)‖ ε⁻¹ with hlow | hhi
  · exact ⟨1, le_refl 1, one_le_truncOrder_of_abs_log hlog,
      signedCentralDecay_ineq_of_interiorCore_lowFrequency
        hε hε1 hm α β hcore hAmaj hlow⟩
  · exact hhigh α β hhi

/-- `λ_ε² = λ²/|log ε|`. -/
theorem lamEps_sq_eq (lam ε : ℝ) :
    lamEps lam ε ^ 2 = lam ^ 2 / |Real.log ε| := by
  unfold lamEps
  rw [div_pow, Real.sq_sqrt (abs_nonneg _)]

/-- The paper-shaped amplitude at `outerConstant = 16·CK·(16 pC)²`
matches the aggregated majorant budget exactly. -/
theorem paper_amplitude_eq_majorant_budget
    (CK primitiveConstant lam ε : ℝ) {m : ℕ} (hm : 0 < m) :
    lamEps lam ε ^ 2 *
        (16 * CK * (16 * primitiveConstant) ^ 2) *
        ((16 * primitiveConstant) * lam) ^ (2 * m - 2) =
      16 * ((16 : ℝ) ^ (2 * m) *
        ((primitiveConstant * lam) ^ (2 * m) *
          (CK / |Real.log ε|))) := by
  have h2m : (2 * m - 2) + 2 = 2 * m := by omega
  have h16pow :
      (16 : ℝ) ^ (2 * m) * (primitiveConstant * lam) ^ (2 * m) =
        ((16 * primitiveConstant) * lam) ^ (2 * m) := by
    rw [← mul_pow, ← mul_assoc]
  have hX :
      ((16 * primitiveConstant) * lam) ^ (2 * m) =
        ((16 * primitiveConstant) * lam) ^ (2 * m - 2) *
          ((16 * primitiveConstant) * lam) ^ 2 := by
    rw [← pow_add, h2m]
  rw [lamEps_sq_eq]
  calc
    lam ^ 2 / |Real.log ε| *
        (16 * CK * (16 * primitiveConstant) ^ 2) *
        ((16 * primitiveConstant) * lam) ^ (2 * m - 2) =
      16 * (((16 * primitiveConstant) * lam) ^ (2 * m - 2) *
          ((16 * primitiveConstant) * lam) ^ 2 *
        (CK / |Real.log ε|)) := by
      ring
    _ = 16 * (((16 * primitiveConstant) * lam) ^ (2 * m) *
          (CK / |Real.log ε|)) := by
      rw [hX]
    _ = 16 * ((16 : ℝ) ^ (2 * m) *
          ((primitiveConstant * lam) ^ (2 * m) *
            (CK / |Real.log ε|))) := by
      rw [← h16pow]
      ring

/-- **The reduced final assembly.**  The paper bound (3.24), in its
frozen `paperDeterministicMomentRHS` shape at an `ε`-uniform outer
constant, follows from the interior inserted-majorant estimate
(Statement 1) together with only the *high-frequency residue* of the
signed central-decay budget: central frequencies `≤ ε⁻¹` are closed
unconditionally here.  The outer constant is explicit:
`16·(Cball·sC² + 2·Creg)·(16 pC)²` with `Cball, Creg` the universal
majorant integration constants. -/
theorem exists_deterministicMoment_paper_bound_of_interiorCore_and_highFrequency
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4),
        0 < m → 0 ≤ lam → 0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        R324InteriorCoreMajorantBound ρ lam ε m
          primitiveConstant supportConstant →
        R324HighCentralFrequencySignedBound ρ lam ε m
          (lamEps lam ε ^ 2 * outerConstant *
            ((16 * primitiveConstant) * lam) ^ (2 * m - 2)) →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (16 * primitiveConstant) lam ε m α β := by
  obtain ⟨Cball, Creg, hCball, hCreg, hmajUB⟩ :=
    exists_integral_primitiveInsertedMajorant_le
  refine ⟨16 * (Cball * supportConstant ^ 2 + 2 * Creg) *
    (16 * primitiveConstant) ^ 2, by positivity, ?_⟩
  intro ρ lam ε m α β hm hlam hε hεsmall hlog hcore hhigh
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

/-- **Literal decay-bracket corollary** of the reduced assembly: the
`min` bracket is bounded by the explicit
`ε⁻⁸⟨α⟩⁻⁴⟨β⟩⁻⁴⟨ε²(α+β)⟩⁻⁸` decay of P-3.5b-det. -/
theorem exists_deterministicMoment_decay_bound_of_interiorCore_and_highFrequency
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4),
        0 < m → 0 ≤ lam → 0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        R324InteriorCoreMajorantBound ρ lam ε m
          primitiveConstant supportConstant →
        R324HighCentralFrequencySignedBound ρ lam ε m
          (lamEps lam ε ^ 2 * outerConstant *
            ((16 * primitiveConstant) * lam) ^ (2 * m - 2)) →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          lamEps lam ε ^ 2 * outerConstant *
            ((16 * primitiveConstant) * lam) ^ (2 * m - 2) *
            paperDeterministicMomentDecay ε α β := by
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_interiorCore_and_highFrequency
      hprimitive hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m α β hm hlam hε hεsmall hlog hcore hhigh
  refine (h ρ lam ε m α β hm hlam hε hεsmall hlog hcore hhigh).trans ?_
  exact paperDeterministicMomentRHS_le_decayBracket outerConstant
    (16 * primitiveConstant) lam ε m α β houter.le
    (mul_nonneg (by positivity) hlam)

/-- The signed central-decay budget is monotone in the amplitude. -/
theorem R324SignedCentralDecayBudget.mono
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {α β : Z4}
    {amplitude amplitude' : ℝ}
    (h : R324SignedCentralDecayBudget ρ lam ε m α β amplitude)
    (hle : amplitude ≤ amplitude') :
    R324SignedCentralDecayBudget ρ lam ε m α β amplitude' := by
  obtain ⟨nInc, hn, hntrunc, hbound⟩ := h
  refine ⟨nInc, hn, hntrunc, hbound.trans ?_⟩
  have hloss := r324EndpointLoss_nonneg ε α β
  have hdecay := eighthOrderFrequencyDecay_nonneg
    ((nInc : ℝ)⁻¹ * ‖z4EuclideanFrequency (α + β)‖)
  apply mul_le_mul_of_nonneg_right _ hdecay
  exact mul_le_mul_of_nonneg_right hle hloss

end

end Anderson4D
