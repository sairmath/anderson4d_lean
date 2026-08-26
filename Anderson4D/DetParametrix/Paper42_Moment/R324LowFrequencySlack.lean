import Anderson4D.DetParametrix.Paper42_Moment.R324ProjectedCovariance
import Anderson4D.PermSum.OpenEdgeWeight

/-!
# The complementary low-frequency branch in R-324

At the selected central scale, the branch `ε² L < 1` does not need a
high-frequency restriction on the chosen Fourier mode.  The cutoff symbol
is bounded by one, the target eighth-order decay is bounded below by an
absolute constant, and the two dummy chain edges cost at most `O(ε⁻⁸)`
under the natural box bound `M ≤ ε⁻¹`.

This file contains only that scalar ledger and its one-open-edge primitive
consumer.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open PlaneTree

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## Scalar low-frequency ledger -/

/-- On the central low-frequency branch, the target eighth-order decay
has the uniform lower bound `1 / 16`. -/
theorem one_div_sixteen_le_eighthOrderFrequencyDecay
    {x : ℝ} (hx : 0 ≤ x) (hxone : x < 1) :
    (1 / 16 : ℝ) ≤ eighthOrderFrequencyDecay x := by
  have hanti :
      eighthOrderFrequencyDecay 1 ≤
        eighthOrderFrequencyDecay x :=
    eighthOrderFrequencyDecay_anti hx (le_of_lt hxone)
  norm_num [eighthOrderFrequencyDecay] at hanti ⊢
  exact hanti

/-- The covariance Fourier coefficient is uniformly bounded by the fixed
white-noise half-density normalization. -/
theorem norm_covarianceModeCoeff_le_whiteNoiseScaleSq
    (ε : ℝ) (k : Z4) :
    ‖ρ.covarianceModeCoeff ε k‖ ≤
      ‖(NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2‖ := by
  have hsymbolNonneg :
      0 ≤ ‖ρ.symbol ε k‖ :=
    norm_nonneg _
  have hsymbolOne :
      ‖ρ.symbol ε k‖ ≤ 1 :=
    ρ.norm_symbol_le_one ε k
  have hsq :
      ‖ρ.symbol ε k‖ ^ 2 ≤ 1 := by
    nlinarith
  unfold covarianceModeCoeff
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hsq
      (norm_nonneg
        ((NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2))

/-- The square box penalty is bounded by `25 ε⁻⁸`.  This deliberately
uses the weaker eighth-order budget needed by the low-frequency branch;
the elementary box estimate actually loses only four powers. -/
theorem boxPenalty_sq_le_twentyfive_mul_epsInv_pow_eight
    {ε : ℝ} {M : ℕ}
    (hε : 0 < ε) (hεone : ε ≤ 1)
    (hM : (M : ℝ) ≤ ε⁻¹) :
    (1 + (2 * (M : ℝ)) ^ 2) ^ 2 ≤
      25 * (ε⁻¹) ^ 8 := by
  let r : ℝ := ε⁻¹
  have hrNonneg : 0 ≤ r := by
    dsimp only [r]
    positivity
  have hrOne : 1 ≤ r := by
    dsimp only [r]
    exact (one_le_inv₀ hε).2 hεone
  have hM' : (M : ℝ) ≤ r := by
    exact hM
  have hMsq :
      (M : ℝ) ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ (by positivity) hM' 2
  have hrSqOne : 1 ≤ r ^ 2 :=
    one_le_pow₀ hrOne
  have hbase :
      1 + (2 * (M : ℝ)) ^ 2 ≤
        5 * r ^ 2 := by
    nlinarith
  have hsq :
      (1 + (2 * (M : ℝ)) ^ 2) ^ 2 ≤
        (5 * r ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hbase 2
  have hrFourOne : 1 ≤ r ^ 4 :=
    one_le_pow₀ hrOne
  calc
    (1 + (2 * (M : ℝ)) ^ 2) ^ 2 ≤
        (5 * r ^ 2) ^ 2 := hsq
    _ = 25 * r ^ 4 := by ring
    _ = 25 * r ^ 4 * 1 := by ring
    _ ≤ 25 * r ^ 4 * r ^ 4 := by
      exact mul_le_mul_of_nonneg_left hrFourOne
        (by positivity)
    _ = 25 * r ^ 8 := by ring
    _ = 25 * (ε⁻¹) ^ 8 := by rfl

/-- Complete selected-mode scalar ledger on the complementary branch
`ε² L < 1`.  No membership assumption on `k` is present. -/
theorem exists_lowFrequency_boxPenalty_sq_mul_covarianceModeCoeff_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ε L : ℝ} {M : ℕ} {k : Z4},
        0 < ε →
        ε ≤ 1 / 4 →
        0 ≤ L →
        ε ^ 2 * L < 1 →
        (M : ℝ) ≤ ε⁻¹ →
        (1 + (2 * (M : ℝ)) ^ 2) ^ 2 *
            ‖ρ.covarianceModeCoeff ε k‖ ≤
          C * (ε⁻¹) ^ 8 *
            eighthOrderFrequencyDecay (ε ^ 2 * L) := by
  let S : ℝ :=
    ‖(NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2‖
  let C : ℝ := 400 * S
  have hS : 0 < S := by
    dsimp only [S]
    exact norm_pos_iff.mpr
      (pow_ne_zero 2
        (Complex.ofReal_ne_zero.mpr
          (ne_of_gt
            NoiseModel.whiteNoiseFourierScale_pos)))
  refine ⟨C, mul_pos (by norm_num) hS, ?_⟩
  intro ε L M k hε hεsmall hL hlow hM
  have hεone : ε ≤ 1 := by
    linarith
  have hyNonneg : 0 ≤ ε ^ 2 * L := by
    positivity
  have hdecay :
      (1 / 16 : ℝ) ≤
        eighthOrderFrequencyDecay (ε ^ 2 * L) :=
    one_div_sixteen_le_eighthOrderFrequencyDecay
      hyNonneg hlow
  have hdecayScaled :
      1 ≤ 16 *
        eighthOrderFrequencyDecay (ε ^ 2 * L) := by
    nlinarith
  have hbox :=
    boxPenalty_sq_le_twentyfive_mul_epsInv_pow_eight
      hε hεone hM
  have hcoeff :
      ‖ρ.covarianceModeCoeff ε k‖ ≤ S := by
    exact ρ.norm_covarianceModeCoeff_le_whiteNoiseScaleSq
      ε k
  have hboxNonneg :
      0 ≤ (1 + (2 * (M : ℝ)) ^ 2) ^ 2 := by
    positivity
  have hcoeffNonneg :
      0 ≤ ‖ρ.covarianceModeCoeff ε k‖ :=
    norm_nonneg _
  have hInvNonneg : 0 ≤ (ε⁻¹) ^ 8 := by
    positivity
  calc
    (1 + (2 * (M : ℝ)) ^ 2) ^ 2 *
          ‖ρ.covarianceModeCoeff ε k‖ ≤
        (25 * (ε⁻¹) ^ 8) * S :=
      mul_le_mul hbox hcoeff hcoeffNonneg
        (mul_nonneg (by norm_num) hInvNonneg)
    _ =
        (25 * S * (ε⁻¹) ^ 8) * 1 := by ring
    _ ≤
        (25 * S * (ε⁻¹) ^ 8) *
          (16 *
            eighthOrderFrequencyDecay (ε ^ 2 * L)) := by
      exact mul_le_mul_of_nonneg_left hdecayScaled
        (by positivity)
    _ =
        C * (ε⁻¹) ^ 8 *
          eighthOrderFrequencyDecay (ε ^ 2 * L) := by
      dsimp only [C]
      ring

/-! ## One-open-edge primitive consumer -/

/-- The low-central-scale counterpart of the high-frequency one-open-edge
consumer.  The selected coefficient pays the two dummy chain edges at the
explicit `ε⁻⁸` cost, with no restriction on its Fourier mode. -/
theorem exists_selectedOpenEdgeLowFrequencyPrimitiveConsumer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {t : PlaneTree} {m M : ℕ}
        {κ : PartialPairing (Fin m)}
        {a b : Fin m} {w : Fin m → HeppLeaf t}
        {Nm : HeppMarking t}
        {z : HeppLeaf t → Fin 4 → ℤ}
        {ε L : ℝ} {k : Z4},
        0 < m →
        κ a = b →
        a < b →
        κ.IsFull →
        IsPrimitive κ →
        (∀ i : Fin m, i ≠ a → i ≠ b →
          w i = w (κ i)) →
        IsAdmissible Nm M z →
        0 < ε →
        ε ≤ 1 / 4 →
        0 ≤ L →
        ε ^ 2 * L < 1 →
        (M : ℝ) ≤ ε⁻¹ →
        NoProperLeafBlock
            (openEdgeAugmentedWord w a b) ∧
          ‖ρ.covarianceModeCoeff ε k‖ *
              heppChainWeight z w ≤
            C * (ε⁻¹) ^ 8 *
                eighthOrderFrequencyDecay (ε ^ 2 * L) *
              heppChainWeight z
                (openEdgeAugmentedWord w a b) := by
  obtain ⟨C, hC, hcoeff⟩ :=
    ρ.exists_lowFrequency_boxPenalty_sq_mul_covarianceModeCoeff_bound
  refine ⟨C, hC, ?_⟩
  intro t m M κ a b w Nm z ε L k hm hκab hab
    hfull hprimitive hrespect hadm hε hεsmall hL hlow
    hM
  refine
    ⟨noProperLeafBlock_openEdgeAugmentedWord
        κ a b hκab hab hfull hprimitive w hrespect, ?_⟩
  have hweight :=
    heppChainWeight_le_boxPenalty_sq_mul_openEdgeAugmented
      hm z hadm w a b
  have hnorm : 0 ≤ ‖ρ.covarianceModeCoeff ε k‖ :=
    norm_nonneg _
  have haug :
      0 ≤ heppChainWeight z
        (openEdgeAugmentedWord w a b) :=
    heppChainWeight_nonneg _ _
  have hcoeffB :=
    hcoeff (k := k) hε hεsmall hL hlow hM
  calc
    ‖ρ.covarianceModeCoeff ε k‖ *
          heppChainWeight z w ≤
        ‖ρ.covarianceModeCoeff ε k‖ *
          ((1 + (2 * (M : ℝ)) ^ 2) ^ 2 *
            heppChainWeight z
              (openEdgeAugmentedWord w a b)) :=
      mul_le_mul_of_nonneg_left hweight hnorm
    _ =
        ((1 + (2 * (M : ℝ)) ^ 2) ^ 2 *
          ‖ρ.covarianceModeCoeff ε k‖) *
            heppChainWeight z
              (openEdgeAugmentedWord w a b) := by
      ring
    _ ≤
        (C * (ε⁻¹) ^ 8 *
          eighthOrderFrequencyDecay (ε ^ 2 * L)) *
            heppChainWeight z
              (openEdgeAugmentedWord w a b) :=
      mul_le_mul_of_nonneg_right hcoeffB haug

end SmoothCutoff

end

end Anderson4D
