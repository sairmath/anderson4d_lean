import Anderson4D.Continuum.CovariancePoissonDeterministic
import Anderson4D.Continuum.FiniteTsumProduct
import Anderson4D.DetParametrix.Paper42_Moment.R324HighFrequencySymbol

/-!
# Projected covariance for the R-324 frequency route

Paper §4.2, Step 4 replaces one occurrence of the mollified noise by
its projection onto modes of size at least `sqrt ε / 2` times the total
external shift.  After Wick contraction this is a deterministic
projection of one covariance Fourier series.  This file constructs that
countable series, proves its exact complement decomposition, and
enumerates it by `ℕ` for the routed-reduction consumer.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- One spatial Fourier mode in the complex cutoff covariance. -/
def r324CovarianceModeTerm
    (ε : ℝ) (z : T4) (k : Z4) : ℂ :=
  ρ.covarianceModeCoeff ε k * charT4 k z

theorem norm_r324CovarianceModeTerm
    (ε : ℝ) (z : T4) (k : Z4) :
    ‖ρ.r324CovarianceModeTerm ε z k‖ =
      ‖ρ.covarianceModeCoeff ε k‖ := by
  unfold r324CovarianceModeTerm
  rw [norm_mul, norm_charT4, mul_one]

theorem summable_r324CovarianceModeTerm
    {ε : ℝ} (hε : 0 < ε) (z : T4) :
    Summable (ρ.r324CovarianceModeTerm ε z) := by
  apply Summable.of_norm
  exact (ρ.summable_norm_covarianceModeCoeff hε).congr
    (fun k => (ρ.norm_r324CovarianceModeTerm ε z k).symm)

/-- The high-mode set selected by the truncation-length pigeonhole
argument. -/
def r324HighModeSet (ε L : ℝ) : Set Z4 :=
  {k |
    (Real.sqrt ε / 2) * L ≤
      ‖z4EuclideanFrequency k‖}

/-- One covariance mode retained by the Step 4 high-frequency
projection. -/
def r324HighCovarianceModeTerm
    (ε L : ℝ) (z : T4) (k : Z4) : ℂ :=
  (r324HighModeSet ε L).indicator
    (ρ.r324CovarianceModeTerm ε z) k

/-- The complementary low-frequency covariance mode. -/
def r324LowCovarianceModeTerm
    (ε L : ℝ) (z : T4) (k : Z4) : ℂ :=
  (r324HighModeSet ε L)ᶜ.indicator
    (ρ.r324CovarianceModeTerm ε z) k

/-- The complex covariance after projecting to routed high modes. -/
def r324ProjectedCovarianceC
    (ε L : ℝ) (z : T4) : ℂ :=
  ∑' k : Z4, ρ.r324HighCovarianceModeTerm ε L z k

/-- The complementary low-mode covariance. -/
def r324LowCovarianceC
    (ε L : ℝ) (z : T4) : ℂ :=
  ∑' k : Z4, ρ.r324LowCovarianceModeTerm ε L z k

theorem summable_r324HighCovarianceModeTerm
    {ε : ℝ} (hε : 0 < ε) (L : ℝ) (z : T4) :
    Summable (ρ.r324HighCovarianceModeTerm ε L z) := by
  unfold r324HighCovarianceModeTerm
  exact (ρ.summable_r324CovarianceModeTerm hε z).indicator _

theorem summable_r324LowCovarianceModeTerm
    {ε : ℝ} (hε : 0 < ε) (L : ℝ) (z : T4) :
    Summable (ρ.r324LowCovarianceModeTerm ε L z) := by
  unfold r324LowCovarianceModeTerm
  exact (ρ.summable_r324CovarianceModeTerm hε z).indicator _

theorem r324Low_add_high_mode
    (ε L : ℝ) (z : T4) (k : Z4) :
    ρ.r324LowCovarianceModeTerm ε L z k +
        ρ.r324HighCovarianceModeTerm ε L z k =
      ρ.r324CovarianceModeTerm ε z k := by
  classical
  by_cases hk : k ∈ r324HighModeSet ε L
  · simp [r324LowCovarianceModeTerm,
      r324HighCovarianceModeTerm, hk]
  · simp [r324LowCovarianceModeTerm,
      r324HighCovarianceModeTerm, hk]

/-- Exact low/high decomposition of the full covariance Fourier
series. -/
theorem complexFourierCovarianceT4_eq_low_add_projected
    {ε : ℝ} (hε : 0 < ε) (L : ℝ) (z : T4) :
    ρ.complexFourierCovarianceT4 ε z =
      ρ.r324LowCovarianceC ε L z +
        ρ.r324ProjectedCovarianceC ε L z := by
  unfold complexFourierCovarianceT4 r324LowCovarianceC
    r324ProjectedCovarianceC
  calc
    (∑' k : Z4,
        ρ.covarianceModeCoeff ε k * charT4 k z) =
        ∑' k : Z4,
          (ρ.r324LowCovarianceModeTerm ε L z k +
            ρ.r324HighCovarianceModeTerm ε L z k) := by
      apply tsum_congr
      intro k
      exact (ρ.r324Low_add_high_mode ε L z k).symm
    _ = (∑' k : Z4,
          ρ.r324LowCovarianceModeTerm ε L z k) +
        ∑' k : Z4,
          ρ.r324HighCovarianceModeTerm ε L z k :=
      (ρ.summable_r324LowCovarianceModeTerm hε L z).tsum_add
        (ρ.summable_r324HighCovarianceModeTerm hε L z)

/-- Spatial covariance equals the exact low/high Fourier decomposition,
with all normalization constants inherited from Poisson summation. -/
theorem etaEpsT4_eq_low_add_projected
    {ε : ℝ} (hε : 0 < ε) (L : ℝ) (z : T4) :
    (ρ.etaEpsT4 ε z : ℂ) =
      ρ.r324LowCovarianceC ε L z +
        ρ.r324ProjectedCovarianceC ε L z := by
  rw [← ρ.complexFourierCovarianceT4_eq_etaEpsT4 hε z]
  exact ρ.complexFourierCovarianceT4_eq_low_add_projected
    hε L z

/-- Canonical enumeration of `ℤ⁴` by natural numbers. -/
local instance : Denumerable Z4 :=
  Denumerable.ofEncodableOfInfinite Z4

def r324NatEquivZ4 : ℕ ≃ Z4 :=
  (Denumerable.eqv Z4).symm

/-- The projected covariance is genuinely an `ℕ`-indexed `tsum`, as
required by `CountableCentralRoutedMomentDecomposition`. -/
theorem r324ProjectedCovarianceC_eq_nat_tsum
    (ε L : ℝ) (z : T4) :
    ρ.r324ProjectedCovarianceC ε L z =
      ∑' a : ℕ,
        ρ.r324HighCovarianceModeTerm
          ε L z (r324NatEquivZ4 a) := by
  unfold r324ProjectedCovarianceC
  exact (r324NatEquivZ4.tsum_eq
    (ρ.r324HighCovarianceModeTerm ε L z)).symm

theorem summable_r324HighCovarianceModeTerm_nat
    {ε : ℝ} (hε : 0 < ε) (L : ℝ) (z : T4) :
    Summable fun a : ℕ =>
      ρ.r324HighCovarianceModeTerm
        ε L z (r324NatEquivZ4 a) := by
  exact (r324NatEquivZ4.summable_iff).2
    (ρ.summable_r324HighCovarianceModeTerm hε L z)

/-- Every retained projected covariance mode carries the central
Japanese-bracket payoff.  The constant depends only on the fixed
cutoff and includes the exact white-noise half-density squared. -/
theorem exists_r324_highCovarianceModeTerm_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ε L : ℝ} {z : T4} {k : Z4},
        0 < ε →
        ε ≤ 1 / 4 →
        0 ≤ L →
        k ∈ r324HighModeSet ε L →
        ‖ρ.r324CovarianceModeTerm ε z k‖ ≤
          C * eighthOrderFrequencyDecay (ε ^ 2 * L) := by
  obtain ⟨C0, hC0, hsymbol⟩ :=
    ρ.exists_r324_highFrequency_symbol_bound
  let S : ℝ :=
    ‖(NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2‖
  refine
    ⟨S * C0, mul_pos ?_ hC0,
      fun {ε L} {z} {k} hε hεsmall hL hk => ?_⟩
  · dsimp only [S]
    exact norm_pos_iff.mpr
      (pow_ne_zero 2
        (Complex.ofReal_ne_zero.mpr
          (ne_of_gt NoiseModel.whiteNoiseFourierScale_pos)))
  have hroute :
      (Real.sqrt ε / 2) * L ≤
        ‖z4EuclideanFrequency k‖ := hk
  have hsym :=
    hsymbol hε hεsmall hL hroute
  have hsymOne := ρ.norm_symbol_le_one ε k
  have hsq :
      ‖ρ.symbol ε k‖ ^ 2 ≤ ‖ρ.symbol ε k‖ := by
    nlinarith [norm_nonneg (ρ.symbol ε k)]
  rw [ρ.norm_r324CovarianceModeTerm]
  unfold covarianceModeCoeff
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  calc
    ‖(NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2‖ *
          ‖ρ.symbol ε k‖ ^ 2
        ≤ S * ‖ρ.symbol ε k‖ := by
      exact mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
    _ ≤ S *
          (C0 *
            eighthOrderFrequencyDecay (ε ^ 2 * L)) := by
      exact mul_le_mul_of_nonneg_left hsym (norm_nonneg _)
    _ = (S * C0) *
          eighthOrderFrequencyDecay (ε ^ 2 * L) := by
      ring

end SmoothCutoff

end

end Anderson4D
