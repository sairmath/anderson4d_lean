import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedQuadCompositionBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324SingleProjectedMarkedPhysicalBridge

/-!
# The actual lattice-mode producer boundary for the refined quad composition

The physical projected-covariance machinery does not expose a bare
`fourierR4 ρ ξ` whose Euclidean frequency also sums to the external lattice
frequency.  Its exact factor is instead

`covarianceModeCoeff ε k = whiteNoiseFourierScale^2 * ‖symbol ε k‖^2`,

with unscaled lattice modes `k : Z4` satisfying frequency conservation.
The symbol itself is evaluated at the scaled argument `ε k`.  Therefore the
earlier abstract `R324RefinedQuadProjectedCompositionData`, which asks its
`fourierR4` arguments both to be the actual cutoff arguments and to have
unscaled conserved Euclidean frequencies, is not constructible from the
physical Fourier expansion without an additional false scaling equality.

This module records the correct producer boundary:

* an exact, integration-level removal of one marked covariance coefficient,
  retaining the complete signed open-edge physical amplitude;
* a lattice-mode composition interface for the complete signed refined quad
  harvest; and
* the paper Step 4(B) payoff from that interface.

No entity-wise norm and no sum of positive route masses is used.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Exact removal of the selected covariance coefficient -/

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- The signed physical integrand left after removing the sole marked
covariance Fourier coefficient.  Every unselected covariance remains inside
`r324MarkedResidualPhysicalOpenEdgeAmplitude`. -/
def r324MarkedResidualPhysicalOpenCovarianceIntegrand
    {m : ℕ} (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (phase : (Fin (2 * m) → T4) → ℂ)
    (k : Z4) (v : Fin (2 * m) → T4) : ℂ :=
  phase v *
    (charT4 k
        (v (r324ResidualMarkedLowerEndpoint selected) -
          v (r324ResidualMarkedUpperEndpoint π selected)) *
      ρ.r324MarkedResidualPhysicalOpenEdgeAmplitude
        ε κp κm π selected v)

/-- Pointwise exact factor removal on a retained high mode. -/
theorem r324MarkedResidualPhysicalModeTerm_mul_phase_eq_coeff_mul_open
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (phase : (Fin (2 * m) → T4) → ℂ)
    (k : Z4) (hk : k ∈ r324HighModeSet ε L)
    (v : Fin (2 * m) → T4) :
    phase v *
        ρ.r324MarkedResidualPhysicalInteriorModeTerm
          ε L κp κm π selected v k =
      ρ.covarianceModeCoeff ε k *
        ρ.r324MarkedResidualPhysicalOpenCovarianceIntegrand
          ε κp κm π selected phase k v := by
  rw [ρ.r324MarkedResidualPhysicalInteriorModeTerm_eq_highMode_mul_amplitude]
  unfold r324HighCovarianceModeTerm
  rw [Set.indicator_of_mem hk]
  unfold r324CovarianceModeTerm
    r324MarkedResidualPhysicalOpenCovarianceIntegrand
  ring

/-- Integral-level exact factor removal.  The norm is still absent: the
complete signed physical integral is factored before any estimate. -/
theorem integral_phase_mul_r324MarkedResidualPhysicalModeTerm_eq
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (phase : (Fin (2 * m) → T4) → ℂ)
    (k : Z4) (hk : k ∈ r324HighModeSet ε L) :
    (∫ v : Fin (2 * m) → T4,
        phase v *
          ρ.r324MarkedResidualPhysicalInteriorModeTerm
            ε L κp κm π selected v k
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) =
      ρ.covarianceModeCoeff ε k *
        ∫ v : Fin (2 * m) → T4,
          ρ.r324MarkedResidualPhysicalOpenCovarianceIntegrand
            ε κp κm π selected phase k v
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun v =>
    ρ.r324MarkedResidualPhysicalModeTerm_mul_phase_eq_coeff_mul_open
      ε L κp κm π selected phase k hk v)]
  exact integral_const_mul (ρ.covarianceModeCoeff ε k)
    (fun v : Fin (2 * m) → T4 =>
      ρ.r324MarkedResidualPhysicalOpenCovarianceIntegrand
        ε κp κm π selected phase k v)

end SmoothCutoff

/-! ## Correct lattice-mode composition data -/

/-- The post-factor-removal inequality for one complete signed refined quad
harvest.  Frequencies are the actual unscaled lattice modes from the
covariance expansion. -/
structure R324RefinedQuadCovarianceCompositionData
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (hm : 0 < m) (p : R324RefinedScheduleIndex m)
    (amplitude : ℝ) where
  factorCount : ℕ
  factorMode : Fin factorCount → Z4
  factorCount_pos : 0 < factorCount
  factorCount_le_trunc : factorCount ≤ truncOrder ε
  factorFrequency_sum :
    (∑ i, z4EuclideanFrequency (factorMode i)) =
      z4EuclideanFrequency (α + β)
  harvest_le_covarianceFactor :
    ∀ i : Fin factorCount,
      ‖r324BetaQuadHarvest ρ ε m α β hm
          (momentRefinedContractionFiber m p.1.1 p.2.1)‖ ≤
        amplitude * ‖ρ.covarianceModeCoeff ε (factorMode i)‖

/-- The exact frequency sum of the *actual* cutoff arguments.  It is the
scaled external frequency, not the unscaled frequency required by
`R324RefinedQuadProjectedCompositionData.factorFrequency_sum`.  This is the
precise normalization obstruction to constructing the abstract
structure from lattice covariance modes. -/
theorem R324RefinedQuadCovarianceCompositionData.actualSymbolFrequency_sum
    {ρ : SmoothCutoff} {ε amplitude : ℝ} {m : ℕ} {α β : Z4}
    {hm : 0 < m} {p : R324RefinedScheduleIndex m}
    (d : R324RefinedQuadCovarianceCompositionData
      ρ ε m α β hm p amplitude) :
    (∑ i,
        SmoothCutoff.euclideanFrequency
          (fun j => ε * (d.factorMode i j : ℝ))) =
      (ε / (2 * Real.pi)) •
        z4EuclideanFrequency (α + β) := by
  simp_rw [SmoothCutoff.euclideanFrequency_scaled_z4]
  rw [← Finset.smul_sum, d.factorFrequency_sum]

/-- Exact factorization form of the remaining algebraic obligation.  For
each composition factor the complete signed refined quad harvest must equal
that covariance coefficient times a complete signed open-factor amplitude.
This equality, after the already-proved physical single-edge identity above
is reassembled over the refined fibre, is the one missing algebraic bridge
in the repository. -/
structure R324RefinedQuadCovarianceFactorization
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (hm : 0 < m) (p : R324RefinedScheduleIndex m)
    (amplitude : ℝ) where
  factorCount : ℕ
  factorMode : Fin factorCount → Z4
  factorCount_pos : 0 < factorCount
  factorCount_le_trunc : factorCount ≤ truncOrder ε
  factorFrequency_sum :
    (∑ i, z4EuclideanFrequency (factorMode i)) =
      z4EuclideanFrequency (α + β)
  openAmplitude : Fin factorCount → ℂ
  harvest_eq_covarianceFactor_mul_openAmplitude :
    ∀ i : Fin factorCount,
      r324BetaQuadHarvest ρ ε m α β hm
          (momentRefinedContractionFiber m p.1.1 p.2.1) =
        ρ.covarianceModeCoeff ε (factorMode i) * openAmplitude i
  norm_openAmplitude_le :
    ∀ i : Fin factorCount, ‖openAmplitude i‖ ≤ amplitude

/-- Exact factorization implies the corresponding complete-signed-harvest
inequality, without splitting the refined fibre. -/
def R324RefinedQuadCovarianceFactorization.toCompositionData
    {ρ : SmoothCutoff} {ε amplitude : ℝ} {m : ℕ} {α β : Z4}
    {hm : 0 < m} {p : R324RefinedScheduleIndex m}
    (d : R324RefinedQuadCovarianceFactorization
      ρ ε m α β hm p amplitude) :
    R324RefinedQuadCovarianceCompositionData
      ρ ε m α β hm p amplitude where
  factorCount := d.factorCount
  factorMode := d.factorMode
  factorCount_pos := d.factorCount_pos
  factorCount_le_trunc := d.factorCount_le_trunc
  factorFrequency_sum := d.factorFrequency_sum
  harvest_le_covarianceFactor := by
    intro i
    rw [d.harvest_eq_covarianceFactor_mul_openAmplitude i, norm_mul]
    calc
      ‖ρ.covarianceModeCoeff ε (d.factorMode i)‖ *
          ‖d.openAmplitude i‖ ≤
        ‖ρ.covarianceModeCoeff ε (d.factorMode i)‖ * amplitude :=
      mul_le_mul_of_nonneg_left (d.norm_openAmplitude_le i) (norm_nonneg _)
      _ = amplitude * ‖ρ.covarianceModeCoeff ε (d.factorMode i)‖ := by
        ring

/-! ## Paper Step 4(B) from the actual covariance factor -/

/-- A true lattice-mode composition produces the paper's `ε²` central
bracket.  The constant is cutoff-dependent only. -/
theorem R324RefinedQuadCovarianceCompositionData.exists_harvest_le_paperScale
    {ρ : SmoothCutoff} {ε amplitude : ℝ} {m : ℕ} {α β : Z4}
    {hm : 0 < m} {p : R324RefinedScheduleIndex m}
    (d : R324RefinedQuadCovarianceCompositionData
      ρ ε m α β hm p amplitude)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hA : 0 ≤ amplitude) :
    ∃ C : ℝ, 0 < C ∧
      ‖r324BetaQuadHarvest ρ ε m α β hm
          (momentRefinedContractionFiber m p.1.1 p.2.1)‖ ≤
        (amplitude * C) * eighthOrderFrequencyDecay
          (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) := by
  obtain ⟨C, hC, hmode⟩ := ρ.exists_r324_highCovarianceModeTerm_bound
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  obtain ⟨i, hi⟩ :=
    r324Step4_exists_large_frequency_factor
      d.factorCount_pos
      (fun i => z4EuclideanFrequency (d.factorMode i))
      hε hε1 d.factorCount_le_trunc d.factorFrequency_sum
  have hk : d.factorMode i ∈ SmoothCutoff.r324HighModeSet ε
      ‖z4EuclideanFrequency (α + β)‖ := hi
  have hcoeff :
      ‖ρ.covarianceModeCoeff ε (d.factorMode i)‖ ≤
        C * eighthOrderFrequencyDecay
          (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) := by
    have hterm := hmode (z := (0 : T4)) hε hεsmall
      (norm_nonneg (z4EuclideanFrequency (α + β))) hk
    simpa only [ρ.norm_r324CovarianceModeTerm] using hterm
  refine ⟨C, hC, (d.harvest_le_covarianceFactor i).trans ?_⟩
  calc
    amplitude * ‖ρ.covarianceModeCoeff ε (d.factorMode i)‖ ≤
        amplitude *
          (C * eighthOrderFrequencyDecay
            (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖)) :=
      mul_le_mul_of_nonneg_left hcoeff hA
    _ = (amplitude * C) * eighthOrderFrequencyDecay
          (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) := by
      ring

/-! ## Uniform residual producer -/

/-- The sole remaining producer in the actual lattice-mode representation.
It asks for exact covariance-factor removal on the complete signed refined
quad harvest, uniformly on the capped range. -/
def R324RefinedQuadCovarianceFactorizationBound
    (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 / 4 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        ∀ (hm : 0 < m) (p : R324RefinedScheduleIndex m),
          Nonempty (R324RefinedQuadCovarianceFactorization
            ρ ε m α β hm p
              ((m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
                ε⁻¹ ^ (8 : ℕ)))

/-- Inequality form of the same actual lattice-mode producer. -/
def R324RefinedQuadCovarianceCompositionBound
    (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 / 4 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        ∀ (hm : 0 < m) (p : R324RefinedScheduleIndex m),
          Nonempty (R324RefinedQuadCovarianceCompositionData
            ρ ε m α β hm p
              ((m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
                ε⁻¹ ^ (8 : ℕ)))

/-- Forgetting the exact equality leaves the covariance-composition
inequality, still on the complete signed refined fibre. -/
theorem R324RefinedQuadCovarianceFactorizationBound.toCompositionBound
    {ρ : SmoothCutoff} {K : ℝ}
    (h : R324RefinedQuadCovarianceFactorizationBound ρ K) :
    R324RefinedQuadCovarianceCompositionBound ρ K := by
  intro ε m α β hε hεsmall hlog hm2 hcap hm p
  obtain ⟨d⟩ := h m α β hε hεsmall hlog hm2 hcap hm p
  exact ⟨d.toCompositionData⟩

/-- The true lattice composition closes the paper-scale refined quad ledger.
The single cutoff-dependent covariance constant is absorbed into the
geometric base. -/
theorem R324RefinedQuadCovarianceCompositionBound.exists_paperQuadHarvest
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (h : R324RefinedQuadCovarianceCompositionBound ρ K) :
    ∃ K' : ℝ, 0 ≤ K' ∧
      R324RefinedPostCollapsePaperQuadHarvestBound ρ K' := by
  obtain ⟨C, hC, hmode⟩ := ρ.exists_r324_highCovarianceModeTerm_bound
  set B : ℝ := max 1 C with hBdef
  have hB1 : (1 : ℝ) ≤ B := by
    rw [hBdef]
    exact le_max_left _ _
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  refine ⟨B * K, mul_nonneg hB0 hK, ?_⟩
  intro ε m α β hε hεsmall hlog hm2 hcap hm p
  obtain ⟨d⟩ := h m α β hε hεsmall hlog hm2 hcap hm p
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  obtain ⟨i, hi⟩ :=
    r324Step4_exists_large_frequency_factor
      d.factorCount_pos
      (fun i => z4EuclideanFrequency (d.factorMode i))
      hε hε1 d.factorCount_le_trunc d.factorFrequency_sum
  have hk : d.factorMode i ∈ SmoothCutoff.r324HighModeSet ε
      ‖z4EuclideanFrequency (α + β)‖ := hi
  have hcoeff :
      ‖ρ.covarianceModeCoeff ε (d.factorMode i)‖ ≤
        C * eighthOrderFrequencyDecay
          (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) := by
    have hterm := hmode (z := (0 : T4)) hε hεsmall
      (norm_nonneg (z4EuclideanFrequency (α + β))) hk
    simpa only [ρ.norm_r324CovarianceModeTerm] using hterm
  have hA :
      0 ≤ (m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
        ε⁻¹ ^ (8 : ℕ) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (pow_nonneg hK m))
        (pow_nonneg (abs_nonneg _) _))
      (by positivity)
  have hraw := (d.harvest_le_covarianceFactor i).trans
    (mul_le_mul_of_nonneg_left hcoeff hA)
  have hCpow : C ≤ B ^ m := by
    calc
      C ≤ B := by rw [hBdef]; exact le_max_right _ _
      _ = B ^ 1 := by ring
      _ ≤ B ^ m := pow_le_pow_right₀ hB1 (by omega)
  have hKC : K ^ m * C ≤ K ^ m * B ^ m :=
    mul_le_mul_of_nonneg_left hCpow (pow_nonneg hK m)
  set X : ℝ :=
    (m : ℝ) ^ 8 * |Real.log ε| ^ (m - 1) * ε⁻¹ ^ (8 : ℕ) *
      eighthOrderFrequencyDecay
        (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (pow_nonneg (Nat.cast_nonneg m) 8)
          (pow_nonneg (abs_nonneg _) _))
        (pow_nonneg (inv_nonneg.mpr hε.le) 8))
      (eighthOrderFrequencyDecay_nonneg _)
  calc
    ‖r324BetaQuadHarvest ρ ε m α β hm
        (momentRefinedContractionFiber m p.1.1 p.2.1)‖ ≤
      (((m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
          ε⁻¹ ^ (8 : ℕ)) * C) *
        eighthOrderFrequencyDecay
          (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) := by
      simpa only [mul_assoc] using hraw
    _ = X * (K ^ m * C) := by rw [hXdef]; ring
    _ ≤ X * (K ^ m * B ^ m) :=
      mul_le_mul_of_nonneg_left hKC hX0
    _ = (m : ℝ) ^ 8 * (B * K) ^ m *
          |Real.log ε| ^ (m - 1) *
            (ε⁻¹ ^ (8 : ℕ) *
              eighthOrderFrequencyDecay
                (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖)) := by
      rw [hXdef, mul_pow]
      ring

end

end Anderson4D
