import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedPostCollapseBracketReduction
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperStep4

/-!
# Signed refined-quad bridge to the paper Step 4(B) composition factor

The proved `CountableCentralRoutedMomentDecomposition` is tied to the
*full* `deterministicMomentPairingSum`; it cannot be specialized to one
`R324RefinedScheduleIndex` without a new exact representation theorem.
Moreover its existing concrete producers estimate a positive sum of
configuration weights, whereas the refined bracket must retain the complete
signed fibre sum.

This module therefore records the deepest cancellation-preserving bridge.
For one refined fibre, `R324RefinedQuadSignedCompositionData` attaches the
frequency increments of one operator composition directly to the complete
signed `r324BetaQuadHarvest`.  There is no entity-wise norm and no route-mass
sum.  The paper's Step 4(B) pigeonhole then gives the `ε^2`-scale bracket.

The scale is important: Step 4(B) proves
`eighthOrderFrequencyDecay (ε^2 * ‖freq (α+β)‖)`.  It does not imply the
stronger `ε`-scale bracket required by `R324HdetBracketLedgerBound`.  The
output here is consequently a separate paper-scale interface; no false
adapter to the Hdet ledger is provided.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

/-! ## A composition attached to the complete signed quad harvest -/

/-- One paper Step 4(B) composition for a complete signed refined-fibre
quadruple harvest.  The final field is deliberately a bound on the entire
harvest for every factor of the composition.  Thus cancellation inside the
refined fibre has already occurred before the norm is taken. -/
structure R324RefinedQuadSignedCompositionData
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (hm : 0 < m) (p : R324RefinedScheduleIndex m)
    (amplitude : ℝ) where
  incrementCount : ℕ
  increment :
    Fin incrementCount → EuclideanSpace ℝ (Fin dim)
  incrementCount_pos : 0 < incrementCount
  incrementCount_le_trunc : incrementCount ≤ truncOrder ε
  increment_sum :
    (∑ i, increment i) = z4EuclideanFrequency (α + β)
  harvest_le_increment_decay :
    ∀ i : Fin incrementCount,
      ‖r324BetaQuadHarvest ρ ε m α β hm
          (momentRefinedContractionFiber m p.1.1 p.2.1)‖ ≤
        amplitude * eighthOrderFrequencyDecay ‖increment i‖

/-- The Step 4(B) pigeonhole, replayed on one complete signed quad harvest.
No summation of positive route weights occurs: the sole estimated value is
the full `r324BetaQuadHarvest`. -/
theorem R324RefinedQuadSignedCompositionData.harvest_le_paperScale
    {ρ : SmoothCutoff} {ε amplitude : ℝ} {m : ℕ} {α β : Z4}
    {hm : 0 < m} {p : R324RefinedScheduleIndex m}
    (d : R324RefinedQuadSignedCompositionData
      ρ ε m α β hm p amplitude)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hA : 0 ≤ amplitude) :
    ‖r324BetaQuadHarvest ρ ε m α β hm
        (momentRefinedContractionFiber m p.1.1 p.2.1)‖ ≤
      amplitude * eighthOrderFrequencyDecay
        (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) := by
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  obtain ⟨i, hi⟩ :=
    r324Step4_exists_large_frequency_factor
      d.incrementCount_pos d.increment
      hε hε1 d.incrementCount_le_trunc d.increment_sum
  have hdecay :
      eighthOrderFrequencyDecay ‖d.increment i‖ ≤
        eighthOrderFrequencyDecay
          (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) :=
    truncation_routed_decay_le_eps_sq_decay
      hε hεsmall (norm_nonneg _) hi
  exact (d.harvest_le_increment_decay i).trans
    (mul_le_mul_of_nonneg_left hdecay hA)

/-! ## The exact projected-factor residue -/

/-- Pre-decay representation of the same signed composition.  Each factor is
an actual Fourier argument of the cutoff, the factor frequencies conserve
`α+β`, and removing any one cutoff factor leaves a common signed amplitude
bound on the *whole* refined quad harvest.

No theorem in the current repository constructs this structure from
`r324BetaQuadHarvest`; that missing representation equality/inequality is the
precise gap between the physical signed harvest and the already-proved
Schwartz decay of the projected symbol. -/
structure R324RefinedQuadProjectedCompositionData
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (hm : 0 < m) (p : R324RefinedScheduleIndex m)
    (amplitude : ℝ) where
  factorCount : ℕ
  factorArgument : Fin factorCount → R4
  factorCount_pos : 0 < factorCount
  factorCount_le_trunc : factorCount ≤ truncOrder ε
  factorFrequency_sum :
    (∑ i, SmoothCutoff.euclideanFrequency (factorArgument i)) =
      z4EuclideanFrequency (α + β)
  harvest_le_factorSymbol :
    ∀ i : Fin factorCount,
      ‖r324BetaQuadHarvest ρ ε m α β hm
          (momentRefinedContractionFiber m p.1.1 p.2.1)‖ ≤
        amplitude * ‖fourierR4 ρ (factorArgument i)‖

/-- The cutoff's unconditional Schwartz bound converts a genuine projected
factor representation into the post-projection signed composition data.
The cutoff constant is fixed before all scale, order and mode parameters. -/
theorem R324RefinedQuadProjectedCompositionData.toSignedComposition
    {ρ : SmoothCutoff} {ε amplitude : ℝ} {m : ℕ} {α β : Z4}
    {hm : 0 < m} {p : R324RefinedScheduleIndex m}
    (d : R324RefinedQuadProjectedCompositionData
      ρ ε m α β hm p amplitude)
    (hA : 0 ≤ amplitude) :
    ∃ C : ℝ, 0 < C ∧
      Nonempty (R324RefinedQuadSignedCompositionData
        ρ ε m α β hm p (amplitude * C)) := by
  obtain ⟨C, hC, hsymbol⟩ :=
    r324Step4_exists_symbol_eighthOrder_decay ρ
  refine ⟨C, hC, ⟨{
    incrementCount := d.factorCount
    increment := fun i =>
      SmoothCutoff.euclideanFrequency (d.factorArgument i)
    incrementCount_pos := d.factorCount_pos
    incrementCount_le_trunc := d.factorCount_le_trunc
    increment_sum := d.factorFrequency_sum
    harvest_le_increment_decay := ?_
  }⟩⟩
  intro i
  calc
    ‖r324BetaQuadHarvest ρ ε m α β hm
        (momentRefinedContractionFiber m p.1.1 p.2.1)‖ ≤
      amplitude * ‖fourierR4 ρ (d.factorArgument i)‖ :=
        d.harvest_le_factorSymbol i
    _ ≤ amplitude *
        (C * eighthOrderFrequencyDecay
          ‖SmoothCutoff.euclideanFrequency (d.factorArgument i)‖) :=
      mul_le_mul_of_nonneg_left (hsymbol (d.factorArgument i)) hA
    _ = (amplitude * C) *
        eighthOrderFrequencyDecay
          ‖SmoothCutoff.euclideanFrequency (d.factorArgument i)‖ := by
      ring

/-- A genuine projected-factor representation therefore yields the paper
`ε²`-scale decay of the whole signed quad harvest. -/
theorem R324RefinedQuadProjectedCompositionData.exists_harvest_le_paperScale
    {ρ : SmoothCutoff} {ε amplitude : ℝ} {m : ℕ} {α β : Z4}
    {hm : 0 < m} {p : R324RefinedScheduleIndex m}
    (d : R324RefinedQuadProjectedCompositionData
      ρ ε m α β hm p amplitude)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hA : 0 ≤ amplitude) :
    ∃ C : ℝ, 0 < C ∧
      ‖r324BetaQuadHarvest ρ ε m α β hm
          (momentRefinedContractionFiber m p.1.1 p.2.1)‖ ≤
        (amplitude * C) * eighthOrderFrequencyDecay
          (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) := by
  obtain ⟨C, hC, ⟨d'⟩⟩ := d.toSignedComposition hA
  refine ⟨C, hC, d'.harvest_le_paperScale hε hεsmall ?_⟩
  exact mul_nonneg hA hC.le

/-! ## Uniform paper-scale interfaces -/

/-- The sole post-projection producer obligation, uniformly on the capped
range.  It is a composition statement about the complete signed refined
fibre, not a positive route-mass budget. -/
def R324RefinedQuadSignedCompositionBound
    (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 / 4 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        ∀ (hm : 0 < m) (p : R324RefinedScheduleIndex m),
          Nonempty (R324RefinedQuadSignedCompositionData
            ρ ε m α β hm p
              ((m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
                ε⁻¹ ^ (8 : ℕ)))

/-- Paper-scale quadruple-harvest ledger.  This differs intentionally from
`R324RefinedPostCollapseQuadHarvestBound`: its central bracket is at `ε²`,
the scale actually produced by paper Step 4(B). -/
def R324RefinedPostCollapsePaperQuadHarvestBound
    (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 / 4 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        ∀ (hm : 0 < m) (p : R324RefinedScheduleIndex m),
          ‖r324BetaQuadHarvest ρ ε m α β hm
              (momentRefinedContractionFiber m p.1.1 p.2.1)‖ ≤
            (m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
              (ε⁻¹ ^ (8 : ℕ) *
                eighthOrderFrequencyDecay
                  (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖))

/-- The signed composition producer closes the paper-scale quadruple ledger
by the Step 4(B) pigeonhole. -/
theorem R324RefinedQuadSignedCompositionBound.toPaperQuadHarvest
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (h : R324RefinedQuadSignedCompositionBound ρ K) :
    R324RefinedPostCollapsePaperQuadHarvestBound ρ K := by
  intro ε m α β hε hεsmall hlog hm2 hcap hm p
  obtain ⟨d⟩ := h m α β hε hεsmall hlog hm2 hcap hm p
  have hA :
      0 ≤ (m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
        ε⁻¹ ^ (8 : ℕ) := by
    positivity
  simpa only [mul_assoc] using
    d.harvest_le_paperScale hε hεsmall hA

/-- Physical refined-fibre form of the paper-scale bracket. -/
def R324RefinedPostCollapsePaperBracketBound
    (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 / 4 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        ∀ p : R324RefinedScheduleIndex m,
          ‖r324RefinedPhysicalIntegral ρ ε m α β p‖ ≤
            (m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
              (r324EndpointLoss ε α β *
                eighthOrderFrequencyDecay
                  (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖))

/-- Exact external endpoint harvesting turns the paper-scale quadruple
ledger into the corresponding physical refined-fibre ledger. -/
theorem R324RefinedPostCollapsePaperQuadHarvestBound.toPaperBracket
    {ρ : SmoothCutoff} {K : ℝ}
    (h : R324RefinedPostCollapsePaperQuadHarvestBound ρ K) :
    R324RefinedPostCollapsePaperBracketBound ρ K := by
  intro ε m α β hε hεsmall hlog hm2 hcap p
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) hm2
  have hendpoint :
      0 ≤ paperFourthOrderModeDecay α * paperFourthOrderModeDecay β :=
    mul_nonneg (paperFourthOrderModeDecay_nonneg α)
      (paperFourthOrderModeDecay_nonneg β)
  rw [r324RefinedPhysicalIntegral_eq_sum_contractionTerms
    ρ hε hε1 α β p,
    r324Beta_sum_eq_endpointDecays_mul_quadHarvest
      ρ hε hε1 hm α β
        (momentRefinedContractionFiber m p.1.1 p.2.1),
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hendpoint]
  calc
    paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
        ‖r324BetaQuadHarvest ρ ε m α β hm
            (momentRefinedContractionFiber m p.1.1 p.2.1)‖ ≤
      paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
        ((m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
          (ε⁻¹ ^ (8 : ℕ) *
            eighthOrderFrequencyDecay
              (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖))) :=
      mul_le_mul_of_nonneg_left
        (h m α β hε hεsmall hlog hm2 hcap hm p) hendpoint
    _ = (m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
          (r324EndpointLoss ε α β *
            eighthOrderFrequencyDecay
              (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖)) := by
      unfold r324EndpointLoss
      ring

end

end Anderson4D
