import Anderson4D.DetParametrix.Paper42_Moment.R324CappedMixedReduction
import Anderson4D.Parametrix.L2KernelBridge

/-!
# Clause B as a Fourier coefficient of the real flat core

`R324CappedBracketDensityLedger` (clause B of `R324CappedCrossLedgerStrong`)
asks for a bound on

`‖∑_{e ∈ F} deterministicMomentContractionTerm ρ ε m α β e‖`

that is *graded by the external modes* `α, β`.  By
`r324CMFlatDensity_modes_indep` this can never come from a modulus
estimate: the four external characters are unimodular and entity
independent.  This file makes the only possible mechanism explicit.

## The core

Every `deterministicMomentIntegrand` is `charT4 α x * charT4 β y *
charT4 (-α) z * charT4 (-β) w` times a **real** number, and that real
number does not depend on `α, β`.  Summing over the entity set `F`
gives one real function on the physical product space, the *flat core*
`r324CMFlatCore`.  Two exact identities follow:

* `r324CMFlatDensity_eq_abs_core` — the clause-A carrier is `|core|`;
* `r324CM_sum_term_eq_core_fourier` — the clause-B left-hand side is the
  modulus of **one Fourier coefficient of the core**, taken at the
  frozen four-fold external mode `(α, β, -α, -β)`.

So clause A is the `L¹` norm of the core and clause B is the decay of
its external Fourier coefficients: exactly the paper's §4.2 mechanism
((4.16)–(4.20)), where the decay is produced by integrating the
external coordinates `x, y, z, w` against their characters *before*
any norm is taken.

## Removing `ε` from the weight

`r324CMBracketWeight ε α β = ε⁻⁸ ⟨α⟩⁻⁴⟨β⟩⁻⁴⟨ε‖α+β‖⟩⁻⁸` still carries
the endpoint loss `ε⁻⁸`.  For `0 < ε ≤ 1` that loss exactly absorbs the
rescaling of the central bracket, so the `ε`-free weight
`r324BracketPaperWeight α β = ⟨α⟩⁻⁴⟨β⟩⁻⁴⟨‖α+β‖⟩⁻⁸` is *smaller*
(`r324BracketPaperWeight_le_cmBracketWeight`).  Clause B therefore
follows from the sharper `ε`-free ledger `R324BracketPaperLedger`,
which is what the harvest of the four endpoint characters produces.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The `ε`-free bracket weight -/

/-- The `ε`-free paper weight `⟨α⟩⁻⁴ ⟨β⟩⁻⁴ ⟨‖α+β‖⟩⁻⁸`: the two endpoint
fourth-order mode decays produced by the four external Green
integrations, times the central eighth-order bracket at the conserved
mode `α + β`, with **no** `ε` rescaling anywhere. -/
def r324BracketPaperWeight (α β : Z4) : ℝ :=
  paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
    eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖

theorem r324BracketPaperWeight_nonneg (α β : Z4) :
    0 ≤ r324BracketPaperWeight α β :=
  mul_nonneg
    (mul_nonneg (paperFourthOrderModeDecay_nonneg α)
      (paperFourthOrderModeDecay_nonneg β))
    (eighthOrderFrequencyDecay_nonneg _)

/-- **The `ε`-free weight is the smaller one.**  On `0 < ε ≤ 1` the
endpoint loss `ε⁻⁸ ≥ 1` and the central bracket only improves when the
frequency is rescaled by `ε ≤ 1`, so the `ε`-free paper weight is
dominated by `r324CMBracketWeight`.  Consequently a bound against the
`ε`-free weight is *stronger* than clause B. -/
theorem r324BracketPaperWeight_le_cmBracketWeight
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (α β : Z4) :
    r324BracketPaperWeight α β ≤ r324CMBracketWeight ε α β := by
  have hN : (0 : ℝ) ≤ ‖z4EuclideanFrequency (α + β)‖ := norm_nonneg _
  have hscale : ε * ‖z4EuclideanFrequency (α + β)‖ ≤
      ‖z4EuclideanFrequency (α + β)‖ := by
    nlinarith
  have hE :
      eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖ ≤
        eighthOrderFrequencyDecay
          (ε * ‖z4EuclideanFrequency (α + β)‖) :=
    eighthOrderFrequencyDecay_anti (by positivity) hscale
  have hEnn : (0 : ℝ) ≤
      eighthOrderFrequencyDecay
        (ε * ‖z4EuclideanFrequency (α + β)‖) :=
    eighthOrderFrequencyDecay_nonneg _
  have hD : (0 : ℝ) ≤
      paperFourthOrderModeDecay α * paperFourthOrderModeDecay β :=
    mul_nonneg (paperFourthOrderModeDecay_nonneg α)
      (paperFourthOrderModeDecay_nonneg β)
  have hloss : (1 : ℝ) ≤ ε⁻¹ ^ (8 : ℕ) := one_le_pow₀ (by
    rw [le_inv_comm₀ one_pos hε]; simpa using hε1)
  have hstep :
      paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
          eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖ ≤
        paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
          eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖) :=
    mul_le_mul_of_nonneg_left hE hD
  have hfinal :
      paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
            eighthOrderFrequencyDecay
              (ε * ‖z4EuclideanFrequency (α + β)‖) ≤
        ε⁻¹ ^ (8 : ℕ) * paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β *
          eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖) := by
    nlinarith [mul_nonneg hD hEnn]
  calc
    r324BracketPaperWeight α β ≤
        paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
          eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖) := hstep
    _ ≤ r324CMBracketWeight ε α β := hfinal

/-! ## The real flat core -/

/-- **The real flat core.**  The entity-summed deterministic integrand
with the four external characters stripped: a *real* function on the
physical product space, independent of `α` and `β`.  Clause A is its
`L¹` norm; clause B is the decay of its external Fourier
coefficients. -/
def r324CMFlatCore
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (F : Finset (MomentContraction m))
    (p : R324PhysicalPoint m) : ℝ :=
  ∑ e ∈ F,
    (detIntegrand ρ ε m e.1
        (assemble p.1 p.2.1 fun i => p.2.2.2.2 (leftMomentIndex i)) *
      detIntegrand ρ ε m e.2.1
        (assemble p.2.2.1 p.2.2.2.1 fun i =>
          p.2.2.2.2 (rightMomentIndex i)) *
      momentCrossCovarianceProduct ρ ε m e.1 e.2.1 e.2.2 p.2.2.2.2)

/-- The four frozen external characters of (4.18) at the modes
`(α, β, -α, -β)`, as a function on the physical product space. -/
def r324ExternalChar (m : ℕ) (α β : Z4) (p : R324PhysicalPoint m) : ℂ :=
  charT4 α p.1 * charT4 β p.2.1 * charT4 (-α) p.2.2.1 *
    charT4 (-β) p.2.2.2.1

theorem norm_r324ExternalChar
    (m : ℕ) (α β : Z4) (p : R324PhysicalPoint m) :
    ‖r324ExternalChar m α β p‖ = 1 := by
  unfold r324ExternalChar
  rw [norm_mul, norm_mul, norm_mul, norm_charT4, norm_charT4,
    norm_charT4, norm_charT4, mul_one, mul_one, mul_one]

/-- **Character/core factorization of the summed flat integrand.**  The
external characters are entity independent, so they factor out of the
entity sum, leaving the real core. -/
theorem r324CM_sum_flatten_eq_char_mul_core
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (F : Finset (MomentContraction m))
    (p : R324PhysicalPoint m) :
    (∑ e ∈ F,
        r324Flatten
          (deterministicMomentIntegrand ρ ε m α β
            e.1 e.2.1 e.2.2) p) =
      r324ExternalChar m α β p *
        ((r324CMFlatCore ρ ε m F p : ℝ) : ℂ) := by
  unfold r324CMFlatCore r324ExternalChar r324Flatten
    deterministicMomentIntegrand
  push_cast
  rw [Finset.mul_sum]

/-- **Clause A's carrier is the modulus of the core.** -/
theorem r324CMFlatDensity_eq_abs_core
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (F : Finset (MomentContraction m))
    (p : R324PhysicalPoint m) :
    r324CMFlatDensity ρ ε m α β F p =
      |r324CMFlatCore ρ ε m F p| := by
  unfold r324CMFlatDensity
  rw [r324CM_sum_flatten_eq_char_mul_core, norm_mul,
    norm_r324ExternalChar, one_mul, Complex.norm_real,
    Real.norm_eq_abs]

/-- **Clause B's left-hand side is one Fourier coefficient of the
core.**  The four external coordinates are integrated against their
characters *before* any norm is taken; this is the sole source of the
mode grading. -/
theorem r324CM_sum_term_eq_core_fourier
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (α β : Z4) (F : Finset (MomentContraction m)) :
    (∑ e ∈ F, deterministicMomentContractionTerm ρ ε m α β e) =
      ∫ p, r324ExternalChar m α β p *
          ((r324CMFlatCore ρ ε m F p : ℝ) : ℂ)
        ∂(r324PhysicalMeasure m) := by
  rw [r324CM_sum_term_eq_integral ρ hε hε1 α β F]
  exact integral_congr_ae (Filter.Eventually.of_forall fun p =>
    r324CM_sum_flatten_eq_char_mul_core ρ ε m α β F p)

/-! ## The `ε`-free ledger and clause B -/

/-- **The `ε`-free bracket ledger.**  The same shape as clause B but
against the sharper weight `r324BracketPaperWeight`: the two endpoint
fourth-order mode decays and the central eighth-order bracket at the
conserved mode `α + β`, with no `ε⁻⁸` endpoint loss and no `ε`
rescaling of the bracket.  This is what the endpoint harvest of the
four external characters produces. -/
def R324BracketPaperLedger (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        ∀ F : Finset (MomentContraction m),
          ‖∑ e ∈ F,
              deterministicMomentContractionTerm ρ ε m α β e‖ ≤
            K ^ m * |Real.log ε| ^ (m - 1) *
              r324BracketPaperWeight α β

/-- **Clause B from the `ε`-free ledger.** -/
theorem R324CappedBracketDensityLedger_of_paperLedger
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (h : R324BracketPaperLedger ρ K) :
    R324CappedBracketDensityLedger ρ K := by
  intro ε m α β hε hε1 hlog hm2 hcap F
  have hKL : (0 : ℝ) ≤ K ^ m * |Real.log ε| ^ (m - 1) :=
    mul_nonneg (pow_nonneg hK m) (pow_nonneg (abs_nonneg _) _)
  refine (h m α β hε hε1 hlog hm2 hcap F).trans ?_
  exact mul_le_mul_of_nonneg_left
    (r324BracketPaperWeight_le_cmBracketWeight hε hε1 α β) hKL

end

end Anderson4D
