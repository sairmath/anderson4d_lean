import Anderson4D.DetParametrix.Paper42_Moment.R324TailEndpointHarvest

/-!
# Closing the tail ledger: what the head harvest leaves

`R324BracketTailLedger` is clause B on the high-frequency region
`r324CMBracketWeight ε α β ≤ 1`.  By
`r324Tail_sum_eq_alphaDecay_mul_headHarvest` its left-hand side is
*exactly*

`⟨α⟩⁻⁴ · ‖r324TailHeadHarvest ρ ε m α β F i₀‖`,

an identity, not an estimate: the two head Green edges `G(x - v_{L,0})`
and `G(z - v_{R,0})` are entity independent, so both external
integrations `∫ e^{iαx} …` and `∫ e^{-iαz} …` are performed with the
entity sum still inside the integrand, and each contributes exactly
`⟨α⟩⁻²` (`norm_translatedGreenMode`).  Because the harvest is an
identity, the remaining decay factors still **multiply** on.

What is left, `r324TailHeadHarvest`, is the integral over the two
innermost variable groups `(w, v)` of

* the two **tail** external characters (`charT4 β y` inside
  `r324TailBetaCoefficient`, `charT4 (-β) w` outside), which must still
  produce `⟨β⟩⁻⁴`, and
* the two **transported head characters** `charT4 α (v_{L,0})`,
  `charT4 (-α) (v_{R,0})`, which is where the mode `α` has been moved:
  it now sits on the internal anchors, against the covariance symbols,
  and that is the only place the central bracket
  `⟨‖α+β‖⟩⁻⁸` can come from (momentum conservation).

That statement is isolated as `R324BracketTailResidual`, and the tail
ledger follows from it (`R324BracketTailLedger_of_residual`).

Unconditionally — with no residual at all — the head harvest already
closes the tail ledger on the sub-region where the `β` endpoint loss is
affordable (`r324Tail_ledger_of_alpha_suffices`).
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The unconditional sub-region -/

/-- If the `β` endpoint decay together with the central bracket is paid
for by the endpoint loss `ε⁻⁸`, the `α` harvest alone already dominates
the bracket weight. -/
theorem paperFourthOrderModeDecay_le_cmBracketWeight
    {ε : ℝ} (α β : Z4)
    (h : 1 ≤ ε⁻¹ ^ (8 : ℕ) * paperFourthOrderModeDecay β *
      eighthOrderFrequencyDecay
        (ε * ‖z4EuclideanFrequency (α + β)‖)) :
    paperFourthOrderModeDecay α ≤ r324CMBracketWeight ε α β := by
  calc
    paperFourthOrderModeDecay α = paperFourthOrderModeDecay α * 1 :=
      (mul_one _).symm
    _ ≤ paperFourthOrderModeDecay α *
        (ε⁻¹ ^ (8 : ℕ) * paperFourthOrderModeDecay β *
          eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖)) :=
      mul_le_mul_of_nonneg_left h (paperFourthOrderModeDecay_nonneg α)
    _ = r324CMBracketWeight ε α β := by
      unfold r324CMBracketWeight r324EndpointLoss
      ring

/-- **The tail ledger, unconditionally, wherever the `α` harvest
suffices.**  No residual and no oscillation beyond the two head
integrations. -/
theorem r324Tail_ledger_of_alpha_suffices
    {ρ : SmoothCutoff} {K : ℝ} (hA : R324CappedDensityLedger ρ K)
    {ε : ℝ} (m : ℕ) (α β : Z4)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hlog : 1 ≤ |Real.log ε|)
    (hm2 : 2 ≤ m) (hcap : m ≤ truncOrder ε)
    (hreg : paperFourthOrderModeDecay α ≤ r324CMBracketWeight ε α β)
    (F : Finset (MomentContraction m)) :
    ‖∑ e ∈ F, deterministicMomentContractionTerm ρ ε m α β e‖ ≤
      K ^ m * |Real.log ε| ^ (m - 1) * r324CMBracketWeight ε α β := by
  have hKL : (0 : ℝ) ≤ K ^ m * |Real.log ε| ^ (m - 1) := by
    refine le_trans ?_ (hA m hε hε1 hlog hm2 hcap F)
    exact integral_nonneg fun p => r324CMFlatDensity_nonneg ρ ε m 0 0 F p
  refine le_trans
    (r324Tail_norm_sum_le_alphaLedger hA m α β hε hε1 hlog hm2 hcap F) ?_
  exact mul_le_mul_of_nonneg_left hreg hKL

/-! ## The residual -/

/-- **The residual of the tail ledger.**  Everything the head harvest
does not do: the two tail endpoint harvests (`⟨β⟩⁻⁴`) and the central
bracket (`⟨‖α+β‖⟩⁻⁸`), stated on the object the head harvest leaves
behind.  Note that this is *not* a bound on a modulus density — the two
transported head characters `charT4 α (v_{L,0})`, `charT4 (-α) (v_{R,0})`
sit inside the integral and carry the mode `α` into the internal
covariance sum, which is exactly what the central bracket needs. -/
def R324BracketTailResidual (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        r324CMBracketWeight ε α β ≤ 1 →
          ∀ (F : Finset (MomentContraction m)) (hm : 0 < m),
            ‖r324TailHeadHarvest ρ ε m α β F ⟨0, hm⟩‖ ≤
              K ^ m * |Real.log ε| ^ (m - 1) *
                (paperFourthOrderModeDecay β *
                  eighthOrderFrequencyDecay
                    ‖z4EuclideanFrequency (α + β)‖)

/-- **The tail ledger from the residual.**  The head harvest is an
identity, so the two decays simply multiply. -/
theorem R324BracketTailLedger_of_residual
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (h : R324BracketTailResidual ρ K) :
    R324BracketTailLedger ρ K := by
  intro ε m α β hε hε1 hlog hm2 hcap hW F
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) hm2
  have hKL : (0 : ℝ) ≤ K ^ m * |Real.log ε| ^ (m - 1) :=
    mul_nonneg (pow_nonneg hK m) (pow_nonneg (abs_nonneg _) _)
  rw [r324Tail_sum_eq_alphaDecay_mul_headHarvest ρ hε hε1 hm α β F,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperFourthOrderModeDecay_nonneg α)]
  calc
    paperFourthOrderModeDecay α *
        ‖r324TailHeadHarvest ρ ε m α β F ⟨0, hm⟩‖ ≤
        paperFourthOrderModeDecay α *
          (K ^ m * |Real.log ε| ^ (m - 1) *
            (paperFourthOrderModeDecay β *
              eighthOrderFrequencyDecay
                ‖z4EuclideanFrequency (α + β)‖)) :=
      mul_le_mul_of_nonneg_left
        (h m α β hε hε1 hlog hm2 hcap hW F hm)
        (paperFourthOrderModeDecay_nonneg α)
    _ = K ^ m * |Real.log ε| ^ (m - 1) *
          r324BracketPaperWeight α β := by
      unfold r324BracketPaperWeight
      ring
    _ ≤ K ^ m * |Real.log ε| ^ (m - 1) * r324CMBracketWeight ε α β :=
      mul_le_mul_of_nonneg_left
        (r324BracketPaperWeight_le_cmBracketWeight hε hε1 α β) hKL

theorem paperFourthOrderModeDecay_pos (k : Z4) :
    0 < paperFourthOrderModeDecay k := by
  unfold paperFourthOrderModeDecay paperModeNormSq
  positivity

/-- **The residual is not an over-assumption.**  It is *equivalent* to
the `ε`-free tail ledger it is used to prove: the head harvest divides
out exactly.  So `R324BracketTailResidual` measures precisely the work
the head harvest leaves — the two tail endpoint harvests and the
central bracket — and nothing more. -/
theorem R324BracketTailResidual_of_tailPaperLedger
    {ρ : SmoothCutoff} {K : ℝ}
    (h : ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
      0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m → m ≤ truncOrder ε →
        r324CMBracketWeight ε α β ≤ 1 →
          ∀ F : Finset (MomentContraction m),
            ‖∑ e ∈ F, deterministicMomentContractionTerm ρ ε m α β e‖ ≤
              K ^ m * |Real.log ε| ^ (m - 1) *
                r324BracketPaperWeight α β) :
    R324BracketTailResidual ρ K := by
  intro ε m α β hε hε1 hlog hm2 hcap hW F hm
  have key := h m α β hε hε1 hlog hm2 hcap hW F
  rw [r324Tail_sum_eq_alphaDecay_mul_headHarvest ρ hε hε1 hm α β F,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperFourthOrderModeDecay_nonneg α)] at key
  refine le_of_mul_le_mul_left ?_ (paperFourthOrderModeDecay_pos α)
  refine le_trans key (le_of_eq ?_)
  unfold r324BracketPaperWeight
  ring

/-- **Clause B from clause A and the residual.** -/
theorem R324CappedBracketDensityLedger_of_residual
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (hA : R324CappedDensityLedger ρ K)
    (h : R324BracketTailResidual ρ K) :
    R324CappedBracketDensityLedger ρ K :=
  R324CappedBracketDensityLedger_of_tail hA
    (R324BracketTailLedger_of_residual hK h)

/-- **The strong capped ledger from clause A and the residual.** -/
theorem R324CappedCrossLedgerStrong_of_residual
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (hA : R324CappedDensityLedger ρ K)
    (h : R324BracketTailResidual ρ K) :
    R324CappedCrossLedgerStrong ρ K :=
  R324CappedCrossLedgerStrong_of_tail hA
    (R324BracketTailLedger_of_residual hK h)

end

end Anderson4D
