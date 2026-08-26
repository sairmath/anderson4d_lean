import Anderson4D.DetParametrix.Paper42_Moment.R324ScaledCentralBudget

/-!
# Clause B at the correct scaling

`R324BetaQuadBracketLedger` (and with it `R324CentralAnchorLedger`,
`R324AnchorCentralBudget`) demands the **`ε`-free** bracket
`⟨‖α+β‖⟩⁻⁸`.  Clause B itself — `R324CappedBracketDensityLedger` — asks
only for

`r324CMBracketWeight ε α β = ε⁻⁸⟨α⟩⁻⁴⟨β⟩⁻⁴ · ⟨ε‖freq(α+β)‖⟩⁻⁸`.

Since `∑_{e∈F} term = ⟨α⟩⁻⁴⟨β⟩⁻⁴ · r324BetaQuadHarvest` *identically*
(`r324Beta_sum_eq_endpointDecays_mul_quadHarvest`), clause B is
**equivalent** to

`‖r324BetaQuadHarvest‖ ≤ Kᵐ|log ε|^{m-1} · ε⁻⁸⟨ε‖freq(α+β)‖⟩⁻⁸`,

which is `R324ScaledQuadBracketLedger` below.  The `ε`-free Prop is
stronger by at least the factor `ε⁻⁸`; that over-strengthening is what
made the half-symbol route look six orders short.

The chain assembled here is

`R324ScaledHalfWindowBudget` (window budget)
  → `R324ScaledAnchorCentralBudget`   (`R324ScaledCentralBudget`)
  → `R324ScaledCentralAnchorLedger`   (+ `R324AnchorCollapseAt`)
  → `R324ScaledQuadBracketLedger`     (four anchor harvests)
  → `R324CappedBracketDensityLedger`  (clause B) — **with no appeal to
    clause A and no region hypothesis `r324CMBracketWeight ≤ 1`**.

Nothing is lost: the `ε`-free ledger implies the scaled one
(`R324ScaledQuadBracketLedger_of_epsFreeQuad`,
`r324Scaled_epsFree_bracket_le`).
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The scaled bracket dominates the `ε`-free one -/

/-- **The over-strengthening, measured.**  For `0 < ε ≤ 1` the `ε`-free
bracket is below the scaled bracket with its `ε⁻⁸` slack, so every
`ε`-free statement implies its scaled companion — and, by
`r324Central_epsScale_gap`, the converse fails by up to `ε⁻¹⁶`. -/
theorem r324Scaled_epsFree_bracket_le
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {x : ℝ} (hx : 0 ≤ x) :
    eighthOrderFrequencyDecay x ≤
      ε⁻¹ ^ (8 : ℕ) * eighthOrderFrequencyDecay (ε * x) := by
  have hanti : eighthOrderFrequencyDecay x ≤
      eighthOrderFrequencyDecay (ε * x) :=
    eighthOrderFrequencyDecay_anti (by positivity)
      (by nlinarith)
  have hone : (1 : ℝ) ≤ ε⁻¹ ^ (8 : ℕ) := by
    have h1 : (1 : ℝ) ≤ ε⁻¹ := one_le_inv_iff₀.mpr ⟨hε, hε1⟩
    exact one_le_pow₀ h1
  calc
    eighthOrderFrequencyDecay x ≤ eighthOrderFrequencyDecay (ε * x) := hanti
    _ = 1 * eighthOrderFrequencyDecay (ε * x) := by ring
    _ ≤ ε⁻¹ ^ (8 : ℕ) * eighthOrderFrequencyDecay (ε * x) :=
      mul_le_mul_of_nonneg_right hone (eighthOrderFrequencyDecay_nonneg _)

/-! ## The scaled central-anchor ledger -/

/-- **`R324CentralAnchorLedger` at the correct scaling.**  Same object,
same estimate, but the bracket is the `ε`-scaled one that the covariance
symbols actually produce.  The region hypothesis
`r324CMBracketWeight ε α β ≤ 1` of the proved Prop is *not* needed:
the scaled bound holds on the whole capped range. -/
def R324ScaledCentralAnchorLedger (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        ∀ (F : Finset (MomentContraction m)) (hm : 0 < m)
          (aL aR : MomentContraction m → Option (Fin m)),
          Integrable (r324CentralAnchorIntegrand ρ ε m α β hm F aL aR)
              (Measure.pi fun _ : Fin (2 * m) => paperMeasure) ∧
            ‖r324CentralAnchorHarvest ρ ε m α β hm F aL aR‖ ≤
              K ^ m * |Real.log ε| ^ (m - 1) *
                eighthOrderFrequencyDecay
                  (ε * ‖z4EuclideanFrequency (α + β)‖)

/-- **The scaled central-anchor ledger from the proved collapse and
the scaled budget.**  Exactly `R324CentralAnchorLedger_of_collapse_and_budget`
with the correctly scaled bracket; the collapse input
`R324AnchorCollapseAt` is the proved one, unchanged. -/
theorem R324ScaledCentralAnchorLedger_of_collapse_and_budget
    {ρ : SmoothCutoff} {C D : ℝ} (hC : 0 ≤ C)
    (hcol : ∀ m : ℕ, R324AnchorCollapseAt ρ C m)
    (hbud : R324ScaledAnchorCentralBudget ρ D) :
    R324ScaledCentralAnchorLedger ρ (C * D) := by
  intro ε m α β hε hε1 hlog hm2 hcap F hm aL aR
  obtain ⟨hint, τ, bL, bR, hle⟩ := hcol m hε hε1 α β hm F aL aR
  refine ⟨hint, ?_⟩
  obtain ⟨_hsum, hbound⟩ := hbud m α β hε hε1 hlog hm2 hcap τ bL bR
  have hCm : (0 : ℝ) ≤ C ^ m := pow_nonneg hC m
  calc
    ‖r324CentralAnchorHarvest ρ ε m α β hm F aL aR‖ ≤
        C ^ m * ∑' q : R324AnchorSector m (-(α + β)),
          r324AnchorLatWeight ρ ε α β bL bR τ (q : Fin m → Z4) := hle
    _ ≤ C ^ m * (D ^ m * |Real.log ε| ^ (m - 1) *
          eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖)) :=
      mul_le_mul_of_nonneg_left hbound hCm
    _ = (C * D) ^ m * |Real.log ε| ^ (m - 1) *
          eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖) := by
      rw [mul_pow]; ring

/-! ## The scaled quadruple-harvest ledger -/

/-- **Clause B's exact residue.**  `R324BetaQuadBracketLedger` with the
bracket clause B really asks for: the `ε`-scaled bracket together with
the `ε⁻⁸` endpoint slack.  By
`r324Beta_sum_eq_endpointDecays_mul_quadHarvest` this is *equivalent* to
clause B on every entity set (the two endpoint decays divide out
exactly). -/
def R324ScaledQuadBracketLedger (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        ∀ (F : Finset (MomentContraction m)) (hm : 0 < m),
          ‖r324BetaQuadHarvest ρ ε m α β hm F‖ ≤
            K ^ m * |Real.log ε| ^ (m - 1) *
              (ε⁻¹ ^ (8 : ℕ) *
                eighthOrderFrequencyDecay
                  (ε * ‖z4EuclideanFrequency (α + β)‖))

/-- **Anchor resolution, at the correct scaling.**  The proved
four-term decomposition `r324BetaQuadHarvest_eq_anchorCombination` is
bracket-agnostic, so the argument of
`R324BetaQuadBracketLedger_of_centralAnchor` transfers verbatim; the
`ε⁻⁸` slack is picked up at the last step and never used. -/
theorem R324ScaledQuadBracketLedger_of_scaledCentralAnchor
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (h : R324ScaledCentralAnchorLedger ρ K) :
    R324ScaledQuadBracketLedger ρ (4 * K) := by
  intro ε m α β hε hε1 hlog hm2 hcap F hm
  obtain ⟨h₁i, h₁b⟩ := h m α β hε hε1 hlog hm2 hcap F hm
    (r324CentralLastAnchor hm) (r324CentralLastAnchor hm)
  obtain ⟨h₂i, h₂b⟩ := h m α β hε hε1 hlog hm2 hcap F hm
    (r324CentralLastAnchor hm) r324CentralRightAnchor
  obtain ⟨h₃i, h₃b⟩ := h m α β hε hε1 hlog hm2 hcap F hm
    r324CentralLeftAnchor (r324CentralLastAnchor hm)
  obtain ⟨h₄i, h₄b⟩ := h m α β hε hε1 hlog hm2 hcap F hm
    r324CentralLeftAnchor r324CentralRightAnchor
  set B : ℝ := K ^ m * |Real.log ε| ^ (m - 1) *
    eighthOrderFrequencyDecay (ε * ‖z4EuclideanFrequency (α + β)‖)
    with hB
  have hsplit : ‖r324BetaQuadHarvest ρ ε m α β hm F‖ ≤ 4 * B := by
    rw [r324BetaQuadHarvest_eq_anchorCombination ρ ε α β hm F h₁i h₂i h₃i h₄i]
    calc
      ‖_ - _ - _ + _‖ ≤ ‖_ - _ - _‖ + ‖_‖ := norm_add_le _ _
      _ ≤ (‖_ - _‖ + ‖_‖) + ‖_‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ((‖_‖ + ‖_‖) + ‖_‖) + ‖_‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ((B + B) + B) + B := by gcongr
      _ = 4 * B := by ring
  refine hsplit.trans ?_
  have hdecay : (0 : ℝ) ≤
      eighthOrderFrequencyDecay (ε * ‖z4EuclideanFrequency (α + β)‖) :=
    eighthOrderFrequencyDecay_nonneg _
  have hone : (1 : ℝ) ≤ ε⁻¹ ^ (8 : ℕ) := by
    have h1 : (1 : ℝ) ≤ ε⁻¹ := one_le_inv_iff₀.mpr ⟨hε, hε1⟩
    exact one_le_pow₀ h1
  have hfour : (4 : ℝ) ≤ 4 ^ m := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ m := by
          apply pow_le_pow_right₀ (by norm_num); omega
  have hstep : 4 * K ^ m ≤ (4 * K) ^ m := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hfour (pow_nonneg hK m)
  have hLnn : (0 : ℝ) ≤ |Real.log ε| ^ (m - 1) := by positivity
  calc
    4 * B = 4 * K ^ m *
        (|Real.log ε| ^ (m - 1) *
          eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖)) := by rw [hB]; ring
    _ ≤ (4 * K) ^ m *
        (|Real.log ε| ^ (m - 1) *
          eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖)) :=
      mul_le_mul_of_nonneg_right hstep (mul_nonneg hLnn hdecay)
    _ ≤ (4 * K) ^ m *
        (|Real.log ε| ^ (m - 1) *
          (ε⁻¹ ^ (8 : ℕ) *
            eighthOrderFrequencyDecay
              (ε * ‖z4EuclideanFrequency (α + β)‖))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul_of_nonneg_left ?_ hLnn
      calc
        eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖) =
            1 * eighthOrderFrequencyDecay
              (ε * ‖z4EuclideanFrequency (α + β)‖) := by ring
        _ ≤ ε⁻¹ ^ (8 : ℕ) *
              eighthOrderFrequencyDecay
                (ε * ‖z4EuclideanFrequency (α + β)‖) :=
          mul_le_mul_of_nonneg_right hone hdecay
    _ = (4 * K) ^ m * |Real.log ε| ^ (m - 1) *
        (ε⁻¹ ^ (8 : ℕ) *
          eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖)) := by ring

/-! ## Clause B -/

/-- **Clause B from the scaled ledger — the whole point.**  The endpoint
identity `r324Beta_sum_eq_endpointDecays_mul_quadHarvest` turns the
scaled quadruple-harvest bound into
`r324CMBracketWeight` *exactly*: the two endpoint decays multiply back
on and the `ε⁻⁸` slack is precisely the endpoint loss.  No clause A, no
region split, no `r324CMBracketWeight ≤ 1` hypothesis. -/
theorem R324CappedBracketDensityLedger_of_scaledQuad
    {ρ : SmoothCutoff} {K : ℝ} (h : R324ScaledQuadBracketLedger ρ K) :
    R324CappedBracketDensityLedger ρ K := by
  intro ε m α β hε hε1 hlog hm2 hcap F
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) hm2
  have hpos : (0 : ℝ) ≤
      paperFourthOrderModeDecay α * paperFourthOrderModeDecay β :=
    mul_nonneg (paperFourthOrderModeDecay_nonneg α)
      (paperFourthOrderModeDecay_nonneg β)
  rw [r324Beta_sum_eq_endpointDecays_mul_quadHarvest ρ hε hε1 hm α β F,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
  calc
    paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
        ‖r324BetaQuadHarvest ρ ε m α β hm F‖ ≤
        paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
          (K ^ m * |Real.log ε| ^ (m - 1) *
            (ε⁻¹ ^ (8 : ℕ) *
              eighthOrderFrequencyDecay
                (ε * ‖z4EuclideanFrequency (α + β)‖))) :=
      mul_le_mul_of_nonneg_left (h m α β hε hε1 hlog hm2 hcap F hm) hpos
    _ = K ^ m * |Real.log ε| ^ (m - 1) * r324CMBracketWeight ε α β := by
      unfold r324CMBracketWeight r324EndpointLoss
      ring

/-- **The strong capped ledger**: clause A (taken as a hypothesis) plus
the scaled ledger. -/
theorem R324CappedCrossLedgerStrong_of_scaledQuad
    {ρ : SmoothCutoff} {K : ℝ}
    (hA : R324CappedDensityLedger ρ K)
    (h : R324ScaledQuadBracketLedger ρ K) :
    R324CappedCrossLedgerStrong ρ K :=
  ⟨hA, R324CappedBracketDensityLedger_of_scaledQuad h⟩

/-- **Nothing is lost.**  The `ε`-free quadruple-harvest ledger — the
content of the proved `R324BetaQuadBracketLedger`, stated without its
region hypothesis — implies the scaled one. -/
theorem R324ScaledQuadBracketLedger_of_epsFreeQuad
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
      0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m → m ≤ truncOrder ε →
        ∀ (F : Finset (MomentContraction m)) (hm : 0 < m),
          ‖r324BetaQuadHarvest ρ ε m α β hm F‖ ≤
            K ^ m * |Real.log ε| ^ (m - 1) *
              eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖) :
    R324ScaledQuadBracketLedger ρ K := by
  intro ε m α β hε hε1 hlog hm2 hcap F hm
  refine (h m α β hε hε1 hlog hm2 hcap F hm).trans ?_
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (pow_nonneg hK m) (pow_nonneg (abs_nonneg _) _))
  exact r324Scaled_epsFree_bracket_le hε hε1 (norm_nonneg _)

/-- **The proved `ε`-free ledger implies the scaled bound** on its own
region of validity. -/
theorem r324Scaled_quad_of_quadBracket
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (h : R324BetaQuadBracketLedger ρ K)
    {ε : ℝ} (m : ℕ) (α β : Z4)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hlog : 1 ≤ |Real.log ε|) (hm2 : 2 ≤ m)
    (hcap : m ≤ truncOrder ε) (hW : r324CMBracketWeight ε α β ≤ 1)
    (F : Finset (MomentContraction m)) (hm : 0 < m) :
    ‖r324BetaQuadHarvest ρ ε m α β hm F‖ ≤
      K ^ m * |Real.log ε| ^ (m - 1) *
        (ε⁻¹ ^ (8 : ℕ) *
          eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖)) := by
  refine (h m α β hε hε1 hlog hm2 hcap hW F hm).trans ?_
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (pow_nonneg hK m) (pow_nonneg (abs_nonneg _) _))
  exact r324Scaled_epsFree_bracket_le hε hε1 (norm_nonneg _)

/-! ## The theorem, with the anchor bracket Props eliminated -/

/-- **Clause B, closed, modulo the window budget and the proved
collapse.**  Chaining
`r324Scaled_anchorCentralBudget_of_halfWindow`,
`R324ScaledCentralAnchorLedger_of_collapse_and_budget`,
`R324ScaledQuadBracketLedger_of_scaledCentralAnchor` and
`R324CappedBracketDensityLedger_of_scaledQuad`. -/
theorem R324CappedBracketDensityLedger_of_halfWindow
    {ρ : SmoothCutoff} {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcol : ∀ m : ℕ, R324AnchorCollapseAt ρ C m)
    (hwin : R324ScaledHalfWindowBudget ρ D) :
    ∃ K : ℝ, 0 ≤ K ∧ R324CappedBracketDensityLedger ρ K := by
  obtain ⟨E, hE, hbud⟩ := r324Scaled_anchorCentralBudget_of_halfWindow hD hwin
  refine ⟨4 * (C * E), by positivity, ?_⟩
  refine R324CappedBracketDensityLedger_of_scaledQuad ?_
  exact R324ScaledQuadBracketLedger_of_scaledCentralAnchor
    (mul_nonneg hC hE)
    (R324ScaledCentralAnchorLedger_of_collapse_and_budget hC hcol hbud)

/-- **`MainConditional`, resting on clause A, the proved anchor
collapse, and the window budget alone.**  `R324AnchorCentralBudget` —
the `ε`-free central bracket that `R324AnchorSuffixCount` showed cannot
be read off the Green brackets, and that
`r324Central_epsScale_gap` showed the symbols miss by `ε⁻¹⁶` — has been
*eliminated*: at the scaling clause B actually needs, the bracket is
produced unconditionally by the covariance symbols themselves. -/
theorem mainConditional_of_scaledWindowBudget
    {M : NoiseModel} {ρ : SmoothCutoff} {C D K : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : R324CappedDensityLedger ρ K)
    (hcol : ∀ m : ℕ, R324AnchorCollapseAt ρ C m)
    (hwin : R324ScaledHalfWindowBudget ρ D) :
    MainConditional M ρ := by
  obtain ⟨K', hK', hB⟩ :=
    R324CappedBracketDensityLedger_of_halfWindow hC hD hcol hwin
  have hmax : (0 : ℝ) ≤ max K K' := le_trans hK (le_max_left _ _)
  refine mainConditional_of_cappedCrossLedgerStrong ⟨max K K', hmax, ?_, ?_⟩
  · exact R324CappedDensityLedger_mono hK (le_max_left _ _) hA
  · intro ε m α β hε hε1 hlog hm2 hcap F
    refine (hB m α β hε hε1 hlog hm2 hcap F).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (r324CMBracketWeight_nonneg ε α β)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hK' (le_max_right _ _) m)
      (pow_nonneg (abs_nonneg _) _)

/-- **Conditional assembly from the graded lattice budget, anchor collapse,
and half-symbol window budget.**  This restates
of `mainConditional_of_gradedBudget` with the anchor *bracket* Prop
`R324AnchorCentralBudget` removed: what is left on the clause-B side is
a pure window budget with no frequency bracket in it. -/
theorem mainConditional_of_gradedBudget_scaled
    {M : NoiseModel} {ρ : SmoothCutoff} {C D E K : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hgrade : ∀ m : ℕ, R324ColGradedBudgetAt ρ E m r324LayerSplitGrade)
    (hbridge : (∀ m : ℕ, R324ColGradedBudgetAt ρ E m r324LayerSplitGrade) →
      R324CappedDensityLedger ρ K)
    (hcol : ∀ m : ℕ, R324AnchorCollapseAt ρ C m)
    (hwin : R324ScaledHalfWindowBudget ρ D) :
    MainConditional M ρ :=
  mainConditional_of_scaledWindowBudget hK hC hD (hbridge hgrade) hcol hwin

end

end Anderson4D
