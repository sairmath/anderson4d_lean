import Anderson4D.DetParametrix.Paper42_Moment.R324HdetAssemblyBracket
import Anderson4D.DetParametrix.Paper42_Moment.R324LedgerThreeClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324SignedPhysicalBudget
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticResidualIteration
import Anderson4D.Main.DeterministicClosure

/-!
# Final hdet assembly: conditional closure of the deterministic moment bound

The analytic residuals are stated as named Props and composed to the exact
`hdet` hypothesis of
`mainConditional_of_deterministic_bounds`, with all constants fixed by
the cutoff before the coupling.

* `R324HdetCrossIntegralBound` — the injectivity-retaining cross-density
  integral hypothesis of the uniform-branch closure
  `exists_momentRefinedIntegratedReductionOutputAt_of_crossIntegral_and_mixed`;
  the bijection sum is retained throughout.
* `R324HdetBracketLedgerBound` — the bracket-retaining variant at the
  same residual-refined fibre level: each fibre term sum pays the
  windowed value `m⁸·K^m·L^{m-1}` times the endpoint loss and one
  central eighth-order bracket at the natural pointwise-harvest scale
  `⟨ε‖freq(α+β)‖⟩⁻⁸` (funded by the half-symbol split
  `r324HdetAssembly_exists_halfSymbol_sq_bracket`, the product bracket
  `r324HdetAssembly_prod_eighthDecay_le` over the momentum-conserving
  keys, and increment telescoping).
* `R324LedgerThreeMixedLedger` — the proved mixed-fibre ledger.

**Routed-branch interfaces.**  At `m = 1` the countable central routed
output is consumed unconditionally through the proved
`countableCentralRoutedMomentReductionOutput_of_routedWindow` chain
(coupling-uniform replay in the kit file).  For `m ≥ 2` the countable
interface `countableCentralRoutedMomentReductionOutput_of_signedCentralDecay`
demands the bracket at a routed-increment scale `⟨‖freq‖/nInc⟩⁻⁸` with
`1 ≤ nInc ≤ truncOrder ε`; on the admissible range `ε ≤ 1/4` one has
`ε ≤ 1/truncOrder ε ≤ 1/nInc`, so every admissible demand is strictly
stronger than the `⟨ε‖freq‖⟩⁻⁸` bracket produced by the pointwise
product harvest — the countable normalization cannot be met from this
Prop.  The `m ≥ 2` branch therefore lands in the paper bracket through
the proved flexible-amplitude combiner
`le_mul_min_of_le_of_le_mul` and the scale comparison
`r324HdetAssembly_endpointLoss_mul_epsScale_le_paper`, parallel to the
proved countable consumer
`deterministicMomentPairingSum_paper_bound_of_uniform_and_countable`
used verbatim at `m = 1`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open Filter Set MeasureTheory
open scoped BigOperators Topology

/-! ## Uniform-branch reduction -/

/-- The complete uniform branch follows from an injectivity-retaining
pure-cross integral bound and the mixed-fibre ledger. -/
theorem exists_momentRefinedIntegratedReductionOutputAt_of_crossIntegral_and_mixed
    (ρ : SmoothCutoff)
    (hcross : ∃ K : ℝ, 0 ≤ K ∧
      ∀ {ε : ℝ} (m : ℕ),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 3 ≤ m →
          ∀ F : Finset (MomentContraction m),
            (∀ e ∈ F, R324LedgerThreeAllCrossEntity e) →
              (∫ p, r324LedgerThreeCrossDensity ρ ε m F p
                  ∂(r324PhysicalMeasure m)) ≤
                K ^ m * |Real.log ε| ^ (m - 1))
    (hmixed : ∃ K : ℝ, 0 ≤ K ∧ R324LedgerThreeMixedLedger ρ K) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (lam : ℝ) {ε : ℝ} (m : ℕ) (α β : Z4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 1 ≤ m →
          MomentRefinedIntegratedReductionOutputAt
            ρ lam ε m α β C₀ 1 := by
  obtain ⟨K, hK, hcrossK⟩ := hcross
  exact
    exists_momentRefinedIntegratedReductionOutputAt_final ρ
      ⟨K, hK,
        r324LedgerThreeCrossLedger_of_integral_bound ρ K hcrossK⟩
      hmixed

/-! ## Analytic hypotheses -/

/-- **Injectivity-retaining cross bound** (uniform branch): verbatim
the `hcross` hypothesis of the proved
`exists_momentRefinedIntegratedReductionOutputAt_of_crossIntegral_and_mixed`:
the phase-free integral of the summed pure-cross density — the
bijection sum, before any permanent enlargement — carries the windowed
value `K^m·L^{m-1}`. -/
def R324HdetCrossIntegralBound
    (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 3 ≤ m →
      ∀ F : Finset (MomentContraction m),
        (∀ e ∈ F, R324LedgerThreeAllCrossEntity e) →
          (∫ p, r324LedgerThreeCrossDensity ρ ε m F p
              ∂(r324PhysicalMeasure m)) ≤
            K ^ m * |Real.log ε| ^ (m - 1)

/-- **Bracket-retaining fibre ledger** (routed branch, `m ≥ 2`): every
residual-refined contraction fibre term sum pays the windowed value
`m⁸·K^m·L^{m-1}`, the endpoint loss `ε⁻⁸⟨α⟩⁻⁴⟨β⟩⁻⁴`, and one central
eighth-order bracket at the natural harvest scale `⟨ε‖freq(α+β)‖⟩⁻⁸`.
The `m⁸` prices the pointwise product bracket over the `2m`
momentum-conserving covariance keys; the `⟨ε‖·‖⟩⁻⁸` normalization is
the one produced by `r324HdetAssembly_prod_eighthDecay_le` applied to
the half-symbol factors, and it dominates the frozen paper bracket by
`r324HdetAssembly_endpointLoss_mul_epsScale_le_paper`. -/
def R324HdetBracketLedgerBound
    (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
      ∀ s ∈ momentContractionSignatures m,
        ∀ r ∈ momentResidualChainSignaturesAt m s,
          ‖momentRefinedDeterministicTermSum ρ ε m α β s r‖ ≤
            (m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
              (r324EndpointLoss ε α β *
                eighthOrderFrequencyDecay
                  (ε * ‖z4EuclideanFrequency (α + β)‖))

/-! ## Summation of the bracket ledger -/

/-- The bracket ledger sums to a pointwise bracket bound on the full
signed pairing sum: signature and residual-schedule counting cost
`4^{2m}` each, the product-bracket price `m⁸` is absorbed as
`m⁸ ≤ 256^m`, and `|λ_ε|^{2m}·L^{m-1}` collapses to
`λ_ε²·λ^{2m-2}` exactly. -/
theorem r324HdetAssembly_pairingSum_le_of_bracketLedger
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (h : R324HdetBracketLedgerBound ρ K)
    (lam : ℝ) {ε : ℝ} {m : ℕ} (α β : Z4)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hlog : 1 ≤ |Real.log ε|)
    (hm2 : 2 ≤ m) (hmtrunc : m ≤ truncOrder ε) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      lamEps lam ε ^ 2 * (65536 * K) ^ m * lam ^ (2 * m - 2) *
        (r324EndpointLoss ε α β *
          eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖)) := by
  have hL0 : (0 : ℝ) < |Real.log ε| :=
    lt_of_lt_of_le one_pos hlog
  set L : ℝ := |Real.log ε| with hLdef
  set D : ℝ :=
    r324EndpointLoss ε α β *
      eighthOrderFrequencyDecay
        (ε * ‖z4EuclideanFrequency (α + β)‖) with hDdef
  have hD0 : 0 ≤ D :=
    mul_nonneg (r324EndpointLoss_nonneg ε α β)
      (eighthOrderFrequencyDecay_nonneg _)
  set B : ℝ := (m : ℝ) ^ 8 * K ^ m * L ^ (m - 1) * D with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (pow_nonneg hK m))
        (pow_nonneg (abs_nonneg _) _)) hD0
  have hper :
      ∀ s ∈ momentContractionSignatures m,
        ‖∑ e ∈ momentContractionFiber m s,
            deterministicMomentContractionTerm ρ ε m α β e‖ ≤
          (4 : ℝ) ^ (2 * m) * B := by
    intro s hs
    rw [← sum_momentRefinedDeterministicTermSum ρ ε m α β s]
    calc
      ‖∑ r ∈ momentResidualChainSignaturesAt m s,
          momentRefinedDeterministicTermSum ρ ε m α β s r‖ ≤
          ∑ r ∈ momentResidualChainSignaturesAt m s,
            ‖momentRefinedDeterministicTermSum ρ ε m α β s r‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _r ∈ momentResidualChainSignaturesAt m s, B :=
        Finset.sum_le_sum fun r hr =>
          h m α β hε hε1 hlog hm2 hmtrunc s hs r hr
      _ = ((momentResidualChainSignaturesAt m s).card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4 : ℝ) ^ (2 * m) * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB0
        exact_mod_cast card_momentResidualChainSignaturesAt_le m s
  have hgrouped :
      groupedDeterministicMomentTermNormSum ρ ε m α β ≤
        (4 : ℝ) ^ (2 * m) * ((4 : ℝ) ^ (2 * m) * B) := by
    unfold groupedDeterministicMomentTermNormSum
    calc
      (∑ s ∈ momentContractionSignatures m,
          ‖∑ e ∈ (Finset.univ :
              Finset (MomentContraction m)) with
            momentContractionSignature e = s,
            deterministicMomentContractionTerm ρ ε m α β e‖) ≤
          ∑ _s ∈ momentContractionSignatures m,
            (4 : ℝ) ^ (2 * m) * B :=
        Finset.sum_le_sum fun s hs => hper s hs
      _ = ((momentContractionSignatures m).card : ℝ) *
            ((4 : ℝ) ^ (2 * m) * B) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4 : ℝ) ^ (2 * m) * ((4 : ℝ) ^ (2 * m) * B) := by
        refine mul_le_mul_of_nonneg_right ?_
          (mul_nonneg (by positivity) hB0)
        exact_mod_cast card_momentContractionSignatures_le m
  have hid :
      |lamEps lam ε| ^ (2 * m) * L ^ (m - 1) =
        lamEps lam ε ^ 2 * lam ^ (2 * m - 2) := by
    rw [abs_lamEps_even_pow m hL0, lamEps_sq hL0, ← hLdef]
    have hLm : L ^ m = L * L ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hlam2 : lam ^ (2 * m) = lam ^ 2 * lam ^ (2 * m - 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hLm, hlam2]
    field_simp
  have hcoeff :
      (4 : ℝ) ^ (2 * m) * (4 : ℝ) ^ (2 * m) *
          ((m : ℝ) ^ 8 * K ^ m) ≤
        (65536 * K) ^ m := by
    have hm8 : (m : ℝ) ^ 8 ≤ (256 : ℝ) ^ m := by
      have h2 : (m : ℝ) ≤ (2 : ℝ) ^ m := by
        exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
      calc
        (m : ℝ) ^ 8 ≤ ((2 : ℝ) ^ m) ^ 8 := by
          have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
          exact pow_le_pow_left₀ hm0 h2 8
        _ = (256 : ℝ) ^ m := by
          rw [← pow_mul, mul_comm m 8, pow_mul]
          norm_num
    calc
      (4 : ℝ) ^ (2 * m) * (4 : ℝ) ^ (2 * m) *
          ((m : ℝ) ^ 8 * K ^ m) ≤
          (4 : ℝ) ^ (2 * m) * (4 : ℝ) ^ (2 * m) *
            ((256 : ℝ) ^ m * K ^ m) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hm8 (pow_nonneg hK m)
      _ = (65536 * K) ^ m := by
        have h4 : (4 : ℝ) ^ (2 * m) = (16 : ℝ) ^ m := by
          rw [pow_mul]
          norm_num
        rw [h4, ← mul_pow, ← mul_pow, ← mul_pow]
        congr 1
        ring
  calc
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        |lamEps lam ε| ^ (2 * m) *
          groupedDeterministicMomentTermNormSum ρ ε m α β :=
      deterministicMomentPairingSum_le_groupedSignatures ρ lam ε m α β
    _ ≤ |lamEps lam ε| ^ (2 * m) *
          ((4 : ℝ) ^ (2 * m) * ((4 : ℝ) ^ (2 * m) * B)) :=
      mul_le_mul_of_nonneg_left hgrouped
        (pow_nonneg (abs_nonneg _) _)
    _ = (4 : ℝ) ^ (2 * m) * (4 : ℝ) ^ (2 * m) *
          ((m : ℝ) ^ 8 * K ^ m) *
          (|lamEps lam ε| ^ (2 * m) * L ^ (m - 1)) * D := by
      rw [hBdef]
      ring
    _ ≤ (65536 * K) ^ m *
          (|lamEps lam ε| ^ (2 * m) * L ^ (m - 1)) * D := by
      refine mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff (by positivity)) hD0
    _ = lamEps lam ε ^ 2 * (65536 * K) ^ m *
          lam ^ (2 * m - 2) * D := by
      rw [hid]
      ring

/-! ## Landing in the frozen deterministic right side -/

/-- Any amplitude dominated by the frozen shape lands the paper `min`
bracket in `deterministicMomentRHS`, through
`paperDeterministicMomentDecay_le` and `min` monotonicity. -/
theorem r324HdetAssembly_rhs_glue
    {value amplitude O P lam ε : ℝ} {m : ℕ} {α β : Z4}
    (h : value ≤
      amplitude * min 1 (paperDeterministicMomentDecay ε α β))
    (hamp : amplitude ≤
      lamEps lam ε ^ 2 * O * (P * lam) ^ (2 * m - 2))
    (hamp0 : 0 ≤ amplitude) :
    value ≤ deterministicMomentRHS O P lam ε m α β := by
  unfold deterministicMomentRHS
  refine h.trans ?_
  have hmin :
      min 1 (paperDeterministicMomentDecay ε α β) ≤
        min 1 (deterministicMomentDecay ε α β) :=
    min_le_min le_rfl (paperDeterministicMomentDecay_le ε α β)
  have hmin0 :
      0 ≤ min 1 (paperDeterministicMomentDecay ε α β) :=
    le_min zero_le_one (paperDeterministicMomentDecay_nonneg ε α β)
  exact mul_le_mul hamp hmin hmin0 (hamp0.trans hamp)

/-- Strong landing lemma which keeps the exact Euclidean Japanese bracket
printed in (3.24), without comparison to a sup-norm decay ledger. -/
theorem r324HdetAssembly_paper_rhs_glue
    {value amplitude O P lam ε : ℝ} {m : ℕ} {α β : Z4}
    (h : value ≤
      amplitude * min 1 (paperDeterministicMomentDecay ε α β))
    (hamp : amplitude ≤
      lamEps lam ε ^ 2 * O * (P * lam) ^ (2 * m - 2))
    (hamp0 : 0 ≤ amplitude) :
    value ≤ paperDeterministicMomentRHS O P lam ε m α β := by
  unfold paperDeterministicMomentRHS
  have hmin0 :
      0 ≤ min 1 (paperDeterministicMomentDecay ε α β) :=
    le_min zero_le_one (paperDeterministicMomentDecay_nonneg ε α β)
  exact h.trans (mul_le_mul hamp le_rfl hmin0 (hamp0.trans hamp))

/-- **The fixed-scale deterministic (3.24) bound from three analytic
hypotheses.**  All constants are chosen by the cutoff before the coupling;
the uniform branch is the injectivity-retaining closure, and the routed
branch is the unconditional countable
output at `m = 1` and the summed bracket ledger at `m ≥ 2`. -/
theorem r324HdetAssembly_exists_deterministicMoment_bound
    (ρ : SmoothCutoff)
    (hcross : ∃ K : ℝ, 0 ≤ K ∧ R324HdetCrossIntegralBound ρ K)
    (hmixed : ∃ K : ℝ, 0 ≤ K ∧ R324LedgerThreeMixedLedger ρ K)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧ R324HdetBracketLedgerBound ρ K) :
    ∃ outerC powerC : ℝ, 0 < outerC ∧ 0 < powerC ∧
      ∀ (lam : ℝ), 0 ≤ lam → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β : Z4,
          ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
            deterministicMomentRHS outerC powerC lam ε m α β := by
  obtain ⟨Kb, hKb, hbr⟩ := hbracket
  obtain ⟨C₀, hC₀, hunif⟩ :=
    exists_momentRefinedIntegratedReductionOutputAt_of_crossIntegral_and_mixed
      ρ hcross hmixed
  obtain ⟨outer, houter, huniform⟩ :=
    exists_deterministicMoment_uniform_bound_of_refinedIntegratedReduction
      hC₀ one_pos
  obtain ⟨C₁, hC₁, hone⟩ :=
    r324HdetAssembly_exists_countableRoutedOutput_one ρ
  refine ⟨outer + 16 * C₁ + 1,
    max (16 * C₀) (max (65536 * Kb) 1),
    by positivity, lt_of_lt_of_le one_pos
      (le_trans (le_max_right _ _) (le_max_right _ _)), ?_⟩
  set O : ℝ := outer + 16 * C₁ + 1 with hOdef
  set P : ℝ := max (16 * C₀) (max (65536 * Kb) 1) with hPdef
  have hP1 : 16 * C₀ ≤ P := le_max_left _ _
  have hP2 : 65536 * Kb ≤ P :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hPge1 : (1 : ℝ) ≤ P :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  intro lam hlam ε hε hεsmall hlog m hm hmtrunc α β
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hu :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        lamEps lam ε ^ 2 * outer *
          ((16 * C₀) * lam) ^ (2 * m - 2) :=
    huniform ρ lam ε m α β hlam hε hε1 hlog hm
      (hunif lam m α β hε hε1 hlog hm)
  have hAu0 :
      0 ≤ lamEps lam ε ^ 2 * outer *
        ((16 * C₀) * lam) ^ (2 * m - 2) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) houter.le)
      (pow_nonneg (mul_nonneg (by positivity) hlam) _)
  have hX :
      ((16 * C₀) * lam) ^ (2 * m - 2) ≤
        (P * lam) ^ (2 * m - 2) :=
    pow_le_pow_left₀ (mul_nonneg (by positivity) hlam)
      (mul_le_mul_of_nonneg_right hP1 hlam) _
  rcases eq_or_lt_of_le hm with hm1 | hm2
  · -- `m = 1`: proved unconditional countable routed output.
    subst hm1
    have hroute :=
      hone lam hε hε1 hlog
        (one_le_truncOrder_of_abs_log hlog) α β
    have hone0 :
        0 ≤ lamEps lam ε ^ 2 *
          (16 * C₁ ^ 1 * lam ^ (2 * 1 - 2)) := by
      have := hC₁.le
      positivity
    have hu' :
        ‖deterministicMomentPairingSum ρ lam ε 1 α β‖ ≤
          lamEps lam ε ^ 2 * outer *
              ((16 * C₀) * lam) ^ (2 * 1 - 2) +
            lamEps lam ε ^ 2 *
              (16 * C₁ ^ 1 * lam ^ (2 * 1 - 2)) :=
      hu.trans (le_add_of_nonneg_right hone0)
    have hcomb :=
      deterministicMomentPairingSum_paper_bound_of_uniform_and_countable
        hε hεsmall hu' hroute
        (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hAu0)
          (r324EndpointLoss_nonneg ε α β))
    refine r324HdetAssembly_rhs_glue hcomb ?_
      (add_nonneg hAu0 hone0)
    have hexp : 2 * 1 - 2 = 0 := by norm_num
    rw [hexp]
    simp only [pow_zero, pow_one, mul_one]
    have hle2 : 0 ≤ lamEps lam ε ^ 2 := sq_nonneg _
    rw [hOdef]
    nlinarith [hC₁.le, houter.le]
  · -- `m ≥ 2`: summed bracket ledger, landed through the
    -- `⟨ε‖·‖⟩⁻⁸ ≤ ⟨ε²‖·‖⟩⁻⁸` scale comparison.
    have hm2' : 2 ≤ m := hm2
    have hb :=
      r324HdetAssembly_pairingSum_le_of_bracketLedger
        hKb hbr lam α β hε hε1 hlog hm2' hmtrunc
    have hamp₂0 :
        0 ≤ lamEps lam ε ^ 2 * (65536 * Kb) ^ m *
          lam ^ (2 * m - 2) :=
      mul_nonneg
        (mul_nonneg (sq_nonneg _)
          (pow_nonneg (by positivity) m))
        (pow_nonneg hlam _)
    have hd :
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          (lamEps lam ε ^ 2 * outer *
              ((16 * C₀) * lam) ^ (2 * m - 2) +
            lamEps lam ε ^ 2 * (65536 * Kb) ^ m *
              lam ^ (2 * m - 2)) *
            paperDeterministicMomentDecay ε α β := by
      refine hb.trans ?_
      have hstep :
          lamEps lam ε ^ 2 * (65536 * Kb) ^ m *
              lam ^ (2 * m - 2) *
            (r324EndpointLoss ε α β *
              eighthOrderFrequencyDecay
                (ε * ‖z4EuclideanFrequency (α + β)‖)) ≤
            lamEps lam ε ^ 2 * (65536 * Kb) ^ m *
              lam ^ (2 * m - 2) *
            paperDeterministicMomentDecay ε α β :=
        mul_le_mul_of_nonneg_left
          (r324HdetAssembly_endpointLoss_mul_epsScale_le_paper
            hε hε1 α β) hamp₂0
      refine hstep.trans ?_
      exact mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hAu0)
        (paperDeterministicMomentDecay_nonneg ε α β)
    have hu' :
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          lamEps lam ε ^ 2 * outer *
              ((16 * C₀) * lam) ^ (2 * m - 2) +
            lamEps lam ε ^ 2 * (65536 * Kb) ^ m *
              lam ^ (2 * m - 2) :=
      hu.trans (le_add_of_nonneg_right hamp₂0)
    have hcomb := le_mul_min_of_le_of_le_mul hu' hd
    refine r324HdetAssembly_rhs_glue hcomb ?_
      (add_nonneg hAu0 hamp₂0)
    have hY :
        (65536 * Kb) ^ m * lam ^ (2 * m - 2) ≤
          (P * lam) ^ (2 * m - 2) := by
      calc
        (65536 * Kb) ^ m * lam ^ (2 * m - 2) ≤
            P ^ m * lam ^ (2 * m - 2) :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) hP2 m)
            (pow_nonneg hlam _)
        _ ≤ P ^ (2 * m - 2) * lam ^ (2 * m - 2) :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ hPge1 (by omega))
            (pow_nonneg hlam _)
        _ = (P * lam) ^ (2 * m - 2) := (mul_pow _ _ _).symm
    have hle2 : 0 ≤ lamEps lam ε ^ 2 := sq_nonneg _
    have hZ0 : 0 ≤ (P * lam) ^ (2 * m - 2) :=
      pow_nonneg (mul_nonneg (by positivity) hlam) _
    calc
      lamEps lam ε ^ 2 * outer *
            ((16 * C₀) * lam) ^ (2 * m - 2) +
          lamEps lam ε ^ 2 * (65536 * Kb) ^ m *
            lam ^ (2 * m - 2) ≤
          lamEps lam ε ^ 2 * outer *
              (P * lam) ^ (2 * m - 2) +
            lamEps lam ε ^ 2 * (P * lam) ^ (2 * m - 2) := by
        refine add_le_add
          (mul_le_mul_of_nonneg_left hX
            (mul_nonneg hle2 houter.le)) ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hY hle2
      _ = lamEps lam ε ^ 2 * (outer + 1) *
            (P * lam) ^ (2 * m - 2) := by
        ring
      _ ≤ lamEps lam ε ^ 2 * O * (P * lam) ^ (2 * m - 2) := by
        refine mul_le_mul_of_nonneg_right ?_ hZ0
        refine mul_le_mul_of_nonneg_left ?_ hle2
        rw [hOdef]
        nlinarith [hC₁.le]

/-! ## The hdet hypothesis and the conditional main theorem -/

/-- **The exact `hdet` hypothesis of
`mainConditional_of_deterministic_bounds`**, delivered from the three
analytic hypotheses.  The constants depend on the cutoff only and are
fixed before the coupling; the scale hypotheses are discharged
eventually along `ε ↓ 0`. -/
theorem r324HdetAssembly_hdet
    (ρ : SmoothCutoff)
    (hcross : ∃ K : ℝ, 0 ≤ K ∧ R324HdetCrossIntegralBound ρ K)
    (hmixed : ∃ K : ℝ, 0 ≤ K ∧ R324LedgerThreeMixedLedger ρ K)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧ R324HdetBracketLedgerBound ρ K) :
    ∃ outerC powerC : ℝ, 0 < outerC ∧ 0 < powerC ∧
      ∀ lam : ℝ, 0 < lam →
        ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
          ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β : Z4,
            ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
              deterministicMomentRHS outerC powerC lam ε m α β := by
  obtain ⟨O, P, hO, hP, hbound⟩ :=
    r324HdetAssembly_exists_deterministicMoment_bound
      ρ hcross hmixed hbracket
  refine ⟨O, P, hO, hP, ?_⟩
  intro lam hlam
  filter_upwards
      [self_mem_nhdsWithin,
        eventually_smallScale_le
          (show (0 : ℝ) < 1 / 4 by norm_num),
        eventually_one_le_abs_log] with
      ε hεmem hεsmall hlog
  intro m hm hmtrunc α β
  exact hbound lam hlam.le hεmem hεsmall hlog m hm hmtrunc α β

/-- **The conditional main theorem from the analytic residuals.**  The
complete `MainConditional M ρ` follows from three analytic hypotheses:

* the injectivity-retaining cross-density integral bound
  (`R324HdetCrossIntegralBound`, uniform branch, `m ≥ 3`);
* the proved mixed-fibre ledger (`R324LedgerThreeMixedLedger`);
* the bracket-retaining fibre ledger
  (`R324HdetBracketLedgerBound`, routed branch, `m ≥ 2`).

The counterterm input is
`R322AnalyticResidualPrefix.exists_r322_renormC2q_bound`; the order-one
routed branch is unconditional. -/
theorem mainConditional_of_analyticResiduals
    {M : NoiseModel} {ρ : SmoothCutoff}
    (hcross : ∃ K : ℝ, 0 ≤ K ∧ R324HdetCrossIntegralBound ρ K)
    (hmixed : ∃ K : ℝ, 0 ≤ K ∧ R324LedgerThreeMixedLedger ρ K)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧ R324HdetBracketLedgerBound ρ K) :
    MainConditional M ρ := by
  obtain ⟨O, P, hO, hP, hdet⟩ :=
    r324HdetAssembly_hdet ρ hcross hmixed hbracket
  obtain ⟨Crenorm, hCrenorm, hren⟩ :=
    R322AnalyticResidualPrefix.exists_r322_renormC2q_bound ρ
  refine
    mainConditional_of_deterministic_bounds
      hO hP hCrenorm hdet ?_
  intro lam hlam
  filter_upwards
      [self_mem_nhdsWithin,
        eventually_smallScale_le zero_lt_one] with
      ε hεmem hεle
  intro q hq
  have hqB := Finset.mem_Icc.mp hq
  exact hren lam ε q hlam hεmem hεle hqB.1 hqB.2

end

end Anderson4D
