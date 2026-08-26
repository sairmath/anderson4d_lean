import Anderson4D.DetParametrix.Paper42_Moment.R324RoutedEvalLowOrder

/-!
# Unconditional routed outputs from the low-order window ledgers

Composition layer over `R324RoutedEvalLowOrder`:

* both routed window Props are monotone in the window constant, so the
  two order-one ledgers can be served by one constant;
* `exists_r324RoutedWindowLedger_one` — one cutoff-only constant funds
  both routed Props at `m = 1`;
* `exists_countableCentralRoutedMomentReductionOutput_one` — the
  countable central routed output of the proved reduction chain
  holds **unconditionally** at `m = 1`, at the windowed amplitude
  `λ_ε²·(16·C·λ⁰)` times the endpoint loss.

`R324RoutedWindowLedgerAt` states the general-order estimate.  The `α+β ≠ 0`
ledger for `m ≥ 2` and the zero-shift ledger for
`m ≥ 3` are *not* provable by the norm-inside route weights (the free
cross slots of a two-cross contraction pay the full coefficient mass
`ε⁻⁴` instead of one retained Green window `C·L`), so they require the
finer physical evaluation used by the final proof.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- The nonzero-shift routed ledger is monotone in the window
constant. -/
theorem R324RoutedPerTermWindowBound.mono
    {ρ : SmoothCutoff} {lam : ℝ} {m : ℕ} {C C' : ℝ}
    (h0 : 0 ≤ C) (hCC : C ≤ C')
    (h : R324RoutedPerTermWindowBound ρ lam m C) :
    R324RoutedPerTermWindowBound ρ lam m C' := by
  intro hm ε hε hε1 hlog hmtrunc α β hexternal
  refine (h hm ε hε hε1 hlog hmtrunc α β hexternal).trans ?_
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (paperFourthOrderModeDecay_nonneg α))
      (paperFourthOrderModeDecay_nonneg β))
  refine mul_le_mul_of_nonneg_left ?_
    (pow_nonneg (abs_nonneg _) _)
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ h0 hCC m) (by positivity)

/-- The zero-shift routed ledger is monotone in the window constant. -/
theorem R324RoutedZeroShiftWindowBound.mono
    {ρ : SmoothCutoff} {lam : ℝ} {m : ℕ} {C C' : ℝ}
    (h0 : 0 ≤ C) (hCC : C ≤ C')
    (h : R324RoutedZeroShiftWindowBound ρ lam m C) :
    R324RoutedZeroShiftWindowBound ρ lam m C' := by
  intro hm ε hε hε1 hlog hmtrunc α β hshift
  refine (h hm ε hε hε1 hlog hmtrunc α β hshift).trans ?_
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (paperFourthOrderModeDecay_nonneg α))
      (paperFourthOrderModeDecay_nonneg β))
  refine mul_le_mul_of_nonneg_left ?_
    (pow_nonneg (abs_nonneg _) _)
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ h0 hCC m) (by positivity)

/-- **The complete routed window ledger at one order.**  This is the
exact pair of Props consumed by the proved frozen-amplitude routed
reduction; it is fully proved here at `m = 1`, while for `m ≥ 2` the
nonzero-shift half remains the open physical obligation. -/
def R324RoutedWindowLedgerAt
    (ρ : SmoothCutoff) (lam C : ℝ) (m : ℕ) : Prop :=
  R324RoutedPerTermWindowBound ρ lam m C ∧
    R324RoutedZeroShiftWindowBound ρ lam m C

/-- **Both routed window Props hold at order one**, with a single
constant depending only on the cutoff. -/
theorem exists_r324RoutedWindowLedger_one
    (ρ : SmoothCutoff) (lam : ℝ) :
    ∃ C : ℝ, 0 < C ∧ R324RoutedWindowLedgerAt ρ lam C 1 := by
  obtain ⟨C₁, hC₁, hnonzero⟩ :=
    exists_r324RoutedPerTermWindowBound_one ρ lam
  obtain ⟨C₂, hC₂, hzero⟩ :=
    exists_r324RoutedZeroShiftWindowBound_one ρ lam
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_, ?_⟩
  · exact hnonzero.mono hC₁.le (le_max_left _ _)
  · exact hzero.mono hC₂.le (le_max_right _ _)

/-- **The unconditional order-one routed output.**  The countable
central routed moment reduction output holds at `m = 1` at the windowed
amplitude, with a constant depending only on the cutoff. -/
theorem exists_countableCentralRoutedMomentReductionOutput_one
    (ρ : SmoothCutoff) (lam : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        1 ≤ truncOrder ε →
        ∀ α β : Z4,
          CountableCentralRoutedMomentReductionOutput
            ρ lam ε 1 α β
            ((lamEps lam ε ^ 2 *
                (16 * C ^ 1 * lam ^ (2 * 1 - 2))) *
              r324EndpointLoss ε α β) := by
  obtain ⟨C, hC, hnonzero, hzero⟩ :=
    exists_r324RoutedWindowLedger_one ρ lam
  refine ⟨C, hC, ?_⟩
  intro ε hε hε1 hlog hmtrunc α β
  exact
    countableCentralRoutedMomentReductionOutput_of_routedWindow
      one_pos hε hε1 hlog hmtrunc hnonzero hzero α β

/-- **The conditional endgame, restated on the named ledger.**  The
deterministic paper bound needs, beyond the proved uniform-branch
output, exactly one `R324RoutedWindowLedgerAt` instance per order
together with the `ε`-free amplitude comparison; order one of that
ledger is unconditional by `exists_r324RoutedWindowLedger_one`. -/
theorem
    exists_deterministicMoment_paper_bound_of_refinedIntegrated_and_ledger
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε C : ℝ) (m : ℕ) (α β : Z4),
        0 ≤ lam → 0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| → 1 ≤ m → m ≤ truncOrder ε →
        MomentRefinedIntegratedReductionOutputAt
          ρ lam ε m α β primitiveConstant supportConstant →
        R324RoutedWindowLedgerAt ρ lam C m →
        16 * C ^ m * lam ^ (2 * m - 2) ≤
          outerConstant *
            ((16 * primitiveConstant) * lam) ^ (2 * m - 2) →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (16 * primitiveConstant) lam ε m α β := by
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_refinedIntegrated_and_routedWindow
      hprimitive hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε C m α β hlam hε hεsmall hlog hm hmtrunc
    hrefined hledger hclose
  exact
    h ρ lam ε C m α β hlam hε hεsmall hlog hm hmtrunc
      hrefined hledger.1 hledger.2 hclose

end

end Anderson4D
