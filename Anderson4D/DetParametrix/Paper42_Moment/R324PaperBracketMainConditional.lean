import Anderson4D.DetParametrix.Paper42_Moment.R324PaperMainConditional
import Anderson4D.DetParametrix.Paper42_Moment.R324HdetAssemblyFinal

/-!
# Paper Steps 2--3 plus the post-collapse bracket ledger

This module assembles the deterministic estimate (3.24) from the two
interfaces that respect the order of operations in paper §4.2.  The canonical
route is residual-signature refined:

* `R324PaperRefinedStep23Input` takes the norm only after the complete
  residual-refined fibre has been integrated and carries the paper's
  truncation cap explicitly;
* `R324HdetBracketLedgerBound` takes the norm only after summing the complete
  residual-refined contraction fibre and retains the central frequency
  bracket needed in Step 4.

The `R324PaperStep23Input` form uses positional `intervalConfigs`; the
residual-signature form below avoids that representation.

In particular, this assembly does not use `R324PaperStep4Input`,
`R324HdetCrossIntegralBound`, or `R324LedgerThreeMixedLedger`.  The order-one
decay branch is already unconditional; at orders at least two the bracket
ledger is summed by `r324HdetAssembly_pairingSum_le_of_bracketLedger`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open Filter Set MeasureTheory

/-! ## The residual-signature form of Steps 2--3 -/

/-- **Paper Steps 2--3 at the residual-refined fibre level.**

One cutoff-dependent primitive constant controls every complete refined
fibre at every order in the paper's truncation range.  The modulus in
`MomentRefinedIntegratedReductionOutputAt` is outside the contraction-fibre
sum and all physical integrations.  Thus this interface records the same
post-removal ordering as Step 2(f), without encoding the laminar extraction
schedule as a family of pairwise-disjoint ambient intervals. -/
def R324PaperRefinedStep23Input
    (ρ : SmoothCutoff) (primitiveConstant supportConstant : ℝ) : Prop :=
  ∀ (lam ε : ℝ) (m : ℕ) (α β : Z4),
    0 ≤ lam → 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
      1 ≤ m → m ≤ truncOrder ε →
        MomentRefinedIntegratedReductionOutputAt
          ρ lam ε m α β primitiveConstant supportConstant

/-! ## Fixed-scale deterministic estimate -/

/-- **The fixed-scale deterministic estimate (3.24) from the paper's
Steps 2--3 and the post-collapse bracket ledger.**

The uniform branch is `exists_r324Step23_config_bound`.  The decay branch is
the unconditional order-one routed estimate at `m = 1`, and the summed
bracket ledger at `m >= 2`.  The two estimates are combined only after the
full deterministic pairing sum has been formed. -/
theorem r324PaperBracket_exists_deterministicMoment_bound
    (ρ : SmoothCutoff) {Cred supportConstant : ℝ}
    (hCred : 0 < Cred) (hsupport : 0 < supportConstant)
    (hstep23 : R324PaperStep23Input ρ Cred supportConstant)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧ R324HdetBracketLedgerBound ρ K) :
    ∃ outerC powerC : ℝ, 0 < outerC ∧ 0 < powerC ∧
      ∀ (lam : ℝ), 0 ≤ lam → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β : Z4,
          ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
            deterministicMomentRHS outerC powerC lam ε m α β := by
  obtain ⟨Kb, hKb, hbr⟩ := hbracket
  obtain ⟨outer, C₀, houter, hC₀, huniform⟩ :=
    exists_r324Step23_config_bound ρ hCred hsupport
  obtain ⟨C₁, hC₁, hone⟩ :=
    r324HdetAssembly_exists_countableRoutedOutput_one ρ
  refine ⟨outer + 16 * C₁ + 1,
    max C₀ (max (65536 * Kb) 1),
    by positivity, lt_of_lt_of_le one_pos
      (le_trans (le_max_right _ _) (le_max_right _ _)), ?_⟩
  set O : ℝ := outer + 16 * C₁ + 1 with hOdef
  set P : ℝ := max C₀ (max (65536 * Kb) 1) with hPdef
  have hP1 : C₀ ≤ P := le_max_left _ _
  have hP2 : 65536 * Kb ≤ P :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hPge1 : (1 : ℝ) ≤ P :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  intro lam hlam ε hε hεsmall hlog m hm hmtrunc α β
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hu :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        lamEps lam ε ^ 2 * outer *
          (C₀ * lam) ^ (2 * m - 2) :=
    huniform lam ε m α β hlam hε hε1 hlog hm
      (hstep23 lam ε m α β hlam hε hε1 hlog hm)
  have hAu0 :
      0 ≤ lamEps lam ε ^ 2 * outer *
        (C₀ * lam) ^ (2 * m - 2) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) houter.le)
      (pow_nonneg (mul_nonneg hC₀.le hlam) _)
  have hX :
      (C₀ * lam) ^ (2 * m - 2) ≤
        (P * lam) ^ (2 * m - 2) :=
    pow_le_pow_left₀ (mul_nonneg hC₀.le hlam)
      (mul_le_mul_of_nonneg_right hP1 hlam) _
  rcases eq_or_lt_of_le hm with hm1 | hm2
  · -- At order one the countable routed output is unconditional.
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
              (C₀ * lam) ^ (2 * 1 - 2) +
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
  · -- From order two on, sum the post-collapse bracket ledger.
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
              (C₀ * lam) ^ (2 * m - 2) +
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
              (C₀ * lam) ^ (2 * m - 2) +
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
            (C₀ * lam) ^ (2 * m - 2) +
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

/-! ## Eventually-small-scale hdet and the conditional main theorem -/

/-- The exact deterministic hypothesis of
`mainConditional_of_deterministic_bounds`, obtained without either of the
pre-collapse norm interfaces. -/
theorem r324PaperBracket_hdet
    (ρ : SmoothCutoff) {Cred supportConstant : ℝ}
    (hCred : 0 < Cred) (hsupport : 0 < supportConstant)
    (hstep23 : R324PaperStep23Input ρ Cred supportConstant)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧ R324HdetBracketLedgerBound ρ K) :
    ∃ outerC powerC : ℝ, 0 < outerC ∧ 0 < powerC ∧
      ∀ lam : ℝ, 0 < lam →
        ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
          ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β : Z4,
            ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
              deterministicMomentRHS outerC powerC lam ε m α β := by
  obtain ⟨O, P, hO, hP, hbound⟩ :=
    r324PaperBracket_exists_deterministicMoment_bound
      ρ hCred hsupport hstep23 hbracket
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

/-- **Conditional Theorem 1.1 from the paper's Steps 2--3 and the
post-collapse bracket ledger.**

The counterterm estimate (3.22) is unconditional.  Consequently the only
remaining deterministic premise is the bracket ledger, whose norm is taken
after every interval removal and after the full residual-fibre sum. -/
theorem mainConditional_of_paperStep23_and_bracketLedger
    {M : NoiseModel} {ρ : SmoothCutoff} {Cred supportConstant : ℝ}
    (hCred : 0 < Cred) (hsupport : 0 < supportConstant)
    (hstep23 : R324PaperStep23Input ρ Cred supportConstant)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧ R324HdetBracketLedgerBound ρ K) :
    MainConditional M ρ := by
  obtain ⟨O, P, hO, hP, hdet⟩ :=
    r324PaperBracket_hdet ρ hCred hsupport hstep23 hbracket
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

/-! ## Canonical residual-refined assembly -/

/-- **The fixed-scale deterministic estimate (3.24) from the
residual-refined Steps 2--3 interface and the post-collapse bracket
ledger.**

Unlike the compatibility theorem above, this statement has no positional
configuration input.  The uniform branch is produced directly by
`exists_deterministicMoment_uniform_bound_of_refinedIntegratedReduction`.
-/
theorem r324PaperRefinedBracket_exists_deterministicMoment_bound
    (ρ : SmoothCutoff) {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant)
    (hstep23 : R324PaperRefinedStep23Input
      ρ primitiveConstant supportConstant)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧ R324HdetBracketLedgerBound ρ K) :
    ∃ outerC powerC : ℝ, 0 < outerC ∧ 0 < powerC ∧
      ∀ (lam : ℝ), 0 ≤ lam → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β : Z4,
          ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
            deterministicMomentRHS outerC powerC lam ε m α β := by
  obtain ⟨Kb, hKb, hbr⟩ := hbracket
  obtain ⟨outer, houter, huniform⟩ :=
    exists_deterministicMoment_uniform_bound_of_refinedIntegratedReduction
      hprimitive hsupport
  obtain ⟨C₁, hC₁, hone⟩ :=
    r324HdetAssembly_exists_countableRoutedOutput_one ρ
  refine ⟨outer + 16 * C₁ + 1,
    max (16 * primitiveConstant) (max (65536 * Kb) 1),
    by positivity, lt_of_lt_of_le one_pos
      (le_trans (le_max_right _ _) (le_max_right _ _)), ?_⟩
  set O : ℝ := outer + 16 * C₁ + 1 with hOdef
  set P : ℝ :=
    max (16 * primitiveConstant) (max (65536 * Kb) 1) with hPdef
  have hP1 : 16 * primitiveConstant ≤ P := le_max_left _ _
  have hP2 : 65536 * Kb ≤ P :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hPge1 : (1 : ℝ) ≤ P :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  intro lam hlam ε hε hεsmall hlog m hm hmtrunc α β
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hu :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        lamEps lam ε ^ 2 * outer *
          ((16 * primitiveConstant) * lam) ^ (2 * m - 2) :=
    huniform ρ lam ε m α β hlam hε hε1 hlog hm
      (hstep23 lam ε m α β hlam hε hε1 hlog hm hmtrunc)
  have hAu0 :
      0 ≤ lamEps lam ε ^ 2 * outer *
        ((16 * primitiveConstant) * lam) ^ (2 * m - 2) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) houter.le)
      (pow_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hprimitive.le) hlam) _)
  have hX :
      ((16 * primitiveConstant) * lam) ^ (2 * m - 2) ≤
        (P * lam) ^ (2 * m - 2) :=
    pow_le_pow_left₀
      (mul_nonneg (mul_nonneg (by norm_num) hprimitive.le) hlam)
      (mul_le_mul_of_nonneg_right hP1 hlam) _
  rcases eq_or_lt_of_le hm with hm1 | hm2
  · -- At order one the countable routed output is unconditional.
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
              ((16 * primitiveConstant) * lam) ^ (2 * 1 - 2) +
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
  · -- From order two on, sum the post-collapse bracket ledger.
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
              ((16 * primitiveConstant) * lam) ^ (2 * m - 2) +
            lamEps lam ε ^ 2 * (65536 * Kb) ^ m *
              lam ^ (2 * m - 2)) *
            paperDeterministicMomentDecay ε α β := by
      refine hb.trans ?_
      have hdecay :
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
      refine hdecay.trans ?_
      exact mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hAu0)
        (paperDeterministicMomentDecay_nonneg ε α β)
    have hu' :
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          lamEps lam ε ^ 2 * outer *
              ((16 * primitiveConstant) * lam) ^ (2 * m - 2) +
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
            ((16 * primitiveConstant) * lam) ^ (2 * m - 2) +
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

/-- The exact eventually-small-scale deterministic hypothesis, now from the
residual-refined Steps 2--3 interface rather than positional
configurations. -/
theorem r324PaperRefinedBracket_hdet
    (ρ : SmoothCutoff) {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant)
    (hstep23 : R324PaperRefinedStep23Input
      ρ primitiveConstant supportConstant)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧ R324HdetBracketLedgerBound ρ K) :
    ∃ outerC powerC : ℝ, 0 < outerC ∧ 0 < powerC ∧
      ∀ lam : ℝ, 0 < lam →
        ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
          ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β : Z4,
            ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
              deterministicMomentRHS outerC powerC lam ε m α β := by
  obtain ⟨O, P, hO, hP, hbound⟩ :=
    r324PaperRefinedBracket_exists_deterministicMoment_bound
      ρ hprimitive hsupport hstep23 hbracket
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

/-- **Canonical conditional Theorem 1.1 from the residual-refined
Steps 2--3 output and the post-collapse bracket ledger.**

This theorem has no dependency on `R324PaperStep23Input` or its
`intervalConfigs` encoding. -/
theorem mainConditional_of_paperRefinedStep23_and_bracketLedger
    {M : NoiseModel} {ρ : SmoothCutoff}
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant)
    (hstep23 : R324PaperRefinedStep23Input
      ρ primitiveConstant supportConstant)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧ R324HdetBracketLedgerBound ρ K) :
    MainConditional M ρ := by
  obtain ⟨O, P, hO, hP, hdet⟩ :=
    r324PaperRefinedBracket_hdet
      ρ hprimitive hsupport hstep23 hbracket
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
