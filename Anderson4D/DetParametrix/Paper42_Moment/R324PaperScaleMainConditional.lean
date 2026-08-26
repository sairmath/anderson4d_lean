import Anderson4D.DetParametrix.Paper42_Moment.R324PaperBracketMainConditional
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperScaleAssembly

/-!
# Conditional main theorem at the exact paper scale

Paper: R-324 — §4.2, (3.24) and conditional Theorem 1.1

This is the final assembly for the residual-refined route.  Its routed
input is `R324RefinedPostCollapsePaperBracketBound`, with the exact
`⟨ε²(α+β)⟩⁻⁸` decay proved in Step 4(B).  No stronger intermediate
central-frequency estimate is assumed.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open Filter Set MeasureTheory

/-- The fixed-scale deterministic estimate (3.24) from the paper's
post-removal uniform bound and its exact `ε²` routed bound. -/
theorem r324PaperScale_exists_deterministicMoment_paper_bound
    (ρ : SmoothCutoff) {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant)
    (hstep23 : R324PaperRefinedStep23Input
      ρ primitiveConstant supportConstant)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧
      R324RefinedPostCollapsePaperBracketBound ρ K) :
    ∃ outerC powerC : ℝ, 0 < outerC ∧ 0 < powerC ∧
      ∀ (lam : ℝ), 0 ≤ lam → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β : Z4,
          ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
            paperDeterministicMomentRHS outerC powerC lam ε m α β := by
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
  · subst hm1
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
    refine r324HdetAssembly_paper_rhs_glue hcomb ?_
      (add_nonneg hAu0 hone0)
    have hexp : 2 * 1 - 2 = 0 := by norm_num
    rw [hexp]
    simp only [pow_zero, pow_one, mul_one]
    have hle2 : 0 ≤ lamEps lam ε ^ 2 := sq_nonneg _
    rw [hOdef]
    nlinarith [hC₁.le, houter.le]
  · have hm2' : 2 ≤ m := hm2
    have hb :=
      r324PaperScale_pairingSum_le_of_postCollapseBracket
        hKb hbr lam α β hε hεsmall hlog hm2' hmtrunc
    have hamp₂0 :
        0 ≤ lamEps lam ε ^ 2 * (65536 * Kb) ^ m *
          lam ^ (2 * m - 2) :=
      mul_nonneg
        (mul_nonneg (sq_nonneg _)
          (pow_nonneg (by positivity) m))
        (pow_nonneg hlam _)
    have hbPaper :
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          lamEps lam ε ^ 2 * (65536 * Kb) ^ m *
            lam ^ (2 * m - 2) *
              paperDeterministicMomentDecay ε α β := by
      simpa only [paperDeterministicMomentDecay_eq_endpoint_mul_central]
        using hb
    have hd :
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          (lamEps lam ε ^ 2 * outer *
              ((16 * primitiveConstant) * lam) ^ (2 * m - 2) +
            lamEps lam ε ^ 2 * (65536 * Kb) ^ m *
              lam ^ (2 * m - 2)) *
            paperDeterministicMomentDecay ε α β :=
      hbPaper.trans
        (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hAu0)
          (paperDeterministicMomentDecay_nonneg ε α β))
    have hu' :
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          lamEps lam ε ^ 2 * outer *
              ((16 * primitiveConstant) * lam) ^ (2 * m - 2) +
            lamEps lam ε ^ 2 * (65536 * Kb) ^ m *
              lam ^ (2 * m - 2) :=
      hu.trans (le_add_of_nonneg_right hamp₂0)
    have hcomb := le_mul_min_of_le_of_le_mul hu' hd
    refine r324HdetAssembly_paper_rhs_glue hcomb ?_
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

/-- The exact paper RHS is stronger than the sup-norm RHS whenever
the named constants and coupling are nonnegative. -/
theorem paperDeterministicMomentRHS_le_deterministicMomentRHS
    {outerC powerC lam ε : Real} {m : Nat} {alpha beta : Z4}
    (houter : 0 <= outerC) (hpower : 0 <= powerC) (hlam : 0 <= lam) :
    paperDeterministicMomentRHS outerC powerC lam ε m alpha beta <=
      deterministicMomentRHS outerC powerC lam ε m alpha beta := by
  unfold paperDeterministicMomentRHS deterministicMomentRHS
  have hmin :
      min 1 (paperDeterministicMomentDecay ε alpha beta) <=
        min 1 (deterministicMomentDecay ε alpha beta) :=
    min_le_min le_rfl (paperDeterministicMomentDecay_le ε alpha beta)
  exact mul_le_mul_of_nonneg_left hmin
    (mul_nonneg
      (mul_nonneg (sq_nonneg _) houter)
      (pow_nonneg (mul_nonneg hpower hlam) _))

/-- Compatibility form of the fixed-scale estimate for the downstream
probability layer, obtained by forgetting only the stronger Euclidean
Japanese bracket in the paper RHS. -/
theorem r324PaperScale_exists_deterministicMoment_bound
    (ρ : SmoothCutoff) {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant)
    (hstep23 : R324PaperRefinedStep23Input
      ρ primitiveConstant supportConstant)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧
      R324RefinedPostCollapsePaperBracketBound ρ K) :
    ∃ outerC powerC : ℝ, 0 < outerC ∧ 0 < powerC ∧
      ∀ (lam : ℝ), 0 ≤ lam → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ alpha beta : Z4,
          ‖deterministicMomentPairingSum ρ lam ε m alpha beta‖ ≤
            deterministicMomentRHS outerC powerC lam ε m alpha beta := by
  obtain ⟨O, P, hO, hP, hbound⟩ :=
    r324PaperScale_exists_deterministicMoment_paper_bound
      ρ hprimitive hsupport hstep23 hbracket
  refine ⟨O, P, hO, hP, ?_⟩
  intro lam hlam ε hε hεsmall hlog m hm hmtrunc alpha beta
  exact (hbound lam hlam hε hεsmall hlog m hm hmtrunc alpha beta).trans
    (paperDeterministicMomentRHS_le_deterministicMomentRHS
      hO.le hP.le hlam)

/-- Eventually-small-scale P-3.5b-det with the exact Euclidean Japanese
bracket printed in (3.24). -/
theorem r324PaperScale_hdet_paper
    (ρ : SmoothCutoff) {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant)
    (hstep23 : R324PaperRefinedStep23Input
      ρ primitiveConstant supportConstant)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧
      R324RefinedPostCollapsePaperBracketBound ρ K) :
    ∃ outerC powerC : ℝ, 0 < outerC ∧ 0 < powerC ∧
      ∀ lam : ℝ, 0 < lam →
        ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
          ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ alpha beta : Z4,
            ‖deterministicMomentPairingSum ρ lam ε m alpha beta‖ ≤
              paperDeterministicMomentRHS
                outerC powerC lam ε m alpha beta := by
  obtain ⟨O, P, hO, hP, hbound⟩ :=
    r324PaperScale_exists_deterministicMoment_paper_bound
      ρ hprimitive hsupport hstep23 hbracket
  refine ⟨O, P, hO, hP, ?_⟩
  intro lam hlam
  filter_upwards
      [self_mem_nhdsWithin,
        eventually_smallScale_le
          (show (0 : ℝ) < 1 / 4 by norm_num),
        eventually_one_le_abs_log] with
      ε hεmem hεsmall hlog
  intro m hm hmtrunc alpha beta
  exact hbound lam hlam.le hεmem hεsmall hlog m hm hmtrunc alpha beta

/-- The eventually-small-scale deterministic hypothesis at the exact
paper central-frequency scale. -/
theorem r324PaperScale_hdet
    (ρ : SmoothCutoff) {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant)
    (hstep23 : R324PaperRefinedStep23Input
      ρ primitiveConstant supportConstant)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧
      R324RefinedPostCollapsePaperBracketBound ρ K) :
    ∃ outerC powerC : ℝ, 0 < outerC ∧ 0 < powerC ∧
      ∀ lam : ℝ, 0 < lam →
        ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
          ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β : Z4,
            ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
              deterministicMomentRHS outerC powerC lam ε m α β := by
  obtain ⟨O, P, hO, hP, hbound⟩ :=
    r324PaperScale_exists_deterministicMoment_bound
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

/-- Conditional Theorem 1.1 from the two paper-faithful §4.2 outputs.
The Gabriel--Rosati input remains explicit in `MainConditional`. -/
theorem mainConditional_of_paperRefinedStep23_and_paperBracket
    {M : NoiseModel} {ρ : SmoothCutoff}
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant)
    (hstep23 : R324PaperRefinedStep23Input
      ρ primitiveConstant supportConstant)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧
      R324RefinedPostCollapsePaperBracketBound ρ K) :
    MainConditional M ρ := by
  obtain ⟨O, P, hO, hP, hdet⟩ :=
    r324PaperScale_hdet
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
