import Anderson4D.DetParametrix.Paper42_Moment.R324PaperStep3Pointwise
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperCollapseBudget
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperClosure

/-!
# The conditional main theorem along the paper's own §4.2

Paper: R-324 — §4.2 assembled: Steps 1–4 ⇒ (3.24) ⇒ Theorem 1.1

The proved top-level route `mainConditional_of_analyticResiduals_capped`
reaches `MainConditional` from `R324CappedCrossLedgerStrong`, whose two
clauses take absolute values of the refined fibre cores *before* any
subinterval has been removed.  The paper does the opposite: Step 2(f) is
explicit that absolute values come **last**, after every removal, and
`not_r324InteriorCoreLogBudget_two` shows that taking them early at
`m ≥ 2` discards the renormalizing Green-difference factor.

This module gives the route that follows the paper's ordering.  Its input
is the paper's own Steps 2–3 output, per interval configuration
(`R324Step23ConfigReduction`: the successive removal has been performed and
only then is a norm taken), together with Step 4(B)'s summable route
budget.  Everything else — Step 1, the positional `16^m` count, the nested
chain of Step 3, Step 4's two decay mechanisms, the counterterm bound
(3.22) — is already unconditional.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory Filter Set

/-- **The Steps 2–3 interface from paper §4.2.**

At every coupling, every small scale, and every order inside the paper
truncation, the successive removal of §4.1 has been carried out on each
Definition 3.1 interval configuration, and only afterwards is a modulus
taken — this is exactly Step 2(f).  `R324Step23ConfigReduction` records the
result: per configuration, the gained `(Cλ)^{2m-2k}` times one integrated
inserted majorant of (4.4). -/
def R324PaperStep23Input (ρ : SmoothCutoff)
    (Cred supportConstant : ℝ) : Prop :=
  ∀ (lam ε : ℝ) (m : ℕ) (α β : Z4),
    0 ≤ lam → 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 1 ≤ m →
      R324Step23ConfigReduction ρ lam ε m α β Cred supportConstant

/-- **The Step 4(B) interface from paper §4.2.**

The central `⟨ε²(α+β)⟩⁻⁸` factor comes from the `ε^{1/2}` pigeonhole over
the at most `|log ε|` composition factors.  After
`countableCentralRoutedMomentReductionOutput_of_tsum_le` the whole
mechanism rests on one summable series and its total mass; `amp` is the
amplitude Steps 2–3 have already produced. -/
def R324PaperStep4Input (ρ : SmoothCutoff) (amp : ℝ → ℝ → ℕ → ℝ) : Prop :=
  ∀ (lam ε : ℝ) (m : ℕ) (hm : 0 < m),
    0 < ε → ε ≤ 1 → m ≤ truncOrder ε →
      Summable (ρ.r324GroupedRouteBaseWeight lam hm ε) ∧
        (∑' p, ρ.r324GroupedRouteBaseWeight lam hm ε p) ≤ amp lam ε m

/-- Step 4(A)'s endpoint premise, in the form the routed budget produces.

`countableCentralRoutedMomentReductionOutput_of_tsum_le` delivers the
routed output at total weight `(16·amp)·r324EndpointLoss`, while
`r324Step4_fourEndpoint_budget_eq` says the product of the four endpoint
budgets *is* `r324EndpointLoss`.  So the premise of
`r324Step4_deterministicMomentRHS_of_step23` holds as soon as `16·amp`
does not exceed the Steps 2–3 amplitude. -/
theorem r324Paper_endpoint_premise
    {ε : ℝ} {α β : Z4} {amp amplitude : ℝ}
    (hloss : 0 ≤ r324EndpointLoss ε α β)
    (h : 16 * amp ≤ amplitude) :
    (16 * amp) * r324EndpointLoss ε α β ≤
      amplitude *
        (r324Step4EndpointBudget ε α * r324Step4EndpointBudget ε β *
          (r324Step4EndpointBudget ε α *
            r324Step4EndpointBudget ε β)) := by
  rw [r324Step4_fourEndpoint_budget_eq ε α β]
  exact mul_le_mul_of_nonneg_right h hloss

/-- **§4.2 assembled: the fixed-scale (3.24) bound from the paper's own
inputs.**

Steps 2–3 give the amplitude; Step 4(B) turns the summable route budget
into the countable routed decomposition; Step 4(A)'s endpoint premise is
the arithmetic above; `r324Step4_deterministicMomentRHS_of_step23` lands
the two together in the frozen right side `deterministicMomentRHS`. -/
theorem r324Paper_deterministicMoment_bound
    (ρ : SmoothCutoff) {Cred supportConstant : ℝ}
    (hCred : 0 < Cred) (hsupport : 0 < supportConstant)
    (hstep23 : R324PaperStep23Input ρ Cred supportConstant) :
    ∃ outerC powerC : ℝ, 0 < outerC ∧ 0 < powerC ∧
      (R324PaperStep4Input ρ
        (fun lam ε m =>
          lamEps lam ε ^ 2 * outerC * (powerC * lam) ^ (2 * m - 2) / 16) →
        ∀ (lam ε : ℝ) (m : ℕ) (α β : Z4),
          0 ≤ lam → 0 < ε → ε ≤ 1 / 4 → 1 ≤ |Real.log ε| → 1 ≤ m →
          m ≤ truncOrder ε →
            ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
              deterministicMomentRHS outerC powerC lam ε m α β) := by
  obtain ⟨outerC, powerC, houter, hpower, hbound⟩ :=
    exists_r324Step23_config_bound ρ hCred hsupport
  refine ⟨outerC, powerC, houter, hpower, ?_⟩
  intro hstep4 lam ε m α β hlam hε hεsmall hlog hm hmtrunc
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  set A : ℝ :=
    lamEps lam ε ^ 2 * outerC * (powerC * lam) ^ (2 * m - 2) with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) houter.le)
      (pow_nonneg (mul_nonneg hpower.le hlam) _)
  -- Steps 2–3: the amplitude
  have hamp : ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤ A :=
    hbound lam ε m α β hlam hε hε1 hlog hm
      (hstep23 lam ε m α β hlam hε hε1 hlog hm)
  -- Step 4(B): the countable routed decomposition
  obtain ⟨hsummable, htsum⟩ := hstep4 lam ε m (by omega) hε hε1 hmtrunc
  have hroute :=
    ρ.countableCentralRoutedMomentReductionOutput_of_tsum_le
      lam (m := m) (by omega) hε hε1 hmtrunc α β hsummable htsum
  -- Step 4(A): the endpoint premise
  have hendpoint :
      (16 * (A / 16)) * r324EndpointLoss ε α β ≤
        A *
          (r324Step4EndpointBudget ε α * r324Step4EndpointBudget ε β *
            (r324Step4EndpointBudget ε α *
              r324Step4EndpointBudget ε β)) :=
    r324Paper_endpoint_premise (r324EndpointLoss_nonneg ε α β)
      (by rw [mul_div_cancel₀]; norm_num)
  exact
    r324Step4_deterministicMomentRHS_of_step23 hε hεsmall hamp hroute
      hendpoint le_rfl

/-- **The `hdet` hypothesis of `mainConditional_of_deterministic_bounds`,
from the paper's own §4.2 inputs.** -/
theorem r324Paper_hdet
    (ρ : SmoothCutoff) {Cred supportConstant : ℝ}
    (hCred : 0 < Cred) (hsupport : 0 < supportConstant)
    (hstep23 : R324PaperStep23Input ρ Cred supportConstant) :
    ∃ outerC powerC : ℝ, 0 < outerC ∧ 0 < powerC ∧
      (R324PaperStep4Input ρ
        (fun lam ε m =>
          lamEps lam ε ^ 2 * outerC * (powerC * lam) ^ (2 * m - 2) / 16) →
        ∀ lam : ℝ, 0 < lam →
          ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
            ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β : Z4,
              ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
                deterministicMomentRHS outerC powerC lam ε m α β) := by
  obtain ⟨outerC, powerC, houter, hpower, hbound⟩ :=
    r324Paper_deterministicMoment_bound ρ hCred hsupport hstep23
  refine ⟨outerC, powerC, houter, hpower, ?_⟩
  intro hstep4 lam hlam
  filter_upwards
      [self_mem_nhdsWithin,
        eventually_smallScale_le (show (0 : ℝ) < 1 / 4 by norm_num),
        eventually_one_le_abs_log] with ε hεmem hεsmall hlog
  intro m hm hmtrunc α β
  exact hbound hstep4 lam ε m α β hlam.le hεmem hεsmall hlog hm hmtrunc

/-- **The conditional main theorem, along the paper's own §4.2.**

`MainConditional M ρ` from the paper's Steps 2–3 output — taken *after*
every removal, per Step 2(f) — together with Step 4(B)'s summable route
budget.  The counterterm side is the proved unconditional
`R322AnalyticResidualPrefix.exists_r322_renormC2q_bound` (paper (3.22)).

This is the sound replacement of
`mainConditional_of_analyticResiduals_capped`: its input respects the
paper's ordering of the modulus, so it is not exposed to the obstruction
`not_r324InteriorCoreLogBudget_two` records for pre-collapse norms. -/
theorem mainConditional_of_paperStep23_and_step4
    {M : NoiseModel} {ρ : SmoothCutoff} {Cred supportConstant : ℝ}
    (hCred : 0 < Cred) (hsupport : 0 < supportConstant)
    (hstep23 : R324PaperStep23Input ρ Cred supportConstant)
    (hstep4 : ∀ outerC powerC : ℝ,
      R324PaperStep4Input ρ
        (fun lam ε m =>
          lamEps lam ε ^ 2 * outerC * (powerC * lam) ^ (2 * m - 2) / 16)) :
    MainConditional M ρ := by
  obtain ⟨outerC, powerC, houter, hpower, hdet⟩ :=
    r324Paper_hdet ρ hCred hsupport hstep23
  obtain ⟨Crenorm, hCrenorm, hren⟩ :=
    R322AnalyticResidualPrefix.exists_r322_renormC2q_bound ρ
  refine
    mainConditional_of_deterministic_bounds houter hpower hCrenorm
      (hdet (hstep4 outerC powerC)) ?_
  intro lam hlam
  filter_upwards
      [self_mem_nhdsWithin, eventually_smallScale_le zero_lt_one] with
      ε hεmem hεle
  intro q hq
  have hqB := Finset.mem_Icc.mp hq
  exact hren lam ε q hlam hεmem hεle hqB.1 hqB.2

end

end Anderson4D
