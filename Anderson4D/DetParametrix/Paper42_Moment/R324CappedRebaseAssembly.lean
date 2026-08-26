import Anderson4D.DetParametrix.Paper42_Moment.R324OrderCapNecessity
import Anderson4D.DetParametrix.Paper42_Moment.R324HdetAssemblyFinal

/-!
# Order-capped R-324 conditional closure

The paper uses the fibre bounds only for
orders `m ≤ truncOrder ε = ⌊|log ε|⌋`.  Under that cap the factorial
count is *affordable inside the same budget*: for `1 ≤ m ≤ truncOrder ε`

`m! ≤ m^m ≤ 2^m · |log ε|^{m-1}`
(`r324CappedRebase_factorial_affordable`), so the floor
`C₀·m!·c^m ≤ ∫ (cross density)` is compatible with
`∫ ≤ K^m·|log ε|^{m-1}` for `K ≥ 2c` — no explicit `m!` allowance is
needed in the capped Props, and none may appear in the term-sum ledger
(a factorial there could not pass the per-order bridge with an
`ε`-uniform primitive constant).  The capped cross Prop still implies
the recorded weakest residual form
`R324PermCrossOrderCappedCrossBound`
(`R324CappedCrossLedger.toOrderCappedCrossBound`).

The capped Props are threaded through the per-`m` bridge and the final
assembly — which only ever instantiates
`m ≤ truncOrder ε` — to the capped conditional main theorem
`mainConditional_of_analyticResiduals_capped`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open Filter Set MeasureTheory
open scoped BigOperators Topology

/-! ## The capped residual Props -/

/-- **Capped cross ledger** (uniform branch): the phase-free integral
of the summed pure-cross density carries the windowed value
`K^m·L^{m-1}`, for orders up to the paper truncation
`A = ⌊|log ε|⌋ = truncOrder ε` only.  By
`r324CappedRebase_factorialFloor_affordable` this budget affords the
proved `m!`-floor on the capped range, unlike its refuted uncapped
ancestor `R324HdetCrossIntegralBound`. -/
def R324CappedCrossLedger (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 3 ≤ m →
      m ≤ truncOrder ε →
        ∀ F : Finset (MomentContraction m),
          (∀ e ∈ F, R324LedgerThreeAllCrossEntity e) →
            (∫ p, r324LedgerThreeCrossDensity ρ ε m F p
                ∂(r324PhysicalMeasure m)) ≤
              K ^ m * |Real.log ε| ^ (m - 1)

/-- **Capped mixed ledger**: the residual-refined fibre logarithmic
bound on fibres retaining a within-half pair, for orders up to the
paper truncation only. -/
def R324CappedMixedLedger (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 3 ≤ m →
      m ≤ truncOrder ε →
        ∀ s ∈ momentContractionSignatures m,
          ∀ r ∈ momentResidualChainSignaturesAt m s,
            ¬ R324LedgerThreeCrossFibre m s r →
              ‖momentRefinedDeterministicTermSum ρ ε m α β s r‖ ≤
                K ^ m * |Real.log ε| ^ (m - 1)

/-- **Capped bracket ledger** (routed branch): the proved
`R324HdetBracketLedgerBound` already carries the order cap
`2 ≤ m ≤ truncOrder ε` and needs no change; it is re-exported under
the capped naming scheme. -/
def R324CappedBracketLedger (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  R324HdetBracketLedgerBound ρ K

/-! ## Affordability of the factorial under the cap -/

/-- **The affordability lemma.**  On the capped range
`1 ≤ m ≤ truncOrder ε ≤ |log ε|` the factorial fibre count fits the
logarithmic budget: `m! ≤ m^m ≤ 2^m·|log ε|^{m-1}`. -/
theorem r324CappedRebase_factorial_affordable
    {ε : ℝ} {m : ℕ} (hm : 1 ≤ m) (hcap : m ≤ truncOrder ε) :
    (m.factorial : ℝ) ≤ 2 ^ m * |Real.log ε| ^ (m - 1) := by
  have hmL : (m : ℝ) ≤ |Real.log ε| := by
    refine le_trans ?_ (Nat.floor_le (abs_nonneg (Real.log ε)))
    exact_mod_cast hcap
  have hfac : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by
    exact_mod_cast Nat.factorial_le_pow m
  have hsplit : (m : ℝ) ^ m = (m : ℝ) ^ (m - 1) * (m : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have h2 : (m : ℝ) ≤ 2 ^ m := by
    calc (m : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
          exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
      _ = 2 ^ m := by push_cast; ring
  calc (m.factorial : ℝ) ≤ (m : ℝ) ^ m := hfac
    _ = (m : ℝ) ^ (m - 1) * (m : ℝ) := hsplit
    _ ≤ |Real.log ε| ^ (m - 1) * 2 ^ m := by
        refine mul_le_mul ?_ h2 (Nat.cast_nonneg m)
          (pow_nonneg (abs_nonneg _) _)
        exact pow_le_pow_left₀ (Nat.cast_nonneg m) hmL _
    _ = 2 ^ m * |Real.log ε| ^ (m - 1) := mul_comm _ _

/-- **The precise reconciliation form**: on the capped range the
proved factorial floor `m!·c^m` sits inside the geometric
logarithmic budget at the doubled constant, so the capped cross Prop
is not floor-refutable. -/
theorem r324CappedRebase_factorialFloor_affordable
    {ε c : ℝ} {m : ℕ} (hc : 0 ≤ c)
    (hm : 1 ≤ m) (hcap : m ≤ truncOrder ε) :
    (m.factorial : ℝ) * c ^ m ≤
      (2 * c) ^ m * |Real.log ε| ^ (m - 1) := by
  calc (m.factorial : ℝ) * c ^ m ≤
      (2 ^ m * |Real.log ε| ^ (m - 1)) * c ^ m :=
        mul_le_mul_of_nonneg_right
          (r324CappedRebase_factorial_affordable hm hcap)
          (pow_nonneg hc m)
    _ = (2 * c) ^ m * |Real.log ε| ^ (m - 1) := by
        rw [mul_pow]
        ring

/-- The capped cross ledger implies the recorded weakest sound
residual form (which grants an explicit `m!` allowance). -/
theorem R324CappedCrossLedger.toOrderCappedCrossBound
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (h : R324CappedCrossLedger ρ K) :
    R324PermCrossOrderCappedCrossBound ρ K := by
  intro ε m hε hε1 hlog hm3 hcap F hF
  refine (h m hε hε1 hlog hm3 hcap F hF).trans ?_
  have hfac : (1 : ℝ) ≤ (m.factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_pos m)
  have hKL : (0 : ℝ) ≤ K ^ m * |Real.log ε| ^ (m - 1) :=
    mul_nonneg (pow_nonneg hK m) (pow_nonneg (abs_nonneg _) _)
  calc K ^ m * |Real.log ε| ^ (m - 1) =
      K ^ m * |Real.log ε| ^ (m - 1) * 1 := (mul_one _).symm
    _ ≤ K ^ m * |Real.log ε| ^ (m - 1) * (m.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left hfac hKL
    _ = K ^ m * (m.factorial : ℝ) * |Real.log ε| ^ (m - 1) := by
        ring

/-! ## The capped uniform branch -/

/-- The two capped case ledgers fund the per-fibre logarithmic ledger
at each fixed capped order, through the proved density majorization
on pure-cross fibres. -/
theorem r324CappedRebase_fibreLogBound
    {ρ : SmoothCutoff} {K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hcross : R324CappedCrossLedger ρ K₁)
    (hmixed : R324CappedMixedLedger ρ K₂)
    {ε : ℝ} (m : ℕ) (α β : Z4) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) (hm3 : 3 ≤ m)
    (hcap : m ≤ truncOrder ε) :
    R324GeneralPeelFibreLogBound ρ ε m α β (max K₁ K₂) := by
  intro s hs r hr
  have hLpow : (0 : ℝ) ≤ |Real.log ε| ^ (m - 1) :=
    pow_nonneg (abs_nonneg _) _
  by_cases hfib : R324LedgerThreeCrossFibre m s r
  · refine ((r324LedgerThree_norm_termSum_le_integral_crossDensity
      ρ hε hε1 α β hfib).trans
      (hcross m hε hε1 hlog hm3 hcap _ hfib)).trans ?_
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hK₁ (le_max_left _ _) m) hLpow
  · exact (hmixed m α β hε hε1 hlog hm3 hcap s hs r hr hfib).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hK₂ (le_max_right _ _) m) hLpow)

/-- **Capped uniform-branch supply.**  One per-cutoff primitive
constant discharges the residual-refined reduction obligation at every
*capped* order `1 ≤ m ≤ truncOrder ε`: the proved unconditional
low orders below three, the capped ledgers through the proved
per-`m` bridge from three. -/
theorem r324CappedRebase_exists_outputAt
    (ρ : SmoothCutoff)
    (hcross : ∃ K : ℝ, 0 ≤ K ∧ R324CappedCrossLedger ρ K)
    (hmixed : ∃ K : ℝ, 0 ≤ K ∧ R324CappedMixedLedger ρ K) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (lam : ℝ) {ε : ℝ} (m : ℕ) (α β : Z4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 1 ≤ m →
          m ≤ truncOrder ε →
          MomentRefinedIntegratedReductionOutputAt
            ρ lam ε m α β C₀ 1 := by
  obtain ⟨K₁, hK₁, hc⟩ := hcross
  obtain ⟨K₂, hK₂, hm'⟩ := hmixed
  obtain ⟨Clow, hClow, hlow⟩ :=
    exists_momentRefinedIntegratedReductionOutputAt_le_two ρ
  have hKmax : (0 : ℝ) ≤ max K₁ K₂ :=
    le_trans hK₁ (le_max_left _ _)
  refine ⟨max Clow (max K₁ K₂ + 1),
    lt_max_of_lt_left hClow, ?_⟩
  intro lam ε m α β hε hε1 hlog hm hcap
  by_cases hm3 : 3 ≤ m
  · refine
      (momentRefinedIntegratedReductionOutputAt_of_generalPeelFibreLogBound
        hm hε hε1 hlog hKmax
        (r324CappedRebase_fibreLogBound hK₁ hK₂ hc hm'
          m α β hε hε1 hlog hm3 hcap)).mono_primitiveConstant
        (by linarith) (le_max_right _ _) hε
  · exact
      (hlow lam m α β hε hε1 hlog hm
        (by omega)).mono_primitiveConstant
        hClow.le (le_max_left _ _) hε

/-! ## Landing in the frozen deterministic right side -/

/-- **The fixed-scale deterministic (3.24) bound from the three capped
residual Props.**  Verbatim the proved assembly
`r324HdetAssembly_exists_deterministicMoment_bound` with the uniform
branch re-based on the capped supply: the assembly only ever
instantiates orders `m ≤ truncOrder ε`, so the cap threads through
with no loss. -/
theorem r324CappedRebase_exists_deterministicMoment_bound
    (ρ : SmoothCutoff)
    (hcross : ∃ K : ℝ, 0 ≤ K ∧ R324CappedCrossLedger ρ K)
    (hmixed : ∃ K : ℝ, 0 ≤ K ∧ R324CappedMixedLedger ρ K)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧ R324CappedBracketLedger ρ K) :
    ∃ outerC powerC : ℝ, 0 < outerC ∧ 0 < powerC ∧
      ∀ (lam : ℝ), 0 ≤ lam → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β : Z4,
          ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
            deterministicMomentRHS outerC powerC lam ε m α β := by
  obtain ⟨Kb, hKb, hbr⟩ := hbracket
  obtain ⟨C₀, hC₀, hunif⟩ :=
    r324CappedRebase_exists_outputAt ρ hcross hmixed
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
      (hunif lam m α β hε hε1 hlog hm hmtrunc)
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
  · -- `m ≥ 2`: capped summed bracket ledger, landed through the
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

/-! ## The hdet hypothesis and the capped conditional main theorem -/

/-- The exact `hdet` hypothesis of the proved
`mainConditional_of_deterministic_bounds`, delivered from the three
capped residual Props. -/
theorem r324CappedRebase_hdet
    (ρ : SmoothCutoff)
    (hcross : ∃ K : ℝ, 0 ≤ K ∧ R324CappedCrossLedger ρ K)
    (hmixed : ∃ K : ℝ, 0 ≤ K ∧ R324CappedMixedLedger ρ K)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧ R324CappedBracketLedger ρ K) :
    ∃ outerC powerC : ℝ, 0 < outerC ∧ 0 < powerC ∧
      ∀ lam : ℝ, 0 < lam →
        ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
          ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β : Z4,
            ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
              deterministicMomentRHS outerC powerC lam ε m α β := by
  obtain ⟨O, P, hO, hP, hbound⟩ :=
    r324CappedRebase_exists_deterministicMoment_bound
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

/-- **The capped conditional main theorem.**  The complete
`MainConditional M ρ` follows from the three *order-capped* analytic
obligations, each restricted to the paper truncation range
`m ≤ truncOrder ε = ⌊|log ε|⌋`:

* the capped pure-cross density bound (`R324CappedCrossLedger`,
  uniform branch, `3 ≤ m ≤ truncOrder ε`) — the sound replacement of
  the refuted `R324HdetCrossIntegralBound`;
* the capped mixed-fibre ledger (`R324CappedMixedLedger`,
  `3 ≤ m ≤ truncOrder ε`) — the sound replacement of the (jointly
  refuted) uncapped `R324LedgerThreeMixedLedger`;
* the bracket-retaining fibre ledger (`R324CappedBracketLedger` =
  proved `R324HdetBracketLedgerBound`, routed branch,
  `2 ≤ m ≤ truncOrder ε`, unchanged).

The counterterm input is the proved unconditional
`R322AnalyticResidualPrefix.exists_r322_renormC2q_bound`; the
order-one routed branch is proved and unconditional.  The three capped Props
are genuine analytic hypotheses; unlike their uncapped counterparts they are not
refutable by the factorial fibre floor
(`r324CappedRebase_factorialFloor_affordable`). -/
theorem mainConditional_of_analyticResiduals_capped
    {M : NoiseModel} {ρ : SmoothCutoff}
    (hcross : ∃ K : ℝ, 0 ≤ K ∧ R324CappedCrossLedger ρ K)
    (hmixed : ∃ K : ℝ, 0 ≤ K ∧ R324CappedMixedLedger ρ K)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧ R324CappedBracketLedger ρ K) :
    MainConditional M ρ := by
  obtain ⟨O, P, hO, hP, hdet⟩ :=
    r324CappedRebase_hdet ρ hcross hmixed hbracket
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
