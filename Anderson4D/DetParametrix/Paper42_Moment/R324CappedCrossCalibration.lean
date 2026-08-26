import Anderson4D.DetParametrix.Paper42_Moment.R324CappedCrossGrading

/-!
# Capped cross ledger, part 1: entity integrals and the graded reduction

This file isolates the *per-entity* integral

`J(e) = ∫ (left chain)·(right chain)·(cross covariance of e) dp`

of a pure-cross contraction entity, records its integrability, and
proves the **graded reduction**: the capped cross ledger
`R324CappedCrossLedger` follows from a per-entity bound `C^m·L^{grade e}`
together with the *graded count* `∑_e L^{grade e} ≤ C^m·L^{m-1}`
(`r324CappedCrossLedger_of_grading`).

The grading is forced.  An ungraded per-entity ceiling `C^m·L^{m-1}`
(which is *sharp*: the identity entity really is of that size, and by
`r324PermCross_integral_crossDensity_ge` every entity is `≥ c^m`)
multiplied by the `m!` entity count only gives `C^m·L^{2(m-1)}` once
`m! ≈ L^{m-1}` at the top of the capped range — over budget by
`L^{m-1}`.  So a proof must exploit that only `≈ C^m` entities carry
the full window power.  Exactly at `m = 3` the count `3! = 6` is itself
`≤ C^m`, so there the ungraded bound suffices
(`r324CappedCrossGradingBound_of_entityBound`), which is why the
`m = 3` calibration is the honest first target.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The per-entity integral -/

/-- The physical integral of one pure-cross contraction entity. -/
def r324CappedCrossEntityIntegral
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (e : MomentContraction m) : ℝ :=
  ∫ p, r324CappedCrossEntityDensity ρ ε m e p ∂(r324PhysicalMeasure m)

/-- Every pure-cross entity density is integrable on the physical
space (proved: it is the density of one permutation summand). -/
theorem r324CappedCrossEntityDensity_integrable
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {m : ℕ}
    {e : MomentContraction m} (he : R324LedgerThreeAllCrossEntity e) :
    Integrable (fun p => r324CappedCrossEntityDensity ρ ε m e p)
      (r324PhysicalMeasure m) := by
  obtain ⟨π, rfl⟩ := he.eq_mk
  exact r324PermCross_integrable_summand ρ hε hε1 π

theorem r324CappedCrossEntityIntegral_nonneg
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (e : MomentContraction m) :
    0 ≤ r324CappedCrossEntityIntegral ρ ε m e :=
  integral_nonneg fun p => r324CappedCrossEntityDensity_nonneg ρ ε m e p

/-- Membership in the permutation entities forces the pure-cross
shape. -/
theorem r324CappedCross_allCross_of_mem_permEntities
    {m : ℕ} {e : MomentContraction m}
    (he : e ∈ r324LedgerThreePermEntities m) :
    R324LedgerThreeAllCrossEntity e := by
  obtain ⟨π, _, rfl⟩ := Finset.mem_image.mp he
  exact ⟨rfl, rfl⟩

/-- **The fibre integral is the entity-wise sum of entity integrals.** -/
theorem r324CappedCross_integral_eq_sum
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {m : ℕ}
    {F : Finset (MomentContraction m)}
    (hF : ∀ e ∈ F, R324LedgerThreeAllCrossEntity e) :
    (∫ p, r324LedgerThreeCrossDensity ρ ε m F p
        ∂(r324PhysicalMeasure m)) =
      ∑ e ∈ F, r324CappedCrossEntityIntegral ρ ε m e := by
  have hcongr :
      (∫ p, r324LedgerThreeCrossDensity ρ ε m F p
          ∂(r324PhysicalMeasure m)) =
        ∫ p, (∑ e ∈ F, r324CappedCrossEntityDensity ρ ε m e p)
          ∂(r324PhysicalMeasure m) := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro p
    exact r324CappedCross_density_eq_sum ρ ε m F p
  rw [hcongr, integral_finsetSum _
    (fun e he => r324CappedCrossEntityDensity_integrable ρ hε hε1 (hF e he))]
  rfl

/-! ## The grading Prop -/

/-- **The graded per-entity ledger.**  At each capped order there is a
grade function on the pure-cross entities such that

* each entity integral is `≤ C^m·L^{grade e}`, and
* the graded count obeys `∑_e L^{grade e} ≤ C^m·L^{m-1}`.

The identity-like entities saturate `grade = m-1` but number only
`≈ C^m`; the deranged ones lose window resonance and carry a strictly
smaller grade.  This is the exact content that a uniform per-entity
bound cannot supply. -/
def R324CappedCrossGradingBoundAt
    (ρ : SmoothCutoff) (C : ℝ) (m : ℕ) : Prop :=
  ∀ {ε : ℝ},
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 3 ≤ m → m ≤ truncOrder ε →
      ∃ grade : MomentContraction m → ℕ,
        (∀ e ∈ r324LedgerThreePermEntities m,
            r324CappedCrossEntityIntegral ρ ε m e ≤
              C ^ m * |Real.log ε| ^ grade e) ∧
          (∑ e ∈ r324LedgerThreePermEntities m,
              |Real.log ε| ^ grade e) ≤
            C ^ m * |Real.log ε| ^ (m - 1)

/-- The grading Prop at every capped order. -/
def R324CappedCrossGradingBound (ρ : SmoothCutoff) (C : ℝ) : Prop :=
  ∀ m : ℕ, R324CappedCrossGradingBoundAt ρ C m

/-- The capped cross ledger at one fixed order. -/
def R324CappedCrossLedgerAt (ρ : SmoothCutoff) (K : ℝ) (m : ℕ) : Prop :=
  ∀ {ε : ℝ},
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 3 ≤ m → m ≤ truncOrder ε →
      ∀ F : Finset (MomentContraction m),
        (∀ e ∈ F, R324LedgerThreeAllCrossEntity e) →
          (∫ p, r324LedgerThreeCrossDensity ρ ε m F p
              ∂(r324PhysicalMeasure m)) ≤
            K ^ m * |Real.log ε| ^ (m - 1)

/-- The order-indexed ledgers assemble to the exact proved Prop. -/
theorem r324CappedCrossLedger_of_at
    {ρ : SmoothCutoff} {K : ℝ}
    (h : ∀ m : ℕ, R324CappedCrossLedgerAt ρ K m) :
    R324CappedCrossLedger ρ K :=
  fun m hε hε1 hlog hm3 hcap F hF => h m hε hε1 hlog hm3 hcap F hF

/-- **The graded reduction at one order.**  The grading Prop delivers
the capped cross ledger at the squared constant. -/
theorem r324CappedCrossLedgerAt_of_gradingAt
    {ρ : SmoothCutoff} {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (h : R324CappedCrossGradingBoundAt ρ C m) :
    R324CappedCrossLedgerAt ρ (C * C) m := by
  intro ε hε hε1 hlog hm3 hcap F hF
  obtain ⟨grade, hent, hcount⟩ := h hε hε1 hlog hm3 hcap
  have hCm : (0 : ℝ) ≤ C ^ m := pow_nonneg hC m
  have hsub : F ⊆ r324LedgerThreePermEntities m :=
    r324LedgerThree_subset_permEntities hF
  rw [r324CappedCross_integral_eq_sum ρ hε hε1 hF]
  calc
    (∑ e ∈ F, r324CappedCrossEntityIntegral ρ ε m e) ≤
        ∑ e ∈ F, C ^ m * |Real.log ε| ^ grade e := by
      refine Finset.sum_le_sum fun e he => hent e (hsub he)
    _ ≤ ∑ e ∈ r324LedgerThreePermEntities m,
          C ^ m * |Real.log ε| ^ grade e := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro e _ _
      exact mul_nonneg hCm (pow_nonneg (abs_nonneg _) _)
    _ = C ^ m * ∑ e ∈ r324LedgerThreePermEntities m,
          |Real.log ε| ^ grade e := by
      rw [Finset.mul_sum]
    _ ≤ C ^ m * (C ^ m * |Real.log ε| ^ (m - 1)) :=
      mul_le_mul_of_nonneg_left hcount hCm
    _ = (C * C) ^ m * |Real.log ε| ^ (m - 1) := by
      rw [mul_pow]; ring

/-- **The graded reduction, all orders.**  The grading Prop delivers
the exact proved `R324CappedCrossLedger` at the squared constant. -/
theorem r324CappedCrossLedger_of_grading
    {ρ : SmoothCutoff} {C : ℝ} (hC : 0 ≤ C)
    (h : R324CappedCrossGradingBound ρ C) :
    R324CappedCrossLedger ρ (C * C) :=
  r324CappedCrossLedger_of_at
    (fun m => r324CappedCrossLedgerAt_of_gradingAt hC (h m))

/-- **The endpoint.**  The graded cross ledger plugs straight into the
proved capped conditional main theorem: `MainConditional` follows
from the grading Prop together with the two other capped residual
Props. -/
theorem mainConditional_of_crossGrading_capped
    {M : NoiseModel} {ρ : SmoothCutoff}
    (hgrade : ∃ C : ℝ, 0 ≤ C ∧ R324CappedCrossGradingBound ρ C)
    (hmixed : ∃ K : ℝ, 0 ≤ K ∧ R324CappedMixedLedger ρ K)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧ R324CappedBracketLedger ρ K) :
    MainConditional M ρ := by
  obtain ⟨C, hC, h⟩ := hgrade
  exact mainConditional_of_analyticResiduals_capped
    ⟨C * C, mul_nonneg hC hC, r324CappedCrossLedger_of_grading hC h⟩
    hmixed hbracket

/-! ## The ungraded per-entity bound and its exact range of validity -/

/-- **The ungraded per-entity ledger**: every pure-cross entity
integral obeys the *full* window bound `C^m·L^{m-1}`.  This is sharp
(the identity entity saturates it) and is the object the `m = 3`
calibration evaluates. -/
def R324CappedCrossEntityBoundAt
    (ρ : SmoothCutoff) (C : ℝ) (m : ℕ) : Prop :=
  ∀ {ε : ℝ},
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 3 ≤ m → m ≤ truncOrder ε →
      ∀ e ∈ r324LedgerThreePermEntities m,
        r324CappedCrossEntityIntegral ρ ε m e ≤
          C ^ m * |Real.log ε| ^ (m - 1)

/-- The number of pure-cross entities is `m!`. -/
theorem r324CappedCross_card_permEntities (m : ℕ) :
    (r324LedgerThreePermEntities m).card = m.factorial := by
  unfold r324LedgerThreePermEntities
  rw [Finset.card_image_of_injective _ ?inj, Finset.card_univ,
    r324PermCross_card_equiv]
  case inj =>
    intro π π' h
    exact r324LedgerThree_mk_injective h

/-- **The ungraded bound funds the grading exactly when the factorial
count at this order is geometric.**  With the constant `D` absorbing
`m!` this gives the grading Prop with the flat grade `m-1`.  At `m = 3`
the hypothesis holds with `D = 2` (`3! = 6 ≤ 8`); for large `m` it
fails for every fixed `D`, which is the precise reason the grading is
unavoidable beyond the lowest orders. -/
theorem r324CappedCrossGradingBoundAt_of_entityBoundAt
    {ρ : SmoothCutoff} {C D : ℝ} {m : ℕ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfac : (m.factorial : ℝ) ≤ D ^ m)
    (h : R324CappedCrossEntityBoundAt ρ C m) :
    R324CappedCrossGradingBoundAt ρ (max C D) m := by
  intro ε hε hε1 hlog hm3 hcap
  refine ⟨fun _ => m - 1, ?_, ?_⟩
  · intro e he
    refine (h hε hε1 hlog hm3 hcap e he).trans ?_
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hC (le_max_left _ _) m)
      (pow_nonneg (abs_nonneg _) _)
  · rw [Finset.sum_const, r324CappedCross_card_permEntities,
      nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_
      (pow_nonneg (abs_nonneg _) _)
    exact hfac.trans (pow_le_pow_left₀ hD (le_max_right _ _) m)

/-- **The `m = 3` slice needs no grading.**  The entity count `3! = 6`
is already geometric, so the ungraded per-entity bound closes the
capped cross ledger at order three outright. -/
theorem r324CappedCrossLedgerAt_three_of_entityBoundAt
    {ρ : SmoothCutoff} {C : ℝ} (hC : 2 ≤ C)
    (h : R324CappedCrossEntityBoundAt ρ C 3) :
    R324CappedCrossLedgerAt ρ (C * C) 3 := by
  have hC0 : (0 : ℝ) ≤ C := le_trans (by norm_num) hC
  have hfac : ((Nat.factorial 3 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 3 := by
    norm_num [Nat.factorial]
  have hgrade :
      R324CappedCrossGradingBoundAt ρ (max C 2) 3 :=
    r324CappedCrossGradingBoundAt_of_entityBoundAt hC0
      (by norm_num) hfac h
  have hmax : max C (2 : ℝ) = C := max_eq_left hC
  rw [hmax] at hgrade
  intro ε hε hε1 hlog hm3 hcap F hF
  exact r324CappedCrossLedgerAt_of_gradingAt hC0 hgrade
    hε hε1 hlog hm3 hcap F hF

end

end Anderson4D
