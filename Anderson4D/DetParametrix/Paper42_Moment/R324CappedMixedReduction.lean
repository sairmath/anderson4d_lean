import Anderson4D.DetParametrix.Paper42_Moment.R324CappedRebaseAssembly
import Anderson4D.DetParametrix.Paper42_Moment.R324LedgerThreeCross

/-!
# Collapsing the three capped residual Props to one

`R324CappedRebaseAssembly.mainConditional_of_analyticResiduals_capped`
consumes three analytic obligations: `R324CappedCrossLedger`,
`R324CappedMixedLedger` and `R324CappedBracketLedger`.  This file
replaces all three by a single ledger `R324CappedCrossLedgerStrong`
stated at the level of the physical density on *arbitrary* finite sets
of order-`m` contraction entities, and proves the three reductions and
the resulting single-obligation conditional main theorem.

## The carrier

`r324CMFlatDensity ρ ε m α β F p = ‖∑_{e ∈ F} flatten(integrand e) p‖`
— the pointwise norm of the summed flattened contraction integrand.
Two proved facts make it the right carrier:

* on an **all-cross** `F` it *equals* the proved nonnegative
  pure-cross density `r324LedgerThreeCrossDensity`
  (`r324LedgerThree_norm_sum_flatten_eq`), so a density ledger
  specializes back to the plain `R324CappedCrossLedger`;
* for an **arbitrary** `F` its integral dominates the norm of the
  summed contraction terms (`r324CM_norm_sum_le_integral_flatDensity`:
  proved joint integrability plus one Bochner triangle
  inequality), so with `F` the residual-refined fibre it dominates
  `momentRefinedDeterministicTermSum` on *every* fibre — cross or
  mixed.  The sum stays inside the norm, so the renormalization
  difference factors of within-half pairs keep their cancellation and
  no factorial entity count is spent.

## Why two clauses are needed

The bracket Prop grades its right-hand side by the external modes
`α, β` through `r324EndpointLoss ε α β · ⟨ε‖freq(α+β)‖⟩⁻⁸`, a weight
that tends to `0` as `‖α‖ → ∞`.  But the density above is **exactly
independent** of `α` and `β` (`r324CMFlatDensity_modes_indep`): the
external modes enter the integrand only through four unimodular
characters, which factor out of the entity sum.  So no bound on a
modulus density — however strong — can imply the bracket ledger: the
mode decay lives in the cancellation of the external `x, y, z, w`
integrations, which any pointwise norm destroys.  The strong ledger
therefore has a second, phase-retaining clause, stated on the summed
contraction *terms*, i.e. after the physical integration.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The absolute flat fibre density -/

/-- **The absolute flat fibre density.**  Pointwise norm of the summed
flattened deterministic integrand over a finite set `F` of order-`m`
contraction entities.  No positivity is assumed of the entities: `F`
may contain entities with within-half pairs, whose flat integrands
carry the signed renormalization difference factors. -/
def r324CMFlatDensity
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (F : Finset (MomentContraction m))
    (p : R324PhysicalPoint m) : ℝ :=
  ‖∑ e ∈ F,
      r324Flatten
        (deterministicMomentIntegrand ρ ε m α β
          e.1 e.2.1 e.2.2) p‖

theorem r324CMFlatDensity_nonneg
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (F : Finset (MomentContraction m))
    (p : R324PhysicalPoint m) :
    0 ≤ r324CMFlatDensity ρ ε m α β F p :=
  norm_nonneg _

/-- **The density is blind to the external modes.**  The four external
characters are unimodular and do not depend on the entity, so they
factor out of the sum and disappear under the norm.  Consequently a
ledger on this density can never see the mode decay demanded by
`R324HdetBracketLedgerBound`: that decay is a property of the external
integrations, not of the pointwise density. -/
theorem r324CMFlatDensity_modes_indep
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β α' β' : Z4)
    (F : Finset (MomentContraction m))
    (p : R324PhysicalPoint m) :
    r324CMFlatDensity ρ ε m α β F p =
      r324CMFlatDensity ρ ε m α' β' F p := by
  unfold r324CMFlatDensity r324Flatten deterministicMomentIntegrand
  simp only [← Finset.mul_sum, norm_mul, norm_charT4, one_mul]

/-- On a pure-cross entity set the absolute flat density **is** the
proved nonnegative pure-cross density: the external phase is
unimodular and every remaining factor is nonnegative. -/
theorem r324CMFlatDensity_eq_crossDensity
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (α β : Z4)
    {F : Finset (MomentContraction m)}
    (hF : ∀ e ∈ F, R324LedgerThreeAllCrossEntity e)
    (p : R324PhysicalPoint m) :
    r324CMFlatDensity ρ ε m α β F p =
      r324LedgerThreeCrossDensity ρ ε m F p :=
  r324LedgerThree_norm_sum_flatten_eq ρ ε α β hF p

/-! ## The integral representation on an arbitrary entity set -/

/-- The summed contraction terms of an arbitrary finite entity set are
one physical integral of the summed flat integrand. -/
theorem r324CM_sum_term_eq_integral
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (α β : Z4) (F : Finset (MomentContraction m)) :
    (∑ e ∈ F, deterministicMomentContractionTerm ρ ε m α β e) =
      ∫ p, ∑ e ∈ F,
          r324Flatten
            (deterministicMomentIntegrand ρ ε m α β
              e.1 e.2.1 e.2.2) p
        ∂(r324PhysicalMeasure m) := by
  rw [integral_finsetSum _
    (fun e _ => r324MomentIntegrable_all ρ hε hε1 α β e)]
  exact Finset.sum_congr rfl fun e _he =>
    (integral_r324Flatten_deterministicMomentIntegrand
      ρ ε m α β e (r324MomentIntegrable_all ρ hε hε1 α β e)).symm

/-- **The cancellation-preserving domination on an arbitrary entity
set.**  Only the Bochner triangle inequality is used; the sum stays
inside the norm, so no factorial entity count is spent. -/
theorem r324CM_norm_sum_le_integral_flatDensity
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (α β : Z4) (F : Finset (MomentContraction m)) :
    ‖∑ e ∈ F, deterministicMomentContractionTerm ρ ε m α β e‖ ≤
      ∫ p, r324CMFlatDensity ρ ε m α β F p
        ∂(r324PhysicalMeasure m) := by
  rw [r324CM_sum_term_eq_integral ρ hε hε1 α β F]
  exact norm_integral_le_integral_norm _

/-- Fibre form: every residual-refined fibre sum — cross **or**
mixed — is dominated by the integral of the absolute flat density of
the fibre. -/
theorem r324CM_norm_termSum_le_integral_flatDensity
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (α β : Z4)
    (s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))) :
    ‖momentRefinedDeterministicTermSum ρ ε m α β s r‖ ≤
      ∫ p, r324CMFlatDensity ρ ε m α β
          (momentRefinedContractionFiber m s r) p
        ∂(r324PhysicalMeasure m) :=
  r324CM_norm_sum_le_integral_flatDensity ρ hε hε1 α β _

/-! ## The bracket weight -/

/-- The bracket-retaining weight of `R324HdetBracketLedgerBound`:
`ε⁻⁸⟨α⟩⁻⁴⟨β⟩⁻⁴ · ⟨ε‖freq(α+β)‖⟩⁻⁸`. -/
def r324CMBracketWeight (ε : ℝ) (α β : Z4) : ℝ :=
  r324EndpointLoss ε α β *
    eighthOrderFrequencyDecay
      (ε * ‖z4EuclideanFrequency (α + β)‖)

theorem r324CMBracketWeight_nonneg (ε : ℝ) (α β : Z4) :
    0 ≤ r324CMBracketWeight ε α β :=
  mul_nonneg (r324EndpointLoss_nonneg ε α β)
    (eighthOrderFrequencyDecay_nonneg _)

/-! ## The unified obligation -/

/-- **Clause A — the capped density ledger.**  The plain
`R324CappedCrossLedger` is exactly this restricted to *pure-cross*
entity sets and to orders `m ≥ 3`
(`R324CappedCrossLedgerStrong.toCross`).  The strengthening is that
`F` ranges over **arbitrary** order-`m` entity sets, so the signed
renormalization difference factors of within-half pairs are covered:
this is the parity-gain peel content missing from the plain form.
The external modes are frozen at `0` — by
`r324CMFlatDensity_modes_indep` the density does not depend on
them. -/
def R324CappedDensityLedger (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        ∀ F : Finset (MomentContraction m),
          (∫ p, r324CMFlatDensity ρ ε m 0 0 F p
              ∂(r324PhysicalMeasure m)) ≤
            K ^ m * |Real.log ε| ^ (m - 1)

/-- **Clause B — the capped bracket density ledger.**  The
phase-retaining companion of clause A: the same entity sets, the same
capped order range, but the norm is taken *after* the physical
integration, so the external `x, y, z, w` cancellation survives and
the mode-graded weight `r324CMBracketWeight` is available.  This
clause cannot be dropped: by `r324CMFlatDensity_modes_indep` no
modulus-density ledger implies mode decay.  It is stated for arbitrary
entity sets `F`, whereas `R324HdetBracketLedgerBound` asks only for
the residual-refined fibres and grants an extra `m⁸`. -/
def R324CappedBracketDensityLedger
    (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        ∀ F : Finset (MomentContraction m),
          ‖∑ e ∈ F,
              deterministicMomentContractionTerm ρ ε m α β e‖ ≤
            K ^ m * |Real.log ε| ^ (m - 1) *
              r324CMBracketWeight ε α β

/-- **The strengthened capped cross ledger**: one Prop, two clauses,
both stated for arbitrary entity sets on the physical measure at every
capped order `2 ≤ m ≤ truncOrder ε`.  It implies all three residual
Props of `R324CappedRebaseAssembly`. -/
def R324CappedCrossLedgerStrong (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  R324CappedDensityLedger ρ K ∧ R324CappedBracketDensityLedger ρ K

/-! ## The three reductions -/

/-- **Reduction 1: the plain capped cross ledger.**  On an all-cross
entity set the absolute flat density equals the proved pure-cross
density, so clause A returns the uniform budget verbatim. -/
theorem R324CappedCrossLedgerStrong.toCross
    {ρ : SmoothCutoff} {K : ℝ}
    (h : R324CappedCrossLedgerStrong ρ K) :
    R324CappedCrossLedger ρ K := by
  intro ε m hε hε1 hlog hm3 hcap F hF
  calc
    (∫ p, r324LedgerThreeCrossDensity ρ ε m F p
        ∂(r324PhysicalMeasure m)) =
        ∫ p, r324CMFlatDensity ρ ε m 0 0 F p
          ∂(r324PhysicalMeasure m) :=
      integral_congr_ae (Filter.Eventually.of_forall fun p =>
        (r324CMFlatDensity_eq_crossDensity ρ ε 0 0 hF p).symm)
    _ ≤ K ^ m * |Real.log ε| ^ (m - 1) :=
      h.1 m hε hε1 hlog (by omega) hcap F

/-- **Reduction 2: the capped mixed ledger.**  The fibre hypothesis
`¬ R324LedgerThreeCrossFibre` is never used: clause A covers arbitrary
entity sets, so the same estimate holds on every fibre.  The external
modes are removed by `r324CMFlatDensity_modes_indep`. -/
theorem R324CappedCrossLedgerStrong.toMixed
    {ρ : SmoothCutoff} {K : ℝ}
    (h : R324CappedCrossLedgerStrong ρ K) :
    R324CappedMixedLedger ρ K := by
  intro ε m α β hε hε1 hlog hm3 hcap s _hs r _hr _hfib
  calc
    ‖momentRefinedDeterministicTermSum ρ ε m α β s r‖ ≤
        ∫ p, r324CMFlatDensity ρ ε m α β
            (momentRefinedContractionFiber m s r) p
          ∂(r324PhysicalMeasure m) :=
      r324CM_norm_termSum_le_integral_flatDensity ρ hε hε1 α β s r
    _ = ∫ p, r324CMFlatDensity ρ ε m 0 0
            (momentRefinedContractionFiber m s r) p
          ∂(r324PhysicalMeasure m) :=
      integral_congr_ae (Filter.Eventually.of_forall fun p =>
        r324CMFlatDensity_modes_indep ρ ε m α β 0 0 _ p)
    _ ≤ K ^ m * |Real.log ε| ^ (m - 1) :=
      h.1 m hε hε1 hlog (by omega) hcap _

/-- **Reduction 3: the bracket-retaining fibre ledger.**  Clause B at
the residual-refined fibre supplies the endpoint loss and the central
eighth-order bracket; the proved `m⁸` allowance is then free. -/
theorem R324CappedCrossLedgerStrong.toBracket
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (h : R324CappedCrossLedgerStrong ρ K) :
    R324CappedBracketLedger ρ K := by
  intro ε m α β hε hε1 hlog hm2 hcap s _hs r _hr
  have hW0 : 0 ≤ r324CMBracketWeight ε α β :=
    r324CMBracketWeight_nonneg ε α β
  have hKL : (0 : ℝ) ≤ K ^ m * |Real.log ε| ^ (m - 1) :=
    mul_nonneg (pow_nonneg hK m) (pow_nonneg (abs_nonneg _) _)
  have hm8 : (1 : ℝ) ≤ (m : ℝ) ^ 8 := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.one_le_of_lt hm2
    exact one_le_pow₀ h1
  calc
    ‖momentRefinedDeterministicTermSum ρ ε m α β s r‖ ≤
        K ^ m * |Real.log ε| ^ (m - 1) *
          r324CMBracketWeight ε α β :=
      h.2 m α β hε hε1 hlog hm2 hcap _
    _ ≤ (m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
          r324CMBracketWeight ε α β := by
      have hXB : (0 : ℝ) ≤
          K ^ m * |Real.log ε| ^ (m - 1) *
            r324CMBracketWeight ε α β :=
        mul_nonneg hKL hW0
      nlinarith [hXB, hm8]

/-! ## Conditional closure from the capped density ledger -/

/-- **The single-obligation conditional main theorem.**  The complete
`MainConditional M ρ` follows from the *one* capped density ledger
`R324CappedCrossLedgerStrong`.  All three capped residual Props of
`R324CappedRebaseAssembly` — the pure-cross density bound, the mixed
fibre ledger and the bracket-retaining routed ledger — are supplied by
it, and every other input of the proved capped assembly
(`mainConditional_of_analyticResiduals_capped`) is unconditional. -/
theorem mainConditional_of_cappedCrossLedgerStrong
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : ∃ K : ℝ, 0 ≤ K ∧ R324CappedCrossLedgerStrong ρ K) :
    MainConditional M ρ := by
  obtain ⟨K, hK, hled⟩ := h
  exact mainConditional_of_analyticResiduals_capped
    ⟨K, hK, hled.toCross⟩
    ⟨K, hK, hled.toMixed⟩
    ⟨K, hK, hled.toBracket hK⟩

end

end Anderson4D
