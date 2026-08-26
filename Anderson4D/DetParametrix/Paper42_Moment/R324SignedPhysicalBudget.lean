import Anderson4D.DetParametrix.Paper42_Moment.R324InsertedMajorantBridge

/-!
# Signed-physical budget route for the R-324 routed branch

Every proved producer of the routing input measures the countable
key/route series through a *norm placed inside the key sum*:

* `signedRoutedPrimitiveSlotCollapseData_of_rawCaseIntegralBudget`
  consumes `∑ cases ∫ r324RawCaseDensity`, and the raw case density is
  the pointwise `tsum` of `‖r324KeyGroupedRefinedEndpointCore‖` over
  the key configurations — norm inside the key sum;
* `countableCentralRoutedMomentReductionOutput_of_zeroShift` consumes
  `∑' p, r324ZeroShiftGroupedWeight`, proportional to
  `r324GroupedRefinedCoreL1`, the integrated norm of one key group;
* `countableCentralRoutedMomentReductionOutput_of_nonzeroRoutes`
  consumes `∑' pr, r324RefinedEndpointNonzeroRouteWeight`, built from
  `‖r324RefinedEndpointNonzeroRouteInternalCore‖`.

By the proved optimality results (`R324KeyedPrimitiveCollapse`
header, `R324TotalMassBudget`), any interface of that shape costs at
least `ε⁻⁶` per marked slot and cannot reach an `ε`-uniform amplitude:
splitting the physical covariance `η_ε` into normed frequency keys
loses the Parseval cancellation.

The consumer side, however, is agnostic:
`CountableCentralRoutedMomentDecomposition` accepts *any* countable
decomposition, in particular the one-term decomposition whose sole
term is the full signed pairing sum with all covariances reassembled.
This file provides that signed-physical producer: the entire routed
branch reduces to one scalar inequality on
`‖deterministicMomentPairingSum‖` — the signed physical integral,
key sum inside — with the central eighth-order decay at a routed
increment scale `‖freq(α+β)‖ / nInc`, `nInc ≤ truncOrder ε`.

It also records the iterated Proposition-4.1 block ledger in signed
physical form: each primitive block is bounded *after* its signed
pairing-fibre sum (`renormC2q` keeps the covariances `η_ε` inside
`detJintegrand`), one block of order `q` costs
`(Cλ)^(2q) · ε⁻²/|log ε|`, and a schedule of `k` blocks costs the
product — `O(1)` per covariance pair, `ε⁻²/|log ε|` once per block.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- `1 ≤ |log ε|` puts at least one routed increment slot below the
paper truncation order. -/
theorem one_le_truncOrder_of_abs_log {ε : ℝ}
    (hlog : 1 ≤ |Real.log ε|) : 1 ≤ truncOrder ε :=
  Nat.le_floor (by exact_mod_cast hlog)

/-- **Signed-physical producer of the countable central routing
output.**  The full signed pairing sum — covariances reassembled, key
sum inside the integral — is used as the single term of a countable
central decomposition; its external frequency is routed through `nInc`
equal increments, `1 ≤ nInc ≤ truncOrder ε`.  No key-normed series
appears: the only obligation is the displayed signed scalar bound. -/
theorem countableCentralRoutedMomentReductionOutput_of_signedCentralDecay
    (ρ : SmoothCutoff) (lam : ℝ) {ε : ℝ} (m : ℕ) (α β : Z4)
    {B : ℝ} (hB : 0 ≤ B) {nInc : ℕ}
    (hn : 1 ≤ nInc) (hntrunc : nInc ≤ truncOrder ε)
    (hsigned :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        B * eighthOrderFrequencyDecay
          ((nInc : ℝ)⁻¹ * ‖z4EuclideanFrequency (α + β)‖)) :
    CountableCentralRoutedMomentReductionOutput
      ρ lam ε m α β B := by
  have hnR : (0 : ℝ) < (nInc : ℝ) := by exact_mod_cast hn
  refine
    ⟨{ term := fun a =>
         if a = 0 then
           deterministicMomentPairingSum ρ lam ε m α β
         else 0
       weight := fun a => if a = 0 then B else 0
       incrementCount := fun _ => nInc
       increment := fun _ _ =>
         (nInc : ℝ)⁻¹ • z4EuclideanFrequency (α + β)
       sum_eq := ?_
       summable_term := ?_
       summable_weight := ?_
       weight_nonneg := ?_
       incrementCount_pos := fun _ => hn
       incrementCount_le_trunc := fun _ => hntrunc
       increment_sum := ?_
       term_le_increment_decay := ?_
       tsum_weight_le := ?_ }⟩
  · exact (tsum_ite_eq (0 : ℕ)
      (fun _ => deterministicMomentPairingSum ρ lam ε m α β)).symm
  · exact summable_of_ne_finset_zero (s := {0})
      (fun b hb => if_neg (by simpa using hb))
  · exact summable_of_ne_finset_zero (s := {0})
      (fun b hb => if_neg (by simpa using hb))
  · intro a
    split_ifs
    · exact hB
    · exact le_rfl
  · intro a
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      mul_inv_cancel₀ hnR.ne', one_smul]
  · intro a i
    split_ifs with ha
    · rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hnR)]
      exact hsigned
    · simp
  · exact le_of_eq (tsum_ite_eq (0 : ℕ) (fun _ => B))

/-! ## The remaining signed-physical routed estimate -/

/-- **The precise remaining routed-branch statement.**  The signed
physical pairing sum — key sum and covariances inside one norm —
carries the endpoint loss `ε⁻⁸⟨α⟩⁻⁴⟨β⟩⁻⁴` and one central
eighth-order decay unit at a routed increment scale
`‖freq(α+β)‖/nInc` for some admissible increment count
`nInc ≤ truncOrder ε`.  With `nInc = truncOrder ε` this is the
weakest hypothesis expressible through the proved countable
interface, and it implies the paper's `⟨ε²(α+β)⟩⁻⁸` bracket. -/
def R324SignedCentralDecayBudget
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4)
    (amplitude : ℝ) : Prop :=
  ∃ nInc : ℕ, 1 ≤ nInc ∧ nInc ≤ truncOrder ε ∧
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      (amplitude * r324EndpointLoss ε α β) *
        eighthOrderFrequencyDecay
          ((nInc : ℝ)⁻¹ * ‖z4EuclideanFrequency (α + β)‖)

/-- The uniform branch and the signed central-decay budget give the
exact paper `min` bracket.  No key-normed series occurs in either
hypothesis. -/
theorem
    deterministicMomentPairingSum_paper_bound_of_uniform_and_signedCentralDecay
    {ρ : SmoothCutoff} {lam ε amplitude : ℝ} {m : ℕ} {α β : Z4}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hamp : 0 ≤ amplitude)
    (huniform :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤ amplitude)
    (hsigned :
      R324SignedCentralDecayBudget ρ lam ε m α β amplitude) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      amplitude * min 1 (paperDeterministicMomentDecay ε α β) := by
  obtain ⟨nInc, hn, hntrunc, hbound⟩ := hsigned
  have hroute :=
    countableCentralRoutedMomentReductionOutput_of_signedCentralDecay
      ρ lam m α β
      (mul_nonneg hamp (r324EndpointLoss_nonneg ε α β))
      hn hntrunc hbound
  exact
    deterministicMomentPairingSum_paper_bound_of_uniform_and_countable
      hε hεsmall huniform hroute (le_refl _)

/-- **The paper bound (P-3.5b-det shape) from two signed-physical
scalar inputs, at an `ε`-uniform outer constant.**  Both hypotheses
place the norm outside the complete signed physical integral:

* the middle estimate `R324RefinedInsertedMajorantBound` bounds each
  refined schedule fibre `‖r324RefinedPhysicalIntegral‖` by the
  integrated inserted majorant (gap (b), Prop. 4.1 iterated);
* `R324SignedCentralDecayBudget` is the routed branch in signed form.

Neither hypothesis mentions a key-normed series, so the proved
`ε⁻⁶`-per-slot obstruction of the norm-inside ledger does not apply.
The outer constant is chosen before the cutoff, coupling, scale,
order, and Fourier modes. -/
theorem
    exists_deterministicMoment_paper_bound_of_insertedMajorant_and_signedCentralDecay
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4),
        0 ≤ lam → 0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| → 1 ≤ m →
        R324RefinedInsertedMajorantBound
          ρ lam ε m α β primitiveConstant supportConstant →
        R324SignedCentralDecayBudget ρ lam ε m α β
          (lamEps lam ε ^ 2 * outerConstant *
            ((16 * primitiveConstant) * lam) ^ (2 * m - 2)) →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (16 * primitiveConstant) lam ε m α β := by
  obtain ⟨outerConstant, houter, huniform⟩ :=
    exists_deterministicMoment_uniform_bound_of_refinedIntegratedReduction
      hprimitive hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m α β hlam hε hεsmall hlog hm
    hmajorant hsigned
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hbase : 0 ≤ (16 * primitiveConstant) * lam :=
    mul_nonneg (by positivity) hlam
  have hamp :
      0 ≤ lamEps lam ε ^ 2 * outerConstant *
        ((16 * primitiveConstant) * lam) ^ (2 * m - 2) :=
    mul_nonneg
      (mul_nonneg (sq_nonneg _) houter.le)
      (pow_nonneg hbase _)
  have hu :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        lamEps lam ε ^ 2 * outerConstant *
          ((16 * primitiveConstant) * lam) ^ (2 * m - 2) :=
    huniform ρ lam ε m α β hlam hε hε1 hlog hm
      (momentRefinedIntegratedReductionOutputAt_of_insertedMajorantBound
        hε hε1 hmajorant)
  have hcombined :=
    deterministicMomentPairingSum_paper_bound_of_uniform_and_signedCentralDecay
      hε hεsmall hamp hu hsigned
  simpa only [paperDeterministicMomentRHS] using hcombined

/-- Mode-free variant: the uniform branch is supplied by the interior
inserted-majorant estimate `R324InteriorCoreMajorantBound` — a bound
on `∫‖(interior skeleton) · (signed compatible covariance-fibre sum)‖`
with the fibre summed *before* the norm — and the routed branch by the
signed central-decay budget.  These are the two hypotheses of the
signed-physical route; neither contains a key-normed
series. -/
theorem
    exists_deterministicMoment_paper_bound_of_interiorCore_and_signedCentralDecay
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4),
        0 < m →
        0 ≤ lam → 0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        R324InteriorCoreMajorantBound
          ρ lam ε m primitiveConstant supportConstant →
        R324SignedCentralDecayBudget ρ lam ε m α β
          (lamEps lam ε ^ 2 * outerConstant *
            ((16 * primitiveConstant) * lam) ^ (2 * m - 2)) →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (16 * primitiveConstant) lam ε m α β := by
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_insertedMajorant_and_signedCentralDecay
      hprimitive hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m α β hm hlam hε hεsmall hlog hcore hsigned
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  exact
    h ρ lam ε m α β hlam hε hεsmall hlog (by omega)
      (r324RefinedInsertedMajorantBound_of_interiorCore
        hε hε1 hm α β hcore)
      hsigned

/-! ## Iterated Proposition 4.1 in signed physical form -/

/-- **The signed-physical block ledger.**  Each primitive block of
order `q` is the *signed* physical integral `renormC2q` — the
covariances `η_ε` sit inside `detJintegrand`, and the absolute value
is taken only after the complete signed pairing-fibre sum, exactly as
in Proposition 4.1.  One block costs `(Cλ)^(2q) · ε⁻²/|log ε|`; a
schedule of `k` blocks of orders `n i` costs the product
`(ε⁻²/|log ε|)^k · (Cλ)^(2Σnᵢ)`: `O(1)` per covariance pair,
`ε⁻²/|log ε|` once per block — the (3.24) ledger.  In contrast, the
proved norm-inside key ledger pays `ε⁻⁴` per covariance pair
(`R324TotalMassBudget`), which is why the routed interface must be
fed by this signed form. -/
theorem exists_prod_abs_renormC2q_le_signedBlockLedger
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ Crenorm : ℝ, 0 < Crenorm ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (k : ℕ) (n : Fin k → ℕ),
        0 ≤ lam → 0 < ε → 1 ≤ |Real.log ε| →
        (∀ i, 1 ≤ n i) →
        (∀ i, RenormReductionOutput ρ lam ε (n i)
          primitiveConstant supportConstant) →
        (∏ i, |renormC2q ρ lam ε (n i)|) ≤
          (ε⁻¹ ^ (2 : ℕ) / |Real.log ε|) ^ k *
            (Crenorm * lam) ^ (2 * ∑ i, n i) := by
  obtain ⟨Crenorm, hCrenorm, hblock⟩ :=
    exists_renormC_bound_of_reduction hprimitive hsupport
  refine ⟨Crenorm, hCrenorm, ?_⟩
  intro ρ lam ε k n hlam hε hlog hn hred
  calc
    (∏ i, |renormC2q ρ lam ε (n i)|) ≤
        ∏ i, (ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
          (Crenorm * lam) ^ (2 * n i)) :=
      Finset.prod_le_prod (fun i _ => abs_nonneg _)
        (fun i _ =>
          hblock ρ lam ε (n i) hlam hε hlog (hn i) (hred i))
    _ = (ε⁻¹ ^ (2 : ℕ) / |Real.log ε|) ^ k *
          ∏ i, (Crenorm * lam) ^ (2 * n i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    _ = (ε⁻¹ ^ (2 : ℕ) / |Real.log ε|) ^ k *
          (Crenorm * lam) ^ (∑ i, 2 * n i) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ = (ε⁻¹ ^ (2 : ℕ) / |Real.log ε|) ^ k *
          (Crenorm * lam) ^ (2 * ∑ i, n i) := by
      rw [← Finset.mul_sum]

end

end Anderson4D
