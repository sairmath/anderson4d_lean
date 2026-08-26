import Anderson4D.DetParametrix.Paper42_Moment.R324UncappedCrossObstruction

/-!
# Necessity of the order cap in the R-324 re-base

The following uncapped bridge
`momentRefinedIntegratedReductionOutputAt_of_generalPeelFibreLogBound`
consumes the per-fibre ledger `R324GeneralPeelFibreLogBound` at *every*
order `m ≥ 1` with no cap.  This file proves that the uncapped residual
ledger `R324GeneralPeelLedgerFromThree` cannot hold — the
factorial fibre floor refutes the cancellation-carrying term-sum ledger
itself, not merely its norm-inside density majorization:

* the bridge's summed object `momentRefinedDeterministicTermSum` is the
  **unnormalized** sum of `deterministicMomentContractionTerm` over a
  residual-refined fibre; no `∏ mₗ!`-type paper normalization discounts
  the fibre count anywhere in that chain;
* at trivial external modes `α = β = 0` the integrand of every entity in
  the **trivial-signature fibre** (both pairings extract nothing, so no
  signed `diffFactor` appears) is the coercion of a pointwise
  *nonnegative* real product — there is no cancellation to hide behind:
  every term is real and nonnegative
  (`r324CappedRebase_term_trivialSig_nonneg`);
* the full `m!` bijection family lies inside that single signature
  fibre, which splits into at most `4^{2m}` refined fibres, so the
  ledger's budget `K^m·L^{m-1}` per refined fibre caps the whole fibre
  sum by `(16K)^m` at the admissible scale `ε = e⁻¹` (`L = 1`), while
  the proved floor `r324PermCross_crossDensity_factorial_floor`
  forces at least `C₀·m!·c^m` — contradiction for large `m`
  (`r324CappedRebase_generalPeelLedgerFromThree_no_constant`).

Consequently the uncapped hypotheses
`R324LedgerThreeCrossLedger` and `R324LedgerThreeMixedLedger` are
incompatible (`r324CappedRebase_crossMixed_incompatible`).  The valid
interface therefore caps the order against `truncOrder ε`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The trivial signature and its fibre -/

/-- The within-half endpoint signature of the identity pairings is the
empty pair: nothing is extracted, so there are no interval endpoints. -/
theorem r324CappedRebase_signature_id (m : ℕ) :
    momentWithinHalfEndpointSignature
        (PartialPairing.id : PartialPairing (Fin m))
        (PartialPairing.id : PartialPairing (Fin m)) =
      (∅, ∅) := by
  unfold momentWithinHalfEndpointSignature leftEndpoints rightEndpoints
  rw [r324LedgerThree_extract_id]
  simp

/-- Any entity realizing the trivial signature has extraction-free
pairings in both halves: an extracted interval would contribute a left
endpoint to the (empty) signature. -/
theorem r324CappedRebase_extract_nil_of_trivialSig {m : ℕ}
    {e : MomentContraction m}
    (h : momentContractionSignature e = (∅, ∅)) :
    extract e.1 = [] ∧ extract e.2.1 = [] := by
  unfold momentContractionSignature
    momentWithinHalfEndpointSignature at h
  have h1 := congrArg Prod.fst h
  dsimp only at h1
  rw [Finset.union_eq_empty] at h1
  obtain ⟨hp, hq⟩ := h1
  rw [Finset.image_eq_empty] at hp hq
  unfold leftEndpoints at hp hq
  rw [List.toFinset_eq_empty_iff, List.map_eq_nil_iff] at hp hq
  exact ⟨hp, hq⟩

/-! ## No cancellation at trivial external modes -/

/-- With nothing extracted there is no signed `diffFactor`: the
deterministic profile is a plain product of Green factors and
covariance factors, hence nonnegative. -/
theorem r324CappedRebase_detIntegrand_nonneg_of_extract_nil
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} {κ : PartialPairing (Fin m)}
    (hnil : extract κ = []) (xt : Fin (m + 2) → T4) :
    0 ≤ detIntegrand ρ ε m κ xt := by
  unfold detIntegrand
  rw [hnil]
  refine mul_nonneg (mul_nonneg
    (Finset.prod_nonneg fun e _ => ?_) (by simp))
    (Finset.prod_nonneg fun i _ => ρ.etaEpsT4_nonneg ε _)
  split
  · exact zero_le_one
  · exact greenFn_nonneg _

/-- The phase-free real profile of one contraction entity: the two
deterministic within-half profiles against the cross covariance. -/
def r324CappedRebaseProfile (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (e : MomentContraction m) (p : R324PhysicalPoint m) : ℝ :=
  detIntegrand ρ ε m e.1
      (assemble p.1 p.2.1
        fun i => p.2.2.2.2 (leftMomentIndex i)) *
    detIntegrand ρ ε m e.2.1
      (assemble p.2.2.1 p.2.2.2.1
        fun i => p.2.2.2.2 (rightMomentIndex i)) *
    momentCrossCovarianceProduct ρ ε m
      e.1 e.2.1 e.2.2 p.2.2.2.2

/-- At `α = β = 0` every contraction integrand is the coercion of the
real profile: all four external characters are `1`. -/
theorem r324CappedRebase_flatten_trivialModes
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (e : MomentContraction m)
    (p : R324PhysicalPoint m) :
    r324Flatten
        (deterministicMomentIntegrand ρ ε m 0 0
          e.1 e.2.1 e.2.2) p =
      ((r324CappedRebaseProfile ρ ε e p : ℝ) : ℂ) := by
  unfold r324Flatten deterministicMomentIntegrand
    r324CappedRebaseProfile
  rw [neg_zero]
  simp [charT4_zero]

/-- **Trivial-signature terms are real and nonnegative at trivial
external modes**: the frozen contraction term of any entity in the
trivial-signature fibre equals the integral of a pointwise nonnegative
real product — no cancellation is available. -/
theorem r324CappedRebase_term_trivialSig_nonneg
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} {e : MomentContraction m}
    (h : momentContractionSignature e = (∅, ∅)) :
    deterministicMomentContractionTerm ρ ε m 0 0 e =
      ((∫ p, r324CappedRebaseProfile ρ ε e p
          ∂(r324PhysicalMeasure m) : ℝ) : ℂ) ∧
      (0 : ℝ) ≤
        ∫ p, r324CappedRebaseProfile ρ ε e p
          ∂(r324PhysicalMeasure m) := by
  obtain ⟨hp, hq⟩ := r324CappedRebase_extract_nil_of_trivialSig h
  constructor
  · rw [← integral_r324Flatten_deterministicMomentIntegrand
      ρ ε m 0 0 e (r324MomentIntegrable_all ρ hε hε1 0 0 e),
      ← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p =>
      r324CappedRebase_flatten_trivialModes ρ ε e p)
  · refine integral_nonneg fun p => ?_
    unfold r324CappedRebaseProfile
    refine mul_nonneg (mul_nonneg
      (r324CappedRebase_detIntegrand_nonneg_of_extract_nil
        ρ ε hp _)
      (r324CappedRebase_detIntegrand_nonneg_of_extract_nil
        ρ ε hq _)) ?_
    exact Finset.prod_nonneg fun i _ => ρ.etaEpsT4_nonneg ε _

/-! ## The trivial-signature fibre sum carries the factorial floor -/

/-- **The trivial-signature fibre sum is real and dominates every
pure-cross density integral at trivial modes.**  No cancellation: all
terms of the fibre are nonnegative reals, and the all-cross subfamily
contributes exactly its summed density. -/
theorem r324CappedRebase_fibreSum_ge_crossDensity
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {m : ℕ}
    {F : Finset (MomentContraction m)}
    (hFcross : ∀ e ∈ F, R324LedgerThreeAllCrossEntity e) :
    ∃ T : ℝ,
      (∑ e ∈ momentContractionFiber m
          (momentWithinHalfEndpointSignature
            (PartialPairing.id : PartialPairing (Fin m))
            PartialPairing.id),
          deterministicMomentContractionTerm ρ ε m 0 0 e) =
        (T : ℂ) ∧
      (∫ p, r324LedgerThreeCrossDensity ρ ε m F p
          ∂(r324PhysicalMeasure m)) ≤ T := by
  classical
  set s₀ := momentWithinHalfEndpointSignature
    (PartialPairing.id : PartialPairing (Fin m))
    PartialPairing.id with hs₀
  have hsig : ∀ e ∈ momentContractionFiber m s₀,
      momentContractionSignature e = (∅, ∅) := fun e he =>
    (mem_momentContractionFiber.mp he).trans
      (r324CappedRebase_signature_id m)
  have hterm := fun e (he : e ∈ momentContractionFiber m s₀) =>
    r324CappedRebase_term_trivialSig_nonneg ρ hε hε1 (hsig e he)
  refine ⟨∑ e ∈ momentContractionFiber m s₀,
    ∫ p, r324CappedRebaseProfile ρ ε e p
      ∂(r324PhysicalMeasure m), ?_, ?_⟩
  · push_cast
    exact Finset.sum_congr rfl fun e he => (hterm e he).1
  · have hFsub : F ⊆ momentContractionFiber m s₀ := by
      intro e he
      obtain ⟨π, rfl⟩ := (hFcross e he).eq_mk
      exact mem_momentContractionFiber.mpr rfl
    have hprof : ∀ e ∈ F, ∀ p : R324PhysicalPoint m,
        r324CappedRebaseProfile ρ ε e p =
          r324LedgerThreeLeftChain m p *
            r324LedgerThreeRightChain m p *
            momentCrossCovarianceProduct ρ ε m
              e.1 e.2.1 e.2.2 p.2.2.2.2 := by
      intro e he p
      obtain ⟨π, rfl⟩ := (hFcross e he).eq_mk
      unfold r324CappedRebaseProfile r324LedgerThreeLeftChain
        r324LedgerThreeRightChain
      rw [r324LedgerThree_detIntegrand_id,
        r324LedgerThree_detIntegrand_id]
    have hint : ∀ e ∈ F,
        Integrable (fun p => r324CappedRebaseProfile ρ ε e p)
          (r324PhysicalMeasure m) := by
      intro e he
      have h0 := hFcross e he
      obtain ⟨π, rfl⟩ := h0.eq_mk
      exact (r324PermCross_integrable_summand ρ hε hε1 π).congr
        (Filter.Eventually.of_forall fun p =>
          (hprof _ he p).symm)
    calc (∫ p, r324LedgerThreeCrossDensity ρ ε m F p
          ∂(r324PhysicalMeasure m))
        = ∑ e ∈ F, ∫ p, r324CappedRebaseProfile ρ ε e p
            ∂(r324PhysicalMeasure m) := by
          rw [← integral_finsetSum F hint]
          refine integral_congr_ae
            (Filter.Eventually.of_forall fun p => ?_)
          unfold r324LedgerThreeCrossDensity
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun e he =>
            (hprof e he p).symm
      _ ≤ ∑ e ∈ momentContractionFiber m s₀,
            ∫ p, r324CappedRebaseProfile ρ ε e p
              ∂(r324PhysicalMeasure m) :=
          Finset.sum_le_sum_of_subset_of_nonneg hFsub
            fun e he _ => (hterm e he).2

/-! ## Nonexistence of an uncapped constant -/

/-- **The uncapped per-fibre ledger has no constant.**  At `ε = e⁻¹`
the trivial-signature fibre sum at trivial external modes is a sum of
nonnegative reals containing the full `m!` bijection family; the
ledger caps it by `4^{2m}·K^m·L^{m-1} = (16K)^m`, which the proved
factorial floor defeats. -/
theorem r324CappedRebase_generalPeelLedgerFromThree_no_constant
    (ρ : SmoothCutoff) :
    ¬ ∃ K : ℝ, 0 ≤ K ∧ R324GeneralPeelLedgerFromThree ρ K := by
  rintro ⟨K, hK, hled⟩
  obtain ⟨c, C₀, hc, hC₀, hfloor⟩ :=
    r324PermCross_crossDensity_factorial_floor ρ
  obtain ⟨m, hm3, hbeats⟩ :=
    r324PermCross_exists_factorial_beats_pow hc hC₀ (16 * K) 3
  set ε : ℝ := Real.exp (-1) with hεdef
  have hε : 0 < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := by
    rw [hεdef, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num)
  have hlog : |Real.log ε| = 1 := by
    rw [hεdef, Real.log_exp]
    norm_num
  have hlog1 : 1 ≤ |Real.log ε| := le_of_eq hlog.symm
  obtain ⟨F, hFcross, hFge⟩ := hfloor m hε hε1 (by omega)
  obtain ⟨T, hTeq, hTge⟩ :=
    r324CappedRebase_fibreSum_ge_crossDensity ρ hε hε1 hFcross
  set s₀ := momentWithinHalfEndpointSignature
    (PartialPairing.id : PartialPairing (Fin m))
    PartialPairing.id with hs₀
  have hs₀mem : s₀ ∈ momentContractionSignatures m :=
    Finset.mem_image.mpr
      ⟨⟨PartialPairing.id, PartialPairing.id, Equiv.refl _⟩,
        Finset.mem_univ _, rfl⟩
  have hup : T ≤ 16 ^ m * K ^ m := by
    have hnorm : ‖(T : ℂ)‖ ≤ 16 ^ m * K ^ m := by
      rw [← hTeq,
        ← sum_momentRefinedDeterministicTermSum ρ ε m 0 0 s₀]
      calc ‖∑ r ∈ momentResidualChainSignaturesAt m s₀,
            momentRefinedDeterministicTermSum ρ ε m 0 0 s₀ r‖
          ≤ ∑ r ∈ momentResidualChainSignaturesAt m s₀,
              ‖momentRefinedDeterministicTermSum ρ ε m 0 0 s₀ r‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _r ∈ momentResidualChainSignaturesAt m s₀,
              K ^ m := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hb := hled m 0 0 hε hε1 hlog1 hm3 s₀ hs₀mem r hr
            rwa [hlog, one_pow, mul_one] at hb
        _ = ((momentResidualChainSignaturesAt m s₀).card : ℝ) *
              K ^ m := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 16 ^ m * K ^ m := by
            refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hK m)
            calc ((momentResidualChainSignaturesAt m s₀).card : ℝ)
                ≤ (4 : ℝ) ^ (2 * m) := by
                  exact_mod_cast
                    card_momentResidualChainSignaturesAt_le m s₀
              _ = 16 ^ m := by
                  rw [pow_mul]
                  norm_num
    calc T ≤ |T| := le_abs_self T
      _ = ‖(T : ℂ)‖ := (Complex.norm_real T).symm
      _ ≤ 16 ^ m * K ^ m := hnorm
  have hbeats' : (16 : ℝ) ^ m * K ^ m <
      C₀ * ((m.factorial : ℝ) * c ^ m) := by
    rwa [mul_pow] at hbeats
  exact absurd ((hFge.trans hTge).trans hup)
    (not_le.mpr hbeats')

/-- The uncapped cross and mixed ledgers cannot both hold: their
composition would produce the unavailable uncapped peel ledger. -/
theorem r324CappedRebase_crossMixed_incompatible (ρ : SmoothCutoff) :
    ¬ ((∃ K : ℝ, 0 ≤ K ∧ R324LedgerThreeCrossLedger ρ K) ∧
        (∃ K : ℝ, 0 ≤ K ∧ R324LedgerThreeMixedLedger ρ K)) := by
  rintro ⟨⟨K₁, hK₁, hcross⟩, ⟨K₂, hK₂, hmixed⟩⟩
  exact r324CappedRebase_generalPeelLedgerFromThree_no_constant ρ
    ⟨max K₁ K₂, le_trans hK₁ (le_max_left _ _),
      r324LedgerThree_generalPeelLedgerFromThree hK₁ hK₂
        hcross hmixed⟩

end

end Anderson4D
