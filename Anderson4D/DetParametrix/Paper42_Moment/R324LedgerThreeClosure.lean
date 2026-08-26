import Anderson4D.DetParametrix.Paper42_Moment.R324LedgerThreeCross

/-!
# Closure of the uniform branch over the two residual case ledgers

The composition theorem of the interface file and the pure-cross
reduction of the cross file leave exactly two analytic obligations:

* `R324LedgerThreeCrossLedger`, reduced here further to a phase-free
  integral bound for the nonnegative pure-cross density
  (`r324LedgerThreeCrossLedger_of_integral_bound`) — the two-chain
  multi-window estimate;
* `R324LedgerThreeMixedLedger` — the fibres retaining a within-half
  pair, to be peeled by the parity/difference gain.

Given both, the **complete uniform branch** follows: one per-cutoff
primitive constant discharges `MomentRefinedIntegratedReductionOutputAt`
at every order `m ≥ 1`, every coupling, every admissible scale and both
external modes, at support constant one.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The cross ledger from the phase-free integral bound -/

/-- The summed pure-cross density is integrable: it is almost
everywhere the norm of the integrable summed flat fibre. -/
theorem r324LedgerThree_integrable_crossDensity
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ}
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (hfib : R324LedgerThreeCrossFibre m s r) :
    Integrable
      (r324LedgerThreeCrossDensity ρ ε m
        (momentRefinedContractionFiber m s r))
      (r324PhysicalMeasure m) := by
  have hint :
      Integrable
        (fun p => ∑ e ∈ momentRefinedContractionFiber m s r,
          r324Flatten
            (deterministicMomentIntegrand ρ ε m 0 0
              e.1 e.2.1 e.2.2) p)
        (r324PhysicalMeasure m) :=
    integrable_finsetSum _
      (fun e _ => r324MomentIntegrable_all ρ hε hε1 0 0 e)
  exact hint.norm.congr
    (Filter.Eventually.of_forall fun p =>
      r324LedgerThree_norm_sum_flatten_eq ρ ε 0 0 hfib p)

/-- **The cross-case ledger follows from a phase-free integral
bound**: it suffices to bound the physical integral of the nonnegative
pure-cross density — two plain Green chains against the permutation
covariance sum — with no reference to the external modes. -/
theorem r324LedgerThreeCrossLedger_of_integral_bound
    (ρ : SmoothCutoff) (K : ℝ)
    (h : ∀ {ε : ℝ} (m : ℕ),
      0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 3 ≤ m →
        ∀ F : Finset (MomentContraction m),
          (∀ e ∈ F, R324LedgerThreeAllCrossEntity e) →
            (∫ p, r324LedgerThreeCrossDensity ρ ε m F p
                ∂(r324PhysicalMeasure m)) ≤
              K ^ m * |Real.log ε| ^ (m - 1)) :
    R324LedgerThreeCrossLedger ρ K := by
  intro ε m α β hε hε1 hlog hm3 s _hs r _hr hfib
  exact
    (r324LedgerThree_norm_termSum_le_integral_crossDensity
      ρ hε hε1 α β hfib).trans
      (h m hε hε1 hlog hm3 _ hfib)

/-! ## The multi-window integrand -/

/-- **The phase-free two-chain multi-window integrand**: two plain
Green chains against the product of the `m` covariance row sums.  This
is the fibre-independent quantity that funds the entire cross case. -/
def r324LedgerThreeWindowIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (p : R324PhysicalPoint m) : ℝ :=
  r324LedgerThreeLeftChain m p * r324LedgerThreeRightChain m p *
    r324LedgerThreeCrossMajorant ρ ε m p.2.2.2.2

/-- The row-sum majorant is jointly measurable on the physical
space. -/
theorem r324LedgerThree_measurable_crossMajorant
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) :
    Measurable (fun p : R324PhysicalPoint m =>
      r324LedgerThreeCrossMajorant ρ ε m p.2.2.2.2) := by
  unfold r324LedgerThreeCrossMajorant
  apply Finset.measurable_prod
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact (ρ.measurable_etaEpsT4 ε).comp
    (((measurable_pi_apply _).comp
        measurable_snd.snd.snd.snd).sub
      ((measurable_pi_apply _).comp
        measurable_snd.snd.snd.snd))

/-- The row-sum majorant is uniformly bounded at each fixed scale by
the `O(ε⁻⁴)` covariance height. -/
theorem exists_r324LedgerThreeCrossMajorant_bound
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) :
    ∃ B : ℝ, ∀ v : Fin (2 * m) → T4,
      r324LedgerThreeCrossMajorant ρ ε m v ≤ B := by
  obtain ⟨Cη, hCηpos, hCη⟩ := ρ.exists_pos_etaEpsT4_uniform_bound
  refine
    ⟨((Fintype.card
        ↥(PartialPairing.id : PartialPairing (Fin m)).singles : ℝ) *
          (ε⁻¹ ^ (dim : ℕ) * Cη)) ^
        Fintype.card
          ↥(PartialPairing.id : PartialPairing (Fin m)).singles,
      fun v => ?_⟩
  unfold r324LedgerThreeCrossMajorant
  have hrow : ∀ i : ↥(PartialPairing.id :
      PartialPairing (Fin m)).singles,
      (∑ j : ↥(PartialPairing.id :
          PartialPairing (Fin m)).singles,
        ρ.etaEpsT4 ε
          (v (leftMomentIndex i.val) -
            v (rightMomentIndex j.val))) ≤
        (Fintype.card
          ↥(PartialPairing.id :
            PartialPairing (Fin m)).singles : ℝ) *
          (ε⁻¹ ^ (dim : ℕ) * Cη) := by
    intro i
    calc
      (∑ j : ↥(PartialPairing.id :
          PartialPairing (Fin m)).singles,
        ρ.etaEpsT4 ε
          (v (leftMomentIndex i.val) -
            v (rightMomentIndex j.val))) ≤
          ∑ _j : ↥(PartialPairing.id :
            PartialPairing (Fin m)).singles,
            ε⁻¹ ^ (dim : ℕ) * Cη :=
        Finset.sum_le_sum fun j _ => hCη hε hε1 _
      _ = (Fintype.card
            ↥(PartialPairing.id :
              PartialPairing (Fin m)).singles : ℝ) *
            (ε⁻¹ ^ (dim : ℕ) * Cη) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    (∏ i : ↥(PartialPairing.id :
        PartialPairing (Fin m)).singles,
      ∑ j : ↥(PartialPairing.id :
          PartialPairing (Fin m)).singles,
        ρ.etaEpsT4 ε
          (v (leftMomentIndex i.val) -
            v (rightMomentIndex j.val))) ≤
        ∏ _i : ↥(PartialPairing.id :
            PartialPairing (Fin m)).singles,
          (Fintype.card
            ↥(PartialPairing.id :
              PartialPairing (Fin m)).singles : ℝ) *
            (ε⁻¹ ^ (dim : ℕ) * Cη) :=
      Finset.prod_le_prod
        (fun i _ => Finset.sum_nonneg fun j _ =>
          ρ.etaEpsT4_nonneg ε _)
        (fun i _ => hrow i)
    _ = _ := by
      rw [Finset.prod_const, Finset.card_univ]

/-- The bare two-chain product is integrable: the proved doubled
profile integrability at the identity pairings. -/
theorem r324LedgerThree_integrable_chainProduct
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) :
    Integrable
      (fun p : R324PhysicalPoint m =>
        r324LedgerThreeLeftChain m p *
          r324LedgerThreeRightChain m p)
      (r324PhysicalMeasure m) := by
  have h :=
    integrable_r324Flatten_detIntegrand_product ρ hε hε1
      (PartialPairing.id : PartialPairing (Fin m))
      PartialPairing.id
  refine h.norm.congr ?_
  filter_upwards with p
  unfold r324Flatten
  dsimp only
  rw [r324LedgerThree_detIntegrand_id,
    r324LedgerThree_detIntegrand_id, Complex.norm_real,
    Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg
    (r324LedgerThree_chain_nonneg m _)
    (r324LedgerThree_chain_nonneg m _))]
  rfl

/-- **The multi-window integrand is integrable** at every fixed
admissible scale: the chains carry the integrable mass and the row-sum
majorant is a bounded measurable factor. -/
theorem r324LedgerThree_integrable_windowIntegrand
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) :
    Integrable (r324LedgerThreeWindowIntegrand ρ ε m)
      (r324PhysicalMeasure m) := by
  obtain ⟨B, hB⟩ :=
    exists_r324LedgerThreeCrossMajorant_bound ρ hε hε1 m
  have h :=
    (r324LedgerThree_integrable_chainProduct ρ hε hε1 m).bdd_mul
      (c := max B 0)
      (r324LedgerThree_measurable_crossMajorant
        ρ ε m).aestronglyMeasurable
      ?_
  · refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    unfold r324LedgerThreeWindowIntegrand
    ring
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg
      (r324LedgerThreeCrossMajorant_nonneg ρ ε m _)]
    exact le_max_of_le_left (hB _)

/-- **The pure-cross fibre integral is dominated by the multi-window
integral**: the pointwise permanent bound integrates against the
integrable majorant. -/
theorem r324LedgerThree_integral_crossDensity_le_windowIntegral
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} {F : Finset (MomentContraction m)}
    (hF : ∀ e ∈ F, R324LedgerThreeAllCrossEntity e) :
    (∫ p, r324LedgerThreeCrossDensity ρ ε m F p
        ∂(r324PhysicalMeasure m)) ≤
      ∫ p, r324LedgerThreeWindowIntegrand ρ ε m p
        ∂(r324PhysicalMeasure m) := by
  refine integral_mono_of_nonneg ?_
    (r324LedgerThree_integrable_windowIntegrand ρ hε hε1 m) ?_
  · filter_upwards with p
    exact r324LedgerThreeCrossDensity_nonneg ρ ε m F p
  · filter_upwards with p
    exact r324LedgerThreeCrossDensity_le_majorant ρ ε hF p

/-- **Cross-case ledger from the multi-window integral bound**: the
sharpest residual form of the cross case.  The obligation no longer
mentions fibres, signatures, or external modes — it is one scalar
integral inequality for the two plain chains against the `m`
covariance row sums. -/
theorem r324LedgerThreeCrossLedger_of_windowIntegral_bound
    (ρ : SmoothCutoff) (K : ℝ)
    (h : ∀ {ε : ℝ} (m : ℕ),
      0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 3 ≤ m →
        (∫ p, r324LedgerThreeWindowIntegrand ρ ε m p
            ∂(r324PhysicalMeasure m)) ≤
          K ^ m * |Real.log ε| ^ (m - 1)) :
    R324LedgerThreeCrossLedger ρ K := by
  apply r324LedgerThreeCrossLedger_of_integral_bound
  intro ε m hε hε1 hlog hm3 F hF
  exact
    (r324LedgerThree_integral_crossDensity_le_windowIntegral
      ρ hε hε1 hF).trans (h m hε hε1 hlog hm3)

/-! ## The final uniform-branch statement -/

/-- **The complete uniform branch over the residual case ledgers.**
Given the two residual case ledgers — the pure-cross multi-window
bound and the mixed parity-gain bound, each with a per-cutoff
constant — every order `m ≥ 1` of the uniform branch closes at one
primitive constant and support constant one. -/
theorem exists_momentRefinedIntegratedReductionOutputAt_final
    (ρ : SmoothCutoff)
    (hcross : ∃ K : ℝ, 0 ≤ K ∧ R324LedgerThreeCrossLedger ρ K)
    (hmixed : ∃ K : ℝ, 0 ≤ K ∧ R324LedgerThreeMixedLedger ρ K) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (lam : ℝ) {ε : ℝ} (m : ℕ) (α β : Z4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 1 ≤ m →
          MomentRefinedIntegratedReductionOutputAt
            ρ lam ε m α β C₀ 1 := by
  obtain ⟨K₁, hK₁, hc⟩ := hcross
  obtain ⟨K₂, hK₂, hm⟩ := hmixed
  exact
    exists_momentRefinedIntegratedReductionOutputAt_of_ledgerFromThree
      ρ
      ⟨max K₁ K₂, le_max_of_le_left hK₁,
        r324LedgerThree_generalPeelLedgerFromThree hK₁ hK₂ hc hm⟩

/-- **Sharpest conditional form.**  The complete uniform branch from
the two terminal residual obligations: the fibre-free multi-window
integral bound and the mixed-fibre ledger. -/
theorem exists_momentRefinedIntegratedReductionOutputAt_of_window_and_mixed
    (ρ : SmoothCutoff)
    (hwin : ∃ K : ℝ, 0 ≤ K ∧
      ∀ {ε : ℝ} (m : ℕ),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 3 ≤ m →
          (∫ p, r324LedgerThreeWindowIntegrand ρ ε m p
              ∂(r324PhysicalMeasure m)) ≤
            K ^ m * |Real.log ε| ^ (m - 1))
    (hmixed : ∃ K : ℝ, 0 ≤ K ∧ R324LedgerThreeMixedLedger ρ K) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (lam : ℝ) {ε : ℝ} (m : ℕ) (α β : Z4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 1 ≤ m →
          MomentRefinedIntegratedReductionOutputAt
            ρ lam ε m α β C₀ 1 := by
  obtain ⟨K, hK, hwinK⟩ := hwin
  exact
    exists_momentRefinedIntegratedReductionOutputAt_final ρ
      ⟨K, hK,
        r324LedgerThreeCrossLedger_of_windowIntegral_bound
          ρ K hwinK⟩
      hmixed

end

end Anderson4D
