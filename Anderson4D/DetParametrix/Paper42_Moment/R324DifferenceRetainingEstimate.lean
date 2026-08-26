import Anderson4D.DetParametrix.Paper42_Moment.R324DifferenceRetainingCore
import Anderson4D.DetParametrix.Paper42_Moment.R324ConcreteRoutingClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324FinalAssembly

/-!
# Difference-retaining order-two middle estimate

`R324InteriorTransport` establishes that the raw interior-core budget is
unavailable at `m = 2`: the endpoint-first split sup-normalizes the
terminal chain edges and discards the renormalizing difference factors,
leaving the divergent raw block mass `(∫ G η_ε)² ≳ ε⁻⁴`.  This file
retains those factors at order two for the corresponding schedule:

* `r324RefinedPhysicalIntegral_twoBlock_eq` — the two-block refined
  physical integral factors *exactly* into its two independent halves,
  each of which still carries its difference factor
  (`detIntegrand` keeps `diffFactor`; nothing is sup-normalized);
* `exists_norm_r324TwoBlockHalfIntegral_le` — each half is bounded by
  a constant `Q` uniform in `ρ`, `ε`, and both external frequencies:
  the difference factor is integrated jointly with the block
  (`integral_pi_twoBlock_u`), parity kills the first-order phase term,
  and the quadratic cosine defect `(1/2)|β|² ∫|z̃|² G η_ε` is exactly
  compensated by the boundary coefficient `(1+|β|²)⁻¹`;
* `exists_r324TwoBlock_insertedMajorantBound` — the middle estimate for
  that schedule: with the difference retained, the
  weighted two-block integral obeys the paper-scale inserted-majorant
  bound `|λ_ε|⁴ ‖⋯‖ ≤ ∫ primitiveInsertedMajorant`, with an `ε`- and
  mode-uniform primitive constant.  (Ledger: `|λ_ε|⁴ Q² = λ⁴ Q²/log²ε`
  against the majorant's `(C₀λ)⁴/|log ε|`; one full power of `|log ε|`
  to spare, so no `ε`-power and no log-power is borrowed.)
* `r324RefinedInsertedMajorantBound_two_of_complement` — the composed
  order-two middle-estimate interface
  `R324RefinedInsertedMajorantBound` (and hence the uniform branch
  `MomentRefinedIntegratedReductionOutputAt` of the final deterministic
  closure) is recovered once the remaining, difference-free order-two
  fibres (the cross-pairing schedules, which have *no* within-half
  extraction and hence no interior divergence mechanism) are bounded.

The two-block schedule is the distinguished order-two obstruction; the
cross-pairing complement hypothesis concerns
schedules whose within-half pairings are trivial, i.e. paper §4.2
Step 3 cross-cut estimates rather than the Step 2 extraction.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## The cross covariance of the two-block contraction is empty -/

theorem momentCrossCovarianceProduct_twoBlock
    (ρ : SmoothCutoff) (ε : ℝ) (v : Fin (2 * 2) → T4) :
    momentCrossCovarianceProduct ρ ε 2
      pairingFinTwo pairingFinTwo (Equiv.refl _) v = 1 := by
  unfold momentCrossCovarianceProduct
  rw [Finset.univ_eq_empty, Finset.prod_empty]

/-! ## Exact two-half factorization of the two-block physical integral -/

/-- **The two-block refined physical integral factors exactly.**  Both
factors are complete halves with their renormalizing difference factors
still in place: the identity contains no interior/endpoint split and
no sup-normalization. -/
theorem r324RefinedPhysicalIntegral_twoBlock_eq
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (α β : Z4) :
    r324RefinedPhysicalIntegral ρ ε 2 α β twoBlockScheduleIndex =
      r324TwoBlockHalfIntegral ρ ε α β *
        r324TwoBlockHalfIntegral ρ ε (-α) (-β) := by
  have hsum :=
    r324RefinedPhysicalIntegral_eq_sum_contractionTerms
      ρ hε hε1 α β twoBlockScheduleIndex
  have hfiber :
      momentRefinedContractionFiber 2
          twoBlockScheduleIndex.1.1 twoBlockScheduleIndex.2.1 =
        {twoBlockContraction} :=
    momentRefinedContractionFiber_twoBlock
  rw [hsum, hfiber, Finset.sum_singleton]
  have hflat :=
    r324MomentIntegrable_all ρ hε hε1 α β twoBlockContraction
  have hfive :=
    r324_integral_product_eq_five
      (deterministicMomentIntegrand ρ ε 2 α β
        pairingFinTwo pairingFinTwo (Equiv.refl _))
      hflat
  have hterm :
      deterministicMomentContractionTerm ρ ε 2 α β
          twoBlockContraction =
        ∫ p, r324Flatten
          (deterministicMomentIntegrand ρ ε 2 α β
            pairingFinTwo pairingFinTwo (Equiv.refl _)) p
          ∂(r324PhysicalMeasure 2) :=
    hfive.symm
  rw [hterm]
  set f₁ : T4 × (T4 × (Fin 2 → T4)) → ℂ :=
    fun q =>
      (charT4 α q.1 * charT4 β q.2.1) *
        ((detIntegrand ρ ε 2 pairingFinTwo
          (assemble q.1 q.2.1 q.2.2) : ℝ) : ℂ)
    with hf₁def
  set f₂ : T4 × (T4 × (Fin 2 → T4)) → ℂ :=
    fun q =>
      (charT4 (-α) q.1 * charT4 (-β) q.2.1) *
        ((detIntegrand ρ ε 2 pairingFinTwo
          (assemble q.1 q.2.1 q.2.2) : ℝ) : ℂ)
    with hf₂def
  have hpoint :
      ∀ p : R324PhysicalPoint 2,
        r324Flatten
          (deterministicMomentIntegrand ρ ε 2 α β
            pairingFinTwo pairingFinTwo (Equiv.refl _)) p =
        (fun q :
            (T4 × (T4 × (Fin 2 → T4))) ×
              (T4 × (T4 × (Fin 2 → T4))) =>
          f₁ q.1 * f₂ q.2)
          (r324PhysicalSplitMeasurableEquiv 2 p) := by
    intro p
    rw [r324PhysicalSplitMeasurableEquiv_apply, hf₁def, hf₂def]
    unfold r324Flatten deterministicMomentIntegrand
    rw [momentCrossCovarianceProduct_twoBlock]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    (measurePreserving_r324PhysicalSplitMeasurableEquiv 2).integral_comp'
      (fun q :
          (T4 × (T4 × (Fin 2 → T4))) ×
            (T4 × (T4 × (Fin 2 → T4))) =>
        f₁ q.1 * f₂ q.2),
    integral_prod_mul f₁ f₂]
  rfl

/-! ## Uniform two-block half bound -/

/-- **Mode- and scale-uniform half bound.**  The constant is uniform in
the cutoff, the scale, and both external frequencies: the boundary
coefficient `(1+|b|²)⁻¹` absorbs the quadratic cosine defect
`(1/2)|b|²` exactly, leaving the `ε`-uniform quadratic block mass. -/
theorem exists_norm_r324TwoBlockHalfIntegral_le :
    ∃ Q : ℝ, 0 < Q ∧
      ∀ (ρ : SmoothCutoff) {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ a b : Z4,
          ‖r324TwoBlockHalfIntegral ρ ε a b‖ ≤ Q := by
  obtain ⟨K, hK, hKbound⟩ :=
    exists_integral_torusDistSq_mul_greenFn_mul_etaEpsT4_le
  refine ⟨(2 * Real.pi) ^ (dim : ℕ) * (K / 2), by positivity, ?_⟩
  intro ρ ε hε hε1 a b
  set s : ℝ := paperModeNormSq b with hsdef
  have hs : 0 ≤ s := paperModeNormSq_nonneg b
  have hspos : 0 < 1 + s := by linarith
  set K₂ : ℝ :=
    ∫ z, torusDistSq z * (greenFn z * ρ.etaEpsT4 ε z)
      ∂paperMeasure with hK₂def
  have hK₂nonneg : 0 ≤ K₂ := by
    rw [hK₂def]
    apply integral_nonneg
    intro z
    exact mul_nonneg (torusDistSq_nonneg z)
      (mul_nonneg (greenFn_nonneg z) (ρ.etaEpsT4_nonneg ε z))
  have hK₂le : K₂ ≤ K := hKbound ρ hε hε1
  refine le_trans (norm_r324TwoBlockHalfIntegral_le ρ hε hε1 a b) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hM := norm_r324BlockFrequencyIntegral_le ρ hε hε1 b
  rw [← hsdef, ← hK₂def] at hM
  calc
    (1 + s)⁻¹ * ‖r324BlockFrequencyIntegral ρ ε b‖ ≤
        (1 + s)⁻¹ * ((1 / 2 : ℝ) * s * K₂) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    _ = ((1 + s)⁻¹ * s) * (K₂ / 2) := by ring
    _ ≤ 1 * (K / 2) := by
      have hfrac : (1 + s)⁻¹ * s ≤ 1 := by
        rw [inv_mul_le_iff₀ hspos]
        linarith
      have hhalf : K₂ / 2 ≤ K / 2 := by linarith
      exact mul_le_mul hfrac hhalf (by linarith) one_pos.le
    _ = K / 2 := one_mul _

/-! ## The order-two middle estimate -/

/-- **The difference-retaining middle estimate for the two-block
schedule.**  With the renormalizing difference factors integrated
jointly with their blocks, the weighted two-block refined physical
integral obeys the paper-scale inserted-majorant bound — the exact
inequality shape demanded by `refined_bound` at `m = 2` — with a
primitive constant uniform in the cutoff, coupling, scale, and modes.

Ledger: `|λ_ε|⁴ ‖⋯‖ ≤ λ⁴ Q²/|log ε|²`, while the inserted majorant
integrates to at least `(C₀λ)⁴/|log ε|`; the estimate closes with one
full power of `|log ε|` to spare and no `ε`-dependence at all,
against the interior-core majorant whose mass is `≳ ε⁻⁴`. -/
theorem exists_r324TwoBlock_insertedMajorantBound :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (ρ : SmoothCutoff) (lam : ℝ) {ε : ℝ} (α β : Z4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
          |lamEps lam ε| ^ (2 * 2) *
              ‖r324RefinedPhysicalIntegral ρ ε 2 α β
                twoBlockScheduleIndex‖ ≤
            ∫ z, primitiveInsertedMajorant C₀ lam ε 1 2 z
              ∂paperMeasure := by
  obtain ⟨Q, hQ, hQbound⟩ := exists_norm_r324TwoBlockHalfIntegral_le
  refine ⟨Q + 1, by linarith, ?_⟩
  intro ρ lam ε α β hε hε1 hlog
  set L : ℝ := |Real.log ε| with hLdef
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hlog
  have hlamEps : |lamEps lam ε| ^ (2 * 2) = lam ^ 4 / L ^ 2 := by
    unfold lamEps
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _), ← hLdef]
    rw [div_pow]
    congr 1
    · rw [show (2 * 2 : ℕ) = 4 from rfl, ← abs_pow]
      exact abs_of_nonneg (by positivity)
    · rw [show (2 * 2 : ℕ) = 4 from rfl,
        show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
        Real.sq_sqrt hL0.le]
  have hphys :
      ‖r324RefinedPhysicalIntegral ρ ε 2 α β
          twoBlockScheduleIndex‖ ≤ Q ^ 2 := by
    rw [r324RefinedPhysicalIntegral_twoBlock_eq ρ hε hε1 α β,
      norm_mul]
    calc
      ‖r324TwoBlockHalfIntegral ρ ε α β‖ *
          ‖r324TwoBlockHalfIntegral ρ ε (-α) (-β)‖ ≤
          Q * Q :=
        mul_le_mul (hQbound ρ hε hε1 α β)
          (hQbound ρ hε hε1 (-α) (-β)) (norm_nonneg _) hQ.le
      _ = Q ^ 2 := (sq Q).symm
  have hmajorant :=
    le_integral_primitiveInsertedMajorant
      (Q + 1) lam ε 1 2 hε hε1 one_pos
  have hmajorant' :
      (Q + 1) ^ 4 * lam ^ 4 * (1 / L) ≤
        ∫ z, primitiveInsertedMajorant (Q + 1) lam ε 1 2 z
          ∂paperMeasure := by
    refine le_trans (le_of_eq ?_) hmajorant
    rw [min_self, mul_pow, ← hLdef]
    norm_num
  refine le_trans ?_ hmajorant'
  rw [hlamEps]
  have hkey : Q ^ 2 ≤ (Q + 1) ^ 4 * L := by
    have h1 : Q ^ 2 ≤ (Q + 1) ^ 4 := by nlinarith
    calc
      Q ^ 2 ≤ (Q + 1) ^ 4 := h1
      _ = (Q + 1) ^ 4 * 1 := (mul_one _).symm
      _ ≤ (Q + 1) ^ 4 * L :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
  calc
    lam ^ 4 / L ^ 2 *
        ‖r324RefinedPhysicalIntegral ρ ε 2 α β
          twoBlockScheduleIndex‖ ≤
        lam ^ 4 / L ^ 2 * Q ^ 2 :=
      mul_le_mul_of_nonneg_left hphys (by positivity)
    _ ≤ lam ^ 4 / L ^ 2 * ((Q + 1) ^ 4 * L) :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (Q + 1) ^ 4 * lam ^ 4 * (1 / L) := by
      field_simp

/-! ## Composition with the cross-pairing complement -/

/-- **Order-two middle estimate from the difference-retaining schedule and the
cross-pairing complement.**  The two-block schedule — the unique
order-two case where the interior-core budget fails — is discharged
unconditionally by the difference-retaining estimate; the middle
estimate `R324RefinedInsertedMajorantBound` at order two then reduces
to the complement schedules, all of which have trivial within-half
pairings (no extraction, no difference factor, no interior-core
mechanism): they are paper §4.2 Step 3 cross-cut objects. -/
theorem exists_r324RefinedInsertedMajorantBound_two_of_complement :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (ρ : SmoothCutoff) (lam : ℝ) {ε : ℝ} (α β : Z4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        (∀ p : R324RefinedScheduleIndex 2,
          p ≠ twoBlockScheduleIndex →
            |lamEps lam ε| ^ (2 * 2) *
                ‖r324RefinedPhysicalIntegral ρ ε 2 α β p‖ ≤
              ∫ z, primitiveInsertedMajorant C₀ lam ε 1 2 z
                ∂paperMeasure) →
        R324RefinedInsertedMajorantBound ρ lam ε 2 α β C₀ 1 := by
  obtain ⟨C₀, hC₀, htwo⟩ := exists_r324TwoBlock_insertedMajorantBound
  refine ⟨C₀, hC₀, ?_⟩
  intro ρ lam ε α β hε hε1 hlog hcomplement p
  by_cases hp : p = twoBlockScheduleIndex
  · rw [hp]
    exact htwo ρ lam α β hε hε1 hlog
  · exact hcomplement p hp

/-- **The uniform branch at order two.**  Under the cross-pairing complement
hypothesis, the uniform estimate `MomentRefinedIntegratedReductionOutputAt` of
`exists_deterministicMoment_paper_bound_of_refinedIntegrated_and_countable`
holds at order two with the difference-retaining constant. -/
theorem exists_momentRefinedIntegratedReductionOutputAt_two_of_complement :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (ρ : SmoothCutoff) (lam : ℝ) {ε : ℝ} (α β : Z4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        (∀ p : R324RefinedScheduleIndex 2,
          p ≠ twoBlockScheduleIndex →
            |lamEps lam ε| ^ (2 * 2) *
                ‖r324RefinedPhysicalIntegral ρ ε 2 α β p‖ ≤
              ∫ z, primitiveInsertedMajorant C₀ lam ε 1 2 z
                ∂paperMeasure) →
        MomentRefinedIntegratedReductionOutputAt
          ρ lam ε 2 α β C₀ 1 := by
  obtain ⟨C₀, hC₀, hmiddle⟩ :=
    exists_r324RefinedInsertedMajorantBound_two_of_complement
  refine ⟨C₀, hC₀, ?_⟩
  intro ρ lam ε α β hε hε1 hlog hcomplement
  exact
    momentRefinedIntegratedReductionOutputAt_of_insertedMajorantBound
      hε hε1 (hmiddle ρ lam α β hε hε1 hlog hcomplement)

end

end Anderson4D
