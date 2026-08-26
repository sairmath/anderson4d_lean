import Anderson4D.DetParametrix.Paper42_Moment.R324HighFrequencyProof
import Anderson4D.DetParametrix.Paper42_Moment.R324NonzeroRoutedDensity

/-!
# The very-high-frequency residue via the routed-key pigeonhole

This file closes `R324VeryHighCentralFrequencySignedBound` from the
proved corrected route decomposition, leaving only a scalar route
weight ledger.

The mechanism is the frequency-conservation pigeonhole at the *routed*
scale: every countable central routed decomposition
(`CountableCentralRoutedMomentDecomposition`) carries, per term, at
most `truncOrder ε` increments summing exactly to
`freq(α+β)`, so one increment has norm at least
`‖freq(α+β)‖ / truncOrder ε` and the proved per-key covariance
symbol decay `term_le_increment_decay` yields the routed decay unit
`⟨‖freq(α+β)‖ / truncOrder ε⟩⁻⁸` directly — the exact bracket demanded
by `R324SignedCentralDecayBudget` at the maximal admissible increment
count `nInc = truncOrder ε`.  No scale conversion through the weaker
`⟨ε²(α+β)⟩⁻⁸` bracket is used, so no decay is discarded.

Instantiated on the corrected endpoint-nonzero route decomposition
(`countableCentralRoutedMomentReductionOutput_of_nonzeroRoutes`), whose
weights already carry the factor `16⟨α⟩⁻⁴⟨β⟩⁻⁴`, the very-high residue
follows from the single scalar ledger
`∑' routes weight ≤ ⟨α⟩⁻⁴⟨β⟩⁻⁴ · B` with `ε⁸ · B ≤ amplitude`: the
paper's `ε⁻⁸` endpoint sacrifice is borrowed entirely by the ledger.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- **Norm pigeonhole.**  Among finitely many Euclidean increments, one
carries at least the average of their sum's norm. -/
theorem r324VHF_exists_norm_sum_le_card_mul_norm
    {N : ℕ} (hN : 0 < N)
    (v : Fin N → EuclideanSpace ℝ (Fin dim)) :
    ∃ i : Fin N, ‖∑ j, v j‖ ≤ (N : ℝ) * ‖v i‖ := by
  by_contra hcon
  push Not at hcon
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlt :
      (∑ i : Fin N, (N : ℝ) * ‖v i‖) <
        ∑ _i : Fin N, ‖∑ j, v j‖ :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      fun i _ => hcon i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum] at hlt
  have hsum : (∑ j, ‖v j‖) < ‖∑ j, v j‖ :=
    lt_of_mul_lt_mul_left hlt hNR.le
  exact absurd (norm_sum_le Finset.univ v) (not_le.mpr hsum)

/-- **Routed-scale pigeonhole payoff.**  Any countable central routed
decomposition of the deterministic moment obeys the eighth-order decay
unit at the maximal routed increment scale
`‖freq(α+β)‖ / truncOrder ε`: per term, one of its at most
`truncOrder ε` conserved increments is at least the routed average, and
the per-key decay field converts it. -/
theorem r324VHF_norm_deterministicMomentPairingSum_le_of_countableRouted
    {ρ : SmoothCutoff} {lam ε weightBudget : ℝ} {m : ℕ} {α β : Z4}
    (htrunc : 1 ≤ truncOrder ε)
    (hred : CountableCentralRoutedMomentReductionOutput
      ρ lam ε m α β weightBudget) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      weightBudget *
        eighthOrderFrequencyDecay
          ((truncOrder ε : ℝ)⁻¹ *
            ‖z4EuclideanFrequency (α + β)‖) := by
  obtain ⟨d⟩ := hred
  have htruncR : (0 : ℝ) < (truncOrder ε : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one htrunc
  set D : ℝ :=
    eighthOrderFrequencyDecay
      ((truncOrder ε : ℝ)⁻¹ *
        ‖z4EuclideanFrequency (α + β)‖) with hD
  have hterm : ∀ a : ℕ, ‖d.term a‖ ≤ d.weight a * D := by
    intro a
    obtain ⟨i, hi⟩ :=
      r324VHF_exists_norm_sum_le_card_mul_norm
        (d.incrementCount_pos a) (d.increment a)
    rw [d.increment_sum a] at hi
    have hroute :
        (truncOrder ε : ℝ)⁻¹ *
            ‖z4EuclideanFrequency (α + β)‖ ≤
          ‖d.increment a i‖ := by
      rw [inv_mul_le_iff₀ htruncR]
      refine hi.trans ?_
      have hcount :
          ((d.incrementCount a : ℕ) : ℝ) ≤ (truncOrder ε : ℝ) := by
        exact_mod_cast d.incrementCount_le_trunc a
      exact mul_le_mul_of_nonneg_right hcount (norm_nonneg _)
    have hdec :
        eighthOrderFrequencyDecay ‖d.increment a i‖ ≤ D := by
      rw [hD]
      exact eighthOrderFrequencyDecay_anti
        (mul_nonneg (inv_nonneg.mpr htruncR.le) (norm_nonneg _))
        hroute
    exact (d.term_le_increment_decay a i).trans
      (mul_le_mul_of_nonneg_left hdec (d.weight_nonneg a))
  have hscaledSummable :
      Summable fun a : ℕ => d.weight a * D :=
    d.summable_weight.mul_right _
  calc
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ =
        ‖∑' a, d.term a‖ := by rw [d.sum_eq]
    _ ≤ ∑' a, ‖d.term a‖ :=
      norm_tsum_le_tsum_norm d.summable_term.norm
    _ ≤ ∑' a, d.weight a * D :=
      d.summable_term.norm.tsum_le_tsum hterm hscaledSummable
    _ = (∑' a, d.weight a) * D := by rw [tsum_mul_right]
    _ ≤ weightBudget * D :=
      mul_le_mul_of_nonneg_right d.tsum_weight_le
        (eighthOrderFrequencyDecay_nonneg _)

/-- **The signed central-decay budget from a routed weight budget.**
Any countable central routed decomposition whose total weight is at
most `amplitude · ε⁻⁸⟨α⟩⁻⁴⟨β⟩⁻⁴` discharges the budget at
`nInc = truncOrder ε`. -/
theorem r324VHF_signedCentralDecayBudget_of_countableRouted
    {ρ : SmoothCutoff} {lam ε weightBudget amplitude : ℝ}
    {m : ℕ} {α β : Z4}
    (htrunc : 1 ≤ truncOrder ε)
    (hW : weightBudget ≤ amplitude * r324EndpointLoss ε α β)
    (hred : CountableCentralRoutedMomentReductionOutput
      ρ lam ε m α β weightBudget) :
    R324SignedCentralDecayBudget ρ lam ε m α β amplitude :=
  ⟨truncOrder ε, htrunc, le_refl _,
    (r324VHF_norm_deterministicMomentPairingSum_le_of_countableRouted
        htrunc hred).trans
      (mul_le_mul_of_nonneg_right hW
        (eighthOrderFrequencyDecay_nonneg _))⟩

/-- **The very-high-frequency residue from the corrected route weight
ledger.**  For central frequencies above `truncOrder ε · ε⁻¹` (indeed
for every nonzero central frequency), the signed central-decay budget
follows from the corrected endpoint-nonzero route decomposition and a
single scalar ledger: the total route weight is at most
`⟨α⟩⁻⁴⟨β⟩⁻⁴ · B` with `ε⁸ · B ≤ amplitude`.  The `ε⁻⁸` endpoint
sacrifice of the budget is thus borrowed entirely by the route mass
`B`; the covariance-key decay itself is supplied by the proved
per-key field of the route decomposition through the pigeonhole at the
routed scale `‖freq(α+β)‖ / truncOrder ε`. -/
theorem r324VeryHighCentralFrequencySignedBound_of_routeWeightLedger
    {ρ : SmoothCutoff} {lam ε amplitude B : ℝ} {m : ℕ}
    (hm : 0 < m) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (hledger : ∀ (α β : Z4) (hexternal : α + β ≠ 0),
      (∑' pr :
          R324RefinedScheduleIndex m ×
            SmoothCutoff.R324NonzeroRouteLabel m,
        ρ.r324RefinedEndpointNonzeroRouteWeight
          lam hm ε α β hexternal hε hε1 hmtrunc
          pr.1 pr.2) ≤
      paperFourthOrderModeDecay α * paperFourthOrderModeDecay β * B)
    (hAmp : ε ^ (8 : ℕ) * B ≤ amplitude) :
    R324VeryHighCentralFrequencySignedBound ρ lam ε m amplitude := by
  intro α β hzone
  have htrunc : 1 ≤ truncOrder ε := le_trans hm hmtrunc
  have htruncR : (0 : ℝ) < (truncOrder ε : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one htrunc
  have hexternal : α + β ≠ 0 := by
    intro h0
    have hzero : z4EuclideanFrequency (α + β) = 0 := by
      rw [h0]
      exact map_zero SmoothCutoff.z4EuclideanFrequencyAddHom
    rw [hzero, norm_zero] at hzone
    have : (0 : ℝ) < (truncOrder ε : ℝ) * ε⁻¹ :=
      mul_pos htruncR (inv_pos.mpr hε)
    linarith
  have hout :=
    ρ.countableCentralRoutedMomentReductionOutput_of_nonzeroRoutes
      lam hm hε α β hexternal hε1 hmtrunc
      (paperFourthOrderModeDecay α * paperFourthOrderModeDecay β * B)
      (hledger α β hexternal)
  refine r324VHF_signedCentralDecayBudget_of_countableRouted
    htrunc ?_ hout
  have hBle : B ≤ amplitude * ε⁻¹ ^ (8 : ℕ) := by
    have h1 :
        ε⁻¹ ^ (8 : ℕ) * (ε ^ (8 : ℕ) * B) ≤
          ε⁻¹ ^ (8 : ℕ) * amplitude :=
      mul_le_mul_of_nonneg_left hAmp (by positivity)
    have h2 : ε⁻¹ ^ (8 : ℕ) * (ε ^ (8 : ℕ) * B) = B := by
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hε.ne',
        one_pow, one_mul]
    rw [h2] at h1
    linarith
  unfold r324EndpointLoss
  calc
    paperFourthOrderModeDecay α * paperFourthOrderModeDecay β * B ≤
        paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
          (amplitude * ε⁻¹ ^ (8 : ℕ)) :=
      mul_le_mul_of_nonneg_left hBle
        (mul_nonneg (paperFourthOrderModeDecay_nonneg α)
          (paperFourthOrderModeDecay_nonneg β))
    _ = amplitude *
          (ε⁻¹ ^ (8 : ℕ) * paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β) := by
      ring

/-! ## Aggregate discharge of the route weight ledger -/

/-- The `α,β`-independent raw route mass: the complete degree-eight raw
covariance route series, summed over the refined schedule set. -/
def r324VHFRawRouteMass
    (ρ : SmoothCutoff) {m : ℕ} (hm : 0 < m) (ε : ℝ) : ℝ :=
  ∑ p : R324RefinedScheduleIndex m,
    ∑' a : ℕ,
      ρ.r324RefinedRawCovarianceRouteWeight hm ε p a

theorem r324VHFRawRouteMass_nonneg
    (ρ : SmoothCutoff) {m : ℕ} (hm : 0 < m) (ε : ℝ) :
    0 ≤ r324VHFRawRouteMass ρ hm ε :=
  Finset.sum_nonneg fun p _ =>
    tsum_nonneg fun a =>
      ρ.r324RefinedRawCovarianceRouteWeight_nonneg hm ε p a

/-- Subtype comparison for nonnegative summable series. -/
private theorem r324VHF_tsum_subtype_le
    {f : ℕ → ℝ} (h0 : ∀ a, 0 ≤ f a) (hf : Summable f)
    (P : ℕ → Prop) :
    (∑' a : {a : ℕ // P a}, f a.1) ≤ ∑' a, f a := by
  calc
    (∑' a : {a : ℕ // P a}, f a.1) =
        ∑' a : ℕ, Set.indicator {a | P a} f a :=
      tsum_subtype {a | P a} f
    _ ≤ ∑' a, f a :=
      (hf.indicator _).tsum_le_tsum
        (fun a => Set.indicator_le_self'
          (fun a _ => h0 a) a) hf

/-- **Aggregate route weight ledger.**  The total corrected route
weight at fixed external modes is at most `⟨α⟩⁻⁴⟨β⟩⁻⁴` times the
`α,β`-independent raw route mass ledger. -/
theorem r324VHF_tsum_routeWeight_le_modeDecay_mul_rawMass
    (ρ : SmoothCutoff) (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) (α β : Z4)
    (hexternal : α + β ≠ 0) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε) :
    (∑' pr :
        R324RefinedScheduleIndex m ×
          SmoothCutoff.R324NonzeroRouteLabel m,
      ρ.r324RefinedEndpointNonzeroRouteWeight
        lam hm ε α β hexternal hε hε1 hmtrunc
        pr.1 pr.2) ≤
      paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
        (16 * |lamEps lam ε| ^ (2 * m) *
          (SmoothCutoff.r324AllContractionInteriorSkeletonL1 m *
            r324VHFRawRouteMass ρ hm ε)) := by
  have hwAll :=
    ρ.summable_all_r324RefinedEndpointNonzeroRouteWeight
      lam hm hε α β hexternal hε1 hmtrunc
  have hmajp := fun p : R324RefinedScheduleIndex m =>
    ρ.summable_r324RefinedEndpointNonzeroRouteRawMajorant
      lam hm hε α β hexternal hε1 hmtrunc p
  have hwp : ∀ p : R324RefinedScheduleIndex m,
      Summable fun route : SmoothCutoff.R324NonzeroRouteLabel m =>
        ρ.r324RefinedEndpointNonzeroRouteWeight
          lam hm ε α β hexternal hε hε1 hmtrunc p route :=
    fun p =>
      (hmajp p).of_nonneg_of_le
        (fun route =>
          ρ.r324RefinedEndpointNonzeroRouteWeight_nonneg
            lam hm ε α β hexternal hε hε1 hmtrunc p route)
        (fun route =>
          ρ.r324RefinedEndpointNonzeroRouteWeight_le_rawMajorant
            lam hm hε α β hexternal hε1 hmtrunc p route)
  -- per-schedule fibre partition and subtype comparison
  have hperp : ∀ p : R324RefinedScheduleIndex m,
      (∑' route : SmoothCutoff.R324NonzeroRouteLabel m,
        ρ.r324RefinedEndpointNonzeroRouteRawMajorant
          lam hm ε α β hexternal hε hε1 hmtrunc p route) ≤
        16 * paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β *
          (|lamEps lam ε| ^ (2 * m) *
            (SmoothCutoff.r324AllContractionInteriorSkeletonL1 m *
              ∑' a : ℕ,
                ρ.r324RefinedRawCovarianceRouteWeight
                  hm ε p a)) := by
    intro p
    have hfib :
        Summable fun a :
            ρ.R324RefinedEndpointNonzeroRawConfiguration
              hm ε α β p =>
          ρ.r324RefinedRawCovarianceRouteWeight hm ε p a.1 :=
      (ρ.summable_r324RefinedRawCovarianceRouteWeight
        hm hε p).subtype _
    have hfibre_eq :
        (∑' route : SmoothCutoff.R324NonzeroRouteLabel m,
          ∑' a :
              ρ.R324RefinedEndpointNonzeroRouteFiber
                hm ε α β hexternal hε hε1 hmtrunc p route,
            ρ.r324RefinedRawCovarianceRouteWeight
              hm ε p a.1.1) =
          ∑' a :
              ρ.R324RefinedEndpointNonzeroRawConfiguration
                hm ε α β p,
            ρ.r324RefinedRawCovarianceRouteWeight hm ε p a.1 :=
      (hfib.hasSum.tsum_fiberwise
        (ρ.r324RefinedEndpointNonzeroRouteLabel
          hm ε α β hexternal hε hε1 hmtrunc p)).tsum_eq
    have hsub :
        (∑' a :
            ρ.R324RefinedEndpointNonzeroRawConfiguration
              hm ε α β p,
          ρ.r324RefinedRawCovarianceRouteWeight hm ε p a.1) ≤
          ∑' a : ℕ,
            ρ.r324RefinedRawCovarianceRouteWeight hm ε p a :=
      r324VHF_tsum_subtype_le
        (fun a =>
          ρ.r324RefinedRawCovarianceRouteWeight_nonneg hm ε p a)
        (ρ.summable_r324RefinedRawCovarianceRouteWeight hm hε p)
        _
    calc
      (∑' route : SmoothCutoff.R324NonzeroRouteLabel m,
          ρ.r324RefinedEndpointNonzeroRouteRawMajorant
            lam hm ε α β hexternal hε hε1 hmtrunc p route) =
          16 * paperFourthOrderModeDecay α *
              paperFourthOrderModeDecay β *
            (|lamEps lam ε| ^ (2 * m) *
              (SmoothCutoff.r324AllContractionInteriorSkeletonL1 m *
                ∑' route : SmoothCutoff.R324NonzeroRouteLabel m,
                  ∑' a :
                      ρ.R324RefinedEndpointNonzeroRouteFiber
                        hm ε α β hexternal hε hε1 hmtrunc
                        p route,
                    ρ.r324RefinedRawCovarianceRouteWeight
                      hm ε p a.1.1)) := by
        simp only
          [SmoothCutoff.r324RefinedEndpointNonzeroRouteRawMajorant]
        rw [tsum_mul_left, tsum_mul_left, tsum_mul_left]
      _ ≤ 16 * paperFourthOrderModeDecay α *
              paperFourthOrderModeDecay β *
            (|lamEps lam ε| ^ (2 * m) *
              (SmoothCutoff.r324AllContractionInteriorSkeletonL1 m *
                ∑' a : ℕ,
                  ρ.r324RefinedRawCovarianceRouteWeight
                    hm ε p a)) := by
        rw [hfibre_eq]
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg
            (mul_nonneg (by norm_num)
              (paperFourthOrderModeDecay_nonneg α))
            (paperFourthOrderModeDecay_nonneg β))
        refine mul_le_mul_of_nonneg_left ?_
          (pow_nonneg (abs_nonneg _) _)
        exact mul_le_mul_of_nonneg_left hsub
          (SmoothCutoff.r324AllContractionInteriorSkeletonL1_nonneg m)
  calc
    (∑' pr :
        R324RefinedScheduleIndex m ×
          SmoothCutoff.R324NonzeroRouteLabel m,
      ρ.r324RefinedEndpointNonzeroRouteWeight
        lam hm ε α β hexternal hε hε1 hmtrunc
        pr.1 pr.2) =
        ∑ p : R324RefinedScheduleIndex m,
          ∑' route : SmoothCutoff.R324NonzeroRouteLabel m,
            ρ.r324RefinedEndpointNonzeroRouteWeight
              lam hm ε α β hexternal hε hε1 hmtrunc p route := by
      rw [hwAll.tsum_prod' fun p => hwp p, tsum_fintype]
    _ ≤ ∑ p : R324RefinedScheduleIndex m,
          16 * paperFourthOrderModeDecay α *
              paperFourthOrderModeDecay β *
            (|lamEps lam ε| ^ (2 * m) *
              (SmoothCutoff.r324AllContractionInteriorSkeletonL1 m *
                ∑' a : ℕ,
                  ρ.r324RefinedRawCovarianceRouteWeight
                    hm ε p a)) := by
      refine Finset.sum_le_sum fun p _ => ?_
      refine le_trans ?_ (hperp p)
      exact (hwp p).tsum_le_tsum
        (fun route =>
          ρ.r324RefinedEndpointNonzeroRouteWeight_le_rawMajorant
            lam hm hε α β hexternal hε1 hmtrunc p route)
        (hmajp p)
    _ = paperFourthOrderModeDecay α * paperFourthOrderModeDecay β *
          (16 * |lamEps lam ε| ^ (2 * m) *
            (SmoothCutoff.r324AllContractionInteriorSkeletonL1 m *
              r324VHFRawRouteMass ρ hm ε)) := by
      simp only [r324VHFRawRouteMass, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring

/-- **The very-high-frequency residue from one proved numeric
ledger.**  `R324VeryHighCentralFrequencySignedBound` holds as soon as
the raw route mass, at the paper's borrowed `ε⁻⁸` endpoint sacrifice,
fits under the amplitude:
`ε⁸ · 16 · |λ_ε|^{2m} · skeletonL1(m) · rawRouteMass ≤ amplitude`. -/
theorem r324VeryHighCentralFrequencySignedBound_of_rawRouteMass
    {ρ : SmoothCutoff} {lam ε amplitude : ℝ} {m : ℕ}
    (hm : 0 < m) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (hAmp : ε ^ (8 : ℕ) *
        (16 * |lamEps lam ε| ^ (2 * m) *
          (SmoothCutoff.r324AllContractionInteriorSkeletonL1 m *
            r324VHFRawRouteMass ρ hm ε)) ≤ amplitude) :
    R324VeryHighCentralFrequencySignedBound ρ lam ε m amplitude :=
  r324VeryHighCentralFrequencySignedBound_of_routeWeightLedger
    hm hε hε1 hmtrunc
    (fun α β hexternal =>
      r324VHF_tsum_routeWeight_le_modeDecay_mul_rawMass
        ρ lam hm hε α β hexternal hε1 hmtrunc)
    hAmp

end

end Anderson4D
