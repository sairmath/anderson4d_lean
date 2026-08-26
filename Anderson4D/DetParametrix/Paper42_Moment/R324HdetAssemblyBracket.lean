import Anderson4D.DetParametrix.Paper42_Moment.R324RoutedEvalOutput
import Anderson4D.DetParametrix.Paper42_Moment.R324CountableFinalClosure
import Anderson4D.Continuum.CutoffFourierDecay
import Mathlib.Algebra.Order.Chebyshev

/-!
# Unconditional bracket-harvest kit for the final hdet assembly

Pointwise central-frequency infrastructure for the R-324 routed branch:

* `r324HdetAssembly_prod_eighthDecay_le` — the product bracket: the
  product of per-key `⟨·⟩⁻⁸` factors is bounded by `n⁴` times the
  bracket at the summed frequency (Weierstrass + Cauchy--Schwarz);
* `r324HdetAssembly_exists_halfSymbol_sq_bracket` — the half-symbol
  split: the squared cutoff symbol carries one full per-key `⟨·⟩⁻⁸`;
* `r324HdetAssembly_endpointLoss_mul_epsScale_le_paper` — the natural
  `⟨ε‖·‖⟩⁻⁸` scale of the pointwise harvest dominates the paper's
  frozen `⟨ε²‖·‖⟩⁻⁸` bracket;
* lam-uniform replays of the proved order-one routed window
  ledgers, so the unconditional `m = 1` countable routed output is
  available with a constant depending on the cutoff only (the
  proved statements quantify `lam` before the constant, which the
  hdet interface cannot absorb).
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## The product bracket -/

/-- Weierstrass product inequality: `1 + Σxᵢ ≤ Π(1 + xᵢ)` for
nonnegative `xᵢ`. -/
theorem r324HdetAssembly_one_add_sum_le_prod
    {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    1 + ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 + x i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    rw [Finset.sum_cons, Finset.prod_cons]
    have hxa : 0 ≤ x a := hx a (Finset.mem_cons_self a t)
    have hxt : ∀ i ∈ t, 0 ≤ x i :=
      fun i hi => hx i (Finset.mem_cons_of_mem hi)
    have hsum : 0 ≤ ∑ i ∈ t, x i := Finset.sum_nonneg hxt
    have hprod := ih hxt
    nlinarith [hprod, hxa, hsum]

/-- Cauchy--Schwarz on `Fin n`: `(Σaᵢ)² ≤ n · Σaᵢ²`. -/
theorem r324HdetAssembly_sq_sum_le_card_mul_sum_sq
    {n : ℕ} (a : Fin n → ℝ) :
    (∑ i, a i) ^ 2 ≤ (n : ℝ) * ∑ i, a i ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin n))) (f := a)
  simpa using h

/-- **The pointwise product bracket.**  For `n ≥ 1` nonnegative key
sizes, the product of the per-key `⟨·⟩⁻⁸` factors is bounded by `n⁴`
times the eighth-order bracket at the summed size:
`Π ⟨aⱼ⟩⁻⁸ ≤ n⁴ · ⟨Σ aⱼ⟩⁻⁸`.  Combined with momentum conservation
(`Σ ±(ε·keys) = ε·freq(α+β)`) this harvests the central frequency
bracket pointwise, with no zone split. -/
theorem r324HdetAssembly_prod_eighthDecay_le
    {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) :
    ∏ i, eighthOrderFrequencyDecay (a i) ≤
      (n : ℝ) ^ 4 *
        eighthOrderFrequencyDecay (∑ i, a i) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hprod :
      (1 + (∑ i, a i) ^ 2) / (n : ℝ) ≤
        ∏ i, (1 + a i ^ 2) := by
    have hW :=
      r324HdetAssembly_one_add_sum_le_prod
        (Finset.univ : Finset (Fin n)) (fun i => a i ^ 2)
        (fun i _ => sq_nonneg _)
    have hCS := r324HdetAssembly_sq_sum_le_card_mul_sum_sq a
    rw [div_le_iff₀ hn0]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [Finset.sum_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        sq_nonneg (a i))]
  have hprod_pos : (0 : ℝ) < ∏ i, (1 + a i ^ 2) :=
    Finset.prod_pos fun i _ => by positivity
  have hbase_pos : (0 : ℝ) < 1 + (∑ i, a i) ^ 2 := by positivity
  unfold eighthOrderFrequencyDecay
  calc
    ∏ i, ((1 + a i ^ 2) ^ 4)⁻¹ =
        ((∏ i, (1 + a i ^ 2)) ^ 4)⁻¹ := by
      rw [← Finset.prod_pow, Finset.prod_inv_distrib]
    _ ≤ (((1 + (∑ i, a i) ^ 2) / (n : ℝ)) ^ 4)⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_left₀ (by positivity) hprod 4
    _ = (n : ℝ) ^ 4 * ((1 + (∑ i, a i) ^ 2) ^ 4)⁻¹ := by
      rw [div_pow]
      field_simp

/-! ## The half-symbol split -/

/-- **Half-symbol bracket.**  The squared cutoff symbol carries one
complete per-key eighth-order bracket: `‖ρ̂(ξ)‖² ≤ C·⟨‖ξ‖⟩⁻⁸`.  One
half of each squared symbol feeds the product bracket over the keys,
the other half remains for the `‖ρ̂‖`-weighted windows. -/
theorem r324HdetAssembly_exists_halfSymbol_sq_bracket
    (ρ : SmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : R4,
      ‖fourierR4 ρ ξ‖ ^ 2 ≤
        C * eighthOrderFrequencyDecay
          ‖SmoothCutoff.euclideanFrequency ξ‖ := by
  obtain ⟨C4, hC4, hbound⟩ :=
    ρ.exists_fourierR4_one_add_norm_bound_nat 4
  refine ⟨C4 ^ 2, by positivity, fun ξ => ?_⟩
  set x : ℝ := ‖SmoothCutoff.euclideanFrequency ξ‖ with hxdef
  have hx0 : 0 ≤ x := norm_nonneg _
  have hkey : (1 + x ^ 2) ^ 2 ≤ (1 + x) ^ 4 := by
    have h : 1 + x ^ 2 ≤ (1 + x) ^ 2 := by nlinarith
    calc
      (1 + x ^ 2) ^ 2 ≤ ((1 + x) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h 2
      _ = (1 + x) ^ 4 := by ring
  have hsymb := hbound ξ
  have hsymb0 : 0 ≤ ‖fourierR4 ρ ξ‖ := norm_nonneg _
  have h1x : (0 : ℝ) < (1 + x) ^ 4 := by positivity
  have hbase : (0 : ℝ) < (1 + x ^ 2) ^ 4 := by positivity
  rw [← hxdef] at hsymb
  rw [eighthOrderFrequencyDecay, le_mul_inv_iff₀ hbase]
  calc
    ‖fourierR4 ρ ξ‖ ^ 2 * (1 + x ^ 2) ^ 4 =
        (‖fourierR4 ρ ξ‖ * (1 + x ^ 2) ^ 2) ^ 2 := by
      ring
    _ ≤ (‖fourierR4 ρ ξ‖ * (1 + x) ^ 4) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul_of_nonneg_left hkey hsymb0
    _ = ((1 + x) ^ 4 * ‖fourierR4 ρ ξ‖) ^ 2 := by
      ring
    _ ≤ C4 ^ 2 :=
      pow_le_pow_left₀
        (mul_nonneg (by positivity) hsymb0) hsymb 2

/-! ## Coupling-uniform order-one routed window ledgers -/

/-- Coupling-uniform replay of the proved
`exists_r324RoutedPerTermWindowBound_one`: the constant is fixed
before the coupling, as required by the hdet interface.  The proof
body is the proved one; only the quantifier order changes. -/
theorem r324HdetAssembly_exists_perTermWindowBound_one
    (ρ : SmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ,
      R324RoutedPerTermWindowBound ρ lam 1 C := by
  obtain ⟨CB, hCB, hpoint⟩ := r324RoutedEval_pointwise_coeff_bound ρ
  set K1 : ℝ :=
    SmoothCutoff.r324AllContractionInteriorSkeletonL1 1 *
      (r324VHFMassContractionEnvelope 1 * (2 * CB)) with hK1def
  have hK10 : 0 ≤ K1 := by
    rw [hK1def]
    exact mul_nonneg
      (SmoothCutoff.r324AllContractionInteriorSkeletonL1_nonneg 1)
      (mul_nonneg (r324VHFMassContractionEnvelope_nonneg 1)
        (by positivity))
  refine ⟨K1 + 1, by positivity, fun lam => ?_⟩
  intro hm ε hε hε1 _hlog hmtrunc α β hexternal
  have hwAll :=
    ρ.summable_all_r324RefinedEndpointNonzeroRouteWeight
      lam hm hε α β hexternal hε1 hmtrunc
  have hwp : ∀ p : R324RefinedScheduleIndex 1,
      Summable fun route : SmoothCutoff.R324NonzeroRouteLabel 1 =>
        ρ.r324RefinedEndpointNonzeroRouteWeight
          lam hm ε α β hexternal hε hε1 hmtrunc p route :=
    fun p =>
      (ρ.summable_r324RefinedEndpointNonzeroRouteRawMajorant
        lam hm hε α β hexternal hε1 hmtrunc p).of_nonneg_of_le
        (fun route =>
          ρ.r324RefinedEndpointNonzeroRouteWeight_nonneg
            lam hm ε α β hexternal hε hε1 hmtrunc p route)
        (fun route =>
          ρ.r324RefinedEndpointNonzeroRouteWeight_le_rawMajorant
            lam hm hε α β hexternal hε1 hmtrunc p route)
  have hεCB : ∀ k : Z4,
      (1 + ‖z4EuclideanFrequency k‖ ^ 2) ^ 4 *
        ‖ρ.covarianceModeCoeff ε k‖ ≤ CB * ε⁻¹ ^ (8 : ℕ) :=
    fun k => hpoint hε hε1 k
  calc
    (∑' pr :
        R324RefinedScheduleIndex 1 ×
          SmoothCutoff.R324NonzeroRouteLabel 1,
      ρ.r324RefinedEndpointNonzeroRouteWeight
        lam hm ε α β hexternal hε hε1 hmtrunc
        pr.1 pr.2) =
        ∑ p : R324RefinedScheduleIndex 1,
          ∑' route : SmoothCutoff.R324NonzeroRouteLabel 1,
            ρ.r324RefinedEndpointNonzeroRouteWeight
              lam hm ε α β hexternal hε hε1 hmtrunc p route := by
      rw [hwAll.tsum_prod' fun p => hwp p, tsum_fintype]
    _ ≤ ∑ p : R324RefinedScheduleIndex 1,
          16 * paperFourthOrderModeDecay α *
              paperFourthOrderModeDecay β *
            (|lamEps lam ε| ^ (2 * 1) *
              (SmoothCutoff.r324AllContractionInteriorSkeletonL1 1 *
                ((Nat.card
                    (SmoothCutoff.R324RefinedContractionIndex
                      p) : ℝ) *
                  (2 * (CB * ε⁻¹ ^ (8 : ℕ)))))) :=
      Finset.sum_le_sum fun p _ =>
        ρ.r324RoutedEval_perSchedule_one lam hm hε hε1 hεCB
          α β hexternal hmtrunc p
    _ = (16 * paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β) *
          (|lamEps lam ε| ^ (2 * 1) *
            (K1 * ε⁻¹ ^ (8 : ℕ))) := by
      rw [hK1def]
      simp only [r324VHFMassContractionEnvelope, Finset.mul_sum,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ (16 * paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β) *
          (|lamEps lam ε| ^ (2 * 1) *
            ((K1 + 1) ^ 1 * |Real.log ε| ^ (1 - 1) *
              ε⁻¹ ^ (8 : ℕ))) := by
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (paperFourthOrderModeDecay_nonneg α))
          (paperFourthOrderModeDecay_nonneg β))
      refine mul_le_mul_of_nonneg_left ?_
        (pow_nonneg (abs_nonneg _) _)
      have hε8 : (0:ℝ) ≤ ε⁻¹ ^ (8 : ℕ) := by positivity
      have hshape :
          (K1 + 1) ^ 1 * |Real.log ε| ^ (1 - 1) *
              ε⁻¹ ^ (8 : ℕ) =
            (K1 + 1) * ε⁻¹ ^ (8 : ℕ) := by
        norm_num
      rw [hshape]
      nlinarith

/-- Coupling-uniform replay of the proved
`exists_r324RoutedZeroShiftWindowBound_one`. -/
theorem r324HdetAssembly_exists_zeroShiftWindowBound_one
    (ρ : SmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ,
      R324RoutedZeroShiftWindowBound ρ lam 1 C := by
  obtain ⟨K, hK0, hledger⟩ :=
    ρ.r324RoutedEval_zeroShift_ledger one_pos one_le_two
  refine ⟨K + 1, by positivity, fun lam => ?_⟩
  intro hm ε hε hε1 _hlog _hmtrunc α β _hshift
  have hεinv1 : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
  refine (hledger lam hε hε1 α β).trans ?_
  have hdd0 : (0:ℝ) ≤
      16 * paperFourthOrderModeDecay α *
        paperFourthOrderModeDecay β :=
    mul_nonneg
      (mul_nonneg (by norm_num)
        (paperFourthOrderModeDecay_nonneg α))
      (paperFourthOrderModeDecay_nonneg β)
  refine mul_le_mul_of_nonneg_left ?_ hdd0
  refine mul_le_mul_of_nonneg_left ?_
    (pow_nonneg (abs_nonneg _) _)
  have hpow : ε⁻¹ ^ (4 * 1) ≤ ε⁻¹ ^ (8 : ℕ) :=
    pow_le_pow_right₀ hεinv1 (by norm_num)
  calc
    K * ε⁻¹ ^ (4 * 1) ≤ K * ε⁻¹ ^ (8 : ℕ) :=
      mul_le_mul_of_nonneg_left hpow hK0
    _ ≤ (K + 1) * ε⁻¹ ^ (8 : ℕ) := by
      have hp : (0:ℝ) ≤ ε⁻¹ ^ (8 : ℕ) := by positivity
      nlinarith
    _ = (K + 1) ^ 1 * |Real.log ε| ^ (1 - 1) *
          ε⁻¹ ^ (8 : ℕ) := by
      norm_num

/-- **The coupling-uniform unconditional order-one routed output.**
One cutoff-only constant funds the countable central routed moment
reduction output at `m = 1` for every coupling, at the windowed
amplitude of the proved interface. -/
theorem r324HdetAssembly_exists_countableRoutedOutput_one
    (ρ : SmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (lam : ℝ) {ε : ℝ}, 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| → 1 ≤ truncOrder ε →
        ∀ α β : Z4,
          CountableCentralRoutedMomentReductionOutput
            ρ lam ε 1 α β
            ((lamEps lam ε ^ 2 *
                (16 * C ^ 1 * lam ^ (2 * 1 - 2))) *
              r324EndpointLoss ε α β) := by
  obtain ⟨C₁, hC₁, hnonzero⟩ :=
    r324HdetAssembly_exists_perTermWindowBound_one ρ
  obtain ⟨C₂, hC₂, hzero⟩ :=
    r324HdetAssembly_exists_zeroShiftWindowBound_one ρ
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  intro lam ε hε hε1 hlog hmtrunc α β
  exact
    countableCentralRoutedMomentReductionOutput_of_routedWindow
      one_pos hε hε1 hlog hmtrunc
      ((hnonzero lam).mono hC₁.le (le_max_left _ _))
      ((hzero lam).mono hC₂.le (le_max_right _ _)) α β

/-! ## Scale comparison: `⟨ε‖·‖⟩⁻⁸` dominates the paper bracket -/

/-- The natural `ε`-scale bracket of the pointwise harvest, priced with
the endpoint loss, is at least as strong as the frozen paper decay,
whose bracket sits at scale `ε²`. -/
theorem r324HdetAssembly_endpointLoss_mul_epsScale_le_paper
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (α β : Z4) :
    r324EndpointLoss ε α β *
        eighthOrderFrequencyDecay
          (ε * ‖z4EuclideanFrequency (α + β)‖) ≤
      paperDeterministicMomentDecay ε α β := by
  unfold r324EndpointLoss paperDeterministicMomentDecay
  have hdecay :
      eighthOrderFrequencyDecay
          (ε * ‖z4EuclideanFrequency (α + β)‖) ≤
        eighthOrderFrequencyDecay
          (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) := by
    apply eighthOrderFrequencyDecay_anti
    · positivity
    · have h0 := norm_nonneg (z4EuclideanFrequency (α + β))
      nlinarith [mul_nonneg (mul_nonneg
        (sub_nonneg.mpr hε1) hε.le) h0]
  exact mul_le_mul_of_nonneg_left hdecay
    (mul_nonneg
      (mul_nonneg (by positivity)
        (paperFourthOrderModeDecay_nonneg α))
      (paperFourthOrderModeDecay_nonneg β))

end

end Anderson4D
