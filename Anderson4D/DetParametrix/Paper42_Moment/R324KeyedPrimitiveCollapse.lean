import Anderson4D.DetParametrix.Paper42_Moment.R324KeyedDecayBudget
import Anderson4D.DetParametrix.Paper42_Moment.R324SignedRoutedEndpointBudget
import Anderson4D.Continuum.CutoffFourierDecay

/-!
# Keyed primitive collapse for the R-324 grouped interior cores

This file proves the residual keyed interior bound
`R324KeyedCoreL1DecayBound` at an explicit `ε`-dependent amplitude
`A₀ · ε⁻¹⁶`, and instantiates the capstone
`exists_deterministicMoment_paper_bound_of_keyedDecay` accordingly.

## The mechanism

For one common-increment group `(p, b)` the interior `L¹` mass is
bounded by the proved skeleton/covariance separation, and the two
eighth-order decay units per frequency slot are extracted from the
covariance weight itself:

* every slot of a raw configuration in the fibre of the key `b` carries
  a mode `qᵢ` with increment key `keyᵢ ∈ {0, qᵢ, -qᵢ}`, so slotwise
  `⟨qᵢ⟩⁻⁸ ≤ ⟨keyᵢ⟩⁻⁸` (`r324KeyedSlotDecay_le_keyDecay`);
* the cutoff symbol obeys the arbitrary-order Schwartz bound, which at
  order `16` yields the slotwise majorant
  `‖covarianceModeCoeff ε k‖ ≤ B ε⁻³² ⟨k⟩⁻³²`
  (`exists_covarianceModeCoeff_keyedDecay_bound`); two of the four
  eighth-order units are retained against the key, the remaining two pay
  the free-mode lattice sums (`≤ 4096` per slot).

## Why the amplitude carries `ε⁻¹⁶`

The prefactor `ε⁻¹⁶` is intrinsic to the interface, not an artifact:
`r324GroupedRefinedCoreL1` integrates the *pointwise norm* of the
grouped core, and every Fourier character has modulus one, so no
physical oscillation survives inside this quantity.  Already at `m = 1`
the interior skeleton is an empty product and the grouped mass of the
key `k` equals a fixed positive multiple of `‖ρ̂(εk)‖²`; since
`‖ρ̂(εk)‖ ≈ ‖ρ̂(0)‖` for `‖k‖ ≲ ε⁻¹`, no `ε`-uniform constant `A` can
satisfy `‖ρ̂(εk)‖² ≤ A² ⟨k⟩⁻¹⁶` on that range.  An `ε`-uniform keyed
bound would therefore require keeping the endpoint/interior
oscillations *outside* the norm, i.e. a different interface than
`R324KeyedCoreL1DecayBound`.  The optimal rate through this interface
is `A ≍ ε⁻⁸`; the constant obtained here is `A₀ ε⁻¹⁶` because the
free-mode lattice sums are paid by the same slotwise symbol bound.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## The slotwise keyed symbol bound -/

/-- The Euclidean frequency of the dilated lattice mode is the dilated
Euclidean frequency of the mode, up to the `2π` Fourier normalization. -/
private theorem euclideanFrequency_eps_mode (ε : ℝ) (k : Z4) :
    euclideanFrequency (fun i => ε * (k i : ℝ)) =
      (ε / (2 * Real.pi)) • z4EuclideanFrequency k := by
  apply PiLp.ext
  intro i
  simp [euclideanFrequency, z4EuclideanFrequency]
  ring

/-- Norm form of the preceding frequency identity. -/
private theorem norm_euclideanFrequency_eps_mode
    {ε : ℝ} (hε : 0 < ε) (k : Z4) :
    ‖euclideanFrequency (fun i => ε * (k i : ℝ))‖ =
      ε / (2 * Real.pi) * ‖z4EuclideanFrequency k‖ := by
  rw [euclideanFrequency_eps_mode, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

/-- The dilation-compatible quadratic comparison used to trade the
`⟨δx⟩` bracket for `δ · ⟨x⟩`. -/
private theorem sq_one_add_mul_ge {δ x : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hx : 0 ≤ x) :
    δ ^ 2 * (1 + x ^ 2) ≤ (1 + δ * x) ^ 2 := by
  nlinarith [sq_nonneg (δ * x), sq_nonneg δ, mul_nonneg hδ.le hx]

/-- **Slotwise keyed symbol bound.**  Every covariance Fourier
coefficient carries four eighth-order decay units at the cost of
`ε⁻³²`: `‖covarianceModeCoeff ε k‖ ≤ B ε⁻³² ⟨k⟩⁻³²`.  This is the
order-16 Schwartz bound for the fixed smooth cutoff. -/
theorem exists_covarianceModeCoeff_keyedDecay_bound :
    ∃ B : ℝ, 0 < B ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ k : Z4,
        ‖ρ.covarianceModeCoeff ε k‖ ≤
          B * ε⁻¹ ^ (32 : ℕ) *
            eighthOrderFrequencyDecay
              ‖z4EuclideanFrequency k‖ ^ (4 : ℕ) := by
  obtain ⟨C, hC, hbound⟩ :=
    ρ.exists_fourierR4_one_add_norm_bound_nat 16
  set S : ℝ := NoiseModel.whiteNoiseFourierScale with hSdef
  have hS : 0 < S := NoiseModel.whiteNoiseFourierScale_pos
  refine ⟨S ^ 2 * C ^ 2 * (2 * Real.pi) ^ (32 : ℕ),
    by positivity, ?_⟩
  intro ε hε hε1 k
  set x : ℝ := ‖z4EuclideanFrequency k‖ with hxdef
  have hx : 0 ≤ x := norm_nonneg _
  set δ : ℝ := ε / (2 * Real.pi) with hδdef
  have hπ : (1 : ℝ) < 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one (by positivity)]
    linarith
  have hbase : (0 : ℝ) < 1 + δ * x := by positivity
  -- the order-16 Schwartz bound at the dilated mode
  have hsym : (1 + δ * x) ^ (16 : ℕ) * ‖ρ.symbol ε k‖ ≤ C := by
    have h := hbound (fun i => ε * (k i : ℝ))
    rw [norm_euclideanFrequency_eps_mode hε k, ← hxdef,
      ← hδdef] at h
    exact h
  -- square it
  have hsymsq :
      ((1 + δ * x) ^ (2 : ℕ)) ^ (16 : ℕ) * ‖ρ.symbol ε k‖ ^ 2 ≤
        C ^ 2 := by
    have hnn : 0 ≤ (1 + δ * x) ^ (16 : ℕ) * ‖ρ.symbol ε k‖ :=
      mul_nonneg (by positivity) (norm_nonneg _)
    have := pow_le_pow_left₀ hnn hsym 2
    calc
      ((1 + δ * x) ^ (2 : ℕ)) ^ (16 : ℕ) * ‖ρ.symbol ε k‖ ^ 2 =
          ((1 + δ * x) ^ (16 : ℕ) * ‖ρ.symbol ε k‖) ^ 2 := by
        ring
      _ ≤ C ^ 2 := this
  -- trade the dilated bracket for `δ³² (1 + x²)¹⁶`
  have htrade :
      δ ^ (32 : ℕ) * (1 + x ^ 2) ^ (16 : ℕ) ≤
        ((1 + δ * x) ^ (2 : ℕ)) ^ (16 : ℕ) := by
    have := pow_le_pow_left₀
      (by positivity : (0 : ℝ) ≤ δ ^ 2 * (1 + x ^ 2))
      (sq_one_add_mul_ge hδ0 hδ1 hx) 16
    calc
      δ ^ (32 : ℕ) * (1 + x ^ 2) ^ (16 : ℕ) =
          (δ ^ 2 * (1 + x ^ 2)) ^ (16 : ℕ) := by
        ring
      _ ≤ ((1 + δ * x) ^ (2 : ℕ)) ^ (16 : ℕ) := this
  have hkey :
      δ ^ (32 : ℕ) * (1 + x ^ 2) ^ (16 : ℕ) *
          ‖ρ.symbol ε k‖ ^ 2 ≤ C ^ 2 := by
    calc
      δ ^ (32 : ℕ) * (1 + x ^ 2) ^ (16 : ℕ) *
          ‖ρ.symbol ε k‖ ^ 2 ≤
          ((1 + δ * x) ^ (2 : ℕ)) ^ (16 : ℕ) *
            ‖ρ.symbol ε k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right htrade (by positivity)
      _ ≤ C ^ 2 := hsymsq
  -- identify the coefficient norm
  have hcoeff :
      ‖ρ.covarianceModeCoeff ε k‖ = S ^ 2 * ‖ρ.symbol ε k‖ ^ 2 := by
    unfold covarianceModeCoeff
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _), norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hS]
  -- assemble
  have hδpow : δ ^ (32 : ℕ) =
      ε ^ (32 : ℕ) / (2 * Real.pi) ^ (32 : ℕ) := by
    rw [hδdef, div_pow]
  have hdecay :
      eighthOrderFrequencyDecay x ^ (4 : ℕ) =
        ((1 + x ^ 2) ^ (16 : ℕ))⁻¹ := by
    unfold eighthOrderFrequencyDecay
    rw [inv_pow, ← pow_mul]
  rw [hcoeff, hdecay]
  have hfinal :
      S ^ 2 * ‖ρ.symbol ε k‖ ^ 2 *
          (ε ^ (32 : ℕ) * (1 + x ^ 2) ^ (16 : ℕ)) ≤
        S ^ 2 * C ^ 2 * (2 * Real.pi) ^ (32 : ℕ) := by
    have hεδ : ε ^ (32 : ℕ) =
        (2 * Real.pi) ^ (32 : ℕ) * δ ^ (32 : ℕ) := by
      rw [hδpow]
      field_simp
    calc
      S ^ 2 * ‖ρ.symbol ε k‖ ^ 2 *
          (ε ^ (32 : ℕ) * (1 + x ^ 2) ^ (16 : ℕ)) =
          S ^ 2 * (2 * Real.pi) ^ (32 : ℕ) *
            (δ ^ (32 : ℕ) * (1 + x ^ 2) ^ (16 : ℕ) *
              ‖ρ.symbol ε k‖ ^ 2) := by
        rw [hεδ]
        ring
      _ ≤ S ^ 2 * (2 * Real.pi) ^ (32 : ℕ) * C ^ 2 :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = S ^ 2 * C ^ 2 * (2 * Real.pi) ^ (32 : ℕ) := by
        ring
  rw [inv_pow, ← div_eq_mul_inv, ← div_eq_mul_inv,
    div_div, le_div_iff₀ (by positivity)]
  exact hfinal

/-! ## The slot modes of a raw refined configuration -/

/-- The standard slot modes of the `a`-th raw refined configuration. -/
private def r324KeyedRawSlotMode
    {m : ℕ} (hm : 0 < m)
    (p : R324RefinedScheduleIndex m) (a : ℕ) :
    Fin m → Z4 :=
  r324NatEquivStandardConfigurations hm
    ((r324NatEquivRefinedContractionConfigurations p a).2)

/-- The raw covariance weight is the slotwise product of coefficient
norms at the standard slot modes. -/
private theorem r324RefinedRawCovarianceWeight_eq_prod
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m) (a : ℕ) :
    ρ.r324RefinedRawCovarianceWeight hm ε p a =
      ∏ i : Fin m,
        ‖ρ.covarianceModeCoeff ε
          (r324KeyedRawSlotMode hm p a i)‖ := by
  unfold r324RefinedRawCovarianceWeight
    r324NatCovarianceConfigurationWeight
    r324CovarianceConfigurationWeight r324KeyedRawSlotMode
  set u := r324NatEquivRefinedContractionConfigurations p a
  set κ := momentContractionEquivFullPairing m u.1.1
  set q : Fin m → Z4 :=
    r324NatEquivStandardConfigurations hm u.2 with hqdef
  rw [← Equiv.prod_comp (r324FullPairIndexEquiv κ)
    (fun j =>
      ‖ρ.covarianceModeCoeff ε
        (r324FullConfigurationOfStandard κ q j)‖)]
  apply Finset.prod_congr rfl
  intro i _hi
  unfold r324FullConfigurationOfStandard
  rw [Function.comp_apply, Equiv.symm_apply_apply]

/-- The increment key of one slot is the slot mode, its negative, or
zero. -/
private theorem r324RefinedRawIncrementKey_cases
    {m : ℕ} (hm : 0 < m)
    (p : R324RefinedScheduleIndex m) (a : ℕ) (i : Fin m) :
    r324RefinedRawIncrementKey hm p a i = 0 ∨
      r324RefinedRawIncrementKey hm p a i =
        r324KeyedRawSlotMode hm p a i ∨
      r324RefinedRawIncrementKey hm p a i =
        -r324KeyedRawSlotMode hm p a i := by
  unfold r324RefinedRawIncrementKey
    r324NatCovarianceIncrementKey r324LeftPairModeContribution
    r324KeyedRawSlotMode
  set u := r324NatEquivRefinedContractionConfigurations p a
  set κ := momentContractionEquivFullPairing m u.1.1
  set q : Fin m → Z4 :=
    r324NatEquivStandardConfigurations hm u.2 with hqdef
  have hconfig :
      r324FullConfigurationOfStandard κ q
        (r324FullPairIndexEquiv κ i) = q i := by
    unfold r324FullConfigurationOfStandard
    rw [Function.comp_apply, Equiv.symm_apply_apply]
  dsimp only
  rw [hconfig]
  split_ifs with h1 h2 h2
  · left
    simp
  · right; right
    simp
  · right; left
    simp
  · left
    simp

/-- Slotwise keyed decay comparison: the decay of the slot mode is at
most the decay of its increment key. -/
private theorem r324KeyedSlotDecay_le_keyDecay
    {m : ℕ} (hm : 0 < m)
    (p : R324RefinedScheduleIndex m) (a : ℕ) (i : Fin m) :
    eighthOrderFrequencyDecay
        ‖z4EuclideanFrequency (r324KeyedRawSlotMode hm p a i)‖ ≤
      eighthOrderFrequencyDecay
        ‖z4EuclideanFrequency
          (r324RefinedRawIncrementKey hm p a i)‖ := by
  rcases r324RefinedRawIncrementKey_cases hm p a i with
    h | h | h
  · rw [h]
    have hzero :
        z4EuclideanFrequency (0 : Z4) = 0 :=
      map_zero z4EuclideanFrequencyAddHom
    rw [hzero, norm_zero]
    have hone : eighthOrderFrequencyDecay 0 = 1 := by
      unfold eighthOrderFrequencyDecay
      norm_num
    rw [hone]
    exact eighthOrderFrequencyDecay_le_one _
  · rw [h]
  · rw [h]
    have hneg :
        z4EuclideanFrequency (-r324KeyedRawSlotMode hm p a i) =
          -z4EuclideanFrequency (r324KeyedRawSlotMode hm p a i) :=
      map_neg z4EuclideanFrequencyAddHom _
    rw [hneg, norm_neg]

/-! ## Lattice sums of the keyed decay weight -/

/-- The keyed decay weights are summable over all keys. -/
private theorem summable_r324KeyedDecaySquared
    {m : ℕ} (hm : 0 < m) :
    Summable fun b : ℕ => r324KeyedDecaySquared hm b := by
  have hcost := summable_keyedDecaySquared_mul_cost hm ⟨0, hm⟩
  refine hcost.of_nonneg_of_le
    (fun b => r324KeyedDecaySquared_nonneg hm b) (fun b => ?_)
  exact le_mul_of_one_le_right
    (r324KeyedDecaySquared_nonneg hm b)
    (one_le_r324GroupedIncrementCost hm b ⟨0, hm⟩)

/-- Total keyed decay budget: `∑_b ∏ⱼ ⟨bⱼ⟩⁻¹⁶ ≤ 4096^m`. -/
private theorem tsum_r324KeyedDecaySquared_le
    {m : ℕ} (hm : 0 < m) :
    (∑' b : ℕ, r324KeyedDecaySquared hm b) ≤
      (4096 : ℝ) ^ m := by
  refine ((summable_r324KeyedDecaySquared hm).tsum_le_tsum
    (fun b => ?_)
    (summable_keyedDecaySquared_mul_cost hm ⟨0, hm⟩)).trans
    (tsum_keyedDecaySquared_mul_cost_le hm ⟨0, hm⟩)
  exact le_mul_of_one_le_right
    (r324KeyedDecaySquared_nonneg hm b)
    (one_le_r324GroupedIncrementCost hm b ⟨0, hm⟩)

/-- The keyed decay weights, transported to the product index. -/
private theorem summable_r324KeyedDecaySquared_prod
    {m : ℕ} (hm : 0 < m) (p : R324RefinedScheduleIndex m) :
    Summable fun u : R324RefinedContractionIndex p × ℕ =>
      r324KeyedDecaySquared hm u.2 := by
  classical
  rw [summable_prod_of_nonneg
    (fun u => r324KeyedDecaySquared_nonneg hm u.2)]
  exact ⟨fun _ => summable_r324KeyedDecaySquared hm,
    Summable.of_finite⟩

/-- The keyed decay weights of all raw refined configurations are
summable. -/
private theorem summable_r324KeyedDecaySquared_raw
    {m : ℕ} (hm : 0 < m) (p : R324RefinedScheduleIndex m) :
    Summable fun a : ℕ =>
      r324KeyedDecaySquared hm
        ((r324NatEquivRefinedContractionConfigurations p a).2) := by
  have hpre :=
    (summable_r324KeyedDecaySquared_prod hm p).comp_injective
      (r324NatEquivRefinedContractionConfigurations p).injective
  exact hpre.congr fun a => by rfl

/-- Raw keyed decay budget: the contraction fibre pays its cardinality
and every slot pays `4096`. -/
private theorem tsum_r324KeyedDecaySquared_raw_le
    {m : ℕ} (hm : 0 < m) (p : R324RefinedScheduleIndex m) :
    (∑' a : ℕ,
      r324KeyedDecaySquared hm
        ((r324NatEquivRefinedContractionConfigurations p a).2)) ≤
      (Nat.card (R324RefinedContractionIndex p) : ℝ) *
        4096 ^ m := by
  have hprod := summable_r324KeyedDecaySquared_prod hm p
  calc
    (∑' a : ℕ,
      r324KeyedDecaySquared hm
        ((r324NatEquivRefinedContractionConfigurations p a).2)) =
        ∑' u : R324RefinedContractionIndex p × ℕ,
          r324KeyedDecaySquared hm u.2 :=
      (r324NatEquivRefinedContractionConfigurations p).tsum_eq
        (fun u : R324RefinedContractionIndex p × ℕ =>
          r324KeyedDecaySquared hm u.2)
    _ = ∑' _e : R324RefinedContractionIndex p, ∑' n : ℕ,
          r324KeyedDecaySquared hm n :=
      hprod.tsum_prod' fun _ => summable_r324KeyedDecaySquared hm
    _ = (Nat.card (R324RefinedContractionIndex p) : ℝ) *
          ∑' n : ℕ, r324KeyedDecaySquared hm n := by
      rw [tsum_const, nsmul_eq_mul]
    _ ≤ (Nat.card (R324RefinedContractionIndex p) : ℝ) *
          4096 ^ m :=
      mul_le_mul_of_nonneg_left
        (tsum_r324KeyedDecaySquared_le hm)
        (Nat.cast_nonneg _)

/-- A nonnegative summable series dominates each of its subseries. -/
private theorem tsum_subtype_le_of_nonneg
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

/-! ## The keyed covariance-weight collapse -/

/-- **Keyed collapse of the grouped covariance weight.**  Two
eighth-order decay units per slot are retained against the common
increment key; the remaining symbol decay pays the free-mode lattice
sums and the amplitude `(B ε⁻³²)^m`. -/
private theorem r324KeyGroupedRefinedCovarianceWeight_le_keyedDecay
    {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε)
    {B : ℝ} (hB : 0 ≤ B)
    (hcoeff : ∀ k : Z4,
      ‖ρ.covarianceModeCoeff ε k‖ ≤
        B * ε⁻¹ ^ (32 : ℕ) *
          eighthOrderFrequencyDecay
            ‖z4EuclideanFrequency k‖ ^ (4 : ℕ))
    (p : R324RefinedScheduleIndex m) (b : ℕ) :
    ρ.r324KeyGroupedRefinedCovarianceWeight hm ε p b ≤
      (Nat.card (R324RefinedContractionIndex p) : ℝ) *
        4096 ^ m *
        ((B * ε⁻¹ ^ (32 : ℕ)) ^ m *
          r324KeyedDecaySquared hm b) := by
  set c : ℝ :=
    (B * ε⁻¹ ^ (32 : ℕ)) ^ m * r324KeyedDecaySquared hm b
    with hcdef
  have hc0 : 0 ≤ c := by
    rw [hcdef]
    exact mul_nonneg (by positivity)
      (r324KeyedDecaySquared_nonneg hm b)
  have hpoint : ∀ a : ℕ,
      r324RefinedRawIncrementKey hm p a =
        r324NatEquivStandardConfigurations hm b →
      ρ.r324RefinedRawCovarianceWeight hm ε p a ≤
        c * r324KeyedDecaySquared hm
          ((r324NatEquivRefinedContractionConfigurations p a).2) := by
    intro a ha
    rw [ρ.r324RefinedRawCovarianceWeight_eq_prod hm ε p a, hcdef]
    have hD0 : ∀ i : Fin m,
        (0 : ℝ) ≤ eighthOrderFrequencyDecay
          ‖z4EuclideanFrequency (r324KeyedRawSlotMode hm p a i)‖ :=
      fun i => eighthOrderFrequencyDecay_nonneg _
    calc
      (∏ i : Fin m,
        ‖ρ.covarianceModeCoeff ε
          (r324KeyedRawSlotMode hm p a i)‖) ≤
          ∏ i : Fin m,
            B * ε⁻¹ ^ (32 : ℕ) *
              eighthOrderFrequencyDecay
                ‖z4EuclideanFrequency
                  (r324KeyedRawSlotMode hm p a i)‖ ^ (4 : ℕ) :=
        Finset.prod_le_prod
          (fun i _ => norm_nonneg _)
          (fun i _ => hcoeff _)
      _ = (B * ε⁻¹ ^ (32 : ℕ)) ^ m *
            ((∏ i : Fin m,
              eighthOrderFrequencyDecay
                ‖z4EuclideanFrequency
                  (r324KeyedRawSlotMode hm p a i)‖ ^ (2 : ℕ)) *
              ∏ i : Fin m,
                eighthOrderFrequencyDecay
                  ‖z4EuclideanFrequency
                    (r324KeyedRawSlotMode hm p a i)‖ ^ (2 : ℕ)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin,
          ← Finset.prod_mul_distrib]
        congr 1
        apply Finset.prod_congr rfl
        intro i _hi
        ring
      _ ≤ (B * ε⁻¹ ^ (32 : ℕ)) ^ m *
            (r324KeyedDecaySquared hm b *
              ∏ i : Fin m,
                eighthOrderFrequencyDecay
                  ‖z4EuclideanFrequency
                    (r324KeyedRawSlotMode hm p a i)‖ ^ (2 : ℕ)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right ?_
            (Finset.prod_nonneg fun i _ => by positivity))
          (by positivity)
        have hprodle :
            (∏ i : Fin m,
              eighthOrderFrequencyDecay
                ‖z4EuclideanFrequency
                  (r324KeyedRawSlotMode hm p a i)‖ ^ (2 : ℕ)) ≤
              ∏ i : Fin m,
                eighthOrderFrequencyDecay
                  ‖z4EuclideanFrequency
                    (r324RefinedRawIncrementKey hm p a i)‖ ^
                      (2 : ℕ) :=
          Finset.prod_le_prod
            (fun i _ => by positivity)
            (fun i _ =>
              pow_le_pow_left₀ (hD0 i)
                (r324KeyedSlotDecay_le_keyDecay hm p a i) 2)
        refine hprodle.trans_eq ?_
        unfold r324KeyedDecaySquared
        apply Finset.prod_congr rfl
        intro i _hi
        rw [ha]
      _ = (B * ε⁻¹ ^ (32 : ℕ)) ^ m *
            r324KeyedDecaySquared hm b *
            r324KeyedDecaySquared hm
              ((r324NatEquivRefinedContractionConfigurations
                p a).2) := by
        unfold r324KeyedDecaySquared r324KeyedRawSlotMode
        ring
  have hraw := ρ.summable_r324RefinedRawCovarianceWeight hm hε p
  have hG := summable_r324KeyedDecaySquared_raw hm p
  unfold r324KeyGroupedRefinedCovarianceWeight tsumByKey
  calc
    (∑' a : {a : ℕ //
        r324RefinedRawIncrementKey hm p a =
          r324NatEquivStandardConfigurations hm b},
      ρ.r324RefinedRawCovarianceWeight hm ε p a.1) ≤
        ∑' a : {a : ℕ //
            r324RefinedRawIncrementKey hm p a =
              r324NatEquivStandardConfigurations hm b},
          c * r324KeyedDecaySquared hm
            ((r324NatEquivRefinedContractionConfigurations
              p a.1).2) :=
      (hraw.subtype _).tsum_le_tsum
        (fun a => hpoint a.1 a.2)
        ((hG.subtype _).mul_left c)
    _ = c * ∑' a : {a : ℕ //
            r324RefinedRawIncrementKey hm p a =
              r324NatEquivStandardConfigurations hm b},
          r324KeyedDecaySquared hm
            ((r324NatEquivRefinedContractionConfigurations
              p a.1).2) :=
      tsum_mul_left
    _ ≤ c * ∑' a : ℕ,
          r324KeyedDecaySquared hm
            ((r324NatEquivRefinedContractionConfigurations
              p a).2) :=
      mul_le_mul_of_nonneg_left
        (tsum_subtype_le_of_nonneg
          (fun a => r324KeyedDecaySquared_nonneg hm _) hG _)
        hc0
    _ ≤ c * ((Nat.card (R324RefinedContractionIndex p) : ℝ) *
          4096 ^ m) :=
      mul_le_mul_of_nonneg_left
        (tsum_r324KeyedDecaySquared_raw_le hm p) hc0
    _ = (Nat.card (R324RefinedContractionIndex p) : ℝ) *
          4096 ^ m *
          ((B * ε⁻¹ ^ (32 : ℕ)) ^ m *
            r324KeyedDecaySquared hm b) := by
      rw [hcdef]
      ring

/-! ## The keyed interior collapse -/

/-- Schedule-uniform envelope: total skeleton mass weighted by the
contraction-fibre cardinalities. -/
private def r324KeyedScheduleEnvelope (m : ℕ) : ℝ :=
  ∑ p : R324RefinedScheduleIndex m,
    r324RefinedInteriorSkeletonL1 p *
      (Nat.card (R324RefinedContractionIndex p) : ℝ)

private theorem r324KeyedScheduleEnvelope_nonneg (m : ℕ) :
    0 ≤ r324KeyedScheduleEnvelope m := by
  unfold r324KeyedScheduleEnvelope
  exact Finset.sum_nonneg fun p _ =>
    mul_nonneg (r324RefinedInteriorSkeletonL1_nonneg p)
      (Nat.cast_nonneg _)

private theorem le_r324KeyedScheduleEnvelope
    {m : ℕ} (p : R324RefinedScheduleIndex m) :
    r324RefinedInteriorSkeletonL1 p *
        (Nat.card (R324RefinedContractionIndex p) : ℝ) ≤
      r324KeyedScheduleEnvelope m := by
  unfold r324KeyedScheduleEnvelope
  exact Finset.single_le_sum
    (f := fun q : R324RefinedScheduleIndex m =>
      r324RefinedInteriorSkeletonL1 q *
        (Nat.card (R324RefinedContractionIndex q) : ℝ))
    (fun q _ =>
      mul_nonneg (r324RefinedInteriorSkeletonL1_nonneg q)
        (Nat.cast_nonneg _))
    (Finset.mem_univ p)

/-- **The keyed interior bound at explicit `ε`-dependent amplitude.**
For every cutoff and truncation order there is a constant `A₀` with
`R324KeyedCoreL1DecayBound ρ hm ε (A₀ ε⁻¹⁶)` throughout the capstone
range: the grouped interior `L¹` mass of one common-increment group
carries two eighth-order decay units per frequency slot at amplitude
`(A₀ ε⁻¹⁶)^{2m} |log ε|^{m-1}`. -/
theorem exists_r324KeyedCoreL1DecayBound
    {m : ℕ} (hm : 0 < m) :
    ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        R324KeyedCoreL1DecayBound ρ hm ε
          (A₀ * ε⁻¹ ^ (16 : ℕ)) := by
  obtain ⟨B, hB, hcoeff⟩ :=
    ρ.exists_covarianceModeCoeff_keyedDecay_bound
  set E : ℝ := r324KeyedScheduleEnvelope m with hEdef
  have hE0 : 0 ≤ E := r324KeyedScheduleEnvelope_nonneg m
  refine ⟨(1 + E) * (1 + 4096 * B), by positivity, ?_⟩
  intro ε hε hε1 hlog pb
  obtain ⟨p, b⟩ := pb
  have hK : 0 ≤ r324KeyedDecaySquared hm b :=
    r324KeyedDecaySquared_nonneg hm b
  have hP : (0 : ℝ) ≤ ε⁻¹ ^ (32 : ℕ) := by positivity
  have hskeleton := r324RefinedInteriorSkeletonL1_nonneg p
  have hcard : (0 : ℝ) ≤
      (Nat.card (R324RefinedContractionIndex p) : ℝ) :=
    Nat.cast_nonneg _
  -- the proved separation followed by the keyed covariance collapse
  have hstep1 :
      ρ.r324GroupedRefinedCoreL1 hm ε (p, b) ≤
        r324RefinedInteriorSkeletonL1 p *
          ((Nat.card (R324RefinedContractionIndex p) : ℝ) *
            4096 ^ m *
            ((B * ε⁻¹ ^ (32 : ℕ)) ^ m *
              r324KeyedDecaySquared hm b)) := by
    refine
      (ρ.r324GroupedRefinedCoreL1_le_skeleton_mul_covariance
        hm hε p b).trans ?_
    exact mul_le_mul_of_nonneg_left
      (ρ.r324KeyGroupedRefinedCovarianceWeight_le_keyedDecay
        hm hε hB.le (hcoeff hε hε1) p b)
      hskeleton
  -- amplitude arithmetic
  have h2m : (1 : ℕ) ≤ 2 * m := by omega
  have hSN :
      r324RefinedInteriorSkeletonL1 p *
          (Nat.card (R324RefinedContractionIndex p) : ℝ) ≤
        (1 + E) ^ (2 * m) := by
    refine (le_r324KeyedScheduleEnvelope p).trans ?_
    calc
      E ≤ 1 + E := by linarith
      _ = (1 + E) ^ (1 : ℕ) := by rw [pow_one]
      _ ≤ (1 + E) ^ (2 * m) :=
        pow_le_pow_right₀ (by linarith) h2m
  have hCpow :
      (4096 : ℝ) ^ m * B ^ m ≤ (1 + 4096 * B) ^ (2 * m) := by
    calc
      (4096 : ℝ) ^ m * B ^ m = (4096 * B) ^ m := by
        rw [mul_pow]
      _ ≤ ((1 + 4096 * B) ^ (2 : ℕ)) ^ m := by
        refine pow_le_pow_left₀ (by positivity) ?_ m
        nlinarith
      _ = (1 + 4096 * B) ^ (2 * m) := by
        rw [← pow_mul]
  have hL1 : (1 : ℝ) ≤ |Real.log ε| ^ (m - 1) :=
    one_le_pow₀ hlog
  have hpowsplit :
      ((1 + E) * (1 + 4096 * B) * ε⁻¹ ^ (16 : ℕ)) ^ (2 * m) =
        (1 + E) ^ (2 * m) * (1 + 4096 * B) ^ (2 * m) *
          (ε⁻¹ ^ (32 : ℕ)) ^ m := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    congr 2
    omega
  calc
    ρ.r324GroupedRefinedCoreL1 hm ε (p, b) ≤
        r324RefinedInteriorSkeletonL1 p *
          ((Nat.card (R324RefinedContractionIndex p) : ℝ) *
            4096 ^ m *
            ((B * ε⁻¹ ^ (32 : ℕ)) ^ m *
              r324KeyedDecaySquared hm b)) := hstep1
    _ = (r324RefinedInteriorSkeletonL1 p *
          (Nat.card (R324RefinedContractionIndex p) : ℝ)) *
          (4096 ^ m * B ^ m) *
          ((ε⁻¹ ^ (32 : ℕ)) ^ m *
            r324KeyedDecaySquared hm b) := by
      rw [mul_pow]
      ring
    _ ≤ (1 + E) ^ (2 * m) * (1 + 4096 * B) ^ (2 * m) *
          ((ε⁻¹ ^ (32 : ℕ)) ^ m *
            r324KeyedDecaySquared hm b) := by
      refine mul_le_mul_of_nonneg_right ?_
        (mul_nonneg (by positivity) hK)
      exact mul_le_mul hSN hCpow
        (mul_nonneg (by positivity) (by positivity))
        (by positivity)
    _ = ((1 + E) * (1 + 4096 * B) * ε⁻¹ ^ (16 : ℕ)) ^ (2 * m) *
          r324KeyedDecaySquared hm b := by
      rw [hpowsplit]
      ring
    _ ≤ ((1 + E) * (1 + 4096 * B) * ε⁻¹ ^ (16 : ℕ)) ^ (2 * m) *
          |Real.log ε| ^ (m - 1) *
          r324KeyedDecaySquared hm b := by
      exact mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right (by positivity) hL1) hK

end SmoothCutoff

/-! ## Unconditional capstone instantiations -/

/-- **The R-324 deterministic moment bound, unconditional form.**
Every analytic input is discharged; the keyed interior bound is
supplied by `exists_r324KeyedCoreL1DecayBound`, so the amplitude
carries the explicit factor `ε⁻¹⁶` (see the header for why this factor
is intrinsic to the `L¹`-keyed interface).  The paper-scale
amplitude — `A` independent of `ε` — is *not* claimed. -/
theorem exists_deterministicMoment_paper_bound_final
    (ρ : SmoothCutoff) {m : ℕ} (hm : 0 < m) {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hlog : 1 ≤ |Real.log ε|)
    (hmtrunc : m ≤ truncOrder ε) :
    ∃ outerConstant A : ℝ, 0 < outerConstant ∧ 0 < A ∧
      ∀ (lam : ℝ) (α β : Z4), 0 ≤ lam →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (65536 * A) lam ε m α β := by
  obtain ⟨A₀, hA₀, hkeyed⟩ :=
    ρ.exists_r324KeyedCoreL1DecayBound hm
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hA : (0 : ℝ) < A₀ * ε⁻¹ ^ (16 : ℕ) := by positivity
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_keyedDecay hA
  exact ⟨outerConstant, A₀ * ε⁻¹ ^ (16 : ℕ), houter, hA,
    fun lam α β hlam =>
      h ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc
        (hkeyed hε hε1 hlog)⟩

/-- Literal decay form of the unconditional estimate: the `min`
bracket is bounded by the P-3.5b-det decay
`ε⁻⁸⟨α⟩⁻⁴⟨β⟩⁻⁴⟨ε²(α+β)⟩⁻⁸`, at the same `ε`-dependent amplitude. -/
theorem exists_deterministicMoment_decay_bound_final
    (ρ : SmoothCutoff) {m : ℕ} (hm : 0 < m) {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hlog : 1 ≤ |Real.log ε|)
    (hmtrunc : m ≤ truncOrder ε) :
    ∃ outerConstant A : ℝ, 0 < outerConstant ∧ 0 < A ∧
      ∀ (lam : ℝ) (α β : Z4), 0 ≤ lam →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          lamEps lam ε ^ 2 * outerConstant *
            ((65536 * A) * lam) ^ (2 * m - 2) *
            paperDeterministicMomentDecay ε α β := by
  obtain ⟨A₀, hA₀, hkeyed⟩ :=
    ρ.exists_r324KeyedCoreL1DecayBound hm
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hA : (0 : ℝ) < A₀ * ε⁻¹ ^ (16 : ℕ) := by positivity
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_decay_bound_of_keyedDecay hA
  exact ⟨outerConstant, A₀ * ε⁻¹ ^ (16 : ℕ), houter, hA,
    fun lam α β hlam =>
      h ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc
        (hkeyed hε hε1 hlog)⟩

/-- The residual slot budget holds unconditionally at the explicit
`ε`-dependent primitive constant `1024 A₀ ε⁻¹⁶`. -/
theorem exists_r324SlotLogBudget_final
    (ρ : SmoothCutoff) {m : ℕ} (hm : 0 < m) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) :
    ∃ A₀ : ℝ, 0 < A₀ ∧
      R324SlotLogBudget ρ hm ε
        (1024 * (A₀ * ε⁻¹ ^ (16 : ℕ))) := by
  obtain ⟨A₀, hA₀, hkeyed⟩ :=
    ρ.exists_r324KeyedCoreL1DecayBound hm
  refine ⟨A₀, hA₀, ?_⟩
  exact r324SlotLogBudget_of_keyedCoreL1DecayBound ρ hm hε hlog
    (by positivity) (hkeyed hε hε1 hlog)

end

end Anderson4D
