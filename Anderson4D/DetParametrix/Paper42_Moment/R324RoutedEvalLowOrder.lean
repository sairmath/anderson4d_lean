import Anderson4D.DetParametrix.Paper42_Moment.R324RoutedWindowBudget
import Anderson4D.DetParametrix.Paper42_Moment.R324RoutedWindowLowOrder
import Anderson4D.DetParametrix.Paper42_Moment.R324VHFMassTotalLedger

/-!
# Discharging the routed window ledgers at low order

This file proves the two routed-branch Props of
`R324RoutedWindowBudget` at the orders where they are true and
reachable from the proved route-weight layer:

* `exists_r324RoutedPerTermWindowBound_one` — the nonzero-shift routed
  per-term ledger at `m = 1`.  Endpoint-licensed zero deletion forces
  the single increment key of every surviving route to be exactly
  `α + β`; the marked slot cost `⟨α+β⟩⁸` against the symbol square at
  that same frequency is worth `C·ε⁻⁸` *pointwise*, so the whole ledger
  collapses to finitely many contraction/selector labels at the
  windowed value `C·ε⁻⁸` with no logarithm spent.
* `exists_r324RoutedZeroShiftWindowBound_one` and `…_two` — the
  zero-shift grouped ledger at `m ≤ 2`.  The grouped weights carry no
  slot cost, so the raw covariance mass `(C·ε⁻⁴)^m` already fits under
  the windowed value `C^m·L^{m-1}·ε⁻⁸` exactly for `m ≤ 2`.

The two ingredients proved here and reused by both branches are the
pointwise marked-window bound
`⟨k⟩⁸·‖ρ̂(εk)‖² ≤ C·ε⁻⁸` (from degree-six symbol decay) and the scaled
symbol mass `Σ_k ‖ρ̂(εk)‖² ≤ C·ε⁻⁴`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- The lattice-to-Euclidean frequency map is injective, so frequency
conservation pins lattice keys exactly. -/
theorem z4EuclideanFrequency_injective :
    Function.Injective z4EuclideanFrequency := by
  intro k l hkl
  funext i
  have hcoord :
      ((k i : ℝ)) = ((l i : ℝ)) := by
    have := congrArg (fun w : EuclideanSpace ℝ (Fin dim) => w i) hkl
    simpa [z4EuclideanFrequency] using this
  exact_mod_cast hcoord

/-- **Pointwise marked window.**  One degree-eight slot cost against the
symbol square at the same frequency is worth the endpoint sacrifice
`ε⁻⁸` at every single lattice mode. -/
theorem r324RoutedEval_pointwise_marked_bound (ρ : SmoothCutoff) :
    ∃ CP : ℝ, 0 < CP ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ k : Z4,
        (1 + ‖z4EuclideanFrequency k‖ ^ 2) ^ 4 *
            ‖ρ.symbol ε k‖ ^ 2 ≤
          CP * ε⁻¹ ^ (8 : ℕ) := by
  obtain ⟨C6, _hC6, hdecay⟩ :=
    ρ.exists_fourierR4_one_add_norm_bound_nat 6
  set B : ℝ := C6 ^ 2 * (2 * Real.pi) ^ 12 with hBdef
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  refine ⟨256 * (B + 1), by positivity, ?_⟩
  intro ε hε hε1 k
  set s : ℝ := (z4SupRadius k : ℝ) with hsdef
  have hs : 0 ≤ s := Nat.cast_nonneg _
  have hεinv1 : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
  have hbracket :
      (1 + ‖z4EuclideanFrequency k‖ ^ 2) ^ 4 ≤
        256 * (1 + s) ^ 8 := by
    rw [norm_sq_z4EuclideanFrequency]
    have hPle := r324RoutedWindow_paperModeNormSq_le k
    rw [← hsdef] at hPle
    have hP0 : 0 ≤ paperModeNormSq k := paperModeNormSq_nonneg k
    have hstep : 1 + paperModeNormSq k ≤ 4 * (1 + s) ^ 2 := by
      nlinarith
    calc
      (1 + paperModeNormSq k) ^ 4 ≤ (4 * (1 + s) ^ 2) ^ 4 :=
        pow_le_pow_left₀ (by linarith) hstep 4
      _ = 256 * (1 + s) ^ 8 := by ring
  by_cases hcase : 1 + s ≤ ε⁻¹
  · have hsymb : ‖ρ.symbol ε k‖ ^ 2 ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (ρ.norm_symbol_le_one ε k)
    have hpow : (1 + s) ^ 8 ≤ ε⁻¹ ^ 8 :=
      pow_le_pow_left₀ (by linarith) hcase 8
    calc
      (1 + ‖z4EuclideanFrequency k‖ ^ 2) ^ 4 *
          ‖ρ.symbol ε k‖ ^ 2 ≤
          (256 * (1 + s) ^ 8) * 1 :=
        mul_le_mul hbracket hsymb (by positivity) (by positivity)
      _ = 256 * (1 + s) ^ 8 := by ring
      _ ≤ 256 * ε⁻¹ ^ 8 := by nlinarith
      _ ≤ 256 * (B + 1) * ε⁻¹ ^ 8 := by
        have hpos : (0:ℝ) < ε⁻¹ ^ 8 :=
          pow_pos (lt_of_lt_of_le one_pos hεinv1) 8
        nlinarith
  · push Not at hcase
    have hsq :=
      r324RoutedWindow_symbol_sq_le_of_decay_six ρ hdecay hε hε1 k
    rw [← hBdef, ← hsdef] at hsq
    have hinv4 : ((1 + s) ^ 4)⁻¹ ≤ ε ^ 4 := by
      have h1s : (0 : ℝ) < 1 + s := by linarith
      have hεle : ε⁻¹ ≤ 1 + s := hcase.le
      have h1 : (ε⁻¹) ^ 4 ≤ (1 + s) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hεle 4
      calc
        ((1 + s) ^ 4)⁻¹ ≤ ((ε⁻¹) ^ 4)⁻¹ :=
          inv_anti₀ (by positivity) h1
        _ = ε ^ 4 := by
          rw [← inv_pow, inv_inv]
    calc
      (1 + ‖z4EuclideanFrequency k‖ ^ 2) ^ 4 *
          ‖ρ.symbol ε k‖ ^ 2 ≤
          (256 * (1 + s) ^ 8) *
            (B * (ε⁻¹ ^ 12 * (((1 + s) ^ 12)⁻¹))) :=
        mul_le_mul hbracket hsq (by positivity) (by positivity)
      _ = (256 * B * ε⁻¹ ^ 12) *
            ((1 + s) ^ 8 * ((1 + s) ^ 12)⁻¹) := by ring
      _ = (256 * B * ε⁻¹ ^ 12) * ((1 + s) ^ 4)⁻¹ := by
        congr 1
        have h1s : (1 + s) ≠ 0 := by positivity
        field_simp
      _ ≤ (256 * B * ε⁻¹ ^ 12) * ε ^ 4 :=
        mul_le_mul_of_nonneg_left hinv4 (by positivity)
      _ = 256 * B * (ε⁻¹ ^ 8 * ((ε⁻¹ ^ 4) * ε ^ 4)) := by ring
      _ = 256 * B * ε⁻¹ ^ 8 := by
        rw [← mul_pow, inv_mul_cancel₀ hε.ne', one_pow, mul_one]
      _ ≤ 256 * (B + 1) * ε⁻¹ ^ 8 := by
        have : (0:ℝ) < ε⁻¹ ^ 8 := pow_pos (by positivity) 8
        nlinarith

/-- **Scaled symbol mass.**  The complete symbol-square lattice mass is
one mollifier volume `ε⁻⁴`. -/
theorem r324RoutedEval_symbol_mass_le (ρ : SmoothCutoff) :
    ∃ CS : ℝ, 0 < CS ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        (Summable fun k : Z4 => ‖ρ.symbol ε k‖ ^ 2) ∧
        (∑' k : Z4, ‖ρ.symbol ε k‖ ^ 2) ≤ CS * ε⁻¹ ^ (4 : ℕ) := by
  obtain ⟨C6, _hC6, hdecay⟩ :=
    ρ.exists_fourierR4_one_add_norm_bound_nat 6
  set B : ℝ := C6 ^ 2 * (2 * Real.pi) ^ 12 with hBdef
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  refine ⟨1296 + 20 * B, by positivity, ?_⟩
  intro ε hε hε1
  set N : ℕ := ⌈ε⁻¹⌉₊ with hNdef
  have hεinv1 : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
  have hNε : ε⁻¹ ≤ (N : ℝ) := Nat.le_ceil _
  set f : Z4 → ℝ := fun k => ‖ρ.symbol ε k‖ ^ 2 with hfdef
  set g : Z4 → ℝ := fun k =>
    if k ∈ z4Cube N then 1 else 0 with hgdef
  set h : Z4 → ℝ := fun k =>
    (B * ε⁻¹ ^ 8) * z4EighthRadialTail (N + 1) k with hhdef
  have hg0 : ∀ k, 0 ≤ g k := by
    intro k
    simp only [hgdef]
    by_cases hk : k ∈ z4Cube N
    · rw [if_pos hk]; norm_num
    · rw [if_neg hk]
  have hh0 : ∀ k, 0 ≤ h k := fun k =>
    mul_nonneg (by positivity) (z4EighthRadialTail_nonneg _ _)
  have hfg : ∀ k, f k ≤ g k + h k := by
    intro k
    set s : ℝ := (z4SupRadius k : ℝ) with hsdef
    have hs : 0 ≤ s := Nat.cast_nonneg _
    by_cases hk : k ∈ z4Cube N
    · refine le_trans ?_ (le_add_of_nonneg_right (hh0 k))
      simp only [hfdef, hgdef]
      rw [if_pos hk]
      exact pow_le_one₀ (norm_nonneg _) (ρ.norm_symbol_le_one ε k)
    · refine le_trans ?_ (le_add_of_nonneg_left (hg0 k))
      have hrad : N + 1 ≤ z4SupRadius k := by
        rw [mem_z4Cube_iff_z4SupRadius_le] at hk
        omega
      have hradR : ε⁻¹ ≤ s := by
        have hNs : ((N : ℝ)) + 1 ≤ s := by
          rw [hsdef]
          exact_mod_cast hrad
        linarith
      simp only [hfdef, hhdef]
      have htail : z4EighthRadialTail (N + 1) k =
          ((1 + s) ^ 8)⁻¹ := by
        unfold z4EighthRadialTail
        rw [if_pos hrad, l2LatticeRadialWeight_eq_z4SupRadius,
          ← hsdef]
      have hsq :=
        r324RoutedWindow_symbol_sq_le_of_decay_six ρ hdecay hε hε1 k
      rw [← hBdef, ← hsdef] at hsq
      have hinv4 : ((1 + s) ^ 4)⁻¹ ≤ ε ^ 4 := by
        have h1 : (ε⁻¹) ^ 4 ≤ (1 + s) ^ 4 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 4
        calc
          ((1 + s) ^ 4)⁻¹ ≤ ((ε⁻¹) ^ 4)⁻¹ :=
            inv_anti₀ (by positivity) h1
          _ = ε ^ 4 := by rw [← inv_pow, inv_inv]
      rw [htail]
      calc
        ‖ρ.symbol ε k‖ ^ 2 ≤
            B * (ε⁻¹ ^ 12 * (((1 + s) ^ 12)⁻¹)) := hsq
        _ = (B * ε⁻¹ ^ 12) *
              (((1 + s) ^ 8)⁻¹ * ((1 + s) ^ 4)⁻¹) := by
          rw [← mul_inv, ← pow_add]
          ring
        _ ≤ (B * ε⁻¹ ^ 12) * (((1 + s) ^ 8)⁻¹ * ε ^ 4) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hinv4 (by positivity)
        _ = (B * (ε⁻¹ ^ 8 * (ε⁻¹ ^ 4 * ε ^ 4))) *
              ((1 + s) ^ 8)⁻¹ := by ring
        _ = (B * ε⁻¹ ^ 8) * ((1 + s) ^ 8)⁻¹ := by
          rw [← mul_pow, inv_mul_cancel₀ hε.ne', one_pow, mul_one]
  have hgsummable : Summable g := by
    apply summable_of_ne_finset_zero (s := z4Cube N)
    intro k hk
    simp only [hgdef]
    exact if_neg hk
  have hhsummable : Summable h := by
    simp only [hhdef]
    exact (summable_z4EighthRadialTail (N + 1)).mul_left _
  have hfsummable : Summable f :=
    Summable.of_nonneg_of_le
      (fun k => by simp only [hfdef]; positivity) hfg
      (hgsummable.add hhsummable)
  refine ⟨hfsummable, ?_⟩
  have hN2ε : (N : ℝ) ≤ 2 * ε⁻¹ := by
    have hceil : (N : ℝ) < ε⁻¹ + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith
  have hgsum : (∑' k, g k) ≤ 1296 * ε⁻¹ ^ 4 := by
    have hgeq : (∑' k, g k) =
        ∑ k ∈ z4Cube N, (1 : ℝ) := by
      rw [tsum_eq_sum (s := z4Cube N) ?_]
      · exact Finset.sum_congr rfl fun k hk => by
          simp only [hgdef]; exact if_pos hk
      · intro k hk
        simp only [hgdef]
        exact if_neg hk
    rw [hgeq, Finset.sum_const, card_z4Cube, nsmul_eq_mul,
      mul_one]
    have hside : ((2 * N + 1 : ℕ) : ℝ) ≤ 6 * ε⁻¹ := by
      push_cast
      linarith
    calc
      (((2 * N + 1) ^ 4 : ℕ) : ℝ) =
          ((2 * N + 1 : ℕ) : ℝ) ^ 4 := by push_cast; ring
      _ ≤ (6 * ε⁻¹) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hside 4
      _ = 1296 * ε⁻¹ ^ 4 := by ring
  have hhsum : (∑' k, h k) ≤ 20 * B * ε⁻¹ ^ 4 := by
    have htail := tsum_z4EighthRadialTail_le (N + 1) (Nat.succ_pos N)
    have hεN : ((N : ℝ) + 1)⁻¹ ≤ ε := by
      have hstep : ε⁻¹ ≤ (N : ℝ) + 1 := by linarith
      calc
        ((N : ℝ) + 1)⁻¹ ≤ (ε⁻¹)⁻¹ := inv_anti₀ (by positivity) hstep
        _ = ε := inv_inv ε
    simp only [hhdef]
    rw [tsum_mul_left]
    calc
      (B * ε⁻¹ ^ 8) *
          ∑' k, z4EighthRadialTail (N + 1) k ≤
          (B * ε⁻¹ ^ 8) *
            (20 * (((N + 1 : ℕ) : ℝ)⁻¹) ^ 4) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ (B * ε⁻¹ ^ 8) * (20 * ε ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by
          push_cast
          ring
        have h4 : (((N + 1 : ℕ) : ℝ)⁻¹) ^ 4 ≤ ε ^ 4 := by
          rw [hcast]
          exact pow_le_pow_left₀ (by positivity) hεN 4
        linarith
      _ = (20 * B * ε⁻¹ ^ 4) * (ε⁻¹ ^ 4 * ε ^ 4) := by ring
      _ = 20 * B * ε⁻¹ ^ 4 := by
        rw [← mul_pow, inv_mul_cancel₀ hε.ne', one_pow, mul_one]
  calc
    (∑' k : Z4, ‖ρ.symbol ε k‖ ^ 2) = ∑' k, f k := by
      simp only [hfdef]
    _ ≤ ∑' k, (g k + h k) :=
      hfsummable.tsum_le_tsum hfg (hgsummable.add hhsummable)
    _ = (∑' k, g k) + ∑' k, h k :=
      hgsummable.tsum_add hhsummable
    _ ≤ 1296 * ε⁻¹ ^ 4 + 20 * B * ε⁻¹ ^ 4 :=
      add_le_add hgsum hhsum
    _ = (1296 + 20 * B) * ε⁻¹ ^ 4 := by ring

/-- Exact norm of one covariance Fourier coefficient. -/
theorem r324RoutedEval_norm_covarianceModeCoeff
    (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    ‖ρ.covarianceModeCoeff ε k‖ =
      NoiseModel.whiteNoiseFourierScale ^ 2 *
        ‖ρ.symbol ε k‖ ^ 2 := by
  unfold SmoothCutoff.covarianceModeCoeff
  rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    abs_of_nonneg (sq_nonneg _)]

/-- **Covariance coefficient mass.**  The total covariance Fourier mass
is one mollifier volume `ε⁻⁴`. -/
theorem r324RoutedEval_covarianceMass_le (ρ : SmoothCutoff) :
    ∃ CV : ℝ, 0 < CV ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        (∑' k : Z4, ‖ρ.covarianceModeCoeff ε k‖) ≤
          CV * ε⁻¹ ^ (4 : ℕ) := by
  obtain ⟨CS, hCS, hmass⟩ := r324RoutedEval_symbol_mass_le ρ
  refine
    ⟨(NoiseModel.whiteNoiseFourierScale ^ 2 + 1) * CS,
      by positivity, ?_⟩
  intro ε hε hε1
  obtain ⟨hsummable, hsum⟩ := hmass hε hε1
  calc
    (∑' k : Z4, ‖ρ.covarianceModeCoeff ε k‖) =
        NoiseModel.whiteNoiseFourierScale ^ 2 *
          ∑' k : Z4, ‖ρ.symbol ε k‖ ^ 2 := by
      rw [← tsum_mul_left]
      exact tsum_congr fun k =>
        r324RoutedEval_norm_covarianceModeCoeff ρ ε k
    _ ≤ NoiseModel.whiteNoiseFourierScale ^ 2 *
          (CS * ε⁻¹ ^ (4 : ℕ)) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ ≤ ((NoiseModel.whiteNoiseFourierScale ^ 2 + 1) * CS) *
          ε⁻¹ ^ (4 : ℕ) := by
      have hp : (0:ℝ) ≤ ε⁻¹ ^ (4 : ℕ) := by positivity
      nlinarith


/-- Pointwise covariance-coefficient marked bound: one degree-eight slot
cost against the coefficient at the same frequency is worth `C·ε⁻⁸`. -/
theorem r324RoutedEval_pointwise_coeff_bound (ρ : SmoothCutoff) :
    ∃ CB : ℝ, 0 < CB ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ k : Z4,
        (1 + ‖z4EuclideanFrequency k‖ ^ 2) ^ 4 *
            ‖ρ.covarianceModeCoeff ε k‖ ≤
          CB * ε⁻¹ ^ (8 : ℕ) := by
  obtain ⟨CP, hCP, hpoint⟩ := r324RoutedEval_pointwise_marked_bound ρ
  refine
    ⟨(NoiseModel.whiteNoiseFourierScale ^ 2 + 1) * CP,
      by positivity, ?_⟩
  intro ε hε hε1 k
  rw [r324RoutedEval_norm_covarianceModeCoeff ρ ε k]
  calc
    (1 + ‖z4EuclideanFrequency k‖ ^ 2) ^ 4 *
        (NoiseModel.whiteNoiseFourierScale ^ 2 *
          ‖ρ.symbol ε k‖ ^ 2) =
        NoiseModel.whiteNoiseFourierScale ^ 2 *
          ((1 + ‖z4EuclideanFrequency k‖ ^ 2) ^ 4 *
            ‖ρ.symbol ε k‖ ^ 2) := by ring
    _ ≤ NoiseModel.whiteNoiseFourierScale ^ 2 *
          (CP * ε⁻¹ ^ (8 : ℕ)) :=
      mul_le_mul_of_nonneg_left (hpoint hε hε1 k) (sq_nonneg _)
    _ ≤ ((NoiseModel.whiteNoiseFourierScale ^ 2 + 1) * CP) *
          ε⁻¹ ^ (8 : ℕ) := by
      have hp : (0:ℝ) ≤ ε⁻¹ ^ (8 : ℕ) := by positivity
      nlinarith

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- The standard slot modes of one raw refined configuration. -/
def r324RoutedEvalSlotMode
    {m : ℕ} (hm : 0 < m)
    (p : R324RefinedScheduleIndex m) (a : ℕ) :
    Fin m → Z4 :=
  r324NatEquivStandardConfigurations hm
    ((r324NatEquivRefinedContractionConfigurations p a).2)

/-- The raw covariance weight is the slotwise product of coefficient
norms at the standard slot modes. -/
theorem r324RoutedEval_covWeight_eq_prod
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m) (a : ℕ) :
    ρ.r324RefinedRawCovarianceWeight hm ε p a =
      ∏ i : Fin m,
        ‖ρ.covarianceModeCoeff ε
          (r324RoutedEvalSlotMode hm p a i)‖ := by
  unfold r324RefinedRawCovarianceWeight
    r324NatCovarianceConfigurationWeight
    r324CovarianceConfigurationWeight r324RoutedEvalSlotMode
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
theorem r324RoutedEval_incrementKey_cases
    {m : ℕ} (hm : 0 < m)
    (p : R324RefinedScheduleIndex m) (a : ℕ) (i : Fin m) :
    r324RefinedRawIncrementKey hm p a i = 0 ∨
      r324RefinedRawIncrementKey hm p a i =
        r324RoutedEvalSlotMode hm p a i ∨
      r324RefinedRawIncrementKey hm p a i =
        -r324RoutedEvalSlotMode hm p a i := by
  unfold r324RefinedRawIncrementKey
    r324NatCovarianceIncrementKey r324LeftPairModeContribution
    r324RoutedEvalSlotMode
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

/-- The routed cost of one increment key never exceeds the cost of its
slot mode. -/
theorem r324RoutedEval_keyCost_le_modeCost
    {m : ℕ} (hm : 0 < m)
    (p : R324RefinedScheduleIndex m) (a : ℕ) (i : Fin m) :
    (1 + ‖z4EuclideanFrequency
        (r324RefinedRawIncrementKey hm p a i)‖ ^ 2) ^ 4 ≤
      (1 + ‖z4EuclideanFrequency
        (r324RoutedEvalSlotMode hm p a i)‖ ^ 2) ^ 4 := by
  have hmode : (0 : ℝ) ≤
      ‖z4EuclideanFrequency (r324RoutedEvalSlotMode hm p a i)‖ :=
    norm_nonneg _
  rcases r324RoutedEval_incrementKey_cases hm p a i with h | h | h
  · rw [h]
    have hzero : z4EuclideanFrequency (0 : Z4) = 0 :=
      map_zero z4EuclideanFrequencyAddHom
    rw [hzero, norm_zero]
    have h1 : (1 : ℝ) ≤ 1 +
        ‖z4EuclideanFrequency
          (r324RoutedEvalSlotMode hm p a i)‖ ^ 2 := by
      nlinarith
    calc ((1 : ℝ) + 0 ^ 2) ^ 4 = 1 := by norm_num
      _ ≤ (1 + ‖z4EuclideanFrequency
            (r324RoutedEvalSlotMode hm p a i)‖ ^ 2) ^ 4 :=
        one_le_pow₀ h1
  · rw [h]
  · rw [h]
    have hneg :
        z4EuclideanFrequency (-r324RoutedEvalSlotMode hm p a i) =
          -z4EuclideanFrequency (r324RoutedEvalSlotMode hm p a i) :=
      map_neg z4EuclideanFrequencyAddHom _
    rw [hneg, norm_neg]

end SmoothCutoff

/-- Low-order product mass: at `m ≤ 2` the assignment series of a
slotwise product is bounded by the per-slot mass to the `m`-th power. -/
theorem r324RoutedEval_tsum_pi_prod_le_pow
    {F : Z4 → ℝ} (hF0 : ∀ k, 0 ≤ F k) (hFs : Summable F)
    {M : ℝ} (hFM : (∑' k, F k) ≤ M)
    {m : ℕ} (hm : 0 < m) (hm2 : m ≤ 2) :
    (Summable fun q : Fin m → Z4 => ∏ i, F (q i)) ∧
      (∑' q : Fin m → Z4, ∏ i, F (q i)) ≤ M ^ m := by
  have hM0 : 0 ≤ M :=
    le_trans (tsum_nonneg hF0) hFM
  interval_cases m
  · have hcongr :
        ∀ q : Fin 1 → Z4, (∏ i, F (q i)) = F (q 0) := by
      intro q
      exact Fin.prod_univ_one _
    have hsum1 :
        Summable fun q : Fin 1 → Z4 => F (q 0) := by
      have := (Equiv.funUnique (Fin 1) Z4).summable_iff.mpr hFs
      exact this
    constructor
    · exact hsum1.congr fun q => (hcongr q).symm
    · calc
        (∑' q : Fin 1 → Z4, ∏ i, F (q i)) =
            ∑' q : Fin 1 → Z4, F (q 0) :=
          tsum_congr hcongr
        _ = ∑' k : Z4, F k :=
          (Equiv.funUnique (Fin 1) Z4).tsum_eq F
        _ ≤ M := hFM
        _ = M ^ 1 := (pow_one M).symm
  · have hcongr :
        ∀ q : Fin 2 → Z4, (∏ i, F (q i)) = F (q 0) * F (q 1) := by
      intro q
      exact Fin.prod_univ_two _
    have hpair :
        Summable fun z : Z4 × Z4 => F z.1 * F z.2 :=
      hFs.mul_of_nonneg hFs hF0 hF0
    have hsum2 :
        Summable fun q : Fin 2 → Z4 => F (q 0) * F (q 1) := by
      have := (piFinTwoEquiv fun _ : Fin 2 => Z4).summable_iff.mpr
        hpair
      exact this
    constructor
    · exact hsum2.congr fun q => (hcongr q).symm
    · calc
        (∑' q : Fin 2 → Z4, ∏ i, F (q i)) =
            ∑' q : Fin 2 → Z4, F (q 0) * F (q 1) :=
          tsum_congr hcongr
        _ = ∑' z : Z4 × Z4, F z.1 * F z.2 :=
          (piFinTwoEquiv fun _ : Fin 2 => Z4).tsum_eq
            (fun z : Z4 × Z4 => F z.1 * F z.2)
        _ = (∑' k : Z4, F k) * ∑' k : Z4, F k :=
          (hFs.tsum_mul_tsum hFs hpair).symm
        _ ≤ M * M :=
          mul_le_mul hFM hFM (tsum_nonneg hF0) hM0
        _ = M ^ 2 := (sq M).symm

namespace SmoothCutoff

/-- The complete raw covariance mass of one refined schedule at
`m ≤ 2`: the contraction fibre pays its cardinality and each slot pays
the full per-slot coefficient mass. -/
theorem r324RoutedEval_tsum_rawCovWeight_le
    (ρ : SmoothCutoff)
    {m : ℕ} (hm : 0 < m) (hm2 : m ≤ 2)
    {ε M : ℝ} (hε : 0 < ε)
    (hMass : (∑' k : Z4, ‖ρ.covarianceModeCoeff ε k‖) ≤ M)
    (p : R324RefinedScheduleIndex m) :
    (∑' a : ℕ, ρ.r324RefinedRawCovarianceWeight hm ε p a) ≤
      (Nat.card (R324RefinedContractionIndex p) : ℝ) * M ^ m := by
  set F : Z4 → ℝ := fun k => ‖ρ.covarianceModeCoeff ε k‖
    with hFdef
  have hF0 : ∀ k, 0 ≤ F k := fun k => norm_nonneg _
  have hFs : Summable F := ρ.summable_norm_covarianceModeCoeff hε
  obtain ⟨hpisum, hpile⟩ :=
    r324RoutedEval_tsum_pi_prod_le_pow hF0 hFs hMass hm hm2
  set e := r324NatEquivRefinedContractionConfigurations p
  set g : R324RefinedContractionIndex p × ℕ → ℝ := fun u =>
    ∏ i, F (r324NatEquivStandardConfigurations hm u.2 i)
    with hgdef
  have hg0 : ∀ u, 0 ≤ g u := fun u =>
    Finset.prod_nonneg fun i _ => hF0 _
  have hgf : ∀ u,
      ρ.r324RefinedRawCovarianceWeight hm ε p (e.symm u) = g u := by
    intro u
    rw [ρ.r324RoutedEval_covWeight_eq_prod hm ε p (e.symm u)]
    simp only [hgdef]
    apply Finset.prod_congr rfl
    intro i _hi
    congr 2
    unfold r324RoutedEvalSlotMode
    rw [show e (e.symm u) = u from e.apply_symm_apply u]
  have hbsum : ∀ eu : R324RefinedContractionIndex p,
      Summable fun b : ℕ => g (eu, b) := by
    intro eu
    have := (r324NatEquivStandardConfigurations hm).summable_iff.mpr
      hpisum
    exact this.congr fun b => rfl
  have hgsum : Summable g := by
    rw [summable_prod_of_nonneg hg0]
    refine ⟨hbsum, Summable.of_finite⟩
  have hbval : ∀ eu : R324RefinedContractionIndex p,
      (∑' b : ℕ, g (eu, b)) ≤ M ^ m := by
    intro eu
    calc
      (∑' b : ℕ, g (eu, b)) =
          ∑' q : Fin m → Z4, ∏ i, F (q i) :=
        (r324NatEquivStandardConfigurations hm).tsum_eq
          (fun q : Fin m → Z4 => ∏ i, F (q i))
      _ ≤ M ^ m := hpile
  have hM0 : 0 ≤ M ^ m :=
    le_trans (tsum_nonneg fun q => Finset.prod_nonneg
      fun i _ => hF0 _) hpile
  calc
    (∑' a : ℕ, ρ.r324RefinedRawCovarianceWeight hm ε p a) =
        ∑' u : R324RefinedContractionIndex p × ℕ,
          ρ.r324RefinedRawCovarianceWeight hm ε p (e.symm u) :=
      (e.symm.tsum_eq
        (ρ.r324RefinedRawCovarianceWeight hm ε p)).symm
    _ = ∑' u : R324RefinedContractionIndex p × ℕ, g u :=
      tsum_congr hgf
    _ = ∑' eu : R324RefinedContractionIndex p,
          ∑' b : ℕ, g (eu, b) :=
      hgsum.tsum_prod' hbsum
    _ = ∑ eu : R324RefinedContractionIndex p,
          ∑' b : ℕ, g (eu, b) :=
      tsum_fintype _
    _ ≤ ∑ _eu : R324RefinedContractionIndex p, M ^ m :=
      Finset.sum_le_sum fun eu _ => hbval eu
    _ = (Nat.card (R324RefinedContractionIndex p) : ℝ) * M ^ m := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card]

/-- The grouped zero-shift mass ledger at `m ≤ 2`: the complete
grouped `L¹` ledger is priced by the raw covariance mass
`K·ε^{-4m}`. -/
theorem r324RoutedEval_zeroShift_ledger
    (ρ : SmoothCutoff)
    {m : ℕ} (hm : 0 < m) (hm2 : m ≤ 2) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (lam : ℝ) {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ α β : Z4,
        (∑' pb : R324RefinedScheduleIndex m × ℕ,
          ρ.r324ZeroShiftGroupedWeight lam hm ε α β pb) ≤
          (16 * paperFourthOrderModeDecay α *
              paperFourthOrderModeDecay β) *
            (|lamEps lam ε| ^ (2 * m) *
              (K * ε⁻¹ ^ (4 * m))) := by
  obtain ⟨CV, hCV, hmass⟩ := r324RoutedEval_covarianceMass_le ρ
  set K0 : ℝ :=
    ∑ p : R324RefinedScheduleIndex m,
      r324RefinedInteriorSkeletonL1 p *
        (Nat.card (SmoothCutoff.R324RefinedContractionIndex p) : ℝ)
    with hK0def
  have hK00 : 0 ≤ K0 := by
    rw [hK0def]
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (r324RefinedInteriorSkeletonL1_nonneg p)
        (Nat.cast_nonneg _)
  refine ⟨K0 * CV ^ m, by positivity, ?_⟩
  intro lam ε hε hε1 α β
  set dd : ℝ :=
    16 * paperFourthOrderModeDecay α *
      paperFourthOrderModeDecay β with hdddef
  have hdd0 : 0 ≤ dd := by
    rw [hdddef]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (paperFourthOrderModeDecay_nonneg α))
      (paperFourthOrderModeDecay_nonneg β)
  have hlam0 : (0:ℝ) ≤ |lamEps lam ε| ^ (2 * m) :=
    pow_nonneg (abs_nonneg _) _
  -- summable majorant for the grouped `L¹` ledger
  have hKGW : ∀ p : R324RefinedScheduleIndex m,
      Summable fun b : ℕ =>
        r324RefinedInteriorSkeletonL1 p *
          ρ.r324KeyGroupedRefinedCovarianceWeight hm ε p b :=
    fun p =>
      (ρ.summable_r324KeyGroupedRefinedCovarianceWeight
        hm hε p).mul_left _
  have hmajS :
      Summable fun pb : R324RefinedScheduleIndex m × ℕ =>
        r324RefinedInteriorSkeletonL1 pb.1 *
          ρ.r324KeyGroupedRefinedCovarianceWeight
            hm ε pb.1 pb.2 := by
    rw [summable_prod_of_nonneg (fun pb =>
      mul_nonneg (r324RefinedInteriorSkeletonL1_nonneg pb.1)
        (ρ.r324KeyGroupedRefinedCovarianceWeight_nonneg
          hm ε pb.1 pb.2))]
    exact ⟨fun p => hKGW p, Summable.of_finite⟩
  have hCore0 : ∀ pb : R324RefinedScheduleIndex m × ℕ,
      0 ≤ ρ.r324GroupedRefinedCoreL1 hm ε pb :=
    fun pb => ρ.r324GroupedRefinedCoreL1_nonneg hm ε pb
  have hCoreMaj : ∀ pb : R324RefinedScheduleIndex m × ℕ,
      ρ.r324GroupedRefinedCoreL1 hm ε pb ≤
        r324RefinedInteriorSkeletonL1 pb.1 *
          ρ.r324KeyGroupedRefinedCovarianceWeight
            hm ε pb.1 pb.2 :=
    fun pb =>
      ρ.r324GroupedRefinedCoreL1_le_skeleton_mul_covariance
        hm hε pb.1 pb.2
  have hCoreS :
      Summable fun pb : R324RefinedScheduleIndex m × ℕ =>
        ρ.r324GroupedRefinedCoreL1 hm ε pb :=
    hmajS.of_nonneg_of_le hCore0 hCoreMaj
  -- the total grouped `L¹` mass
  have hCoreTotal :
      (∑' pb : R324RefinedScheduleIndex m × ℕ,
        ρ.r324GroupedRefinedCoreL1 hm ε pb) ≤
        K0 * (CV * ε⁻¹ ^ (4 : ℕ)) ^ m := by
    have hperp : ∀ p : R324RefinedScheduleIndex m,
        (∑' b : ℕ,
          ρ.r324GroupedRefinedCoreL1 hm ε (p, b)) ≤
          r324RefinedInteriorSkeletonL1 p *
            ((Nat.card
                (SmoothCutoff.R324RefinedContractionIndex p) : ℝ) *
              (CV * ε⁻¹ ^ (4 : ℕ)) ^ m) := by
      intro p
      have hKGWsum :
          (∑' b : ℕ,
            ρ.r324KeyGroupedRefinedCovarianceWeight hm ε p b) =
            ∑' a : ℕ,
              ρ.r324RefinedRawCovarianceWeight hm ε p a := by
        calc
          (∑' b : ℕ,
              ρ.r324KeyGroupedRefinedCovarianceWeight hm ε p b) =
              ∑' k : Fin m → Z4,
                tsumByKey
                  (ρ.r324RefinedRawCovarianceWeight hm ε p)
                  (r324RefinedRawIncrementKey hm p) k :=
            (r324NatEquivStandardConfigurations hm).tsum_eq
              (tsumByKey
                (ρ.r324RefinedRawCovarianceWeight hm ε p)
                (r324RefinedRawIncrementKey hm p))
          _ = ∑' a : ℕ,
                ρ.r324RefinedRawCovarianceWeight hm ε p a :=
            tsum_tsumByKey _ _
              (ρ.summable_r324RefinedRawCovarianceWeight hm hε p)
      calc
        (∑' b : ℕ,
            ρ.r324GroupedRefinedCoreL1 hm ε (p, b)) ≤
            ∑' b : ℕ,
              r324RefinedInteriorSkeletonL1 p *
                ρ.r324KeyGroupedRefinedCovarianceWeight
                  hm ε p b :=
          (hCoreS.prod_factor p).tsum_le_tsum
            (fun b => hCoreMaj (p, b)) (hKGW p)
        _ = r324RefinedInteriorSkeletonL1 p *
              ∑' b : ℕ,
                ρ.r324KeyGroupedRefinedCovarianceWeight
                  hm ε p b := by
          rw [tsum_mul_left]
        _ ≤ r324RefinedInteriorSkeletonL1 p *
              ((Nat.card
                  (SmoothCutoff.R324RefinedContractionIndex
                    p) : ℝ) *
                (CV * ε⁻¹ ^ (4 : ℕ)) ^ m) := by
          refine mul_le_mul_of_nonneg_left ?_
            (r324RefinedInteriorSkeletonL1_nonneg p)
          rw [hKGWsum]
          exact
            ρ.r324RoutedEval_tsum_rawCovWeight_le hm hm2 hε
              (hmass hε hε1) p
    calc
      (∑' pb : R324RefinedScheduleIndex m × ℕ,
          ρ.r324GroupedRefinedCoreL1 hm ε pb) =
          ∑' p : R324RefinedScheduleIndex m,
            ∑' b : ℕ,
              ρ.r324GroupedRefinedCoreL1 hm ε (p, b) :=
        hCoreS.tsum_prod' fun p => hCoreS.prod_factor p
      _ = ∑ p : R324RefinedScheduleIndex m,
            ∑' b : ℕ,
              ρ.r324GroupedRefinedCoreL1 hm ε (p, b) :=
        tsum_fintype _
      _ ≤ ∑ p : R324RefinedScheduleIndex m,
            r324RefinedInteriorSkeletonL1 p *
              ((Nat.card
                  (SmoothCutoff.R324RefinedContractionIndex
                    p) : ℝ) *
                (CV * ε⁻¹ ^ (4 : ℕ)) ^ m) :=
        Finset.sum_le_sum fun p _ => hperp p
      _ = K0 * (CV * ε⁻¹ ^ (4 : ℕ)) ^ m := by
        rw [hK0def, Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => by ring
  -- assemble
  calc
    (∑' pb : R324RefinedScheduleIndex m × ℕ,
        ρ.r324ZeroShiftGroupedWeight lam hm ε α β pb) =
        dd * (|lamEps lam ε| ^ (2 * m) *
          ∑' pb : R324RefinedScheduleIndex m × ℕ,
            ρ.r324GroupedRefinedCoreL1 hm ε pb) := by
      rw [← tsum_mul_left, ← tsum_mul_left]
      exact tsum_congr fun pb => by
        unfold SmoothCutoff.r324ZeroShiftGroupedWeight
          SmoothCutoff.r324ZeroShiftGroupedCoreWeight
        rw [hdddef]
    _ ≤ dd * (|lamEps lam ε| ^ (2 * m) *
          (K0 * (CV * ε⁻¹ ^ (4 : ℕ)) ^ m)) := by
      refine mul_le_mul_of_nonneg_left ?_ hdd0
      exact mul_le_mul_of_nonneg_left hCoreTotal hlam0
    _ = dd * (|lamEps lam ε| ^ (2 * m) *
          ((K0 * CV ^ m) * ε⁻¹ ^ (4 * m))) := by
      rw [mul_pow, pow_mul]
      ring
    _ = (16 * paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β) *
          (|lamEps lam ε| ^ (2 * m) *
            ((K0 * CV ^ m) * ε⁻¹ ^ (4 * m))) := by
      rw [hdddef]

end SmoothCutoff

/-- **The zero-shift routed window ledger holds at order one.** -/
theorem exists_r324RoutedZeroShiftWindowBound_one
    (ρ : SmoothCutoff) (lam : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      R324RoutedZeroShiftWindowBound ρ lam 1 C := by
  obtain ⟨K, hK0, hledger⟩ :=
    ρ.r324RoutedEval_zeroShift_ledger one_pos one_le_two
  refine ⟨K + 1, by positivity, ?_⟩
  intro hm ε hε hε1 hlog _hmtrunc α β _hshift
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

/-- **The zero-shift routed window ledger holds at order two.** -/
theorem exists_r324RoutedZeroShiftWindowBound_two
    (ρ : SmoothCutoff) (lam : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      R324RoutedZeroShiftWindowBound ρ lam 2 C := by
  obtain ⟨K, hK0, hledger⟩ :=
    ρ.r324RoutedEval_zeroShift_ledger two_pos le_rfl
  refine ⟨K + 1, by positivity, ?_⟩
  intro hm ε hε hε1 hlog _hmtrunc α β _hshift
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
  have hp : (0:ℝ) ≤ ε⁻¹ ^ (8 : ℕ) := by positivity
  have hKC : K ≤ (K + 1) ^ 2 * |Real.log ε| ^ (2 - 1) := by
    have h1 : (1:ℝ) ≤ |Real.log ε| ^ (2 - 1) := by
      simpa using hlog
    have h2 : K ≤ (K + 1) ^ 2 := by nlinarith
    calc
      K ≤ (K + 1) ^ 2 := h2
      _ = (K + 1) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (K + 1) ^ 2 * |Real.log ε| ^ (2 - 1) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
  calc
    K * ε⁻¹ ^ (4 * 2) = K * ε⁻¹ ^ (8 : ℕ) := by norm_num
    _ ≤ ((K + 1) ^ 2 * |Real.log ε| ^ (2 - 1)) *
          ε⁻¹ ^ (8 : ℕ) :=
      mul_le_mul_of_nonneg_right hKC hp
    _ = (K + 1) ^ 2 * |Real.log ε| ^ (2 - 1) *
          ε⁻¹ ^ (8 : ℕ) := by ring

/-- One-slot configuration sums collapse to plain lattice sums. -/
theorem r324RoutedEval_tsum_finOne
    {H : Z4 → ℝ} (hH : Summable H) :
    (Summable fun q : Fin 1 → Z4 => H (q 0)) ∧
      (∑' q : Fin 1 → Z4, H (q 0)) = ∑' k : Z4, H k := by
  constructor
  · exact (Equiv.funUnique (Fin 1) Z4).summable_iff.mpr hH
  · exact (Equiv.funUnique (Fin 1) Z4).tsum_eq H

namespace SmoothCutoff

/-- **The endpoint-constrained order-one route mass.**  At `m = 1`
frequency conservation of endpoint-nonzero configurations pins the
single increment key to `α + β`, hence the slot mode to `±(α + β)`;
the surviving routed mass is the contraction-fibre cardinality times
twice the marked slot value. -/
theorem r324RoutedEval_nonzeroMass_one
    (ρ : SmoothCutoff) (hm : 0 < 1) {ε CB : ℝ} (hε : 0 < ε)
    (hCB : ∀ k : Z4,
      (1 + ‖z4EuclideanFrequency k‖ ^ 2) ^ 4 *
        ‖ρ.covarianceModeCoeff ε k‖ ≤ CB)
    (α β : Z4) (hexternal : α + β ≠ 0)
    (p : R324RefinedScheduleIndex 1) :
    (∑' a :
        ρ.R324RefinedEndpointNonzeroRawConfiguration hm ε α β p,
      ρ.r324RefinedRawCovarianceRouteWeight hm ε p a.1) ≤
      (Nat.card (R324RefinedContractionIndex p) : ℝ) *
        (2 * CB) := by
  classical
  have hCB0 : 0 ≤ CB :=
    le_trans (mul_nonneg (by positivity) (norm_nonneg _)) (hCB 0)
  -- the key of every endpoint-nonzero configuration is pinned
  have hkey_forced : ∀ a : ℕ,
      ρ.r324RefinedRawFullPairingIntegral hm ε α β p a ≠ 0 →
      r324RoutedEvalSlotMode hm p a 0 = α + β ∨
        r324RoutedEvalSlotMode hm p a 0 = -(α + β) := by
    intro a hne
    have hneF :
        ρ.r324RefinedRawFourierIntegral hm ε α β p a ≠ 0 := by
      rw [ρ.r324RefinedRawFourierIntegral_eq_rawFullPairingIntegral
        hm ε α β p a]
      exact hne
    have hcons :=
      ρ.sum_r324RefinedRawIncrementKey_eq_external_of_ne_zero
        hm ε α β p a hneF
    rw [Fin.sum_univ_one] at hcons
    have hkey : r324RefinedRawIncrementKey hm p a 0 = α + β :=
      z4EuclideanFrequency_injective hcons
    rcases r324RoutedEval_incrementKey_cases hm p a 0
      with h | h | h
    · exact absurd (hkey.symm.trans h) hexternal
    · exact Or.inl (h.symm.trans hkey)
    · refine Or.inr ?_
      have := h.symm.trans hkey
      rw [neg_eq_iff_eq_neg] at this
      exact this
  -- the pinned-slot majorant on all raw configurations
  set G : ℕ → ℝ := fun n =>
    if r324RoutedEvalSlotMode hm p n 0 = α + β ∨
        r324RoutedEvalSlotMode hm p n 0 = -(α + β) then
      ρ.r324RefinedRawCovarianceRouteWeight hm ε p n
    else 0 with hGdef
  have hG0 : ∀ n, 0 ≤ G n := by
    intro n
    simp only [hGdef]
    split_ifs
    · exact ρ.r324RefinedRawCovarianceRouteWeight_nonneg hm ε p n
    · exact le_rfl
  have hGle : ∀ n,
      G n ≤ ρ.r324RefinedRawCovarianceRouteWeight hm ε p n := by
    intro n
    simp only [hGdef]
    split_ifs
    · exact le_rfl
    · exact ρ.r324RefinedRawCovarianceRouteWeight_nonneg hm ε p n
  have hGsum : Summable G :=
    (ρ.summable_r324RefinedRawCovarianceRouteWeight
      hm hε p).of_nonneg_of_le hG0 hGle
  -- step 1: pass from the endpoint-nonzero subtype to `G`
  have hstep1 :
      (∑' a :
          ρ.R324RefinedEndpointNonzeroRawConfiguration
            hm ε α β p,
        ρ.r324RefinedRawCovarianceRouteWeight hm ε p a.1) ≤
        ∑' n : ℕ, G n := by
    have hcongr : ∀ a :
        ρ.R324RefinedEndpointNonzeroRawConfiguration
          hm ε α β p,
        ρ.r324RefinedRawCovarianceRouteWeight hm ε p a.1 =
          G a.1 := by
      intro a
      simp only [hGdef]
      rw [if_pos (hkey_forced a.1 a.2)]
    calc
      (∑' a :
          ρ.R324RefinedEndpointNonzeroRawConfiguration
            hm ε α β p,
        ρ.r324RefinedRawCovarianceRouteWeight hm ε p a.1) =
          ∑' a :
            ρ.R324RefinedEndpointNonzeroRawConfiguration
              hm ε α β p, G a.1 :=
        tsum_congr hcongr
      _ = ∑' n : ℕ,
            Set.indicator
              {n : ℕ |
                ρ.r324RefinedRawFullPairingIntegral
                  hm ε α β p n ≠ 0} G n :=
        tsum_subtype _ G
      _ ≤ ∑' n : ℕ, G n :=
        (hGsum.indicator _).tsum_le_tsum
          (fun n => Set.indicator_le_self'
            (fun n _ => hG0 n) n) hGsum
  refine hstep1.trans ?_
  -- step 2: evaluate `G` through the contraction/configuration split
  set e := r324NatEquivRefinedContractionConfigurations p
  set H : Z4 → ℝ := fun k =>
    if k = α + β ∨ k = -(α + β) then
      ‖ρ.covarianceModeCoeff ε k‖ *
        (1 + ‖z4EuclideanFrequency k‖ ^ 2) ^ 4
    else 0 with hHdef
  have hH0 : ∀ k, 0 ≤ H k := by
    intro k
    simp only [hHdef]
    split_ifs
    · positivity
    · exact le_rfl
  have hHvanish : ∀ k : Z4,
      k ∉ ({α + β, -(α + β)} : Finset Z4) → H k = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    simp only [hHdef]
    rw [if_neg]
    intro hcase
    rcases hcase with h | h
    · exact hk (Or.inl h)
    · exact hk (Or.inr h)
  have hHsum : Summable H :=
    summable_of_ne_finset_zero hHvanish
  obtain ⟨hHq, hHqeq⟩ := r324RoutedEval_tsum_finOne hHsum
  have hHb0 :=
    (r324NatEquivStandardConfigurations hm).summable_iff.mpr hHq
  have hHb : Summable fun b : ℕ =>
      H (r324NatEquivStandardConfigurations hm b 0) :=
    hHb0.congr fun b => rfl
  have hHu : Summable fun u : R324RefinedContractionIndex p × ℕ =>
      H (r324NatEquivStandardConfigurations hm u.2 0) := by
    rw [summable_prod_of_nonneg (fun u => hH0 _)]
    exact ⟨fun _ => hHb, Summable.of_finite⟩
  have hslot : ∀ u : R324RefinedContractionIndex p × ℕ,
      r324RoutedEvalSlotMode hm p (e.symm u) 0 =
        r324NatEquivStandardConfigurations hm u.2 0 := by
    intro u
    unfold r324RoutedEvalSlotMode
    rw [show e (e.symm u) = u from e.apply_symm_apply u]
  have hGH : ∀ u : R324RefinedContractionIndex p × ℕ,
      G (e.symm u) ≤
        H (r324NatEquivStandardConfigurations hm u.2 0) := by
    intro u
    simp only [hGdef, hHdef]
    rw [hslot u]
    split_ifs with hcase
    · have hkeycost :
          r324IncrementKeyCost
              (r324RefinedRawIncrementKey hm p (e.symm u)) ≤
            (1 + ‖z4EuclideanFrequency
              (r324NatEquivStandardConfigurations
                hm u.2 0)‖ ^ 2) ^ 4 := by
        unfold r324IncrementKeyCost
        rw [Fin.sum_univ_one]
        rw [← hslot u]
        exact r324RoutedEval_keyCost_le_modeCost hm p (e.symm u) 0
      have hcov :
          ρ.r324RefinedRawCovarianceWeight hm ε p (e.symm u) =
            ‖ρ.covarianceModeCoeff ε
              (r324NatEquivStandardConfigurations hm u.2 0)‖ := by
        rw [ρ.r324RoutedEval_covWeight_eq_prod hm ε p (e.symm u),
          Fin.prod_univ_one, hslot u]
      unfold r324RefinedRawCovarianceRouteWeight
      rw [hcov]
      exact mul_le_mul_of_nonneg_left hkeycost (norm_nonneg _)
    · exact le_rfl
  have hGesum0 := e.symm.summable_iff.mpr hGsum
  have hGesum : Summable fun u :
      R324RefinedContractionIndex p × ℕ => G (e.symm u) :=
    hGesum0.congr fun u => rfl
  have hHkval : (∑' k : Z4, H k) ≤ 2 * CB := by
    rw [tsum_eq_sum (s := ({α + β, -(α + β)} : Finset Z4))
      hHvanish]
    have hterm : ∀ k ∈ ({α + β, -(α + β)} : Finset Z4),
        H k ≤ CB := by
      intro k _hk
      simp only [hHdef]
      split_ifs
      · rw [mul_comm]
        exact hCB k
      · exact hCB0
    calc
      (∑ k ∈ ({α + β, -(α + β)} : Finset Z4), H k) ≤
          ∑ _k ∈ ({α + β, -(α + β)} : Finset Z4), CB :=
        Finset.sum_le_sum hterm
      _ = (({α + β, -(α + β)} : Finset Z4).card : ℝ) * CB := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * CB := by
        refine mul_le_mul_of_nonneg_right ?_ hCB0
        have hcard :
            ({α + β, -(α + β)} : Finset Z4).card ≤ 2 :=
          le_trans (Finset.card_insert_le _ _) (by simp)
        exact_mod_cast hcard
  have hqcollapse :
      (∑' b : ℕ,
        H (r324NatEquivStandardConfigurations hm b 0)) =
        ∑' k : Z4, H k := by
    calc
      (∑' b : ℕ,
          H (r324NatEquivStandardConfigurations hm b 0)) =
          ∑' q : Fin 1 → Z4, H (q 0) :=
        (r324NatEquivStandardConfigurations hm).tsum_eq
          (fun q : Fin 1 → Z4 => H (q 0))
      _ = ∑' k : Z4, H k := hHqeq
  calc
    (∑' n : ℕ, G n) =
        ∑' u : R324RefinedContractionIndex p × ℕ,
          G (e.symm u) :=
      (e.symm.tsum_eq G).symm
    _ ≤ ∑' u : R324RefinedContractionIndex p × ℕ,
          H (r324NatEquivStandardConfigurations hm u.2 0) :=
      hGesum.tsum_le_tsum hGH hHu
    _ = ∑' eu : R324RefinedContractionIndex p,
          ∑' b : ℕ,
            H (r324NatEquivStandardConfigurations hm b 0) :=
      hHu.tsum_prod' fun eu => hHb
    _ = ∑ eu : R324RefinedContractionIndex p,
          ∑' b : ℕ,
            H (r324NatEquivStandardConfigurations hm b 0) :=
      tsum_fintype _
    _ ≤ ∑ _eu : R324RefinedContractionIndex p, 2 * CB := by
      refine Finset.sum_le_sum fun eu _ => ?_
      rw [hqcollapse]
      exact hHkval
    _ = (Nat.card (R324RefinedContractionIndex p) : ℝ) *
          (2 * CB) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card]

/-- Per-schedule routed weight ledger at `m = 1`: the corrected route
weights of one refined schedule are worth the skeleton envelope times
the endpoint-constrained mass. -/
theorem r324RoutedEval_perSchedule_one
    (ρ : SmoothCutoff) (lam : ℝ) (hm : 0 < 1)
    {ε CB : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCB : ∀ k : Z4,
      (1 + ‖z4EuclideanFrequency k‖ ^ 2) ^ 4 *
        ‖ρ.covarianceModeCoeff ε k‖ ≤ CB)
    (α β : Z4) (hexternal : α + β ≠ 0)
    (hmtrunc : 1 ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex 1) :
    (∑' route : R324NonzeroRouteLabel 1,
      ρ.r324RefinedEndpointNonzeroRouteWeight
        lam hm ε α β hexternal hε hε1 hmtrunc p route) ≤
      16 * paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β *
        (|lamEps lam ε| ^ (2 * 1) *
          (r324AllContractionInteriorSkeletonL1 1 *
            ((Nat.card (R324RefinedContractionIndex p) : ℝ) *
              (2 * CB)))) := by
  have hmajp :=
    ρ.summable_r324RefinedEndpointNonzeroRouteRawMajorant
      lam hm hε α β hexternal hε1 hmtrunc p
  have hwp :
      Summable fun route : R324NonzeroRouteLabel 1 =>
        ρ.r324RefinedEndpointNonzeroRouteWeight
          lam hm ε α β hexternal hε hε1 hmtrunc p route :=
    hmajp.of_nonneg_of_le
      (fun route =>
        ρ.r324RefinedEndpointNonzeroRouteWeight_nonneg
          lam hm ε α β hexternal hε hε1 hmtrunc p route)
      (fun route =>
        ρ.r324RefinedEndpointNonzeroRouteWeight_le_rawMajorant
          lam hm hε α β hexternal hε1 hmtrunc p route)
  have hfib :
      Summable fun a :
          ρ.R324RefinedEndpointNonzeroRawConfiguration
            hm ε α β p =>
        ρ.r324RefinedRawCovarianceRouteWeight hm ε p a.1 :=
    (ρ.summable_r324RefinedRawCovarianceRouteWeight
      hm hε p).subtype _
  have hfibre_eq :
      (∑' route : R324NonzeroRouteLabel 1,
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
  have hmass :=
    ρ.r324RoutedEval_nonzeroMass_one hm hε hCB α β hexternal p
  calc
    (∑' route : R324NonzeroRouteLabel 1,
        ρ.r324RefinedEndpointNonzeroRouteWeight
          lam hm ε α β hexternal hε hε1 hmtrunc p route) ≤
        ∑' route : R324NonzeroRouteLabel 1,
          ρ.r324RefinedEndpointNonzeroRouteRawMajorant
            lam hm ε α β hexternal hε hε1 hmtrunc p route :=
      hwp.tsum_le_tsum
        (fun route =>
          ρ.r324RefinedEndpointNonzeroRouteWeight_le_rawMajorant
            lam hm hε α β hexternal hε1 hmtrunc p route)
        hmajp
    _ = 16 * paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β *
          (|lamEps lam ε| ^ (2 * 1) *
            (r324AllContractionInteriorSkeletonL1 1 *
              ∑' route : R324NonzeroRouteLabel 1,
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
          (|lamEps lam ε| ^ (2 * 1) *
            (r324AllContractionInteriorSkeletonL1 1 *
              ((Nat.card (R324RefinedContractionIndex p) : ℝ) *
                (2 * CB)))) := by
      rw [hfibre_eq]
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (paperFourthOrderModeDecay_nonneg α))
          (paperFourthOrderModeDecay_nonneg β))
      refine mul_le_mul_of_nonneg_left ?_
        (pow_nonneg (abs_nonneg _) _)
      exact mul_le_mul_of_nonneg_left hmass
        (r324AllContractionInteriorSkeletonL1_nonneg 1)

end SmoothCutoff

/-- **The routed per-term window ledger holds at order one.**  The
constant depends only on the cutoff. -/
theorem exists_r324RoutedPerTermWindowBound_one
    (ρ : SmoothCutoff) (lam : ℝ) :
    ∃ C : ℝ, 0 < C ∧
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
  refine ⟨K1 + 1, by positivity, ?_⟩
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

end

end Anderson4D
