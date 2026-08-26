import Anderson4D.DetParametrix.Paper42_Moment.R324CountableConfigurations
import Anderson4D.DetParametrix.Paper42_Moment.R324FrequencyRoutingClosure
import Anderson4D.Continuum.CutoffFourierSummability

/-!
# Summable routed weights for one R-324 full pairing

For one full doubled pairing, every Fourier configuration has exactly
`m` signed covariance-mode increments.  This file attaches to the
configuration its physical `L¹` norm times the sum of the inverse
eighth-order decays of those increments.  Only one covariance slot is
polynomially weighted at a time, so the construction pays one
degree-eight cutoff loss rather than an incorrect product of `m` such
losses.

Zero integrated configurations are harmless analytically, but the
downstream routing structure asks for exact frequency conservation for
every enumerated term.  Their increments are therefore replaced by one
external increment followed by zeros.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## Polynomial control of one routed increment -/

/-- The exact reciprocal cost of one eighth-order routed decay. -/
def r324PairDecayCost
    {m : ℕ}
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q : Fin m → Z4) (i : Fin m) : ℝ :=
  (1 + ‖r324StandardPairIncrement κ q i‖ ^ 2) ^ 4

theorem r324PairDecayCost_pos
    {m : ℕ}
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q : Fin m → Z4) (i : Fin m) :
    0 < r324PairDecayCost κ q i := by
  unfold r324PairDecayCost
  positivity

theorem r324PairDecayCost_mul_decay
    {m : ℕ}
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q : Fin m → Z4) (i : Fin m) :
    r324PairDecayCost κ q i *
        eighthOrderFrequencyDecay
          ‖r324StandardPairIncrement κ q i‖ =
      1 := by
  unfold r324PairDecayCost eighthOrderFrequencyDecay
  have h :
      (1 + ‖r324StandardPairIncrement κ q i‖ ^ 2) ^ 4 ≠ 0 := by
    positivity
  exact mul_inv_cancel₀ h

/-- A signed left-copy contribution is either `q i`, `-q i`, or zero. -/
theorem norm_r324StandardPairIncrement_le_mode
    {m : ℕ}
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q : Fin m → Z4) (i : Fin m) :
    ‖r324StandardPairIncrement κ q i‖ ≤
      ‖z4EuclideanFrequency (q i)‖ := by
  let a :=
    (r324PairFinEquiv κ.1
      (r324FullPairIndexEquiv κ i)).1
  by_cases ha : a.val < m
  · by_cases hκa : (κ.1 a).val < m
    · simp [r324StandardPairIncrement,
        r324LeftPairModeContribution,
        r324FullConfigurationOfStandard, a, ha, hκa]
      change ‖z4EuclideanFrequencyAddHom 0‖ ≤
        ‖z4EuclideanFrequencyAddHom (q i)‖
      simp
    · simp [r324StandardPairIncrement,
        r324LeftPairModeContribution,
        r324FullConfigurationOfStandard, a, ha, hκa]
      change ‖z4EuclideanFrequencyAddHom (-q i)‖ ≤
        ‖z4EuclideanFrequencyAddHom (q i)‖
      rw [map_neg, norm_neg]
  · by_cases hκa : (κ.1 a).val < m
    · simp [r324StandardPairIncrement,
        r324LeftPairModeContribution,
        r324FullConfigurationOfStandard, a, ha, hκa]
    · simp [r324StandardPairIncrement,
        r324LeftPairModeContribution,
        a, ha, hκa]
      change ‖z4EuclideanFrequencyAddHom 0‖ ≤
        ‖z4EuclideanFrequencyAddHom (q i)‖
      simp

/-- The raw Euclidean lattice norm is controlled by twice the
coordinatewise polynomial base. -/
theorem norm_z4EuclideanFrequency_le_two_mul_latticeBase
    (k : Z4) :
    ‖z4EuclideanFrequency k‖ ≤
      2 * ∑ i, ((Int.natAbs (k i) : ℝ) + 1) := by
  let S : ℝ := ∑ i, ((Int.natAbs (k i) : ℝ) + 1)
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun i _ => by positivity
  have hcoord (i : Fin dim) :
      (k i : ℝ) ^ 2 ≤ S ^ 2 := by
    have hi :
        (Int.natAbs (k i) : ℝ) + 1 ≤ S := by
      dsimp only [S]
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j : Fin dim =>
          (Int.natAbs (k j) : ℝ) + 1)
        (fun j _ => by positivity) (Finset.mem_univ i)
    have habs :
        |(k i : ℝ)| = (Int.natAbs (k i) : ℝ) := by
      calc
        |(k i : ℝ)| = ((|(k i)| : ℤ) : ℝ) :=
          (Int.cast_abs (R := ℝ)).symm
        _ = ((((k i).natAbs : ℕ) : ℤ) : ℝ) :=
          congrArg (fun z : ℤ => (z : ℝ))
            (Int.natCast_natAbs (k i)).symm
        _ = ((k i).natAbs : ℝ) := by norm_num
    have hki : |(k i : ℝ)| ≤ S := by
      rw [habs]
      linarith
    nlinarith [sq_nonneg (|(k i : ℝ)|),
      sq_abs (k i : ℝ)]
  have hsum :
      paperModeNormSq k ≤ 4 * S ^ 2 := by
    unfold paperModeNormSq
    calc
      (∑ i : Fin dim, (k i : ℝ) ^ 2) ≤
          ∑ _i : Fin dim, S ^ 2 :=
        Finset.sum_le_sum fun i _ => hcoord i
      _ = 4 * S ^ 2 := by simp [dim]
  have hsq :
      ‖z4EuclideanFrequency k‖ ^ 2 ≤ (2 * S) ^ 2 := by
    rw [norm_sq_z4EuclideanFrequency]
    nlinarith
  nlinarith [norm_nonneg (z4EuclideanFrequency k)]

/-- One reciprocal routed decay is bounded by a fixed multiple of the
degree-eight lattice weight of the corresponding covariance mode. -/
theorem r324PairDecayCost_le_latticePolynomialWeight
    {m : ℕ}
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q : Fin m → Z4) (i : Fin m) :
    r324PairDecayCost κ q i ≤
      625 * latticePolynomialWeight 8 (q i) := by
  let S : ℝ :=
    ∑ j, ((Int.natAbs (q i j) : ℝ) + 1)
  have hS : 1 ≤ S := by
    have hterm :
        (1 : ℝ) ≤
          (Int.natAbs (q i (0 : Fin dim)) : ℝ) + 1 := by
      have h :
          0 ≤ (Int.natAbs (q i (0 : Fin dim)) : ℝ) := by
        positivity
      linarith
    have hsingle :
        (Int.natAbs (q i (0 : Fin dim)) : ℝ) + 1 ≤ S := by
      dsimp only [S]
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j : Fin dim =>
          (Int.natAbs (q i j) : ℝ) + 1)
        (fun j _ => by positivity)
        (Finset.mem_univ (0 : Fin dim))
    exact hterm.trans hsingle
  have hinc :
      ‖r324StandardPairIncrement κ q i‖ ≤ 2 * S := by
    exact (norm_r324StandardPairIncrement_le_mode κ q i).trans
      (by
        simpa only [S] using
          norm_z4EuclideanFrequency_le_two_mul_latticeBase (q i))
  have hbase :
      1 + ‖r324StandardPairIncrement κ q i‖ ^ 2 ≤
        5 * S ^ 2 := by
    nlinarith [norm_nonneg
      (r324StandardPairIncrement κ q i)]
  unfold r324PairDecayCost latticePolynomialWeight
  change
    (1 + ‖r324StandardPairIncrement κ q i‖ ^ 2) ^ 4 ≤
      625 * S ^ 8
  calc
    (1 + ‖r324StandardPairIncrement κ q i‖ ^ 2) ^ 4 ≤
        (5 * S ^ 2) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hbase 4
    _ = 625 * S ^ 8 := by ring

/-! ## A single polynomially weighted covariance slot -/

/-- The covariance coefficient remains summable after one degree-eight
lattice weight is inserted. -/
theorem summable_latticePolynomialWeight_mul_norm_covarianceModeCoeff
    {ε : ℝ} (hε : 0 < ε) :
    Summable fun k : Z4 =>
      latticePolynomialWeight 8 k *
        ‖ρ.covarianceModeCoeff ε k‖ := by
  let C : ℝ :=
    ‖(NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2‖
  have hmajor :
      Summable fun k : Z4 =>
        C *
          (latticePolynomialWeight 8 k *
            ‖ρ.symbol ε k‖) :=
    (ρ.summable_latticePolynomialWeight_mul_norm_symbol
      8 hε).mul_left C
  refine hmajor.of_nonneg_of_le
    (fun k => mul_nonneg
      (latticePolynomialWeight_nonneg 8 k)
      (norm_nonneg _)) ?_
  intro k
  have hsymbol := ρ.norm_symbol_le_one ε k
  have hsq :
      ‖ρ.symbol ε k‖ ^ 2 ≤ ‖ρ.symbol ε k‖ := by
    nlinarith [norm_nonneg (ρ.symbol ε k)]
  unfold covarianceModeCoeff
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  dsimp only [C]
  calc
    latticePolynomialWeight 8 k *
          (‖(NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2‖ *
            ‖ρ.symbol ε k‖ ^ 2)
        ≤ latticePolynomialWeight 8 k *
            (‖(NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2‖ *
              ‖ρ.symbol ε k‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsq (norm_nonneg _))
        (latticePolynomialWeight_nonneg 8 k)
    _ = ‖(NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2‖ *
          (latticePolynomialWeight 8 k *
            ‖ρ.symbol ε k‖) := by ring

/-- After standardizing the pair enumeration, weighting any one
covariance slot by a degree-eight lattice polynomial preserves
summability of the full configuration product. -/
theorem summable_standardConfigurationWeight_mul_latticePolynomialWeight
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (i : Fin m) :
    Summable fun q : Fin m → Z4 =>
      ρ.r324CovarianceConfigurationWeight ε κ.1
          (r324FullConfigurationOfStandard κ q) *
        latticePolynomialWeight 8 (q i) := by
  let f : Fin m → Z4 → ℂ := fun j k =>
    ((‖ρ.covarianceModeCoeff ε k‖ *
      if j = i then latticePolynomialWeight 8 k else 1 : ℝ) : ℂ)
  have hf :
      ∀ j, Summable fun k : Z4 => ‖f j k‖ := by
    intro j
    by_cases hji : j = i
    · subst j
      exact
        (ρ.summable_latticePolynomialWeight_mul_norm_covarianceModeCoeff
          hε).congr fun k => by
            simp only [f, if_pos, Complex.norm_real,
              Real.norm_eq_abs,
              abs_of_nonneg (mul_nonneg (norm_nonneg _)
                (latticePolynomialWeight_nonneg 8 _))]
            ring
    · simpa only [f, hji, if_false, mul_one,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)] using
          ρ.summable_norm_covarianceModeCoeff hε
  have hproduct :
      Summable fun q : Fin m → Z4 =>
        ‖finSeriesAssignmentTerm m f q‖ :=
    summable_norm_finSeriesAssignmentTerm m f hf
  refine hproduct.congr fun q => ?_
  have hconfig :
      ρ.r324CovarianceConfigurationWeight ε κ.1
          (r324FullConfigurationOfStandard κ q) =
        ∏ j : Fin m, ‖ρ.covarianceModeCoeff ε (q j)‖ := by
    unfold r324CovarianceConfigurationWeight
    let e := r324FullPairIndexEquiv κ
    calc
      (∏ j, ‖ρ.covarianceModeCoeff ε
          (r324FullConfigurationOfStandard κ q j)‖) =
          ∏ j : Fin m,
            ‖ρ.covarianceModeCoeff ε
              (r324FullConfigurationOfStandard κ q (e j))‖ := by
        exact (e.prod_comp fun j =>
          ‖ρ.covarianceModeCoeff ε
            (r324FullConfigurationOfStandard κ q j)‖).symm
      _ = ∏ j : Fin m,
          ‖ρ.covarianceModeCoeff ε (q j)‖ := by
        apply Finset.prod_congr rfl
        intro j _hj
        simp [e, r324FullConfigurationOfStandard]
  unfold finSeriesAssignmentTerm f
  rw [norm_prod]
  have hfactor_nonneg (j : Fin m) :
      0 ≤ ‖ρ.covarianceModeCoeff ε (q j)‖ *
        (if j = i then
          latticePolynomialWeight 8 (q j) else 1) :=
    mul_nonneg (norm_nonneg _) (by
      by_cases hji : j = i
      · simp only [hji, if_pos]
        exact latticePolynomialWeight_nonneg 8 _
      · simp only [hji, if_false]
        exact zero_le_one)
  simp_rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hfactor_nonneg _)]
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_ite_eq' Finset.univ i
    (fun _ => latticePolynomialWeight 8 (q _))]
  simp only [Finset.mem_univ, if_true]
  rw [hconfig]

theorem summable_standardConfigurationWeight_mul_pairDecayCost
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (i : Fin m) :
    Summable fun q : Fin m → Z4 =>
      ρ.r324CovarianceConfigurationWeight ε κ.1
          (r324FullConfigurationOfStandard κ q) *
        r324PairDecayCost κ q i := by
  have hmajor :
      Summable fun q : Fin m → Z4 =>
        625 *
          (ρ.r324CovarianceConfigurationWeight ε κ.1
              (r324FullConfigurationOfStandard κ q) *
            latticePolynomialWeight 8 (q i)) :=
    (ρ.summable_standardConfigurationWeight_mul_latticePolynomialWeight
      hε κ i).mul_left 625
  refine hmajor.of_nonneg_of_le
    (fun q => mul_nonneg
      (ρ.r324CovarianceConfigurationWeight_nonneg ε κ.1 _)
      (r324PairDecayCost_pos κ q i).le) ?_
  intro q
  calc
    ρ.r324CovarianceConfigurationWeight ε κ.1
          (r324FullConfigurationOfStandard κ q) *
        r324PairDecayCost κ q i
        ≤ ρ.r324CovarianceConfigurationWeight ε κ.1
            (r324FullConfigurationOfStandard κ q) *
          (625 * latticePolynomialWeight 8 (q i)) :=
      mul_le_mul_of_nonneg_left
        (r324PairDecayCost_le_latticePolynomialWeight κ q i)
        (ρ.r324CovarianceConfigurationWeight_nonneg ε κ.1 _)
    _ = 625 *
        (ρ.r324CovarianceConfigurationWeight ε κ.1
            (r324FullConfigurationOfStandard κ q) *
          latticePolynomialWeight 8 (q i)) := by ring

/-! ## Physical `L¹` weight and natural enumeration -/

/-- The bare two-skeleton `L¹` mass of one full doubled pairing. -/
def r324BareSkeletonL1
    {m : ℕ}
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull}) : ℝ :=
  let e := (momentContractionEquivFullPairing m).symm κ
  ∫ p : R324PhysicalPoint m,
    ‖renormalizedGreenSkeleton e.1
          (assemble p.1 p.2.1
            fun i => p.2.2.2.2 (leftMomentIndex i)) *
      renormalizedGreenSkeleton e.2.1
          (assemble p.2.2.1 p.2.2.2.1
            fun i => p.2.2.2.2 (rightMomentIndex i))‖
    ∂(r324PhysicalMeasure m)

theorem r324BareSkeletonL1_nonneg
    {m : ℕ}
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull}) :
    0 ≤ r324BareSkeletonL1 κ :=
  integral_nonneg fun _ => norm_nonneg _

/-- Exact separation of a configuration's constant covariance weight
from the physical `L¹` mass. -/
theorem integral_norm_r324FullPairingFourierIntegrand
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q :
      Fin (κ.1.pairSupport.filter (fun i => i < κ.1 i)).card → Z4) :
    (∫ p,
      ‖r324Flatten
        (ρ.r324FullPairingFourierIntegrand
          ε α β κ q) p‖
      ∂(r324PhysicalMeasure m)) =
      ρ.r324CovarianceConfigurationWeight ε κ.1 q *
        r324BareSkeletonL1 κ := by
  unfold r324BareSkeletonL1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  unfold r324Flatten r324FullPairingFourierIntegrand
  dsimp only
  simp only [norm_mul]
  have hphaseNorm :
      ‖momentFourierPhase α β
        p.1 p.2.1 p.2.2.1 p.2.2.2.1‖ = 1 := by
    unfold momentFourierPhase
    simp only [norm_mul, norm_charT4, mul_one]
  rw [hphaseNorm, one_mul,
    ρ.norm_r324CovarianceFourierConfigurationTerm]
  ring

/-- Routed `L¹` majorant of one standardized Fourier configuration. -/
def r324StandardFullPairingRouteWeight
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q : Fin m → Z4) : ℝ :=
  (∫ p,
    ‖r324Flatten
      (ρ.r324FullPairingFourierIntegrand ε α β κ
        (r324FullConfigurationOfStandard κ q)) p‖
    ∂(r324PhysicalMeasure m)) *
    ∑ i, r324PairDecayCost κ q i

theorem r324StandardFullPairingRouteWeight_nonneg
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q : Fin m → Z4) :
    0 ≤ ρ.r324StandardFullPairingRouteWeight ε α β κ q :=
  mul_nonneg (integral_nonneg fun _ => norm_nonneg _)
    (Finset.sum_nonneg fun i _ =>
      (r324PairDecayCost_pos κ q i).le)

theorem summable_r324StandardFullPairingRouteWeight
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull}) :
    Summable
      (ρ.r324StandardFullPairingRouteWeight ε α β κ) := by
  have hslots :
      Summable fun q : Fin m → Z4 =>
        ∑ i,
          ρ.r324CovarianceConfigurationWeight ε κ.1
              (r324FullConfigurationOfStandard κ q) *
            r324PairDecayCost κ q i := by
    classical
    induction (Finset.univ : Finset (Fin m)) using
      Finset.induction_on with
    | empty =>
        simp
    | @insert i s hi ih =>
        simp_rw [Finset.sum_insert hi]
        exact
          (ρ.summable_standardConfigurationWeight_mul_pairDecayCost
            hε κ i).add ih
  have hscaled :
      Summable fun q : Fin m → Z4 =>
        r324BareSkeletonL1 κ *
          ∑ i,
            ρ.r324CovarianceConfigurationWeight ε κ.1
                (r324FullConfigurationOfStandard κ q) *
              r324PairDecayCost κ q i :=
    hslots.mul_left (r324BareSkeletonL1 κ)
  refine hscaled.congr fun q => ?_
  unfold r324StandardFullPairingRouteWeight
  rw [ρ.integral_norm_r324FullPairingFourierIntegrand
    ε α β κ (r324FullConfigurationOfStandard κ q)]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The physical integral is bounded by every routed slot after paying
that slot's eighth-order decay. -/
theorem norm_r324FullPairingFourierIntegral_le_routeWeight_mul_decay
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q : Fin m → Z4) (i : Fin m) :
    ‖ρ.r324FullPairingFourierIntegral ε α β κ
        (r324FullConfigurationOfStandard κ q)‖ ≤
      ρ.r324StandardFullPairingRouteWeight ε α β κ q *
        eighthOrderFrequencyDecay
          ‖r324StandardPairIncrement κ q i‖ := by
  let A : ℝ :=
    ∫ p,
      ‖r324Flatten
        (ρ.r324FullPairingFourierIntegrand ε α β κ
          (r324FullConfigurationOfStandard κ q)) p‖
      ∂(r324PhysicalMeasure m)
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hcost :
      r324PairDecayCost κ q i ≤
        ∑ j, r324PairDecayCost κ q j :=
    Finset.single_le_sum
      (fun j _ => (r324PairDecayCost_pos κ q j).le)
      (Finset.mem_univ i)
  have hdecay :
      0 ≤ eighthOrderFrequencyDecay
        ‖r324StandardPairIncrement κ q i‖ :=
    eighthOrderFrequencyDecay_nonneg _
  calc
    ‖ρ.r324FullPairingFourierIntegral ε α β κ
        (r324FullConfigurationOfStandard κ q)‖
        ≤ A := norm_integral_le_integral_norm _
    _ = A *
        (r324PairDecayCost κ q i *
          eighthOrderFrequencyDecay
            ‖r324StandardPairIncrement κ q i‖) := by
      rw [r324PairDecayCost_mul_decay]
      ring
    _ ≤ A *
        ((∑ j, r324PairDecayCost κ q j) *
          eighthOrderFrequencyDecay
            ‖r324StandardPairIncrement κ q i‖) := by
      gcongr
    _ = ρ.r324StandardFullPairingRouteWeight ε α β κ q *
          eighthOrderFrequencyDecay
            ‖r324StandardPairIncrement κ q i‖ := by
      unfold r324StandardFullPairingRouteWeight A
      ring

/-- Cancellation-preserving routed weight.  In contrast to
`r324StandardFullPairingRouteWeight`, all five physical variable groups
are integrated before the norm is taken.  Thus the external `α`/`β`
oscillations remain available to the endpoint-first argument. -/
def r324SharpFullPairingRouteWeight
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q : Fin m → Z4) : ℝ :=
  ‖ρ.r324FullPairingFourierIntegral ε α β κ
      (r324FullConfigurationOfStandard κ q)‖ *
    ∑ i, r324PairDecayCost κ q i

theorem r324SharpFullPairingRouteWeight_nonneg
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q : Fin m → Z4) :
    0 ≤ ρ.r324SharpFullPairingRouteWeight ε α β κ q :=
  mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun i _ =>
      (r324PairDecayCost_pos κ q i).le)

/-- The sharp routed weight is dominated by the absolute-integral
weight.  This transfers summability without moving the norm inside in
the final endpoint budget. -/
theorem r324SharpFullPairingRouteWeight_le_standard
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q : Fin m → Z4) :
    ρ.r324SharpFullPairingRouteWeight ε α β κ q ≤
      ρ.r324StandardFullPairingRouteWeight ε α β κ q := by
  unfold r324SharpFullPairingRouteWeight
    r324StandardFullPairingRouteWeight
  exact mul_le_mul_of_nonneg_right
    (norm_integral_le_integral_norm _)
    (Finset.sum_nonneg fun i _ =>
      (r324PairDecayCost_pos κ q i).le)

theorem summable_r324SharpFullPairingRouteWeight
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull}) :
    Summable
      (ρ.r324SharpFullPairingRouteWeight ε α β κ) := by
  exact
    (ρ.summable_r324StandardFullPairingRouteWeight
      hε α β κ).of_nonneg_of_le
      (ρ.r324SharpFullPairingRouteWeight_nonneg ε α β κ)
      (ρ.r324SharpFullPairingRouteWeight_le_standard ε α β κ)

/-- Each slot pays one eighth-order routed decay while the sharp
weight retains the fully integrated endpoint oscillations. -/
theorem norm_r324FullPairingFourierIntegral_le_sharpRouteWeight_mul_decay
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q : Fin m → Z4) (i : Fin m) :
    ‖ρ.r324FullPairingFourierIntegral ε α β κ
        (r324FullConfigurationOfStandard κ q)‖ ≤
      ρ.r324SharpFullPairingRouteWeight ε α β κ q *
        eighthOrderFrequencyDecay
          ‖r324StandardPairIncrement κ q i‖ := by
  let A : ℝ :=
    ‖ρ.r324FullPairingFourierIntegral ε α β κ
      (r324FullConfigurationOfStandard κ q)‖
  have hA : 0 ≤ A := norm_nonneg _
  have hcost :
      r324PairDecayCost κ q i ≤
        ∑ j, r324PairDecayCost κ q j :=
    Finset.single_le_sum
      (fun j _ => (r324PairDecayCost_pos κ q j).le)
      (Finset.mem_univ i)
  have hdecay :
      0 ≤ eighthOrderFrequencyDecay
        ‖r324StandardPairIncrement κ q i‖ :=
    eighthOrderFrequencyDecay_nonneg _
  calc
    ‖ρ.r324FullPairingFourierIntegral ε α β κ
        (r324FullConfigurationOfStandard κ q)‖ =
        A *
          (r324PairDecayCost κ q i *
            eighthOrderFrequencyDecay
              ‖r324StandardPairIncrement κ q i‖) := by
      rw [r324PairDecayCost_mul_decay]
      simp only [mul_one, A]
    _ ≤ A *
        ((∑ j, r324PairDecayCost κ q j) *
          eighthOrderFrequencyDecay
            ‖r324StandardPairIncrement κ q i‖) := by
      gcongr
    _ = ρ.r324SharpFullPairingRouteWeight ε α β κ q *
          eighthOrderFrequencyDecay
            ‖r324StandardPairIncrement κ q i‖ := by
      unfold r324SharpFullPairingRouteWeight A
      ring

/-- Natural-number form of the routed configuration weight. -/
def r324NatFullPairingRouteWeight
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (a : ℕ) : ℝ :=
  ρ.r324StandardFullPairingRouteWeight ε α β κ
    (r324NatEquivStandardConfigurations hm a)

/-- Natural-number form of the cancellation-preserving sharp routed
weight. -/
def r324NatSharpFullPairingRouteWeight
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (a : ℕ) : ℝ :=
  ρ.r324SharpFullPairingRouteWeight ε α β κ
    (r324NatEquivStandardConfigurations hm a)

/-- Conservation-complete increments: nonzero terms retain their
genuine signed covariance modes; zero terms are padded by the external
mode in the first slot and zeros elsewhere. -/
def r324NatFullPairingRoutedIncrement
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (a : ℕ) (i : Fin m) :
    EuclideanSpace ℝ (Fin dim) :=
  if ρ.r324NatFullPairingFourierTerm hm ε α β κ a = 0 then
    if i = ⟨0, hm⟩ then z4EuclideanFrequency (α + β) else 0
  else
    r324NatFullPairingIncrement hm κ a i

theorem summable_r324NatFullPairingRouteWeight
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull}) :
    Summable
      (ρ.r324NatFullPairingRouteWeight hm ε α β κ) := by
  exact
    ((r324NatEquivStandardConfigurations hm).summable_iff).2
      (ρ.summable_r324StandardFullPairingRouteWeight
        hε α β κ)

theorem summable_r324NatSharpFullPairingRouteWeight
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull}) :
    Summable
      (ρ.r324NatSharpFullPairingRouteWeight
        hm ε α β κ) := by
  exact
    ((r324NatEquivStandardConfigurations hm).summable_iff).2
      (ρ.summable_r324SharpFullPairingRouteWeight
        hε α β κ)

theorem r324NatSharpFullPairingRouteWeight_nonneg
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (a : ℕ) :
    0 ≤
      ρ.r324NatSharpFullPairingRouteWeight
        hm ε α β κ a :=
  ρ.r324SharpFullPairingRouteWeight_nonneg
    ε α β κ _

theorem r324NatFullPairingRouteWeight_nonneg
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (a : ℕ) :
    0 ≤ ρ.r324NatFullPairingRouteWeight hm ε α β κ a :=
  ρ.r324StandardFullPairingRouteWeight_nonneg
    ε α β κ _

theorem sum_r324NatFullPairingRoutedIncrement
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (a : ℕ) :
    (∑ i,
      ρ.r324NatFullPairingRoutedIncrement
        hm ε α β κ a i) =
      z4EuclideanFrequency (α + β) := by
  by_cases hzero :
      ρ.r324NatFullPairingFourierTerm
        hm ε α β κ a = 0
  · simp only [r324NatFullPairingRoutedIncrement, hzero,
      if_pos]
    simp
  · simp only [r324NatFullPairingRoutedIncrement, hzero,
      ite_false]
    exact
      ρ.sum_r324NatFullPairingIncrement_eq_external_of_ne_zero
        hm ε α β κ a hzero

theorem norm_r324NatFullPairingFourierTerm_le_routeWeight_mul_decay
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (a : ℕ) (i : Fin m) :
    ‖ρ.r324NatFullPairingFourierTerm hm ε α β κ a‖ ≤
      ρ.r324NatFullPairingRouteWeight hm ε α β κ a *
        eighthOrderFrequencyDecay
          ‖ρ.r324NatFullPairingRoutedIncrement
            hm ε α β κ a i‖ := by
  by_cases hzero :
      ρ.r324NatFullPairingFourierTerm
        hm ε α β κ a = 0
  · rw [hzero, norm_zero]
    exact mul_nonneg
      (ρ.r324NatFullPairingRouteWeight_nonneg
        hm ε α β κ a)
      (eighthOrderFrequencyDecay_nonneg _)
  · have hincrement :
        ρ.r324NatFullPairingRoutedIncrement
            hm ε α β κ a i =
          r324NatFullPairingIncrement hm κ a i := by
      simp [r324NatFullPairingRoutedIncrement, hzero]
    rw [hincrement]
    simpa only [r324NatFullPairingFourierTerm,
      r324NatFullPairingRouteWeight,
      r324NatFullPairingIncrement] using
      ρ.norm_r324FullPairingFourierIntegral_le_routeWeight_mul_decay
        ε α β κ
        (r324NatEquivStandardConfigurations hm a) i

theorem norm_r324NatFullPairingFourierTerm_le_sharpRouteWeight_mul_decay
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (a : ℕ) (i : Fin m) :
    ‖ρ.r324NatFullPairingFourierTerm hm ε α β κ a‖ ≤
      ρ.r324NatSharpFullPairingRouteWeight hm ε α β κ a *
        eighthOrderFrequencyDecay
          ‖ρ.r324NatFullPairingRoutedIncrement
            hm ε α β κ a i‖ := by
  by_cases hzero :
      ρ.r324NatFullPairingFourierTerm
        hm ε α β κ a = 0
  · rw [hzero, norm_zero]
    exact mul_nonneg
      (ρ.r324NatSharpFullPairingRouteWeight_nonneg
        hm ε α β κ a)
      (eighthOrderFrequencyDecay_nonneg _)
  · have hincrement :
        ρ.r324NatFullPairingRoutedIncrement
            hm ε α β κ a i =
          r324NatFullPairingIncrement hm κ a i := by
      simp [r324NatFullPairingRoutedIncrement, hzero]
    rw [hincrement]
    simpa only [r324NatFullPairingFourierTerm,
      r324NatSharpFullPairingRouteWeight,
      r324NatFullPairingIncrement] using
      ρ.norm_r324FullPairingFourierIntegral_le_sharpRouteWeight_mul_decay
        ε α β κ
        (r324NatEquivStandardConfigurations hm a) i

/-! ## Raw countable reindexing across all full pairings

This is deliberately an intermediate Fourier/Fubini layer.  It gives an
exact single `ℕ`-indexed series and a summable majorant, but the final
R-324 reduction must regroup terms by a residual-refined primitive
schedule before taking norms. -/

/-- Finite outer index of full doubled pairings. -/
abbrev R324FullPairingIndex (m : ℕ) :=
  {τ : PartialPairing (Fin (2 * m)) // τ.IsFull}

/-- A canonical contraction witnesses that the finite full-pairing
index is nonempty for every `m`. -/
def r324CanonicalMomentContraction (m : ℕ) :
    MomentContraction m :=
  ⟨PartialPairing.id, PartialPairing.id, Equiv.refl _⟩

instance instNonemptyR324FullPairingIndex (m : ℕ) :
    Nonempty (R324FullPairingIndex m) :=
  ⟨momentContractionEquivFullPairing m
    (r324CanonicalMomentContraction m)⟩

/-- One exact enumeration of all pairs `(full pairing, Fourier
configuration number)`. -/
def r324NatEquivRawFullPairingConfigurations (m : ℕ) :
    ℕ ≃ R324FullPairingIndex m × ℕ := by
  classical
  letI : Encodable (R324FullPairingIndex m) :=
    Fintype.toEncodable _
  letI : Denumerable (R324FullPairingIndex m × ℕ) :=
    Denumerable.ofEncodableOfInfinite _
  exact (Denumerable.eqv
    (R324FullPairingIndex m × ℕ)).symm

/-- Raw term obtained by flattening the finite full-pairing sum and each
pairing's natural-number Fourier series. -/
def r324RawMomentFourierTerm
    {m : ℕ} (hm : 0 < m)
    (lam ε : ℝ) (α β : Z4) (a : ℕ) : ℂ :=
  let p := r324NatEquivRawFullPairingConfigurations m a
  (lamEps lam ε ^ (2 * m) : ℂ) *
    ρ.r324NatFullPairingFourierTerm
      hm ε α β p.1 p.2

/-- Raw cancellation-preserving weight for one flattened term.  It is
used only as a summable majorant before the residual-refined regrouping. -/
def r324RawMomentRouteWeight
    {m : ℕ} (hm : 0 < m)
    (lam ε : ℝ) (α β : Z4) (a : ℕ) : ℝ :=
  let p := r324NatEquivRawFullPairingConfigurations m a
  |lamEps lam ε| ^ (2 * m) *
    ρ.r324NatSharpFullPairingRouteWeight
      hm ε α β p.1 p.2

/-- Every raw flattened term carries exactly the `m` covariance-pair
increments of its full doubled pairing. -/
def r324RawMomentRoutedIncrement
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4) (a : ℕ) (i : Fin m) :
    EuclideanSpace ℝ (Fin dim) :=
  let p := r324NatEquivRawFullPairingConfigurations m a
  ρ.r324NatFullPairingRoutedIncrement
    hm ε α β p.1 p.2 i

theorem r324RawMomentRouteWeight_nonneg
    {m : ℕ} (hm : 0 < m)
    (lam ε : ℝ) (α β : Z4) (a : ℕ) :
    0 ≤ ρ.r324RawMomentRouteWeight
      hm lam ε α β a := by
  unfold r324RawMomentRouteWeight
  exact mul_nonneg (pow_nonneg (abs_nonneg _) _)
    (ρ.r324NatSharpFullPairingRouteWeight_nonneg
      hm ε α β _ _)

set_option maxHeartbeats 3000000 in
theorem summable_r324RawMomentRouteWeight
    {m : ℕ} (hm : 0 < m)
    (lam : ℝ) {ε : ℝ} (hε : 0 < ε)
    (α β : Z4) :
    Summable
      (ρ.r324RawMomentRouteWeight hm lam ε α β) := by
  let scalar : ℝ := |lamEps lam ε| ^ (2 * m)
  let f : R324FullPairingIndex m × ℕ → ℝ := fun p =>
    scalar *
      ρ.r324NatSharpFullPairingRouteWeight
        hm ε α β p.1 p.2
  have hfnonneg : ∀ p, 0 ≤ f p := by
    intro p
    exact mul_nonneg
      (pow_nonneg (abs_nonneg _) _)
      (ρ.r324NatSharpFullPairingRouteWeight_nonneg
        hm ε α β p.1 p.2)
  have hf : Summable f := by
    rw [summable_prod_of_nonneg hfnonneg]
    constructor
    · intro κ
      exact
        (ρ.summable_r324NatSharpFullPairingRouteWeight
          hm hε α β κ).mul_left scalar
    · exact Summable.of_finite
  change
    Summable
      (f ∘ r324NatEquivRawFullPairingConfigurations m)
  exact
    ((r324NatEquivRawFullPairingConfigurations m).summable_iff).2
      hf

theorem sum_r324RawMomentRoutedIncrement
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4) (a : ℕ) :
    (∑ i,
      ρ.r324RawMomentRoutedIncrement
        hm ε α β a i) =
      z4EuclideanFrequency (α + β) := by
  unfold r324RawMomentRoutedIncrement
  exact ρ.sum_r324NatFullPairingRoutedIncrement
    hm ε α β _ _

theorem norm_r324RawMomentFourierTerm_le_routeWeight_mul_decay
    {m : ℕ} (hm : 0 < m)
    (lam ε : ℝ) (α β : Z4)
    (a : ℕ) (i : Fin m) :
    ‖ρ.r324RawMomentFourierTerm
        hm lam ε α β a‖ ≤
      ρ.r324RawMomentRouteWeight hm lam ε α β a *
        eighthOrderFrequencyDecay
          ‖ρ.r324RawMomentRoutedIncrement
            hm ε α β a i‖ := by
  let p := r324NatEquivRawFullPairingConfigurations m a
  change
    ‖(lamEps lam ε ^ (2 * m) : ℂ) *
        ρ.r324NatFullPairingFourierTerm
          hm ε α β p.1 p.2‖ ≤
      (|lamEps lam ε| ^ (2 * m) *
          ρ.r324NatSharpFullPairingRouteWeight
            hm ε α β p.1 p.2) *
        eighthOrderFrequencyDecay
          ‖ρ.r324NatFullPairingRoutedIncrement
            hm ε α β p.1 p.2 i‖
  rw [norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs]
  calc
    |lamEps lam ε| ^ (2 * m) *
          ‖ρ.r324NatFullPairingFourierTerm
            hm ε α β p.1 p.2‖ ≤
        |lamEps lam ε| ^ (2 * m) *
          (ρ.r324NatSharpFullPairingRouteWeight
              hm ε α β p.1 p.2 *
            eighthOrderFrequencyDecay
              ‖ρ.r324NatFullPairingRoutedIncrement
                hm ε α β p.1 p.2 i‖) :=
      mul_le_mul_of_nonneg_left
        (ρ.norm_r324NatFullPairingFourierTerm_le_sharpRouteWeight_mul_decay
          hm ε α β p.1 p.2 i)
        (pow_nonneg (abs_nonneg _) _)
    _ =
        (|lamEps lam ε| ^ (2 * m) *
            ρ.r324NatSharpFullPairingRouteWeight
              hm ε α β p.1 p.2) *
          eighthOrderFrequencyDecay
            ‖ρ.r324NatFullPairingRoutedIncrement
              hm ε α β p.1 p.2 i‖ := by ring

end SmoothCutoff

end

end Anderson4D
