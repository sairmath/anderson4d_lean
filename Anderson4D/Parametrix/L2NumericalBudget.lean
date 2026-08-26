import Anderson4D.Parametrix.PerrLeftBoundaryMoment
import Anderson4D.DetParametrix.Core.FrequencyRouting
import Anderson4D.Continuum.LogAsymptotics

/-!
# Numerical closure of the one-sided `L²` good-event budgets

This file records the elementary small-scale estimates which turn the
explicit budgets in `PerrLeftBoundaryMoment` into the powers used in
paper §3.4:

* the physical truncated-parametrix second moment is at most
  `ε⁻²⁴`;
* the left-boundary first moment is at most `ε³⁰`.

All constants are selected before the coupling and before the scale.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Anderson4D

noncomputable section

open Filter Set MeasureTheory
open scoped BigOperators Topology
open SmoothCutoff

namespace PartialPairing

/-! ## A scale-uniform Fourier-symbol sum -/

/-- A fixed eighth-order Schwartz constant for the cutoff. -/
def cutoffFourierDecayConstant (ρ : SmoothCutoff) : ℝ :=
  Classical.choose ρ.exists_fourierR4_one_add_norm_bound

theorem cutoffFourierDecayConstant_pos (ρ : SmoothCutoff) :
    0 < cutoffFourierDecayConstant ρ :=
  (Classical.choose_spec
    ρ.exists_fourierR4_one_add_norm_bound).1

theorem cutoffFourierDecayConstant_spec
    (ρ : SmoothCutoff) (ξ : R4) :
    (1 + ‖euclideanFrequency ξ‖) ^ 8 *
        ‖fourierR4 ρ ξ‖ ≤ cutoffFourierDecayConstant ρ :=
  (Classical.choose_spec
    ρ.exists_fourierR4_one_add_norm_bound).2 ξ

/-- The fixed summability constant which appears after restricting the
Schwartz multiplier to the lattice. -/
def cutoffSymbolSumConstant (ρ : SmoothCutoff) : ℝ :=
  cutoffFourierDecayConstant ρ *
    (2 * Real.pi) ^ 8 *
    ∑' k : Z4, latticeSummabilityWeight k

theorem cutoffSymbolSumConstant_pos (ρ : SmoothCutoff) :
    0 < cutoffSymbolSumConstant ρ := by
  have hsum :
      0 < ∑' k : Z4, latticeSummabilityWeight k := by
    exact
      summable_latticeSummabilityWeight.tsum_pos
        (fun k => by
          unfold latticeSummabilityWeight
          positivity)
        0
        (by
          unfold latticeSummabilityWeight
          positivity)
  unfold cutoffSymbolSumConstant
  exact
    mul_pos
      (mul_pos (cutoffFourierDecayConstant_pos ρ)
        (pow_pos (by positivity) _))
      hsum

/-- Uniform polynomial control of the absolutely summable cutoff symbol.
The power eight is deliberately wasteful but is fixed independently of
the scale. -/
theorem tsum_norm_symbol_le_cutoffSymbolSumConstant
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    (∑' k : Z4, ‖ρ.symbol ε k‖) ≤
      cutoffSymbolSumConstant ρ * ε⁻¹ ^ (8 : ℕ) := by
  let d : ℝ := ε / (2 * Real.pi)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hd1 : d ≤ 1 := by
    dsimp [d]
    have htwoPi : 1 ≤ 2 * Real.pi := by
      have hpi : 3 < Real.pi := Real.pi_gt_three
      nlinarith
    exact (div_le_one (by positivity)).2 (hεle.trans htwoPi)
  have hpoint (k : Z4) :
      ‖ρ.symbol ε k‖ ≤
        (cutoffFourierDecayConstant ρ * d⁻¹ ^ 8) *
          latticeSummabilityWeight k := by
    let ξ : R4 := fun i => ε * (k i : ℝ)
    let w : EuclideanR4 := euclideanFrequency ξ
    let P : ℝ :=
      ∏ i, ((Int.natAbs (k i) : ℝ) + 1) ^ 2
    have hcoord (i : Fin dim) :
        d * ((Int.natAbs (k i) : ℝ) + 1) ≤
          1 + ‖w‖ := by
      have hki :
          d * (Int.natAbs (k i) : ℝ) ≤ ‖w‖ := by
        calc
          d * (Int.natAbs (k i) : ℝ) = ‖w i‖ := by
            simp only [d, w, ξ, euclideanFrequency_apply,
              Real.norm_eq_abs]
            rw [abs_div, abs_mul, abs_of_pos hε,
              abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
              Nat.cast_natAbs, Int.cast_abs]
            field_simp
          _ ≤ ‖w‖ := PiLp.norm_apply_le w i
      calc
        d * ((Int.natAbs (k i) : ℝ) + 1) =
            d * (Int.natAbs (k i) : ℝ) + d := by ring
        _ ≤ ‖w‖ + 1 := by gcongr
        _ = 1 + ‖w‖ := by ring
    have hprod :
        d ^ 8 * P ≤ (1 + ‖w‖) ^ 8 := by
      have hsquares :
          ∏ i,
              (d * ((Int.natAbs (k i) : ℝ) + 1)) ^ 2 ≤
            ∏ _i : Fin dim, (1 + ‖w‖) ^ 2 := by
        apply Finset.prod_le_prod
        · intro i hi
          positivity
        · intro i hi
          exact pow_le_pow_left₀ (by positivity) (hcoord i) 2
      calc
        d ^ 8 * P =
            ∏ i,
              (d * ((Int.natAbs (k i) : ℝ) + 1)) ^ 2 := by
          symm
          calc
            _ = ∏ i, d ^ 2 *
                (((Int.natAbs (k i) : ℝ) + 1) ^ 2) := by
              apply Finset.prod_congr rfl
              intro i hi
              ring
            _ = (∏ _i : Fin dim, d ^ 2) * P := by
              rw [Finset.prod_mul_distrib]
            _ = d ^ 8 * P := by
              rw [Finset.prod_const]
              change (d ^ 2) ^ 4 * P = d ^ 8 * P
              ring
        _ ≤ ∏ _i : Fin dim, (1 + ‖w‖) ^ 2 := hsquares
        _ = (1 + ‖w‖) ^ 8 := by
          rw [Finset.prod_const]
          change ((1 + ‖w‖) ^ 2) ^ 4 =
            (1 + ‖w‖) ^ 8
          ring
    have hschwartz :
        (1 + ‖w‖) ^ 8 * ‖ρ.symbol ε k‖ ≤
          cutoffFourierDecayConstant ρ := by
      simpa [w, ξ, SmoothCutoff.symbol] using
        cutoffFourierDecayConstant_spec ρ ξ
    have hPpos : 0 < P := by
      unfold P
      exact Finset.prod_pos fun i hi =>
        sq_pos_of_pos (by positivity)
    have hden : 0 < d ^ 8 * P :=
      mul_pos (pow_pos hd _) hPpos
    have hcombined :
        d ^ 8 * P * ‖ρ.symbol ε k‖ ≤
          cutoffFourierDecayConstant ρ :=
      (mul_le_mul_of_nonneg_right hprod
        (norm_nonneg _)).trans hschwartz
    have hdivide :
        ‖ρ.symbol ε k‖ ≤
          cutoffFourierDecayConstant ρ / (d ^ 8 * P) :=
      (le_div_iff₀ hden).2
        (by simpa [mul_assoc, mul_comm, mul_left_comm] using
          hcombined)
    calc
      ‖ρ.symbol ε k‖ ≤
          cutoffFourierDecayConstant ρ / (d ^ 8 * P) :=
        hdivide
      _ =
          (cutoffFourierDecayConstant ρ * d⁻¹ ^ 8) *
            latticeSummabilityWeight k := by
        simp only [latticeSummabilityWeight,
          Finset.prod_inv_distrib]
        change
          cutoffFourierDecayConstant ρ / (d ^ 8 * P) =
            (cutoffFourierDecayConstant ρ * d⁻¹ ^ 8) *
              P⁻¹
        field_simp [hd.ne', hPpos.ne']
  calc
    (∑' k : Z4, ‖ρ.symbol ε k‖) ≤
        ∑' k : Z4,
          (cutoffFourierDecayConstant ρ * d⁻¹ ^ 8) *
            latticeSummabilityWeight k :=
      (ρ.summable_norm_symbol hε).tsum_le_tsum
        hpoint
        (summable_latticeSummabilityWeight.mul_left
          (cutoffFourierDecayConstant ρ * d⁻¹ ^ 8))
    _ =
        (cutoffFourierDecayConstant ρ * d⁻¹ ^ 8) *
          ∑' k : Z4, latticeSummabilityWeight k := by
      rw [tsum_mul_left]
    _ =
        cutoffSymbolSumConstant ρ * ε⁻¹ ^ (8 : ℕ) := by
      unfold cutoffSymbolSumConstant
      dsimp [d]
      have hεne : ε ≠ 0 := hε.ne'
      have hpi : 2 * Real.pi ≠ 0 := by positivity
      field_simp

/-! ## Exponential decay at the logarithmic truncation order -/

/-- A fixed geometric ratio raised to `⌊|log ε|⌋` gives an arbitrary
prescribed polynomial power of `ε`.  The factor `exp N` is exactly the
single unit lost by taking the floor. -/
theorem exp_neg_nat_pow_truncOrder_le
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1) :
    Real.exp (-(N : ℝ)) ^ truncOrder ε ≤
      Real.exp (N : ℝ) * ε ^ N := by
  have habs :
      |Real.log ε| = -Real.log ε := by
    rw [abs_of_nonpos (Real.log_nonpos hε.le hεle)]
  have hfloor :
      |Real.log ε| - 1 ≤ (truncOrder ε : ℝ) := by
    exact
      (Nat.sub_one_lt_floor
        |Real.log ε|).le
  have hneg :
      -(N : ℝ) * (truncOrder ε : ℝ) ≤
        -(N : ℝ) * (|Real.log ε| - 1) :=
    mul_le_mul_of_nonpos_left hfloor
      (neg_nonpos.mpr (Nat.cast_nonneg N))
  calc
    Real.exp (-(N : ℝ)) ^ truncOrder ε =
        Real.exp
          ((truncOrder ε : ℝ) * (-(N : ℝ))) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp
          (-(N : ℝ) * (truncOrder ε : ℝ)) := by
      congr 1
      ring
    _ ≤ Real.exp (-(N : ℝ) *
          (|Real.log ε| - 1)) :=
      Real.exp_le_exp.mpr hneg
    _ = Real.exp (N : ℝ) * ε ^ N := by
      rw [habs]
      have hexponent :
          -(N : ℝ) * (-Real.log ε - 1) =
            (N : ℝ) + (N : ℝ) * Real.log ε := by
        ring
      rw [hexponent, Real.exp_add, Real.exp_nat_mul,
        Real.exp_log hε]

/-- One fewer geometric factor costs one further fixed exponential
constant. -/
theorem exp_neg_nat_pow_truncOrder_sub_one_le
    (N : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hA : 1 ≤ truncOrder ε) :
    Real.exp (-(N : ℝ)) ^ (truncOrder ε - 1) ≤
      Real.exp (2 * (N : ℝ)) * ε ^ N := by
  let θ : ℝ := Real.exp (-(N : ℝ))
  have hθ : 0 < θ := Real.exp_pos _
  have hbase :=
    exp_neg_nat_pow_truncOrder_le N hε hεle
  have hsplit :
      θ ^ (truncOrder ε - 1) =
        θ ^ truncOrder ε * θ⁻¹ := by
    have hsucc :
        truncOrder ε - 1 + 1 = truncOrder ε :=
      Nat.sub_add_cancel hA
    calc
      θ ^ (truncOrder ε - 1) =
          (θ ^ (truncOrder ε - 1) * θ) * θ⁻¹ := by
        field_simp [hθ.ne']
      _ = θ ^ truncOrder ε * θ⁻¹ := by
        rw [← pow_succ, hsucc]
  calc
    Real.exp (-(N : ℝ)) ^ (truncOrder ε - 1) =
        θ ^ (truncOrder ε - 1) := rfl
    _ = θ ^ truncOrder ε * θ⁻¹ := hsplit
    _ ≤ (Real.exp (N : ℝ) * ε ^ N) * θ⁻¹ := by
      gcongr
    _ = Real.exp (2 * (N : ℝ)) * ε ^ N := by
      dsimp [θ]
      rw [Real.exp_neg, inv_inv]
      calc
        Real.exp (N : ℝ) * ε ^ N * Real.exp (N : ℝ) =
            (Real.exp (N : ℝ) * Real.exp (N : ℝ)) *
              ε ^ N := by ring
        _ = Real.exp (2 * (N : ℝ)) * ε ^ N := by
          rw [← Real.exp_add]
          congr 2
          ring

/-! ## The physical second-moment budget -/

/-- The scale- and order-independent part of the orderwise P-3.5b
`L²` budget. -/
def physicalSecondMomentConstant (outerConstant : ℝ) : ℝ :=
  32768 *
    ‖(paperTorusVolume : ℂ)⁻¹‖ ^ 2 *
    outerConstant *
    (∑' k : Z4, l2LatticeRadialWeight 5 k) ^ 2

theorem physicalSecondMomentConstant_nonneg
    {outerConstant : ℝ} (houter : 0 ≤ outerConstant) :
    0 ≤ physicalSecondMomentConstant outerConstant := by
  unfold physicalSecondMomentConstant
  positivity

/-- Once both the coupling and the geometric order ratio are at most
one, every positive-order second moment is bounded by the same
`ε⁻²⁰` envelope. -/
theorem canonicalParametrixOrderL2SecondMomentBudget_le_coarse
    {outerConstant powerConstant lam ε : ℝ} {m : ℕ}
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam) (hlamle : lam ≤ 1)
    (hratio : powerConstant * lam ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) :
    canonicalParametrixOrderL2SecondMomentBudget
        outerConstant powerConstant lam ε m ≤
      physicalSecondMomentConstant outerConstant *
        ε⁻¹ ^ (20 : ℕ) := by
  have hsqrt :
      1 ≤ Real.sqrt |Real.log ε| :=
    Real.one_le_sqrt.mpr hlog
  have hlamEps0 : 0 ≤ lamEps lam ε := by
    unfold lamEps
    positivity
  have hlamEps1 : lamEps lam ε ≤ 1 := by
    unfold lamEps
    exact (div_le_self hlam hsqrt).trans hlamle
  have hlamEpsSq :
      lamEps lam ε ^ 2 ≤ 1 :=
    pow_le_one₀ hlamEps0 hlamEps1
  have hratio0 : 0 ≤ powerConstant * lam :=
    mul_nonneg hpower hlam
  have hratioPow :
      (powerConstant * lam) ^ (2 * m - 2) ≤ 1 :=
    pow_le_one₀ hratio0 hratio
  unfold canonicalParametrixOrderL2SecondMomentBudget
    parametrixOrderL2Scalar physicalSecondMomentConstant
  calc
    32768 *
          (‖(paperTorusVolume : ℂ)⁻¹‖ ^ 2 *
              lamEps lam ε ^ 2 * outerConstant *
              (powerConstant * lam) ^ (2 * m - 2)) *
          ε⁻¹ ^ (20 : ℕ) *
          (∑' k : Z4, l2LatticeRadialWeight 5 k) ^ 2 ≤
        32768 *
          (‖(paperTorusVolume : ℂ)⁻¹‖ ^ 2 *
              1 * outerConstant * 1) *
          ε⁻¹ ^ (20 : ℕ) *
          (∑' k : Z4, l2LatticeRadialWeight 5 k) ^ 2 := by
      gcongr
    _ =
        (32768 *
            ‖(paperTorusVolume : ℂ)⁻¹‖ ^ 2 *
            outerConstant *
            (∑' k : Z4, l2LatticeRadialWeight 5 k) ^ 2) *
          ε⁻¹ ^ (20 : ℕ) := by
      ring

/-- The moving physical finite sum admits a deliberately coarse
`ε⁻²²` bound.  This leaves two full powers for absorbing its fixed
constant into the paper's `ε⁻²⁴` threshold. -/
theorem canonicalPhysicalTruncatedParametrixL2SecondMomentBudget_le_coarse
    {outerConstant powerConstant lam ε : ℝ}
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam) (hlamle : lam ≤ 1)
    (hratio : powerConstant * lam ≤ 1)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) :
    canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
        outerConstant powerConstant lam ε (truncOrder ε) ≤
      9 * (physicalSecondMomentConstant outerConstant + 1) *
        ε⁻¹ ^ (22 : ℕ) := by
  let K : ℝ := physicalSecondMomentConstant outerConstant
  have hK : 0 ≤ K :=
    physicalSecondMomentConstant_nonneg houter
  have hinv1 : 1 ≤ ε⁻¹ :=
    (one_le_inv₀ hε).2 hεle
  have hpow20 : 1 ≤ ε⁻¹ ^ (20 : ℕ) :=
    one_le_pow₀ hinv1
  have hpiece :
      ∀ i : Fin (truncOrder ε + 1),
        canonicalPhysicalParametrixL2PieceSecondMomentBudget
            outerConstant powerConstant lam ε i ≤
          (K + 1) * ε⁻¹ ^ (20 : ℕ) := by
    intro i
    unfold canonicalPhysicalParametrixL2PieceSecondMomentBudget
    split_ifs with hi
    · calc
        1 ≤ 1 * ε⁻¹ ^ (20 : ℕ) := by simpa using hpow20
        _ ≤ (K + 1) * ε⁻¹ ^ (20 : ℕ) := by
          have : 1 ≤ K + 1 := by linarith
          gcongr
    · calc
        canonicalParametrixOrderL2SecondMomentBudget
            outerConstant powerConstant lam ε i.val ≤
            K * ε⁻¹ ^ (20 : ℕ) :=
          canonicalParametrixOrderL2SecondMomentBudget_le_coarse
            houter hpower hlam hlamle hratio hlog
        _ ≤ (K + 1) * ε⁻¹ ^ (20 : ℕ) := by
          have : K ≤ K + 1 := by linarith
          gcongr
  have hsum :
      (∑ i : Fin (truncOrder ε + 1),
          canonicalPhysicalParametrixL2PieceSecondMomentBudget
            outerConstant powerConstant lam ε i) ≤
        (truncOrder ε + 1 : ℝ) *
          ((K + 1) * ε⁻¹ ^ (20 : ℕ)) := by
    calc
      (∑ i : Fin (truncOrder ε + 1),
          canonicalPhysicalParametrixL2PieceSecondMomentBudget
            outerConstant powerConstant lam ε i) ≤
          ∑ _i : Fin (truncOrder ε + 1),
            ((K + 1) * ε⁻¹ ^ (20 : ℕ)) :=
        Finset.sum_le_sum fun i hi => hpiece i
      _ = (truncOrder ε + 1 : ℝ) *
          ((K + 1) * ε⁻¹ ^ (20 : ℕ)) := by
        simp
  have hepsSqrt :
      ε ≤ Real.sqrt ε := by
    nlinarith [Real.sq_sqrt hε.le, Real.sqrt_nonneg ε]
  have hsqrtInv :
      (Real.sqrt ε)⁻¹ ≤ ε⁻¹ :=
    (inv_le_inv₀ (Real.sqrt_pos.2 hε) hε).2 hepsSqrt
  have hA :
      (truncOrder ε : ℝ) ≤ 2 * ε⁻¹ :=
    (truncOrder_cast_le_two_mul_inv_sqrt hε hεle).trans
      (mul_le_mul_of_nonneg_left hsqrtInv (by norm_num))
  have hA1 :
      (truncOrder ε + 1 : ℝ) ≤ 3 * ε⁻¹ := by
    nlinarith
  unfold canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
  calc
    (truncOrder ε + 1 : ℝ) *
        ∑ i : Fin (truncOrder ε + 1),
          canonicalPhysicalParametrixL2PieceSecondMomentBudget
            outerConstant powerConstant lam ε i ≤
        (truncOrder ε + 1 : ℝ) *
          ((truncOrder ε + 1 : ℝ) *
            ((K + 1) * ε⁻¹ ^ (20 : ℕ))) := by
      gcongr
    _ ≤ (3 * ε⁻¹) *
          ((3 * ε⁻¹) *
            ((K + 1) * ε⁻¹ ^ (20 : ℕ))) := by
      gcongr
    _ =
        9 * (physicalSecondMomentConstant outerConstant + 1) *
          ε⁻¹ ^ (22 : ℕ) := by
      dsimp [K]
      ring

/-- The physical budget eventually meets the exact power used in the
Chebyshev threshold of paper (3.32). -/
theorem eventually_canonicalPhysicalTruncatedParametrixL2SecondMomentBudget_le
    {outerConstant powerConstant lam : ℝ}
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam) (hlamle : lam ≤ 1)
    (hratio : powerConstant * lam ≤ 1) :
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
      canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
          outerConstant powerConstant lam ε (truncOrder ε) ≤
        ε ^ (-24 : ℤ) := by
  let C : ℝ :=
    9 * (physicalSecondMomentConstant outerConstant + 1)
  have hC : 0 ≤ C := by
    dsimp [C]
    have hK :=
      physicalSecondMomentConstant_nonneg houter
    positivity
  have hid :
      Tendsto (fun ε : ℝ => ε)
        (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hvanish :
      Tendsto (fun ε : ℝ => C * ε ^ 2)
        (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    simpa using
      (hid.pow 2).const_mul C
  have habsorb :
      ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
        C * ε ^ 2 ≤ 1 :=
    hvanish.eventually_le_const zero_lt_one
  filter_upwards
      [self_mem_nhdsWithin,
        eventually_smallScale_le zero_lt_one,
        eventually_one_le_abs_log,
        habsorb] with
      ε hε hεle hlog habsorbε
  have hεpos : 0 < ε := hε
  have hcoarse :=
    canonicalPhysicalTruncatedParametrixL2SecondMomentBudget_le_coarse
      houter hpower hlam hlamle hratio
      hεpos hεle hlog
  calc
    canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
        outerConstant powerConstant lam ε (truncOrder ε) ≤
        C * ε⁻¹ ^ (22 : ℕ) := by
      simpa only [C] using hcoarse
    _ = (C * ε ^ 2) * ε⁻¹ ^ (24 : ℕ) := by
      field_simp [hεpos.ne']
    _ ≤ 1 * ε⁻¹ ^ (24 : ℕ) := by
      gcongr
    _ = ε ^ (-24 : ℤ) := by
      simp only [one_mul]
      rw [show (-24 : ℤ) = -(24 : ℤ) by norm_num,
        zpow_neg, inv_pow]
      rfl

/-! ## Square-root envelopes for the boundary terms -/

/-- Square root of the fixed P-3.5b second-moment constant. -/
def physicalFirstMomentConstant (outerConstant : ℝ) : ℝ :=
  Real.sqrt (physicalSecondMomentConstant outerConstant)

theorem physicalFirstMomentConstant_nonneg
    (outerConstant : ℝ) :
    0 ≤ physicalFirstMomentConstant outerConstant :=
  Real.sqrt_nonneg _

/-- Exact square-root factorization of the positive-order P-3.5b
budget. -/
theorem sqrt_canonicalParametrixOrderL2SecondMomentBudget_eq
    {outerConstant powerConstant lam ε : ℝ} {m : ℕ}
    (hm : 1 ≤ m)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam) :
    Real.sqrt
        (canonicalParametrixOrderL2SecondMomentBudget
          outerConstant powerConstant lam ε m) =
      physicalFirstMomentConstant outerConstant *
        lamEps lam ε *
        (powerConstant * lam) ^ (m - 1) *
        ε⁻¹ ^ (10 : ℕ) := by
  let K := physicalSecondMomentConstant outerConstant
  let X :=
    lamEps lam ε *
      (powerConstant * lam) ^ (m - 1) *
      ε⁻¹ ^ (10 : ℕ)
  have hK : 0 ≤ K :=
    physicalSecondMomentConstant_nonneg houter
  have hX : 0 ≤ X := by
    dsimp [X]
    unfold lamEps
    positivity
  have hexponent :
      2 * m - 2 = 2 * (m - 1) := by omega
  have hratioPow :
      (powerConstant * lam) ^ (2 * m - 2) =
        ((powerConstant * lam) ^ (m - 1)) ^ 2 := by
    calc
      (powerConstant * lam) ^ (2 * m - 2) =
          (powerConstant * lam) ^ (2 * (m - 1)) := by
        rw [hexponent]
      _ = (powerConstant * lam) ^ ((m - 1) * 2) := by
        rw [Nat.mul_comm]
      _ = ((powerConstant * lam) ^ (m - 1)) ^ 2 := by
        rw [pow_mul]
  have hepsPow :
      ε⁻¹ ^ (20 : ℕ) =
        (ε⁻¹ ^ (10 : ℕ)) ^ 2 := by ring
  have hbudget :
      canonicalParametrixOrderL2SecondMomentBudget
          outerConstant powerConstant lam ε m =
        K * X ^ 2 := by
    unfold canonicalParametrixOrderL2SecondMomentBudget
      parametrixOrderL2Scalar
    rw [hratioPow, hepsPow]
    dsimp [K, X, physicalSecondMomentConstant]
    ring
  rw [hbudget, Real.sqrt_mul hK, Real.sqrt_sq hX]
  dsimp [K, X, physicalFirstMomentConstant]
  ring

/-- Coarse positive-order square-root envelope after discarding the
inverse-logarithmic gain in `λ_ε`. -/
theorem sqrt_canonicalPhysicalParametrixOrderL2SecondMomentBudget_le
    {outerConstant powerConstant lam ε : ℝ} {m : ℕ}
    (hm : 1 ≤ m)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam) (hlamle : lam ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) :
    Real.sqrt
        (canonicalPhysicalParametrixOrderL2SecondMomentBudget
          outerConstant powerConstant lam ε m) ≤
      physicalFirstMomentConstant outerConstant *
        (powerConstant * lam) ^ (m - 1) *
        ε⁻¹ ^ (10 : ℕ) := by
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hsqrt :
      1 ≤ Real.sqrt |Real.log ε| :=
    Real.one_le_sqrt.mpr hlog
  have hlamEps0 : 0 ≤ lamEps lam ε := by
    unfold lamEps
    positivity
  have hlamEps1 : lamEps lam ε ≤ 1 := by
    unfold lamEps
    exact (div_le_self hlam hsqrt).trans hlamle
  rw [canonicalPhysicalParametrixOrderL2SecondMomentBudget,
    if_neg hm0,
    sqrt_canonicalParametrixOrderL2SecondMomentBudget_eq
      hm houter hpower hlam]
  have hfixed :
      0 ≤ physicalFirstMomentConstant outerConstant :=
    physicalFirstMomentConstant_nonneg _
  have hpow :
      0 ≤ (powerConstant * lam) ^ (m - 1) :=
    pow_nonneg (mul_nonneg hpower hlam) _
  have hepsPow : 0 ≤ ε⁻¹ ^ (10 : ℕ) := by positivity
  nlinarith [mul_nonneg hfixed
    (mul_nonneg hpow hepsPow)]

/-- Fixed constant in the square-root noise envelope. -/
def noiseFirstMomentConstant (ρ : SmoothCutoff) : ℝ :=
  ‖NoiseModel.whiteNoiseFourierScale‖ *
    cutoffSymbolSumConstant ρ

theorem noiseFirstMomentConstant_nonneg (ρ : SmoothCutoff) :
    0 ≤ noiseFirstMomentConstant ρ := by
  unfold noiseFirstMomentConstant
  exact mul_nonneg (norm_nonneg _)
    (cutoffSymbolSumConstant_pos ρ).le

/-- Polynomial envelope for the degree-one noise multiplier. -/
theorem sqrt_canonicalNoiseMultiplicationL2SecondMomentBudget_le
    (ρ : SmoothCutoff) {lam ε : ℝ}
    (hlam : 0 ≤ lam) (hlamle : lam ≤ 1)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) :
    Real.sqrt
        (canonicalNoiseMultiplicationL2SecondMomentBudget
          ρ lam ε) ≤
      noiseFirstMomentConstant ρ *
        ε⁻¹ ^ (8 : ℕ) := by
  have hsqrt :
      1 ≤ Real.sqrt |Real.log ε| :=
    Real.one_le_sqrt.mpr hlog
  have hlamEps0 : 0 ≤ lamEps lam ε := by
    unfold lamEps
    positivity
  have hlamEps1 : lamEps lam ε ≤ 1 := by
    unfold lamEps
    exact (div_le_self hlam hsqrt).trans hlamle
  have hlamNorm :
      ‖(lamEps lam ε : ℂ)‖ = lamEps lam ε := by
    simp [Real.norm_eq_abs, abs_of_nonneg hlamEps0]
  have hsum :=
    tsum_norm_symbol_le_cutoffSymbolSumConstant
      ρ hε hεle
  unfold canonicalNoiseMultiplicationL2SecondMomentBudget
  rw [Real.sqrt_sq (mul_nonneg (norm_nonneg _)
    (mul_nonneg (norm_nonneg _)
      (tsum_nonneg fun _ => norm_nonneg _)))]
  rw [hlamNorm]
  unfold noiseFirstMomentConstant
  calc
    lamEps lam ε *
          (‖NoiseModel.whiteNoiseFourierScale‖ *
            ∑' k : Z4, ‖ρ.symbol ε k‖) ≤
        1 *
          (‖NoiseModel.whiteNoiseFourierScale‖ *
            (cutoffSymbolSumConstant ρ *
              ε⁻¹ ^ (8 : ℕ))) := by
      gcongr
    _ =
        ‖NoiseModel.whiteNoiseFourierScale‖ *
          cutoffSymbolSumConstant ρ *
          ε⁻¹ ^ (8 : ℕ) := by ring

/-! ## Geometric routing in the boundary sum -/

/-- A deliberately tiny fixed ratio.  Sixty-four powers of `ε` leave
ample room for all polynomial losses in (3.32). -/
def boundaryGeometricRatio : ℝ :=
  Real.exp (-64)

theorem boundaryGeometricRatio_pos :
    0 < boundaryGeometricRatio :=
  Real.exp_pos _

theorem boundaryGeometricRatio_nonneg :
    0 ≤ boundaryGeometricRatio :=
  boundaryGeometricRatio_pos.le

theorem boundaryGeometricRatio_le_one :
    boundaryGeometricRatio ≤ 1 := by
  unfold boundaryGeometricRatio
  exact Real.exp_le_one_iff.mpr (by norm_num)

/-- The routing inequality `A < r + 2q` turns the two perturbative
ratios into at least `A` powers of the common geometric ratio. -/
theorem mul_order_pow_counterterm_pow_le_boundaryGeometricRatio
    {b c : ℝ} {A r q : ℕ}
    (hb0 : 0 ≤ b) (hb : b ≤ boundaryGeometricRatio)
    (hc0 : 0 ≤ c) (hc : c ≤ boundaryGeometricRatio)
    (hr : 1 ≤ r) (hroute : A < r + 2 * q) :
    b ^ (r - 1) * c ^ (2 * q) ≤
      boundaryGeometricRatio ^ A := by
  have hexponent : A ≤ (r - 1) + 2 * q := by omega
  calc
    b ^ (r - 1) * c ^ (2 * q) ≤
        boundaryGeometricRatio ^ (r - 1) *
          boundaryGeometricRatio ^ (2 * q) := by
      gcongr
      exact pow_nonneg boundaryGeometricRatio_nonneg _
    _ = boundaryGeometricRatio ^
          ((r - 1) + 2 * q) := by
      rw [pow_add]
    _ ≤ boundaryGeometricRatio ^ A :=
      pow_le_pow_of_le_one boundaryGeometricRatio_nonneg
        boundaryGeometricRatio_le_one hexponent

/-- Order zero has no parametrix ratio, but the routing condition then
puts all `A` geometric powers into the counterterm. -/
theorem counterterm_pow_le_boundaryGeometricRatio
    {c : ℝ} {A q : ℕ}
    (hc0 : 0 ≤ c) (hc : c ≤ boundaryGeometricRatio)
    (hroute : A < 2 * q) :
    c ^ (2 * q) ≤ boundaryGeometricRatio ^ A := by
  have hexponent : A ≤ 2 * q := hroute.le
  calc
    c ^ (2 * q) ≤ boundaryGeometricRatio ^ (2 * q) := by
      gcongr
    _ ≤ boundaryGeometricRatio ^ A :=
      pow_le_pow_of_le_one boundaryGeometricRatio_nonneg
        boundaryGeometricRatio_le_one hexponent

/-- Fixed coefficient in the final `ε⁴⁶` boundary envelope. -/
def boundaryFirstMomentConstant
    (outerConstant : ℝ) (ρ : SmoothCutoff) : ℝ :=
  physicalFirstMomentConstant outerConstant *
      noiseFirstMomentConstant ρ * Real.exp 128 +
    9 * (physicalFirstMomentConstant outerConstant + 1) *
      Real.exp 64

theorem boundaryFirstMomentConstant_nonneg
    {outerConstant : ℝ} (ρ : SmoothCutoff) :
    0 ≤ boundaryFirstMomentConstant outerConstant ρ := by
  unfold boundaryFirstMomentConstant
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg
        (physicalFirstMomentConstant_nonneg _)
        (noiseFirstMomentConstant_nonneg ρ))
      (Real.exp_nonneg _))
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (by
          have hK :=
            physicalFirstMomentConstant_nonneg outerConstant
          linarith))
      (Real.exp_nonneg _))

/-! ## The boundary first-moment budget -/

/-- Under the paper's routing condition, sufficiently small fixed
geometric ratios turn the entire finite boundary sum into `O(ε⁴⁶)`.
The exponent is deliberately stronger than the required `30`. -/
theorem canonicalPerrLeftBoundaryFirstMomentBudget_le_coarse
    {outerConstant powerConstant Crenorm lam ε : ℝ}
    (ρ : SmoothCutoff)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hCrenorm : 0 ≤ Crenorm)
    (hlam : 0 ≤ lam) (hlamle : lam ≤ 1)
    (hpowerRatio :
      powerConstant * lam ≤ boundaryGeometricRatio)
    (hrenormRatio :
      Crenorm * lam ≤ boundaryGeometricRatio)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) :
    canonicalPerrLeftBoundaryFirstMomentBudget
        outerConstant powerConstant ρ lam ε (truncOrder ε)
        (fun q =>
          ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
            (Crenorm * lam) ^ (2 * q)) ≤
      boundaryFirstMomentConstant outerConstant ρ *
        ε ^ (46 : ℕ) := by
  let A : ℕ := truncOrder ε
  let K : ℝ := physicalFirstMomentConstant outerConstant
  let N : ℝ := noiseFirstMomentConstant ρ
  let b : ℝ := powerConstant * lam
  let c : ℝ := Crenorm * lam
  let θ : ℝ := boundaryGeometricRatio
  let R : ℕ → ℝ :=
    fun q =>
      ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
        c ^ (2 * q)
  let T : ℕ → ℕ → ℝ :=
    fun r q =>
      Real.sqrt
          (canonicalPhysicalParametrixOrderL2SecondMomentBudget
            outerConstant powerConstant lam ε r) *
        R q
  let X : ℝ :=
    (K + 1) * θ ^ A * ε⁻¹ ^ (12 : ℕ)
  have hK : 0 ≤ K :=
    physicalFirstMomentConstant_nonneg _
  have hN : 0 ≤ N :=
    noiseFirstMomentConstant_nonneg ρ
  have hb0 : 0 ≤ b := by
    dsimp [b]
    positivity
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hθ0 : 0 ≤ θ := by
    simpa only [θ] using boundaryGeometricRatio_nonneg
  have hθ1 : θ ≤ 1 := by
    simpa only [θ] using boundaryGeometricRatio_le_one
  have hb : b ≤ θ := by
    simpa only [b, θ] using hpowerRatio
  have hc : c ≤ θ := by
    simpa only [c, θ] using hrenormRatio
  have hA : 1 ≤ A := by
    dsimp [A, truncOrder]
    exact Nat.le_floor (by exact_mod_cast hlog)
  have hinv1 : 1 ≤ ε⁻¹ :=
    (one_le_inv₀ hε).2 hεle
  have hinvPow :
      ε⁻¹ ^ (2 : ℕ) ≤ ε⁻¹ ^ (12 : ℕ) :=
    pow_le_pow_right₀ hinv1 (by norm_num)
  have hthetaA :
      θ ^ A ≤ Real.exp 64 * ε ^ (64 : ℕ) := by
    simpa [θ, A, boundaryGeometricRatio] using
      (exp_neg_nat_pow_truncOrder_le 64 hε hεle)
  have hthetaShift :
      θ ^ (A - 1) ≤ Real.exp 128 * ε ^ (64 : ℕ) := by
    simpa [θ, A, boundaryGeometricRatio,
      show (2 : ℝ) * 64 = 128 by norm_num] using
      (exp_neg_nat_pow_truncOrder_sub_one_le
        64 hε hεle hA)
  have horderHead :
      Real.sqrt
          (canonicalPhysicalParametrixOrderL2SecondMomentBudget
            outerConstant powerConstant lam ε A) ≤
        K * b ^ (A - 1) * ε⁻¹ ^ (10 : ℕ) := by
    simpa only [K, b, A] using
      (sqrt_canonicalPhysicalParametrixOrderL2SecondMomentBudget_le
        hA houter hpower hlam hlamle hlog)
  have hnoise :
      Real.sqrt
          (canonicalNoiseMultiplicationL2SecondMomentBudget
            ρ lam ε) ≤
        N * ε⁻¹ ^ (8 : ℕ) := by
    simpa only [N] using
      (sqrt_canonicalNoiseMultiplicationL2SecondMomentBudget_le
        ρ hlam hlamle hε hεle hlog)
  have hbHead :
      b ^ (A - 1) ≤ θ ^ (A - 1) := by
    gcongr
  have hhead :
      Real.sqrt
          (canonicalPhysicalParametrixOrderL2SecondMomentBudget
            outerConstant powerConstant lam ε A) *
        Real.sqrt
          (canonicalNoiseMultiplicationL2SecondMomentBudget
            ρ lam ε) ≤
        K * N * Real.exp 128 * ε ^ (46 : ℕ) := by
    calc
      Real.sqrt
            (canonicalPhysicalParametrixOrderL2SecondMomentBudget
              outerConstant powerConstant lam ε A) *
          Real.sqrt
            (canonicalNoiseMultiplicationL2SecondMomentBudget
              ρ lam ε) ≤
          (K * b ^ (A - 1) * ε⁻¹ ^ (10 : ℕ)) *
            (N * ε⁻¹ ^ (8 : ℕ)) := by
        exact mul_le_mul horderHead hnoise
          (Real.sqrt_nonneg _)
          (mul_nonneg
            (mul_nonneg hK (pow_nonneg hb0 _))
            (by positivity))
      _ ≤
          (K * θ ^ (A - 1) * ε⁻¹ ^ (10 : ℕ)) *
            (N * ε⁻¹ ^ (8 : ℕ)) := by
        gcongr
      _ ≤
          (K * (Real.exp 128 * ε ^ (64 : ℕ)) *
              ε⁻¹ ^ (10 : ℕ)) *
            (N * ε⁻¹ ^ (8 : ℕ)) := by
        gcongr
      _ = K * N * Real.exp 128 * ε ^ (46 : ℕ) := by
        field_simp [hε.ne']
  have hRnonneg (q : ℕ) : 0 ≤ R q := by
    dsimp [R]
    positivity
  have hRle (q : ℕ) :
      R q ≤ ε⁻¹ ^ (2 : ℕ) * c ^ (2 * q) := by
    dsimp [R]
    have hdiv :
        ε⁻¹ ^ (2 : ℕ) / |Real.log ε| ≤
          ε⁻¹ ^ (2 : ℕ) :=
      div_le_self (by positivity) hlog
    exact mul_le_mul_of_nonneg_right hdiv
      (pow_nonneg hc0 _)
  have hX : 0 ≤ X := by
    dsimp [X]
    positivity
  have hterm :
      ∀ r ∈ Finset.range (A + 1),
        ∀ q ∈ (Finset.Icc 1 A).filter
          (fun q => A < r + 2 * q),
          T r q ≤ X := by
    intro r hr q hq
    have hrA : r ≤ A :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    have hqdata :=
      Finset.mem_filter.mp hq
    have hroute : A < r + 2 * q := hqdata.2
    by_cases hr0 : r = 0
    · subst r
      have hcgeom :
          c ^ (2 * q) ≤ θ ^ A := by
        apply counterterm_pow_le_boundaryGeometricRatio
          hc0 hc
        simpa using hroute
      dsimp [T]
      rw [canonicalPhysicalParametrixOrderL2SecondMomentBudget,
        if_pos rfl, Real.sqrt_one, one_mul]
      calc
        R q ≤ ε⁻¹ ^ (2 : ℕ) * c ^ (2 * q) :=
          hRle q
        _ ≤ ε⁻¹ ^ (2 : ℕ) * θ ^ A := by
          gcongr
        _ ≤ ε⁻¹ ^ (12 : ℕ) * θ ^ A := by
          gcongr
        _ ≤ (K + 1) *
              (ε⁻¹ ^ (12 : ℕ) * θ ^ A) := by
          have hK1 : 1 ≤ K + 1 := by linarith
          have hY :
              0 ≤ ε⁻¹ ^ (12 : ℕ) * θ ^ A :=
            mul_nonneg (by positivity) (pow_nonneg hθ0 A)
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hK1 hY)
        _ = X := by
          dsimp [X]
          ring
    · have hr1 : 1 ≤ r :=
        Nat.one_le_iff_ne_zero.mpr hr0
      have horder :
          Real.sqrt
              (canonicalPhysicalParametrixOrderL2SecondMomentBudget
                outerConstant powerConstant lam ε r) ≤
            K * b ^ (r - 1) * ε⁻¹ ^ (10 : ℕ) := by
        simpa only [K, b] using
          (sqrt_canonicalPhysicalParametrixOrderL2SecondMomentBudget_le
            hr1 houter hpower hlam hlamle hlog)
      have hgeom :
          b ^ (r - 1) * c ^ (2 * q) ≤ θ ^ A := by
        exact
          mul_order_pow_counterterm_pow_le_boundaryGeometricRatio
            hb0 hb hc0 hc hr1 hroute
      dsimp [T]
      calc
        Real.sqrt
              (canonicalPhysicalParametrixOrderL2SecondMomentBudget
                outerConstant powerConstant lam ε r) *
            R q ≤
          (K * b ^ (r - 1) * ε⁻¹ ^ (10 : ℕ)) *
            (ε⁻¹ ^ (2 : ℕ) * c ^ (2 * q)) := by
          exact mul_le_mul horder (hRle q)
            (hRnonneg q)
            (mul_nonneg
              (mul_nonneg hK (pow_nonneg hb0 _))
              (by positivity))
        _ =
            K * (b ^ (r - 1) * c ^ (2 * q)) *
              ε⁻¹ ^ (12 : ℕ) := by ring
        _ ≤ K * θ ^ A * ε⁻¹ ^ (12 : ℕ) := by
          gcongr
        _ ≤ (K + 1) * θ ^ A *
              ε⁻¹ ^ (12 : ℕ) := by
          have hKle : K ≤ K + 1 := by linarith
          gcongr
        _ = X := by
          dsimp [X]
  have hinner :
      ∀ r ∈ Finset.range (A + 1),
        (∑ q ∈ (Finset.Icc 1 A).filter
            (fun q => A < r + 2 * q), T r q) ≤
          (A + 1 : ℝ) * X := by
    intro r hr
    let s :=
      (Finset.Icc 1 A).filter
        (fun q => A < r + 2 * q)
    have hsubset : s ⊆ Finset.range (A + 1) := by
      intro q hq
      have hqIcc :=
        (Finset.mem_filter.mp hq).1
      exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Finset.mem_Icc.mp hqIcc).2)
    have hcard : (s.card : ℝ) ≤ (A + 1 : ℝ) := by
      have hcardNat := Finset.card_le_card hsubset
      rw [Finset.card_range] at hcardNat
      exact_mod_cast hcardNat
    change (∑ q ∈ s, T r q) ≤ _
    calc
      (∑ q ∈ s, T r q) ≤ ∑ _q ∈ s, X :=
        Finset.sum_le_sum fun q hq => hterm r hr q hq
      _ = (s.card : ℝ) * X := by
        simp [nsmul_eq_mul]
      _ ≤ (A + 1 : ℝ) * X :=
        mul_le_mul_of_nonneg_right hcard hX
  have htail :
      (∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ (Finset.Icc 1 A).filter
            (fun q => A < r + 2 * q), T r q) ≤
        (A + 1 : ℝ) * ((A + 1 : ℝ) * X) := by
    calc
      (∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ (Finset.Icc 1 A).filter
            (fun q => A < r + 2 * q), T r q) ≤
          ∑ _r ∈ Finset.range (A + 1),
            ((A + 1 : ℝ) * X) :=
        Finset.sum_le_sum fun r hr => hinner r hr
      _ = (A + 1 : ℝ) * ((A + 1 : ℝ) * X) := by
        simp [nsmul_eq_mul]
  have hepsSqrt :
      ε ≤ Real.sqrt ε := by
    nlinarith [Real.sq_sqrt hε.le, Real.sqrt_nonneg ε]
  have hsqrtInv :
      (Real.sqrt ε)⁻¹ ≤ ε⁻¹ :=
    (inv_le_inv₀ (Real.sqrt_pos.2 hε) hε).2 hepsSqrt
  have hAupper :
      (A : ℝ) ≤ 2 * ε⁻¹ := by
    dsimp [A]
    exact
      (truncOrder_cast_le_two_mul_inv_sqrt hε hεle).trans
        (mul_le_mul_of_nonneg_left hsqrtInv (by norm_num))
  have hA1 :
      (A + 1 : ℝ) ≤ 3 * ε⁻¹ := by
    nlinarith
  have htailCoarse :
      (∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ (Finset.Icc 1 A).filter
            (fun q => A < r + 2 * q), T r q) ≤
        9 * (K + 1) * Real.exp 64 *
          ε ^ (50 : ℕ) := by
    calc
      (∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ (Finset.Icc 1 A).filter
            (fun q => A < r + 2 * q), T r q) ≤
          (A + 1 : ℝ) * ((A + 1 : ℝ) * X) :=
        htail
      _ ≤ (3 * ε⁻¹) * ((3 * ε⁻¹) * X) := by
        gcongr
      _ = 9 * (K + 1) * θ ^ A *
            ε⁻¹ ^ (14 : ℕ) := by
        dsimp [X]
        ring
      _ ≤ 9 * (K + 1) *
            (Real.exp 64 * ε ^ (64 : ℕ)) *
            ε⁻¹ ^ (14 : ℕ) := by
        gcongr
      _ = 9 * (K + 1) * Real.exp 64 *
            ε ^ (50 : ℕ) := by
        field_simp [hε.ne']
  have hepsPow :
      ε ^ (50 : ℕ) ≤ ε ^ (46 : ℕ) :=
    pow_le_pow_of_le_one hε.le hεle (by norm_num)
  unfold canonicalPerrLeftBoundaryFirstMomentBudget
  change
    Real.sqrt
          (canonicalPhysicalParametrixOrderL2SecondMomentBudget
            outerConstant powerConstant lam ε A) *
        Real.sqrt
          (canonicalNoiseMultiplicationL2SecondMomentBudget
            ρ lam ε) +
      (∑ r ∈ Finset.range (A + 1),
        ∑ q ∈ (Finset.Icc 1 A).filter
          (fun q => A < r + 2 * q), T r q) ≤ _
  calc
    Real.sqrt
          (canonicalPhysicalParametrixOrderL2SecondMomentBudget
            outerConstant powerConstant lam ε A) *
        Real.sqrt
          (canonicalNoiseMultiplicationL2SecondMomentBudget
            ρ lam ε) +
      (∑ r ∈ Finset.range (A + 1),
        ∑ q ∈ (Finset.Icc 1 A).filter
          (fun q => A < r + 2 * q), T r q) ≤
        K * N * Real.exp 128 * ε ^ (46 : ℕ) +
          9 * (K + 1) * Real.exp 64 *
            ε ^ (50 : ℕ) :=
      add_le_add hhead htailCoarse
    _ ≤ K * N * Real.exp 128 * ε ^ (46 : ℕ) +
          9 * (K + 1) * Real.exp 64 *
            ε ^ (46 : ℕ) := by
      gcongr
    _ = boundaryFirstMomentConstant outerConstant ρ *
          ε ^ (46 : ℕ) := by
      dsimp [K, N]
      unfold boundaryFirstMomentConstant
      ring

/-- The coarse `ε⁴⁶` estimate eventually meets the exact `ε³⁰`
first-moment threshold of paper (3.32). -/
theorem eventually_canonicalPerrLeftBoundaryFirstMomentBudget_le
    {outerConstant powerConstant Crenorm lam : ℝ}
    (ρ : SmoothCutoff)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hCrenorm : 0 ≤ Crenorm)
    (hlam : 0 ≤ lam) (hlamle : lam ≤ 1)
    (hpowerRatio :
      powerConstant * lam ≤ boundaryGeometricRatio)
    (hrenormRatio :
      Crenorm * lam ≤ boundaryGeometricRatio) :
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
      canonicalPerrLeftBoundaryFirstMomentBudget
          outerConstant powerConstant ρ lam ε (truncOrder ε)
          (fun q =>
            ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
              (Crenorm * lam) ^ (2 * q)) ≤
        ε ^ (30 : ℕ) := by
  let C : ℝ :=
    boundaryFirstMomentConstant outerConstant ρ
  have hC : 0 ≤ C :=
    boundaryFirstMomentConstant_nonneg ρ
  have hid :
      Tendsto (fun ε : ℝ => ε)
        (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hvanish :
      Tendsto (fun ε : ℝ => C * ε ^ (16 : ℕ))
        (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    simpa using
      (hid.pow 16).const_mul C
  have habsorb :
      ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
        C * ε ^ (16 : ℕ) ≤ 1 :=
    hvanish.eventually_le_const zero_lt_one
  filter_upwards
      [self_mem_nhdsWithin,
        eventually_smallScale_le zero_lt_one,
        eventually_one_le_abs_log,
        habsorb] with
      ε hε hεle hlog habsorbε
  have hεpos : 0 < ε := hε
  have hcoarse :=
    canonicalPerrLeftBoundaryFirstMomentBudget_le_coarse
      ρ houter hpower hCrenorm hlam hlamle
      hpowerRatio hrenormRatio hεpos hεle hlog
  calc
    canonicalPerrLeftBoundaryFirstMomentBudget
        outerConstant powerConstant ρ lam ε (truncOrder ε)
        (fun q =>
          ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
            (Crenorm * lam) ^ (2 * q)) ≤
        C * ε ^ (46 : ℕ) := by
      simpa only [C] using hcoarse
    _ = (C * ε ^ (16 : ℕ)) * ε ^ (30 : ℕ) := by
      ring
    _ ≤ 1 * ε ^ (30 : ℕ) := by
      gcongr
    _ = ε ^ (30 : ℕ) := one_mul _

/-- Coupling threshold chosen after the named deterministic constants
but before `λ` and `ε`.  Below this threshold both numerical budgets
close simultaneously. -/
theorem exists_couplingThreshold_eventually_oneSidedBudgets
    {outerConstant powerConstant Crenorm : ℝ}
    (ρ : SmoothCutoff)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hCrenorm : 0 ≤ Crenorm) :
    ∃ lam0 : ℝ, 0 < lam0 ∧
      ∀ lam : ℝ, 0 ≤ lam → lam < lam0 →
        (∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
          canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
              outerConstant powerConstant lam ε (truncOrder ε) ≤
            ε ^ (-24 : ℤ)) ∧
        (∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
          canonicalPerrLeftBoundaryFirstMomentBudget
              outerConstant powerConstant ρ lam ε (truncOrder ε)
              (fun q =>
                ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
                  (Crenorm * lam) ^ (2 * q)) ≤
            ε ^ (30 : ℕ)) := by
  let D : ℝ := powerConstant + Crenorm + 1
  let lam0 : ℝ :=
    min 1 (boundaryGeometricRatio / D)
  have hD : 0 < D := by
    dsimp [D]
    linarith
  have hquot :
      0 < boundaryGeometricRatio / D :=
    div_pos boundaryGeometricRatio_pos hD
  have hlam0 : 0 < lam0 := by
    dsimp [lam0]
    exact lt_min zero_lt_one hquot
  refine ⟨lam0, hlam0, fun lam hlam hlamlt => ?_⟩
  have hlamle1 : lam ≤ 1 :=
    (le_of_lt hlamlt).trans
      (min_le_left 1 (boundaryGeometricRatio / D))
  have hlamlequot :
      lam ≤ boundaryGeometricRatio / D :=
    (le_of_lt hlamlt).trans
      (min_le_right 1 (boundaryGeometricRatio / D))
  have hDlam :
      D * lam ≤ boundaryGeometricRatio := by
    have :=
      (le_div_iff₀ hD).1 hlamlequot
    simpa [mul_comm] using this
  have hpowerD : powerConstant ≤ D := by
    dsimp [D]
    linarith
  have hCrenormD : Crenorm ≤ D := by
    dsimp [D]
    linarith
  have hpowerRatio :
      powerConstant * lam ≤ boundaryGeometricRatio :=
    (mul_le_mul_of_nonneg_right hpowerD hlam).trans
      hDlam
  have hrenormRatio :
      Crenorm * lam ≤ boundaryGeometricRatio :=
    (mul_le_mul_of_nonneg_right hCrenormD hlam).trans
      hDlam
  refine ⟨?_, ?_⟩
  · exact
      eventually_canonicalPhysicalTruncatedParametrixL2SecondMomentBudget_le
        houter hpower hlam hlamle1
        (hpowerRatio.trans boundaryGeometricRatio_le_one)
  · exact
      eventually_canonicalPerrLeftBoundaryFirstMomentBudget_le
        ρ houter hpower hCrenorm hlam hlamle1
        hpowerRatio hrenormRatio

/-! ## Final numerical good-event closure -/

/-- Adapter from the moving deterministic P-3.5a/P-3.5b/P-3.4 inputs
to the exact `2 ε²` exceptional-set estimate.  No numerical budget
hypothesis remains. -/
theorem
    eventually_measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_two_mul_sq
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant Crenorm lam : ℝ}
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hCrenorm : 0 ≤ Crenorm)
    (hlam : 0 ≤ lam) (hlamle : lam ≤ 1)
    (hpowerRatio :
      powerConstant * lam ≤ boundaryGeometricRatio)
    (hrenormRatio :
      Crenorm * lam ≤ boundaryGeometricRatio)
    (hdet :
      ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
        ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
          ‖deterministicMomentPairingSum
              ρ lam ε m α β‖ ≤
            deterministicMomentRHS
              outerConstant powerConstant lam ε m α β)
    (hagree :
      ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
        ∀ᵐ ω ∂(volume : Measure M.Ω),
          ParametrixGradedCoefficientAgreement
            M ρ lam ε (truncOrder ε) ω)
    (hcounter :
      ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
        ∀ q ∈ Finset.Icc 1 (truncOrder ε),
          |renormC2q ρ lam ε q| ≤
            ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
              (Crenorm * lam) ^ (2 * q)) :
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
      (volume : Measure M.Ω).real
          (canonicalOneSidedL2ParametrixGoodEvent
            M ρ lam ε (truncOrder ε)
            (canonicalGradedTruncatedParametrixL2Factor
              M ρ lam ε (truncOrder ε))
            (canonicalPerrLeftRemainder
              M ρ lam ε (truncOrder ε)))ᶜ ≤
        2 * ε ^ 2 := by
  have hphysical :=
    eventually_canonicalPhysicalTruncatedParametrixL2SecondMomentBudget_le
      houter hpower hlam hlamle
      (hpowerRatio.trans boundaryGeometricRatio_le_one)
  have hboundary :=
    eventually_canonicalPerrLeftBoundaryFirstMomentBudget_le
      ρ houter hpower hCrenorm hlam hlamle
      hpowerRatio hrenormRatio
  filter_upwards
      [self_mem_nhdsWithin,
        eventually_smallScale_le zero_lt_one,
        hphysical, hboundary, hdet, hagree, hcounter] with
      ε hε hεle hphysicalε hboundaryε
      hdetε hagreeε hcounterε
  have hεpos : 0 < ε := hε
  exact
    measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_two_mul_sq_of_budgets
      (fun q =>
        ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
          (Crenorm * lam) ^ (2 * q))
      hdetε houter hpower hlam hεpos hεle
      hphysicalε hagreeε hcounterε hboundaryε

end PartialPairing

end

end Anderson4D
