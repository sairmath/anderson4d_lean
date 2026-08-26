import Anderson4D.Continuum.PrimitiveEndpointPeriodic
import Anderson4D.Continuum.PrimitiveBaseBound

/-!
# Scaling ledger for the endpoint-preserving R-51 estimate

This file converts the natural dyadic logarithm and the compatible periodic
mesh in `PrimitiveEndpointPeriodic` to the real logarithm and covariance
scale occurring in Proposition 4.1.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open scoped BigOperators

noncomputable section

/-- The dyadic logarithm occurring in the endpoint Hepp-tree estimate. -/
def primitiveDyadicPeriodLog (q : ℕ) : ℕ :=
  Nat.log 2 (4 * (2 * q)) + 1

theorem primitiveDyadicPeriodLog_pos (q : ℕ) :
    0 < primitiveDyadicPeriodLog q := by
  unfold primitiveDyadicPeriodLog
  omega

/-- The reciprocal covariance scale is below the compatible period count,
and hence below the enlarged dyadic carrier used by R-51. -/
theorem inv_le_eight_mul_compatiblePeriod
    {ε : ℝ} (hε : 0 < ε)
    {q : ℕ} (hqε : (q : ℤ) = compatibleCellCount ε) :
    ε⁻¹ ≤ (4 * (2 * q) : ℕ) := by
  have hqcast :
      (q : ℝ) = (compatibleCellCount ε : ℝ) := by
    exact_mod_cast hqε
  have hceil :
      (2 * Real.pi) / ε ≤
        (compatibleCellCount ε : ℝ) :=
    Int.le_ceil _
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hinvq : ε⁻¹ ≤ (q : ℝ) := by
    calc
      ε⁻¹ = 1 / ε := by rw [one_div]
      _ ≤ (2 * Real.pi) / ε :=
        (div_le_div_iff_of_pos_right hε).2 hpi
      _ ≤ (compatibleCellCount ε : ℝ) := hceil
      _ = q := hqcast.symm
  calc
    ε⁻¹ ≤ (q : ℝ) := hinvq
    _ ≤ (4 * (2 * q) : ℕ) := by
      norm_cast
      omega

/-- The real logarithmic scale is bounded above by the natural dyadic
logarithm selected by the compatible period. -/
theorem abs_log_le_primitiveDyadicPeriodLog
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {q : ℕ} (hqε : (q : ℤ) = compatibleCellCount ε) :
    |Real.log ε| ≤ (primitiveDyadicPeriodLog q : ℝ) := by
  let N : ℕ := 4 * (2 * q)
  let L : ℕ := primitiveDyadicPeriodLog q
  have hqposZ : (0 : ℤ) < (q : ℤ) := by
    rw [hqε]
    exact compatibleCellCount_pos hε
  have hqpos : 0 < q := by exact_mod_cast hqposZ
  have hNpos : 0 < N := by
    dsimp only [N]
    positivity
  have hpowNat : N < 2 ^ L := by
    dsimp only [L, primitiveDyadicPeriodLog, N]
    exact Nat.lt_pow_succ_log_self (by omega) _
  have hpowReal : (N : ℝ) < (2 : ℝ) ^ L := by
    exact_mod_cast hpowNat
  have hinvpos : 0 < ε⁻¹ := inv_pos.mpr hε
  have hinvN : ε⁻¹ ≤ (N : ℝ) := by
    simpa only [N] using
      inv_le_eight_mul_compatiblePeriod hε hqε
  have hlogInv :
      Real.log ε⁻¹ < Real.log ((2 : ℝ) ^ L) := by
    exact Real.log_lt_log hinvpos (hinvN.trans_lt hpowReal)
  have hlogTwoLtOne : Real.log 2 < 1 := by
    have h :=
      Real.log_lt_sub_one_of_pos
        (show (0 : ℝ) < 2 by norm_num)
        (show (2 : ℝ) ≠ 1 by norm_num)
    norm_num at h
    exact h
  have hL0 : 0 ≤ (L : ℝ) := by positivity
  have hlogPow :
      Real.log ((2 : ℝ) ^ L) =
        (L : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  have hlogInvLt : Real.log ε⁻¹ < (L : ℝ) := by
    calc
      Real.log ε⁻¹ <
          Real.log ((2 : ℝ) ^ L) := hlogInv
      _ = (L : ℝ) * Real.log 2 := hlogPow
      _ ≤ (L : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hlogTwoLtOne.le hL0
      _ = (L : ℝ) := by ring
  have habs : |Real.log ε| = Real.log ε⁻¹ := by
    rw [Real.log_inv]
    exact abs_of_nonpos (Real.log_nonpos hε.le hε1)
  rw [habs]
  exact hlogInvLt.le

/-- A coarse upper comparison in the small-scale regime used below.

The deliberately generous factor `100` absorbs the harmless ceiling and
torus-period constants already when `2 ≤ |log ε|`.  This weaker threshold is
essential at the public Proposition 4.1 boundary: together with `2 ≤ n` and
`n ≤ |log ε|`, it covers every order up to the paper's truncation
`⌊|log ε|⌋`. -/
theorem primitiveDyadicPeriodLog_le_hundred_abs_log
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlogLarge : 2 ≤ |Real.log ε|)
    {q : ℕ} (hqε : (q : ℤ) = compatibleCellCount ε) :
    (primitiveDyadicPeriodLog q : ℝ) ≤
      100 * |Real.log ε| := by
  let N : ℕ := 4 * (2 * q)
  let k : ℕ := Nat.log 2 N
  let L : ℕ := primitiveDyadicPeriodLog q
  have hqposZ : (0 : ℤ) < (q : ℤ) := by
    rw [hqε]
    exact compatibleCellCount_pos hε
  have hqpos : 0 < q := by exact_mod_cast hqposZ
  have hNpos : 0 < N := by
    dsimp only [N]
    positivity
  have hqcast :
      (q : ℝ) = (compatibleCellCount ε : ℝ) := by
    exact_mod_cast hqε
  have hceil :
      (compatibleCellCount ε : ℝ) <
        (2 * Real.pi) / ε + 1 :=
    Int.ceil_lt_add_one _
  have hpi : 2 * Real.pi + ε < 9 := by
    nlinarith [Real.pi_lt_four]
  have hqUpper : (q : ℝ) < 9 / ε := by
    rw [hqcast]
    calc
      (compatibleCellCount ε : ℝ) <
          (2 * Real.pi) / ε + 1 := hceil
      _ = (2 * Real.pi + ε) / ε := by
        field_simp [ne_of_gt hε]
      _ < 9 / ε :=
        (div_lt_div_iff_of_pos_right hε).2 hpi
  have hNUpper : (N : ℝ) < 72 / ε := by
    calc
      (N : ℝ) = 8 * (q : ℝ) := by
        dsimp only [N]
        push_cast
        ring
      _ < 8 * (9 / ε) :=
        mul_lt_mul_of_pos_left hqUpper (by norm_num)
      _ = 72 / ε := by ring
  have hpowLowerNat : 2 ^ k ≤ N := by
    exact Nat.pow_log_le_self 2 (ne_of_gt hNpos)
  have hpowLowerReal : (2 : ℝ) ^ k ≤ (N : ℝ) := by
    exact_mod_cast hpowLowerNat
  have hlogNUpper :
      Real.log (N : ℝ) ≤
        Real.log 72 + |Real.log ε| := by
    have h72 : (0 : ℝ) < 72 := by norm_num
    have hlogLt :
        Real.log (N : ℝ) < Real.log (72 / ε) :=
      Real.log_lt_log (by exact_mod_cast hNpos) hNUpper
    have hεne : ε ≠ 0 := ne_of_gt hε
    have habs : |Real.log ε| = -Real.log ε :=
      abs_of_nonpos (Real.log_nonpos hε.le hε1)
    calc
      Real.log (N : ℝ) ≤ Real.log (72 / ε) :=
        hlogLt.le
      _ = Real.log 72 - Real.log ε :=
        Real.log_div h72.ne' hεne
      _ = Real.log 72 + |Real.log ε| := by
        rw [habs]
        ring
  have hlog72 : Real.log 72 ≤ 71 := by
    simpa only [show (71 : ℝ) = 72 - 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 72)
  have hlogNUpper' :
      Real.log (N : ℝ) ≤ 37 * |Real.log ε| := by
    calc
      Real.log (N : ℝ) ≤
          Real.log 72 + |Real.log ε| := hlogNUpper
      _ ≤ 71 + |Real.log ε| := by linarith
      _ ≤ 37 * |Real.log ε| := by linarith
  have hlogLower :
      (k : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
    have hlogMono :=
      Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) k)
        hpowLowerReal
    simpa only [Real.log_pow] using hlogMono
  have hlogTwoLower : (1 / 2 : ℝ) ≤ Real.log 2 := by
    exact (by
      have := Real.log_two_gt_d9
      norm_num at this ⊢
      linarith)
  have hk :
      (k : ℝ) ≤ 74 * |Real.log ε| := by
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    have hhalf :
        (k : ℝ) * (1 / 2 : ℝ) ≤
          (k : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlogTwoLower hk0
    nlinarith [hhalf.trans (hlogLower.trans hlogNUpper')]
  have hL : L = k + 1 := by
    rfl
  change (L : ℝ) ≤ 100 * |Real.log ε|
  rw [hL]
  push_cast
  have hone : (1 : ℝ) ≤ |Real.log ε| := by
    linarith
  linarith

/-- Up to the paper's full truncation window `n ≤ |log ε|`, the R-51
hypothesis is available with the fixed natural constant `K = 1`. -/
theorem order_le_primitiveDyadicPeriodLog
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {n q : ℕ} (_hn : 1 ≤ n)
    (horder : (n : ℝ) ≤ |Real.log ε|)
    (hqε : (q : ℤ) = compatibleCellCount ε) :
    n ≤ primitiveDyadicPeriodLog q := by
  have hlogL :=
    abs_log_le_primitiveDyadicPeriodLog hε hε1 hqε
  exact_mod_cast horder.trans hlogL

/-! ## Exponential absorption of the Hepp-tree coefficient -/

theorem real_natCast_sq_le_four_pow
    (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) ^ 2 ≤ (4 : ℝ) ^ n := by
  have hnat : n ^ 2 ≤ 4 ^ n := by
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
        have hstep : (n + 1) ^ 2 ≤ 4 * n ^ 2 := by
          nlinarith
        calc
          (n + 1) ^ 2 ≤ 4 * n ^ 2 := hstep
          _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_left 4 ih
          _ = 4 ^ (n + 1) := by
            rw [pow_succ]
            ring
  exact_mod_cast hnat

theorem two_le_two_pow (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) ≤ (2 : ℝ) ^ n := by
  calc
    (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := by
      exact pow_le_pow_right₀ (by norm_num) hn

/-- A single fixed base which absorbs every non-logarithmic factor in
`primitiveEndpointUniformCoefficient C M n 1`. -/
def primitiveEndpointCoefficientBase (C : ℝ) : ℝ :=
  (4 : ℝ) ^ 8 *
    (2 *
      (16 +
        ((16 * volumeEstimateFinalConstant) ^ 2 *
          (2 * (8192 * C)))))

theorem primitiveEndpointCoefficientBase_pos
    {C : ℝ} (hC : 0 ≤ C) :
    0 < primitiveEndpointCoefficientBase C := by
  unfold primitiveEndpointCoefficientBase
  have hvol : 0 ≤ volumeEstimateFinalConstant := by
    unfold volumeEstimateFinalConstant
    positivity
  positivity

/-- The full endpoint coefficient is one exponential times the exact
`L^(n-2)` critical logarithmic power. -/
theorem primitiveEndpointUniformCoefficient_le_base_pow
    {C : ℝ} (hC : 0 ≤ C)
    (M n : ℕ) (hn : 2 ≤ n) :
    primitiveEndpointUniformCoefficient C M n 1 ≤
      primitiveEndpointCoefficientBase C ^ n *
        (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
          (n - 2)) := by
  let L : ℝ :=
    (Nat.log 2 (4 * M) : ℝ) + 1
  let d : ℝ := 8192 * C
  let b : ℝ := (16 * volumeEstimateFinalConstant) ^ 2
  let S : ℝ := 16 + b * (2 * d)
  have hL : 0 ≤ L := by positivity
  have hd : 0 ≤ d := by
    dsimp only [d]
    positivity
  have hb : 0 ≤ b := by
    dsimp only [b]
    positivity
  have hS : 0 ≤ S := by
    dsimp only [S]
    positivity
  have htwo : (2 : ℝ) ≤ 2 ^ n :=
    two_le_two_pow n (by omega)
  have hsmallBase : 512 * C ≤ d := by
    dsimp only [d]
    nlinarith
  have hlargeBase : 4 * (2048 * C) = d := by
    dsimp only [d]
    ring
  have hsmall :
      ((2 : ℝ) ^ n * (256 * C) ^ n) ≤ d ^ n := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have hlarge :
      ((n : ℝ) ^ 2 * (2048 * C) ^ n) ≤ d ^ n := by
    calc
      (n : ℝ) ^ 2 * (2048 * C) ^ n ≤
          (4 : ℝ) ^ n * (2048 * C) ^ n := by
        apply mul_le_mul_of_nonneg_right
          (real_natCast_sq_le_four_pow n hn)
        positivity
      _ = d ^ n := by
        rw [← mul_pow, hlargeBase]
  have hpair :
      (2 : ℝ) ^ n * (256 * C) ^ n +
          (n : ℝ) ^ 2 * (2048 * C) ^ n ≤
        (2 * d) ^ n := by
    calc
      (2 : ℝ) ^ n * (256 * C) ^ n +
          (n : ℝ) ^ 2 * (2048 * C) ^ n ≤
        d ^ n + d ^ n := add_le_add hsmall hlarge
      _ = 2 * d ^ n := by ring
      _ ≤ 2 ^ n * d ^ n := by
        apply mul_le_mul_of_nonneg_right htwo
        positivity
      _ = (2 * d) ^ n := by
        dsimp only [d]
        simp only [mul_pow]
  have hvolume :
      (16 * volumeEstimateFinalConstant) ^ (2 * n) =
        b ^ n := by
    dsimp only [b]
    rw [← pow_mul]
  have hsecond :
      (16 * volumeEstimateFinalConstant) ^ (2 * n) *
          (((2 : ℝ) ^ n * (256 * C) ^ n) +
            (n : ℝ) ^ 2 * (2048 * C) ^ n) ≤
        (b * (2 * d)) ^ n := by
    rw [hvolume]
    calc
      b ^ n *
          ((2 : ℝ) ^ n * (256 * C) ^ n +
            (n : ℝ) ^ 2 * (2048 * C) ^ n) ≤
        b ^ n * (2 * d) ^ n :=
          mul_le_mul_of_nonneg_left hpair (pow_nonneg hb n)
      _ = (b * (2 * d)) ^ n := by
        simp only [mul_pow]
  have hinside :
      (16 : ℝ) ^ n +
          (16 * volumeEstimateFinalConstant) ^ (2 * n) *
            (((2 : ℝ) ^ n * (256 * C) ^ n) +
              (n : ℝ) ^ 2 * (2048 * C) ^ n) ≤
        (2 * S) ^ n := by
    have h16S : (16 : ℝ) ≤ S := by
      dsimp only [S]
      exact le_add_of_nonneg_right
        (mul_nonneg hb (mul_nonneg (by positivity) hd))
    have hbS : b * (2 * d) ≤ S := by
      dsimp only [S]
      linarith
    calc
      (16 : ℝ) ^ n +
          (16 * volumeEstimateFinalConstant) ^ (2 * n) *
            (((2 : ℝ) ^ n * (256 * C) ^ n) +
              (n : ℝ) ^ 2 * (2048 * C) ^ n) ≤
        S ^ n + S ^ n := by
          exact add_le_add
            (pow_le_pow_left₀ (by positivity) h16S n)
            (hsecond.trans
              (pow_le_pow_left₀ (by positivity) hbS n))
      _ = 2 * S ^ n := by ring
      _ ≤ 2 ^ n * S ^ n := by
        apply mul_le_mul_of_nonneg_right htwo
        positivity
      _ = (2 * S) ^ n := by rw [mul_pow]
  have houter :
      (4 : ℝ) ^ (8 * n) = ((4 : ℝ) ^ 8) ^ n := by
    rw [pow_mul]
  unfold primitiveEndpointUniformCoefficient
  push_cast
  norm_num
  rw [show 4 * (2 * n) = 8 * n by omega]
  rw [show (32 : ℝ) * (4 * C) * 2 = 256 * C by ring]
  rw [show (256 : ℝ) * (4 * C) * 2 = 2048 * C by ring]
  rw [show (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 by ring]
  change
    (4 : ℝ) ^ (8 * n) *
        ((16 : ℝ) ^ n * L ^ (n - 2) +
          (16 * volumeEstimateFinalConstant) ^ (2 * n) *
            (((2 : ℝ) ^ n *
                ((256 * C) ^ n * L ^ (n - 2))) +
              ((n : ℝ) ^ 2 *
                ((2048 * C) ^ n * L ^ (n - 2))))) ≤
      primitiveEndpointCoefficientBase C ^ n *
        L ^ (n - 2)
  have hfactor :
      (16 : ℝ) ^ n * L ^ (n - 2) +
          (16 * volumeEstimateFinalConstant) ^ (2 * n) *
            (((2 : ℝ) ^ n *
                ((256 * C) ^ n * L ^ (n - 2))) +
              ((n : ℝ) ^ 2 *
                ((2048 * C) ^ n * L ^ (n - 2)))) =
        ((16 : ℝ) ^ n +
          (16 * volumeEstimateFinalConstant) ^ (2 * n) *
            (((2 : ℝ) ^ n * (256 * C) ^ n) +
              ((n : ℝ) ^ 2 * (2048 * C) ^ n))) *
          L ^ (n - 2) := by ring
  rw [hfactor, houter]
  have hbase :
      primitiveEndpointCoefficientBase C =
        (4 : ℝ) ^ 8 * (2 * S) := by
    unfold primitiveEndpointCoefficientBase
    dsimp only [S, b, d]
  rw [hbase,
    mul_pow ((4 : ℝ) ^ 8) (2 * S) n]
  calc
    ((4 : ℝ) ^ 8) ^ n *
        ((16 ^ n +
          (16 * volumeEstimateFinalConstant) ^ (2 * n) *
            (2 ^ n * (256 * C) ^ n +
              (n : ℝ) ^ 2 * (2048 * C) ^ n)) *
          L ^ (n - 2)) ≤
      ((4 : ℝ) ^ 8) ^ n *
        ((2 * S) ^ n * L ^ (n - 2)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right hinside
          (pow_nonneg hL (n - 2))
      · positivity
    _ = ((4 : ℝ) ^ 8) ^ n *
          (2 * S) ^ n * L ^ (n - 2) := by ring

/-! ## Simplifying the periodic endpoint bound -/

def primitiveR51EndpointConstant (R : ℝ) : ℝ :=
  (160000 * (R + 2) ^ 4) ^ 2 *
    (9 * (1 + 4 * R ^ 2)) ^ 2

theorem primitiveR51EndpointConstant_nonneg (R : ℝ) :
    0 ≤ primitiveR51EndpointConstant R := by
  unfold primitiveR51EndpointConstant
  positivity

/-- Fixed exponential base for the purely discrete and endpoint-geometric
part of R-51. -/
def primitiveR51ExponentialBase (C R : ℝ) : ℝ :=
  Real.exp 24 *
    ((3 : ℝ) ^ 8) * 4 *
    primitiveEndpointCoefficientBase C *
    (1 + primitiveR51EndpointConstant R)

theorem primitiveR51ExponentialBase_pos
    {C R : ℝ} (hC : 0 ≤ C) :
    0 < primitiveR51ExponentialBase C R := by
  unfold primitiveR51ExponentialBase
  have hendpoint := primitiveR51EndpointConstant_nonneg R
  have hcoeff := primitiveEndpointCoefficientBase_pos hC
  positivity

/-- R-51 after all fixed combinatorial factors have been absorbed into
one exponential.  The only order-dependent remainder is the critical
`L^(n-2)` factor. -/
theorem primitiveR51GlobalDecayBound_le_exponential
    {C : ℝ} (hC : 0 ≤ C)
    {n q : ℕ} (hn : 2 ≤ n)
    (δ R : ℝ) (z w : T4) :
    primitiveR51GlobalDecayBound C n q 1 δ R z w ≤
      primitiveR51ExponentialBase C R ^ n *
        (primitiveDyadicPeriodLog q : ℝ) ^ (n - 2) *
        δ ^ 4 *
        (torusDistSq (z - w) + δ ^ 2)⁻¹ ^ 2 := by
  let L : ℝ := (primitiveDyadicPeriodLog q : ℝ)
  let E : ℝ := primitiveR51EndpointConstant R
  let B : ℝ := primitiveEndpointCoefficientBase C
  have hL : 0 ≤ L := by positivity
  have hE : 0 ≤ E := primitiveR51EndpointConstant_nonneg R
  have hB : 0 ≤ B :=
    (primitiveEndpointCoefficientBase_pos hC).le
  have hcoeff :
      primitiveEndpointUniformCoefficient C (2 * q) n 1 ≤
        B ^ n * L ^ (n - 2) := by
    simpa only [B, L, primitiveDyadicPeriodLog,
      show 4 * (2 * q) = 4 * (2 * q) by rfl] using
      primitiveEndpointUniformCoefficient_le_base_pow
        hC (2 * q) n hn
  have hExp :
      Real.exp (12 * (2 * n - 1)) ≤
        Real.exp 24 ^ n := by
    have hsub :
        ((2 * n - 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
      exact_mod_cast Nat.sub_le (2 * n) 1
    calc
      Real.exp (12 * (2 * n - 1)) ≤
          Real.exp (24 * (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = Real.exp ((n : ℝ) * 24) := by ring
      _ = Real.exp 24 ^ n := Real.exp_nat_mul 24 n
  have hfiber :
      ((((3 ^ 4) ^ (2 * n) : ℕ) : ℝ)) =
        ((3 : ℝ) ^ 8) ^ n := by
    push_cast
    rw [show (3 : ℝ) ^ 8 = 6561 by norm_num]
    change (81 : ℝ) ^ (2 * n) = (6561 : ℝ) ^ n
    rw [show (6561 : ℝ) = 81 ^ 2 by norm_num,
      pow_mul]
  have htwoPower :
      (((2 ^ (2 * n) : ℕ) : ℝ)) =
        (4 : ℝ) ^ n := by
    push_cast
    calc
      (2 : ℝ) ^ (2 * n) =
          ((2 : ℝ) ^ 2) ^ n := by rw [pow_mul]
      _ = (4 : ℝ) ^ n := by norm_num
  have hEpow : E ≤ (1 + E) ^ n := by
    have hbase : E ≤ 1 + E := by linarith
    have hone : (1 : ℝ) ≤ 1 + E := by linarith
    calc
      E ≤ 1 + E := hbase
      _ = (1 + E) ^ 1 := by ring
      _ ≤ (1 + E) ^ n :=
        pow_le_pow_right₀ hone (by omega)
  have hdecay0 :
      0 ≤ (torusDistSq (z - w) + δ ^ 2)⁻¹ ^ 2 := by
    positivity
  have hcoeff0 :
      0 ≤ primitiveEndpointUniformCoefficient
        C (2 * q) n 1 :=
    primitiveEndpointUniformCoefficient_nonneg hC _ _ _
  have hcore :
      Real.exp (12 * (2 * n - 1)) *
          ((((3 ^ 4) ^ (2 * n) : ℕ) : ℝ) *
            ((((2 ^ (2 * n) : ℕ) : ℝ) *
                primitiveEndpointUniformCoefficient
                  C (2 * q) n 1) *
              E)) ≤
        primitiveR51ExponentialBase C R ^ n *
          L ^ (n - 2) := by
    rw [hfiber, htwoPower]
    calc
      Real.exp (12 * (2 * n - 1)) *
          (((3 : ℝ) ^ 8) ^ n *
            (((4 : ℝ) ^ n *
                primitiveEndpointUniformCoefficient
                  C (2 * q) n 1) * E)) ≤
        Real.exp 24 ^ n *
          (((3 : ℝ) ^ 8) ^ n *
            (((4 : ℝ) ^ n *
                (B ^ n * L ^ (n - 2))) *
              (1 + E) ^ n)) := by
        gcongr
      _ = primitiveR51ExponentialBase C R ^ n *
          L ^ (n - 2) := by
        unfold primitiveR51ExponentialBase
        dsimp only [B, E]
        rw [mul_pow, mul_pow, mul_pow, mul_pow]
        ring
  have hendpointFactor :
      (160000 * (R + 2) ^ 4) ^ 2 *
          ((9 * (1 + 4 * R ^ 2)) ^ 2 * δ ^ 4 *
            (torusDistSq (z - w) + δ ^ 2)⁻¹ ^ 2) =
        E * δ ^ 4 *
          (torusDistSq (z - w) + δ ^ 2)⁻¹ ^ 2 := by
    dsimp only [E, primitiveR51EndpointConstant]
    ring
  unfold primitiveR51GlobalDecayBound
  rw [hendpointFactor]
  change
    Real.exp (12 * (2 * n - 1)) *
          ((((3 ^ 4) ^ (2 * n) : ℕ) : ℝ) *
            ((((2 ^ (2 * n) : ℕ) : ℝ) *
                primitiveEndpointUniformCoefficient
                  C (2 * q) n 1) *
              (E * δ ^ 4 *
                (torusDistSq (z - w) + δ ^ 2)⁻¹ ^ 2))) ≤
        primitiveR51ExponentialBase C R ^ n *
          L ^ (n - 2) * δ ^ 4 *
          (torusDistSq (z - w) + δ ^ 2)⁻¹ ^ 2
  calc
    Real.exp (12 * (2 * n - 1)) *
        ((((3 ^ 4) ^ (2 * n) : ℕ) : ℝ) *
          ((((2 ^ (2 * n) : ℕ) : ℝ) *
              primitiveEndpointUniformCoefficient
                C (2 * q) n 1) *
            (E * δ ^ 4 *
              (torusDistSq (z - w) + δ ^ 2)⁻¹ ^ 2))) =
      (Real.exp (12 * (2 * n - 1)) *
        ((((3 ^ 4) ^ (2 * n) : ℕ) : ℝ) *
          ((((2 ^ (2 * n) : ℕ) : ℝ) *
              primitiveEndpointUniformCoefficient
                C (2 * q) n 1) * E))) *
        δ ^ 4 *
        (torusDistSq (z - w) + δ ^ 2)⁻¹ ^ 2 := by ring
    _ ≤ (primitiveR51ExponentialBase C R ^ n *
          L ^ (n - 2)) *
        δ ^ 4 *
        (torusDistSq (z - w) + δ ^ 2)⁻¹ ^ 2 := by
      gcongr
    _ = _ := by ring

/-! ## Compatible-mesh cancellations -/

theorem compatibleMesh_invFour_cancel
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ((ε⁻¹ ^ 4) ^ n) *
        compatibleMeshSize ε ^ (4 * n) ≤ 1 := by
  let δ : ℝ := compatibleMeshSize ε
  have hδ : 0 ≤ δ := (compatibleMeshSize_pos hε).le
  have hδε : δ ≤ ε := compatibleMeshSize_le hε
  have hbase0 : 0 ≤ ε⁻¹ * δ :=
    mul_nonneg (inv_nonneg.mpr hε.le) hδ
  have hbase1 : ε⁻¹ * δ ≤ 1 :=
    (inv_mul_le_one₀ hε).2 hδε
  have hpow :
      (ε⁻¹ * δ) ^ (4 * n) ≤ (1 : ℝ) ^ (4 * n) :=
    pow_le_pow_left₀ hbase0 hbase1 _
  dsimp only [δ] at hpow ⊢
  rw [one_pow] at hpow
  have hinvPow :
      (ε⁻¹ ^ 4) ^ n = ε⁻¹ ^ (4 * n) :=
    (pow_mul ε⁻¹ 4 n).symm
  calc
    (ε⁻¹ ^ 4) ^ n *
        compatibleMeshSize ε ^ (4 * n) =
      ε⁻¹ ^ (4 * n) *
        compatibleMeshSize ε ^ (4 * n) := by
          rw [hinvPow]
    _ = (ε⁻¹ * compatibleMeshSize ε) ^ (4 * n) := by
          rw [mul_pow]
    _ ≤ 1 := hpow

/-- Replacing the compatible mesh by the covariance scale costs at most
`16` in the inserted endpoint decay. -/
theorem compatibleMesh_invEndpointSq_le
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (z w : T4) :
    (torusDistSq (z - w) +
        compatibleMeshSize ε ^ 2)⁻¹ ^ 2 ≤
      16 * (torusDistSq (z - w) + ε ^ 2)⁻¹ ^ 2 := by
  let δ : ℝ := compatibleMeshSize ε
  let A : ℝ := torusDistSq (z - w) + δ ^ 2
  let B : ℝ := torusDistSq (z - w) + ε ^ 2
  have hδ : 0 < δ := compatibleMeshSize_pos hε
  have hεδ : ε < 2 * δ :=
    lt_two_mul_compatibleMeshSize hε hε1
  have htorus : 0 ≤ torusDistSq (z - w) :=
    torusDistSq_nonneg _
  have hA : 0 < A := by
    dsimp only [A]
    nlinarith [sq_pos_of_pos hδ]
  have hB : 0 < B := by
    dsimp only [B]
    nlinarith [sq_pos_of_pos hε]
  have hεsq : ε ^ 2 ≤ 4 * δ ^ 2 := by
    nlinarith [sq_nonneg (2 * δ - ε)]
  have hBA : B ≤ 4 * A := by
    dsimp only [A, B]
    nlinarith
  have hinv : A⁻¹ ≤ 4 * B⁻¹ := by
    apply (le_div_iff₀ hB).2
    calc
      A⁻¹ * B ≤ A⁻¹ * (4 * A) :=
        mul_le_mul_of_nonneg_left hBA (inv_nonneg.mpr hA.le)
      _ = 4 := by
        field_simp [hA.ne']
  have hsquare :
      A⁻¹ ^ 2 ≤ (4 * B⁻¹) ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hA.le) hinv 2
  dsimp only [A, B, δ] at hsquare ⊢
  nlinarith

/-- The same comparison with one additional endpoint factor, as needed
for the ordinary (non-inserted) kernel. -/
theorem compatibleMesh_invEndpointCube_le
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (z w : T4) :
    (torusDistSq (z - w) + ε ^ 2)⁻¹ *
        (torusDistSq (z - w) +
          compatibleMeshSize ε ^ 2)⁻¹ ^ 2 ≤
      16 * (torusDistSq (z - w) + ε ^ 2)⁻¹ ^ 3 := by
  have h :=
    compatibleMesh_invEndpointSq_le hε hε1 z w
  have hnonneg :
      0 ≤ (torusDistSq (z - w) + ε ^ 2)⁻¹ := by
    exact inv_nonneg.mpr
      (add_nonneg (torusDistSq_nonneg _) (sq_nonneg ε))
  calc
    (torusDistSq (z - w) + ε ^ 2)⁻¹ *
        (torusDistSq (z - w) +
          compatibleMeshSize ε ^ 2)⁻¹ ^ 2 ≤
      (torusDistSq (z - w) + ε ^ 2)⁻¹ *
        (16 * (torusDistSq (z - w) + ε ^ 2)⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_left h hnonneg
    _ = 16 * (torusDistSq (z - w) + ε ^ 2)⁻¹ ^ 3 := by
      ring

/-! ## Covariance and cell-volume power ledger -/

/-- A fixed nonnegative multiplier and a power with a bounded exponent
deficit are absorbed into one exponential base. -/
theorem fixed_mul_pow_sub_le_pow
    {c a : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a)
    (m n k : ℕ) (hn : 1 ≤ n) :
    c * a ^ (m * n - k) ≤
      ((1 + c) * (1 + a) ^ m) ^ n := by
  have hcbase : c ≤ 1 + c := by linarith
  have hcOne : (1 : ℝ) ≤ 1 + c := by linarith
  have hcpow : c ≤ (1 + c) ^ n := by
    calc
      c ≤ 1 + c := hcbase
      _ = (1 + c) ^ 1 := by ring
      _ ≤ (1 + c) ^ n :=
        pow_le_pow_right₀ hcOne hn
  have habase : a ≤ 1 + a := by linarith
  have haOne : (1 : ℝ) ≤ 1 + a := by linarith
  have hapow :
      a ^ (m * n - k) ≤
        ((1 + a) ^ m) ^ n := by
    calc
      a ^ (m * n - k) ≤
          (1 + a) ^ (m * n - k) :=
        pow_le_pow_left₀ ha habase _
      _ ≤ (1 + a) ^ (m * n) :=
        pow_le_pow_right₀ haOne (Nat.sub_le _ _)
      _ = ((1 + a) ^ m) ^ n := by
        rw [pow_mul]
  calc
    c * a ^ (m * n - k) ≤
        (1 + c) ^ n * ((1 + a) ^ m) ^ n :=
      mul_le_mul hcpow hapow (pow_nonneg ha _)
        (pow_nonneg (by linarith) n)
    _ = ((1 + c) * (1 + a) ^ m) ^ n := by
      rw [mul_pow]

def primitiveR51FarCore (R : ℝ) : ℝ :=
  (12 + 32 * R ^ 2) *
    terminalRadiusFactor R

def primitiveR51FarStep (Ccell R : ℝ) : ℝ :=
  Ccell * (R ^ 2 + R ^ 4)

def primitiveR51NearStep (Ccell R : ℝ) : ℝ :=
  Ccell * cellChainRadiusFactor R

/-- Exponential base absorbing both cellwise analytic branches. -/
def primitiveR51CellCoreBase (Ccell R : ℝ) : ℝ :=
  2 *
    (((1 + primitiveR51FarCore R) *
        (1 + primitiveR51FarStep Ccell R) ^ 2) +
      ((1 + (12 + 32 * R ^ 2)) *
        (1 + primitiveR51NearStep Ccell R) ^ 2))

theorem primitiveR51CellCoreBase_pos
    {Ccell R : ℝ} (hCcell : 0 < Ccell) (hR : 0 < R) :
    0 < primitiveR51CellCoreBase Ccell R := by
  unfold primitiveR51CellCoreBase primitiveR51FarCore
    primitiveR51FarStep primitiveR51NearStep
  have hterminal := terminalRadiusFactor_pos hR
  have hchain := cellChainRadiusFactor_pos R
  positivity

/-- Both branches of the cellwise R-51 estimate share the exact
`δ^(4n-4)` factor and have a uniform exponential coefficient. -/
theorem primitiveR51CellCoefficients_le
    {Ccell R δ : ℝ} (hCcell : 0 < Ccell) (hR : 0 < R)
    (n : ℕ) (hn : 2 ≤ n) :
    let farCoeff :=
      (12 + 32 * R ^ 2) *
        (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
        terminalRadiusFactor R * δ ^ (4 * n - 4)
    let nearCoeff :=
      (12 + 32 * R ^ 2) *
        (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
        δ ^ (4 * n - 4)
    farCoeff + nearCoeff ≤
      primitiveR51CellCoreBase Ccell R ^ n *
        δ ^ (4 * n - 4) := by
  let F : ℝ := primitiveR51FarCore R
  let A : ℝ := primitiveR51FarStep Ccell R
  let N : ℝ := 12 + 32 * R ^ 2
  let B : ℝ := primitiveR51NearStep Ccell R
  let S : ℝ :=
    (1 + F) * (1 + A) ^ 2 +
      (1 + N) * (1 + B) ^ 2
  have hF : 0 ≤ F := by
    dsimp only [F, primitiveR51FarCore]
    exact mul_nonneg (by positivity)
      (terminalRadiusFactor_pos hR).le
  have hA : 0 ≤ A := by
    dsimp only [A, primitiveR51FarStep]
    positivity
  have hN : 0 ≤ N := by
    dsimp only [N]
    positivity
  have hB : 0 ≤ B := by
    dsimp only [B, primitiveR51NearStep]
    exact mul_nonneg hCcell.le
      (cellChainRadiusFactor_pos R).le
  have hS : 0 ≤ S := by
    dsimp only [S]
    positivity
  have hfar :
      F * A ^ (2 * n - 2) ≤
        ((1 + F) * (1 + A) ^ 2) ^ n :=
    fixed_mul_pow_sub_le_pow hF hA 2 n 2 (by omega)
  have hnear :
      N * B ^ (2 * n - 3) ≤
        ((1 + N) * (1 + B) ^ 2) ^ n :=
    fixed_mul_pow_sub_le_pow hN hB 2 n 3 (by omega)
  have hfarS :
      ((1 + F) * (1 + A) ^ 2) ^ n ≤ S ^ n := by
    apply pow_le_pow_left₀
    · positivity
    · dsimp only [S]
      exact le_add_of_nonneg_right (by positivity)
  have hnearS :
      ((1 + N) * (1 + B) ^ 2) ^ n ≤ S ^ n := by
    apply pow_le_pow_left₀
    · positivity
    · dsimp only [S]
      exact le_add_of_nonneg_left (by positivity)
  have htwo : (2 : ℝ) ≤ 2 ^ n :=
    two_le_two_pow n (by omega)
  have hsum :
      F * A ^ (2 * n - 2) +
          N * B ^ (2 * n - 3) ≤
        (2 * S) ^ n := by
    calc
      F * A ^ (2 * n - 2) +
          N * B ^ (2 * n - 3) ≤
        S ^ n + S ^ n :=
          add_le_add (hfar.trans hfarS)
            (hnear.trans hnearS)
      _ = 2 * S ^ n := by ring
      _ ≤ 2 ^ n * S ^ n := by
        exact mul_le_mul_of_nonneg_right htwo (pow_nonneg hS n)
      _ = (2 * S) ^ n := by rw [mul_pow]
  have hbase :
      primitiveR51CellCoreBase Ccell R = 2 * S := by
    unfold primitiveR51CellCoreBase
    dsimp only [S, F, A, N, B]
  have hδpow : 0 ≤ δ ^ (4 * n - 4) := by
    have hexp : 4 * n - 4 = 2 * (2 * n - 2) := by omega
    rw [hexp, pow_mul]
    positivity
  calc
    (12 + 32 * R ^ 2) *
          (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
          terminalRadiusFactor R * δ ^ (4 * n - 4) +
        (12 + 32 * R ^ 2) *
          (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
          δ ^ (4 * n - 4) =
      (F * A ^ (2 * n - 2) +
        N * B ^ (2 * n - 3)) *
          δ ^ (4 * n - 4) := by
        dsimp only [F, A, N, B, primitiveR51FarCore,
          primitiveR51FarStep, primitiveR51NearStep]
        ring
    _ ≤ (2 * S) ^ n * δ ^ (4 * n - 4) :=
      mul_le_mul_of_nonneg_right hsum
        hδpow
    _ = primitiveR51CellCoreBase Ccell R ^ n *
        δ ^ (4 * n - 4) := by rw [hbase]

/-- Covariance scaling and cell volume cancel exactly at the compatible
mesh, leaving only one fixed exponential. -/
def primitiveR51AnalyticBase (Ccov Ccell R : ℝ) : ℝ :=
  Ccov * primitiveR51CellCoreBase Ccell R

theorem primitiveR51AnalyticBase_pos
    {Ccov Ccell R : ℝ}
    (hCcov : 0 < Ccov) (hCcell : 0 < Ccell) (hR : 0 < R) :
    0 < primitiveR51AnalyticBase Ccov Ccell R :=
  mul_pos hCcov (primitiveR51CellCoreBase_pos hCcell hR)

theorem primitiveR51AnalyticLedger_le
    {Ccov Ccell : ℝ} (hCcov : 0 < Ccov)
    (hCcell : 0 < Ccell) {ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R)
    (n : ℕ) (hn : 2 ≤ n) :
    let δ := compatibleMeshSize ε
    let farCoeff :=
      (12 + 32 * R ^ 2) *
        (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
        terminalRadiusFactor R * δ ^ (4 * n - 4)
    let nearCoeff :=
      (12 + 32 * R ^ 2) *
        (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
        δ ^ (4 * n - 4)
    let Q := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
    Q * (farCoeff + nearCoeff) * δ ^ 4 ≤
      primitiveR51AnalyticBase Ccov Ccell R ^ n := by
  let δ : ℝ := compatibleMeshSize ε
  let farCoeff : ℝ :=
    (12 + 32 * R ^ 2) *
      (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R * δ ^ (4 * n - 4)
  let nearCoeff : ℝ :=
    (12 + 32 * R ^ 2) *
      (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
      δ ^ (4 * n - 4)
  let Q : ℝ := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
  let A : ℝ := primitiveR51CellCoreBase Ccell R
  have hA : 0 ≤ A :=
    (primitiveR51CellCoreBase_pos hCcell hR).le
  have hcell :
      farCoeff + nearCoeff ≤
        A ^ n * δ ^ (4 * n - 4) := by
    simpa only [farCoeff, nearCoeff, A] using
      primitiveR51CellCoefficients_le
        (δ := δ) hCcell hR n hn
  have hδ : 0 ≤ δ := (compatibleMeshSize_pos hε).le
  have hfour : 4 ≤ 4 * n := by omega
  have hδcombine :
      δ ^ (4 * n - 4) * δ ^ 4 = δ ^ (4 * n) := by
    rw [← pow_add]
    congr 1
    omega
  have hcancel :=
    compatibleMesh_invFour_cancel hε n
  calc
    Q * (farCoeff + nearCoeff) * δ ^ 4 ≤
      Q * (A ^ n * δ ^ (4 * n - 4)) * δ ^ 4 := by
        gcongr
    _ = (Ccov * A) ^ n *
        (((ε⁻¹ ^ 4) ^ n) * δ ^ (4 * n)) := by
      dsimp only [Q, dim]
      calc
        (ε⁻¹ ^ 4 * Ccov) ^ n *
            (A ^ n * δ ^ (4 * n - 4)) * δ ^ 4 =
          ((ε⁻¹ ^ 4 * Ccov) ^ n * A ^ n) *
            (δ ^ (4 * n - 4) * δ ^ 4) := by ring
        _ = ((ε⁻¹ ^ 4 * Ccov) ^ n * A ^ n) *
            δ ^ (4 * n) := by rw [hδcombine]
        _ = (Ccov * A) ^ n *
            (((ε⁻¹ ^ 4) ^ n) * δ ^ (4 * n)) := by
          simp only [mul_pow]
          ring
    _ ≤ (Ccov * A) ^ n * 1 := by
      exact mul_le_mul_of_nonneg_left hcancel
        (pow_nonneg (mul_nonneg hCcov.le hA) n)
    _ = primitiveR51AnalyticBase Ccov Ccell R ^ n := by
      unfold primitiveR51AnalyticBase
      dsimp only [A]
      ring

/-! ## Coupling and logarithmic power cancellation -/

/-- The `n` coupling factors cancel all but two powers of the logarithm
after the critical R-51 factor `L^(n-2)` is inserted.  The fixed factor
`100` absorbs the comparison between the natural dyadic logarithm and
`|log ε|` throughout the full paper truncation window. -/
theorem lamEps_mul_primitiveDyadicPeriodLog_pow_le
    {lam ε : ℝ} (hlam : 0 < lam)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlogLarge : 2 ≤ |Real.log ε|)
    {q : ℕ} (hqε : (q : ℤ) = compatibleCellCount ε)
    (n : ℕ) (hn : 2 ≤ n) :
    lamEps lam ε ^ (2 * n) *
        (primitiveDyadicPeriodLog q : ℝ) ^ (n - 2) ≤
      (100 * lam) ^ (2 * n) /
        |Real.log ε| ^ 2 := by
  let h : ℝ := |Real.log ε|
  let L : ℝ := (primitiveDyadicPeriodLog q : ℝ)
  have hh : 0 < h := by
    dsimp only [h]
    linarith
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hLupper : L ≤ 100 * h := by
    simpa only [L, h] using
      primitiveDyadicPeriodLog_le_hundred_abs_log
        hε hε1 hlogLarge hqε
  have hLpow :
      L ^ (n - 2) ≤ (100 * h) ^ (n - 2) :=
    pow_le_pow_left₀ hL hLupper _
  have hcoupling :
      lamEps lam ε ^ (2 * n) =
        lam ^ (2 * n) / h ^ n := by
    calc
      lamEps lam ε ^ (2 * n) =
          |lamEps lam ε ^ (2 * n)| :=
        (abs_of_nonneg
          ((even_two_mul n).pow_nonneg
            (lamEps lam ε))).symm
      _ = |lamEps lam ε| ^ (2 * n) := by
        rw [abs_pow]
      _ = lam ^ (2 * n) /
          |Real.log ε| ^ n :=
        abs_lamEps_even_pow n (by simpa only [h] using hh)
      _ = lam ^ (2 * n) / h ^ n := by
        rfl
  have hcoupling0 :
      0 ≤ lam ^ (2 * n) / h ^ n :=
    div_nonneg (pow_nonneg hlam.le _) (pow_nonneg hh.le _)
  have hhpow :
      h ^ n = h ^ (n - 2) * h ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  have hreduce :
      lam ^ (2 * n) / h ^ n *
          (100 * h) ^ (n - 2) =
        (lam ^ (2 * n) * 100 ^ (n - 2)) / h ^ 2 := by
    rw [hhpow, mul_pow]
    field_simp [ne_of_gt hh]
  have hhundred :
      (100 : ℝ) ^ (n - 2) ≤ 100 ^ (2 * n) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hnum :
      lam ^ (2 * n) * 100 ^ (n - 2) ≤
        (100 * lam) ^ (2 * n) := by
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hhundred
      (pow_nonneg hlam.le (2 * n))]
  calc
    lamEps lam ε ^ (2 * n) * L ^ (n - 2) =
        (lam ^ (2 * n) / h ^ n) * L ^ (n - 2) := by
      rw [hcoupling]
    _ ≤ (lam ^ (2 * n) / h ^ n) *
        (100 * h) ^ (n - 2) :=
      mul_le_mul_of_nonneg_left hLpow hcoupling0
    _ = (lam ^ (2 * n) * 100 ^ (n - 2)) /
        h ^ 2 := hreduce
    _ ≤ (100 * lam) ^ (2 * n) / h ^ 2 :=
      (div_le_div_iff_of_pos_right (sq_pos_of_pos hh)).2 hnum
    _ = (100 * lam) ^ (2 * n) /
        |Real.log ε| ^ 2 := by rfl

/-! ## Final exponential base -/

/-- One fixed base absorbing the analytic, combinatorial, and endpoint
comparison constants in the higher-order branch of Proposition 4.1. -/
def primitiveR51TotalBase
    (C Ccov Ccell R : ℝ) : ℝ :=
  200 *
    (1 + primitiveR51AnalyticBase Ccov Ccell R) *
    (1 + primitiveR51ExponentialBase C R)

theorem primitiveR51TotalBase_pos
    {C Ccov Ccell R : ℝ}
    (hC : 0 ≤ C) (hCcov : 0 < Ccov)
    (hCcell : 0 < Ccell) (hR : 0 < R) :
    0 < primitiveR51TotalBase C Ccov Ccell R := by
  unfold primitiveR51TotalBase
  have hA :=
    primitiveR51AnalyticBase_pos hCcov hCcell hR
  have hB := primitiveR51ExponentialBase_pos
    (R := R) hC
  positivity

/-- The factor `16` in the compatible-mesh endpoint comparison and the
two fixed exponential bases are all absorbed into
`primitiveR51TotalBase^(2n)`. -/
theorem primitiveR51FixedFactors_le_totalBase
    {C Ccov Ccell R lam : ℝ}
    (hC : 0 ≤ C) (hCcov : 0 < Ccov)
    (hCcell : 0 < Ccell) (hR : 0 < R)
    (hlam : 0 < lam) (n : ℕ) (hn : 2 ≤ n) :
    16 * (100 * lam) ^ (2 * n) *
          primitiveR51AnalyticBase Ccov Ccell R ^ n *
          primitiveR51ExponentialBase C R ^ n ≤
      (primitiveR51TotalBase C Ccov Ccell R * lam) ^
        (2 * n) := by
  let A : ℝ := primitiveR51AnalyticBase Ccov Ccell R
  let B : ℝ := primitiveR51ExponentialBase C R
  let P : ℝ := (1 + A) * (1 + B)
  have hA : 0 ≤ A :=
    (primitiveR51AnalyticBase_pos hCcov hCcell hR).le
  have hB : 0 ≤ B :=
    (primitiveR51ExponentialBase_pos
      (R := R) hC).le
  have hP : 0 ≤ P := by
    dsimp only [P]
    positivity
  have hAB : A * B ≤ P ^ 2 := by
    have hAP : A ≤ P := by
      dsimp only [P]
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + A)
        (by linarith : 0 ≤ B)]
    have hBP : B ≤ P := by
      dsimp only [P]
      nlinarith [mul_nonneg (by linarith : 0 ≤ A)
        (by linarith : 0 ≤ 1 + B)]
    nlinarith [mul_le_mul hAP hBP hB hP]
  have hABpow :
      (A * B) ^ n ≤ (P ^ 2) ^ n :=
    pow_le_pow_left₀ (mul_nonneg hA hB) hAB _
  have hsixteen : (16 : ℝ) ≤ 4 ^ n := by
    calc
      (16 : ℝ) = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ n :=
        pow_le_pow_right₀ (by norm_num) hn
  calc
    16 * (100 * lam) ^ (2 * n) * A ^ n * B ^ n ≤
        4 ^ n * (100 * lam) ^ (2 * n) *
          A ^ n * B ^ n := by
      gcongr
    _ = (200 * lam) ^ (2 * n) * (A * B) ^ n := by
      rw [pow_mul (100 * lam) 2 n,
        pow_mul (200 * lam) 2 n]
      rw [← mul_pow]
      rw [← mul_pow]
      rw [← mul_pow]
      ring
    _ ≤ (200 * lam) ^ (2 * n) * (P ^ 2) ^ n :=
      mul_le_mul_of_nonneg_left hABpow
        ((even_two_mul n).pow_nonneg (200 * lam))
    _ = (primitiveR51TotalBase C Ccov Ccell R * lam) ^
        (2 * n) := by
      unfold primitiveR51TotalBase
      dsimp only [A, B, P]
      rw [pow_mul (200 * lam) 2 n,
        pow_mul
          (200 *
            (1 + primitiveR51AnalyticBase Ccov Ccell R) *
            (1 + primitiveR51ExponentialBase C R) *
            lam) 2 n]
      rw [← mul_pow]
      congr 1
      ring

/-- Complete real-valued scaling ledger for the endpoint-preserving
R-51 bound.  This is the point where the cell scale, covariance scale,
critical dyadic logarithm, coupling, and endpoint comparison are all
simultaneously discharged. -/
theorem primitiveR51ScaledAnalyticDecay_le
    {C Ccov Ccell : ℝ}
    (hC : 0 ≤ C) (hCcov : 0 < Ccov)
    (hCcell : 0 < Ccell)
    {lam ε R : ℝ} (hlam : 0 < lam)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hlogLarge : 2 ≤ |Real.log ε|)
    {q : ℕ} (hqε : (q : ℤ) = compatibleCellCount ε)
    (n : ℕ) (hn : 2 ≤ n) (z w : T4) :
    let δ := compatibleMeshSize ε
    let farCoeff :=
      (12 + 32 * R ^ 2) *
        (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
        terminalRadiusFactor R * δ ^ (4 * n - 4)
    let nearCoeff :=
      (12 + 32 * R ^ 2) *
        (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
        δ ^ (4 * n - 4)
    let Q := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
    lamEps lam ε ^ (2 * n) *
        (Q * (farCoeff + nearCoeff) *
          primitiveR51GlobalDecayBound
            C n q 1 δ R z w) ≤
      (primitiveR51TotalBase C Ccov Ccell R * lam) ^
          (2 * n) *
        (1 / |Real.log ε| ^ 2) *
        (torusDistSq (z - w) + ε ^ 2)⁻¹ ^ 2 := by
  let δ : ℝ := compatibleMeshSize ε
  let farCoeff : ℝ :=
    (12 + 32 * R ^ 2) *
      (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R * δ ^ (4 * n - 4)
  let nearCoeff : ℝ :=
    (12 + 32 * R ^ 2) *
      (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
      δ ^ (4 * n - 4)
  let Q : ℝ := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
  let A : ℝ := primitiveR51AnalyticBase Ccov Ccell R
  let B : ℝ := primitiveR51ExponentialBase C R
  let L : ℝ := (primitiveDyadicPeriodLog q : ℝ)
  let Dδ : ℝ :=
    (torusDistSq (z - w) + δ ^ 2)⁻¹ ^ 2
  let Dε : ℝ :=
    (torusDistSq (z - w) + ε ^ 2)⁻¹ ^ 2
  have hδ : 0 < δ := compatibleMeshSize_pos hε
  have hA : 0 ≤ A :=
    (primitiveR51AnalyticBase_pos hCcov hCcell hR).le
  have hB : 0 ≤ B :=
    (primitiveR51ExponentialBase_pos
      (R := R) hC).le
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hDδ : 0 ≤ Dδ := by
    dsimp only [Dδ]
    positivity
  have hDε : 0 ≤ Dε := by
    dsimp only [Dε]
    positivity
  have hQ : 0 ≤ Q := by
    dsimp only [Q, dim]
    positivity
  have hfar : 0 ≤ farCoeff := by
    dsimp only [farCoeff]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity)
          (pow_nonneg
            (mul_nonneg hCcell.le (by positivity)) _))
        (terminalRadiusFactor_pos hR).le)
      (pow_nonneg hδ.le _)
  have hnear : 0 ≤ nearCoeff := by
    dsimp only [nearCoeff]
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (pow_nonneg
          (mul_nonneg hCcell.le
            (cellChainRadiusFactor_pos R).le) _))
      (pow_nonneg hδ.le _)
  have hcoeff :
      0 ≤ Q * (farCoeff + nearCoeff) :=
    mul_nonneg hQ (add_nonneg hfar hnear)
  have hglobal :
      primitiveR51GlobalDecayBound
          C n q 1 δ R z w ≤
        B ^ n * L ^ (n - 2) * δ ^ 4 * Dδ := by
    simpa only [B, L, Dδ] using
      primitiveR51GlobalDecayBound_le_exponential
        hC hn δ R z w
  have hanalytic :
      Q * (farCoeff + nearCoeff) * δ ^ 4 ≤
        A ^ n := by
    simpa only [Q, farCoeff, nearCoeff, δ, A] using
      primitiveR51AnalyticLedger_le
        hCcov hCcell hε hR n hn
  have hproduct :
      Q * (farCoeff + nearCoeff) *
          primitiveR51GlobalDecayBound
            C n q 1 δ R z w ≤
        A ^ n * B ^ n * L ^ (n - 2) * Dδ := by
    calc
      Q * (farCoeff + nearCoeff) *
          primitiveR51GlobalDecayBound
            C n q 1 δ R z w ≤
        Q * (farCoeff + nearCoeff) *
          (B ^ n * L ^ (n - 2) * δ ^ 4 * Dδ) :=
        mul_le_mul_of_nonneg_left hglobal hcoeff
      _ = (Q * (farCoeff + nearCoeff) * δ ^ 4) *
          B ^ n * L ^ (n - 2) * Dδ := by ring
      _ ≤ A ^ n * B ^ n * L ^ (n - 2) * Dδ := by
        gcongr
  have hcoupling0 :
      0 ≤ lamEps lam ε ^ (2 * n) :=
    (even_two_mul n).pow_nonneg _
  have hcoupling :
      lamEps lam ε ^ (2 * n) * L ^ (n - 2) ≤
        (100 * lam) ^ (2 * n) /
          |Real.log ε| ^ 2 := by
    simpa only [L] using
      lamEps_mul_primitiveDyadicPeriodLog_pow_le
        hlam hε hε1 hlogLarge hqε n hn
  have hmesh : Dδ ≤ 16 * Dε := by
    simpa only [Dδ, Dε, δ] using
      compatibleMesh_invEndpointSq_le hε hε1 z w
  have hfixed :
      16 * (100 * lam) ^ (2 * n) * A ^ n * B ^ n ≤
        (primitiveR51TotalBase C Ccov Ccell R * lam) ^
          (2 * n) := by
    simpa only [A, B] using
      primitiveR51FixedFactors_le_totalBase
        hC hCcov hCcell hR hlam n hn
  have hh : 0 < |Real.log ε| := by
    linarith
  calc
    lamEps lam ε ^ (2 * n) *
        (Q * (farCoeff + nearCoeff) *
          primitiveR51GlobalDecayBound
            C n q 1 δ R z w) ≤
      lamEps lam ε ^ (2 * n) *
        (A ^ n * B ^ n * L ^ (n - 2) * Dδ) :=
      mul_le_mul_of_nonneg_left hproduct hcoupling0
    _ = (lamEps lam ε ^ (2 * n) *
          L ^ (n - 2)) * A ^ n * B ^ n * Dδ := by
      ring
    _ ≤ ((100 * lam) ^ (2 * n) /
          |Real.log ε| ^ 2) * A ^ n * B ^ n * Dδ := by
      gcongr
    _ ≤ ((100 * lam) ^ (2 * n) /
          |Real.log ε| ^ 2) * A ^ n * B ^ n *
          (16 * Dε) := by
      gcongr
    _ = (16 * (100 * lam) ^ (2 * n) *
          A ^ n * B ^ n) /
          |Real.log ε| ^ 2 * Dε := by
      ring
    _ ≤ (primitiveR51TotalBase C Ccov Ccell R * lam) ^
          (2 * n) /
          |Real.log ε| ^ 2 * Dε := by
      exact mul_le_mul_of_nonneg_right
        ((div_le_div_iff_of_pos_right (sq_pos_of_pos hh)).2
          hfixed) hDε
    _ = (primitiveR51TotalBase C Ccov Ccell R * lam) ^
          (2 * n) *
        (1 / |Real.log ε| ^ 2) *
        (torusDistSq (z - w) + ε ^ 2)⁻¹ ^ 2 := by
      dsimp only [Dε]
      ring

end

end Anderson4D
