import Anderson4D.DetParametrix.Paper42_Moment.R324ProjectedCovariance

/-!
# Spare cutoff decay in the high-frequency R-324 branch

Paper Section 4.2, Step 4 only records the eighth-order central-frequency
payoff.  The selected noise mode is in fact larger than the target scale by
a factor of order `ε⁻¹/²`.  Using twelfth-order Schwartz decay therefore
leaves an additional factor `ε⁴`.

This slack is kept explicit here.  It can pay a polynomial cell-scale cost
inside a one-open-edge primitive estimate without consuming the separate
`ε⁻⁸` budget attached to the four external endpoint integrations.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- The routed cutoff frequency controls `ε² L` with the stronger
`sqrt ε` factor retained. -/
theorem eps_sq_mul_le_sixteen_mul_sqrt_mul_norm_euclideanFrequency
    {ε L : ℝ} {k : Z4}
    (hε : 0 < ε) (hL : 0 ≤ L)
    (hroute :
      (Real.sqrt ε / 2) * L ≤
        ‖z4EuclideanFrequency k‖) :
    ε ^ 2 * L ≤
      16 * Real.sqrt ε *
        ‖euclideanFrequency (fun i => ε * (k i : ℝ))‖ := by
  rw [norm_euclideanFrequency_scaled_z4 hε.le]
  let s : ℝ := Real.sqrt ε
  let y : ℝ := ε ^ 2 * L
  have hs : 0 ≤ s := Real.sqrt_nonneg ε
  have hs_sq : s ^ 2 = ε := by
    exact Real.sq_sqrt hε.le
  have hy : 0 ≤ y := by
    dsimp only [y]
    positivity
  have hpiRatio : 1 ≤ 4 / Real.pi := by
    exact (le_div_iff₀ Real.pi_pos).2 (by
      simpa using Real.pi_le_four)
  have hfactor :
      0 ≤ 16 * s * (ε / (2 * Real.pi)) := by
    positivity
  change
    y ≤
      16 * s *
        ((ε / (2 * Real.pi)) *
          ‖z4EuclideanFrequency k‖)
  calc
    y ≤ y * (4 / Real.pi) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hpiRatio hy
    _ =
        16 * s *
          ((ε / (2 * Real.pi)) *
            ((s / 2) * L)) := by
      dsimp only [y]
      field_simp [Real.pi_ne_zero]
      nlinarith [hs_sq]
    _ ≤
        16 * s *
          ((ε / (2 * Real.pi)) *
            ‖z4EuclideanFrequency k‖) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hroute hfactor

/-- Twelfth-order cutoff decay yields the paper's eighth-order routed
decay together with an explicit spare factor `ε⁴`. -/
theorem one_add_norm_twelve_decay_le_eps_four_routed_decay
    {ε L : ℝ} {k : Z4}
    (hε : 0 < ε) (hL : 0 ≤ L)
    (hlarge : 1 ≤ ε ^ 2 * L)
    (hroute :
      (Real.sqrt ε / 2) * L ≤
        ‖z4EuclideanFrequency k‖) :
    ((1 +
        ‖euclideanFrequency (fun i => ε * (k i : ℝ))‖) ^ 12)⁻¹ ≤
      16 ^ (9 : ℕ) * ε ^ 4 *
        eighthOrderFrequencyDecay (ε ^ 2 * L) := by
  let s : ℝ := Real.sqrt ε
  let w : ℝ :=
    ‖euclideanFrequency (fun i => ε * (k i : ℝ))‖
  let y : ℝ := ε ^ 2 * L
  have hs : 0 ≤ s := Real.sqrt_nonneg ε
  have hw : 0 ≤ w := by
    dsimp only [w]
    positivity
  have hy : 0 ≤ y := by
    dsimp only [y]
    positivity
  have hy_one : 1 ≤ y := by
    exact hlarge
  have hs_sq : s ^ 2 = ε := Real.sq_sqrt hε.le
  have hs_eight : s ^ 8 = ε ^ 4 := by
    calc
      s ^ 8 = (s ^ 2) ^ 4 := by ring
      _ = ε ^ 4 := by rw [hs_sq]
  have hyw :
      y ≤ 16 * s * w := by
    simpa only [s, w, y] using
      eps_sq_mul_le_sixteen_mul_sqrt_mul_norm_euclideanFrequency
        hε hL hroute
  have hyquad :
      1 + y ^ 2 ≤ 2 * y ^ 2 := by
    nlinarith [sq_nonneg y]
  have hy_eight :
      y ^ 8 ≤ 16 ^ (8 : ℕ) * ε ^ 4 * w ^ 8 := by
    calc
      y ^ 8 ≤ (16 * s * w) ^ 8 :=
        pow_le_pow_left₀ hy hyw 8
      _ = 16 ^ (8 : ℕ) * s ^ 8 * w ^ 8 := by
        ring
      _ = 16 ^ (8 : ℕ) * ε ^ 4 * w ^ 8 := by
        rw [hs_eight]
  have hw_eight :
      w ^ 8 ≤ (1 + w) ^ 12 := by
    have hwbase : w ≤ 1 + w := by linarith
    have hfirst :
        w ^ 8 ≤ (1 + w) ^ 8 :=
      pow_le_pow_left₀ hw hwbase 8
    have hfour : 1 ≤ (1 + w) ^ 4 :=
      one_le_pow₀ (by linarith)
    calc
      w ^ 8 ≤ (1 + w) ^ 8 := hfirst
      _ = (1 + w) ^ 8 * 1 := by ring
      _ ≤ (1 + w) ^ 8 * (1 + w) ^ 4 := by
        exact mul_le_mul_of_nonneg_left hfour (by positivity)
      _ = (1 + w) ^ 12 := by ring
  have hden :
      (1 + y ^ 2) ^ 4 ≤
        (16 ^ (9 : ℕ) * ε ^ 4) * (1 + w) ^ 12 := by
    calc
      (1 + y ^ 2) ^ 4 ≤ (2 * y ^ 2) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hyquad 4
      _ = 16 * y ^ 8 := by ring
      _ ≤ 16 * (16 ^ (8 : ℕ) * ε ^ 4 * w ^ 8) := by
        exact mul_le_mul_of_nonneg_left hy_eight (by norm_num)
      _ ≤ 16 *
          (16 ^ (8 : ℕ) * ε ^ 4 * (1 + w) ^ 12) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hw_eight (by positivity))
          (by norm_num)
      _ =
          (16 ^ (9 : ℕ) * ε ^ 4) * (1 + w) ^ 12 := by
        ring
  have hwpos : 0 < (1 + w) ^ 12 := by positivity
  have hypos : 0 < (1 + y ^ 2) ^ 4 := by positivity
  unfold eighthOrderFrequencyDecay
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hypos).2
  calc
    ((1 + w) ^ 12)⁻¹ * (1 + y ^ 2) ^ 4 ≤
        ((1 + w) ^ 12)⁻¹ *
          ((16 ^ (9 : ℕ) * ε ^ 4) * (1 + w) ^ 12) := by
      exact mul_le_mul_of_nonneg_left hden (by positivity)
    _ = 16 ^ (9 : ℕ) * ε ^ 4 := by
      field_simp [hwpos.ne']

/-- The selected cutoff symbol has an `ε⁴` reserve on the genuinely large
central-frequency branch `1 ≤ ε² L`. -/
theorem exists_r324_highFrequency_symbol_bound_with_eps_four :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ε L : ℝ} {k : Z4},
        0 < ε →
        ε ≤ 1 / 4 →
        0 ≤ L →
        1 ≤ ε ^ 2 * L →
        (Real.sqrt ε / 2) * L ≤
          ‖z4EuclideanFrequency k‖ →
        ‖ρ.symbol ε k‖ ≤
          C * ε ^ 4 *
            eighthOrderFrequencyDecay (ε ^ 2 * L) := by
  obtain ⟨C0, hC0, hcut⟩ :=
    ρ.exists_fourierR4_one_add_norm_bound_nat 12
  let C : ℝ := C0 * 16 ^ (9 : ℕ)
  refine ⟨C, mul_pos hC0 (by positivity), ?_⟩
  intro ε L k hε _hεsmall hL hlarge hroute
  let w : ℝ :=
    ‖euclideanFrequency (fun i => ε * (k i : ℝ))‖
  have hwpos : 0 < (1 + w) ^ 12 := by
    dsimp only [w]
    positivity
  have hschwartz :
      (1 + w) ^ 12 * ‖ρ.symbol ε k‖ ≤ C0 := by
    simpa [w, SmoothCutoff.symbol] using
      hcut (fun i => ε * (k i : ℝ))
  have hdivide :
      ‖ρ.symbol ε k‖ ≤
        C0 * ((1 + w) ^ 12)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hwpos).2
      (by simpa [mul_comm] using hschwartz)
  calc
    ‖ρ.symbol ε k‖ ≤
        C0 * ((1 + w) ^ 12)⁻¹ := hdivide
    _ ≤ C0 *
        (16 ^ (9 : ℕ) * ε ^ 4 *
          eighthOrderFrequencyDecay (ε ^ 2 * L)) := by
      exact mul_le_mul_of_nonneg_left
        (by
          simpa only [w] using
            one_add_norm_twelve_decay_le_eps_four_routed_decay
              hε hL hlarge hroute)
        hC0.le
    _ = C * ε ^ 4 *
          eighthOrderFrequencyDecay (ε ^ 2 * L) := by
      dsimp only [C]
      ring

/-- Covariance-mode form of the same spare `ε⁴` payoff, including the
fixed white-noise half-density normalization. -/
theorem exists_r324_covarianceModeCoeff_bound_with_eps_four :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ε L : ℝ} {k : Z4},
        0 < ε →
        ε ≤ 1 / 4 →
        0 ≤ L →
        1 ≤ ε ^ 2 * L →
        k ∈ r324HighModeSet ε L →
        ‖ρ.covarianceModeCoeff ε k‖ ≤
          C * ε ^ 4 *
            eighthOrderFrequencyDecay (ε ^ 2 * L) := by
  obtain ⟨C0, hC0, hsymbol⟩ :=
    ρ.exists_r324_highFrequency_symbol_bound_with_eps_four
  let S : ℝ :=
    ‖(NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2‖
  refine
    ⟨S * C0, mul_pos ?_ hC0, ?_⟩
  · dsimp only [S]
    exact norm_pos_iff.mpr
      (pow_ne_zero 2
        (Complex.ofReal_ne_zero.mpr
          (ne_of_gt NoiseModel.whiteNoiseFourierScale_pos)))
  · intro ε L k hε hεsmall hL hlarge hk
    have hsym :=
      hsymbol hε hεsmall hL hlarge hk
    have hsymOne := ρ.norm_symbol_le_one ε k
    have hsq :
        ‖ρ.symbol ε k‖ ^ 2 ≤ ‖ρ.symbol ε k‖ := by
      nlinarith [norm_nonneg (ρ.symbol ε k)]
    unfold covarianceModeCoeff
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    calc
      ‖(NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2‖ *
            ‖ρ.symbol ε k‖ ^ 2
          ≤ S * ‖ρ.symbol ε k‖ := by
        exact mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
      _ ≤ S *
            (C0 * ε ^ 4 *
              eighthOrderFrequencyDecay (ε ^ 2 * L)) := by
        exact mul_le_mul_of_nonneg_left hsym (norm_nonneg _)
      _ = (S * C0) * ε ^ 4 *
            eighthOrderFrequencyDecay (ε ^ 2 * L) := by
        ring

end SmoothCutoff

end

end Anderson4D
