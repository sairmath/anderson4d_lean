import Anderson4D.Continuum.CutoffFourierDecay
import Anderson4D.DetParametrix.Core.MomentReduction

/-!
# High-frequency cutoff payoff for R-324

This file supplies the deterministic multiplier estimate used in paper
§4.2, Step 4.  Once the routing argument selects a noise frequency of
size at least `sqrt ε / 2` times the total external frequency, rapid
Fourier decay of the cutoff gives the central
`⟨ε²(α+β)⟩⁻⁸` payoff.

The result is deliberately below the probability layer: it concerns
only the deterministic cutoff symbol and the lattice frequency selected
after the Wick expansion.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- Exact comparison between the frequency convention of the Euclidean
Schwartz transform and the unscaled lattice frequency used by the
parametrix. -/
theorem euclideanFrequency_scaled_z4
    (ε : ℝ) (k : Z4) :
    euclideanFrequency (fun i => ε * (k i : ℝ)) =
      (ε / (2 * Real.pi)) • z4EuclideanFrequency k := by
  ext i
  simp only [euclideanFrequency_apply, z4EuclideanFrequency,
    PiLp.smul_apply, smul_eq_mul]
  ring

/-- Norm form of `euclideanFrequency_scaled_z4` on positive scales. -/
theorem norm_euclideanFrequency_scaled_z4
    {ε : ℝ} (hε : 0 ≤ ε) (k : Z4) :
    ‖euclideanFrequency (fun i => ε * (k i : ℝ))‖ =
      (ε / (2 * Real.pi)) * ‖z4EuclideanFrequency k‖ := by
  rw [euclideanFrequency_scaled_z4, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hε (by positivity))]

/-- The routed lattice mode is large enough at the actual Schwartz
frequency scale.  The numerical constant `16` harmlessly absorbs the
project's `2π` Fourier convention. -/
theorem eps_sq_mul_le_sixteen_mul_norm_euclideanFrequency
    {ε L : ℝ} {k : Z4}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hL : 0 ≤ L)
    (hroute :
      (Real.sqrt ε / 2) * L ≤
        ‖z4EuclideanFrequency k‖) :
    ε ^ 2 * L ≤
      16 *
        ‖euclideanFrequency (fun i => ε * (k i : ℝ))‖ := by
  rw [norm_euclideanFrequency_scaled_z4 hε.le]
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hεsqrt : ε ≤ Real.sqrt ε := by
    apply (Real.le_sqrt hε.le hε.le).2
    nlinarith [sq_nonneg (ε - 1)]
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hscale :
      ε ^ 2 * L ≤
        16 * (ε / (2 * Real.pi)) *
          ((Real.sqrt ε / 2) * L) := by
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have hsqrt_nonneg : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
    have hbase :
        ε ^ 2 ≤
          16 * (ε / (2 * Real.pi)) *
            (Real.sqrt ε / 2) := by
      calc
        ε ^ 2 ≤
            (4 * ε * Real.sqrt ε) / Real.pi := by
          apply (le_div_iff₀ hpi_pos).2
          calc
            ε ^ 2 * Real.pi ≤ ε ^ 2 * 4 := by
              gcongr
            _ ≤ 4 * ε * Real.sqrt ε := by
              nlinarith
        _ = 16 * (ε / (2 * Real.pi)) *
              (Real.sqrt ε / 2) := by
          field_simp [Real.pi_ne_zero]
          ring
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hbase hL
  have hfactor :
      0 ≤ 16 * (ε / (2 * Real.pi)) :=
    mul_nonneg (by norm_num)
      (div_nonneg hε.le (by positivity))
  have hrouteScaled :
      (16 * (ε / (2 * Real.pi))) *
          ((Real.sqrt ε / 2) * L) ≤
        (16 * (ε / (2 * Real.pi))) *
          ‖z4EuclideanFrequency k‖ :=
    mul_le_mul_of_nonneg_left hroute hfactor
  exact hscale.trans (by
    simpa only [mul_assoc] using hrouteScaled)

/-- Polynomial decay at Schwartz frequency controls the Japanese
bracket used in (3.24), once the routed mode is selected. -/
theorem one_add_norm_decay_le_routed_decay
    {ε L : ℝ} {k : Z4}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hL : 0 ≤ L)
    (hroute :
      (Real.sqrt ε / 2) * L ≤
        ‖z4EuclideanFrequency k‖) :
    ((1 +
        ‖euclideanFrequency (fun i => ε * (k i : ℝ))‖) ^ 8)⁻¹ ≤
      16 ^ (8 : ℕ) *
        eighthOrderFrequencyDecay (ε ^ 2 * L) := by
  let w : ℝ :=
    ‖euclideanFrequency (fun i => ε * (k i : ℝ))‖
  let x : ℝ := ε ^ 2 * L
  have hw : 0 ≤ w := norm_nonneg _
  have hx : 0 ≤ x := mul_nonneg (sq_nonneg ε) hL
  have hxw : x ≤ 16 * w := by
    simpa only [w, x] using
      eps_sq_mul_le_sixteen_mul_norm_euclideanFrequency
        hε hεsmall hL hroute
  have hquad :
      1 + x ^ 2 ≤
        16 ^ 2 * (1 + w) ^ 2 := by
    calc
      1 + x ^ 2 ≤ 1 + (16 * w) ^ 2 := by
        gcongr
      _ ≤ 16 ^ 2 * (1 + w) ^ 2 := by
        nlinarith [sq_nonneg (1 + w)]
  have hpow :
      (1 + x ^ 2) ^ 4 ≤
        16 ^ 8 * (1 + w) ^ 8 := by
    calc
      (1 + x ^ 2) ^ 4 ≤
          (16 ^ 2 * (1 + w) ^ 2) ^ 4 := by
        exact pow_le_pow_left₀ (by positivity) hquad 4
      _ = 16 ^ 8 * (1 + w) ^ 8 := by ring
  have hleft_pos : 0 < (1 + w) ^ 8 := by positivity
  have hright_pos : 0 < (1 + x ^ 2) ^ 4 := by positivity
  unfold eighthOrderFrequencyDecay
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hright_pos).2
  calc
    ((1 + w) ^ 8)⁻¹ * (1 + x ^ 2) ^ 4 ≤
        ((1 + w) ^ 8)⁻¹ *
          (16 ^ 8 * (1 + w) ^ 8) := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 16 ^ 8 := by
      field_simp [hleft_pos.ne']

/-- Paper §4.2, Step 4 at the level of a single selected cutoff
multiplier.  The constant depends only on the fixed cutoff. -/
theorem exists_r324_highFrequency_symbol_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ε L : ℝ} {k : Z4},
        0 < ε →
        ε ≤ 1 / 4 →
        0 ≤ L →
        (Real.sqrt ε / 2) * L ≤
          ‖z4EuclideanFrequency k‖ →
        ‖ρ.symbol ε k‖ ≤
          C * eighthOrderFrequencyDecay (ε ^ 2 * L) := by
  obtain ⟨C0, hC0, hcut⟩ :=
    ρ.exists_fourierR4_one_add_norm_bound
  refine ⟨C0 * 16 ^ (8 : ℕ), mul_pos hC0 (by positivity),
    fun {ε L} {k} hε hεsmall hL hroute => ?_⟩
  let w : ℝ :=
    ‖euclideanFrequency (fun i => ε * (k i : ℝ))‖
  have hwpos : 0 < (1 + w) ^ 8 := by
    dsimp only [w]
    positivity
  have hschwartz :
      (1 + w) ^ 8 * ‖ρ.symbol ε k‖ ≤ C0 := by
    simpa [w, SmoothCutoff.symbol] using
      hcut (fun i => ε * (k i : ℝ))
  have hdivide :
      ‖ρ.symbol ε k‖ ≤
        C0 * ((1 + w) ^ 8)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hwpos).2
      (by simpa [mul_comm] using hschwartz)
  calc
    ‖ρ.symbol ε k‖ ≤
        C0 * ((1 + w) ^ 8)⁻¹ := hdivide
    _ ≤ C0 *
          (16 ^ (8 : ℕ) *
            eighthOrderFrequencyDecay (ε ^ 2 * L)) := by
      gcongr
      simpa only [w] using
        one_add_norm_decay_le_routed_decay
          hε hεsmall hL hroute
    _ = (C0 * 16 ^ (8 : ℕ)) *
          eighthOrderFrequencyDecay (ε ^ 2 * L) := by
      ring

end SmoothCutoff

end

end Anderson4D
