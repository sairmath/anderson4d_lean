import Anderson4D.Continuum.Basic

/-!
# Frequency routing and endpoint oscillation (paper §4.2, Step 4)

This file isolates the deterministic inequalities used in the
frequency-decay part of the proof of (3.24):

* if a composition of finitely many factors produces a total frequency
  shift, one factor carries at least the average shift;
* under a bound on the number of factors, this gives the
  `ε^(1/2) L` high-frequency factor singled out in the paper;
* the endpoint phase difference has both the global linear estimate and
  the even, quadratic cosine estimate used after the `𝓔`-cancellation.

Keeping these statements independent of the parametrix syntax makes the
frequency-routing step reusable when the closed deterministic profiles are
assembled in `Estimates.lean`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open scoped BigOperators

noncomputable section

/-! ## A large increment carries the total frequency shift -/

/-- A finite sum in a seminormed group has a summand carrying at least its
average norm.  The division-free form is convenient for the paper's
`O(|log ε|)` composition length. -/
theorem exists_large_frequency_increment
    {E : Type*} [SeminormedAddCommGroup E]
    (N : ℕ) (hN : 0 < N) (δ : Fin N → E) :
    ∃ i : Fin N, ‖∑ j, δ j‖ ≤ (N : ℝ) * ‖δ i‖ := by
  have huniv : (Finset.univ : Finset (Fin N)).Nonempty :=
    ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  obtain ⟨i, _hi, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin N))
      (fun j => ‖δ j‖) huniv
  refine ⟨i, (norm_sum_le Finset.univ δ).trans ?_⟩
  calc
    ∑ j : Fin N, ‖δ j‖ ≤ ∑ _j : Fin N, ‖δ i‖ := by
      exact Finset.sum_le_sum fun j hj => hmax j hj
    _ = (N : ℝ) * ‖δ i‖ := by simp

/-- Threshold form of frequency routing.  If the number of factors is at
most `r⁻¹`, one factor shifts frequency by at least `r` times the total
shift.  In the paper one takes `r = ε^(1/2)`. -/
theorem exists_frequency_increment_above_threshold
    {E : Type*} [SeminormedAddCommGroup E]
    (N : ℕ) (hN : 0 < N) (δ : Fin N → E)
    (r : ℝ) (hr : 0 < r) (hcount : (N : ℝ) ≤ r⁻¹) :
    ∃ i : Fin N, r * ‖∑ j, δ j‖ ≤ ‖δ i‖ := by
  obtain ⟨i, hi⟩ := exists_large_frequency_increment N hN δ
  refine ⟨i, ?_⟩
  calc
    r * ‖∑ j, δ j‖ ≤ r * ((N : ℝ) * ‖δ i‖) :=
      mul_le_mul_of_nonneg_left hi hr.le
    _ ≤ r * (r⁻¹ * ‖δ i‖) := by
      gcongr
    _ = ‖δ i‖ := by
      rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

/-- The concrete square-root-scale version quoted in paper §4.2 Step 4.
It is stated with `sqrt ε`, avoiding any ambiguity about real powers. -/
theorem exists_frequency_increment_above_sqrt
    {E : Type*} [SeminormedAddCommGroup E]
    (N : ℕ) (hN : 0 < N) (δ : Fin N → E)
    (ε : ℝ) (hε : 0 < ε)
    (hcount : (N : ℝ) ≤ (Real.sqrt ε)⁻¹) :
    ∃ i : Fin N, Real.sqrt ε * ‖∑ j, δ j‖ ≤ ‖δ i‖ :=
  exists_frequency_increment_above_threshold N hN δ
    (Real.sqrt ε) (Real.sqrt_pos.2 hε) hcount

/-- The paper's truncation length is eventually much smaller than the
inverse square-root scale.  The explicit constant `2` follows directly
from `log x ≤ x^(1/2)/(1/2)`. -/
theorem truncOrder_cast_le_two_mul_inv_sqrt
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (truncOrder ε : ℝ) ≤ 2 * (Real.sqrt ε)⁻¹ := by
  have hfloor :
      (truncOrder ε : ℝ) ≤ |Real.log ε| := by
    exact Nat.floor_le (abs_nonneg (Real.log ε))
  have habslog :
      |Real.log ε| = Real.log ε⁻¹ := by
    rw [abs_of_nonpos (Real.log_nonpos hε.le hε1), Real.log_inv]
  have hlog :=
    Real.log_le_rpow_div (x := ε⁻¹) (inv_nonneg.mpr hε.le)
      (show (0 : ℝ) < 1 / 2 by norm_num)
  calc
    (truncOrder ε : ℝ) ≤ |Real.log ε| := hfloor
    _ = Real.log ε⁻¹ := habslog
    _ ≤ ε⁻¹ ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) := hlog
    _ = 2 * (Real.sqrt ε)⁻¹ := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_inv]
      ring

/-- Concrete routing at the actual truncation order.  A chain of at most
`A = floor |log ε|` factors contains a shift of size at least
`(sqrt ε / 2)` times the total shift.  The absolute factor `2` is harmless
in the multiplier decay and is now explicit rather than hidden by `≳`. -/
theorem exists_frequency_increment_at_truncation_scale
    {E : Type*} [SeminormedAddCommGroup E]
    (N : ℕ) (hN : 0 < N) (δ : Fin N → E)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hNtrunc : N ≤ truncOrder ε) :
    ∃ i : Fin N,
      (Real.sqrt ε / 2) * ‖∑ j, δ j‖ ≤ ‖δ i‖ := by
  obtain ⟨i, hi⟩ := exists_large_frequency_increment N hN δ
  refine ⟨i, ?_⟩
  have hcount : (N : ℝ) ≤ 2 * (Real.sqrt ε)⁻¹ := by
    exact (Nat.cast_le.mpr hNtrunc).trans
      (truncOrder_cast_le_two_mul_inv_sqrt hε hε1)
  calc
    (Real.sqrt ε / 2) * ‖∑ j, δ j‖
        ≤ (Real.sqrt ε / 2) * ((N : ℝ) * ‖δ i‖) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ (Real.sqrt ε / 2) *
          ((2 * (Real.sqrt ε)⁻¹) * ‖δ i‖) := by
      gcongr
    _ = ‖δ i‖ := by
      have hsqrt : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.2 hε).ne'
      field_simp

/-! ## The eighth-order multiplier payoff -/

/-- The paper's `⟨x⟩⁻⁸`, written without real powers:
`(1 + x²)⁻⁴`.  This form has the same value and a simpler order API. -/
def eighthOrderFrequencyDecay (x : ℝ) : ℝ :=
  ((1 + x ^ 2) ^ 4)⁻¹

theorem eighthOrderFrequencyDecay_nonneg (x : ℝ) :
    0 ≤ eighthOrderFrequencyDecay x := by
  unfold eighthOrderFrequencyDecay
  positivity

/-- `⟨x⟩⁻⁸` is decreasing on the nonnegative half-line. -/
theorem eighthOrderFrequencyDecay_anti
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    eighthOrderFrequencyDecay y ≤ eighthOrderFrequencyDecay x := by
  unfold eighthOrderFrequencyDecay
  apply inv_anti₀ (by positivity)
  apply pow_le_pow_left₀ (by positivity) _ 4
  gcongr

/-- A routed shift of size `sqrt ε · L` supplies at least the decay at that
scale. -/
theorem routed_decay_le_sqrt_decay
    {ε L h : ℝ} (_hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hroute : Real.sqrt ε * L ≤ h) :
    eighthOrderFrequencyDecay h ≤
      eighthOrderFrequencyDecay (Real.sqrt ε * L) :=
  eighthOrderFrequencyDecay_anti
    (mul_nonneg (Real.sqrt_nonneg ε) hL) hroute

/-- For `0 < ε ≤ 1`, the routed `sqrt ε · L` decay is stronger than the
`ε² L` decay printed in (3.24).  This is the precise scale comparison left
implicit in paper §4.2 Step 4. -/
theorem sqrt_decay_le_eps_sq_decay
    {ε L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hL : 0 ≤ L) :
    eighthOrderFrequencyDecay (Real.sqrt ε * L) ≤
      eighthOrderFrequencyDecay (ε ^ 2 * L) := by
  apply eighthOrderFrequencyDecay_anti
  · positivity
  · apply mul_le_mul_of_nonneg_right _ hL
    have hsq : ε ^ 2 ≤ ε := by
      nlinarith [sq_nonneg (ε - 1)]
    have hsqrt : ε ≤ Real.sqrt ε := by
      exact (Real.le_sqrt hε.le hε.le).2 hsq
    exact hsq.trans hsqrt

/-- The complete scalar payoff of the routing argument: a selected
high-frequency factor at `sqrt ε · L` yields the exact
`⟨ε²L⟩⁻⁸` factor used in (3.24). -/
theorem routed_decay_le_eps_sq_decay
    {ε L h : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hL : 0 ≤ L)
    (hroute : Real.sqrt ε * L ≤ h) :
    eighthOrderFrequencyDecay h ≤
      eighthOrderFrequencyDecay (ε ^ 2 * L) :=
  (routed_decay_le_sqrt_decay hε.le hL hroute).trans
    (sqrt_decay_le_eps_sq_decay hε hε1 hL)

/-- On the eventual range `ε ≤ 1/4`, the explicit factor `1/2` from the
truncation-length routing still dominates the paper's `ε²` scale. -/
theorem eps_sq_le_sqrt_div_two
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) :
    ε ^ 2 ≤ Real.sqrt ε / 2 := by
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hsqε : ε ^ 2 ≤ ε := by
    nlinarith [sq_nonneg (ε - 1)]
  have hεsqrt : ε ≤ Real.sqrt ε :=
    (Real.le_sqrt hε.le hε.le).2 hsqε
  have hquarter : ε ^ 2 ≤ ε / 4 := by
    nlinarith
  nlinarith [Real.sqrt_nonneg ε]

/-- Exact decay payoff for a shift selected at the actual truncation order.
This is the paper's Step 4 scale comparison with all eventual constants
visible. -/
theorem truncation_routed_decay_le_eps_sq_decay
    {ε L h : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hL : 0 ≤ L)
    (hroute : (Real.sqrt ε / 2) * L ≤ h) :
    eighthOrderFrequencyDecay h ≤
      eighthOrderFrequencyDecay (ε ^ 2 * L) := by
  apply eighthOrderFrequencyDecay_anti
  · positivity
  · exact (mul_le_mul_of_nonneg_right
      (eps_sq_le_sqrt_div_two hε hεsmall) hL).trans hroute

/-! ## Endpoint oscillation -/

/-- Global endpoint-phase estimate.  This is the bound used before taking
absolute values in the four external variables of (4.18). -/
theorem norm_complex_phase_sub_one_le (θ : ℝ) :
    ‖Complex.exp (Complex.I * θ) - 1‖ ≤ |θ| := by
  simpa [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ))

/-- The global bounded estimate for the real endpoint oscillation. -/
theorem abs_cos_sub_one_le_two (θ : ℝ) :
    |Real.cos θ - 1| ≤ 2 := by
  calc
    |Real.cos θ - 1| ≤ |Real.cos θ| + |(1 : ℝ)| := abs_sub _ _
    _ = |Real.cos θ| + 1 := by norm_num
    _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one θ) le_rfl
    _ = 2 := by norm_num

/-- The quadratic endpoint estimate after the odd part has vanished by
`𝓔`-symmetry.  The paper only needs the coarser constant `1`; the elementary
identity actually gives the sharper constant `1/2`. -/
theorem abs_cos_sub_one_le_sq (θ : ℝ) :
    |Real.cos θ - 1| ≤ θ ^ 2 := by
  have hsin := Real.abs_sin_le_abs (x := θ / 2)
  have hsin_sq :
      Real.sin (θ / 2) ^ 2 ≤ (θ / 2) ^ 2 := by
    exact sq_le_sq.mpr hsin
  have hphase :
      Real.cos θ - 1 = -2 * Real.sin (θ / 2) ^ 2 := by
    rw [show θ = 2 * (θ / 2) by ring_nf, Real.cos_two_mul_eq_one_sub]
    ring_nf
  rw [hphase, abs_of_nonpos (by
    nlinarith [sq_nonneg (Real.sin (θ / 2))])]
  nlinarith [sq_nonneg θ]

/-- Both endpoint bounds in one interface.  The assembly chooses the
quadratic branch when the inserted diameter is available and the bounded
branch when preserving Fourier decay costs the paper's `ε⁻²` loss. -/
theorem endpoint_oscillation_bounds (θ : ℝ) :
    |Real.cos θ - 1| ≤ θ ^ 2 ∧ |Real.cos θ - 1| ≤ 2 :=
  ⟨abs_cos_sub_one_le_sq θ, abs_cos_sub_one_le_two θ⟩

end

end Anderson4D
