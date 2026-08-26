import Anderson4D.DetParametrix.Paper42_Moment.R324ComplementScheduleCore

/-!
# Shifted-window lattice sums for the general-`m` cross peel

The proved complement-schedule closure bounded the diagonal window
`Σ_k ‖ρ̂(εk)‖⁴⟨k⟩⁻⁴ ≤ C(ρ)|log ε|`.  The general-`m` peel meets
translated windows `Σ_k ‖ρ̂(εk)‖²⟨k+α⟩⁻²⟨k+β⟩⁻²`.  This file proves
the shifted bounds, uniformly in the shifts, with per-mollifier
constants:

* `r324SW_symbol_mass_le` — total symbol mass `Σ_k ‖ρ̂(εk)‖² ≤ C ε⁻⁴`;
* `r324SW_translated_window_le_log` — `Σ_k ‖ρ̂(εk)‖²⟨k+γ⟩⁻⁴ ≤ C|log ε|`;
* `r324SW_shifted_window_le_log` — the bilinear form, via `2xy ≤ x²+y²`;
* `r324SW_separated_window_le_log` — the decay-retaining variant with
  the `⟨α-β⟩⁻⁴` separation factor.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- Degree-four decay of the scaled symbol against the sup bracket,
squared: the degree-eight companion of `symbol_sq_le_of_decay`. -/
theorem r324SW_symbol_sq_le_of_decay_eight
    (ρ : SmoothCutoff) {C0 : ℝ}
    (hdecay : ∀ ξ : R4,
      (1 + ‖SmoothCutoff.euclideanFrequency ξ‖) ^ 8 *
        ‖fourierR4 ρ ξ‖ ≤ C0)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (k : Z4) :
    ‖ρ.symbol ε k‖ ^ 2 ≤
      (C0 ^ 2 * (2 * Real.pi) ^ 8) *
        (ε⁻¹ ^ 8 * (((1 + (z4SupRadius k : ℝ)) ^ 8)⁻¹)) := by
  set ξ : R4 := fun i => ε * (k i : ℝ) with hξdef
  set w := SmoothCutoff.euclideanFrequency ξ with hwdef
  set s : ℝ := (z4SupRadius k : ℝ) with hsdef
  have hs : 0 ≤ s := Nat.cast_nonneg _
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have hC0 : 0 ≤ C0 := by
    have h := hdecay 0
    have h1 : (0:ℝ) ≤
        (1 + ‖SmoothCutoff.euclideanFrequency (0 : R4)‖) ^ 8 *
          ‖fourierR4 ρ (0 : R4)‖ := by positivity
    linarith
  have hsym : ‖ρ.symbol ε k‖ = ‖fourierR4 ρ ξ‖ := rfl
  have hwlow : ε / (2 * Real.pi) * s ≤ ‖w‖ := by
    obtain ⟨i₀, _hi₀, hsup⟩ :=
      Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin dim))
        ⟨0, Finset.mem_univ 0⟩ (fun i => Int.natAbs (k i))
    have hcoord : ε / (2 * Real.pi) * s = ‖w i₀‖ := by
      rw [hsdef]
      unfold z4SupRadius
      rw [hsup]
      simp only [hwdef, hξdef,
        SmoothCutoff.euclideanFrequency_apply, Real.norm_eq_abs]
      rw [abs_div, abs_mul, abs_of_pos hε,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
        Nat.cast_natAbs, Int.cast_abs]
      field_simp
    rw [hcoord]
    exact PiLp.norm_apply_le w i₀
  have hbracket : ε / (2 * Real.pi) * (1 + s) ≤ 1 + ‖w‖ := by
    have hone : ε / (2 * Real.pi) ≤ 1 := by
      have hπ : (1 : ℝ) ≤ 2 * Real.pi := by
        nlinarith [Real.pi_gt_three]
      rw [div_le_one (by positivity)]
      linarith
    calc
      ε / (2 * Real.pi) * (1 + s) =
          ε / (2 * Real.pi) + ε / (2 * Real.pi) * s := by ring
      _ ≤ 1 + ‖w‖ := add_le_add hone hwlow
  have hsymle : ‖ρ.symbol ε k‖ ≤ C0 * ((1 + ‖w‖) ^ 4)⁻¹ := by
    have h8 := hdecay ξ
    rw [← hwdef, ← hsym] at h8
    have hpow : (1 + ‖w‖) ^ 4 ≤ (1 + ‖w‖) ^ 8 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    have h4 : (1 + ‖w‖) ^ 4 * ‖ρ.symbol ε k‖ ≤ C0 :=
      le_trans
        (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) h8
    rw [mul_comm, ← le_div_iff₀
      (by positivity : (0:ℝ) < (1 + ‖w‖) ^ 4), div_eq_mul_inv]
      at h4
    exact h4
  have hbr4 :
      ((1 + ‖w‖) ^ 4)⁻¹ ≤
        ((2 * Real.pi) ^ 4 * ε⁻¹ ^ 4) * ((1 + s) ^ 4)⁻¹ := by
    have hlhs : 0 < ε / (2 * Real.pi) * (1 + s) := by positivity
    have hinv :
        (1 + ‖w‖)⁻¹ ≤ (ε / (2 * Real.pi) * (1 + s))⁻¹ :=
      inv_anti₀ hlhs hbracket
    have hval :
        (ε / (2 * Real.pi) * (1 + s))⁻¹ =
          (2 * Real.pi) * ε⁻¹ * (1 + s)⁻¹ := by
      rw [mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
      ring
    have hq :
        ((1 + ‖w‖)⁻¹) ^ 4 ≤
          ((2 * Real.pi) * ε⁻¹ * (1 + s)⁻¹) ^ 4 := by
      rw [← hval]
      exact pow_le_pow_left₀ (by positivity) hinv 4
    calc
      ((1 + ‖w‖) ^ 4)⁻¹ = ((1 + ‖w‖)⁻¹) ^ 4 := by rw [inv_pow]
      _ ≤ ((2 * Real.pi) * ε⁻¹ * (1 + s)⁻¹) ^ 4 := hq
      _ = ((2 * Real.pi) ^ 4 * ε⁻¹ ^ 4) * ((1 + s) ^ 4)⁻¹ := by
        have h1s : (1 + s) ≠ 0 := by positivity
        field_simp
  calc
    ‖ρ.symbol ε k‖ ^ 2 ≤
        (C0 * (((2 * Real.pi) ^ 4 * ε⁻¹ ^ 4) *
          ((1 + s) ^ 4)⁻¹)) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      calc
        ‖ρ.symbol ε k‖ ≤ C0 * ((1 + ‖w‖) ^ 4)⁻¹ := hsymle
        _ ≤ C0 * (((2 * Real.pi) ^ 4 * ε⁻¹ ^ 4) *
              ((1 + s) ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left hbr4 hC0
    _ = (C0 ^ 2 * (2 * Real.pi) ^ 8) *
          (ε⁻¹ ^ 8 * (((1 + s) ^ 8)⁻¹)) := by
      have h1s : (1 + s) ≠ 0 := by positivity
      field_simp

/-- The squared scaled symbol is summable over the frequency lattice. -/
theorem r324SW_summable_symbol_sq
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Summable fun k : Z4 => ‖ρ.symbol ε k‖ ^ 2 := by
  obtain ⟨C0, _hC0, hdecay⟩ := ρ.exists_fourierR4_one_add_norm_bound
  refine (summable_l2LatticeRadialWeight_eight.mul_left
    ((C0 ^ 2 * (2 * Real.pi) ^ 8) * ε⁻¹ ^ 8)).of_nonneg_of_le
    (fun k => by positivity) (fun k => ?_)
  have h := r324SW_symbol_sq_le_of_decay_eight ρ hdecay hε hε1 k
  rw [l2LatticeRadialWeight_eq_z4SupRadius]
  exact h.trans_eq (by ring)

/-- **Total symbol mass.**  The `ε`-cube carries `≲ ε⁻⁴` unit terms
and the degree-8 decay pays the eighth-order radial tail, so
`Σ_k ‖ρ̂(εk)‖² ≤ C(ρ) ε⁻⁴`. -/
theorem r324SW_symbol_mass_le (ρ : SmoothCutoff) :
    ∃ CM : ℝ, 0 < CM ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        (∑' k : Z4, ‖ρ.symbol ε k‖ ^ 2) ≤ CM * ε⁻¹ ^ 4 := by
  obtain ⟨C0, hC0, hdecay⟩ := ρ.exists_fourierR4_one_add_norm_bound
  set B : ℝ := C0 ^ 2 * (2 * Real.pi) ^ 8 with hBdef
  have hB : 0 < B := by rw [hBdef]; positivity
  refine ⟨1296 + 20 * B, by positivity, ?_⟩
  intro ε hε hε1
  set N : ℕ := ⌈ε⁻¹⌉₊ with hNdef
  have hεinv1 : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
  have hNε : ε⁻¹ ≤ (N : ℝ) := Nat.le_ceil _
  have hNup : (N : ℝ) + 1 ≤ 3 * ε⁻¹ := by
    have hceil : (N : ℝ) < ε⁻¹ + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith
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
    by_cases hk : k ∈ z4Cube N
    · refine le_trans ?_ (le_add_of_nonneg_right (hh0 k))
      simp only [hfdef, hgdef]
      rw [if_pos hk]
      exact pow_le_one₀ (norm_nonneg _) (ρ.norm_symbol_le_one ε k)
    · refine le_trans ?_ (le_add_of_nonneg_left (hg0 k))
      have hrad : N + 1 ≤ z4SupRadius k := by
        rw [mem_z4Cube_iff_z4SupRadius_le] at hk
        omega
      simp only [hfdef, hhdef]
      have htail : z4EighthRadialTail (N + 1) k =
          l2LatticeRadialWeight 8 k := by
        unfold z4EighthRadialTail
        rw [if_pos hrad]
      rw [htail, l2LatticeRadialWeight_eq_z4SupRadius]
      exact (r324SW_symbol_sq_le_of_decay_eight
        ρ hdecay hε hε1 k).trans_eq (by ring)
  have hgsummable : Summable g := by
    apply summable_of_ne_finset_zero (s := z4Cube N)
    intro k hk
    simp only [hgdef]
    exact if_neg hk
  have hhsummable : Summable h := by
    simp only [hhdef]
    exact (summable_z4EighthRadialTail (N + 1)).mul_left _
  have hfsummable : Summable f :=
    Summable.of_nonneg_of_le (fun k => by simp only [hfdef]; positivity)
      hfg (hgsummable.add hhsummable)
  have hgsum : (∑' k, g k) ≤ 1296 * ε⁻¹ ^ 4 := by
    have hgeq : (∑' k, g k) = ∑ k ∈ z4Cube N, (1 : ℝ) := by
      rw [tsum_eq_sum (s := z4Cube N) ?_]
      · exact Finset.sum_congr rfl fun k hk => by
          simp only [hgdef]; exact if_pos hk
      · intro k hk
        simp only [hgdef]
        exact if_neg hk
    rw [hgeq, Finset.sum_const, nsmul_eq_mul, mul_one,
      card_z4Cube]
    have hside : ((2 * N + 1 : ℕ) : ℝ) ≤ 6 * ε⁻¹ := by
      push_cast
      linarith
    calc
      (((2 * N + 1) ^ 4 : ℕ) : ℝ) = ((2 * N + 1 : ℕ) : ℝ) ^ 4 := by
        push_cast
        ring
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
    have hεN4 : (((N + 1 : ℕ) : ℝ)⁻¹) ^ 4 ≤ ε ^ 4 := by
      push_cast
      exact pow_le_pow_left₀ (by positivity) hεN 4
    have hcancel : ε⁻¹ ^ 4 * ε ^ 4 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hε.ne', one_pow]
    simp only [hhdef]
    rw [tsum_mul_left]
    calc
      (B * ε⁻¹ ^ 8) * ∑' k, z4EighthRadialTail (N + 1) k ≤
          (B * ε⁻¹ ^ 8) * (20 * (((N + 1 : ℕ) : ℝ)⁻¹) ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact htail
      _ ≤ (B * ε⁻¹ ^ 8) * (20 * ε ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      _ = (20 * B * ε⁻¹ ^ 4) * (ε⁻¹ ^ 4 * ε ^ 4) := by ring
      _ = 20 * B * ε⁻¹ ^ 4 := by rw [hcancel, mul_one]
  calc
    (∑' k, f k) ≤ ∑' k, (g k + h k) :=
      hfsummable.tsum_le_tsum hfg (hgsummable.add hhsummable)
    _ = (∑' k, g k) + ∑' k, h k :=
      hgsummable.tsum_add hhsummable
    _ ≤ 1296 * ε⁻¹ ^ 4 + 20 * B * ε⁻¹ ^ 4 := add_le_add hgsum hhsum
    _ = (1296 + 20 * B) * ε⁻¹ ^ 4 := by ring

/-- The squared Euclidean bracket dominated by the fourth-order sup
bracket, at an arbitrary lattice point. -/
theorem r324SW_bracket4 (m : Z4) :
    ((1 + paperModeNormSq m)⁻¹) ^ 2 ≤
      4 * (((1 + (z4SupRadius m : ℝ)) ^ 4)⁻¹) := by
  have hb := inv_one_add_paperModeNormSq_le m
  have hP := paperModeNormSq_nonneg m
  have h0 : (0:ℝ) ≤ (1 + paperModeNormSq m)⁻¹ :=
    inv_nonneg.mpr (by linarith)
  calc
    ((1 + paperModeNormSq m)⁻¹) ^ 2 ≤
        (2 * (((1 + (z4SupRadius m : ℝ)) ^ 2)⁻¹)) ^ 2 :=
      pow_le_pow_left₀ h0 hb 2
    _ = 4 * (((1 + (z4SupRadius m : ℝ)) ^ 2) ^ 2)⁻¹ := by
      rw [mul_pow, inv_pow]
      norm_num
    _ = 4 * (((1 + (z4SupRadius m : ℝ)) ^ 4)⁻¹) := by
      rw [← pow_mul]

/-- The Euclidean bracket is at most one. -/
theorem r324SW_bracket_le_one (m : Z4) :
    (1 + paperModeNormSq m)⁻¹ ≤ 1 := by
  have hP := paperModeNormSq_nonneg m
  have h : (1 + paperModeNormSq m)⁻¹ ≤ (1 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) (by linarith)
  rwa [inv_one] at h

theorem r324SW_bracket_nonneg (m : Z4) :
    0 ≤ (1 + paperModeNormSq m)⁻¹ :=
  inv_nonneg.mpr (by linarith [paperModeNormSq_nonneg m])

/-- The translated-window integrand is summable, for every shift. -/
theorem r324SW_summable_translated_window
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (γ : Z4) :
    Summable fun k : Z4 =>
      ‖ρ.symbol ε k‖ ^ 2 *
        ((1 + paperModeNormSq (k + γ))⁻¹) ^ 2 := by
  refine (r324SW_summable_symbol_sq ρ hε hε1).of_nonneg_of_le
    (fun k => mul_nonneg (by positivity) (sq_nonneg _))
    (fun k => ?_)
  calc
    ‖ρ.symbol ε k‖ ^ 2 * ((1 + paperModeNormSq (k + γ))⁻¹) ^ 2 ≤
        ‖ρ.symbol ε k‖ ^ 2 * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_one₀ (r324SW_bracket_nonneg (k + γ))
        (r324SW_bracket_le_one (k + γ))
    _ = ‖ρ.symbol ε k‖ ^ 2 := mul_one _

/-- **The translated window is logarithmic, uniformly in the shift.**
The head is the cube `|k+γ|_∞ ≤ ⌈ε⁻¹⌉`, which re-centers to the
proved diagonal harmonic-shell estimate; outside it the bracket is
`≤ 4ε⁴` pointwise and the total symbol mass pays the `ε⁻⁴`. -/
theorem r324SW_translated_window_le_log (ρ : SmoothCutoff) :
    ∃ CT : ℝ, 0 < CT ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        ∀ γ : Z4,
        (∑' k : Z4,
          ‖ρ.symbol ε k‖ ^ 2 *
            ((1 + paperModeNormSq (k + γ))⁻¹) ^ 2) ≤
          CT * |Real.log ε| := by
  obtain ⟨CM, hCM, hmass⟩ := r324SW_symbol_mass_le ρ
  refine ⟨1280 + 4 * CM, by positivity, ?_⟩
  intro ε hε hε1 hlog γ
  set L : ℝ := |Real.log ε| with hLdef
  have hL1 : (1 : ℝ) ≤ L := hlog
  set N : ℕ := ⌈ε⁻¹⌉₊ with hNdef
  have hεinv1 : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
  have hNε : ε⁻¹ ≤ (N : ℝ) := Nat.le_ceil _
  have hNup : (N : ℝ) + 1 ≤ 3 * ε⁻¹ := by
    have hceil : (N : ℝ) < ε⁻¹ + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith
  set f : Z4 → ℝ := fun k =>
    ‖ρ.symbol ε k‖ ^ 2 * ((1 + paperModeNormSq (k + γ))⁻¹) ^ 2
    with hfdef
  set G : Z4 → ℝ := fun j =>
    if j ∈ z4Cube N then 4 * l2LatticeRadialWeight 4 j else 0
    with hGdef
  set g : Z4 → ℝ := fun k => G (k + γ) with hgdef
  set h : Z4 → ℝ := fun k => (4 * ε ^ 4) * ‖ρ.symbol ε k‖ ^ 2
    with hhdef
  have hG0 : ∀ j, 0 ≤ G j := by
    intro j
    simp only [hGdef]
    by_cases hj : j ∈ z4Cube N
    · rw [if_pos hj]
      unfold l2LatticeRadialWeight
      positivity
    · rw [if_neg hj]
  have hg0 : ∀ k, 0 ≤ g k := fun k => hG0 (k + γ)
  have hh0 : ∀ k, 0 ≤ h k := by
    intro k
    simp only [hhdef]
    positivity
  have hf0 : ∀ k, 0 ≤ f k := fun k =>
    mul_nonneg (by positivity) (sq_nonneg _)
  have hfg : ∀ k, f k ≤ g k + h k := by
    intro k
    by_cases hk : k + γ ∈ z4Cube N
    · refine le_trans ?_ (le_add_of_nonneg_right (hh0 k))
      simp only [hfdef, hgdef, hGdef]
      rw [if_pos hk]
      calc
        ‖ρ.symbol ε k‖ ^ 2 *
            ((1 + paperModeNormSq (k + γ))⁻¹) ^ 2 ≤
            1 * ((1 + paperModeNormSq (k + γ))⁻¹) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact pow_le_one₀ (norm_nonneg _)
            (ρ.norm_symbol_le_one ε k)
        _ = ((1 + paperModeNormSq (k + γ))⁻¹) ^ 2 := one_mul _
        _ ≤ 4 * (((1 + (z4SupRadius (k + γ) : ℝ)) ^ 4)⁻¹) :=
          r324SW_bracket4 (k + γ)
        _ = 4 * l2LatticeRadialWeight 4 (k + γ) := by
          rw [l2LatticeRadialWeight_eq_z4SupRadius]
    · refine le_trans ?_ (le_add_of_nonneg_left (hg0 k))
      have hrad : N + 1 ≤ z4SupRadius (k + γ) := by
        rw [mem_z4Cube_iff_z4SupRadius_le] at hk
        omega
      have hcast : ((N : ℝ)) + 1 ≤ (z4SupRadius (k + γ) : ℝ) := by
        exact_mod_cast hrad
      have hsup : ε⁻¹ ≤ 1 + (z4SupRadius (k + γ) : ℝ) := by
        linarith
      have hbr : ((1 + (z4SupRadius (k + γ) : ℝ)) ^ 4)⁻¹ ≤
          ε ^ 4 := by
        have h4 : (ε⁻¹) ^ 4 ≤
            (1 + (z4SupRadius (k + γ) : ℝ)) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hsup 4
        have hi := inv_anti₀
          (by positivity : (0:ℝ) < (ε⁻¹) ^ 4) h4
        rwa [inv_pow, inv_inv] at hi
      simp only [hfdef, hhdef]
      calc
        ‖ρ.symbol ε k‖ ^ 2 *
            ((1 + paperModeNormSq (k + γ))⁻¹) ^ 2 ≤
            ‖ρ.symbol ε k‖ ^ 2 * (4 * ε ^ 4) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (r324SW_bracket4 (k + γ)).trans
            (mul_le_mul_of_nonneg_left hbr (by norm_num))
        _ = (4 * ε ^ 4) * ‖ρ.symbol ε k‖ ^ 2 := by ring
  have hGsummable : Summable G := by
    apply summable_of_ne_finset_zero (s := z4Cube N)
    intro j hj
    simp only [hGdef]
    exact if_neg hj
  have hgsummable : Summable g := by
    rw [hgdef]
    have hcomp := hGsummable.comp_injective (add_left_injective γ)
    simpa [Function.comp_def] using hcomp
  have hhsummable : Summable h := by
    simp only [hhdef]
    exact (r324SW_summable_symbol_sq ρ hε hε1).mul_left _
  have hfsummable : Summable f :=
    Summable.of_nonneg_of_le hf0 hfg (hgsummable.add hhsummable)
  have hgsum_eq : (∑' k, g k) = ∑' j, G j := by
    simp only [hgdef]
    rw [← Equiv.tsum_eq (Equiv.addRight γ) G]
    simp only [Equiv.coe_addRight]
  have hGsum : (∑' j, G j) ≤ 1280 * L := by
    have hGeq : (∑' j, G j) =
        ∑ j ∈ z4Cube N, 4 * l2LatticeRadialWeight 4 j := by
      rw [tsum_eq_sum (s := z4Cube N) ?_]
      · exact Finset.sum_congr rfl fun j hj => by
          simp only [hGdef]
          exact if_pos hj
      · intro j hj
        simp only [hGdef]
        exact if_neg hj
    rw [hGeq, ← Finset.mul_sum]
    have hshell := sum_z4Cube_l2LatticeRadialWeight_four_le_log N
    have hlogN : Real.log ((N : ℝ) + 1) ≤ 2 + L := by
      have h3 : Real.log ((N : ℝ) + 1) ≤ Real.log (3 * ε⁻¹) :=
        Real.log_le_log (by positivity) hNup
      have hsplit : Real.log (3 * ε⁻¹) =
          Real.log 3 + Real.log ε⁻¹ :=
        Real.log_mul (by norm_num) (by positivity)
      have hlog3 : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (x := 3) (by norm_num)
        linarith
      have hinvlog : Real.log ε⁻¹ = L := by
        rw [Real.log_inv, hLdef,
          abs_of_nonpos (Real.log_nonpos hε.le hε1)]
      linarith [h3, hsplit.le, hsplit.ge]
    calc
      4 * ∑ j ∈ z4Cube N, l2LatticeRadialWeight 4 j ≤
          4 * (80 * (1 + Real.log ((N : ℝ) + 1))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa using hshell
      _ ≤ 4 * (80 * (1 + (2 + L))) := by
        have hmono : (1 : ℝ) + Real.log ((N : ℝ) + 1) ≤
            1 + (2 + L) := by
          linarith
        nlinarith
      _ ≤ 1280 * L := by nlinarith
  have hhsum : (∑' k, h k) ≤ 4 * CM := by
    have hm := hmass hε hε1
    have hcancel : ε ^ 4 * ε⁻¹ ^ 4 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hε.ne', one_pow]
    simp only [hhdef]
    rw [tsum_mul_left]
    calc
      (4 * ε ^ 4) * ∑' k, ‖ρ.symbol ε k‖ ^ 2 ≤
          (4 * ε ^ 4) * (CM * ε⁻¹ ^ 4) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = 4 * CM * (ε ^ 4 * ε⁻¹ ^ 4) := by ring
      _ = 4 * CM := by rw [hcancel, mul_one]
  calc
    (∑' k, f k) ≤ ∑' k, (g k + h k) :=
      hfsummable.tsum_le_tsum hfg (hgsummable.add hhsummable)
    _ = (∑' k, g k) + ∑' k, h k := hgsummable.tsum_add hhsummable
    _ ≤ 1280 * L + 4 * CM := by
      rw [hgsum_eq]
      exact add_le_add hGsum hhsum
    _ ≤ 1280 * L + 4 * CM * L := by nlinarith
    _ = (1280 + 4 * CM) * L := by ring

/-- The bilinear shifted-window integrand is summable. -/
theorem r324SW_summable_shifted_window
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (α β : Z4) :
    Summable fun k : Z4 =>
      ‖ρ.symbol ε k‖ ^ 2 *
        ((1 + paperModeNormSq (k + α))⁻¹ *
          (1 + paperModeNormSq (k + β))⁻¹) := by
  refine (r324SW_summable_symbol_sq ρ hε hε1).of_nonneg_of_le
    (fun k => mul_nonneg (by positivity)
      (mul_nonneg (r324SW_bracket_nonneg _)
        (r324SW_bracket_nonneg _)))
    (fun k => ?_)
  calc
    ‖ρ.symbol ε k‖ ^ 2 *
        ((1 + paperModeNormSq (k + α))⁻¹ *
          (1 + paperModeNormSq (k + β))⁻¹) ≤
        ‖ρ.symbol ε k‖ ^ 2 * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_one₀ (r324SW_bracket_le_one (k + α))
        (r324SW_bracket_nonneg (k + β))
        (r324SW_bracket_le_one (k + β))
    _ = ‖ρ.symbol ε k‖ ^ 2 := mul_one _

/-- **The shifted window is logarithmic, uniformly in both shifts.**
`2xy ≤ x² + y²` splits the bilinear window into the two translated
quartic windows. -/
theorem r324SW_shifted_window_le_log (ρ : SmoothCutoff) :
    ∃ CS : ℝ, 0 < CS ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        ∀ α β : Z4,
        (∑' k : Z4,
          ‖ρ.symbol ε k‖ ^ 2 *
            ((1 + paperModeNormSq (k + α))⁻¹ *
              (1 + paperModeNormSq (k + β))⁻¹)) ≤
          CS * |Real.log ε| := by
  obtain ⟨CT, hCT, hwin⟩ := r324SW_translated_window_le_log ρ
  refine ⟨CT, hCT, ?_⟩
  intro ε hε hε1 hlog α β
  have hα := r324SW_summable_translated_window ρ hε hε1 α
  have hβ := r324SW_summable_translated_window ρ hε hε1 β
  have hsummand : ∀ k : Z4,
      ‖ρ.symbol ε k‖ ^ 2 *
        ((1 + paperModeNormSq (k + α))⁻¹ *
          (1 + paperModeNormSq (k + β))⁻¹) ≤
      (1/2) * (‖ρ.symbol ε k‖ ^ 2 *
          ((1 + paperModeNormSq (k + α))⁻¹) ^ 2) +
        (1/2) * (‖ρ.symbol ε k‖ ^ 2 *
          ((1 + paperModeNormSq (k + β))⁻¹) ^ 2) := by
    intro k
    have hx := r324SW_bracket_nonneg (k + α)
    have hy := r324SW_bracket_nonneg (k + β)
    have hs : (0:ℝ) ≤ ‖ρ.symbol ε k‖ ^ 2 := by positivity
    nlinarith [sq_nonneg ((1 + paperModeNormSq (k + α))⁻¹ -
      (1 + paperModeNormSq (k + β))⁻¹),
      mul_nonneg hs (sq_nonneg ((1 + paperModeNormSq (k + α))⁻¹ -
        (1 + paperModeNormSq (k + β))⁻¹))]
  have hmaj : Summable fun k : Z4 =>
      (1/2) * (‖ρ.symbol ε k‖ ^ 2 *
          ((1 + paperModeNormSq (k + α))⁻¹) ^ 2) +
        (1/2) * (‖ρ.symbol ε k‖ ^ 2 *
          ((1 + paperModeNormSq (k + β))⁻¹) ^ 2) :=
    (hα.mul_left _).add (hβ.mul_left _)
  calc
    (∑' k : Z4,
        ‖ρ.symbol ε k‖ ^ 2 *
          ((1 + paperModeNormSq (k + α))⁻¹ *
            (1 + paperModeNormSq (k + β))⁻¹)) ≤
        ∑' k : Z4,
          ((1/2) * (‖ρ.symbol ε k‖ ^ 2 *
              ((1 + paperModeNormSq (k + α))⁻¹) ^ 2) +
            (1/2) * (‖ρ.symbol ε k‖ ^ 2 *
              ((1 + paperModeNormSq (k + β))⁻¹) ^ 2)) :=
      (r324SW_summable_shifted_window ρ hε hε1 α β).tsum_le_tsum
        hsummand hmaj
    _ = (1/2) * (∑' k : Z4, ‖ρ.symbol ε k‖ ^ 2 *
            ((1 + paperModeNormSq (k + α))⁻¹) ^ 2) +
        (1/2) * (∑' k : Z4, ‖ρ.symbol ε k‖ ^ 2 *
            ((1 + paperModeNormSq (k + β))⁻¹) ^ 2) := by
      rw [(hα.mul_left _).tsum_add (hβ.mul_left _),
        tsum_mul_left, tsum_mul_left]
    _ ≤ (1/2) * (CT * |Real.log ε|) +
        (1/2) * (CT * |Real.log ε|) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hwin hε hε1 hlog α)
          (by norm_num))
        (mul_le_mul_of_nonneg_left (hwin hε hε1 hlog β)
          (by norm_num))
    _ = CT * |Real.log ε| := by ring

/-- Quartic-symbol variant of the translated window: immediate from
`‖ρ̂‖ ≤ 1`. -/
theorem r324SW_translated_window_quartic_le_log (ρ : SmoothCutoff) :
    ∃ CT : ℝ, 0 < CT ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        ∀ γ : Z4,
        (∑' k : Z4,
          ‖ρ.symbol ε k‖ ^ 4 *
            ((1 + paperModeNormSq (k + γ))⁻¹) ^ 2) ≤
          CT * |Real.log ε| := by
  obtain ⟨CT, hCT, hwin⟩ := r324SW_translated_window_le_log ρ
  refine ⟨CT, hCT, ?_⟩
  intro ε hε hε1 hlog γ
  have hpt : ∀ k : Z4,
      ‖ρ.symbol ε k‖ ^ 4 *
        ((1 + paperModeNormSq (k + γ))⁻¹) ^ 2 ≤
      ‖ρ.symbol ε k‖ ^ 2 *
        ((1 + paperModeNormSq (k + γ))⁻¹) ^ 2 := by
    intro k
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have h1 := ρ.norm_symbol_le_one ε k
    have h0 := norm_nonneg (ρ.symbol ε k)
    calc
      ‖ρ.symbol ε k‖ ^ 4 =
          ‖ρ.symbol ε k‖ ^ 2 * ‖ρ.symbol ε k‖ ^ 2 := by ring
      _ ≤ 1 * ‖ρ.symbol ε k‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
      _ = ‖ρ.symbol ε k‖ ^ 2 := one_mul _
  have hqsummable : Summable fun k : Z4 =>
      ‖ρ.symbol ε k‖ ^ 4 *
        ((1 + paperModeNormSq (k + γ))⁻¹) ^ 2 :=
    (r324SW_summable_translated_window ρ hε hε1 γ).of_nonneg_of_le
      (fun k => mul_nonneg (by positivity) (sq_nonneg _)) hpt
  calc
    (∑' k : Z4,
        ‖ρ.symbol ε k‖ ^ 4 *
          ((1 + paperModeNormSq (k + γ))⁻¹) ^ 2) ≤
        ∑' k : Z4,
          ‖ρ.symbol ε k‖ ^ 2 *
            ((1 + paperModeNormSq (k + γ))⁻¹) ^ 2 :=
      hqsummable.tsum_le_tsum hpt
        (r324SW_summable_translated_window ρ hε hε1 γ)
    _ ≤ CT * |Real.log ε| := hwin hε hε1 hlog γ

/-- Subtracted orientation of the shifted window, for peels that
produce `k - α` normal forms. -/
theorem r324SW_shifted_window_sub_le_log (ρ : SmoothCutoff) :
    ∃ CS : ℝ, 0 < CS ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        ∀ α β : Z4,
        (∑' k : Z4,
          ‖ρ.symbol ε k‖ ^ 2 *
            ((1 + paperModeNormSq (k - α))⁻¹ *
              (1 + paperModeNormSq (k - β))⁻¹)) ≤
          CS * |Real.log ε| := by
  obtain ⟨CS, hCS, hwin⟩ := r324SW_shifted_window_le_log ρ
  refine ⟨CS, hCS, ?_⟩
  intro ε hε hε1 hlog α β
  calc
    (∑' k : Z4,
        ‖ρ.symbol ε k‖ ^ 2 *
          ((1 + paperModeNormSq (k - α))⁻¹ *
            (1 + paperModeNormSq (k - β))⁻¹)) =
        ∑' k : Z4,
          ‖ρ.symbol ε k‖ ^ 2 *
            ((1 + paperModeNormSq (k + -α))⁻¹ *
              (1 + paperModeNormSq (k + -β))⁻¹) := by
      apply tsum_congr
      intro k
      rw [sub_eq_add_neg, sub_eq_add_neg]
    _ ≤ CS * |Real.log ε| := hwin hε hε1 hlog (-α) (-β)

/-- Quartic-symbol variant of the shifted window: immediate from
`‖ρ̂‖ ≤ 1`. -/
theorem r324SW_shifted_window_quartic_le_log (ρ : SmoothCutoff) :
    ∃ CS : ℝ, 0 < CS ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        ∀ α β : Z4,
        (∑' k : Z4,
          ‖ρ.symbol ε k‖ ^ 4 *
            ((1 + paperModeNormSq (k + α))⁻¹ *
              (1 + paperModeNormSq (k + β))⁻¹)) ≤
          CS * |Real.log ε| := by
  obtain ⟨CS, hCS, hwin⟩ := r324SW_shifted_window_le_log ρ
  refine ⟨CS, hCS, ?_⟩
  intro ε hε hε1 hlog α β
  have hpt : ∀ k : Z4,
      ‖ρ.symbol ε k‖ ^ 4 *
        ((1 + paperModeNormSq (k + α))⁻¹ *
          (1 + paperModeNormSq (k + β))⁻¹) ≤
      ‖ρ.symbol ε k‖ ^ 2 *
        ((1 + paperModeNormSq (k + α))⁻¹ *
          (1 + paperModeNormSq (k + β))⁻¹) := by
    intro k
    apply mul_le_mul_of_nonneg_right _
      (mul_nonneg (r324SW_bracket_nonneg _) (r324SW_bracket_nonneg _))
    have h1 := ρ.norm_symbol_le_one ε k
    have h0 := norm_nonneg (ρ.symbol ε k)
    calc
      ‖ρ.symbol ε k‖ ^ 4 =
          ‖ρ.symbol ε k‖ ^ 2 * ‖ρ.symbol ε k‖ ^ 2 := by ring
      _ ≤ 1 * ‖ρ.symbol ε k‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
      _ = ‖ρ.symbol ε k‖ ^ 2 := one_mul _
  have hqsummable : Summable fun k : Z4 =>
      ‖ρ.symbol ε k‖ ^ 4 *
        ((1 + paperModeNormSq (k + α))⁻¹ *
          (1 + paperModeNormSq (k + β))⁻¹) :=
    (r324SW_summable_shifted_window ρ hε hε1 α β).of_nonneg_of_le
      (fun k => mul_nonneg (by positivity)
        (mul_nonneg (r324SW_bracket_nonneg _)
          (r324SW_bracket_nonneg _)))
      hpt
  calc
    (∑' k : Z4,
        ‖ρ.symbol ε k‖ ^ 4 *
          ((1 + paperModeNormSq (k + α))⁻¹ *
            (1 + paperModeNormSq (k + β))⁻¹)) ≤
        ∑' k : Z4,
          ‖ρ.symbol ε k‖ ^ 2 *
            ((1 + paperModeNormSq (k + α))⁻¹ *
              (1 + paperModeNormSq (k + β))⁻¹) :=
      hqsummable.tsum_le_tsum hpt
        (r324SW_summable_shifted_window ρ hε hε1 α β)
    _ ≤ CS * |Real.log ε| := hwin hε hε1 hlog α β

/-- **Bracket separation.**  The product of two shifted quartic
brackets retains the separation of the shifts: with
`a = ⟨k+α⟩²`, `b = ⟨k+β⟩²`, `d = ⟨α-β⟩²` one has
`a⁻²b⁻² ≤ 16 d⁻² (a⁻² + b⁻²)`, because `d ≤ 2a + 2b ≤ 4·max`. -/
theorem r324SW_bracket_separation (α β k : Z4) :
    ((1 + paperModeNormSq (k + α))⁻¹) ^ 2 *
      ((1 + paperModeNormSq (k + β))⁻¹) ^ 2 ≤
    16 * ((1 + paperModeNormSq (α - β))⁻¹) ^ 2 *
      (((1 + paperModeNormSq (k + α))⁻¹) ^ 2 +
        ((1 + paperModeNormSq (k + β))⁻¹) ^ 2) := by
  set a : ℝ := 1 + paperModeNormSq (k + α) with hadef
  set b : ℝ := 1 + paperModeNormSq (k + β) with hbdef
  set d : ℝ := 1 + paperModeNormSq (α - β) with hddef
  have ha1 : 1 ≤ a := by
    rw [hadef]
    linarith [paperModeNormSq_nonneg (k + α)]
  have hb1 : 1 ≤ b := by
    rw [hbdef]
    linarith [paperModeNormSq_nonneg (k + β)]
  have hd1 : 1 ≤ d := by
    rw [hddef]
    linarith [paperModeNormSq_nonneg (α - β)]
  have hP : paperModeNormSq (α - β) ≤
      2 * paperModeNormSq (k + α) + 2 * paperModeNormSq (k + β) := by
    unfold paperModeNormSq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hcoord : (((α - β) i : ℤ) : ℝ) =
        (((k + α) i : ℤ) : ℝ) - (((k + β) i : ℤ) : ℝ) := by
      simp only [Pi.sub_apply, Pi.add_apply]
      push_cast
      ring
    rw [hcoord]
    nlinarith [sq_nonneg ((((k + α) i : ℤ) : ℝ) +
      (((k + β) i : ℤ) : ℝ))]
  have hd : d ≤ 2 * a + 2 * b := by
    rw [hddef, hadef, hbdef]
    linarith
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le one_pos ha1
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le one_pos hb1
  have hd0 : (0:ℝ) < d := lt_of_lt_of_le one_pos hd1
  have key : ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → d ≤ 4 * y →
      (x⁻¹) ^ 2 * (y⁻¹) ^ 2 ≤
        16 * (d⁻¹) ^ 2 * ((x⁻¹) ^ 2 + (y⁻¹) ^ 2) := by
    intro x y hx1 hy1 hdy
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy1
    have hyinv : y⁻¹ ≤ 4 * d⁻¹ := by
      have h1 : d / 4 ≤ y := by linarith
      have h2 : y⁻¹ ≤ (d / 4)⁻¹ := inv_anti₀ (by linarith) h1
      have h3 : (d / 4)⁻¹ = 4 * d⁻¹ := by
        rw [inv_div, div_eq_mul_inv]
      rwa [h3] at h2
    have hysq : (y⁻¹) ^ 2 ≤ 16 * (d⁻¹) ^ 2 := by
      calc
        (y⁻¹) ^ 2 ≤ (4 * d⁻¹) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hyinv 2
        _ = 16 * (d⁻¹) ^ 2 := by ring
    calc
      (x⁻¹) ^ 2 * (y⁻¹) ^ 2 ≤
          (x⁻¹) ^ 2 * (16 * (d⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_left hysq (sq_nonneg _)
      _ = 16 * (d⁻¹) ^ 2 * (x⁻¹) ^ 2 := by ring
      _ ≤ 16 * (d⁻¹) ^ 2 * ((x⁻¹) ^ 2 + (y⁻¹) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (by norm_num) (sq_nonneg _))
        exact le_add_of_nonneg_right (sq_nonneg _)
  rcases le_total a b with hab | hab
  · exact key a b ha1 hb1 (by linarith)
  · have h := key b a hb1 ha1 (by linarith)
    calc
      (a⁻¹) ^ 2 * (b⁻¹) ^ 2 = (b⁻¹) ^ 2 * (a⁻¹) ^ 2 := by ring
      _ ≤ 16 * (d⁻¹) ^ 2 * ((b⁻¹) ^ 2 + (a⁻¹) ^ 2) := h
      _ = 16 * (d⁻¹) ^ 2 * ((a⁻¹) ^ 2 + (b⁻¹) ^ 2) := by ring

/-- **Decay-retaining shifted window.**  When both quartic brackets
are present, the window keeps the separation of the two centers:
`Σ_k ‖ρ̂(εk)‖²⟨k+α⟩⁻⁴⟨k+β⟩⁻⁴ ≤ C(ρ)·⟨α-β⟩⁻⁴·|log ε|`, in the sharp
multiplicative form. -/
theorem r324SW_separated_window_le_log (ρ : SmoothCutoff) :
    ∃ CD : ℝ, 0 < CD ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        ∀ α β : Z4,
        (∑' k : Z4,
          ‖ρ.symbol ε k‖ ^ 2 *
            (((1 + paperModeNormSq (k + α))⁻¹) ^ 2 *
              ((1 + paperModeNormSq (k + β))⁻¹) ^ 2)) ≤
          CD * ((1 + paperModeNormSq (α - β))⁻¹) ^ 2 *
            |Real.log ε| := by
  obtain ⟨CT, hCT, hwin⟩ := r324SW_translated_window_le_log ρ
  refine ⟨32 * CT, by positivity, ?_⟩
  intro ε hε hε1 hlog α β
  have hα := r324SW_summable_translated_window ρ hε hε1 α
  have hβ := r324SW_summable_translated_window ρ hε hε1 β
  have hD0 : (0:ℝ) ≤ ((1 + paperModeNormSq (α - β))⁻¹) ^ 2 :=
    sq_nonneg _
  have hpt : ∀ k : Z4,
      ‖ρ.symbol ε k‖ ^ 2 *
        (((1 + paperModeNormSq (k + α))⁻¹) ^ 2 *
          ((1 + paperModeNormSq (k + β))⁻¹) ^ 2) ≤
      (16 * ((1 + paperModeNormSq (α - β))⁻¹) ^ 2) *
        (‖ρ.symbol ε k‖ ^ 2 *
            ((1 + paperModeNormSq (k + α))⁻¹) ^ 2 +
          ‖ρ.symbol ε k‖ ^ 2 *
            ((1 + paperModeNormSq (k + β))⁻¹) ^ 2) := by
    intro k
    calc
      ‖ρ.symbol ε k‖ ^ 2 *
          (((1 + paperModeNormSq (k + α))⁻¹) ^ 2 *
            ((1 + paperModeNormSq (k + β))⁻¹) ^ 2) ≤
          ‖ρ.symbol ε k‖ ^ 2 *
            (16 * ((1 + paperModeNormSq (α - β))⁻¹) ^ 2 *
              (((1 + paperModeNormSq (k + α))⁻¹) ^ 2 +
                ((1 + paperModeNormSq (k + β))⁻¹) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (r324SW_bracket_separation α β k) (by positivity)
      _ = (16 * ((1 + paperModeNormSq (α - β))⁻¹) ^ 2) *
          (‖ρ.symbol ε k‖ ^ 2 *
              ((1 + paperModeNormSq (k + α))⁻¹) ^ 2 +
            ‖ρ.symbol ε k‖ ^ 2 *
              ((1 + paperModeNormSq (k + β))⁻¹) ^ 2) := by
        ring
  have hlhs : Summable fun k : Z4 =>
      ‖ρ.symbol ε k‖ ^ 2 *
        (((1 + paperModeNormSq (k + α))⁻¹) ^ 2 *
          ((1 + paperModeNormSq (k + β))⁻¹) ^ 2) := by
    refine hα.of_nonneg_of_le
      (fun k => mul_nonneg (by positivity)
        (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      (fun k => ?_)
    calc
      ‖ρ.symbol ε k‖ ^ 2 *
          (((1 + paperModeNormSq (k + α))⁻¹) ^ 2 *
            ((1 + paperModeNormSq (k + β))⁻¹) ^ 2) =
          (‖ρ.symbol ε k‖ ^ 2 *
              ((1 + paperModeNormSq (k + α))⁻¹) ^ 2) *
            ((1 + paperModeNormSq (k + β))⁻¹) ^ 2 := by
        ring
      _ ≤ (‖ρ.symbol ε k‖ ^ 2 *
            ((1 + paperModeNormSq (k + α))⁻¹) ^ 2) * 1 := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (by positivity) (sq_nonneg _))
        exact pow_le_one₀ (r324SW_bracket_nonneg (k + β))
          (r324SW_bracket_le_one (k + β))
      _ = ‖ρ.symbol ε k‖ ^ 2 *
            ((1 + paperModeNormSq (k + α))⁻¹) ^ 2 := mul_one _
  calc
    (∑' k : Z4,
        ‖ρ.symbol ε k‖ ^ 2 *
          (((1 + paperModeNormSq (k + α))⁻¹) ^ 2 *
            ((1 + paperModeNormSq (k + β))⁻¹) ^ 2)) ≤
        ∑' k : Z4,
          (16 * ((1 + paperModeNormSq (α - β))⁻¹) ^ 2) *
            (‖ρ.symbol ε k‖ ^ 2 *
                ((1 + paperModeNormSq (k + α))⁻¹) ^ 2 +
              ‖ρ.symbol ε k‖ ^ 2 *
                ((1 + paperModeNormSq (k + β))⁻¹) ^ 2) :=
      hlhs.tsum_le_tsum hpt ((hα.add hβ).mul_left _)
    _ = (16 * ((1 + paperModeNormSq (α - β))⁻¹) ^ 2) *
        ((∑' k : Z4, ‖ρ.symbol ε k‖ ^ 2 *
            ((1 + paperModeNormSq (k + α))⁻¹) ^ 2) +
          ∑' k : Z4, ‖ρ.symbol ε k‖ ^ 2 *
            ((1 + paperModeNormSq (k + β))⁻¹) ^ 2) := by
      rw [tsum_mul_left, hα.tsum_add hβ]
    _ ≤ (16 * ((1 + paperModeNormSq (α - β))⁻¹) ^ 2) *
        (CT * |Real.log ε| + CT * |Real.log ε|) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (hwin hε hε1 hlog α) (hwin hε hε1 hlog β))
        (mul_nonneg (by norm_num) hD0)
    _ = 32 * CT * ((1 + paperModeNormSq (α - β))⁻¹) ^ 2 *
        |Real.log ε| := by
      ring

end

end Anderson4D
