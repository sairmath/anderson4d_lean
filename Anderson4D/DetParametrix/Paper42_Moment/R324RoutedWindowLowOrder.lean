import Anderson4D.DetParametrix.Paper42_Moment.R324ShiftedWindow

/-!
# The routed window values at low order

**(D) The unconditional window side.**  The routed ledgers of
`R324RoutedWindowBudget` measure each covariance pair against a lattice
window.  This file closes the *value* side of those ledgers at the
orders the paper needs first:

* `r324RoutedWindow_marked_window_le` — the **marked-slot window**: one
  degree-eight routing cost `(1+‖k‖²)⁴`, damped by the single retained
  diagonal Green window `⟨k⟩⁻⁴`, costs exactly the endpoint sacrifice:
  `Σ_k (1+‖k‖²)⁴·⟨k⟩⁻⁴·‖ρ̂(εk)‖² ≤ C·ε⁻⁸`.  This is the factor the
  scalar raw ledger provably lost (`ε⁻¹²` without the window), and it
  is the per-marked-pair factor of the windowed value at *every* `m`;
* `r324RoutedWindow_value_one` / `r324RoutedWindow_value_two` — the
  `m ≤ 2` windowed values in the exact `C^m·L^{m-1}·ε⁻⁸` normal form of
  the routed Props: at `m = 1` the marked window alone (no logarithm);
  at `m = 2` the marked window times the decay-retaining separated
  window `r324SW_separated_window_le_log`, which slots into the cross
  pair and keeps the `⟨γ-δ⟩⁻⁴` separation of the two window centers.

The tail of the marked window needs symbol decay strictly beyond the
proved degree-eight bound, so we first derive the degree-twelve
scaled bound from the arbitrary-order rapid decay
`exists_fourierR4_one_add_norm_bound_nat 6`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- Degree-six decay of the scaled symbol against the sup bracket,
squared: the degree-twelve companion of
`r324SW_symbol_sq_le_of_decay_eight`, needed because the marked slot
retains a net fourth-order growth. -/
theorem r324RoutedWindow_symbol_sq_le_of_decay_six
    (ρ : SmoothCutoff) {C0 : ℝ}
    (hdecay : ∀ ξ : R4,
      (1 + ‖SmoothCutoff.euclideanFrequency ξ‖) ^ 6 *
        ‖fourierR4 ρ ξ‖ ≤ C0)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (k : Z4) :
    ‖ρ.symbol ε k‖ ^ 2 ≤
      (C0 ^ 2 * (2 * Real.pi) ^ 12) *
        (ε⁻¹ ^ 12 * (((1 + (z4SupRadius k : ℝ)) ^ 12)⁻¹)) := by
  set ξ : R4 := fun i => ε * (k i : ℝ) with hξdef
  set w := SmoothCutoff.euclideanFrequency ξ with hwdef
  set s : ℝ := (z4SupRadius k : ℝ) with hsdef
  have hs : 0 ≤ s := Nat.cast_nonneg _
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have hC0 : 0 ≤ C0 := by
    have h := hdecay 0
    have h1 : (0:ℝ) ≤
        (1 + ‖SmoothCutoff.euclideanFrequency (0 : R4)‖) ^ 6 *
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
  have hsymle : ‖ρ.symbol ε k‖ ≤ C0 * ((1 + ‖w‖) ^ 6)⁻¹ := by
    have h6 := hdecay ξ
    rw [← hwdef, ← hsym] at h6
    rw [mul_comm, ← le_div_iff₀
      (by positivity : (0:ℝ) < (1 + ‖w‖) ^ 6), div_eq_mul_inv]
      at h6
    exact h6
  have hbr6 :
      ((1 + ‖w‖) ^ 6)⁻¹ ≤
        ((2 * Real.pi) ^ 6 * ε⁻¹ ^ 6) * ((1 + s) ^ 6)⁻¹ := by
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
        ((1 + ‖w‖)⁻¹) ^ 6 ≤
          ((2 * Real.pi) * ε⁻¹ * (1 + s)⁻¹) ^ 6 := by
      rw [← hval]
      exact pow_le_pow_left₀ (by positivity) hinv 6
    calc
      ((1 + ‖w‖) ^ 6)⁻¹ = ((1 + ‖w‖)⁻¹) ^ 6 := by rw [inv_pow]
      _ ≤ ((2 * Real.pi) * ε⁻¹ * (1 + s)⁻¹) ^ 6 := hq
      _ = ((2 * Real.pi) ^ 6 * ε⁻¹ ^ 6) * ((1 + s) ^ 6)⁻¹ := by
        have h1s : (1 + s) ≠ 0 := by positivity
        field_simp
  calc
    ‖ρ.symbol ε k‖ ^ 2 ≤
        (C0 * (((2 * Real.pi) ^ 6 * ε⁻¹ ^ 6) *
          ((1 + s) ^ 6)⁻¹)) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      calc
        ‖ρ.symbol ε k‖ ≤ C0 * ((1 + ‖w‖) ^ 6)⁻¹ := hsymle
        _ ≤ C0 * (((2 * Real.pi) ^ 6 * ε⁻¹ ^ 6) *
              ((1 + s) ^ 6)⁻¹) :=
          mul_le_mul_of_nonneg_left hbr6 hC0
    _ = (C0 ^ 2 * (2 * Real.pi) ^ 12) *
          (ε⁻¹ ^ 12 * (((1 + s) ^ 12)⁻¹)) := by
      have h1s : (1 + s) ≠ 0 := by positivity
      field_simp

/-- The Euclidean mode square is at most `dim` sup-radius squares. -/
theorem r324RoutedWindow_paperModeNormSq_le (k : Z4) :
    paperModeNormSq k ≤ 4 * (z4SupRadius k : ℝ) ^ 2 := by
  unfold paperModeNormSq
  have hcoord : ∀ i : Fin dim,
      (k i : ℝ) ^ 2 ≤ (z4SupRadius k : ℝ) ^ 2 := by
    intro i
    have habs : ((k i).natAbs : ℝ) ≤ (z4SupRadius k : ℝ) := by
      exact_mod_cast Finset.le_sup
        (f := fun j => (k j).natAbs) (Finset.mem_univ i)
    have hsq : (k i : ℝ) ^ 2 = ((k i).natAbs : ℝ) ^ 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [hsq]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) habs 2
  calc
    (∑ i, (k i : ℝ) ^ 2) ≤
        ∑ _i : Fin dim, (z4SupRadius k : ℝ) ^ 2 :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ = 4 * (z4SupRadius k : ℝ) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      norm_num [dim]

/-- **The marked-slot window.**  One degree-eight routing cost, damped
by the retained diagonal Green window, costs exactly the endpoint
sacrifice `ε⁻⁸` — not the raw `ε⁻¹²` of the windowless ledger:
`Σ_k (1+‖k‖²)⁴ ⟨k⟩⁻⁴ ‖ρ̂(εk)‖² ≤ CM·ε⁻⁸`. -/
theorem r324RoutedWindow_marked_window_le (ρ : SmoothCutoff) :
    ∃ CM : ℝ, 0 < CM ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        (∑' k : Z4,
          (1 + ‖z4EuclideanFrequency k‖ ^ 2) ^ 4 *
            paperFourthOrderModeDecay k *
            ‖ρ.symbol ε k‖ ^ 2) ≤ CM * ε⁻¹ ^ (8 : ℕ) := by
  obtain ⟨C6, hC6, hdecay⟩ :=
    ρ.exists_fourierR4_one_add_norm_bound_nat 6
  set B : ℝ := C6 ^ 2 * (2 * Real.pi) ^ 12 with hBdef
  have hB : 0 < B := by rw [hBdef]; positivity
  refine ⟨374544 + 320 * B, by positivity, ?_⟩
  intro ε hε hε1
  have hsummand : ∀ k : Z4,
      (1 + ‖z4EuclideanFrequency k‖ ^ 2) ^ 4 *
          paperFourthOrderModeDecay k * ‖ρ.symbol ε k‖ ^ 2 =
        (1 + paperModeNormSq k) ^ 2 * ‖ρ.symbol ε k‖ ^ 2 := by
    intro k
    have hP0 : 0 ≤ paperModeNormSq k := paperModeNormSq_nonneg k
    rw [norm_sq_z4EuclideanFrequency]
    unfold paperFourthOrderModeDecay
    congr 1
    have h1P : (0:ℝ) < 1 + paperModeNormSq k := by positivity
    field_simp
  set N : ℕ := ⌈ε⁻¹⌉₊ with hNdef
  have hεinv1 : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
  have hNε : ε⁻¹ ≤ (N : ℝ) := Nat.le_ceil _
  have hNup : (N : ℝ) + 1 ≤ 3 * ε⁻¹ := by
    have hceil : (N : ℝ) < ε⁻¹ + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith
  set f : Z4 → ℝ := fun k =>
    (1 + paperModeNormSq k) ^ 2 * ‖ρ.symbol ε k‖ ^ 2 with hfdef
  set g : Z4 → ℝ := fun k =>
    if k ∈ z4Cube N then (1 + 4 * (N : ℝ) ^ 2) ^ 2 else 0
    with hgdef
  set h : Z4 → ℝ := fun k =>
    (16 * B * ε⁻¹ ^ 12) * z4EighthRadialTail (N + 1) k with hhdef
  have hg0 : ∀ k, 0 ≤ g k := by
    intro k
    simp only [hgdef]
    by_cases hk : k ∈ z4Cube N
    · rw [if_pos hk]; positivity
    · rw [if_neg hk]
  have hh0 : ∀ k, 0 ≤ h k := fun k =>
    mul_nonneg (by positivity) (z4EighthRadialTail_nonneg _ _)
  have hN2ε : (N : ℝ) ≤ 2 * ε⁻¹ := by
    have hceil : (N : ℝ) < ε⁻¹ + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith
  have hfg : ∀ k, f k ≤ g k + h k := by
    intro k
    set s : ℝ := (z4SupRadius k : ℝ) with hsdef
    have hs : 0 ≤ s := Nat.cast_nonneg _
    have hPle := r324RoutedWindow_paperModeNormSq_le k
    rw [← hsdef] at hPle
    by_cases hk : k ∈ z4Cube N
    · refine le_trans ?_ (le_add_of_nonneg_right (hh0 k))
      simp only [hfdef, hgdef]
      rw [if_pos hk]
      have hsN : s ≤ (N : ℝ) := by
        rw [mem_z4Cube_iff_z4SupRadius_le] at hk
        rw [hsdef]
        exact_mod_cast hk
      have hsymb1 : ‖ρ.symbol ε k‖ ^ 2 ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) (ρ.norm_symbol_le_one ε k)
      have hs2 : s ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hs hsN 2
      have hbra : (1 + paperModeNormSq k) ^ 2 ≤
          (1 + 4 * (N : ℝ) ^ 2) ^ 2 := by
        have h1P : (0:ℝ) ≤ 1 + paperModeNormSq k := by
          linarith [paperModeNormSq_nonneg k]
        exact pow_le_pow_left₀ h1P (by linarith) 2
      calc
        (1 + paperModeNormSq k) ^ 2 * ‖ρ.symbol ε k‖ ^ 2 ≤
            (1 + paperModeNormSq k) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hsymb1 (by positivity)
        _ = (1 + paperModeNormSq k) ^ 2 := mul_one _
        _ ≤ (1 + 4 * (N : ℝ) ^ 2) ^ 2 := hbra
    · refine le_trans ?_ (le_add_of_nonneg_left (hg0 k))
      have hrad : N + 1 ≤ z4SupRadius k := by
        rw [mem_z4Cube_iff_z4SupRadius_le] at hk
        omega
      simp only [hfdef, hhdef]
      have htail : z4EighthRadialTail (N + 1) k =
          ((1 + s) ^ 8)⁻¹ := by
        unfold z4EighthRadialTail
        rw [if_pos hrad, l2LatticeRadialWeight_eq_z4SupRadius,
          ← hsdef]
      have hsq :=
        r324RoutedWindow_symbol_sq_le_of_decay_six ρ hdecay hε hε1 k
      rw [← hBdef, ← hsdef] at hsq
      have hbra : (1 + paperModeNormSq k) ^ 2 ≤
          16 * (1 + s) ^ 4 := by
        have hP2 : 1 + paperModeNormSq k ≤ (1 + 2 * s) ^ 2 := by
          nlinarith
        have h1P : (0:ℝ) ≤ 1 + paperModeNormSq k := by
          linarith [paperModeNormSq_nonneg k]
        calc
          (1 + paperModeNormSq k) ^ 2 ≤ ((1 + 2 * s) ^ 2) ^ 2 :=
            pow_le_pow_left₀ h1P hP2 2
          _ ≤ ((2 * (1 + s)) ^ 2) ^ 2 := by
            have hstep : (1 + 2 * s) ^ 2 ≤ (2 * (1 + s)) ^ 2 :=
              pow_le_pow_left₀ (by linarith) (by linarith) 2
            exact pow_le_pow_left₀ (sq_nonneg _) hstep 2
          _ = 16 * (1 + s) ^ 4 := by ring
      rw [htail]
      calc
        (1 + paperModeNormSq k) ^ 2 * ‖ρ.symbol ε k‖ ^ 2 ≤
            (16 * (1 + s) ^ 4) *
              (B * (ε⁻¹ ^ 12 * (((1 + s) ^ 12)⁻¹))) :=
          mul_le_mul hbra hsq (by positivity)
            (by positivity)
        _ = (16 * B * ε⁻¹ ^ 12) *
              ((1 + s) ^ 4 * ((1 + s) ^ 12)⁻¹) := by ring
        _ = (16 * B * ε⁻¹ ^ 12) * ((1 + s) ^ 8)⁻¹ := by
          congr 1
          have h1s : (1 + s) ≠ 0 := by positivity
          field_simp
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
  have hgsum : (∑' k, g k) ≤ 374544 * ε⁻¹ ^ 8 := by
    have hgeq : (∑' k, g k) =
        ∑ k ∈ z4Cube N, (1 + 4 * (N : ℝ) ^ 2) ^ 2 := by
      rw [tsum_eq_sum (s := z4Cube N) ?_]
      · exact Finset.sum_congr rfl fun k hk => by
          simp only [hgdef]; exact if_pos hk
      · intro k hk
        simp only [hgdef]
        exact if_neg hk
    rw [hgeq, Finset.sum_const, card_z4Cube, nsmul_eq_mul]
    have hcount : (((2 * N + 1) ^ 4 : ℕ) : ℝ) ≤ 1296 * ε⁻¹ ^ 4 := by
      have hside : ((2 * N + 1 : ℕ) : ℝ) ≤ 6 * ε⁻¹ := by
        push_cast
        linarith
      calc
        (((2 * N + 1) ^ 4 : ℕ) : ℝ) =
            ((2 * N + 1 : ℕ) : ℝ) ^ 4 := by push_cast; ring
        _ ≤ (6 * ε⁻¹) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hside 4
        _ = 1296 * ε⁻¹ ^ 4 := by ring
    have hbra2 : (1 + 4 * (N : ℝ) ^ 2) ^ 2 ≤ 289 * ε⁻¹ ^ 4 := by
      have hNsq : (N : ℝ) ^ 2 ≤ (2 * ε⁻¹) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hN2ε 2
      have h17 : 1 + 4 * (N : ℝ) ^ 2 ≤ 17 * ε⁻¹ ^ 2 := by
        nlinarith [hεinv1]
      calc
        (1 + 4 * (N : ℝ) ^ 2) ^ 2 ≤ (17 * ε⁻¹ ^ 2) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h17 2
        _ = 289 * ε⁻¹ ^ 4 := by ring
    calc
      (((2 * N + 1) ^ 4 : ℕ) : ℝ) * (1 + 4 * (N : ℝ) ^ 2) ^ 2 ≤
          (1296 * ε⁻¹ ^ 4) * (289 * ε⁻¹ ^ 4) :=
        mul_le_mul hcount hbra2 (by positivity) (by positivity)
      _ = 374544 * ε⁻¹ ^ 8 := by ring
  have hhsum : (∑' k, h k) ≤ 320 * B * ε⁻¹ ^ 8 := by
    have htail := tsum_z4EighthRadialTail_le (N + 1) (Nat.succ_pos N)
    have hεN : ((N : ℝ) + 1)⁻¹ ≤ ε := by
      have hstep : ε⁻¹ ≤ (N : ℝ) + 1 := by linarith
      calc
        ((N : ℝ) + 1)⁻¹ ≤ (ε⁻¹)⁻¹ := inv_anti₀ (by positivity) hstep
        _ = ε := inv_inv ε
    simp only [hhdef]
    rw [tsum_mul_left]
    calc
      (16 * B * ε⁻¹ ^ 12) *
          ∑' k, z4EighthRadialTail (N + 1) k ≤
          (16 * B * ε⁻¹ ^ 12) *
            (20 * (((N + 1 : ℕ) : ℝ)⁻¹) ^ 4) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ (16 * B * ε⁻¹ ^ 12) * (20 * ε ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by
          push_cast
          ring
        have h4 : (((N + 1 : ℕ) : ℝ)⁻¹) ^ 4 ≤ ε ^ 4 := by
          rw [hcast]
          exact pow_le_pow_left₀ (by positivity) hεN 4
        linarith
      _ = (320 * B * ε⁻¹ ^ 8) * (ε⁻¹ ^ 4 * ε ^ 4) := by ring
      _ = 320 * B * ε⁻¹ ^ 8 := by
        rw [← mul_pow, inv_mul_cancel₀ hε.ne', one_pow, mul_one]
  calc
    (∑' k : Z4,
        (1 + ‖z4EuclideanFrequency k‖ ^ 2) ^ 4 *
          paperFourthOrderModeDecay k * ‖ρ.symbol ε k‖ ^ 2) =
        ∑' k, f k :=
      tsum_congr fun k => by simp only [hfdef]; exact hsummand k
    _ ≤ ∑' k, (g k + h k) :=
      hfsummable.tsum_le_tsum hfg (hgsummable.add hhsummable)
    _ = (∑' k, g k) + ∑' k, h k :=
      hgsummable.tsum_add hhsummable
    _ ≤ 374544 * ε⁻¹ ^ 8 + 320 * B * ε⁻¹ ^ 8 :=
      add_le_add hgsum hhsum
    _ = (374544 + 320 * B) * ε⁻¹ ^ 8 := by ring

/-- **The order-one routed window value**, in the exact
`C^m·L^{m-1}·ε⁻⁸` normal form of the routed Props: at `m = 1` the
marked window alone funds the budget and no logarithm is spent. -/
theorem r324RoutedWindow_value_one (ρ : SmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        (∑' k : Z4,
          (1 + ‖z4EuclideanFrequency k‖ ^ 2) ^ 4 *
            paperFourthOrderModeDecay k *
            ‖ρ.symbol ε k‖ ^ 2) ≤
        C ^ 1 * |Real.log ε| ^ (1 - 1) * ε⁻¹ ^ (8 : ℕ) := by
  obtain ⟨CM, hCM, hmarked⟩ := r324RoutedWindow_marked_window_le ρ
  refine ⟨CM, hCM, ?_⟩
  intro ε hε hε1 _hlog
  simpa using hmarked hε hε1

/-- **The order-two routed window value.**  The marked pair pays the
endpoint sacrifice `ε⁻⁸`; the second (cross) pair is evaluated by the
decay-retaining separated window, worth one logarithm and keeping the
`⟨γ-δ⟩⁻⁴` separation of its two centers: the windowed pair-pattern
value is `C²·L^{2-1}·ε⁻⁸` with the separation retained as a bonus. -/
theorem r324RoutedWindow_value_two (ρ : SmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        ∀ γ δ : Z4,
        (∑' k : Z4,
            (1 + ‖z4EuclideanFrequency k‖ ^ 2) ^ 4 *
              paperFourthOrderModeDecay k *
              ‖ρ.symbol ε k‖ ^ 2) *
          (∑' k : Z4,
            ‖ρ.symbol ε k‖ ^ 2 *
              (((1 + paperModeNormSq (k + γ))⁻¹) ^ 2 *
                ((1 + paperModeNormSq (k + δ))⁻¹) ^ 2)) ≤
        (C ^ 2 * |Real.log ε| ^ (2 - 1) * ε⁻¹ ^ (8 : ℕ)) *
          ((1 + paperModeNormSq (γ - δ))⁻¹) ^ 2 := by
  obtain ⟨CM, hCM, hmarked⟩ := r324RoutedWindow_marked_window_le ρ
  obtain ⟨CD, hCD, hsep⟩ := r324SW_separated_window_le_log ρ
  refine ⟨CM + CD, by positivity, ?_⟩
  intro ε hε hε1 hlog γ δ
  have h1 := hmarked hε hε1
  have h2 := hsep hε hε1 hlog γ δ
  have hS2 : 0 ≤
      ∑' k : Z4,
        ‖ρ.symbol ε k‖ ^ 2 *
          (((1 + paperModeNormSq (k + γ))⁻¹) ^ 2 *
            ((1 + paperModeNormSq (k + δ))⁻¹) ^ 2) :=
    tsum_nonneg fun k =>
      mul_nonneg (by positivity)
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hprod :=
    mul_le_mul h1 h2 hS2 (by positivity)
  refine hprod.trans ?_
  have hCMCD : CM * CD ≤ (CM + CD) ^ 2 := by nlinarith
  calc
    (CM * ε⁻¹ ^ (8 : ℕ)) *
        (CD * ((1 + paperModeNormSq (γ - δ))⁻¹) ^ 2 *
          |Real.log ε|) =
        (CM * CD) *
          (|Real.log ε| * ε⁻¹ ^ (8 : ℕ) *
            ((1 + paperModeNormSq (γ - δ))⁻¹) ^ 2) := by
      ring
    _ ≤ ((CM + CD) ^ 2) *
          (|Real.log ε| * ε⁻¹ ^ (8 : ℕ) *
            ((1 + paperModeNormSq (γ - δ))⁻¹) ^ 2) :=
      mul_le_mul_of_nonneg_right hCMCD (by positivity)
    _ = ((CM + CD) ^ 2 * |Real.log ε| ^ (2 - 1) *
          ε⁻¹ ^ (8 : ℕ)) *
          ((1 + paperModeNormSq (γ - δ))⁻¹) ^ 2 := by
      rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one]
      ring

end

end Anderson4D
