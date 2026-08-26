import Anderson4D.PermSum.Local

/-!
# Refined bilinear lattice-cluster bound (Lemma 5.14 of arXiv:2607.10105, eq. (5.58))

Paper: L-5.14 — (5.58) — the refined bilinear lattice bound

This file completes the PAPER_MAP node **L-5.14**: the bilinear cluster bound (5.58)
*with* the refining factor `min (1, (Q/P)^{1/4})`, `P = |A|·M⁴`, `Q = |B|·N⁴`.

Contents:
* `single_y_bound` — the pointwise (in `y`) estimate, paper **(5.63)/(5.64)**;
* `bilinear_cluster_S_bound` — the `Q ≤ P` (`S`-)bound
  `∑∑ ≲ |A|^{1/4} M⁻³ |B|^{3/4} N⁻¹`, paper **(5.65)–(5.67)**;
* `bilinear_cluster_bound` — the fully refined **(5.58)**, combining the `S`-bound with
  `bilinear_cluster_bound_weak` from `Anderson4D.PermSum.Local`.

Quarter powers are `Real.rpow` (`· ^ (1/4 : ℝ)`); indicator constraints are
`Finset.filter`; constants are explicit in private lemmas and existential in the two
public theorems.  The dyadic engine of `Local.lean` is private there, so the small
parametric geometric-sum lemmas are (re)proved here in ratio-generic form.
-/

open scoped BigOperators
open Finset

namespace Anderson4D

/-- Triangle inequality for `znorm`. -/
private lemma znorm_add_le (a b : Fin 4 → ℤ) : znorm (a + b) ≤ znorm a + znorm b := by
  unfold znorm
  have h : (fun i => (((a + b) i) : ℝ))
      = (fun i => ((a i) : ℝ)) + (fun i => ((b i) : ℝ)) := by
    funext i; simp
  rw [h]
  exact norm_add_le _ _

/-- Three-point triangle inequality in the form used below. -/
private lemma znorm_triangle (u x y : Fin 4 → ℤ) :
    znorm (u - y) ≤ znorm (u - x) + znorm (x - y) := by
  have h : u - y = (u - x) + (x - y) := by abel
  rw [h]
  exact znorm_add_le _ _

/-- Parametric increasing geometric sum: for ratio `r > 1`, a sum of `c·r^j` over indices
`≤ m` is at most `c·r^m·(r/(r-1))`. -/
private lemma geom_incr_le (r c : ℝ) (hr : 1 < r) (hc : 0 ≤ c) (J : Finset ℕ) (m : ℕ)
    (hm : ∀ j ∈ J, j ≤ m) : ∑ j ∈ J, c * r ^ j ≤ c * r ^ m * (r / (r - 1)) := by
  have hr0 : (0 : ℝ) < r := lt_trans one_pos hr
  have hr1 : (0 : ℝ) < r - 1 := by linarith
  have hsub : J ⊆ Finset.range (m + 1) := fun j hj =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hm j hj))
  have hstep : (r ^ (m + 1) - 1) / (r - 1) ≤ r ^ m * (r / (r - 1)) := by
    rw [div_le_iff₀ hr1]
    have h₁ : r / (r - 1) * (r - 1) = r := div_mul_cancel₀ r (ne_of_gt hr1)
    have h₂ : r ^ m * (r / (r - 1)) * (r - 1) = r ^ (m + 1) := by
      calc r ^ m * (r / (r - 1)) * (r - 1) = r ^ m * (r / (r - 1) * (r - 1)) := by ring
        _ = r ^ m * r := by rw [h₁]
        _ = r ^ (m + 1) := (pow_succ r m).symm
    rw [h₂]
    linarith
  calc ∑ j ∈ J, c * r ^ j
      ≤ ∑ j ∈ Finset.range (m + 1), c * r ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => mul_nonneg hc (by positivity))
    _ = c * ∑ j ∈ Finset.range (m + 1), r ^ j := by rw [Finset.mul_sum]
    _ = c * ((r ^ (m + 1) - 1) / (r - 1)) := by rw [geom_sum_eq (ne_of_gt hr)]
    _ ≤ c * (r ^ m * (r / (r - 1))) := mul_le_mul_of_nonneg_left hstep hc
    _ = c * r ^ m * (r / (r - 1)) := by ring

/-- Parametric decreasing geometric sum: for ratio `r > 1`, a sum of `c·r^{-j}` over
indices `≥ m` (all `< n`) is at most `c·r^{-m}·(r/(r-1))`. -/
private lemma geom_decr_le (r c : ℝ) (hr : 1 < r) (hc : 0 ≤ c) (n : ℕ) (J : Finset ℕ)
    (hJ : J ⊆ Finset.range n) (m : ℕ) (hm : ∀ j ∈ J, m ≤ j) :
    ∑ j ∈ J, c * (r ^ j)⁻¹ ≤ c * (r ^ m)⁻¹ * (r / (r - 1)) := by
  have hr0 : (0 : ℝ) < r := lt_trans one_pos hr
  have hr1 : (0 : ℝ) < r - 1 := by linarith
  have hrinv : r⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]; right; exact hr
  have hinj : ∀ x ∈ J, ∀ y ∈ J, x - m = y - m → x = y := by
    intro x hx y hy hxy
    have hx' := hm x hx; have hy' := hm y hy; omega
  have key : ∑ j ∈ J, c * (r ^ j)⁻¹
      = c * (r ^ m)⁻¹ * ∑ j ∈ J, (r ^ (j - m))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjm : m ≤ j := hm j hj
    have hsplit : r ^ j = r ^ m * r ^ (j - m) := by
      rw [← pow_add, Nat.add_sub_cancel' hjm]
    rw [hsplit, mul_inv]; ring
  rw [key]
  have hgs : ∑ k ∈ Finset.range n, (r⁻¹) ^ k ≤ r / (r - 1) := by
    rw [geom_sum_eq (ne_of_lt hrinv)]
    rw [div_le_iff_of_neg (by linarith : r⁻¹ - 1 < 0)]
    have h₂ : r * (r⁻¹ - 1) = 1 - r := by
      field_simp
    have h₁ : r / (r - 1) * (r⁻¹ - 1) = -1 := by
      rw [div_mul_eq_mul_div, h₂, show (1 - r) = -(r - 1) by ring, neg_div,
        div_self (ne_of_gt hr1)]
    rw [h₁]
    have hpos : (0 : ℝ) ≤ (r⁻¹) ^ n := by positivity
    linarith
  have hsum : ∑ j ∈ J, (r ^ (j - m))⁻¹ ≤ r / (r - 1) := by
    have himg : ∑ k ∈ J.image (fun j => j - m), (r ^ k)⁻¹
        = ∑ j ∈ J, (r ^ (j - m))⁻¹ := Finset.sum_image hinj
    rw [← himg]
    calc ∑ k ∈ J.image (fun j => j - m), (r ^ k)⁻¹
        ≤ ∑ k ∈ Finset.range n, (r ^ k)⁻¹ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by positivity)
          intro k hk
          rw [Finset.mem_image] at hk
          obtain ⟨j, hjJ, rfl⟩ := hk
          exact Finset.mem_range.mpr (by have := Finset.mem_range.mp (hJ hjJ); omega)
      _ = ∑ k ∈ Finset.range n, (r⁻¹) ^ k := by
          refine Finset.sum_congr rfl (fun k _ => ?_); rw [inv_pow]
      _ ≤ r / (r - 1) := hgs
  calc c * (r ^ m)⁻¹ * ∑ j ∈ J, (r ^ (j - m))⁻¹
      ≤ c * (r ^ m)⁻¹ * (r / (r - 1)) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hc (by positivity))

/-! ### `rpow` helpers for quarter powers -/

private lemma pow16_rpow_quarter (k : ℕ) : ((16 : ℝ) ^ k) ^ (1/4 : ℝ) = 2 ^ k := by
  have h16 : (16 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ (4 : ℕ) := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [h16, show (1/4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]

private lemma pow16_rpow_threequarter (k : ℕ) : ((16 : ℝ) ^ k) ^ (3/4 : ℝ) = 8 ^ k := by
  have h : ((16 : ℝ) ^ k) ^ (3/4 : ℝ) = (((16 : ℝ) ^ k) ^ (1/4 : ℝ)) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast (((16 : ℝ) ^ k) ^ (1/4 : ℝ)) 3, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [h, pow16_rpow_quarter, ← pow_mul, show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, ← pow_mul,
    Nat.mul_comm]

private lemma rpow_quarter_pow4 (s : ℝ) (hs : 0 ≤ s) : (s ^ (4 : ℕ)) ^ (1/4 : ℝ) = s := by
  rw [show (1/4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast hs (by norm_num)]

private lemma rpow_34_add_14 (c : ℝ) (hc : 0 ≤ c) : c ^ (3/4 : ℝ) * c ^ (1/4 : ℝ) = c := by
  rcases eq_or_lt_of_le hc with h | h
  · rw [← h, Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num), mul_zero]
  · rw [← Real.rpow_add h, show (3/4 : ℝ) + (1/4 : ℝ) = 1 by norm_num, Real.rpow_one]

/-- Quarter-power interpolation of a `min`: `min a b ≤ a^{3/4}·b^{1/4}`. -/
private lemma min_le_rpow34 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min a b ≤ a ^ (3/4 : ℝ) * b ^ (1/4 : ℝ) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    calc a = a ^ (3/4 : ℝ) * a ^ (1/4 : ℝ) := (rpow_34_add_14 a ha).symm
      _ ≤ a ^ (3/4 : ℝ) * b ^ (1/4 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha h (by norm_num))
          (Real.rpow_nonneg ha _)
  · rw [min_eq_right h]
    calc b = b ^ (3/4 : ℝ) * b ^ (1/4 : ℝ) := (rpow_34_add_14 b hb).symm
      _ ≤ a ^ (3/4 : ℝ) * b ^ (1/4 : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hb h (by norm_num))
          (Real.rpow_nonneg hb _)

/-- `(c·M⁴)^{1/4} = c^{1/4}·M` for nonnegative `c, M`. -/
private lemma rpow_quarter_mul_pow4 (c M : ℝ) (hc : 0 ≤ c) (hM : 0 ≤ M) :
    (c * M ^ 4) ^ (1/4 : ℝ) = c ^ (1/4 : ℝ) * M := by
  rw [Real.mul_rpow hc (by positivity), rpow_quarter_pow4 M hM]

/-! ### Dyadic bracketing and per-term bounds (threshold-`T` versions) -/

/-- With `k := log₂ ⌊t/T⌋₊`, one has `2^k·T ≤ t < 2^{k+1}·T`. -/
private lemma dyadic_bracket' {T t : ℝ} (hT : 1 ≤ T) (ht : T ≤ t) :
    (2 : ℝ) ^ (Nat.log 2 ⌊t / T⌋₊) * T ≤ t ∧
      t < (2 : ℝ) ^ (Nat.log 2 ⌊t / T⌋₊ + 1) * T := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT
  have h1T : (1 : ℝ) ≤ t / T := (one_le_div hT0).mpr ht
  have hfloor1 : 1 ≤ ⌊t / T⌋₊ := Nat.le_floor (by exact_mod_cast h1T)
  have hne : ⌊t / T⌋₊ ≠ 0 := by omega
  have hpow_le : (2 : ℝ) ^ (Nat.log 2 ⌊t / T⌋₊) ≤ (⌊t / T⌋₊ : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hne
  have hnn_le : (⌊t / T⌋₊ : ℝ) ≤ t / T := Nat.floor_le (by positivity)
  have hlt_nn : t / T < (⌊t / T⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨?_, ?_⟩
  · have h2 : (2 : ℝ) ^ (Nat.log 2 ⌊t / T⌋₊) ≤ t / T := le_trans hpow_le hnn_le
    calc (2 : ℝ) ^ (Nat.log 2 ⌊t / T⌋₊) * T ≤ (t / T) * T :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt hT0)
      _ = t := by field_simp
  · have hnat : ⌊t / T⌋₊ + 1 ≤ 2 ^ (Nat.log 2 ⌊t / T⌋₊ + 1) :=
      Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) _)
    have hcast : (⌊t / T⌋₊ : ℝ) + 1 ≤ (2 : ℝ) ^ (Nat.log 2 ⌊t / T⌋₊ + 1) := by
      exact_mod_cast hnat
    have hchain : t / T < (2 : ℝ) ^ (Nat.log 2 ⌊t / T⌋₊ + 1) := by linarith
    calc t = (t / T) * T := by field_simp
      _ < (2 : ℝ) ^ (Nat.log 2 ⌊t / T⌋₊ + 1) * T := mul_lt_mul_of_pos_right hchain hT0

/-- `t⁻² ≤ 4^{-k}·T⁻²` when `2^k·T ≤ t`. -/
private lemma term_bound_sq {T t : ℝ} (hT0 : 0 < T) (k : ℕ)
    (hlow : (2 : ℝ) ^ k * T ≤ t) : t⁻¹ ^ 2 ≤ ((4 : ℝ) ^ k)⁻¹ * (T⁻¹) ^ 2 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k * T := by positivity
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hpos hlow
  have h1 : t⁻¹ ≤ ((2 : ℝ) ^ k * T)⁻¹ := inv_anti₀ hpos hlow
  have h2 : (0 : ℝ) ≤ t⁻¹ := le_of_lt (inv_pos.mpr ht0)
  calc t⁻¹ ^ 2 ≤ (((2 : ℝ) ^ k * T)⁻¹) ^ 2 := pow_le_pow_left₀ h2 h1 2
    _ = ((4 : ℝ) ^ k)⁻¹ * (T⁻¹) ^ 2 := by
        rw [mul_inv, mul_pow, inv_pow, show ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k by
          rw [pow_two, ← mul_pow]; norm_num]

/-- `t⁻¹ ≤ 2^{-k}·T⁻¹` when `2^k·T ≤ t`. -/
private lemma term_bound_one {T t : ℝ} (hT0 : 0 < T) (k : ℕ)
    (hlow : (2 : ℝ) ^ k * T ≤ t) : t⁻¹ ≤ ((2 : ℝ) ^ k)⁻¹ * T⁻¹ := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k * T := by positivity
  have h1 : t⁻¹ ≤ ((2 : ℝ) ^ k * T)⁻¹ := inv_anti₀ hpos hlow
  rwa [mul_inv] at h1

/-- Packing count for the ball of radius `2^{k+1}·T` (`T ≥ M`): an `M`-separated `A`
meets it in at most `16·min(|A|, 256·16^k·(T/M)⁴)` points. -/
private lemma fiber_card_bound (A : Finset (Fin 4 → ℤ)) (M : ℝ) (hM : 1 ≤ M)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → M ≤ znorm (x - y)) (v : Fin 4 → ℤ)
    (T : ℝ) (hMT : M ≤ T) (k : ℕ) :
    ((A.filter fun x => znorm (v - x) ≤ (2 : ℝ) ^ (k + 1) * T).card : ℝ)
      ≤ 16 * min (A.card : ℝ) (256 * 16 ^ k * (T / M) ^ 4) := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hTM1 : (1 : ℝ) ≤ T / M := (one_le_div hM0).mpr hMT
  have harith : ((2 : ℝ) ^ (k + 1) * T / M + 1) ^ 4 ≤ 256 * 16 ^ k * (T / M) ^ 4 := by
    have h1 : (2 : ℝ) ^ (k + 1) * T / M = 2 ^ (k + 1) * (T / M) := by ring
    have h2 : (2 : ℝ) ^ (k + 1) * (T / M) + 1 ≤ 2 ^ (k + 2) * (T / M) := by
      have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
      have h4 : (2 : ℝ) ^ (k + 2) = 2 ^ (k + 1) * 2 := pow_succ 2 (k + 1)
      rw [h4]; nlinarith
    have h5 : ((2 : ℝ) ^ (k + 2)) ^ 4 = 256 * 16 ^ k := by
      rw [← pow_mul, show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← pow_mul,
        show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, ← pow_add]
      congr 1; ring
    calc ((2 : ℝ) ^ (k + 1) * T / M + 1) ^ 4 ≤ ((2 : ℝ) ^ (k + 2) * (T / M)) ^ 4 := by
          rw [h1]; exact pow_le_pow_left₀ (by positivity) h2 4
      _ = 256 * 16 ^ k * (T / M) ^ 4 := by rw [mul_pow, h5]
  calc ((A.filter fun x => znorm (v - x) ≤ (2 : ℝ) ^ (k + 1) * T).card : ℝ)
      ≤ 16 * min (A.card : ℝ) (((2 : ℝ) ^ (k + 1) * T / M + 1) ^ 4) :=
        card_ball_center_le v A M hM hsep _
    _ ≤ 16 * min (A.card : ℝ) (256 * 16 ^ k * (T / M) ^ 4) :=
        mul_le_mul_of_nonneg_left (min_le_min le_rfl harith) (by norm_num)

/-- Per-shell estimate: the fiber `{x ∈ S : log₂⌊|v-x|/T⌋ = j}` of an `M`-separated `A`
(`S ⊆ A`, all points at distance `≥ T ≥ M` from `v`) contributes at most
`4096·T²·M⁻⁴·4^j` to `∑ |v-x|⁻²`. -/
private lemma fiber_sum_le (A : Finset (Fin 4 → ℤ)) (M : ℝ) (hM : 1 ≤ M)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → M ≤ znorm (x - y)) (v : Fin 4 → ℤ)
    (T : ℝ) (hMT : M ≤ T) (j : ℕ) (S : Finset (Fin 4 → ℤ))
    (hS : ∀ x ∈ S, x ∈ A ∧ T ≤ znorm (v - x)) :
    ∑ x ∈ S.filter (fun x => Nat.log 2 ⌊znorm (v - x) / T⌋₊ = j), (znorm (v - x))⁻¹ ^ 2
      ≤ 4096 * (T ^ 2 * (M⁻¹) ^ 4) * 4 ^ j := by
  classical
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hT1 : (1 : ℝ) ≤ T := le_trans hM hMT
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
  set Sj := S.filter (fun x => Nat.log 2 ⌊znorm (v - x) / T⌋₊ = j) with hSj
  have hterm : ∀ x ∈ Sj, (znorm (v - x))⁻¹ ^ 2 ≤ ((4 : ℝ) ^ j)⁻¹ * (T⁻¹) ^ 2 := by
    intro x hx
    rw [hSj, mem_filter] at hx
    obtain ⟨hxS, hlog⟩ := hx
    obtain ⟨-, hTx⟩ := hS x hxS
    have hbr := (dyadic_bracket' hT1 hTx).1
    rw [hlog] at hbr
    exact term_bound_sq hT0 j hbr
  have hsub : Sj ⊆ A.filter (fun x => znorm (v - x) ≤ (2 : ℝ) ^ (j + 1) * T) := by
    intro x hx
    rw [hSj, mem_filter] at hx
    obtain ⟨hxS, hlog⟩ := hx
    obtain ⟨hxA, hTx⟩ := hS x hxS
    rw [mem_filter]
    refine ⟨hxA, ?_⟩
    have hbr := (dyadic_bracket' hT1 hTx).2
    rw [hlog] at hbr
    exact le_of_lt hbr
  have hcard : ((Sj.card : ℝ)) ≤ 16 * (256 * 16 ^ j * (T / M) ^ 4) := by
    calc ((Sj.card : ℝ))
        ≤ ((A.filter (fun x => znorm (v - x) ≤ (2 : ℝ) ^ (j + 1) * T)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ 16 * min (A.card : ℝ) (256 * 16 ^ j * (T / M) ^ 4) :=
          fiber_card_bound A M hM hsep v T hMT j
      _ ≤ 16 * (256 * 16 ^ j * (T / M) ^ 4) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
  have hid : 16 * (256 * (16 : ℝ) ^ j * (T / M) ^ 4) * (((4 : ℝ) ^ j)⁻¹ * (T⁻¹) ^ 2)
      = 4096 * (T ^ 2 * (M⁻¹) ^ 4) * 4 ^ j := by
    have h16 : (16 : ℝ) ^ j = 4 ^ j * 4 ^ j := by rw [← mul_pow]; norm_num
    have h4 : ((4 : ℝ) ^ j) ≠ 0 := by positivity
    have hT' : T ≠ 0 := ne_of_gt hT0
    have hM' : M ≠ 0 := ne_of_gt hM0
    field_simp [h16]
    rw [pow_two, ← h16]
    ring
  calc ∑ x ∈ Sj, (znorm (v - x))⁻¹ ^ 2
      ≤ ∑ _x ∈ Sj, ((4 : ℝ) ^ j)⁻¹ * (T⁻¹) ^ 2 := Finset.sum_le_sum hterm
    _ = (Sj.card : ℝ) * (((4 : ℝ) ^ j)⁻¹ * (T⁻¹) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 16 * (256 * 16 ^ j * (T / M) ^ 4) * (((4 : ℝ) ^ j)⁻¹ * (T⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 4096 * (T ^ 2 * (M⁻¹) ^ 4) * 4 ^ j := hid

/-- Truncated single-variable dyadic sum (increasing branch of (5.62)): for
`M`-separated `A`, threshold `T ≥ M`, radius `R`:
`∑_{x ∈ A, T ≤ |v-x| ≤ R} |v-x|⁻² ≤ (16384/3)·R²·M⁻⁴`. -/
private lemma ball_sum_bound (A : Finset (Fin 4 → ℤ)) (M : ℝ) (hM : 1 ≤ M)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → M ≤ znorm (x - y)) (v : Fin 4 → ℤ)
    (T R : ℝ) (hMT : M ≤ T) :
    ∑ x ∈ A.filter (fun x => T ≤ znorm (v - x) ∧ znorm (v - x) ≤ R),
      (znorm (v - x))⁻¹ ^ 2 ≤ (16384/3) * R ^ 2 * (M⁻¹) ^ 4 := by
  classical
  have hT1 : (1 : ℝ) ≤ T := le_trans hM hMT
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
  set S := A.filter (fun x => T ≤ znorm (v - x) ∧ znorm (v - x) ≤ R) with hSdef
  have hSfacts : ∀ x ∈ S, x ∈ A ∧ T ≤ znorm (v - x) := by
    intro x hx
    rw [hSdef, mem_filter] at hx
    exact ⟨hx.1, hx.2.1⟩
  set K := S.sup (fun x => Nat.log 2 ⌊znorm (v - x) / T⌋₊) with hK
  have hmapsK : ∀ x ∈ S, Nat.log 2 ⌊znorm (v - x) / T⌋₊ ∈ Finset.range (K + 1) := by
    intro x hx
    rw [Finset.mem_range]
    have hle : Nat.log 2 ⌊znorm (v - x) / T⌋₊ ≤ K :=
      Finset.le_sup (f := fun x => Nat.log 2 ⌊znorm (v - x) / T⌋₊) hx
    omega
  have hzero : ∀ j ∈ Finset.range (K + 1),
      (∑ x ∈ S.filter (fun x => Nat.log 2 ⌊znorm (v - x) / T⌋₊ = j),
        (znorm (v - x))⁻¹ ^ 2) ≠ 0 → (2 : ℝ) ^ j * T ≤ R := by
    intro j _ hne
    by_contra hnot
    apply hne
    apply Finset.sum_eq_zero
    intro x hx
    exfalso
    rw [mem_filter] at hx
    obtain ⟨hxS, hlog⟩ := hx
    rw [hSdef, mem_filter] at hxS
    obtain ⟨-, hTx, hxR⟩ := hxS
    have hbr := (dyadic_bracket' hT1 hTx).1
    rw [hlog] at hbr
    exact hnot (le_trans hbr hxR)
  set J := (Finset.range (K + 1)).filter (fun j => (2 : ℝ) ^ j * T ≤ R) with hJdef
  have hlast : ∑ j ∈ J, 4096 * (T ^ 2 * (M⁻¹) ^ 4) * 4 ^ j
      ≤ (16384/3) * R ^ 2 * (M⁻¹) ^ 4 := by
    rcases J.eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty]; positivity
    · have hub : ∀ j ∈ J, j ≤ J.max' hne := fun j hj => Finset.le_max' _ j hj
      have hmR : (2 : ℝ) ^ (J.max' hne) * T ≤ R :=
        (mem_filter.mp (J.max'_mem hne)).2
      have hRT : (4 : ℝ) ^ (J.max' hne) * T ^ 2 ≤ R ^ 2 := by
        have h2m : (0 : ℝ) ≤ (2 : ℝ) ^ (J.max' hne) * T := by positivity
        have hsq := pow_le_pow_left₀ h2m hmR 2
        calc (4 : ℝ) ^ (J.max' hne) * T ^ 2 = ((2 : ℝ) ^ (J.max' hne) * T) ^ 2 := by
              rw [mul_pow, show ((2 : ℝ) ^ (J.max' hne)) ^ 2 = 4 ^ (J.max' hne) by
                rw [pow_two, ← mul_pow]; norm_num]
          _ ≤ R ^ 2 := hsq
      calc ∑ j ∈ J, 4096 * (T ^ 2 * (M⁻¹) ^ 4) * 4 ^ j
          ≤ 4096 * (T ^ 2 * (M⁻¹) ^ 4) * 4 ^ (J.max' hne) * (4 / (4 - 1)) :=
            geom_incr_le 4 _ (by norm_num) (by positivity) J _ hub
        _ = (16384/3) * ((4 : ℝ) ^ (J.max' hne) * T ^ 2) * (M⁻¹) ^ 4 := by ring
        _ ≤ (16384/3) * R ^ 2 * (M⁻¹) ^ 4 := by
            have h4 : (0 : ℝ) ≤ (M⁻¹) ^ 4 := by positivity
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hRT (by norm_num)) h4
  calc ∑ x ∈ S, (znorm (v - x))⁻¹ ^ 2
      = ∑ j ∈ Finset.range (K + 1),
          ∑ x ∈ S.filter (fun x => Nat.log 2 ⌊znorm (v - x) / T⌋₊ = j),
          (znorm (v - x))⁻¹ ^ 2 :=
        (Finset.sum_fiberwise_of_maps_to hmapsK _).symm
    _ = ∑ j ∈ J, ∑ x ∈ S.filter (fun x => Nat.log 2 ⌊znorm (v - x) / T⌋₊ = j),
          (znorm (v - x))⁻¹ ^ 2 := (Finset.sum_filter_of_ne hzero).symm
    _ ≤ ∑ j ∈ J, 4096 * (T ^ 2 * (M⁻¹) ^ 4) * 4 ^ j :=
        Finset.sum_le_sum (fun j _ => fiber_sum_le A M hM hsep v T hMT j S hSfacts)
    _ ≤ (16384/3) * R ^ 2 * (M⁻¹) ^ 4 := hlast

/-- Dyadic min-sum with constant cap: `∑_{k<n} min(a·16^{-k}, b) ≤ b·(16/15) + b·(a/b)^{1/4}`.
The second term counts the non-decaying scales (paper (5.64), `log ≤ 1 + P^{1/4}/…`). -/
private lemma sum_min_const_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (n : ℕ) :
    ∑ k ∈ Finset.range n, min (a * ((16 : ℝ) ^ k)⁻¹) b
      ≤ b * (16/15) + b * (a / b) ^ (1/4 : ℝ) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range n)
      (fun k => a * ((16 : ℝ) ^ k)⁻¹ ≤ b) (fun k => min (a * ((16 : ℝ) ^ k)⁻¹) b)
  have h1 : ∑ k ∈ (Finset.range n).filter (fun k => a * ((16 : ℝ) ^ k)⁻¹ ≤ b),
      min (a * ((16 : ℝ) ^ k)⁻¹) b ≤ b * (16/15) := by
    set J := (Finset.range n).filter (fun k => a * ((16 : ℝ) ^ k)⁻¹ ≤ b) with hJ
    rcases J.eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty]; positivity
    · have hlb : ∀ j ∈ J, J.min' hne ≤ j := fun j hj => Finset.min'_le _ j hj
      have hsubn : J ⊆ Finset.range n := Finset.filter_subset _ _
      have hmem : a * ((16 : ℝ) ^ (J.min' hne))⁻¹ ≤ b := (mem_filter.mp (J.min'_mem hne)).2
      calc ∑ k ∈ J, min (a * ((16 : ℝ) ^ k)⁻¹) b
          ≤ ∑ k ∈ J, a * ((16 : ℝ) ^ k)⁻¹ :=
            Finset.sum_le_sum (fun k _ => min_le_left _ _)
        _ ≤ a * ((16 : ℝ) ^ (J.min' hne))⁻¹ * (16 / (16 - 1)) :=
            geom_decr_le 16 a (by norm_num) ha n J hsubn _ hlb
        _ ≤ b * (16/15) := by
            rw [show (16 : ℝ) / (16 - 1) = 16/15 by norm_num]
            exact mul_le_mul_of_nonneg_right hmem (by norm_num)
  have h2 : ∑ k ∈ (Finset.range n).filter (fun k => ¬ a * ((16 : ℝ) ^ k)⁻¹ ≤ b),
      min (a * ((16 : ℝ) ^ k)⁻¹) b ≤ b * (a / b) ^ (1/4 : ℝ) := by
    set J := (Finset.range n).filter (fun k => ¬ a * ((16 : ℝ) ^ k)⁻¹ ≤ b) with hJ
    rcases J.eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty]; positivity
    · set m := J.max' hne with hm
      have hub : ∀ j ∈ J, j ≤ m := fun j hj => Finset.le_max' _ j hj
      have hmm : b < a * ((16 : ℝ) ^ m)⁻¹ := not_le.mp (mem_filter.mp (J.max'_mem hne)).2
      have h16m : (16 : ℝ) ^ m ≤ a / b := by
        rw [le_div_iff₀ hb]
        have h16 : (0 : ℝ) < (16 : ℝ) ^ m := by positivity
        have hstep := mul_lt_mul_of_pos_right hmm h16
        rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt h16), mul_one] at hstep
        linarith
      have h2m : (2 : ℝ) ^ m ≤ (a / b) ^ (1/4 : ℝ) := by
        rw [← pow16_rpow_quarter m]
        exact Real.rpow_le_rpow (by positivity) h16m (by norm_num)
      have hcard : ((J.card : ℝ)) ≤ (2 : ℝ) ^ m := by
        have hsub : J ⊆ Finset.range (m + 1) := fun j hj =>
          Finset.mem_range.mpr (Nat.lt_succ_of_le (hub j hj))
        have hc1 : J.card ≤ m + 1 := by
          calc J.card ≤ (Finset.range (m + 1)).card := Finset.card_le_card hsub
            _ = m + 1 := Finset.card_range _
        have hc2 : m + 1 ≤ 2 ^ m := Nat.succ_le_of_lt Nat.lt_two_pow_self
        calc ((J.card : ℝ)) ≤ ((m : ℝ) + 1) := by exact_mod_cast hc1
          _ ≤ (2 : ℝ) ^ m := by exact_mod_cast hc2
      calc ∑ k ∈ J, min (a * ((16 : ℝ) ^ k)⁻¹) b
          ≤ ∑ _k ∈ J, b := Finset.sum_le_sum (fun k _ => min_le_right _ _)
        _ = (J.card : ℝ) * b := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 : ℝ) ^ m * b := mul_le_mul_of_nonneg_right hcard (le_of_lt hb)
        _ ≤ (a / b) ^ (1/4 : ℝ) * b := mul_le_mul_of_nonneg_right h2m (le_of_lt hb)
        _ = b * (a / b) ^ (1/4 : ℝ) := mul_comm _ _
  rw [← hsplit]
  linarith [h1, h2]

/-- Quartic per-shell estimate at scale `2^j·S` (`S ≥ M`): the shell contributes at most
`16·min(|A|·S⁻⁴·16^{-j}, 256·M⁻⁴)` to `∑ |u-x|⁻⁴`. -/
private lemma fiber_sum4_le (A : Finset (Fin 4 → ℤ)) (M : ℝ) (hM : 1 ≤ M)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → M ≤ znorm (x - y)) (u : Fin 4 → ℤ)
    (S : ℝ) (hMS : M ≤ S) (j : ℕ) :
    ∑ x ∈ (A.filter (fun x => S ≤ znorm (u - x))).filter
        (fun x => Nat.log 2 ⌊znorm (u - x) / S⌋₊ = j), ((znorm (u - x))⁻¹ ^ 2) ^ 2
      ≤ 16 * min ((A.card : ℝ) * (S⁻¹) ^ 4 * ((16 : ℝ) ^ j)⁻¹) (256 * (M⁻¹) ^ 4) := by
  classical
  have hS1 : (1 : ℝ) ≤ S := le_trans hM hMS
  have hS0 : (0 : ℝ) < S := lt_of_lt_of_le one_pos hS1
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  set Fj := (A.filter (fun x => S ≤ znorm (u - x))).filter
      (fun x => Nat.log 2 ⌊znorm (u - x) / S⌋₊ = j) with hFj
  have hterm : ∀ x ∈ Fj, ((znorm (u - x))⁻¹ ^ 2) ^ 2
      ≤ ((16 : ℝ) ^ j)⁻¹ * ((S⁻¹) ^ 2) ^ 2 := by
    intro x hx
    rw [hFj, mem_filter] at hx
    obtain ⟨hxS, hlog⟩ := hx
    rw [mem_filter] at hxS
    have hbr := (dyadic_bracket' hS1 hxS.2).1
    rw [hlog] at hbr
    have h1 := term_bound_sq hS0 j hbr
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    calc ((znorm (u - x))⁻¹ ^ 2) ^ 2 ≤ (((4 : ℝ) ^ j)⁻¹ * (S⁻¹) ^ 2) ^ 2 := h2
      _ = ((16 : ℝ) ^ j)⁻¹ * ((S⁻¹) ^ 2) ^ 2 := by
          rw [mul_pow, inv_pow, show ((4 : ℝ) ^ j) ^ 2 = 16 ^ j by
            rw [pow_two, ← mul_pow]; norm_num]
  have hsub : Fj ⊆ A.filter (fun x => znorm (u - x) ≤ (2 : ℝ) ^ (j + 1) * S) := by
    intro x hx
    rw [hFj, mem_filter] at hx
    obtain ⟨hxS, hlog⟩ := hx
    rw [mem_filter] at hxS ⊢
    refine ⟨hxS.1, ?_⟩
    have hbr := (dyadic_bracket' hS1 hxS.2).2
    rw [hlog] at hbr
    exact le_of_lt hbr
  have hcard : ((Fj.card : ℝ)) ≤ 16 * min (A.card : ℝ) (256 * 16 ^ j * (S / M) ^ 4) := by
    calc ((Fj.card : ℝ))
        ≤ ((A.filter (fun x => znorm (u - x) ≤ (2 : ℝ) ^ (j + 1) * S)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ 16 * min (A.card : ℝ) (256 * 16 ^ j * (S / M) ^ 4) :=
          fiber_card_bound A M hM hsep u S hMS j
  have hmin_id : min ((A.card : ℝ)) (256 * 16 ^ j * (S / M) ^ 4)
        * (((16 : ℝ) ^ j)⁻¹ * ((S⁻¹) ^ 2) ^ 2)
      = min ((A.card : ℝ) * (S⁻¹) ^ 4 * ((16 : ℝ) ^ j)⁻¹) (256 * (M⁻¹) ^ 4) := by
    rw [min_mul_of_nonneg _ _ (by positivity)]
    congr 1
    · ring
    · have h16 : ((16 : ℝ) ^ j) ≠ 0 := by positivity
      have hS' : S ≠ 0 := ne_of_gt hS0
      have hM' : M ≠ 0 := ne_of_gt hM0
      field_simp
  calc ∑ x ∈ Fj, ((znorm (u - x))⁻¹ ^ 2) ^ 2
      ≤ ∑ _x ∈ Fj, ((16 : ℝ) ^ j)⁻¹ * ((S⁻¹) ^ 2) ^ 2 := Finset.sum_le_sum hterm
    _ = (Fj.card : ℝ) * (((16 : ℝ) ^ j)⁻¹ * ((S⁻¹) ^ 2) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 16 * min ((A.card : ℝ)) (256 * 16 ^ j * (S / M) ^ 4)
          * (((16 : ℝ) ^ j)⁻¹ * ((S⁻¹) ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 16 * min ((A.card : ℝ) * (S⁻¹) ^ 4 * ((16 : ℝ) ^ j)⁻¹) (256 * (M⁻¹) ^ 4) := by
        rw [mul_assoc, hmin_id]

/-- Far-field quartic sum, paper (5.64): for `M`-separated `A` and `S ≥ M`,
`∑_{x ∈ A, S ≤ |u-x|} |u-x|⁻⁴ ≤ 4370·M⁻⁴·(1 + P^{1/4}/S)` with `P = |A|·M⁴`. -/
private lemma far_sum_bound (A : Finset (Fin 4 → ℤ)) (M : ℝ) (hM : 1 ≤ M)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → M ≤ znorm (x - y)) (u : Fin 4 → ℤ)
    (S : ℝ) (hMS : M ≤ S) :
    ∑ x ∈ A.filter (fun x => S ≤ znorm (u - x)), ((znorm (u - x))⁻¹ ^ 2) ^ 2
      ≤ 4370 * (M⁻¹) ^ 4 * (1 + ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / S) := by
  classical
  have hS1 : (1 : ℝ) ≤ S := le_trans hM hMS
  have hS0 : (0 : ℝ) < S := lt_of_lt_of_le one_pos hS1
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  set F := A.filter (fun x => S ≤ znorm (u - x)) with hF
  set K := F.sup (fun x => Nat.log 2 ⌊znorm (u - x) / S⌋₊) with hK
  have hmapsK : ∀ x ∈ F, Nat.log 2 ⌊znorm (u - x) / S⌋₊ ∈ Finset.range (K + 1) := by
    intro x hx
    rw [Finset.mem_range]
    have hle : Nat.log 2 ⌊znorm (u - x) / S⌋₊ ≤ K :=
      Finset.le_sup (f := fun x => Nat.log 2 ⌊znorm (u - x) / S⌋₊) hx
    omega
  set a := (A.card : ℝ) * (S⁻¹) ^ 4 with ha
  set b := (256 : ℝ) * (M⁻¹) ^ 4 with hb
  have hbpos : (0 : ℝ) < b := by rw [hb]; positivity
  have hannonneg : (0 : ℝ) ≤ a := by rw [ha]; positivity
  have hsum : ∑ x ∈ F, ((znorm (u - x))⁻¹ ^ 2) ^ 2
      ≤ 16 * ∑ k ∈ Finset.range (K + 1), min (a * ((16 : ℝ) ^ k)⁻¹) b := by
    calc ∑ x ∈ F, ((znorm (u - x))⁻¹ ^ 2) ^ 2
        = ∑ j ∈ Finset.range (K + 1),
            ∑ x ∈ F.filter (fun x => Nat.log 2 ⌊znorm (u - x) / S⌋₊ = j),
            ((znorm (u - x))⁻¹ ^ 2) ^ 2 :=
          (Finset.sum_fiberwise_of_maps_to hmapsK _).symm
      _ ≤ ∑ j ∈ Finset.range (K + 1), 16 * min (a * ((16 : ℝ) ^ j)⁻¹) b := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          have h := fiber_sum4_le A M hM hsep u S hMS j
          rw [← hF] at h
          calc ∑ x ∈ F.filter (fun x => Nat.log 2 ⌊znorm (u - x) / S⌋₊ = j),
                ((znorm (u - x))⁻¹ ^ 2) ^ 2
              ≤ 16 * min ((A.card : ℝ) * (S⁻¹) ^ 4 * ((16 : ℝ) ^ j)⁻¹)
                  (256 * (M⁻¹) ^ 4) := h
            _ = 16 * min (a * ((16 : ℝ) ^ j)⁻¹) b := by rw [ha, hb]
      _ = 16 * ∑ k ∈ Finset.range (K + 1), min (a * ((16 : ℝ) ^ k)⁻¹) b := by
          rw [Finset.mul_sum]
  have hab : a / b ≤ (A.card : ℝ) * M ^ 4 * (S⁻¹) ^ 4 := by
    rw [div_le_iff₀ hbpos]
    have hMM : M ^ 4 * (M⁻¹) ^ 4 = 1 := by field_simp
    calc a ≤ 256 * a := by linarith
      _ = 256 * a * (M ^ 4 * (M⁻¹) ^ 4) := by rw [hMM, mul_one]
      _ = (A.card : ℝ) * M ^ 4 * (S⁻¹) ^ 4 * (256 * (M⁻¹) ^ 4) := by rw [ha]; ring
  have habq : (a / b) ^ (1/4 : ℝ) ≤ ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / S := by
    have h1 : (a / b) ^ (1/4 : ℝ) ≤ ((A.card : ℝ) * M ^ 4 * (S⁻¹) ^ 4) ^ (1/4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hab (by norm_num)
    have h2 : ((A.card : ℝ) * M ^ 4 * (S⁻¹) ^ 4) ^ (1/4 : ℝ)
        = ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) * S⁻¹ :=
      rpow_quarter_mul_pow4 _ _ (by positivity) (by positivity)
    rw [div_eq_mul_inv]
    rw [h2] at h1
    exact h1
  have hrnn : (0 : ℝ) ≤ ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / S :=
    div_nonneg (Real.rpow_nonneg (by positivity) _) (le_of_lt hS0)
  have h4 : (0 : ℝ) ≤ (M⁻¹) ^ 4 := by positivity
  calc ∑ x ∈ F, ((znorm (u - x))⁻¹ ^ 2) ^ 2
      ≤ 16 * ∑ k ∈ Finset.range (K + 1), min (a * ((16 : ℝ) ^ k)⁻¹) b := hsum
    _ ≤ 16 * (b * (16/15) + b * (a / b) ^ (1/4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_min_const_le a b hannonneg hbpos (K + 1))
          (by norm_num)
    _ ≤ 4370 * (M⁻¹) ^ 4 * (1 + ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / S) := by
        rw [hb]
        have hprod := mul_le_mul_of_nonneg_left habq h4
        have hprodnn := mul_nonneg h4 hrnn
        nlinarith [hprod, hprodnn, h4]

/-! ### The three cases of the pointwise estimate (5.63) -/

/-- Case (a1): `M ≤ |u-x| ≤ 2S` and `|x-y| ≥ S/4`.  Contribution `≲ M⁻⁴`. -/
private lemma case_a1_bound (A : Finset (Fin 4 → ℤ)) (M : ℝ) (hM : 1 ≤ M)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → M ≤ znorm (x - y)) (u y : Fin 4 → ℤ)
    (S : ℝ) (hMS : M ≤ S) (T : Finset (Fin 4 → ℤ)) (hTA : T ⊆ A)
    (hcond : ∀ x ∈ T, M ≤ znorm (u - x) ∧ znorm (u - x) ≤ 2 * S ∧ S / 4 ≤ znorm (x - y)) :
    ∑ x ∈ T, (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
      ≤ 1048576/3 * (M⁻¹) ^ 4 := by
  have hS0 : (0 : ℝ) < S := lt_of_lt_of_le (lt_of_lt_of_le one_pos hM) hMS
  have hS40 : (0 : ℝ) < S / 4 := by positivity
  have hstep : ∀ x ∈ T, (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
      ≤ (znorm (u - x))⁻¹ ^ 2 * (16 * (S⁻¹) ^ 2) := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hcond x hx
    have hinv : (znorm (x - y))⁻¹ ≤ (S / 4)⁻¹ := inv_anti₀ hS40 h3
    have hinv2 : (znorm (x - y))⁻¹ ^ 2 ≤ ((S / 4)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr (znorm_nonneg _)) hinv 2
    have hid : ((S / 4)⁻¹) ^ 2 = 16 * (S⁻¹) ^ 2 := by
      rw [inv_div, div_pow, inv_pow, div_eq_mul_inv]
      norm_num
    rw [hid] at hinv2
    exact mul_le_mul_of_nonneg_left hinv2 (by positivity)
  calc ∑ x ∈ T, (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
      ≤ ∑ x ∈ T, (znorm (u - x))⁻¹ ^ 2 * (16 * (S⁻¹) ^ 2) := Finset.sum_le_sum hstep
    _ = (∑ x ∈ T, (znorm (u - x))⁻¹ ^ 2) * (16 * (S⁻¹) ^ 2) := by rw [← Finset.sum_mul]
    _ ≤ ((16384 : ℝ)/3 * (2 * S) ^ 2 * (M⁻¹) ^ 4) * (16 * (S⁻¹) ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc ∑ x ∈ T, (znorm (u - x))⁻¹ ^ 2
            ≤ ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x) ∧ znorm (u - x) ≤ 2 * S),
                (znorm (u - x))⁻¹ ^ 2 := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => by positivity)
              intro x hx
              rw [mem_filter]
              obtain ⟨h1, h2, -⟩ := hcond x hx
              exact ⟨hTA hx, h1, h2⟩
          _ ≤ (16384 : ℝ)/3 * (2 * S) ^ 2 * (M⁻¹) ^ 4 :=
              ball_sum_bound A M hM hsep u M (2 * S) le_rfl
    _ = 1048576/3 * (M⁻¹) ^ 4 * (S ^ 2 * (S⁻¹) ^ 2) := by ring
    _ = 1048576/3 * (M⁻¹) ^ 4 := by
        rw [show S ^ 2 * (S⁻¹) ^ 2 = 1 by field_simp, mul_one]

/-- Case (a2): `max M N ≤ |x-y| ≤ S/4` forces `S = |u-y|` and `|u-x| ≥ 3S/4`;
contribution `≲ M⁻⁴`. -/
private lemma case_a2_bound (A : Finset (Fin 4 → ℤ)) (M N : ℝ) (hM : 1 ≤ M)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → M ≤ znorm (x - y)) (u y : Fin 4 → ℤ)
    (S : ℝ) (hS : S = max (znorm (u - y)) (max M N))
    (T : Finset (Fin 4 → ℤ)) (hTA : T ⊆ A)
    (hcond : ∀ x ∈ T, max M N ≤ znorm (x - y) ∧ znorm (x - y) ≤ S / 4) :
    ∑ x ∈ T, (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
      ≤ 16384/27 * (M⁻¹) ^ 4 := by
  have hMS : M ≤ S := by
    rw [hS]; exact le_trans (le_max_left M N) (le_max_right _ _)
  have hS0 : (0 : ℝ) < S := lt_of_lt_of_le (lt_of_lt_of_le one_pos hM) hMS
  have hstep : ∀ x ∈ T, (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
      ≤ (16/9 * (S⁻¹) ^ 2) * (znorm (x - y))⁻¹ ^ 2 := by
    intro x hx
    obtain ⟨h1, h2⟩ := hcond x hx
    have hmax4 : max M N ≤ S / 4 := le_trans h1 h2
    have hSy : S = znorm (u - y) := by
      rcases max_cases (znorm (u - y)) (max M N) with ⟨he, -⟩ | ⟨he, -⟩
      · rw [hS, he]
      · exfalso
        rw [hS, he] at hmax4
        have hM1 : (1 : ℝ) ≤ max M N := le_trans hM (le_max_left M N)
        linarith
    have htri := znorm_triangle u x y
    rw [← hSy] at htri
    have hux : 3 / 4 * S ≤ znorm (u - x) := by linarith
    have h34 : (0 : ℝ) < 3 / 4 * S := by positivity
    have hinv : (znorm (u - x))⁻¹ ≤ (3 / 4 * S)⁻¹ := inv_anti₀ h34 hux
    have hinv2 : (znorm (u - x))⁻¹ ^ 2 ≤ ((3 / 4 * S)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr (znorm_nonneg _)) hinv 2
    have hid : ((3 / 4 * S)⁻¹) ^ 2 = 16/9 * (S⁻¹) ^ 2 := by
      rw [mul_inv, mul_pow]
      norm_num
    rw [hid] at hinv2
    exact mul_le_mul_of_nonneg_right hinv2 (by positivity)
  calc ∑ x ∈ T, (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
      ≤ ∑ x ∈ T, (16/9 * (S⁻¹) ^ 2) * (znorm (x - y))⁻¹ ^ 2 := Finset.sum_le_sum hstep
    _ = (16/9 * (S⁻¹) ^ 2) * ∑ x ∈ T, (znorm (x - y))⁻¹ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (16/9 * (S⁻¹) ^ 2) * (16384/3 * (S/4) ^ 2 * (M⁻¹) ^ 4) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hswap : ∑ x ∈ T, (znorm (x - y))⁻¹ ^ 2 = ∑ x ∈ T, (znorm (y - x))⁻¹ ^ 2 :=
          Finset.sum_congr rfl (fun x _ => by rw [znorm_sub_comm])
        rw [hswap]
        calc ∑ x ∈ T, (znorm (y - x))⁻¹ ^ 2
            ≤ ∑ x ∈ A.filter (fun x => max M N ≤ znorm (y - x) ∧ znorm (y - x) ≤ S/4),
                (znorm (y - x))⁻¹ ^ 2 := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => by positivity)
              intro x hx
              rw [mem_filter, znorm_sub_comm y x]
              obtain ⟨h1, h2⟩ := hcond x hx
              exact ⟨hTA hx, h1, h2⟩
          _ ≤ 16384/3 * (S/4) ^ 2 * (M⁻¹) ^ 4 :=
              ball_sum_bound A M hM hsep y (max M N) (S/4) (le_max_left M N)
    _ = 16384/27 * (M⁻¹) ^ 4 * (S ^ 2 * (S⁻¹) ^ 2) := by ring
    _ = 16384/27 * (M⁻¹) ^ 4 := by
        rw [show S ^ 2 * (S⁻¹) ^ 2 = 1 by field_simp, mul_one]

/-- Case (b): `|u-x| > 2S` gives `|x-y| > |u-x|/2`; quartic far-field contribution
`≤ 17480·M⁻⁴·(1 + P^{1/4}/S)`. -/
private lemma case_b_bound (A : Finset (Fin 4 → ℤ)) (M : ℝ) (hM : 1 ≤ M)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → M ≤ znorm (x - y)) (u y : Fin 4 → ℤ)
    (S : ℝ) (hMS : M ≤ S) (hyS : znorm (u - y) ≤ S)
    (T : Finset (Fin 4 → ℤ)) (hTA : T ⊆ A)
    (hcond : ∀ x ∈ T, 2 * S < znorm (u - x)) :
    ∑ x ∈ T, (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
      ≤ 17480 * (M⁻¹) ^ 4 * (1 + ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / S) := by
  have hS0 : (0 : ℝ) < S := lt_of_lt_of_le (lt_of_lt_of_le one_pos hM) hMS
  have hstep : ∀ x ∈ T, (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
      ≤ 4 * ((znorm (u - x))⁻¹ ^ 2) ^ 2 := by
    intro x hx
    have hb := hcond x hx
    have hux0 : (0 : ℝ) < znorm (u - x) := lt_trans (by positivity) hb
    have htri := znorm_triangle u y x
    rw [znorm_sub_comm y x] at htri
    have hxy : znorm (u - x) / 2 ≤ znorm (x - y) := by linarith
    have hhalf : (0 : ℝ) < znorm (u - x) / 2 := by positivity
    have hinv : (znorm (x - y))⁻¹ ≤ (znorm (u - x) / 2)⁻¹ := inv_anti₀ hhalf hxy
    have hinv2 : (znorm (x - y))⁻¹ ^ 2 ≤ ((znorm (u - x) / 2)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr (znorm_nonneg _)) hinv 2
    have hid : ((znorm (u - x) / 2)⁻¹) ^ 2 = 4 * (znorm (u - x))⁻¹ ^ 2 := by
      rw [inv_div, div_pow, inv_pow, div_eq_mul_inv]
      norm_num
    rw [hid] at hinv2
    calc (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
        ≤ (znorm (u - x))⁻¹ ^ 2 * (4 * (znorm (u - x))⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_left hinv2 (by positivity)
      _ = 4 * ((znorm (u - x))⁻¹ ^ 2) ^ 2 := by ring
  calc ∑ x ∈ T, (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
      ≤ ∑ x ∈ T, 4 * ((znorm (u - x))⁻¹ ^ 2) ^ 2 := Finset.sum_le_sum hstep
    _ = 4 * ∑ x ∈ T, ((znorm (u - x))⁻¹ ^ 2) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 4 * (4370 * (M⁻¹) ^ 4 * (1 + ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / S)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        calc ∑ x ∈ T, ((znorm (u - x))⁻¹ ^ 2) ^ 2
            ≤ ∑ x ∈ A.filter (fun x => S ≤ znorm (u - x)),
                ((znorm (u - x))⁻¹ ^ 2) ^ 2 := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => by positivity)
              intro x hx
              rw [mem_filter]
              refine ⟨hTA hx, le_of_lt (lt_of_le_of_lt ?_ (hcond x hx))⟩
              linarith
          _ ≤ 4370 * (M⁻¹) ^ 4 * (1 + ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / S) :=
              far_sum_bound A M hM hsep u S hMS
    _ = 17480 * (M⁻¹) ^ 4 * (1 + ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / S) := by ring

/-- **Pointwise (in `y`) bilinear estimate, paper (5.63).**  For `M`-separated `A`
(`M ≥ 1`), any `u, y` and any `N`,
`∑_{x ∈ A, |u-x| ≥ M, |x-y| ≥ max(M,N)} |u-x|⁻²|x-y|⁻²
  ≤ 524288·M⁻⁴·(1 + P^{1/4}/max(|u-y|, M, N))` with `P = |A|·M⁴`. -/
theorem single_y_bound (A : Finset (Fin 4 → ℤ)) (M N : ℝ) (hM : 1 ≤ M)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → M ≤ znorm (x - y)) (u y : Fin 4 → ℤ) :
    ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x) ∧ max M N ≤ znorm (x - y)),
      (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
    ≤ 524288 * (M⁻¹) ^ 4
        * (1 + ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / max (znorm (u - y)) (max M N)) := by
  classical
  set S := max (znorm (u - y)) (max M N) with hS
  have hMS : M ≤ S := le_trans (le_max_left M N) (le_max_right _ _)
  have hS0 : (0 : ℝ) < S := lt_of_lt_of_le (lt_of_lt_of_le one_pos hM) hMS
  have hyS : znorm (u - y) ≤ S := le_max_left _ _
  set Φ := A.filter (fun x => M ≤ znorm (u - x) ∧ max M N ≤ znorm (x - y)) with hΦ
  have hΦA : Φ ⊆ A := Finset.filter_subset _ _
  have hΦfacts : ∀ x ∈ Φ, M ≤ znorm (u - x) ∧ max M N ≤ znorm (x - y) := by
    intro x hx; rw [hΦ, mem_filter] at hx; exact hx.2
  have hsplit1 := Finset.sum_filter_add_sum_filter_not Φ (fun x => znorm (u - x) ≤ 2 * S)
      (fun x => (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2)
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
      (Φ.filter (fun x => znorm (u - x) ≤ 2 * S)) (fun x => S / 4 ≤ znorm (x - y))
      (fun x => (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2)
  have ha1 : ∑ x ∈ (Φ.filter (fun x => znorm (u - x) ≤ 2 * S)).filter
        (fun x => S / 4 ≤ znorm (x - y)),
      (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2 ≤ 1048576/3 * (M⁻¹) ^ 4 := by
    refine case_a1_bound A M hM hsep u y S hMS _
      (fun x hx => hΦA (Finset.filter_subset _ _ (Finset.filter_subset _ _ hx))) ?_
    intro x hx
    rw [mem_filter] at hx
    obtain ⟨hx1, hq⟩ := hx
    rw [mem_filter] at hx1
    obtain ⟨hxΦ, hp⟩ := hx1
    exact ⟨(hΦfacts x hxΦ).1, hp, hq⟩
  have ha2 : ∑ x ∈ (Φ.filter (fun x => znorm (u - x) ≤ 2 * S)).filter
        (fun x => ¬ S / 4 ≤ znorm (x - y)),
      (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2 ≤ 16384/27 * (M⁻¹) ^ 4 := by
    refine case_a2_bound A M N hM hsep u y S hS _
      (fun x hx => hΦA (Finset.filter_subset _ _ (Finset.filter_subset _ _ hx))) ?_
    intro x hx
    rw [mem_filter] at hx
    obtain ⟨hx1, hq⟩ := hx
    rw [mem_filter] at hx1
    obtain ⟨hxΦ, -⟩ := hx1
    exact ⟨(hΦfacts x hxΦ).2, le_of_lt (not_le.mp hq)⟩
  have hb : ∑ x ∈ Φ.filter (fun x => ¬ znorm (u - x) ≤ 2 * S),
      (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
      ≤ 17480 * (M⁻¹) ^ 4 * (1 + ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / S) := by
    refine case_b_bound A M hM hsep u y S hMS hyS _
      (fun x hx => hΦA (Finset.filter_subset _ _ hx)) ?_
    intro x hx
    rw [mem_filter] at hx
    exact not_le.mp hx.2
  have hM4 : (0 : ℝ) ≤ (M⁻¹) ^ 4 := by positivity
  have hρnn : (0 : ℝ) ≤ ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / S :=
    div_nonneg (Real.rpow_nonneg (by positivity) _) (le_of_lt hS0)
  have hprod := mul_nonneg hM4 hρnn
  linarith [hsplit1, hsplit2, ha1, ha2, hb, hM4, hρnn, hprod]

/-! ### Stage 2: summation in `y`, small-`y` case (paper (5.66)–(5.67)) -/

/-- Fubini for the filtered bilinear sum: swap to `y`-outer form. -/
private lemma bilinear_swap (A B : Finset (Fin 4 → ℤ)) (M L : ℝ) (u : Fin 4 → ℤ)
    (f : (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℝ) :
    ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x)),
      ∑ y ∈ B.filter (fun y => L ≤ znorm (x - y)), f x y
    = ∑ y ∈ B, ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x) ∧ L ≤ znorm (x - y)), f x y := by
  classical
  calc ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x)),
        ∑ y ∈ B.filter (fun y => L ≤ znorm (x - y)), f x y
      = ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x)),
          ∑ y ∈ B, if L ≤ znorm (x - y) then f x y else 0 :=
        Finset.sum_congr rfl (fun x _ => Finset.sum_filter _ _)
    _ = ∑ y ∈ B, ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x)),
          if L ≤ znorm (x - y) then f x y else 0 := Finset.sum_comm
    _ = ∑ y ∈ B, ∑ x ∈ (A.filter (fun x => M ≤ znorm (u - x))).filter
          (fun x => L ≤ znorm (x - y)), f x y :=
        Finset.sum_congr rfl (fun y _ => (Finset.sum_filter _ _).symm)
    _ = ∑ y ∈ B, ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x) ∧ L ≤ znorm (x - y)), f x y := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.filter_filter]

/-- Under `Q ≤ P`: `|B|·M⁻⁴ ≤ |A|^{1/4}·M⁻³·|B|^{3/4}·N⁻¹` (the `(Q/P)^{1/2} ≤ (Q/P)^{1/4}`
step of (5.65)). -/
private lemma B_M4_le (A B : Finset (Fin 4 → ℤ)) (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hQP : (B.card : ℝ) * N ^ 4 ≤ (A.card : ℝ) * M ^ 4) :
    (B.card : ℝ) * (M⁻¹) ^ 4
      ≤ (A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹ := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
  have hM' : M ≠ 0 := ne_of_gt hM0
  have hq : ((B.card : ℝ) * N ^ 4) ^ (1/4 : ℝ) ≤ ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hQP (by norm_num)
  rw [rpow_quarter_mul_pow4 _ _ (by positivity) (le_of_lt hN0),
    rpow_quarter_mul_pow4 _ _ (by positivity) (le_of_lt hM0)] at hq
  have hsplit : (B.card : ℝ) = (B.card : ℝ) ^ (3/4 : ℝ) * (B.card : ℝ) ^ (1/4 : ℝ) :=
    (rpow_34_add_14 _ (by positivity)).symm
  have hkey : (B.card : ℝ) ^ (1/4 : ℝ) * N * ((B.card : ℝ) ^ (3/4 : ℝ) * (M⁻¹) ^ 4 * N⁻¹)
      ≤ (A.card : ℝ) ^ (1/4 : ℝ) * M * ((B.card : ℝ) ^ (3/4 : ℝ) * (M⁻¹) ^ 4 * N⁻¹) :=
    mul_le_mul_of_nonneg_right hq
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity))
        (by positivity))
  have hMM : M * (M⁻¹) ^ 4 = (M⁻¹) ^ 3 := by
    have h4 : (M⁻¹) ^ 4 = (M⁻¹) ^ 3 * M⁻¹ := by ring
    rw [h4, show M * ((M⁻¹) ^ 3 * M⁻¹) = (M⁻¹) ^ 3 * (M * M⁻¹) from by ring,
      mul_inv_cancel₀ hM', mul_one]
  calc (B.card : ℝ) * (M⁻¹) ^ 4
      = (B.card : ℝ) ^ (1/4 : ℝ) * N * ((B.card : ℝ) ^ (3/4 : ℝ) * (M⁻¹) ^ 4 * N⁻¹) := by
        rw [show (B.card : ℝ) ^ (1/4 : ℝ) * N * ((B.card : ℝ) ^ (3/4 : ℝ) * (M⁻¹) ^ 4 * N⁻¹)
          = ((B.card : ℝ) ^ (3/4 : ℝ) * (B.card : ℝ) ^ (1/4 : ℝ)) * (M⁻¹) ^ 4 * (N * N⁻¹)
          by ring, ← hsplit, mul_inv_cancel₀ (ne_of_gt hN0), mul_one]
    _ ≤ (A.card : ℝ) ^ (1/4 : ℝ) * M * ((B.card : ℝ) ^ (3/4 : ℝ) * (M⁻¹) ^ 4 * N⁻¹) := hkey
    _ = (A.card : ℝ) ^ (1/4 : ℝ) * (M * (M⁻¹) ^ 4) * ((B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹) := by
        ring
    _ = (A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹ := by
        rw [hMM]; ring

/-- `P^{1/4}·M⁻⁴ = |A|^{1/4}·M⁻³`. -/
private lemma P_M4 (A : Finset (Fin 4 → ℤ)) (M : ℝ) (hM0 : 0 < M) :
    ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) * (M⁻¹) ^ 4
      = (A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 := by
  have hM' : M ≠ 0 := ne_of_gt hM0
  rw [rpow_quarter_mul_pow4 _ _ (Nat.cast_nonneg _) (le_of_lt hM0)]
  have h4 : (M⁻¹) ^ 4 = (M⁻¹) ^ 3 * M⁻¹ := by ring
  rw [show (A.card : ℝ) ^ (1/4 : ℝ) * M * (M⁻¹) ^ 4
      = (A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (M * M⁻¹) from by rw [h4]; ring,
    mul_inv_cancel₀ hM', mul_one]

/-- Count of `y ∈ B` in the ball `|u-y| ≤ L` (`L ≥ N`): `≤ 16·min(|B|, 16·(L/N)⁴)`. -/
private lemma small_count_le (B : Finset (Fin 4 → ℤ)) (N : ℝ) (hN : 1 ≤ N)
    (hsepB : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → N ≤ znorm (x - y)) (u : Fin 4 → ℤ)
    (L : ℝ) (hNL : N ≤ L) :
    ((B.filter (fun y => znorm (u - y) ≤ L)).card : ℝ)
      ≤ 16 * min (B.card : ℝ) (16 * (L / N) ^ 4) := by
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
  have h2 : (L / N + 1) ^ 4 ≤ 16 * (L / N) ^ 4 := by
    have hLN1 : (1 : ℝ) ≤ L / N := (one_le_div hN0).mpr hNL
    have h3 : L / N + 1 ≤ 2 * (L / N) := by linarith
    calc (L / N + 1) ^ 4 ≤ (2 * (L / N)) ^ 4 := pow_le_pow_left₀ (by positivity) h3 4
      _ = 16 * (L / N) ^ 4 := by ring
  calc ((B.filter (fun y => znorm (u - y) ≤ L)).card : ℝ)
      ≤ 16 * min (B.card : ℝ) ((L / N + 1) ^ 4) := card_ball_center_le u B N hN hsepB L
    _ ≤ 16 * min (B.card : ℝ) (16 * (L / N) ^ 4) :=
        mul_le_mul_of_nonneg_left (min_le_min le_rfl h2) (by norm_num)

/-- Interpolated count: `#{y ∈ B : |u-y| ≤ L} ≤ 32·|B|^{3/4}·(L/N)` (`L ≥ N ≥ 1`). -/
private lemma small_count_rpow_le (B : Finset (Fin 4 → ℤ)) (N : ℝ) (hN : 1 ≤ N)
    (hsepB : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → N ≤ znorm (x - y)) (u : Fin 4 → ℤ)
    (L : ℝ) (hNL : N ≤ L) :
    ((B.filter (fun y => znorm (u - y) ≤ L)).card : ℝ)
      ≤ 32 * (B.card : ℝ) ^ (3/4 : ℝ) * (L / N) := by
  have hmin : min (B.card : ℝ) (16 * (L / N) ^ 4)
      ≤ (B.card : ℝ) ^ (3/4 : ℝ) * ((16 : ℝ) * (L / N) ^ 4) ^ (1/4 : ℝ) :=
    min_le_rpow34 _ _ (Nat.cast_nonneg _) (by positivity)
  have h16q : (16 : ℝ) ^ (1/4 : ℝ) = 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, rpow_quarter_pow4 2 (by norm_num)]
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
  have hLN0 : (0 : ℝ) ≤ L / N := div_nonneg (le_trans (le_of_lt hN0) hNL) (le_of_lt hN0)
  have h164 : ((16 : ℝ) * (L / N) ^ 4) ^ (1/4 : ℝ) = 2 * (L / N) := by
    rw [rpow_quarter_mul_pow4 16 (L / N) (by norm_num) hLN0, h16q]
  calc ((B.filter (fun y => znorm (u - y) ≤ L)).card : ℝ)
      ≤ 16 * min (B.card : ℝ) (16 * (L / N) ^ 4) := small_count_le B N hN hsepB u L hNL
    _ ≤ 16 * ((B.card : ℝ) ^ (3/4 : ℝ) * (2 * (L / N))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [← h164]; exact hmin
    _ = 32 * (B.card : ℝ) ^ (3/4 : ℝ) * (L / N) := by ring

/-- **Stage 2 (paper (5.66)–(5.67)).**  Summing the pointwise bound (5.63) over the `y`
with `max(|u-y|, M, N) = max(M, N)`, under `Q ≤ P`, meets the `S`-target
`|A|^{1/4}·M⁻³·|B|^{3/4}·N⁻¹`. -/
theorem S_bound_smallcases (A B : Finset (Fin 4 → ℤ)) (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hsepB : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → N ≤ znorm (x - y)) (u : Fin 4 → ℤ)
    (hQP : (B.card : ℝ) * N ^ 4 ≤ (A.card : ℝ) * M ^ 4) :
    ∑ y ∈ B.filter (fun y => znorm (u - y) ≤ max M N),
      524288 * (M⁻¹) ^ 4
        * (1 + ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / max (znorm (u - y)) (max M N))
    ≤ 48 * 524288
        * ((A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹) := by
  classical
  have hNL : N ≤ max M N := le_max_right M N
  have hL1 : (1 : ℝ) ≤ max M N := le_trans hN hNL
  have hL0 : (0 : ℝ) < max M N := lt_of_lt_of_le one_pos hL1
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hP4nn : (0 : ℝ) ≤ ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  set Bs := B.filter (fun y => znorm (u - y) ≤ max M N) with hBs
  have hsum_eq : ∑ y ∈ Bs, 524288 * (M⁻¹) ^ 4
        * (1 + ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / max (znorm (u - y)) (max M N))
      = (Bs.card : ℝ) * (524288 * (M⁻¹) ^ 4
          * (1 + ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / max M N)) := by
    rw [Finset.sum_congr rfl (fun y hy => ?_), Finset.sum_const, nsmul_eq_mul]
    rw [hBs, mem_filter] at hy
    rw [max_eq_right hy.2]
  have hpart1 : (Bs.card : ℝ) * (524288 * (M⁻¹) ^ 4)
      ≤ 16 * 524288
        * ((A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹) := by
    calc (Bs.card : ℝ) * (524288 * (M⁻¹) ^ 4)
        ≤ (16 * (B.card : ℝ)) * (524288 * (M⁻¹) ^ 4) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc (Bs.card : ℝ)
              ≤ 16 * min (B.card : ℝ) (16 * (max M N / N) ^ 4) :=
                small_count_le B N hN hsepB u (max M N) hNL
            _ ≤ 16 * (B.card : ℝ) :=
                mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
      _ = 16 * 524288 * ((B.card : ℝ) * (M⁻¹) ^ 4) := by ring
      _ ≤ 16 * 524288
            * ((A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹) :=
          mul_le_mul_of_nonneg_left (B_M4_le A B M N hM hN hQP) (by norm_num)
  have hpart2 : (Bs.card : ℝ)
        * (524288 * (M⁻¹) ^ 4 * (((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / max M N))
      ≤ 32 * 524288
        * ((A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹) := by
    have hc2 := small_count_rpow_le B N hN hsepB u (max M N) hNL
    have hfac : (0 : ℝ) ≤ 524288 * (M⁻¹) ^ 4
        * (((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / max M N) :=
      mul_nonneg (by positivity) (div_nonneg hP4nn (le_of_lt hL0))
    calc (Bs.card : ℝ)
          * (524288 * (M⁻¹) ^ 4 * (((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / max M N))
        ≤ (32 * (B.card : ℝ) ^ (3/4 : ℝ) * (max M N / N))
            * (524288 * (M⁻¹) ^ 4 * (((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / max M N)) :=
          mul_le_mul_of_nonneg_right hc2 hfac
      _ = 32 * 524288 * (((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) * (M⁻¹) ^ 4)
            * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹ * (max M N * (max M N)⁻¹) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      _ = 32 * 524288
            * ((A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹) := by
          rw [mul_inv_cancel₀ (ne_of_gt hL0), mul_one, P_M4 A M hM0]; ring
  calc ∑ y ∈ Bs, 524288 * (M⁻¹) ^ 4
        * (1 + ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / max (znorm (u - y)) (max M N))
      = (Bs.card : ℝ) * (524288 * (M⁻¹) ^ 4)
        + (Bs.card : ℝ)
          * (524288 * (M⁻¹) ^ 4 * (((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / max M N)) := by
        rw [hsum_eq]; ring
    _ ≤ 48 * 524288
          * ((A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹) := by
        have := add_le_add hpart1 hpart2
        linarith

/-! ### Stage 3: summation in `y`, case `max = |u-y|` (paper (5.65)) -/

private lemma mul_div_rpow34 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    b * (a / b) ^ (3/4 : ℝ) = a ^ (3/4 : ℝ) * b ^ (1/4 : ℝ) := by
  have hb34 : (0 : ℝ) < b ^ (3/4 : ℝ) := Real.rpow_pos_of_pos hb _
  have hbq : b / b ^ (3/4 : ℝ) = b ^ (1/4 : ℝ) := by
    rw [div_eq_iff (ne_of_gt hb34), mul_comm]
    exact (rpow_34_add_14 b (le_of_lt hb)).symm
  calc b * (a / b) ^ (3/4 : ℝ) = b * (a ^ (3/4 : ℝ) / b ^ (3/4 : ℝ)) := by
        rw [Real.div_rpow (le_of_lt ha) (le_of_lt hb)]
    _ = a ^ (3/4 : ℝ) * (b / b ^ (3/4 : ℝ)) := by ring
    _ = a ^ (3/4 : ℝ) * b ^ (1/4 : ℝ) := by rw [hbq]

private lemma mul_div_rpow14 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a * (b / a) ^ (1/4 : ℝ) = a ^ (3/4 : ℝ) * b ^ (1/4 : ℝ) := by
  have ha14 : (0 : ℝ) < a ^ (1/4 : ℝ) := Real.rpow_pos_of_pos ha _
  have haq : a / a ^ (1/4 : ℝ) = a ^ (3/4 : ℝ) := by
    rw [div_eq_iff (ne_of_gt ha14)]
    exact (rpow_34_add_14 a (le_of_lt ha)).symm
  calc a * (b / a) ^ (1/4 : ℝ) = a * (b ^ (1/4 : ℝ) / a ^ (1/4 : ℝ)) := by
        rw [Real.div_rpow (le_of_lt hb) (le_of_lt ha)]
    _ = (a / a ^ (1/4 : ℝ)) * b ^ (1/4 : ℝ) := by ring
    _ = a ^ (3/4 : ℝ) * b ^ (1/4 : ℝ) := by rw [haq]

private lemma dyadic34_part1 (a b : ℝ) (hapos : 0 < a) (hbpos : 0 < b) (n : ℕ) :
    ∑ k ∈ (Finset.range n).filter (fun k => b * (8 : ℝ) ^ k ≤ a * ((2 : ℝ) ^ k)⁻¹),
      min (a * ((2 : ℝ) ^ k)⁻¹) (b * (8 : ℝ) ^ k) ≤ 2 * (a ^ (3/4 : ℝ) * b ^ (1/4 : ℝ)) := by
  classical
  set J := (Finset.range n).filter (fun k => b * (8 : ℝ) ^ k ≤ a * ((2 : ℝ) ^ k)⁻¹) with hJ
  rcases J.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (Real.rpow_nonneg (le_of_lt hapos) _) (Real.rpow_nonneg (le_of_lt hbpos) _))
  · have hub : ∀ j ∈ J, j ≤ J.max' hne := fun j hj => Finset.le_max' _ j hj
    have hmm : b * (8 : ℝ) ^ (J.max' hne) ≤ a * ((2 : ℝ) ^ (J.max' hne))⁻¹ :=
      (mem_filter.mp (J.max'_mem hne)).2
    have h16 : (16 : ℝ) ^ (J.max' hne) ≤ a / b := by
      rw [le_div_iff₀ hbpos]
      have h2m : (0 : ℝ) < (2 : ℝ) ^ (J.max' hne) := by positivity
      have hcancel : a * ((2 : ℝ) ^ (J.max' hne))⁻¹ * (2 : ℝ) ^ (J.max' hne) = a := by
        rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt h2m), mul_one]
      have hstep := mul_le_mul_of_nonneg_right hmm (le_of_lt h2m)
      rw [hcancel] at hstep
      have h82 : b * (8 : ℝ) ^ (J.max' hne) * (2 : ℝ) ^ (J.max' hne)
          = b * 16 ^ (J.max' hne) := by
        rw [mul_assoc, ← mul_pow]; norm_num
      rw [h82] at hstep
      linarith
    have h8m : (8 : ℝ) ^ (J.max' hne) ≤ (a / b) ^ (3/4 : ℝ) := by
      rw [← pow16_rpow_threequarter]
      exact Real.rpow_le_rpow (by positivity) h16 (by norm_num)
    calc ∑ k ∈ J, min (a * ((2 : ℝ) ^ k)⁻¹) (b * (8 : ℝ) ^ k)
        ≤ ∑ k ∈ J, b * (8 : ℝ) ^ k := Finset.sum_le_sum (fun k _ => min_le_right _ _)
      _ ≤ b * (8 : ℝ) ^ (J.max' hne) * (8 / (8 - 1)) :=
          geom_incr_le 8 b (by norm_num) (le_of_lt hbpos) J _ hub
      _ ≤ b * (a / b) ^ (3/4 : ℝ) * 2 := by
          have hb8 : b * (8 : ℝ) ^ (J.max' hne) ≤ b * (a / b) ^ (3/4 : ℝ) :=
            mul_le_mul_of_nonneg_left h8m (le_of_lt hbpos)
          have hbnn : (0 : ℝ) ≤ b * (8 : ℝ) ^ (J.max' hne) :=
            mul_nonneg (le_of_lt hbpos) (by positivity)
          linarith
      _ = 2 * (a ^ (3/4 : ℝ) * b ^ (1/4 : ℝ)) := by rw [mul_div_rpow34 a b hapos hbpos]; ring

private lemma dyadic34_part2 (a b : ℝ) (hapos : 0 < a) (hbpos : 0 < b) (n : ℕ) :
    ∑ k ∈ (Finset.range n).filter (fun k => ¬ b * (8 : ℝ) ^ k ≤ a * ((2 : ℝ) ^ k)⁻¹),
      min (a * ((2 : ℝ) ^ k)⁻¹) (b * (8 : ℝ) ^ k) ≤ 2 * (a ^ (3/4 : ℝ) * b ^ (1/4 : ℝ)) := by
  classical
  set J := (Finset.range n).filter (fun k => ¬ b * (8 : ℝ) ^ k ≤ a * ((2 : ℝ) ^ k)⁻¹) with hJ
  rcases J.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (Real.rpow_nonneg (le_of_lt hapos) _) (Real.rpow_nonneg (le_of_lt hbpos) _))
  · have hlb : ∀ j ∈ J, J.min' hne ≤ j := fun j hj => Finset.min'_le _ j hj
    have hsubn : J ⊆ Finset.range n := by rw [hJ]; exact Finset.filter_subset _ _
    have hmm : a * ((2 : ℝ) ^ (J.min' hne))⁻¹ < b * (8 : ℝ) ^ (J.min' hne) :=
      not_le.mp (mem_filter.mp (J.min'_mem hne)).2
    have h16 : a / b ≤ (16 : ℝ) ^ (J.min' hne) := by
      rw [div_le_iff₀ hbpos]
      have h2m : (0 : ℝ) < (2 : ℝ) ^ (J.min' hne) := by positivity
      have hcancel : a * ((2 : ℝ) ^ (J.min' hne))⁻¹ * (2 : ℝ) ^ (J.min' hne) = a := by
        rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt h2m), mul_one]
      have hstep := mul_le_mul_of_nonneg_right (le_of_lt hmm) (le_of_lt h2m)
      rw [hcancel] at hstep
      have h82 : b * (8 : ℝ) ^ (J.min' hne) * (2 : ℝ) ^ (J.min' hne)
          = b * 16 ^ (J.min' hne) := by
        rw [mul_assoc, ← mul_pow]; norm_num
      rw [h82] at hstep
      linarith
    have hq : (a / b) ^ (1/4 : ℝ) ≤ (2 : ℝ) ^ (J.min' hne) := by
      rw [← pow16_rpow_quarter]
      exact Real.rpow_le_rpow (div_nonneg (le_of_lt hapos) (le_of_lt hbpos)) h16 (by norm_num)
    have hinv : ((2 : ℝ) ^ (J.min' hne))⁻¹ ≤ ((a / b) ^ (1/4 : ℝ))⁻¹ :=
      inv_anti₀ (Real.rpow_pos_of_pos (div_pos hapos hbpos) _) hq
    have hgoalm : a * ((2 : ℝ) ^ (J.min' hne))⁻¹ ≤ a ^ (3/4 : ℝ) * b ^ (1/4 : ℝ) := by
      calc a * ((2 : ℝ) ^ (J.min' hne))⁻¹ ≤ a * ((a / b) ^ (1/4 : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_left hinv (le_of_lt hapos)
        _ = a * (b / a) ^ (1/4 : ℝ) := by
            rw [← Real.inv_rpow (div_nonneg (le_of_lt hapos) (le_of_lt hbpos)), inv_div]
        _ = a ^ (3/4 : ℝ) * b ^ (1/4 : ℝ) := mul_div_rpow14 a b hapos hbpos
    calc ∑ k ∈ J, min (a * ((2 : ℝ) ^ k)⁻¹) (b * (8 : ℝ) ^ k)
        ≤ ∑ k ∈ J, a * ((2 : ℝ) ^ k)⁻¹ := Finset.sum_le_sum (fun k _ => min_le_left _ _)
      _ ≤ a * ((2 : ℝ) ^ (J.min' hne))⁻¹ * (2 / (2 - 1)) :=
          geom_decr_le 2 a (by norm_num) (le_of_lt hapos) n J hsubn _ hlb
      _ ≤ 2 * (a ^ (3/4 : ℝ) * b ^ (1/4 : ℝ)) := by
          have h0 : (0 : ℝ) ≤ a * ((2 : ℝ) ^ (J.min' hne))⁻¹ :=
            mul_nonneg (le_of_lt hapos) (by positivity)
          have h21 : (2 : ℝ) / (2 - 1) = 2 := by norm_num
          rw [h21]
          linarith

/-- Two-crossover geometric-min sum behind (5.65):
`∑_{k<n} min(a·2^{-k}, b·8^k) ≤ 4·a^{3/4}·b^{1/4}`. -/
private lemma dyadic_min_geom_sum_34 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    ∑ k ∈ Finset.range n, min (a * ((2 : ℝ) ^ k)⁻¹) (b * (8 : ℝ) ^ k)
      ≤ 4 * (a ^ (3/4 : ℝ) * b ^ (1/4 : ℝ)) := by
  classical
  have hRHSnn : (0 : ℝ) ≤ 4 * (a ^ (3/4 : ℝ) * b ^ (1/4 : ℝ)) :=
    mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _))
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · have hz : ∀ k ∈ Finset.range n, min (a * ((2 : ℝ) ^ k)⁻¹) (b * (8 : ℝ) ^ k) = 0 := by
      intro k _
      rw [← ha0, zero_mul]
      exact min_eq_left (mul_nonneg hb (by positivity))
    rw [Finset.sum_congr rfl hz, Finset.sum_const, smul_zero]
    exact hRHSnn
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · have hz : ∀ k ∈ Finset.range n, min (a * ((2 : ℝ) ^ k)⁻¹) (b * (8 : ℝ) ^ k) = 0 := by
      intro k _
      rw [← hb0, zero_mul]
      exact min_eq_right (mul_nonneg (le_of_lt hapos) (by positivity))
    rw [Finset.sum_congr rfl hz, Finset.sum_const, smul_zero]
    exact hRHSnn
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range n)
      (fun k => b * (8 : ℝ) ^ k ≤ a * ((2 : ℝ) ^ k)⁻¹)
      (fun k => min (a * ((2 : ℝ) ^ k)⁻¹) (b * (8 : ℝ) ^ k))
  have h1 := dyadic34_part1 a b hapos hbpos n
  have h2 := dyadic34_part2 a b hapos hbpos n
  linarith

/-- Per-shell estimate for the inverse-norm sum over an `N`-separated `B` at scale
`2^j·L` (`L ≥ N`): contribution `≤ 16·L⁻¹·min(|B|·2^{-j}, 256·(L/N)⁴·8^j)`. -/
private lemma fiber_sum1_le (B : Finset (Fin 4 → ℤ)) (N : ℝ) (hN : 1 ≤ N)
    (hsepB : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → N ≤ znorm (x - y)) (u : Fin 4 → ℤ)
    (L : ℝ) (hNL : N ≤ L) (j : ℕ) :
    ∑ y ∈ (B.filter (fun y => L ≤ znorm (u - y))).filter
        (fun y => Nat.log 2 ⌊znorm (u - y) / L⌋₊ = j), (znorm (u - y))⁻¹
      ≤ 16 * L⁻¹ * min ((B.card : ℝ) * ((2 : ℝ) ^ j)⁻¹)
          (256 * (L / N) ^ 4 * (8 : ℝ) ^ j) := by
  classical
  have hL1 : (1 : ℝ) ≤ L := le_trans hN hNL
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  set Fj := (B.filter (fun y => L ≤ znorm (u - y))).filter
      (fun y => Nat.log 2 ⌊znorm (u - y) / L⌋₊ = j) with hFj
  have hterm : ∀ y ∈ Fj, (znorm (u - y))⁻¹ ≤ ((2 : ℝ) ^ j)⁻¹ * L⁻¹ := by
    intro y hy
    rw [hFj, mem_filter] at hy
    obtain ⟨hyF, hlog⟩ := hy
    rw [mem_filter] at hyF
    have hbr := (dyadic_bracket' hL1 hyF.2).1
    rw [hlog] at hbr
    exact term_bound_one hL0 j hbr
  have hsub : Fj ⊆ B.filter (fun y => znorm (u - y) ≤ (2 : ℝ) ^ (j + 1) * L) := by
    intro y hy
    rw [hFj, mem_filter] at hy
    obtain ⟨hyF, hlog⟩ := hy
    rw [mem_filter] at hyF ⊢
    refine ⟨hyF.1, ?_⟩
    have hbr := (dyadic_bracket' hL1 hyF.2).2
    rw [hlog] at hbr
    exact le_of_lt hbr
  have hcard : ((Fj.card : ℝ)) ≤ 16 * min (B.card : ℝ) (256 * 16 ^ j * (L / N) ^ 4) := by
    calc ((Fj.card : ℝ))
        ≤ ((B.filter (fun y => znorm (u - y) ≤ (2 : ℝ) ^ (j + 1) * L)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ 16 * min (B.card : ℝ) (256 * 16 ^ j * (L / N) ^ 4) :=
          fiber_card_bound B N hN hsepB u L hNL j
  have hpow : (16 : ℝ) ^ j * ((2 : ℝ) ^ j)⁻¹ = 8 ^ j := by
    rw [show (16 : ℝ) ^ j = 8 ^ j * 2 ^ j from by rw [← mul_pow]; norm_num,
      mul_assoc, mul_inv_cancel₀ (by positivity : ((2 : ℝ) ^ j) ≠ 0), mul_one]
  have hminid : min ((B.card : ℝ)) (256 * 16 ^ j * (L / N) ^ 4) * (((2 : ℝ) ^ j)⁻¹ * L⁻¹)
      = L⁻¹ * min ((B.card : ℝ) * ((2 : ℝ) ^ j)⁻¹) (256 * (L / N) ^ 4 * (8 : ℝ) ^ j) := by
    rw [show min ((B.card : ℝ)) (256 * 16 ^ j * (L / N) ^ 4) * (((2 : ℝ) ^ j)⁻¹ * L⁻¹)
        = min ((B.card : ℝ)) (256 * 16 ^ j * (L / N) ^ 4) * ((2 : ℝ) ^ j)⁻¹ * L⁻¹
        from by ring,
      min_mul_of_nonneg _ _ (by positivity)]
    have h1682 : 256 * (16 : ℝ) ^ j * (L / N) ^ 4 * ((2 : ℝ) ^ j)⁻¹
        = 256 * (L / N) ^ 4 * (8 : ℝ) ^ j := by
      calc 256 * (16 : ℝ) ^ j * (L / N) ^ 4 * ((2 : ℝ) ^ j)⁻¹
          = 256 * (L / N) ^ 4 * ((16 : ℝ) ^ j * ((2 : ℝ) ^ j)⁻¹) := by ring
        _ = 256 * (L / N) ^ 4 * (8 : ℝ) ^ j := by rw [hpow]
    rw [h1682]
    ring
  calc ∑ y ∈ Fj, (znorm (u - y))⁻¹
      ≤ ∑ _y ∈ Fj, ((2 : ℝ) ^ j)⁻¹ * L⁻¹ := Finset.sum_le_sum hterm
    _ = (Fj.card : ℝ) * (((2 : ℝ) ^ j)⁻¹ * L⁻¹) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 16 * min ((B.card : ℝ)) (256 * 16 ^ j * (L / N) ^ 4) * (((2 : ℝ) ^ j)⁻¹ * L⁻¹) :=
        mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (by positivity) (inv_nonneg.mpr (le_of_lt hL0)))
    _ = 16 * L⁻¹ * min ((B.card : ℝ) * ((2 : ℝ) ^ j)⁻¹)
          (256 * (L / N) ^ 4 * (8 : ℝ) ^ j) := by
        rw [mul_assoc, hminid]
        ring

/-- Weighted count for (5.65): `∑_{y ∈ B, |u-y| ≥ L} |u-y|⁻¹ ≤ 256·|B|^{3/4}·N⁻¹`
for `N`-separated `B` and `L ≥ N ≥ 1`. -/
private lemma sum_inv_norm_le (B : Finset (Fin 4 → ℤ)) (N : ℝ) (hN : 1 ≤ N)
    (hsepB : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → N ≤ znorm (x - y)) (u : Fin 4 → ℤ)
    (L : ℝ) (hNL : N ≤ L) :
    ∑ y ∈ B.filter (fun y => L ≤ znorm (u - y)), (znorm (u - y))⁻¹
      ≤ 256 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹ := by
  classical
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
  have hL1 : (1 : ℝ) ≤ L := le_trans hN hNL
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  set F := B.filter (fun y => L ≤ znorm (u - y)) with hF
  set K := F.sup (fun y => Nat.log 2 ⌊znorm (u - y) / L⌋₊) with hK
  have hmapsK : ∀ y ∈ F, Nat.log 2 ⌊znorm (u - y) / L⌋₊ ∈ Finset.range (K + 1) := by
    intro y hy
    rw [Finset.mem_range]
    have hle : Nat.log 2 ⌊znorm (u - y) / L⌋₊ ≤ K :=
      Finset.le_sup (f := fun y => Nat.log 2 ⌊znorm (u - y) / L⌋₊) hy
    omega
  have h2564 : ((256 : ℝ) * (L / N) ^ 4) ^ (1/4 : ℝ) = 4 * (L / N) := by
    rw [rpow_quarter_mul_pow4 256 (L / N) (by norm_num)
        (div_nonneg (le_of_lt hL0) (le_of_lt hN0)),
      show (256 : ℝ) ^ (1/4 : ℝ) = 4 from by
        rw [show (256 : ℝ) = 4 ^ (4 : ℕ) by norm_num, rpow_quarter_pow4 4 (by norm_num)]]
  calc ∑ y ∈ F, (znorm (u - y))⁻¹
      = ∑ j ∈ Finset.range (K + 1),
          ∑ y ∈ F.filter (fun y => Nat.log 2 ⌊znorm (u - y) / L⌋₊ = j),
          (znorm (u - y))⁻¹ :=
        (Finset.sum_fiberwise_of_maps_to hmapsK _).symm
    _ ≤ ∑ j ∈ Finset.range (K + 1), 16 * L⁻¹
          * min ((B.card : ℝ) * ((2 : ℝ) ^ j)⁻¹) (256 * (L / N) ^ 4 * (8 : ℝ) ^ j) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have h := fiber_sum1_le B N hN hsepB u L hNL j
        rw [← hF] at h
        exact h
    _ = 16 * L⁻¹ * ∑ j ∈ Finset.range (K + 1),
          min ((B.card : ℝ) * ((2 : ℝ) ^ j)⁻¹) (256 * (L / N) ^ 4 * (8 : ℝ) ^ j) := by
        rw [Finset.mul_sum]
    _ ≤ 16 * L⁻¹
          * (4 * ((B.card : ℝ) ^ (3/4 : ℝ) * ((256 : ℝ) * (L / N) ^ 4) ^ (1/4 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (dyadic_min_geom_sum_34 _ _ (Nat.cast_nonneg _) (by positivity) (K + 1))
          (mul_nonneg (by norm_num) (inv_nonneg.mpr (le_of_lt hL0)))
    _ = 256 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹ * (L⁻¹ * L) := by
        rw [h2564, div_eq_mul_inv]
        ring
    _ = 256 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹ := by
        rw [inv_mul_cancel₀ (ne_of_gt hL0), mul_one]

/-- **Stage 3 (paper (5.65)).**  Summing the pointwise bound (5.63) over the `y` with
`max(|u-y|, M, N) = |u-y|`, under `Q ≤ P`, meets the `S`-target. -/
theorem S_bound_largecase (A B : Finset (Fin 4 → ℤ)) (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hsepB : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → N ≤ znorm (x - y)) (u : Fin 4 → ℤ)
    (hQP : (B.card : ℝ) * N ^ 4 ≤ (A.card : ℝ) * M ^ 4) :
    ∑ y ∈ B.filter (fun y => ¬ znorm (u - y) ≤ max M N),
      524288 * (M⁻¹) ^ 4
        * (1 + ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / max (znorm (u - y)) (max M N))
    ≤ 257 * 524288
        * ((A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹) := by
  classical
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hNL : N ≤ max M N := le_max_right M N
  set P4 := ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) with hP4
  have hP4nn : (0 : ℝ) ≤ P4 := by
    rw [hP4]; exact Real.rpow_nonneg (by positivity) _
  have hP4eq : P4 * (M⁻¹) ^ 4 = (A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 := by
    rw [hP4]; exact P_M4 A M hM0
  set Bl := B.filter (fun y => ¬ znorm (u - y) ≤ max M N) with hBl
  have hpt : ∀ y ∈ Bl, 524288 * (M⁻¹) ^ 4 * (1 + P4 / max (znorm (u - y)) (max M N))
      = 524288 * (M⁻¹) ^ 4 + 524288 * (M⁻¹) ^ 4 * P4 * (znorm (u - y))⁻¹ := by
    intro y hy
    rw [hBl, mem_filter] at hy
    have hlt : max M N < znorm (u - y) := not_le.mp hy.2
    rw [max_eq_left (le_of_lt hlt), div_eq_mul_inv]
    ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
  have hpart1 : ∑ _y ∈ Bl, 524288 * (M⁻¹) ^ 4
      ≤ 524288 * ((A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    calc (Bl.card : ℝ) * (524288 * (M⁻¹) ^ 4)
        ≤ (B.card : ℝ) * (524288 * (M⁻¹) ^ 4) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast Finset.card_filter_le B _
      _ = 524288 * ((B.card : ℝ) * (M⁻¹) ^ 4) := by ring
      _ ≤ 524288
            * ((A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹) :=
          mul_le_mul_of_nonneg_left (B_M4_le A B M N hM hN hQP) (by norm_num)
  have hpart2 : ∑ y ∈ Bl, 524288 * (M⁻¹) ^ 4 * P4 * (znorm (u - y))⁻¹
      ≤ 256 * 524288
        * ((A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹) := by
    rw [show ∑ y ∈ Bl, 524288 * (M⁻¹) ^ 4 * P4 * (znorm (u - y))⁻¹
        = 524288 * (M⁻¹) ^ 4 * P4 * ∑ y ∈ Bl, (znorm (u - y))⁻¹ from by
      rw [Finset.mul_sum]]
    have hsum : ∑ y ∈ Bl, (znorm (u - y))⁻¹
        ≤ 256 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹ := by
      calc ∑ y ∈ Bl, (znorm (u - y))⁻¹
          ≤ ∑ y ∈ B.filter (fun y => max M N ≤ znorm (u - y)), (znorm (u - y))⁻¹ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_
              (fun y _ _ => inv_nonneg.mpr (znorm_nonneg _))
            intro y hy
            rw [hBl, mem_filter] at hy
            rw [mem_filter]
            exact ⟨hy.1, le_of_lt (not_le.mp hy.2)⟩
        _ ≤ 256 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹ :=
            sum_inv_norm_le B N hN hsepB u (max M N) hNL
    calc 524288 * (M⁻¹) ^ 4 * P4 * ∑ y ∈ Bl, (znorm (u - y))⁻¹
        ≤ 524288 * (M⁻¹) ^ 4 * P4 * (256 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg (by positivity) hP4nn)
      _ = 256 * 524288 * ((P4 * (M⁻¹) ^ 4) * ((B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹)) := by ring
      _ = 256 * 524288
            * ((A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹) := by
          rw [hP4eq]; ring
  linarith

/-! ### Stage 4: assembly of the refined (5.58) -/

/-- For nonempty `A`: `|A|^{1/4}M⁻³|B|^{3/4}N⁻¹ = √|A|·M⁻²·√|B|·N⁻²·(Q/P)^{1/4}`. -/
private lemma S_target_eq (A B : Finset (Fin 4 → ℤ)) (M N : ℝ) (hM0 : 0 < M) (hN0 : 0 < N)
    (hA0 : (0 : ℝ) < (A.card : ℝ)) :
    (A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹
      = Real.sqrt (A.card : ℝ) * (M⁻¹) ^ 2 * Real.sqrt (B.card : ℝ) * (N⁻¹) ^ 2
        * ((((B.card : ℝ) * N ^ 4) / ((A.card : ℝ) * M ^ 4)) ^ (1/4 : ℝ)) := by
  have hP0 : (0 : ℝ) < (A.card : ℝ) * M ^ 4 := mul_pos hA0 (by positivity)
  have hQnn : (0 : ℝ) ≤ (B.card : ℝ) * N ^ 4 := by positivity
  have hdiv : (((B.card : ℝ) * N ^ 4) / ((A.card : ℝ) * M ^ 4)) ^ (1/4 : ℝ)
      = (B.card : ℝ) ^ (1/4 : ℝ) * N * ((A.card : ℝ) ^ (1/4 : ℝ) * M)⁻¹ := by
    rw [Real.div_rpow hQnn (le_of_lt hP0),
      rpow_quarter_mul_pow4 _ _ (Nat.cast_nonneg _) (le_of_lt hN0),
      rpow_quarter_mul_pow4 _ _ (Nat.cast_nonneg _) (le_of_lt hM0), div_eq_mul_inv]
  rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) B.card) with hB0 | hBpos
  · rw [← hB0, Real.zero_rpow (by norm_num : (3/4 : ℝ) ≠ 0), Real.sqrt_zero, zero_mul,
      zero_div, Real.zero_rpow (by norm_num : (1/4 : ℝ) ≠ 0)]
    ring
  · have hA14 : (0 : ℝ) < (A.card : ℝ) ^ (1/4 : ℝ) := Real.rpow_pos_of_pos hA0 _
    have h2A : Real.sqrt (A.card : ℝ)
        = (A.card : ℝ) ^ (1/4 : ℝ) * (A.card : ℝ) ^ (1/4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hA0]; norm_num
    have h2B : Real.sqrt (B.card : ℝ) * (B.card : ℝ) ^ (1/4 : ℝ)
        = (B.card : ℝ) ^ (3/4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hBpos]; norm_num
    have hMM : (M⁻¹) ^ 2 * M⁻¹ = (M⁻¹) ^ 3 := by ring
    have hNN : (N⁻¹) ^ 2 * N = N⁻¹ := by
      rw [pow_two, mul_assoc, inv_mul_cancel₀ (ne_of_gt hN0), mul_one]
    have hAc : (A.card : ℝ) ^ (1/4 : ℝ) * ((A.card : ℝ) ^ (1/4 : ℝ))⁻¹ = 1 :=
      mul_inv_cancel₀ (ne_of_gt hA14)
    rw [hdiv, h2A, mul_inv]
    symm
    calc (A.card : ℝ) ^ (1/4 : ℝ) * (A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 2
          * Real.sqrt (B.card : ℝ) * (N⁻¹) ^ 2
          * ((B.card : ℝ) ^ (1/4 : ℝ) * N * (((A.card : ℝ) ^ (1/4 : ℝ))⁻¹ * M⁻¹))
        = ((A.card : ℝ) ^ (1/4 : ℝ) * (((A.card : ℝ) ^ (1/4 : ℝ))
              * ((A.card : ℝ) ^ (1/4 : ℝ))⁻¹))
            * (Real.sqrt (B.card : ℝ) * (B.card : ℝ) ^ (1/4 : ℝ))
            * ((M⁻¹) ^ 2 * M⁻¹) * ((N⁻¹) ^ 2 * N) := by ring
      _ = (A.card : ℝ) ^ (1/4 : ℝ) * (B.card : ℝ) ^ (3/4 : ℝ) * (M⁻¹) ^ 3 * N⁻¹ := by
          rw [hAc, mul_one, h2B, hMM, hNN]
      _ = (A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹ := by
          ring

/-- **Bilinear cluster `S`-bound (the `Q ≤ P` case of (5.58)).**  For `M`-separated `A`,
`N`-separated `B`, `M, N ≥ 1`, any `u`, under `Q = |B|N⁴ ≤ P = |A|M⁴`:
`∑∑ 𝟙·𝟙·|u-x|⁻²|x-y|⁻² ≤ C·|A|^{1/4}·M⁻³·|B|^{3/4}·N⁻¹`. -/
theorem bilinear_cluster_S_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : Finset (Fin 4 → ℤ)) (M N : ℝ), 1 ≤ M → 1 ≤ N →
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → M ≤ znorm (x - y)) →
      (∀ x ∈ B, ∀ y ∈ B, x ≠ y → N ≤ znorm (x - y)) → ∀ (u : Fin 4 → ℤ),
      (B.card : ℝ) * N ^ 4 ≤ (A.card : ℝ) * M ^ 4 →
      ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x)),
        ∑ y ∈ B.filter (fun y => max M N ≤ znorm (x - y)),
          (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
        ≤ C * (A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹ := by
  refine ⟨305 * 524288, by norm_num, ?_⟩
  intro A B M N hM hN hsepA hsepB u hQP
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not B (fun y => znorm (u - y) ≤ max M N)
      (fun y => 524288 * (M⁻¹) ^ 4
        * (1 + ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / max (znorm (u - y)) (max M N)))
  have hsmall := S_bound_smallcases A B M N hM hN hsepB u hQP
  have hlarge := S_bound_largecase A B M N hM hN hsepB u hQP
  calc ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x)),
        ∑ y ∈ B.filter (fun y => max M N ≤ znorm (x - y)),
          (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
      = ∑ y ∈ B, ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x) ∧ max M N ≤ znorm (x - y)),
          (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2 :=
        bilinear_swap A B M (max M N) u _
    _ ≤ ∑ y ∈ B, 524288 * (M⁻¹) ^ 4
          * (1 + ((A.card : ℝ) * M ^ 4) ^ (1/4 : ℝ) / max (znorm (u - y)) (max M N)) :=
        Finset.sum_le_sum (fun y _ => single_y_bound A M N hM hsepA u y)
    _ ≤ 305 * 524288
          * ((A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹) := by
        rw [← hsplit]
        linarith
    _ = 305 * 524288 * (A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ)
          * N⁻¹ := by ring

/-- **Refined bilinear cluster bound, paper (5.58) (Lemma 5.14).**  For `M`-separated
`A`, `N`-separated `B` (`M, N ≥ 1`) and any `u`,
`∑∑ 𝟙_{|u-x| ≥ M}·𝟙_{|x-y| ≥ max(M,N)}·|u-x|⁻²|x-y|⁻²
   ≤ C·|A|^{1/2}M⁻²·|B|^{1/2}N⁻²·min(1, (Q/P)^{1/4})`,
`P = |A|M⁴`, `Q = |B|N⁴` (with Lean's `x/0 = 0` convention when `A = ∅`). -/
theorem bilinear_cluster_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : Finset (Fin 4 → ℤ)) (M N : ℝ), 1 ≤ M → 1 ≤ N →
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → M ≤ znorm (x - y)) →
      (∀ x ∈ B, ∀ y ∈ B, x ≠ y → N ≤ znorm (x - y)) → ∀ (u : Fin 4 → ℤ),
      ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x)),
        ∑ y ∈ B.filter (fun y => max M N ≤ znorm (x - y)),
          (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
        ≤ C * Real.sqrt (A.card : ℝ) * (M⁻¹) ^ 2 * Real.sqrt (B.card : ℝ) * (N⁻¹) ^ 2
            * min 1 ((((B.card : ℝ) * N ^ 4) / ((A.card : ℝ) * M ^ 4)) ^ (1/4 : ℝ)) := by
  obtain ⟨Cw, hCw0, hCw⟩ := bilinear_cluster_bound_weak
  obtain ⟨Cs, hCs0, hCs⟩ := bilinear_cluster_S_bound
  refine ⟨max Cw Cs, lt_max_of_lt_left hCw0, ?_⟩
  intro A B M N hM hN hsepA hsepB u
  classical
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
  have hCnn : (0 : ℝ) ≤ max Cw Cs := le_of_lt (lt_max_of_lt_left hCw0)
  rcases eq_or_ne A ∅ with rfl | hAne
  · rw [Finset.filter_empty, Finset.sum_empty]
    have hrnn : (0 : ℝ)
        ≤ (((B.card : ℝ) * N ^ 4) / (((∅ : Finset (Fin 4 → ℤ)).card : ℝ) * M ^ 4))
            ^ (1/4 : ℝ) :=
      Real.rpow_nonneg (div_nonneg (by positivity) (by positivity)) _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCnn
      (Real.sqrt_nonneg _)) (by positivity)) (Real.sqrt_nonneg _)) (by positivity))
      (le_min zero_le_one hrnn)
  · have hA0 : (0 : ℝ) < (A.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hAne)
    have hP0 : (0 : ℝ) < (A.card : ℝ) * M ^ 4 := mul_pos hA0 (by positivity)
    rcases le_total ((B.card : ℝ) * N ^ 4) ((A.card : ℝ) * M ^ 4) with hQP | hPQ
    · have hr1 : (((B.card : ℝ) * N ^ 4) / ((A.card : ℝ) * M ^ 4)) ^ (1/4 : ℝ) ≤ 1 :=
        Real.rpow_le_one (div_nonneg (by positivity) (le_of_lt hP0))
          ((div_le_one hP0).mpr hQP) (by norm_num)
      rw [min_eq_right hr1]
      have hrnn : (0 : ℝ) ≤ (((B.card : ℝ) * N ^ 4) / ((A.card : ℝ) * M ^ 4)) ^ (1/4 : ℝ) :=
        Real.rpow_nonneg (div_nonneg (by positivity) (le_of_lt hP0)) _
      calc ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x)),
            ∑ y ∈ B.filter (fun y => max M N ≤ znorm (x - y)),
              (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
          ≤ Cs * (A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹ :=
            hCs A B M N hM hN hsepA hsepB u hQP
        _ = Cs * ((A.card : ℝ) ^ (1/4 : ℝ) * (M⁻¹) ^ 3 * (B.card : ℝ) ^ (3/4 : ℝ) * N⁻¹) := by
            ring
        _ = Cs * (Real.sqrt (A.card : ℝ) * (M⁻¹) ^ 2 * Real.sqrt (B.card : ℝ) * (N⁻¹) ^ 2
              * ((((B.card : ℝ) * N ^ 4) / ((A.card : ℝ) * M ^ 4)) ^ (1/4 : ℝ))) := by
            rw [S_target_eq A B M N hM0 hN0 hA0]
        _ ≤ max Cw Cs * (Real.sqrt (A.card : ℝ) * (M⁻¹) ^ 2 * Real.sqrt (B.card : ℝ)
              * (N⁻¹) ^ 2
              * ((((B.card : ℝ) * N ^ 4) / ((A.card : ℝ) * M ^ 4)) ^ (1/4 : ℝ))) := by
            refine mul_le_mul_of_nonneg_right (le_max_right Cw Cs) ?_
            exact mul_nonneg (by positivity) hrnn
        _ = max Cw Cs * Real.sqrt (A.card : ℝ) * (M⁻¹) ^ 2 * Real.sqrt (B.card : ℝ)
              * (N⁻¹) ^ 2
              * ((((B.card : ℝ) * N ^ 4) / ((A.card : ℝ) * M ^ 4)) ^ (1/4 : ℝ)) := by
            ring
    · have h1r : (1 : ℝ) ≤ (((B.card : ℝ) * N ^ 4) / ((A.card : ℝ) * M ^ 4)) ^ (1/4 : ℝ) :=
        Real.one_le_rpow ((one_le_div hP0).mpr hPQ) (by norm_num)
      rw [min_eq_left h1r, mul_one]
      calc ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x)),
            ∑ y ∈ B.filter (fun y => max M N ≤ znorm (x - y)),
              (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
          ≤ Cw * Real.sqrt (A.card : ℝ) * (M⁻¹) ^ 2 * Real.sqrt (B.card : ℝ) * (N⁻¹) ^ 2 :=
            hCw A B M N hM hN hsepA hsepB u
        _ = Cw * (Real.sqrt (A.card : ℝ) * (M⁻¹) ^ 2 * Real.sqrt (B.card : ℝ)
              * (N⁻¹) ^ 2) := by ring
        _ ≤ max Cw Cs * (Real.sqrt (A.card : ℝ) * (M⁻¹) ^ 2 * Real.sqrt (B.card : ℝ)
              * (N⁻¹) ^ 2) :=
            mul_le_mul_of_nonneg_right (le_max_left Cw Cs) (by positivity)
        _ = max Cw Cs * Real.sqrt (A.card : ℝ) * (M⁻¹) ^ 2 * Real.sqrt (B.card : ℝ)
              * (N⁻¹) ^ 2 := by ring

end Anderson4D
