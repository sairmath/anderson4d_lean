import Mathlib

/-!
# Bilinear lattice-cluster bound (Lemma 5.14 of arXiv:2607.10105)

This file formalizes the PAPER_MAP node **L-5.14** of the Deng–Shen four-dimensional
Anderson model paper (Y. Deng, H. Shen, *The four-dimensional Anderson model: a case
study for critical SPDEs*, arXiv:2607.10105).  It provides:

* `card_shell_le` — the separated-points-in-a-ball packing/shell count, paper **(5.61)**;
* `sum_inv_sq_le` — the single-variable dyadic sum estimate, paper **(5.60)/(5.62)**;
* `bilinear_cluster_bound_weak` — the trivial-direction component of (5.58),
  obtained by iterating (5.60). The refined factor is proved in
  `LocalRefined.lean`.

## Design notes (project DESIGN §5.4)

* The ambient norm on `ℤ⁴` is fixed to the **sup norm** on `Fin 4 → ℝ` (mathlib's default
  `Pi` norm) applied to the real coercion of an integer vector; this is packaged as
  `Anderson4D.znorm`.  *All* constants below are norm-choice dependent and are absorbed
  into the named line-constants; the paper's `≳/≲` become explicit constants introduced
  existentially (single-use line constants) or the concrete value `16` in `card_shell_le`.
* **Powers.**  Half-powers `|A|^{1/2}` are written with `Real.sqrt`.  (The refined
  bound's quarter power `(Q/P)^{1/4}` would be `Real.rpow`, `· ^ (1/4 : ℝ)`; it is not
  present in the delivered `_weak` form.)
* **Indicators.**  The membership constraints `𝟙_{|u-x| ≳ M}` etc. are represented as
  `Finset.filter` on the summation domain (equivalently, sub-sums), not as `if … then 1`.
* The recurring **dyadic-decomposition** engine is factored into the reusable private
  lemmas `sum_geom_incr_le`, `sum_geom_decr_le`, `dyadic_min_geom_sum`.
-/

open scoped BigOperators
open Finset

namespace Anderson4D

/-- Sup-norm of an integer 4-vector `x : Fin 4 → ℤ`, defined via the real coercion
`(fun i => (x i : ℝ))` and mathlib's default `Pi` (sup) norm on `Fin 4 → ℝ`.
See paper §5.4; all constants below are relative to this choice. -/
def znorm (x : Fin 4 → ℤ) : ℝ := ‖(fun i => (x i : ℝ))‖

lemma znorm_nonneg (x : Fin 4 → ℤ) : 0 ≤ znorm x := norm_nonneg _

/-- Each coordinate is controlled by the sup norm. -/
lemma znorm_coord_le (x : Fin 4 → ℤ) (i : Fin 4) : |(x i : ℝ)| ≤ znorm x := by
  simpa only [znorm, Real.norm_eq_abs] using norm_le_pi_norm (fun j => (x j : ℝ)) i

/-- Coordinatewise bound for a difference. -/
lemma znorm_sub_coord (x y : Fin 4 → ℤ) (i : Fin 4) :
    |(x i : ℝ) - (y i : ℝ)| ≤ znorm (x - y) := by
  have h := znorm_coord_le (x - y) i
  simpa only [Pi.sub_apply, Int.cast_sub] using h

/-- The sup norm is `< M` iff every coordinate is. -/
lemma znorm_lt_iff (v : Fin 4 → ℤ) (M : ℝ) (hM : 0 < M) :
    znorm v < M ↔ ∀ i, |(v i : ℝ)| < M := by
  simp only [znorm, pi_norm_lt_iff hM, Real.norm_eq_abs]

/-- Reflection symmetry of `znorm`. -/
lemma znorm_neg (x : Fin 4 → ℤ) : znorm (-x) = znorm x := by
  unfold znorm
  rw [show (fun i => (((-x) i) : ℝ)) = -(fun i => ((x i) : ℝ)) by funext i; simp, norm_neg]

lemma znorm_sub_comm (x y : Fin 4 → ℤ) : znorm (x - y) = znorm (y - x) := by
  rw [← znorm_neg (y - x)]; congr 1; abel

/-- Helper: `((z.toNat : ℝ))^4 ≤ s^4` whenever `(z : ℝ) < s`.  Handles the sign of `z`
uniformly (used for the grid box-count in `card_ball_center_le`). -/
private lemma pow4_toNat_lt (z : ℤ) (s : ℝ) (h : (z : ℝ) < s) :
    ((z.toNat : ℝ)) ^ 4 ≤ s ^ 4 := by
  rcases le_total 0 z with hz | hz
  · have hcast : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hz
    rw [hcast]
    have hz0 : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    exact pow_le_pow_left₀ hz0 h.le 4
  · have h0 : z.toNat = 0 := Int.toNat_of_nonpos hz
    rw [h0, Nat.cast_zero, zero_pow (by norm_num)]
    positivity

/-- Multiplication distributes over `min` for nonnegative factors (right version). -/
private lemma min_mul_nonneg (a b c : ℝ) (hc : 0 ≤ c) :
    min a b * c = min (a * c) (b * c) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_right h hc)]
  · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_right h hc)]

/-- **Shell / packing count, paper (5.61)**, centered form.  A set `A` whose distinct
points are `M`-separated (`M ≤ znorm (x - y)`) meets the ball `{x : znorm (u - x) ≤ X}`
in at most `16 · min(|A|, (X/M + 1)⁴)` points.

Proof: the rounding map `x ↦ (fun i => ⌊(xᵢ - uᵢ)/M⌋)` is injective on an `M`-separated
set (two points in a common `M`-grid cell have sup-distance `< M`) and lands in a box of
at most `(2X/M + 2)⁴ = 16 (X/M + 1)⁴` cells; combined with the trivial bound `≤ |A|`. -/
theorem card_ball_center_le (u : Fin 4 → ℤ) (A : Finset (Fin 4 → ℤ)) (M : ℝ) (hM : 1 ≤ M)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → M ≤ znorm (x - y)) (X : ℝ) :
    ((A.filter fun x => znorm (u - x) ≤ X).card : ℝ)
      ≤ 16 * min (A.card : ℝ) ((X / M + 1) ^ 4) := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  -- box-count bound via the injective rounding map
  have hcard : ((A.filter fun x => znorm (u - x) ≤ X).card : ℝ) ≤ 16 * (X / M + 1) ^ 4 := by
    have hmaps : Set.MapsTo (fun x : Fin 4 → ℤ => (fun i => ⌊((x i : ℝ) - (u i : ℝ)) / M⌋))
        (↑(A.filter fun x => znorm (u - x) ≤ X))
        (↑(Fintype.piFinset (fun _ : Fin 4 => Finset.Icc ⌊(-X) / M⌋ ⌊X / M⌋))) := by
      intro x hxS
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      have hx : znorm (u - x) ≤ X := (mem_filter.mp hxS).2
      have hcoord : |(x i : ℝ) - (u i : ℝ)| ≤ X := by
        calc |(x i : ℝ) - (u i : ℝ)| = |(u i : ℝ) - (x i : ℝ)| := abs_sub_comm _ _
          _ ≤ znorm (u - x) := znorm_sub_coord u x i
          _ ≤ X := hx
      rw [abs_le] at hcoord
      refine ⟨Int.floor_le_floor ?_, Int.floor_le_floor ?_⟩
      · rw [div_le_div_iff_of_pos_right hM0]; linarith [hcoord.1]
      · rw [div_le_div_iff_of_pos_right hM0]; linarith [hcoord.2]
    have hinj : Set.InjOn (fun x : Fin 4 → ℤ => (fun i => ⌊((x i : ℝ) - (u i : ℝ)) / M⌋))
        (↑(A.filter fun x => znorm (u - x) ≤ X)) := by
      intro x hxS y hyS hxy
      by_contra hne
      have hxA : x ∈ A := (mem_filter.mp hxS).1
      have hyA : y ∈ A := (mem_filter.mp hyS).1
      have hsepxy : M ≤ znorm (x - y) := hsep x hxA y hyA hne
      have hlt : znorm (x - y) < M := by
        rw [znorm_lt_iff _ _ hM0]
        intro i
        have hfi : ⌊((x i : ℝ) - (u i : ℝ)) / M⌋ = ⌊((y i : ℝ) - (u i : ℝ)) / M⌋ :=
          congrFun hxy i
        have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hfi
        have h2 : ((x i : ℝ) - (u i : ℝ)) / M - ((y i : ℝ) - (u i : ℝ)) / M
            = ((x i : ℝ) - (y i : ℝ)) / M := by ring
        rw [h2, abs_div, abs_of_pos hM0, div_lt_one hM0] at h1
        simpa only [Pi.sub_apply, Int.cast_sub] using h1
      exact absurd hsepxy (not_le.mpr hlt)
    have hcnat : (A.filter fun x => znorm (u - x) ≤ X).card
        ≤ (Fintype.piFinset (fun _ : Fin 4 => Finset.Icc ⌊(-X) / M⌋ ⌊X / M⌋)).card :=
      Finset.card_le_card_of_injOn _ hmaps hinj
    have hzlt : ((⌊X / M⌋ + 1 - ⌊(-X) / M⌋ : ℤ) : ℝ) < 2 * (X / M) + 2 := by
      have hb : (⌊X / M⌋ : ℝ) ≤ X / M := Int.floor_le _
      have ha : (-X) / M - 1 < (⌊(-X) / M⌋ : ℝ) := Int.sub_one_lt_floor _
      have hne : (-X) / M = -(X / M) := by ring
      push_cast
      linarith [hb, ha, hne]
    calc ((A.filter fun x => znorm (u - x) ≤ X).card : ℝ)
        ≤ ((Fintype.piFinset (fun _ : Fin 4 => Finset.Icc ⌊(-X) / M⌋ ⌊X / M⌋)).card : ℝ) := by
          exact_mod_cast hcnat
      _ = ((⌊X / M⌋ + 1 - ⌊(-X) / M⌋ : ℤ).toNat : ℝ) ^ 4 := by
          rw [Fintype.card_piFinset_const, Int.card_Icc, Nat.cast_pow]
      _ ≤ (2 * (X / M) + 2) ^ 4 := pow4_toNat_lt _ _ hzlt
      _ = 16 * (X / M + 1) ^ 4 := by ring
  -- combine with the trivial `≤ |A|` bound to produce the `min`
  have htriv : ((A.filter fun x => znorm (u - x) ≤ X).card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast card_filter_le A _
  rcases min_cases (A.card : ℝ) ((X / M + 1) ^ 4) with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm]
  · linarith [htriv, Nat.cast_nonneg (α := ℝ) A.card]
  · exact hcard

/-- **Shell / packing count, paper (5.61)** (centered at the origin).  Special case of
`card_ball_center_le` with `u = 0`. -/
theorem card_shell_le (A : Finset (Fin 4 → ℤ)) (M : ℝ) (hM : 1 ≤ M)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → M ≤ znorm (x - y)) (X : ℝ) :
    ((A.filter fun x => znorm x ≤ X).card : ℝ)
      ≤ 16 * min (A.card : ℝ) ((X / M + 1) ^ 4) := by
  have h := card_ball_center_le 0 A M hM hsep X
  have heq : (A.filter fun x => znorm ((0 : Fin 4 → ℤ) - x) ≤ X)
      = A.filter (fun x => znorm x ≤ X) := by
    apply Finset.filter_congr
    intro x _
    simp only [zero_sub, znorm_neg]
  rwa [heq] at h

/-! ### Dyadic-decomposition engine for paper (5.62) -/

/-- `x ≤ √y` from `x ≥ 0` and `x² ≤ y`. -/
private lemma le_sqrt_of_sq_le {x y : ℝ} (hx : 0 ≤ x) (h : x ^ 2 ≤ y) : x ≤ Real.sqrt y := by
  rw [← Real.sqrt_sq hx]; exact Real.sqrt_le_sqrt h

private lemma two_pow_sq (kx : ℕ) : ((2 : ℝ) ^ kx) ^ 2 = (4 : ℝ) ^ kx := by
  rw [pow_two, ← mul_pow]; norm_num

/-- Single dyadic term bound: `t⁻² ≤ 4^{-k}·M⁻²` when `2^k·M ≤ t`. -/
private lemma term_bound {M t : ℝ} (hM0 : 0 < M) (kx : ℕ)
    (hlow : (2 : ℝ) ^ kx * M ≤ t) : t⁻¹ ^ 2 ≤ ((4 : ℝ) ^ kx)⁻¹ * (M⁻¹) ^ 2 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ kx * M := by positivity
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hpos hlow
  have h1 : t⁻¹ ≤ ((2 : ℝ) ^ kx * M)⁻¹ := inv_anti₀ hpos hlow
  have h2 : (0 : ℝ) ≤ t⁻¹ := le_of_lt (inv_pos.mpr ht0)
  calc t⁻¹ ^ 2 ≤ (((2 : ℝ) ^ kx * M)⁻¹) ^ 2 := pow_le_pow_left₀ h2 h1 2
    _ = ((4 : ℝ) ^ kx)⁻¹ * (M⁻¹) ^ 2 := by
        rw [mul_inv, mul_pow, inv_pow, two_pow_sq]

/-- Dyadic bracketing: with `k := log₂ ⌊t/M⌋₊`, one has `2^k·M ≤ t < 2^{k+1}·M`. -/
private lemma dyadic_bracket {M t : ℝ} (hM : 1 ≤ M) (ht : M ≤ t) :
    (2 : ℝ) ^ (Nat.log 2 ⌊t / M⌋₊) * M ≤ t ∧ t < (2 : ℝ) ^ (Nat.log 2 ⌊t / M⌋₊ + 1) * M := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have h1M : (1 : ℝ) ≤ t / M := (one_le_div hM0).mpr ht
  have hfloor1 : 1 ≤ ⌊t / M⌋₊ := Nat.le_floor (by exact_mod_cast h1M)
  have hne : ⌊t / M⌋₊ ≠ 0 := by omega
  have hpow_le : (2 : ℝ) ^ (Nat.log 2 ⌊t / M⌋₊) ≤ (⌊t / M⌋₊ : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hne
  have hnn_le : (⌊t / M⌋₊ : ℝ) ≤ t / M := Nat.floor_le (by positivity)
  have hlt_nn : t / M < (⌊t / M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨?_, ?_⟩
  · have h2 : (2 : ℝ) ^ (Nat.log 2 ⌊t / M⌋₊) ≤ t / M := le_trans hpow_le hnn_le
    calc (2 : ℝ) ^ (Nat.log 2 ⌊t / M⌋₊) * M ≤ (t / M) * M :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt hM0)
      _ = t := by field_simp
  · have hnat : ⌊t / M⌋₊ + 1 ≤ 2 ^ (Nat.log 2 ⌊t / M⌋₊ + 1) :=
      Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) _)
    have hcast : (⌊t / M⌋₊ : ℝ) + 1 ≤ (2 : ℝ) ^ (Nat.log 2 ⌊t / M⌋₊ + 1) := by exact_mod_cast hnat
    have hchain : t / M < (2 : ℝ) ^ (Nat.log 2 ⌊t / M⌋₊ + 1) := by linarith [hlt_nn, hcast]
    calc t = (t / M) * M := by field_simp
      _ < (2 : ℝ) ^ (Nat.log 2 ⌊t / M⌋₊ + 1) * M := mul_lt_mul_of_pos_right hchain hM0

/-- Reusable dyadic block: an increasing geometric (ratio `4`) sum truncated to indices
`≤ m` is `≤ (4/3)·c·4^m`. -/
private lemma sum_geom_incr_le (c : ℝ) (hc : 0 ≤ c) (J : Finset ℕ) (m : ℕ)
    (hm : ∀ j ∈ J, j ≤ m) : ∑ j ∈ J, c * (4 : ℝ) ^ j ≤ c * (4 : ℝ) ^ m * (4 / 3) := by
  have hsub : J ⊆ Finset.range (m + 1) := fun j hj =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hm j hj))
  have hstep : ((4 : ℝ) ^ (m + 1) - 1) / (4 - 1) ≤ (4 : ℝ) ^ m * (4 / 3) := by
    have h4 : (0 : ℝ) ≤ (4 : ℝ) ^ m := by positivity
    rw [pow_succ, show (4 : ℝ) - 1 = 3 by norm_num, div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith [h4]
  calc ∑ j ∈ J, c * (4 : ℝ) ^ j
      ≤ ∑ j ∈ Finset.range (m + 1), c * (4 : ℝ) ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => mul_nonneg hc (by positivity))
    _ = c * ∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ j := by rw [Finset.mul_sum]
    _ = c * (((4 : ℝ) ^ (m + 1) - 1) / (4 - 1)) := by rw [geom_sum_eq (by norm_num)]
    _ ≤ c * ((4 : ℝ) ^ m * (4 / 3)) := mul_le_mul_of_nonneg_left hstep hc
    _ = c * (4 : ℝ) ^ m * (4 / 3) := by ring

/-- Reusable dyadic block: a decreasing geometric (ratio `1/4`) sum truncated to indices
`≥ m` (all `< n`) is `≤ (4/3)·c·4^{-m}`. -/
private lemma sum_geom_decr_le (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (J : Finset ℕ)
    (hJ : J ⊆ Finset.range n) (m : ℕ) (hm : ∀ j ∈ J, m ≤ j) :
    ∑ j ∈ J, c * ((4 : ℝ) ^ j)⁻¹ ≤ c * ((4 : ℝ) ^ m)⁻¹ * (4 / 3) := by
  have hinj : ∀ x ∈ J, ∀ y ∈ J, x - m = y - m → x = y := by
    intro x hx y hy hxy
    have hx' := hm x hx; have hy' := hm y hy; omega
  have key : ∑ j ∈ J, c * ((4 : ℝ) ^ j)⁻¹
      = c * ((4 : ℝ) ^ m)⁻¹ * ∑ j ∈ J, ((4 : ℝ) ^ (j - m))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjm : m ≤ j := hm j hj
    have hsplit : (4 : ℝ) ^ j = (4 : ℝ) ^ m * (4 : ℝ) ^ (j - m) := by
      rw [← pow_add, Nat.add_sub_cancel' hjm]
    rw [hsplit, mul_inv]; ring
  rw [key]
  have hsum : ∑ j ∈ J, ((4 : ℝ) ^ (j - m))⁻¹ ≤ 4 / 3 := by
    have himg : ∑ k ∈ J.image (fun j => j - m), ((4 : ℝ) ^ k)⁻¹
        = ∑ j ∈ J, ((4 : ℝ) ^ (j - m))⁻¹ := Finset.sum_image hinj
    rw [← himg]
    calc ∑ k ∈ J.image (fun j => j - m), ((4 : ℝ) ^ k)⁻¹
        ≤ ∑ k ∈ Finset.range n, ((4 : ℝ) ^ k)⁻¹ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by positivity)
          intro k hk
          rw [Finset.mem_image] at hk
          obtain ⟨j, hjJ, rfl⟩ := hk
          exact Finset.mem_range.mpr (by have := Finset.mem_range.mp (hJ hjJ); omega)
      _ = ∑ k ∈ Finset.range n, ((1 / 4 : ℝ)) ^ k := by
          refine Finset.sum_congr rfl (fun k _ => ?_); rw [one_div, inv_pow]
      _ ≤ 4 / 3 := by
          rw [geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1),
            show (1 / 4 : ℝ) - 1 = -(3 / 4) by norm_num,
            div_le_iff_of_neg (by norm_num : (-(3 / 4) : ℝ) < 0)]
          have hh : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ n := by positivity
          nlinarith [hh]
  calc c * ((4 : ℝ) ^ m)⁻¹ * ∑ j ∈ J, ((4 : ℝ) ^ (j - m))⁻¹
      ≤ c * ((4 : ℝ) ^ m)⁻¹ * (4 / 3) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hc (by positivity))

/-- The geometric-min sum: for `a, b ≥ 0`,
`∑_{j<n} min(a·4^{-j}, b·4^j) ≤ (8/3)·√(ab)`.  Split at the crossover; each geometric
tail is summed by `sum_geom_incr_le` / `sum_geom_decr_le`. -/
private lemma dyadic_min_geom_sum (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    ∑ j ∈ Finset.range n, min (a * ((4 : ℝ) ^ j)⁻¹) (b * (4 : ℝ) ^ j)
      ≤ (8 / 3) * Real.sqrt (a * b) := by
  classical
  have hb1 : ∑ j ∈ (Finset.range n).filter (fun j => b * (4 : ℝ) ^ j ≤ a * ((4 : ℝ) ^ j)⁻¹),
      min (a * ((4 : ℝ) ^ j)⁻¹) (b * (4 : ℝ) ^ j) ≤ (4 / 3) * Real.sqrt (a * b) := by
    refine (Finset.sum_le_sum (fun j _ => min_le_right _ _)).trans ?_
    rcases Finset.eq_empty_or_nonempty
        ((Finset.range n).filter (fun j => b * (4 : ℝ) ^ j ≤ a * ((4 : ℝ) ^ j)⁻¹)) with he | hne
    · rw [he, Finset.sum_empty]; positivity
    · set J := (Finset.range n).filter (fun j => b * (4 : ℝ) ^ j ≤ a * ((4 : ℝ) ^ j)⁻¹) with hJdef
      have hmem : J.max' hne ∈ J := Finset.max'_mem _ hne
      have hub : ∀ j ∈ J, j ≤ J.max' hne := fun j hj => Finset.le_max' _ j hj
      have hbm : b * (4 : ℝ) ^ (J.max' hne) ≤ Real.sqrt (a * b) := by
        apply le_sqrt_of_sq_le (by positivity)
        have hP : b * (4 : ℝ) ^ (J.max' hne) ≤ a * ((4 : ℝ) ^ (J.max' hne))⁻¹ :=
          (Finset.mem_filter.mp hmem).2
        have h4 : (4 : ℝ) ^ (J.max' hne) ≠ 0 := by positivity
        calc (b * (4 : ℝ) ^ (J.max' hne)) ^ 2
            = (b * (4 : ℝ) ^ (J.max' hne)) * (b * (4 : ℝ) ^ (J.max' hne)) := by ring
          _ ≤ (a * ((4 : ℝ) ^ (J.max' hne))⁻¹) * (b * (4 : ℝ) ^ (J.max' hne)) :=
              mul_le_mul_of_nonneg_right hP (by positivity)
          _ = a * b := by
              rw [show (a * ((4 : ℝ) ^ (J.max' hne))⁻¹) * (b * (4 : ℝ) ^ (J.max' hne))
                = a * b * (((4 : ℝ) ^ (J.max' hne))⁻¹ * (4 : ℝ) ^ (J.max' hne)) by ring,
                inv_mul_cancel₀ h4, mul_one]
      calc ∑ j ∈ J, b * (4 : ℝ) ^ j
          ≤ b * (4 : ℝ) ^ (J.max' hne) * (4 / 3) := sum_geom_incr_le b hb J _ hub
        _ ≤ Real.sqrt (a * b) * (4 / 3) := mul_le_mul_of_nonneg_right hbm (by norm_num)
        _ = (4 / 3) * Real.sqrt (a * b) := by ring
  have hb2 : ∑ j ∈ (Finset.range n).filter (fun j => ¬ b * (4 : ℝ) ^ j ≤ a * ((4 : ℝ) ^ j)⁻¹),
      min (a * ((4 : ℝ) ^ j)⁻¹) (b * (4 : ℝ) ^ j) ≤ (4 / 3) * Real.sqrt (a * b) := by
    refine (Finset.sum_le_sum (fun j _ => min_le_left _ _)).trans ?_
    rcases Finset.eq_empty_or_nonempty
        ((Finset.range n).filter (fun j => ¬ b * (4 : ℝ) ^ j ≤ a * ((4 : ℝ) ^ j)⁻¹)) with he | hne
    · rw [he, Finset.sum_empty]; positivity
    · set J := (Finset.range n).filter (fun j => ¬ b * (4 : ℝ) ^ j ≤ a * ((4 : ℝ) ^ j)⁻¹) with hJdef
      have hmem : J.min' hne ∈ J := Finset.min'_mem _ hne
      have hlb : ∀ j ∈ J, J.min' hne ≤ j := fun j hj => Finset.min'_le _ j hj
      have hsubn : J ⊆ Finset.range n := by rw [hJdef]; exact Finset.filter_subset _ _
      have ham : a * ((4 : ℝ) ^ (J.min' hne))⁻¹ ≤ Real.sqrt (a * b) := by
        apply le_sqrt_of_sq_le (by positivity)
        have hP : a * ((4 : ℝ) ^ (J.min' hne))⁻¹ ≤ b * (4 : ℝ) ^ (J.min' hne) :=
          le_of_lt (not_le.mp (Finset.mem_filter.mp hmem).2)
        have h4 : (4 : ℝ) ^ (J.min' hne) ≠ 0 := by positivity
        calc (a * ((4 : ℝ) ^ (J.min' hne))⁻¹) ^ 2
            = (a * ((4 : ℝ) ^ (J.min' hne))⁻¹) * (a * ((4 : ℝ) ^ (J.min' hne))⁻¹) := by ring
          _ ≤ (a * ((4 : ℝ) ^ (J.min' hne))⁻¹) * (b * (4 : ℝ) ^ (J.min' hne)) :=
              mul_le_mul_of_nonneg_left hP (by positivity)
          _ = a * b := by
              rw [show (a * ((4 : ℝ) ^ (J.min' hne))⁻¹) * (b * (4 : ℝ) ^ (J.min' hne))
                = a * b * (((4 : ℝ) ^ (J.min' hne))⁻¹ * (4 : ℝ) ^ (J.min' hne)) by ring,
                inv_mul_cancel₀ h4, mul_one]
      calc ∑ j ∈ J, a * ((4 : ℝ) ^ j)⁻¹
          ≤ a * ((4 : ℝ) ^ (J.min' hne))⁻¹ * (4 / 3) := sum_geom_decr_le a ha n J hsubn _ hlb
        _ ≤ Real.sqrt (a * b) * (4 / 3) := mul_le_mul_of_nonneg_right ham (by norm_num)
        _ = (4 / 3) * Real.sqrt (a * b) := by ring
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range n)
      (fun j => b * (4 : ℝ) ^ j ≤ a * ((4 : ℝ) ^ j)⁻¹)
      (fun j => min (a * ((4 : ℝ) ^ j)⁻¹) (b * (4 : ℝ) ^ j))
  rw [← hsplit]
  linarith [hb1, hb2]

/-- **Single-variable dyadic sum estimate, paper (5.60)/(5.62).**  For an `M`-separated
set `A` and any center `u`,
`∑_{x ∈ A, |u-x| ≥ M} |u-x|^{-2} ≲ |A|^{1/2} M^{-2}`.  The constant is the single-use
existential line-constant `C = 256·(8/3)`; `|A|^{1/2}` is `Real.sqrt (A.card)`. -/
theorem sum_inv_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (Fin 4 → ℤ)) (M : ℝ), 1 ≤ M →
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → M ≤ znorm (x - y)) → ∀ (u : Fin 4 → ℤ),
      ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x)), (znorm (u - x))⁻¹ ^ 2
        ≤ C * Real.sqrt (A.card : ℝ) * (M⁻¹) ^ 2 := by
  refine ⟨256 * (8 / 3), by norm_num, ?_⟩
  intro A M hM hsep u
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  set S := A.filter (fun x => M ≤ znorm (u - x)) with hS
  set K := S.sup (fun x => Nat.log 2 ⌊znorm (u - x) / M⌋₊) with hK
  have hmapsK : ∀ x ∈ S, Nat.log 2 ⌊znorm (u - x) / M⌋₊ ∈ Finset.range (K + 1) := by
    intro x hx
    rw [Finset.mem_range]
    have hle : Nat.log 2 ⌊znorm (u - x) / M⌋₊ ≤ K := by
      rw [hK]; exact Finset.le_sup (f := fun x => Nat.log 2 ⌊znorm (u - x) / M⌋₊) hx
    omega
  have hfiber : ∀ j ∈ Finset.range (K + 1),
      ∑ x ∈ S.filter (fun x => Nat.log 2 ⌊znorm (u - x) / M⌋₊ = j), (znorm (u - x))⁻¹ ^ 2
        ≤ 16 * (M⁻¹) ^ 2 * min ((A.card : ℝ) * ((4 : ℝ) ^ j)⁻¹) (256 * (4 : ℝ) ^ j) := by
    intro j _
    have step1 : ∑ x ∈ S.filter (fun x => Nat.log 2 ⌊znorm (u - x) / M⌋₊ = j),
          (znorm (u - x))⁻¹ ^ 2
        ≤ ((S.filter (fun x => Nat.log 2 ⌊znorm (u - x) / M⌋₊ = j)).card : ℝ)
          * (((4 : ℝ) ^ j)⁻¹ * (M⁻¹) ^ 2) := by
      calc ∑ x ∈ S.filter (fun x => Nat.log 2 ⌊znorm (u - x) / M⌋₊ = j), (znorm (u - x))⁻¹ ^ 2
          ≤ ∑ _x ∈ S.filter (fun x => Nat.log 2 ⌊znorm (u - x) / M⌋₊ = j),
              (((4 : ℝ) ^ j)⁻¹ * (M⁻¹) ^ 2) := by
            apply Finset.sum_le_sum
            intro x hx
            rw [mem_filter] at hx
            obtain ⟨hxS, hkxj⟩ := hx
            rw [hS, mem_filter] at hxS
            obtain ⟨_, hdx⟩ := hxS
            have ht := term_bound hM0 (Nat.log 2 ⌊znorm (u - x) / M⌋₊) (dyadic_bracket hM hdx).1
            rwa [hkxj] at ht
        _ = ((S.filter (fun x => Nat.log 2 ⌊znorm (u - x) / M⌋₊ = j)).card : ℝ)
              * (((4 : ℝ) ^ j)⁻¹ * (M⁻¹) ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hcnt : ((S.filter (fun x => Nat.log 2 ⌊znorm (u - x) / M⌋₊ = j)).card : ℝ)
        ≤ 16 * min (A.card : ℝ) (256 * 16 ^ j) := by
      have hsub : S.filter (fun x => Nat.log 2 ⌊znorm (u - x) / M⌋₊ = j)
          ⊆ A.filter (fun x => znorm (u - x) ≤ (2 : ℝ) ^ (j + 1) * M) := by
        intro x hx
        rw [mem_filter] at hx ⊢
        obtain ⟨hxS, hkxj⟩ := hx
        rw [hS, mem_filter] at hxS
        obtain ⟨hxA, hdx⟩ := hxS
        refine ⟨hxA, ?_⟩
        have hbr := (dyadic_bracket hM hdx).2
        rw [hkxj] at hbr
        exact le_of_lt hbr
      have hxy : (((2 : ℝ) ^ (j + 1) * M / M + 1) ^ 4) ≤ 256 * 16 ^ j := by
        have hMM : (2 : ℝ) ^ (j + 1) * M / M = 2 ^ (j + 1) := by field_simp
        rw [hMM]
        have hb1 : (2 : ℝ) ^ (j + 1) + 1 ≤ 2 ^ (j + 2) := by
          have h1 : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
          have h22 : (2 : ℝ) ^ (j + 2) = 2 ^ (j + 1) * 2 := pow_succ 2 (j + 1)
          rw [h22]; linarith
        have e1 : ((2 : ℝ) ^ (j + 2)) ^ 4 = (2 : ℝ) ^ (4 * j + 8) := by
          rw [← pow_mul]; congr 1; ring
        have e2 : (256 : ℝ) * 16 ^ j = (2 : ℝ) ^ (4 * j + 8) := by
          rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul,
            show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_add]
          congr 1; ring
        calc ((2 : ℝ) ^ (j + 1) + 1) ^ 4 ≤ ((2 : ℝ) ^ (j + 2)) ^ 4 :=
              pow_le_pow_left₀ (by positivity) hb1 4
          _ = 256 * 16 ^ j := by rw [e1, e2]
      calc ((S.filter (fun x => Nat.log 2 ⌊znorm (u - x) / M⌋₊ = j)).card : ℝ)
          ≤ ((A.filter (fun x => znorm (u - x) ≤ (2 : ℝ) ^ (j + 1) * M)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ 16 * min (A.card : ℝ) (((2 : ℝ) ^ (j + 1) * M / M + 1) ^ 4) :=
            card_ball_center_le u A M hM hsep _
        _ ≤ 16 * min (A.card : ℝ) (256 * 16 ^ j) :=
            mul_le_mul_of_nonneg_left (min_le_min le_rfl hxy) (by norm_num)
    have hmineq : (16 : ℝ) * min (A.card : ℝ) (256 * 16 ^ j) * (((4 : ℝ) ^ j)⁻¹ * (M⁻¹) ^ 2)
        = 16 * (M⁻¹) ^ 2 * min ((A.card : ℝ) * ((4 : ℝ) ^ j)⁻¹) (256 * (4 : ℝ) ^ j) := by
      have hc : (0 : ℝ) ≤ ((4 : ℝ) ^ j)⁻¹ := by positivity
      have hid : (256 * 16 ^ j : ℝ) * ((4 : ℝ) ^ j)⁻¹ = 256 * (4 : ℝ) ^ j := by
        have h16 : (16 : ℝ) ^ j = (4 : ℝ) ^ j * (4 : ℝ) ^ j := by rw [← mul_pow]; norm_num
        have h4ne : (4 : ℝ) ^ j ≠ 0 := by positivity
        rw [h16]; field_simp
      rw [show (16 : ℝ) * min (A.card : ℝ) (256 * 16 ^ j) * (((4 : ℝ) ^ j)⁻¹ * (M⁻¹) ^ 2)
          = 16 * (M⁻¹) ^ 2 * (min (A.card : ℝ) (256 * 16 ^ j) * ((4 : ℝ) ^ j)⁻¹) by ring,
        min_mul_nonneg _ _ _ hc, hid]
    calc ∑ x ∈ S.filter (fun x => Nat.log 2 ⌊znorm (u - x) / M⌋₊ = j), (znorm (u - x))⁻¹ ^ 2
        ≤ ((S.filter (fun x => Nat.log 2 ⌊znorm (u - x) / M⌋₊ = j)).card : ℝ)
            * (((4 : ℝ) ^ j)⁻¹ * (M⁻¹) ^ 2) := step1
      _ ≤ (16 * min (A.card : ℝ) (256 * 16 ^ j)) * (((4 : ℝ) ^ j)⁻¹ * (M⁻¹) ^ 2) :=
          mul_le_mul_of_nonneg_right hcnt (by positivity)
      _ = 16 * (M⁻¹) ^ 2 * min ((A.card : ℝ) * ((4 : ℝ) ^ j)⁻¹) (256 * (4 : ℝ) ^ j) := hmineq
  calc ∑ x ∈ S, (znorm (u - x))⁻¹ ^ 2
      = ∑ j ∈ Finset.range (K + 1),
          ∑ x ∈ S.filter (fun x => Nat.log 2 ⌊znorm (u - x) / M⌋₊ = j), (znorm (u - x))⁻¹ ^ 2 :=
        (Finset.sum_fiberwise_of_maps_to hmapsK _).symm
    _ ≤ ∑ j ∈ Finset.range (K + 1),
          16 * (M⁻¹) ^ 2 * min ((A.card : ℝ) * ((4 : ℝ) ^ j)⁻¹) (256 * (4 : ℝ) ^ j) :=
        Finset.sum_le_sum hfiber
    _ = 16 * (M⁻¹) ^ 2
          * ∑ j ∈ Finset.range (K + 1), min ((A.card : ℝ) * ((4 : ℝ) ^ j)⁻¹) (256 * (4 : ℝ) ^ j) := by
        rw [Finset.mul_sum]
    _ ≤ 16 * (M⁻¹) ^ 2 * ((8 / 3) * Real.sqrt ((A.card : ℝ) * 256)) :=
        mul_le_mul_of_nonneg_left
          (dyadic_min_geom_sum (A.card : ℝ) 256 (by positivity) (by norm_num) (K + 1))
          (by positivity)
    _ = 256 * (8 / 3) * Real.sqrt (A.card : ℝ) * (M⁻¹) ^ 2 := by
        rw [show Real.sqrt ((A.card : ℝ) * 256) = 16 * Real.sqrt (A.card : ℝ) from by
          rw [Real.sqrt_mul (by positivity), show (256 : ℝ) = 16 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]; ring]
        ring

/-! ### Bilinear cluster bound (paper (5.58)) -/

/-- **Bilinear cluster bound (5.58) — trivial-direction ("weak") form.**  The bound
`∑∑ 𝟙·𝟙·|u-x|^{-2}|x-y|^{-2} ≲ |A|^{1/2}M^{-2}|B|^{1/2}N^{-2}` *without* the refining
factor `min(1,(Q/P)^{1/4})`.  Obtained by iterating (5.60) (`sum_inv_sq_le`): sum in `y`,
then in `x`.  Indicators are represented as `Finset.filter`; half-powers via `Real.sqrt`.

Together with the `S`-bound in `LocalRefined.lean`, the elementary
`min`-combination gives the complete factor `min(1,(Q/P)^{1/4})` in (5.58). -/
theorem bilinear_cluster_bound_weak :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : Finset (Fin 4 → ℤ)) (M N : ℝ), 1 ≤ M → 1 ≤ N →
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → M ≤ znorm (x - y)) →
      (∀ x ∈ B, ∀ y ∈ B, x ≠ y → N ≤ znorm (x - y)) → ∀ (u : Fin 4 → ℤ),
      ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x)),
        ∑ y ∈ B.filter (fun y => max M N ≤ znorm (x - y)),
          (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
        ≤ C * Real.sqrt (A.card : ℝ) * (M⁻¹) ^ 2 * Real.sqrt (B.card : ℝ) * (N⁻¹) ^ 2 := by
  obtain ⟨C, hC, hC2⟩ := sum_inv_sq_le
  refine ⟨C ^ 2, pow_pos hC 2, ?_⟩
  intro A B M N hM hN hsepA hsepB u
  have hinner : ∀ x, ∑ y ∈ B.filter (fun y => max M N ≤ znorm (x - y)), (znorm (x - y))⁻¹ ^ 2
      ≤ C * Real.sqrt (B.card : ℝ) * (N⁻¹) ^ 2 := by
    intro x
    calc ∑ y ∈ B.filter (fun y => max M N ≤ znorm (x - y)), (znorm (x - y))⁻¹ ^ 2
        ≤ ∑ y ∈ B.filter (fun y => N ≤ znorm (x - y)), (znorm (x - y))⁻¹ ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro y hy
            rw [mem_filter] at hy ⊢
            exact ⟨hy.1, le_trans (le_max_right M N) hy.2⟩
          · intro y _ _; positivity
      _ ≤ C * Real.sqrt (B.card : ℝ) * (N⁻¹) ^ 2 := hC2 B N hN hsepB x
  calc ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x)),
        ∑ y ∈ B.filter (fun y => max M N ≤ znorm (x - y)),
          (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2
      = ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x)),
          (znorm (u - x))⁻¹ ^ 2 * ∑ y ∈ B.filter (fun y => max M N ≤ znorm (x - y)),
            (znorm (x - y))⁻¹ ^ 2 := by
        refine Finset.sum_congr rfl (fun x _ => ?_); rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x)),
          (znorm (u - x))⁻¹ ^ 2 * (C * Real.sqrt (B.card : ℝ) * (N⁻¹) ^ 2) := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        exact mul_le_mul_of_nonneg_left (hinner x) (by positivity)
    _ = (C * Real.sqrt (B.card : ℝ) * (N⁻¹) ^ 2)
          * ∑ x ∈ A.filter (fun x => M ≤ znorm (u - x)), (znorm (u - x))⁻¹ ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun x _ => ?_); ring
    _ ≤ (C * Real.sqrt (B.card : ℝ) * (N⁻¹) ^ 2) * (C * Real.sqrt (A.card : ℝ) * (M⁻¹) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (hC2 A M hM hsepA u) ?_
        exact mul_nonneg (mul_nonneg hC.le (Real.sqrt_nonneg _)) (by positivity)
    _ = C ^ 2 * Real.sqrt (A.card : ℝ) * (M⁻¹) ^ 2 * Real.sqrt (B.card : ℝ) * (N⁻¹) ^ 2 := by
        ring

end Anderson4D
