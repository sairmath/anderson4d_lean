/-
Copyright (c) 2026 The Anderson4D Project Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Toy model for the permutation-sum machine (paper (1.14)/(1.15))

Paper: T-toy — (1.14)/(1.15) — the toy estimate

This file formalizes the *toy model* of arXiv:2607.10105, equations (1.14) and
(1.15), which is the model computation behind the §5.4 permutation-sum machine.
Points live in `Fin 4 → ℝ` equipped with the sup (Pi) norm; all constants are
norm-dependent and are absorbed into explicit absolute constants.

## Main results

* `Anderson4D.packing_lemma` — the packing/shell bound (1.15): for a
  `τ`-separated finite set `A` and any point `x`, the sum of
  `‖x - y‖⁻¹ ^ 2` over the points `y ∈ A` with `τ ≤ ‖x - y‖` is at most
  `packing_const * √#A * τ⁻¹ ^ 2`.
* `Anderson4D.toy_injTuple_bound` — the toy bound (1.14) for sums over
  injective tuples of points of `A`: the sum over injective `m`-tuples of the
  consecutive inverse-square chain product is at most
  `C ^ n * √(n !) * τ⁻¹ ^ (2 * (m - 1))`.
* `Anderson4D.toy_permSum_bound` — the specialization (1.14) to sums over
  permutations of `n` separated points.
-/

namespace Anderson4D

open Finset
open scoped Nat

/-- The explicit absolute constant in the packing lemma (1.15) for the sup norm
on `Fin 4 → ℝ`.  It arises as `256 * 4`: shell `j` contains at most
`256 * 16 ^ j` points and the dyadic-shell comparison series contributes a
factor `4`. -/
def packing_const : ℝ := 1024

/-- Increasing geometric series bound: `∑_{j<n} 4^j ≤ 4^n / 3`. -/
private lemma sum_pow_four_le (n : ℕ) :
    ∑ j ∈ range n, (4 : ℝ) ^ j ≤ 4 ^ n / 3 := by
  rw [geom_sum_eq (by norm_num) n]
  have h : (0 : ℝ) < 4 ^ n := by positivity
  norm_num
  linarith

/-- Decreasing geometric series bound: `∑_{j<n} (4⁻¹)^j ≤ 4 / 3`. -/
private lemma sum_pow_quarter_le (n : ℕ) :
    ∑ j ∈ range n, ((4 : ℝ)⁻¹) ^ j ≤ 4 / 3 := by
  rw [geom_sum_eq (by norm_num) n]
  have h : (0 : ℝ) ≤ (4 : ℝ)⁻¹ ^ n := by positivity
  have h4 : ((4 : ℝ)⁻¹ ^ n - 1) / ((4 : ℝ)⁻¹ - 1) =
      (1 - (4 : ℝ)⁻¹ ^ n) * (4 / 3) := by ring
  rw [h4]
  nlinarith [pow_le_one₀ (by norm_num : (0:ℝ) ≤ (4:ℝ)⁻¹) (by norm_num : (4:ℝ)⁻¹ ≤ 1) (n := n)]
/-- Core scalar comparison for the dyadic-shell sum in (1.15): splitting the
sum at the crossover `4 ^ j ≈ √M` of the two branches of the minimum, each side
is dominated by a geometric series, giving `∑_j min (4^j) (M/4^j) ≤ 4 √M`. -/
private lemma sum_min_geom_le (J : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∑ j ∈ range J, min ((4 : ℝ) ^ j) (M * (4 : ℝ)⁻¹ ^ j) ≤ 4 * Real.sqrt M := by
  set t := Real.sqrt M with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg M
  have htsq : t * t = M := Real.mul_self_sqrt hM
  rw [← Finset.sum_filter_add_sum_filter_not (range J) (fun j => (4 : ℝ) ^ j ≤ t)]
  have h1 : ∑ j ∈ (range J).filter (fun j => (4 : ℝ) ^ j ≤ t),
      min ((4 : ℝ) ^ j) (M * (4 : ℝ)⁻¹ ^ j) ≤ 2 * t := by
    set S := (range J).filter (fun j => (4 : ℝ) ^ j ≤ t) with hS
    rcases S.eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty]; positivity
    · have hjm : S.max' h ∈ S := S.max'_mem h
      have hjmt : (4 : ℝ) ^ (S.max' h) ≤ t := (Finset.mem_filter.1 hjm).2
      calc ∑ j ∈ S, min ((4 : ℝ) ^ j) (M * (4 : ℝ)⁻¹ ^ j)
          ≤ ∑ j ∈ S, (4 : ℝ) ^ j := Finset.sum_le_sum fun j _ => min_le_left _ _
        _ ≤ ∑ j ∈ range (S.max' h + 1), (4 : ℝ) ^ j := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro j hj
              exact Finset.mem_range.2 (Nat.lt_succ_of_le (S.le_max' j hj))
            · intro j _ _; positivity
        _ ≤ 4 ^ (S.max' h + 1) / 3 := sum_pow_four_le _
        _ = (4 / 3) * 4 ^ (S.max' h) := by ring
        _ ≤ (4 / 3) * t := by gcongr
        _ ≤ 2 * t := by linarith
  have h2 : ∑ j ∈ (range J).filter (fun j => ¬ (4 : ℝ) ^ j ≤ t),
      min ((4 : ℝ) ^ j) (M * (4 : ℝ)⁻¹ ^ j) ≤ 2 * t := by
    set T := (range J).filter (fun j => ¬ (4 : ℝ) ^ j ≤ t) with hT
    rcases T.eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty]; positivity
    · have hjn : T.min' h ∈ T := T.min'_mem h
      have hjnt : t < (4 : ℝ) ^ (T.min' h) := lt_of_not_ge (Finset.mem_filter.1 hjn).2
      rcases ht0.eq_or_lt with h' | ht0'
      · -- `t = 0` forces `M = 0`, so every term of the sum vanishes.
        have hM0 : M = 0 := by rw [← htsq, ← h']; ring
        have : ∑ j ∈ T, min ((4 : ℝ) ^ j) (M * (4 : ℝ)⁻¹ ^ j) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          rw [hM0, zero_mul]
          exact min_eq_right (by positivity)
        rw [this, ← h']
        norm_num
      calc ∑ j ∈ T, min ((4 : ℝ) ^ j) (M * (4 : ℝ)⁻¹ ^ j)
          ≤ ∑ j ∈ T, M * (4 : ℝ)⁻¹ ^ j := Finset.sum_le_sum fun j _ => min_le_right _ _
        _ ≤ ∑ j ∈ Finset.Ico (T.min' h) J, M * (4 : ℝ)⁻¹ ^ j := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro j hj
              exact Finset.mem_Ico.2 ⟨T.min'_le j hj,
                Finset.mem_range.1 (Finset.mem_filter.1 hj).1⟩
            · intro j _ _; positivity
        _ = ∑ i ∈ range (J - T.min' h), M * (4 : ℝ)⁻¹ ^ (T.min' h + i) := by
            rw [Finset.sum_Ico_eq_sum_range]
        _ = M * (4 : ℝ)⁻¹ ^ (T.min' h) * ∑ i ∈ range (J - T.min' h), (4 : ℝ)⁻¹ ^ i := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [pow_add]; ring
        _ ≤ M * (4 : ℝ)⁻¹ ^ (T.min' h) * (4 / 3) := by
            have hnn : 0 ≤ M * (4 : ℝ)⁻¹ ^ (T.min' h) := by positivity
            exact mul_le_mul_of_nonneg_left (sum_pow_quarter_le _) hnn
        _ ≤ M * t⁻¹ * (4 / 3) := by
            have : (4 : ℝ)⁻¹ ^ (T.min' h) ≤ t⁻¹ := by
              rw [inv_pow]
              gcongr
            gcongr
        _ = (4 / 3) * t := by
            field_simp
            nlinarith [htsq]
        _ ≤ 2 * t := by linarith
  linarith

/-- Dyadic-shell series bound for (1.15): shell `j` contributes weight
`4⁻¹ ^ j` per point and at most `min (256 * 16 ^ j) M` points. -/
private lemma sum_shell_series_le (J : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∑ j ∈ range J, (4 : ℝ)⁻¹ ^ j * min (256 * 16 ^ j) M ≤ 1024 * Real.sqrt M := by
  have key : ∀ j : ℕ, (4 : ℝ)⁻¹ ^ j * min (256 * 16 ^ j) M ≤
      256 * min ((4 : ℝ) ^ j) (M * (4 : ℝ)⁻¹ ^ j) := by
    intro j
    have h4 : (0 : ℝ) < (4 : ℝ) ^ j := by positivity
    have hq : (0 : ℝ) < (4 : ℝ)⁻¹ ^ j := by positivity
    have hqm : (4 : ℝ)⁻¹ ^ j * (16 : ℝ) ^ j = 4 ^ j := by
      rw [← mul_pow]; norm_num
    rcases le_total (256 * (16 : ℝ) ^ j) M with h | h
    · rw [min_eq_left h]
      have h1 : (4 : ℝ) ^ j ≤ M * (4 : ℝ)⁻¹ ^ j := by
        calc (4 : ℝ) ^ j ≤ 256 * (16 : ℝ) ^ j * (4 : ℝ)⁻¹ ^ j := by
              nlinarith [hqm]
          _ ≤ M * (4 : ℝ)⁻¹ ^ j := by gcongr
      rw [min_eq_left h1]
      nlinarith [hqm]
    · rw [min_eq_right h]
      have hmin : M * (4 : ℝ)⁻¹ ^ j ≤ 256 * min ((4 : ℝ) ^ j) (M * (4 : ℝ)⁻¹ ^ j) := by
        rcases le_total ((4 : ℝ) ^ j) (M * (4 : ℝ)⁻¹ ^ j) with h' | h'
        · rw [min_eq_left h']
          calc M * (4 : ℝ)⁻¹ ^ j ≤ 256 * (16 : ℝ) ^ j * (4 : ℝ)⁻¹ ^ j := by gcongr
            _ = 256 * 4 ^ j := by linear_combination (256 : ℝ) * hqm
        · rw [min_eq_right h']
          nlinarith [mul_nonneg hM hq.le]
      calc (4 : ℝ)⁻¹ ^ j * M = M * (4 : ℝ)⁻¹ ^ j := by ring
        _ ≤ 256 * min ((4 : ℝ) ^ j) (M * (4 : ℝ)⁻¹ ^ j) := hmin
  calc ∑ j ∈ range J, (4 : ℝ)⁻¹ ^ j * min (256 * 16 ^ j) M
      ≤ ∑ j ∈ range J, 256 * min ((4 : ℝ) ^ j) (M * (4 : ℝ)⁻¹ ^ j) :=
        Finset.sum_le_sum fun j _ => key j
    _ = 256 * ∑ j ∈ range J, min ((4 : ℝ) ^ j) (M * (4 : ℝ)⁻¹ ^ j) := by
        rw [Finset.mul_sum]
    _ ≤ 256 * (4 * Real.sqrt M) :=
        mul_le_mul_of_nonneg_left (sum_min_geom_le J hM) (by norm_num)
    _ = 1024 * Real.sqrt M := by ring

/-- Grid-counting step for (1.15): a `τ`-separated set of points at sup-distance
`< 2 ^ (j + 1) * τ` from `x` has at most `256 * 16 ^ j` elements.  The floor-scaled
map `y ↦ ⌊(y - x) / τ⌋` (componentwise) is injective on a `τ`-separated set, since
two points in the same half-open grid cell are at sup-distance `< τ`. -/
private lemma card_shell_le (A : Finset (Fin 4 → ℝ)) {τ : ℝ} (hτ : 0 < τ)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → τ ≤ ‖a - b‖) (x : Fin 4 → ℝ) (j : ℕ)
    (hA : ∀ y ∈ A, ‖x - y‖ < 2 ^ (j + 1) * τ) :
    (A.card : ℝ) ≤ 256 * 16 ^ j := by
  classical
  set B : Finset (Fin 4 → ℤ) :=
    Fintype.piFinset fun _ => Finset.Icc (-(2 ^ (j + 1) : ℤ)) (2 ^ (j + 1) - 1) with hB
  have hmaps : ∀ y ∈ A, (fun i => ⌊(y i - x i) / τ⌋) ∈ B := by
    intro y hy
    rw [hB, Fintype.mem_piFinset]
    intro i
    have hcoord : |y i - x i| < 2 ^ (j + 1) * τ := by
      calc |y i - x i| = ‖(y - x) i‖ := by rw [Pi.sub_apply, Real.norm_eq_abs]
        _ ≤ ‖y - x‖ := norm_le_pi_norm (y - x) i
        _ = ‖x - y‖ := (norm_sub_rev x y).symm
        _ < 2 ^ (j + 1) * τ := hA y hy
    rw [abs_lt] at hcoord
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]
      rw [le_div_iff₀ hτ]
      push_cast
      nlinarith [hcoord.1]
    · have hlt : ⌊(y i - x i) / τ⌋ < (2 ^ (j + 1) : ℤ) := by
        rw [Int.floor_lt]
        rw [div_lt_iff₀ hτ]
        push_cast
        nlinarith [hcoord.2]
      omega
  have hinj : Set.InjOn (fun (y : Fin 4 → ℝ) (i : Fin 4) => ⌊(y i - x i) / τ⌋) A := by
    intro y hy z hz hyz
    by_contra hne
    have hτle : τ ≤ ‖y - z‖ := hsep y hy z hz hne
    have hlt : ‖y - z‖ < τ := by
      rw [pi_norm_lt_iff hτ]
      intro i
      have hfl : ⌊(y i - x i) / τ⌋ = ⌊(z i - x i) / τ⌋ := congrFun hyz i
      have habs : |(y i - x i) / τ - (z i - x i) / τ| < 1 :=
        Int.abs_sub_lt_one_of_floor_eq_floor hfl
      have hsub : (y i - x i) / τ - (z i - x i) / τ = (y i - z i) / τ := by ring
      rw [hsub, abs_div, abs_of_pos hτ, div_lt_one hτ] at habs
      rw [Pi.sub_apply, Real.norm_eq_abs]
      exact habs
    exact absurd hτle (not_le.2 hlt)
  have hcard : A.card ≤ B.card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  have hBcard : B.card = 2 ^ (4 * j + 8) := by
    rw [hB, Fintype.card_piFinset]
    have hIcc : (Finset.Icc (-(2 ^ (j + 1) : ℤ)) (2 ^ (j + 1) - 1)).card = 2 ^ (j + 2) := by
      rw [Int.card_Icc]
      have h2 : (0 : ℤ) < 2 ^ (j + 1) := by positivity
      have h1 : (2 ^ (j + 1) - 1 + 1 - -(2 ^ (j + 1)) : ℤ) = ((2 ^ (j + 2) : ℕ) : ℤ) := by
        push_cast
        ring
      rw [h1, Int.toNat_natCast]
    rw [hIcc]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
    ring
  calc (A.card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hcard
    _ = 2 ^ (4 * j + 8) := by rw [hBcard]; push_cast; ring
    _ = 256 * 16 ^ j := by rw [pow_add, pow_mul]; norm_num [mul_comm]

/-- **Packing lemma**, the toy-model estimate (1.15) of arXiv:2607.10105: for a
`τ`-separated finite set `A ⊆ Fin 4 → ℝ` (sup norm) and any point `x`,
`∑_{y ∈ A, τ ≤ ‖x-y‖} ‖x - y‖⁻² ≤ packing_const · √#A · τ⁻²`.
The proof decomposes the sum into dyadic shells `2^j τ ≤ ‖x - y‖ < 2^{j+1} τ`;
shell `j` has at most `min (256 · 16^j) #A` points, and comparing the resulting
series with two geometric series at the crossover `16^j ≈ #A` yields `√#A`. -/
theorem packing_lemma (A : Finset (Fin 4 → ℝ)) {τ : ℝ} (hτ : 0 < τ)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → τ ≤ ‖a - b‖) (x : Fin 4 → ℝ) :
    ∑ y ∈ A.filter (fun y => τ ≤ ‖x - y‖), ‖x - y‖⁻¹ ^ 2
      ≤ packing_const * Real.sqrt A.card * τ⁻¹ ^ 2 := by
  classical
  set F := A.filter (fun y => τ ≤ ‖x - y‖) with hF
  set g : (Fin 4 → ℝ) → ℕ := fun y => Nat.log 2 ⌊‖x - y‖ / τ⌋₊ with hg
  set J := F.sup g + 1 with hJ
  have hmaps : ∀ y ∈ F, g y ∈ range J := fun y hy =>
    mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup hy))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun y => ‖x - y‖⁻¹ ^ 2)]
  have hshell : ∀ j ∈ range J,
      ∑ y ∈ F.filter (fun y => g y = j), ‖x - y‖⁻¹ ^ 2
        ≤ (4 : ℝ)⁻¹ ^ j * min (256 * 16 ^ j) (A.card : ℝ) * τ⁻¹ ^ 2 := by
    intro j _
    set S := F.filter (fun y => g y = j) with hS
    -- Distance facts on the shell.
    have hmem : ∀ y ∈ S, τ ≤ ‖x - y‖ ∧ g y = j := by
      intro y hy
      have h1 := Finset.mem_filter.1 hy
      exact ⟨(Finset.mem_filter.1 h1.1).2, h1.2⟩
    have hlow : ∀ y ∈ S, (2 : ℝ) ^ j * τ ≤ ‖x - y‖ := by
      intro y hy
      obtain ⟨h1, h2⟩ := hmem y hy
      have hd : (1 : ℝ) ≤ ‖x - y‖ / τ := (one_le_div hτ).2 h1
      have hn1 : 1 ≤ ⌊‖x - y‖ / τ⌋₊ := Nat.le_floor (by exact_mod_cast hd)
      have hpow : (2 : ℕ) ^ j ≤ ⌊‖x - y‖ / τ⌋₊ := by
        rw [← h2, hg]
        exact Nat.pow_log_le_self 2 (by omega)
      have hfl : (⌊‖x - y‖ / τ⌋₊ : ℝ) ≤ ‖x - y‖ / τ := Nat.floor_le (by positivity)
      rw [← le_div_iff₀ hτ]
      calc (2 : ℝ) ^ j = ((2 ^ j : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (⌊‖x - y‖ / τ⌋₊ : ℝ) := by exact_mod_cast hpow
        _ ≤ ‖x - y‖ / τ := hfl
    have hhigh : ∀ y ∈ S, ‖x - y‖ < 2 ^ (j + 1) * τ := by
      intro y hy
      obtain ⟨_, h2⟩ := hmem y hy
      have hnlt : ⌊‖x - y‖ / τ⌋₊ < 2 ^ (j + 1) := by
        rw [← h2, hg]
        exact Nat.lt_pow_succ_log_self (by omega) _
      have hfl : ‖x - y‖ / τ < ⌊‖x - y‖ / τ⌋₊ + 1 := Nat.lt_floor_add_one _
      rw [← div_lt_iff₀ hτ]
      calc ‖x - y‖ / τ < (⌊‖x - y‖ / τ⌋₊ : ℝ) + 1 := hfl
        _ ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hnlt
        _ = 2 ^ (j + 1) := by push_cast; ring
    -- Cardinality of the shell.
    have hcard : (S.card : ℝ) ≤ min (256 * 16 ^ j) (A.card : ℝ) := by
      refine le_min ?_ ?_
      · exact card_shell_le S hτ
          (fun a ha b hb hab =>
            hsep a (Finset.filter_subset _ _ (Finset.filter_subset _ _ ha))
              b (Finset.filter_subset _ _ (Finset.filter_subset _ _ hb)) hab)
          x j (fun y hy => hhigh y hy)
      · exact_mod_cast Finset.card_le_card
          ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
    -- Per-point weight bound on the shell.
    have hweight : ∀ y ∈ S, ‖x - y‖⁻¹ ^ 2 ≤ (4 : ℝ)⁻¹ ^ j * τ⁻¹ ^ 2 := by
      intro y hy
      have h1 := hlow y hy
      have hpos : (0 : ℝ) < (2 : ℝ) ^ j * τ := by positivity
      have hinv : ‖x - y‖⁻¹ ≤ ((2 : ℝ) ^ j * τ)⁻¹ :=
        (inv_le_inv₀ (hpos.trans_le h1) hpos).2 h1
      have h24 : (((2 : ℝ) ^ j)⁻¹) ^ 2 = (4 : ℝ)⁻¹ ^ j := by
        rw [← inv_pow, ← pow_mul, mul_comm j 2, pow_mul]
        norm_num
      have hid : (((2 : ℝ) ^ j * τ)⁻¹) ^ 2 = (4 : ℝ)⁻¹ ^ j * τ⁻¹ ^ 2 := by
        rw [mul_inv, mul_pow, h24]
      calc ‖x - y‖⁻¹ ^ 2 ≤ (((2 : ℝ) ^ j * τ)⁻¹) ^ 2 := by gcongr
        _ = (4 : ℝ)⁻¹ ^ j * τ⁻¹ ^ 2 := hid
    calc ∑ y ∈ S, ‖x - y‖⁻¹ ^ 2 ≤ ∑ _y ∈ S, (4 : ℝ)⁻¹ ^ j * τ⁻¹ ^ 2 :=
          Finset.sum_le_sum hweight
      _ = (S.card : ℝ) * ((4 : ℝ)⁻¹ ^ j * τ⁻¹ ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ min (256 * 16 ^ j) (A.card : ℝ) * ((4 : ℝ)⁻¹ ^ j * τ⁻¹ ^ 2) := by
          apply mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (4 : ℝ)⁻¹ ^ j * min (256 * 16 ^ j) (A.card : ℝ) * τ⁻¹ ^ 2 := by ring
  calc ∑ j ∈ range J, ∑ y ∈ F.filter (fun y => g y = j), ‖x - y‖⁻¹ ^ 2
      ≤ ∑ j ∈ range J, (4 : ℝ)⁻¹ ^ j * min (256 * 16 ^ j) (A.card : ℝ) * τ⁻¹ ^ 2 :=
        Finset.sum_le_sum hshell
    _ = (∑ j ∈ range J, (4 : ℝ)⁻¹ ^ j * min (256 * 16 ^ j) (A.card : ℝ)) * τ⁻¹ ^ 2 := by
        rw [Finset.sum_mul]
    _ ≤ 1024 * Real.sqrt A.card * τ⁻¹ ^ 2 := by
        apply mul_le_mul_of_nonneg_right
          (sum_shell_series_le J (by positivity)) (by positivity)
    _ = packing_const * Real.sqrt A.card * τ⁻¹ ^ 2 := by rw [packing_const]

/-! ### Sums over injective tuples: the toy bound (1.14) -/

/-- The finite set of injective `m`-tuples of points of `A` (as functions
`Fin m → (Fin 4 → ℝ)` with all values in `A`).  Summing the chain weight
`chainWeight` over `injTuples n A` with `#A = n` is the paper's sum (1.14)
over orderings of the points of `A`. -/
noncomputable def injTuples (m : ℕ) (A : Finset (Fin 4 → ℝ)) :
    Finset (Fin m → (Fin 4 → ℝ)) := by
  classical
  exact (Fintype.piFinset fun _ => A).filter Function.Injective

/-- The consecutive inverse-square chain product
`∏_{j<m-1} ‖f j - f (j+1)‖⁻²` of a tuple, the summand of (1.14). -/
noncomputable def chainWeight (m : ℕ) (f : Fin m → (Fin 4 → ℝ)) : ℝ :=
  ∏ j : Fin (m - 1),
    ‖f ⟨j.1, by have := j.isLt; omega⟩ - f ⟨j.1 + 1, by have := j.isLt; omega⟩‖⁻¹ ^ 2

lemma chainWeight_nonneg (m : ℕ) (f : Fin m → (Fin 4 → ℝ)) :
    0 ≤ chainWeight m f :=
  Finset.prod_nonneg fun _ _ => by positivity

lemma mem_injTuples {m : ℕ} {A : Finset (Fin 4 → ℝ)} {f : Fin m → (Fin 4 → ℝ)} :
    f ∈ injTuples m A ↔ (∀ i, f i ∈ A) ∧ Function.Injective f := by
  classical
  simp [injTuples, Fintype.mem_piFinset]

/-- Restriction (dropping the last entry) maps injective `(m+1)`-tuples to
injective `m`-tuples. -/
private lemma init_mem_injTuples {m : ℕ} {A : Finset (Fin 4 → ℝ)}
    {f : Fin (m + 1) → (Fin 4 → ℝ)} (hf : f ∈ injTuples (m + 1) A) :
    Fin.init f ∈ injTuples m A := by
  rw [mem_injTuples] at hf ⊢
  exact ⟨fun i => hf.1 _, fun i j hij => Fin.castSucc_injective m (hf.2 hij)⟩

/-- Peeling the last chain factor: for an `(m+2)`-tuple,
`chainWeight = chainWeight of the initial (m+1)-tuple × last factor`. -/
private lemma chainWeight_succ (m : ℕ) (f : Fin (m + 2) → (Fin 4 → ℝ)) :
    chainWeight (m + 2) f =
      chainWeight (m + 1) (Fin.init f) *
        ‖f ⟨m, by omega⟩ - f ⟨m + 1, by omega⟩‖⁻¹ ^ 2 := by
  show (∏ j : Fin (m + 1),
      ‖f ⟨j.1, by have := j.isLt; omega⟩ - f ⟨j.1 + 1, by have := j.isLt; omega⟩‖⁻¹ ^ 2) =
    (∏ j : Fin m,
      ‖Fin.init f ⟨j.1, by have := j.isLt; omega⟩ -
        Fin.init f ⟨j.1 + 1, by have := j.isLt; omega⟩‖⁻¹ ^ 2) *
      ‖f ⟨m, by omega⟩ - f ⟨m + 1, by omega⟩‖⁻¹ ^ 2
  rw [Fin.prod_univ_castSucc]
  rfl

/-- The (1.14) recursion: peeling the last point of an injective chain costs at
most one factor `packing_const · √#A · τ⁻²`, by the packing lemma (1.15). -/
private lemma injTuples_sum_succ_le (A : Finset (Fin 4 → ℝ)) {τ : ℝ} (hτ : 0 < τ)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → τ ≤ ‖a - b‖) (m : ℕ) :
    ∑ f ∈ injTuples (m + 2) A, chainWeight (m + 2) f
      ≤ (packing_const * Real.sqrt A.card * τ⁻¹ ^ 2) *
        ∑ g ∈ injTuples (m + 1) A, chainWeight (m + 1) g := by
  classical
  have hmaps : ∀ f ∈ injTuples (m + 2) A, Fin.init f ∈ injTuples (m + 1) A :=
    fun f hf => init_mem_injTuples hf
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (chainWeight (m + 2)), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro g hg
  set x₀ : Fin 4 → ℝ := g ⟨m, by omega⟩ with hx₀
  have hstep : ∀ f ∈ (injTuples (m + 2) A).filter (fun f => Fin.init f = g),
      chainWeight (m + 2) f =
        chainWeight (m + 1) g * ‖x₀ - f (Fin.last (m + 1))‖⁻¹ ^ 2 := by
    intro f hf
    have hfg : Fin.init f = g := (Finset.mem_filter.1 hf).2
    have hfx : f ⟨m, by omega⟩ = x₀ := by
      have h1 : f ⟨m, by omega⟩ = Fin.init f ⟨m, by omega⟩ := rfl
      rw [h1, hfg]
    have hlast : f ⟨m + 1, by omega⟩ = f (Fin.last (m + 1)) := rfl
    rw [chainWeight_succ, hfg, hfx, hlast]
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  have hinner : ∑ f ∈ (injTuples (m + 2) A).filter (fun f => Fin.init f = g),
      ‖x₀ - f (Fin.last (m + 1))‖⁻¹ ^ 2
        ≤ packing_const * Real.sqrt A.card * τ⁻¹ ^ 2 := by
    have hinj : ∀ f₁ ∈ (injTuples (m + 2) A).filter (fun f => Fin.init f = g),
        ∀ f₂ ∈ (injTuples (m + 2) A).filter (fun f => Fin.init f = g),
        f₁ (Fin.last (m + 1)) = f₂ (Fin.last (m + 1)) → f₁ = f₂ := by
      intro f₁ h₁ f₂ h₂ hl
      have e₁ : Fin.init f₁ = g := (Finset.mem_filter.1 h₁).2
      have e₂ : Fin.init f₂ = g := (Finset.mem_filter.1 h₂).2
      rw [← Fin.snoc_init_self f₁, ← Fin.snoc_init_self f₂, e₁, e₂, hl]
    have himg : ∑ y ∈ ((injTuples (m + 2) A).filter (fun f => Fin.init f = g)).image
          (fun f => f (Fin.last (m + 1))), ‖x₀ - y‖⁻¹ ^ 2
        = ∑ f ∈ (injTuples (m + 2) A).filter (fun f => Fin.init f = g),
            ‖x₀ - f (Fin.last (m + 1))‖⁻¹ ^ 2 := Finset.sum_image hinj
    rw [← himg]
    have hsub : ((injTuples (m + 2) A).filter (fun f => Fin.init f = g)).image
        (fun f => f (Fin.last (m + 1))) ⊆ A.filter (fun y => τ ≤ ‖x₀ - y‖) := by
      intro y hy
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hy
      have hfmem := Finset.mem_filter.1 hf
      obtain ⟨hval, hinjf⟩ := mem_injTuples.1 hfmem.1
      refine Finset.mem_filter.2 ⟨hval _, ?_⟩
      have hx : x₀ = f (Fin.castSucc ⟨m, by omega⟩) := by
        rw [hx₀, ← hfmem.2]
        rfl
      have hne : x₀ ≠ f (Fin.last (m + 1)) := by
        rw [hx]
        intro h
        have h2 := hinjf h
        have h4 := congrArg Fin.val h2
        simp at h4
      have hxA : x₀ ∈ A := by
        rw [hx]
        exact hval _
      exact hsep x₀ hxA _ (hval _) hne
    calc ∑ y ∈ ((injTuples (m + 2) A).filter (fun f => Fin.init f = g)).image
            (fun f => f (Fin.last (m + 1))), ‖x₀ - y‖⁻¹ ^ 2
        ≤ ∑ y ∈ A.filter (fun y => τ ≤ ‖x₀ - y‖), ‖x₀ - y‖⁻¹ ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro y _ _
          positivity
      _ ≤ packing_const * Real.sqrt A.card * τ⁻¹ ^ 2 := packing_lemma A hτ hsep x₀
  calc chainWeight (m + 1) g * ∑ f ∈ (injTuples (m + 2) A).filter
          (fun f => Fin.init f = g), ‖x₀ - f (Fin.last (m + 1))‖⁻¹ ^ 2
      ≤ chainWeight (m + 1) g * (packing_const * Real.sqrt A.card * τ⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_left hinner (chainWeight_nonneg _ _)
    _ = packing_const * Real.sqrt A.card * τ⁻¹ ^ 2 * chainWeight (m + 1) g := by ring

/-- Base case of (1.14): the sum over `1`-tuples is at most `#A`. -/
private lemma injTuples_sum_one_le (A : Finset (Fin 4 → ℝ)) :
    ∑ f ∈ injTuples 1 A, chainWeight 1 f ≤ (A.card : ℝ) := by
  classical
  have h1 : ∀ f ∈ injTuples 1 A, chainWeight 1 f = 1 := by
    intro f _
    unfold chainWeight
    apply Finset.prod_eq_one
    intro j _
    exact absurd j.isLt (by omega)
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h3 : (injTuples 1 A).card ≤ (Fintype.piFinset fun _ : Fin 1 => A).card := by
    apply Finset.card_le_card
    intro f hf
    exact Fintype.mem_piFinset.2 (mem_injTuples.1 hf).1
  rw [Fintype.card_piFinset] at h3
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one] at h3
  exact_mod_cast h3

/-- Iterating the recursion from the base case: the (1.14) chain sum over
injective `(m+1)`-tuples is at most `#A · (packing_const · √#A · τ⁻²)^m`. -/
private lemma injTuples_sum_le_pow (A : Finset (Fin 4 → ℝ)) {τ : ℝ} (hτ : 0 < τ)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → τ ≤ ‖a - b‖) (m : ℕ) :
    ∑ f ∈ injTuples (m + 1) A, chainWeight (m + 1) f
      ≤ (A.card : ℝ) * (packing_const * Real.sqrt A.card * τ⁻¹ ^ 2) ^ m := by
  induction m with
  | zero => simpa using injTuples_sum_one_le A
  | succ k ih =>
      have hK : 0 ≤ packing_const * Real.sqrt A.card * τ⁻¹ ^ 2 := by
        unfold packing_const
        positivity
      calc ∑ f ∈ injTuples (k + 2) A, chainWeight (k + 2) f
          ≤ (packing_const * Real.sqrt A.card * τ⁻¹ ^ 2) *
              ∑ g ∈ injTuples (k + 1) A, chainWeight (k + 1) g :=
            injTuples_sum_succ_le A hτ hsep k
        _ ≤ (packing_const * Real.sqrt A.card * τ⁻¹ ^ 2) *
              ((A.card : ℝ) * (packing_const * Real.sqrt A.card * τ⁻¹ ^ 2) ^ k) :=
            mul_le_mul_of_nonneg_left ih hK
        _ = (A.card : ℝ) * (packing_const * Real.sqrt A.card * τ⁻¹ ^ 2) ^ (k + 1) := by
            ring

/-- Factorial comparison `n ^ n ≤ 4 ^ n * (n)!`, proved via
`n^n ≤ (n+1)^n ≤ (2n)!/n! = C(2n,n) · (n)! ≤ 4^n · (n)!` (the middle step is
`Nat.pow_sub_le_descFactorial`, and `C(2n,n) ≤ 4^n` follows from the binomial
row sum `Nat.sum_range_choose`). -/
private lemma pow_self_le_four_pow_mul_factorial (n : ℕ) : n ^ n ≤ 4 ^ n * (n)! := by
  have h2 : (n + 1) ^ n ≤ (2 * n).descFactorial n := by
    have h := Nat.pow_sub_le_descFactorial (2 * n) n
    have he : 2 * n + 1 - n = n + 1 := by omega
    rwa [he] at h
  have h3 : (2 * n).descFactorial n = (2 * n).choose n * (n)! := by
    have hle : n ≤ 2 * n := by omega
    have hA := Nat.choose_mul_factorial_mul_factorial hle
    have hB := Nat.factorial_mul_descFactorial hle
    have he : 2 * n - n = n := by omega
    rw [he] at hA hB
    apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos n)
    calc (n)! * (2 * n).descFactorial n = (2 * n)! := hB
      _ = (2 * n).choose n * (n)! * (n)! := hA.symm
      _ = (n)! * ((2 * n).choose n * (n)!) := by ring
  have h4 : (2 * n).choose n ≤ 4 ^ n := by
    calc (2 * n).choose n ≤ (∑ i ∈ range (2 * n + 1), (2 * n).choose i) :=
          Finset.single_le_sum (f := fun i => (2 * n).choose i)
            (fun i _ => Nat.zero_le _) (mem_range.2 (by omega))
      _ = 2 ^ (2 * n) := Nat.sum_range_choose (2 * n)
      _ = 4 ^ n := by rw [pow_mul]; norm_num
  calc n ^ n ≤ (n + 1) ^ n := Nat.pow_le_pow_left (by omega) n
    _ ≤ (2 * n).descFactorial n := h2
    _ = (2 * n).choose n * (n)! := h3
    _ ≤ 4 ^ n * (n)! := Nat.mul_le_mul_right _ h4

/-- **Toy theorem (1.14), injective-tuple form.**  For `n` `τ`-separated points
in `Fin 4 → ℝ` (sup norm) and any `m ≤ n`, the sum over injective `m`-tuples of
the consecutive inverse-square chain product is at most
`C ^ n · √(n!) · τ^{-2(m-1)}` with an absolute constant `C`.  This is the
paper's bound (1.14) on the ordering sum, in the form that feeds the §5.4
permutation-sum machine; it follows by iterating the packing lemma (1.15) and
the factorial comparison `n^n ≤ 4^n n!` (giving `n^{(n-1)/2} ≤ 2^n √(n!)`). -/
theorem toy_injTuple_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n m : ℕ) (τ : ℝ), 0 < τ →
      ∀ A : Finset (Fin 4 → ℝ), A.card = n →
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → τ ≤ ‖a - b‖) → m ≤ n →
        ∑ f ∈ injTuples m A, chainWeight m f
          ≤ C ^ n * Real.sqrt ((n)! : ℝ) * τ⁻¹ ^ (2 * (m - 1)) := by
  refine ⟨4096, by norm_num, ?_⟩
  intro n m τ hτ A hcard hsep hmn
  have hfac0 : (0 : ℝ) ≤ ((n)! : ℝ) := by positivity
  have hfac1 : (1 : ℝ) ≤ Real.sqrt ((n)! : ℝ) :=
    Real.one_le_sqrt.2 (by exact_mod_cast Nat.factorial_pos n)
  match m with
  | 0 =>
    have h1 : ∀ f ∈ injTuples 0 A, chainWeight 0 f = 1 := by
      intro f _
      unfold chainWeight
      apply Finset.prod_eq_one
      intro j _
      exact absurd j.isLt (by omega)
    have h0 : ∑ f ∈ injTuples 0 A, chainWeight 0 f ≤ 1 := by
      rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
      have h2 : (injTuples 0 A).card ≤ (Fintype.piFinset fun _ : Fin 0 => A).card :=
        Finset.card_le_card fun f hf => Fintype.mem_piFinset.2 (mem_injTuples.1 hf).1
      rw [Fintype.card_piFinset] at h2
      simp only [Finset.univ_eq_empty, Finset.prod_empty] at h2
      exact_mod_cast h2
    have hp : (1 : ℝ) ≤ 4096 ^ n := one_le_pow₀ (by norm_num)
    calc ∑ f ∈ injTuples 0 A, chainWeight 0 f ≤ 1 := h0
      _ ≤ 4096 ^ n * Real.sqrt ((n)! : ℝ) * τ⁻¹ ^ (2 * (0 - 1)) := by
          norm_num
          nlinarith
  | m' + 1 =>
    have hn1 : 1 ≤ n := le_trans (by omega) hmn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hsq1 : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.2 hnR
    -- Core scalar bound `n · (√n)^{n-1} ≤ 4^n · √(n!)`, by squaring.
    have hn4 : n ≤ 4 ^ n := by
      calc n ≤ 2 ^ n := (Nat.lt_two_pow_self).le
        _ ≤ 4 ^ n := Nat.pow_le_pow_left (by norm_num) n
    have hnat : n ^ (n + 1) ≤ 16 ^ n * (n)! := by
      calc n ^ (n + 1) = n ^ n * n := pow_succ n n
        _ ≤ (4 ^ n * (n)!) * 4 ^ n :=
            Nat.mul_le_mul (pow_self_le_four_pow_mul_factorial n) hn4
        _ = 16 ^ n * (n)! := by
            rw [show (16 : ℕ) = 4 * 4 from rfl, mul_pow]
            ring
    have hexp : 2 + (n - 1) = n + 1 := by omega
    have e1 : ((n : ℝ) * Real.sqrt n ^ (n - 1)) ^ 2 = (n : ℝ) ^ (n + 1) := by
      rw [mul_pow, ← pow_mul, mul_comm (n - 1) 2, pow_mul,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ)), ← pow_add, hexp]
    have e2 : ((4 : ℝ) ^ n * Real.sqrt ((n)! : ℝ)) ^ 2 = 16 ^ n * ((n)! : ℝ) := by
      rw [mul_pow, Real.sq_sqrt hfac0, ← pow_mul, mul_comm n 2, pow_mul]
      norm_num
    have hcore : (n : ℝ) * Real.sqrt n ^ (n - 1) ≤ 4 ^ n * Real.sqrt ((n)! : ℝ) := by
      have ha : (0 : ℝ) ≤ (n : ℝ) * Real.sqrt n ^ (n - 1) := by positivity
      have hb : (0 : ℝ) ≤ (4 : ℝ) ^ n * Real.sqrt ((n)! : ℝ) := by positivity
      have h2 : ((n : ℝ) * Real.sqrt n ^ (n - 1)) ^ 2
          ≤ ((4 : ℝ) ^ n * Real.sqrt ((n)! : ℝ)) ^ 2 := by
        rw [e1, e2]
        exact_mod_cast hnat
      calc (n : ℝ) * Real.sqrt n ^ (n - 1)
          = Real.sqrt (((n : ℝ) * Real.sqrt n ^ (n - 1)) ^ 2) := (Real.sqrt_sq ha).symm
        _ ≤ Real.sqrt (((4 : ℝ) ^ n * Real.sqrt ((n)! : ℝ)) ^ 2) := Real.sqrt_le_sqrt h2
        _ = 4 ^ n * Real.sqrt ((n)! : ℝ) := Real.sqrt_sq hb
    calc ∑ f ∈ injTuples (m' + 1) A, chainWeight (m' + 1) f
        ≤ (A.card : ℝ) * (packing_const * Real.sqrt A.card * τ⁻¹ ^ 2) ^ m' :=
          injTuples_sum_le_pow A hτ hsep m'
      _ = (n : ℝ) * (1024 ^ m' * Real.sqrt n ^ m' * τ⁻¹ ^ (2 * m')) := by
          rw [hcard]
          unfold packing_const
          rw [mul_pow, mul_pow, ← pow_mul]
      _ ≤ (n : ℝ) * (1024 ^ n * Real.sqrt n ^ (n - 1) * τ⁻¹ ^ (2 * m')) := by
          have hb1 : (1024 : ℝ) ^ m' ≤ 1024 ^ n :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have hb2 : Real.sqrt n ^ m' ≤ Real.sqrt n ^ (n - 1) :=
            pow_le_pow_right₀ hsq1 (by omega)
          have hXY : (1024 : ℝ) ^ m' * Real.sqrt n ^ m'
              ≤ 1024 ^ n * Real.sqrt n ^ (n - 1) :=
            mul_le_mul hb1 hb2 (by positivity) (by positivity)
          have h1 : (1024 : ℝ) ^ m' * Real.sqrt n ^ m' * τ⁻¹ ^ (2 * m')
              ≤ 1024 ^ n * Real.sqrt n ^ (n - 1) * τ⁻¹ ^ (2 * m') :=
            mul_le_mul_of_nonneg_right hXY (by positivity)
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1024 ^ n * ((n : ℝ) * Real.sqrt n ^ (n - 1)) * τ⁻¹ ^ (2 * m') := by ring
      _ ≤ 1024 ^ n * (4 ^ n * Real.sqrt ((n)! : ℝ)) * τ⁻¹ ^ (2 * m') := by
          gcongr
      _ = 4096 ^ n * Real.sqrt ((n)! : ℝ) * τ⁻¹ ^ (2 * m') := by
          rw [show (4096 : ℝ) = 1024 * 4 by norm_num, mul_pow]
          ring

/-- **Toy theorem (1.14), permutation form.**  For `n` pairwise `τ`-separated
points `x 0, …, x (n-1)` in `Fin 4 → ℝ` (sup norm), the sum over all orderings
(permutations `π`) of the consecutive inverse-square chain product
`∏_{j<n-1} ‖x (π j) - x (π (j+1))‖⁻²` — here `chainWeight n (x ∘ π)` — is at
most `C ^ n · √(n!) · τ^{-2(n-1)}`.  This is exactly (1.14): the naive bound on
the `n!` orderings would be `n! · τ^{-2(n-1)}`, and the packing lemma (1.15)
upgrades it to `√(n!)` up to `C^n`. -/
theorem toy_permSum_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (τ : ℝ), 0 < τ →
      ∀ x : Fin n → (Fin 4 → ℝ), Function.Injective x →
        (∀ i j, i ≠ j → τ ≤ ‖x i - x j‖) →
        ∑ π : Equiv.Perm (Fin n), chainWeight n (fun k => x (π k))
          ≤ C ^ n * Real.sqrt ((n)! : ℝ) * τ⁻¹ ^ (2 * (n - 1)) := by
  obtain ⟨C, hC1, hC⟩ := toy_injTuple_bound
  refine ⟨C, hC1, ?_⟩
  intro n τ hτ x hxinj hsep
  classical
  set A : Finset (Fin 4 → ℝ) := Finset.image x Finset.univ with hA
  have hcard : A.card = n := by
    rw [hA, Finset.card_image_of_injective _ hxinj, Finset.card_univ, Fintype.card_fin]
  have hsepA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → τ ≤ ‖a - b‖ := by
    intro a ha b hb hab
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hb
    exact hsep i j fun h => hab (by rw [h])
  have hinj2 : ∀ π₁ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))),
      ∀ π₂ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))),
      (fun k => x (π₁ k)) = (fun k => x (π₂ k)) → π₁ = π₂ := by
    intro π₁ _ π₂ _ h
    ext k
    exact congrArg Fin.val (hxinj (congrFun h k))
  have himg : ∑ f ∈ Finset.univ.image (fun π : Equiv.Perm (Fin n) => fun k => x (π k)),
      chainWeight n f
      = ∑ π : Equiv.Perm (Fin n), chainWeight n (fun k => x (π k)) :=
    Finset.sum_image hinj2
  rw [← himg]
  have hsub : Finset.univ.image (fun π : Equiv.Perm (Fin n) => fun k => x (π k))
      ⊆ injTuples n A := by
    intro f hf
    obtain ⟨π, _, rfl⟩ := Finset.mem_image.1 hf
    rw [mem_injTuples]
    exact ⟨fun i => Finset.mem_image_of_mem x (Finset.mem_univ _),
      fun i j hij => π.injective (hxinj hij)⟩
  calc ∑ f ∈ Finset.univ.image (fun π : Equiv.Perm (Fin n) => fun k => x (π k)),
        chainWeight n f
      ≤ ∑ f ∈ injTuples n A, chainWeight n f :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun f _ _ => chainWeight_nonneg n f
    _ ≤ C ^ n * Real.sqrt ((n)! : ℝ) * τ⁻¹ ^ (2 * (n - 1)) :=
        hC n n τ hτ A hcard hsepA le_rfl

end Anderson4D
