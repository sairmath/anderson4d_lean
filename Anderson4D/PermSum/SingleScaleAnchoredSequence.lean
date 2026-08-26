import Anderson4D.PermSum.SingleScaleSequence

/-!
# Anchored bidirectional sequence gain

In the general case of paper Step 4, the position carrying the smallest
scale need not be the first position.  The paper then sums "left and right
separately" from that position.  This file implements exactly that
orientation:

* the left word starts at the anchor and reads the original word backwards;
* the right word starts at the anchor and reads the original word forwards;
* positions past either endpoint repeat the endpoint, hence contribute gain
  one;
* one global exception set is partitioned and reindexed into the two
  outward words.

For a fixed anchor, the original word injects into the pair consisting of
its padded left and right words.  The two unrestricted finite sums can
therefore be bounded independently by the rectangular form of Lemma 5.13.
Finally the at most `m` anchor positions cost only another exponential
factor.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## Words read outwards from an anchor -/

/--
Read a word from `a` towards the left.  After reaching position zero, keep
repeating the endpoint; all added consecutive-pair gains are therefore one.
-/
def anchoredLeftWord {α : Type*} {n : ℕ} (a : Fin (n + 1))
    (w : Fin (n + 1) → α) : Fin (n + 1) → α :=
  fun i =>
    if h : i.1 ≤ a.1 then
      w ⟨a.1 - i.1, by omega⟩
    else
      w ⟨0, Nat.zero_lt_succ n⟩

/--
Read a word from `a` towards the right.  After reaching the final position,
keep repeating that endpoint.
-/
def anchoredRightWord {α : Type*} {n : ℕ} (a : Fin (n + 1))
    (w : Fin (n + 1) → α) : Fin (n + 1) → α :=
  fun i =>
    if h : a.1 + i.1 < n + 1 then
      w ⟨a.1 + i.1, h⟩
    else
      w (Fin.last n)

@[simp] theorem anchoredLeftWord_zero {α : Type*} {n : ℕ}
    (a : Fin (n + 1)) (w : Fin (n + 1) → α) :
    anchoredLeftWord a w 0 = w a := by
  simp [anchoredLeftWord]

@[simp] theorem anchoredRightWord_zero {α : Type*} {n : ℕ}
    (a : Fin (n + 1)) (w : Fin (n + 1) → α) :
    anchoredRightWord a w 0 = w a := by
  rw [anchoredRightWord, dif_pos (by simpa using a.isLt)]
  congr 1

theorem anchoredLeftWord_recover {α : Type*} {n : ℕ}
    (a j : Fin (n + 1)) (w : Fin (n + 1) → α) (hj : j.1 ≤ a.1) :
    anchoredLeftWord a w
        ⟨a.1 - j.1, by omega⟩ = w j := by
  let i : Fin (n + 1) := ⟨a.1 - j.1, by omega⟩
  change anchoredLeftWord a w i = w j
  rw [anchoredLeftWord, dif_pos (by dsimp only [i]; omega)]
  congr 1
  apply Fin.ext
  dsimp only [i]
  omega

theorem anchoredRightWord_recover {α : Type*} {n : ℕ}
    (a j : Fin (n + 1)) (w : Fin (n + 1) → α) (hj : a.1 ≤ j.1) :
    anchoredRightWord a w
        ⟨j.1 - a.1, by omega⟩ = w j := by
  let i : Fin (n + 1) := ⟨j.1 - a.1, by omega⟩
  change anchoredRightWord a w i = w j
  rw [anchoredRightWord, dif_pos (by dsimp only [i]; omega)]
  congr 1
  apply Fin.ext
  dsimp only [i]
  omega

theorem anchoredOutwardPair_injective {α : Type*} {n : ℕ}
    (a : Fin (n + 1)) :
    Function.Injective fun w : Fin (n + 1) → α =>
      (anchoredLeftWord a w, anchoredRightWord a w) := by
  intro w v hwv
  have hleft :
      anchoredLeftWord a w = anchoredLeftWord a v :=
    congrArg Prod.fst hwv
  have hright :
      anchoredRightWord a w = anchoredRightWord a v :=
    congrArg Prod.snd hwv
  funext j
  by_cases hj : j.1 ≤ a.1
  · have h := congrFun hleft
      (⟨a.1 - j.1, by omega⟩ : Fin (n + 1))
    simpa [anchoredLeftWord_recover a j w hj,
      anchoredLeftWord_recover a j v hj] using h
  · have haj : a.1 ≤ j.1 := by omega
    have h := congrFun hright
      (⟨j.1 - a.1, by omega⟩ : Fin (n + 1))
    simpa [anchoredRightWord_recover a j w haj,
      anchoredRightWord_recover a j v haj] using h

theorem anchoredLeftWord_map {α β : Type*} {n : ℕ}
    (f : α → β) (a : Fin (n + 1)) (w : Fin (n + 1) → α) :
    anchoredLeftWord a (fun j => f (w j)) =
      fun j => f (anchoredLeftWord a w j) := by
  funext j
  simp only [anchoredLeftWord]
  split <;> rfl

theorem anchoredRightWord_map {α β : Type*} {n : ℕ}
    (f : α → β) (a : Fin (n + 1)) (w : Fin (n + 1) → α) :
    anchoredRightWord a (fun j => f (w j)) =
      fun j => f (anchoredRightWord a w j) := by
  funext j
  simp only [anchoredRightWord]
  split <;> rfl

/-! ## Reindexing one global exception set -/

/-- An original left edge is reflected into the outward-left indexing. -/
def anchoredLeftExceptionIndex {n : ℕ} (a : Fin (n + 1))
    (j : Fin n) : Fin n :=
  ⟨a.1 - 1 - j.1, by omega⟩

/-- An original right edge is translated into the outward-right indexing. -/
def anchoredRightExceptionIndex {n : ℕ} (a : Fin (n + 1))
    (j : Fin n) : Fin n :=
  ⟨j.1 - a.1, by omega⟩

/-- Exceptions on original edges strictly left of the anchor, reflected. -/
def anchoredLeftExceptions {n : ℕ} (a : Fin (n + 1))
    (E : Finset (Fin n)) : Finset (Fin n) :=
  (E.filter fun j => j.1 < a.1).image
    (anchoredLeftExceptionIndex a)

/-- Exceptions on original edges at or right of the anchor, translated. -/
def anchoredRightExceptions {n : ℕ} (a : Fin (n + 1))
    (E : Finset (Fin n)) : Finset (Fin n) :=
  (E.filter fun j => a.1 ≤ j.1).image
    (anchoredRightExceptionIndex a)

theorem card_anchoredLeftExceptions {n : ℕ} (a : Fin (n + 1))
    (E : Finset (Fin n)) :
    (anchoredLeftExceptions a E).card =
      (E.filter fun j => j.1 < a.1).card := by
  apply Finset.card_image_of_injOn
  intro i hi j hj hij
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [anchoredLeftExceptionIndex] at hval
  omega

theorem card_anchoredRightExceptions {n : ℕ} (a : Fin (n + 1))
    (E : Finset (Fin n)) :
    (anchoredRightExceptions a E).card =
      (E.filter fun j => a.1 ≤ j.1).card := by
  apply Finset.card_image_of_injOn
  intro i hi j hj hij
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [anchoredRightExceptionIndex] at hval
  omega

/-- The two side budgets are an exact partition of the one global budget. -/
theorem card_anchoredExceptions_add {n : ℕ} (a : Fin (n + 1))
    (E : Finset (Fin n)) :
    (anchoredLeftExceptions a E).card +
        (anchoredRightExceptions a E).card = E.card := by
  rw [card_anchoredLeftExceptions, card_anchoredRightExceptions]
  simpa only [not_lt] using
    (Finset.card_filter_add_card_filter_not
      (s := E) fun j : Fin n => j.1 < a.1)

theorem card_anchoredLeftExceptions_le {n : ℕ} (a : Fin (n + 1))
    (E : Finset (Fin n)) :
    (anchoredLeftExceptions a E).card ≤ E.card := by
  calc
    (anchoredLeftExceptions a E).card ≤
        (E.filter fun j => j.1 < a.1).card := by
      exact Finset.card_image_le
    _ ≤ E.card := Finset.card_filter_le _ _

theorem card_anchoredRightExceptions_le {n : ℕ} (a : Fin (n + 1))
    (E : Finset (Fin n)) :
    (anchoredRightExceptions a E).card ≤ E.card := by
  calc
    (anchoredRightExceptions a E).card ≤
        (E.filter fun j => a.1 ≤ j.1).card := by
      exact Finset.card_image_le
    _ ≤ E.card := Finset.card_filter_le _ _

/-! ## Dyadic gains and the two outward products -/

/-- One consecutive-pair gain for a code word of dyadic exponents. -/
noncomputable def anchoredCodeEdgeGain (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (w : Fin (n + 1) → Fin ν) (j : Fin n) : ℝ :=
  min 1 (((2 : ℝ) ^ e (w j.succ) /
    (2 : ℝ) ^ e (w j.castSucc)) ^ θ)

theorem anchoredCodeEdgeGain_nonneg (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (w : Fin (n + 1) → Fin ν) (j : Fin n) :
    0 ≤ anchoredCodeEdgeGain θ e w j := by
  exact le_min zero_le_one (Real.rpow_nonneg (by positivity) _)

theorem anchoredLeftWord_eq_first_of_anchor_le {α : Type*} {n : ℕ}
    (a i : Fin (n + 1)) (w : Fin (n + 1) → α) (hi : a.1 ≤ i.1) :
    anchoredLeftWord a w i = w 0 := by
  rw [anchoredLeftWord]
  split
  · congr 1
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  · rfl

theorem anchoredRightWord_eq_last_of_le_sum {α : Type*} {n : ℕ}
    (a i : Fin (n + 1)) (w : Fin (n + 1) → α)
    (hi : n ≤ a.1 + i.1) :
    anchoredRightWord a w i = w (Fin.last n) := by
  rw [anchoredRightWord]
  split
  · congr 1
    apply Fin.ext
    simp only [Fin.val_last]
    omega
  · rfl

/--
At a genuine original left edge, the outward-left word gives the reverse
ratio: its current endpoint is `j+1` and its next endpoint is `j`.
-/
theorem anchoredLeftCodeEdgeGain_at_original (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (w : Fin (n + 1) → Fin ν)
    (a : Fin (n + 1)) (j : Fin n) (hj : j.1 < a.1) :
    anchoredCodeEdgeGain θ e (anchoredLeftWord a w)
        (anchoredLeftExceptionIndex a j) =
      min 1 (((2 : ℝ) ^ e (w j.castSucc) /
        (2 : ℝ) ^ e (w j.succ)) ^ θ) := by
  have hcurr :
      anchoredLeftWord a w
          (anchoredLeftExceptionIndex a j).castSucc =
        w j.succ := by
    have hidx :
        (anchoredLeftExceptionIndex a j).castSucc =
          (⟨a.1 - j.succ.1, by
            simp only [Fin.val_succ]
            omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [anchoredLeftExceptionIndex, Fin.val_castSucc,
        Fin.val_succ]
      omega
    rw [hidx]
    exact anchoredLeftWord_recover a j.succ w
      (by
        simp only [Fin.val_succ]
        omega)
  have hnext :
      anchoredLeftWord a w
          (anchoredLeftExceptionIndex a j).succ =
        w j.castSucc := by
    have hidx :
        (anchoredLeftExceptionIndex a j).succ =
          (⟨a.1 - j.castSucc.1, by
            simp only [Fin.val_castSucc]
            omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [anchoredLeftExceptionIndex, Fin.val_succ,
        Fin.val_castSucc]
      omega
    rw [hidx]
    exact anchoredLeftWord_recover a j.castSucc w
      (by
        simp only [Fin.val_castSucc]
        omega)
  simp only [anchoredCodeEdgeGain, hcurr, hnext]

/-- At a genuine original right edge, the outward-right ratio is forward. -/
theorem anchoredRightCodeEdgeGain_at_original (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (w : Fin (n + 1) → Fin ν)
    (a : Fin (n + 1)) (j : Fin n) (hj : a.1 ≤ j.1) :
    anchoredCodeEdgeGain θ e (anchoredRightWord a w)
        (anchoredRightExceptionIndex a j) =
      anchoredCodeEdgeGain θ e w j := by
  have hcurr :
      anchoredRightWord a w
          (anchoredRightExceptionIndex a j).castSucc =
        w j.castSucc := by
    have hidx :
        (anchoredRightExceptionIndex a j).castSucc =
          (⟨j.castSucc.1 - a.1, by
            simp only [Fin.val_castSucc]
            omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [anchoredRightExceptionIndex, Fin.val_castSucc]
    rw [hidx]
    exact anchoredRightWord_recover a j.castSucc w
      (by
        simp only [Fin.val_castSucc]
        omega)
  have hnext :
      anchoredRightWord a w
          (anchoredRightExceptionIndex a j).succ =
        w j.succ := by
    have hidx :
        (anchoredRightExceptionIndex a j).succ =
          (⟨j.succ.1 - a.1, by
            simp only [Fin.val_succ]
            omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp only [anchoredRightExceptionIndex, Fin.val_succ]
      omega
    rw [hidx]
    exact anchoredRightWord_recover a j.succ w
      (by
        simp only [Fin.val_succ]
        omega)
  simp only [anchoredCodeEdgeGain, hcurr, hnext]

/-- Every padded edge after the genuine left segment has gain exactly one. -/
theorem anchoredLeftCodeEdgeGain_eq_one_of_anchor_le (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (w : Fin (n + 1) → Fin ν)
    (a : Fin (n + 1)) (j : Fin n) (hj : a.1 ≤ j.1) :
    anchoredCodeEdgeGain θ e (anchoredLeftWord a w) j = 1 := by
  rw [anchoredCodeEdgeGain,
    anchoredLeftWord_eq_first_of_anchor_le a j.castSucc w
      (by
        simp only [Fin.val_castSucc]
        exact hj),
    anchoredLeftWord_eq_first_of_anchor_le a j.succ w
      (by
        simp only [Fin.val_succ]
        omega)]
  have hne : (2 : ℝ) ^ e (w 0) ≠ 0 := by positivity
  simp [hne]

/-- Every padded edge after the genuine right segment has gain exactly one. -/
theorem anchoredRightCodeEdgeGain_eq_one_of_le_anchor_add (θ : ℝ)
    {n ν : ℕ} (e : Fin ν → ℤ) (w : Fin (n + 1) → Fin ν)
    (a : Fin (n + 1)) (j : Fin n) (hj : n ≤ a.1 + j.1) :
    anchoredCodeEdgeGain θ e (anchoredRightWord a w) j = 1 := by
  rw [anchoredCodeEdgeGain,
    anchoredRightWord_eq_last_of_le_sum a j.castSucc w
      (by
        simp only [Fin.val_castSucc]
        exact hj),
    anchoredRightWord_eq_last_of_le_sum a j.succ w
      (by
        simp only [Fin.val_succ]
        omega)]
  have hne : (2 : ℝ) ^ e (w (Fin.last n)) ≠ 0 := by positivity
  simp [hne]

noncomputable def anchoredLeftCodeWeight (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (E : Finset (Fin n)) (a : Fin (n + 1))
    (w : Fin (n + 1) → Fin ν) : ℝ :=
  ∏ j ∈ Finset.univ \ anchoredLeftExceptions a E,
    anchoredCodeEdgeGain θ e (anchoredLeftWord a w) j

noncomputable def anchoredRightCodeWeight (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (E : Finset (Fin n)) (a : Fin (n + 1))
    (w : Fin (n + 1) → Fin ν) : ℝ :=
  ∏ j ∈ Finset.univ \ anchoredRightExceptions a E,
    anchoredCodeEdgeGain θ e (anchoredRightWord a w) j

/--
The bidirectional weight: both products start at the same anchor, the left
one in reverse original order and the right one in original order.
-/
noncomputable def anchoredBidirectionalCodeWeight (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (E : Finset (Fin n)) (a : Fin (n + 1))
    (w : Fin (n + 1) → Fin ν) : ℝ :=
  anchoredLeftCodeWeight θ e E a w *
    anchoredRightCodeWeight θ e E a w

theorem anchoredLeftCodeWeight_nonneg (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (E : Finset (Fin n)) (a : Fin (n + 1))
    (w : Fin (n + 1) → Fin ν) :
    0 ≤ anchoredLeftCodeWeight θ e E a w := by
  exact Finset.prod_nonneg fun j _ =>
    anchoredCodeEdgeGain_nonneg θ e _ j

theorem anchoredRightCodeWeight_nonneg (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (E : Finset (Fin n)) (a : Fin (n + 1))
    (w : Fin (n + 1) → Fin ν) :
    0 ≤ anchoredRightCodeWeight θ e E a w := by
  exact Finset.prod_nonneg fun j _ =>
    anchoredCodeEdgeGain_nonneg θ e _ j

theorem anchoredBidirectionalCodeWeight_nonneg (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (E : Finset (Fin n)) (a : Fin (n + 1))
    (w : Fin (n + 1) → Fin ν) :
    0 ≤ anchoredBidirectionalCodeWeight θ e E a w :=
  mul_nonneg (anchoredLeftCodeWeight_nonneg θ e E a w)
    (anchoredRightCodeWeight_nonneg θ e E a w)

/-! ## Fixed-anchor and all-anchor bounds -/

/--
For a fixed anchor, left and right are bounded separately by Lemma 5.13.
The map from the original word to the pair of outward words is injective,
so enlarging to all pairs is a valid nonnegative overcount.
-/
theorem anchoredBidirectional_code_fixedAnchor_sum_le
    (θ : ℝ) (hθ : 0 < θ) (B : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (n ν : ℕ) (e : Fin ν → ℤ),
        ν ≤ n + 1 → Function.Injective e →
        ∀ E : Finset (Fin n), E.card ≤ B →
        ∀ a : Fin (n + 1),
          ∑ w : Fin (n + 1) → Fin ν,
              anchoredBidirectionalCodeWeight θ e E a w
            ≤ C ^ (n + 1) := by
  obtain ⟨C, hC, hseq⟩ :=
    sum_min_ratio_pow_skip_le_rect θ hθ B
  refine ⟨C ^ 2, by nlinarith [sq_nonneg C], ?_⟩
  intro n ν e hν he E hE a
  let W := Fin (n + 1) → Fin ν
  let φ : W → W × W :=
    fun w => (anchoredLeftWord a w, anchoredRightWord a w)
  let L : W → ℝ := fun u =>
    ∏ j ∈ Finset.univ \ anchoredLeftExceptions a E,
      anchoredCodeEdgeGain θ e u j
  let R : W → ℝ := fun u =>
    ∏ j ∈ Finset.univ \ anchoredRightExceptions a E,
      anchoredCodeEdgeGain θ e u j
  have hφ : Function.Injective φ :=
    anchoredOutwardPair_injective a
  have hEL : (anchoredLeftExceptions a E).card ≤ B :=
    (card_anchoredLeftExceptions_le a E).trans hE
  have hER : (anchoredRightExceptions a E).card ≤ B :=
    (card_anchoredRightExceptions_le a E).trans hE
  have hL : (∑ u : W, L u) ≤ C ^ (n + 1) := by
    simpa [L, anchoredCodeEdgeGain] using
      hseq n ν e hν he (anchoredLeftExceptions a E) hEL
  have hR : (∑ u : W, R u) ≤ C ^ (n + 1) := by
    simpa [R, anchoredCodeEdgeGain] using
      hseq n ν e hν he (anchoredRightExceptions a E) hER
  have hsumL : 0 ≤ ∑ u : W, L u :=
    Finset.sum_nonneg fun u _ =>
      Finset.prod_nonneg fun j _ =>
        anchoredCodeEdgeGain_nonneg θ e u j
  have hsumR : 0 ≤ ∑ u : W, R u :=
    Finset.sum_nonneg fun u _ =>
      Finset.prod_nonneg fun j _ =>
        anchoredCodeEdgeGain_nonneg θ e u j
  calc
    (∑ w : W, anchoredBidirectionalCodeWeight θ e E a w) =
        ∑ w : W, L (φ w).1 * R (φ w).2 := by
      simp only [anchoredBidirectionalCodeWeight,
        anchoredLeftCodeWeight, anchoredRightCodeWeight, L, R, φ]
    _ = ∑ p ∈ Finset.univ.image φ, L p.1 * R p.2 := by
      symm
      exact Finset.sum_image
        (fun x _hx y _hy hxy => hφ hxy)
    _ ≤ ∑ p : W × W, L p.1 * R p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _)
        (fun p _hp _himage =>
          mul_nonneg
            (Finset.prod_nonneg fun j _ =>
              anchoredCodeEdgeGain_nonneg θ e p.1 j)
            (Finset.prod_nonneg fun j _ =>
              anchoredCodeEdgeGain_nonneg θ e p.2 j))
    _ = (∑ u : W, L u) * ∑ v : W, R v := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
    _ ≤ C ^ (n + 1) * C ^ (n + 1) :=
      mul_le_mul hL hR hsumR (pow_nonneg (le_trans zero_le_one hC) _)
    _ = (C ^ 2) ^ (n + 1) := by
      rw [← mul_pow]
      ring

/--
Sum also over the choice of anchor position.  Since there are `n+1`
positions and `n+1 ≤ 2^(n+1)`, that final choice is absorbed into the
universal exponential base.
-/
theorem anchoredBidirectional_code_sum_le
    (θ : ℝ) (hθ : 0 < θ) (B : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (n ν : ℕ) (e : Fin ν → ℤ),
        ν ≤ n + 1 → Function.Injective e →
        ∀ E : Finset (Fin n), E.card ≤ B →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → Fin ν,
              anchoredBidirectionalCodeWeight θ e E a w
            ≤ C ^ (n + 1) := by
  obtain ⟨C, hC, hfixed⟩ :=
    anchoredBidirectional_code_fixedAnchor_sum_le θ hθ B
  refine ⟨2 * C, by nlinarith, ?_⟩
  intro n ν e hν he E hE
  have hM :
      ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
    exact_mod_cast Nat.le_of_lt (n + 1).lt_two_pow_self
  calc
    (∑ a : Fin (n + 1),
        ∑ w : Fin (n + 1) → Fin ν,
          anchoredBidirectionalCodeWeight θ e E a w) ≤
        ∑ _a : Fin (n + 1), C ^ (n + 1) :=
      Finset.sum_le_sum fun a _ => hfixed n ν e hν he E hE a
    _ = ((n + 1 : ℕ) : ℝ) * C ^ (n + 1) := by simp
    _ ≤ (2 : ℝ) ^ (n + 1) * C ^ (n + 1) :=
      mul_le_mul_of_nonneg_right hM
        (pow_nonneg (le_trans zero_le_one hC) _)
    _ = (2 * C) ^ (n + 1) := by rw [mul_pow]

/-! ## Reindexing to the active paper carrier -/

/-- One consecutive-pair gain on the actual active `P` carrier. -/
noncomputable def anchoredActivePEdgeGain (θ : ℝ) {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t} {n : ℕ}
    (w : Fin (n + 1) → ActivePClass Nm mu) (j : Fin n) : ℝ :=
  min 1 (((((w j.succ).1 : ℕ) : ℝ) /
    (((w j.castSucc).1 : ℕ) : ℝ)) ^ θ)

/-- Actual-carrier form of the two products read outwards from the anchor. -/
noncomputable def anchoredBidirectionalActivePWeight (θ : ℝ)
    {t : PlaneTree} {Nm : HeppMarking t} {mu : Multiplicities t}
    {n : ℕ} (E : Finset (Fin n)) (a : Fin (n + 1))
    (w : Fin (n + 1) → ActivePClass Nm mu) : ℝ :=
  (∏ j ∈ Finset.univ \ anchoredLeftExceptions a E,
      anchoredActivePEdgeGain θ (anchoredLeftWord a w) j) *
    ∏ j ∈ Finset.univ \ anchoredRightExceptions a E,
      anchoredActivePEdgeGain θ (anchoredRightWord a w) j

theorem anchoredActivePEdgeGain_enumeration (θ : ℝ)
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    {n : ℕ}
    (x : Fin (n + 1) → Fin (activePCount Nm mu)) (j : Fin n) :
    anchoredActivePEdgeGain θ
        (fun i => activePEnumeration Nm mu (x i)) j =
      anchoredCodeEdgeGain θ (activePExponent Nm mu) x j := by
  unfold anchoredActivePEdgeGain anchoredCodeEdgeGain
  rw [activePEnumeration_cast_eq_zpow Nm mu (x j.succ),
    activePEnumeration_cast_eq_zpow Nm mu (x j.castSucc)]

theorem anchoredBidirectionalActivePWeight_enumeration (θ : ℝ)
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    {n : ℕ} (E : Finset (Fin n)) (a : Fin (n + 1))
    (x : Fin (n + 1) → Fin (activePCount Nm mu)) :
    anchoredBidirectionalActivePWeight θ E a
        (fun i => activePEnumeration Nm mu (x i)) =
      anchoredBidirectionalCodeWeight θ
        (activePExponent Nm mu) E a x := by
  unfold anchoredBidirectionalActivePWeight
    anchoredBidirectionalCodeWeight anchoredLeftCodeWeight
    anchoredRightCodeWeight
  rw [anchoredLeftWord_map, anchoredRightWord_map]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro j _hj
    exact anchoredActivePEdgeGain_enumeration θ Nm mu
      (anchoredLeftWord a x) j
  · apply Finset.prod_congr rfl
    intro j _hj
    exact anchoredActivePEdgeGain_enumeration θ Nm mu
      (anchoredRightWord a x) j

/--
Assembly-facing active-`P` form for an arbitrary positive exponent and
fixed global exception budget.  The constant is outside the tree, marking,
multiplicity, length, exception, anchor, and word quantifiers.
-/
theorem anchoredBidirectional_activeP
    (θ : ℝ) (hθ : 0 < θ) (B : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (n : ℕ), activePCount Nm mu ≤ n + 1 →
        ∀ E : Finset (Fin n), E.card ≤ B →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredBidirectionalActivePWeight θ E a w
            ≤ C ^ (n + 1) := by
  obtain ⟨C, hC, hcode⟩ :=
    anchoredBidirectional_code_sum_le θ hθ B
  refine ⟨C, hC, ?_⟩
  intro t Nm mu n hν E hE
  have hbound :=
    hcode n (activePCount Nm mu) (activePExponent Nm mu)
      hν (activePExponent_injective Nm mu) E hE
  let wordEquiv := activePWordEquiv Nm mu (n + 1)
  have hreindex : (∑ a : Fin (n + 1),
      ∑ x : Fin (n + 1) → Fin (activePCount Nm mu),
        anchoredBidirectionalCodeWeight θ
          (activePExponent Nm mu) E a x) =
      ∑ a : Fin (n + 1),
        ∑ w : Fin (n + 1) → ActivePClass Nm mu,
          anchoredBidirectionalActivePWeight θ E a w := by
    apply Fintype.sum_congr
    intro a
    apply Fintype.sum_equiv wordEquiv
    intro x
    exact
      (anchoredBidirectionalActivePWeight_enumeration
        θ Nm mu E a x).symm
  rw [← hreindex]
  exact hbound

/--
The local inequalities initially produce the `1/8` gain.  This specialization
is retained for the inner-estimate boundary.
-/
theorem anchoredBidirectional_activeP_oneEighth_hundred :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (n : ℕ), activePCount Nm mu ≤ n + 1 →
        ∀ E : Finset (Fin n), E.card ≤ 100 →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredBidirectionalActivePWeight (1 / 8 : ℝ) E a w
            ≤ C ^ (n + 1) :=
  anchoredBidirectional_activeP (1 / 8 : ℝ) (by norm_num) 100

/--
Counting interface at the `1/16` exponent used by the separately proved
even/odd geometric-mean assembly in Step 4.
-/
theorem anchoredBidirectional_activeP_oneSixteenth_hundred :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (n : ℕ), activePCount Nm mu ≤ n + 1 →
        ∀ E : Finset (Fin n), E.card ≤ 100 →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredBidirectionalActivePWeight (1 / 16 : ℝ) E a w
            ≤ C ^ (n + 1) :=
  anchoredBidirectional_activeP (1 / 16 : ℝ) (by norm_num) 100

/--
Counting interface at the paper's weakened `1/20` exponent, for use after
the separately proved outer/inner Hölder allocation.
-/
theorem anchoredBidirectional_activeP_oneTwentieth_hundred :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (n : ℕ), activePCount Nm mu ≤ n + 1 →
        ∀ E : Finset (Fin n), E.card ≤ 100 →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredBidirectionalActivePWeight (1 / 20 : ℝ) E a w
            ≤ C ^ (n + 1) :=
  anchoredBidirectional_activeP (1 / 20 : ℝ) (by norm_num) 100

/-!
The literal paper-length specialization.  Here `n = m - 1` is the number
of adjacent edges and the outer sum ranges over all `m` possible anchor
positions.
-/
theorem anchoredBidirectional_totalMultiplicity
    (θ : ℝ) (hθ : 0 < θ) (B : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t),
        let n := totalMultiplicity mu - 1
        ∀ E : Finset (Fin n), E.card ≤ B →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredBidirectionalActivePWeight θ E a w
            ≤ C ^ totalMultiplicity mu := by
  obtain ⟨C, hC, hbound⟩ :=
    anchoredBidirectional_activeP θ hθ B
  refine ⟨C, hC, ?_⟩
  intro t Nm mu
  dsimp only
  intro E hE
  have hm1 : 1 ≤ totalMultiplicity mu :=
    le_trans (by omega) (two_le_totalMultiplicity mu)
  have hlen :
      totalMultiplicity mu - 1 + 1 = totalMultiplicity mu :=
    Nat.sub_add_cancel hm1
  have hν :
      activePCount Nm mu ≤ totalMultiplicity mu - 1 + 1 := by
    rw [hlen]
    exact activePCount_le_totalMultiplicity Nm mu
  have h :=
    hbound Nm mu (totalMultiplicity mu - 1) hν E hE
  simpa only [hlen] using h

theorem anchoredBidirectional_totalMultiplicity_oneEighth_hundred :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t),
        let n := totalMultiplicity mu - 1
        ∀ E : Finset (Fin n), E.card ≤ 100 →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredBidirectionalActivePWeight (1 / 8 : ℝ) E a w
            ≤ C ^ totalMultiplicity mu :=
  anchoredBidirectional_totalMultiplicity (1 / 8 : ℝ) (by norm_num) 100

theorem anchoredBidirectional_totalMultiplicity_oneSixteenth_hundred :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t),
        let n := totalMultiplicity mu - 1
        ∀ E : Finset (Fin n), E.card ≤ 100 →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredBidirectionalActivePWeight (1 / 16 : ℝ) E a w
            ≤ C ^ totalMultiplicity mu :=
  anchoredBidirectional_totalMultiplicity (1 / 16 : ℝ) (by norm_num) 100

theorem anchoredBidirectional_totalMultiplicity_oneTwentieth_hundred :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t),
        let n := totalMultiplicity mu - 1
        ∀ E : Finset (Fin n), E.card ≤ 100 →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredBidirectionalActivePWeight (1 / 20 : ℝ) E a w
            ≤ C ^ totalMultiplicity mu :=
  anchoredBidirectional_totalMultiplicity (1 / 20 : ℝ) (by norm_num) 100

/-! ## Paper specialization

The generic theorem above handles an arbitrary anchor and one global
exception set of any fixed budget.  The `1/8`, budget-`100` result is
stronger than the paper's intermediate 20/40-exception uses.  In
particular, no pointwise comparison between a forward and a reverse gain
is used: the two outward finite sums are independent applications of
Lemma 5.13.
-/

theorem anchoredBidirectional_code_oneEighth_hundred :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (n ν : ℕ) (e : Fin ν → ℤ),
        ν ≤ n + 1 → Function.Injective e →
        ∀ E : Finset (Fin n), E.card ≤ 100 →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → Fin ν,
              anchoredBidirectionalCodeWeight (1 / 8 : ℝ) e E a w
            ≤ C ^ (n + 1) :=
  anchoredBidirectional_code_sum_le (1 / 8 : ℝ) (by norm_num) 100

end

end Anderson4D
