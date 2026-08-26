import Anderson4D.DetParametrix.Paper42_Moment.R324CentralAnchorBracket

/-!
# The anchor-resolved suffix sums, and the exact conserved-mode count

This file settles — by explicit arithmetic, *before* any analysis — the
question the central-anchor ledger turns on:

> how many of the Green brackets produced by collapsing
> `r324CentralAnchorHarvest` sit at the conserved mode `α + β`?

## The set-up

`r324Col_piChain_integral` evaluates an `n`-fold Green chain carrying one
character per internal coordinate to `r324ColPiProp n q`, one bracket
`⟨·⟩⁻²` per **suffix sum** `S_i = q_i + … + q_{n-1}`.  In the
anchor-resolved harvest the momentum at internal slot `j` of a half chain
is

`q_j = k_j + α·[j = 0] + β·[j = a]`,

where `k` are the free covariance modes of the cross legs and `a` is the
tail anchor of the entity (`r324CentralLastAnchor` puts `a = m - 1`).
That assignment is `r324AnchorKeys`.

## The count (this is the crux)

`r324Anchor_colPartial_eq` computes every prefix sum, hence
(`r324Anchor_suffix_eq`) every suffix sum:

`S_i = T_i(k) + α·[i = 0] + β·[i ≤ a]`,  `T_i(k) = k_i + … + k_{n-1}`.

So **as an identity in the free keys the conserved mode `α + β` occurs in
exactly one suffix sum, the head one `S_0`** — and `S_0` is precisely the
one that momentum conservation annihilates: the closed chain
(`r324Col_piChain_closed`) contributes only on `S_0 = 0`, where the head
bracket is `⟨0⟩⁻² = 1` (`r324Anchor_colBrk_zero`).  This is
`r324Anchor_head_suffix_zero_of_closed`.

On the closed sector the remaining suffix sums read
(`r324Anchor_suffix_closed`)

* `1 ≤ i ≤ a`  : `S_i = -α - P_i(k)`   — the *α* family;
* `a < i < n`  : `S_i = -(α+β) - P_i(k)` — the *conserved* family,

with `P_i(k) = k_0 + … + k_{i-1}` a **free** prefix sum that is summed
over.  Hence the number of brackets sitting at the conserved mode, up to
a free lattice shift, is exactly

`#{i | a < i < n} = n - 1 - a`   (`r324Anchor_conservedCount`).

**Consequences, stated as theorems below.**

* For the constant `r324CentralLastAnchor` (`a = n - 1`, the dominant
  term of the anchor resolution) the count is `0`
  (`r324Anchor_lastAnchor_conservedCount`): *no* Green bracket of that
  harvest sits at `α + β`.  So the candidate mechanism "four Green
  brackets carry the conserved mode" is **refuted**; the head bracket,
  which is the only one that carries `α + β` freely, is `1`.
* Even for the shortcut anchors the count `n - 1 - a` is not bounded
  below by `4` (it is `≤ n - 2`, and vanishes whenever `a = n - 1`), so
  no anchor choice funds `⟨α+β⟩⁻⁸` bracket-by-bracket.

## What the brackets *can* fund

The residual mechanism is the one through the free shifts: on the closed
sector `P_n(k) = -(α+β)`, so the keys must *sum* to the conserved mode,
and a large conserved mode forces a large key
(`r324Anchor_conserved_le_prod_keyBrackets`):

`1 + ‖α+β‖² ≤ (2^n·n + 1) · ∏_{j<n} (1 + ‖k_j‖²)`.

Each key bracket `⟨k_j⟩` is in turn bought from *two* neighbouring chain
brackets by Peetre (`r324Anchor_key_le_peetre`), and every chain bracket
is available to at most two keys.  So a half chain of `n` internal
coordinates carries `n - 1` brackets `⟨·⟩⁻²`, i.e. `2(n-1)` unit powers,
of which the telescoping consumes **all** of them to produce a single
power `⟨α+β⟩⁻¹`; two half chains give `⟨α+β⟩⁻²`.

**Exact power count: the two half chains of the anchor harvest fund
`⟨α+β⟩⁻²`, and do so only by spending their entire bracket budget.  The
ledger asks for `⟨α+β⟩⁻⁸` *and* a surviving `|log ε|^{m-1}` window sum.
The shortfall is six orders.**  Together with the proved
`r324Central_epsScale_gap` (the `ε`-scaled symbols miss by `ε⁻¹⁶`) and
`r324Central_endpointTrade_sq` (the endpoint trade needs `⟨α⟩⁻⁸⟨β⟩⁻⁸`
where only `⟨α⟩⁻⁴⟨β⟩⁻⁴` is on the table), all three single mechanisms
are now priced, and none of them closes `R324CentralAnchorLedger` on its
own.  `R324AnchorLedgerAssembly` therefore isolates the missing input as
one named Prop and assembles everything else.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## The anchor-resolved key assignment -/

/-- **The anchor-resolved momentum assignment of one half chain**: the
free covariance key `k j` at every internal slot, plus the head mode `α`
at slot `0` and the tail mode `β` at the anchor slot `a`. -/
def r324AnchorKeys (α β : Z4) (a : ℕ) (k : ℕ → Z4) : ℕ → Z4 :=
  fun j => k j + (if j = 0 then α else 0) + (if j = a then β else 0)

/-- With `k = 0` the anchor keys are the proved two-mode assignment
`r324CentralKeys`. -/
theorem r324AnchorKeys_zero (α β : Z4) {a : ℕ} (ha : 0 < a) :
    r324AnchorKeys α β a (fun _ => 0) = r324CentralKeys α β a := by
  funext j
  unfold r324AnchorKeys r324CentralKeys
  rcases eq_or_ne j 0 with hj | hj
  · subst hj
    simp [ha.ne]
  · rcases eq_or_ne j a with hja | hja
    · subst hja
      simp [hj]
    · simp [hj, hja]

/-! ## Every prefix sum, exactly -/

/-- **The prefix sums of the anchor keys.**  `α` enters as soon as the
prefix is nonempty; `β` enters as soon as the prefix passes the anchor. -/
theorem r324Anchor_colPartial_eq (α β : Z4) (a : ℕ) (k : ℕ → Z4) (i : ℕ) :
    r324ColPartial (r324AnchorKeys α β a k) i =
      r324ColPartial k i + (if 0 < i then α else 0) +
        (if a < i then β else 0) := by
  unfold r324ColPartial r324AnchorKeys
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · congr 1
    rw [Finset.sum_ite_eq' (Finset.range i) 0 (fun _ => α)]
    simp only [Finset.mem_range]
  · rw [Finset.sum_ite_eq' (Finset.range i) a (fun _ => β)]
    simp only [Finset.mem_range]

/-! ## Every suffix sum, exactly -/

/-- The suffix sum consumed by the `i`-th factor of `r324ColPiProp`. -/
def r324AnchorSuffix (q : ℕ → Z4) (n i : ℕ) : Z4 :=
  r324ColPartial (fun j => q (j + i)) (n - i)

/-- A suffix sum is the difference of two prefix sums. -/
theorem r324AnchorSuffix_eq_sub (q : ℕ → Z4) {n i : ℕ} (hi : i ≤ n) :
    r324AnchorSuffix q n i = r324ColPartial q n - r324ColPartial q i := by
  unfold r324AnchorSuffix r324ColPartial
  have hshift : (∑ j ∈ Finset.range (n - i), q (j + i)) =
      ∑ j ∈ Finset.Ico i n, q j := by
    rw [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_comm]
  rw [hshift, Finset.sum_Ico_eq_sub _ hi]

/-- **The suffix sums of the anchor keys.**  `α` occurs in the head
suffix only; `β` occurs in every suffix that starts at or before the
anchor. -/
theorem r324Anchor_suffix_eq (α β : Z4) {a : ℕ} (k : ℕ → Z4) {n i : ℕ}
    (hi : i ≤ n) (han : a < n) :
    r324AnchorSuffix (r324AnchorKeys α β a k) n i =
      r324AnchorSuffix k n i + (if i = 0 then α else 0) +
        (if i ≤ a then β else 0) := by
  rw [r324AnchorSuffix_eq_sub _ hi, r324AnchorSuffix_eq_sub _ hi,
    r324Anchor_colPartial_eq, r324Anchor_colPartial_eq]
  have hn : 0 < n := by omega
  split_ifs <;> first | (exfalso; omega) | abel

/-! ## The head suffix is the conserved mode, and conservation kills it -/

/-- **Momentum conservation at the head.**  The head suffix sum of the
anchor keys is the total key sum plus the conserved mode `α + β`. -/
theorem r324Anchor_head_suffix (α β : Z4) {a : ℕ} (k : ℕ → Z4) {n : ℕ}
    (han : a < n) :
    r324AnchorSuffix (r324AnchorKeys α β a k) n 0 =
      r324ColPartial k n + (α + β) := by
  rw [r324Anchor_suffix_eq α β k (by omega) han, if_pos rfl,
    if_pos (by omega), r324AnchorSuffix_eq_sub _ (by omega : 0 ≤ n)]
  unfold r324ColPartial
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero]
  abel

theorem r324Anchor_colBrk_zero : r324ColBrk 0 = 1 := by
  unfold r324ColBrk paperModeNormSq
  simp

/-- **The conserved bracket is `1`.**  The closed chain
(`r324Col_piChain_closed`) contributes only where the total momentum
vanishes, i.e. exactly where the *unique* suffix sum containing `α + β`
freely is zero.  So the one Green bracket that sits at the conserved mode
is `⟨0⟩⁻² = 1` and carries no decay at all. -/
theorem r324Anchor_head_suffix_zero_of_closed (α β : Z4) {a : ℕ}
    (k : ℕ → Z4) {n : ℕ} (_han : a < n)
    (hclosed : r324ColPartial (r324AnchorKeys α β a k) n = 0) :
    r324ColBrk (r324AnchorSuffix (r324AnchorKeys α β a k) n 0) = 1 := by
  have h0 : r324AnchorSuffix (r324AnchorKeys α β a k) n 0 = 0 := by
    rw [r324AnchorSuffix_eq_sub _ (by omega : 0 ≤ n), hclosed]
    unfold r324ColPartial
    simp
  rw [h0]
  exact r324Anchor_colBrk_zero

/-- **The key sum is minus the conserved mode.**  This is the only place
the conserved mode survives on the closed sector: as the *constraint* on
the free covariance keys. -/
theorem r324Anchor_key_sum_closed (α β : Z4) {a : ℕ} (k : ℕ → Z4) {n : ℕ}
    (han : a < n)
    (hclosed : r324ColPartial (r324AnchorKeys α β a k) n = 0) :
    r324ColPartial k n = -(α + β) := by
  have h := r324Anchor_head_suffix α β k han
  rw [r324AnchorSuffix_eq_sub _ (by omega : 0 ≤ n), hclosed] at h
  unfold r324ColPartial at h ⊢
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero] at h
  have h' : (0 : Z4) = ∑ j ∈ Finset.range n, k j + (α + β) := h
  linear_combination (norm := abel) -h'

/-- **Every non-head suffix sum, on the closed sector.**  For `1 ≤ i ≤ a`
the suffix carries `-α`; for `a < i` it carries `-(α+β)`.  In both cases
it is shifted by the free prefix sum `P_i(k)`, which is summed over. -/
theorem r324Anchor_suffix_closed (α β : Z4) {a : ℕ} (k : ℕ → Z4) {n i : ℕ}
    (hi0 : 0 < i) (hi : i ≤ n) (han : a < n)
    (hclosed : r324ColPartial (r324AnchorKeys α β a k) n = 0) :
    r324AnchorSuffix (r324AnchorKeys α β a k) n i =
      -(if i ≤ a then α else α + β) - r324ColPartial k i := by
  rw [r324Anchor_suffix_eq α β k hi han, r324AnchorSuffix_eq_sub _ hi,
    r324Anchor_key_sum_closed α β k han hclosed]
  split_ifs <;> first | (exfalso; omega) | abel

/-! ## The exact conserved-mode count -/

/-- **The conserved-mode bracket count.**  On the closed sector the
suffix sums that carry the full conserved mode `α + β` (up to a free
lattice shift) are exactly those with index `i` in `(a, n)`, so there are
`n - 1 - a` of them.  (Index `0` is excluded: its bracket is `1`.) -/
theorem r324Anchor_conservedCount {a n : ℕ} (han : a < n) :
    ((Finset.Ico 1 n).filter (fun i => a < i)).card = n - 1 - a := by
  have hEq : (Finset.Ico 1 n).filter (fun i => a < i) =
      Finset.Ico (a + 1) n := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by omega, h2⟩, by omega⟩
  rw [hEq, Nat.card_Ico]
  omega

/-- **The last anchor carries no conserved bracket.**  This is the
dominant term of the anchor resolution (`r324CentralLastAnchor` puts the
tail character at slot `m - 1`), and for it the conserved-mode bracket
count is `0`: the eighth-order `ε`-free bracket cannot be read off the
Green brackets of this half chain. -/
theorem r324Anchor_lastAnchor_conservedCount {n : ℕ} (hn : 0 < n) :
    ((Finset.Ico 1 n).filter (fun i => n - 1 < i)).card = 0 := by
  rw [r324Anchor_conservedCount (a := n - 1) (by omega)]
  omega

/-- **No anchor funds eight orders.**  Both half chains together offer at
most `2·(n-2)` conserved-mode brackets, i.e. `⟨α+β⟩^{-4(n-2)}`, and the
count is `0` at the last anchor; in particular the count is not `≥ 4` at
the orders `n = 2, 3` the capped ledger must cover. -/
theorem r324Anchor_conservedCount_le {a n : ℕ} (han : a < n) (ha : 0 < a) :
    ((Finset.Ico 1 n).filter (fun i => a < i)).card ≤ n - 2 := by
  rw [r324Anchor_conservedCount han]
  omega

/-! ## What the brackets do fund: a large key is forced -/

theorem r324Anchor_paperModeNormSq_zero : paperModeNormSq 0 = 0 := by
  unfold paperModeNormSq
  simp

theorem r324Anchor_paperModeNormSq_nonneg (k : Z4) :
    0 ≤ paperModeNormSq k := by
  unfold paperModeNormSq
  positivity

/-- The mode norm of a range sum, with a geometric constant. -/
theorem r324Anchor_paperModeNormSq_sum_le : ∀ (n : ℕ) (k : ℕ → Z4),
    paperModeNormSq (∑ j ∈ Finset.range n, k j) ≤
      2 ^ n * ∑ j ∈ Finset.range n, paperModeNormSq (k j) := by
  intro n
  induction n with
  | zero =>
      intro k
      simp [r324Anchor_paperModeNormSq_zero]
  | succ n ih =>
      intro k
      rw [Finset.sum_range_succ' k n]
      refine le_trans (paperModeNormSq_add_le _ _) ?_
      have h1 : paperModeNormSq (∑ j ∈ Finset.range n, k (j + 1)) ≤
          2 ^ n * ∑ j ∈ Finset.range n, paperModeNormSq (k (j + 1)) :=
        ih (fun j => k (j + 1))
      have h2 : (0 : ℝ) ≤ paperModeNormSq (k 0) :=
        r324Anchor_paperModeNormSq_nonneg _
      have h3 : (0 : ℝ) ≤ ∑ j ∈ Finset.range n, paperModeNormSq (k (j + 1)) :=
        Finset.sum_nonneg fun j _ => r324Anchor_paperModeNormSq_nonneg _
      have h4 : (2 : ℝ) ≤ 2 ^ (n + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n + 1) := by
              apply pow_le_pow_right₀ (by norm_num); omega
      rw [Finset.sum_range_succ' (fun j => paperModeNormSq (k j)) n]
      have hpow : (2 : ℝ) * (2 ^ n *
          ∑ j ∈ Finset.range n, paperModeNormSq (k (j + 1))) =
          2 ^ (n + 1) * ∑ j ∈ Finset.range n, paperModeNormSq (k (j + 1)) := by
        ring
      nlinarith [h1, h2, h3, h4, mul_le_mul_of_nonneg_right h4 h2]

/-- Each summand is dominated by the product of the shifted summands. -/
theorem r324Anchor_single_le_prod {n : ℕ} (k : ℕ → Z4) {j : ℕ}
    (hj : j ∈ Finset.range n) :
    1 + paperModeNormSq (k j) ≤
      ∏ i ∈ Finset.range n, (1 + paperModeNormSq (k i)) := by
  have hle : ∀ i ∈ Finset.range n,
      (if i = j then 1 + paperModeNormSq (k i) else 1) ≤
        1 + paperModeNormSq (k i) := by
    intro i _
    rcases eq_or_ne i j with h | h
    · rw [if_pos h]
    · rw [if_neg h]
      have := r324Anchor_paperModeNormSq_nonneg (k i)
      linarith
  have hnn : ∀ i ∈ Finset.range n,
      (0 : ℝ) ≤ (if i = j then 1 + paperModeNormSq (k i) else 1) := by
    intro i _
    rcases eq_or_ne i j with h | h
    · rw [if_pos h]
      have := r324Anchor_paperModeNormSq_nonneg (k i)
      linarith
    · rw [if_neg h]; norm_num
  refine le_trans (le_of_eq ?_) (Finset.prod_le_prod hnn hle)
  rw [Finset.prod_ite_eq' (Finset.range n) j
    (fun i => 1 + paperModeNormSq (k i)), if_pos hj]

/-- **The conserved mode is bought from the key brackets.**  On the
closed sector the free keys must sum to `-(α+β)`, so a large conserved
mode forces a large key: the product of the key brackets dominates the
conserved bracket, with a geometric constant.  This — not any single
Green bracket — is the only route from the chain to `⟨α+β⟩⁻¹`. -/
theorem r324Anchor_conserved_le_prod_keyBrackets (n : ℕ) (k : ℕ → Z4) :
    1 + paperModeNormSq (r324ColPartial k n) ≤
      (2 ^ n * n + 1) * ∏ j ∈ Finset.range n, (1 + paperModeNormSq (k j)) := by
  set P : ℝ := ∏ j ∈ Finset.range n, (1 + paperModeNormSq (k j)) with hP
  have hP1 : (1 : ℝ) ≤ P := by
    rw [hP]
    have h := Finset.prod_le_prod (s := Finset.range n)
      (f := fun _ : ℕ => (1 : ℝ))
      (g := fun j => 1 + paperModeNormSq (k j))
      (fun _ _ => zero_le_one)
      (fun i _ => by
        have := r324Anchor_paperModeNormSq_nonneg (k i); linarith)
    simpa using h
  have hsum : (∑ j ∈ Finset.range n, paperModeNormSq (k j)) ≤ n * P := by
    have hstep : ∀ j ∈ Finset.range n, paperModeNormSq (k j) ≤ P := by
      intro j hj
      have h := r324Anchor_single_le_prod (n := n) k hj
      have := r324Anchor_paperModeNormSq_nonneg (k j)
      rw [hP]
      linarith [h]
    calc (∑ j ∈ Finset.range n, paperModeNormSq (k j)) ≤
        ∑ _j ∈ Finset.range n, P := Finset.sum_le_sum hstep
      _ = n * P := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmain : paperModeNormSq (r324ColPartial k n) ≤ 2 ^ n * (n * P) := by
    refine le_trans (r324Anchor_paperModeNormSq_sum_le n k) ?_
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  nlinarith [hmain, hP1]

/-- **Peetre for a key.**  A single key bracket is bought from the two
neighbouring chain brackets: the key is the difference of two consecutive
prefix sums, and Peetre's inequality prices that difference. -/
theorem r324Anchor_key_le_peetre (x y : Z4) :
    1 + paperModeNormSq (x - y) ≤
      2 * ((1 + paperModeNormSq x) * (1 + paperModeNormSq y)) := by
  have h := r324Central_peetre x (-y)
  rw [show x + -y = x - y by abel] at h
  rwa [paperModeNormSq_neg] at h

end

end Anderson4D
