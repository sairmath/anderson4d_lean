import Anderson4D.Continuum.Basic

/-!
# The σ-grading count: the arithmetic that clause A actually needs

The permutation-grading estimate asks for `∑_{σ ∈ S_m} I(σ) ≤ K^m·L^{m-1}` with
`L = |log ε|` and the capped range `3 ≤ m ≤ ⌊L⌋`.  The proved
interface `R324CappedCrossGradingBoundAt` factors this through a grade
`r : S_m → ℕ` with

* a per-entity bound `I(σ) ≤ C^m·L^{r σ}`, and
* the **graded count** `∑_σ L^{r σ} ≤ C^m·L^{m-1}`.

This file proves the graded count from a purely combinatorial layer
hypothesis, and nothing else.  It is the half of the σ-grading that is
independent of any analysis.

## Deriving the requirement (the arithmetic, verified below)

The identity entity really is of size `≍ C^m·L^{m-1}`, so `r id = m-1`
is forced and the per-entity bound cannot be improved uniformly.  The
flat grade `r ≡ m-1` gives `∑_σ L^{r σ} = m!·L^{m-1}`, which is over
budget exactly once `m! > C^m` (`r324CappedCross_flatGrade_over_budget`).
On the capped range the order cap gives `m ≤ L` (`r324Grade_cast_le_log`
below), hence

`m! ≤ m^{m-1} ≤ L^{m-1}`  (`r324Grade_factorial_le_pow`),

so the flat grade is over budget by *exactly one* factor `L^{m-1}` and
no more.  Writing `N_j = #{σ : r σ = j}` the graded count reads
`∑_{j≤m-1} N_j·L^j ≤ C^m·L^{m-1}`, and since `m ≤ L` a sufficient
condition, uniform in `ε`, is

`N_j ≤ A^m·m^{m-1-j}`   (`r324Grade_sum_pow_le`),

equivalently — because `(m-j)! ≤ m^{m-1-j}` — the more quotable

`N_j ≤ A^m·(m-j)!`      (`r324Grade_sum_pow_le_of_factorial`).

**Each unit of grade must cost a factor `m` in the count.**  The two
ends of this criterion are exactly the two facts one knows: at `j = 0`
it is the trivial `N_0 ≤ m!`, and at `j = m-1` it is
`#{σ : r σ = m-1} ≤ A^m` — only geometrically many entities may carry
the full window power.  So **clause A's budget `K^m·L^{m-1}` is right
as stated**; no factorial allowance is needed, provided the analytic
grade decays with the count at this factorial rate.  (The `m = 3` slice
sits inside the criterion with room to spare: `r ≡ 2` there needs
`3! = 6 ≤ A³·(3-2)! = A³`, true for `A = 2`;
`r324Grade_three_flat_count` records it.)
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## The order cap -/

/-- **The order cap in analytic form.**  `truncOrder ε = ⌊|log ε|⌋`, so
a capped order satisfies `m ≤ L`.  This is the single inequality that
makes the factorial count affordable. -/
theorem r324Grade_cast_le_log {ε : ℝ} {m : ℕ} (hm : m ≤ truncOrder ε) :
    (m : ℝ) ≤ |Real.log ε| :=
  (Nat.le_floor_iff (abs_nonneg _)).mp hm

/-! ## `n! ≤ n^{n-1}` -/

/-- `n! ≤ n^{n-1}`: the factorial is *below* the top window power. -/
theorem r324Grade_factorial_le_pow (n : ℕ) : n.factorial ≤ n ^ (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · have hsucc : n - 1 + 1 = n := by omega
        calc (n + 1).factorial = (n + 1) * n.factorial := rfl
          _ ≤ (n + 1) * n ^ (n - 1) := Nat.mul_le_mul_left _ ih
          _ ≤ (n + 1) * (n + 1) ^ (n - 1) :=
              Nat.mul_le_mul_left _
                (Nat.pow_le_pow_left (Nat.le_succ n) _)
          _ = (n + 1) ^ (n - 1 + 1) := by rw [pow_succ]; ring
          _ = (n + 1) ^ (n + 1 - 1) := by rw [hsucc]; norm_num


/-- The layer form: `(m-j)! ≤ m^{m-1-j}` for `j ≤ m-1`.  This is why the
factorial criterion implies the power criterion. -/
theorem r324Grade_factorial_sub_le (m j : ℕ) (hj : j ≤ m - 1) :
    (m - j).factorial ≤ m ^ (m - 1 - j) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp_all
  · have hjm : j ≤ m - 1 := hj
    have hj' : j < m := lt_of_le_of_lt hjm (Nat.sub_lt hm Nat.one_pos)
    have h1 : (m - j).factorial ≤ (m - j) ^ (m - j - 1) :=
      r324Grade_factorial_le_pow _
    have h2 : (m - j) ^ (m - j - 1) ≤ m ^ (m - j - 1) :=
      Nat.pow_le_pow_left (Nat.sub_le m j) _
    have h3 : m - j - 1 = m - 1 - j := by omega
    calc (m - j).factorial ≤ (m - j) ^ (m - j - 1) := h1
      _ ≤ m ^ (m - j - 1) := h2
      _ = m ^ (m - 1 - j) := by rw [h3]

/-! ## The graded count -/

/-- **The graded count from layer cardinalities.**  If every grade is at
most `m-1` and the `j`-th layer has at most `A^m·m^{m-1-j}` members,
then the graded sum obeys clause A's budget with constant `2A`, on the
capped range `m ≤ L`.

This is the exact statement `R324CappedCrossGradingBoundAt` needs for
its second clause; the proof is one line of power counting once the
sum is fibred over the grade:
`∑_j N_j·L^j ≤ ∑_j A^m·L^{m-1-j}·L^j = m·A^m·L^{m-1} ≤ (2A)^m·L^{m-1}`. -/
theorem r324Grade_sum_pow_le {α : Type*}
    (E : Finset α) (grade : α → ℕ) {m : ℕ} {A L : ℝ}
    (hA : 0 ≤ A) (hm : 1 ≤ m) (hL : (m : ℝ) ≤ L)
    (hgrade : ∀ e ∈ E, grade e ≤ m - 1)
    (hcount : ∀ j ≤ m - 1,
      (((E.filter fun e => grade e = j)).card : ℝ) ≤
        A ^ m * (m : ℝ) ^ (m - 1 - j)) :
    ∑ e ∈ E, L ^ grade e ≤ (2 * A) ^ m * L ^ (m - 1) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hL1 : (1 : ℝ) ≤ L := le_trans (by exact_mod_cast hm) hL
  have hL0 : (0 : ℝ) ≤ L := le_trans zero_le_one hL1
  have hAm : (0 : ℝ) ≤ A ^ m := pow_nonneg hA m
  -- fibre the sum over the grade
  have hmaps : ∀ e ∈ E, grade e ∈ Finset.range m := by
    intro e he
    exact Finset.mem_range.mpr (lt_of_le_of_lt (hgrade e he)
      (Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one hm) Nat.one_pos))
  have hfib :
      ∑ j ∈ Finset.range m, ∑ e ∈ E.filter (fun e => grade e = j),
          L ^ grade e = ∑ e ∈ E, L ^ grade e :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  rw [← hfib]
  have hlayer : ∀ j ∈ Finset.range m,
      (∑ e ∈ E.filter (fun e => grade e = j), L ^ grade e) ≤
        A ^ m * L ^ (m - 1) := by
    intro j hj
    have hjm : j ≤ m - 1 := by
      have := Finset.mem_range.mp hj
      omega
    have hconst : (∑ e ∈ E.filter (fun e => grade e = j), L ^ grade e) =
        ((E.filter fun e => grade e = j).card : ℝ) * L ^ j := by
      rw [Finset.sum_congr rfl (fun e he => by
        rw [(Finset.mem_filter.mp he).2]), Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    have hpow : (m : ℝ) ^ (m - 1 - j) ≤ L ^ (m - 1 - j) :=
      pow_le_pow_left₀ hm0 hL _
    calc ((E.filter fun e => grade e = j).card : ℝ) * L ^ j
        ≤ (A ^ m * (m : ℝ) ^ (m - 1 - j)) * L ^ j :=
          mul_le_mul_of_nonneg_right (hcount j hjm) (pow_nonneg hL0 j)
      _ ≤ (A ^ m * L ^ (m - 1 - j)) * L ^ j := by
          gcongr
      _ = A ^ m * L ^ (m - 1 - j + j) := by rw [pow_add]; ring
      _ = A ^ m * L ^ (m - 1) := by
          congr 2
          omega
  calc ∑ j ∈ Finset.range m, ∑ e ∈ E.filter (fun e => grade e = j),
        L ^ grade e
      ≤ ∑ _j ∈ Finset.range m, A ^ m * L ^ (m - 1) :=
        Finset.sum_le_sum hlayer
    _ = (m : ℝ) * (A ^ m * L ^ (m - 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ m * (A ^ m * L ^ (m - 1)) := by
        have hm2 : (m : ℝ) ≤ (2 : ℝ) ^ m := by
          exact_mod_cast Nat.lt_two_pow_self.le
        exact mul_le_mul_of_nonneg_right hm2
          (mul_nonneg hAm (pow_nonneg hL0 _))
    _ = (2 * A) ^ m * L ^ (m - 1) := by rw [mul_pow]; ring

/-- **The graded count from a factorial layer criterion.**  The
quotable form: if the `j`-th grade layer has at most `A^m·(m-j)!`
members then clause A's budget holds with constant `2A`.  At `j = 0`
this is the trivial `N_0 ≤ A^m·m!`; at `j = m-1` it is the sharp
requirement that only `A^m` entities carry the full window power. -/
theorem r324Grade_sum_pow_le_of_factorial {α : Type*}
    (E : Finset α) (grade : α → ℕ) {m : ℕ} {A L : ℝ}
    (hA : 0 ≤ A) (hm : 1 ≤ m) (hL : (m : ℝ) ≤ L)
    (hgrade : ∀ e ∈ E, grade e ≤ m - 1)
    (hcount : ∀ j ≤ m - 1,
      (((E.filter fun e => grade e = j)).card : ℝ) ≤
        A ^ m * ((m - j).factorial : ℝ)) :
    ∑ e ∈ E, L ^ grade e ≤ (2 * A) ^ m * L ^ (m - 1) := by
  refine r324Grade_sum_pow_le E grade hA hm hL hgrade ?_
  intro j hj
  refine (hcount j hj).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hA m)
  have := r324Grade_factorial_sub_le m j hj
  exact_mod_cast this

/-- The `m = 3` slice inside the criterion: the flat grade `r ≡ 2`
there needs `3! ≤ A³·(3-2)!`, i.e. `6 ≤ A³`, true for `A = 2`.  So the
proved order-three calibration is the `j = m-1` end of the factorial
criterion, with room to spare. -/
theorem r324Grade_three_flat_count :
    ((Nat.factorial 3 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 3 * ((3 - 2).factorial : ℝ) := by
  norm_num [Nat.factorial]

end

end Anderson4D
