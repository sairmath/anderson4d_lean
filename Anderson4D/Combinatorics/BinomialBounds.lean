import Mathlib

/-!
# Binomial and multinomial bounds for lacunary exponent tuples

Paper: L-5.12 — (5.49)–(5.51) — binomial/lacunary bounds

Formalization of **Definition 5.11** and **Lemma 5.12** of Deng–Shen
(arXiv:2607.10105), PAPER_MAP nodes **D-5.11** and **L-5.12**.

* `Anderson4D.choose_le_pow_mul_pow` — paper (5.49): for `α > 1` and all
  `m, n`, `(m+n).choose m ≤ α ^ m * β ^ n` with the explicit constant
  `β = α / (α - 1)`.
* `Anderson4D.Lacunary` — paper Def 5.11: a family `n : ι → ℕ` is
  `K`-lacunary on `s` if every dyadic-type window `[X, 2X)` with `X ≥ 1`
  contains at most `K` of its members.
* `Anderson4D.multinomial_le_pow_mul_pow` — paper (5.50): the multinomial
  coefficient of `(n 0, …, n (r-1))` is at most
  `α ^ (∑ i, (i+1) * n i) * β ^ (∑ i, n i)`.
* `Anderson4D.multinomial_le_pow_of_lacunary` — paper (5.51): for a
  `K`-lacunary family the multinomial coefficient is at most `C(K) ^ (∑ i, n i)`
  with a constant depending only on `K`.

The proof of (5.49) follows the paper: for `t = 1/(α-1) > 0` the term `k = m`
of the binomial expansion of `(t+1)^(m+n)` dominates `(m+n).choose m * t^m`,
and `α * t = 1 + t`, `α/(α-1) = 1 + t` turn the resulting quotient into
`α ^ m * (α/(α-1)) ^ n`.
-/

namespace Anderson4D

open Finset

/-- **Paper (5.49), Lemma 5.12.**  For `α > 1` and all `m n : ℕ`,
`(m+n).choose m ≤ α ^ m * β ^ n` with the explicit constant `β = α / (α - 1)`. -/
theorem choose_le_pow_mul_pow (α : ℝ) (hα : 1 < α) :
    ∀ m n : ℕ, ((m + n).choose m : ℝ) ≤ α ^ m * (α / (α - 1)) ^ n := by
  intro m n
  have hα1 : (0 : ℝ) < α - 1 := by linarith
  have hα1' : α - 1 ≠ 0 := ne_of_gt hα1
  set t : ℝ := 1 / (α - 1) with ht_def
  have ht : 0 < t := by positivity
  have hαt : α * t = 1 + t := by
    rw [ht_def]; field_simp; ring
  have hβ : α / (α - 1) = 1 + t := by
    rw [ht_def]; field_simp; ring
  -- the `k = m` term of the binomial expansion of `(t+1)^(m+n)`
  have key : ((m + n).choose m : ℝ) * t ^ m ≤ (t + 1) ^ (m + n) := by
    have hm : m ∈ Finset.range (m + n + 1) := Finset.mem_range.mpr (by omega)
    calc ((m + n).choose m : ℝ) * t ^ m
        = t ^ m * (1 : ℝ) ^ (m + n - m) * ((m + n).choose m : ℝ) := by
          rw [one_pow]; ring
      _ ≤ ∑ k ∈ Finset.range (m + n + 1),
            t ^ k * (1 : ℝ) ^ (m + n - k) * ((m + n).choose k : ℝ) :=
          Finset.single_le_sum
            (f := fun k => t ^ k * (1 : ℝ) ^ (m + n - k) * ((m + n).choose k : ℝ))
            (fun i _ => by positivity) hm
      _ = (t + 1) ^ (m + n) := (add_pow t 1 (m + n)).symm
  -- rewrite the right-hand side as `α ^ m * β ^ n * t ^ m`
  have hfac : α ^ m * (α / (α - 1)) ^ n * t ^ m = (t + 1) ^ (m + n) := by
    rw [hβ, pow_add]
    have h1 : α ^ m * t ^ m = (t + 1) ^ m := by
      rw [← mul_pow, hαt, add_comm]
    calc α ^ m * (1 + t) ^ n * t ^ m = α ^ m * t ^ m * (1 + t) ^ n := by ring
      _ = (t + 1) ^ m * (t + 1) ^ n := by rw [h1, add_comm 1 t]
  exact le_of_mul_le_mul_right (key.trans_eq hfac.symm) (pow_pos ht m)

/-- **Paper (5.49), convenience form.**  Any `β ≥ α/(α-1)` works on the right. -/
theorem choose_le_pow_mul_pow' (α β : ℝ) (hα : 1 < α) (hβ : α / (α - 1) ≤ β)
    (m n : ℕ) : ((m + n).choose m : ℝ) ≤ α ^ m * β ^ n := by
  refine (choose_le_pow_mul_pow α hα m n).trans ?_
  have h0 : (0 : ℝ) ≤ α / (α - 1) := by
    have : (0 : ℝ) < α - 1 := by linarith
    positivity
  have hαpos : (0 : ℝ) ≤ α ^ m := by positivity
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hβ n) hαpos

/-- **Paper Definition 5.11 (node D-5.11).**  A family of integers
`n : ι → ℕ`, indexed by a finite set `s`, is *`K`-lacunary* if for every
`X ≥ 1` the window `[X, 2X)` contains at most `K` of the values `n j`, `j ∈ s`
(counted with multiplicity of indices). -/
def Lacunary (K : ℕ) {ι : Type*} (s : Finset ι) (n : ι → ℕ) : Prop :=
  ∀ X : ℕ, 1 ≤ X → (s.filter fun j => X ≤ n j ∧ n j < 2 * X).card ≤ K

/-- The multinomial coefficient of a mapped finset: reindexing along an
embedding.  Auxiliary for the `Fin`-recursion in paper (5.50). -/
theorem multinomial_map {ι κ : Type*} (e : ι ↪ κ) (s : Finset ι) (f : κ → ℕ) :
    Nat.multinomial (s.map e) f = Nat.multinomial s (f ∘ e) := by
  simp only [Nat.multinomial, Finset.sum_map, Finset.prod_map, Function.comp_apply]

/-- The multinomial coefficient over `univ` is invariant under precomposition
with an equivalence of the (finite) index type.  This is the permutation
invariance used to reduce paper (5.51) to a sorted tuple. -/
theorem multinomial_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : κ → ℕ) :
    Nat.multinomial Finset.univ (f ∘ e) = Nat.multinomial Finset.univ f := by
  simp only [Nat.multinomial, Function.comp_apply]
  rw [Equiv.sum_comp e f, Equiv.prod_comp e fun x => Nat.factorial (f x)]

/-- Lacunarity (Def 5.11) on `univ` is invariant under precomposition with an
equivalence of the index type. -/
theorem lacunary_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] {K : ℕ}
    {n : κ → ℕ} (e : ι ≃ κ) (h : Lacunary K Finset.univ n) :
    Lacunary K Finset.univ (n ∘ e) := by
  intro X hX
  refine le_trans (le_of_eq (Finset.card_equiv e fun i => ?_)) (h X hX)
  simp [Function.comp_apply]

/-- Sharp form of paper **(5.50)** with 0-based weights `i.val`: splitting off
the first index, the telescoping of (5.54) is exact for these weights. -/
theorem multinomial_le_pow_mul_pow_aux (α : ℝ) (hα : 1 < α) :
    ∀ (r : ℕ) (n : Fin r → ℕ),
      (Nat.multinomial Finset.univ n : ℝ)
        ≤ α ^ (∑ i, i.val * n i) * (α / (α - 1)) ^ (∑ i, n i) := by
  intro r
  induction r with
  | zero =>
      intro n
      simp [Finset.univ_eq_empty]
  | succ r ih =>
      intro n
      have hβ0 : (0 : ℝ) < α / (α - 1) := div_pos (by linarith) (by linarith)
      have hα0 : (0 : ℝ) < α := by linarith
      have hsplit : Nat.multinomial (Finset.univ : Finset (Fin (r + 1))) n
          = (n 0 + ∑ i : Fin r, n i.succ).choose (n 0)
            * Nat.multinomial Finset.univ (n ∘ Fin.succ) := by
        rw [Fin.univ_succ, Nat.multinomial_cons, multinomial_map]
        simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
      -- the split-off binomial factor, bounded by (5.49)
      have h1 : ((n 0 + ∑ i : Fin r, n i.succ).choose (n 0) : ℝ)
          ≤ α ^ (∑ i : Fin r, n i.succ) * (α / (α - 1)) ^ (n 0) := by
        have h := choose_le_pow_mul_pow α hα (∑ i : Fin r, n i.succ) (n 0)
        rwa [Nat.choose_symm_add, add_comm (∑ i : Fin r, n i.succ) (n 0)] at h
      -- inductive bound for the remaining multinomial
      have h2 : (Nat.multinomial Finset.univ (n ∘ Fin.succ) : ℝ)
          ≤ α ^ (∑ i : Fin r, i.val * n i.succ)
            * (α / (α - 1)) ^ (∑ i : Fin r, n i.succ) := by
        simpa [Function.comp_apply] using ih (n ∘ Fin.succ)
      -- exponent bookkeeping
      have E1 : ∑ i : Fin (r + 1), i.val * n i
          = (∑ i : Fin r, n i.succ) + ∑ i : Fin r, i.val * n i.succ := by
        rw [Fin.sum_univ_succ (f := fun i => i.val * n i)]
        simp only [Fin.val_zero, zero_mul, zero_add, Fin.val_succ, add_mul,
          one_mul, Finset.sum_add_distrib]
        omega
      have E2 : ∑ i : Fin (r + 1), n i = n 0 + ∑ i : Fin r, n i.succ :=
        Fin.sum_univ_succ n
      rw [hsplit, E1, E2]
      push_cast
      calc ((n 0 + ∑ i : Fin r, n i.succ).choose (n 0) : ℝ)
            * (Nat.multinomial Finset.univ (n ∘ Fin.succ) : ℝ)
          ≤ (α ^ (∑ i : Fin r, n i.succ) * (α / (α - 1)) ^ (n 0))
            * (α ^ (∑ i : Fin r, i.val * n i.succ)
              * (α / (α - 1)) ^ (∑ i : Fin r, n i.succ)) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = α ^ ((∑ i : Fin r, n i.succ) + ∑ i : Fin r, i.val * n i.succ)
            * (α / (α - 1)) ^ (n 0 + ∑ i : Fin r, n i.succ) := by
            rw [pow_add, pow_add]; ring

/-- **Paper (5.50), Lemma 5.12.**  For `α > 1`, `β = α/(α-1)`, and any tuple
`n : Fin r → ℕ`, the multinomial coefficient `(∑ n i)! / ∏ (n i)!` is at most
`α ^ (∑ i, (i+1) * n i) * β ^ (∑ i, n i)` (1-based weights, as in the paper). -/
theorem multinomial_le_pow_mul_pow (α : ℝ) (hα : 1 < α) (r : ℕ) (n : Fin r → ℕ) :
    (Nat.multinomial Finset.univ n : ℝ)
      ≤ α ^ (∑ i, (i.val + 1) * n i) * (α / (α - 1)) ^ (∑ i, n i) := by
  refine (multinomial_le_pow_mul_pow_aux α hα r n).trans ?_
  have hexp : (∑ i : Fin r, i.val * n i) ≤ ∑ i : Fin r, (i.val + 1) * n i :=
    Finset.sum_le_sum fun i _ => Nat.mul_le_mul (Nat.le_succ _) le_rfl
  have hβ0 : (0 : ℝ) < α / (α - 1) := div_pos (by linarith) (by linarith)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hα.le hexp)
    (le_of_lt (pow_pos hβ0 _))

/-- Geometric-decay tail bound: if `N` is non-increasing and halves every `K`
steps, any tail sum `∑_{i ∈ [j, r)} N i` is at most `2K · N j`.  Auxiliary for
paper (5.51); `d` is downward-induction fuel bounding `r - j`. -/
private theorem tail_sum_le (K r : ℕ) (hK1 : 1 ≤ K) (N : ℕ → ℕ)
    (hdec : ∀ i j : ℕ, i ≤ j → N j ≤ N i)
    (hdecay : ∀ j : ℕ, 2 * N (j + K) ≤ N j) :
    ∀ d j : ℕ, r - j ≤ d → ∑ i ∈ Finset.Ico j r, N i ≤ 2 * K * N j := by
  intro d
  induction d with
  | zero =>
      intro j hj
      rw [Finset.Ico_eq_empty (by omega)]
      simp
  | succ d ih =>
      intro j hj
      by_cases hjr : r ≤ j
      · rw [Finset.Ico_eq_empty (by omega)]; simp
      · by_cases hK : r ≤ j + K
        · -- short tail: at most `K` terms, each at most `N j`
          calc ∑ i ∈ Finset.Ico j r, N i
              ≤ ∑ i ∈ Finset.Ico j r, N j :=
                Finset.sum_le_sum fun i hi => hdec j i (Finset.mem_Ico.mp hi).1
            _ = (r - j) * N j := by
                rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
            _ ≤ 2 * K * N j := Nat.mul_le_mul (by omega) le_rfl
        · -- split off the first `K` terms and recurse on the tail
          have hsplit : (∑ i ∈ Finset.Ico j (j + K), N i)
              + ∑ i ∈ Finset.Ico (j + K) r, N i = ∑ i ∈ Finset.Ico j r, N i :=
            Finset.sum_Ico_consecutive N (by omega) (by omega)
          have h1 : ∑ i ∈ Finset.Ico j (j + K), N i ≤ K * N j := by
            calc ∑ i ∈ Finset.Ico j (j + K), N i
                ≤ ∑ i ∈ Finset.Ico j (j + K), N j :=
                  Finset.sum_le_sum fun i hi => hdec j i (Finset.mem_Ico.mp hi).1
              _ = K * N j := by
                  rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul,
                    Nat.add_sub_cancel_left]
          have h2 : ∑ i ∈ Finset.Ico (j + K) r, N i ≤ 2 * K * N (j + K) :=
            ih (j + K) (by omega)
          have h3 : 2 * K * N (j + K) ≤ K * N j := by
            calc 2 * K * N (j + K) = K * (2 * N (j + K)) := by ring
              _ ≤ K * N j := Nat.mul_le_mul le_rfl (hdecay j)
          calc ∑ i ∈ Finset.Ico j r, N i
              = (∑ i ∈ Finset.Ico j (j + K), N i)
                + ∑ i ∈ Finset.Ico (j + K) r, N i := hsplit.symm
            _ ≤ K * N j + K * N j :=
                Nat.add_le_add h1 (h2.trans h3)
            _ = 2 * K * N j := by ring

/-- Weighted tail bound, the combinatorial heart of paper (5.51): under the
same monotone geometric decay, the linearly-weighted tail sum
`∑_{i ∈ [j, r)} (i + 1 - j) · N i` is controlled by `2K²` times the plain tail
sum.  Downward induction with fuel `d ≥ r - j`. -/
private theorem weighted_tail_sum_le (K r : ℕ) (hK1 : 1 ≤ K) (N : ℕ → ℕ)
    (hdec : ∀ i j : ℕ, i ≤ j → N j ≤ N i)
    (hdecay : ∀ j : ℕ, 2 * N (j + K) ≤ N j) :
    ∀ d j : ℕ, r - j ≤ d →
      ∑ i ∈ Finset.Ico j r, (i + 1 - j) * N i
        ≤ 2 * K ^ 2 * ∑ i ∈ Finset.Ico j r, N i := by
  intro d
  induction d with
  | zero =>
      intro j hj
      rw [Finset.Ico_eq_empty (by omega)]
      simp
  | succ d ih =>
      intro j hj
      by_cases hjr : r ≤ j
      · rw [Finset.Ico_eq_empty (by omega)]; simp
      · by_cases hshort : r ≤ j + K
        · -- short tail: every weight is at most `K ≤ 2K²`
          have hle : ∑ i ∈ Finset.Ico j r, (i + 1 - j) * N i
              ≤ ∑ i ∈ Finset.Ico j r, K * N i := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hi' := Finset.mem_Ico.mp hi
            exact Nat.mul_le_mul (by omega) le_rfl
          rw [← Finset.mul_sum] at hle
          refine hle.trans (Nat.mul_le_mul ?_ le_rfl)
          calc K = K * 1 := (mul_one K).symm
            _ ≤ K * (2 * K) := Nat.mul_le_mul le_rfl (by omega)
            _ = 2 * K ^ 2 := by ring
        · -- split both sums at `j + K`
          have hsplitW : (∑ i ∈ Finset.Ico j (j + K), (i + 1 - j) * N i)
              + ∑ i ∈ Finset.Ico (j + K) r, (i + 1 - j) * N i
              = ∑ i ∈ Finset.Ico j r, (i + 1 - j) * N i :=
            Finset.sum_Ico_consecutive _ (by omega) (by omega)
          have hsplitT : (∑ i ∈ Finset.Ico j (j + K), N i)
              + ∑ i ∈ Finset.Ico (j + K) r, N i = ∑ i ∈ Finset.Ico j r, N i :=
            Finset.sum_Ico_consecutive N (by omega) (by omega)
          -- far part: weights relative to `j + K`, plus `K` extra each
          have hshift : ∑ i ∈ Finset.Ico (j + K) r, (i + 1 - j) * N i
              = (∑ i ∈ Finset.Ico (j + K) r, (i + 1 - (j + K)) * N i)
                + K * ∑ i ∈ Finset.Ico (j + K) r, N i := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i hi => ?_
            have hi' := Finset.mem_Ico.mp hi
            have hw : i + 1 - j = (i + 1 - (j + K)) + K := by omega
            rw [hw, add_mul]
          -- near part: at most `K` terms, weight at most `K`, value at most `N j`
          have hblock : ∑ i ∈ Finset.Ico j (j + K), (i + 1 - j) * N i
              ≤ K * (K * N j) := by
            calc ∑ i ∈ Finset.Ico j (j + K), (i + 1 - j) * N i
                ≤ ∑ i ∈ Finset.Ico j (j + K), K * N j := by
                  refine Finset.sum_le_sum fun i hi => ?_
                  have hi' := Finset.mem_Ico.mp hi
                  exact Nat.mul_le_mul (by omega) (hdec j i hi'.1)
              _ = K * (K * N j) := by
                  rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul,
                    Nat.add_sub_cancel_left]
          have hW' := ih (j + K) (by omega)
          have hT' := tail_sum_le K r hK1 N hdec hdecay (r - (j + K)) (j + K) le_rfl
          have hNj : N j ≤ ∑ i ∈ Finset.Ico j (j + K), N i :=
            Finset.single_le_sum (f := N) (fun i _ => Nat.zero_le _)
              (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
          -- the `K`-fold extra weight on the far tail is absorbed via the decay
          have hKT' : K * (∑ i ∈ Finset.Ico (j + K) r, N i) ≤ K ^ 2 * N j := by
            calc K * (∑ i ∈ Finset.Ico (j + K) r, N i)
                ≤ K * (2 * K * N (j + K)) := Nat.mul_le_mul le_rfl hT'
              _ = K ^ 2 * (2 * N (j + K)) := by ring
              _ ≤ K ^ 2 * N j := Nat.mul_le_mul le_rfl (hdecay j)
          calc ∑ i ∈ Finset.Ico j r, (i + 1 - j) * N i
              = (∑ i ∈ Finset.Ico j (j + K), (i + 1 - j) * N i)
                + ((∑ i ∈ Finset.Ico (j + K) r, (i + 1 - (j + K)) * N i)
                  + K * ∑ i ∈ Finset.Ico (j + K) r, N i) := by
                rw [← hshift, hsplitW]
            _ ≤ K * (K * N j)
                + ((2 * K ^ 2 * ∑ i ∈ Finset.Ico (j + K) r, N i) + K ^ 2 * N j) :=
                Nat.add_le_add hblock (Nat.add_le_add hW' hKT')
            _ = 2 * K ^ 2 * N j + 2 * K ^ 2 * ∑ i ∈ Finset.Ico (j + K) r, N i := by
                ring
            _ ≤ 2 * K ^ 2 * (∑ i ∈ Finset.Ico j (j + K), N i)
                + 2 * K ^ 2 * ∑ i ∈ Finset.Ico (j + K) r, N i :=
                Nat.add_le_add_right (Nat.mul_le_mul le_rfl hNj) _
            _ = 2 * K ^ 2 * ∑ i ∈ Finset.Ico j r, N i := by
                rw [← Nat.mul_add, hsplitT]

/-- Dyadic pigeonhole (proof of paper (5.51)): a non-increasing `K`-lacunary
tuple halves every `K` steps.  If not, the `K + 1` values
`n ⟨j⟩ ≥ ⋯ ≥ n ⟨j+K⟩` would all lie in the window `[X, 2X)` with
`X = n ⟨j+K⟩ ≥ 1`, contradicting Def 5.11. -/
private theorem lacunary_decay {K r : ℕ} {n : Fin r → ℕ}
    (hlac : Lacunary K Finset.univ n)
    (hmono : ∀ i j : Fin r, i ≤ j → n j ≤ n i)
    {j : ℕ} (hj : j < r) (hjK : j + K < r) :
    2 * n ⟨j + K, hjK⟩ ≤ n ⟨j, hj⟩ := by
  by_contra hcon
  have hcon' : n ⟨j, hj⟩ < 2 * n ⟨j + K, hjK⟩ := by omega
  have hX1 : 1 ≤ n ⟨j + K, hjK⟩ := by
    by_contra h0
    omega
  have hcard := hlac (n ⟨j + K, hjK⟩) hX1
  have hinj : (Finset.Icc j (j + K)).card
      ≤ (Finset.univ.filter fun i : Fin r =>
          n ⟨j + K, hjK⟩ ≤ n i ∧ n i < 2 * n ⟨j + K, hjK⟩).card := by
    refine Finset.card_le_card_of_injOn
      (fun t => if ht : t < r then (⟨t, ht⟩ : Fin r) else ⟨j, hj⟩) ?_ ?_
    · intro t htmem
      rw [Finset.mem_coe, Finset.mem_Icc] at htmem
      have htr : t < r := by omega
      simp only [dif_pos htr, Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact hmono ⟨t, htr⟩ ⟨j + K, hjK⟩ (Fin.mk_le_mk.mpr (by omega))
      · have h1 : n ⟨t, htr⟩ ≤ n ⟨j, hj⟩ :=
          hmono ⟨j, hj⟩ ⟨t, htr⟩ (Fin.mk_le_mk.mpr (by omega))
        omega
    · intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_Icc] at ha hb
      have har : a < r := by omega
      have hbr : b < r := by omega
      simp only [dif_pos har, dif_pos hbr] at hab
      simpa using hab
  rw [Nat.card_Icc] at hinj
  omega

/-- Sorted core of paper **(5.51)**: for a non-increasing `K`-lacunary tuple
the 1-based weighted sum `∑ (i+1)·n i` is at most `2K²` times `∑ n i`. -/
private theorem weighted_sum_le (K r : ℕ) (hK1 : 1 ≤ K) (n : Fin r → ℕ)
    (hmono : ∀ i j : Fin r, i ≤ j → n j ≤ n i)
    (hlac : Lacunary K Finset.univ n) :
    ∑ i : Fin r, (i.val + 1) * n i ≤ 2 * K ^ 2 * ∑ i : Fin r, n i := by
  classical
  -- extend `n` by zero to a non-increasing sequence on all of `ℕ`
  let N : ℕ → ℕ := fun i => if h : i < r then n ⟨i, h⟩ else 0
  have hNpos : ∀ (i : ℕ) (h : i < r), N i = n ⟨i, h⟩ := fun i h => dif_pos h
  have hNneg : ∀ i : ℕ, ¬i < r → N i = 0 := fun i h => dif_neg h
  have hNval : ∀ i : Fin r, N i.val = n i := by
    intro i
    rw [hNpos i.val i.isLt]
  have hdec : ∀ i j : ℕ, i ≤ j → N j ≤ N i := by
    intro i j hij
    by_cases hjr : j < r
    · have hir : i < r := lt_of_le_of_lt hij hjr
      rw [hNpos j hjr, hNpos i hir]
      exact hmono ⟨i, hir⟩ ⟨j, hjr⟩ (Fin.mk_le_mk.mpr hij)
    · rw [hNneg j hjr]
      exact Nat.zero_le _
  have hdecay : ∀ j : ℕ, 2 * N (j + K) ≤ N j := by
    intro j
    by_cases hjK : j + K < r
    · have hjr : j < r := by omega
      rw [hNpos (j + K) hjK, hNpos j hjr]
      exact lacunary_decay hlac hmono hjr hjK
    · rw [hNneg (j + K) hjK]
      simp
  have hs1 : ∑ i : Fin r, (i.val + 1) * n i
      = ∑ i ∈ Finset.Ico 0 r, (i + 1 - 0) * N i := by
    rw [← Finset.range_eq_Ico,
      ← Fin.sum_univ_eq_sum_range (fun i => (i + 1 - 0) * N i) r]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hNval i]
    simp
  have hs2 : ∑ i : Fin r, n i = ∑ i ∈ Finset.Ico 0 r, N i := by
    rw [← Finset.range_eq_Ico, ← Fin.sum_univ_eq_sum_range (fun i => N i) r]
    exact Finset.sum_congr rfl fun i _ => (hNval i).symm
  rw [hs1, hs2]
  exact weighted_tail_sum_le K r hK1 N hdec hdecay r 0 (by omega)

/-- **Paper (5.51), Lemma 5.12 — sorted form.**  A non-increasing `K`-lacunary
tuple (Def 5.11) has multinomial coefficient at most
`(2 ^ (2K² + 1)) ^ (∑ i, n i)`: apply (5.50) with `α = 2` (so
`β = α/(α-1) = 2`) and absorb the weighted exponent via `weighted_sum_le`. -/
theorem multinomial_le_pow_of_lacunary_sorted (K : ℕ) (hK : 1 ≤ K) (r : ℕ)
    (n : Fin r → ℕ) (hmono : ∀ i j : Fin r, i ≤ j → n j ≤ n i)
    (hlac : Lacunary K Finset.univ n) :
    (Nat.multinomial Finset.univ n : ℝ)
      ≤ ((2 : ℝ) ^ (2 * K ^ 2 + 1)) ^ (∑ i, n i) := by
  have h50 := multinomial_le_pow_mul_pow 2 one_lt_two r n
  have hβ : (2 : ℝ) / (2 - 1) = 2 := by norm_num
  rw [hβ] at h50
  have hw := weighted_sum_le K r hK n hmono hlac
  calc (Nat.multinomial Finset.univ n : ℝ)
      ≤ 2 ^ (∑ i, (i.val + 1) * n i) * 2 ^ (∑ i, n i) := h50
    _ ≤ 2 ^ (2 * K ^ 2 * ∑ i, n i) * 2 ^ (∑ i, n i) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hw)
          (by positivity)
    _ = ((2 : ℝ) ^ (2 * K ^ 2 + 1)) ^ (∑ i, n i) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring

/-- **Paper (5.51), Lemma 5.12 (node L-5.12).**  For every `K ≥ 1` there is a
constant `C = 2 ^ (2K² + 1) ≥ 1`, depending only on `K`, such that every
`K`-lacunary tuple (Def 5.11) satisfies
`multinomial (n 0, …, n (r-1)) ≤ C ^ (∑ i, n i)`.  The tuple is reduced to a
non-increasing one using the permutation invariance of the multinomial
coefficient (`multinomial_comp_equiv`) along the decreasing rearrangement
built from `Tuple.sort` and `Fin.revPerm`. -/
theorem multinomial_le_pow_of_lacunary (K : ℕ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (r : ℕ) (n : Fin r → ℕ), Lacunary K Finset.univ n →
      (Nat.multinomial Finset.univ n : ℝ) ≤ C ^ (∑ i, n i) := by
  refine ⟨(2 : ℝ) ^ (2 * K ^ 2 + 1), one_le_pow₀ one_le_two, ?_⟩
  intro r n hlac
  -- decreasing rearrangement of `n`
  set e : Equiv.Perm (Fin r) := Fin.revPerm.trans (Tuple.sort n) with he
  have hmono : ∀ i j : Fin r, i ≤ j → (n ∘ e) j ≤ (n ∘ e) i := by
    intro i j hij
    have hs := Tuple.monotone_sort n (Fin.rev_le_rev.mpr hij)
    simpa [he, Equiv.trans_apply, Function.comp_apply] using hs
  have hlac' : Lacunary K Finset.univ (n ∘ e) := lacunary_comp_equiv e hlac
  have hle := multinomial_le_pow_of_lacunary_sorted K hK r (n ∘ e) hmono hlac'
  have h1 : Nat.multinomial Finset.univ (n ∘ e) = Nat.multinomial Finset.univ n :=
    multinomial_comp_equiv e n
  have h2 : ∑ i, (n ∘ e) i = ∑ i, n i := by
    simpa [Function.comp_apply] using Equiv.sum_comp e n
  rw [h1, h2] at hle
  exact hle

end Anderson4D
