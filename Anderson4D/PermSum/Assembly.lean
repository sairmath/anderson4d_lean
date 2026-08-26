import Anderson4D.PermSum.Main

/-!
# Lattice-level assembly after Proposition 5.7

This file records the elementary scale-summation and factorial/logarithm
ledger used at the end of paper §5.2, equations (5.16)--(5.17).  The
geometric tree summation and the continuum discretization are kept as
separate interfaces; the lemma below closes the final numerical step without
hiding its uniform exponential constant.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open scoped BigOperators

noncomputable section

/-! ## Independent dyadic-scale summation -/

/-- Product weight obtained after summing a Hepp marking from the leaves
toward the root.  Coordinates in `free` carry the logarithmic loss; every
other coordinate carries a summable dyadic gap.  This is the factorized
majorant behind paper (5.17). -/
def dyadicAssignmentWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ℕ) (free : Finset ι) (a : ι → Fin L) : ℝ :=
  ∏ i : ι, if i ∈ free then 1 else (1 / 2 : ℝ) ^ (a i).val

/-- **Factorized geometric summation in (5.17).**  Each unrestricted scale
costs `L`, whereas a scale carrying a parent-ratio factor costs at most the
geometric constant `2`.  The actual increasing-marking domain injects into
this independent gap domain, so this is the reusable numerical estimate
consumed by the tree-specific assembly. -/
theorem sum_dyadicAssignmentWeight_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ℕ) (free : Finset ι) :
    (∑ a : ι → Fin L, dyadicAssignmentWeight L free a) ≤
      (L : ℝ) ^ free.card *
        2 ^ (Fintype.card ι - free.card) := by
  unfold dyadicAssignmentWeight
  let f : ∀ _i : ι, Fin L → ℝ :=
    fun i j => if i ∈ free then 1 else (1 / 2 : ℝ) ^ j.val
  change (∑ a : ι → Fin L, ∏ i : ι, f i (a i)) ≤ _
  rw [← Fintype.prod_sum f]
  calc
    (∏ i : ι, ∑ j : Fin L,
        if i ∈ free then 1 else (1 / 2 : ℝ) ^ j.val) ≤
        ∏ i : ι, if i ∈ free then (L : ℝ) else 2 := by
      apply Finset.prod_le_prod
      · intro i _
        apply Finset.sum_nonneg
        intro j _
        by_cases hi : i ∈ free
        · simp [hi]
        · simp [hi, pow_nonneg]
      · intro i _
        by_cases hi : i ∈ free
        · simp [hi]
        · simp only [hi, ↓reduceIte]
          simpa only [Fin.sum_univ_eq_sum_range] using
            sum_geometric_two_le L
    _ = (L : ℝ) ^ free.card *
          2 ^ (Fintype.card ι - free.card) := by
      have hyes :
          Finset.univ.filter (fun i : ι => i ∈ free) = free := by
        ext i
        simp
      have hno :
          Finset.univ.filter (fun i : ι => ¬i ∈ free) =
            Finset.univ \ free := by
        ext i
        simp
      rw [Finset.prod_ite]
      rw [hyes, hno, Finset.prod_const, Finset.prod_const,
        Finset.card_sdiff_of_subset (Finset.subset_univ free),
        Finset.card_univ]

/-! ## The factorial--logarithm balance -/

/-- A deliberately coarse exponential envelope for the cubic residue in the
factorial/logarithm balance. -/
theorem cube_le_eight_pow (k : ℕ) : k ^ 3 ≤ 8 ^ k := by
  have hk : k ≤ 2 ^ k := k.lt_two_pow_self.le
  calc
    k ^ 3 ≤ (2 ^ k) ^ 3 := Nat.pow_le_pow_left hk 3
    _ = 2 ^ (k * 3) := by rw [pow_mul]
    _ = 2 ^ (3 * k) := by rw [Nat.mul_comm]
    _ = (2 ^ 3) ^ k := by rw [pow_mul]
    _ = 8 ^ k := by norm_num

/-- **The elementary inequality after (5.17), natural-scale form.**

If the perturbative order satisfies `n ≤ K L`, then, uniformly for
`0 ≤ s ≤ n-2`,

`(n-s)! L^min(s+1,n-2) ≤ (8 (K+1))^n L^(n-2)`.

Here `L` is the number of available dyadic scales (later comparable to
`|log ε|`).  The proof separates the endpoint cases `n-s ≤ 3`; away from
them, exactly `n-s-3` powers of `L` pay for the factorial, while the cubic
residue is absorbed by `8^n`. -/
theorem factorial_log_balance_nat
    (n s L K : ℕ) (hn : 2 ≤ n) (hs : s ≤ n - 2)
    (hnL : n ≤ K * L) :
    (n - s).factorial * L ^ min (s + 1) (n - 2) ≤
      (8 * (K + 1)) ^ n * L ^ (n - 2) := by
  let k := n - s
  have hk_le_n : k ≤ n := Nat.sub_le n s
  have hk_two : 2 ≤ k := by
    dsimp only [k]
    omega
  by_cases hk : k ≤ 3
  · have hmin : min (s + 1) (n - 2) = n - 2 := by
      apply min_eq_right
      dsimp only [k] at hk
      omega
    have hfac : k.factorial ≤ 6 := by
      have hfac' := Nat.factorial_le hk
      norm_num [Nat.factorial] at hfac'
      exact hfac'
    have hbase : 6 ≤ (8 * (K + 1)) ^ n := by
      have h8 : 8 ≤ 8 * (K + 1) := by omega
      calc
        6 ≤ 8 ^ 1 := by norm_num
        _ ≤ (8 * (K + 1)) ^ 1 :=
          Nat.pow_le_pow_left h8 1
        _ ≤ (8 * (K + 1)) ^ n :=
          Nat.pow_le_pow_right (by omega) (by omega)
    rw [hmin]
    exact Nat.mul_le_mul_right _ (hfac.trans hbase)
  · have hk_four : 4 ≤ k := by omega
    have hmin : min (s + 1) (n - 2) = s + 1 := by
      apply min_eq_left
      dsimp only [k] at hk_four
      omega
    have hexp : s + 1 + (k - 3) = n - 2 := by
      dsimp only [k]
      omega
    have hkKL : k ≤ K * L := hk_le_n.trans hnL
    have hfacPow : k.factorial ≤ k ^ k := Nat.factorial_le_pow k
    have hk_split : k - 3 + 3 = k := by omega
    have hpowKL : k ^ (k - 3) ≤ (K * L) ^ (k - 3) :=
      Nat.pow_le_pow_left hkKL (k - 3)
    have hcubic : k ^ 3 ≤ 8 ^ k := cube_le_eight_pow k
    have hfactor :
        k.factorial ≤
          (8 * (K + 1)) ^ n * L ^ (k - 3) := by
      calc
        k.factorial ≤ k ^ k := hfacPow
        _ = k ^ (k - 3) * k ^ 3 := by rw [← pow_add, hk_split]
        _ ≤ (K * L) ^ (k - 3) * 8 ^ k :=
          Nat.mul_le_mul hpowKL hcubic
        _ = (K ^ (k - 3) * 8 ^ k) * L ^ (k - 3) := by
          rw [mul_pow]
          ring
        _ ≤ (8 * (K + 1)) ^ n * L ^ (k - 3) := by
          apply Nat.mul_le_mul_right
          have hKbase : K ≤ K + 1 := Nat.le_succ K
          have hKpow₁ :
              K ^ (k - 3) ≤ (K + 1) ^ (k - 3) :=
            Nat.pow_le_pow_left hKbase (k - 3)
          have hKpow₂ :
              (K + 1) ^ (k - 3) ≤ (K + 1) ^ k :=
            Nat.pow_le_pow_right (by omega) (by omega)
          have hcombine :
              K ^ (k - 3) * 8 ^ k ≤ (8 * (K + 1)) ^ k := by
            calc
              K ^ (k - 3) * 8 ^ k
                  ≤ (K + 1) ^ k * 8 ^ k :=
                Nat.mul_le_mul_right _ (hKpow₁.trans hKpow₂)
              _ = (8 * (K + 1)) ^ k := by
                rw [mul_pow]
                ac_rfl
          exact hcombine.trans
            (Nat.pow_le_pow_right (by omega) hk_le_n)
    rw [hmin]
    change k.factorial * L ^ (s + 1) ≤
      (8 * (K + 1)) ^ n * L ^ (n - 2)
    have hscaled :=
      Nat.mul_le_mul_right (L ^ (s + 1)) hfactor
    calc
      k.factorial * L ^ (s + 1) ≤
          ((8 * (K + 1)) ^ n * L ^ (k - 3)) *
            L ^ (s + 1) := hscaled
      _ = (8 * (K + 1)) ^ n *
            L ^ ((k - 3) + (s + 1)) := by rw [pow_add]; ring
      _ = (8 * (K + 1)) ^ n * L ^ (n - 2) := by
        congr 2
        omega

/-- Real-valued form used by the analytic assembly.  It is an exact cast of
`factorial_log_balance_nat`, so no Archimedean or asymptotic argument is left
implicit. -/
theorem factorial_log_balance
    (n s L K : ℕ) (hn : 2 ≤ n) (hs : s ≤ n - 2)
    (hnL : n ≤ K * L) :
    ((n - s).factorial : ℝ) *
        (L : ℝ) ^ min (s + 1) (n - 2) ≤
      (8 * (K + 1) : ℝ) ^ n * (L : ℝ) ^ (n - 2) := by
  exact_mod_cast factorial_log_balance_nat n s L K hn hs hnL

/-- Powerset-summed form of the final estimate after (5.17).  The hypothesis
`B.card ≤ n-2` is the paper's `|B|-1 ≤ r-2 ≤ n-2` after removing the root.
The number of choices of `W` costs at most `2ⁿ`, absorbed into the displayed
base `16(K+1)`. -/
theorem sum_factorial_log_balance
    {α : Type*} [DecidableEq α]
    (B : Finset α) (n L K : ℕ)
    (hn : 2 ≤ n) (hB : B.card ≤ n - 2)
    (hnL : n ≤ K * L) :
    (∑ W ∈ B.powerset,
        ((n - W.card).factorial : ℝ) *
          (L : ℝ) ^ min (W.card + 1) (n - 2)) ≤
      (16 * (K + 1) : ℝ) ^ n * (L : ℝ) ^ (n - 2) := by
  let A : ℝ :=
    (8 * (K + 1) : ℝ) ^ n * (L : ℝ) ^ (n - 2)
  have hpoint :
      ∀ W ∈ B.powerset,
        ((n - W.card).factorial : ℝ) *
            (L : ℝ) ^ min (W.card + 1) (n - 2) ≤ A := by
    intro W hW
    have hcard : W.card ≤ n - 2 :=
      (Finset.card_le_card (Finset.mem_powerset.mp hW)).trans hB
    exact factorial_log_balance n W.card L K hn hcard hnL
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  calc
    (∑ W ∈ B.powerset,
        ((n - W.card).factorial : ℝ) *
          (L : ℝ) ^ min (W.card + 1) (n - 2))
        ≤ ∑ _W ∈ B.powerset, A :=
      Finset.sum_le_sum hpoint
    _ = (2 : ℝ) ^ B.card * A := by
      simp [Finset.card_powerset]
    _ ≤ (2 : ℝ) ^ n * A := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (hB.trans (Nat.sub_le n 2))) hA
    _ = (16 * (K + 1) : ℝ) ^ n *
          (L : ℝ) ^ (n - 2) := by
      dsimp only [A]
      calc
        (2 : ℝ) ^ n *
              ((8 * (K + 1) : ℝ) ^ n * (L : ℝ) ^ (n - 2)) =
            ((2 : ℝ) * (8 * (K + 1) : ℝ)) ^ n *
              (L : ℝ) ^ (n - 2) := by
                have hp :
                    ((2 : ℝ) * (8 * (K + 1) : ℝ)) ^ n =
                      (2 : ℝ) ^ n * (8 * (K + 1) : ℝ) ^ n :=
                  mul_pow _ _ _
                rw [hp]
                ring
        _ = (16 * (K + 1) : ℝ) ^ n *
              (L : ℝ) ^ (n - 2) := by
                rw [show
                  (2 : ℝ) * (8 * (K + 1) : ℝ) =
                    (16 * (K + 1) : ℝ) by ring]

end

end Anderson4D
