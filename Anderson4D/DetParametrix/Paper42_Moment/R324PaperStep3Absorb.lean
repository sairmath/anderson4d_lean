import Anderson4D.DetParametrix.Paper42_Moment.R324PaperStep3Chain

/-!
# Paper §4.2, Step 3: absorbing the chain constant into the base

Paper: R-324 — §4.2 Step 3, the `K^t` absorption

`exists_r324Step3_nestedChain_le` delivers the nested-chain bound in the
form `(Cλ)^{2 Σ k_i} · K^t`, with one factor of the elementary
eight-dimensional constant `K` per removed interval.  The shape the rest
of §4.2 consumes — `R324Step23ConfigReduction`, and behind it the paper's
own `(Cλ)^{2m-2k}` bookkeeping — carries no separate constant: every
constant lives in the base of the power.

The two agree because each removed interval has at least one pair, so
`t ≤ Σ k_i`, and one factor of `max K 1` per removed *site* pays for one
factor of `K` per removed *interval*.  This is the same absorption
`r324RemovalStepConstant_le` performs for the §4.1 iteration.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- Each removed interval contributes at least one to the site count, so the
number of reductions never exceeds the total number of pairs removed. -/
theorem r324Step3_card_le_sum {t : ℕ} {ks : ℕ → ℕ}
    (hk : ∀ i, i < t → 1 ≤ ks i) :
    t ≤ ∑ i ∈ Finset.range t, ks i := by
  calc t = ∑ _i ∈ Finset.range t, 1 := by simp
    _ ≤ ∑ i ∈ Finset.range t, ks i :=
        Finset.sum_le_sum fun i hi => hk i (Finset.mem_range.mp hi)

/-- **The chain constant is absorbed into the base.**

`(Cλ)^{2Σk_i}·K^t ≤ ((C·max K 1)·λ)^{2Σk_i}`: one factor of `max K 1` per
removed site more than pays for one factor of `K` per removed interval. -/
theorem r324Step3_absorb_chainConstant {C lam K : ℝ} {t : ℕ} {ks : ℕ → ℕ}
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hK : 0 ≤ K)
    (hk : ∀ i, i < t → 1 ≤ ks i) :
    (C * lam) ^ (2 * ∑ i ∈ Finset.range t, ks i) * K ^ t ≤
      ((C * max K 1) * lam) ^ (2 * ∑ i ∈ Finset.range t, ks i) := by
  set S : ℕ := ∑ i ∈ Finset.range t, ks i with hS
  have hK1 : (1 : ℝ) ≤ max K 1 := le_max_right _ _
  have hbase : (0 : ℝ) ≤ (C * lam) ^ (2 * S) := by positivity
  have hKt : K ^ t ≤ (max K 1) ^ (2 * S) := by
    calc K ^ t ≤ (max K 1) ^ t := pow_le_pow_left₀ hK (le_max_left K 1) t
      _ ≤ (max K 1) ^ (2 * S) := by
          refine pow_le_pow_right₀ hK1 ?_
          have := r324Step3_card_le_sum hk
          omega
  calc
    (C * lam) ^ (2 * S) * K ^ t ≤ (C * lam) ^ (2 * S) * (max K 1) ^ (2 * S) :=
      mul_le_mul_of_nonneg_left hKt hbase
    _ = ((C * max K 1) * lam) ^ (2 * S) := by
      rw [← mul_pow]
      congr 1
      ring

/-- **Step 3, in the constant-free shape §4.2 consumes.**

The nested-chain bound with the elementary constant absorbed, ready to be
read as the `(Cλ)^{…}` bookkeeping of `R324Step23ConfigReduction`. -/
theorem r324Step3_chain_le_absorbed {C lam K M : ℝ} {t : ℕ} {ks : ℕ → ℕ}
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hk : ∀ i, i < t → 1 ≤ ks i)
    {E0 : ℝ}
    (hchain : E0 ≤ (C * lam) ^ (2 * ∑ i ∈ Finset.range t, ks i) * K ^ t * M) :
    E0 ≤ ((C * max K 1) * lam) ^ (2 * ∑ i ∈ Finset.range t, ks i) * M :=
  hchain.trans
    (mul_le_mul_of_nonneg_right
      (r324Step3_absorb_chainConstant hC hlam hK hk) hM)

end

end Anderson4D
