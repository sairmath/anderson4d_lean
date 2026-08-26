import Anderson4D.DetParametrix.Paper42_Moment.R324PaperStep23

/-!
# Paper §4.2, Step 3(c)--(d): the nested chain reduced, in closed form

Paper: R-324 — §4.2 Step 3(c)–(d) — the nested chain, closed form

Step 3 of the paper reduces the surviving fully paired subintervals of
`κ₀` one at a time.  Two facts make that possible and are already proved
in `R324PaperStep23.lean`:

* the surviving subintervals form a **strictly nested chain**
  `1 ≤ a_t < … < a₁ ≤ p < p+1 ≤ b₁ < … < b_t ≤ p+q`
  (`r324Step3_fullyPaired_straddles`, `r324Step3_strict_nested`), so they
  can be removed innermost-outermost with no interaction;
* removing `[a_i, b_i]` costs exactly the **elementary eight-dimensional
  integral** `∫∫ |u-a|⁻² · J̃_{k_i,prim}(a-b) · |b-v|⁻² da db ≤ (Cλ)^{2k_i}·K`
  (`exists_r324Step3_elementaryEightDim_le`), uniformly in the flanking
  chain variables `u = x_{a_i-1}`, `v = x_{b_i+1}`, in `ε`, and in `k_i`.

This module composes the two into the paper's own sentence *"iterate over
`[a₂,b₂]`, …"*: after all `t` reductions the value is bounded by
`(Cλ)^{2Σk_i}·K^t` times the value on the residual chain, on which (4.4)
is then applied one last time.

Nothing here takes an absolute value: the reductions are the ones Step 2(f)
permits, performed on values already made real by the earlier collapses.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- **Step 3(c) at one nested interval, in the shape the chain induction
consumes.**

If the value before the reduction is dominated by the elementary
eight-dimensional integral at the interval's flanking pair times the value
after it, then it is dominated by `(Cλ)^{2k}·K` times that value — `K`
being the single constant of `exists_r324Step3_elementaryEightDim_le`. -/
theorem r324Step3_nestedStep_le
    {C lam ε supportConstant K Ecur Enext : ℝ} {k : ℕ} {u v : T4}
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) (hnext : 0 ≤ Enext)
    (height :
      ∀ (C' lam' ε' : ℝ) (k' : ℕ) (u' v' : T4),
        0 ≤ C' → 0 ≤ lam' → 0 < ε' → ε' ≤ 1 → 1 ≤ |Real.log ε'| →
          (∫ a, ∫ b,
            r324Step3EightDimIntegrand C' lam' ε' supportConstant k' u' v'
              a b
            ∂paperMeasure ∂paperMeasure) ≤ (C' * lam') ^ (2 * k') * K)
    (hstep :
      Ecur ≤
        (∫ a, ∫ b,
          r324Step3EightDimIntegrand C lam ε supportConstant k u v a b
          ∂paperMeasure ∂paperMeasure) * Enext) :
    Ecur ≤ (C * lam) ^ (2 * k) * K * Enext :=
  hstep.trans
    (mul_le_mul_of_nonneg_right
      (height C lam ε k u v hC hlam hε hε1 hlog) hnext)

/-- **Step 3(c)--(d), assembled.**

The paper's Step 3 in closed form: given the per-interval reductions of
the strictly nested chain — each dominated by the elementary
eight-dimensional integral at that interval's flanking pair — the value at
the top of the chain obeys

`E₀ ≤ (Cλ)^{2 Σ k_i} · K^t · E_t`,

where `E_t` is the value on the residual chain, to which (4.4) is applied
one last time.  The constant `K` is chosen before the coupling, the scale,
the chain length, and the interval lengths. -/
theorem exists_r324Step3_nestedChain_le
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C lam ε : ℝ) (t : ℕ) (E : ℕ → ℝ) (k : ℕ → ℕ) (u v : ℕ → T4),
        0 ≤ C → 0 ≤ lam → 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        (∀ i, 0 ≤ E i) →
        (∀ i, i < t →
          E i ≤
            (∫ a, ∫ b,
              r324Step3EightDimIntegrand C lam ε supportConstant (k i)
                (u i) (v i) a b
              ∂paperMeasure ∂paperMeasure) * E (i + 1)) →
          E 0 ≤
            (C * lam) ^ (2 * ∑ i ∈ Finset.range t, k i) * K ^ t * E t := by
  obtain ⟨K, hK, height⟩ := exists_r324Step3_elementaryEightDim_le hsupport
  refine ⟨K, hK, ?_⟩
  intro C lam ε t E k u v hC hlam hε hε1 hlog hE hstep
  refine r324Step3_chain_induction (mul_nonneg hC hlam) hK.le E k ?_
  intro i hi
  exact
    r324Step3_nestedStep_le hC hlam hε hε1 hlog (hE (i + 1))
      (fun C' lam' ε' k' u' v' hC' hlam' hε' hε1' hlog' =>
        height C' lam' ε' k' u' v' hC' hlam' hε' hε1' hlog')
      (hstep i hi)

/-- **Step 3, landed on the last application of (4.4).**

After the nested chain has been reduced, the residual chain carries a
primitive pairing on `2k` sites, and (4.4) bounds its value by the
integrated inserted majorant.  Composing that with the chain bound gives
the shape `R324Step23ConfigReduction` records per interval configuration:
`(Cλ)^{2m-2k}` times a single integrated majorant. -/
theorem r324Step3_chain_le_insertedMajorant
    {C lam ε supportConstant K : ℝ} {t : ℕ} {E : ℕ → ℝ} {k : ℕ → ℕ}
    {kres : ℕ}
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hK : 0 ≤ K)
    (hchain :
      E 0 ≤ (C * lam) ^ (2 * ∑ i ∈ Finset.range t, k i) * K ^ t * E t)
    (hres :
      E t ≤
        ∫ z, primitiveInsertedMajorant C lam ε supportConstant kres z
          ∂paperMeasure) :
    E 0 ≤
      (C * lam) ^ (2 * ∑ i ∈ Finset.range t, k i) * K ^ t *
        ∫ z, primitiveInsertedMajorant C lam ε supportConstant kres z
          ∂paperMeasure :=
  hchain.trans
    (mul_le_mul_of_nonneg_left hres
      (mul_nonneg (pow_nonneg (mul_nonneg hC hlam) _) (pow_nonneg hK _)))

end

end Anderson4D
