import Anderson4D.DetParametrix.Paper42_Moment.R324PaperStep3Absorb

/-!
# Paper §4.2, Step 3(c): the per-step domination

Paper: R-324 — §4.2 Step 3(c), one nested interval dominated by (4.4)

Step 3(c) of the paper, verbatim:

> "For `[a₁, b₁]` with `k₁ = b₁ − a₁ + 1`: the induced pairing is
> primitive, so (4.4) bounds the inner sum, which is exactly
> `J̃_{k₁,prim}(x_{a₁} − x_{b₁})`."

Three pointwise facts, all already proved elsewhere, make that a one-line
estimate:

* the chain edge entering the interval is an admissible input,
  `|H(z)| ≤ |z|⁻²` — `exists_r324ReducedInput_admissible`, which normalizes
  the §4.1 collapse so no constant survives;
* the same for the edge leaving it;
* the inner sum on the block is bounded by the inserted majorant of (4.4)
  — `proposition41_at_truncation`.

Multiplying them is exactly the integrand `r324Step3EightDimIntegrand` of
Step 3(c), so integrating in the two block endpoints and applying
`exists_r324Step3_elementaryEightDim_le` removes the interval at the cost
of `(Cλ)^{2k}·K`.  This is the single hypothesis
`exists_r324Step3_nestedChain_le` takes.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- **Step 3(c), pointwise.**

The chain edge entering the removed interval, the inner sum on the
interval, and the chain edge leaving it are bounded respectively by
`|u-a|⁻²`, the inserted majorant of (4.4), and `|b-v|⁻²`.  Their product is
therefore bounded by the Step 3(c) integrand. -/
theorem r324Step3_pointwise_le_eightDimIntegrand
    {Gp Gr Jblock : T4 → ℝ} {C lam ε supportConstant : ℝ} {k : ℕ}
    (hGp : ∀ z, |Gp z| ≤ invSqKer z)
    (hGr : ∀ z, |Gr z| ≤ invSqKer z)
    (hJ : ∀ z,
      |Jblock z| ≤ primitiveInsertedMajorant C lam ε supportConstant k z)
    (u v a b : T4) :
    |Gp (u - a) * Jblock (a - b) * Gr (b - v)| ≤
      r324Step3EightDimIntegrand C lam ε supportConstant k u v a b := by
  unfold r324Step3EightDimIntegrand
  rw [abs_mul, abs_mul]
  refine mul_le_mul (mul_le_mul (hGp _) (hJ _) (abs_nonneg _)
    (invSqKer_nonneg _)) (hGr _) (abs_nonneg _) ?_
  exact mul_nonneg (invSqKer_nonneg _)
    (primitiveInsertedMajorant_nonneg' C lam ε supportConstant k _)

/-- **Step 3(c), integrated in the two block endpoints.**

The value carried by the interval before its removal is dominated by the
elementary eight-dimensional integral at the interval's flanking pair.
Both integrability premises are on the actual integrands, not on sections
chosen after the fact. -/
theorem r324Step3_integral_le_eightDim
    {Gp Gr Jblock : T4 → ℝ} {C lam ε supportConstant : ℝ} {k : ℕ}
    (hGp : ∀ z, |Gp z| ≤ invSqKer z)
    (hGr : ∀ z, |Gr z| ≤ invSqKer z)
    (hJ : ∀ z,
      |Jblock z| ≤ primitiveInsertedMajorant C lam ε supportConstant k z)
    (u v : T4)
    (hleft : ∀ a : T4,
      Integrable (fun b => Gp (u - a) * Jblock (a - b) * Gr (b - v))
        paperMeasure)
    (hright : ∀ a : T4,
      Integrable
        (fun b =>
          r324Step3EightDimIntegrand C lam ε supportConstant k u v a b)
        paperMeasure)
    (houterL :
      Integrable
        (fun a =>
          ∫ b, Gp (u - a) * Jblock (a - b) * Gr (b - v) ∂paperMeasure)
        paperMeasure)
    (houterR :
      Integrable
        (fun a =>
          ∫ b,
            r324Step3EightDimIntegrand C lam ε supportConstant k u v a b
            ∂paperMeasure)
        paperMeasure) :
    (∫ a, ∫ b, Gp (u - a) * Jblock (a - b) * Gr (b - v)
        ∂paperMeasure ∂paperMeasure) ≤
      ∫ a, ∫ b,
        r324Step3EightDimIntegrand C lam ε supportConstant k u v a b
        ∂paperMeasure ∂paperMeasure := by
  refine integral_mono houterL houterR fun a => ?_
  refine integral_mono (hleft a) (hright a) fun b => ?_
  exact le_trans (le_abs_self _)
    (r324Step3_pointwise_le_eightDimIntegrand hGp hGr hJ u v a b)

/-- **Step 3(c), landed on the constant of Step 3(c).**

Composing the previous domination with
`exists_r324Step3_elementaryEightDim_le`: the interval is removed at the
uniform cost `(Cλ)^{2k}·K`, which is the per-step hypothesis of
`exists_r324Step3_nestedChain_le`. -/
theorem r324Step3_integral_le_cost
    {Gp Gr Jblock : T4 → ℝ} {C lam ε supportConstant K : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|)
    (height :
      ∀ (C' lam' ε' : ℝ) (k' : ℕ) (u' v' : T4),
        0 ≤ C' → 0 ≤ lam' → 0 < ε' → ε' ≤ 1 → 1 ≤ |Real.log ε'| →
          (∫ a, ∫ b,
            r324Step3EightDimIntegrand C' lam' ε' supportConstant k' u' v'
              a b
            ∂paperMeasure ∂paperMeasure) ≤ (C' * lam') ^ (2 * k') * K)
    (hGp : ∀ z, |Gp z| ≤ invSqKer z)
    (hGr : ∀ z, |Gr z| ≤ invSqKer z)
    (hJ : ∀ z,
      |Jblock z| ≤ primitiveInsertedMajorant C lam ε supportConstant k z)
    (u v : T4)
    (hleft : ∀ a : T4,
      Integrable (fun b => Gp (u - a) * Jblock (a - b) * Gr (b - v))
        paperMeasure)
    (hright : ∀ a : T4,
      Integrable
        (fun b =>
          r324Step3EightDimIntegrand C lam ε supportConstant k u v a b)
        paperMeasure)
    (houterL :
      Integrable
        (fun a =>
          ∫ b, Gp (u - a) * Jblock (a - b) * Gr (b - v) ∂paperMeasure)
        paperMeasure)
    (houterR :
      Integrable
        (fun a =>
          ∫ b,
            r324Step3EightDimIntegrand C lam ε supportConstant k u v a b
            ∂paperMeasure)
        paperMeasure) :
    (∫ a, ∫ b, Gp (u - a) * Jblock (a - b) * Gr (b - v)
        ∂paperMeasure ∂paperMeasure) ≤ (C * lam) ^ (2 * k) * K :=
  (r324Step3_integral_le_eightDim hGp hGr hJ u v hleft hright houterL
    houterR).trans
    (height C lam ε k u v hC hlam hε hε1 hlog)

end

end Anderson4D
