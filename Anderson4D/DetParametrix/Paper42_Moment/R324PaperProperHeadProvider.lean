import Anderson4D.DetParametrix.Paper42_Moment.R324NestedCrossBudgetIteration
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperStep3Pointwise

/-!
# Paper §4.2, Step 3(c): the proper-head provider, discharged

Paper: R-324 — §4.2 Step 3(c), `R324ProperHeadSharpProvider` proved

`R324NestedCrossBudgetIteration` performs Step 3's nested-cross iteration
on the actual carrier, and takes exactly one analytic input: the
`R324ProperHeadSharpProvider`, whose single field is

```
∀ ctx left right, ctx.properHeadIntegral ρ lam ε left right ≤ (D·λ)^{2·order}
```

Unfolding, `properHeadIntegral` is

```
∫ p, |left − p₁|⁻² · crossGapPrimitiveTerm(p₁ − p₂) · |p₂ − right|⁻²
```

which is **literally** the elementary eight-dimensional integral of paper
Step 3(c).  So the provider is the paper's own sentence

> "the induced pairing is primitive, so (4.4) bounds the inner sum"

and it follows from four proved facts, in this order:

1. `crossGapPrimitiveTerm_le_insertedTerm` — the moving-gap term is below
   the inserted pairing term at the block's own pairing (the hypotheses are
   `normalizedInput_{measurable,nonneg,admissible}`);
2. `primitivePairingKernelInsertedTerm_le_kernel` — one pairing's term is
   below the primitive sum (`blockPairing_mem`);
3. `proposition41_at_truncation` — (4.4) bounds that by the inserted
   majorant, at any order inside the paper truncation, which
   `order_le_ambient` supplies from the cap `m ≤ ⌊|log ε|⌋`;
4. `exists_r324ProperInsertedConvolution_le` — the resulting
   `|·|⁻² ∗ J̃ ∗ |·|⁻²` convolution is bounded by `(Cλ)^{2·order}·K`, whose
   `K` is absorbed into the base.

The nonnegativity used in 1–2 is the `|G_j|` branch of (4.19)–(4.20): it is
legitimate here precisely because the removals of Step 2(d)–(e) have
already been performed, i.e. Step 2(f) has been passed.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- One factor of `max K 1` per removed *site* pays for the single
elementary constant `K` of Step 3(c). -/
private theorem r324ProperHead_absorb {C lam K : ℝ} {n : ℕ}
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hn : 1 ≤ n) :
    (C * lam) ^ (2 * n) * K ≤ ((C * max K 1) * lam) ^ (2 * n) := by
  have hK1 : (1 : ℝ) ≤ max K 1 := le_max_right _ _
  have hbase : (0 : ℝ) ≤ (C * lam) ^ (2 * n) := by positivity
  have hKt : K ≤ (max K 1) ^ (2 * n) := by
    calc K ≤ max K 1 := le_max_left _ _
      _ = (max K 1) ^ 1 := (pow_one _).symm
      _ ≤ (max K 1) ^ (2 * n) := pow_le_pow_right₀ hK1 (by omega)
  calc
    (C * lam) ^ (2 * n) * K ≤ (C * lam) ^ (2 * n) * (max K 1) ^ (2 * n) :=
      mul_le_mul_of_nonneg_left hKt hbase
    _ = ((C * max K 1) * lam) ^ (2 * n) := by
      rw [← mul_pow]; congr 1; ring

/-- **Step 3(c) at one proper nested head: the moving-gap term is below
the inserted majorant of (4.4).** -/
theorem r324NestedCross_crossGapPrimitiveTerm_le_majorant
    (ρ : SmoothCutoff) {lam ε : ℝ} {supportConstant C : ℝ}
    (hprop :
      ∀ (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        0 < lam → 0 < ε → ε ≤ 1 → n ≤ truncOrder ε →
        IsAdmissiblePrimitiveInput n G →
        ∀ z : T4,
          |primitiveKernelInsertedDiff ρ lam ε n hn G z| ≤
            primitiveInsertedMajorant C lam ε supportConstant n z)
    (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossStepContext κp κm π)
    (hmtrunc : m ≤ truncOrder ε) (z : T4) :
    ctx.crossGapPrimitiveTerm ρ lam ε ctx.normalizedInput z 0 ≤
      primitiveInsertedMajorant C lam ε supportConstant ctx.order z := by
  have hktrunc : ctx.order ≤ truncOrder ε :=
    le_trans ctx.order_le_ambient hmtrunc
  have hstep1 :=
    ctx.crossGapPrimitiveTerm_le_insertedTerm ρ lam hε hε1
      ctx.normalizedInput ctx.normalizedInput_measurable
      ctx.normalizedInput_admissible ctx.normalizedInput_nonneg z 0
  have hstep2 :=
    primitivePairingKernelInsertedTerm_le_kernel ρ lam ε ctx.order
      ctx.one_le_order ctx.normalizedInput ctx.normalizedInput_nonneg
      ctx.blockPairing ctx.blockPairing_mem z 0
  have hstep3 :
      primitiveKernelInserted ρ lam ε ctx.order ctx.one_le_order
          ctx.normalizedInput z 0 ≤
        primitiveInsertedMajorant C lam ε supportConstant ctx.order z := by
    have := hprop lam ε ctx.order ctx.one_le_order ctx.normalizedInput
      hlam hε hε1 hktrunc ctx.normalizedInput_admissible z
    exact le_trans (le_abs_self _) this
  exact (hstep1.trans hstep2).trans hstep3

/-- **The proper-head provider of Step 3, discharged.**

Every hypothesis is the paper's: a positive coupling, a small scale, and
the paper truncation `m ≤ ⌊|log ε|⌋` under which (3.24) is asserted at
all.  The constant is chosen before the coupling, the scale, the order,
the pairings, and the head. -/
theorem exists_r324ProperHeadSharpProvider (ρ : SmoothCutoff) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (lam ε : ℝ) {m : ℕ} {κp κm : PartialPairing (Fin m)}
        (π : κp.singles ≃ κm.singles),
        0 < lam → 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → m ≤ truncOrder ε →
          R324ProperHeadSharpProvider ρ lam ε D κp κm π := by
  obtain ⟨supportConstant, C, hsupport, hC, hprop⟩ :=
    proposition41_at_truncation ρ
  obtain ⟨K, hK, hconv⟩ := exists_r324ProperInsertedConvolution_le hsupport
  refine ⟨C * max K 1, by positivity, ?_⟩
  intro lam ε m κp κm π hlam hε hε1 hlog hmtrunc
  refine ⟨?_⟩
  intro ctx left right
  set n : ℕ := ctx.step.order with hn
  have hn1 : 1 ≤ n := ctx.step.one_le_order
  -- (1)-(3): the moving-gap term is below the inserted majorant of (4.4)
  have hgap : ∀ z : T4,
      ctx.step.crossGapPrimitiveTerm ρ lam ε ctx.step.normalizedInput z 0 ≤
        primitiveInsertedMajorant C lam ε supportConstant n z := by
    intro z
    exact
      r324NestedCross_crossGapPrimitiveTerm_le_majorant ρ
        (fun lam' ε' n' hn' G hlam' hε' hε1' htrunc' hadm' z' =>
          (hprop lam' ε' n' hn' G hlam' hε' hε1' htrunc' hadm').2.2 z' |>.2)
        hlam hε hε1 ctx.step hmtrunc z
  -- (4): the elementary eight-dimensional integral
  obtain ⟨hint, hbound⟩ :=
    hconv C lam ε n left right hC.le hlam.le hε hε1 hlog
  have hle :
      ctx.properHeadIntegral ρ lam ε left right ≤
        ∫ p : T4 × T4,
          r324ProperInsertedConvolutionIntegrand C lam ε supportConstant n
            left right p
          ∂(paperMeasure.prod paperMeasure) := by
    unfold R324NestedCrossProperStepContext.properHeadIntegral
    refine integral_mono_of_nonneg (.of_forall fun p => ?_) hint
      (.of_forall fun p => ?_)
    · exact mul_nonneg
        (mul_nonneg (invSqKer_nonneg _)
          (ctx.step.crossGapPrimitiveTerm_nonneg ρ lam ε
            ctx.step.normalizedInput ctx.step.normalizedInput_nonneg _ _))
        (invSqKer_nonneg _)
    · unfold r324ProperInsertedConvolutionIntegrand
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hgap _) (invSqKer_nonneg _))
        (invSqKer_nonneg _)
  calc
    ctx.properHeadIntegral ρ lam ε left right ≤
        ∫ p : T4 × T4,
          r324ProperInsertedConvolutionIntegrand C lam ε supportConstant n
            left right p
          ∂(paperMeasure.prod paperMeasure) := hle
    _ = ∫ a, ∫ b,
          invSqKer (left - a) *
            primitiveInsertedMajorant C lam ε supportConstant n (a - b) *
            invSqKer (b - right)
          ∂paperMeasure ∂paperMeasure := by
      rw [integral_prod _ hint]
      rfl
    _ ≤ (C * lam) ^ (2 * n) * K := hbound
    _ ≤ ((C * max K 1) * lam) ^ (2 * n) :=
      r324ProperHead_absorb hC.le hlam.le hn1

end

end Anderson4D
