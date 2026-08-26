import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticProperStepEstimate
/-!
# Quantitative certificates for production R-322 edge states
The primitive kernel is built from the current heterogeneous internal edges.
Its complete product scale is therefore charged to the predecessor edge at
every proper collapse.
-/
set_option warningAsError true
set_option autoImplicit false
namespace Anderson4D
noncomputable section
open MeasureTheory
open scoped BigOperators
structure R322AnalyticEdgeCertificate
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq)
    (scale : Fin (2 * q - 1) → ℝ) : Prop where
  scale_pos : ∀ edge, 0 < scale edge
  memE : ∀ edge, MemEClassT4 (state.edges edge)
  bound : ∀ edge z, z ≠ 0 →
    |state.edges edge z| ≤ scale edge * invSqKer z
@[simp]
theorem r322CollapseIntegrand_const_mul_middle
    (c : ℝ) (Gp J Gr : T4 → ℝ) (u : T4) (p : T4 × T4) :
    r322CollapseIntegrand Gp (fun z => c * J z) Gr u p =
      c * r322CollapseIntegrand Gp J Gr u p := by
  unfold r322CollapseIntegrand
  ring
/-- The collapse is linear in its middle (primitive-kernel) input. -/
theorem r322Collapse_const_mul_middle
    (c : ℝ) (Gp J Gr : T4 → ℝ) (u : T4) :
    r322Collapse Gp (fun z => c * J z) Gr u =
      c * r322Collapse Gp J Gr u := by
  unfold r322Collapse
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  exact r322CollapseIntegrand_const_mul_middle c Gp J Gr u p

/-- Scale-covariant form of the one-block estimate.  Only the raw
integrability hypothesis is needed: integrability after normalization follows
by multiplication by `Jscale⁻¹`. -/
theorem exists_r322Collapse_le_scaled_middle
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C lam ε A Jscale : ℝ) (n : ℕ)
        (Gp J : T4 → ℝ) (x : T4),
        0 ≤ C → 0 ≤ lam → 0 ≤ A → 0 < Jscale →
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → x ≠ 0 →
        Measurable J → MemEClassT4 J →
        (∀ u, |J u| ≤ Jscale *
          primitiveKernelMajorant C lam ε supportConstant n u) →
        (∀ z, z ≠ 0 → |Gp z| ≤ A * invSqKer z) →
        Integrable (r322CollapseIntegrand Gp J greenFn x)
          (paperMeasure.prod paperMeasure) →
        |r322Collapse Gp J greenFn x| ≤
          A * Jscale * (C * lam) ^ (2 * n) * K * invSqKer x := by
  obtain ⟨K, hK, hcollapse⟩ := exists_r322Collapse_le hsupport
  refine ⟨K, hK, ?_⟩
  intro C lam ε A Jscale n Gp J x hC hlam hA hJscale
    hε hε1 hlog hx hJmeas hJmem hJbound hGp hint
  let Jnorm : T4 → ℝ := fun z => Jscale⁻¹ * J z
  have hJnormMeas : Measurable Jnorm := hJmeas.const_mul _
  have hJnormMem : MemEClassT4 Jnorm := hJmem.const_mul _
  have hJnormBound : ∀ u, |Jnorm u| ≤
      primitiveKernelMajorant C lam ε supportConstant n u := by
    intro u
    dsimp only [Jnorm]
    rw [abs_mul, abs_of_pos (inv_pos.mpr hJscale)]
    calc
      Jscale⁻¹ * |J u| ≤
          Jscale⁻¹ * (Jscale *
            primitiveKernelMajorant C lam ε supportConstant n u) :=
        mul_le_mul_of_nonneg_left (hJbound u)
          (inv_nonneg.mpr hJscale.le)
      _ = primitiveKernelMajorant C lam ε supportConstant n u := by
        rw [← mul_assoc, inv_mul_cancel₀ hJscale.ne', one_mul]
  have hintNorm :
      Integrable (r322CollapseIntegrand Gp Jnorm greenFn x)
        (paperMeasure.prod paperMeasure) := by
    refine (hint.const_mul Jscale⁻¹).congr ?_
    filter_upwards with p
    simp only [Jnorm, r322CollapseIntegrand]
    ring
  have hnorm := hcollapse C lam ε A n Gp Jnorm x
    hC hlam hA hε hε1 hlog hx hJnormMeas hJnormMem
    hJnormBound hGp hintNorm
  have hrecover : (fun z => Jscale * Jnorm z) = J := by
    funext z
    dsimp only [Jnorm]
    rw [← mul_assoc, mul_inv_cancel₀ hJscale.ne', one_mul]
  have hcollapseRecover :
      r322Collapse Gp J greenFn x =
        Jscale * r322Collapse Gp Jnorm greenFn x := by
    rw [← hrecover, r322Collapse_const_mul_middle]
  rw [hcollapseRecover, abs_mul, abs_of_pos hJscale]
  calc
    Jscale * |r322Collapse Gp Jnorm greenFn x| ≤
        Jscale *
          (A * (C * lam) ^ (2 * n) * K * invSqKer x) :=
      mul_le_mul_of_nonneg_left hnorm hJscale.le
    _ = A * Jscale * (C * lam) ^ (2 * n) * K * invSqKer x := by
      ring

/-- At a proper step, the raw primitive scale is the product of all current
internal heterogeneous edge scales. -/
def r322AnalyticInternalEdgeScaleProduct
    {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticProperStepContext q hq)
    (scale : Fin (2 * q - 1) → ℝ) : ℝ :=
  ∏ j : Fin (2 * residualBlockOrder ctx.step.2 - 1),
    scale (ctx.internalEdge j)

theorem R322AnalyticEdgeCertificate.internalEdgeScaleProduct_pos
    {q : ℕ} {hq : 1 ≤ q}
    {ctx : R322AnalyticProperStepContext q hq}
    {scale : Fin (2 * q - 1) → ℝ}
    (hcert : R322AnalyticEdgeCertificate ctx.state scale) :
    0 < r322AnalyticInternalEdgeScaleProduct ctx scale := by
  unfold r322AnalyticInternalEdgeScaleProduct
  exact Finset.prod_pos fun j _ => hcert.scale_pos (ctx.internalEdge j)

/-- Exact ledger update: predecessor scale, raw internal-edge product, block
order power, and universal collapse constant are each charged once. -/
def r322AnalyticUpdatedEdgeScale
    {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticProperStepContext q hq)
    (scale : Fin (2 * q - 1) → ℝ)
    (Jscale C lam K : ℝ) : Fin (2 * q - 1) → ℝ :=
  Function.update scale ctx.predecessorEdge
    (scale ctx.predecessorEdge * Jscale *
      (C * lam) ^ (2 * residualBlockOrder ctx.step.2) * K)

@[simp]
theorem r322AnalyticUpdatedEdgeScale_predecessor
    {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticProperStepContext q hq)
    (scale : Fin (2 * q - 1) → ℝ) (Jscale C lam K : ℝ) :
    r322AnalyticUpdatedEdgeScale ctx scale Jscale C lam K
        ctx.predecessorEdge =
      scale ctx.predecessorEdge * Jscale *
        (C * lam) ^ (2 * residualBlockOrder ctx.step.2) * K := by
  simp [r322AnalyticUpdatedEdgeScale]

theorem r322AnalyticUpdatedEdgeScale_of_ne
    {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticProperStepContext q hq)
    (scale : Fin (2 * q - 1) → ℝ) (Jscale C lam K : ℝ)
    (edge : Fin (2 * q - 1)) (hne : edge ≠ ctx.predecessorEdge) :
    r322AnalyticUpdatedEdgeScale ctx scale Jscale C lam K edge =
      scale edge := by
  simp [r322AnalyticUpdatedEdgeScale, hne]

namespace R322AnalyticProperStepContext

variable {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticProperStepContext q hq)

theorem nextState_edges_eq_of_ne
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (edge : Fin (2 * q - 1)) (hne : edge ≠ ctx.predecessorEdge) :
    (ctx.nextState ρ lam ε).edges edge = ctx.state.edges edge := by
  have hne' : edge ≠
      r322AnalyticPredecessorEdge ctx.state ctx.step ctx.bounds.1 := by
    simpa only [predecessorEdge] using hne
  funext u
  unfold nextState R322AnalyticEdgeState.updateProper
  exact r322ReplaceEdge_apply_ne ctx.state.edges
    (r322AnalyticPredecessorEdge ctx.state ctx.step ctx.bounds.1)
    edge hne'
    (ctx.state.edges
      (r322AnalyticPredecessorEdge ctx.state ctx.step ctx.bounds.1))
    (primitiveKernelDiff ρ lam ε (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges)
    (ctx.state.edges (r322AnalyticOutgoingEdge ctx.step ctx.bounds.2)) u

end R322AnalyticProperStepContext

theorem exists_r322InitialAnalyticEdgeCertificate
    (q : ℕ) (hq : 1 ≤ q) :
    ∃ A : ℝ, 0 < A ∧ R322AnalyticEdgeCertificate
      (r322InitialAnalyticEdgeState q hq) (fun _ => A) := by
  obtain ⟨A, hA, hgreen⟩ := greenFn_le
  refine ⟨A, hA, ⟨fun _ => hA, ?_, ?_⟩⟩
  · intro edge
    simpa [r322InitialAnalyticEdgeState] using greenFn_memE
  · intro edge z hz
    change |greenFn z| ≤ A * invSqKer z
    rw [abs_of_nonneg (greenFn_nonneg z)]
    have hdist : torusDistSq z ≠ 0 := by
      intro hzero
      exact hz ((torusDistSq_eq_zero_iff z).mp hzero)
    simpa [invSqKer, div_eq_mul_inv] using hgreen z hdist

/-- One proper production update preserves the full slotwise certificate.
Unlike the normalized one-block theorem, this production interface explicitly
charges the raw primitive scale `Jscale`. -/
theorem exists_r322AnalyticEdgeCertificate_updateProper
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ρ : SmoothCutoff) (C lam ε Jscale : ℝ)
        (q : ℕ) (hq : 1 ≤ q)
        (κ : PartialPairing (Fin (2 * q)))
        (hκ : κ ∈ nonSplitPairings q)
        (ctx : R322AnalyticProperStepContext q hq)
        (_hstate : R322AnalyticAbsorbedState
          ρ lam ε hq κ hκ ctx.state)
        (_hpairing : ctx.pairing = κ)
        (scale : Fin (2 * q - 1) → ℝ),
        R322AnalyticEdgeCertificate ctx.state scale →
        0 < C → 0 < lam → 0 < Jscale →
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        Measurable (primitiveKernelDiff ρ lam ε
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder ctx.internalEdges) →
        MemEClassT4 (primitiveKernelDiff ρ lam ε
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder ctx.internalEdges) →
        (∀ u, |primitiveKernelDiff ρ lam ε
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder ctx.internalEdges u| ≤
          Jscale * primitiveKernelMajorant C lam ε supportConstant
            (residualBlockOrder ctx.step.2) u) →
        (∀ x, x ≠ 0 → Integrable (r322CollapseIntegrand
          (ctx.state.edges ctx.predecessorEdge)
          (primitiveKernelDiff ρ lam ε
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder ctx.internalEdges)
          greenFn x) (paperMeasure.prod paperMeasure)) →
        R322AnalyticEdgeCertificate (ctx.nextState ρ lam ε)
          (r322AnalyticUpdatedEdgeScale
            ctx scale Jscale C lam K) := by
  obtain ⟨K, hK, hstep⟩ :=
    exists_r322Collapse_le_scaled_middle hsupport
  refine ⟨K, hK, ?_⟩
  intro ρ C lam ε Jscale q hq κ hκ ctx hstate hpairing scale
    hcert hC hlam hJscale hε hε1 hlog hJmeas hJmem hJbound hint
  let J : T4 → ℝ := primitiveKernelDiff ρ lam ε
    (residualBlockOrder ctx.step.2)
    ctx.one_le_blockOrder ctx.internalEdges
  have hpredBound : ∀ x : T4, x ≠ 0 →
      |(ctx.nextState ρ lam ε).edges ctx.predecessorEdge x| ≤
        scale ctx.predecessorEdge * Jscale *
          (C * lam) ^ (2 * residualBlockOrder ctx.step.2) *
          K * invSqKer x := by
    intro x hx
    rw [ctx.nextState_predecessor_eq_r322Collapse_greenFn
      hstate hpairing x]
    exact hstep C lam ε (scale ctx.predecessorEdge) Jscale
      (residualBlockOrder ctx.step.2)
      (ctx.state.edges ctx.predecessorEdge) J x
      hC.le hlam.le (hcert.scale_pos ctx.predecessorEdge).le hJscale
      hε hε1 hlog hx hJmeas hJmem hJbound
      (hcert.bound ctx.predecessorEdge) (hint x hx)
  refine ⟨?_, ?_, ?_⟩
  · intro edge
    by_cases hedge : edge = ctx.predecessorEdge
    · subst edge
      rw [r322AnalyticUpdatedEdgeScale_predecessor]
      exact mul_pos
        (mul_pos (mul_pos (hcert.scale_pos _) hJscale)
          (pow_pos (mul_pos hC hlam) _)) hK
    · rw [r322AnalyticUpdatedEdgeScale_of_ne
        ctx scale Jscale C lam K edge hedge]
      exact hcert.scale_pos edge
  · intro edge
    by_cases hedge : edge = ctx.predecessorEdge
    · subst edge
      have heq : (ctx.nextState ρ lam ε).edges ctx.predecessorEdge =
          r322Collapse (ctx.state.edges ctx.predecessorEdge)
            J greenFn := by
        funext u
        exact ctx.nextState_predecessor_eq_r322Collapse_greenFn
          hstate hpairing u
      rw [heq]
      exact r322Collapse_memE
        (hcert.memE ctx.predecessorEdge) hJmem greenFn_memE
    · rw [ctx.nextState_edges_eq_of_ne ρ lam ε edge hedge]
      exact hcert.memE edge
  · intro edge z hz
    by_cases hedge : edge = ctx.predecessorEdge
    · subst edge
      simpa using hpredBound z hz
    · rw [ctx.nextState_edges_eq_of_ne ρ lam ε edge hedge,
        r322AnalyticUpdatedEdgeScale_of_ne
          ctx scale Jscale C lam K edge hedge]
      exact hcert.bound edge z hz

/-- Production specialization: `Jscale` is the product of the actual current
internal edge scales, rather than an unrelated external normalization. -/
theorem exists_r322AnalyticEdgeCertificate_updateProper_internalProduct
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ρ : SmoothCutoff) (C lam ε : ℝ)
      (q : ℕ) (hq : 1 ≤ q) (κ : PartialPairing (Fin (2 * q)))
      (hκ : κ ∈ nonSplitPairings q) (ctx : R322AnalyticProperStepContext q hq)
      (_hstate : R322AnalyticAbsorbedState ρ lam ε hq κ hκ ctx.state)
      (_hpairing : ctx.pairing = κ) (scale : Fin (2 * q - 1) → ℝ),
      R322AnalyticEdgeCertificate ctx.state scale → 0 < C → 0 < lam →
      0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
      Measurable (primitiveKernelDiff ρ lam ε (residualBlockOrder ctx.step.2) ctx.one_le_blockOrder ctx.internalEdges) →
      MemEClassT4 (primitiveKernelDiff ρ lam ε (residualBlockOrder ctx.step.2) ctx.one_le_blockOrder ctx.internalEdges) →
      (∀ u, |primitiveKernelDiff ρ lam ε (residualBlockOrder ctx.step.2) ctx.one_le_blockOrder ctx.internalEdges u| ≤
        r322AnalyticInternalEdgeScaleProduct ctx scale *
          primitiveKernelMajorant C lam ε supportConstant (residualBlockOrder ctx.step.2) u) →
      (∀ x, x ≠ 0 → Integrable (r322CollapseIntegrand (ctx.state.edges ctx.predecessorEdge)
        (primitiveKernelDiff ρ lam ε (residualBlockOrder ctx.step.2) ctx.one_le_blockOrder ctx.internalEdges)
        greenFn x) (paperMeasure.prod paperMeasure)) →
      R322AnalyticEdgeCertificate (ctx.nextState ρ lam ε)
        (r322AnalyticUpdatedEdgeScale ctx scale
          (r322AnalyticInternalEdgeScaleProduct ctx scale) C lam K) := by
  obtain ⟨K, hK, hstep⟩ := exists_r322AnalyticEdgeCertificate_updateProper hsupport
  refine ⟨K, hK, ?_⟩
  intro ρ C lam ε q hq κ hκ ctx hstate hpairing scale hcert hC hlam hε hε1 hlog hmeas hmem hbound hint
  exact hstep ρ C lam ε (r322AnalyticInternalEdgeScaleProduct ctx scale)
    q hq κ hκ ctx hstate hpairing scale hcert hC hlam
    hcert.internalEdgeScaleProduct_pos hε hε1 hlog hmeas hmem hbound hint

end

end Anderson4D
