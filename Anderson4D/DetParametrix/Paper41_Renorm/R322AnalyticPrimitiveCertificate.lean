import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticEdgeCertificate
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticIterationClosure

/-!
# Actual primitive certificates for production R-322

Edge certificates control kernels only away from the identity.  This file
keeps that distinction exact: the raw primitive kernel is replaced at one
point only inside the collapse integral, where the diagonal is null.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- The diagonal in the two-endpoint paper product is null. -/
theorem ae_fst_ne_snd_paperMeasure :
    ∀ᵐ p : T4 × T4 ∂(paperMeasure.prod paperMeasure), p.1 ≠ p.2 := by
  rw [Measure.ae_prod_iff_ae_ae]
  · filter_upwards with x
    filter_upwards
        [compl_mem_ae_iff.mpr (paperMeasure_singleton x)] with y hy
    exact Ne.symm (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy)
  · exact (measurableSet_eq_fun
      (f := fun p : T4 × T4 => p.1)
      (g := fun p : T4 × T4 => p.2)
      measurable_fst measurable_snd).compl

/-- Zeroing the primitive input at the identity changes the collapse
integrand only on the null endpoint diagonal. -/
theorem r322CollapseIntegrand_offDiagonalRepresentative_ae_eq
    (Gp J Gr : T4 → ℝ) (u : T4) :
    r322CollapseIntegrand Gp (offDiagonalRepresentative J) Gr u =ᵐ[
        paperMeasure.prod paperMeasure]
      r322CollapseIntegrand Gp J Gr u := by
  filter_upwards [ae_fst_ne_snd_paperMeasure] with p hp
  unfold r322CollapseIntegrand
  rw [offDiagonalRepresentative_eq J (sub_ne_zero.mpr hp)]

theorem r322Collapse_offDiagonalRepresentative
    (Gp J Gr : T4 → ℝ) (u : T4) :
    r322Collapse Gp (offDiagonalRepresentative J) Gr u =
      r322Collapse Gp J Gr u := by
  unfold r322Collapse
  exact integral_congr_ae
    (r322CollapseIntegrand_offDiagonalRepresentative_ae_eq Gp J Gr u)

theorem measurable_offDiagonalRepresentative
    {J : T4 → ℝ} (hJ : Measurable J) :
    Measurable (offDiagonalRepresentative J) := by
  unfold offDiagonalRepresentative
  exact Measurable.ite (measurableSet_singleton 0)
    measurable_const hJ

/-- Scaled one-block closure from an off-diagonal primitive bound.  Raw
integrability remains an explicit premise and is transported by a.e.
equality; it is not inferred from the pointwise majorant. -/
theorem exists_r322Collapse_le_scaled_middle_offDiagonal
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C lam ε A Jscale : ℝ) (n : ℕ)
        (Gp J : T4 → ℝ) (x : T4),
        0 ≤ C → 0 ≤ lam → 0 ≤ A → 0 < Jscale →
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → x ≠ 0 →
        Measurable J → MemEClassT4 J →
        (∀ u, u ≠ 0 → |J u| ≤ Jscale *
          primitiveKernelMajorant C lam ε supportConstant n u) →
        (∀ z, z ≠ 0 → |Gp z| ≤ A * invSqKer z) →
        Integrable (r322CollapseIntegrand Gp J greenFn x)
          (paperMeasure.prod paperMeasure) →
        |r322Collapse Gp J greenFn x| ≤
          A * Jscale * (C * lam) ^ (2 * n) * K * invSqKer x := by
  obtain ⟨K, hK, hscaled⟩ :=
    exists_r322Collapse_le_scaled_middle hsupport
  refine ⟨K, hK, ?_⟩
  intro C lam ε A Jscale n Gp J x hC hlam hA hJscale
    hε hε1 hlog hx hJmeas hJmem hJbound hGp hint
  have hbound' : ∀ u, |offDiagonalRepresentative J u| ≤
      Jscale * primitiveKernelMajorant
        C lam ε supportConstant n u := by
    intro u
    by_cases hu : u = 0
    · subst u
      rw [offDiagonalRepresentative_zero, abs_zero]
      exact mul_nonneg hJscale.le
        (primitiveKernelMajorant_nonneg hC hlam)
    · rw [offDiagonalRepresentative_eq J hu]
      exact hJbound u hu
  have hint' : Integrable
      (r322CollapseIntegrand Gp (offDiagonalRepresentative J) greenFn x)
      (paperMeasure.prod paperMeasure) := by
    exact (integrable_congr
      (r322CollapseIntegrand_offDiagonalRepresentative_ae_eq
        Gp J greenFn x)).mpr hint
  rw [← r322Collapse_offDiagonalRepresentative Gp J greenFn x]
  exact hscaled C lam ε A Jscale n Gp
    (offDiagonalRepresentative J) x hC hlam hA hJscale
    hε hε1 hlog hx (measurable_offDiagonalRepresentative hJmeas)
    (offDiagonalRepresentative_memE hJmem) hbound' hGp hint'

/-- Product-scale Proposition 4.1 estimate valid away from the external
diagonal at every order, including order one. -/
theorem primitiveKernelDiff_le_prod_edgeScales_mul_majorant_offDiagonal
    (ρ : SmoothCutoff)
    {lam ε supportConstant primitiveConstant : ℝ}
    {n : ℕ} (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (Cedge : Fin (2 * n - 1) → ℝ)
    (hCedge : ∀ j, 0 < Cedge j)
    (hmem : ∀ j, MemEClassT4 (G j))
    (hbound : ∀ j z, z ≠ 0 →
      |G j z| ≤ Cedge j * invSqKer z)
    (hprop : ∀ (H : Fin (2 * n - 1) → T4 → ℝ),
      IsAdmissiblePrimitiveInput n H →
        MemEClassT4 (primitiveKernelDiff ρ lam ε n hn H) ∧
        MemEClassT4 (primitiveKernelInsertedDiff ρ lam ε n hn H) ∧
        PrimitiveKernelBounds ρ lam ε n hn H
          supportConstant primitiveConstant)
    (z : T4) (hz : z ≠ 0) :
    |primitiveKernelDiff ρ lam ε n hn G z| ≤
      (∏ j, Cedge j) *
        primitiveKernelMajorant primitiveConstant lam ε
          supportConstant n z := by
  by_cases hnOne : n = 1
  · subst n
    let H : Fin 1 → T4 → ℝ :=
      fun j => normalizedOffDiagonalRepresentative (Cedge j) (G j)
    have hadm : IsAdmissiblePrimitiveInput 1 H :=
      normalizedOffDiagonalRepresentative_admissible
        hCedge hmem hbound
    have hbounds := (hprop H hadm).2.2
    have hprod : 0 ≤ ∏ j : Fin 1, Cedge j :=
      Finset.prod_nonneg fun j _ => (hCedge j).le
    have heq : primitiveKernelDiff ρ lam ε 1 hn G z =
        (∏ j : Fin 1, Cedge j) *
          primitiveKernelDiff ρ lam ε 1 hn H z := by
      unfold primitiveKernelDiff
      rw [primitiveKernel_one, primitiveKernel_one, sub_zero]
      have hzero := mul_normalizedOffDiagonalRepresentative_eq
        (hCedge (0 : Fin 1)) (G 0) hz
      simp only [H, Fin.prod_univ_one]
      rw [← hzero]
      ring
    rw [heq, abs_mul, abs_of_nonneg hprod]
    exact mul_le_mul_of_nonneg_left (hbounds z).1 hprod
  · have hnTwo : 2 ≤ n := by omega
    exact primitiveKernelDiff_le_prod_edgeScales_mul_majorant
      ρ hnTwo G Cedge hCedge hmem hbound hprop z

/-- The actual primitive kernel data consumed by a production proper step.
Integrability is intentionally a field, not a derived claim. -/
structure R322AnalyticPrimitiveCertificate
    {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticProperStepContext q hq)
    (scale : Fin (2 * q - 1) → ℝ)
    (ρ : SmoothCutoff) (C lam ε supportConstant : ℝ) : Prop where
  measurable : Measurable (primitiveKernelDiff ρ lam ε
    (residualBlockOrder ctx.step.2) ctx.one_le_blockOrder ctx.internalEdges)
  memE : MemEClassT4 (primitiveKernelDiff ρ lam ε
    (residualBlockOrder ctx.step.2) ctx.one_le_blockOrder ctx.internalEdges)
  bound : ∀ u, u ≠ 0 →
    |primitiveKernelDiff ρ lam ε (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges u| ≤
    r322AnalyticInternalEdgeScaleProduct ctx scale *
      primitiveKernelMajorant C lam ε supportConstant
        (residualBlockOrder ctx.step.2) u
  integrable : ∀ x, x ≠ 0 → Integrable (r322CollapseIntegrand
    (ctx.state.edges ctx.predecessorEdge)
    (primitiveKernelDiff ρ lam ε (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges) greenFn x)
    (paperMeasure.prod paperMeasure)

/-- Proposition 4.1 plus explicit raw measurability and integrability premises
produce the actual primitive certificate. -/
theorem R322AnalyticEdgeCertificate.primitiveCertificate
    {q : ℕ} {hq : 1 ≤ q}
    {ctx : R322AnalyticProperStepContext q hq}
    {scale : Fin (2 * q - 1) → ℝ}
    (hcert : R322AnalyticEdgeCertificate ctx.state scale)
    (ρ : SmoothCutoff) (C lam ε supportConstant : ℝ)
    (hmeas : Measurable (primitiveKernelDiff ρ lam ε
      (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges))
    (hprop : ∀ H, IsAdmissiblePrimitiveInput
        (residualBlockOrder ctx.step.2) H →
      MemEClassT4 (primitiveKernelDiff ρ lam ε
        (residualBlockOrder ctx.step.2) ctx.one_le_blockOrder H) ∧
      MemEClassT4 (primitiveKernelInsertedDiff ρ lam ε
        (residualBlockOrder ctx.step.2) ctx.one_le_blockOrder H) ∧
      PrimitiveKernelBounds ρ lam ε (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder H supportConstant C)
    (hint : ∀ x, x ≠ 0 → Integrable (r322CollapseIntegrand
      (ctx.state.edges ctx.predecessorEdge)
      (primitiveKernelDiff ρ lam ε (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder ctx.internalEdges) greenFn x)
      (paperMeasure.prod paperMeasure)) :
    R322AnalyticPrimitiveCertificate
      ctx scale ρ C lam ε supportConstant := by
  refine ⟨hmeas, ?_, ?_, hint⟩
  · exact primitiveKernelDiff_memE ρ lam ε _ ctx.one_le_blockOrder
      ctx.internalEdges fun j => hcert.memE (ctx.internalEdge j)
  · intro u hu
    simpa [r322AnalyticInternalEdgeScaleProduct,
      R322AnalyticProperStepContext.internalEdges] using
      primitiveKernelDiff_le_prod_edgeScales_mul_majorant_offDiagonal
        ρ ctx.one_le_blockOrder ctx.internalEdges
        (fun j => scale (ctx.internalEdge j))
        (fun j => hcert.scale_pos (ctx.internalEdge j))
        (fun j => hcert.memE (ctx.internalEdge j))
        (fun j => hcert.bound (ctx.internalEdge j))
        hprop u hu

/-- One-step production closure driven by an actual off-diagonal primitive
certificate. -/
theorem exists_r322AnalyticEdgeCertificate_updateProper_internalProduct_offDiagonal
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ρ : SmoothCutoff) (C lam ε : ℝ)
        (q : ℕ) (hq : 1 ≤ q) (κ : PartialPairing (Fin (2 * q)))
        (hκ : κ ∈ nonSplitPairings q)
        (ctx : R322AnalyticProperStepContext q hq)
        (_hstate : R322AnalyticAbsorbedState ρ lam ε hq κ hκ ctx.state)
        (_hpairing : ctx.pairing = κ)
        (scale : Fin (2 * q - 1) → ℝ),
        R322AnalyticEdgeCertificate ctx.state scale →
        R322AnalyticPrimitiveCertificate
          ctx scale ρ C lam ε supportConstant →
        0 < C → 0 < lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| →
        R322AnalyticEdgeCertificate (ctx.nextState ρ lam ε)
          (r322AnalyticUpdatedEdgeScale ctx scale
            (r322AnalyticInternalEdgeScaleProduct ctx scale)
            C lam K) := by
  obtain ⟨K, hK, hstep⟩ :=
    exists_r322Collapse_le_scaled_middle_offDiagonal hsupport
  refine ⟨K, hK, ?_⟩
  intro ρ C lam ε q hq κ hκ ctx hstate hpairing scale
    hcert hprimitive hC hlam hε hε1 hlog
  let J := primitiveKernelDiff ρ lam ε
    (residualBlockOrder ctx.step.2) ctx.one_le_blockOrder ctx.internalEdges
  have hJscale := hcert.internalEdgeScaleProduct_pos
  have hpred : ∀ x, x ≠ 0 →
      |(ctx.nextState ρ lam ε).edges ctx.predecessorEdge x| ≤
      scale ctx.predecessorEdge *
        r322AnalyticInternalEdgeScaleProduct ctx scale *
        (C * lam) ^ (2 * residualBlockOrder ctx.step.2) *
        K * invSqKer x := by
    intro x hx
    rw [ctx.nextState_predecessor_eq_r322Collapse_greenFn
      hstate hpairing x]
    exact hstep C lam ε (scale ctx.predecessorEdge)
      (r322AnalyticInternalEdgeScaleProduct ctx scale)
      (residualBlockOrder ctx.step.2)
      (ctx.state.edges ctx.predecessorEdge) J x
      hC.le hlam.le (hcert.scale_pos _).le hJscale
      hε hε1 hlog hx hprimitive.measurable hprimitive.memE
      hprimitive.bound (hcert.bound _) (hprimitive.integrable x hx)
  refine ⟨?_, ?_, ?_⟩
  · intro edge
    by_cases hedge : edge = ctx.predecessorEdge
    · subst edge
      rw [r322AnalyticUpdatedEdgeScale_predecessor]
      exact mul_pos (mul_pos (mul_pos (hcert.scale_pos _) hJscale)
        (pow_pos (mul_pos hC hlam) _)) hK
    · rw [r322AnalyticUpdatedEdgeScale_of_ne
        ctx scale _ C lam K edge hedge]
      exact hcert.scale_pos edge
  · intro edge
    by_cases hedge : edge = ctx.predecessorEdge
    · subst edge
      have heq : (ctx.nextState ρ lam ε).edges ctx.predecessorEdge =
          r322Collapse (ctx.state.edges ctx.predecessorEdge) J greenFn := by
        funext u
        exact ctx.nextState_predecessor_eq_r322Collapse_greenFn
          hstate hpairing u
      rw [heq]
      exact r322Collapse_memE (hcert.memE _) hprimitive.memE greenFn_memE
    · rw [ctx.nextState_edges_eq_of_ne ρ lam ε edge hedge]
      exact hcert.memE edge
  · intro edge z hz
    by_cases hedge : edge = ctx.predecessorEdge
    · subst edge
      simpa using hpred z hz
    · rw [ctx.nextState_edges_eq_of_ne ρ lam ε edge hedge,
        r322AnalyticUpdatedEdgeScale_of_ne
          ctx scale _ C lam K edge hedge]
      exact hcert.bound edge z hz

end

end Anderson4D
