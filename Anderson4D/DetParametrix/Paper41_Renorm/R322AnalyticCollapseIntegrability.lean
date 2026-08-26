import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticPrimitiveCertificate
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticReachableIntegrability
import Anderson4D.Continuum.CellChainComplete

/-!
# Fixed-endpoint integrability for production R-322 collapses

This file closes the raw Bochner-integrability field in the production
primitive certificate.  The proof is pointwise at every nonzero external
endpoint; it does not promote the almost-everywhere section supplied by
Fubini.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

private theorem integrable_invSqTripleProduct (x y : T4) :
    Integrable
      (fun p : T4 × T4 =>
        invSqKer (x - p.1) * invSqKer (p.1 - p.2) *
          invSqKer (p.2 - y))
      (paperMeasure.prod paperMeasure) := by
  exact integrable_localTripleProduct x y

private theorem ae_fst_ne_paperMeasure (a : T4) :
    ∀ᵐ p : T4 × T4 ∂(paperMeasure.prod paperMeasure), p.1 ≠ a := by
  rw [Measure.ae_prod_iff_ae_ae]
  · filter_upwards
      [compl_mem_ae_iff.mpr (paperMeasure_singleton a)] with z hz
    filter_upwards with w
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
  · exact
      (measurableSet_eq_fun
        (f := fun p : T4 × T4 => p.1)
        (g := fun _ => a)
        measurable_fst measurable_const).compl

private theorem ae_snd_ne_paperMeasure (a : T4) :
    ∀ᵐ p : T4 × T4 ∂(paperMeasure.prod paperMeasure), p.2 ≠ a := by
  rw [Measure.ae_prod_iff_ae_ae]
  · filter_upwards with z
    filter_upwards
        [compl_mem_ae_iff.mpr (paperMeasure_singleton a)] with w hw
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hw
  · exact
      (measurableSet_eq_fun
        (f := fun p : T4 × T4 => p.2)
        (g := fun _ => a)
        measurable_snd measurable_const).compl

private theorem integrable_invSqBridgeProduct
    {x : T4} (hx : x ≠ 0) :
    Integrable
      (fun p : T4 × T4 =>
        (invSqKer (x - p.1) * invSqKer p.1) *
          invSqKer (p.1 - p.2))
      (paperMeasure.prod paperMeasure) := by
  let f : T4 → ℝ := fun z =>
    invSqKer (x - z) * invSqKer z
  have hf : Integrable f paperMeasure :=
    integrable_invSqKer_sub_mul_invSqKer_of_ne hx
  have hmeas :
      AEStronglyMeasurable
        (fun p : T4 × T4 =>
          f p.2 * invSqKer (p.2 - p.1))
        (paperMeasure.prod paperMeasure) :=
    (((measurable_invSqKer.comp
        (measurable_const.sub measurable_snd)).mul
      (measurable_invSqKer.comp measurable_snd)).mul
      (measurable_invSqKer.comp
        (measurable_snd.sub measurable_fst))).aestronglyMeasurable
  have hswap :
      Integrable
        (fun p : T4 × T4 =>
          f p.2 * invSqKer (p.2 - p.1))
        (paperMeasure.prod paperMeasure) := by
    rw [integrable_prod_iff' hmeas]
    constructor
    · filter_upwards with z
      exact (integrable_invSqKer_sub_left z).const_mul (f z)
    · have hnormIntegral :
          (fun z : T4 =>
            ∫ w, ‖f z * invSqKer (z - w)‖ ∂paperMeasure) =
          fun z => ‖f z‖ * invSqKerMass := by
        funext z
        rw [show
            (fun w : T4 => ‖f z * invSqKer (z - w)‖) =
              fun w => ‖f z‖ * invSqKer (z - w) by
            funext w
            rw [norm_mul]
            congr 1
            rw [Real.norm_eq_abs,
              abs_of_nonneg (invSqKer_nonneg _)]]
        rw [integral_const_mul, integral_invSqKer_sub_left]
      rw [hnormIntegral]
      exact hf.norm.mul_const invSqKerMass
  have h := hswap.swap
  convert h using 1
  funext p
  rfl

private theorem integrable_invSqCollapseMajorant
    {x : T4} (hx : x ≠ 0) :
    Integrable
      (fun p : T4 × T4 =>
        invSqKer (x - p.1) * invSqKer (p.1 - p.2) *
            invSqKer p.2 +
          invSqKer (x - p.1) * invSqKer p.2 +
          (invSqKer (x - p.1) * invSqKer p.1) *
            invSqKer (p.1 - p.2) +
          invSqKer (x - p.1) * invSqKer p.1)
      (paperMeasure.prod paperMeasure) := by
  have htriple :
      Integrable
        (fun p : T4 × T4 =>
          invSqKer (x - p.1) * invSqKer (p.1 - p.2) *
            invSqKer (p.2 - 0))
        (paperMeasure.prod paperMeasure) :=
    integrable_invSqTripleProduct x 0
  have hseparated :
      Integrable
        (fun p : T4 × T4 =>
          invSqKer (x - p.1) * invSqKer p.2)
        (paperMeasure.prod paperMeasure) :=
    (integrable_invSqKer_sub_left x).mul_prod integrable_invSqKer
  have hbridge := integrable_invSqBridgeProduct hx
  have hbinary :
      Integrable
        (fun z : T4 =>
          invSqKer (x - z) * invSqKer z)
        paperMeasure :=
    integrable_invSqKer_sub_mul_invSqKer_of_ne hx
  have hbinaryLift :
      Integrable
        (fun p : T4 × T4 =>
          invSqKer (x - p.1) * invSqKer p.1)
        (paperMeasure.prod paperMeasure) := by
    have h := hbinary.mul_prod
      (integrable_const (μ := paperMeasure) (c := (1 : ℝ)))
    convert h using 1
    funext p
    simp
  have hsum :=
    ((htriple.add hseparated).add hbridge).add hbinaryLift
  apply hsum.congr
  filter_upwards with p
  simp only [sub_zero, Pi.add_apply]

/-- A fixed nonzero endpoint makes the raw proper-block collapse absolutely
integrable as soon as its predecessor and middle kernels have the paper's
inverse-square bounds.  This is a pointwise statement, not an a.e.-section
consequence of joint Fubini. -/
theorem integrable_r322CollapseIntegrand_of_invSq_add_one
    {Gp J : T4 → ℝ} {A B Cgreen : ℝ} {x : T4}
    (hGpMeas : Measurable Gp) (hJMeas : Measurable J)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hCgreen : 0 ≤ Cgreen)
    (hGp : ∀ z, z ≠ 0 →
      |Gp z| ≤ A * invSqKer z)
    (hJ : ∀ z, z ≠ 0 →
      |J z| ≤ B * (invSqKer z + 1))
    (hgreen : ∀ z, z ≠ 0 →
      |greenFn z| ≤ Cgreen * invSqKer z)
    (hx : x ≠ 0) :
    Integrable (r322CollapseIntegrand Gp J greenFn x)
      (paperMeasure.prod paperMeasure) := by
  let M : T4 × T4 → ℝ := fun p =>
    (A * B * Cgreen) *
      (invSqKer (x - p.1) * invSqKer (p.1 - p.2) *
          invSqKer p.2 +
        invSqKer (x - p.1) * invSqKer p.2 +
        (invSqKer (x - p.1) * invSqKer p.1) *
          invSqKer (p.1 - p.2) +
        invSqKer (x - p.1) * invSqKer p.1)
  have hMint : Integrable M
      (paperMeasure.prod paperMeasure) :=
    (integrable_invSqCollapseMajorant hx).const_mul
      (A * B * Cgreen)
  have hmeas :
      AEStronglyMeasurable
        (r322CollapseIntegrand Gp J greenFn x)
        (paperMeasure.prod paperMeasure) := by
    exact
      (((hGpMeas.comp
          (measurable_const.sub measurable_fst)).mul
        (hJMeas.comp
          (measurable_fst.sub measurable_snd))).mul
        ((measurable_greenFn.comp measurable_snd).sub
          (measurable_greenFn.comp measurable_fst)))
        |>.aestronglyMeasurable
  refine Integrable.mono' hMint hmeas ?_
  filter_upwards
      [ae_fst_ne_paperMeasure x,
        ae_fst_ne_paperMeasure 0,
        ae_snd_ne_paperMeasure 0,
        ae_fst_ne_snd_paperMeasure]
      with p hpx hpz hpw hpzw
  have hxz : x - p.1 ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hpx)
  have hzw : p.1 - p.2 ≠ 0 :=
    sub_ne_zero.mpr hpzw
  have hGp' := hGp (x - p.1) hxz
  have hJ' := hJ (p.1 - p.2) hzw
  have hGw := hgreen p.2 hpw
  have hGz := hgreen p.1 hpz
  have hdiff :
      |greenFn p.2 - greenFn p.1| ≤
        Cgreen * invSqKer p.2 +
          Cgreen * invSqKer p.1 :=
    (abs_sub _ _).trans (add_le_add hGw hGz)
  have hleft : 0 ≤ A * invSqKer (x - p.1) :=
    mul_nonneg hA (invSqKer_nonneg _)
  have hmiddle : 0 ≤ B *
      (invSqKer (p.1 - p.2) + 1) :=
    mul_nonneg hB (add_nonneg (invSqKer_nonneg _) zero_le_one)
  have hright : 0 ≤ Cgreen * invSqKer p.2 +
      Cgreen * invSqKer p.1 :=
    add_nonneg
      (mul_nonneg hCgreen (invSqKer_nonneg _))
      (mul_nonneg hCgreen (invSqKer_nonneg _))
  rw [Real.norm_eq_abs]
  unfold r322CollapseIntegrand
  rw [abs_mul, abs_mul]
  calc
    |Gp (x - p.1)| * |J (p.1 - p.2)| *
          |greenFn p.2 - greenFn p.1| ≤
        (A * invSqKer (x - p.1)) *
          (B * (invSqKer (p.1 - p.2) + 1)) *
          (Cgreen * invSqKer p.2 +
            Cgreen * invSqKer p.1) :=
      mul_le_mul
        (mul_le_mul hGp' hJ' (abs_nonneg _) hleft)
        hdiff (abs_nonneg _) (mul_nonneg hleft hmiddle)
    _ = M p := by
      dsimp only [M]
      ring

/-- At a fixed positive mollification scale, the Proposition 4.1 majorant
is bounded by one nonnegative constant times `invSqKer + 1`.  The constant
may depend on the scale; only raw integrability is asserted here. -/
theorem exists_primitiveKernelMajorant_le_invSq_add_one
    (C lam ε supportConstant : ℝ) (n : ℕ)
    (hε : 0 < ε) (hlog : 0 < |Real.log ε|) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : T4,
      primitiveKernelMajorant C lam ε supportConstant n z ≤
        B * (invSqKer z + 1) := by
  let P : ℝ := (C * lam) ^ (2 * n)
  let a : ℝ := ε⁻¹ ^ (4 : ℕ) / |Real.log ε|
  let b : ℝ :=
    (1 / |Real.log ε| ^ 2) * (ε ^ 2)⁻¹ ^ (3 : ℕ)
  let B : ℝ := P * (a + b)
  have hP : 0 ≤ P := by
    dsimp only [P]
    exact (even_two_mul n).pow_nonneg (C * lam)
  have ha : 0 ≤ a := by
    dsimp only [a]
    exact div_nonneg (by positivity) hlog.le
  have hb : 0 ≤ b := by
    dsimp only [b]
    exact mul_nonneg
      (div_nonneg zero_le_one (sq_nonneg _))
      (pow_nonneg (inv_nonneg.mpr (sq_nonneg ε)) 3)
  have hB : 0 ≤ B :=
    mul_nonneg hP (add_nonneg ha hb)
  refine ⟨B, hB, ?_⟩
  intro z
  have hindicator :
      primitiveSupportIndicator supportConstant ε z ≤ 1 := by
    unfold primitiveSupportIndicator
    split_ifs <;> norm_num
  have hinv :
      (torusDistSq z + ε ^ 2)⁻¹ ≤ (ε ^ 2)⁻¹ := by
    exact inv_anti₀ (sq_pos_of_pos hε)
      (le_add_of_nonneg_left (torusDistSq_nonneg z))
  have hreg :
      (torusDistSq z + ε ^ 2)⁻¹ ^ (3 : ℕ) ≤
        (ε ^ 2)⁻¹ ^ (3 : ℕ) := by
    exact pow_le_pow_left₀
      (inv_nonneg.mpr
        (add_nonneg (torusDistSq_nonneg z) (sq_nonneg ε)))
      hinv 3
  have hlocal :
      a * invSqKer z *
          primitiveSupportIndicator supportConstant ε z ≤
        a * invSqKer z := by
    calc
      a * invSqKer z *
            primitiveSupportIndicator supportConstant ε z ≤
          a * invSqKer z * 1 :=
        mul_le_mul_of_nonneg_left hindicator
          (mul_nonneg ha (invSqKer_nonneg z))
      _ = a * invSqKer z := by ring
  have hregular :
      (1 / |Real.log ε| ^ 2) *
          (torusDistSq z + ε ^ 2)⁻¹ ^ (3 : ℕ) ≤ b := by
    dsimp only [b]
    exact mul_le_mul_of_nonneg_left hreg
      (div_nonneg zero_le_one (sq_nonneg _))
  unfold primitiveKernelMajorant
  change
    P *
        (a * invSqKer z *
            primitiveSupportIndicator supportConstant ε z +
          (1 / |Real.log ε| ^ 2) *
            (torusDistSq z + ε ^ 2)⁻¹ ^ (3 : ℕ)) ≤
      B * (invSqKer z + 1)
  calc
    P *
        (a * invSqKer z *
            primitiveSupportIndicator supportConstant ε z +
          (1 / |Real.log ε| ^ 2) *
            (torusDistSq z + ε ^ 2)⁻¹ ^ (3 : ℕ)) ≤
        P * (a * invSqKer z + b) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hlocal hregular) hP
    _ ≤ P * ((a + b) * (invSqKer z + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hP
      nlinarith [mul_nonneg hb (invSqKer_nonneg z)]
    _ = B * (invSqKer z + 1) := by
      dsimp only [B]
      ring

/-- Reachability, the current edge certificate, and the Proposition 4.1
primitive bound prove raw collapse integrability at every nonzero endpoint.
No a.e.-section theorem is used. -/
theorem
    R322AnalyticAbsorbedState.integrable_stepCollapseIntegrand_offDiagonal
    {ρ : SmoothCutoff} {C lam ε supportConstant : ℝ}
    {q : ℕ} {hq : 1 ≤ q}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    {scale : Fin (2 * q - 1) → ℝ}
    (ctx : R322AnalyticProperStepContext q hq)
    (hstate :
      R322AnalyticAbsorbedState
        ρ lam ε hq κ hκ ctx.state)
    (hcert : R322AnalyticEdgeCertificate ctx.state scale)
    (hε : 0 < ε) (hlog : 0 < |Real.log ε|)
    (hprop : ∀ H, IsAdmissiblePrimitiveInput
        (residualBlockOrder ctx.step.2) H →
      MemEClassT4 (primitiveKernelDiff ρ lam ε
        (residualBlockOrder ctx.step.2) ctx.one_le_blockOrder H) ∧
      MemEClassT4 (primitiveKernelInsertedDiff ρ lam ε
        (residualBlockOrder ctx.step.2) ctx.one_le_blockOrder H) ∧
      PrimitiveKernelBounds ρ lam ε (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder H supportConstant C)
    (x : T4) (hx : x ≠ 0) :
    Integrable (r322CollapseIntegrand
      (ctx.state.edges ctx.predecessorEdge)
      (primitiveKernelDiff ρ lam ε
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder ctx.internalEdges)
      greenFn x)
      (paperMeasure.prod paperMeasure) := by
  let J : T4 → ℝ :=
    primitiveKernelDiff ρ lam ε
      (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges
  let Jscale : ℝ :=
    r322AnalyticInternalEdgeScaleProduct ctx scale
  obtain ⟨B, hB, hmajor⟩ :=
    exists_primitiveKernelMajorant_le_invSq_add_one
      C lam ε supportConstant
      (residualBlockOrder ctx.step.2) hε hlog
  obtain ⟨Cgreen, hCgreen, hgreen⟩ := greenFn_le
  have hJscale : 0 ≤ Jscale := by
    exact (hcert.internalEdgeScaleProduct_pos
      (ctx := ctx)).le
  have hJMeas : Measurable J := by
    exact hstate.measurable_stepPrimitiveKernel ctx
  have hJbound :
      ∀ z, z ≠ 0 →
        |J z| ≤ (Jscale * B) * (invSqKer z + 1) := by
    intro z hz
    have hraw :
        |J z| ≤ Jscale *
          primitiveKernelMajorant C lam ε supportConstant
            (residualBlockOrder ctx.step.2) z := by
      dsimp only [J, Jscale]
      simpa [r322AnalyticInternalEdgeScaleProduct,
        R322AnalyticProperStepContext.internalEdges] using
        primitiveKernelDiff_le_prod_edgeScales_mul_majorant_offDiagonal
          ρ ctx.one_le_blockOrder ctx.internalEdges
          (fun j => scale (ctx.internalEdge j))
          (fun j => hcert.scale_pos (ctx.internalEdge j))
          (fun j => hcert.memE (ctx.internalEdge j))
          (fun j => hcert.bound (ctx.internalEdge j))
          hprop z hz
    calc
      |J z| ≤ Jscale *
          primitiveKernelMajorant C lam ε supportConstant
            (residualBlockOrder ctx.step.2) z := hraw
      _ ≤ Jscale * (B * (invSqKer z + 1)) :=
        mul_le_mul_of_nonneg_left (hmajor z) hJscale
      _ = (Jscale * B) * (invSqKer z + 1) := by ring
  exact integrable_r322CollapseIntegrand_of_invSq_add_one
    (hstate.measurable_edges ctx.predecessorEdge)
    hJMeas
    (hcert.scale_pos ctx.predecessorEdge).le
    (mul_nonneg hJscale hB)
    hCgreen.le
    (hcert.bound ctx.predecessorEdge)
    hJbound
    (fun z hz => greenFn_abs_le_mul_invSqKer hgreen z hz)
    hx

/-- Production constructor for the actual primitive certificate, with its
raw integrability field discharged from reachability and Proposition 4.1. -/
theorem
    R322AnalyticEdgeCertificate.primitiveCertificate_of_reachable
    {ρ : SmoothCutoff} {C lam ε supportConstant : ℝ}
    {q : ℕ} {hq : 1 ≤ q}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    {ctx : R322AnalyticProperStepContext q hq}
    {scale : Fin (2 * q - 1) → ℝ}
    (hstate :
      R322AnalyticAbsorbedState
        ρ lam ε hq κ hκ ctx.state)
    (hcert : R322AnalyticEdgeCertificate ctx.state scale)
    (hε : 0 < ε) (hlog : 0 < |Real.log ε|)
    (hprop : ∀ H, IsAdmissiblePrimitiveInput
        (residualBlockOrder ctx.step.2) H →
      MemEClassT4 (primitiveKernelDiff ρ lam ε
        (residualBlockOrder ctx.step.2) ctx.one_le_blockOrder H) ∧
      MemEClassT4 (primitiveKernelInsertedDiff ρ lam ε
        (residualBlockOrder ctx.step.2) ctx.one_le_blockOrder H) ∧
      PrimitiveKernelBounds ρ lam ε (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder H supportConstant C) :
    R322AnalyticPrimitiveCertificate
      ctx scale ρ C lam ε supportConstant := by
  apply hcert.primitiveCertificate ρ C lam ε supportConstant
    (hstate.measurable_stepPrimitiveKernel ctx) hprop
  intro x hx
  exact hstate.integrable_stepCollapseIntegrand_offDiagonal
    ctx hcert hε hlog hprop x hx

end

end Anderson4D
