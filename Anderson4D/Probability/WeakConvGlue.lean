import Anderson4D.ForMathlib.GoodEventConvergence
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Filter-indexed weak-convergence glue

Mathlib's reverse Lévy theorem is sequence-indexed, but the implication
needed after a weak-convergence proof is valid over every filter:
convergence in distribution gives pointwise convergence of
characteristic functions.  This file exposes that implication both in
law form and as integrals over the original probability spaces.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter MeasureTheory
open scoped InnerProductSpace Topology

variable {ι Ω' E : Type*} {Ω : ι → Type*}
  [∀ i, MeasurableSpace (Ω i)]
  (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
  [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ']
  [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] in
/-- Weak convergence implies convergence of every bounded continuous
complex test integral, over an arbitrary index filter. -/
theorem TendstoInDistribution.tendsto_boundedContinuous_integral
    {l : Filter ι} {X : (i : ι) → Ω i → E} {Z : Ω' → E}
    (h : TendstoInDistribution X l Z μ μ')
    (f : BoundedContinuousFunction E ℂ) :
    Tendsto
      (fun i ↦ ∫ x, f x ∂(μ i).map (X i)) l
      (𝓝 (∫ x, f x ∂μ'.map Z)) := by
  have hf :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1
      h.tendsto f
  simpa only [ProbabilityMeasure.coe_mk] using hf

/-- Filter-indexed forward Lévy implication for convergence in
distribution. -/
theorem TendstoInDistribution.tendsto_charFun
    {l : Filter ι} {X : (i : ι) → Ω i → E} {Z : Ω' → E}
    (h : TendstoInDistribution X l Z μ μ') (t : E) :
    Tendsto
      (fun i ↦ charFun ((μ i).map (X i)) t) l
      (𝓝 (charFun (μ'.map Z) t)) := by
  simpa only [charFun_eq_integral_innerProbChar] using
    Anderson4D.TendstoInDistribution.tendsto_boundedContinuous_integral
      μ μ' h
      (BoundedContinuousFunction.innerProbChar t)

/-- The same characteristic-function convergence, rewritten as
expectations on the original probability spaces. -/
theorem TendstoInDistribution.tendsto_charFun_integral
    {l : Filter ι} {X : (i : ι) → Ω i → E} {Z : Ω' → E}
    (h : TendstoInDistribution X l Z μ μ') (t : E) :
    Tendsto
      (fun i ↦ ∫ ω, Complex.exp (⟪X i ω, t⟫_ℝ * Complex.I) ∂μ i) l
      (𝓝 (∫ ω, Complex.exp (⟪Z ω, t⟫_ℝ * Complex.I) ∂μ')) := by
  have hchar :=
    Anderson4D.TendstoInDistribution.tendsto_charFun μ μ' h t
  have hsource (i : ι) :
      charFun ((μ i).map (X i)) t =
        ∫ ω, Complex.exp (⟪X i ω, t⟫_ℝ * Complex.I) ∂μ i := by
    rw [charFun_eq_integral_innerProbChar,
      integral_map (h.forall_aemeasurable i)
        (BoundedContinuousFunction.innerProbChar t).continuous.aestronglyMeasurable]
    rfl
  have hlimit :
      charFun (μ'.map Z) t =
        ∫ ω, Complex.exp (⟪Z ω, t⟫_ℝ * Complex.I) ∂μ' := by
    rw [charFun_eq_integral_innerProbChar,
      integral_map h.aemeasurable_limit
        (BoundedContinuousFunction.innerProbChar t).continuous.aestronglyMeasurable]
    rfl
  simpa only [hsource, hlimit] using hchar

/-- Scalar specialization at frequency one, in the exact exponential
shape used by paper (3.34). -/
theorem TendstoInDistribution.tendsto_real_exp_integral
    {l : Filter ι} {X : (i : ι) → Ω i → ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution X l Z μ μ') :
    Tendsto
      (fun i ↦ ∫ ω, Complex.exp (Complex.I * (X i ω : ℂ)) ∂μ i) l
      (𝓝 (∫ ω, Complex.exp (Complex.I * (Z ω : ℂ)) ∂μ')) := by
  have hchar :=
    Anderson4D.TendstoInDistribution.tendsto_charFun_integral
      μ μ' h (1 : ℝ)
  simpa [real_inner_comm, mul_comm] using hchar

end

end Anderson4D
