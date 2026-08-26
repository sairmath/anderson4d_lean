import Anderson4D.DetParametrix.Paper42_Moment.R324PrimitiveIterationClosure
import Anderson4D.DetParametrix.Paper41_Renorm.R322OneBlockCollapse
import Anderson4D.DetParametrix.Core.MeasurableAssembly

/-!
# Successive integrated primitive collapses for R-324

This file constructs the analytic stages used by the corrected integrated
R-324 reduction.  A stage is the actual primitive kernel for a measurable
admissible chain-input family; its measurability, class-`E` property, and
Proposition 4.1 majorant are derived rather than postulated.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Measurability of genuine primitive kernels -/

/-- The Proposition 4.1 integrand is jointly measurable in its complete
tuple whenever every chain input is measurable. -/
theorem measurable_primitiveIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, Measurable (G j))
    (κ : PartialPairing (Fin (2 * n))) :
    Measurable (primitiveIntegrand ρ ε n hn G κ) := by
  unfold primitiveIntegrand
    primitiveChainProduct
    primitiveCovarianceProduct
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro j _hj
    exact
      (hG j).comp
        ((measurable_pi_apply
          (primitiveEdgeLeft n hn j)).sub
        (measurable_pi_apply
          (primitiveEdgeRight n hn j)))
  · apply Finset.measurable_prod
    intro i _hi
    exact
      (ρ.measurable_etaEpsT4 ε).comp
        ((measurable_pi_apply i).sub
          (measurable_pi_apply (κ i)))

/-- Joint measurability after assembling one free endpoint, one zero
endpoint, and the internal primitive tuple. -/
theorem measurable_primitiveIntegrand_assemble_zero
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, Measurable (G j))
    (κ : PartialPairing (Fin (2 * n))) :
    Measurable fun p :
        T4 × (Fin (2 * n - 2) → T4) =>
      primitiveIntegrand ρ ε n hn G κ
        (primitiveAssemble n hn p.1 0 p.2) := by
  have hassemble :
      Measurable fun p :
          T4 × (Fin (2 * n - 2) → T4) =>
        primitiveAssemble n hn p.1 0 p.2 := by
    have hraw :
        Measurable fun p :
            T4 × (Fin (2 * n - 2) → T4) =>
          assemble p.1 0 p.2 :=
      (measurable_assemble_prod (2 * n - 2)).comp
        (measurable_fst.prodMk
          (measurable_const.prodMk measurable_snd))
    apply measurable_pi_lambda
    intro j
    exact
      (measurable_pi_apply
        (Fin.cast (by omega : 2 * n = (2 * n - 2) + 2) j)).comp
        hraw
  exact
    (measurable_primitiveIntegrand
      ρ ε n hn G hG κ).comp hassemble

/-- The genuine primitive kernel supplied to a later collapse is
measurable.  This closes a condition not included in the bare
`IsAdmissiblePrimitiveInput` predicate. -/
theorem measurable_primitiveKernelDiff
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, Measurable (G j)) :
    Measurable
      (primitiveKernelDiff ρ lam ε n hn G) := by
  unfold primitiveKernelDiff primitiveKernel
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro κ _hκ
  have hjoint :=
    measurable_primitiveIntegrand_assemble_zero
      ρ ε n hn G hG κ
  exact
    hjoint.stronglyMeasurable
      |>.integral_prod_right.measurable

/-! ## Proposition 4.1 produces actual analytic stages -/

/-- One genuine primitive kernel, with all `R322AnalyticStage` fields
derived from Proposition 4.1. -/
def r324PrimitiveAnalyticStage
    (ρ : SmoothCutoff)
    (lam ε C supportConstant : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j))
    (hreg :
      PrimitiveEstimateRegime
        n lam ε 1 supportConstant C)
    (hinput : IsAdmissiblePrimitiveInput n G)
    (hprop :
      Prop41BoundPredicate ρ lam ε n hn G
        1 supportConstant C) :
    R322AnalyticStage C lam ε supportConstant where
  order := n
  order_pos := hn
  kernel := primitiveKernelDiff ρ lam ε n hn G
  measurable_kernel :=
    measurable_primitiveKernelDiff
      ρ lam ε n hn G hGmeas
  memE_kernel :=
    (hprop hreg hinput).1
  kernel_le := fun u =>
    ((hprop hreg hinput).2.2 u).1

/-- The proved truncation-specialized Proposition 4.1 constructs the stage
for any concrete measurable admissible input family. -/
theorem exists_r324PrimitiveAnalyticStage_at_truncation
    (ρ : SmoothCutoff) :
    ∃ supportConstant C : ℝ,
      0 < supportConstant ∧ 0 < C ∧
      ∀ (lam ε : ℝ) (n : ℕ) (_hn : 1 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        0 < lam → 0 < ε → ε ≤ 1 →
        n ≤ truncOrder ε →
        (∀ j, Measurable (G j)) →
        IsAdmissiblePrimitiveInput n G →
          Nonempty
            (R322AnalyticStage
              C lam ε supportConstant) := by
  obtain ⟨supportConstant, C,
      hsupport, hC, hprop⟩ :=
    proposition41_at_truncation ρ
  refine
    ⟨supportConstant, C, hsupport, hC, ?_⟩
  intro lam ε n hn G hlam hε hε1
    hntrunc hGmeas hinput
  have hreg :
      PrimitiveEstimateRegime
        n lam ε 1 supportConstant C :=
    primitiveEstimateRegime_of_le_truncOrder
      hn hε hε1 hlam hsupport hC hntrunc
  exact
    ⟨r324PrimitiveAnalyticStage
      ρ lam ε C supportConstant n hn G
      hGmeas hreg hinput
      (fun _hreg _hinput =>
        hprop lam ε n hn G hlam hε hε1
          hntrunc hinput)⟩

end

end Anderson4D
