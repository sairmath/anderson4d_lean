import Anderson4D.PermSum.SingleScaleFiberKernelAlignment
import Anderson4D.PermSum.SingleScaleStatementReduction

/-!
# Statement summands on a fixed `(N,X)` fiber

This file connects the frozen single-scale summand to the canonical
anchor/phase edge kernel.  It is deliberately upstream of the analytic
finite-Fubini estimate: the only input here is the pointwise
statement-kernel comparison.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/-- Every canonical anchor/phase edge kernel is nonnegative. -/
theorem finAnchorNXArrangementEdgeKernel_nonneg
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (O : Finset (AdjacentIndex m))
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (x : Fin m → ActiveNXClass Nm mu)
    (σ : Fin m → HeppLabeledCopy mu)
    (edge : AdjacentIndex m) :
    0 ≤ finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
      R O leftPhase rightPhase anchor x σ edge := by
  exact
    nxClassEdgeKernel_nonneg ht hroot Nm mu z hz R O
      (finAnchorNXKernelStrongEdges leftPhase rightPhase anchor)
      x (fun i => (σ i).1) edge

/-- The product used by either canonical phase choice is nonnegative. -/
theorem finAnchorNXArrangementEdgeKernelProduct_nonneg
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (O : Finset (AdjacentIndex m))
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (x : Fin m → ActiveNXClass Nm mu)
    (σ : Fin m → HeppLabeledCopy mu) :
    0 ≤ ∏ edge : AdjacentIndex m,
      finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
        R O leftPhase rightPhase anchor x σ edge := by
  exact Finset.prod_nonneg fun edge _ =>
    finAnchorNXArrangementEdgeKernel_nonneg
      ht hroot Nm mu z hz R O leftPhase rightPhase
      anchor x σ edge

/-- The whole canonical edge-kernel fiber sum is nonnegative. -/
theorem sum_arrangementsAtNXWord_finAnchorNXEdgeKernel_nonneg
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ)
    (O : Finset (AdjacentIndex (totalMultiplicity mu)))
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu) :
    0 ≤ ∑ σ ∈ arrangementsAtNXWord Nm mu x,
      ∏ edge : AdjacentIndex (totalMultiplicity mu),
        finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
          R O leftPhase rightPhase anchor x σ edge := by
  exact Finset.sum_nonneg fun σ _ =>
    finAnchorNXArrangementEdgeKernelProduct_nonneg
      ht hroot Nm mu z hz R O leftPhase rightPhase
      anchor x σ

/--
Pointwise frozen-summand comparison for two independently selectable
canonical phases.
-/
theorem singleScaleChainWeight_induced_le_finAnchorNXEdgeKernelProduct
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (hR : R ≠ 0)
    (O : Finset (AdjacentIndex (totalMultiplicity mu)))
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (σ : HeppArrangement mu)
    (hσ : σ ∈ arrangementsAtNXWord Nm mu x) :
    singleScaleChainWeight z O
        (inducedWord (leafMultiplicity mu) σ) ≤
      R ^ (2 * O.card) *
        ∏ edge : AdjacentIndex (totalMultiplicity mu),
          finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
            R O leftPhase rightPhase anchor x σ edge := by
  unfold singleScaleChainWeight
  by_cases hno :
      NoAdjacentOutside O
        (inducedWord (leafMultiplicity mu) σ)
  · rw [if_pos hno]
    change
      heppChainWeightExcept z O
          (inducedWord (leafMultiplicity mu) σ) ≤
        R ^ (2 * O.card) *
          ∏ edge : AdjacentIndex (totalMultiplicity mu),
            nxClassEdgeKernel ht hroot Nm mu z hz R O
              (finAnchorNXKernelStrongEdges
                leftPhase rightPhase anchor)
              x (inducedWord (leafMultiplicity mu) σ) edge
    exact
      heppChainWeightExcept_le_nxClassEdgeKernelProduct
        ht hroot Nm mu z hz R hR O
        (finAnchorNXKernelStrongEdges
          leftPhase rightPhase anchor)
        x (inducedWord (leafMultiplicity mu) σ)
        (arrangementNXWord_class_eq Nm mu x σ hσ) hno
  · rw [if_neg hno]
    have hpow : 0 ≤ R ^ (2 * O.card) := by
      rw [show 2 * O.card = O.card * 2 by omega,
        pow_mul]
      exact sq_nonneg (R ^ O.card)
    exact mul_nonneg hpow
      (finAnchorNXArrangementEdgeKernelProduct_nonneg
        ht hroot Nm mu z hz R O leftPhase rightPhase
        anchor x σ)

/--
Fixed `(N,X)`-word fiber bridge, generalized to independent phases on the
left and right runs.  No validity hypothesis on `x` is needed for this
stronger local statement.
-/
theorem
    sum_arrangementsAtNXWord_singleScaleChainWeight_le_edgeKernelWithPhases
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (hR : R ≠ 0)
    (O : Finset (AdjacentIndex (totalMultiplicity mu)))
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu) :
    (∑ σ ∈ arrangementsAtNXWord Nm mu x,
        singleScaleChainWeight z O
          (inducedWord (leafMultiplicity mu) σ)) ≤
      R ^ (2 * O.card) *
        ∑ σ ∈ arrangementsAtNXWord Nm mu x,
          ∏ edge : AdjacentIndex (totalMultiplicity mu),
            finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
              R O leftPhase rightPhase anchor x σ edge := by
  calc
    (∑ σ ∈ arrangementsAtNXWord Nm mu x,
        singleScaleChainWeight z O
          (inducedWord (leafMultiplicity mu) σ)) ≤
      ∑ σ ∈ arrangementsAtNXWord Nm mu x,
        R ^ (2 * O.card) *
          ∏ edge : AdjacentIndex (totalMultiplicity mu),
            finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
              R O leftPhase rightPhase anchor x σ edge := by
      apply Finset.sum_le_sum
      intro σ hσ
      exact
        singleScaleChainWeight_induced_le_finAnchorNXEdgeKernelProduct
          ht hroot Nm mu z hz R hR O leftPhase rightPhase
          anchor x σ hσ
    _ = R ^ (2 * O.card) *
        ∑ σ ∈ arrangementsAtNXWord Nm mu x,
          ∏ edge : AdjacentIndex (totalMultiplicity mu),
            finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
              R O leftPhase rightPhase anchor x σ edge := by
      rw [Finset.mul_sum]

/--
Frozen-data specialization: the scale is a positive natural number, the
class word is valid, and both outward runs use the same phase.
-/
theorem
    sum_arrangementsAtNXWord_singleScaleChainWeight_le_edgeKernel
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℕ) (hR : 0 < R)
    (O : Finset (AdjacentIndex (totalMultiplicity mu)))
    (phase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (_hx : x ∈ validWords (M := totalMultiplicity mu)
      (activeNXMultiplicity Nm mu)) :
    (∑ σ ∈ arrangementsAtNXWord Nm mu x,
        singleScaleChainWeight z O
          (inducedWord (leafMultiplicity mu) σ)) ≤
      (R : ℝ) ^ (2 * O.card) *
        ∑ σ ∈ arrangementsAtNXWord Nm mu x,
          ∏ edge : AdjacentIndex (totalMultiplicity mu),
            finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
              (R : ℝ) O phase phase anchor x σ edge := by
  exact
    sum_arrangementsAtNXWord_singleScaleChainWeight_le_edgeKernelWithPhases
      ht hroot Nm mu z hz (R : ℝ)
      (by exact_mod_cast hR.ne') O phase phase anchor x

end XYCluster

end

end Anderson4D
