import Anderson4D.PermSum.SingleScaleAnchorChoice
import Anderson4D.PermSum.SingleScaleWeightBridge

/-!
# Statement-boundary reduction to fixed class-word kernel sums

This file combines the exact finite Fubini decomposition with the
pointwise kernel comparison.  It is the first genuinely weighted bridge
from the frozen left side of Proposition 5.10 to the fixed `(P,NX)` fibers
used by the outer and inner arguments.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

theorem arrangementNXWord_class_eq
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (σ : HeppArrangement mu) (hσ : σ ∈ arrangementsAtNXWord Nm mu x)
    (i : Fin (totalMultiplicity mu)) :
    singleScaleSigma1 Nm mu
        (inducedWord (leafMultiplicity mu) σ i) =
      (x i).1 := by
  have hword := congrFun
    ((mem_arrangementsAtNXWord_iff Nm mu x σ).mp hσ) i
  exact congrArg Subtype.val hword

/--
For any choice of strong-edge schedule depending on the fixed `(N,X)`
word, the full paper sum is bounded by the corresponding finite Fubini sum
of kernel products.  The skipped-edge factor `R^(2|O|)` is explicit in
every arrangement summand.
-/
theorem paperSum_singleScaleChainWeight_le_kernelFubini
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℕ) (hR : 0 < R)
    (O : Finset (AdjacentIndex (totalMultiplicity mu)))
    (strongEdges :
      (Fin (totalMultiplicity mu) → ActiveNXClass Nm mu) →
        Finset (AdjacentIndex (totalMultiplicity mu))) :
    paperSum (M := totalMultiplicity mu) (leafMultiplicity mu)
        (singleScaleChainWeight
          (m := totalMultiplicity mu) z O) ≤
      ∑ y ∈ validWords (M := totalMultiplicity mu)
          (activePMultiplicity Nm mu),
        ∑ x ∈ validRefinements
            (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
          ∑ σ ∈ arrangementsAtNXWord Nm mu x,
            (R : ℝ) ^ (2 * O.card) *
              ∏ j : AdjacentIndex (totalMultiplicity mu),
                nxClassEdgeKernel ht hroot Nm mu z hz
                  (R : ℝ) O (strongEdges x) x
                  (inducedWord (leafMultiplicity mu) σ) j := by
  rw [paperSum_eq_sum_PWords_NXWords_arrangements]
  apply Finset.sum_le_sum
  intro y _hy
  apply Finset.sum_le_sum
  intro x _hx
  apply Finset.sum_le_sum
  intro σ hσ
  unfold singleScaleChainWeight
  by_cases hno :
      NoAdjacentOutside O (inducedWord (leafMultiplicity mu) σ)
  · rw [if_pos hno]
    exact heppChainWeightExcept_le_nxClassEdgeKernelProduct
      ht hroot Nm mu z hz (R : ℝ)
      (by exact_mod_cast hR.ne') O (strongEdges x) x
      (inducedWord (leafMultiplicity mu) σ)
      (arrangementNXWord_class_eq Nm mu x σ hσ) hno
  · rw [if_neg hno]
    exact mul_nonneg (by positivity)
      (Finset.prod_nonneg fun j _ =>
        nxClassEdgeKernel_nonneg ht hroot Nm mu z hz
          (R : ℝ) O (strongEdges x) x
          (inducedWord (leafMultiplicity mu) σ) j)

end XYCluster

end

end Anderson4D
