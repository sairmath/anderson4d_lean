import Anderson4D.HeppTree.ClusterDiameter
import Anderson4D.PermSum.Statements

/-!
# Admissibility implies the Proposition 5.9 diameter hypothesis

Paper §5.4 invokes the cluster-diameter estimate from Proposition 5.6 before
applying Proposition 5.9.  The geometric estimate uses the child-count scale
`tildeScale`; the latter is bounded termwise by `accumulatedScale` because
`gammaInf` counts every child and possibly additional leaf multiplicities.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- The multiplicity-weighted accumulated scale dominates the purely
tree-geometric cluster scale. -/
theorem tildeScale_le_accumulatedScale
    {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (v : VPos t) :
    tildeScale Nm v ≤ (accumulatedScale Nm mu v : ℝ) := by
  unfold tildeScale accumulatedScale branchDescendants branchNodesUnder
  push_cast
  apply Finset.sum_le_sum
  intro u hu
  have hgamma :
      childCount t u.1 ≤ gammaInf mu u := by
    unfold gammaInf
    rw [← card_childrenOf t u]
    omega
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast hgamma)
    (by positivity)

/-- An admissible leaf embedding satisfies condition (5.32) for every
choice of leaf multiplicities. -/
theorem IsAdmissible.satisfiesSubtreeDiameter
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : HeppLeaf t → Fin 4 → ℤ}
    (hadm : IsAdmissible Nm M z)
    (mu : Multiplicities t) :
    SatisfiesSubtreeDiameter Nm mu z := by
  intro v _hv l hl l' hl'
  exact
    (clusterDiameter_le_tildeScale hadm v hl hl').trans
      (tildeScale_le_accumulatedScale Nm mu v)

end

end Anderson4D
