import Anderson4D.PermSum.SingleScaleSetup
import Anderson4D.PermSum.SingleScaleMixed

/-!
# Orientation identities for single-scale kernels

The anchored elimination order traverses one side of the original word in
reverse.  This file isolates the purely analytic facts which make that change
of orientation harmless.  The stronger two-class cutoff is symmetric, and it
can always be relaxed to the one-class cutoff at either endpoint.
-/

namespace Anderson4D

open PlaneTree

noncomputable section

namespace XYCluster

/-- A one-class kernel is symmetric in its two lattice points. -/
theorem lambda_comm (c : XYCluster) (R : ℝ) (skipped : Bool)
    (x y : Fin 4 → ℤ) :
    c.lambda R skipped x y = c.lambda R skipped y x := by
  simp only [lambda, znorm_sub_comm x y]

/-- The two-class kernel is unchanged when both endpoint data are swapped. -/
theorem strongLambda_comm (a b : XYCluster) (R : ℝ) (skipped : Bool)
    (x y : Fin 4 → ℤ) :
    strongLambda a b R skipped x y =
      strongLambda b a R skipped y x := by
  simp only [strongLambda, max_comm a.N b.N, znorm_sub_comm x y]

/-- Forgetting the right endpoint scale weakens the strong cutoff. -/
theorem strongLambda_le_leftLambda
    (a b : XYCluster) (R : ℝ) (skipped : Bool)
    (x y : Fin 4 → ℤ) :
    strongLambda a b R skipped x y ≤ a.lambda R skipped x y := by
  cases skipped with
  | true =>
      simp [strongLambda, lambda]
  | false =>
      simp only [strongLambda, lambda, Bool.false_eq_true, if_false]
      by_cases hstrong : max a.N b.N ≤ znorm (x - y)
      · have hleft : a.N ≤ znorm (x - y) :=
          (le_max_left a.N b.N).trans hstrong
        simp [hstrong, hleft]
      · rw [if_neg hstrong]
        split_ifs <;> positivity

/-- Forgetting the left endpoint scale weakens the strong cutoff. -/
theorem strongLambda_le_rightLambda
    (a b : XYCluster) (R : ℝ) (skipped : Bool)
    (x y : Fin 4 → ℤ) :
    strongLambda a b R skipped x y ≤ b.lambda R skipped x y := by
  cases skipped with
  | true =>
      simp [strongLambda, lambda]
  | false =>
      simp only [strongLambda, lambda, Bool.false_eq_true, if_false]
      by_cases hstrong : max a.N b.N ≤ znorm (x - y)
      · have hright : b.N ≤ znorm (x - y) :=
          (le_max_right a.N b.N).trans hstrong
        simp [hstrong, hright]
      · rw [if_neg hstrong]
        split_ifs <;> positivity

/-- Right-endpoint relaxation in the reversed point orientation. -/
theorem strongLambda_le_rightLambda_rev
    (a b : XYCluster) (R : ℝ) (skipped : Bool)
    (x y : Fin 4 → ℤ) :
    strongLambda a b R skipped x y ≤ b.lambda R skipped y x := by
  rw [lambda_comm b R skipped y x]
  exact strongLambda_le_rightLambda a b R skipped x y

/-! ## Active `(N,X)` class specializations -/

/-- `strongLambda_comm` specialized to the clusters of two active classes. -/
theorem nxClassStrongLambda_comm
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (a b : ActiveNXClass Nm mu) (R : ℝ) (skipped : Bool)
    (x y : Fin 4 → ℤ) :
    strongLambda
        (nxClassCluster ht hroot Nm mu z hz a.1 a.2)
        (nxClassCluster ht hroot Nm mu z hz b.1 b.2)
        R skipped x y =
      strongLambda
        (nxClassCluster ht hroot Nm mu z hz b.1 b.2)
        (nxClassCluster ht hroot Nm mu z hz a.1 a.2)
        R skipped y x :=
  strongLambda_comm _ _ R skipped x y

/-- Left-class relaxation for two active `(N,X)` classes. -/
theorem nxClassStrongLambda_le_leftLambda
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (a b : ActiveNXClass Nm mu) (R : ℝ) (skipped : Bool)
    (x y : Fin 4 → ℤ) :
    strongLambda
        (nxClassCluster ht hroot Nm mu z hz a.1 a.2)
        (nxClassCluster ht hroot Nm mu z hz b.1 b.2)
        R skipped x y ≤
      (nxClassCluster ht hroot Nm mu z hz a.1 a.2).lambda
        R skipped x y :=
  strongLambda_le_leftLambda _ _ R skipped x y

/-- Right-class relaxation for two active `(N,X)` classes. -/
theorem nxClassStrongLambda_le_rightLambda
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (a b : ActiveNXClass Nm mu) (R : ℝ) (skipped : Bool)
    (x y : Fin 4 → ℤ) :
    strongLambda
        (nxClassCluster ht hroot Nm mu z hz a.1 a.2)
        (nxClassCluster ht hroot Nm mu z hz b.1 b.2)
        R skipped x y ≤
      (nxClassCluster ht hroot Nm mu z hz b.1 b.2).lambda
        R skipped x y :=
  strongLambda_le_rightLambda _ _ R skipped x y

/-- Reversed-point right-class relaxation for active `(N,X)` classes. -/
theorem nxClassStrongLambda_le_rightLambda_rev
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (a b : ActiveNXClass Nm mu) (R : ℝ) (skipped : Bool)
    (x y : Fin 4 → ℤ) :
    strongLambda
        (nxClassCluster ht hroot Nm mu z hz a.1 a.2)
        (nxClassCluster ht hroot Nm mu z hz b.1 b.2)
        R skipped x y ≤
      (nxClassCluster ht hroot Nm mu z hz b.1 b.2).lambda
        R skipped y x :=
  strongLambda_le_rightLambda_rev _ _ R skipped x y

end XYCluster

end

end Anderson4D
