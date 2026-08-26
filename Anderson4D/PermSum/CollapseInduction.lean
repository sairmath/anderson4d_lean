import Anderson4D.PermSum.CollapseBase

/-!
# Strong-induction shell for Proposition 5.9

This module separates the well-founded recursion from the analytic collapse
estimate.  The no-eligible branch is already closed by Proposition 5.10; the
its local input is a step at a chosen lowest eligible branch.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree

noncomputable section

/-- The quantified conclusion of Proposition 5.9 for one fixed tree. -/
def InductiveConclusion (C0 D : ℝ) (t : PlaneTree) : Prop :=
  ∀ (m : ℕ) (Nm : HeppMarking t)
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (z : HeppLeaf t → Fin 4 → ℤ),
    t.isValid = true →
    rootV t ∈ BranchNodes t →
    compound ⊆ Leaves t →
    totalMultiplicity mu = m →
    IsSeparatedEmbedding Nm z →
    SatisfiesSubtreeDiameter Nm mu z →
    paperSum (M := m) (leafMultiplicity mu)
        (primitiveSeparatedChainWeight z) ≤
      inductiveRHS C0 D m t Nm mu compound

/-- The sole recursive input left after the no-eligible case: assuming the
Proposition 5.9 conclusion for every smaller tree, prove it by collapsing a
chosen lowest eligible branch. -/
def EligibleCollapseStep (C0 D : ℝ) : Prop :=
  ∀ (t : PlaneTree),
    (∀ u : PlaneTree, u.size < t.size →
      InductiveConclusion C0 D u) →
    ∀ (m : ℕ) (Nm : HeppMarking t)
      (mu : Multiplicities t) (compound : Finset (VPos t))
      (z : HeppLeaf t → Fin 4 → ℤ),
      t.isValid = true →
      rootV t ∈ BranchNodes t →
      compound ⊆ Leaves t →
      totalMultiplicity mu = m →
      IsSeparatedEmbedding Nm z →
      SatisfiesSubtreeDiameter Nm mu z →
      ∀ r : VPos t, IsLowestCollapseEligible Nm mu r →
      paperSum (M := m) (leafMultiplicity mu)
          (primitiveSeparatedChainWeight z) ≤
        inductiveRHS C0 D m t Nm mu compound

/-- Strong induction closes the full statement once the eligible collapse
step is supplied. -/
theorem inductiveEstimate_of_singleScale_of_eligibleStep
    {C0 D : ℝ} (hsingle : SingleScaleEstimate C0)
    (hD : D = Real.exp (C0 ^ (10 : ℕ)))
    (hstep : EligibleCollapseStep C0 D) :
    InductiveEstimate C0 D := by
  refine ⟨hsingle.1, hD, ?_⟩
  have hAllSize :
      ∀ k : ℕ, ∀ t : PlaneTree, t.size = k →
        InductiveConclusion C0 D t := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t htSize m Nm mu compound z
        ht hroot hcompound htotal hsep hdiam
      by_cases hempty : eligibleBranches Nm mu = ∅
      · exact noEligible_case_of_singleScale
          hsingle hD m t Nm mu compound z ht hroot hcompound
          htotal hsep hempty
      · have hnonempty :
            (eligibleBranches Nm mu).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hempty
        obtain ⟨r, hr⟩ :=
          exists_lowestCollapseEligible Nm mu hnonempty
        exact hstep t
          (fun u hu =>
            ih u.size (by simpa [htSize] using hu) u rfl)
          m Nm mu compound z ht hroot hcompound htotal hsep hdiam r hr
  intro m t Nm mu compound z ht hroot hcompound htotal hsep hdiam
  exact hAllSize t.size t rfl
    m Nm mu compound z ht hroot hcompound htotal hsep hdiam

end

end Anderson4D
