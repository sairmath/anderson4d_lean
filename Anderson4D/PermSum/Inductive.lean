import Anderson4D.PermSum.CollapseActiveShapes
import Anderson4D.PermSum.CollapseFixedShapeBound
import Anderson4D.PermSum.CollapseFixedShapeScalar
import Anderson4D.PermSum.CollapseInduction
import Anderson4D.PermSum.CollapseScaledShapeSum
import Anderson4D.PermSum.CollapseShapeLedger
import Anderson4D.PermSum.SingleScale

/-!
# The inductive permutation-sum estimate

This module closes Proposition 5.9.  At a lowest eligible branch, the raw
word sum is partitioned by active collapse shape.  The valid-word Fubini
bound and the two analytic calls control each shape, while the composition
count is absorbed by the `2^n` factor in the fixed-shape scalar ledger.
Strong induction on tree size then closes the theorem.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- The local eligible-branch step used by the strong-induction shell. -/
theorem eligibleCollapseStep
    {C0 D : ℝ} (hsingle : SingleScaleEstimate C0)
    (hD : D = Real.exp (C0 ^ (10 : ℕ))) :
    EligibleCollapseStep C0 D := by
  intro t hIH m Nm mu compound z
    ht hroot hcompound htotal hsep hdiam r hr
  let lstar : InsideLeaf r :=
    Classical.choice (nonempty_insideLeaf r)
  let B : ℝ :=
    C0 ^ (totalMultiplicity mu) *
      D ^ (BranchNodes t).card *
      ∑ W' ∈ (nonrootBranches t).powerset,
        inductiveRHSSummand (totalMultiplicity mu)
          t Nm mu compound W'
  have hrBranch : r ∈ nonrootBranches t := hr.1.1
  have hsize :
      (contractAt t r.1).size < t.size :=
    contractAt_size_lt_of_branch
      (Finset.mem_erase.mp hrBranch).2
  have hIHcontract :
      InductiveConclusion C0 D (contractAt t r.1) :=
    hIH (contractAt t r.1) hsize
  have hcard :
      (activeCollapseShapes mu r m).card ≤
        2 ^ totalMultiplicity (restrictMultiplicities mu r) := by
    exact le_trans
      (Finset.card_le_card (Finset.filter_subset _ _))
      (card_validCollapseShapes_split_le_two_pow_restrict mu r m)
  have hB : 0 ≤ B := by
    have hC0 : 0 ≤ C0 := by linarith [hsingle.1]
    have hDpos : 0 < D := by
      rw [hD]
      positivity
    have hsum :
        0 ≤
          ∑ W' ∈ (nonrootBranches t).powerset,
            inductiveRHSSummand (totalMultiplicity mu)
              t Nm mu compound W' := by
      exact Finset.sum_nonneg fun W' _ =>
        inductiveRHSSummand_nonneg
          (totalMultiplicity mu) t Nm mu compound W'
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hC0 _) (pow_nonneg hDpos.le _))
      hsum
  have hshapes :
      (∑ shape ∈ activeCollapseShapes mu r m,
          ∑ d ∈
            (specFixedRawCollapseData
              (splitLeafMultiplicity mu r) m).filter
                (fun d => d.1.collapseShape = shape),
            collapseRawFixedWordSummand mu r z lstar d.1) ≤
        B := by
    apply sum_le_of_card_le_two_pow_of_two_pow_mul_le
      (activeCollapseShapes mu r m)
      (fun shape =>
        ∑ d ∈
          (specFixedRawCollapseData
            (splitLeafMultiplicity mu r) m).filter
              (fun d => d.1.collapseShape = shape),
          collapseRawFixedWordSummand mu r z lstar d.1)
      B
      (totalMultiplicity (restrictMultiplicities mu r))
      hcard hB
    intro shape hshape
    have hshapeData :=
      (mem_activeCollapseShapes_iff mu r m shape).mp hshape
    obtain ⟨d₀, hSpec₀, hdshape⟩ :=
      (mem_validCollapseShapes_iff
        (splitLeafMultiplicity mu r) m shape).mp hshapeData.1
    have hblocks : 2 ≤ d₀.1.blocks.length := by
      rw [← d₀.1.collapseShape_length, hdshape]
      exact hshapeData.2
    have hinside :
        d₀.1.insideLength =
          totalMultiplicity (restrictMultiplicities mu r) :=
      d₀.1.insideLength_eq_totalMultiplicity_restrict
        mu r hSpec₀
    have hfiber :
        (∑ d ∈
            (specFixedRawCollapseData
              (splitLeafMultiplicity mu r) m).filter
                (fun d => d.1.collapseShape = shape),
            collapseRawFixedWordSummand mu r z lstar d.1) =
          ∑ d ∈ Finset.univ.filter
              (fun d : FixedRawCollapseData
                  (InsideLeaf r) (OutsideLeaf r) m =>
                CollapseMultiplicitySpec
                    (splitLeafMultiplicity mu r) d.1 ∧
                  d.1.collapseShape = d₀.1.collapseShape),
            collapseRawFixedWordSummand mu r z lstar d.1 := by
      apply Finset.sum_congr
      · ext d
        simp [hdshape]
      · intro d hd
        rfl
    have hfixed :=
      sum_filter_witnessShape_collapseRawFixedWordSummand_le_sum_combinedCollapseTerm
        hsingle ht hroot Nm mu compound hcompound z hsep hdiam
        hr lstar d₀ hSpec₀ hblocks hIHcontract
    have hscalar :=
      two_pow_mul_sum_combinedCollapseTerm_le_inductiveRHSSum
        C0 D hsingle.1 hD ht hroot Nm mu compound r
        hrBranch d₀.1 hSpec₀ hblocks
    rw [hfiber, ← hinside]
    exact le_trans
      (mul_le_mul_of_nonneg_left hfixed (by positivity))
      hscalar
  calc
    paperSum (M := m) (leafMultiplicity mu)
          (primitiveSeparatedChainWeight z) ≤
        ∑ d : FixedRawCollapseData
            (InsideLeaf r) (OutsideLeaf r) m,
          collapseRawFixedWordSummand mu r z lstar d.1 :=
      paperSum_primitiveSeparated_le_sum_collapseRawFixedWord
        ht Nm mu compound z hsep hdiam hr lstar
    _ =
        ∑ shape ∈ activeCollapseShapes mu r m,
          ∑ d ∈
            (specFixedRawCollapseData
              (splitLeafMultiplicity mu r) m).filter
                (fun d => d.1.collapseShape = shape),
            collapseRawFixedWordSummand mu r z lstar d.1 :=
      sum_collapseRawFixedWordSummand_eq_sum_activeShapes
        ht hroot mu r hrBranch z lstar
    _ ≤ B := hshapes
    _ = inductiveRHS C0 D m t Nm mu compound := by
      subst m
      exact
        (inductiveRHS_eq_factored C0 D
          (totalMultiplicity mu) t Nm mu compound).symm

/-- **Proposition 5.9 / (5.32)--(5.33).** -/
theorem inductive_estimate :
    ∃ C0 D : ℝ, InductiveEstimate C0 D := by
  obtain ⟨C0, hsingle⟩ := singleScale_estimate
  let D : ℝ := Real.exp (C0 ^ (10 : ℕ))
  refine ⟨C0, D, ?_⟩
  exact inductiveEstimate_of_singleScale_of_eligibleStep
    hsingle rfl (eligibleCollapseStep hsingle rfl)

end

end Anderson4D
