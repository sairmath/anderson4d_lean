import Anderson4D.PermSum.SingleScaleSetup

/-!
# Power-counting reduction for the single-scale estimate

This file closes the product-to-exponential part of paper (5.69).  Under
the single-scale condition, every inverse parent-scale ratio is bounded by
`8` times an exponential of its normalized accumulated scale.  Reordering
those exponents and applying (5.68) gives one uniform exponential loss in
the total multiplicity.

The paper writes the final loss as an unspecified `C^m`; here the explicit
choice is `(8 * exp 4)^m`.  The factor `4` includes the inclusive-ancestor
constant recorded in `docs/PAPER_NOTES.md` under (5.69).
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- The reciprocal of `parentScaleRatio`, namely `N_{v⁺}/N_v`. -/
def inverseParentScaleRatio {t : PlaneTree}
    (Nm : HeppMarking t) (v : VPos t) : ℝ :=
  (scaleN Nm (parentV v) : ℝ) / (scaleN Nm v : ℝ)

theorem inverseParentScaleRatio_nonneg {t : PlaneTree}
    (Nm : HeppMarking t) (v : VPos t) :
    0 ≤ inverseParentScaleRatio Nm v := by
  unfold inverseParentScaleRatio
  positivity

/-- The auxiliary inverse ratio cancels the ratio appearing in the frozen
right-hand sides. -/
theorem inverseParentScaleRatio_mul_parentScaleRatio {t : PlaneTree}
    (Nm : HeppMarking t) (v : VPos t) :
    inverseParentScaleRatio Nm v * parentScaleRatio Nm v = 1 := by
  have hparent : (scaleN Nm (parentV v) : ℝ) ≠ 0 := by
    exact_mod_cast (scaleN_pos Nm (parentV v)).ne'
  have hchild : (scaleN Nm v : ℝ) ≠ 0 := by
    exact_mod_cast (scaleN_pos Nm v).ne'
  unfold inverseParentScaleRatio parentScaleRatio
  field_simp

/--
One factor in (5.69), before multiplying over non-root branch nodes.
-/
theorem inverseParentScaleRatio_le_eight_mul_exp {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : SatisfiesSingleScaleCondition Nm mu)
    {v : VPos t} (hv : v ∈ nonrootBranches t) :
    inverseParentScaleRatio Nm v ≤
      8 * Real.exp
        ((accumulatedScale Nm mu v : ℝ) / scaleN Nm v) := by
  have hN : 0 < (scaleN Nm v : ℝ) := by
    exact_mod_cast scaleN_pos Nm v
  have hsingle :
      (scaleN Nm (parentV v) : ℝ) ≤
        8 * (accumulatedScale Nm mu v : ℝ) := by
    exact_mod_cast hscale v hv
  calc
    inverseParentScaleRatio Nm v ≤
        (8 * (accumulatedScale Nm mu v : ℝ)) /
          scaleN Nm v := by
      exact div_le_div_of_nonneg_right hsingle hN.le
    _ = 8 * ((accumulatedScale Nm mu v : ℝ) / scaleN Nm v) := by
      ring
    _ ≤ 8 * Real.exp
        ((accumulatedScale Nm mu v : ℝ) / scaleN Nm v) := by
      gcongr
      linarith [Real.add_one_le_exp
        ((accumulatedScale Nm mu v : ℝ) / scaleN Nm v)]

/--
Finite-product form of (5.69), before bounding the number of branch nodes
and the reordered exponent.
-/
theorem prod_inverseParentScaleRatio_le_exp_cost {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : SatisfiesSingleScaleCondition Nm mu) :
    (∏ v ∈ nonrootBranches t, inverseParentScaleRatio Nm v) ≤
      (8 : ℝ) ^ (nonrootBranches t).card *
        Real.exp (singleScaleExponentCost Nm mu) := by
  calc
    (∏ v ∈ nonrootBranches t, inverseParentScaleRatio Nm v) ≤
        ∏ v ∈ nonrootBranches t,
          (8 * Real.exp
            ((accumulatedScale Nm mu v : ℝ) / scaleN Nm v)) := by
      exact Finset.prod_le_prod
        (fun v _ => inverseParentScaleRatio_nonneg Nm v)
        (fun v hv =>
          inverseParentScaleRatio_le_eight_mul_exp Nm mu hscale hv)
    _ = (8 : ℝ) ^ (nonrootBranches t).card *
        Real.exp
          (∑ v ∈ nonrootBranches t,
            (accumulatedScale Nm mu v : ℝ) / scaleN Nm v) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      congr 1
      exact (Real.exp_sum _ _).symm
    _ = (8 : ℝ) ^ (nonrootBranches t).card *
        Real.exp (singleScaleExponentCost Nm mu) := by
      rw [sum_accumulatedScale_div_eq_exponentCost]

/-- A valid tree has no more non-root branch nodes than word positions. -/
theorem card_nonrootBranches_le_totalMultiplicity {t : PlaneTree}
    (ht : t.isValid = true) (mu : Multiplicities t) :
    (nonrootBranches t).card ≤ totalMultiplicity mu := by
  have hbranch :
      (BranchNodes t).card ≤ branchExcess t := by
    rw [← sum_branchNodes_childCount_sub_one_eq_branchExcess,
      Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun v hv => by
      have htwo : 2 ≤ childCount t v.1 := by
        simpa [BranchNodes] using hv
      omega
  have hnonroot :
      (nonrootBranches t).card ≤ (BranchNodes t).card :=
    Finset.card_erase_le
  have hleaf :
      t.leafCount ≤ totalMultiplicity mu := by
    have hcard :
        Fintype.card (HeppLeaf t) = t.leafCount := by
      rw [Fintype.card_coe, card_Leaves_eq_leafCount]
    rw [← hcard, totalMultiplicity, Fintype.card_eq_sum_ones]
    exact Finset.sum_le_sum fun l _ =>
      le_trans (by omega) (mu.two_le l.1 l.2)
  calc
    (nonrootBranches t).card ≤ (BranchNodes t).card := hnonroot
    _ ≤ branchExcess t := hbranch
    _ = t.leafCount - 1 :=
      branchExcess_eq_leafCount_sub_one t ht
    _ ≤ t.leafCount := Nat.sub_le _ _
    _ ≤ totalMultiplicity mu := hleaf

/--
Explicit `C^m` form of paper (5.69), with `C = 8 exp(4)`.
-/
theorem prod_inverseParentScaleRatio_le_uniform_power {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : SatisfiesSingleScaleCondition Nm mu) :
    (∏ v ∈ nonrootBranches t, inverseParentScaleRatio Nm v) ≤
      (8 * Real.exp 4) ^ totalMultiplicity mu := by
  let m := totalMultiplicity mu
  have hprod :=
    prod_inverseParentScaleRatio_le_exp_cost Nm mu hscale
  have hcard : (nonrootBranches t).card ≤ m :=
    card_nonrootBranches_le_totalMultiplicity ht mu
  have hcost :
      singleScaleExponentCost Nm mu ≤ 4 * (m : ℝ) := by
    calc
      singleScaleExponentCost Nm mu ≤
          4 * ((m - 1 : ℕ) : ℝ) :=
        singleScaleExponentCost_le_four_mul_total_sub_one
          ht hroot Nm mu
      _ ≤ 4 * (m : ℝ) := by
        gcongr
        exact_mod_cast Nat.sub_le m 1
  calc
    (∏ v ∈ nonrootBranches t, inverseParentScaleRatio Nm v) ≤
        (8 : ℝ) ^ (nonrootBranches t).card *
          Real.exp (singleScaleExponentCost Nm mu) := hprod
    _ ≤ (8 : ℝ) ^ m * Real.exp (4 * (m : ℝ)) := by
      exact mul_le_mul
        (pow_le_pow_right₀ (by norm_num) hcard)
        (Real.exp_le_exp.mpr hcost)
        (Real.exp_pos _).le
        (pow_nonneg (by norm_num) _)
    _ = (8 * Real.exp 4) ^ m := by
      rw [mul_pow]
      congr 1
      rw [show 4 * (m : ℝ) = (m : ℝ) * 4 by ring,
        Real.exp_nat_mul]

end

end Anderson4D
