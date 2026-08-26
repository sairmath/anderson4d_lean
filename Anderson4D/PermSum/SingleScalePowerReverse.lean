import Anderson4D.PermSum.SingleScalePowerLedger

/-!
# Reverse single-scale power comparison

Equation (5.71) also gives the comparison in the direction needed by the
final single-scale assembly.  The price is the square of the off-path inverse
parent-scale ratios.  This file bounds that product by the uniform loss from
(5.69), and packages the subsequent insertion of the full ratio cube.
-/

set_option warningAsError true

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- The branch-scale power on the left of paper (5.72). -/
def singleScaleBranchPower {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) : ℝ :=
  ∏ v ∈ BranchNodes t,
    (scaleN Nm v : ℝ) ^
      ((-2 : ℤ) * ((gamma2 mu compound v : ℤ) - 1))

/-- The leaf-scale power on the right of paper (5.72), including the
distinguished-parent factor. -/
def singleScaleLeafPower {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (l₀ : HeppLeaf t) : ℝ :=
  (∏ l ∈ simpleLeaves t compound,
      (scaleN Nm (parentV l) : ℝ) ^ (-4 : ℤ)) *
    (∏ l ∈ compoundLeaves t compound,
      (scaleN Nm (parentV l) : ℝ) ^
        ((-2 : ℤ) * (mu.m l : ℤ))) *
    (scaleN Nm (parentV l₀.1) : ℝ) ^ (2 : ℤ)

/-- The residual product in (5.71), specialized to the dyadic marking. -/
def offPathInverseRatioProduct {t : PlaneTree}
    (Nm : HeppMarking t) (l₀ : HeppLeaf t) : ℝ :=
  ∏ v ∈ branchesOffLeafPath l₀, inverseParentScaleRatio Nm v

/-- Every off-path branch is a non-root branch. -/
theorem branchesOffLeafPath_subset_nonrootBranches {t : PlaneTree}
    (l₀ : HeppLeaf t) :
    branchesOffLeafPath l₀ ⊆ nonrootBranches t := by
  intro v hv
  have hv' := Finset.mem_filter.mp hv
  rw [nonrootBranches, Finset.mem_erase]
  refine ⟨?_, hv'.1⟩
  intro h
  subst v
  apply hv'.2
  change ([] : List ℕ) <+: l₀.1.1
  exact List.nil_prefix

/-- On a non-root branch, the inverse parent-scale ratio is at least one. -/
theorem one_le_inverseParentScaleRatio_of_mem_nonrootBranches
    {t : PlaneTree} (Nm : HeppMarking t) {v : VPos t}
    (hv : v ∈ nonrootBranches t) :
    1 ≤ inverseParentScaleRatio Nm v := by
  have hvBranch : v ∈ BranchNodes t := by
    exact (Finset.mem_erase.mp hv).2
  have hvRoot : v ≠ rootV t := by
    exact (Finset.mem_erase.mp hv).1
  have hchild : 0 < (scaleN Nm v : ℝ) := by
    exact_mod_cast scaleN_pos Nm v
  rw [inverseParentScaleRatio, one_le_div₀ hchild]
  have hmark := (Nm.parent_gt v hvBranch hvRoot).le
  exact_mod_cast Nat.pow_le_pow_right (by omega) hmark

/-- The off-path inverse-ratio product is bounded by the product over all
non-root branches. -/
theorem offPathInverseRatioProduct_le_fullProduct
    {t : PlaneTree} (Nm : HeppMarking t) (l₀ : HeppLeaf t) :
    offPathInverseRatioProduct Nm l₀ ≤
      ∏ v ∈ nonrootBranches t, inverseParentScaleRatio Nm v := by
  let s := branchesOffLeafPath l₀
  let u := nonrootBranches t
  have hsu : s ⊆ u :=
    branchesOffLeafPath_subset_nonrootBranches l₀
  have hdiff :
      1 ≤ ∏ v ∈ u \ s, inverseParentScaleRatio Nm v := by
    apply Finset.one_le_prod
    intro v hv
    exact one_le_inverseParentScaleRatio_of_mem_nonrootBranches Nm
      (Finset.mem_sdiff.mp hv).1
  have hsnonneg :
      0 ≤ ∏ v ∈ s, inverseParentScaleRatio Nm v := by
    exact Finset.prod_nonneg fun v _ =>
      inverseParentScaleRatio_nonneg Nm v
  calc
    offPathInverseRatioProduct Nm l₀ =
        ∏ v ∈ s, inverseParentScaleRatio Nm v := by
      rfl
    _ ≤
        (∏ v ∈ u \ s, inverseParentScaleRatio Nm v) *
          ∏ v ∈ s, inverseParentScaleRatio Nm v := by
      nlinarith
    _ = ∏ v ∈ u, inverseParentScaleRatio Nm v := by
      exact Finset.prod_sdiff hsu
    _ = ∏ v ∈ nonrootBranches t,
          inverseParentScaleRatio Nm v := by
      rfl

/-- Uniform `(8 exp 4)^m` bound for the residual product in (5.71). -/
theorem offPathInverseRatioProduct_le_uniformPower
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (_compound : Finset (VPos t)) (l₀ : HeppLeaf t)
    (hscale : SatisfiesSingleScaleCondition Nm mu) :
    offPathInverseRatioProduct Nm l₀ ≤
      (8 * Real.exp 4) ^ totalMultiplicity mu := by
  calc
    offPathInverseRatioProduct Nm l₀ ≤
        ∏ v ∈ nonrootBranches t,
          inverseParentScaleRatio Nm v :=
      offPathInverseRatioProduct_le_fullProduct Nm l₀
    _ ≤ (8 * Real.exp 4) ^ totalMultiplicity mu :=
      prod_inverseParentScaleRatio_le_uniform_power
        ht hroot Nm mu hscale

/--
Exact reverse form of (5.71): the leaf power is the branch power times the
square of the residual off-path inverse-ratio product.
-/
theorem singleScale_leafPower_eq_branchPower_mul_offPathSquare
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (l₀ : HeppLeaf t) :
    singleScaleLeafPower Nm mu compound l₀ =
      singleScaleBranchPower Nm mu compound *
        offPathInverseRatioProduct Nm l₀ ^ 2 := by
  let A : ℝ :=
    ∏ v ∈ BranchNodes t,
      (scaleN Nm v : ℝ) ^
        ((gamma2 mu compound v : ℤ) - 1)
  let B : ℝ :=
    (∏ l ∈ simpleLeaves t compound,
      (scaleN Nm (parentV l) : ℝ) ^ (2 : ℤ)) *
    (∏ l ∈ compoundLeaves t compound,
      (scaleN Nm (parentV l) : ℝ) ^ (mu.m l : ℤ)) *
    (scaleN Nm (parentV l₀.1) : ℝ) ^ (-1 : ℤ)
  let Q : ℝ := offPathInverseRatioProduct Nm l₀
  have hN : ∀ v ∈ BranchNodes t, 0 < (scaleN Nm v : ℝ) := by
    intro v _hv
    exact_mod_cast scaleN_pos Nm v
  have hABQ : A = B * Q := by
    dsimp only [A, B, Q, offPathInverseRatioProduct,
      inverseParentScaleRatio]
    exact paper571_direct_product_identity
      ht hroot mu compound l₀ (fun v => (scaleN Nm v : ℝ)) hN
  have hQpos : 0 < Q := by
    dsimp only [Q, offPathInverseRatioProduct,
      inverseParentScaleRatio]
    apply Finset.prod_pos
    intro v _hv
    exact div_pos
      (by exact_mod_cast scaleN_pos Nm (parentV v))
      (by exact_mod_cast scaleN_pos Nm v)
  have hQne : Q ≠ 0 := hQpos.ne'
  have hbranch :
      singleScaleBranchPower Nm mu compound =
        A ^ (-2 : ℤ) := by
    dsimp only [singleScaleBranchPower, A]
    rw [← Finset.prod_zpow]
    apply Finset.prod_congr rfl
    intro v _hv
    rw [← zpow_mul]
    congr 1
    ring
  have hsimple :
      (∏ l ∈ simpleLeaves t compound,
          (scaleN Nm (parentV l) : ℝ) ^ (2 : ℤ)) ^ (-2 : ℤ) =
        ∏ l ∈ simpleLeaves t compound,
          (scaleN Nm (parentV l) : ℝ) ^ (-4 : ℤ) := by
    rw [← Finset.prod_zpow]
    apply Finset.prod_congr rfl
    intro l _hl
    rw [← zpow_mul]
    congr 1
  have hcompound :
      (∏ l ∈ compoundLeaves t compound,
          (scaleN Nm (parentV l) : ℝ) ^
            (mu.m l : ℤ)) ^ (-2 : ℤ) =
        ∏ l ∈ compoundLeaves t compound,
          (scaleN Nm (parentV l) : ℝ) ^
            ((-2 : ℤ) * (mu.m l : ℤ)) := by
    rw [← Finset.prod_zpow]
    apply Finset.prod_congr rfl
    intro l _hl
    rw [← zpow_mul]
    congr 1
    ring
  have hleaf :
      singleScaleLeafPower Nm mu compound l₀ =
        B ^ (-2 : ℤ) := by
    dsimp only [singleScaleLeafPower, B]
    rw [mul_zpow, mul_zpow, hsimple, hcompound, ← zpow_mul]
    congr 2
  have hcancel :
      (B * Q) ^ (-2 : ℤ) * Q ^ (2 : ℤ) =
        B ^ (-2 : ℤ) := by
    rw [mul_zpow]
    calc
      B ^ (-2 : ℤ) * Q ^ (-2 : ℤ) * Q ^ (2 : ℤ) =
          B ^ (-2 : ℤ) *
            (Q ^ (-2 : ℤ) * Q ^ (2 : ℤ)) := by ring
      _ = B ^ (-2 : ℤ) * Q ^ ((-2 : ℤ) + 2) := by
        rw [zpow_add₀ hQne]
      _ = B ^ (-2 : ℤ) := by norm_num
  calc
    singleScaleLeafPower Nm mu compound l₀ =
        B ^ (-2 : ℤ) := hleaf
    _ = (B * Q) ^ (-2 : ℤ) * Q ^ (2 : ℤ) := hcancel.symm
    _ = A ^ (-2 : ℤ) * Q ^ (2 : ℤ) := by rw [← hABQ]
    _ = singleScaleBranchPower Nm mu compound *
        offPathInverseRatioProduct Nm l₀ ^ 2 := by
      rw [hbranch]
      rfl

/--
The closure direction needed after the copy elimination:
`leafPower ≤ (8 exp 4)^(2m) * branchPower`.
-/
theorem singleScale_leafPower_le_uniformPower_mul_branchPower
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (l₀ : HeppLeaf t)
    (hscale : SatisfiesSingleScaleCondition Nm mu) :
    singleScaleLeafPower Nm mu compound l₀ ≤
      (8 * Real.exp 4) ^ (2 * totalMultiplicity mu) *
        singleScaleBranchPower Nm mu compound := by
  let K : ℝ := 8 * Real.exp 4
  let m : ℕ := totalMultiplicity mu
  let Q : ℝ := offPathInverseRatioProduct Nm l₀
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q, offPathInverseRatioProduct]
    exact Finset.prod_nonneg fun v _ =>
      inverseParentScaleRatio_nonneg Nm v
  have hQ :
      Q ≤ K ^ m := by
    simpa only [Q, K, m] using
      offPathInverseRatioProduct_le_uniformPower
        ht hroot Nm mu compound l₀ hscale
  have hQsq :
      Q ^ 2 ≤ K ^ (2 * m) := by
    calc
      Q ^ 2 ≤ (K ^ m) ^ 2 :=
        pow_le_pow_left₀ hQ0 hQ 2
      _ = K ^ (2 * m) := by
        rw [← pow_mul]
        congr 1
        omega
  have hbranch0 :
      0 ≤ singleScaleBranchPower Nm mu compound := by
    unfold singleScaleBranchPower
    exact Finset.prod_nonneg fun v _ => zpow_nonneg (by positivity) _
  rw [singleScale_leafPower_eq_branchPower_mul_offPathSquare
    ht hroot Nm mu compound l₀]
  dsimp only [Q] at hQsq
  calc
    singleScaleBranchPower Nm mu compound *
        offPathInverseRatioProduct Nm l₀ ^ 2 ≤
      singleScaleBranchPower Nm mu compound * K ^ (2 * m) :=
        mul_le_mul_of_nonneg_left hQsq hbranch0
    _ = K ^ (2 * m) *
        singleScaleBranchPower Nm mu compound := by ring
    _ = (8 * Real.exp 4) ^ (2 * totalMultiplicity mu) *
        singleScaleBranchPower Nm mu compound := by rfl

/--
Consumable final form: after reversing (5.72), reinsert the full cube of
parent-scale ratios at total cost `(8 exp 4)^(5m)`.
-/
theorem singleScale_leafPower_le_uniformPower_mul_branchPower_mul_ratioCube
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (l₀ : HeppLeaf t)
    (hscale : SatisfiesSingleScaleCondition Nm mu) :
    singleScaleLeafPower Nm mu compound l₀ ≤
      (8 * Real.exp 4) ^ (5 * totalMultiplicity mu) *
        singleScaleBranchPower Nm mu compound *
        ∏ v ∈ nonrootBranches t, (parentScaleRatio Nm v) ^ 3 := by
  let K : ℝ := 8 * Real.exp 4
  let m : ℕ := totalMultiplicity mu
  let B : ℝ := singleScaleBranchPower Nm mu compound
  let P : ℝ :=
    ∏ v ∈ nonrootBranches t, (parentScaleRatio Nm v) ^ 3
  have hreverse :
      singleScaleLeafPower Nm mu compound l₀ ≤
        K ^ (2 * m) * B := by
    simpa only [K, m, B] using
      singleScale_leafPower_le_uniformPower_mul_branchPower
        ht hroot Nm mu compound l₀ hscale
  have hinsert :
      1 ≤ K ^ (3 * m) * P := by
    simpa only [K, m, P] using
      one_le_uniformPower_mul_parentScaleRatioCube
        ht hroot Nm mu hscale
  have hbase0 : 0 ≤ K ^ (2 * m) * B := by
    dsimp only [K, B, singleScaleBranchPower]
    positivity
  calc
    singleScaleLeafPower Nm mu compound l₀ ≤
        K ^ (2 * m) * B := hreverse
    _ = (K ^ (2 * m) * B) * 1 := by ring
    _ ≤ (K ^ (2 * m) * B) * (K ^ (3 * m) * P) :=
      mul_le_mul_of_nonneg_left hinsert hbase0
    _ = K ^ (5 * m) * B * P := by
      calc
        K ^ (2 * m) * B * (K ^ (3 * m) * P) =
            (K ^ (2 * m) * K ^ (3 * m)) * B * P := by ring
        _ = K ^ (2 * m + 3 * m) * B * P := by
          rw [pow_add]
        _ = K ^ (5 * m) * B * P := by
          rw [show 2 * m + 3 * m = 5 * m by omega]
    _ = (8 * Real.exp 4) ^ (5 * totalMultiplicity mu) *
        singleScaleBranchPower Nm mu compound *
        ∏ v ∈ nonrootBranches t, (parentScaleRatio Nm v) ^ 3 := by
      rfl

end

end Anderson4D
